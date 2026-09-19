! LispReader: text into the GC heap.
!
! The counterpart to Printer.f90.
!
! Together the two give a ROUND TRIP -- read a form, print it, get the
! input back -- which tests the whole layer against real Clojure text
! rather than against structures built by hand in a test. A reader and
! a printer can only agree if the thing between them actually holds
! what it was given.
!
! Recursive descent straight over the character buffer, with no
! separate token array. The pre-GC reader had one because it recorded a
! line and column per token; source positions are an open question for
! the new representation (PLAN.md: a GC object has i1/i2 and count
! already took i1), so this deliberately does not pretend to solve it.
!
! Errors thread through module state, the same shape LispReader uses:
! Fortran has no exceptions, so every routine checks has_error after a
! call that could set it and bails early.
!
! DEFERRED, and listed rather than silently missing: the discard macro
! (#_), sets (#{}), regex literals and auto-gensym. Those are reader MACROS layered on the
! core shapes; the shapes are what the data layer needs proving.
module LispReader
  use GC
  use PersistentList
  use PersistentVector
  use Assoc
  use Regex
  use, intrinsic :: ieee_arithmetic
  implicit none
  private

  character(len=:), allocatable :: last_error
  logical :: has_error = .false.

  public :: gcr_read, gcr_read_all, gcr_error, gcr_has_error
  public :: gcr_begin_file, gcr_read_next, gcr_position

  ! SOURCE POSITIONS. A list form records where it was read from:
  ! OBJ_CONS's i2 (free: i1 is the count) holds file-id * 2^26 + the
  ! 1-based character offset of its opening paren. The analyser copies
  ! it onto the node, and an error names it. Line and column are
  ! recovered from the offset by a binary search over line_starts,
  ! computed once per file by gcr_begin_file -- cheaper than counting
  ! newlines per form and simpler than threading a line counter
  ! through every read_* routine. Files are named once, in a small
  ! table; id 0 is "no file" (the REPL).
  integer, parameter :: POS_SHIFT = 2**26
  integer, parameter :: MAX_FILES = 64
  ! One entry per file ever loaded, line index included: a position
  ! inside core.clj is asked about long after some other file became
  ! current, and must be answered against core.clj's own lines.
  type :: src_file
     character(len=512) :: name = ""
     integer, allocatable :: line_starts(:)
  end type src_file
  type(src_file), save :: files(MAX_FILES)
  integer, save :: n_files = 0
  integer, save :: cur_file = 0

contains

  function gcr_has_error() result(yes)
    logical :: yes
    yes = has_error
  end function gcr_has_error

  function gcr_error() result(s)
    character(len=:), allocatable :: s
    s = ""
    if (allocated(last_error)) s = last_error
  end function gcr_error

  subroutine fail(msg)
    character(len=*), intent(in) :: msg
    has_error = .true.
    last_error = msg
  end subroutine fail

  ! Names the file the next gcr_read_next calls read from, and indexes
  ! its lines. Call once per file, before the first form.
  subroutine gcr_begin_file(text, name)
    character(len=*), intent(in) :: text, name
    integer :: i, n, k
    cur_file = 0
    do i = 1, n_files
       if (trim(files(i)%name) == name) cur_file = i
    end do
    if (cur_file == 0 .and. n_files < MAX_FILES) then
       n_files = n_files + 1
       files(n_files)%name = name
       cur_file = n_files
    end if
    if (cur_file == 0) return
    n = 1
    do i = 1, len(text)
       if (text(i:i) == achar(10)) n = n + 1
    end do
    if (allocated(files(cur_file)%line_starts)) deallocate(files(cur_file)%line_starts)
    allocate(files(cur_file)%line_starts(n))
    files(cur_file)%line_starts(1) = 1
    k = 1
    do i = 1, len(text)
       if (text(i:i) == achar(10)) then
          k = k + 1
          files(cur_file)%line_starts(k) = i + 1
       end if
    end do
  end subroutine gcr_begin_file

  ! The next form after pos, advancing pos past it; eof when only
  ! whitespace and comments remain. What Compiler.load does per form:
  ! read, then evaluate, then read again -- so a form can depend on
  ! what the one before it changed (DEVIATIONS 1, closed).
  function gcr_read_next(text, pos, roots, eof) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    logical, intent(out) :: eof
    type(gc_value) :: v
    has_error = .false.
    last_error = ""
    eof = .false.
    v = gc_nil()
    call skip_ignorables(text, pos, roots)
    if (pos > len(text)) then
       eof = .true.
       return
    end if
    v = read_form(text, pos, roots)
  end function gcr_read_next

  ! "file:line:col" for a packed position, or "line:col" with no file.
  function gcr_position(packed) result(s)
    integer, intent(in) :: packed
    character(len=:), allocatable :: s
    character(len=24) :: lb, cb
    integer :: fid, off, lo, hi, mid, line, col
    fid = packed / POS_SHIFT
    off = mod(packed, POS_SHIFT)
    line = 1
    col = off
    if (fid >= 1 .and. fid <= n_files) then
       if (allocated(files(fid)%line_starts)) then
          lo = 1
          hi = size(files(fid)%line_starts)
          do while (lo < hi)
             mid = (lo + hi + 1) / 2
             if (files(fid)%line_starts(mid) <= off) then
                lo = mid
             else
                hi = mid - 1
             end if
          end do
          line = lo
          col = off - files(fid)%line_starts(lo) + 1
       end if
    end if
    write(lb, '(I0)') line
    write(cb, '(I0)') col
    if (fid >= 1 .and. fid <= n_files) then
       s = trim(files(fid)%name) // ":" // trim(lb) // ":" // trim(cb)
    else
       s = trim(lb) // ":" // trim(cb)
    end if
  end function gcr_position

  ! Reads ONE form from text. Trailing text is ignored, which is what
  ! a REPL line wants; a whole-file reader would loop on the position.
  function gcr_read(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: pos
    has_error = .false.
    last_error = ""
    pos = 1
    v = read_form(text, pos, roots)
  end function gcr_read

  ! Every form in the text, as a vector. What a file needs, as
  ! opposed to gcr_read's single form: the position carries across
  ! calls instead of restarting, so `(def a 1) (def b 2)` is two forms
  ! rather than one form and some ignored text.
  function gcr_read_all(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, form
    integer :: pos, base

    has_error = .false.
    last_error = ""
    pos = 1
    base = vs_enter(1)
    v = gcv_empty(roots)
    call vs_set(base + 1, v)
    do
       call skip_ignorables(text, pos, [vs_get(base + 1)])
       if (pos > len(text)) exit
       form = read_form(text, pos, [vs_get(base + 1)])
       if (has_error) exit
       v = gcv_conj(vs_get(base + 1), form, roots)
       call vs_set(base + 1, v)
    end do
    v = vs_get(base + 1)
    call vs_leave(base)
  end function gcr_read_all

  ! ---- character classification (mirrors LispReader's) ----

  pure function is_space(c) result(yes)
    character, intent(in) :: c
    logical :: yes
    ! Comma is whitespace in Clojure, which is why {:a 1, :b 2} reads.
    yes = (c == " " .or. c == achar(9) .or. c == achar(10) .or. &
           c == achar(13) .or. c == achar(12) .or. c == ",")
  end function is_space

  ! LispReader.isTerminatingMacro: a macro character ENDS a token,
  ! except for #, % and the quote -- which is why ss' and x' are single
  ! symbols in Clojure rather than a symbol followed by a quote form.
  ! Treating the quote as a delimiter here made every prime-suffixed
  ! name a reader error, and one reader error aborts the whole file
  ! (DEVIATIONS.md 1).
  pure function is_delim(c) result(yes)
    character, intent(in) :: c
    logical :: yes
    yes = (c == "(" .or. c == ")" .or. c == "[" .or. c == "]" .or. &
           c == "{" .or. c == "}" .or. c == '"' .or. c == ";" .or. &
           c == "`" .or. c == "~" .or. c == "@" .or. c == "^")
  end function is_delim

  subroutine skip_space(text, pos)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    do while (pos <= len(text))
       if (text(pos:pos) == ";") then
          do while (pos <= len(text))
             if (text(pos:pos) == achar(10)) exit
             pos = pos + 1
          end do
       else if (is_space(text(pos:pos))) then
          pos = pos + 1
       else
          exit
       end if
    end do
  end subroutine skip_space

  ! Whitespace, commas, comments -- AND discards. #_ is not a form that
  ! evaluates to nothing; LispReader's CommentReader returns the reader
  ! itself as a sentinel and every collection loop skips it, so what #_
  ! really is, is another kind of space.
  !
  ! Reading it as "discard one form, then read the next" is what this
  ! replaces, and it worked everywhere except the place that matters:
  ! at the END of a collection there IS no next form, so
  ! (and true #_(= 1 1)) died on "unexpected ')'". That shape is in
  ! Clojure's own suite -- test-empty in sequences.clj carries a
  ! commented-out assertion exactly that way -- and one reader error
  ! aborts the whole file, so the namespace defined no tests at all.
  recursive subroutine skip_ignorables(text, pos, roots)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: ignored

    do
       call skip_space(text, pos)
       if (pos + 1 > len(text)) return
       if (text(pos:pos + 1) /= "#_") return
       pos = pos + 2
       ignored = read_form(text, pos, roots)
       if (has_error) return
    end do
  end subroutine skip_ignorables

  ! ---- forms ----

  recursive function read_form(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character :: c

    v = gc_nil()
    call skip_ignorables(text, pos, roots)
    if (pos > len(text)) then
       call fail("EOF while reading")
       return
    end if

    c = text(pos:pos)
    select case (c)
    case ("(")
       block
         integer :: start
         start = pos
         pos = pos + 1
         v = read_seq(text, pos, ")", .false., roots)
         ! the position, on the head cell of a non-empty list only:
         ! the empty list may be shared
         if (.not. has_error) then
            if (gcl_is(v)) then
               if (gcl_count(v) > 0) call gc_set_i2(v, cur_file * POS_SHIFT + start)
            end if
         end if
       end block
    case ("[")
       pos = pos + 1
       v = read_seq(text, pos, "]", .true., roots)
    case ("{")
       pos = pos + 1
       v = read_map(text, pos, roots)
    case (")", "]", "}")
       call fail("unexpected '" // c // "'")
    case ('"')
       v = read_string(text, pos, roots)
    case ("^")
       pos = pos + 1
       v = read_meta(text, pos, roots)
    case ("#")
       v = read_dispatch(text, pos, roots)
    case ("'")
       pos = pos + 1
       v = wrap("quote", text, pos, roots)
    case ("`")
       pos = pos + 1
       v = wrap("quasiquote", text, pos, roots)
    case ("@")
       pos = pos + 1
       v = wrap("deref", text, pos, roots)
    case ("~")
       pos = pos + 1
       if (pos <= len(text)) then
          if (text(pos:pos) == "@") then
             pos = pos + 1
             v = wrap("splice-unquote", text, pos, roots)
             return
          end if
       end if
       v = wrap("unquote", text, pos, roots)
    case default
       if (c == achar(92)) then
          v = read_char(text, pos, roots)
       else
          v = read_atom(text, pos, roots)
       end if
    end select
  end function read_form

  ! Like a string, but backslashes stay literal: a pattern writes
  ! \\d meaning the two characters, not an escape.
  ! #"..." COMPILES AT READ TIME, matching real Clojure: LispReader's
  ! own regex literal calls Pattern.compile immediately, so #"..." is
  ! already a Pattern object by the time anything evaluates it, not a
  ! string that becomes one later. See Regex.f90 and DEVIATIONS.md on
  ! why ICU is vendored for this rather than written from scratch.
  function read_regex(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, src
    integer :: start, handle

    v = gc_nil()
    pos = pos + 1
    start = pos
    do
       if (pos > len(text)) then
          call fail("EOF while reading a regex literal")
          return
       end if
       if (text(pos:pos) == achar(34)) exit
       if (text(pos:pos) == achar(92)) pos = pos + 1
       pos = pos + 1
    end do
    handle = regex_compile(text(start:pos - 1))
    if (handle == 0) then
       call fail("regex: " // regex_last_error())
       return
    end if
    src = gc_str(text(start:pos - 1), roots)
    v = gc_obj(OBJ_REGEX, [src], [src])
    call gc_set_i1(v, handle)
    pos = pos + 1
  end function read_regex

  ! #(...) -- the anonymous-function shorthand, expanded exactly as
  ! real Clojure's reader does:
  !
  !   #(+ % 1)      -> (fn* [p1] (+ p1 1))
  !   #(+ %1 %2)    -> (fn* [p1 p2] (+ p1 p2))
  !   #(apply f %&) -> (fn* [& pr] (apply f pr))
  !
  ! The arity comes from the HIGHEST %n used, not from how many
  ! appear: #(+ %2 %2) takes two arguments and ignores the first,
  ! which is what Clojure does.
  !
  ! Parameter names are fixed rather than gensymed, so a body that
  ! itself binds p1 would shadow. Real Clojure gensyms here; this
  ! waits on auto-gensym in the reader, and the collision is noted
  ! rather than hidden.
  recursive function read_anon_fn(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, body, params, sym
    integer :: base, maxn, i
    logical :: has_rest
    character(len=16) :: nm

    v = gc_nil()
    base = vs_enter(4)
    body = read_seq(text, pos, ")", .false., roots)
    if (has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 1, body)

    maxn = 0
    has_rest = .false.
    call scan_percent(vs_get(base + 1), maxn, has_rest)

    ! `roots` in every allocation -- the caller's values are plain
    ! locals reachable only through it, and reading #(...) inside a
    ! larger form must not collect the form being built around it.
    ! Same defect read_set had.
    params = gcv_empty(roots)
    call vs_set(base + 2, params)
    do i = 1, maxn
       write(nm, '(A,I0)') "p", i
       sym = gc_sym(trim(nm), roots)
       call vs_set(base + 3, sym)
       params = gcv_conj(vs_get(base + 2), vs_get(base + 3), roots)
       call vs_set(base + 2, params)
    end do
    if (has_rest) then
       sym = gc_sym("&", roots)
       call vs_set(base + 3, sym)
       params = gcv_conj(vs_get(base + 2), vs_get(base + 3), roots)
       call vs_set(base + 2, params)
       sym = gc_sym("pr", roots)
       call vs_set(base + 3, sym)
       params = gcv_conj(vs_get(base + 2), vs_get(base + 3), roots)
       call vs_set(base + 2, params)
    end if

    body = rewrite_percent(vs_get(base + 1), roots)
    call vs_set(base + 1, body)
    sym = gc_sym("fn*", roots)
    call vs_set(base + 3, sym)
    v = gcl_empty(roots)
    call vs_set(base + 4, v)
    v = gcl_cons(vs_get(base + 1), vs_get(base + 4), roots)
    call vs_set(base + 4, v)
    v = gcl_cons(vs_get(base + 2), vs_get(base + 4), roots)
    call vs_set(base + 4, v)
    v = gcl_cons(vs_get(base + 3), vs_get(base + 4), roots)
    call vs_leave(base)
  end function read_anon_fn

  ! Highest %n used anywhere in the form, and whether %& appears.
  recursive subroutine scan_percent(form, maxn, has_rest)
    type(gc_value), intent(in) :: form
    integer, intent(inout) :: maxn
    logical, intent(inout) :: has_rest
    type(gc_value) :: walk
    character(len=:), allocatable :: t
    integer :: i, num, ios

    if (form%tag == GCT_SYM) then
       t = gc_ref_text(form%ref)
       if (len(t) >= 1) then
          if (t(1:1) == "%") then
             if (t == "%") then
                maxn = max(maxn, 1)
             else if (t == "%&") then
                has_rest = .true.
             else
                read(t(2:), *, iostat=ios) num
                if (ios == 0) maxn = max(maxn, num)
             end if
          end if
       end if
       return
    end if
    ! A hinted symbol -- (.getClassName ^StackTraceElement %1) -- is
    ! wrapped in metadata; the walk looks through the wrapper.
    if (gc_kind(form) == OBJ_META) then
       call scan_percent(gc_slot(form, 1), maxn, has_rest)
       return
    end if
    if (gcl_is(form)) then
       walk = form
       do while (gcl_count(walk) > 0)
          call scan_percent(gcl_first(walk), maxn, has_rest)
          walk = gcl_rest(walk, [form])
       end do
    else if (gcv_is(form)) then
       do i = 0, gcv_count(form) - 1
          call scan_percent(gcv_nth(form, i), maxn, has_rest)
       end do
    end if
  end subroutine scan_percent

  ! Replaces %, %n and %& with the parameter names chosen above.
  recursive function rewrite_percent(form, roots) result(out)
    type(gc_value), intent(in) :: form
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, acc, walk, item
    character(len=:), allocatable :: t
    character(len=16) :: nm
    integer :: base, i, num, ios

    out = form
    if (form%tag == GCT_SYM) then
       t = gc_ref_text(form%ref)
       if (len(t) < 1) return
       if (t(1:1) /= "%") return
       if (t == "%") then
          out = gc_sym("p1", roots)
       else if (t == "%&") then
          out = gc_sym("pr", roots)
       else
          read(t(2:), *, iostat=ios) num
          if (ios == 0) then
             write(nm, '(A,I0)') "p", num
             out = gc_sym(trim(nm), roots)
          end if
       end if
       return
    end if

    base = vs_enter(3)
    call vs_set(base + 1, form)
    if (gc_kind(form) == OBJ_META) then
       ! rewrite the value inside the wrapper, keep the metadata
       item = rewrite_percent(gc_slot(vs_get(base + 1), 1), roots)
       call vs_set(base + 2, item)
       out = gc_obj(OBJ_META, [vs_get(base + 2), gc_slot(vs_get(base + 1), 2)], &
            [roots, vs_get(base + 1), vs_get(base + 2)])
    else if (gcl_is(form)) then
       acc = gcv_empty(roots)
       call vs_set(base + 2, acc)
       walk = vs_get(base + 1)
       call vs_set(base + 3, walk)
       do while (gcl_count(vs_get(base + 3)) > 0)
          item = rewrite_percent(gcl_first(vs_get(base + 3)), roots)
          acc = gcv_conj(vs_get(base + 2), item, roots)
          call vs_set(base + 2, acc)
          walk = gcl_rest(vs_get(base + 3), roots)
          call vs_set(base + 3, walk)
       end do
       out = gcl_empty(roots)
       do i = gcv_count(vs_get(base + 2)) - 1, 0, -1
          ! `out` is a plain local, so it has to stay in the root set
          ! by name -- the value stack cannot see it.
          out = gcl_cons(gcv_nth(vs_get(base + 2), i), out, with(roots, out))
       end do
    else if (gcv_is(form)) then
       acc = gcv_empty(roots)
       call vs_set(base + 2, acc)
       do i = 0, gcv_count(vs_get(base + 1)) - 1
          item = rewrite_percent(gcv_nth(vs_get(base + 1), i), roots)
          acc = gcv_conj(vs_get(base + 2), item, roots)
          call vs_set(base + 2, acc)
       end do
       out = vs_get(base + 2)
    end if
    call vs_leave(base)
  end function rewrite_percent

  ! #{...} -- elements read like a vector's, then each maps to
  ! itself. Duplicates collapse, as they must.
  recursive function read_set(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, items, m, item
    integer :: base, i

    v = gc_nil()
    base = vs_enter(3)
    items = read_seq(text, pos, "}", .true., roots)
    if (has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 1, items)
    ! `roots` IN EVERY ALLOCATION. This function keeps its own values
    ! on the value stack, which the collector scans -- but the CALLER'S
    ! values are plain Fortran locals reachable only through the roots
    ! array it passed in. Dropping it here meant that reading a set
    ! INSIDE another form could collect the form being built around
    ! it: (case* ... #{2}) read back as (), silently, with no error.
    !
    ! read_map threads roots correctly and is the shape to copy.
    m = gca_empty(roots)
    call vs_set(base + 2, m)
    do i = 0, gcv_count(vs_get(base + 1)) - 1
       item = gcv_nth(vs_get(base + 1), i)
       call vs_set(base + 3, item)
       m = gca_assoc(vs_get(base + 2), vs_get(base + 3), vs_get(base + 3), roots)
       call vs_set(base + 2, m)
    end do
    v = gc_obj(OBJ_SET, [vs_get(base + 2)], roots)
    call vs_leave(base)
  end function read_set

  ! # is a DISPATCH character, not part of a symbol: what follows it
  ! decides the form. Treating it as an ordinary symbol character
  ! is not harmless -- #{1 2 3} then reads as the symbol # followed
  ! by a three-element map literal, and the error you get is
  ! "map literal has an odd number of forms", nowhere near the
  ! cause.
  !
  ! Note the ordering hazard: an auto-gensym (x#) ends with #, so #
  ! must stay a regular character in the MIDDLE of a token and only
  ! dispatch at the start of one.
  recursive function read_dispatch(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character :: c

    v = gc_nil()
    if (pos + 1 > len(text)) then
       call fail("EOF after #")
       return
    end if
    c = text(pos + 1:pos + 1)
    select case (c)
    case ("^")
       ! #^ is the OLD spelling of ^. Deprecated in Clojure and
       ! still read, and Clojure's own suite still writes it.
       pos = pos + 2
       v = read_meta(text, pos, roots)
    case ("'")
       pos = pos + 2
       v = wrap("var", text, pos, roots)
    case ("{")
       pos = pos + 2
       v = read_set(text, pos, roots)
    case (achar(34))
       ! #"..." -- compiled to a real ICU pattern HERE, at read
       ! time, as Clojure does: a bad pattern is a reader error, not a
       ! runtime one. Backslashes stay literal, the pattern needing
       ! them; the source text is kept alongside the handle so the
       ! literal prints as itself.
       pos = pos + 1
       v = read_regex(text, pos, roots)
    case ("(")
       pos = pos + 2
       v = read_anon_fn(text, pos, roots)
    case ("#")
       pos = pos + 2
       v = read_symbolic(text, pos, roots)
    case default
       call fail("reader: no dispatch for #" // c)
    end select
  end function read_dispatch

  ! ##Inf, ##-Inf and ##NaN -- the symbolic values. They have no
  ! literal spelling of their own, which is the whole reason the reader
  ! macro exists; LispReader.java maps exactly these three and rejects
  ! anything else.
  function read_symbolic(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character(len=:), allocatable :: tok
    integer :: start

    v = gc_nil()
    start = pos
    do while (pos <= len(text))
       if (is_space(text(pos:pos)) .or. is_delim(text(pos:pos))) exit
       pos = pos + 1
    end do
    tok = text(start:pos - 1)
    select case (tok)
    case ("Inf")
       v = gc_real(ieee_value(1.0d0, ieee_positive_inf))
    case ("-Inf")
       v = gc_real(ieee_value(1.0d0, ieee_negative_inf))
    case ("NaN")
       v = gc_real(ieee_value(1.0d0, ieee_quiet_nan))
    case default
       call fail("Invalid token: ##" // tok)
    end select
  end function read_symbolic

  ! ^meta form -- the metadata shorthands, normalised exactly as real
  ! Clojure's reader does:
  !
  !   ^:kw form    -> {:kw true}
  !   ^Type form   -> {:tag Type}
  !   ^"str" form  -> {:tag "str"}
  !   ^{...} form  -> the map itself
  !
  ! The result WRAPS the form rather than annotating it, because
  ! symbol text is interned and a shared pool slot cannot carry
  ! per-occurrence metadata. See OBJ_META in GC.f90.
  recursive function read_meta(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, m, form, key
    integer :: base

    v = gc_nil()
    base = vs_enter(3)
    m = read_form(text, pos, roots)
    if (has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 1, m)

    ! Normalise the shorthands into a map.
    if (gca_is(vs_get(base + 1))) then
       continue
    else if (m%tag == GCT_KEY) then
       ! `roots` again: ^:kw on a form inside another form.
       v = gca_empty(roots)
       call vs_set(base + 2, v)
       m = gca_assoc(vs_get(base + 2), vs_get(base + 1), gc_bool(.true.), roots)
       call vs_set(base + 1, m)
    else if (gcv_is(vs_get(base + 1))) then
       ! A VECTOR is param-tags -- Clojure 1.12's ^[long] on a
       ! method reference. MetaReader maps it to :param-tags the
       ! same way it maps a symbol to :tag.
       v = gca_empty(roots)
       call vs_set(base + 2, v)
       key = gc_key("param-tags", roots)
       call vs_set(base + 3, key)
       m = gca_assoc(vs_get(base + 2), vs_get(base + 3), vs_get(base + 1), roots)
       call vs_set(base + 1, m)
    else if (m%tag == GCT_SYM .or. m%tag == GCT_STR) then
       v = gca_empty(roots)
       call vs_set(base + 2, v)
       key = gc_key("tag", roots)
       call vs_set(base + 3, key)
       m = gca_assoc(vs_get(base + 2), vs_get(base + 3), vs_get(base + 1), roots)
       call vs_set(base + 1, m)
    else
       call fail("Metadata must be Symbol,Keyword,String,Vector or Map")
       call vs_leave(base); return
    end if

    form = read_form(text, pos, roots)
    if (has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 2, form)
    v = gc_obj(OBJ_META, [vs_get(base + 2), vs_get(base + 1)], roots)
    call vs_leave(base)
  end function read_meta

  ! (sym form) -- what ', `, @ and ~ expand to.
  recursive function wrap(name, text, pos, roots) result(v)
    character(len=*), intent(in) :: name
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, inner, sym
    type(gc_value), allocatable :: r2(:)

    v = gc_nil()
    inner = read_form(text, pos, roots)
    if (has_error) return
    r2 = with(roots, inner)
    sym = gc_sym(name, r2)
    r2 = with(r2, sym)
    v = gcl_empty(r2)
    v = gcl_cons(inner, v, with(r2, v))
    v = gcl_cons(sym, v, with(r2, v))
  end function wrap

  ! Elements accumulate in a VECTOR, which is rooted through the roots
  ! argument on every conj. A plain Fortran array of gc_value would not
  ! be seen by the collector, and a form long enough to trigger one
  ! mid-read would lose its earlier elements.
  recursive function read_seq(text, pos, closer, as_vector, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    character, intent(in) :: closer
    logical, intent(in) :: as_vector
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, acc, item
    type(gc_value), allocatable :: r2(:)
    integer :: i

    v = gc_nil()
    acc = gcv_empty(roots)
    do
       r2 = with(roots, acc)
       call skip_ignorables(text, pos, r2)
       if (pos > len(text)) then
          call fail("EOF while reading, expected '" // closer // "'")
          return
       end if
       if (text(pos:pos) == closer) then
          pos = pos + 1
          exit
       end if
       item = read_form(text, pos, r2)
       if (has_error) return
       acc = gcv_conj(acc, item, with(r2, item))
    end do

    if (as_vector) then
       v = acc
       return
    end if
    ! Build the list back to front, so it comes out in order.
    r2 = with(roots, acc)
    v = gcl_empty(r2)
    do i = gcv_count(acc) - 1, 0, -1
       v = gcl_cons(gcv_nth(acc, i), v, with(r2, v))
    end do
  end function read_seq

  recursive function read_map(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, k, val
    type(gc_value), allocatable :: r2(:)

    v = gca_empty(roots)
    do
       r2 = with(roots, v)
       call skip_ignorables(text, pos, r2)
       if (pos > len(text)) then
          call fail("EOF while reading, expected '}'")
          return
       end if
       if (text(pos:pos) == "}") then
          pos = pos + 1
          return
       end if
       k = read_form(text, pos, r2)
       if (has_error) return
       call skip_ignorables(text, pos, r2)
       if (pos > len(text)) then
          call fail("map literal has an odd number of forms")
          return
       end if
       if (text(pos:pos) == "}") then
          call fail("map literal has an odd number of forms")
          return
       end if
       val = read_form(text, pos, with(r2, k))
       if (has_error) return
       v = gca_assoc(v, k, val, with(with(r2, k), val))
    end do
  end function read_map

  function read_string(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character(len=:), allocatable :: acc
    character :: c

    v = gc_nil()
    pos = pos + 1 ! consume the opening quote
    acc = ""
    do
       if (pos > len(text)) then
          call fail("EOF while reading a string")
          return
       end if
       c = text(pos:pos)
       if (c == '"') then
          pos = pos + 1
          exit
       end if
       if (c == achar(92)) then
          pos = pos + 1
          if (pos > len(text)) then
             call fail("EOF in a string escape")
             return
          end if
          select case (text(pos:pos))
          case ("n"); acc = acc // achar(10)
          case ("t"); acc = acc // achar(9)
          case ("r"); acc = acc // achar(13)
          case ('"'); acc = acc // '"'
          case default; acc = acc // text(pos:pos)
          end select
       else
          acc = acc // c
       end if
       pos = pos + 1
    end do
    v = gc_str(acc, roots)
  end function read_string

  ! A backslash takes the very next character unconditionally, then
  ! any word characters after it -- so \( and \" read, and the named
  ! forms (\newline, \space) stay one token.
  function read_char(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: start
    character(len=:), allocatable :: name

    v = gc_nil()
    start = pos
    pos = pos + 2
    if (start + 1 > len(text)) then
       call fail("EOF after a backslash")
       return
    end if
    do while (pos <= len(text))
       if (is_space(text(pos:pos)) .or. is_delim(text(pos:pos))) exit
       pos = pos + 1
    end do
    name = text(start + 1:pos - 1)
    select case (name)
    case ("newline");   v = gc_char(achar(10))
    case ("space");     v = gc_char(" ")
    case ("tab");       v = gc_char(achar(9))
    case ("return");    v = gc_char(achar(13))
    case ("backspace"); v = gc_char(achar(8))
    case ("formfeed");  v = gc_char(achar(12))
    case default
       if (len(name) == 1) then
          v = gc_char(name(1:1))
       else
          call fail("unsupported character literal: " // achar(92) // name)
       end if
    end select
  end function read_char

  function read_atom(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: start
    integer(gc_ip) :: ival
    logical :: iok, iclaim
    logical :: rok, rclaim
    type(gc_value) :: rval
    character(len=:), allocatable :: tok

    start = pos
    do while (pos <= len(text))
       if (is_space(text(pos:pos)) .or. is_delim(text(pos:pos))) exit
       pos = pos + 1
    end do
    tok = text(start:pos - 1)

    ! A token can only be empty if pos did not move, which means
    ! the character here is one read_form has no case for -- ^ and
    ! # today. Without this the reader spins forever instead of
    ! failing: a hang is a far worse failure than an error, and it
    ! is what loading real core.clj (which opens with ^{...})
    ! actually did.
    if (len(tok) == 0) then
       call fail("reader: no dispatch for '" // text(pos:pos) // "'")
       v = gc_nil()
       return
    end if

    if (tok == "nil") then
       v = gc_nil()
    else if (tok == "true") then
       v = gc_bool(.true.)
    else if (tok == "false") then
       v = gc_bool(.false.)
    else if (starts_numeric(tok)) then
       ! A digit-initial token is a NUMBER or an error -- never a
       ! name. LispReader.read hands it to readNumber and there is no
       ! path from there back to interpretToken, so `08` and `1e`
       ! raise rather than interning.
       rok = .false.
       rclaim = .false.
       call parse_int(tok, ival, iok, iclaim)
       if (.not. iclaim) call parse_ratio(tok, rval, rok, rclaim)
       if (iok) then
          v = gc_int(ival)
       else if (.not. iclaim .and. rok) then
          v = rval
       else if (.not. iclaim .and. .not. rclaim .and. looks_real(tok)) then
          v = gc_real(to_real(tok))
       else if (suffixed_number(tok, v, roots)) then
          continue
       else
          call fail("Invalid number: " // tok)
          v = gc_nil()
       end if
    else if (len(tok) > 1 .and. tok(1:1) == ":") then
       v = gc_key(tok(2:), roots)
    else
       v = gc_sym(tok, roots)
    end if
  end function read_atom

  ! ---- number recognition ----
  !
  ! Clojure's reader decides this with three regexes -- LispReader.java
  ! lines 70-74 at 71b4623d, the commit the vendored core.clj comes
  ! from:
  !
  !   intPat   ([-+]?)(?:(0)|([1-9][0-9]*)|0[xX]([0-9A-Fa-f]+)
  !              |0([0-7]+)|([1-9][0-9]?)[rR]([0-9A-Za-z]+)|0[0-9]+)(N)?
  !   floatPat ([-+]?[0-9]+(\.[0-9]*)?([eE][-+]?[0-9]+)?)(M)?
  !   ratioPat ([-+]?[0-9]+)/([0-9]+)
  !
  ! and matchNumber tries them IN THAT ORDER, so a token that matches
  ! intPat never reaches floatPat. Three consequences worth stating,
  ! because clotran got all three wrong by treating "all digits" as
  ! the whole story:
  !
  !   077   is 63, not 77   -- a leading zero means octal
  !   .5    is a SYMBOL     -- floatPat needs a digit BEFORE the dot
  !   08    is an ERROR     -- it matches intPat's last alternative,
  !                            which captures nothing, and Clojure
  !                            raises "Invalid number" rather than
  !                            falling through to read it as 8.0
  !
  ! And the reason the third one is an error rather than a symbol is
  ! structural: LispReader.read (line 278, and 294 for a leading sign)
  ! sends EVERY digit-initial token to readNumber, which throws when
  ! none of the three patterns match. There is no path back to
  ! interpretToken, so a token starting with a digit is a number or
  ! it is an error -- it is never a name. `1e` is the case that
  ! caught this: it matches no pattern, and Clojure raises rather
  ! than interning it.
  !
  ! Not implemented: the `N` (BigInt) and `M` (BigDecimal) suffixes and
  ! ratios, all of which need a numeric tower clotran does not have.
  ! They stay unreadable rather than being silently truncated into a
  ! fixed-width answer -- see DEVIATIONS.

  ! A number Clojure reads happily and clotran has no TYPE for: the
  ! `N` and `M` suffixes (`42N`, `1.5M`). Ratios USED to be here and
  ! are not any more -- there is a GCT_RATIO now, so `2/3` reads as
  ! the number it is.
  !
  ! These must not raise. The digit-initial rule above says such a token
  ! is a number or an error, and that is right ONLY where clotran can
  ! read every number Clojure can -- which it cannot. Raising instead
  ! costs far more than it explains: clotran's load aborts the whole
  ! file on a reader error (DEVIATIONS 1), so one `2/3` deep in a file
  ! takes every form after it down with it. Twelve of Clojure's 67 test
  ! namespaces contain a ratio literal; making them errors turned 766
  ! passing assertions into 223, and `control.clj` alone lost 153.
  !
  ! So they fall back to what they were before the number patterns went
  ! in: an ordinary symbol, which resolves to nothing and fails at USE
  ! rather than at read. That is still wrong -- `(+ 1 2/3)` says
  ! "unable to resolve symbol" where Clojure says 5/3 -- but it is
  ! wrong in one form instead of wrong in every form after it.
  !
  ! Both better fixes are real work rather than a reader tweak: a Ratio
  ! type and a numeric tower (DEVIATIONS 26), or per-form reader
  ! recovery so that one bad form does not abort a load.
  ! The N and M SUFFIXES, on a token that is otherwise a number.
  ! Clojure reads 1N as a BigInt and 1M as a BigDecimal; clotran
  ! has neither, and used to read both as SYMBOLS -- so (cond 0M
  ! :a true :b) was "unable to resolve symbol" rather than :a.
  !
  ! Each suffix drops to the nearest thing clotran does have, and
  ! the choice is made by what `=` then says, not by what looks
  ! closest:
  !
  !   1N -> an INTEGER, because (= 1N 1) is true in Clojure and
  !         stays true here.
  !   1M -> a DOUBLE, because (= 1M 1) is FALSE in Clojure -- a
  !         BigDecimal is its own equality category -- and
  !         (= 1.0 1) is false here for the same reason. Reading
  !         45M as the integer 45 would have made it true.
  !
  ! What is lost is arbitrary precision and the type: 1N is not a
  ! BigInt, 1M is not exact decimal, and both print without their
  ! suffix. DEVIATIONS.md 30.
  function suffixed_number(s, val, roots) result(yes)
    character(len=*), intent(in) :: s
    type(gc_value), intent(out) :: val
    type(gc_value), intent(in) :: roots(:)
    logical :: yes, iok, iclaim
    integer :: n, start
    integer(gc_ip) :: iv
    yes = .false.
    val = gc_nil()
    n = len(s)
    if (n == 0) return
    start = 1
    if (s(1:1) == "-" .or. s(1:1) == "+") start = 2
    if (start > n) return
    if (n <= start) return
    if (s(n:n) == "N") then
       call parse_int(s(1:n - 1), iv, iok, iclaim)
       if (iok) then
          val = gc_int(iv)
          yes = .true.
       end if
    else if (s(n:n) == "M") then
       if (looks_real(s(1:n - 1))) then
          val = gc_real(to_real(s(1:n - 1)))
          yes = .true.
       end if
    end if
    if (.false.) val = gc_sym(s, roots)
  end function suffixed_number

  ! ratioPat: ([-+]?[0-9]+)/([0-9]+). A denominator of zero is an
  ! error, the same as (/ 1 0) -- Clojure raises rather than reading
  ! it, and gc_ratio would answer nil.
  subroutine parse_ratio(s, val, ok, claim)
    character(len=*), intent(in) :: s
    type(gc_value), intent(out) :: val
    logical, intent(out) :: ok, claim
    integer :: n, start, k, slash
    integer(gc_ip) :: num, den
    logical :: nok, dok
    logical :: neg
    ok = .false.
    claim = .false.
    val = gc_nil()
    n = len(s)
    if (n == 0) return
    start = 1
    neg = .false.
    if (s(1:1) == "-" .or. s(1:1) == "+") then
       neg = (s(1:1) == "-")
       start = 2
    end if
    if (start > n) return
    slash = 0
    do k = start, n
       if (s(k:k) == "/") then
          slash = k
          exit
       end if
    end do
    if (slash <= start .or. slash >= n) return
    if (.not. all_decimal(s(start:slash - 1))) return
    if (.not. all_decimal(s(slash + 1:n))) return
    claim = .true.
    call digits_radix(s(start:slash - 1), 10, num, nok)
    call digits_radix(s(slash + 1:n), 10, den, dok)
    if (.not. nok .or. .not. dok .or. den == 0) return
    if (neg) num = -num
    val = gc_ratio(num, den)
    ok = .true.
  end subroutine parse_ratio

  ! What LispReader.read tests before calling readNumber: a digit, or
  ! a sign with a digit right after it (lines 278 and 294). Every such
  ! token is a number or an error.
  pure function starts_numeric(s) result(yes)
    character(len=*), intent(in) :: s
    logical :: yes
    integer :: i
    yes = .false.
    if (len(s) == 0) return
    i = 1
    if (s(1:1) == "-" .or. s(1:1) == "+") i = 2
    if (i > len(s)) return
    yes = (s(i:i) >= "0" .and. s(i:i) <= "9")
  end function starts_numeric

  ! Digits of `s` in `radix`, most significant first. ok is false for
  ! an empty string or any character that is not a digit of that radix
  ! -- which is how the callers tell `0xZ` from `0x1F`.
  pure subroutine digits_radix(s, radix, val, ok)
    character(len=*), intent(in) :: s
    integer, intent(in) :: radix
    integer(gc_ip), intent(out) :: val
    logical, intent(out) :: ok
    integer :: i, d
    character :: c
    ok = .false.
    val = 0
    if (len(s) == 0) return
    do i = 1, len(s)
       c = s(i:i)
       if (c >= "0" .and. c <= "9") then
          d = iachar(c) - iachar("0")
       else if (c >= "a" .and. c <= "z") then
          d = iachar(c) - iachar("a") + 10
       else if (c >= "A" .and. c <= "Z") then
          d = iachar(c) - iachar("A") + 10
       else
          return
       end if
       if (d >= radix) return
       val = val * radix + d
    end do
    ok = .true.
  end subroutine digits_radix

  pure function all_decimal(s) result(yes)
    character(len=*), intent(in) :: s
    logical :: yes
    integer :: i
    yes = .false.
    if (len(s) == 0) return
    do i = 1, len(s)
       if (s(i:i) < "0" .or. s(i:i) > "9") return
    end do
    yes = .true.
  end function all_decimal

  ! An integer literal in any of Clojure's four radix spellings.
  !
  ! Two separate answers, because intPat's match is EXCLUSIVE: a token
  ! it matches never reaches floatPat, even when the match captures
  ! nothing and the number turns out to be invalid. `08` is the case
  ! that proves it -- intPat's last alternative, bare `0[0-9]+`,
  ! matches it, so Clojure raises rather than reading 8.0. Collapsing
  ! these two into one logical silently made `08` a double here.
  !
  !   ok    -- a valid integer, its value in `val`
  !   claim -- intPat matched the SHAPE, so the float reader must not
  !            be tried; ok false with claim true is "Invalid number"
  pure subroutine parse_int(s, val, ok, claim)
    character(len=*), intent(in) :: s
    integer(gc_ip), intent(out) :: val
    logical, intent(out) :: ok, claim
    integer :: n, start, rp, k
    integer(gc_ip) :: radix
    logical :: neg, dok
    ok = .false.
    claim = .false.
    val = 0
    n = len(s)
    if (n == 0) return
    start = 1
    neg = .false.
    if (s(1:1) == "-" .or. s(1:1) == "+") then
       neg = (s(1:1) == "-")
       start = 2
    end if
    if (start > n) return
    if (s(start:start) < "0" .or. s(start:start) > "9") return

    ! Zero on its own -- intPat's first alternative.
    if (start == n .and. s(start:start) == "0") then
       ok = .true.
       claim = .true.
       return
    end if

    ! 0x / 0X, hexadecimal. The `0x` prefix is the claim; whether the
    ! digits after it are hex decides only validity.
    if (s(start:start) == "0" .and. n > start) then
       if (s(start+1:start+1) == "x" .or. s(start+1:start+1) == "X") then
          claim = .true.
          if (n < start + 2) return
          call digits_radix(s(start+2:n), 16, val, dok)
          if (dok) then
             if (neg) val = -val
             ok = .true.
          end if
          return
       end if
    end if

    ! A leading zero on a run of DIGITS is octal -- and is claimed even
    ! when a digit is 8 or 9, which is exactly `08`. `0.5` and `0e3`
    ! are not that shape at all, so they are left to the float reader.
    if (s(start:start) == "0") then
       if (.not. all_decimal(s(start+1:n))) return
       claim = .true.
       call digits_radix(s(start+1:n), 8, val, dok)
       if (dok) then
          if (neg) val = -val
          ok = .true.
       end if
       return
    end if

    ! NNrDIGITS -- an explicit radix, 2 through 36.
    rp = 0
    do k = start, n
       if (s(k:k) == "r" .or. s(k:k) == "R") then
          rp = k
          exit
       end if
    end do
    if (rp > 0) then
       claim = .true.
       call digits_radix(s(start:rp - 1), 10, radix, dok)
       if (.not. dok .or. radix < 2 .or. radix > 36 .or. rp == n) return
       ! radix is 2..36, checked just above, so this narrowing is exact.
       call digits_radix(s(rp + 1:n), int(radix, kind=4), val, dok)
       if (dok) then
          if (neg) val = -val
          ok = .true.
       end if
       return
    end if

    ! Plain decimal. A dot or an exponent is not an integer and is not
    ! claimed, so `1.5` and `1e3` go on to the float reader.
    call digits_radix(s(start:n), 10, val, dok)
    if (dok) then
       if (neg) val = -val
       ok = .true.
       claim = .true.
    end if
  end subroutine parse_int

  ! floatPat, minus the M suffix: [-+]?[0-9]+(\.[0-9]*)?([eE][-+]?[0-9]+)?
  ! The leading run of digits is REQUIRED, which is what makes `.5` a
  ! symbol and `5.` a double.
  pure function looks_real(s) result(yes)
    character(len=*), intent(in) :: s
    logical :: yes
    integer :: i, n, ndig
    yes = .false.
    n = len(s)
    if (n == 0) return
    i = 1
    if (s(1:1) == "-" .or. s(1:1) == "+") i = 2
    ndig = 0
    do while (i <= n)
       if (s(i:i) < "0" .or. s(i:i) > "9") exit
       ndig = ndig + 1
       i = i + 1
    end do
    if (ndig == 0) return
    if (i <= n) then
       if (s(i:i) == ".") then
          i = i + 1
          do while (i <= n)
             if (s(i:i) < "0" .or. s(i:i) > "9") exit
             i = i + 1
          end do
       end if
    end if
    if (i <= n) then
       if (s(i:i) == "e" .or. s(i:i) == "E") then
          i = i + 1
          if (i <= n) then
             if (s(i:i) == "-" .or. s(i:i) == "+") i = i + 1
          end if
          ndig = 0
          do while (i <= n)
             if (s(i:i) < "0" .or. s(i:i) > "9") exit
             ndig = ndig + 1
             i = i + 1
          end do
          if (ndig == 0) return    ! `1e` -- an exponent with no digits
       end if
    end if
    yes = (i > n)
  end function looks_real

  function to_real(s) result(r)
    character(len=*), intent(in) :: s
    real(gc_dp) :: r
    integer :: ios
    read(s, *, iostat=ios) r
    if (ios /= 0) r = 0.0_gc_dp
  end function to_real

  function with(roots, v) result(out)
    type(gc_value), intent(in) :: roots(:), v
    type(gc_value), allocatable :: out(:)
    allocate(out(size(roots) + 1))
    out(1:size(roots)) = roots
    out(size(roots) + 1) = v
  end function with

end module LispReader
