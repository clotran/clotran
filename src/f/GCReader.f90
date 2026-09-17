! GCReader: text into the GC heap.
!
! The counterpart to GCPrinter.f90, and the last piece of the new data
! layer built standalone. Nothing uses it yet. See PLAN.md 3c-2/3d.
!
! Together the two give a ROUND TRIP -- read a form, print it, get the
! input back -- which tests the whole layer against real Clojure text
! rather than against structures built by hand in a test. A reader and
! a printer can only agree if the thing between them actually holds
! what it was given.
!
! Recursive descent straight over the character buffer, with no
! separate token array. LispReader.f90 has one because it records a
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
module GCReader
  use GC
  use GCList
  use GCVector
  use GCAssoc
  use Regex
  use, intrinsic :: ieee_arithmetic
  implicit none
  private

  character(len=:), allocatable :: last_error
  logical :: has_error = .false.

  public :: gcr_read, gcr_read_all, gcr_error, gcr_has_error

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
       call skip_space(text, pos)
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

  pure function is_delim(c) result(yes)
    character, intent(in) :: c
    logical :: yes
    yes = (c == "(" .or. c == ")" .or. c == "[" .or. c == "]" .or. &
           c == "{" .or. c == "}" .or. c == '"' .or. c == ";" .or. &
           c == "'" .or. c == "`" .or. c == "~" .or. c == "@" .or. c == "^")
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

  ! ---- forms ----

  recursive function read_form(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character :: c

    v = gc_nil()
    call skip_space(text, pos)
    if (pos > len(text)) then
       call fail("EOF while reading")
       return
    end if

    c = text(pos:pos)
    select case (c)
    case ("(")
       pos = pos + 1
       v = read_seq(text, pos, ")", .false., roots)
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
    if (gcl_is(form)) then
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
    type(gc_value) :: v, ignored
    character :: c

    v = gc_nil()
    if (pos + 1 > len(text)) then
       call fail("EOF after #")
       return
    end if
    c = text(pos + 1:pos + 1)
    select case (c)
    case ("_")
       ! #_ discards the NEXT FORM, not the next token -- so
       ! #_(a b c) skips the whole list.
       pos = pos + 2
       ignored = read_form(text, pos, roots)
       if (has_error) return
       v = read_form(text, pos, roots)
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
    else if (m%tag == GCT_SYM .or. m%tag == GCT_STR) then
       v = gca_empty(roots)
       call vs_set(base + 2, v)
       key = gc_key("tag", roots)
       call vs_set(base + 3, key)
       m = gca_assoc(vs_get(base + 2), vs_get(base + 3), vs_get(base + 1), roots)
       call vs_set(base + 1, m)
    else
       call fail("Metadata must be Symbol, Keyword, String or Map")
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
       call skip_space(text, pos)
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
       call skip_space(text, pos)
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
       call skip_space(text, pos)
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
    else if (looks_int(tok)) then
       v = gc_int(to_int(tok))
    else if (looks_real(tok)) then
       v = gc_real(to_real(tok))
    else if (len(tok) > 1 .and. tok(1:1) == ":") then
       v = gc_key(tok(2:), roots)
    else
       v = gc_sym(tok, roots)
    end if
  end function read_atom

  ! ---- number recognition ----

  pure function looks_int(s) result(yes)
    character(len=*), intent(in) :: s
    logical :: yes
    integer :: i, start
    yes = .false.
    if (len(s) == 0) return
    start = 1
    if (s(1:1) == "-" .or. s(1:1) == "+") start = 2
    if (start > len(s)) return
    do i = start, len(s)
       if (s(i:i) < "0" .or. s(i:i) > "9") return
    end do
    yes = .true.
  end function looks_int

  ! A '.' with digits on at least one side -- so 1.5, 1. and .5 read
  ! as reals but a bare '.' or a symbol like `foo.bar` does not.
  pure function looks_real(s) result(yes)
    character(len=*), intent(in) :: s
    logical :: yes
    integer :: i, start, dots, digits
    yes = .false.
    if (len(s) == 0) return
    start = 1
    if (s(1:1) == "-" .or. s(1:1) == "+") start = 2
    if (start > len(s)) return
    dots = 0
    digits = 0
    do i = start, len(s)
       if (s(i:i) == ".") then
          dots = dots + 1
       else if (s(i:i) >= "0" .and. s(i:i) <= "9") then
          digits = digits + 1
       else
          return
       end if
    end do
    yes = (dots == 1 .and. digits > 0)
  end function looks_real

  function to_int(s) result(n)
    character(len=*), intent(in) :: s
    integer :: n, ios
    read(s, *, iostat=ios) n
    if (ios /= 0) n = 0
  end function to_int

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

end module GCReader