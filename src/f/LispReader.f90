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
  use BigInt
  use BigDec
  use PersistentList
  use PersistentVector
  use Assoc
  use Regex
  use Printer, only: gcp_str
  use clotran_ieee
  use Threads, only: th_key, th_key_create, th_key_set, th_key_get
  use iso_c_binding, only: c_ptr, c_loc, c_f_pointer, c_associated
  implicit none
  private

  public :: gcr_read, gcr_read_all, gcr_error, gcr_has_error, gcr_error_class
  public :: gcr_begin_file, gcr_read_next, gcr_position, gcr_position_parts, POS_SHIFT
  public :: gcr_set_ns_resolver, gcr_set_tag_markers, gcr_set_read_cond, gcr_current_file, gcr_set_sq_expander, gcr_set_eval_reader
  public :: gcr_image_write, gcr_image_read, gcr_file_count, gcr_file_name

  ! ::x is resolved at READ time against the current namespace, and
  ! ::a/x against its aliases -- which the reader does not know. The
  ! evaluator installs the lookup; a resolver is what LispReader
  ! reaches through Compiler.currentNS and namespaceFor.
  abstract interface
     subroutine ns_resolver_i(alias, ns)
       character(len=*), intent(in) :: alias
       character(len=:), allocatable, intent(out) :: ns
     end subroutine ns_resolver_i
  end interface
  procedure(ns_resolver_i), pointer, save :: ns_resolver => null()

  ! `form is expanded at READ time, as SyntaxQuoteReader does; the
  ! expansion resolves names in the current namespace, which the reader
  ! does not know, so the evaluator installs it (Eval's sq_reader_hook).
  ! err is a message to fail with (of class cls), or "".
  abstract interface
     subroutine sq_expander_i(form, roots, out, err, cls)
       import :: gc_value
       type(gc_value), intent(in) :: form
       type(gc_value), intent(in) :: roots(:)
       type(gc_value), intent(out) :: out
       character(len=:), allocatable, intent(out) :: err, cls
     end subroutine sq_expander_i
  end interface
  procedure(sq_expander_i), pointer, save :: sq_expander => null()

  ! #=form, EvalReader: the evaluator's too. Asked first with `check`
  ! true, before the form is read -- refused while *read-eval* is false
  ! -- then with the form read, to answer its value.
  abstract interface
     subroutine eval_reader_i(check, form, roots, out, err, cls)
       import :: gc_value
       logical, intent(in) :: check
       type(gc_value), intent(in) :: form
       type(gc_value), intent(in) :: roots(:)
       type(gc_value), intent(out) :: out
       character(len=:), allocatable, intent(out) :: err, cls
     end subroutine eval_reader_i
  end interface
  procedure(eval_reader_i), pointer, save :: eval_reader => null()

  ! SOURCE POSITIONS. A list form records where it was read from:
  ! OBJ_CONS's i2 (free: i1 is the count) holds file-id * 2^26 + the
  ! 1-based character offset of its opening paren. The analyser copies
  ! it onto the node, and an error names it. Line and column are
  ! recovered from the offset by a binary search over line_starts,
  ! computed once per file by gcr_begin_file -- cheaper than counting
  ! newlines per form and simpler than threading a line counter
  ! through every read_* routine. Files are named once, in a small
  ! table; id 0 is "no file" (the REPL).
  ! 2^24: an offset up to 16M characters, a file id up to 127. 2^26 let
  ! the 32nd file overflow the packed integer.
  integer, parameter :: POS_SHIFT = 2**24
  integer, parameter :: MAX_FILES = 120
  ! One entry per file ever loaded, line index included: a position
  ! inside core.clj is asked about long after some other file became
  ! current, and must be answered against core.clj's own lines.
  type :: src_file
     character(len=512) :: name = ""
     integer, allocatable :: line_starts(:)
     logical :: read_cond = .false.   ! a .cljc: #? is read (Compiler.load)
  end type src_file
  type(src_file), save :: files(MAX_FILES)
  integer, save :: n_files = 0
  ! the suffix the last #(...) read gave its parameters: one counter for
  ! every thread, as RT.nextID is, so no two reads name them alike
  integer, save :: anon_seq = 0
  ! What a read in progress keeps: one per thread, found through rd_key
  ! (PLAN.md step 14b), made the first time its thread reads.
  type :: rd_state
     character(len=:), allocatable :: last_error
     ! the class clj's LispReader throws, when it is not RuntimeException:
     ! an IllegalArgumentException for a bad digit or metadata, a
     ! NumberFormatException for a bad number (gcr_error_class)
     character(len=:), allocatable :: last_class
     logical :: has_error = .false.
     integer :: cur_file = 0   ! the file being read; 0 is the REPL
     ! Reader conditionals. A #?(...) that selects nothing is another kind
     ! of space, like #_ (see skip_ignorables), and #?@ splices a
     ! collection into the enclosing one. Whoever called read_form --
     ! read_seq, read_map, the top level -- checks these two flags straight
     ! after the call and clears them. LispReader hands back the
     ! reader itself as its nothing-sentinel; a flag is the same signal
     ! without inventing a value for it.
     logical :: rc_nothing = .false., rc_splice = .false.
     ! True while reading a branch the conditional did not select: a
     ! tagged literal there is read past rather than resolved, which is
     ! what *suppress-read* does, so a :cljs branch may hold #js {}.
     logical :: suppress_read = .false.
     ! Whether #? may be read at all -- LispReader.checkConditionalAllowed.
     ! rc_file is the file's (a .cljc), rc_allow read-string's {:read-cond
     ! :allow}, and rc_features its :features, blank-separated.
     logical :: rc_file = .false., rc_allow = .false.
     character(len=:), allocatable :: rc_features
     ! the forms a #?@ left where one form was wanted (pending_push)
     integer :: n_pending = 0
     type(gc_root) :: pending
     ! When on, #tag form READS as a marker map instead of failing --
     ! {:clotran/tagged-literal true :tag t :form f}, the same shape
     ! `tagged-literal` builds. The reader cannot apply a data reader
     ! itself (it would have to call the evaluator, and Eval uses this
     ! module, not the other way round), so the caller that turned this
     ! on resolves the markers afterwards. Off for ordinary source, so
     ! an unknown tag in a file is still a reader error there.
     logical :: tag_markers = .true.   ! #tag form is a marker, resolved before analysis (clotran.reader)
     ! and each parameter's own number, given when the body first uses
     ! it, as FnReader's garg does (0 until then; anon_rest for %&)
     integer, allocatable :: anon_ids(:)
     integer :: anon_rest = 0, anon_max = 0
     ! inside a #(...)'s body: another is refused (FnReader)
     logical :: in_anon = .false.
     ! the map read next is a #:ns map's: its odd count says so
     logical :: ns_map = .false.
  end type rd_state
  type(th_key), save :: rd_key
  logical, save :: rd_key_made = .false.

contains


  ! This thread's reader state, made on its first read.
  ! ponytail: one per thread that ever reads, never freed -- a few dozen
  ! bytes; a pthread key destructor frees them if threads ever churn.
  function rd_self() result(r)
    type(rd_state), pointer :: r
    type(c_ptr) :: p
    logical :: ok
    ! the first read is on the main thread, before any task exists
    if (.not. rd_key_made) then
       if (.not. th_key_create(rd_key)) error stop "clotran: no thread key for the reader"
       rd_key_made = .true.
    end if
    p = th_key_get(rd_key)
    if (c_associated(p)) then
       call c_f_pointer(p, r)
    else
       allocate(r)
       r%last_error = ""
       ok = th_key_set(rd_key, c_loc(r))
    end if
  end function rd_self

  function gcr_has_error() result(yes)
    type(rd_state), pointer :: rdx
    logical :: yes
    rdx => rd_self()
    yes = rdx%has_error
  end function gcr_has_error

  subroutine gcr_error(s)
    type(rd_state), pointer :: rdx
    character(len=:), allocatable, intent(out) :: s
    rdx => rd_self()
    s = ""
    if (allocated(rdx%last_error)) s = rdx%last_error
  end subroutine gcr_error

  subroutine fail(msg, cls)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: msg
    character(len=*), intent(in), optional :: cls
    rdx => rd_self()
    ! the FIRST error stands: one after it is its cascade -- #_\space6
    ! read on and blamed the ] it never reached (scripts/fuzz-read)
    if (rdx%has_error) return
    rdx%has_error = .true.
    rdx%last_error = msg
    rdx%last_class = ""
    if (present(cls)) rdx%last_class = cls
  end subroutine fail

  ! The last error's class, or "" for clotran.host.runtime_exception
  subroutine gcr_error_class(s)
    type(rd_state), pointer :: rdx
    character(len=:), allocatable, intent(out) :: s
    rdx => rd_self()
    s = ""
    if (allocated(rdx%last_class)) s = rdx%last_class
  end subroutine gcr_error_class

  ! Names a file and indexes its lines; answers its id, which the
  ! loader hands back to every gcr_read_next for that file. It must:
  ! reading is interleaved with evaluation, and a (require ...) in the
  ! middle of a file loads other files, each of which becomes the
  ! current one -- so the next form of the OUTER file would otherwise
  ! be stamped with the last inner file's id.
  ! --- the image: the file table, so a position inside core.clj is still
  ! a line and a column after a restart -----------------------------------
  subroutine gcr_image_write(u)
    integer, intent(in) :: u
    integer :: i
    write(u) n_files, anon_seq
    do i = 1, n_files
       write(u) files(i)%name
       if (allocated(files(i)%line_starts)) then
          write(u) size(files(i)%line_starts)
          write(u) files(i)%line_starts
       else
          write(u) -1
       end if
    end do
  end subroutine gcr_image_write

  subroutine gcr_image_read(u)
    integer, intent(in) :: u
    integer :: i, k
    read(u) n_files, anon_seq
    do i = 1, n_files
       read(u) files(i)%name
       read(u) k
       if (allocated(files(i)%line_starts)) deallocate(files(i)%line_starts)
       if (k >= 0) then
          allocate(files(i)%line_starts(k))
          read(u) files(i)%line_starts
       end if
    end do
  end subroutine gcr_image_read

  ! The files read so far, by classpath name, for the image's staleness check
  function gcr_file_count() result(n)
    integer :: n
    n = n_files
  end function gcr_file_count

  subroutine gcr_file_name(i, name)
    integer, intent(in) :: i
    character(len=:), allocatable, intent(out) :: name
    name = ""
    if (i >= 1 .and. i <= n_files) name = trim(files(i)%name)
  end subroutine gcr_file_name

  function gcr_begin_file(text, name) result(fid)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text, name
    integer :: fid
    integer :: i, n, k
    character(len=:), allocatable :: rel
    rdx => rd_self()
    rdx%cur_file = 0
    ! a file of the vendored tree is known by its CLASSPATH name, as the
    ! clj knows it: (:file (meta #'map)) is "clojure/core.clj" there, and
    ! a stack frame reads (clojure/core.clj:270:13)
    rel = name
    k = index(name, "src/clj/", back=.true.)
    if (k > 0) rel = name(k + 8:)
    call gc_state_lock()
    do i = 1, n_files
       if (trim(files(i)%name) == rel) rdx%cur_file = i
    end do
    if (rdx%cur_file == 0 .and. n_files < MAX_FILES) then
       n_files = n_files + 1
       files(n_files)%name = rel
       rdx%cur_file = n_files
    end if
    rdx%rc_file = len(rel) >= 5
    if (rdx%rc_file) rdx%rc_file = rel(len(rel) - 4:) == ".cljc"
    if (rdx%cur_file > 0) files(rdx%cur_file)%read_cond = rdx%rc_file
    call gc_state_unlock()
    fid = rdx%cur_file
    if (rdx%cur_file == 0) return
    n = 1
    do i = 1, len(text)
       if (text(i:i) == achar(10)) n = n + 1
    end do
    if (allocated(files(rdx%cur_file)%line_starts)) deallocate(files(rdx%cur_file)%line_starts)
    allocate(files(rdx%cur_file)%line_starts(n))
    files(rdx%cur_file)%line_starts(1) = 1
    k = 1
    do i = 1, len(text)
       if (text(i:i) == achar(10)) then
          k = k + 1
          files(rdx%cur_file)%line_starts(k) = i + 1
       end if
    end do
  end function gcr_begin_file

  ! The next form after pos, advancing pos past it; eof when only
  ! whitespace and comments remain. What Compiler.load does per form:
  ! read, then evaluate, then read again -- so a form can depend on
  ! what the one before it changed (DEVIATIONS 1, closed).
  function gcr_read_next(text, pos, roots, eof, fid) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    logical, intent(out) :: eof
    integer, intent(in) :: fid
    type(gc_value) :: v
    rdx => rd_self()
    rdx%cur_file = fid
    if (fid > 0) rdx%rc_file = files(fid)%read_cond
    rdx%has_error = .false.
    rdx%in_anon = .false.
    rdx%last_error = ""
    eof = .false.
    v = gc_nil()
    call pending_clear()
    do
       call skip_ignorables(text, pos, roots)
       if (rdx%has_error) return
       if (rdx%n_pending > 0) then
          v = pending_pop()
          return
       end if
       if (pos > len(text)) then
          eof = .true.
          return
       end if
       v = read_form1(text, pos, roots)
       call pending_clear()
       if (rdx%has_error) return
       if (rdx%rc_splice) then
          rdx%rc_splice = .false.
          call fail("Reader conditional splicing not allowed at the top level.")
          return
       end if
       if (.not. rdx%rc_nothing) return
       rdx%rc_nothing = .false.
    end do
  end function gcr_read_next

  ! "file:line:col" for a packed position, or "line:col" with no file.
  subroutine gcr_position(packed, s)
    integer, intent(in) :: packed
    character(len=:), allocatable, intent(out) :: s
    character(len=:), allocatable :: fname
    character(len=24) :: lb, cb
    integer :: line, col
    call gcr_position_parts(packed, fname, line, col)
    write(lb, '(I0)') line
    write(cb, '(I0)') col
    if (len(fname) > 0) then
       s = fname // ":" // trim(lb) // ":" // trim(cb)
    else
       s = trim(lb) // ":" // trim(cb)
    end if
  end subroutine gcr_position

  ! The parts: file name (empty when none), line and column.
  subroutine gcr_position_parts(packed, fname, line, col)
    integer, intent(in) :: packed
    character(len=:), allocatable, intent(out) :: fname
    integer, intent(out) :: line, col
    integer :: fid, off, lo, hi, mid
    fid = packed / POS_SHIFT
    off = mod(packed, POS_SHIFT)
    fname = ""
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
    if (fid >= 1 .and. fid <= n_files) fname = trim(files(fid)%name)
  end subroutine gcr_position_parts

  ! Reads ONE form from text. Trailing text is ignored, which is what
  ! a REPL line wants; a whole-file reader would loop on the position.
  ! A REPL form belongs to no file: an error in it reports line:col,
  ! not the file that happened to load last.
  function gcr_read(text, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: pos
    rdx => rd_self()
    rdx%has_error = .false.
    rdx%in_anon = .false.
    rdx%last_error = ""
    rdx%cur_file = 0
    rdx%rc_file = .false.
    pos = 1
    call pending_clear()
    do
       call skip_ignorables(text, pos, roots)
       if (rdx%has_error) return
       if (rdx%n_pending > 0) then
          v = pending_pop()
          return
       end if
       v = read_form1(text, pos, roots)
       call pending_clear()
       if (rdx%has_error) return
       if (rdx%rc_splice) then
          rdx%rc_splice = .false.
          call fail("Reader conditional splicing not allowed at the top level.")
          return
       end if
       if (.not. rdx%rc_nothing) return
       ! nothing selected: the next form is the one, as read-string does
       rdx%rc_nothing = .false.
       call skip_ignorables(text, pos, roots)
       if (pos > len(text)) then
          call fail("EOF while reading")
          return
       end if
    end do
  end function gcr_read

  ! Every form in the text, as a vector. What a file needs, as
  ! opposed to gcr_read's single form: the position carries across
  ! calls instead of restarting, so `(def a 1) (def b 2)` is two forms
  ! rather than one form and some ignored text.
  function gcr_read_all(text, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, form
    integer :: pos, base

    rdx => rd_self()
    rdx%has_error = .false.
    rdx%in_anon = .false.
    rdx%last_error = ""
    pos = 1
    base = vs_enter(1)
    v = gcv_empty(roots)
    call vs_set(base + 1, v)
    call pending_clear()
    do
       call skip_ignorables(text, pos, [vs_get(base + 1)])
       if (rdx%has_error) exit
       if (rdx%n_pending > 0) then
          call vs_set(base + 1, gcv_conj(vs_get(base + 1), pending_pop(), roots))
          cycle
       end if
       if (pos > len(text)) exit
       form = read_form1(text, pos, [vs_get(base + 1)])
       call pending_clear()
       if (rdx%has_error) exit
       if (rdx%rc_splice) then
          rdx%rc_splice = .false.
          call fail("Reader conditional splicing not allowed at the top level.")
          exit
       end if
       if (rdx%rc_nothing) then
          rdx%rc_nothing = .false.
          cycle
       end if
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
  ! (DEVIATIONS.md 1). The backslash is one: x\u0041 is x and \A,
  ! 31.95\M a number and \M (scripts/fuzz-read).
  pure function is_delim(c) result(yes)
    character, intent(in) :: c
    logical :: yes
    yes = (c == "(" .or. c == ")" .or. c == "[" .or. c == "]" .or. &
           c == "{" .or. c == "}" .or. c == '"' .or. c == ";" .or. &
           c == "`" .or. c == "~" .or. c == "@" .or. c == "^" .or. c == "\")
  end function is_delim

  ! LispReader.isMacro: the characters with a reader of their own
  pure function is_macro(c) result(yes)
    character, intent(in) :: c
    logical :: yes
    yes = index('";''@^`~()[]{}%#', c) > 0 .or. c == achar(92)
  end function is_macro

  logical function rd_self_in_anon()
    type(rd_state), pointer :: r
    r => rd_self()
    rd_self_in_anon = r%in_anon
  end function rd_self_in_anon

  ! intPat's radix shape, NNrDIGITS -- one or two digits, the first not
  ! 0 -- with NN outside 2..36: "Radix out of range", as the BigInteger
  ! matchNumber makes it from says
  pure logical function radix_out_of_range(t) result(yes)
    character(len=*), intent(in) :: t
    integer :: s0, rp, r
    yes = .false.
    s0 = 1
    if (len(t) > 0) then
       if (t(1:1) == "-" .or. t(1:1) == "+") s0 = 2
    end if
    rp = scan(t, "rR")
    if (rp < s0 + 1 .or. rp > s0 + 2 .or. rp == len(t)) return
    if (verify(t(s0:rp-1), "0123456789") /= 0 .or. t(s0:s0) == "0") return
    if (verify(t(rp+1:), "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") /= 0) return
    read(t(s0:rp-1), *) r
    yes = r < 2 .or. r > 36
  end function radix_out_of_range

  ! How many bytes the UTF-8 character led by c takes
  pure function u8_len(c) result(n)
    character, intent(in) :: c
    integer :: n
    select case (iachar(c))
    case (240:247); n = 4
    case (224:239); n = 3
    case (192:223); n = 2
    case default; n = 1
    end select
  end function u8_len

  ! Character.digit for ASCII: c's value in base, or -1
  pure function digit_of(c, base) result(d)
    character, intent(in) :: c
    integer, intent(in) :: base
    integer :: d
    select case (c)
    case ("0":"9"); d = iachar(c) - iachar("0")
    case ("a":"z"); d = iachar(c) - iachar("a") + 10
    case ("A":"Z"); d = iachar(c) - iachar("A") + 10
    case default; d = -1
    end select
    if (d >= base) d = -1
  end function digit_of

  ! LispReader.readUnicodeChar over the text: the digit at pos and up to
  ! length - 1 more, stopping at whitespace, a macro character or the
  ! end; pos is left on the last digit taken. exact: fewer is an error.
  function read_code_unit(text, pos, base, length, exact) result(uc)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    integer, intent(in) :: base, length
    logical, intent(in) :: exact
    integer :: uc, i, d
    character(len=16) :: b1, b2
    uc = digit_of(text(pos:pos), base)
    if (uc < 0) then
       call fail("Invalid digit: " // text(pos:min(len(text), pos + u8_len(text(pos:pos)) - 1)), "clotran.host.illegal_argument_exception")
       return
    end if
    i = 1
    do while (i < length)
       if (pos + 1 > len(text)) exit
       if (is_space(text(pos+1:pos+1)) .or. is_macro(text(pos+1:pos+1))) exit
       d = digit_of(text(pos+1:pos+1), base)
       if (d < 0) then
          call fail("Invalid digit: " // text(pos+1:min(len(text), pos + u8_len(text(pos+1:pos+1)))), "clotran.host.illegal_argument_exception")
          return
       end if
       uc = uc * base + d
       pos = pos + 1
       i = i + 1
    end do
    if (i /= length .and. exact) then
       write(b1, '(I0)') i
       write(b2, '(I0)') length
       call fail("Invalid character length: " // trim(b1) // ", should be: " // trim(b2), &
            "clotran.host.illegal_argument_exception")
    end if
  end function read_code_unit

  subroutine skip_space(text, pos)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    do while (pos <= len(text))
       ! ; and #! are comments to the end of the line (CommentReader)
       if (text(pos:pos) == ";" .or. text(pos:min(pos + 1, len(text))) == "#!") then
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
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: ignored

    rdx => rd_self()
    do
       call skip_space(text, pos)
       if (pos + 1 > len(text)) return
       if (text(pos:pos + 1) /= "#_") return
       pos = pos + 2
       ignored = read_form(text, pos, roots)
       if (rdx%has_error) return
    end do
  end subroutine skip_ignorables

  ! ---- forms ----

  ! The next form, as LispReader.read hands it over: a form a splice left
  ! pending first, then the text's, a conditional that chose nothing
  ! skipped and a splice's forms queued. done when the text reaches
  ! closer instead; achar(0) is none, and an unmatched closer is then
  ! read_form1's error.
  recursive function read_next(text, pos, closer, roots, done) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    character, intent(in) :: closer
    type(gc_value), intent(in) :: roots(:)
    logical, intent(out) :: done
    type(gc_value) :: v
    rdx => rd_self()
    done = .false.
    v = gc_nil()
    do
       if (rdx%n_pending > 0) then
          v = pending_pop()
          return
       end if
       call skip_ignorables(text, pos, roots)
       if (rdx%has_error) return
       if (rdx%n_pending > 0) cycle
       if (pos > len(text)) then
          call fail("EOF while reading")
          return
       end if
       if (text(pos:pos) == closer) then
          pos = pos + 1
          done = .true.
          return
       end if
       v = read_form1(text, pos, roots)
       if (rdx%has_error) return
       if (rdx%rc_nothing) then
          rdx%rc_nothing = .false.
       else if (rdx%rc_splice) then
          rdx%rc_splice = .false.
          call pending_push(v, roots)
       else
          return
       end if
    end do
  end function read_next

  ! One form where exactly one is wanted -- after ', ^, @, #' and the
  ! rest, and what #_ discards.
  recursive function read_form(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    logical :: done
    v = read_next(text, pos, achar(0), roots, done)
  end function read_form

  ! The forms a #?@ left over where one form was wanted, for whatever
  ! reads next (LispReader's pendingForms): a list in a global root,
  ! emptied at each top-level read.
  subroutine pending_push(coll, roots)
    type(rd_state), pointer :: rdx
    type(gc_value), intent(in) :: coll
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: p
    integer :: base, i
    rdx => rd_self()
    base = vs_enter(2)
    call vs_set(base + 1, splice_into(gcv_empty([roots, coll]), coll, [roots, coll]))
    p = gc_nil()
    if (rdx%n_pending > 0) p = gc_root_get(rdx%pending)
    call vs_set(base + 2, p)
    do i = gcv_count(vs_get(base + 1)) - 1, 0, -1
       p = gcl_cons(gcv_nth(vs_get(base + 1), i), vs_get(base + 2), [roots, vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, p)
    end do
    call gc_global_keep(rdx%pending, vs_get(base + 2))
    rdx%n_pending = rdx%n_pending + gcv_count(vs_get(base + 1))
    call vs_leave(base)
  end subroutine pending_push

  function pending_pop() result(v)
    type(rd_state), pointer :: rdx
    type(gc_value) :: v, p
    integer :: base
    rdx => rd_self()
    p = gc_root_get(rdx%pending)
    base = vs_enter(1)
    call vs_set(base + 1, gcl_first(p))
    call gc_global_keep(rdx%pending, gcl_rest(p, [vs_get(base + 1)]))
    rdx%n_pending = rdx%n_pending - 1
    v = vs_get(base + 1)
    call vs_leave(base)
  end function pending_pop

  subroutine pending_clear()
    type(rd_state), pointer :: rdx
    rdx => rd_self()
    if (rdx%n_pending == 0) return
    rdx%n_pending = 0
    call gc_global_keep(rdx%pending, gc_nil())
  end subroutine pending_clear

  recursive function read_form1(text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character :: c

    rdx => rd_self()
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
         if (.not. rdx%has_error) then
            if (gcl_is(v)) then
               if (gcl_count(v) > 0) call gc_set_i2(v, rdx%cur_file * POS_SHIFT + start)
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
       call fail("Unmatched delimiter: " // c)
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
       ! expanded by the evaluator's expander; a reader with none (the
       ! reader's own tests) leaves the form (quasiquote x)
       if (associated(sq_expander)) then
          v = read_syntax_quote(text, pos, roots)
       else
          v = wrap("quasiquote", text, pos, roots)
       end if
    case ("@")
       pos = pos + 1
       ! qualified, as LispReader reads them: @x is (clojure.core/deref x)
       v = wrap("clojure.core/deref", text, pos, roots)
    case ("~")
       pos = pos + 1
       if (pos <= len(text)) then
          if (text(pos:pos) == "@") then
             pos = pos + 1
             v = wrap("clojure.core/unquote-splicing", text, pos, roots)
             return
          end if
       end if
       v = wrap("clojure.core/unquote", text, pos, roots)
    case default
       if (c == "%" .and. rdx%in_anon) then
          v = read_arg(text, pos, roots)
       else if (c == achar(92)) then
          v = read_char(text, pos, roots)
       else
          v = read_atom(text, pos, roots)
       end if
    end select
  end function read_form1

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
    character(len=:), allocatable :: rerr

    v = gc_nil()
    pos = pos + 1
    start = pos
    do
       if (pos > len(text)) then
          call fail("EOF while reading regex")
          return
       end if
       if (text(pos:pos) == achar(34)) exit
       if (text(pos:pos) == achar(92)) pos = pos + 1
       pos = pos + 1
    end do
    handle = regex_compile(text(start:pos - 1), rerr, grow=.true.)
    if (handle == 0) then
       call fail("regex: " // rerr, "clotran.host.pattern_syntax_exception")
       return
    end if
    src = gc_str(text(start:pos - 1), roots)
    ! the CALLER'S roots too: they hold the form being read around this
    ! literal, and with only src rooted a collection here freed it --
    ! (def p #"a") read as nothing, silently, when a collection landed
    ! on this allocation. The oracle's one-in-a-hundred flake (PLAN
    ! step 20), found with CLOTRAN_GC_EVERY=1.
    v = gc_obj(OBJ_REGEX, [src], [roots, src])
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
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, body, params, sym
    integer :: base, maxn, i
    logical :: has_rest
    character(len=16) :: nm

    rdx => rd_self()
    v = gc_nil()
    if (rdx%in_anon) then
       call fail("Nested #()s are not allowed", "clotran.host.illegal_state_exception")
       return
    end if
    base = vs_enter(4)
    ! ARG_ENV: each %n read in the body is its parameter's name at once
    ! (read_arg), numbered at its first use, as FnReader's ArgReader does
    if (allocated(rdx%anon_ids)) deallocate(rdx%anon_ids)
    allocate(rdx%anon_ids(8))
    rdx%anon_ids = 0
    rdx%anon_rest = 0
    rdx%anon_max = 0
    rdx%in_anon = .true.
    body = read_seq(text, pos, ")", .false., roots)
    rdx%in_anon = .false.
    if (rdx%has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 1, body)
    maxn = rdx%anon_max
    has_rest = rdx%anon_rest /= 0

    ! `roots` in every allocation -- the caller's values are plain
    ! locals reachable only through it, and reading #(...) inside a
    ! larger form must not collect the form being built around it.
    ! Same defect read_set had.
    ! Each parameter is a gensym as Clojure's are (p1__1#), numbered as
    ! FnReader numbers them: when the body first uses it, in reading
    ! order, and one the body skips after the body -- so it cannot shadow
    ! a `p1` of the program's own (every-pred's #() once read the
    ! predicate as its own argument).
    params = gcv_empty(roots)
    call vs_set(base + 2, params)
    do i = 1, maxn
       write(nm, '(A,I0,A,I0,A)') "p", i, "__", anon_id(i), "#"
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
       write(nm, '(A,I0,A)') "rest__", anon_id(-1), "#"
       sym = gc_sym(trim(nm), roots)
       call vs_set(base + 3, sym)
       params = gcv_conj(vs_get(base + 2), vs_get(base + 3), roots)
       call vs_set(base + 2, params)
    end if
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

  ! The number of #()'s parameter n (-1 for %&), given at its first use;
  ! the highest n used is the arity (FnReader's registerArg).
  integer function anon_id(n) result(id)
    integer, intent(in) :: n
    type(rd_state), pointer :: rdx
    integer, allocatable :: bigger(:)
    rdx => rd_self()
    if (n < 0) then
       if (rdx%anon_rest == 0) rdx%anon_rest = gc_next(anon_seq)
       id = rdx%anon_rest
    else
       if (n + 1 > size(rdx%anon_ids)) then
          allocate(bigger(2 * (n + 1)))
          bigger = 0
          bigger(1:size(rdx%anon_ids)) = rdx%anon_ids
          call move_alloc(bigger, rdx%anon_ids)
       end if
       ! slot n + 1: %0 is a name of its own too
       if (rdx%anon_ids(n + 1) == 0) rdx%anon_ids(n + 1) = gc_next(anon_seq)
       id = rdx%anon_ids(n + 1)
       rdx%anon_max = max(rdx%anon_max, n)
    end if
  end function anon_id

  ! ArgReader: inside #(...), the token a % begins -- up to whitespace or
  ! a terminating macro character -- is % (the first parameter), %& (the
  ! rest) or %n for n from 1, matched whole (argPat); anything else is
  ! refused. It is read as the parameter's name at once, so a
  ! syntax-quote or a quote around it sees the name, as in clj. pos is
  ! at the %.
  recursive function read_arg(text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: n, e, ios
    character(len=:), allocatable :: tok
    character(len=24) :: nm
    rdx => rd_self()
    v = gc_nil()
    pos = pos + 1
    e = pos
    do while (e <= len(text))
       if (is_space(text(e:e)) .or. is_delim(text(e:e))) exit
       e = e + 1
    end do
    tok = text(pos:e - 1)
    pos = e
    if (len(tok) == 0) then
       n = 1
    else if (tok == "&") then
       n = -1
    else if (verify(tok, "0123456789") == 0 .and. tok(1:1) /= "0" .and. len(tok) <= 9) then
       read(tok, *, iostat=ios) n
    else
       call fail("arg literal must be %, %& or %integer", "clotran.host.illegal_state_exception")
       return
    end if
    if (n < 0) then
       write(nm, '(A,I0,A)') "rest__", anon_id(-1), "#"
    else
       write(nm, '(A,I0,A,I0,A)') "p", n, "__", anon_id(n), "#"
    end if
    v = gc_sym(trim(nm), roots)
  end function read_arg

  ! A key as clj's "Duplicate key" message names it (toString): a
  ! keyword resolved, a string's text, a symbol or integer as itself,
  ! anything else as it was written (src)
  subroutine key_text(k, src, t)
    type(gc_value), intent(in) :: k
    character(len=*), intent(in) :: src
    character(len=:), allocatable, intent(out) :: t
    character(len=24) :: b
    select case (k%tag)
    case (GCT_KEY)
       call gc_ref_text(k%ref, s=t)
       t = ":" // t
    case (GCT_STR, GCT_SYM)
       call gc_ref_text(k%ref, s=t)
    case (GCT_INT)
       write(b, '(I0)') k%ival
       t = trim(b)
    case (GCT_CHAR)
       call gcp_str(k, .false., s=t)
    case (GCT_REAL)
       ! a double as toString writes it: Infinity and NaN, not ##Inf
       if (gc_rval(k) /= gc_rval(k)) then
          t = "NaN"
       else if (gc_rval(k) > huge(1.0_gc_dp)) then
          t = "Infinity"
       else if (gc_rval(k) < -huge(1.0_gc_dp)) then
          t = "-Infinity"
       else
          call gcp_str(k, .false., s=t)
       end if
    case default
       ! printed, as toString prints it: a BigInt without its N, a
       ! BigDecimal without its M
       call gcp_str(k, .true., s=t)
       if ((k%tag == GCT_BIG .or. k%tag == GCT_DEC) .and. len(t) > 1) t = t(1:len(t) - 1)
       if (len(t) == 0) t = trim(adjustl(src))
    end select
  end subroutine key_text

  ! #{...} -- elements read like a vector's, then each maps to
  ! itself; an element twice is an error, as in clj.
  recursive function read_set(text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, items, m, item
    integer :: base, i

    rdx => rd_self()
    v = gc_nil()
    base = vs_enter(3)
    items = read_seq(text, pos, "}", .true., roots)
    if (rdx%has_error) then
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
    ! a set is hashed at every size, as PersistentHashSet is
    m = gca_hash_empty(roots)
    call vs_set(base + 2, m)
    do i = 0, gcv_count(vs_get(base + 1)) - 1
       item = gcv_nth(vs_get(base + 1), i)
       call vs_set(base + 3, item)
       ! PersistentHashSet.createWithCheck: an element twice is an error
       if (gca_contains(vs_get(base + 2), vs_get(base + 3))) then
          block
            character(len=:), allocatable :: kt
            call key_text(vs_get(base + 3), "", kt)
            call fail("Duplicate key: " // kt, "clotran.host.illegal_argument_exception")
          end block
          call vs_leave(base); return
       end if
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
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character :: c
    integer :: p0

    rdx => rd_self()
    v = gc_nil()
    if (pos + 1 > len(text)) then
       call fail("EOF while reading character")
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
    case ("=")
       pos = pos + 2
       v = read_eval_form(text, pos, roots)
    case ("#")
       pos = pos + 2
       v = read_symbolic(text, pos, roots)
    case ("?")
       pos = pos + 2
       v = read_cond(text, pos, roots)
    case (":")
       v = read_ns_map(text, pos, roots)
    case ("<")
       ! #<...> is how an unreadable object prints (UnreadableReader)
       call fail("Unreadable form")
    case default
       if (rdx%suppress_read .and. ((c >= "a" .and. c <= "z") .or. (c >= "A" .and. c <= "Z"))) then
          ! #tag form in a branch nobody selected: read past the tag and
          ! the form. A selected branch still has no data readers, and
          ! fails below by tag as before.
          pos = pos + 1
          v = read_form(text, pos, roots)
          if (rdx%has_error) return
          v = read_form(text, pos, roots)
          v = gc_nil()
       else if (rdx%tag_markers .and. ((c >= "a" .and. c <= "z") .or. &
            (c >= "A" .and. c <= "Z"))) then
          pos = pos + 1
          v = read_tagged(text, pos, roots)
       else
          ! CtorReader: the tag is read as a form, and must be a symbol
          pos = pos + 1
          call skip_space(text, pos)
          if (pos > len(text)) then
             call fail("EOF while reading")
          else
             p0 = pos
             v = read_form(text, pos, roots)
             if (.not. rdx%has_error) then
                if (v%tag == GCT_SYM .and. rdx%tag_markers) then
                   ! a symbol tag however spelled -- # uuid, #.x -- is a tagged
                   ! literal as #uuid is, resolved by its data reader or as a
                   ! record class (clotran.reader)
                   pos = p0
                   v = read_tagged(text, pos, roots)
                   return
                else if (v%tag == GCT_SYM) then
                   ! the tagged form is read first: an error in it wins
                   block
                     character(len=:), allocatable :: tn
                     type(gc_value) :: tf
                     call gc_ref_text(v%ref, s=tn)
                     tf = read_form(text, pos, roots)
                     if (.not. rdx%has_error) call fail("No reader function for tag " // tn)
                   end block
                else
                   call fail("Reader tag must be a symbol")
                end if
                v = gc_nil()
             end if
          end if
       end if
    end select
  end function read_dispatch

  ! #tag form as a marker map. The tag is read as a symbol and the
  ! form as any form, exactly as LispReader.CtorReader does before it
  ! looks the tag up.
  recursive function read_tagged(text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, tag, form, m, k
    integer :: base
    rdx => rd_self()
    v = gc_nil()
    base = vs_enter(4)
    tag = read_form(text, pos, roots)
    if (rdx%has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 1, tag)
    if (tag%tag /= GCT_SYM) then
       call fail("Reader tag must be a symbol")
       call vs_leave(base); return
    end if
    form = read_form(text, pos, [roots, [vs_get(base + 1)]])
    if (rdx%has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 2, form)
    m = gca_empty([roots, [vs_get(base + 1), vs_get(base + 2)]])
    call vs_set(base + 3, m)
    k = gc_key("clotran/tagged-literal", [roots, [vs_get(base + 1), &
         vs_get(base + 2), vs_get(base + 3)]])
    call vs_set(base + 4, k)
    m = gca_assoc(vs_get(base + 3), vs_get(base + 4), gc_bool(.true.), &
         [roots, [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), &
         vs_get(base + 4)]])
    call vs_set(base + 3, m)
    k = gc_key("tag", [roots, [vs_get(base + 1), vs_get(base + 2), &
         vs_get(base + 3)]])
    call vs_set(base + 4, k)
    m = gca_assoc(vs_get(base + 3), vs_get(base + 4), vs_get(base + 1), &
         [roots, [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), &
         vs_get(base + 4)]])
    call vs_set(base + 3, m)
    k = gc_key("form", [roots, [vs_get(base + 1), vs_get(base + 2), &
         vs_get(base + 3)]])
    call vs_set(base + 4, k)
    m = gca_assoc(vs_get(base + 3), vs_get(base + 4), vs_get(base + 2), &
         [roots, [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), &
         vs_get(base + 4)]])
    call vs_set(base + 3, m)
    ! the reader's own, to be resolved: a tagged-literal a program
    ! built has the same shape without this key
    k = gc_key("clotran/unread", [roots, [vs_get(base + 1), vs_get(base + 2), &
         vs_get(base + 3)]])
    call vs_set(base + 4, k)
    v = gca_assoc(vs_get(base + 3), vs_get(base + 4), gc_bool(.true.), &
         [roots, [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), &
         vs_get(base + 4)]])
    call vs_leave(base)
  end function read_tagged

  ! The name of the file being read on this thread, "" at the REPL:
  ! the analyser asks whether a form came from the vendored tree
  ! (direct linking, DEVIATIONS 55).
  subroutine gcr_current_file(s)
    type(rd_state), pointer :: rdx
    character(len=:), allocatable, intent(out) :: s
    rdx => rd_self()
    s = ""
    if (rdx%cur_file > 0) s = trim(files(rdx%cur_file)%name)
  end subroutine gcr_current_file

  ! Turns #tag markers on or off, and answers what it was, so the
  ! caller can restore it.
  ! read-string's :read-cond and :features, set around its read and put
  ! back after: allow is {:read-cond :allow}, features the extra feature
  ! names blank-separated. Answers what they were.
  subroutine gcr_set_read_cond(allow, features, was_allow, was_features)
    type(rd_state), pointer :: rdx
    logical, intent(in) :: allow
    character(len=*), intent(in) :: features
    logical, intent(out) :: was_allow
    character(len=:), allocatable, intent(out) :: was_features
    rdx => rd_self()
    was_allow = rdx%rc_allow
    was_features = ""
    if (allocated(rdx%rc_features)) was_features = rdx%rc_features
    rdx%rc_allow = allow
    rdx%rc_features = features
  end subroutine gcr_set_read_cond

  logical function gcr_set_tag_markers(on) result(was)
    type(rd_state), pointer :: rdx
    logical, intent(in) :: on
    rdx => rd_self()
    was = rdx%tag_markers
    rdx%tag_markers = on
  end function gcr_set_tag_markers

  ! ---- reader conditionals ----
  !
  ! #?(:feature form ...) and #?@(...). The features claimed here are
  ! :cljf and :default; :clj is clj and is not claimed, so a .cljc
  ! library ported to clotran gets a :cljf branch beside each :clj one
  ! and that is the port. Branches are read in order, the first whose
  ! feature matches is kept, and every other branch is read under
  ! suppress_read and dropped -- LispReader.readCondDelimited, without
  ! the :preserve mode (DEVIATIONS 33). Only a .cljc file, or read-string
  ! given {:read-cond :allow}, may read one at all.
  recursive function read_cond(text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, k, val
    logical :: splicing, chosen, match, saved, done
    integer :: base
    character(len=:), allocatable :: kt

    rdx => rd_self()
    v = gc_nil()
    if (.not. (rdx%rc_file .or. rdx%rc_allow)) then
       call fail("Conditional read not allowed")
       return
    end if
    rdx%rc_nothing = .false.
    rdx%rc_splice = .false.
    splicing = .false.
    if (pos <= len(text)) then
       if (text(pos:pos) == "@") then
          splicing = .true.
          pos = pos + 1
       end if
    end if
    call skip_space(text, pos)
    if (pos > len(text)) then
       call fail("EOF while reading")
       return
    end if
    if (text(pos:pos) /= "(") then
       call fail("read-cond body must be a list")
       return
    end if
    pos = pos + 1
    base = vs_enter(1)
    call vs_set(base + 1, gc_nil())
    chosen = .false.
    ! readCondDelimited's loop: a feature, and its form when the feature
    ! is claimed; then one form read past. Once a branch is chosen, every
    ! form after it is read past with nothing checked.
    do
       if (.not. chosen) then
          k = read_next(text, pos, ")", [roots, vs_get(base + 1)], done)
          if (rdx%has_error .or. done) exit
          if (k%tag /= GCT_KEY) then
             ! its toString, as clj's message has it: a pattern's is its source
             ! (String concatenation makes a nil "null")
             if (k%tag == GCT_NIL) then
                kt = "null"
             else if (gc_kind(k) == OBJ_REGEX) then
                call gcp_str(gc_slot(k, 1), .false., s=kt)
             else
                call gcp_str(k, .false., s=kt)
             end if
             call fail("Feature should be a keyword: " // kt)
             exit
          end if
          if (gc_ref_is(k%ref, "else") .or. gc_ref_is(k%ref, "none")) then
             call gc_ref_text(k%ref, s=kt)
             call fail("Feature name :" // kt // " is reserved.")
             exit
          end if
          match = gc_ref_is(k%ref, "cljf") .or. gc_ref_is(k%ref, "default")
          if (.not. match .and. allocated(rdx%rc_features)) then
             call gc_ref_text(k%ref, s=kt)
             match = index(" " // rdx%rc_features // " ", " " // kt // " ") > 0
          end if
          if (match) then
             val = read_next(text, pos, ")", [roots, vs_get(base + 1)], done)
             if (rdx%has_error) exit
             if (done) then
                call fail("read-cond requires an even number of forms.")
                exit
             end if
             chosen = .true.
             call vs_set(base + 1, val)
          end if
       end if
       saved = rdx%suppress_read
       rdx%suppress_read = .true.
       val = read_next(text, pos, ")", [roots, vs_get(base + 1)], done)
       rdx%suppress_read = saved
       if (rdx%has_error .or. done) exit
    end do
    if (.not. rdx%has_error) then
       if (.not. chosen) then
          rdx%rc_nothing = .true.
       else
          v = vs_get(base + 1)
          if (splicing) then
             if (gcl_is(v) .or. gcv_is(v)) then
                rdx%rc_splice = .true.
             else
                v = gc_nil()
                call fail("Spliced form list in read-cond-splicing must implement clotran.host.list")
             end if
          end if
       end if
    end if
    call vs_leave(base)
  end function read_cond

  ! Every element of coll -- a list or a vector -- conj'd onto acc.
  function splice_into(acc, coll, roots) result(out)
    type(gc_value), intent(in) :: acc, coll
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i
    base = vs_enter(2)
    call vs_set(base + 1, acc)
    call vs_set(base + 2, coll)
    if (gcv_is(coll)) then
       do i = 0, gcv_count(vs_get(base + 2)) - 1
          call vs_set(base + 1, gcv_conj(vs_get(base + 1), gcv_nth(vs_get(base + 2), i), roots))
       end do
    else
       do while (gcl_count(vs_get(base + 2)) > 0)
          call vs_set(base + 1, gcv_conj(vs_get(base + 1), gcl_first(vs_get(base + 2)), roots))
          call vs_set(base + 2, gcl_rest(vs_get(base + 2), roots))
       end do
    end if
    out = vs_get(base + 1)
    call vs_leave(base)
  end function splice_into


  ! ##Inf, ##-Inf and ##NaN -- the symbolic values. They have no
  ! literal spelling of their own, which is the whole reason the reader
  ! macro exists; LispReader maps exactly these three and rejects
  ! anything else.
  function read_symbolic(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character(len=:), allocatable :: tok
    integer :: start

    v = gc_nil()
    ! SymbolicValueReader reads a FORM: whitespace, commas and comments
    ! before it are skipped, as read skips them -- ##,NaN is ##NaN
    call skip_ignorables(text, pos, roots)
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
       ! SymbolicValueReader reads a FORM, and its own errors come first
       ! (##_/ is "Invalid token: _/"): a symbol it does not know, or
       ! anything else, by its text
       pos = start
       if (pos > len(text)) then
          call fail("EOF while reading")
          return
       end if
       block
         type(gc_value) :: o
         character(len=:), allocatable :: ot
         o = read_form(text, pos, roots)
         if (gcr_has_error()) return
         ! inside #(...) each %-arg is already its p1__N# or rest__N#, as
         ! ArgReader leaves it, so the message shows that (read_arg)
         if (o%tag == GCT_SYM) then
            call gc_ref_text(o%ref, s=ot)
            call fail("Unknown symbolic value: ##" // ot)
         else if (o%tag == GCT_STR .or. o%tag == GCT_CHAR) then
            ! toString: a string's text, a character itself
            call gcp_str(o, .false., s=ot)
            call fail("Invalid token: ##" // ot)
         else if (o%tag == GCT_REAL .and. .not. ieee_is_finite(gc_rval(o))) then
            ! a double's toString: Infinity, -Infinity, NaN
            if (ieee_is_nan(gc_rval(o))) then
               ot = "NaN"
            else if (gc_rval(o) > 0) then
               ot = "Infinity"
            else
               ot = "-Infinity"
            end if
            call fail("Invalid token: ##" // ot)
         else
            call gcp_str(o, .true., s=ot)
            call fail("Invalid token: ##" // ot)
         end if
         v = gc_nil()
       end block
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
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, m, form, key
    integer :: base, caret

    rdx => rd_self()
    v = gc_nil()
    caret = pos - 1   ! the ^, whichever spelling reached here
    base = vs_enter(4)
    m = read_form(text, pos, roots)
    if (rdx%has_error) then
       call vs_leave(base); return
    end if
    ! metadata on the metadata (^^:a x y) is the inner form's own: x is
    ! still a symbol, so a :tag -- whose value is x as read, its own
    ! metadata kept, as MetaReader keeps it
    call vs_set(base + 4, m)
    do while (gc_kind(m) == OBJ_META)
       m = gc_slot(m, 1)
    end do
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
       m = gca_assoc(vs_get(base + 2), vs_get(base + 3), vs_get(base + 4), roots)
       call vs_set(base + 1, m)
    else if (m%tag == GCT_SYM .or. m%tag == GCT_STR) then
       v = gca_empty(roots)
       call vs_set(base + 2, v)
       key = gc_key("tag", roots)
       call vs_set(base + 3, key)
       m = gca_assoc(vs_get(base + 2), vs_get(base + 3), vs_get(base + 4), roots)
       call vs_set(base + 1, m)
    else
       call fail("Metadata must be Symbol,Keyword,String,Vector or Map", "clotran.host.illegal_argument_exception")
       call vs_leave(base); return
    end if

    form = read_form(text, pos, roots)
    if (rdx%has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 2, form)
    ! only what can hold metadata takes it (MetaReader: IMeta) -- a
    ! symbol or a collection, not a string, number, char, keyword,
    ! boolean, nil or pattern (scripts/fuzz-read)
    select case (form%tag)
    case (GCT_NIL, GCT_BOOL, GCT_INT, GCT_REAL, GCT_CHAR, GCT_STR, GCT_KEY, &
          GCT_RATIO, GCT_BIG, GCT_DEC, GCT_BIGRATIO)
       call fail("Metadata can only be applied to IMetas", "clotran.host.illegal_argument_exception")
       call vs_leave(base); return
    end select
    if (gc_kind(form) == OBJ_REGEX) then
       call fail("Metadata can only be applied to IMetas", "clotran.host.illegal_argument_exception")
       call vs_leave(base); return
    end if
    ! A form with metadata already (^int ^:foo x): MetaReader merges, the
    ! outer ^'s entries over the form's own -- {:foo true, :tag int} --
    ! where a second wrapper hid the first and records' ^int
    ! ^:unsynchronized-mutable __hash read as immutable
    if (gc_kind(vs_get(base + 2)) == OBJ_META) then
       block
         type(gc_value), allocatable :: ks(:), vals(:)
         integer :: i
         call gca_entries(vs_get(base + 1), ks, vals)
         call vs_set(base + 3, gc_slot(vs_get(base + 2), 2))
         call vs_set(base + 2, gc_slot(vs_get(base + 2), 1))
         do i = 1, size(ks)
            m = gca_assoc(vs_get(base + 3), ks(i), vals(i), roots)
            call vs_set(base + 3, m)
         end do
         call vs_set(base + 1, vs_get(base + 3))
       end block
    end if
    ! On a list read from a file, MetaReader adds the ^'s own line and
    ! column to the map, over any the map gave.
    if (gcl_is(vs_get(base + 2)) .and. rdx%cur_file /= 0) then
       block
         character(len=:), allocatable :: pf
         integer :: pl, pc
         call gcr_position_parts(rdx%cur_file * POS_SHIFT + caret, pf, pl, pc)
         key = gc_key("line", roots)
         call vs_set(base + 3, key)
         m = gca_assoc(vs_get(base + 1), vs_get(base + 3), gc_int(pl), roots)
         call vs_set(base + 1, m)
         key = gc_key("column", roots)
         call vs_set(base + 3, key)
         m = gca_assoc(vs_get(base + 1), vs_get(base + 3), gc_int(pc), roots)
         call vs_set(base + 1, m)
       end block
    end if
    v = gc_obj(OBJ_META, [vs_get(base + 2), vs_get(base + 1)], roots)
    call vs_leave(base)
  end function read_meta

  ! (sym form) -- what ', `, @ and ~ expand to.
  ! #=form, read and evaluated by the evaluator (EvalReader); a branch a
  ! reader conditional did not select is read past.
  recursive function read_eval_form(text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, inner
    character(len=:), allocatable :: err, cls
    rdx => rd_self()
    v = gc_nil()
    if (.not. associated(eval_reader)) then
       call fail("#= needs an evaluator")
       return
    end if
    if (.not. rdx%suppress_read) then
       call eval_reader(.true., gc_nil(), roots, v, err, cls)
       if (len(err) > 0) then
          call fail(err, cls)
          return
       end if
    end if
    inner = read_form(text, pos, roots)
    if (rdx%has_error) return
    if (rdx%suppress_read) return
    call eval_reader(.false., inner, with(roots, inner), v, err, cls)
    if (len(err) > 0) then
       call fail(err, cls)
       v = gc_nil()
    end if
  end function read_eval_form

  ! `form: the next form, expanded by the evaluator's expander
  recursive function read_syntax_quote(text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, inner
    character(len=:), allocatable :: err, cls
    rdx => rd_self()
    v = gc_nil()
    inner = read_form(text, pos, roots)
    if (rdx%has_error) return
    call sq_expander(inner, with(roots, inner), v, err, cls)
    if (len(err) > 0) then
       call fail(err, cls)
       v = gc_nil()
    end if
  end function read_syntax_quote

  recursive function wrap(name, text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: name
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, inner, sym
    type(gc_value), allocatable :: r2(:)

    rdx => rd_self()
    v = gc_nil()
    inner = read_form(text, pos, roots)
    if (rdx%has_error) return
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
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    character, intent(in) :: closer
    logical, intent(in) :: as_vector
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, acc, item
    type(gc_value), allocatable :: r2(:)
    integer :: i
    logical :: done

    rdx => rd_self()
    v = gc_nil()
    acc = gcv_empty(roots)
    do
       r2 = with(roots, acc)
       item = read_next(text, pos, closer, r2, done)
       if (rdx%has_error) return
       if (done) exit
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
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, k, val
    type(gc_value), allocatable :: r2(:)
    integer :: kp, ke
    character(len=:), allocatable :: odd, dup
    logical :: has_dup, done

    rdx => rd_self()
    odd = "Map literal must contain an even number of forms"
    if (rdx%ns_map) odd = "Namespaced map literal must contain an even number of forms"
    rdx%ns_map = .false.
    dup = ""
    has_dup = .false.
    v = gca_empty(roots)
    do
       r2 = with(roots, v)
       if (rdx%n_pending == 0) call skip_ignorables(text, pos, r2)
       if (rdx%has_error) return
       kp = pos
       k = read_next(text, pos, "}", r2, done)
       if (rdx%has_error) return
       if (done) then
          ! a key twice is refused once the map is read through, as clj
          ! reads every form before createWithCheck: an error after it
          ! in the map comes first
          if (has_dup) call fail("Duplicate key: " // dup, "clotran.host.illegal_argument_exception")
          return
       end if
       ke = pos - 1
       val = read_next(text, pos, "}", with(r2, k), done)
       if (rdx%has_error) return
       if (done) then
          call fail(odd)
          return
       end if
       ! PersistentArrayMap.createWithCheck: a key twice is an error
       if (gca_contains(v, k)) then
          if (.not. has_dup) call key_text(k, text(kp:ke), dup)
          has_dup = .true.
       end if
       v = gca_assoc(v, k, val, with(with(r2, k), val))
    end do
  end function read_map


  ! #:ns{:a 1} -- a NAMESPACED MAP: every unqualified key takes that
  ! namespace, :_/x means none, and an already-qualified key is left
  ! alone. #::{...} is the current namespace and #::alias{...} goes
  ! through an alias, the same resolver ::keywords use. Symbol keys
  ! qualify too; anything else is a key like any other.
  recursive function read_ns_map(text, pos, roots) result(v)
    type(rd_state), pointer :: rdx
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, m, k2
    type(gc_value), allocatable :: ks(:), vls(:)
    character(len=:), allocatable :: tok, ns
    integer :: base, i
    logical :: auto, have_sym
    type(gc_value) :: sym

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    rdx => rd_self()
    v = gc_nil()
    ! LispReader.NamespaceMapReader, check for check: #: or #:: (auto),
    ! then whitespace only before { when auto, else a FORM -- the
    ! namespace -- read as any form, so its own errors come first
    pos = pos + 2            ! past the # and the :
    auto = .false.
    if (pos <= len(text)) then
       if (text(pos:pos) == ":") then
          auto = .true.
          pos = pos + 1
       end if
    end if
    have_sym = .false.
    sym = gc_nil()
    base = vs_enter(3)
    if (pos <= len(text) .and. is_space(text(min(pos, len(text)):min(pos, len(text))))) then
       if (.not. auto) then
          call fail("Namespaced map must specify a namespace")
          call vs_leave(base); return
       end if
       do while (pos <= len(text))
          if (.not. is_space(text(pos:pos))) exit
          pos = pos + 1
       end do
       if (pos > len(text) .or. text(min(pos, len(text)):min(pos, len(text))) /= "{") then
          call fail("Namespaced map must specify a namespace")
          call vs_leave(base); return
       end if
    else if (pos > len(text) .or. text(min(pos, len(text)):min(pos, len(text))) /= "{") then
       sym = read_form(text, pos, roots)
       if (rdx%has_error) then
          call vs_leave(base); return
       end if
       call vs_set(base + 1, sym)
       have_sym = .true.
       do while (pos <= len(text))
          if (.not. is_space(text(pos:pos))) exit
          pos = pos + 1
       end do
    end if
    if (pos > len(text) .or. text(min(pos, len(text)):min(pos, len(text))) /= "{") then
       call fail("Namespaced map must specify a map")
       call vs_leave(base); return
    end if
    tok = ""
    if (have_sym) then
       if (sym%tag == GCT_SYM) then
          call gc_ref_text(sym%ref, s=tok)
       else
          call gcp_str(sym, .true., s=tok)
       end if
       if (sym%tag /= GCT_SYM .or. (index(tok, "/") > 0 .and. tok /= "/")) then
          call fail("Namespaced map must specify a valid namespace: " // tok)
          call vs_leave(base); return
       end if
    end if
    if (auto) then
       if (.not. associated(ns_resolver)) then
          call fail("reader: no namespace resolver for ::" // tok)
          call vs_leave(base); return
       end if
       block
          call ns_resolver(tok, ns=dlt_1)
          ns = dlt_1
       end block
       if (len(ns) == 0) then
          call fail("Unknown auto-resolved namespace alias: " // tok)
          call vs_leave(base); return
       end if
    else if (.not. have_sym) then
       ! #:{ -- clj names the missing namespace "null"
       call fail("Namespaced map must specify a namespace")
       call vs_leave(base); return
    else
       ns = tok
    end if
    call vs_leave(base)
    pos = pos + 1
    rdx%ns_map = .true.
    m = read_map(text, pos, roots)
    if (rdx%has_error) return

    base = vs_enter(3)
    call vs_set(base + 1, m)
    call gca_entries(vs_get(base + 1), ks, vls)
    v = gca_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, v)
    do i = 1, size(ks)
       k2 = qualify_key(ks(i), ns, [roots, vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 3, k2)
       v = gca_assoc(vs_get(base + 2), vs_get(base + 3), vls(i), &
            [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
       call vs_set(base + 2, v)
    end do
    v = vs_get(base + 2)
    call vs_leave(base)
  end function read_ns_map

  function qualify_key(k, ns, roots) result(out)
    type(gc_value), intent(in) :: k
    character(len=*), intent(in) :: ns
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    character(len=:), allocatable :: t
    integer :: slash
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    out = k
    if (k%tag /= GCT_KEY .and. k%tag /= GCT_SYM) return
    block
       call gc_ref_text(k%ref, s=dlt_1)
       t = dlt_1
    end block
    slash = index(t, "/")
    if (slash == 0) then
       t = ns // "/" // t
    else if (t(1:slash-1) == "_") then
       t = t(slash+1:)
    else
       return
    end if
    if (k%tag == GCT_KEY) then
       out = gc_key(t, roots)
    else
       out = gc_sym(t, roots)
    end if
  end function qualify_key

  function read_string(text, pos, roots) result(v)
    character(len=*), intent(in) :: text
    integer, intent(inout) :: pos
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character(len=:), allocatable :: acc
    character :: c

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    v = gc_nil()
    pos = pos + 1 ! consume the opening quote
    acc = ""
    do
       if (pos > len(text)) then
          call fail("EOF while reading string")
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
             call fail("EOF while reading string")
             return
          end if
          ! LispReader.StringReader's escapes, and its refusals
          select case (text(pos:pos))
          case ("n"); acc = acc // achar(10)
          case ("t"); acc = acc // achar(9)
          case ("r"); acc = acc // achar(13)
          case ("b"); acc = acc // achar(8)
          case ("f"); acc = acc // achar(12)
          case ('"'); acc = acc // '"'
          case (achar(92)); acc = acc // achar(92)
          case ("u")
             ! \uXXXX: exactly four hex digits, the code point, as UTF-8
             ! bytes -- a string is bytes here, so "é" is the two of e-acute
             pos = pos + 1
             if (pos > len(text)) then
                call fail("EOF while reading string")
                return
             end if
             if (digit_of(text(pos:pos), 16) < 0) then
                call fail("Invalid unicode escape: \u" // text(pos:pos))
                return
             end if
             block
               integer :: cp
               cp = read_code_unit(text, pos, 16, 4, .true.)
               if (gcr_has_error()) return
               call u8_enc(cp, s=dlt_1)
               acc = acc // dlt_1
             end block
          case ("0":"9")
             ! \NNN: up to three octal digits, at most 377
             block
               integer :: cp
               cp = read_code_unit(text, pos, 8, 3, .false.)
               if (gcr_has_error()) return
               if (cp > 255) then
                  call fail("Octal escape sequence must be in range [0, 377].")
                  return
               end if
               call u8_enc(cp, s=dlt_1)
               acc = acc // dlt_1
             end block
          case default
             call fail("Unsupported escape character: \" // text(pos:min(len(text), pos + u8_len(text(pos:pos)) - 1)))
             return
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
       call fail("EOF while reading character")
       return
    end if
    ! the token runs to whitespace or a MACRO-TERMINATING character, as
    ! LispReader.readToken's does -- a backslash among them, so \\\\ is
    ! two backslash characters, not one token of three
    do while (pos <= len(text))
       if (is_space(text(pos:pos)) .or. is_delim(text(pos:pos))) exit
       if (index('\";@^`~', text(pos:pos)) > 0) exit
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
       ! LispReader.CharacterReader: one character however many bytes;
       ! \uXXXX exactly four hex digits, not a surrogate; \oNNN at most
       ! three octal digits, at most 377; anything else refused
       block
         integer :: cp, i, d, w
         character(len=16) :: b
         if (u8_count(name) == 1) then
            v = gc_char_cp(u8_at(name, 0))
            return
         end if
         if (name(1:1) == "u") then
            ! the length in characters, as clj's token is; a digit that is
            ! not one is named whole, a UTF-8 character and not its first byte
            if (u8_count(name) /= 5) then
               call fail("Invalid unicode character: " // achar(92) // name, "clotran.host.illegal_argument_exception")
               return
            end if
            cp = 0
            i = 2
            do while (i <= len(name))
               w = u8_len(name(i:i))
               d = -1
               if (w == 1) d = digit_of(name(i:i), 16)
               if (d < 0) then
                  call fail("Invalid digit: " // name(i:min(len(name), i + w - 1)), "clotran.host.illegal_argument_exception")
                  return
               end if
               cp = cp * 16 + d
               i = i + w
            end do
            if (cp >= 55296 .and. cp <= 57343) then
               write(b, '(Z0)') cp
               do i = 1, len_trim(b)
                  if (b(i:i) >= "A" .and. b(i:i) <= "F") b(i:i) = achar(iachar(b(i:i)) + 32)
               end do
               call fail("Invalid character constant: " // achar(92) // "u" // trim(b))
               return
            end if
            v = gc_char_cp(cp)
            return
         end if
         if (name(1:1) == "o") then
            ! in characters, as the token's length is
            if (u8_count(name) - 1 > 3) then
               write(b, '(I0)') u8_count(name) - 1
               call fail("Invalid octal escape sequence length: " // trim(b))
               return
            end if
            cp = 0
            i = 2
            do while (i <= len(name))
               w = u8_len(name(i:i))
               d = -1
               if (w == 1) d = digit_of(name(i:i), 8)
               if (d < 0) then
                  call fail("Invalid digit: " // name(i:min(len(name), i + w - 1)), "clotran.host.illegal_argument_exception")
                  return
               end if
               cp = cp * 8 + d
               i = i + w
            end do
            if (cp > 255) then
               call fail("Octal escape sequence must be in range [0, 377].")
               return
            end if
            v = gc_char_cp(cp)
            return
         end if
       end block
       call fail("Unsupported character: " // achar(92) // name)
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
    logical :: numeric

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    start = pos
    ! a NUMBER -- a digit first, or a sign and then one -- ends at any
    ! macro character, # ' and % too (LispReader.readNumber's isMacro):
    ! 3'x is 3 and 'x, 8# is 8 and a # (scripts/fuzz-read); a symbol
    ! only at a terminating one
    numeric = index("0123456789", text(pos:pos)) > 0
    if (.not. numeric .and. pos < len(text) .and. index("+-", text(pos:pos)) > 0) &
         numeric = index("0123456789", text(pos+1:pos+1)) > 0
    do while (pos <= len(text))
       if (is_space(text(pos:pos)) .or. is_delim(text(pos:pos))) exit
       if (numeric .and. pos > start .and. is_macro(text(pos:pos))) exit
       pos = pos + 1
    end do
    tok = text(start:pos - 1)

    ! inside #(...), a % token is checked as it is read, as ArgReader
    ! does: before anything after it can fail first. argPat is
    ! %(?:(&)|([1-9][0-9]*))?, so %0 and %0363 are refused too
    if (len(tok) >= 2) then
       if (rd_self_in_anon() .and. tok(1:1) == "%" .and. tok /= "%&" .and. &
           (verify(tok(2:), "0123456789") /= 0 .or. tok(2:2) == "0")) then
          call fail("arg literal must be %, %& or %integer", "clotran.host.illegal_state_exception")
          v = gc_nil()
          return
       end if
    end if

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
       ! A plain decimal integer too big for 64 bits READS AS A BigInt,
       ! as Clojure's readNumber does: 12345678901234567890 is a
       ! BigInt there, not a wrapped long. Only the plain decimal
       ! shape -- a radix or hex literal past the range still wraps,
       ! which is what digits_radix has always done.
       if (plain_decimal(tok)) then
          if (.not. big_fits_i64(tok)) then
             v = gc_big(tok, roots)
             return
          end if
       end if
       call parse_int(tok, ival, iok, iclaim)
       if (.not. iclaim) call parse_ratio(tok, rval, rok, rclaim, roots)
       if (iok) then
          v = gc_int(ival)
       else if (.not. iclaim .and. rok) then
          v = rval
       else if (.not. iclaim .and. .not. rclaim .and. looks_real(tok)) then
          v = gc_real(to_real(tok))
       else if (suffixed_number(tok, v, roots)) then
          continue
       else
          if (radix_out_of_range(tok)) then
             call fail("Radix out of range", "clotran.host.number_format_exception")
          else
             call fail("Invalid number: " // tok, "clotran.host.number_format_exception")
          end if
          v = gc_nil()
       end if
    else if (.not. symbol_token_ok(tok)) then
       call fail("Invalid token: " // tok)
       v = gc_nil()
    else if (len(tok) > 2 .and. tok(1:2) == "::" .and. associated(ns_resolver)) then
       ! ::name is :current-ns/name and ::alias/name goes through
       ! the alias, as LispReader.matchSymbol reads them; an alias
       ! that resolves to nothing is "Invalid token: ::a/x". It was
       ! read as a keyword whose NAME began with a colon, so ::a and
       ! :user/a were two different keywords and (namespace ::a) nil.
       block
         character(len=:), allocatable :: ns
         integer :: slash
         slash = index(tok, "/")
         if (slash > 0) then
            block
               call ns_resolver(tok(3:slash-1), ns=dlt_1)
               ns = dlt_1
            end block
         else
            block
               call ns_resolver("", ns=dlt_1)
               ns = dlt_1
            end block
         end if
         if (len(ns) == 0) then
            call fail("Invalid token: " // tok)
            v = gc_nil()
         else if (slash > 0) then
            v = gc_key(ns // tok(slash:), roots)
         else
            v = gc_key(ns // "/" // tok(3:), roots)
         end if
       end block
    else if (len(tok) > 1 .and. tok(1:1) == ":") then
       v = gc_key(tok(2:), roots)
    else
       v = gc_sym(tok, roots)
    end if
  end function read_atom

  ! Is tok a symbol or keyword LispReader.matchSymbol accepts? Its
  ! symbolPat, [:]?([\D&&[^/]].*/)?(/|[\D&&[^/]][^/]*), tried in the
  ! order clj's backtracking tries it -- the colon taken, then the
  ! longest namespace, then none -- and the first match checked for a
  ! namespace ending ":/", a name ending ":" or a "::" past the start.
  ! Failing the pattern, arraySymbolPat ([\D&&[^/:]].*)/([1-9]) is
  ! String/1, an array class (CLJ-2807).
  logical function symbol_token_ok(tok) result(ok)
    character(len=*), intent(in) :: tok
    integer :: c0, p, n
    n = len(tok)
    ok = .false.
    do c0 = min(1, merge(1, 0, n > 0 .and. tok(1:min(1,n)) == ":")), 0, -1
       do p = n, c0 + 2, -1
          if (tok(p:p) /= "/") cycle
          if (.not. ns_start(tok(c0+1:c0+1))) cycle
          if (.not. name_ok(tok(p+1:))) cycle
          ok = checks(tok(c0+1:p), tok(p+1:))
          return
       end do
       if (name_ok(tok(c0+1:))) then
          ok = checks("", tok(c0+1:))
          return
       end if
    end do
    ! String/1
    if (n >= 3) then
       if (tok(n-1:n-1) == "/" .and. index("123456789", tok(n:n)) > 0 .and. &
            ns_start(tok(1:1)) .and. tok(1:1) /= ":") ok = .true.
    end if
  contains
    logical function ns_start(c)
      character(len=1), intent(in) :: c
      ns_start = index("0123456789/", c) == 0
    end function ns_start
    logical function name_ok(s)
      character(len=*), intent(in) :: s
      if (s == "/" .and. len(s) == 1) then
         name_ok = .true.
      else
         name_ok = len(s) >= 1
         if (name_ok) name_ok = ns_start(s(1:1)) .and. index(s, "/") == 0
      end if
    end function name_ok
    logical function checks(ns, nm)
      character(len=*), intent(in) :: ns, nm
      checks = .true.
      if (len(ns) >= 2) then
         if (ns(len(ns)-1:) == ":/") checks = .false.
      end if
      if (nm(len(nm):len(nm)) == ":") checks = .false.
      if (len(tok) > 1) then
         if (index(tok(2:), "::") > 0) checks = .false.
      end if
    end function checks
  end function symbol_token_ok

  subroutine gcr_set_eval_reader(f)
    procedure(eval_reader_i) :: f
    eval_reader => f
  end subroutine gcr_set_eval_reader

  subroutine gcr_set_sq_expander(f)
    procedure(sq_expander_i) :: f
    sq_expander => f
  end subroutine gcr_set_sq_expander

  subroutine gcr_set_ns_resolver(f)
    procedure(ns_resolver_i) :: f
    ns_resolver => f
  end subroutine gcr_set_ns_resolver

  ! ---- number recognition ----
  !
  ! Clojure's reader decides this with three regexes -- LispReader
  ! lines 70-74 at clojure-1.12.6, the release the vendored core.clj
  ! comes from:
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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    yes = .false.
    val = gc_nil()
    n = len(s)
    if (n == 0) return
    start = 1
    if (s(1:1) == "-" .or. s(1:1) == "+") start = 2
    if (start > n) return
    if (n <= start) return
    ! NNrDIGITS: the digits run to the end, N among them (intPat's
    ! [0-9A-Za-z]+ is greedy), so 9r81N is not 9r81 and a suffix but a
    ! base-9 number with an N in it -- refused (36rZZN is 46643)
    block
      integer :: rp
      rp = scan(s(start:n), "rR")
      if (rp >= 2 .and. rp <= 3) then
         if (verify(s(start:start + rp - 2), "0123456789") == 0) return
      end if
    end block
    if (s(n:n) == "N") then
       ! 42N is a BigInt, of any size. A plain decimal keeps its own
       ! text; a radix or hex literal goes through parse_int first,
       ! which is where its value comes from.
       if (plain_decimal(s(1:n - 1))) then
          val = gc_big(s(1:n - 1), roots)
          yes = .true.
       else
          call parse_int(s(1:n - 1), iv, iok, iclaim)
          if (iok) then
             block
                call int_text(iv, s=dlt_1)
                val = gc_big(dlt_1, roots)
             end block
             yes = .true.
          end if
       end if
    else if (s(n:n) == "M") then
       ! 1.0M is a BigDecimal, and the literal's own text decides its
       ! scale: 1M, 1.0M and 1.00M are three different decimals.
       block
         character(len=:), allocatable :: dv
         logical :: dok
         call dec_from_text(s(1:n - 1), dv, dok)
         if (dok) then
            val = gc_dec(dv, roots)
            yes = .true.
         end if
       end block
    end if
    if (.false.) val = gc_sym(s, roots)
  end function suffixed_number

  pure subroutine int_text(i, s)
    integer(gc_ip), intent(in) :: i
    character(len=:), allocatable, intent(out) :: s
    call gc_int_text(i, s)
  end subroutine int_text

  ! ratioPat: ([-+]?[0-9]+)/([0-9]+). A denominator of zero is an
  ! error, the same as (/ 1 0) -- Clojure raises rather than reading
  ! it, and gc_ratio would answer nil.
  subroutine parse_ratio(s, val, ok, claim, roots)
    character(len=*), intent(in) :: s
    type(gc_value), intent(out) :: val
    logical, intent(out) :: ok, claim
    type(gc_value), intent(in) :: roots(:)
    character(len=:), allocatable :: nt, dt
    integer :: n, start, k, slash
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
    ! parts of any size, reduced to the one form a value has (gc_rat_make):
    ! 4/2 reads as 2 and 99999999999999999999/7 as itself, as clj's
    ! reader reduces them; a ratio's parts had been 64-bit, the
    ! denominator 32 (DEVIATIONS 26)
    call big_norm(s(start:slash - 1), o=nt)
    call big_norm(s(slash + 1:n), o=dt)
    if (dt == "0") then
       ! the reader divides the parts, as matchNumber does: 1/0 throws
       call fail("Divide by zero", "clotran.host.arithmetic_exception")
       return
    end if
    if (neg) nt = "-" // nt
    val = gc_rat_make(nt, dt, .false., roots)
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

  ! [-+]?[0-9]+ and nothing else: the shape whose VALUE is its own
  ! text, so a BigInt can be made from it without parsing.
  pure function plain_decimal(s) result(yes)
    character(len=*), intent(in) :: s
    logical :: yes
    integer :: start
    yes = .false.
    start = 1
    if (len(s) >= 1) then
       if (s(1:1) == "-" .or. s(1:1) == "+") start = 2
    end if
    if (len(s) < start) return
    ! a single leading zero is octal in Clojure, not decimal
    if (len(s) > start .and. s(min(start, len(s)):min(start, len(s))) == "0") return
    yes = all_decimal(s(start:))
  end function plain_decimal

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
    logical :: ok
    call text_double(s, r, ok)
    if (.not. ok) r = 0.0_gc_dp
  end function to_real

  function with(roots, v) result(out)
    type(gc_value), intent(in) :: roots(:), v
    type(gc_value), allocatable :: out(:)
    allocate(out(size(roots) + 1))
    out(1:size(roots)) = roots
    out(size(roots) + 1) = v
  end function with

end module LispReader
