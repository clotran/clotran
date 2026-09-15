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
! DEFERRED, and listed rather than silently missing: metadata (^),
! the discard macro (#_), sets (#{}), regex literals, syntax-quote
! expansion and auto-gensym. Those are reader MACROS layered on the
! core shapes; the shapes are what the data layer needs proving.
module GCReader
  use GC
  use GCList
  use GCVector
  use GCAssoc
  implicit none
  private

  character(len=:), allocatable :: last_error
  logical :: has_error = .false.

  public :: gcr_read, gcr_error, gcr_has_error

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
