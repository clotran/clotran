! GCPrinter: values in the GC heap, back to text.
!
! Built and tested standalone -- nothing uses it yet. See PLAN.md
! 3c-2/3d.
!
! Written now, before the evaluator switch, for two reasons beyond
! eventually needing it:
!
!   1. It is the first thing that walks EVERY structure in the new
!      data layer at once -- list, vector, both map representations,
!      text, immediates. A representation mistake that each module's
!      own tests miss shows up here immediately.
!   2. Debugging the switch without being able to print a value would
!      be miserable.
!
! `readable` mirrors clotran's existing printer (pr-str versus
! print-str): readable escapes strings and prints characters as \a,
! not-readable writes their contents raw. That distinction is real
! Clojure's, and getting it wrong is how (println "a\nb") starts
! printing quotes.
module GCPrinter
  use GC
  use GCList
  use GCVector
  use GCAssoc
  implicit none
  private

  ! Realising a lazy seq means CALLING its thunk, and only the
  ! evaluator can call anything -- but the evaluator sits above this
  ! module, so it cannot be called from here directly. The evaluator
  ! hands its forcer down at startup instead, exactly the dependency
  ! inversion clotran's own rt_set_lazy_forcer already uses.
  !
  ! It must be a MODULE procedure, not an internal one: flang
  ! segfaults passing a host-associated internal procedure as a
  ! callback on macOS/ARM64 (NOTES.md), which is also rule 5 of the
  ! native-buffer rules in PLAN.md.
  abstract interface
     subroutine forcer_i(v)
       import :: gc_value
       type(gc_value), intent(in) :: v
     end subroutine forcer_i
  end interface
  procedure(forcer_i), pointer, save :: lazy_forcer => null()

  public :: gcp_str, gcp_set_forcer

contains

  subroutine gcp_set_forcer(f)
    procedure(forcer_i) :: f
    lazy_forcer => f
  end subroutine gcp_set_forcer

  recursive function gcp_str(v, readable) result(s)
    type(gc_value), intent(in) :: v
    logical, intent(in) :: readable
    character(len=:), allocatable :: s
    character(len=32) :: buf

    select case (v%tag)
    case (GCT_NIL)
       s = "nil"
    case (GCT_BOOL)
       if (v%ival /= 0) then
          s = "true"
       else
          s = "false"
       end if
    case (GCT_INT)
       write(buf, '(I0)') v%ival
       s = trim(buf)
    case (GCT_REAL)
       s = real_str(v%rval)
    case (GCT_CHAR)
       if (readable) then
          s = char_readable(v%ival)
       else
          s = achar(v%ival)
       end if
    case (GCT_STR)
       if (readable) then
          s = quoted(gc_ref_text(v%ref))
       else
          s = gc_ref_text(v%ref)
       end if
    case (GCT_SYM)
       s = gc_ref_text(v%ref)
    case (GCT_KEY)
       s = ":" // gc_ref_text(v%ref)
    case default
       s = obj_str(v, readable)
    end select
  end function gcp_str

  recursive function obj_str(v, readable) result(s)
    type(gc_value), intent(in) :: v
    logical, intent(in) :: readable
    character(len=:), allocatable :: s
    type(gc_value) :: p
    type(gc_value), allocatable :: keys(:), vals(:)
    integer :: i, n
    type(gc_value) :: none(0)

    select case (gc_kind(v))
    case (OBJ_CONS)
       s = "("
       p = v
       i = 0
       do while (gcl_is(p) .and. gcl_count(p) > 0)
          if (i > 0) s = s // " "
          s = s // gcp_str(gcl_first(p), readable)
          p = gcl_rest(p, none)
          i = i + 1
       end do
       s = s // ")"
    case (OBJ_VECTOR)
       s = "["
       n = gcv_count(v)
       do i = 0, n - 1
          if (i > 0) s = s // " "
          s = s // gcp_str(gcv_nth(v, i), readable)
       end do
       s = s // "]"
    case (OBJ_MAP, OBJ_HAMT)
       ! Both representations print identically -- which is the point
       ! of the promotion being invisible. A map that printed
       ! differently once it crossed 8 entries would be a leak of the
       ! implementation into the language.
       call gca_entries(v, keys, vals)
       s = "{"
       do i = 1, size(keys)
          if (i > 1) s = s // ", "
          s = s // gcp_str(keys(i), readable) // " " // gcp_str(vals(i), readable)
       end do
       s = s // "}"
    case (OBJ_LAZY)
       ! Printing a lazy seq realises it, one cell at a time, which is
       ! what real Clojure does too -- printing is a use, and a use
       ! forces. An unrealised seq with no forcer registered prints as
       ! a marker rather than lying about being empty.
       if (.not. associated(lazy_forcer)) then
          s = "#<lazy>"
          return
       end if
       s = "("
       p = v
       i = 0
       do
          call lazy_forcer(p)
          if (gc_i1(p) /= LAZY_CONS) exit
          if (i > 0) s = s // " "
          s = s // gcp_str(gc_slot(p, 2), readable)
          p = gc_slot(p, 3)
          i = i + 1
          if (.not. (gc_kind(p) == OBJ_LAZY)) then
             ! The tail became a concrete seq: print the rest of it
             ! inside these same parens rather than nesting.
             if (gc_kind(p) == OBJ_CONS) then
                do while (gcl_count(p) > 0)
                   s = s // " " // gcp_str(gcl_first(p), readable)
                   p = gcl_rest(p, none)
                end do
             end if
             exit
          end if
       end do
       s = s // ")"
    case (OBJ_CLOSURE)
       s = "#<fn>"
    case (OBJ_ATOM)
       s = "#<atom " // gcp_str(gc_slot(v, 1), readable) // ">"
    case (OBJ_ENV)
       s = "#<env>"
    case default
       s = "#<object>"
    end select
  end function obj_str

  ! Trailing zeros trimmed but always at least one decimal, so a
  ! double prints as 2.0 rather than 2 -- otherwise it reads back as an
  ! integer, which is a round-trip failure rather than a cosmetic one.
  function real_str(r) result(s)
    real(gc_dp), intent(in) :: r
    character(len=:), allocatable :: s
    character(len=32) :: buf
    integer :: i
    write(buf, '(F0.10)') r
    s = trim(buf)
    i = len(s)
    do while (i > 1)
       if (s(i:i) /= "0") exit
       if (s(i-1:i-1) == ".") exit
       i = i - 1
    end do
    s = s(1:i)
    if (s(1:1) == ".") s = "0" // s
  end function real_str

  function quoted(t) result(s)
    character(len=*), intent(in) :: t
    character(len=:), allocatable :: s
    integer :: i
    s = '"'
    do i = 1, len(t)
       select case (t(i:i))
       case ('"');       s = s // '\"'
       case (achar(92)); s = s // achar(92) // achar(92)
       case (achar(10)); s = s // achar(92) // "n"
       case (achar(9));  s = s // achar(92) // "t"
       case default;     s = s // t(i:i)
       end select
    end do
    s = s // '"'
  end function quoted

  ! The named characters, matching real Clojure's reader so what is
  ! printed can be read back.
  function char_readable(code) result(s)
    integer, intent(in) :: code
    character(len=:), allocatable :: s
    select case (code)
    case (10); s = achar(92) // "newline"
    case (32); s = achar(92) // "space"
    case (9);  s = achar(92) // "tab"
    case (13); s = achar(92) // "return"
    case (8);  s = achar(92) // "backspace"
    case (12); s = achar(92) // "formfeed"
    case default; s = achar(92) // achar(code)
    end select
  end function char_readable

end module GCPrinter
