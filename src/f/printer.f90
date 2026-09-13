! pr_str: cons_value -> printed text. Mirrors clojure.core's pr-str.
! readable (optional, default true) distinguishes pr-str/prn's
! *print-readably* mode (strings quoted/escaped, round-trips through
! the reader) from str/println's "display" mode (a string's own raw
! text) -- real Clojure's two printing conventions. Only strings
! differ between the two; everything else (numbers, keywords, nil,
! ...) prints the same either way. Nested elements (list/vector/map/
! atom contents) always follow the same mode as the top-level call.
module printer
  use values
  use RT, only: seq, first, next
  use PersistentArrayMap, only: array_map_count, array_map_nth_key, array_map_nth_val
  use Atom, only: atom_deref
  implicit none
  private

  public :: pr_str

contains

  recursive function pr_str(v, readable) result(str)
    type(cons_value), intent(in) :: v
    logical, intent(in), optional :: readable
    character(len=:), allocatable :: str
    logical :: r

    r = .true.
    if (present(readable)) r = readable

    select case (v%tag)
    case (TAG_NIL)
       str = "nil"
    case (TAG_BOOL)
       if (v%bool_val) then
          str = "true"
       else
          str = "false"
       end if
    case (TAG_INT)
       str = stringify_int(v%int_val)
    case (TAG_REAL)
       str = stringify_real(v%real_val)
    case (TAG_STRING)
       if (r) then
          str = stringify_string(v%str_val)
       else
          str = v%str_val
       end if
    case (TAG_SYMBOL)
       str = v%str_val
    case (TAG_KEYWORD)
       str = ':' // v%str_val
    case (TAG_LIST)
       str = pr_seq(v, "(", ")", r)
    case (TAG_VECTOR)
       str = pr_seq(v, "[", "]", r)
    case (TAG_HASHMAP)
       str = pr_hashmap(v, r)
    case (TAG_BUILTIN)
       str = "#<builtin " // v%str_val // ">"
    case (TAG_FN)
       if (allocated(v%fn_val)) then
          if (v%fn_val%is_macro) then
             str = "#<macro>"
          else
             str = "#<fn>"
          end if
       else
          str = "#<fn>"
       end if
    case (TAG_ATOM)
       str = "(atom " // pr_str(atom_deref(v), r) // ")"
    case default
       str = "nil"
    end select
  end function pr_str

  recursive function pr_hashmap(v, readable) result(str)
    type(cons_value), intent(in) :: v
    logical, intent(in) :: readable
    character(len=:), allocatable :: str
    character(len=:), allocatable :: key_str, val_str
    integer :: i, n

    str = "{"
    if (allocated(v%map_val)) then
       n = array_map_count(v%map_val)
       do i = 0, n - 1
          if (i > 0) str = str // " "
          ! Two recursive, deferred-length pr_str calls chained into one
          ! concatenation corrupts memory on gfortran (not flang) --
          ! materializing each result into its own variable first avoids it.
          key_str = pr_str(array_map_nth_key(v%map_val, i), readable)
          val_str = pr_str(array_map_nth_val(v%map_val, i), readable)
          str = str // key_str // " " // val_str
       end do
    end if
    str = str // "}"
  end function pr_hashmap

  recursive function pr_seq(v, open, close, readable) result(str)
    type(cons_value), intent(in) :: v
    character(len=*), intent(in) :: open, close
    logical, intent(in) :: readable
    character(len=:), allocatable :: str
    type(cons_value) :: s
    logical :: is_first

    str = open
    is_first = .true.
    s = seq(v)
    do while (s%tag == TAG_LIST)
       if (.not. is_first) str = str // " "
       str = str // pr_str(first(s), readable)
       is_first = .false.
       s = next(s)
    end do
    str = str // close
  end function pr_seq

  function stringify_int(i) result(str)
    integer, intent(in) :: i
    character(len=:), allocatable :: str
    character(20) :: temp
    write(temp, '(I0)') i
    str = trim(adjustl(temp))
  end function stringify_int

  function stringify_real(r) result(str)
    real(dp), intent(in) :: r
    character(len=:), allocatable :: str
    character(20) :: temp
    write(temp, '(F0.2)') r
    str = trim(adjustl(temp))
  end function stringify_real

  function stringify_string(c) result(str)
    character(len=:), allocatable, intent(in) :: c
    character(len=:), allocatable :: str
    integer :: i, n
    n = 0
    if (allocated(c)) n = len(c)
    str = '"'
    do i = 1, n
       select case (c(i:i))
       case ('"')
          str = str // '\"'
       case (achar(92)) ! backslash
          str = str // '\\'
       case (achar(10)) ! newline
          str = str // '\n'
       case default
          str = str // c(i:i)
       end select
    end do
    str = str // '"'
  end function stringify_string

end module printer
