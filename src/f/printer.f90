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
  use PersistentArrayMap, only: array_map_entries
  use Atom, only: atom_deref
  use NativeArray, only: array_elem_string
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
    case (TAG_CHAR)
       if (r) then
          str = stringify_char(v%str_val)
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
    case (TAG_SET)
       str = pr_hashset(v, r)
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
    case (TAG_VAR)
       str = "#'" // v%str_val
    case (TAG_MULTIFN)
       str = "#<multifn>"
    case (TAG_ARRAY)
       ! Kind and shape, which is what identifies a Fortran array --
       ! contents come out through seq/vec like any other collection.
       str = "#<" // array_elem_string(v) // ">"
    case (TAG_STRING_BUILDER)
       ! What (str sb) has to give back -- with-out-str reads its
       ! StringWriter that way, and a builder's "value" is its text.
       block
         type(cons_value) :: held ! not atom_deref(v)%str_val -- see NOTES.md
         held = atom_deref(v)
         str = ""
         if (allocated(held%str_val)) str = held%str_val
       end block
    case (TAG_REDUCED)
       str = "#<reduced " // pr_str(atom_deref(v), r) // ">"
    case (TAG_LAZYSEQ)
       ! Printing realizes the whole seq, same as real Clojure without
       ! *print-length* -- printing an infinite one doesn't terminate
       ! there either.
       str = pr_seq(v, "(", ")", r)
    case default
       str = "nil"
    end select
  end function pr_str

  recursive function pr_hashmap(v, readable) result(str)
    type(cons_value), intent(in) :: v
    logical, intent(in) :: readable
    character(len=:), allocatable :: str
    character(len=:), allocatable :: key_str, val_str
    type(cons_value), allocatable :: keys(:), vals(:)
    integer :: i

    str = "{"
    if (allocated(v%map_val)) then
       call array_map_entries(v%map_val, keys, vals)
       do i = 1, size(keys)
          if (i > 1) str = str // " "
          ! Two recursive, deferred-length pr_str calls chained into one
          ! concatenation corrupts memory on gfortran (not flang) --
          ! materializing each result into its own variable first avoids it.
          key_str = pr_str(keys(i), readable)
          val_str = pr_str(vals(i), readable)
          str = str // key_str // " " // val_str
       end do
    end if
    str = str // "}"
  end function pr_hashmap

  recursive function pr_hashset(v, readable) result(str)
    type(cons_value), intent(in) :: v
    logical, intent(in) :: readable
    character(len=:), allocatable :: str
    character(len=:), allocatable :: elem_str
    type(cons_value), allocatable :: keys(:), discard(:)
    integer :: i

    str = "#{"
    if (allocated(v%map_val)) then
       call array_map_entries(v%map_val, keys, discard)
       do i = 1, size(keys)
          if (i > 1) str = str // " "
          elem_str = pr_str(keys(i), readable)
          str = str // elem_str
       end do
    end if
    str = str // "}"
  end function pr_hashset

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
    ! A lazy seq stays a lazy seq as it's walked (next realizes one
    ! cell at a time), so the loop has to accept both shapes.
    do while (s%tag == TAG_LIST .or. s%tag == TAG_LAZYSEQ)
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

  ! F0.2 drops the leading zero on a value below 1 (".50", "-.50"),
  ! which is not how Clojure -- or Fortran source -- writes a number.
  ! Put it back.
  function stringify_real(r) result(str)
    real(dp), intent(in) :: r
    character(len=:), allocatable :: str
    character(20) :: temp
    write(temp, '(F0.2)') r
    str = trim(adjustl(temp))
    if (len(str) > 0) then
       if (str(1:1) == ".") then
          str = "0" // str
       else if (len(str) > 1 .and. str(1:1) == "-") then
          if (str(2:2) == ".") str = "-0" // str(2:)
       end if
    end if
  end function stringify_real

  ! The inverse of the reader's read_char_literal: the named forms
  ! print by name, everything else as the bare character after a '\'.
  function stringify_char(c) result(str)
    character(len=:), allocatable, intent(in) :: c
    character(len=:), allocatable :: str
    character :: ch

    if (.not. allocated(c)) then
       str = achar(92) // "space"
       return
    end if
    ch = c(1:1)
    select case (ch)
    case (achar(10))
       str = achar(92) // "newline"
    case (" ")
       str = achar(92) // "space"
    case (achar(9))
       str = achar(92) // "tab"
    case (achar(13))
       str = achar(92) // "return"
    case (achar(12))
       str = achar(92) // "formfeed"
    case (achar(8))
       str = achar(92) // "backspace"
    case default
       str = achar(92) // ch
    end select
  end function stringify_char

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
