! NativeArray: a REAL Fortran array as a clotran value.
!
! Deliberately not a port of java.lang.Object[] -- emulating the JVM's
! array would throw away the only thing this host has that the JVM
! does not, namely that the bytes ARE a Fortran array and can be handed
! to a Fortran library directly.
!
! Generic over kind AND rank:
!
!   kind  the payload is class(*), allocatable :: buf(:), allocated
!         with an explicit type-spec, so real(8)/real(4)/integer(4)/
!         integer(8)/complex(8)/logical all use one type. Same
!         mechanism native_test already validates for scalars and
!         structs.
!
!   rank  one rank-1 contiguous buffer plus a shape, with the index
!         arithmetic done here. Rank is part of a Fortran type
!         declaration, so a derived-type component cannot be "any
!         rank"; doing the arithmetic ourselves is what makes every
!         rank work rather than a hand-written case per rank. The
!         layout is column-major, which is Fortran's own, so the
!         buffer is bit-identical to what a Fortran routine expects.
!
! Lower bounds are stored per dimension. A Fortran array may start at
! any index, so a Clojure-facing array simply starts at 0 (what aget
! promises) and an imported Fortran one keeps the bounds it was
! declared with -- no translation layer and no convention to remember.
module NativeArray
  use values
  implicit none
  private

  public :: array_new, array_aget, array_aset, array_length, array_shape_list, &
       array_rank, array_kind_name, array_is, array_kind_of_value, array_elem_string

contains

  function array_is(v) result(yes)
    type(cons_value), intent(in) :: v
    logical :: yes
    yes = (v%tag == TAG_ARRAY)
    if (yes) yes = allocated(v%array_val)
    if (yes) yes = associated(v%array_val%ptr)
  end function array_is

  ! The kind name a value would naturally live in, so that
  ! (into-array [1 2 3]) picks something sensible without being told.
  function array_kind_of_value(v) result(kind_name)
    type(cons_value), intent(in) :: v
    character(len=:), allocatable :: kind_name
    select case (v%tag)
    case (TAG_INT);  kind_name = "int4"
    case (TAG_REAL); kind_name = "real8"
    case (TAG_BOOL); kind_name = "logical"
    case default;    kind_name = "value" ! a clotran value, not a Fortran scalar
    end select
  end function array_kind_of_value

  ! Allocates the buffer with an explicit type-spec per kind. "value"
  ! is the escape hatch: an array of clotran values (what plain
  ! (into-array [:a "b"]) needs), still contiguous, just not something
  ! a Fortran library would accept.
  function array_new(kind_name, extents, lows, err) result(val)
    character(len=*), intent(in) :: kind_name
    integer, intent(in) :: extents(:), lows(:)
    character(len=:), allocatable, intent(out) :: err
    type(cons_value) :: val
    type(native_array_node), pointer :: node
    integer :: total, i

    err = ""
    total = 1
    do i = 1, size(extents)
       if (extents(i) < 0) then
          err = "make-array: negative extent"
          return
       end if
       total = total * extents(i)
    end do

    allocate(node)
    node%refcount = 1
    node%elem_kind = kind_name
    node%extents = extents
    node%lows = lows
    native_array_node_total_allocated = native_array_node_total_allocated + 1

    select case (kind_name)
    case ("real8");   allocate(real(dp)    :: node%buf(total))
    case ("real4");   allocate(real(4)     :: node%buf(total))
    case ("int4");    allocate(integer(4)  :: node%buf(total))
    case ("int8");    allocate(integer(8)  :: node%buf(total))
    case ("logical"); allocate(logical     :: node%buf(total))
    case ("complex8");allocate(complex(dp) :: node%buf(total))
    case ("value");   allocate(cons_value  :: node%buf(total))
    case default
       deallocate(node)
       native_array_node_total_allocated = native_array_node_total_allocated - 1
       err = "make-array: unknown element kind '" // kind_name // "'"
       return
    end select
    call zero_fill(node)

    val%tag = TAG_ARRAY
    allocate(val%array_val)
    val%array_val%ptr => node
  end function array_new

  ! Fortran leaves a fresh allocation undefined; Clojure's make-array
  ! promises zeros (and nil for a value array), so fill explicitly.
  subroutine zero_fill(node)
    type(native_array_node), pointer, intent(in) :: node
    select type (b => node%buf)
    type is (real(dp));    b = 0.0_dp
    type is (real(4));     b = 0.0_4
    type is (integer(4));  b = 0_4
    type is (integer(8));  b = 0_8
    type is (logical);     b = .false.
    type is (complex(dp)); b = (0.0_dp, 0.0_dp)
    end select
  end subroutine zero_fill

  function array_rank(v) result(r)
    type(cons_value), intent(in) :: v
    integer :: r
    r = 0
    if (array_is(v)) r = size(v%array_val%ptr%extents)
  end function array_rank

  function array_kind_name(v) result(kind_name)
    type(cons_value), intent(in) :: v
    character(len=:), allocatable :: kind_name
    kind_name = ""
    if (array_is(v)) kind_name = v%array_val%ptr%elem_kind
  end function array_kind_name

  ! Total element count, across every dimension -- what alength reports
  ! for a rank-1 array and what `count` means for any of them.
  function array_length(v) result(n)
    type(cons_value), intent(in) :: v
    integer :: n
    integer :: i
    n = 0
    if (.not. array_is(v)) return
    n = 1
    do i = 1, size(v%array_val%ptr%extents)
       n = n * v%array_val%ptr%extents(i)
    end do
  end function array_length

  function array_shape_list(v) result(extents)
    type(cons_value), intent(in) :: v
    integer, allocatable :: extents(:)
    if (array_is(v)) then
       extents = v%array_val%ptr%extents
    else
       allocate(extents(0))
    end if
  end function array_shape_list

  ! Column-major, the same order Fortran itself stores in: the first
  ! subscript varies fastest. Returns 0 when any subscript is out of
  ! bounds, which callers report rather than reading past the buffer.
  function linear_index(node, idx) result(pos)
    type(native_array_node), pointer, intent(in) :: node
    integer, intent(in) :: idx(:)
    integer :: pos
    integer :: d, offset, stride

    pos = 0
    if (size(idx) /= size(node%extents)) return
    offset = 0
    stride = 1
    do d = 1, size(idx)
       if (idx(d) < node%lows(d)) return
       if (idx(d) > node%lows(d) + node%extents(d) - 1) return
       offset = offset + (idx(d) - node%lows(d)) * stride
       stride = stride * node%extents(d)
    end do
    pos = offset + 1
  end function linear_index

  function array_aget(v, idx, err) result(out)
    type(cons_value), intent(in) :: v
    integer, intent(in) :: idx(:)
    character(len=:), allocatable, intent(out) :: err
    type(cons_value) :: out
    integer :: pos

    err = ""
    if (.not. array_is(v)) then
       err = "aget: not an array"
       return
    end if
    pos = linear_index(v%array_val%ptr, idx)
    if (pos == 0) then
       err = "aget: index out of bounds"
       return
    end if
    select type (b => v%array_val%ptr%buf)
    type is (real(dp));    out%tag = TAG_REAL; out%real_val = b(pos)
    type is (real(4));     out%tag = TAG_REAL; out%real_val = real(b(pos), dp)
    type is (integer(4));  out%tag = TAG_INT;  out%int_val = int(b(pos))
    type is (integer(8));  out%tag = TAG_INT;  out%int_val = int(b(pos))
    type is (logical);     out%tag = TAG_BOOL; out%bool_val = b(pos)
    type is (complex(dp)); out%tag = TAG_REAL; out%real_val = real(b(pos), dp)
    type is (cons_value);  out = b(pos)
    class default
       err = "aget: unsupported element kind"
    end select
  end function array_aget

  ! Mutates in place: an array is a genuinely mutable slot shared by
  ! reference, like an Atom, which is what aset means in Clojure too.
  subroutine array_aset(v, idx, new_val, err)
    type(cons_value), intent(in) :: v
    integer, intent(in) :: idx(:)
    type(cons_value), intent(in) :: new_val
    character(len=:), allocatable, intent(out) :: err
    integer :: pos

    err = ""
    if (.not. array_is(v)) then
       err = "aset: not an array"
       return
    end if
    pos = linear_index(v%array_val%ptr, idx)
    if (pos == 0) then
       err = "aset: index out of bounds"
       return
    end if
    select type (b => v%array_val%ptr%buf)
    type is (real(dp));    b(pos) = as_real(new_val)
    type is (real(4));     b(pos) = real(as_real(new_val), 4)
    type is (integer(4));  b(pos) = int(as_int(new_val), 4)
    type is (integer(8));  b(pos) = int(as_int(new_val), 8)
    type is (logical);     b(pos) = .not. (new_val%tag == TAG_NIL .or. &
                                (new_val%tag == TAG_BOOL .and. .not. new_val%bool_val))
    type is (complex(dp)); b(pos) = cmplx(as_real(new_val), 0.0_dp, dp)
    type is (cons_value);  b(pos) = new_val
    class default
       err = "aset: unsupported element kind"
    end select
  end subroutine array_aset

  function as_real(v) result(r)
    type(cons_value), intent(in) :: v
    real(dp) :: r
    r = 0.0_dp
    if (v%tag == TAG_REAL) r = v%real_val
    if (v%tag == TAG_INT) r = real(v%int_val, dp)
  end function as_real

  function as_int(v) result(i)
    type(cons_value), intent(in) :: v
    integer :: i
    i = 0
    if (v%tag == TAG_INT) i = v%int_val
    if (v%tag == TAG_REAL) i = int(v%real_val)
  end function as_int

  ! "#<real8[2 3]>" -- kind and shape, which is what actually
  ! identifies a Fortran array. The contents print through the ordinary
  ! seq path (see printer.f90).
  function array_elem_string(v) result(s)
    type(cons_value), intent(in) :: v
    character(len=:), allocatable :: s
    character(len=16) :: buf
    integer :: d
    s = ""
    if (.not. array_is(v)) return
    s = v%array_val%ptr%elem_kind // "["
    do d = 1, size(v%array_val%ptr%extents)
       if (d > 1) s = s // " "
       write(buf, '(I0)') v%array_val%ptr%extents(d)
       s = s // trim(buf)
    end do
    s = s // "]"
  end function array_elem_string

end module NativeArray
