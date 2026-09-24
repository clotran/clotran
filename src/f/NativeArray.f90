! NativeArray: a REAL Fortran array as a clotran value, on the GC heap.
!
! Deliberately not a port of java.lang.Object[]. Emulating the JVM's
! array would throw away the one thing this host has that the JVM does
! not: the bytes ARE a Fortran array and can be handed to a Fortran
! library directly.
!
! WHY A REGISTRY RATHER THAN THE HEAP. gc_value has four scalar
! components and no pointer, which is the whole reason copying one is
! cheap; a pool of them cannot hold real(8), and a buffer that lived in
! a pool could not be handed to dgemm anyway. So the buffer lives here,
! in a module array that nothing moves, and the object holds an integer
! HANDLE -- exactly what Regex.f90 does with an ICU pattern, and the
! reason PLAN.md insists the collector be non-moving.
!
! Generic over kind AND rank, unchanged from the original reasoning:
!
!   kind  the payload is class(*), allocatable :: buf(:), allocated
!         with an explicit type-spec, so real8/real4/int4/int8/
!         complex8/logical all use one type.
!
!   rank  one rank-1 contiguous buffer plus a shape, with the index
!         arithmetic done here. Rank is part of a Fortran type
!         declaration, so a derived-type component cannot be "any
!         rank"; doing the arithmetic ourselves is what makes every
!         rank work rather than a hand-written case per rank. The
!         layout is COLUMN-MAJOR, Fortran's own, so the buffer is
!         bit-identical to what a Fortran routine expects.
!
! Lower bounds are per dimension. A Fortran array may start at any
! index, so a Clojure-facing array starts at 0 (what aget promises) and
! an imported Fortran one keeps the bounds it was declared with -- no
! translation layer and no convention to remember.
!
! THE `value` KIND IS DIFFERENT and does not live here. Its elements
! are clotran values, which hold heap references, so they must be
! TRACED or the collector frees them out from under the array. Those go
! in a GC run in the object's slot 1, which push_mark already walks.
! This registry then owns only buffers the collector has no opinion
! about.
module NativeArray
  use GC
  implicit none
  private

  integer, parameter :: dp = gc_dp

  ! One live array. `used` is false for a slot whose object has been
  ! collected -- gcna_release puts it back, driven by the sweep.
  type :: na_node
     logical :: used = .false.
     character(len=:), allocatable :: elem_kind
     integer, allocatable :: extents(:)
     integer, allocatable :: lows(:)
     class(*), allocatable :: buf(:)
  end type na_node

  ! target: a binding takes a POINTER into a buffer for the length of
  ! one call (gcna_real8_ptr); claim() must not reallocate `reg` while
  ! such a pointer is live, and it cannot, since the routine on the
  ! other end allocates no clotran arrays.
  type(na_node), allocatable, save, target :: reg(:)
  integer, save :: reg_used = 0

  public :: gcna_new, gcna_release, gcna_reset, gcna_is, gcna_kind, gcna_rank, &
       gcna_extents, gcna_lows, gcna_total, gcna_index, &
       gcna_get_real, gcna_get_int, gcna_get_logical, &
       gcna_set_real, gcna_set_int, gcna_set_logical, gcna_elem_string, &
       gcna_live_count, gcna_real8_ptr, gcna_int4_ptr, gcna_int8_ptr

contains

  ! A contiguous pointer to a real8 buffer, or ok = false. This is how
  ! a binding hands a clotran array to a routine declared over `x(*)`
  ! or `x(3,*)`: sequence association over the pointer, no copy.
  subroutine gcna_real8_ptr(handle, p, ok)
    integer, intent(in) :: handle
    real(dp), pointer, contiguous, intent(out) :: p(:)
    logical, intent(out) :: ok
    ok = .false.
    p => null()
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (real(dp))
       p => b
       ok = .true.
    end select
  end subroutine gcna_real8_ptr

  ! The same for an int8 buffer, which is what long-array makes.
  subroutine gcna_int8_ptr(handle, p, ok)
    integer, intent(in) :: handle
    integer(8), pointer, contiguous, intent(out) :: p(:)
    logical, intent(out) :: ok
    ok = .false.
    p => null()
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (integer(8))
       p => b
       ok = .true.
    end select
  end subroutine gcna_int8_ptr

  subroutine gcna_int4_ptr(handle, p, ok)
    integer, intent(in) :: handle
    integer, pointer, contiguous, intent(out) :: p(:)
    logical, intent(out) :: ok
    ok = .false.
    p => null()
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (integer(4))
       p => b
       ok = .true.
    end select
  end subroutine gcna_int4_ptr

  ! C = A x B through the reference BLAS, the first Fortran routine
  ! clotran calls. The three buffers are `real(dp)` here and go to
  ! DGEMM as the `A(LDA,*)` it declares -- sequence association over a
  ! contiguous buffer, no copy, no descriptor. The caller has checked
  ! the kinds and the shapes; this only refuses what would corrupt
  ! memory, since xerbla would STOP the process.

  ! Claims a registry slot and allocates the buffer. Returns the
  ! HANDLE, or 0 with err set.
  !
  ! `value` is accepted as a kind but allocates no buffer: its storage
  ! is the caller's GC run. Everything else about it -- shape, bounds,
  ! indexing -- is identical, which is the point of keeping one node
  ! type for both.
  function gcna_new(kind_name, extents, lows, err) result(handle)
    character(len=*), intent(in) :: kind_name
    integer, intent(in) :: extents(:), lows(:)
    character(len=:), allocatable, intent(out) :: err
    integer :: handle, total, i

    err = ""
    handle = 0
    total = 1
    do i = 1, size(extents)
       if (extents(i) < 0) then
          err = "make-array: negative extent"
          return
       end if
       total = total * extents(i)
    end do

    handle = claim()
    reg(handle)%elem_kind = kind_name
    reg(handle)%extents = extents
    reg(handle)%lows = lows

    select case (kind_name)
    case ("real8");    allocate(real(dp)     :: reg(handle)%buf(total))
    case ("real4");    allocate(real(4)      :: reg(handle)%buf(total))
    case ("int4");     allocate(integer(4)   :: reg(handle)%buf(total))
    case ("int8");     allocate(integer(8)   :: reg(handle)%buf(total))
    case ("logical");  allocate(logical      :: reg(handle)%buf(total))
    case ("complex8"); allocate(complex(dp)  :: reg(handle)%buf(total))
    case ("value")     ! storage is a GC run, held by the caller
    case default
       call gcna_release(handle)
       handle = 0
       err = "make-array: unknown element kind '" // kind_name // "'"
       return
    end select
    call zero_fill(handle)
  end function gcna_new

  ! Called by the sweep, through the finalizer hook, when the object
  ! holding this handle is collected. Idempotent: the sweep can only
  ! reach a given object once, but a handle of 0 or a stale index must
  ! not be an error.
  subroutine gcna_release(handle)
    integer, intent(in) :: handle
    if (.not. allocated(reg)) return
    if (handle < 1 .or. handle > reg_used) return
    if (.not. reg(handle)%used) return
    if (allocated(reg(handle)%buf)) deallocate(reg(handle)%buf)
    if (allocated(reg(handle)%extents)) deallocate(reg(handle)%extents)
    if (allocated(reg(handle)%lows)) deallocate(reg(handle)%lows)
    if (allocated(reg(handle)%elem_kind)) deallocate(reg(handle)%elem_kind)
    reg(handle)%used = .false.
  end subroutine gcna_release

  ! Drops EVERY entry. gc_init wipes the whole heap, so every
  ! OBJ_ARRAY that referred in here is gone and no sweep will ever
  ! report those handles -- they would be orphaned buffers, held for
  ! the life of the process. The evaluator calls this from
  ! gce_base_env, which is the one place that always follows a
  ! gc_init, because GC.f90 sits below this module and cannot call
  ! up into it.
  subroutine gcna_reset()
    integer :: i
    if (.not. allocated(reg)) return
    do i = 1, reg_used
       call gcna_release(i)
    end do
    reg_used = 0
  end subroutine gcna_reset

  logical function gcna_is(handle)
    integer, intent(in) :: handle
    gcna_is = .false.
    if (.not. allocated(reg)) return
    if (handle < 1 .or. handle > reg_used) return
    gcna_is = reg(handle)%used
  end function gcna_is

  ! How many registry slots are in use. For the tests: a collection
  ! that frees the object must free the buffer too, and this is what
  ! makes that observable.
  integer function gcna_live_count()
    integer :: i
    gcna_live_count = 0
    if (.not. allocated(reg)) return
    do i = 1, reg_used
       if (reg(i)%used) gcna_live_count = gcna_live_count + 1
    end do
  end function gcna_live_count

  function gcna_kind(handle) result(s)
    integer, intent(in) :: handle
    character(len=:), allocatable :: s
    s = ""
    if (gcna_is(handle)) s = reg(handle)%elem_kind
  end function gcna_kind

  integer function gcna_rank(handle)
    integer, intent(in) :: handle
    gcna_rank = 0
    if (gcna_is(handle)) gcna_rank = size(reg(handle)%extents)
  end function gcna_rank

  function gcna_extents(handle) result(e)
    integer, intent(in) :: handle
    integer, allocatable :: e(:)
    allocate(e(0))
    if (gcna_is(handle)) e = reg(handle)%extents
  end function gcna_extents

  function gcna_lows(handle) result(l)
    integer, intent(in) :: handle
    integer, allocatable :: l(:)
    allocate(l(0))
    if (gcna_is(handle)) l = reg(handle)%lows
  end function gcna_lows

  ! Total element count -- alength for rank 1, and the size of the
  ! flat buffer for any rank.
  integer function gcna_total(handle)
    integer, intent(in) :: handle
    integer :: i
    gcna_total = 0
    if (.not. gcna_is(handle)) return
    gcna_total = 1
    do i = 1, size(reg(handle)%extents)
       gcna_total = gcna_total * reg(handle)%extents(i)
    end do
  end function gcna_total

  ! COLUMN-MAJOR flat index from per-dimension subscripts, 1-based for
  ! Fortran. Returns 0 when any subscript is out of bounds, so every
  ! caller gets one bounds check rather than each writing its own.
  !
  ! Column-major is not a preference: it is what makes the buffer
  ! bit-identical to what a Fortran routine expects to receive.
  integer function gcna_index(handle, subs)
    integer, intent(in) :: handle
    integer, intent(in) :: subs(:)
    integer :: i, off, stride
    gcna_index = 0
    if (.not. gcna_is(handle)) return
    if (size(subs) /= size(reg(handle)%extents)) return
    off = 0
    stride = 1
    do i = 1, size(subs)
       off = off + (subs(i) - reg(handle)%lows(i)) * stride
       if (subs(i) < reg(handle)%lows(i)) return
       if (subs(i) > reg(handle)%lows(i) + reg(handle)%extents(i) - 1) return
       stride = stride * reg(handle)%extents(i)
    end do
    gcna_index = off + 1
  end function gcna_index

  ! --- element access ----------------------------------------------
  !
  ! Read and write go through select type, which is how one class(*)
  ! buffer serves every kind. `ok` is reported rather than guessed so a
  ! caller can tell "not that kind" from "the value was zero".

  subroutine gcna_get_real(handle, at, val, ok)
    integer, intent(in) :: handle, at
    real(dp), intent(out) :: val
    logical, intent(out) :: ok
    val = 0.0_dp
    ok = .false.
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    if (at < 1 .or. at > size(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (real(dp));    val = b(at); ok = .true.
    type is (real(4));     val = real(b(at), dp); ok = .true.
    type is (integer(4));  val = real(b(at), dp); ok = .true.
    type is (integer(8));  val = real(b(at), dp); ok = .true.
    end select
  end subroutine gcna_get_real

  subroutine gcna_get_int(handle, at, val, ok)
    integer, intent(in) :: handle, at
    integer(8), intent(out) :: val
    logical, intent(out) :: ok
    val = 0
    ok = .false.
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    if (at < 1 .or. at > size(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (integer(4));  val = int(b(at), 8); ok = .true.
    type is (integer(8));  val = b(at); ok = .true.
    end select
  end subroutine gcna_get_int

  subroutine gcna_get_logical(handle, at, val, ok)
    integer, intent(in) :: handle, at
    logical, intent(out) :: val
    logical, intent(out) :: ok
    val = .false.
    ok = .false.
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    if (at < 1 .or. at > size(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (logical); val = b(at); ok = .true.
    end select
  end subroutine gcna_get_logical

  subroutine gcna_set_real(handle, at, val, ok)
    integer, intent(in) :: handle, at
    real(dp), intent(in) :: val
    logical, intent(out) :: ok
    ok = .false.
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    if (at < 1 .or. at > size(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (real(dp));   b(at) = val; ok = .true.
    type is (real(4));    b(at) = real(val, 4); ok = .true.
    type is (integer(4)); b(at) = int(val, 4); ok = .true.
    type is (integer(8)); b(at) = int(val, 8); ok = .true.
    end select
  end subroutine gcna_set_real

  ! `val` is 64-bit so that an int8 array can actually hold a 64-bit
  ! value. It was a default integer, which quietly narrowed every
  ! element of one on the way in and out.
  subroutine gcna_set_int(handle, at, val, ok)
    integer, intent(in) :: handle, at
    integer(8), intent(in) :: val
    logical, intent(out) :: ok
    ok = .false.
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    if (at < 1 .or. at > size(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (integer(4)); b(at) = int(val, 4); ok = .true.
    type is (integer(8)); b(at) = int(val, 8); ok = .true.
    type is (real(dp));   b(at) = real(val, dp); ok = .true.
    type is (real(4));    b(at) = real(val, 4); ok = .true.
    end select
  end subroutine gcna_set_int

  subroutine gcna_set_logical(handle, at, val, ok)
    integer, intent(in) :: handle, at
    logical, intent(in) :: val
    logical, intent(out) :: ok
    ok = .false.
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    if (at < 1 .or. at > size(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (logical); b(at) = val; ok = .true.
    end select
  end subroutine gcna_set_logical

  ! One element as text, for the printer. Kept here because this module
  ! is the only one that knows what the buffer's dynamic type is.
  function gcna_elem_string(handle, at) result(s)
    integer, intent(in) :: handle, at
    character(len=:), allocatable :: s
    character(len=48) :: buf
    s = "?"
    if (.not. gcna_is(handle)) return
    if (.not. allocated(reg(handle)%buf)) return
    if (at < 1 .or. at > size(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (real(dp));    write(buf, '(G0)') b(at); s = trim(buf)
    type is (real(4));     write(buf, '(G0)') b(at); s = trim(buf)
    type is (integer(4));  write(buf, '(I0)') b(at); s = trim(buf)
    type is (integer(8));  write(buf, '(I0)') b(at); s = trim(buf)
    type is (logical)
       if (b(at)) then
          s = "true"
       else
          s = "false"
       end if
    type is (complex(dp))
       write(buf, '(G0,A,G0)') real(b(at)), " ", aimag(b(at))
       s = trim(buf)
    end select
  end function gcna_elem_string

  ! --- registry plumbing -------------------------------------------

  ! Reuses a released slot before growing, so a program that allocates
  ! and drops arrays in a loop does not grow the registry without
  ! bound.
  integer function claim()
    integer :: i
    type(na_node), allocatable :: bigger(:)
    if (.not. allocated(reg)) then
       allocate(reg(16))
       reg_used = 0
    end if
    do i = 1, reg_used
       if (.not. reg(i)%used) then
          reg(i)%used = .true.
          claim = i
          return
       end if
    end do
    if (reg_used >= size(reg)) then
       ! Each component MOVES, it is not copied. An assignment of
       ! the nodes deep-copies every allocatable component, so
       ! every array's buffer used to change address whenever the
       ! registry grew -- and a compiled loop holds a pointer into
       ! a buffer across allocations. move_alloc hands over the
       ! allocation itself, so a buffer is where it always was.
       allocate(bigger(2 * size(reg)))
       do i = 1, reg_used
          bigger(i)%used = reg(i)%used
          if (allocated(reg(i)%elem_kind)) call move_alloc(reg(i)%elem_kind, bigger(i)%elem_kind)
          if (allocated(reg(i)%extents)) call move_alloc(reg(i)%extents, bigger(i)%extents)
          if (allocated(reg(i)%lows)) call move_alloc(reg(i)%lows, bigger(i)%lows)
          if (allocated(reg(i)%buf)) call move_alloc(reg(i)%buf, bigger(i)%buf)
       end do
       call move_alloc(bigger, reg)
    end if
    reg_used = reg_used + 1
    reg(reg_used)%used = .true.
    claim = reg_used
  end function claim

  ! A fresh array reads as zeros, not as whatever the allocator left.
  ! An uninitialised buffer handed to a Fortran routine is the kind of
  ! bug that reproduces once a week.
  subroutine zero_fill(handle)
    integer, intent(in) :: handle
    if (.not. allocated(reg(handle)%buf)) return
    select type (b => reg(handle)%buf)
    type is (real(dp));    b = 0.0_dp
    type is (real(4));     b = 0.0_4
    type is (integer(4));  b = 0
    type is (integer(8));  b = 0
    type is (logical);     b = .false.
    type is (complex(dp)); b = (0.0_dp, 0.0_dp)
    end select
  end subroutine zero_fill

end module NativeArray
