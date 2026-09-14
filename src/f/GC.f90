! GC: a non-moving mark-sweep heap, built standalone.
!
! Nothing in clotran uses this yet. It exists so the collector can be
! written and tested on its own before the value representation is
! committed to it -- see PLAN.md step 3.
!
! WHY THIS EXISTS AT ALL. Measured: one `cons_value` copy costs 497 ns,
! and 94.7% of clotran's runtime is flang's generic derived-type
! machinery. That is a per-COPY cost, not allocation and not freeing,
! and it is there because `cons_value` has a FINAL binding and nine
! allocatable components. The same data in a type with no FINAL copies
! in 4 ns. So the value type has to lose FINAL, which means its
! components can no longer free themselves, which means something else
! has to reclaim them. Hence a tracing collector.
!
! THE SHAPE, and why each choice:
!
!   non-moving   A compacting collector relocates objects, which
!                invalidates any pointer a Fortran library is holding.
!                Handing array buffers to dgemm or ChemSol is the point
!                of the project, so addresses stay put. It also keeps
!                rooting simple: a root is a value, not the ADDRESS of
!                a local that the collector would have to rewrite.
!
!   handles      A reference is an INDEX into a pool, not a pointer. It
!                can be bounds-checked, dumped, and printed; a corrupt
!                reference is a bad index rather than a wild pointer.
!                We will be debugging this collector, and that matters.
!
!   pool/kind    Fortran cannot cast, so each node kind gets its own
!                typed array. One untyped blob would mean class(*)
!                everywhere, buying back the dispatch cost being
!                removed.
!
!   roots passed The root set is an ARGUMENT, never a module global.
!                Per PLAN.md, concurrency comes after this, and a
!                thread is then just another context with its own
!                roots. Making the root set global here would mean
!                rewriting the collector later.
!
! `gc_value` deliberately has no allocatable components and no FINAL,
! which is the entire point: copying one is a flat 16-byte move.
module GC
  implicit none
  private

  integer, parameter, public :: gc_dp = kind(1.0d0)

  ! Tags double as the pool selector: a tag says both what a value IS
  ! and, for heap-backed tags, which pool `ref` indexes into.
  !
  ! GCT_, not GC_: Fortran is case-insensitive, so a parameter GC_CONS
  ! and a function gc_cons are the SAME name and collide. Same trap as
  ! LAZY_CONS/lazy_cons in the gotchas catalog.
  integer, parameter, public :: GCT_NIL  = 0
  integer, parameter, public :: GCT_INT  = 1
  integer, parameter, public :: GCT_REAL = 2
  integer, parameter, public :: GCT_CONS = 3
  integer, parameter, public :: GCT_STR  = 4

  type, public :: gc_value
     integer :: tag = GCT_NIL
     integer :: ival = 0
     real(gc_dp) :: rval = 0.0_gc_dp
     integer :: ref = 0 ! index into this tag's pool; 0 for immediates
  end type gc_value

  ! --- cons pool -------------------------------------------------
  type :: cons_node
     type(gc_value) :: car
     type(gc_value) :: cdr
  end type cons_node

  type(cons_node), allocatable :: cons_pool(:)
  logical, allocatable :: cons_mark(:)
  integer, allocatable :: cons_free_next(:) ! free-list links, 0 = end
  integer :: cons_free_head = 0
  integer :: cons_used = 0 ! high-water mark of pool slots handed out

  ! --- string pool -----------------------------------------------
  ! Strings are heap objects too: a value must stay copyable by memcpy,
  ! so it cannot own a deferred-length character of its own.
  type :: str_node
     character(len=:), allocatable :: text
  end type str_node

  type(str_node), allocatable :: str_pool(:)
  logical, allocatable :: str_mark(:)
  integer, allocatable :: str_free_next(:)
  integer :: str_free_head = 0
  integer :: str_used = 0

  ! --- marking work list -----------------------------------------
  ! An explicit stack, not recursion: a long list is a chain thousands
  ! of nodes deep, and recursive marking would overflow the real stack
  ! on exactly the structures this language builds most.
  type(gc_value), allocatable :: mark_stack(:)
  integer :: mark_sp = 0

  ! --- statistics, for tests and for the debugger ----------------
  integer, public :: gc_allocs = 0
  integer, public :: gc_frees = 0
  integer, public :: gc_collections = 0

  ! Collect at EVERY allocation. Catches a missing root immediately and
  ! deterministically rather than once a month; the test suite runs
  ! under it.
  logical, public :: gc_torture = .false.

  public :: gc_init, gc_cons, gc_str, gc_int, gc_real, gc_nil
  public :: gc_car, gc_cdr, gc_text, gc_set_car, gc_set_cdr
  public :: gc_collect, gc_live_count, gc_capacity

contains

  subroutine gc_init(initial)
    integer, intent(in), optional :: initial
    integer :: n
    n = 256
    if (present(initial)) n = max(initial, 8)
    call reset_cons(n)
    call reset_str(n)
    if (allocated(mark_stack)) deallocate(mark_stack)
    allocate(mark_stack(n))
    mark_sp = 0
    gc_allocs = 0
    gc_frees = 0
    gc_collections = 0
  end subroutine gc_init

  subroutine reset_cons(n)
    integer, intent(in) :: n
    if (allocated(cons_pool)) deallocate(cons_pool)
    if (allocated(cons_mark)) deallocate(cons_mark)
    if (allocated(cons_free_next)) deallocate(cons_free_next)
    allocate(cons_pool(n), cons_mark(n), cons_free_next(n))
    cons_mark = .false.
    cons_free_next = 0
    cons_free_head = 0
    cons_used = 0
  end subroutine reset_cons

  subroutine reset_str(n)
    integer, intent(in) :: n
    if (allocated(str_pool)) deallocate(str_pool)
    if (allocated(str_mark)) deallocate(str_mark)
    if (allocated(str_free_next)) deallocate(str_free_next)
    allocate(str_pool(n), str_mark(n), str_free_next(n))
    str_mark = .false.
    str_free_next = 0
    str_free_head = 0
    str_used = 0
  end subroutine reset_str

  ! --- immediates: no heap involved at all -----------------------

  function gc_nil() result(v)
    type(gc_value) :: v
    v%tag = GCT_NIL
  end function gc_nil

  function gc_int(i) result(v)
    integer, intent(in) :: i
    type(gc_value) :: v
    v%tag = GCT_INT
    v%ival = i
  end function gc_int

  function gc_real(r) result(v)
    real(gc_dp), intent(in) :: r
    type(gc_value) :: v
    v%tag = GCT_REAL
    v%rval = r
  end function gc_real

  ! --- allocation ------------------------------------------------
  !
  ! Takes the caller's roots so that torture mode can collect here
  ! without losing anything: under torture the collection happens
  ! BEFORE the new object exists, so the roots passed in are exactly
  ! what must survive.

  function gc_cons(car, cdr, roots) result(v)
    type(gc_value), intent(in) :: car, cdr
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: idx

    ! car and cdr are roots for any collection that happens HERE, and
    ! the caller cannot have added them: they are freshly built and not
    ! reachable from anything yet -- the cell that will hold them does
    ! not exist. (gc_cons (gc_str ...) ...) would otherwise free the
    ! string between the two calls, and only under torture or at an
    ! unlucky heap size, which is the worst way to find a bug.
    idx = take_cons_slot(roots, car, cdr)
    cons_pool(idx)%car = car
    cons_pool(idx)%cdr = cdr
    v%tag = GCT_CONS
    v%ref = idx
    gc_allocs = gc_allocs + 1
  end function gc_cons

  function gc_str(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: idx

    idx = take_str_slot(roots)
    str_pool(idx)%text = text
    v%tag = GCT_STR
    v%ref = idx
    gc_allocs = gc_allocs + 1
  end function gc_str

  ! A free slot, collecting or growing if there is none. car/cdr are
  ! passed so they can be treated as roots during that collection --
  ! they are live by definition, and are not reachable from `roots`
  ! yet because the cell that will hold them does not exist.
  function take_cons_slot(roots, car, cdr) result(idx)
    type(gc_value), intent(in) :: roots(:), car, cdr
    integer :: idx
    type(gc_value), allocatable :: all_roots(:)
    logical :: need_space

    need_space = (cons_free_head == 0 .and. cons_used >= size(cons_pool))
    if (gc_torture .or. need_space) then
       allocate(all_roots(size(roots) + 2))
       all_roots(1:size(roots)) = roots
       all_roots(size(roots) + 1) = car
       all_roots(size(roots) + 2) = cdr
       call gc_collect(all_roots)
       if (cons_free_head == 0 .and. cons_used >= size(cons_pool)) call grow_cons()
    end if
    if (cons_free_head /= 0) then
       idx = cons_free_head
       cons_free_head = cons_free_next(idx)
    else
       cons_used = cons_used + 1
       idx = cons_used
    end if
  end function take_cons_slot

  function take_str_slot(roots) result(idx)
    type(gc_value), intent(in) :: roots(:)
    integer :: idx
    if (gc_torture .or. (str_free_head == 0 .and. str_used >= size(str_pool))) then
       call gc_collect(roots)
       if (str_free_head == 0 .and. str_used >= size(str_pool)) call grow_str()
    end if
    if (str_free_head /= 0) then
       idx = str_free_head
       str_free_head = str_free_next(idx)
    else
       str_used = str_used + 1
       idx = str_used
    end if
  end function take_str_slot

  ! Doubling, with move_alloc rather than array assignment -- see the
  ! reallocating-assignment entries in NOTES.md's gotchas catalog.
  subroutine grow_cons()
    type(cons_node), allocatable :: bigger(:)
    logical, allocatable :: bigger_mark(:)
    integer, allocatable :: bigger_free(:)
    integer :: n, i
    n = size(cons_pool)
    allocate(bigger(2 * n), bigger_mark(2 * n), bigger_free(2 * n))
    do i = 1, n
       bigger(i) = cons_pool(i)
    end do
    bigger_mark = .false.
    bigger_free = 0
    bigger_free(1:n) = cons_free_next(1:n)
    call move_alloc(bigger, cons_pool)
    call move_alloc(bigger_mark, cons_mark)
    call move_alloc(bigger_free, cons_free_next)
  end subroutine grow_cons

  subroutine grow_str()
    type(str_node), allocatable :: bigger(:)
    logical, allocatable :: bigger_mark(:)
    integer, allocatable :: bigger_free(:)
    integer :: n, i
    n = size(str_pool)
    allocate(bigger(2 * n), bigger_mark(2 * n), bigger_free(2 * n))
    do i = 1, n
       if (allocated(str_pool(i)%text)) bigger(i)%text = str_pool(i)%text
    end do
    bigger_mark = .false.
    bigger_free = 0
    bigger_free(1:n) = str_free_next(1:n)
    call move_alloc(bigger, str_pool)
    call move_alloc(bigger_mark, str_mark)
    call move_alloc(bigger_free, str_free_next)
  end subroutine grow_str

  ! --- accessors -------------------------------------------------

  function gc_car(v) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value) :: out
    if (v%tag == GCT_CONS) out = cons_pool(v%ref)%car
  end function gc_car

  function gc_cdr(v) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value) :: out
    if (v%tag == GCT_CONS) out = cons_pool(v%ref)%cdr
  end function gc_cdr

  subroutine gc_set_car(v, x)
    type(gc_value), intent(in) :: v, x
    if (v%tag == GCT_CONS) cons_pool(v%ref)%car = x
  end subroutine gc_set_car

  ! Mutation is what makes CYCLES possible, which is the case
  ! refcounting structurally cannot reclaim and this collector can.
  subroutine gc_set_cdr(v, x)
    type(gc_value), intent(in) :: v, x
    if (v%tag == GCT_CONS) cons_pool(v%ref)%cdr = x
  end subroutine gc_set_cdr

  function gc_text(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    s = ""
    if (v%tag /= GCT_STR) return
    if (allocated(str_pool(v%ref)%text)) s = str_pool(v%ref)%text
  end function gc_text

  ! --- collection ------------------------------------------------

  subroutine gc_collect(roots)
    type(gc_value), intent(in) :: roots(:)
    integer :: i

    gc_collections = gc_collections + 1
    cons_mark = .false.
    str_mark = .false.
    mark_sp = 0

    do i = 1, size(roots)
       call push_mark(roots(i))
    end do
    call drain_mark_stack()
    call sweep_cons()
    call sweep_str()
  end subroutine gc_collect

  subroutine push_mark(v)
    type(gc_value), intent(in) :: v
    type(gc_value), allocatable :: bigger(:)
    integer :: n
    if (v%tag /= GCT_CONS .and. v%tag /= GCT_STR) return ! immediates hold nothing
    if (v%ref == 0) return
    if (mark_sp >= size(mark_stack)) then
       n = size(mark_stack)
       allocate(bigger(2 * n))
       bigger(1:n) = mark_stack(1:n)
       call move_alloc(bigger, mark_stack)
    end if
    mark_sp = mark_sp + 1
    mark_stack(mark_sp) = v
  end subroutine push_mark

  subroutine drain_mark_stack()
    type(gc_value) :: v
    do while (mark_sp > 0)
       v = mark_stack(mark_sp)
       mark_sp = mark_sp - 1
       select case (v%tag)
       case (GCT_CONS)
          ! Already-marked stops the walk, which is what makes a cycle
          ! terminate instead of looping forever.
          if (cons_mark(v%ref)) cycle
          cons_mark(v%ref) = .true.
          call push_mark(cons_pool(v%ref)%car)
          call push_mark(cons_pool(v%ref)%cdr)
       case (GCT_STR)
          str_mark(v%ref) = .true. ! a leaf: holds no references
       end select
    end do
  end subroutine drain_mark_stack

  subroutine sweep_cons()
    integer :: i
    do i = 1, cons_used
       if (cons_mark(i)) cycle
       if (on_free_list(cons_free_next, cons_free_head, i)) cycle
       cons_pool(i)%car = gc_nil()
       cons_pool(i)%cdr = gc_nil()
       cons_free_next(i) = cons_free_head
       cons_free_head = i
       gc_frees = gc_frees + 1
    end do
  end subroutine sweep_cons

  subroutine sweep_str()
    integer :: i
    do i = 1, str_used
       if (str_mark(i)) cycle
       if (on_free_list(str_free_next, str_free_head, i)) cycle
       ! Release the character data now rather than at process exit:
       ! this is the one place a finalizer genuinely belongs, run once
       ! per object by sweep instead of once per copy.
       if (allocated(str_pool(i)%text)) deallocate(str_pool(i)%text)
       str_free_next(i) = str_free_head
       str_free_head = i
       gc_frees = gc_frees + 1
    end do
  end subroutine sweep_str

  ! A slot already on the free list must not be freed twice, or the
  ! list develops a loop and the same slot is handed out repeatedly.
  ! ponytail: linear in the free list, so sweep is O(free^2) in the
  ! worst case. A per-slot "is free" flag is the fix if it shows up.
  function on_free_list(links, head, idx) result(found)
    integer, intent(in) :: links(:), head, idx
    logical :: found
    integer :: p
    found = .false.
    p = head
    do while (p /= 0)
       if (p == idx) then
          found = .true.
          return
       end if
       p = links(p)
    end do
  end function on_free_list

  function gc_live_count() result(n)
    integer :: n
    integer :: i
    n = 0
    do i = 1, cons_used
       if (.not. on_free_list(cons_free_next, cons_free_head, i)) n = n + 1
    end do
    do i = 1, str_used
       if (.not. on_free_list(str_free_next, str_free_head, i)) n = n + 1
    end do
  end function gc_live_count

  function gc_capacity() result(n)
    integer :: n
    n = size(cons_pool)
  end function gc_capacity

end module GC
