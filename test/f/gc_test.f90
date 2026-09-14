! Exercises the mark-sweep heap on its own, before anything in clotran
! depends on it. The cases that matter are the ones refcounting could
! not do (cycles) and the ones that only fail intermittently in a real
! system (a missing root, growth during a live traversal) -- so those
! are tested deterministically here, under torture mode.
program gc_test
  use GC
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_immediates()
  call check_cons_roundtrip()
  call check_reachable_survives()
  call check_unreachable_freed()
  call check_free_list_reuse()
  call check_cycle_is_collected()
  call check_growth()
  call check_string_release()
  call check_torture_keeps_live_data()
  call check_argument_is_rooted()

  if (all_ok) then
     print *, ""
     print *, "ALL GC CHECKS PASSED"
  else
     print *, ""
     print *, "GC CHECKS FAILED"
     stop 1
  end if

contains

  subroutine ok(label, condition)
    character(len=*), intent(in) :: label
    logical, intent(in) :: condition
    if (condition) then
       print '(A,A)', "ok   - ", label
    else
       print '(A,A)', "FAIL - ", label
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok

  subroutine ok_int(label, got, expected)
    character(len=*), intent(in) :: label
    integer, intent(in) :: got, expected
    if (got == expected) then
       print '(A,A,I0)', "ok   - ", label, got
    else
       print '(A,A,I0,A,I0,A)', "FAIL - ", label, got, "  (expected ", expected, ")"
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok_int

  ! An immediate never touches the heap -- which is the point: most
  ! values in a running program are integers and nil, and they should
  ! cost nothing to allocate or collect.
  subroutine check_immediates()
    type(gc_value) :: i, n
    call gc_init(16)
    i = gc_int(42)
    n = gc_nil()
    call ok("1a. an integer holds no heap reference: ", i%ref == 0)
    call ok("1b. ...and neither does nil: ", n%ref == 0)
    call gc_collect(no_roots)
    call ok_int("1c. collecting with no roots frees nothing: ", gc_live_count(), 0)
  end subroutine check_immediates

  subroutine check_cons_roundtrip()
    type(gc_value) :: c, roots(0)
    call gc_init(16)
    c = gc_cons(gc_int(1), gc_int(2), roots)
    call ok_int("2a. car reads back: ", car_int(c), 1)
    call ok_int("2b. cdr reads back: ", cdr_int(c), 2)
    call ok_int("2c. one cell is live: ", gc_live_count(), 1)
  end subroutine check_cons_roundtrip

  ! A chain of 500 cells, held only by its head.
  subroutine check_reachable_survives()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(16)
    head = gc_nil()
    do i = 1, 500
       roots(1) = head
       head = gc_cons(gc_int(i), head, roots)
    end do
    roots(1) = head
    call gc_collect(roots)
    call ok_int("3a. a 500-cell chain survives, held by its head: ", gc_live_count(), 500)
    call ok_int("3b. ...and is still intact: ", chain_length(head), 500)
    call ok_int("3c. ...with its contents unchanged: ", car_int(head), 500)
  end subroutine check_reachable_survives

  subroutine check_unreachable_freed()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(16)
    head = gc_nil()
    do i = 1, 100
       roots(1) = head
       head = gc_cons(gc_int(i), head, roots)
    end do
    call gc_collect(no_roots) ! nothing is a root: all of it is garbage
    call ok_int("4a. an unreachable chain is collected entirely: ", gc_live_count(), 0)
  end subroutine check_unreachable_freed

  subroutine check_free_list_reuse()
    type(gc_value) :: c, roots(0)
    integer :: cap_before, i
    call gc_init(64)
    do i = 1, 50
       c = gc_cons(gc_int(i), gc_nil(), roots)
    end do
    call gc_collect(no_roots)
    cap_before = gc_capacity()
    do i = 1, 50
       c = gc_cons(gc_int(i), gc_nil(), roots)
    end do
    call ok_int("5a. freed slots are reused, not grown past: ", gc_capacity(), cap_before)
    call ok_int("5b. ...and the live count is right again: ", gc_live_count(), 50)
  end subroutine check_free_list_reuse

  ! The case refcounting structurally cannot reclaim, and the reason
  ! clotran leaks today: a closure bound into its own environment for
  ! `recur` is exactly this shape.
  subroutine check_cycle_is_collected()
    type(gc_value) :: a, b, roots(1)
    call gc_init(16)
    a = gc_cons(gc_int(1), gc_nil(), no_roots)
    roots(1) = a
    b = gc_cons(gc_int(2), a, roots)
    call gc_set_cdr(a, b) ! a -> b -> a
    roots(1) = a
    call gc_collect(roots)
    call ok_int("6a. a cycle held by a root survives: ", gc_live_count(), 2)
    call gc_collect(no_roots)
    call ok_int("6b. ...and is collected once unreachable: ", gc_live_count(), 0)
  end subroutine check_cycle_is_collected

  ! Growth has to happen mid-traversal without losing the live chain --
  ! the pool is reallocated underneath values that already point into it.
  subroutine check_growth()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(8)
    head = gc_nil()
    do i = 1, 300
       roots(1) = head
       head = gc_cons(gc_int(i), head, roots)
    end do
    roots(1) = head
    call ok("7a. the pool grew past its initial size: ", gc_capacity() >= 300)
    call ok_int("7b. ...and the chain survived growth intact: ", chain_length(head), 300)
    call gc_collect(roots)
    call ok_int("7c. ...and still does after a collection: ", chain_length(head), 300)
  end subroutine check_growth

  subroutine check_string_release()
    type(gc_value) :: s, roots(1)
    call gc_init(16)
    s = gc_str("a string on the heap", no_roots)
    roots(1) = s
    call gc_collect(roots)
    call ok("8a. a rooted string survives: ", gc_text(s) == "a string on the heap")
    call gc_collect(no_roots)
    call ok_int("8b. ...and is released when unreachable: ", gc_live_count(), 0)
  end subroutine check_string_release

  ! Torture mode collects at EVERY allocation, so anything not passed
  ! as a root is destroyed immediately. A missing root then fails here
  ! and now, deterministically, instead of corrupting memory later.
  subroutine check_torture_keeps_live_data()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(8)
    gc_torture = .true.
    head = gc_nil()
    do i = 1, 200
       roots(1) = head
       head = gc_cons(gc_int(i), head, roots)
    end do
    call ok_int("9a. under torture, a properly rooted chain is intact: ", &
         chain_length(head), 200)
    call ok_int("9b. ...its contents are correct: ", car_int(head), 200)
    call ok("9c. ...and it really did collect every allocation: ", gc_collections >= 200)
    gc_torture = .false.
  end subroutine check_torture_keeps_live_data

  ! A freshly built value passed as an ARGUMENT is live, but the caller
  ! cannot have listed it as a root -- nothing references it yet. If
  ! allocation does not root its own arguments, (cons (str ...) ...)
  ! frees the string between the two calls: only under torture or at an
  ! unlucky heap size, which is the worst way to find a bug.
  subroutine check_argument_is_rooted()
    type(gc_value) :: c, roots(0)
    call gc_init(8)
    gc_torture = .true.
    c = gc_cons(gc_str("inner", roots), gc_int(7), roots)
    call ok("10a. an argument built at the call site survives: ", &
         gc_text(gc_car(c)) == "inner")
    call ok_int("10b. ...and the cell around it is intact: ", cdr_int(c), 7)
    gc_torture = .false.
  end subroutine check_argument_is_rooted

  ! --- helpers ---

  function car_int(c) result(i)
    type(gc_value), intent(in) :: c
    type(gc_value) :: v
    integer :: i
    v = gc_car(c)
    i = v%ival
  end function car_int

  function cdr_int(c) result(i)
    type(gc_value), intent(in) :: c
    type(gc_value) :: v
    integer :: i
    v = gc_cdr(c)
    i = v%ival
  end function cdr_int

  function chain_length(head) result(n)
    type(gc_value), intent(in) :: head
    type(gc_value) :: p
    integer :: n
    n = 0
    p = head
    do while (p%tag == GCT_CONS)
       n = n + 1
       p = gc_cdr(p)
    end do
  end function chain_length

end program gc_test
