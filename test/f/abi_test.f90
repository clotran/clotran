! abi_test: the C-callable runtime surface, exercised the way generated
! code and an embedder will use it.
!
! THE POINT OF THIS FILE IS WHAT IT DOES NOT DO. There is no `use GC`,
! no `use Eval`, no clotran module of any kind. Every entry point is
! declared here, by hand, from its C binding alone. If this compiles and
! passes, then a compiled namespace or a foreign program can reach the
! runtime without clotran's module files -- which is the whole claim
! ClotranABI.f90 makes, and the thing PLAN step 10 has to be true before
! a code generator is worth writing.
!
! It also proves the rooting model. Values live only in shadow-stack
! slots here; nothing is held in a Fortran variable. A collection is
! forced with live values in slots, and they are read back afterwards.
! If the slots were not roots, this test would read freed memory, which
! under torture mode is a crash rather than a wrong answer.
program abi_test
  use iso_c_binding
  implicit none

  interface
     subroutine clotran_init() bind(C, name="clotran_init")
     end subroutine clotran_init
     function clotran_boot(home, n) bind(C, name="clotran_boot") result(st)
       import :: c_char, c_int
       character(kind=c_char), intent(in) :: home(*)
       integer(c_int), value :: n
       integer(c_int) :: st
     end function clotran_boot
     function clotran_eval(src, n, dst) bind(C, name="clotran_eval") result(st)
       import :: c_char, c_int
       character(kind=c_char), intent(in) :: src(*)
       integer(c_int), value :: n, dst
       integer(c_int) :: st
     end function clotran_eval
     function clotran_frame_enter(n) bind(C, name="clotran_frame_enter") result(base)
       import :: c_int
       integer(c_int), value :: n
       integer(c_int) :: base
     end function clotran_frame_enter
     subroutine clotran_frame_leave(base) bind(C, name="clotran_frame_leave")
       import :: c_int
       integer(c_int), value :: base
     end subroutine clotran_frame_leave
     subroutine clotran_set_int(slot, n) bind(C, name="clotran_set_int")
       import :: c_int, c_int64_t
       integer(c_int), value :: slot
       integer(c_int64_t), value :: n
     end subroutine clotran_set_int
     subroutine clotran_set_real(slot, x) bind(C, name="clotran_set_real")
       import :: c_int, c_double
       integer(c_int), value :: slot
       real(c_double), value :: x
     end subroutine clotran_set_real
     subroutine clotran_set_str(slot, chars, n) bind(C, name="clotran_set_str")
       import :: c_int, c_char
       integer(c_int), value :: slot
       character(kind=c_char), intent(in) :: chars(*)
       integer(c_int), value :: n
     end subroutine clotran_set_str
     function clotran_tag(slot) bind(C, name="clotran_tag") result(t)
       import :: c_int
       integer(c_int), value :: slot
       integer(c_int) :: t
     end function clotran_tag
     function clotran_int(slot) bind(C, name="clotran_int") result(n)
       import :: c_int, c_int64_t
       integer(c_int), value :: slot
       integer(c_int64_t) :: n
     end function clotran_int
     function clotran_real(slot) bind(C, name="clotran_real") result(x)
       import :: c_int, c_double
       integer(c_int), value :: slot
       real(c_double) :: x
     end function clotran_real
     function clotran_str_len(slot) bind(C, name="clotran_str_len") result(n)
       import :: c_int
       integer(c_int), value :: slot
       integer(c_int) :: n
     end function clotran_str_len
     function clotran_str_copy(slot, buf, n) bind(C, name="clotran_str_copy") result(w)
       import :: c_int, c_char
       integer(c_int), value :: slot
       character(kind=c_char), intent(out) :: buf(*)
       integer(c_int), value :: n
       integer(c_int) :: w
     end function clotran_str_copy
     subroutine clotran_vec_empty(slot) bind(C, name="clotran_vec_empty")
       import :: c_int
       integer(c_int), value :: slot
     end subroutine clotran_vec_empty
     subroutine clotran_vec_conj(dst, vec, x) bind(C, name="clotran_vec_conj")
       import :: c_int
       integer(c_int), value :: dst, vec, x
     end subroutine clotran_vec_conj
     function clotran_vec_count(slot) bind(C, name="clotran_vec_count") result(n)
       import :: c_int
       integer(c_int), value :: slot
       integer(c_int) :: n
     end function clotran_vec_count
     subroutine clotran_vec_nth(dst, vec, i) bind(C, name="clotran_vec_nth")
       import :: c_int
       integer(c_int), value :: dst, vec, i
     end subroutine clotran_vec_nth
     function clotran_var(slot, ns, nsn, name, namen) bind(C, name="clotran_var") result(ok)
       import :: c_int, c_char
       integer(c_int), value :: slot
       character(kind=c_char), intent(in) :: ns(*), name(*)
       integer(c_int), value :: nsn, namen
       integer(c_int) :: ok
     end function clotran_var
     subroutine clotran_deref(dst, var) bind(C, name="clotran_deref")
       import :: c_int
       integer(c_int), value :: dst, var
     end subroutine clotran_deref
     function clotran_call(dst, fn, args) bind(C, name="clotran_call") result(st)
       import :: c_int
       integer(c_int), value :: dst, fn, args
       integer(c_int) :: st
     end function clotran_call
     function clotran_has_error() bind(C, name="clotran_has_error") result(b)
       import :: c_int
       integer(c_int) :: b
     end function clotran_has_error
     subroutine clotran_clear_error() bind(C, name="clotran_clear_error")
     end subroutine clotran_clear_error
     subroutine clotran_collect() bind(C, name="clotran_collect")
     end subroutine clotran_collect
     function clotran_live_count() bind(C, name="clotran_live_count") result(n)
       import :: c_int
       integer(c_int) :: n
     end function clotran_live_count
     subroutine clotran_set_torture(on) bind(C, name="clotran_set_torture")
       import :: c_int
       integer(c_int), value :: on
     end subroutine clotran_set_torture
  end interface

  integer :: failures
  failures = 0

  call clotran_init()
  call check_boot()
  call check_scalars()
  call check_strings()
  call check_vectors()
  call check_survives_collection()
  call check_eval()
  call check_call_a_var()
  call check_error_is_reported_not_thrown()
  call check_many_allocations_under_collection()

  ! AGAIN, collecting at every allocation. A slot the caller forgot
  ! to write would be freed between one line and the next here, so a
  ! rooting mistake in the surface itself cannot hide.
  print *, "--- torture ---"
  call clotran_set_torture(1_c_int)
  call check_scalars()
  call check_strings()
  call check_vectors()
  call check_survives_collection()
  call check_eval()
  call check_call_a_var()
  call clotran_set_torture(0_c_int)

  if (failures == 0) then
     print *, ""
     print *, "ABI TESTS PASSED"
  else
     print *, ""
     print *, "ABI TESTS FAILED:", failures
     stop 1
  end if

contains

  subroutine ok(label, cond)
    character(len=*), intent(in) :: label
    logical, intent(in) :: cond
    if (cond) then
       print *, "ok   - ", label
    else
       print *, "FAIL - ", label
       failures = failures + 1
    end if
  end subroutine ok

  ! A Fortran string as the (chars, n) pair every text entry point takes.
  function cbuf(s) result(a)
    character(len=*), intent(in) :: s
    character(kind=c_char) :: a(len(s))
    integer :: i
    do i = 1, len(s)
       a(i) = s(i:i)
    end do
  end function cbuf

  subroutine check_boot()
    integer(c_int) :: st
    st = clotran_boot(cbuf("."), 1_c_int)
    call ok("the environment builds through the C surface", st == 0)
  end subroutine check_boot

  subroutine check_scalars()
    integer(c_int) :: b
    b = clotran_frame_enter(2_c_int)
    call clotran_set_int(b + 1, 42_c_int64_t)
    call clotran_set_real(b + 2, 1.5_c_double)
    call ok("an integer goes into a slot and comes back", clotran_int(b + 1) == 42)
    call ok("and a double", abs(clotran_real(b + 2) - 1.5_c_double) < 1.0e-12_c_double)
    call ok("the tags differ", clotran_tag(b + 1) /= clotran_tag(b + 2))
    call clotran_frame_leave(b)
  end subroutine check_scalars

  subroutine check_strings()
    integer(c_int) :: b, n, w
    character(kind=c_char) :: buf(16)
    character(len=16) :: got
    integer :: i
    b = clotran_frame_enter(1_c_int)
    call clotran_set_str(b + 1, cbuf("hello"), 5_c_int)
    n = clotran_str_len(b + 1)
    call ok("a string knows its byte length", n == 5)
    w = clotran_str_copy(b + 1, buf, 16_c_int)
    got = ""
    do i = 1, int(w)
       got(i:i) = buf(i)
    end do
    call ok("and copies back out", w == 5 .and. got(1:5) == "hello")
    call clotran_frame_leave(b)
  end subroutine check_strings

  subroutine check_vectors()
    integer(c_int) :: b
    b = clotran_frame_enter(3_c_int)
    call clotran_vec_empty(b + 1)
    call ok("an empty vector counts zero", clotran_vec_count(b + 1) == 0)
    call clotran_set_int(b + 2, 10_c_int64_t)
    call clotran_vec_conj(b + 1, b + 1, b + 2)
    call clotran_set_int(b + 2, 20_c_int64_t)
    call clotran_vec_conj(b + 1, b + 1, b + 2)
    call ok("conj grows it", clotran_vec_count(b + 1) == 2)
    call clotran_vec_nth(b + 3, b + 1, 1_c_int)
    call ok("nth is zero-based", clotran_int(b + 3) == 20)
    call clotran_frame_leave(b)
  end subroutine check_vectors

  ! THE CLAIM. A value held ONLY in a slot survives a collection. If the
  ! shadow stack were not the root set, the vector's storage would be
  ! swept here and the count afterwards would be wrong or the read would
  ! crash.
  subroutine check_survives_collection()
    integer(c_int) :: b, i
    b = clotran_frame_enter(2_c_int)
    call clotran_vec_empty(b + 1)
    do i = 1, 100
       call clotran_set_int(b + 2, int(i, c_int64_t))
       call clotran_vec_conj(b + 1, b + 1, b + 2)
    end do
    ! under torture every one of those conjs already collected
    call clotran_collect()
    call clotran_collect()
    call ok("a vector held only in a slot survives collection", &
         clotran_vec_count(b + 1) == 100)
    call clotran_vec_nth(b + 2, b + 1, 99_c_int)
    call ok("and its elements are intact", clotran_int(b + 2) == 100)
    call clotran_frame_leave(b)
  end subroutine check_survives_collection

  subroutine check_eval()
    integer(c_int) :: b, st
    b = clotran_frame_enter(1_c_int)
    st = clotran_eval(cbuf("(+ 1 2)"), 7_c_int, b + 1)
    call ok("eval through the surface answers", st == 0 .and. clotran_int(b + 1) == 3)
    call clotran_frame_leave(b)
  end subroutine check_eval

  ! What a compiled call site does: look the Var up once, deref it,
  ! build an argument vector, call. No core.clj is loaded here -- the
  ! builtins gce_base_env binds into clojure.core are enough.
  subroutine check_call_a_var()
    integer(c_int) :: b, found, st
    b = clotran_frame_enter(4_c_int)
    found = clotran_var(b + 1, cbuf("clojure.core"), 12_c_int, cbuf("+"), 1_c_int)
    call ok("a Var resolves by namespace and name", found == 1)
    call clotran_deref(b + 2, b + 1)
    call clotran_vec_empty(b + 3)
    call clotran_set_int(b + 4, 40_c_int64_t)
    call clotran_vec_conj(b + 3, b + 3, b + 4)
    call clotran_set_int(b + 4, 2_c_int64_t)
    call clotran_vec_conj(b + 3, b + 3, b + 4)
    st = clotran_call(b + 4, b + 2, b + 3)
    call ok("and calling it through the surface gives 42", &
         st == 0 .and. clotran_int(b + 4) == 42)
    call clotran_frame_leave(b)
  end subroutine check_call_a_var

  ! An error must be REPORTED, not thrown: it cannot unwind through a
  ! foreign caller's frames. The status says so and the flag can be
  ! cleared, after which the surface still works.
  subroutine check_error_is_reported_not_thrown()
    integer(c_int) :: b, found, st
    b = clotran_frame_enter(4_c_int)
    found = clotran_var(b + 1, cbuf("clojure.core"), 12_c_int, cbuf("+"), 1_c_int)
    call clotran_deref(b + 2, b + 1)
    call clotran_vec_empty(b + 3)
    call clotran_set_str(b + 4, cbuf("not a number"), 12_c_int)
    call clotran_vec_conj(b + 3, b + 3, b + 4)
    st = clotran_call(b + 4, b + 2, b + 3)
    call ok("a raising call returns a status", st == 1)
    call ok("and the error flag is set", clotran_has_error() == 1)
    call clotran_clear_error()
    call ok("which clears", clotran_has_error() == 0)
    st = clotran_eval(cbuf("(+ 2 3)"), 7_c_int, b + 1)
    call ok("and the surface still works afterwards", &
         st == 0 .and. clotran_int(b + 1) == 5)
    call clotran_frame_leave(b)
  end subroutine check_error_is_reported_not_thrown

  ! Allocation pressure with the only roots being slots. A generated
  ! procedure looks like this: a frame, a handful of slots, and a lot of
  ! garbage made and dropped between collections.
  subroutine check_many_allocations_under_collection()
    integer(c_int) :: b, i, live_before, live_after
    b = clotran_frame_enter(3_c_int)
    call clotran_vec_empty(b + 1)
    call clotran_set_int(b + 2, 7_c_int64_t)
    call clotran_vec_conj(b + 1, b + 1, b + 2)
    live_before = clotran_live_count()
    do i = 1, 2000
       ! a vector built and dropped every iteration: garbage on purpose
       call clotran_vec_empty(b + 3)
       call clotran_set_int(b + 2, int(i, c_int64_t))
       call clotran_vec_conj(b + 3, b + 3, b + 2)
    end do
    call clotran_collect()
    live_after = clotran_live_count()
    call clotran_vec_nth(b + 2, b + 1, 0_c_int)
    call ok("the kept vector is still right after 2000 allocations", &
         clotran_vec_count(b + 1) == 1 .and. clotran_int(b + 2) == 7)
    call ok("and the garbage was actually collected", &
         live_after < live_before + 2000)
    call clotran_frame_leave(b)
  end subroutine check_many_allocations_under_collection

end program abi_test
