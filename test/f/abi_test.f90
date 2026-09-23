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
module clotran_abi_decl
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
     function clotran_bool(slot) bind(C, name="clotran_bool") result(b)
       import :: c_int
       integer(c_int), value :: slot
       integer(c_int) :: b
     end function clotran_bool
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
     subroutine clotran_copy(dst, src) bind(C, name="clotran_copy")
       import :: c_int
       integer(c_int), value :: dst, src
     end subroutine clotran_copy
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
     function clotran_error_copy(buf, n) bind(C, name="clotran_error_copy") result(w)
       import :: c_int, c_char
       character(kind=c_char), intent(out) :: buf(*)
       integer(c_int), value :: n
       integer(c_int) :: w
     end function clotran_error_copy
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
     function clotran_def_fn(ns, nsn, name, namen, fp, arity) &
          bind(C, name="clotran_def_fn") result(st)
       import :: c_int, c_char, c_funptr
       character(kind=c_char), intent(in) :: ns(*), name(*)
       integer(c_int), value :: nsn, namen, arity
       type(c_funptr), value :: fp
       integer(c_int) :: st
     end function clotran_def_fn
  end interface

end module clotran_abi_decl

! WHAT A COMPILED FUNCTION LOOKS LIKE. These two are written by hand
! as the generator will write them: one procedure per Clojure fn, the
! arguments already in consecutive slots, the answer into one more.
! Nothing is passed by value and nothing allocates a vector to make a
! call, which is most of the reason to compile at all.
module abi_test_fns
  use iso_c_binding
  use clotran_abi_decl
  implicit none
contains

  ! (defn add2 [a b] (+ a b)) at its simplest: no allocation, no call.
  subroutine abi_add2(argbase, nargs, dst) bind(C, name="abi_add2")
    integer(c_int), value :: argbase, nargs, dst
    call clotran_set_int(dst, clotran_int(argbase + 1) + clotran_int(argbase + 2))
  end subroutine abi_add2

  ! (defn pair [a b] [a b]) -- it ALLOCATES, so the collector is in the
  ! middle of it. The frame is the generated procedure's own scratch
  ! space; the answer is copied DOWN into dst before the frame goes, or
  ! it would be cleared with everything else.
  subroutine abi_pair(argbase, nargs, dst) bind(C, name="abi_pair")
    integer(c_int), value :: argbase, nargs, dst
    integer(c_int) :: b
    b = clotran_frame_enter(1_c_int)
    call clotran_vec_empty(b + 1)
    call clotran_vec_conj(b + 1, b + 1, argbase + 1)
    call clotran_vec_conj(b + 1, b + 1, argbase + 2)
    call clotran_copy(dst, b + 1)
    call clotran_frame_leave(b)
  end subroutine abi_pair

  ! What a RECOMPILE installs: the same name, a different procedure.
  subroutine abi_add2b(argbase, nargs, dst) bind(C, name="abi_add2b")
    integer(c_int), value :: argbase, nargs, dst
    call clotran_set_int(dst, clotran_int(argbase + 1) + clotran_int(argbase + 2) + 100_c_int64_t)
  end subroutine abi_add2b

  ! A compiled procedure CALLING BACK into the language: it looks the
  ! Var up and applies it, which is what every call through a Var
  ! handle will do.
  subroutine abi_twice(argbase, nargs, dst) bind(C, name="abi_twice")
    integer(c_int), value :: argbase, nargs, dst
    integer(c_int) :: b, found, st
    b = clotran_frame_enter(3_c_int)
    found = clotran_var(b + 1, ctext("clojure.core"), 12_c_int, ctext("+"), 1_c_int)
    call clotran_deref(b + 2, b + 1)
    call clotran_vec_empty(b + 3)
    call clotran_vec_conj(b + 3, b + 3, argbase + 1)
    call clotran_vec_conj(b + 3, b + 3, argbase + 1)
    st = clotran_call(dst, b + 2, b + 3)
    call clotran_frame_leave(b)
  end subroutine abi_twice

  ! the (chars, n) pair, again, because a module cannot see the
  ! program's internal helpers
  function ctext(s) result(a)
    character(len=*), intent(in) :: s
    character(kind=c_char) :: a(len(s))
    integer :: i
    do i = 1, len(s)
       a(i) = s(i:i)
    end do
  end function ctext
end module abi_test_fns

program abi_test
  use iso_c_binding
  use clotran_abi_decl
  use abi_test_fns
  implicit none

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
  call check_compiled_functions()

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
  call check_compiled_functions()
  call clotran_set_torture(0_c_int)
  call check_language_sees_compiled_fns()

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

  ! Evaluate a form. The LENGTH COMES FROM THE STRING: passing it by
  ! hand got three of these wrong by one, and a truncated form is a
  ! reader error with an empty message, which is a miserable thing
  ! to debug. Every text entry point should be wrapped like this.
  function ev(s, slot) result(st)
    character(len=*), intent(in) :: s
    integer(c_int), intent(in) :: slot
    integer(c_int) :: st
    st = clotran_eval(cbuf(s), int(len(s), c_int), slot)
  end function ev

  function deffn(ns, nm, fp, arity) result(st)
    character(len=*), intent(in) :: ns, nm
    type(c_funptr), intent(in) :: fp
    integer(c_int), intent(in) :: arity
    integer(c_int) :: st
    st = clotran_def_fn(cbuf(ns), int(len(ns), c_int), cbuf(nm), &
         int(len(nm), c_int), fp, arity)
  end function deffn

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
    st = ev("(+ 1 2)", b + 1)
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
    st = ev("(+ 2 3)", b + 1)
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

  subroutine show_error()
    character(kind=c_char) :: eb(400)
    character(len=400) :: msg
    integer(c_int) :: w
    integer :: i
    w = clotran_error_copy(eb, 400_c_int)
    msg = ""
    do i = 1, int(w)
       msg(i:i) = eb(i)
    end do
    print *, "       error: ", trim(msg)
  end subroutine show_error

  ! WITH THE LANGUAGE LOADED. Everything above runs on the builtins
  ! alone, which is enough to prove the surface but not enough to
  ! prove that core.clj ACCEPTS a compiled procedure as a function.
  ! load-file is itself a builtin, so an embedder brings the language
  ! up exactly this way -- boot, load core, call. Once, and with
  ! torture off: collecting at every allocation while core.clj loads
  ! would take the rest of the afternoon.
  subroutine check_language_sees_compiled_fns()
    integer(c_int) :: b, st
    b = clotran_frame_enter(1_c_int)
    st = ev("(load-file ""src/clj/clojure/core.clj"")", b + 1)
    call ok("core.clj loads through the surface", st == 0)
    if (st /= 0) then
       call show_error()
       call clotran_frame_leave(b)
       return
    end if
    st = ev("(fn? compiled.test/add2)", b + 1)
    call ok("and core calls a compiled procedure a fn?", &
         st == 0 .and. clotran_bool(b + 1) == 1)
    st = ev("(ifn? compiled.test/add2)", b + 1)
    call ok("and an ifn?", st == 0 .and. clotran_bool(b + 1) == 1)
    st = ev("(reduce + (map compiled.test/add2 [1 2] [10 20]))", b + 1)
    call ok("and map takes it like any other function", &
         st == 0 .and. clotran_int(b + 1) == 33)
    call clotran_frame_leave(b)
  end subroutine check_language_sees_compiled_fns

  ! THE CALL PATH, end to end. A hand-written Fortran procedure is
  ! installed as a Clojure function and reached from Clojure source
  ! through the ordinary call, which is what a generated one will do.
  ! If this works, the generator has nothing left to prove about
  ! HOW its output is reached -- only about what it emits.
  subroutine check_compiled_functions()
    integer(c_int) :: b, st
    st = deffn("compiled.test", "add2", c_funloc(abi_add2), 2_c_int)
    call ok("a compiled procedure installs as a Var", st == 0)
    st = deffn("compiled.test", "pair", c_funloc(abi_pair), 2_c_int)
    st = deffn("compiled.test", "twice", c_funloc(abi_twice), 1_c_int)
    b = clotran_frame_enter(2_c_int)
    st = ev("(compiled.test/add2 40 2)", b + 1)
    if (st /= 0) call show_error()
    call ok("and Clojure source calls it", st == 0 .and. clotran_int(b + 1) == 42)
    st = ev("(count (compiled.test/pair 1 2))", b + 1)
    call ok("one that allocates answers a real collection", &
         st == 0 .and. clotran_int(b + 1) == 2)
    st = ev("(compiled.test/twice 21)", b + 1)
    call ok("and one that calls back through a Var", &
         st == 0 .and. clotran_int(b + 1) == 42)
    st = ev("(apply compiled.test/add2 [3 4])", b + 1)
    call ok("apply reaches it too", st == 0 .and. clotran_int(b + 1) == 7)
    st = ev("(compiled.test/add2 1)", b + 1)
    call ok("and the wrong arity is an error, not a crash", st == 1)
    call clotran_clear_error()
    ! An unrelated def of the same NAME in another namespace must not
    ! touch it. fn* rather than fn, because core.clj is not loaded
    ! here and fn is one of its macros.
    st = ev("(def add2 (fn* [a b] 0))", b + 1)
    st = ev("(compiled.test/add2 1 2)", b + 1)
    call ok("an unrelated def leaves the compiled Var alone", &
         st == 0 .and. clotran_int(b + 1) == 3)
    ! RECOMPILATION: installing a different procedure under the same
    ! name repoints the Var, and everything that calls through it
    ! reaches the new one on its next call. This is what makes
    ! compile-while-you-work possible at all.
    st = deffn("compiled.test", "add2", c_funloc(abi_add2b), 2_c_int)
    st = ev("(compiled.test/add2 1 2)", b + 1)
    call ok("recompiling the same name reaches the new procedure", &
         st == 0 .and. clotran_int(b + 1) == 103)
    st = deffn("compiled.test", "add2", c_funloc(abi_add2), 2_c_int)
    ! It has to BE a function to the language, not just be callable:
    ! core asks fn? and ifn? of things it is handed, and a compiled
    ! procedure that answered "object" would be refused by map.
    ! It has to NAME ITSELF when printed: a trace saying #<fn> tells
    ! you nothing about which compiled procedure you are in. fn? and
    ! ifn? are core.clj functions and core is not loaded here, so
    ! those are asserted in test/clj/language_test.clj instead.
    st = ev("(str compiled.test/add2)", b + 1)
    call ok("a compiled procedure names itself when printed", &
         st == 0 .and. clotran_str_len(b + 1) > 10)
    call clotran_clear_error()
    call clotran_frame_leave(b)
  end subroutine check_compiled_functions

end program abi_test
