! examples/embed/heat.f90 -- clotran EMBEDDED in a Fortran program.
!
! The program owns main and the time loop, as a solver does. It boots
! the runtime through the C surface (src/f/ClotranABI.f90) -- no
! clotran module is used; every entry is declared below from its C
! binding, as any Fortran or C program would -- loads core.clj, then
! examples/embed/control.cljf, and asks Clojure for the grid: a double
! array whose buffer this program takes a pointer to
! (clotran_array_view) and integrates in place. Clojure's aget/aset
! and this program's u(:) are the same memory, so the control
! strategy -- the initial condition, a source switched on mid-run, the
! stopping rule -- is Clojure code reading and writing the solver's
! own array, with nothing copied in either direction.
!
!   make embed && examples/embed/heat        (from the repository root)
!
! The runtime is linked in, as a solver would link it; the same
! objects make clotran-bin. `make test` runs this and compares the
! output with examples/embed/expected.txt.
!
! With HEAT_REPL=<port> (0: any free one) it also serves a REPL into the
! run (control.cljf's serve!, clotran.server): `nc localhost <port>`, then
! (embed.control/peak embed.control/grid) reads the live grid, and
! (swap! embed.control/steer assoc :stop true) ends the run. The time loop
! runs outside the running mutators (clotran_native_begin), stepping back
! in only to call Clojure, so the REPL's thread never waits on the solver.
module embed_abi
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
     function clotran_stack() bind(C, name="clotran_stack") result(cs)
       import :: c_ptr
       type(c_ptr) :: cs
     end function clotran_stack
     function clotran_frame_enter(cs, n) bind(C, name="clotran_frame_enter") result(base)
       import :: c_ptr, c_int
       type(c_ptr), value :: cs
       integer(c_int), value :: n
       integer(c_int) :: base
     end function clotran_frame_enter
     subroutine clotran_frame_leave(cs, base) bind(C, name="clotran_frame_leave")
       import :: c_ptr, c_int
       type(c_ptr), value :: cs
       integer(c_int), value :: base
     end subroutine clotran_frame_leave
     subroutine clotran_set_int(cs, slot, n) bind(C, name="clotran_set_int")
       import :: c_ptr, c_int, c_int64_t
       type(c_ptr), value :: cs
       integer(c_int), value :: slot
       integer(c_int64_t), value :: n
     end subroutine clotran_set_int
     function clotran_bool(cs, slot) bind(C, name="clotran_bool") result(b)
       import :: c_ptr, c_int
       type(c_ptr), value :: cs
       integer(c_int), value :: slot
       integer(c_int) :: b, me, rel
     end function clotran_bool
     subroutine clotran_vec_empty(slot) bind(C, name="clotran_vec_empty")
       import :: c_int
       integer(c_int), value :: slot
     end subroutine clotran_vec_empty
     subroutine clotran_vec_conj(dst, vec, x) bind(C, name="clotran_vec_conj")
       import :: c_int
       integer(c_int), value :: dst, vec, x
     end subroutine clotran_vec_conj
     function clotran_var(slot, ns, nsn, name, namen) bind(C, name="clotran_var") result(ok)
       import :: c_char, c_int
       integer(c_int), value :: slot
       character(kind=c_char), intent(in) :: ns(*), name(*)
       integer(c_int), value :: nsn, namen
       integer(c_int) :: ok
     end function clotran_var
     subroutine clotran_deref(cs, dst, var) bind(C, name="clotran_deref")
       import :: c_ptr, c_int
       type(c_ptr), value :: cs
       integer(c_int), value :: dst, var
     end subroutine clotran_deref
     function clotran_call(dst, fn, args) bind(C, name="clotran_call") result(st)
       import :: c_int
       integer(c_int), value :: dst, fn, args
       integer(c_int) :: st
     end function clotran_call
     function clotran_array_view(cs, slot, kind, ptr, n) bind(C, name="clotran_array_view") result(ok)
       import :: c_ptr, c_int, c_int64_t
       type(c_ptr), value :: cs
       integer(c_int), value :: slot, kind
       type(c_ptr), intent(out) :: ptr
       integer(c_int64_t), intent(out) :: n
       integer(c_int) :: ok
     end function clotran_array_view
     subroutine clotran_native_begin(me, rel) bind(C, name="clotran_native_begin")
       import :: c_int
       integer(c_int), intent(out) :: me, rel
     end subroutine clotran_native_begin
     subroutine clotran_reacquire(me, rel) bind(C, name="clotran_reacquire")
       import :: c_int
       integer(c_int), value :: me
       integer(c_int), intent(inout) :: rel
     end subroutine clotran_reacquire
     function clotran_error_copy(buf, n) bind(C, name="clotran_error_copy") result(w)
       import :: c_int, c_char
       character(kind=c_char), intent(out) :: buf(*)
       integer(c_int), value :: n
       integer(c_int) :: w
     end function clotran_error_copy
  end interface
end module embed_abi

program heat
  use iso_c_binding
  use embed_abi
  implicit none
  integer, parameter :: nx = 64, nsteps = 2000, every = 100
  ! dt/dx^2; explicit diffusion is stable below one half
  real(c_double), parameter :: r = 0.25_c_double
  type(c_ptr) :: cs, p
  integer(c_int) :: b, me, rel
  integer(c_int64_t) :: n
  real(c_double), pointer, contiguous :: u(:)
  real(c_double) :: lap(nx)
  integer :: step, i

  call clotran_init()
  cs = clotran_stack()
  call must(clotran_boot(cbuf("."), 1_c_int), "boot")
  ! four slots on the runtime's shadow stack: the grid, a function, its
  ! arguments, its answer. A slot is a root, which is what keeps the
  ! grid alive for the whole run: no value is held anywhere else.
  b = clotran_frame_enter(cs, 4_c_int)
  call must(ev("(load-file ""src/clj/clojure/core.clj"")", b + 4), "core.clj")
  call must(ev("(load-file ""examples/embed/control.cljf"")", b + 4), "control.cljf")

  ! THE GRID: allocated by the runtime, integrated here. The address is
  ! good for as long as the array lives -- the collector does not move
  ! objects -- and the array lives while slot b+1 holds it.
  call must(ev("(double-array 64)", b + 1), "double-array")
  if (clotran_array_view(cs, b + 1, 1_c_int, p, n) /= 1) stop "not a double array"
  call c_f_pointer(p, u, [n])
  u = 0.0_c_double

  ! Clojure writes the initial condition into u(:)
  call control("init!", 0)
  print '(a,f8.3,a,f8.3)', "fortran  read it back              total ", sum(u), "  peak ", maxval(u)
  ! a REPL into the run, if HEAT_REPL names a port
  call control("serve!", 0)

  ! the solver's own work runs outside the heap; it steps back in to call
  ! Clojure, and out again after
  call clotran_native_begin(me, rel)
  do step = 1, nsteps
     do i = 2, nx - 1
        lap(i) = u(i - 1) - 2.0_c_double * u(i) + u(i + 1)
     end do
     do i = 2, nx - 1
        u(i) = u(i) + r * lap(i)
     end do
     if (mod(step, every) == 0) then
        ! the strategy: reads the grid, may write it, says whether to go on
        call clotran_reacquire(me, rel)
        call control("on-step", step)
        if (clotran_bool(cs, b + 4) == 0) exit
        call clotran_native_begin(me, rel)
     end if
  end do
  call clotran_reacquire(me, rel)
  print '(a,i4,a,f8.3,a,f8.3)', "fortran  stopped at step ", min(step, nsteps), "      total ", sum(u), "  peak ", maxval(u)
  call clotran_frame_leave(cs, b)

contains

  ! (embed.control/name u) or (embed.control/name u step), the answer
  ! left in slot b+4
  subroutine control(name, step)
    character(len=*), intent(in) :: name
    integer, intent(in) :: step
    character(len=*), parameter :: ns = "embed.control"
    if (clotran_var(b + 2, cbuf(ns), int(len(ns), c_int), cbuf(name), int(len(name), c_int)) /= 1) &
         stop "no such function"
    call clotran_deref(cs, b + 2, b + 2)
    call clotran_vec_empty(b + 3)
    call clotran_vec_conj(b + 3, b + 3, b + 1)
    if (step > 0) then
       call clotran_set_int(cs, b + 4, int(step, c_int64_t))
       call clotran_vec_conj(b + 3, b + 3, b + 4)
    end if
    call must(clotran_call(b + 4, b + 2, b + 3), name)
  end subroutine control

  function ev(s, slot) result(st)
    character(len=*), intent(in) :: s
    integer(c_int), intent(in) :: slot
    integer(c_int) :: st
    st = clotran_eval(cbuf(s), int(len(s), c_int), slot)
  end function ev

  ! A Fortran string as the (chars, n) pair every text entry point takes.
  function cbuf(s) result(a)
    character(len=*), intent(in) :: s
    character(kind=c_char) :: a(len(s))
    integer :: i
    do i = 1, len(s)
       a(i) = s(i:i)
    end do
  end function cbuf

  ! An error is reported, never thrown across this boundary: read it.
  subroutine must(st, what)
    integer(c_int), intent(in) :: st
    character(len=*), intent(in) :: what
    character(kind=c_char) :: eb(400)
    character(len=400) :: msg
    integer(c_int) :: w
    integer :: i
    if (st == 0) return
    w = clotran_error_copy(eb, 400_c_int)
    msg = ""
    do i = 1, int(w)
       msg(i:i) = eb(i)
    end do
    print *, what, " failed: ", trim(msg)
    stop 1
  end subroutine must
end program heat
