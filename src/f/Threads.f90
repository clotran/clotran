! Threads.f90 -- OS threads for clotran's tasks (PLAN.md step 11, stage 1).
!
! The whole interface: start a thread running a procedure, join it, and
! a lock and a condition to hand work between threads. Nothing else, on
! purpose: a thread here exists to give a task its OWN machine stack, so
! a task blocked below compiled code can wait where it is instead of
! pinning (DEVIATIONS 49). Only one thread runs clotran code at a time
! -- the baton, Eval's business -- so the heap stays single-threaded.
!
! This is the POSIX implementation: pthreads, bound straight through
! iso_c_binding, with no C of clotran's own. macOS and Linux share it;
! Windows gets a second file behind the same interface (PACKAGES.md,
! the OS seam), as LLVM's OpenMP runtime keeps z_Linux_util.cpp and
! z_Windows_NT_util.cpp.
!
! A pthread_mutex_t and a pthread_cond_t are opaque structs of a
! platform's own size -- 64 and 48 bytes on macOS, 40 and 48 with glibc
! -- so each lives in 128 bytes of 8-byte-aligned storage, which covers
! both with room to spare.
module Threads
  use iso_c_binding
  implicit none
  private

  public :: th_lock, th_cond, th_thread
  public :: th_lock_init, th_lock_acquire, th_lock_release
  public :: th_cond_init, th_cond_wait, th_cond_broadcast
  public :: th_start, th_join, th_spawn, th_exit

  integer, parameter :: OPAQUE_WORDS = 16   ! 128 bytes

  type :: th_lock
     integer(c_int64_t) :: raw(OPAQUE_WORDS) = 0
  end type th_lock

  type :: th_cond
     integer(c_int64_t) :: raw(OPAQUE_WORDS) = 0
  end type th_cond

  type :: th_thread
     type(c_ptr) :: handle = c_null_ptr
  end type th_thread

  interface
     function pthread_create(t, attr, fn, arg) bind(C, name="pthread_create") result(r)
       import :: c_ptr, c_funptr, c_int
       type(c_ptr) :: t
       type(c_ptr), value :: attr, arg
       type(c_funptr), value :: fn
       integer(c_int) :: r
     end function pthread_create
     function pthread_join(t, ret) bind(C, name="pthread_join") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: t, ret
       integer(c_int) :: r
     end function pthread_join
     function pthread_mutex_init(m, a) bind(C, name="pthread_mutex_init") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: m, a
       integer(c_int) :: r
     end function pthread_mutex_init
     function pthread_mutex_lock(m) bind(C, name="pthread_mutex_lock") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: m
       integer(c_int) :: r
     end function pthread_mutex_lock
     function pthread_mutex_unlock(m) bind(C, name="pthread_mutex_unlock") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: m
       integer(c_int) :: r
     end function pthread_mutex_unlock
     function pthread_cond_init(c, a) bind(C, name="pthread_cond_init") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: c, a
       integer(c_int) :: r
     end function pthread_cond_init
     function pthread_cond_wait(c, m) bind(C, name="pthread_cond_wait") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: c, m
       integer(c_int) :: r
     end function pthread_cond_wait
     function pthread_cond_broadcast(c) bind(C, name="pthread_cond_broadcast") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: c
       integer(c_int) :: r
     end function pthread_cond_broadcast
     function pthread_detach(t) bind(C, name="pthread_detach") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: t
       integer(c_int) :: r
     end function pthread_detach
     subroutine pthread_exit(ret) bind(C, name="pthread_exit")
       import :: c_ptr
       type(c_ptr), value :: ret
     end subroutine pthread_exit
     function pthread_attr_init(a) bind(C, name="pthread_attr_init") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: a
       integer(c_int) :: r
     end function pthread_attr_init
     function pthread_attr_destroy(a) bind(C, name="pthread_attr_destroy") result(r)
       import :: c_ptr, c_int
       type(c_ptr), value :: a
       integer(c_int) :: r
     end function pthread_attr_destroy
     function pthread_attr_setstacksize(a, n) bind(C, name="pthread_attr_setstacksize") result(r)
       import :: c_ptr, c_int, c_size_t
       type(c_ptr), value :: a
       integer(c_size_t), value :: n
       integer(c_int) :: r
     end function pthread_attr_setstacksize
  end interface

contains

  ! Each routine answers .true. on success; the pthread error number is
  ! not interpreted here -- the caller only needs to know the step failed.

  logical function th_lock_init(l)
    type(th_lock), target, intent(inout) :: l
    th_lock_init = pthread_mutex_init(c_loc(l%raw), c_null_ptr) == 0
  end function th_lock_init

  logical function th_lock_acquire(l)
    type(th_lock), target, intent(inout) :: l
    th_lock_acquire = pthread_mutex_lock(c_loc(l%raw)) == 0
  end function th_lock_acquire

  logical function th_lock_release(l)
    type(th_lock), target, intent(inout) :: l
    th_lock_release = pthread_mutex_unlock(c_loc(l%raw)) == 0
  end function th_lock_release

  logical function th_cond_init(c)
    type(th_cond), target, intent(inout) :: c
    th_cond_init = pthread_cond_init(c_loc(c%raw), c_null_ptr) == 0
  end function th_cond_init

  ! Wait on c, releasing l while waiting and holding it again on return.
  ! A wake-up can be spurious: callers re-check their condition in a loop.
  logical function th_cond_wait(c, l)
    type(th_cond), target, intent(inout) :: c
    type(th_lock), target, intent(inout) :: l
    th_cond_wait = pthread_cond_wait(c_loc(c%raw), c_loc(l%raw)) == 0
  end function th_cond_wait

  logical function th_cond_broadcast(c)
    type(th_cond), target, intent(inout) :: c
    th_cond_broadcast = pthread_cond_broadcast(c_loc(c%raw)) == 0
  end function th_cond_broadcast

  ! Start a thread running fn(arg). fn must be a bind(C) function taking
  ! one c_ptr by value and answering a c_ptr.
  logical function th_start(t, fn, arg)
    type(th_thread), intent(inout) :: t
    type(c_funptr), intent(in) :: fn
    type(c_ptr), intent(in) :: arg
    th_start = pthread_create(t%handle, c_null_ptr, fn, arg) == 0
  end function th_start

  ! Start a DETACHED thread running fn(arg) on a stack of `bytes`: a
  ! task's thread runs the interpreter, whose depth the main thread's
  ! 8 MB bounds, and a secondary thread's default is far smaller (512 KB
  ! on macOS). Detached by pthread_detach rather than an attribute, whose
  ! constant differs between macOS and Linux.
  logical function th_spawn(fn, arg, bytes)
    type(c_funptr), intent(in) :: fn
    type(c_ptr), intent(in) :: arg
    integer(c_size_t), intent(in) :: bytes
    integer(c_int64_t), target :: attr(OPAQUE_WORDS)
    type(c_ptr) :: t
    th_spawn = .false.
    attr = 0
    if (pthread_attr_init(c_loc(attr)) /= 0) return
    if (pthread_attr_setstacksize(c_loc(attr), bytes) /= 0) return
    if (pthread_create(t, c_loc(attr), fn, arg) /= 0) return
    if (pthread_attr_destroy(c_loc(attr)) /= 0) return
    th_spawn = pthread_detach(t) == 0
  end function th_spawn

  ! End the calling thread here, unwinding nothing.
  subroutine th_exit()
    call pthread_exit(c_null_ptr)
  end subroutine th_exit

  logical function th_join(t)
    type(th_thread), intent(inout) :: t
    th_join = pthread_join(t%handle, c_null_ptr) == 0
  end function th_join

end module Threads
