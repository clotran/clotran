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

  public :: th_lock, th_cond, th_thread, th_start_sized
  public :: th_lock_init, th_lock_acquire, th_lock_release
  public :: th_cond_init, th_cond_wait, th_cond_broadcast
  public :: th_start, th_join, th_spawn, th_exit, th_ncpus
  public :: th_key, th_key_create, th_key_set, th_key_get
  public :: th_cond_timedwait, th_sleep_ms

  integer, parameter :: OPAQUE_WORDS = 16   ! 128 bytes
  ! the platform's sysconf name for online processors (Makefile)
  include 'osconst.inc'

  type :: th_lock
     integer(c_int64_t) :: raw(OPAQUE_WORDS) = 0
  end type th_lock

  type :: th_cond
     integer(c_int64_t) :: raw(OPAQUE_WORDS) = 0
  end type th_cond

  type :: th_thread
     type(c_ptr) :: handle = c_null_ptr
  end type th_thread

  ! A thread-local slot: one pointer per thread under one key. Standard
  ! Fortran has no thread-local variables, so this is how a thread finds
  ! its own state (PLAN.md step 14b). pthread_key_t is an unsigned long
  ! on macOS and an unsigned int in glibc and musl: PTHREAD_KEY_KIND.
  type :: th_key
     integer(PTHREAD_KEY_KIND) :: k = 0
     integer :: slot = 0
  end type th_key

  ! WHILE ONE THREAD RUNS CLOTRAN, its slots are plain variables: a
  ! lookup per runtime entry was 15% of a compiled loop's samples. The
  ! OWNER is the first thread to set a key (the evaluator's, main.f90);
  ! its values are kept here on every set. th_start and th_spawn turn
  ! the cache off for good before the new thread exists, and so does a
  ! set from any other thread (an embedder's own); from then on every
  ! lookup is pthread's, the owner's included -- the cache still agrees
  ! with it, as the owner keeps updating it.
  integer, parameter :: TLS_SLOTS = 16
  type(c_ptr), save :: tls_cache(TLS_SLOTS) = c_null_ptr
  logical, save :: tls_multi = .false.
  logical, save :: tls_owned = .false.
  integer(c_intptr_t), save :: tls_owner = 0
  integer, save :: tls_next = 0

  interface
     function pthread_create(t, attr, fn, arg) bind(C, name="pthread_create") result(r)
       import :: c_ptr, c_funptr, c_int
       type(c_ptr) :: t
       type(c_ptr), value :: attr, arg
       type(c_funptr), value :: fn
       integer(c_int) :: r
     end function pthread_create
     function pthread_key_create(k, d) bind(C, name="pthread_key_create") result(r)
       import :: c_funptr, c_int, PTHREAD_KEY_KIND
       integer(PTHREAD_KEY_KIND) :: k
       type(c_funptr), value :: d
       integer(c_int) :: r
     end function pthread_key_create
     function pthread_setspecific(k, v) bind(C, name="pthread_setspecific") result(r)
       import :: c_ptr, c_int, PTHREAD_KEY_KIND
       integer(PTHREAD_KEY_KIND), value :: k
       type(c_ptr), value :: v
       integer(c_int) :: r
     end function pthread_setspecific
     function pthread_self() bind(C, name="pthread_self") result(t)
       import :: c_intptr_t
       integer(c_intptr_t) :: t
     end function pthread_self
     function pthread_getspecific(k) bind(C, name="pthread_getspecific") result(v)
       import :: c_ptr, PTHREAD_KEY_KIND
       integer(PTHREAD_KEY_KIND), value :: k
       type(c_ptr) :: v
     end function pthread_getspecific
     ! struct timespec is two C longs on macOS (sys/_types/_timespec.h)
     ! and on 64-bit glibc; CLOCK_REALTIME is 0 on both (_time.h,
     ! bits/time.h)
     function pthread_cond_timedwait(c, m, ts) bind(C, name="pthread_cond_timedwait") result(r)
       import :: c_ptr, c_int, c_long
       type(c_ptr), value :: c, m
       integer(c_long), intent(in) :: ts(2)
       integer(c_int) :: r
     end function pthread_cond_timedwait
     function clock_gettime(id, ts) bind(C, name="clock_gettime") result(r)
       import :: c_int, c_long
       integer(c_int), value :: id
       integer(c_long), intent(out) :: ts(2)
       integer(c_int) :: r
     end function clock_gettime
     function nanosleep(req, rem) bind(C, name="nanosleep") result(r)
       import :: c_int, c_long, c_ptr
       integer(c_long), intent(in) :: req(2)
       type(c_ptr), value :: rem
       integer(c_int) :: r
     end function nanosleep
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
     function sysconf(name) bind(C, name="sysconf") result(r)
       import :: c_int, c_long
       integer(c_int), value :: name
       integer(c_long) :: r
     end function sysconf
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
  ! fn by VALUE in each of these: by reference, gfortran made a call's
  ! c_funloc(...) a constant in .rodata, holding an address the loader
  ! must relocate -- a text relocation, which musl's loader does not do
  ! (it crashed before main on Alpine) and hardened systems refuse.
  logical function th_start(t, fn, arg)
    type(th_thread), intent(inout) :: t
    type(c_funptr), value :: fn
    type(c_ptr), intent(in) :: arg
    tls_multi = .true.
    th_start = pthread_create(t%handle, c_null_ptr, fn, arg) == 0
  end function th_start

  ! Start a JOINABLE thread running fn(arg) on a stack of `bytes`: the
  ! program's own body (main.f90), which needs more than the main
  ! thread's 8 MB.
  logical function th_start_sized(t, fn, arg, bytes)
    type(th_thread), intent(inout) :: t
    type(c_funptr), value :: fn
    type(c_ptr), intent(in) :: arg
    integer(c_size_t), intent(in) :: bytes
    integer(c_int64_t), target :: attr(OPAQUE_WORDS)
    th_start_sized = .false.
    attr = 0
    if (pthread_attr_init(c_loc(attr)) /= 0) return
    if (pthread_attr_setstacksize(c_loc(attr), bytes) /= 0) return
    th_start_sized = pthread_create(t%handle, c_loc(attr), fn, arg) == 0
    if (pthread_attr_destroy(c_loc(attr)) /= 0) continue
  end function th_start_sized

  ! Start a DETACHED thread running fn(arg) on a stack of `bytes`: a
  ! task's thread runs the interpreter, whose depth the main thread's
  ! 8 MB bounds, and a secondary thread's default is far smaller (512 KB
  ! on macOS). Detached by pthread_detach rather than an attribute, whose
  ! constant differs between macOS and Linux.
  logical function th_spawn(fn, arg, bytes)
    type(c_funptr), value :: fn
    type(c_ptr), intent(in) :: arg
    integer(c_size_t), intent(in) :: bytes
    integer(c_int64_t), target :: attr(OPAQUE_WORDS)
    type(c_ptr) :: t
    th_spawn = .false.
    attr = 0
    if (pthread_attr_init(c_loc(attr)) /= 0) return
    if (pthread_attr_setstacksize(c_loc(attr), bytes) /= 0) return
    tls_multi = .true.
    if (pthread_create(t, c_loc(attr), fn, arg) /= 0) return
    if (pthread_attr_destroy(c_loc(attr)) /= 0) return
    th_spawn = pthread_detach(t) == 0
  end function th_spawn

  ! Processors online now: Runtime.availableProcessors, which sizes
  ! pmap's look-ahead. At least 1, whatever sysconf answers.
  integer function th_ncpus()
    th_ncpus = max(1, int(sysconf(SC_NPROCESSORS_ONLN)))
  end function th_ncpus

  ! End the calling thread here, unwinding nothing.
  subroutine th_exit()
    call pthread_exit(c_null_ptr)
  end subroutine th_exit

  ! A new key; every thread's slot under it starts null.
  logical function th_key_create(key)
    type(th_key), intent(inout) :: key
    th_key_create = pthread_key_create(key%k, c_null_funptr) == 0
    tls_next = tls_next + 1
    if (tls_next > TLS_SLOTS) error stop "clotran: more thread keys than TLS_SLOTS"
    key%slot = tls_next
  end function th_key_create

  ! This thread's slot under key -- no other thread's changes.
  logical function th_key_set(key, p)
    type(th_key), intent(in) :: key
    type(c_ptr), intent(in) :: p
    integer(c_intptr_t) :: me
    th_key_set = pthread_setspecific(key%k, p) == 0
    me = pthread_self()
    if (.not. tls_owned) then
       tls_owner = me
       tls_owned = .true.
    end if
    if (me == tls_owner) then
       tls_cache(key%slot) = p
    else
       tls_multi = .true.
    end if
  end function th_key_set

  ! This thread's slot under key: null until this thread sets it.
  type(c_ptr) function th_key_get(key)
    type(th_key), intent(in) :: key
    if (.not. tls_multi) then
       th_key_get = tls_cache(key%slot)
       return
    end if
    th_key_get = pthread_getspecific(key%k)
  end function th_key_get

  ! Wait on c at most ms milliseconds: .true. when woken, .false. when
  ! the time ran out. Spurious wake-ups happen: callers re-check.
  logical function th_cond_timedwait(c, l, ms)
    type(th_cond), target, intent(inout) :: c
    type(th_lock), target, intent(inout) :: l
    integer(c_long), intent(in) :: ms
    integer(c_long) :: ts(2)
    integer(c_int) :: r
    r = clock_gettime(0_c_int, ts)
    ts(1) = ts(1) + ms / 1000_c_long
    ts(2) = ts(2) + mod(ms, 1000_c_long) * 1000000_c_long
    if (ts(2) >= 1000000000_c_long) then
       ts(1) = ts(1) + 1
       ts(2) = ts(2) - 1000000000_c_long
    end if
    th_cond_timedwait = pthread_cond_timedwait(c_loc(c%raw), c_loc(l%raw), ts) == 0
  end function th_cond_timedwait

  ! Sleep this thread ms milliseconds.
  subroutine th_sleep_ms(ms)
    integer(c_long), intent(in) :: ms
    integer(c_long) :: ts(2)
    integer(c_int) :: r
    ts(1) = ms / 1000_c_long
    ts(2) = mod(ms, 1000_c_long) * 1000000_c_long
    r = nanosleep(ts, c_null_ptr)
  end subroutine th_sleep_ms

  logical function th_join(t)
    type(th_thread), intent(inout) :: t
    th_join = pthread_join(t%handle, c_null_ptr) == 0
  end function th_join

end module Threads
