! clotran-bin: load the files named on the command line, then a REPL.
! ./clotran, the launcher, wraps this in rlwrap and hands it core.clj.
!
! Reads a form per line, evaluates, prints. No line editing of its own
! -- the launcher supplies rlwrap.
program clotran
  use GC
  use LispReader
  use Printer
  use Eval
  use Namespace
  use PersistentVector
  implicit none

  type(gc_value) :: env
  type(gc_value) :: none(0)
  integer :: base, i, arglen, st
  character(len=1024) :: argbuf
  character(len=8) :: statbuf, tortbuf

  call gc_init(65536)
  block
     character(len=:), allocatable :: dlr_1
     call home_dir(d=dlr_1)
     call gce_set_home(dlr_1)
  end block
  base = vs_enter(3)
  env = gce_base_env(none)
  call vs_set(base + 1, env)

  ! The host shim -- type predicates that core.clj cannot supply,
  ! because it would ask instance? about Java classes. NOT a core
  ! library: everything else Clojure programs use must come from
  ! the real core.clj, which is the point of the project.
  block
     character(len=:), allocatable :: dlr_2
     call under_home("src/clj/host.clj", p=dlr_2)
     call load_file(dlr_2, vs_get(base + 1))
  end block
  ! host.clj leaves clojure.core current, being part of its bootstrap.

  ! Any files named on the command line load next, in order, so
  ! that `clotran some.clj` is how a file gets tried against
  ! this evaluator. Loading real core.clj is the point: the first
  ! error it reports IS the next thing to build.
  do i = 1, command_argument_count()
     call get_command_argument(i, argbuf, arglen)
     call load_file(argbuf(1:arglen), vs_get(base + 1))
     ! RT.CHECK_SPECS: once core.clj -- the first file -- has loaded,
     ! every macro call is checked against clojure.core.specs.alpha,
     ! unless CLOTRAN_SPEC_SKIP_MACROS is set (clojure.spec.skip-macros)
     if (i == 1) then
        call gce_main_bindings()
        ! CLOTRAN_GC_TORTURE=1 collects at EVERY allocation from here on --
        ! what test/f's torture pass does, and the only way a rooting bug
        ! shows reliably: a value that is not on the shadow stack is
        ! collected the moment the next allocation happens. It starts
        ! AFTER the first file (core.clj takes minutes under it), so the
        ! form under suspicion runs tortured and the bootstrap does not.
        call get_environment_variable("CLOTRAN_GC_TORTURE", tortbuf)
        gc_torture = (trim(tortbuf) == "1")
        call get_environment_variable("CLOTRAN_SPEC_SKIP_MACROS", status=st)
        call gce_set_spec_check(st /= 0)
     end if
  end do

  ! The REPL starts in user, as Clojure's does -- AFTER the files on the
  ! command line, because core.clj's own (ns clojure.core) leaves that
  ! namespace current and anything typed at the prompt would otherwise
  ! be defined into clojure.core.
  call gcn_set_current(gcn_find_or_create("user", none))

  ! The loop itself is Eval's (repl.inc): the same loop runs nested at
  ! a break, where it is the debugger's default handler.
  call gce_repl()
  print *, ""
  call get_environment_variable("CLOTRAN_STATS", statbuf)
  if (trim(statbuf) == "1") then
     write(0, '(A,I0,A,I0,A,I0,A,I0,A,I0)') "stats: evals=", gce_evals, " allocs=", gc_allocs, &
          " collections=", gc_collections, " marked=", gc_marked, " obj_capacity=", gc_obj_capacity()
     block
       integer :: cap, used, live
       call gc_arena_stats(cap, used, live)
       write(0, '(A,I0,A,I0,A,I0)') "arena: capacity=", cap, " used=", used, " live=", live
     end block
     write(0, '(A,I0,A,F0.1,A,F0.2,A,I0,A,F0.1,A,F0.2)') "pauses: young ", gc_young_collections, &
          " total_ms=", gc_young_ms, " max_ms=", gc_young_max_ms, &
          " full ", gc_collections - gc_young_collections, " total_ms=", gc_full_ms, " max_ms=", gc_full_max_ms
  end if

contains

  ! Reads a whole file and evaluates every form in it.
  !
  ! The first error ENDS THE LOAD, as Compiler.load does -- its only
  ! catch is for ReaderException, to attach a line and rethrow.
  !
  ! This started out the other way, reporting each failure and carrying
  ! on, on the theory that the useful number was how much of core.clj
  ! works. It is not, and core.clj demonstrated why. (defmacro let ...)
  ! expands to a `do`: the defn inside it SUCCEEDED and replaced the
  ! working bootstrap `let` with the destructuring one, and only the
  ! form after it failed. Carrying on left a namespace holding a `let`
  ! whose own dependencies had never loaded -- one missing definition,
  ! 206 cascading failures, and a count that measured nothing.
  !
  ! Stopping is not caution, it is the only way the count means
  ! anything: N forms in, this is the first thing missing.
  !
  ! One deviation remains, recorded as #1: Clojure interleaves read and
  ! eval, one form at a time, and we read the whole file first.
  subroutine load_file(path, env)
    character(len=*), intent(in) :: path
    type(gc_value), intent(in) :: env
    character(len=:), allocatable :: text
    type(gc_value) :: forms, r
    integer :: u, st, lb, i, fsize, pos, fid
    logical :: eof
    character(len=8) :: envbuf
    logical :: trace

    ! Read in ONE allocation, via stream access, rather than
    ! appending line by line. Appending is O(n^2) -- each // builds a
    ! whole new string -- and on an 8000-line file that is not slow,
    ! it is indistinguishable from a hang. An earlier reader carried the
    ! same warning for the same reason; this repeated the mistake.
    open(newunit=u, file=path, access="stream", form="unformatted", &
         status="old", action="read", iostat=st)
    if (st /= 0) then
       print '(A,A)', "load: cannot open ", path
       return
    end if
    inquire(unit=u, size=fsize)
    allocate(character(len=fsize) :: text)
    read(u, iostat=st) text
    close(u)

    lb = vs_enter(3)
    call vs_set(lb + 1, env)
    ! CLOTRAN_LOAD_TRACE=1 names each form before evaluating it. An
    ! error names its own form; a HANG does not, and this is the only
    ! way to see which form never came back.
    call get_environment_variable("CLOTRAN_LOAD_TRACE", envbuf)
    trace = (trim(envbuf) == "1")

    ! One form at a time: read, analyse, evaluate, read the next -- as
    ! Compiler.load does, so a form sees what the one before it did
    ! to *ns*, *data-readers* or a ::keyword's namespace.
    fid = gcr_begin_file(text, path)
    pos = 1
    i = 0
    do
       forms = gcr_read_next(text, pos, [vs_get(lb + 1)], eof, fid)
       if (gcr_has_error()) then
          block
             character(len=:), allocatable :: dlr_3
             call gcr_error(s=dlr_3)
             print '(A,A,A,A)', "load ", path, ": reader error: ", dlr_3
          end block
          exit
       end if
       if (eof) exit
       i = i + 1
       call vs_set(lb + 2, forms)
       if (trace) then
          block
             character(len=:), allocatable :: dlr_4, dlr_5
             call gcp_str(vs_get(lb + 2), .true., s=dlr_4)
             call first_line(dlr_4, out=dlr_5)
             print '(A,I0,A,A)', "[", i, "] ", dlr_5
          end block
          flush(6)
       end if
       call gce_clear_error()
       r = gce_analyze(vs_get(lb + 2), vs_get(lb + 1))
       if (.not. gce_has_error()) r = gce_eval(r, vs_get(lb + 1), no_roots())
       call vs_set(lb + 3, r)
       if (gce_has_error()) then
          block
             character(len=:), allocatable :: dlr_6
             call gce_error(s=dlr_6)
             print '(A,A)', "  ", dlr_6
          end block
          block
             character(len=:), allocatable :: dlr_7, dlr_8
             call gce_trace(s=dlr_7)
             if (len(dlr_7) > 0) then
                call gce_trace(s=dlr_8)
                write(*, '(A)', advance='no') dlr_8
             end if
          end block
          block
             character(len=:), allocatable :: dlr_9, dlr_10
             call gcp_str(vs_get(lb + 2), .true., s=dlr_9)
             call first_line(dlr_9, out=dlr_10)
             print '(A,A)', "    in: ", dlr_10
          end block
          print '(A,A,A,I0)', "load ", path, ": stopped at form ", i
          call vs_leave(lb)
          return
       end if
    end do
    call vs_leave(lb)
    if (.not. gcr_has_error()) call gce_install_compiled(path)
  end subroutine load_file

  ! Just enough of a form to identify it in a report.
  subroutine first_line(t, out)
    character(len=*), intent(in) :: t
    character(len=:), allocatable, intent(out) :: out
    integer :: k
    out = t
    k = index(t, achar(10))
    if (k > 0) out = t(1:k-1)
    if (len(out) > 72) then
       block
          character(len=:), allocatable :: dlw
          dlw = out(1:72) // "..."
          call move_alloc(dlw, out)
       end block
    end if
  end subroutine first_line

  function no_roots() result(r)
    type(gc_value) :: r(0)
  end function no_roots

  ! The directory the binary was started from, by argv(0): the repo
  ! root when it is ./clotran, and a classpath root either way (Eval's
  ! classpath_find), so `clotran` works from any directory.
  subroutine home_dir(d)
    character(len=:), allocatable, intent(out) :: d
    character(len=1024) :: exe
    integer :: n, k
    d = "."
    call get_command_argument(0, exe, n)
    k = index(exe(1:n), "/", back=.true.)
    if (k > 1) d = exe(1:k-1)
  end subroutine home_dir

  ! A file relative to the cwd if it is there, else under home.
  subroutine under_home(rel, p)
    character(len=*), intent(in) :: rel
    character(len=:), allocatable, intent(out) :: p
    logical :: there
    p = rel
    inquire(file=p, exist=there)
    if (.not. there) then
       block
          character(len=:), allocatable :: dlr_11
          call gce_home(h=dlr_11)
          p = dlr_11 // "/" // rel
       end block
    end if
  end subroutine under_home

end program clotran
