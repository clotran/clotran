! The clotran program: load the files named on the command line, then
! a REPL. scripts/clotran wraps this in rlwrap and hands it core.clj.
!
! Reads a form per line, evaluates, prints. No line editing of its own
! -- scripts/clotran's rlwrap trick applies here too if wanted.
program clotran
  use GC
  use LispReader
  use Printer
  use Eval
  use Namespace
  use PersistentVector
  implicit none

  character(len=:), allocatable :: line, pending
  character(len=4096) :: buf
  type(gc_value) :: env, form, result
  type(gc_value) :: none(0)
  integer :: base, ios, size_read, i, arglen
  character(len=1024) :: argbuf

  call gc_init(65536)
  base = vs_enter(3)
  env = gce_base_env(none)
  call vs_set(base + 1, env)

  ! The host shim -- type predicates that core.clj cannot supply,
  ! because it would ask instance? about Java classes. NOT a core
  ! library: everything else Clojure programs use must come from
  ! the real core.clj, which is the point of the project.
  call load_file("src/clj/host.clj", vs_get(base + 1))
  ! host.clj leaves clojure.core current, being part of its bootstrap.

  ! Any files named on the command line load next, in order, so
  ! that `clotran some.clj` is how a file gets tried against
  ! this evaluator. Loading real core.clj is the point: the first
  ! error it reports IS the next thing to build.
  do i = 1, command_argument_count()
     call get_command_argument(i, argbuf, arglen)
     call load_file(argbuf(1:arglen), vs_get(base + 1))
  end do

  ! The REPL starts in user, as Clojure's does -- AFTER the files on the
  ! command line, because core.clj's own (ns clojure.core) leaves that
  ! namespace current and anything typed at the prompt would otherwise
  ! be defined into clojure.core.
  call gcn_set_current(gcn_find_or_create("user", none))

  ! The REPL reads FORMS, not lines. A line that does not close what it
  ! opened is not an error, it is a request for more input -- without
  ! this, (defn f [x] <enter> was unusable and every definition had to
  ! be typed on one line.
  pending = ""
  do
     if (len(pending) == 0) then
        write(*, '(A)', advance='no') gcn_name(gcn_current(none)) // "=> "
     else
        write(*, '(A)', advance='no') "#_=> "
     end if
     flush(6)
     read(*, '(A)', iostat=ios, size=size_read, advance='no') buf
     if (ios < 0 .and. size_read == 0) exit   ! EOF
     line = trim(buf(1:max(size_read, 0)))
     if (len(pending) == 0 .and. len(line) == 0) cycle
     if (len(pending) == 0) then
        pending = line
     else
        ! Newline, not a space: a ; comment must still end at its line.
        pending = pending // new_line('a') // line
     end if

     form = gcr_read(pending, [vs_get(base + 1)])
     if (gcr_has_error()) then
        ! Every unclosed-form message the reader produces begins this
        ! way -- an unclosed list, vector, map, string or regex. Any
        ! other reader error is real.
        if (index(gcr_error(), "EOF while reading") == 1) cycle
        print '(A,A)', "reader error: ", gcr_error()
        pending = ""
        cycle
     end if
     pending = ""
     call vs_set(base + 2, form)

     call gce_clear_error()
     result = gce_analyze(vs_get(base + 2), vs_get(base + 1))
     if (.not. gce_has_error()) &
          result = gce_eval(result, vs_get(base + 1), no_roots())
     call vs_set(base + 3, result)
     if (gce_has_error()) then
        print '(A,A)', "error: ", gce_error()
        cycle
     end if
     print '(A)', gcp_str(vs_get(base + 3), .true.)
  end do
  print *, ""

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
    integer :: u, st, lb, i, fsize, nfail
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
    forms = gcr_read_all(text, [vs_get(lb + 1)])
    if (gcr_has_error()) then
       print '(A,A,A,A)', "load ", path, ": reader error: ", gcr_error()
       call vs_leave(lb)
       return
    end if
    call vs_set(lb + 2, forms)
    ! CLOTRAN_LOAD_TRACE=1 names each form before evaluating it. An
    ! error names its own form; a HANG does not, and this is the only
    ! way to see which form never came back.
    call get_environment_variable("CLOTRAN_LOAD_TRACE", envbuf)
    trace = (trim(envbuf) == "1")

    nfail = 0
    do i = 0, gcv_count(vs_get(lb + 2)) - 1
       if (trace) then
          print '(A,I0,A,A)', "[", i + 1, "] ", &
               first_line(gcp_str(gcv_nth(vs_get(lb + 2), i), .true.))
          flush(6)
       end if
       call gce_clear_error()
       ! Analysed, then evaluated -- the two halves Compiler.load does
       ! per form. Analysis here is macroexpansion and nothing else.
       r = gce_analyze(gcv_nth(vs_get(lb + 2), i), vs_get(lb + 1))
       if (.not. gce_has_error()) r = gce_eval(r, vs_get(lb + 1), no_roots())
       call vs_set(lb + 3, r)
       if (gce_has_error()) then
          nfail = 1
          print '(A,A)', "  ", gce_error()
          print '(A,A)', "    in: ", &
               first_line(gcp_str(gcv_nth(vs_get(lb + 2), i), .true.))
          print '(A,A,A,I0,A,I0,A)', "load ", path, ": stopped at form ", &
               i + 1, " of ", gcv_count(vs_get(lb + 2)), ""
          exit
       end if
    end do
    call vs_leave(lb)
  end subroutine load_file

  ! Just enough of a form to identify it in a report.
  function first_line(t) result(out)
    character(len=*), intent(in) :: t
    character(len=:), allocatable :: out
    integer :: k
    out = t
    k = index(t, achar(10))
    if (k > 0) out = t(1:k-1)
    if (len(out) > 72) out = out(1:72) // "..."
  end function first_line

  function no_roots() result(r)
    type(gc_value) :: r(0)
  end function no_roots

end program clotran