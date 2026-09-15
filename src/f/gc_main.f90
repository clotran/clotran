! A REPL over the new GC-backed stack.
!
! Not clotran-bin: that drives the refcounted evaluator, and both have
! to keep working until the switch. This exists so the new stack can
! be driven by hand and fed real Clojure, which is how the remaining
! gaps get FOUND rather than guessed at.
!
! Reads a form per line, evaluates, prints. No line editing of its own
! -- scripts/clotran's rlwrap trick applies here too if wanted.
program gc_repl
  use GC
  use GCReader
  use GCPrinter
  use GCEval
  use GCNamespace
  use GCVector
  implicit none

  character(len=:), allocatable :: line
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

  ! Any files named on the command line load next, in order, so
  ! that `clotran-gc some.clj` is how a file gets tried against
  ! this evaluator. Loading real core.clj is the point: the first
  ! error it reports IS the next thing to build.
  do i = 1, command_argument_count()
     call get_command_argument(i, argbuf, arglen)
     call load_file(argbuf(1:arglen), vs_get(base + 1))
  end do

  do
     write(*, '(A)', advance='no') gcn_name(gcn_current(none)) // "=> "
     flush(6)
     read(*, '(A)', iostat=ios, size=size_read, advance='no') buf
     if (ios < 0 .and. size_read == 0) exit   ! EOF
     line = trim(buf(1:max(size_read, 0)))
     if (len(line) == 0) cycle

     form = gcr_read(line, [vs_get(base + 1)])
     if (gcr_has_error()) then
        print '(A,A)', "reader error: ", gcr_error()
        cycle
     end if
     call vs_set(base + 2, form)

     call gce_clear_error()
     result = gce_eval(vs_get(base + 2), vs_get(base + 1), no_roots())
     call vs_set(base + 3, result)
     if (gce_has_error()) then
        print '(A,A)', "error: ", gce_error()
        cycle
     end if
     print '(A)', gcp_str(vs_get(base + 3), .true.)
  end do
  print *, ""

contains

  ! Reads a whole file and evaluates every form in it. Errors are
  ! reported with the form that caused them and loading STOPS --
  ! continuing past a broken definition just produces a second,
  ! more confusing error somewhere else.
  subroutine load_file(path, env)
    character(len=*), intent(in) :: path
    type(gc_value), intent(in) :: env
    character(len=:), allocatable :: text
    type(gc_value) :: forms, r
    integer :: u, st, lb, i, fsize

    ! Read in ONE allocation, via stream access, rather than
    ! appending line by line. Appending is O(n^2) -- each // builds a
    ! whole new string -- and on an 8000-line file that is not slow,
    ! it is indistinguishable from a hang. LispReader.f90 carries the
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
    do i = 0, gcv_count(vs_get(lb + 2)) - 1
       call gce_clear_error()
       r = gce_eval(gcv_nth(vs_get(lb + 2), i), vs_get(lb + 1), no_roots())
       call vs_set(lb + 3, r)
       if (gce_has_error()) then
          print '(A,A,A,A)', "load ", path, ": ", gce_error()
          print '(A,A)',   "  in form: ", &
               gcp_str(gcv_nth(vs_get(lb + 2), i), .true.)
          exit
       end if
    end do
    call vs_leave(lb)
  end subroutine load_file

  function no_roots() result(r)
    type(gc_value) :: r(0)
  end function no_roots

end program gc_repl