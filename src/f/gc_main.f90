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
  ! host.clj leaves clojure.core current, being part of its bootstrap.
  ! The REPL starts in user, as Clojure's does.
  call gcn_set_current(gcn_find_or_create("user", none))

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

  ! Reads a whole file and evaluates every form in it.
  !
  ! TWO DELIBERATE DEVIATIONS from Compiler.load, both temporary and
  ! both only because bootstrapping is incomplete. See DEVIATIONS.md.
  !
  !   1. Clojure interleaves read and eval, one form at a time. We read
  !      the whole file first. That is wrong in general -- the reader
  !      consults *ns* (for ::kw) and a macro cannot affect how later
  !      forms READ -- but it is what lets a single reader error be
  !      reported once instead of aborting at form one.
  !   2. Clojure lets an exception out of the loop, ending the load.
  !      We report each failing form and continue, because the number
  !      that matters right now is how much of core.clj works.
  subroutine load_file(path, env)
    character(len=*), intent(in) :: path
    type(gc_value), intent(in) :: env
    character(len=:), allocatable :: text
    type(gc_value) :: forms, r
    integer :: u, st, lb, i, fsize, nfail

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
    nfail = 0
    do i = 0, gcv_count(vs_get(lb + 2)) - 1
       call gce_clear_error()
       r = gce_eval(gcv_nth(vs_get(lb + 2), i), vs_get(lb + 1), no_roots())
       call vs_set(lb + 3, r)
       if (gce_has_error()) then
          ! Report and CONTINUE -- deviation 2 above.
          nfail = nfail + 1
          if (nfail <= 5) then
             print '(A,A)', "  ", gce_error()
             print '(A,A)', "    in: ", &
                  first_line(gcp_str(gcv_nth(vs_get(lb + 2), i), .true.))
          end if
       end if
    end do
    if (nfail > 0) then
       print '(A,A,A,I0,A,I0,A)', "load ", path, ": ", &
            gcv_count(vs_get(lb + 2)) - nfail, " of ", &
            gcv_count(vs_get(lb + 2)), " forms loaded"
    end if
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

end program gc_repl