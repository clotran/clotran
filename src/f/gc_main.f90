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
  integer :: base, ios, size_read

  call gc_init(65536)
  base = vs_enter(3)
  env = gce_base_env(none)
  call vs_set(base + 1, env)

  ! The host shim -- type predicates that core.clj cannot supply,
  ! because it would ask instance? about Java classes. NOT a core
  ! library: everything else Clojure programs use must come from
  ! the real core.clj, which is the point of the project.
  call load_file("src/clj/host.clj", vs_get(base + 1))

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
    character(len=8192) :: chunk
    type(gc_value) :: forms, r
    integer :: u, st, nread, lb, i

    open(newunit=u, file=path, status="old", action="read", iostat=st)
    if (st /= 0) then
       print '(A,A)', "load: cannot open ", path
       return
    end if
    text = ""
    ! Line at a time, advancing. The non-advancing form is a trap
    ! here: end-of-RECORD reports a negative iostat just as
    ! end-of-file does, so a loop testing `st < 0` stops after the
    ! first line and silently loads nothing.
    do
       read(u, '(A)', iostat=st) chunk
       if (st /= 0) exit
       text = text // trim(chunk) // achar(10)
    end do
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
