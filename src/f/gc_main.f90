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
  implicit none

  character(len=:), allocatable :: line
  character(len=4096) :: buf
  type(gc_value) :: env, form, result
  type(gc_value) :: none(0)
  integer :: base, ios, size_read

  call gc_init(4096)
  base = vs_enter(3)
  env = gce_base_env(none)
  call vs_set(base + 1, env)

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

  function no_roots() result(r)
    type(gc_value) :: r(0)
  end function no_roots

end program gc_repl
