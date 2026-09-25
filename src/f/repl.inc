  ! ---- the REPL --------------------------------------------------------
  !
  ! One loop, at the top level (main.f90 calls gce_repl) and nested at
  ! a break, where it is the default handler: the paused state is
  ! printed and the command comes from the keyboard, (clotran-resume
  ! cmd). A form is read across lines until it closes. At the top
  ! level this prints exactly what it always did -- scripts/oracle
  ! reads that output.

  ! Starting a REPL makes it the break handler, unless a file loaded
  ! first bound one of its own.
  subroutine gce_repl()
    type(gc_value) :: v
    if (gc_root_live(handler_var_root) .and. gc_root_live(repl_fn_root)) then
       v = gcn_var_value(gc_root_get(handler_var_root))
       if (v%tag == GCT_NIL) call gcn_set_var(gc_root_get(handler_var_root), gc_root_get(repl_fn_root))
    end if
    v = repl_loop(gc_nil())
  end subroutine gce_repl

  ! Reads, evaluates and prints until EOF or, nested, until a form has
  ! called clotran-resume; answers that command, or :continue at EOF.
  recursive function repl_loop(bm) result(cmd)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: bm
    type(gc_value) :: cmd, form, result
    type(gc_value) :: none(0)
    character(len=:), allocatable :: line, pending, prompt
    character(len=4096) :: buf
    character(len=16) :: dbuf
    integer :: base, ios, size_read

    tctx => ctx_self()
    repl_depth = repl_depth + 1
    base = vs_enter(3)
    call vs_set(base + 1, gc_root_get(global_env_root))
    if (repl_depth > 1) then
       if (gca_is(bm)) call write_break(bm, 6, 8)
       print '(A)', ";; (clotran-resume :continue | {:continue v} | :step-in | :step-over | :step-out | :abort)"
    end if
    pending = ""
    do
       if (len(pending) > 0) then
          ! A line that does not close what it opened is not an error,
          ! it is a request for more input.
          prompt = "#_=> "
       else
          prompt = gcn_name(gcn_current(none)) // "=> "
          if (repl_depth > 1) then
             write(dbuf, '(I0)') repl_depth - 1
             prompt = "[" // trim(dbuf) // "] " // prompt
          end if
       end if
       write(*, '(A)', advance='no') prompt
       flush(6)
       read(*, '(A)', iostat=ios, size=size_read, advance='no') buf
       ! End of file, or a read error -- gfortran reports a read AFTER
       ! the end as a positive code, and looping on it never ends. An
       ! empty line is end of RECORD with size 0, which is a line.
       if (is_iostat_end(ios) .or. ios > 0) exit
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
       if (.not. tctx%has_error) result = gce_eval(result, vs_get(base + 1), none)
       call vs_set(base + 3, result)
       if (resume_pending) exit
       if (tctx%has_error) then
          print '(A,A)', "error: ", gce_error()
          if (len(gce_trace()) > 0) write(*, '(A)', advance='no') gce_trace()
          cycle
       end if
       print '(A)', gcp_str(vs_get(base + 3), .true.)
    end do
    if (resume_pending) then
       resume_pending = .false.
       cmd = gc_root_get(resume_root)
    else
       cmd = gc_key("continue", none)
    end if
    call vs_leave(base)
    repl_depth = repl_depth - 1
  end function repl_loop
