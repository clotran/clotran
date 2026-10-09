  ! ===================================================================
  ! THE JIT, stage 1 (PLAN step 31; model/vmj.lisp). Each function the VM
  ! compiles is translated once to arm64: push, load, slide, jmpf and jmp
  ! as native code (vmj-block's ops), everything else a call of the step
  ! the interpreter runs (vm_jit_step -> vmg_xstep). vmj-run-is: this
  ! machine is the interpreter step for step.
  !
  ! The registers while native code runs:
  !   x19 the run's vm_jit_ctx   x20 fb   x21 sp   x22 the stack's base
  !   x23 the stack's length     x24 the pool's base   x25 pc (set where
  !   it is read: a slow step, an exit)   x26 the pc -> native table
  !   x27 the highest sp seen (what vm_run clears after)
  ! A value is 16 bytes: its tag the first 4, its integer at 8.
  !
  ! The region starts with three stubs: ENTER (saves the callee-saved
  ! registers, loads the run's, jumps to its pc's code), EXIT, and SLOW
  ! (stores the registers, calls vm_jit_step, reloads them, then exits or
  ! jumps to the pc's code). A pc no function's translation covers is SLOW
  ! in the table, so code that leaves for it is interpreted.
  ! ===================================================================

  ! CLOTRAN_JIT=1 with the VM on, and an arm64 host
  logical function vmj_enabled()
    character(len=8) :: e, tr
    if (vmj_mode == 0) then
       vmj_mode = 2
       call get_environment_variable("CLOTRAN_JIT", e)
       ! the fuzzer's negative control (scripts/fuzz -m jit-control)
       call get_environment_variable("CLOTRAN_JIT_BREAK", tr)
       vmj_break = trim(tr) == "1"
       if (trim(e) == "1" .and. vm_enabled()) then
          if (clotran_jit_arch() == 1) then
             if (vmj_init()) vmj_mode = 1
          end if
       end if
    end if
    vmj_enabled = vmj_mode == 1
  end function vmj_enabled

  ! ---- arm64 encodings (each the instruction word; registers 0..31) ----

  integer(c_int64_t) function a_addi(d, n, i)          ! add xd, xn, #i
    integer, intent(in) :: d, n, i
    a_addi = int(z'91000000', c_int64_t) + i * 1024_gc_ip + n * 32 + d
  end function a_addi
  integer(c_int64_t) function a_subi(d, n, i)          ! sub xd, xn, #i
    integer, intent(in) :: d, n, i
    a_subi = int(z'D1000000', c_int64_t) + i * 1024_gc_ip + n * 32 + d
  end function a_subi
  integer(c_int64_t) function a_addl(d, n, m, s)       ! add xd, xn, xm, lsl #s
    integer, intent(in) :: d, n, m, s
    a_addl = int(z'8B000000', c_int64_t) + m * 65536_gc_ip + s * 1024 + n * 32 + d
  end function a_addl
  integer(c_int64_t) function a_cmp(n, m)              ! cmp xn, xm
    integer, intent(in) :: n, m
    a_cmp = int(z'EB000000', c_int64_t) + m * 65536_gc_ip + n * 32 + 31
  end function a_cmp
  integer(c_int64_t) function a_cmpi(n, i)             ! cmp xn, #i
    integer, intent(in) :: n, i
    a_cmpi = int(z'F1000000', c_int64_t) + i * 1024_gc_ip + n * 32 + 31
  end function a_cmpi
  integer(c_int64_t) function a_cmpwi(n, i)            ! cmp wn, #i
    integer, intent(in) :: n, i
    a_cmpwi = int(z'71000000', c_int64_t) + i * 1024_gc_ip + n * 32 + 31
  end function a_cmpwi
  integer(c_int64_t) function a_bc(off, c)             ! b.c off (words)
    integer, intent(in) :: off, c
    a_bc = int(z'54000000', c_int64_t) + iand(int(off, c_int64_t), int(z'7FFFF', c_int64_t)) * 32 + c
  end function a_bc
  integer(c_int64_t) function a_b(off)                 ! b off (words)
    integer(c_int64_t), intent(in) :: off
    a_b = int(z'14000000', c_int64_t) + iand(off, int(z'3FFFFFF', c_int64_t))
  end function a_b
  integer(c_int64_t) function a_cbzw(t, off)           ! cbz wt, off
    integer, intent(in) :: t, off
    a_cbzw = int(z'34000000', c_int64_t) + iand(int(off, c_int64_t), int(z'7FFFF', c_int64_t)) * 32 + t
  end function a_cbzw
  integer(c_int64_t) function a_cbnzw(t, off)          ! cbnz wt, off
    integer, intent(in) :: t, off
    a_cbnzw = int(z'35000000', c_int64_t) + iand(int(off, c_int64_t), int(z'7FFFF', c_int64_t)) * 32 + t
  end function a_cbnzw
  integer(c_int64_t) function a_cbnz(t, off)           ! cbnz xt, off
    integer, intent(in) :: t, off
    a_cbnz = int(z'B5000000', c_int64_t) + iand(int(off, c_int64_t), int(z'7FFFF', c_int64_t)) * 32 + t
  end function a_cbnz
  integer(c_int64_t) function a_ldp(t, t2, n, off)     ! ldp xt, xt2, [xn, #off]
    integer, intent(in) :: t, t2, n, off
    a_ldp = int(z'A9400000', c_int64_t) + iand(int(off / 8, c_int64_t), 127_gc_ip) * 32768 + t2 * 1024 + n * 32 + t
  end function a_ldp
  integer(c_int64_t) function a_stp(t, t2, n, off)     ! stp xt, xt2, [xn, #off]
    integer, intent(in) :: t, t2, n, off
    a_stp = int(z'A9000000', c_int64_t) + iand(int(off / 8, c_int64_t), 127_gc_ip) * 32768 + t2 * 1024 + n * 32 + t
  end function a_stp
  integer(c_int64_t) function a_ldr(t, n, off)         ! ldr xt, [xn, #off]
    integer, intent(in) :: t, n, off
    a_ldr = int(z'F9400000', c_int64_t) + (off / 8) * 1024_gc_ip + n * 32 + t
  end function a_ldr
  integer(c_int64_t) function a_str(t, n, off)         ! str xt, [xn, #off]
    integer, intent(in) :: t, n, off
    a_str = int(z'F9000000', c_int64_t) + (off / 8) * 1024_gc_ip + n * 32 + t
  end function a_str
  integer(c_int64_t) function a_ldrw(t, n, off)        ! ldr wt, [xn, #off]
    integer, intent(in) :: t, n, off
    a_ldrw = int(z'B9400000', c_int64_t) + (off / 4) * 1024_gc_ip + n * 32 + t
  end function a_ldrw
  integer(c_int64_t) function a_ldrx3(t, n, m)         ! ldr xt, [xn, xm, lsl #3]
    integer, intent(in) :: t, n, m
    a_ldrx3 = int(z'F8607800', c_int64_t) + m * 65536_gc_ip + n * 32 + t
  end function a_ldrx3
  integer(c_int64_t) function a_movz(d, i, hw)         ! movz xd, #i, lsl #(16 hw)
    integer, intent(in) :: d, hw
    integer(c_int64_t), intent(in) :: i
    a_movz = int(z'D2800000', c_int64_t) + hw * 2097152_gc_ip + iand(i, 65535_gc_ip) * 32 + d
  end function a_movz
  integer(c_int64_t) function a_movk(d, i, hw)         ! movk xd, #i, lsl #(16 hw)
    integer, intent(in) :: d, hw
    integer(c_int64_t), intent(in) :: i
    a_movk = int(z'F2800000', c_int64_t) + hw * 2097152_gc_ip + iand(i, 65535_gc_ip) * 32 + d
  end function a_movk
  integer(c_int64_t) function a_csel(d, n, m, c)       ! csel xd, xn, xm, c
    integer, intent(in) :: d, n, m, c
    a_csel = int(z'9A800000', c_int64_t) + m * 65536_gc_ip + c * 4096 + n * 32 + d
  end function a_csel
  integer(c_int64_t) function a_mov(d, m)              ! mov xd, xm
    integer, intent(in) :: d, m
    a_mov = int(z'AA0003E0', c_int64_t) + m * 65536_gc_ip + d
  end function a_mov
  integer(c_int64_t) function a_br(n)                  ! br xn
    integer, intent(in) :: n
    a_br = int(z'D61F0000', c_int64_t) + n * 32
  end function a_br
  integer(c_int64_t) function a_blr(n)                 ! blr xn
    integer, intent(in) :: n
    a_blr = int(z'D63F0000', c_int64_t) + n * 32
  end function a_blr

  ! ---- the buffer a translation is emitted into ----

  subroutine vmj_put(buf, nw, x)
    integer(c_int32_t), allocatable, intent(inout) :: buf(:)
    integer, intent(inout) :: nw
    integer(c_int64_t), intent(in) :: x
    integer(c_int32_t), allocatable :: t(:)
    if (nw >= size(buf)) then
       allocate(t(2 * size(buf)))
       t(1:nw) = buf(1:nw)
       call move_alloc(t, buf)
    end if
    nw = nw + 1
    buf(nw) = transfer(x, int(0, c_int32_t))
  end subroutine vmj_put

  ! word i of buf replaced (an encoding patched once its target is known)
  subroutine vmj_patch(buf, i, x)
    integer(c_int32_t), intent(inout) :: buf(:)
    integer, intent(in) :: i
    integer(c_int64_t), intent(in) :: x
    buf(i) = transfer(x, int(0, c_int32_t))
  end subroutine vmj_patch

  ! the region, its stubs, the table
  logical function vmj_init()
    integer(c_int32_t), allocatable :: buf(:)
    integer :: nw, i, cbx
    integer(c_int64_t) :: base
    vmj_init = .false.
    vmj_cap = 16777216_gc_ip                     ! words: 64 MB
    vmj_base = clotran_jit_alloc(4 * vmj_cap)
    if (.not. c_associated(vmj_base)) return
    base = transfer(vmj_base, 0_gc_ip)
    allocate(buf(256))
    nw = 0
    ! ENTER (at word 0)
    call vmj_put(buf, nw, int(z'A9BA7BFD', c_int64_t))     ! stp x29, x30, [sp, #-96]!
    call vmj_put(buf, nw, a_addi(29, 31, 0))           ! mov x29, sp
    do i = 0, 4
       call vmj_put(buf, nw, a_stp(19 + 2 * i, 20 + 2 * i, 31, 16 + 16 * i))
    end do
    call vmj_put(buf, nw, a_mov(19, 0))
    call vmj_load_regs(buf, nw)
    call vmj_put(buf, nw, a_ldr(22, 19, 32))
    call vmj_put(buf, nw, a_ldr(23, 19, 40))
    call vmj_put(buf, nw, a_ldr(24, 19, 48))
    call vmj_put(buf, nw, a_ldr(26, 19, 56))
    call vmj_put(buf, nw, a_ldrx3(9, 26, 25))
    call vmj_put(buf, nw, a_br(9))
    ! EXIT
    cbx = nw + 1
    do i = 4, 0, -1
       call vmj_put(buf, nw, a_ldp(19 + 2 * i, 20 + 2 * i, 31, 16 + 16 * i))
    end do
    call vmj_put(buf, nw, int(z'A8C67BFD', c_int64_t))     ! ldp x29, x30, [sp], #96
    call vmj_put(buf, nw, int(z'D65F03C0', c_int64_t))     ! ret
    ! SLOW
    vmj_stub = base + 4 * nw
    call vmj_put(buf, nw, a_str(25, 19, 0))
    call vmj_put(buf, nw, a_str(20, 19, 8))
    call vmj_put(buf, nw, a_str(21, 19, 16))
    call vmj_put(buf, nw, a_str(27, 19, 24))
    call vmj_put(buf, nw, a_mov(0, 19))
    call vmj_put(buf, nw, a_ldr(16, 19, 64))
    call vmj_put(buf, nw, a_blr(16))
    call vmj_load_regs(buf, nw)
    call vmj_put(buf, nw, a_cbnzw(0, cbx - (nw + 1)))  ! to EXIT
    call vmj_put(buf, nw, a_ldrx3(9, 26, 25))
    call vmj_put(buf, nw, a_br(9))
    vmj_enter = base
    call clotran_jit_write(vmj_base, buf, int(nw, c_int64_t))
    vmj_used = nw
    allocate(vmj_tab(0:VMP_INSTRS - 1))
    vmj_tab = vmj_stub
    vmj_init = .true.
  end function vmj_init

  ! pc, fb, sp and hi from the context
  subroutine vmj_load_regs(buf, nw)
    integer(c_int32_t), allocatable, intent(inout) :: buf(:)
    integer, intent(inout) :: nw
    call vmj_put(buf, nw, a_ldr(25, 19, 0))
    call vmj_put(buf, nw, a_ldr(20, 19, 8))
    call vmj_put(buf, nw, a_ldr(21, 19, 16))
    call vmj_put(buf, nw, a_ldr(27, 19, 24))
  end subroutine vmj_load_regs

  ! the slow step, answering 1 to leave the native code: the run's state
  ! from the registers, the interpreter's step (vm_run's loop, one turn),
  ! the registers from the state
  integer(c_int32_t) function vm_jit_step(cx) bind(c)
    type(vm_jit_ctx), intent(inout) :: cx
    type(vm_state), pointer :: st
    type(gc_stack), pointer :: vst
    call c_f_pointer(cx%st, st)
    st%pc = cx%pc
    st%fb = cx%fb
    st%sp = cx%sp
    vm_jit_step = 1
    if (st%status /= 0) return
    if (st%code(4 * st%pc) == 11 .and. st%ctop == 0) return
    vst => gc_my_stack()
    vst%vm_ctl_top = int(cx%ct0 + st%ctop + 1)
    call vmg_xstep(st)
    cx%steps = cx%steps + 1
    if (iand(cx%steps, 4095_gc_ip) == 0) then
       if (gc_stop_pending()) call gc_poll()
    end if
    cx%pc = st%pc
    cx%fb = st%fb
    cx%sp = st%sp
    if (cx%sp > cx%hi) cx%hi = cx%sp
    if (st%status /= 0) return
    vm_jit_step = 0
  end function vm_jit_step

  ! ---- THE TRANSLATION: vmj-block per pc of [p0, pend) ----

  ! x(r) := the address of slot base(b) + k: b 0 the frame base, 1 sp
  subroutine vmj_slot(buf, nw, r, b, k)
    integer(c_int32_t), allocatable, intent(inout) :: buf(:)
    integer, intent(inout) :: nw
    integer, intent(in) :: r, b, k
    integer :: br
    br = merge(20, 21, b == 0)
    if (k > 0) then
       call vmj_put(buf, nw, a_addi(r, br, k))
       call vmj_put(buf, nw, a_addl(r, 22, r, 4))
    else if (k < 0) then
       call vmj_put(buf, nw, a_subi(r, br, -k))
       call vmj_put(buf, nw, a_addl(r, 22, r, 4))
    else
       call vmj_put(buf, nw, a_addl(r, 22, br, 4))
    end if
  end subroutine vmj_slot

  ! (:chk-ix b k): to the block's slow tail unless base(b)+k < the length
  subroutine vmj_chk_ix(buf, nw, b, k, nf, fails)
    integer(c_int32_t), allocatable, intent(inout) :: buf(:)
    integer, intent(inout) :: nw, nf
    integer, intent(in) :: b, k
    integer, intent(inout) :: fails(:)
    integer :: br
    br = merge(20, 21, b == 0)
    if (k > 0) then
       call vmj_put(buf, nw, a_addi(9, br, k))
       call vmj_put(buf, nw, a_cmp(9, 23))
    else if (k < 0) then
       call vmj_put(buf, nw, a_subi(9, br, -k))
       call vmj_put(buf, nw, a_cmp(9, 23))
    else
       call vmj_put(buf, nw, a_cmp(br, 23))
    end if
    call vmj_put(buf, nw, 0_gc_ip)                     ! b.hs SLOW, patched
    nf = nf + 1
    fails(nf) = nw
  end subroutine vmj_chk_ix

  ! x25 := v
  subroutine vmj_movpc(buf, nw, r, v)
    integer(c_int32_t), allocatable, intent(inout) :: buf(:)
    integer, intent(inout) :: nw
    integer, intent(in) :: r
    integer(c_int64_t), intent(in) :: v
    call vmj_put(buf, nw, a_movz(r, v, 0))
    call vmj_put(buf, nw, a_movk(r, ishft(v, -16), 1))
  end subroutine vmj_movpc

  ! to the block of bytecode pc tg: a direct branch inside the function
  ! (patched once its block is placed), elsewhere through the table
  subroutine vmj_jump(buf, nw, tg, p0, pend, nj, jat, jto)
    integer(c_int32_t), allocatable, intent(inout) :: buf(:)
    integer, intent(inout) :: nw, nj
    integer(c_int64_t), intent(in) :: tg, p0, pend
    integer, intent(inout) :: jat(:)
    integer(c_int64_t), intent(inout) :: jto(:)
    if (tg >= p0 .and. tg < pend) then
       call vmj_put(buf, nw, 0_gc_ip)
       nj = nj + 1
       jat(nj) = nw
       jto(nj) = tg
    else
       call vmj_movpc(buf, nw, 25, tg)
       call vmj_put(buf, nw, a_ldrx3(9, 26, 25))
       call vmj_put(buf, nw, a_br(9))
    end if
  end subroutine vmj_jump

  ! the code of [p0, pend), placed in the region and entered in the table
  subroutine vmj_compile(p0, pend)
    integer(c_int64_t), intent(in) :: p0, pend
    integer(c_int32_t), allocatable :: buf(:)
    integer :: nw, nf, nj, ns, i, fails(8)
    integer, allocatable :: blk(:), jat(:), sat(:)
    integer(c_int64_t), allocatable :: jto(:), sto(:)
    integer(c_int64_t) :: p, op, a, at, n
    logical :: inl
    n = pend - p0
    if (n <= 0) return
    allocate(buf(64 * n + 64), blk(0:n), jat(2 * n + 2), jto(2 * n + 2), sat(n + 1), sto(n + 1))
    nw = 0
    nj = 0
    ns = 0
    do p = p0, pend - 1
       blk(p - p0) = nw + 1
       op = vmp%code(4 * p)
       a = vmp%code(4 * p + 1)
       nf = 0
       inl = .true.
       select case (op)
       case (1)                                        ! push
          if (a >= 0 .and. a < VMP_INSTRS) then
             call vmj_chk_ix(buf, nw, 1, 0, nf, fails)
             call vmj_movpc(buf, nw, 9, a)
             call vmj_put(buf, nw, a_addl(9, 24, 9, 4))
             call vmj_put(buf, nw, a_ldp(10, 11, 9, 0))
             call vmj_slot(buf, nw, 12, 1, 0)
             call vmj_put(buf, nw, a_stp(10, 11, 12, 0))
             call vmj_sp_up(buf, nw)
          else
             inl = .false.
          end if
       case (2)                                        ! load
          if (a >= 0 .and. a < 4096) then
             call vmj_chk_ix(buf, nw, 0, int(a), nf, fails)
             call vmj_chk_ix(buf, nw, 1, 0, nf, fails)
             call vmj_slot(buf, nw, 9, 0, int(a))
             call vmj_put(buf, nw, a_ldp(10, 11, 9, 0))
             call vmj_slot(buf, nw, 12, 1, 0)
             call vmj_put(buf, nw, a_stp(10, 11, 12, 0))
             call vmj_sp_up(buf, nw)
          else
             inl = .false.
          end if
       case (5)                                        ! slide
          call vmj_put(buf, nw, a_cmpi(21, 2))
          call vmj_put(buf, nw, 0_gc_ip)               ! b.lo SLOW
          nf = nf + 1
          fails(nf) = -nw
          call vmj_chk_ix(buf, nw, 1, -1, nf, fails)
          call vmj_slot(buf, nw, 9, 1, -1)
          call vmj_put(buf, nw, a_ldp(10, 11, 9, 0))
          call vmj_slot(buf, nw, 12, 1, -2)
          call vmj_put(buf, nw, a_stp(10, 11, 12, 0))
          call vmj_put(buf, nw, a_subi(21, 21, 1))
       case (6)                                        ! jmpf
          call vmj_put(buf, nw, a_cmpi(21, 1))
          call vmj_put(buf, nw, 0_gc_ip)               ! b.lo SLOW
          nf = nf + 1
          fails(nf) = -nw
          call vmj_chk_ix(buf, nw, 1, -1, nf, fails)
          call vmj_put(buf, nw, a_subi(21, 21, 1))
          call vmj_slot(buf, nw, 9, 1, 0)
          call vmj_put(buf, nw, a_ldrw(10, 9, 0))
          call vmj_put(buf, nw, a_ldr(11, 9, 8))
          ! false or nil: tag 0, or tag 1 with 0 -- to the target; else on
          at = nw
          call vmj_put(buf, nw, 0_gc_ip)               ! cbz w10, T
          call vmj_put(buf, nw, a_cmpwi(10, 1))
          call vmj_put(buf, nw, 0_gc_ip)               ! b.ne N
          call vmj_put(buf, nw, 0_gc_ip)               ! cbnz x11, N
          call vmj_patch(buf, int(at) + 1, a_cbzw(10, 4))
          if (vmj_break) call vmj_patch(buf, int(at) + 1, a_cbnzw(10, 4))
          call vmj_jump(buf, nw, a, p0, pend, nj, jat, jto)
          call vmj_patch(buf, int(at) + 3, a_bc(nw + 1 - (int(at) + 3), 1))
          call vmj_patch(buf, int(at) + 4, a_cbnz(11, nw + 1 - (int(at) + 4)))
       case (7)                                        ! jmp
          call vmj_jump(buf, nw, a, p0, pend, nj, jat, jto)
       case default
          inl = .false.
       end select
       if (.not. inl) then
          ! the step: pc, then the stub
          call vmj_movpc(buf, nw, 25, p)
          call vmj_put(buf, nw, 0_gc_ip)
          ns = ns + 1
          sat(ns) = nw
          cycle
       end if
       vmj_n_inline = vmj_n_inline + 1
       ! on to the next block: falls through when it is next, else jumps
       if (op /= 7) then
          if (p + 1 >= pend) call vmj_jump(buf, nw, p + 1, p0, pend, nj, jat, jto)
       end if
       ! the slow tail a failed check goes to
       if (nf > 0) then
          if (p + 1 < pend .and. op /= 7) then
             ! over the tail (pc's two words and its branch) to the next block
             call vmj_put(buf, nw, a_b(int(4, c_int64_t)))
          end if
          do i = 1, nf
             if (fails(i) > 0) then
                call vmj_patch(buf, fails(i), a_bc(nw + 1 - fails(i), 2))     ! b.hs
             else
                call vmj_patch(buf, -fails(i), a_bc(nw + 1 + fails(i), 3))    ! b.lo
             end if
          end do
          call vmj_movpc(buf, nw, 25, p)
          call vmj_put(buf, nw, 0_gc_ip)
          ns = ns + 1
          sat(ns) = nw
       end if
    end do
    blk(n) = nw + 1
    ! the region: reserved, then each branch's offset from where it lands
    call gc_state_lock()
    if (vmj_used + nw > vmj_cap) then
       call gc_state_unlock()
       return
    end if
    at = vmj_used
    vmj_used = vmj_used + nw
    call gc_state_unlock()
    do i = 1, nj
       call vmj_patch(buf, jat(i), a_b(int(blk(jto(i) - p0) - jat(i), c_int64_t)))
    end do
    do i = 1, ns
       call vmj_patch(buf, sat(i), a_b((vmj_stub - transfer(vmj_base, 0_gc_ip)) / 4 - (at + sat(i) - 1)))
    end do
    call clotran_jit_write(transfer(transfer(vmj_base, 0_gc_ip) + 4 * at, vmj_base), buf, int(nw, c_int64_t))
    do p = p0, pend - 1
       vmj_tab(p) = transfer(vmj_base, 0_gc_ip) + 4 * (at + blk(p - p0) - 1)
    end do
    vmj_n_fns = vmj_n_fns + 1
  end subroutine vmj_compile

  ! sp up by one, the highest seen kept
  subroutine vmj_sp_up(buf, nw)
    integer(c_int32_t), allocatable, intent(inout) :: buf(:)
    integer, intent(inout) :: nw
    call vmj_put(buf, nw, a_addi(21, 21, 1))
    call vmj_put(buf, nw, a_cmp(21, 27))
    call vmj_put(buf, nw, a_csel(27, 21, 27, 8))     ! hi
  end subroutine vmj_sp_up

  ! the run in st, natively: from its pc until it halts, stops or throws
  subroutine vmj_run(st, ct0, hi, steps)
    type(vm_state), intent(inout), target :: st
    integer(gc_ip), intent(in) :: ct0
    integer, intent(inout) :: hi
    integer(gc_ip), intent(inout) :: steps
    type(vm_jit_ctx), target :: cx
    cx%pc = st%pc
    cx%fb = st%fb
    cx%sp = st%sp
    cx%hi = hi
    cx%stk = c_loc(st%stk(0))
    cx%stklen = size(st%stk, kind=c_int64_t)
    cx%pool = c_loc(vmp%pool(0))
    cx%tab = c_loc(vmj_tab(0))
    cx%step = c_funloc(vm_jit_step)
    cx%st = c_loc(st)
    cx%ct0 = ct0
    cx%steps = 0
    call clotran_jit_enter(transfer(vmj_enter, c_null_ptr), c_loc(cx))
    hi = int(max(int(hi, c_int64_t), cx%hi))
    steps = steps + cx%steps
  end subroutine vmj_run
