  ! GENERATED from model/heaprtg.lisp by scripts/acl2-fortran -b heaprtg. Do not edit:
  ! change the model, prove it, and generate again. Included in GC.f90's contains
  ! part: the value stack's operations on a thread's gc_stack and the global
  ! roots', guard-verified.
  ! heaprtg proves each is heaprt's (vsg-enter-refines, vsg-leave-refines,
  ! vsg-set-refines, vsg-get-refines, vsg-reset-refines), so heaprt's frame-balance
  ! and ops-keep-callers hold of this stack; and equal to heaprt's gl-new, keep-g,
  ! root-get, live and gl-init (glg-new-refines, glg-keep-refines, ...); push_roots'
  ! loops push heaprt's rootset (vsg-push-refines, glg-push-refines, push-roots-refines);
  ! each size's spare frames are a stack of at most 8, a give clearing the frame's
  ! words and nothing else (spg-take-refines, spg-give-refines, spg-reset-refines).
  subroutine vsg_enter(s, n_, r)
    type(gc_stack), intent(inout) :: s
    integer(int64), value :: n_
    integer(int64), intent(out) :: r
    integer(int64) :: m_2
    integer(int64) :: top_1
    top_1 = s%vs_top
    m_2 = max(0_int64, n_)
    if (((size(s%slots0, kind=int64) + (-top_1)) < m_2)) then
      r = (-1_int64)
    else
      s%vs_top = (top_1 + m_2)
      if ((s%vs_hi < (top_1 + m_2))) then
        s%vs_hi = (top_1 + m_2)
      else
      end if
      r = top_1
    end if
  end subroutine vsg_enter

  subroutine vsg_clear(s, i_, e_)
    type(gc_stack), intent(inout) :: s
    integer(int64), value :: i_
    integer(int64), value :: e_
    integer(int64) :: e_6
    integer(int64) :: i_3
    integer(int64) :: i_5
    logical :: t_1
    logical :: t_2
    type(gc_value) :: v_4
    type(gc_value), pointer, contiguous :: slots0_p(:)
    slots0_p => s%slots0
    do
      if ((.not. .true.)) then
        t_2 = (.not. .true.)
      else
        if ((.not. .true.)) then
          t_1 = (.not. .true.)
        else
          t_1 = (.not. (i_ < e_))
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        i_3 = i_
        v_4 = rt_nil()
        slots0_p(i_3) = v_4
        i_5 = (1_int64 + i_)
        e_6 = e_
        i_ = i_5
        e_ = e_6
        cycle
      end if
      exit
    end do
  end subroutine vsg_clear

  subroutine vsg_leave(s, base_)
    type(gc_stack), intent(inout) :: s
    integer(int64), value :: base_
    logical :: t_2
    integer(int64) :: top_1
    top_1 = s%vs_top
    if ((base_ < 0_int64)) then
      t_2 = (base_ < 0_int64)
    else
      t_2 = (top_1 < base_)
    end if
    if (t_2) then
    else
      call vsg_clear(s, base_, top_1)
      s%vs_top = base_
    end if
  end subroutine vsg_leave

  subroutine vsg_set(s, k_, v_)
    type(gc_stack), intent(inout) :: s
    integer(int64), value :: k_
    type(gc_value), value :: v_
    integer(int64) :: i_2
    logical :: t_1
    type(gc_value) :: v_3
    if ((.not. (k_ < 1_int64))) then
      t_1 = (.not. (s%vs_top < k_))
    else
      t_1 = .false.
    end if
    if (t_1) then
      i_2 = ((-1_int64) + k_)
      v_3 = v_
      s%slots0(i_2) = v_3
    else
    end if
  end subroutine vsg_set

  function vsg_get(s, k_) result(r)
    type(gc_stack), intent(in) :: s
    integer(int64), value :: k_
    type(gc_value) :: r
    logical :: t_1
    if ((.not. (k_ < 1_int64))) then
      t_1 = (.not. (s%vs_top < k_))
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = s%slots0(((-1_int64) + k_))
      return
    else
      r = rt_nil()
      return
    end if
  end function vsg_get

  subroutine vsg_reset(s)
    type(gc_stack), intent(inout) :: s
    integer(int64) :: hi_1
    logical :: t_2
    hi_1 = s%vs_hi
    if ((.not. (hi_1 < 0_int64))) then
      t_2 = (.not. (size(s%slots0, kind=int64) < hi_1))
    else
      t_2 = .false.
    end if
    if (t_2) then
      call vsg_clear(s, 0_int64, hi_1)
    else
    end if
    s%vs_top = 0_int64
    s%vs_hi = 0_int64
  end subroutine vsg_reset

  subroutine glg_new(gr, v_, r)
    type(gc_globals), intent(inout) :: gr
    type(gc_value), value :: v_
    integer(int64), intent(out) :: r
    integer(int64) :: c_1
    integer(int64) :: i_6
    integer(int64) :: n_2
    integer(int64) :: n_5
    logical :: t_3
    integer(int64) :: t_4
    type(gc_value) :: v_7
    c_1 = gr%count
    n_2 = size(gr%tbl, kind=int64)
    if ((.not. (c_1 < n_2))) then
      t_3 = (.not. (n_2 < 549755813888_int64))
    else
      t_3 = .false.
    end if
    if (t_3) then
      r = 0_int64
    else
      if ((.not. (c_1 < n_2))) then
        if ((n_2 < 4_int64)) then
          t_4 = 8_int64
        else
          t_4 = (2_int64 * n_2)
        end if
        n_5 = t_4
        call rt_resize_val(gr%tbl, n_5)
      else
      end if
      if ((.not. (c_1 < size(gr%tbl, kind=int64)))) then
        r = 0_int64
      else
        i_6 = c_1
        v_7 = v_
        gr%tbl(i_6) = v_7
        gr%count = (1_int64 + c_1)
        r = (1_int64 + c_1)
      end if
    end if
  end subroutine glg_new

  pure function glg_live(gr, hgen_, hidx_) result(r)
    type(gc_globals), intent(in) :: gr
    integer(int64), value :: hgen_
    integer(int64), value :: hidx_
    logical :: r
    if ((hgen_ == gr%gen)) then
      if ((.not. (hidx_ < 1_int64))) then
        r = (.not. (gr%count < hidx_))
        return
      else
        r = .false.
        return
      end if
    else
      r = .false.
      return
    end if
  end function glg_live

  function glg_get(gr, hgen_, hidx_) result(r)
    type(gc_globals), intent(in) :: gr
    integer(int64), value :: hgen_
    integer(int64), value :: hidx_
    type(gc_value) :: r
    if (glg_live(gr, hgen_, hidx_)) then
      r = gr%tbl(((-1_int64) + hidx_))
      return
    else
      r = rt_nil()
      return
    end if
  end function glg_get

  subroutine glg_keep(gr, hgen_, hidx_, v_, r1, r2)
    type(gc_globals), intent(inout) :: gr
    integer(int64), value :: hgen_
    integer(int64), value :: hidx_
    type(gc_value), value :: v_
    integer(int64), intent(out) :: r1
    integer(int64), intent(out) :: r2
    integer(int64) :: i_1
    integer(int64) :: i_4
    integer(int64) :: mv_3
    type(gc_value) :: v_2
    if (glg_live(gr, hgen_, hidx_)) then
      i_1 = ((-1_int64) + hidx_)
      v_2 = v_
      gr%tbl(i_1) = v_2
      r1 = hgen_
      r2 = hidx_
    else
      call glg_new(gr, v_, mv_3)
      i_4 = mv_3
      r1 = gr%gen
      r2 = i_4
    end if
  end subroutine glg_keep

  subroutine glg_set(gr, idx_, v_)
    type(gc_globals), intent(inout) :: gr
    integer(int64), value :: idx_
    type(gc_value), value :: v_
    integer(int64) :: i_2
    logical :: t_1
    type(gc_value) :: v_3
    if ((.not. (idx_ < 1_int64))) then
      t_1 = (.not. (gr%count < idx_))
    else
      t_1 = .false.
    end if
    if (t_1) then
      i_2 = ((-1_int64) + idx_)
      v_3 = v_
      gr%tbl(i_2) = v_3
    else
    end if
  end subroutine glg_set

  function glg_at(gr, idx_) result(r)
    type(gc_globals), intent(in) :: gr
    integer(int64), value :: idx_
    type(gc_value) :: r
    logical :: t_1
    if ((.not. (idx_ < 1_int64))) then
      t_1 = (.not. (gr%count < idx_))
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = gr%tbl(((-1_int64) + idx_))
      return
    else
      r = rt_nil()
      return
    end if
  end function glg_at

  subroutine glg_init(gr)
    type(gc_globals), intent(inout) :: gr
    integer(int64) :: gen_1
    integer(int64) :: n_4
    integer(int64) :: n_5
    logical :: t_2
    integer(int64) :: t_3
    gen_1 = gr%gen
    if ((.not. (gen_1 < 0_int64))) then
      t_2 = (gen_1 < 549755813888_int64)
    else
      t_2 = .false.
    end if
    if (t_2) then
      t_3 = (1_int64 + gen_1)
    else
      t_3 = 1_int64
    end if
    gr%gen = t_3
    gr%count = 0_int64
    n_4 = 0_int64
    call rt_resize_val(gr%tbl, n_4)
    n_5 = 8_int64
    call rt_resize_val(gr%tbl, n_5)
  end subroutine glg_init

  subroutine vsg_push(s, hs, i_)
    type(gc_stack), intent(in) :: s
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: i_4
    logical :: t_1
    logical :: t_2
    type(gc_value) :: v_3
    type(gc_value), pointer, contiguous :: slots0_p(:)
    slots0_p => s%slots0
    do
      if ((.not. .true.)) then
        t_2 = (.not. .true.)
      else
        if ((.not. .true.)) then
          t_1 = (.not. .true.)
        else
          t_1 = (.not. (i_ < s%vs_top))
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        v_3 = slots0_p(i_)
        call hpg_push(hs, gv_tag(v_3), gv_ref(v_3))
        i_4 = (1_int64 + i_)
        i_ = i_4
        cycle
      end if
      exit
    end do
  end subroutine vsg_push

  subroutine glg_push(gr, hs, i_)
    type(gc_globals), intent(in) :: gr
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: i_4
    logical :: t_1
    logical :: t_2
    type(gc_value) :: v_3
    do
      if ((.not. .true.)) then
        t_2 = (.not. .true.)
      else
        if ((.not. .true.)) then
          t_1 = (.not. .true.)
        else
          t_1 = (.not. (i_ < gr%count))
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        v_3 = gr%tbl(i_)
        call hpg_push(hs, gv_tag(v_3), gv_ref(v_3))
        i_4 = (1_int64 + i_)
        i_ = i_4
        cycle
      end if
      exit
    end do
  end subroutine glg_push

  subroutine spg_take(s, n_, r)
    type(gc_stack), intent(inout) :: s
    integer(int64), value :: n_
    type(gc_value), intent(out) :: r
    integer(int64) :: d_2
    integer(int64) :: i_4
    logical :: t_1
    type(gc_value) :: v_3
    integer(int64) :: v_5
    if ((.not. (n_ < 1_int64))) then
      t_1 = (.not. (32_int64 < n_))
    else
      t_1 = .false.
    end if
    if (t_1) then
      d_2 = s%nspare0(((-1_int64) + n_))
      if ((0_int64 < d_2)) then
        v_3 = s%spare0(((8_int64 * ((-1_int64) + n_)) + ((-1_int64) + d_2)))
        i_4 = ((-1_int64) + n_)
        v_5 = ((-1_int64) + d_2)
        s%nspare0(i_4) = v_5
        r = v_3
      else
        r = rt_nil()
      end if
    else
      r = rt_nil()
    end if
  end subroutine spg_take

  subroutine spg_clr(hs, j_, e_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: j_
    integer(int64), value :: e_
    integer(int64) :: e_10
    integer(int64) :: i_3
    integer(int64) :: i_5
    integer(int64) :: i_7
    integer(int64) :: j_9
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    integer(int64) :: v_6
    integer(int64) :: v_8
    do
      if ((.not. .true.)) then
        t_2 = (.not. .true.)
      else
        if ((.not. .true.)) then
          t_1 = (.not. .true.)
        else
          t_1 = (.not. (j_ < e_))
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        i_3 = j_
        v_4 = 0_int64
        call hp_set_atag(i_3, v_4)
        i_5 = j_
        v_6 = 0_int64
        call hp_set_aref(i_5, v_6)
        i_7 = j_
        v_8 = 0_int64
        call hp_set_aival(i_7, v_8)
        j_9 = (1_int64 + j_)
        e_10 = e_
        j_ = j_9
        e_ = e_10
        cycle
      end if
      exit
    end do
  end subroutine spg_clr

  subroutine spg_give(s, hs, v_)
    type(gc_stack), intent(inout) :: s
    type(heap_state), intent(inout) :: hs
    type(gc_value), value :: v_
    integer(int64) :: d_4
    integer(int64) :: i_6
    integer(int64) :: i_8
    integer(int64) :: n_2
    integer(int64) :: off_5
    integer(int64) :: ref_1
    logical :: t_3
    type(gc_value) :: v_7
    integer(int64) :: v_9
    if ((.not. (gv_tag(v_) == 9_int64))) then
    else
      ref_1 = gv_ref(v_)
      n_2 = hp_vlen(ref_1)
      if ((.not. (n_2 < 1_int64))) then
        t_3 = (.not. (32_int64 < n_2))
      else
        t_3 = .false.
      end if
      if (t_3) then
        d_4 = s%nspare0(((-1_int64) + n_2))
        if ((d_4 < 8_int64)) then
          off_5 = hp_voff(ref_1)
          call spg_clr(hs, off_5, (off_5 + n_2))
          i_6 = ((8_int64 * ((-1_int64) + n_2)) + d_4)
          v_7 = v_
          s%spare0(i_6) = v_7
          i_8 = ((-1_int64) + n_2)
          v_9 = (1_int64 + d_4)
          s%nspare0(i_8) = v_9
        else
        end if
      else
      end if
    end if
  end subroutine spg_give

  subroutine spg_reset(s, k_)
    type(gc_stack), intent(inout) :: s
    integer(int64), value :: k_
    integer(int64) :: i_2
    integer(int64) :: k_4
    logical :: t_1
    integer(int64) :: v_3
    do
      if ((.not. (k_ >= 0_int64))) then
        t_1 = (.not. (k_ >= 0_int64))
      else
        t_1 = (.not. (k_ < 32_int64))
      end if
      if (t_1) then
      else
        i_2 = k_
        v_3 = 0_int64
        s%nspare0(i_2) = v_3
        k_4 = (1_int64 + k_)
        k_ = k_4
        cycle
      end if
      exit
    end do
  end subroutine spg_reset
