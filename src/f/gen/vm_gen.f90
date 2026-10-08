! GENERATED from model/vmg.lisp by scripts/acl2-fortran. Do not edit:
! change the model, prove it, and generate again (PLAN step 30).
! Every function here has its guards verified in ACL2: every index in
! bounds, every integer inside 64 bits. vmg-correct proves that a
! program run by vmg_run answers what it means. The superinstructions
! and the pass that tags them come from model/vmfg.lisp: vmfg-correct
! proves a compiled program, fused and run by vmg_xrun, answers the same.
module vm_gen
  use iso_fortran_env, only: int64
  use vm_runtime
  implicit none
contains
  pure function bnd40p(x_) result(r)
    integer(int64), value :: x_
    logical :: r
    if (.true.) then
      if ((.not. (x_ < 0_int64))) then
        r = (.not. (1099511627776_int64 < x_))
        return
      else
        r = .false.
        return
      end if
    else
      r = .false.
      return
    end if
  end function bnd40p

  pure function vmg_lens(st) result(r)
    type(vm_state), intent(in) :: st
    logical :: r
    if ((.not. (1099511627776_int64 < size(st%code, kind=int64)))) then
      if ((.not. (1099511627776_int64 < size(st%pool, kind=int64)))) then
        if ((.not. (1099511627776_int64 < size(st%stk, kind=int64)))) then
          if ((.not. (1099511627776_int64 < size(st%ckind, kind=int64)))) then
            if ((.not. (size(st%ca, kind=int64) < size(st%ckind, kind=int64)))) then
              if ((.not. (size(st%cb, kind=int64) < size(st%ckind, kind=int64)))) then
                if ((.not. (size(st%cc, kind=int64) < size(st%ckind, kind=int64)))) then
                  if ((.not. (size(st%cprev, kind=int64) < size(st%ckind, kind=int64)))) then
                    if ((.not. (1099511627776_int64 < size(st%fnfirst, kind=int64)))) then
                      if ((.not. (size(st%fncount, kind=int64) < size(st%fnfirst, kind=int64)))) then
                        if ((.not. (1099511627776_int64 < size(st%cln, kind=int64)))) then
                          if ((.not. (size(st%clent, kind=int64) < size(st%cln, kind=int64)))) then
                            r = (.not. (size(st%clrest, kind=int64) < size(st%cln, kind=int64)))
                            return
                          else
                            r = .false.
                            return
                          end if
                        else
                          r = .false.
                          return
                        end if
                      else
                        r = .false.
                        return
                      end if
                    else
                      r = .false.
                      return
                    end if
                  else
                    r = .false.
                    return
                  end if
                else
                  r = .false.
                  return
                end if
              else
                r = .false.
                return
              end if
            else
              r = .false.
              return
            end if
          else
            r = .false.
            return
          end if
        else
          r = .false.
          return
        end if
      else
        r = .false.
        return
      end if
    else
      r = .false.
      return
    end if
  end function vmg_lens

  pure function words_ok(st, i_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: i_
    logical :: r
    integer(int64) :: i_1
    do
      if ((i_ <= 0_int64)) then
        r = .true.
        return
      else
        if (bnd40p(st%code((-1_int64 + i_)))) then
          i_1 = (-1_int64 + i_)
          i_ = i_1
          cycle
        else
          r = .false.
          return
        end if
      end if
    end do
  end function words_ok

  pure function cls_ok(st, c_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: c_
    logical :: r
    integer(int64) :: c_1
    do
      if ((c_ <= 0_int64)) then
        r = .true.
        return
      else
        if (bnd40p(st%cln((-1_int64 + c_)))) then
          if (bnd40p(st%clent((-1_int64 + c_)))) then
            c_1 = (-1_int64 + c_)
            c_ = c_1
            cycle
          else
            r = .false.
            return
          end if
        else
          r = .false.
          return
        end if
      end if
    end do
  end function cls_ok

  pure function fns_ok(st, f_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: f_
    logical :: r
    integer(int64) :: f_1
    do
      if ((f_ <= 0_int64)) then
        r = .true.
        return
      else
        if (bnd40p(st%fnfirst((-1_int64 + f_)))) then
          if (bnd40p(st%fncount((-1_int64 + f_)))) then
            if ((.not. (size(st%cln, kind=int64) < (st%fnfirst((-1_int64 + f_)) + st%fncount((-1_int64 + f_)))))) then
              f_1 = (-1_int64 + f_)
              f_ = f_1
              cycle
            else
              r = .false.
              return
            end if
          else
            r = .false.
            return
          end if
        else
          r = .false.
          return
        end if
      end if
    end do
  end function fns_ok

  pure function recs_ok(st, j_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: j_
    logical :: r
    integer(int64) :: j_3
    logical :: t_1
    logical :: t_2
    do
      if ((j_ <= 0_int64)) then
        r = .true.
        return
      else
        if (bnd40p(st%ca((-1_int64 + j_)))) then
          if (bnd40p(st%cb((-1_int64 + j_)))) then
            if (bnd40p(st%cc((-1_int64 + j_)))) then
              if (.true.) then
                if ((.not. (st%cprev((-1_int64 + j_)) < -1_int64))) then
                  if ((st%cprev((-1_int64 + j_)) < (-1_int64 + j_))) then
                    if ((st%ckind((-1_int64 + j_)) == 2_int64)) then
                      if ((st%cprev((-1_int64 + j_)) < 0_int64)) then
                        t_1 = (st%cprev((-1_int64 + j_)) < 0_int64)
                      else
                        t_1 = (st%ckind(st%cprev((-1_int64 + j_))) == 2_int64)
                      end if
                      t_2 = t_1
                    else
                      t_2 = .true.
                    end if
                    if (t_2) then
                      j_3 = (-1_int64 + j_)
                      j_ = j_3
                      cycle
                    else
                      r = .false.
                      return
                    end if
                  else
                    r = .false.
                    return
                  end if
                else
                  r = .false.
                  return
                end if
              else
                r = .false.
                return
              end if
            else
              r = .false.
              return
            end if
          else
            r = .false.
            return
          end if
        else
          r = .false.
          return
        end if
      end if
    end do
  end function recs_ok

  pure function vmg_bnd(st) result(r)
    type(vm_state), intent(in) :: st
    logical :: r
    logical :: t_1
    if (vmg_lens(st)) then
      if (bnd40p(st%pc)) then
        if (bnd40p(st%fb)) then
          if (bnd40p(st%sp)) then
            if ((st%ctop >= 0_int64)) then
              if ((.not. (size(st%ckind, kind=int64) < st%ctop))) then
                if ((.not. (st%hidx < -1_int64))) then
                  if ((st%hidx < st%ctop)) then
                    if ((st%hidx < 0_int64)) then
                      t_1 = (st%hidx < 0_int64)
                    else
                      t_1 = (st%ckind(st%hidx) == 2_int64)
                    end if
                    if (t_1) then
                      if (words_ok(st, size(st%code, kind=int64))) then
                        if (cls_ok(st, size(st%cln, kind=int64))) then
                          if (fns_ok(st, size(st%fnfirst, kind=int64))) then
                            r = recs_ok(st, st%ctop)
                            return
                          else
                            r = .false.
                            return
                          end if
                        else
                          r = .false.
                          return
                        end if
                      else
                        r = .false.
                        return
                      end if
                    else
                      r = .false.
                      return
                    end if
                  else
                    r = .false.
                    return
                  end if
                else
                  r = .false.
                  return
                end if
              else
                r = .false.
                return
              end if
            else
              r = .false.
              return
            end if
          else
            r = .false.
            return
          end if
        else
          r = .false.
          return
        end if
      else
        r = .false.
        return
      end if
    else
      r = .false.
      return
    end if
  end function vmg_bnd

  pure function vmg_good(st) result(r)
    type(vm_state), intent(in) :: st
    logical :: r
    logical :: t_1
    if ((st%status == 0_int64)) then
      t_1 = vmg_bnd(st)
    else
      t_1 = .true.
    end if
    r = t_1
    return
  end function vmg_good

  pure function vmg_w(st, pc_, k_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: pc_
    integer(int64), value :: k_
    integer(int64) :: r
    integer(int64) :: i_3
    integer(int64) :: t_4
    integer(int64) :: var_1
    integer(int64) :: var_2
    var_1 = (4_int64 * max(0_int64, pc_))
    var_2 = (var_1 + max(0_int64, k_))
    i_3 = var_2
    if ((i_3 < size(st%code, kind=int64))) then
      t_4 = st%code(i_3)
    else
      t_4 = 0_int64
    end if
    r = t_4
    return
  end function vmg_w

  function vmg_poolv(st, i_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: i_
    type(value) :: r
    if ((max(0_int64, i_) < size(st%pool, kind=int64))) then
      r = st%pool(max(0_int64, i_))
      return
    else
      r = rt_nil()
      return
    end if
  end function vmg_poolv

  function vmg_sreg(st, i_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: i_
    type(value) :: r
    if ((max(0_int64, i_) < size(st%stk, kind=int64))) then
      r = st%stk(max(0_int64, i_))
      return
    else
      r = rt_nil()
      return
    end if
  end function vmg_sreg

  subroutine vmg_sset(st, i_, v_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: i_
    type(value), value :: v_
    integer(int64) :: i_1
    type(value) :: v_2
    if ((max(0_int64, i_) < size(st%stk, kind=int64))) then
      i_1 = max(0_int64, i_)
      v_2 = v_
      st%stk(i_1) = v_2
    else
      st%status = 2_int64
    end if
  end subroutine vmg_sset

  subroutine vmg_copy_down(st, src_, dst_, k_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: src_
    integer(int64), value :: dst_
    integer(int64), value :: k_
    integer(int64) :: dst_4
    integer(int64) :: k_5
    integer(int64) :: src_2
    integer(int64) :: var_1
    integer(int64) :: var_3
    do
      if ((k_ <= 0_int64)) then
      else
        call vmg_sset(st, max(0_int64, dst_), vmg_sreg(st, max(0_int64, src_)))
        var_1 = (1_int64 + max(0_int64, src_))
        src_2 = var_1
        var_3 = (1_int64 + max(0_int64, dst_))
        dst_4 = var_3
        k_5 = (-1_int64 + k_)
        src_ = src_2
        dst_ = dst_4
        k_ = k_5
        cycle
      end if
      exit
    end do
  end subroutine vmg_copy_down

  subroutine vmg_push_rec(st, kind_, a_, b_, c_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: kind_
    integer(int64), value :: a_
    integer(int64), value :: b_
    integer(int64), value :: c_
    integer(int64) :: i_10
    integer(int64) :: i_2
    integer(int64) :: i_4
    integer(int64) :: i_6
    integer(int64) :: i_8
    integer(int64) :: j_1
    integer(int64) :: v_11
    integer(int64) :: v_3
    integer(int64) :: v_5
    integer(int64) :: v_7
    integer(int64) :: v_9
    integer(int64) :: var_12
    j_1 = max(0_int64, st%ctop)
    if ((j_1 < size(st%ckind, kind=int64))) then
      i_2 = j_1
      v_3 = kind_
      st%ckind(i_2) = v_3
      i_4 = j_1
      v_5 = a_
      st%ca(i_4) = v_5
      i_6 = j_1
      v_7 = b_
      st%cb(i_6) = v_7
      i_8 = j_1
      v_9 = c_
      st%cc(i_8) = v_9
      i_10 = j_1
      v_11 = st%hidx
      st%cprev(i_10) = v_11
      if ((kind_ == 2_int64)) then
        st%hidx = j_1
      else
      end if
      var_12 = (1_int64 + j_1)
      st%ctop = var_12
    else
      st%status = 2_int64
    end if
  end subroutine vmg_push_rec

  subroutine vmg_pop_rec(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: j_2
    integer(int64) :: var_1
    var_1 = (-1_int64 + max(0_int64, st%ctop))
    j_2 = var_1
    if ((j_2 < 0_int64)) then
    else
      if ((st%ckind(j_2) == 2_int64)) then
        st%hidx = st%cprev(j_2)
      else
      end if
      st%ctop = j_2
    end if
  end subroutine vmg_pop_rec

  subroutine vmg_unwind(st, v_)
    type(vm_state), intent(inout) :: st
    type(value), value :: v_
    integer(int64) :: h_3
    integer(int64) :: hd_5
    integer(int64) :: hfb_4
    integer(int64) :: j_1
    logical :: t_2
    integer(int64) :: var_6
    integer(int64) :: var_7
    j_1 = st%hidx
    if ((.not. .true.)) then
      t_2 = (.not. .true.)
    else
      t_2 = (j_1 < 0_int64)
    end if
    if (t_2) then
      call vmg_sset(st, 0_int64, v_)
      if ((st%status == 2_int64)) then
      else
        st%status = 1_int64
      end if
      st%pc = 0_int64
      st%fb = 0_int64
      st%sp = 1_int64
      st%ctop = 0_int64
      st%hidx = -1_int64
    else
      h_3 = max(0_int64, st%ca(j_1))
      hfb_4 = max(0_int64, st%cb(j_1))
      hd_5 = max(0_int64, st%cc(j_1))
      var_6 = (hfb_4 + hd_5)
      call vmg_sset(st, var_6, v_)
      st%pc = h_3
      st%fb = hfb_4
      var_7 = (hfb_4 + (hd_5 + 1_int64))
      st%sp = var_7
      st%ctop = j_1
      st%hidx = st%cprev(j_1)
    end if
  end subroutine vmg_unwind

  pure function vmg_pick_fixed(st, ci_, k_, m_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: ci_
    integer(int64), value :: k_
    integer(int64), value :: m_
    integer(int64) :: r
    integer(int64) :: ci_3
    integer(int64) :: k_4
    integer(int64) :: m_5
    logical :: t_1
    integer(int64) :: var_2
    do
      if ((k_ <= 0_int64)) then
        r = -1_int64
        return
      else
        if ((.not. (st%clrest(max(0_int64, ci_)) == 1_int64))) then
          t_1 = (max(0_int64, st%cln(max(0_int64, ci_))) == m_)
        else
          t_1 = .false.
        end if
        if (t_1) then
          r = max(0_int64, ci_)
          return
        else
          var_2 = (1_int64 + max(0_int64, ci_))
          ci_3 = var_2
          k_4 = (-1_int64 + k_)
          m_5 = m_
          ci_ = ci_3
          k_ = k_4
          m_ = m_5
          cycle
        end if
      end if
    end do
  end function vmg_pick_fixed

  pure function vmg_pick_rest(st, ci_, k_, m_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: ci_
    integer(int64), value :: k_
    integer(int64), value :: m_
    integer(int64) :: r
    integer(int64) :: ci_3
    integer(int64) :: k_4
    integer(int64) :: m_5
    logical :: t_1
    integer(int64) :: var_2
    do
      if ((k_ <= 0_int64)) then
        r = -1_int64
        return
      else
        if ((st%clrest(max(0_int64, ci_)) == 1_int64)) then
          t_1 = (.not. (m_ < max(0_int64, st%cln(max(0_int64, ci_)))))
        else
          t_1 = .false.
        end if
        if (t_1) then
          r = max(0_int64, ci_)
          return
        else
          var_2 = (1_int64 + max(0_int64, ci_))
          ci_3 = var_2
          k_4 = (-1_int64 + k_)
          m_5 = m_
          ci_ = ci_3
          k_ = k_4
          m_ = m_5
          cycle
        end if
      end if
    end do
  end function vmg_pick_rest

  pure function vmg_pick(st, f_, m_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: f_
    integer(int64), value :: m_
    integer(int64) :: r
    integer(int64) :: ci_2
    integer(int64) :: k_3
    logical :: t_1
    integer(int64) :: t_5
    integer(int64) :: x_4
    if ((f_ >= 0_int64)) then
      t_1 = (f_ < size(st%fnfirst, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      ci_2 = st%fnfirst(f_)
      k_3 = st%fncount(f_)
      x_4 = vmg_pick_fixed(st, ci_2, k_3, m_)
      if ((.not. (x_4 < 0_int64))) then
        t_5 = x_4
      else
        t_5 = vmg_pick_rest(st, ci_2, k_3, m_)
      end if
      r = t_5
      return
    else
      r = -1_int64
      return
    end if
  end function vmg_pick

  subroutine vmg_push(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: sp_1
    integer(int64) :: var_2
    integer(int64) :: var_3
    sp_1 = max(0_int64, st%sp)
    call vmg_sset(st, sp_1, vmg_poolv(st, vmg_w(st, st%pc, 1_int64)))
    var_2 = (1_int64 + sp_1)
    st%sp = var_2
    var_3 = (1_int64 + max(0_int64, st%pc))
    st%pc = var_3
  end subroutine vmg_push

  subroutine vmg_load(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: sp_1
    integer(int64) :: var_2
    integer(int64) :: var_3
    integer(int64) :: var_4
    sp_1 = max(0_int64, st%sp)
    var_2 = (max(0_int64, st%fb) + max(0_int64, vmg_w(st, st%pc, 1_int64)))
    call vmg_sset(st, sp_1, vmg_sreg(st, var_2))
    var_3 = (1_int64 + sp_1)
    st%sp = var_3
    var_4 = (1_int64 + max(0_int64, st%pc))
    st%pc = var_4
  end subroutine vmg_load

  subroutine vmg_add(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: sp_1
    integer(int64) :: var_2
    integer(int64) :: var_3
    integer(int64) :: var_4
    integer(int64) :: var_5
    integer(int64) :: var_6
    sp_1 = max(0_int64, st%sp)
    if ((sp_1 < 2_int64)) then
    else
      var_2 = (-2_int64 + sp_1)
      var_3 = (-2_int64 + sp_1)
      var_4 = (-1_int64 + sp_1)
      call vmg_sset(st, var_2, rt_add(vmg_sreg(st, var_3), vmg_sreg(st, var_4)))
      var_5 = (-1_int64 + sp_1)
      st%sp = var_5
      var_6 = (1_int64 + max(0_int64, st%pc))
      st%pc = var_6
    end if
  end subroutine vmg_add

  subroutine vmg_lt(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: sp_1
    integer(int64) :: var_2
    integer(int64) :: var_3
    integer(int64) :: var_4
    integer(int64) :: var_5
    integer(int64) :: var_6
    sp_1 = max(0_int64, st%sp)
    if ((sp_1 < 2_int64)) then
    else
      var_2 = (-2_int64 + sp_1)
      var_3 = (-2_int64 + sp_1)
      var_4 = (-1_int64 + sp_1)
      call vmg_sset(st, var_2, rt_lt(vmg_sreg(st, var_3), vmg_sreg(st, var_4)))
      var_5 = (-1_int64 + sp_1)
      st%sp = var_5
      var_6 = (1_int64 + max(0_int64, st%pc))
      st%pc = var_6
    end if
  end subroutine vmg_lt

  subroutine vmg_slide(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: sp_1
    integer(int64) :: var_2
    integer(int64) :: var_3
    integer(int64) :: var_4
    integer(int64) :: var_5
    sp_1 = max(0_int64, st%sp)
    if ((sp_1 < 2_int64)) then
    else
      var_2 = (-2_int64 + sp_1)
      var_3 = (-1_int64 + sp_1)
      call vmg_sset(st, var_2, vmg_sreg(st, var_3))
      var_4 = (-1_int64 + sp_1)
      st%sp = var_4
      var_5 = (1_int64 + max(0_int64, st%pc))
      st%pc = var_5
    end if
  end subroutine vmg_slide

  subroutine vmg_jmpf(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: sp_1
    integer(int64) :: var_2
    integer(int64) :: var_3
    integer(int64) :: var_4
    sp_1 = max(0_int64, st%sp)
    if ((sp_1 <= 0_int64)) then
    else
      var_2 = (-1_int64 + sp_1)
      st%sp = var_2
      var_3 = (-1_int64 + sp_1)
      if (rt_truthy(vmg_sreg(st, var_3))) then
        var_4 = (1_int64 + max(0_int64, st%pc))
        st%pc = var_4
      else
        st%pc = max(0_int64, vmg_w(st, st%pc, 1_int64))
      end if
    end if
  end subroutine vmg_jmpf

  subroutine vmg_jmp(st)
    type(vm_state), intent(inout) :: st
    st%pc = max(0_int64, vmg_w(st, st%pc, 1_int64))
  end subroutine vmg_jmp

  subroutine vmg_mkclo(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: k_2
    integer(int64) :: sp_1
    integer(int64) :: var_3
    integer(int64) :: var_4
    integer(int64) :: var_5
    integer(int64) :: var_6
    sp_1 = max(0_int64, st%sp)
    k_2 = max(0_int64, vmg_w(st, st%pc, 2_int64))
    if ((sp_1 < k_2)) then
    else
      var_3 = (sp_1 + (-k_2))
      var_4 = (sp_1 + (-k_2))
      call vmg_sset(st, var_3, rt_clo(vmg_w(st, st%pc, 1_int64), rt_list_from(st, var_4, k_2)))
      var_5 = (1_int64 + (sp_1 + (-k_2)))
      st%sp = var_5
      var_6 = (1_int64 + max(0_int64, st%pc))
      st%pc = var_6
    end if
  end subroutine vmg_mkclo

  subroutine vmg_capt(st)
    type(vm_state), intent(inout) :: st
    type(value) :: c_3
    integer(int64) :: sp_1
    integer(int64) :: var_2
    integer(int64) :: var_4
    integer(int64) :: var_5
    sp_1 = max(0_int64, st%sp)
    var_2 = (max(0_int64, st%fb) + max(0_int64, vmg_w(st, st%pc, 1_int64)))
    c_3 = vmg_sreg(st, var_2)
    call vmg_sset(st, sp_1, rt_capt(max(0_int64, vmg_w(st, st%pc, 2_int64)), c_3))
    var_4 = (1_int64 + sp_1)
    st%sp = var_4
    var_5 = (1_int64 + max(0_int64, st%pc))
    st%pc = var_5
  end subroutine vmg_capt

  subroutine vmg_callv(st)
    type(vm_state), intent(inout) :: st
    type(value) :: c_5
    integer(int64) :: ci_6
    integer(int64) :: ent_11
    integer(int64) :: fb2_9
    integer(int64) :: m_2
    integer(int64) :: n_10
    integer(int64) :: sp_1
    integer(int64) :: var_12
    integer(int64) :: var_13
    integer(int64) :: var_14
    integer(int64) :: var_15
    integer(int64) :: var_16
    integer(int64) :: var_17
    integer(int64) :: var_3
    integer(int64) :: var_4
    integer(int64) :: var_7
    integer(int64) :: var_8
    sp_1 = max(0_int64, st%sp)
    m_2 = max(0_int64, vmg_w(st, st%pc, 1_int64))
    var_3 = (1_int64 + m_2)
    if ((sp_1 < var_3)) then
    else
      var_4 = (-1_int64 + sp_1)
      c_5 = vmg_sreg(st, var_4)
      if ((.not. rt_clop(c_5))) then
        call vmg_unwind(st, rt_keyword("not-fn"))
      else
        ci_6 = vmg_pick(st, rt_clo_f(c_5), m_2)
        if ((ci_6 < 0_int64)) then
          call vmg_unwind(st, rt_keyword("arity"))
        else
          var_7 = (1_int64 + m_2)
          var_8 = (sp_1 + (-var_7))
          fb2_9 = var_8
          n_10 = max(0_int64, st%cln(ci_6))
          ent_11 = max(0_int64, st%clent(ci_6))
          var_12 = (1_int64 + max(0_int64, st%pc))
          call vmg_push_rec(st, 1_int64, var_12, max(0_int64, st%fb), 0_int64)
          if ((st%clrest(ci_6) == 1_int64)) then
            var_13 = (fb2_9 + n_10)
            var_14 = (fb2_9 + n_10)
            var_15 = (m_2 + (-n_10))
            call vmg_sset(st, var_13, rt_list_from(st, var_14, var_15))
            var_16 = (fb2_9 + (n_10 + 1_int64))
            call vmg_sset(st, var_16, c_5)
            st%fb = fb2_9
            var_17 = (fb2_9 + (n_10 + 2_int64))
            st%sp = var_17
            st%pc = ent_11
          else
            st%fb = fb2_9
            st%pc = ent_11
          end if
        end if
      end if
    end if
  end subroutine vmg_callv

  subroutine vmg_ret(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: fb_2
    logical :: hp_7
    integer(int64) :: j_6
    integer(int64) :: nfb_11
    integer(int64) :: npc_9
    integer(int64) :: sp_1
    integer(int64) :: t_10
    integer(int64) :: t_8
    type(value) :: v_4
    integer(int64) :: var_12
    integer(int64) :: var_3
    integer(int64) :: var_5
    sp_1 = max(0_int64, st%sp)
    fb_2 = max(0_int64, st%fb)
    if ((sp_1 <= 0_int64)) then
    else
      var_3 = (-1_int64 + sp_1)
      v_4 = vmg_sreg(st, var_3)
      if ((st%ctop <= 0_int64)) then
        call vmg_sset(st, 0_int64, v_4)
        st%sp = 1_int64
      else
        var_5 = (-1_int64 + st%ctop)
        j_6 = var_5
        hp_7 = (st%ckind(j_6) == 2_int64)
        if (hp_7) then
          t_8 = 0_int64
        else
          t_8 = max(0_int64, st%ca(j_6))
        end if
        npc_9 = t_8
        if (hp_7) then
          t_10 = max(0_int64, st%ca(j_6))
        else
          t_10 = max(0_int64, st%cb(j_6))
        end if
        nfb_11 = t_10
        call vmg_sset(st, fb_2, v_4)
        var_12 = (1_int64 + fb_2)
        st%sp = var_12
        call vmg_pop_rec(st)
        st%fb = nfb_11
        st%pc = npc_9
      end if
    end if
  end subroutine vmg_ret

  subroutine vmg_recur(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: b_3
    integer(int64) :: fb_5
    integer(int64) :: k_2
    integer(int64) :: l_4
    integer(int64) :: pc_1
    integer(int64) :: sp_6
    integer(int64) :: var_10
    integer(int64) :: var_7
    integer(int64) :: var_8
    integer(int64) :: var_9
    pc_1 = st%pc
    k_2 = max(0_int64, vmg_w(st, pc_1, 1_int64))
    b_3 = max(0_int64, vmg_w(st, pc_1, 2_int64))
    l_4 = max(0_int64, vmg_w(st, pc_1, 3_int64))
    fb_5 = max(0_int64, st%fb)
    sp_6 = max(0_int64, st%sp)
    var_7 = (fb_5 + (b_3 + k_2))
    if ((sp_6 < var_7)) then
    else
      var_8 = (sp_6 + (-k_2))
      var_9 = (fb_5 + b_3)
      call vmg_copy_down(st, var_8, var_9, k_2)
      var_10 = (fb_5 + (b_3 + k_2))
      st%sp = var_10
      st%pc = l_4
    end if
  end subroutine vmg_recur

  subroutine vmg_prim(st)
    type(vm_state), intent(inout) :: st
    type(value) :: a_4
    integer(int64) :: n_2
    integer(int64) :: sp_1
    integer(int64) :: var_3
    integer(int64) :: var_5
    integer(int64) :: var_6
    integer(int64) :: var_7
    sp_1 = max(0_int64, st%sp)
    n_2 = max(0_int64, vmg_w(st, st%pc, 2_int64))
    if ((sp_1 < n_2)) then
    else
      var_3 = (sp_1 + (-n_2))
      a_4 = rt_prim(vmg_poolv(st, vmg_w(st, st%pc, 1_int64)), rt_list_from(st, var_3, n_2))
      if (rt_throwp(a_4)) then
        call vmg_unwind(st, rt_thrown(a_4))
      else
        var_5 = (sp_1 + (-n_2))
        call vmg_sset(st, var_5, a_4)
        var_6 = (1_int64 + (sp_1 + (-n_2)))
        st%sp = var_6
        var_7 = (1_int64 + max(0_int64, st%pc))
        st%pc = var_7
      end if
    end if
  end subroutine vmg_prim

  subroutine vmg_throw(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: sp_1
    integer(int64) :: var_2
    sp_1 = max(0_int64, st%sp)
    if ((sp_1 <= 0_int64)) then
    else
      var_2 = (-1_int64 + sp_1)
      call vmg_unwind(st, vmg_sreg(st, var_2))
    end if
  end subroutine vmg_throw

  subroutine vmg_try(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: pc_1
    integer(int64) :: var_2
    pc_1 = st%pc
    call vmg_push_rec(st, 2_int64, max(0_int64, vmg_w(st, pc_1, 1_int64)), max(0_int64, st%fb), max(0_int64, vmg_w(st, pc_1, 2_int64)))
    var_2 = (1_int64 + max(0_int64, st%pc))
    st%pc = var_2
  end subroutine vmg_try

  subroutine vmg_endtry(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: var_1
    call vmg_pop_rec(st)
    var_1 = (1_int64 + max(0_int64, st%pc))
    st%pc = var_1
  end subroutine vmg_endtry

  subroutine vmg_step(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: case_do_not_use_elsewhere_1
    if ((.not. (st%status == 0_int64))) then
    else
      case_do_not_use_elsewhere_1 = vmg_w(st, st%pc, 0_int64)
      if ((case_do_not_use_elsewhere_1 == 1_int64)) then
        call vmg_push(st)
      else
        if ((case_do_not_use_elsewhere_1 == 2_int64)) then
          call vmg_load(st)
        else
          if ((case_do_not_use_elsewhere_1 == 3_int64)) then
            call vmg_add(st)
          else
            if ((case_do_not_use_elsewhere_1 == 4_int64)) then
              call vmg_lt(st)
            else
              if ((case_do_not_use_elsewhere_1 == 5_int64)) then
                call vmg_slide(st)
              else
                if ((case_do_not_use_elsewhere_1 == 6_int64)) then
                  call vmg_jmpf(st)
                else
                  if ((case_do_not_use_elsewhere_1 == 7_int64)) then
                    call vmg_jmp(st)
                  else
                    if ((case_do_not_use_elsewhere_1 == 8_int64)) then
                      call vmg_mkclo(st)
                    else
                      if ((case_do_not_use_elsewhere_1 == 9_int64)) then
                        call vmg_capt(st)
                      else
                        if ((case_do_not_use_elsewhere_1 == 10_int64)) then
                          call vmg_callv(st)
                        else
                          if ((case_do_not_use_elsewhere_1 == 11_int64)) then
                            call vmg_ret(st)
                          else
                            if ((case_do_not_use_elsewhere_1 == 12_int64)) then
                              call vmg_recur(st)
                            else
                              if ((case_do_not_use_elsewhere_1 == 13_int64)) then
                                call vmg_prim(st)
                              else
                                if ((case_do_not_use_elsewhere_1 == 14_int64)) then
                                  call vmg_throw(st)
                                else
                                  if ((case_do_not_use_elsewhere_1 == 15_int64)) then
                                    call vmg_try(st)
                                  else
                                    if ((case_do_not_use_elsewhere_1 == 16_int64)) then
                                      call vmg_endtry(st)
                                    else
                                    end if
                                  end if
                                end if
                              end if
                            end if
                          end if
                        end if
                      end if
                    end if
                  end if
                end if
              end if
            end if
          end if
        end if
      end if
    end if
  end subroutine vmg_step

  subroutine vmg_run(st, n_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: n_
    integer(int64) :: n_1
    do
      if ((n_ <= 0_int64)) then
      else
        call vmg_step(st)
        n_1 = (-1_int64 + n_)
        n_ = n_1
        cycle
      end if
      exit
    end do
  end subroutine vmg_run

  subroutine vmg_f17(st)
    type(vm_state), intent(inout) :: st
    type(value) :: b_7
    integer(int64) :: i_11
    integer(int64) :: i_8
    integer(int64) :: p_1
    integer(int64) :: sp_2
    type(value) :: v_12
    type(value) :: v_9
    integer(int64) :: var_10
    integer(int64) :: var_13
    integer(int64) :: var_14
    integer(int64) :: var_3
    integer(int64) :: var_5
    type(value) :: x_4
    type(value) :: y_6
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    var_3 = (max(0_int64, st%fb) + max(0_int64, vmg_w(st, p_1, 1_int64)))
    x_4 = vmg_sreg(st, var_3)
    var_5 = (p_1 + 1_int64)
    y_6 = vmg_poolv(st, vmg_w(st, var_5, 1_int64))
    b_7 = rt_lt(x_4, y_6)
    i_8 = sp_2
    v_9 = b_7
    st%stk(i_8) = v_9
    var_10 = (sp_2 + 1_int64)
    i_11 = var_10
    v_12 = y_6
    st%stk(i_11) = v_12
    st%sp = sp_2
    if (rt_truthy(b_7)) then
      var_13 = (p_1 + 4_int64)
      st%pc = var_13
    else
      var_14 = (p_1 + 3_int64)
      st%pc = max(0_int64, vmg_w(st, var_14, 1_int64))
    end if
  end subroutine vmg_f17

  subroutine vmg_f18(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: i_10
    integer(int64) :: i_7
    integer(int64) :: p_1
    integer(int64) :: sp_2
    type(value) :: v_11
    type(value) :: v_8
    integer(int64) :: var_12
    integer(int64) :: var_13
    integer(int64) :: var_3
    integer(int64) :: var_5
    integer(int64) :: var_9
    type(value) :: x_4
    type(value) :: y_6
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    var_3 = (max(0_int64, st%fb) + max(0_int64, vmg_w(st, p_1, 1_int64)))
    x_4 = vmg_sreg(st, var_3)
    var_5 = (p_1 + 1_int64)
    y_6 = vmg_poolv(st, vmg_w(st, var_5, 1_int64))
    i_7 = sp_2
    v_8 = rt_add(x_4, y_6)
    st%stk(i_7) = v_8
    var_9 = (sp_2 + 1_int64)
    i_10 = var_9
    v_11 = y_6
    st%stk(i_10) = v_11
    var_12 = (sp_2 + 1_int64)
    st%sp = var_12
    var_13 = (p_1 + 3_int64)
    st%pc = var_13
  end subroutine vmg_f18

  subroutine vmg_f19(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: fb_3
    integer(int64) :: i_11
    integer(int64) :: i_14
    integer(int64) :: i_6
    integer(int64) :: p_1
    integer(int64) :: sp_2
    type(value) :: v_12
    type(value) :: v_15
    type(value) :: v_7
    integer(int64) :: var_13
    integer(int64) :: var_16
    integer(int64) :: var_17
    integer(int64) :: var_4
    integer(int64) :: var_8
    integer(int64) :: var_9
    type(value) :: x_5
    type(value) :: y_10
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    fb_3 = max(0_int64, st%fb)
    var_4 = (fb_3 + max(0_int64, vmg_w(st, p_1, 1_int64)))
    x_5 = vmg_sreg(st, var_4)
    i_6 = sp_2
    v_7 = x_5
    st%stk(i_6) = v_7
    var_8 = (p_1 + 1_int64)
    var_9 = (fb_3 + max(0_int64, vmg_w(st, var_8, 1_int64)))
    y_10 = vmg_sreg(st, var_9)
    i_11 = sp_2
    v_12 = rt_add(x_5, y_10)
    st%stk(i_11) = v_12
    var_13 = (sp_2 + 1_int64)
    i_14 = var_13
    v_15 = y_10
    st%stk(i_14) = v_15
    var_16 = (sp_2 + 1_int64)
    st%sp = var_16
    var_17 = (p_1 + 3_int64)
    st%pc = var_17
  end subroutine vmg_f19

  subroutine vmg_f20_ok(st, r_)
    type(vm_state), intent(inout) :: st
    type(value), value :: r_
    integer(int64) :: i_3
    integer(int64) :: p_1
    integer(int64) :: sp_2
    type(value) :: v_4
    integer(int64) :: var_5
    integer(int64) :: var_6
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    i_3 = sp_2
    v_4 = r_
    st%stk(i_3) = v_4
    st%sp = sp_2
    if (rt_truthy(r_)) then
      var_5 = (p_1 + 4_int64)
      st%pc = var_5
    else
      var_6 = (p_1 + 3_int64)
      st%pc = max(0_int64, vmg_w(st, var_6, 1_int64))
    end if
  end subroutine vmg_f20_ok

  subroutine vmg_fk_ok(st, r_, k_)
    type(vm_state), intent(inout) :: st
    type(value), value :: r_
    integer(int64), value :: k_
    integer(int64) :: i_3
    integer(int64) :: p_1
    integer(int64) :: sp_2
    type(value) :: v_4
    integer(int64) :: var_5
    integer(int64) :: var_6
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    i_3 = sp_2
    v_4 = r_
    st%stk(i_3) = v_4
    var_5 = (sp_2 + 1_int64)
    st%sp = var_5
    var_6 = (p_1 + max(0_int64, k_))
    st%pc = var_6
  end subroutine vmg_fk_ok

  subroutine vmg_f20(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: i_12
    integer(int64) :: i_9
    integer(int64) :: p_1
    type(value) :: r_8
    integer(int64) :: sp_2
    type(value) :: v_10
    type(value) :: v_13
    integer(int64) :: var_11
    integer(int64) :: var_3
    integer(int64) :: var_5
    integer(int64) :: var_7
    type(value) :: x_4
    type(value) :: y_6
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    var_3 = (max(0_int64, st%fb) + max(0_int64, vmg_w(st, p_1, 1_int64)))
    x_4 = vmg_sreg(st, var_3)
    var_5 = (p_1 + 1_int64)
    y_6 = vmg_poolv(st, vmg_w(st, var_5, 1_int64))
    var_7 = (p_1 + 2_int64)
    r_8 = rt_prim2(vmg_poolv(st, vmg_w(st, var_7, 1_int64)), x_4, y_6)
    i_9 = sp_2
    v_10 = x_4
    st%stk(i_9) = v_10
    var_11 = (sp_2 + 1_int64)
    i_12 = var_11
    v_13 = y_6
    st%stk(i_12) = v_13
    if (rt_throwp(r_8)) then
      call vmg_unwind(st, rt_thrown(r_8))
    else
      call vmg_f20_ok(st, r_8)
    end if
  end subroutine vmg_f20

  subroutine vmg_f21(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: i_7
    integer(int64) :: p_1
    type(value) :: r_6
    integer(int64) :: sp_2
    type(value) :: v_8
    integer(int64) :: var_3
    integer(int64) :: var_5
    type(value) :: x_4
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    var_3 = (max(0_int64, st%fb) + max(0_int64, vmg_w(st, p_1, 1_int64)))
    x_4 = vmg_sreg(st, var_3)
    var_5 = (p_1 + 1_int64)
    r_6 = rt_prim1(vmg_poolv(st, vmg_w(st, var_5, 1_int64)), x_4)
    i_7 = sp_2
    v_8 = x_4
    st%stk(i_7) = v_8
    if (rt_throwp(r_6)) then
      call vmg_unwind(st, rt_thrown(r_6))
    else
      call vmg_fk_ok(st, r_6, 2_int64)
    end if
  end subroutine vmg_f21

  subroutine vmg_f22(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: fb_3
    integer(int64) :: i_12
    integer(int64) :: i_6
    integer(int64) :: p_1
    type(value) :: r_15
    integer(int64) :: sp_2
    type(value) :: v_13
    type(value) :: v_7
    integer(int64) :: var_11
    integer(int64) :: var_14
    integer(int64) :: var_4
    integer(int64) :: var_8
    integer(int64) :: var_9
    type(value) :: x_5
    type(value) :: y_10
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    fb_3 = max(0_int64, st%fb)
    var_4 = (fb_3 + max(0_int64, vmg_w(st, p_1, 1_int64)))
    x_5 = vmg_sreg(st, var_4)
    i_6 = sp_2
    v_7 = x_5
    st%stk(i_6) = v_7
    var_8 = (p_1 + 1_int64)
    var_9 = (fb_3 + max(0_int64, vmg_w(st, var_8, 1_int64)))
    y_10 = vmg_sreg(st, var_9)
    var_11 = (sp_2 + 1_int64)
    i_12 = var_11
    v_13 = y_10
    st%stk(i_12) = v_13
    var_14 = (p_1 + 2_int64)
    r_15 = rt_prim2(vmg_poolv(st, vmg_w(st, var_14, 1_int64)), x_5, y_10)
    if (rt_throwp(r_15)) then
      call vmg_unwind(st, rt_thrown(r_15))
    else
      call vmg_fk_ok(st, r_15, 3_int64)
    end if
  end subroutine vmg_f22

  subroutine vmg_f23(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: i_12
    integer(int64) :: i_9
    integer(int64) :: p_1
    type(value) :: r_8
    integer(int64) :: sp_2
    type(value) :: v_10
    type(value) :: v_13
    integer(int64) :: var_11
    integer(int64) :: var_3
    integer(int64) :: var_5
    integer(int64) :: var_7
    type(value) :: x_4
    type(value) :: y_6
    p_1 = max(0_int64, st%pc)
    sp_2 = max(0_int64, st%sp)
    var_3 = (max(0_int64, st%fb) + max(0_int64, vmg_w(st, p_1, 1_int64)))
    x_4 = vmg_sreg(st, var_3)
    var_5 = (p_1 + 1_int64)
    y_6 = vmg_poolv(st, vmg_w(st, var_5, 1_int64))
    var_7 = (p_1 + 2_int64)
    r_8 = rt_prim2(vmg_poolv(st, vmg_w(st, var_7, 1_int64)), x_4, y_6)
    i_9 = sp_2
    v_10 = x_4
    st%stk(i_9) = v_10
    var_11 = (sp_2 + 1_int64)
    i_12 = var_11
    v_13 = y_6
    st%stk(i_12) = v_13
    if (rt_throwp(r_8)) then
      call vmg_unwind(st, rt_thrown(r_8))
    else
      call vmg_fk_ok(st, r_8, 3_int64)
    end if
  end subroutine vmg_f23

  subroutine vmg_xstep(st)
    type(vm_state), intent(inout) :: st
    integer(int64) :: p_1
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_17
    logical :: t_18
    logical :: t_21
    logical :: t_22
    logical :: t_27
    logical :: t_28
    logical :: t_29
    logical :: t_30
    logical :: t_33
    logical :: t_34
    logical :: t_38
    logical :: t_39
    logical :: t_40
    logical :: t_44
    logical :: t_45
    logical :: t_46
    logical :: t_5
    logical :: t_6
    logical :: t_7
    integer(int64) :: tag_8
    integer(int64) :: var_10
    integer(int64) :: var_11
    integer(int64) :: var_15
    integer(int64) :: var_16
    integer(int64) :: var_19
    integer(int64) :: var_2
    integer(int64) :: var_20
    integer(int64) :: var_23
    integer(int64) :: var_24
    integer(int64) :: var_25
    integer(int64) :: var_26
    integer(int64) :: var_3
    integer(int64) :: var_31
    integer(int64) :: var_32
    integer(int64) :: var_35
    integer(int64) :: var_36
    integer(int64) :: var_37
    integer(int64) :: var_4
    integer(int64) :: var_41
    integer(int64) :: var_42
    integer(int64) :: var_43
    integer(int64) :: var_9
    p_1 = max(0_int64, st%pc)
    if ((st%status == 0_int64)) then
      var_2 = (4_int64 * p_1)
      var_3 = (15_int64 + var_2)
      if ((var_3 < size(st%code, kind=int64))) then
        if ((vmg_w(st, p_1, 0_int64) == 2_int64)) then
          var_4 = (1_int64 + max(0_int64, st%sp))
          t_5 = (var_4 < size(st%stk, kind=int64))
        else
          t_5 = .false.
        end if
        t_6 = t_5
      else
        t_6 = .false.
      end if
      t_7 = t_6
    else
      t_7 = .false.
    end if
    if (t_7) then
      tag_8 = vmg_w(st, p_1, 3_int64)
      if ((tag_8 == 17_int64)) then
        var_9 = (p_1 + 1_int64)
        if ((vmg_w(st, var_9, 0_int64) == 1_int64)) then
          var_10 = (p_1 + 2_int64)
          if ((vmg_w(st, var_10, 0_int64) == 4_int64)) then
            var_11 = (p_1 + 3_int64)
            t_12 = (vmg_w(st, var_11, 0_int64) == 6_int64)
          else
            t_12 = .false.
          end if
          t_13 = t_12
        else
          t_13 = .false.
        end if
        t_14 = t_13
      else
        t_14 = .false.
      end if
      if (t_14) then
        call vmg_f17(st)
      else
        if ((tag_8 == 18_int64)) then
          var_15 = (p_1 + 1_int64)
          if ((vmg_w(st, var_15, 0_int64) == 1_int64)) then
            var_16 = (p_1 + 2_int64)
            t_17 = (vmg_w(st, var_16, 0_int64) == 3_int64)
          else
            t_17 = .false.
          end if
          t_18 = t_17
        else
          t_18 = .false.
        end if
        if (t_18) then
          call vmg_f18(st)
        else
          if ((tag_8 == 19_int64)) then
            var_19 = (p_1 + 1_int64)
            if ((vmg_w(st, var_19, 0_int64) == 2_int64)) then
              var_20 = (p_1 + 2_int64)
              t_21 = (vmg_w(st, var_20, 0_int64) == 3_int64)
            else
              t_21 = .false.
            end if
            t_22 = t_21
          else
            t_22 = .false.
          end if
          if (t_22) then
            call vmg_f19(st)
          else
            if ((tag_8 == 20_int64)) then
              var_23 = (p_1 + 1_int64)
              if ((vmg_w(st, var_23, 0_int64) == 1_int64)) then
                var_24 = (p_1 + 2_int64)
                if ((vmg_w(st, var_24, 0_int64) == 13_int64)) then
                  var_25 = (p_1 + 2_int64)
                  if ((vmg_w(st, var_25, 2_int64) == 2_int64)) then
                    var_26 = (p_1 + 3_int64)
                    t_27 = (vmg_w(st, var_26, 0_int64) == 6_int64)
                  else
                    t_27 = .false.
                  end if
                  t_28 = t_27
                else
                  t_28 = .false.
                end if
                t_29 = t_28
              else
                t_29 = .false.
              end if
              t_30 = t_29
            else
              t_30 = .false.
            end if
            if (t_30) then
              call vmg_f20(st)
            else
              if ((tag_8 == 21_int64)) then
                var_31 = (p_1 + 1_int64)
                if ((vmg_w(st, var_31, 0_int64) == 13_int64)) then
                  var_32 = (p_1 + 1_int64)
                  t_33 = (vmg_w(st, var_32, 2_int64) == 1_int64)
                else
                  t_33 = .false.
                end if
                t_34 = t_33
              else
                t_34 = .false.
              end if
              if (t_34) then
                call vmg_f21(st)
              else
                if ((tag_8 == 22_int64)) then
                  var_35 = (p_1 + 1_int64)
                  if ((vmg_w(st, var_35, 0_int64) == 2_int64)) then
                    var_36 = (p_1 + 2_int64)
                    if ((vmg_w(st, var_36, 0_int64) == 13_int64)) then
                      var_37 = (p_1 + 2_int64)
                      t_38 = (vmg_w(st, var_37, 2_int64) == 2_int64)
                    else
                      t_38 = .false.
                    end if
                    t_39 = t_38
                  else
                    t_39 = .false.
                  end if
                  t_40 = t_39
                else
                  t_40 = .false.
                end if
                if (t_40) then
                  call vmg_f22(st)
                else
                  if ((tag_8 == 23_int64)) then
                    var_41 = (p_1 + 1_int64)
                    if ((vmg_w(st, var_41, 0_int64) == 1_int64)) then
                      var_42 = (p_1 + 2_int64)
                      if ((vmg_w(st, var_42, 0_int64) == 13_int64)) then
                        var_43 = (p_1 + 2_int64)
                        t_44 = (vmg_w(st, var_43, 2_int64) == 2_int64)
                      else
                        t_44 = .false.
                      end if
                      t_45 = t_44
                    else
                      t_45 = .false.
                    end if
                    t_46 = t_45
                  else
                    t_46 = .false.
                  end if
                  if (t_46) then
                    call vmg_f23(st)
                  else
                    call vmg_step(st)
                  end if
                end if
              end if
            end if
          end if
        end if
      end if
    else
      call vmg_step(st)
    end if
  end subroutine vmg_xstep

  subroutine vmg_xrun(st, n_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: n_
    integer(int64) :: n_1
    do
      if ((n_ <= 0_int64)) then
      else
        call vmg_xstep(st)
        n_1 = (-1_int64 + n_)
        n_ = n_1
        cycle
      end if
      exit
    end do
  end subroutine vmg_xrun

  pure function vmg_tag(st, i_) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), value :: i_
    integer(int64) :: r
    integer(int64) :: n1_8
    integer(int64) :: n2_10
    integer(int64) :: o1_2
    integer(int64) :: o2_4
    integer(int64) :: o3_6
    logical :: t_11
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_15
    logical :: t_16
    logical :: t_17
    logical :: t_18
    logical :: t_19
    logical :: t_20
    logical :: t_21
    logical :: t_22
    integer(int64) :: t_23
    integer(int64) :: t_24
    integer(int64) :: t_25
    integer(int64) :: t_26
    integer(int64) :: t_27
    integer(int64) :: t_28
    integer(int64) :: t_29
    integer(int64) :: var_1
    integer(int64) :: var_3
    integer(int64) :: var_5
    integer(int64) :: var_7
    integer(int64) :: var_9
    var_1 = (i_ + 1_int64)
    o1_2 = vmg_w(st, var_1, 0_int64)
    var_3 = (i_ + 2_int64)
    o2_4 = vmg_w(st, var_3, 0_int64)
    var_5 = (i_ + 3_int64)
    o3_6 = vmg_w(st, var_5, 0_int64)
    var_7 = (i_ + 1_int64)
    n1_8 = vmg_w(st, var_7, 2_int64)
    var_9 = (i_ + 2_int64)
    n2_10 = vmg_w(st, var_9, 2_int64)
    if ((o1_2 == 1_int64)) then
      if ((o2_4 == 4_int64)) then
        t_11 = (o3_6 == 6_int64)
      else
        t_11 = .false.
      end if
      t_12 = t_11
    else
      t_12 = .false.
    end if
    if (t_12) then
      t_29 = 17_int64
    else
      if ((o1_2 == 1_int64)) then
        if ((o2_4 == 13_int64)) then
          if ((n2_10 == 2_int64)) then
            t_13 = (o3_6 == 6_int64)
          else
            t_13 = .false.
          end if
          t_14 = t_13
        else
          t_14 = .false.
        end if
        t_15 = t_14
      else
        t_15 = .false.
      end if
      if (t_15) then
        t_28 = 20_int64
      else
        if ((o1_2 == 13_int64)) then
          t_16 = (n1_8 == 1_int64)
        else
          t_16 = .false.
        end if
        if (t_16) then
          t_27 = 21_int64
        else
          if ((o1_2 == 2_int64)) then
            if ((o2_4 == 13_int64)) then
              t_17 = (n2_10 == 2_int64)
            else
              t_17 = .false.
            end if
            t_18 = t_17
          else
            t_18 = .false.
          end if
          if (t_18) then
            t_26 = 22_int64
          else
            if ((o1_2 == 1_int64)) then
              if ((o2_4 == 13_int64)) then
                t_19 = (n2_10 == 2_int64)
              else
                t_19 = .false.
              end if
              t_20 = t_19
            else
              t_20 = .false.
            end if
            if (t_20) then
              t_25 = 23_int64
            else
              if ((o1_2 == 1_int64)) then
                t_21 = (o2_4 == 3_int64)
              else
                t_21 = .false.
              end if
              if (t_21) then
                t_24 = 18_int64
              else
                if ((o1_2 == 2_int64)) then
                  t_22 = (o2_4 == 3_int64)
                else
                  t_22 = .false.
                end if
                if (t_22) then
                  t_23 = 19_int64
                else
                  t_23 = 0_int64
                end if
                t_24 = t_23
              end if
              t_25 = t_24
            end if
            t_26 = t_25
          end if
          t_27 = t_26
        end if
        t_28 = t_27
      end if
      t_29 = t_28
    end if
    r = t_29
    return
  end function vmg_tag

  subroutine vmg_fuse(st, i_, n_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: i_
    integer(int64), value :: n_
    integer(int64) :: i_6
    integer(int64) :: i_9
    integer(int64) :: n_10
    logical :: t_3
    integer(int64) :: v_7
    integer(int64) :: var_1
    integer(int64) :: var_2
    integer(int64) :: var_4
    integer(int64) :: var_5
    integer(int64) :: var_8
    do
      if ((.not. (max(0_int64, i_) < max(0_int64, n_)))) then
        t_3 = (.not. (max(0_int64, i_) < max(0_int64, n_)))
      else
        var_1 = (4_int64 * max(0_int64, i_))
        var_2 = (3_int64 + var_1)
        t_3 = (.not. (var_2 < size(st%code, kind=int64)))
      end if
      if (t_3) then
      else
        if ((vmg_w(st, max(0_int64, i_), 0_int64) == 2_int64)) then
          var_4 = (4_int64 * max(0_int64, i_))
          var_5 = (3_int64 + var_4)
          i_6 = var_5
          v_7 = vmg_tag(st, max(0_int64, i_))
          st%code(i_6) = v_7
        else
        end if
        var_8 = (1_int64 + max(0_int64, i_))
        i_9 = var_8
        n_10 = n_
        i_ = i_9
        n_ = n_10
        cycle
      end if
      exit
    end do
  end subroutine vmg_fuse

  subroutine vmg_fuse_prog(st)
    type(vm_state), intent(inout) :: st
    if ((.not. (1099511627776_int64 < size(st%code, kind=int64)))) then
      call vmg_fuse(st, 0_int64, size(st%code, kind=int64))
    else
    end if
  end subroutine vmg_fuse_prog
end module vm_gen
