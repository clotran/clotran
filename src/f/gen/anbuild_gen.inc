  ! GENERATED from model/anbuild.lisp by scripts/acl2-fortran -b anbuild. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the analyzer's node assembly -- anb_an, one form to its node:
  ! a local, or if, do, def, quote, throw, let*, loop*, letfn*, try, set!, ., new,
  ! recur and fn* built here, their drivers included (what the host decides of
  ! their forms read through analyze.inc's anb_*_kind hooks), the rest the host's
  ! -- guard-verified, reading forms through analyze.inc's
  ! frf_*/frm_* shims and building nodes on the context's value stack through
  ! its anb_* shims, so no node is held in a variable here. anbuild-proof.lisp
  ! proves a whole analysis with no error leaves one node, well-formed by
  ! anpass's reads; anbuild-cost.lisp counts the steps.
  recursive function anb_try_n(xs_) result(r)
    type(gc_value), value :: xs_
    integer(int64) :: r
    integer(int64) :: k_2
    logical :: t_1
    integer(int64) :: t_3
    if ((frf_len(xs_) == 0_int64)) then
      t_1 = (frf_len(xs_) == 0_int64)
    else
      t_1 = (.not. (anf_try_op(frf_nth(xs_, 0_int64)) == 0_int64))
    end if
    if (t_1) then
      r = 0_int64
      return
    else
      if ((frf_len(xs_) < 2_int64)) then
        r = 1_int64
        return
      else
        k_2 = anb_try_n(frf_rest(xs_))
        if ((k_2 < ((-2_int64) + 1099511627776_int64))) then
          t_3 = (1_int64 + k_2)
        else
          t_3 = k_2
        end if
        r = t_3
        return
      end if
    end if
  end function anb_try_n

  function anb_drop(xs_, n_) result(r)
    type(gc_value), value :: xs_
    integer(int64), value :: n_
    type(gc_value) :: r
    integer(int64) :: n_3
    logical :: t_1
    type(gc_value) :: xs_2
    do
      if ((.not. (n_ >= 0_int64))) then
        t_1 = (.not. (n_ >= 0_int64))
      else
        t_1 = (n_ == 0_int64)
      end if
      if (t_1) then
        r = xs_
        return
      else
        xs_2 = frf_rest(xs_)
        n_3 = ((-1_int64) + n_)
        xs_ = xs_2
        n_ = n_3
        cycle
      end if
    end do
  end function anb_drop

  function anb_try_fin(cls_) result(r)
    type(gc_value), value :: cls_
    integer(int64) :: r
    type(gc_value) :: cls_1
    do
      if ((frf_len(cls_) == 0_int64)) then
        r = 0_int64
        return
      else
        if ((anf_try_op(frf_nth(cls_, 0_int64)) == 2_int64)) then
          r = 1_int64
          return
        else
          if ((frf_len(cls_) < 2_int64)) then
            r = 0_int64
            return
          else
            cls_1 = frf_rest(cls_)
            cls_ = cls_1
            cycle
          end if
        end if
      end if
    end do
  end function anb_try_fin

  subroutine anb_lfnames(ls, bs, bv_, i_, c_, start_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: bv_
    integer(int64), value :: i_
    integer(int64), value :: c_
    integer(int64), value :: start_
    integer(int64), intent(out) :: r
    type(gc_value) :: bv_4
    integer(int64) :: c_6
    integer(int64) :: code_3
    integer(int64) :: i_5
    type(gc_value) :: k_2
    integer(int64) :: start_7
    logical :: t_1
    do
      if ((i_ >= 0_int64)) then
        t_1 = (i_ < frm_pairs(bv_))
      else
        t_1 = .false.
      end if
      if (t_1) then
        k_2 = frm_nth(bv_, (2_int64 * i_))
        code_3 = anl_name_code(k_2)
        if ((.not. (code_3 == 0_int64))) then
          call anb_refuse(bs, code_3, k_2)
          r = code_3
        else
          call anl_bind(ls, c_, frm_bid(k_2), (start_ + i_))
          bv_4 = bv_
          i_5 = (1_int64 + i_)
          c_6 = c_
          start_7 = start_
          bv_ = bv_4
          i_ = i_5
          c_ = c_6
          start_ = start_7
          cycle
        end if
      else
        r = 0_int64
      end if
      exit
    end do
  end subroutine anb_lfnames

  subroutine anb_defend(ls, bs, x_, b_, i2_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), value :: i2_
    integer(int64), intent(out) :: r
    integer(int64) :: e_3
    integer(int64) :: m_4
    integer(int64) :: mv_1
    integer(int64) :: mv_2
    call anb_meta(ls, bs, x_, b_, mv_1, mv_2)
    e_3 = mv_1
    m_4 = mv_2
    if ((.not. (e_3 == 0_int64))) then
      r = e_3
    else
      call anb_def(bs, x_, i2_, m_4)
      r = 0_int64
    end if
  end subroutine anb_defend

  recursive subroutine anb_an(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    integer(int64) :: bx_4
    integer(int64) :: code_10
    integer(int64) :: code_11
    integer(int64) :: code_14
    integer(int64) :: code_16
    integer(int64) :: code_17
    integer(int64) :: code_18
    integer(int64) :: code_7
    integer(int64) :: e_13
    integer(int64) :: e_9
    integer(int64) :: mv_1
    integer(int64) :: mv_12
    integer(int64) :: mv_2
    integer(int64) :: mv_8
    integer(int64) :: n_6
    integer(int64) :: slot_3
    integer(int64) :: sp_5
    integer(int64) :: t_15
    if ((frf_kind(x_) == 2_int64)) then
      call anl_lookup(ls, b_, frm_sid(x_), mv_1, mv_2)
      slot_3 = mv_1
      bx_4 = mv_2
      if ((.not. (bx_4 < 0_int64))) then
        call anb_local(bs, x_, slot_3)
        r = 0_int64
      else
        call anb_host(ls, bs, x_, b_, r)
      end if
    else
      if ((.not. (frf_kind(x_) == 3_int64))) then
        call anb_host(ls, bs, x_, b_, r)
      else
        sp_5 = frf_sp(x_)
        n_6 = frf_len(x_)
        select case (sp_5)
        case (1_int64)
          code_7 = anf_if(n_6)
          if ((.not. (code_7 == 0_int64))) then
            call anb_refuse(bs, code_7, x_)
            r = code_7
          else
            call anb_listn(ls, bs, frf_rest(x_), ((-1_int64) + n_6), b_, mv_8)
            e_9 = mv_8
            if ((.not. (e_9 == 0_int64))) then
              r = e_9
            else
              call anb_node(bs, 4_int64, 0_int64, ((-1_int64) + n_6))
              r = 0_int64
            end if
          end if
        case (2_int64)
          call anb_body(ls, bs, frf_rest(x_), b_, r)
        case (3_int64)
          call anb_deff(ls, bs, x_, b_, r)
        case (4_int64)
          code_10 = anf_quote(n_6)
          if ((.not. (code_10 == 0_int64))) then
            call anb_refuse(bs, code_10, x_)
            r = code_10
          else
            call anb_const(bs, frf_nth(x_, 1_int64))
            r = 0_int64
          end if
        case (5_int64)
          code_11 = anf_throw(n_6)
          if ((.not. (code_11 == 0_int64))) then
            call anb_refuse(bs, code_11, x_)
            r = code_11
          else
            call anb_sub(ls, bs, frf_nth(x_, 1_int64), b_, mv_12)
            e_13 = mv_12
            if ((.not. (e_13 == 0_int64))) then
              r = e_13
            else
              call anb_node(bs, 17_int64, 0_int64, 1_int64)
              r = 0_int64
            end if
          end if
        case (6_int64)
          call anb_try(ls, bs, x_, b_, r)
        case (7_int64)
          code_14 = anf_set(n_6)
          if ((code_14 == 0_int64)) then
            t_15 = anf_set_target(frf_nth(x_, 1_int64))
          else
            t_15 = code_14
          end if
          code_16 = t_15
          if ((.not. (code_16 == 0_int64))) then
            call anb_refuse(bs, code_16, x_)
            r = code_16
          else
            call anb_set(ls, bs, x_, b_, r)
          end if
        case (8_int64)
          code_17 = anf_dot(x_)
          if ((.not. (code_17 == 0_int64))) then
            call anb_refuse(bs, code_17, x_)
            r = code_17
          else
            call anb_dot(ls, bs, x_, b_, r)
          end if
        case (9_int64)
          code_18 = anf_new(x_)
          if ((.not. (code_18 == 0_int64))) then
            call anb_refuse(bs, code_18, x_)
            r = code_18
          else
            call anb_new(ls, bs, x_, b_, r)
          end if
        case (11_int64)
          call anb_let(ls, bs, x_, b_, 11_int64, r)
        case (12_int64)
          call anb_let(ls, bs, x_, b_, 12_int64, r)
        case (13_int64)
          call anb_recur(ls, bs, x_, b_, r)
        case (14_int64)
          call anb_fn(ls, bs, x_, b_, r)
        case (15_int64)
          call anb_letfn(ls, bs, x_, b_, r)
        case default
          call anb_host(ls, bs, x_, b_, r)
        end select
      end if
    end if
  end subroutine anb_an

  recursive subroutine anb_deff(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    integer(int64) :: code_1
    integer(int64) :: e_4
    integer(int64) :: init_2
    integer(int64) :: mv_3
    code_1 = anf_def(x_, 0_int64)
    if ((.not. (code_1 == 0_int64))) then
      call anb_refuse(bs, code_1, x_)
      r = code_1
    else
      init_2 = anf_def(x_, 1_int64)
      call anb_defvar(bs, x_)
      if ((0_int64 < init_2)) then
        call anb_hint(bs, frf_nth(x_, 1_int64))
        call anb_sub(ls, bs, frf_nth(x_, init_2), b_, mv_3)
        e_4 = mv_3
        if ((.not. (e_4 == 0_int64))) then
          r = e_4
        else
          call anb_defend(ls, bs, x_, b_, 1_int64, r)
        end if
      else
        call anb_defend(ls, bs, x_, b_, 0_int64, r)
      end if
    end if
  end subroutine anb_deff

  recursive subroutine anb_listn(ls, bs, xs_, n_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: xs_
    integer(int64), value :: n_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    integer(int64) :: b_8
    integer(int64) :: e_4
    integer(int64) :: mv_3
    integer(int64) :: n_7
    logical :: t_1
    logical :: t_2
    logical :: t_5
    type(gc_value) :: xs_6
    do
      if ((.not. (n_ >= 0_int64))) then
        t_2 = (.not. (n_ >= 0_int64))
      else
        if ((n_ == 0_int64)) then
          t_1 = (n_ == 0_int64)
        else
          t_1 = (frf_len(xs_) == 0_int64)
        end if
        t_2 = t_1
      end if
      if (t_2) then
        r = 0_int64
      else
        call anb_sub(ls, bs, frf_nth(xs_, 0_int64), b_, mv_3)
        e_4 = mv_3
        if ((.not. (e_4 == 0_int64))) then
          t_5 = (.not. (e_4 == 0_int64))
        else
          t_5 = (frf_len(xs_) < 2_int64)
        end if
        if (t_5) then
          r = e_4
        else
          xs_6 = frf_rest(xs_)
          n_7 = ((-1_int64) + n_)
          b_8 = b_
          xs_ = xs_6
          n_ = n_7
          b_ = b_8
          cycle
        end if
      end if
      exit
    end do
  end subroutine anb_listn

  recursive subroutine anb_body(ls, bs, xs_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: xs_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    integer(int64) :: e_2
    integer(int64) :: mv_1
    call anb_listn(ls, bs, xs_, frf_len(xs_), b_, mv_1)
    e_2 = mv_1
    if ((.not. (e_2 == 0_int64))) then
      r = e_2
    else
      call anb_node(bs, 5_int64, 0_int64, frf_len(xs_))
      r = 0_int64
    end if
  end subroutine anb_body

  recursive subroutine anb_binds(ls, bs, bv_, i_, c_, start_, loopp_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: bv_
    integer(int64), value :: i_
    integer(int64), value :: c_
    integer(int64), value :: start_
    integer(int64), value :: loopp_
    integer(int64), intent(out) :: r
    type(gc_value) :: bv_8
    integer(int64) :: c_10
    integer(int64) :: code_3
    integer(int64) :: e_5
    integer(int64) :: e_7
    integer(int64) :: i_9
    type(gc_value) :: k_2
    integer(int64) :: loopp_12
    integer(int64) :: mv_4
    integer(int64) :: slot_6
    integer(int64) :: start_11
    logical :: t_1
    do
      if ((i_ >= 0_int64)) then
        t_1 = (i_ < frm_pairs(bv_))
      else
        t_1 = .false.
      end if
      if (t_1) then
        k_2 = frm_nth(bv_, (2_int64 * i_))
        code_3 = anl_name_code(k_2)
        if ((.not. (code_3 == 0_int64))) then
          call anb_refuse(bs, code_3, k_2)
          r = code_3
        else
          call anb_hint(bs, k_2)
          call anb_sub(ls, bs, frm_nth(bv_, (1_int64 + (2_int64 * i_))), c_, mv_4)
          e_5 = mv_4
          if ((.not. (e_5 == 0_int64))) then
            r = e_5
          else
            slot_6 = (start_ + i_)
            call anl_bind(ls, c_, frm_bid(k_2), slot_6)
            e_7 = anb_let_kind(k_2, c_, slot_6, loopp_)
            if ((.not. (e_7 == 0_int64))) then
              r = e_7
            else
              bv_8 = bv_
              i_9 = (1_int64 + i_)
              c_10 = c_
              start_11 = start_
              loopp_12 = loopp_
              bv_ = bv_8
              i_ = i_9
              c_ = c_10
              start_ = start_11
              loopp_ = loopp_12
              cycle
            end if
          end if
        end if
      else
        r = 0_int64
      end if
      exit
    end do
  end subroutine anb_binds

  recursive subroutine anb_let(ls, bs, x_, b_, kind_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), value :: kind_
    integer(int64), intent(out) :: r
    type(gc_value) :: bv_1
    integer(int64) :: c_4
    integer(int64) :: code_2
    integer(int64) :: e_13
    integer(int64) :: e_15
    integer(int64) :: e_17
    integer(int64) :: loopp_7
    integer(int64) :: mv_12
    integer(int64) :: mv_14
    integer(int64) :: mv_3
    integer(int64) :: mv_8
    integer(int64) :: n_5
    integer(int64) :: ret_11
    integer(int64) :: start_9
    integer(int64) :: t_10
    integer(int64) :: t_16
    integer(int64) :: t_6
    bv_1 = frf_nth(x_, 1_int64)
    code_2 = anl_shape(bv_1)
    if ((.not. (code_2 == 0_int64))) then
      call anb_refuse(bs, code_2, bv_1)
      r = code_2
    else
      call anb_child(ls, b_, mv_3)
      c_4 = mv_3
      n_5 = frm_pairs(bv_1)
      if ((kind_ == 12_int64)) then
        t_6 = 1_int64
      else
        t_6 = 0_int64
      end if
      loopp_7 = t_6
      call anl_reserve(ls, c_4, n_5, mv_8)
      start_9 = mv_8
      if ((loopp_7 == 1_int64)) then
        t_10 = anb_loop_open(c_4, start_9, n_5)
      else
        t_10 = 0_int64
      end if
      ret_11 = t_10
      call anb_binds(ls, bs, bv_1, 0_int64, c_4, start_9, loopp_7, mv_12)
      e_13 = mv_12
      if ((.not. (e_13 == 0_int64))) then
        r = e_13
      else
        call anb_body(ls, bs, frf_rest(frf_rest(x_)), c_4, mv_14)
        e_15 = mv_14
        if ((.not. (e_15 == 0_int64))) then
          r = e_15
        else
          if ((loopp_7 == 1_int64)) then
            t_16 = anb_let_ret(c_4, ret_11)
          else
            t_16 = 0_int64
          end if
          e_17 = t_16
          if ((.not. (e_17 == 0_int64))) then
            r = e_17
          else
            call anb_node_s(bs, kind_, n_5, (1_int64 + n_5), start_9)
            r = 0_int64
          end if
        end if
      end if
    end if
  end subroutine anb_let

  recursive subroutine anb_lfinits(ls, bs, bv_, i_, c_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: bv_
    integer(int64), value :: i_
    integer(int64), value :: c_
    integer(int64), intent(out) :: r
    type(gc_value) :: bv_4
    integer(int64) :: c_6
    integer(int64) :: e_3
    integer(int64) :: i_5
    integer(int64) :: mv_2
    logical :: t_1
    do
      if ((i_ >= 0_int64)) then
        t_1 = (i_ < frm_pairs(bv_))
      else
        t_1 = .false.
      end if
      if (t_1) then
        call anb_sub(ls, bs, frm_nth(bv_, (1_int64 + (2_int64 * i_))), c_, mv_2)
        e_3 = mv_2
        if ((.not. (e_3 == 0_int64))) then
          r = e_3
        else
          bv_4 = bv_
          i_5 = (1_int64 + i_)
          c_6 = c_
          bv_ = bv_4
          i_ = i_5
          c_ = c_6
          cycle
        end if
      else
        r = 0_int64
      end if
      exit
    end do
  end subroutine anb_lfinits

  recursive subroutine anb_letfn(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    type(gc_value) :: bv_1
    integer(int64) :: c_4
    integer(int64) :: code_2
    integer(int64) :: code_9
    integer(int64) :: e_11
    integer(int64) :: e_13
    integer(int64) :: mv_10
    integer(int64) :: mv_12
    integer(int64) :: mv_3
    integer(int64) :: mv_6
    integer(int64) :: mv_8
    integer(int64) :: n_5
    integer(int64) :: start_7
    bv_1 = frf_nth(x_, 1_int64)
    code_2 = anl_shape(bv_1)
    if ((.not. (code_2 == 0_int64))) then
      call anb_refuse(bs, code_2, bv_1)
      r = code_2
    else
      call anb_child(ls, b_, mv_3)
      c_4 = mv_3
      n_5 = frm_pairs(bv_1)
      call anl_reserve(ls, c_4, n_5, mv_6)
      start_7 = mv_6
      call anb_lfnames(ls, bs, bv_1, 0_int64, c_4, start_7, mv_8)
      code_9 = mv_8
      if ((.not. (code_9 == 0_int64))) then
        r = code_9
      else
        call anb_lfinits(ls, bs, bv_1, 0_int64, c_4, mv_10)
        e_11 = mv_10
        if ((.not. (e_11 == 0_int64))) then
          r = e_11
        else
          call anb_body(ls, bs, frf_rest(frf_rest(x_)), c_4, mv_12)
          e_13 = mv_12
          if ((.not. (e_13 == 0_int64))) then
            r = e_13
          else
            call anb_node_s(bs, 13_int64, n_5, (1_int64 + n_5), start_7)
            r = 0_int64
          end if
        end if
      end if
    end if
  end subroutine anb_letfn

  recursive subroutine anb_try(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    type(gc_value) :: cls_5
    integer(int64) :: e_4
    integer(int64) :: e_7
    integer(int64) :: mv_3
    integer(int64) :: mv_6
    integer(int64) :: nb_2
    type(gc_value) :: xs_1
    xs_1 = frf_rest(x_)
    nb_2 = anb_try_n(xs_1)
    call anb_listn(ls, bs, xs_1, nb_2, b_, mv_3)
    e_4 = mv_3
    if ((.not. (e_4 == 0_int64))) then
      r = e_4
    else
      call anb_node(bs, 5_int64, 0_int64, nb_2)
      cls_5 = anb_drop(xs_1, nb_2)
      call anb_try_walk(ls, bs, cls_5, 0_int64, b_, mv_6)
      e_7 = mv_6
      if ((.not. (e_7 == 0_int64))) then
        r = e_7
      else
        call anb_trynode(bs, anb_try_fin(cls_5))
        r = 0_int64
      end if
    end if
  end subroutine anb_try

  recursive subroutine anb_try_walk(ls, bs, cls_, st_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: cls_
    integer(int64), value :: st_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    integer(int64) :: b_16
    integer(int64) :: b_19
    integer(int64) :: c_9
    type(gc_value) :: cls_14
    type(gc_value) :: cls_17
    integer(int64) :: code_4
    integer(int64) :: code_7
    integer(int64) :: e_13
    type(gc_value) :: f_1
    integer(int64) :: lastp_3
    integer(int64) :: mv_10
    integer(int64) :: mv_12
    integer(int64) :: mv_8
    integer(int64) :: op_5
    integer(int64) :: slot_11
    integer(int64) :: st2_6
    integer(int64) :: st_15
    integer(int64) :: st_18
    integer(int64) :: t_2
    do
      if ((frf_len(cls_) == 0_int64)) then
        r = 0_int64
      else
        f_1 = frf_nth(cls_, 0_int64)
        if ((frf_len(cls_) < 2_int64)) then
          t_2 = 1_int64
        else
          t_2 = 0_int64
        end if
        lastp_3 = t_2
        code_4 = anf_try_step(st_, f_1, lastp_3, 0_int64)
        op_5 = anf_try_step(st_, f_1, lastp_3, 1_int64)
        st2_6 = anf_try_step(st_, f_1, lastp_3, 2_int64)
        if ((.not. (code_4 == 0_int64))) then
          call anb_refuse(bs, code_4, f_1)
          r = code_4
        else
          if ((op_5 == 1_int64)) then
            code_7 = anf_catch(f_1)
            if ((.not. (code_7 == 0_int64))) then
              call anb_refuse_catch(bs, code_7, f_1)
              r = code_7
            else
              call anb_child(ls, b_, mv_8)
              c_9 = mv_8
              call anl_reserve(ls, c_9, 1_int64, mv_10)
              slot_11 = mv_10
              call anl_bind(ls, c_9, frm_bid(frf_nth(f_1, 2_int64)), slot_11)
              call anb_body(ls, bs, frf_rest(frf_rest(frf_rest(f_1))), c_9, mv_12)
              e_13 = mv_12
              if ((.not. (e_13 == 0_int64))) then
                r = e_13
              else
                call anb_catch(bs, f_1, slot_11)
                if ((frf_len(cls_) < 2_int64)) then
                  r = 0_int64
                else
                  cls_14 = frf_rest(cls_)
                  st_15 = st2_6
                  b_16 = b_
                  cls_ = cls_14
                  st_ = st_15
                  b_ = b_16
                  cycle
                end if
              end if
            end if
          else
            if ((op_5 == 2_int64)) then
              call anb_body(ls, bs, frf_rest(f_1), b_, r)
            else
              if ((frf_len(cls_) < 2_int64)) then
                r = 0_int64
              else
                cls_17 = frf_rest(cls_)
                st_18 = st2_6
                b_19 = b_
                cls_ = cls_17
                st_ = st_18
                b_ = b_19
                cycle
              end if
            end if
          end if
        end if
      end if
      exit
    end do
  end subroutine anb_try_walk

  subroutine anb_params(ls, pv_, i_, c_, k_)
    type(anl_state), intent(inout) :: ls
    type(gc_value), value :: pv_
    integer(int64), value :: i_
    integer(int64), value :: c_
    integer(int64), value :: k_
    integer(int64) :: c_5
    integer(int64) :: c_9
    integer(int64) :: i_4
    integer(int64) :: i_8
    integer(int64) :: k_10
    integer(int64) :: k_6
    type(gc_value) :: p_2
    type(gc_value) :: pv_3
    type(gc_value) :: pv_7
    logical :: t_1
    do
      if ((i_ >= 0_int64)) then
        t_1 = (i_ < frm_count(pv_))
      else
        t_1 = .false.
      end if
      if (t_1) then
        p_2 = frm_nth(pv_, i_)
        if ((frm_amp(p_2) == 1_int64)) then
          pv_3 = pv_
          i_4 = (1_int64 + i_)
          c_5 = c_
          k_6 = k_
          pv_ = pv_3
          i_ = i_4
          c_ = c_5
          k_ = k_6
          cycle
        else
          call anl_bind(ls, c_, frm_bid(p_2), k_)
          pv_7 = pv_
          i_8 = (1_int64 + i_)
          c_9 = c_
          k_10 = (1_int64 + k_)
          pv_ = pv_7
          i_ = i_8
          c_ = c_9
          k_ = k_10
          cycle
        end if
      else
      end if
      exit
    end do
  end subroutine anb_params

  subroutine anb_self(ls, r_, nm_, r)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: r_
    type(gc_value), value :: nm_
    integer(int64), intent(out) :: r
    integer(int64) :: mv_1
    integer(int64) :: s_2
    if ((frm_kind(nm_) == 2_int64)) then
      call anl_reserve(ls, r_, 1_int64, mv_1)
      s_2 = mv_1
      call anl_bind(ls, r_, frm_bid(nm_), s_2)
      r = s_2
    else
      r = (-1_int64)
    end if
  end subroutine anb_self

  recursive subroutine anb_set(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    integer(int64) :: e_4
    integer(int64) :: e_6
    integer(int64) :: e_8
    integer(int64) :: k_1
    integer(int64) :: mv_3
    integer(int64) :: mv_5
    integer(int64) :: mv_7
    logical :: t_2
    k_1 = anb_set_kind(x_, b_)
    if ((k_1 == 2_int64)) then
      call anb_host2(ls, bs, 1_int64, x_, b_, r)
    else
      if ((k_1 == 1_int64)) then
        t_2 = (frf_kind(frf_nth(x_, 1_int64)) == 3_int64)
      else
        t_2 = .false.
      end if
      if (t_2) then
        call anb_sub(ls, bs, frf_nth(frf_nth(x_, 1_int64), 1_int64), b_, mv_3)
        e_4 = mv_3
        if ((.not. (e_4 == 0_int64))) then
          r = e_4
        else
          call anb_sub(ls, bs, frf_nth(x_, 2_int64), b_, mv_5)
          e_6 = mv_5
          if ((.not. (e_6 == 0_int64))) then
            r = e_6
          else
            call anb_setnode(bs, x_, 2_int64)
            r = 0_int64
          end if
        end if
      else
        if ((k_1 == 0_int64)) then
          call anb_sub(ls, bs, frf_nth(x_, 2_int64), b_, mv_7)
          e_8 = mv_7
          if ((.not. (e_8 == 0_int64))) then
            r = e_8
          else
            call anb_setnode(bs, x_, 1_int64)
            r = 0_int64
          end if
        else
          r = 1_int64
        end if
      end if
    end if
  end subroutine anb_set

  recursive subroutine anb_dot(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    type(gc_value) :: args_11
    type(gc_value) :: args_5
    integer(int64) :: e_13
    integer(int64) :: e_2
    integer(int64) :: e_7
    integer(int64) :: e_9
    integer(int64) :: k_3
    integer(int64) :: mv_1
    integer(int64) :: mv_12
    integer(int64) :: mv_6
    integer(int64) :: mv_8
    type(gc_value) :: t_10
    type(gc_value) :: t_4
    if ((.not. (anf_dot_member(frf_len(x_), frf_norm(frf_nth(x_, 2_int64))) == 0_int64))) then
      if ((frf_class(frf_nth(x_, 1_int64)) == 1_int64)) then
        call anb_refuse(bs, 37_int64, x_)
        r = 37_int64
      else
        call anb_sub(ls, bs, frf_nth(x_, 1_int64), b_, mv_1)
        e_2 = mv_1
        if ((.not. (e_2 == 0_int64))) then
          r = e_2
        else
          call anb_refuse(bs, 37_int64, x_)
          r = 37_int64
        end if
      end if
    else
      k_3 = anb_dot_kind(x_, b_)
      select case (k_3)
      case (2_int64)
        call anb_host2(ls, bs, 2_int64, x_, b_, r)
      case (1_int64)
        call anb_const(bs, frf_nth(x_, 1_int64))
        if ((frf_kind(frf_norm(frf_nth(x_, 2_int64))) == 3_int64)) then
          t_4 = frf_rest(frf_norm(frf_nth(x_, 2_int64)))
        else
          t_4 = frf_rest(frf_rest(frf_rest(x_)))
        end if
        args_5 = t_4
        call anb_listn(ls, bs, args_5, frf_len(args_5), b_, mv_6)
        e_7 = mv_6
        if ((.not. (e_7 == 0_int64))) then
          r = e_7
        else
          call anb_dotnode(bs, x_, 1_int64, (1_int64 + frf_len(args_5)))
          r = 0_int64
        end if
      case (0_int64)
        call anb_sub(ls, bs, frf_nth(x_, 1_int64), b_, mv_8)
        e_9 = mv_8
        if ((.not. (e_9 == 0_int64))) then
          r = e_9
        else
          if ((frf_kind(frf_norm(frf_nth(x_, 2_int64))) == 3_int64)) then
            t_10 = frf_rest(frf_norm(frf_nth(x_, 2_int64)))
          else
            t_10 = frf_rest(frf_rest(frf_rest(x_)))
          end if
          args_11 = t_10
          call anb_listn(ls, bs, args_11, frf_len(args_11), b_, mv_12)
          e_13 = mv_12
          if ((.not. (e_13 == 0_int64))) then
            r = e_13
          else
            call anb_dotnode(bs, x_, 0_int64, (1_int64 + frf_len(args_11)))
            r = 0_int64
          end if
        end if
      case default
        r = 1_int64
      end select
    end if
  end subroutine anb_dot

  recursive subroutine anb_new(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    type(gc_value) :: args_1
    integer(int64) :: e_3
    integer(int64) :: mv_2
    if ((anb_new_kind(x_) == 2_int64)) then
      call anb_host2(ls, bs, 3_int64, x_, b_, r)
    else
      args_1 = frf_rest(frf_rest(x_))
      call anb_listn(ls, bs, args_1, frf_len(args_1), b_, mv_2)
      e_3 = mv_2
      if ((.not. (e_3 == 0_int64))) then
        r = e_3
      else
        call anb_newnode(bs, x_, frf_len(args_1))
        r = 0_int64
      end if
    end if
  end subroutine anb_new

  recursive subroutine anb_recur(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    type(gc_value) :: args_1
    integer(int64) :: e_3
    integer(int64) :: mv_2
    args_1 = frf_rest(x_)
    if ((.not. (anb_recur_open(x_, b_) == 0_int64))) then
      r = 1_int64
    else
      call anb_listn(ls, bs, args_1, frf_len(args_1), b_, mv_2)
      e_3 = mv_2
      if ((.not. (e_3 == 0_int64))) then
        r = e_3
      else
        if ((.not. (anb_recur_check(x_, b_, frf_len(args_1)) == 0_int64))) then
          r = 1_int64
        else
          call anb_recurnode(bs, x_, b_, frf_len(args_1))
          r = 0_int64
        end if
      end if
    end if
  end subroutine anb_recur

  recursive subroutine anb_fn(ls, bs, x_, b_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), intent(out) :: r
    integer(int64) :: e_14
    integer(int64) :: e_16
    integer(int64) :: h_8
    integer(int64) :: mv_13
    integer(int64) :: mv_15
    integer(int64) :: mv_4
    integer(int64) :: mv_6
    integer(int64) :: n_12
    integer(int64) :: named_3
    type(gc_value) :: nm_1
    integer(int64) :: r_5
    integer(int64) :: self_7
    integer(int64) :: t_11
    integer(int64) :: t_2
    type(gc_value) :: t_9
    type(gc_value) :: xs_10
    nm_1 = frf_nth(x_, 1_int64)
    if ((frm_kind(nm_1) == 2_int64)) then
      t_2 = 1_int64
    else
      t_2 = 0_int64
    end if
    named_3 = t_2
    call anb_newfn(ls, b_, mv_4)
    r_5 = mv_4
    call anb_self(ls, r_5, nm_1, mv_6)
    self_7 = mv_6
    h_8 = anb_fn_open(x_, r_5, self_7)
    if ((named_3 == 1_int64)) then
      t_9 = frf_rest(frf_rest(x_))
    else
      t_9 = frf_rest(x_)
    end if
    xs_10 = t_9
    if ((frm_kind(frf_nth(xs_10, 0_int64)) == 1_int64)) then
      t_11 = 1_int64
    else
      t_11 = frf_len(xs_10)
    end if
    n_12 = t_11
    if ((.not. (h_8 == 0_int64))) then
      r = h_8
    else
      if ((frm_kind(frf_nth(xs_10, 0_int64)) == 1_int64)) then
        call anb_method(ls, bs, xs_10, r_5, mv_13)
        e_14 = mv_13
        if ((.not. (e_14 == 0_int64))) then
          r = e_14
        else
          if ((.not. (anl_arity_end(ls, r_5) == 0_int64))) then
            call anb_refuse(bs, 12_int64, x_)
            r = 12_int64
          else
            if ((.not. (anb_fn_check(x_, r_5, n_12) == 0_int64))) then
              r = 1_int64
            else
              call anl_caps_of(ls, r_5)
              call anb_fnclose(ls, bs, x_, r_5, n_12)
              r = 0_int64
            end if
          end if
        end if
      else
        call anb_methods(ls, bs, xs_10, frf_len(xs_10), r_5, mv_15)
        e_16 = mv_15
        if ((.not. (e_16 == 0_int64))) then
          r = e_16
        else
          if ((.not. (anl_arity_end(ls, r_5) == 0_int64))) then
            call anb_refuse(bs, 12_int64, x_)
            r = 12_int64
          else
            if ((.not. (anb_fn_check(x_, r_5, n_12) == 0_int64))) then
              r = 1_int64
            else
              call anl_caps_of(ls, r_5)
              call anb_fnclose(ls, bs, x_, r_5, n_12)
              r = 0_int64
            end if
          end if
        end if
      end if
    end if
  end subroutine anb_fn

  recursive subroutine anb_methods(ls, bs, ms_, n_, r_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: ms_
    integer(int64), value :: n_
    integer(int64), value :: r_
    integer(int64), intent(out) :: r
    integer(int64) :: e_4
    type(gc_value) :: ms_6
    integer(int64) :: mv_3
    integer(int64) :: n_7
    integer(int64) :: r_8
    logical :: t_1
    logical :: t_2
    logical :: t_5
    do
      if ((.not. (n_ >= 0_int64))) then
        t_2 = (.not. (n_ >= 0_int64))
      else
        if ((n_ == 0_int64)) then
          t_1 = (n_ == 0_int64)
        else
          t_1 = (frf_len(ms_) == 0_int64)
        end if
        t_2 = t_1
      end if
      if (t_2) then
        r = 0_int64
      else
        call anb_method(ls, bs, frf_nth(ms_, 0_int64), r_, mv_3)
        e_4 = mv_3
        if ((.not. (e_4 == 0_int64))) then
          t_5 = (.not. (e_4 == 0_int64))
        else
          t_5 = (frf_len(ms_) < 2_int64)
        end if
        if (t_5) then
          r = e_4
        else
          ms_6 = frf_rest(ms_)
          n_7 = ((-1_int64) + n_)
          r_8 = r_
          ms_ = ms_6
          n_ = n_7
          r_ = r_8
          cycle
        end if
      end if
      exit
    end do
  end subroutine anb_methods

  recursive subroutine anb_method(ls, bs, m_, r_, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: m_
    integer(int64), value :: r_
    integer(int64), intent(out) :: r
    type(gc_value) :: cl_1
    integer(int64) :: code_14
    integer(int64) :: code_18
    integer(int64) :: code_3
    integer(int64) :: e_12
    integer(int64) :: e_16
    integer(int64) :: h_10
    integer(int64) :: mb_7
    integer(int64) :: mv_11
    integer(int64) :: mv_13
    integer(int64) :: mv_15
    integer(int64) :: mv_17
    integer(int64) :: mv_6
    integer(int64) :: mv_8
    integer(int64) :: nreq_4
    type(gc_value) :: pv_2
    integer(int64) :: rest_5
    integer(int64) :: start_9
    cl_1 = frf_norm(m_)
    pv_2 = frf_nth(cl_1, 0_int64)
    if ((.not. (frm_kind(pv_2) == 1_int64))) then
      call anb_refuse(bs, 13_int64, cl_1)
      r = 13_int64
    else
      code_3 = anl_params(pv_2, 0_int64)
      if ((.not. (code_3 == 0_int64))) then
        call anb_refuse(bs, code_3, frm_nth(pv_2, anl_params(pv_2, 1_int64)))
        r = code_3
      else
        nreq_4 = anl_params(pv_2, 2_int64)
        rest_5 = anl_params(pv_2, 3_int64)
        call anb_child(ls, r_, mv_6)
        mb_7 = mv_6
        call anl_reserve(ls, mb_7, (nreq_4 + rest_5), mv_8)
        start_9 = mv_8
        call anb_params(ls, pv_2, 0_int64, mb_7, start_9)
        h_10 = anb_method_open(cl_1, r_, mb_7, start_9, nreq_4, rest_5)
        if ((h_10 == 1_int64)) then
          r = 1_int64
        else
          if ((h_10 == 2_int64)) then
            call anb_host2(ls, bs, 4_int64, cl_1, mb_7, mv_11)
            e_12 = mv_11
            if ((.not. (e_12 == 0_int64))) then
              r = e_12
            else
              if ((.not. (anb_method_check(mb_7) == 0_int64))) then
                r = 1_int64
              else
                call anl_arity(ls, r_, nreq_4, rest_5, mv_13)
                code_14 = mv_13
                if ((.not. (code_14 == 0_int64))) then
                  call anb_refuse(bs, code_14, cl_1)
                  r = code_14
                else
                  call anb_arity(bs, cl_1, mb_7, start_9, nreq_4, rest_5)
                  r = 0_int64
                end if
              end if
            end if
          else
            call anb_body(ls, bs, frf_rest(cl_1), mb_7, mv_15)
            e_16 = mv_15
            if ((.not. (e_16 == 0_int64))) then
              r = e_16
            else
              if ((.not. (anb_method_check(mb_7) == 0_int64))) then
                r = 1_int64
              else
                call anl_arity(ls, r_, nreq_4, rest_5, mv_17)
                code_18 = mv_17
                if ((.not. (code_18 == 0_int64))) then
                  call anb_refuse(bs, code_18, cl_1)
                  r = code_18
                else
                  call anb_arity(bs, cl_1, mb_7, start_9, nreq_4, rest_5)
                  r = 0_int64
                end if
              end if
            end if
          end if
        end if
      end if
    end if
  end subroutine anb_method
