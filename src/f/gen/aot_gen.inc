  ! GENERATED from model/aot.lisp by scripts/acl2-fortran -b aot. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the ahead-of-time compiler's eligibility scan (aot_sc: some
  ! node of a kind compiler.cljf does not emit has a recur under it, aot_fr, not
  ! past a loop, fn or lazy seq), guard-verified, reading the tree through
  ! analyze.inc's ast_* shims and Eval.f90's aot_nbods, aot_bod. B_AOTSCAN
  ! (clotran-aot-scan) answers it to decline-reason. aot-proof.lisp proves a node
  ! with no such recur makes none in any run (aot-handed-norec), that a passing
  ! scan leaves none (aot-sc-sound, aot-scan-norec), and counts it (aot-sc-steps-bound).
  ! And the compiler's type inference (aot_ty: infer, call-type, bind-types, loop-env)
  ! over aot_state, reading aot_hop, aot_cty, aot_kw, aot_i2, aot_s2, aot_rs, aot_rn;
  ! B_AOTTY (clotran-aot-ty, analyze.inc's aot_infer) answers it. Its proof is owed
  ! (model/aot-PLAN.md, slice 2).
  function aot_ch(fl_, x_, i_) result(r)
    integer(int64), value :: fl_
    type(gc_value), value :: x_
    integer(int64), value :: i_
    type(gc_value) :: r
    if ((fl_ == 3_int64)) then
      r = ast_alt(x_, i_)
      return
    else
      if ((fl_ == 5_int64)) then
        r = aot_bod(x_, i_)
        return
      else
        r = ast_kid(x_, i_)
        return
      end if
    end if
  end function aot_ch

  pure function aot_cop(k_) result(r)
    integer(int64), value :: k_
    logical :: r
    select case (k_)
    case (1_int64)
      r = (k_ == 1_int64)
      return
    case (2_int64)
      r = (k_ == 2_int64)
      return
    case (3_int64)
      r = (k_ == 3_int64)
      return
    case (4_int64)
      r = (k_ == 4_int64)
      return
    case (5_int64)
      r = (k_ == 5_int64)
      return
    case (6_int64)
      r = (k_ == 6_int64)
      return
    case (11_int64)
      r = (k_ == 11_int64)
      return
    case (12_int64)
      r = (k_ == 12_int64)
      return
    case (14_int64)
      r = (k_ == 14_int64)
      return
    case (15_int64)
      r = (k_ == 15_int64)
      return
    case (16_int64)
      r = (k_ == 16_int64)
      return
    case (21_int64)
      r = (k_ == 21_int64)
      return
    case default
      r = (k_ == 22_int64)
      return
    end select
  end function aot_cop

  recursive function aot_fr(fl_, x_, j_, m_) result(r)
    integer(int64), value :: fl_
    type(gc_value), value :: x_
    integer(int64), value :: j_
    integer(int64), value :: m_
    logical :: r
    integer(int64) :: fl_18
    integer(int64) :: j_20
    integer(int64) :: k_1
    integer(int64) :: m_21
    logical :: t_10
    logical :: t_11
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_15
    logical :: t_16
    logical :: t_17
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    type(gc_value) :: x_19
    do
      if ((fl_ == 0_int64)) then
        k_1 = ast_kind(x_)
        if ((k_1 == 16_int64)) then
          t_14 = .true.
        else
          if ((k_1 == 0_int64)) then
            t_5 = (k_1 == 0_int64)
          else
            if ((k_1 == 12_int64)) then
              t_4 = (k_1 == 12_int64)
            else
              if ((k_1 == 14_int64)) then
                t_3 = (k_1 == 14_int64)
              else
                if ((k_1 == 15_int64)) then
                  t_2 = (k_1 == 15_int64)
                else
                  t_2 = (k_1 == 20_int64)
                end if
                t_3 = t_2
              end if
              t_4 = t_3
            end if
            t_5 = t_4
          end if
          if (t_5) then
            t_13 = .false.
          else
            if ((k_1 == 18_int64)) then
              if (aot_fr(0_int64, ast_kid(x_, 0_int64), 0_int64, 0_int64)) then
                t_7 = .true.
              else
                if (aot_fr(3_int64, x_, 0_int64, ast_nalts(x_))) then
                  t_6 = .true.
                else
                  t_6 = aot_fr(0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64)
                end if
                t_7 = t_6
              end if
              t_12 = t_7
            else
              if ((k_1 == 19_int64)) then
                if (aot_fr(3_int64, x_, 0_int64, ast_nalts(x_))) then
                  t_8 = .true.
                else
                  t_8 = aot_fr(1_int64, x_, 0_int64, ast_nkids(x_))
                end if
                t_11 = t_8
              else
                if ((k_1 == 10_int64)) then
                  if (aot_fr(0_int64, ast_s3(x_), 0_int64, 0_int64)) then
                    t_9 = .true.
                  else
                    t_9 = aot_fr(1_int64, x_, 0_int64, ast_nkids(x_))
                  end if
                  t_10 = t_9
                else
                  t_10 = aot_fr(1_int64, x_, 0_int64, ast_nkids(x_))
                end if
                t_11 = t_10
              end if
              t_12 = t_11
            end if
            t_13 = t_12
          end if
          t_14 = t_13
        end if
        r = t_14
        return
      else
        if ((.not. (ast_kind(x_) == 0_int64))) then
          if ((j_ >= 0_int64)) then
            if (.true.) then
              t_15 = (j_ < m_)
            else
              t_15 = .false.
            end if
            t_16 = t_15
          else
            t_16 = .false.
          end if
          t_17 = t_16
        else
          t_17 = .false.
        end if
        if (t_17) then
          if (aot_fr(0_int64, aot_ch(fl_, x_, j_), 0_int64, 0_int64)) then
            r = .true.
            return
          else
            fl_18 = fl_
            x_19 = x_
            j_20 = (1_int64 + j_)
            m_21 = m_
            fl_ = fl_18
            x_ = x_19
            j_ = j_20
            m_ = m_21
            cycle
          end if
        else
          r = .false.
          return
        end if
      end if
    end do
  end function aot_fr

  recursive function aot_sc(fl_, x_, j_, m_) result(r)
    integer(int64), value :: fl_
    type(gc_value), value :: x_
    integer(int64), value :: j_
    integer(int64), value :: m_
    logical :: r
    integer(int64) :: fl_15
    integer(int64) :: j_17
    integer(int64) :: k_1
    integer(int64) :: m_18
    logical :: t_10
    logical :: t_11
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    type(gc_value) :: x_16
    do
      if ((fl_ == 0_int64)) then
        k_1 = ast_kind(x_)
        if ((k_1 == 0_int64)) then
          t_11 = .false.
        else
          if ((.not. aot_cop(k_1))) then
            t_2 = aot_fr(0_int64, x_, 0_int64, 0_int64)
          else
            t_2 = .false.
          end if
          if (t_2) then
            t_10 = .true.
          else
            if (aot_sc(1_int64, x_, 0_int64, ast_nkids(x_))) then
              t_9 = .true.
            else
              if ((k_1 == 10_int64)) then
                t_8 = aot_sc(0_int64, ast_s3(x_), 0_int64, 0_int64)
              else
                if ((k_1 == 18_int64)) then
                  t_4 = (k_1 == 18_int64)
                else
                  if ((k_1 == 19_int64)) then
                    t_3 = (k_1 == 19_int64)
                  else
                    t_3 = (k_1 == 20_int64)
                  end if
                  t_4 = t_3
                end if
                if (t_4) then
                  t_7 = aot_sc(3_int64, x_, 0_int64, ast_nalts(x_))
                else
                  if ((k_1 == 14_int64)) then
                    t_5 = (k_1 == 14_int64)
                  else
                    t_5 = (k_1 == 15_int64)
                  end if
                  if (t_5) then
                    t_6 = aot_sc(5_int64, x_, 0_int64, aot_nbods(x_))
                  else
                    t_6 = .false.
                  end if
                  t_7 = t_6
                end if
                t_8 = t_7
              end if
              t_9 = t_8
            end if
            t_10 = t_9
          end if
          t_11 = t_10
        end if
        r = t_11
        return
      else
        if ((.not. (ast_kind(x_) == 0_int64))) then
          if ((j_ >= 0_int64)) then
            if (.true.) then
              t_12 = (j_ < m_)
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
          if (aot_sc(0_int64, aot_ch(fl_, x_, j_), 0_int64, 0_int64)) then
            r = .true.
            return
          else
            fl_15 = fl_
            x_16 = x_
            j_17 = (1_int64 + j_)
            m_18 = m_
            fl_ = fl_15
            x_ = x_16
            j_ = j_17
            m_ = m_18
            cycle
          end if
        else
          r = .false.
          return
        end if
      end if
    end do
  end function aot_sc

  pure function aot_code(v_) result(r)
    integer(int64), value :: v_
    integer(int64) :: r
    logical :: t_1
    if ((v_ >= 0_int64)) then
      t_1 = (.not. (6_int64 < v_))
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = v_
      return
    else
      r = 1_int64
      return
    end if
  end function aot_code

  pure function aot_jn(a_, b_) result(r)
    integer(int64), value :: a_
    integer(int64), value :: b_
    integer(int64) :: r
    if ((a_ == 0_int64)) then
      r = b_
      return
    else
      if ((b_ == 0_int64)) then
        r = a_
        return
      else
        if ((a_ == b_)) then
          r = a_
          return
        else
          r = 1_int64
          return
        end if
      end if
    end if
  end function aot_jn

  pure function aot_and(a_, b_) result(r)
    integer(int64), value :: a_
    integer(int64), value :: b_
    integer(int64) :: r
    logical :: t_1
    if ((a_ == 1_int64)) then
      t_1 = (b_ == 1_int64)
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = 1_int64
      return
    else
      r = 0_int64
      return
    end if
  end function aot_and

  pure function aot_num(a_) result(r)
    integer(int64), value :: a_
    logical :: r
    if ((a_ == 2_int64)) then
      r = (a_ == 2_int64)
      return
    else
      r = (a_ == 3_int64)
      return
    end if
  end function aot_num

  pure function aot_arr(a_) result(r)
    integer(int64), value :: a_
    logical :: r
    if ((a_ == 5_int64)) then
      r = (a_ == 5_int64)
      return
    else
      r = (a_ == 6_int64)
      return
    end if
  end function aot_arr

  pure function aot_optab(k_, n_, t0_, t1_, t2_) result(r)
    integer(int64), value :: k_
    integer(int64), value :: n_
    integer(int64), value :: t0_
    integer(int64), value :: t1_
    integer(int64), value :: t2_
    integer(int64) :: r
    logical :: t_1
    logical :: t_10
    logical :: t_11
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_15
    logical :: t_16
    logical :: t_17
    logical :: t_18
    logical :: t_19
    logical :: t_2
    logical :: t_20
    logical :: t_21
    logical :: t_22
    logical :: t_23
    logical :: t_24
    logical :: t_25
    logical :: t_26
    logical :: t_27
    logical :: t_28
    logical :: t_29
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    select case (k_)
    case (1_int64)
      if ((n_ == 2_int64)) then
        if (aot_num(t0_)) then
          t_1 = aot_num(t1_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        if ((t0_ == 2_int64)) then
          t_3 = (t1_ == 2_int64)
        else
          t_3 = .false.
        end if
        if (t_3) then
          r = 2_int64
          return
        else
          r = 3_int64
          return
        end if
      else
        r = 1_int64
        return
      end if
    case (2_int64)
      if ((n_ == 2_int64)) then
        if (aot_num(t0_)) then
          if (aot_num(t1_)) then
            if ((t0_ == 3_int64)) then
              t_4 = (t0_ == 3_int64)
            else
              t_4 = (t1_ == 3_int64)
            end if
            t_5 = t_4
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
        r = 3_int64
        return
      else
        r = 1_int64
        return
      end if
    case (3_int64)
      if ((n_ == 1_int64)) then
        t_8 = aot_num(t0_)
      else
        t_8 = .false.
      end if
      if (t_8) then
        r = t0_
        return
      else
        r = 1_int64
        return
      end if
    case (4_int64)
      if ((n_ == 2_int64)) then
        if (aot_num(t0_)) then
          t_9 = aot_num(t0_)
        else
          t_9 = aot_num(t1_)
        end if
        if (t_9) then
          if (aot_num(t0_)) then
            t_10 = aot_num(t0_)
          else
            t_10 = (t0_ == 1_int64)
          end if
          if (t_10) then
            if (aot_num(t1_)) then
              t_11 = aot_num(t1_)
            else
              t_11 = (t1_ == 1_int64)
            end if
            t_12 = t_11
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
        r = 4_int64
        return
      else
        r = 1_int64
        return
      end if
    case (5_int64)
      if ((n_ == 2_int64)) then
        if (aot_num(t0_)) then
          t_15 = (t0_ == t1_)
        else
          t_15 = .false.
        end if
        t_16 = t_15
      else
        t_16 = .false.
      end if
      if (t_16) then
        r = 4_int64
        return
      else
        r = 1_int64
        return
      end if
    case (6_int64)
      if ((n_ == 1_int64)) then
        t_17 = aot_num(t0_)
      else
        t_17 = .false.
      end if
      if (t_17) then
        r = 4_int64
        return
      else
        r = 1_int64
        return
      end if
    case (7_int64)
      if ((n_ == 2_int64)) then
        if (aot_arr(t0_)) then
          t_18 = (t1_ == 2_int64)
        else
          t_18 = .false.
        end if
        t_19 = t_18
      else
        t_19 = .false.
      end if
      if (t_19) then
        if ((t0_ == 5_int64)) then
          r = 3_int64
          return
        else
          r = 2_int64
          return
        end if
      else
        r = 1_int64
        return
      end if
    case (8_int64)
      if ((n_ == 3_int64)) then
        if (aot_arr(t0_)) then
          if ((t1_ == 2_int64)) then
            if ((t0_ == 5_int64)) then
              t_20 = aot_num(t2_)
            else
              t_20 = (t2_ == 2_int64)
            end if
            t_21 = t_20
          else
            t_21 = .false.
          end if
          t_22 = t_21
        else
          t_22 = .false.
        end if
        t_23 = t_22
      else
        t_23 = .false.
      end if
      if (t_23) then
        if ((t0_ == 5_int64)) then
          r = 3_int64
          return
        else
          r = 2_int64
          return
        end if
      else
        r = 1_int64
        return
      end if
    case (9_int64)
      if ((n_ == 1_int64)) then
        t_24 = aot_arr(t0_)
      else
        t_24 = .false.
      end if
      if (t_24) then
        r = 2_int64
        return
      else
        r = 1_int64
        return
      end if
    case (10_int64)
      if ((n_ == 1_int64)) then
        t_25 = aot_num(t0_)
      else
        t_25 = .false.
      end if
      if (t_25) then
        r = 2_int64
        return
      else
        r = 1_int64
        return
      end if
    case (11_int64)
      if ((n_ == 1_int64)) then
        t_26 = aot_num(t0_)
      else
        t_26 = .false.
      end if
      if (t_26) then
        r = 3_int64
        return
      else
        r = 1_int64
        return
      end if
    case (12_int64)
      if ((n_ == 1_int64)) then
        t_27 = aot_num(t0_)
      else
        t_27 = .false.
      end if
      if (t_27) then
        r = 3_int64
        return
      else
        r = 1_int64
        return
      end if
    case (13_int64)
      if ((n_ == 2_int64)) then
        if (aot_num(t0_)) then
          t_28 = aot_num(t1_)
        else
          t_28 = .false.
        end if
        t_29 = t_28
      else
        t_29 = .false.
      end if
      if (t_29) then
        r = 3_int64
        return
      else
        r = 1_int64
        return
      end if
    case default
      r = 1_int64
      return
    end select
  end function aot_optab

  pure function aot_get(as, s_) result(r)
    type(aot_state), intent(in) :: as
    integer(int64), value :: s_
    integer(int64) :: r
    logical :: t_1
    if ((s_ >= 0_int64)) then
      t_1 = (s_ < size(as%tv, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = aot_code(as%tv(s_))
      return
    else
      r = 1_int64
      return
    end if
  end function aot_get

  pure function aot_raw(as, s_) result(r)
    type(aot_state), intent(in) :: as
    integer(int64), value :: s_
    integer(int64) :: r
    logical :: t_1
    if ((s_ >= 0_int64)) then
      t_1 = (s_ < size(as%tv, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = as%tv(s_)
      return
    else
      r = 1_int64
      return
    end if
  end function aot_raw

  subroutine aot_put(as, s_, v_)
    type(aot_state), intent(inout) :: as
    integer(int64), value :: s_
    integer(int64), value :: v_
    integer(int64) :: i_2
    logical :: t_1
    integer(int64) :: v_3
    if ((s_ >= 0_int64)) then
      t_1 = (s_ < size(as%tv, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      i_2 = s_
      v_3 = v_
      as%tv(i_2) = v_3
    else
    end if
  end subroutine aot_put

  pure function aot_rget(as, s_) result(r)
    type(aot_state), intent(in) :: as
    integer(int64), value :: s_
    integer(int64) :: r
    logical :: t_1
    if ((s_ >= 0_int64)) then
      t_1 = (s_ < size(as%rc, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = aot_code(as%rc(s_))
      return
    else
      r = 0_int64
      return
    end if
  end function aot_rget

  subroutine aot_rjn(as, s_, v_)
    type(aot_state), intent(inout) :: as
    integer(int64), value :: s_
    integer(int64), value :: v_
    integer(int64) :: i_2
    logical :: t_1
    integer(int64) :: v_3
    if ((s_ >= 0_int64)) then
      t_1 = (s_ < size(as%rc, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      i_2 = s_
      v_3 = aot_jn(aot_rget(as, s_), aot_code(v_))
      as%rc(i_2) = v_3
    else
    end if
  end subroutine aot_rjn

  subroutine aot_rz(as, s_)
    type(aot_state), intent(inout) :: as
    integer(int64), value :: s_
    integer(int64) :: i_2
    logical :: t_1
    integer(int64) :: v_3
    if ((s_ >= 0_int64)) then
      t_1 = (s_ < size(as%rc, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      i_2 = s_
      v_3 = 0_int64
      as%rc(i_2) = v_3
    else
    end if
  end subroutine aot_rz

  subroutine aot_lput(as, s_, v_)
    type(aot_state), intent(inout) :: as
    integer(int64), value :: s_
    integer(int64), value :: v_
    integer(int64) :: i_2
    logical :: t_1
    integer(int64) :: v_3
    if ((s_ >= 0_int64)) then
      t_1 = (s_ < size(as%lo, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      i_2 = s_
      v_3 = v_
      as%lo(i_2) = v_3
    else
    end if
  end subroutine aot_lput

  subroutine aot_tick(as)
    type(aot_state), intent(inout) :: as
    integer(int64) :: n_1
    logical :: t_2
    n_1 = as%ns
    if ((n_1 >= 0_int64)) then
      t_2 = (n_1 < 1099511627776_int64)
    else
      t_2 = .false.
    end if
    if (t_2) then
      as%ns = (1_int64 + n_1)
    else
    end if
  end subroutine aot_tick

  subroutine aot_rzero(as, b_, i_, m_)
    type(aot_state), intent(inout) :: as
    integer(int64), value :: b_
    integer(int64), value :: i_
    integer(int64), value :: m_
    integer(int64) :: b_3
    integer(int64) :: i_4
    integer(int64) :: m_5
    logical :: t_1
    logical :: t_2
    do
      if ((i_ >= 0_int64)) then
        if ((m_ >= 0_int64)) then
          t_1 = (i_ < m_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        call aot_rz(as, (b_ + i_))
        b_3 = b_
        i_4 = (1_int64 + i_)
        m_5 = m_
        b_ = b_3
        i_ = i_4
        m_ = m_5
        cycle
      else
      end if
      exit
    end do
  end subroutine aot_rzero

  pure function aot_settled(as, b_, i_, m_) result(r)
    type(aot_state), intent(in) :: as
    integer(int64), value :: b_
    integer(int64), value :: i_
    integer(int64), value :: m_
    logical :: r
    integer(int64) :: b_3
    integer(int64) :: i_4
    integer(int64) :: m_5
    logical :: t_1
    logical :: t_2
    do
      if ((i_ >= 0_int64)) then
        if ((m_ >= 0_int64)) then
          t_1 = (i_ < m_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        if ((aot_jn(aot_get(as, (b_ + i_)), aot_rget(as, (b_ + i_))) == aot_get(as, (b_ + i_)))) then
          b_3 = b_
          i_4 = (1_int64 + i_)
          m_5 = m_
          b_ = b_3
          i_ = i_4
          m_ = m_5
          cycle
        else
          r = .false.
          return
        end if
      else
        r = .true.
        return
      end if
    end do
  end function aot_settled

  subroutine aot_lcopy(as, b_, i_, m_)
    type(aot_state), intent(inout) :: as
    integer(int64), value :: b_
    integer(int64), value :: i_
    integer(int64), value :: m_
    integer(int64) :: b_3
    integer(int64) :: i_4
    integer(int64) :: m_5
    logical :: t_1
    logical :: t_2
    do
      if ((i_ >= 0_int64)) then
        if ((m_ >= 0_int64)) then
          t_1 = (i_ < m_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        call aot_lput(as, (b_ + i_), aot_get(as, (b_ + i_)))
        b_3 = b_
        i_4 = (1_int64 + i_)
        m_5 = m_
        b_ = b_3
        i_ = i_4
        m_ = m_5
        cycle
      else
      end if
      exit
    end do
  end subroutine aot_lcopy

  recursive subroutine aot_ty(as, fl_, e_, j_, m_, k_, r1, r2)
    type(aot_state), intent(inout) :: as
    integer(int64), value :: fl_
    type(gc_value), value :: e_
    integer(int64), value :: j_
    integer(int64), value :: m_
    integer(int64), value :: k_
    integer(int64), intent(out) :: r1
    integer(int64), intent(out) :: r2
    type(gc_value) :: a_150
    integer(int64) :: b_105
    integer(int64) :: b_91
    logical :: cast_158
    integer(int64) :: cb_33
    integer(int64) :: cn_34
    logical :: d_169
    logical :: dj_98
    type(gc_value) :: e_111
    type(gc_value) :: e_116
    type(gc_value) :: e_127
    type(gc_value) :: e_23
    type(gc_value) :: e_28
    type(gc_value) :: e_6
    type(gc_value) :: e_87
    integer(int64) :: fl_110
    integer(int64) :: fl_115
    integer(int64) :: fl_126
    integer(int64) :: fl_22
    integer(int64) :: fl_27
    integer(int64) :: fl_5
    integer(int64) :: fl_86
    logical :: fresh_74
    integer(int64) :: h_151
    logical :: hit_35
    integer(int64) :: j_112
    integer(int64) :: j_117
    integer(int64) :: j_128
    integer(int64) :: j_24
    integer(int64) :: j_29
    integer(int64) :: j_7
    integer(int64) :: j_88
    integer(int64) :: k_114
    integer(int64) :: k_119
    integer(int64) :: k_130
    integer(int64) :: k_26
    integer(int64) :: k_31
    integer(int64) :: k_9
    integer(int64) :: k_90
    integer(int64) :: kd_4
    integer(int64) :: m_113
    integer(int64) :: m_118
    integer(int64) :: m_129
    integer(int64) :: m_25
    integer(int64) :: m_30
    integer(int64) :: m_8
    integer(int64) :: m_89
    integer(int64) :: mm_40
    integer(int64) :: mv_10
    integer(int64) :: mv_100
    integer(int64) :: mv_106
    integer(int64) :: mv_107
    integer(int64) :: mv_11
    integer(int64) :: mv_122
    integer(int64) :: mv_123
    integer(int64) :: mv_133
    integer(int64) :: mv_134
    integer(int64) :: mv_137
    integer(int64) :: mv_138
    integer(int64) :: mv_14
    integer(int64) :: mv_141
    integer(int64) :: mv_142
    integer(int64) :: mv_146
    integer(int64) :: mv_147
    integer(int64) :: mv_15
    integer(int64) :: mv_159
    integer(int64) :: mv_160
    integer(int64) :: mv_163
    integer(int64) :: mv_164
    integer(int64) :: mv_172
    integer(int64) :: mv_173
    integer(int64) :: mv_18
    integer(int64) :: mv_19
    integer(int64) :: mv_41
    integer(int64) :: mv_42
    integer(int64) :: mv_53
    integer(int64) :: mv_54
    integer(int64) :: mv_57
    integer(int64) :: mv_58
    integer(int64) :: mv_63
    integer(int64) :: mv_64
    integer(int64) :: mv_67
    integer(int64) :: mv_68
    integer(int64) :: mv_75
    integer(int64) :: mv_76
    integer(int64) :: mv_79
    integer(int64) :: mv_80
    integer(int64) :: mv_99
    integer(int64) :: nk_32
    integer(int64) :: o0_109
    integer(int64) :: o0_13
    integer(int64) :: o0_140
    integer(int64) :: o0_144
    integer(int64) :: o0_162
    integer(int64) :: o0_44
    integer(int64) :: o0_66
    integer(int64) :: o0_78
    integer(int64) :: o1_102
    integer(int64) :: o1_125
    integer(int64) :: o1_136
    integer(int64) :: o1_149
    integer(int64) :: o1_17
    integer(int64) :: o1_175
    integer(int64) :: o1_70
    integer(int64) :: o1_82
    integer(int64) :: o2_21
    integer(int64) :: ocb_92
    integer(int64) :: ocn_93
    integer(int64) :: oh_56
    integer(int64) :: oi_167
    integer(int64) :: old_121
    integer(int64) :: old_132
    integer(int64) :: old_73
    integer(int64) :: ow_60
    integer(int64) :: s0_49
    integer(int64) :: s1_50
    integer(int64) :: s2_51
    integer(int64) :: s_120
    integer(int64) :: s_131
    integer(int64) :: s_72
    integer(int64) :: sd_52
    integer(int64) :: t0_108
    integer(int64) :: t0_12
    integer(int64) :: t0_139
    integer(int64) :: t0_143
    integer(int64) :: t0_161
    integer(int64) :: t0_43
    integer(int64) :: t0_65
    integer(int64) :: t0_77
    integer(int64) :: t1_101
    integer(int64) :: t1_124
    integer(int64) :: t1_135
    integer(int64) :: t1_148
    integer(int64) :: t1_16
    integer(int64) :: t1_174
    integer(int64) :: t1_69
    integer(int64) :: t1_81
    integer(int64) :: t2_20
    logical :: t_1
    logical :: t_103
    integer(int64) :: t_104
    logical :: t_145
    logical :: t_152
    logical :: t_153
    logical :: t_154
    logical :: t_155
    logical :: t_156
    logical :: t_157
    integer(int64) :: t_165
    logical :: t_168
    integer(int64) :: t_170
    integer(int64) :: t_171
    logical :: t_2
    logical :: t_3
    logical :: t_36
    logical :: t_37
    logical :: t_38
    integer(int64) :: t_39
    logical :: t_45
    logical :: t_46
    logical :: t_47
    integer(int64) :: t_48
    integer(int64) :: t_61
    logical :: t_71
    logical :: t_83
    logical :: t_84
    integer(int64) :: t_85
    logical :: t_94
    logical :: t_95
    logical :: t_96
    logical :: t_97
    integer(int64) :: tc_62
    integer(int64) :: th_55
    integer(int64) :: ti_166
    integer(int64) :: tw_59
    do
      call aot_tick(as)
      if ((ast_kind(e_) == 0_int64)) then
        t_3 = (ast_kind(e_) == 0_int64)
      else
        if ((.not. (j_ >= 0_int64))) then
          t_2 = (.not. (j_ >= 0_int64))
        else
          if ((.not. (m_ >= 0_int64))) then
            t_1 = (.not. (m_ >= 0_int64))
          else
            t_1 = (.not. (k_ >= 0_int64))
          end if
          t_2 = t_1
        end if
        t_3 = t_2
      end if
      if (t_3) then
        r1 = 1_int64
        r2 = 1_int64
      else
        if ((fl_ == 0_int64)) then
          kd_4 = ast_kind(e_)
          select case (kd_4)
          case (1_int64)
            r1 = aot_cty(e_)
            r2 = 1_int64
          case (2_int64)
            r1 = aot_get(as, aot_i2(e_))
            r2 = 1_int64
          case (5_int64)
            if ((ast_nkids(e_) == 0_int64)) then
              r1 = 1_int64
              r2 = 1_int64
            else
              fl_5 = 1_int64
              e_6 = e_
              j_7 = 0_int64
              m_8 = ast_nkids(e_)
              k_9 = 0_int64
              fl_ = fl_5
              e_ = e_6
              j_ = j_7
              m_ = m_8
              k_ = k_9
              cycle
            end if
          case (4_int64)
            call aot_ty(as, 0_int64, ast_kid(e_, 0_int64), 0_int64, 0_int64, 0_int64, mv_10, mv_11)
            t0_12 = mv_10
            o0_13 = mv_11
            call aot_ty(as, 0_int64, ast_kid(e_, 1_int64), 0_int64, 0_int64, 0_int64, mv_14, mv_15)
            t1_16 = mv_14
            o1_17 = mv_15
            call aot_ty(as, 0_int64, ast_kid(e_, 2_int64), 0_int64, 0_int64, 0_int64, mv_18, mv_19)
            t2_20 = mv_18
            o2_21 = mv_19
            r1 = aot_jn(t1_16, t2_20)
            r2 = aot_and(o0_13, aot_and(o1_17, o2_21))
          case (11_int64)
            fl_22 = 2_int64
            e_23 = e_
            j_24 = 0_int64
            m_25 = aot_i2(e_)
            k_26 = 0_int64
            fl_ = fl_22
            e_ = e_23
            j_ = j_24
            m_ = m_25
            k_ = k_26
            cycle
          case (12_int64)
            fl_27 = 6_int64
            e_28 = e_
            j_29 = 0_int64
            m_30 = aot_i2(e_)
            k_31 = 0_int64
            fl_ = fl_27
            e_ = e_28
            j_ = j_29
            m_ = m_30
            k_ = k_31
            cycle
          case (16_int64)
            nk_32 = ast_nkids(e_)
            cb_33 = as%cb
            cn_34 = as%cn
            hit_35 = (aot_rs(e_) == cb_33)
            if (hit_35) then
              if ((cn_34 >= 0_int64)) then
                t_36 = (cn_34 < 1099511627776_int64)
              else
                t_36 = .false.
              end if
              if (t_36) then
                t_37 = (nk_32 < cn_34)
              else
                t_37 = .false.
              end if
              t_38 = t_37
            else
              t_38 = .false.
            end if
            if (t_38) then
              t_39 = cn_34
            else
              t_39 = nk_32
            end if
            mm_40 = t_39
            call aot_ty(as, 3_int64, e_, 0_int64, mm_40, 0_int64, mv_41, mv_42)
            t0_43 = mv_41
            o0_44 = mv_42
            r1 = 0_int64
            if ((o0_44 == 1_int64)) then
              if (hit_35) then
                if ((nk_32 == cn_34)) then
                  t_45 = (aot_rn(e_) == cn_34)
                else
                  t_45 = .false.
                end if
                t_46 = t_45
              else
                t_46 = .false.
              end if
              t_47 = t_46
            else
              t_47 = .false.
            end if
            if (t_47) then
              t_48 = 1_int64
            else
              t_48 = 0_int64
            end if
            r2 = t_48
          case (6_int64)
            s0_49 = as%a0
            s1_50 = as%a1
            s2_51 = as%a2
            sd_52 = as%ad
            as%a0 = 1_int64
            as%a1 = 1_int64
            as%a2 = 1_int64
            as%ad = 0_int64
            call aot_ty(as, 0_int64, ast_kid(e_, 0_int64), 0_int64, 0_int64, 0_int64, mv_53, mv_54)
            th_55 = mv_53
            oh_56 = mv_54
            call aot_ty(as, 4_int64, e_, 1_int64, ast_nkids(e_), 0_int64, mv_57, mv_58)
            tw_59 = mv_57
            ow_60 = mv_58
            if ((0_int64 < ast_nkids(e_))) then
              t_61 = ((-1_int64) + ast_nkids(e_))
            else
              t_61 = 0_int64
            end if
            tc_62 = aot_optab(aot_hop(e_), t_61, as%a0, as%a1, as%a2)
            as%a0 = s0_49
            as%a1 = s1_50
            as%a2 = s2_51
            as%ad = sd_52
            r1 = tc_62
            r2 = aot_and(oh_56, ow_60)
          case default
            r1 = 1_int64
            r2 = 1_int64
          end select
        else
          if ((fl_ == 1_int64)) then
            if ((j_ < m_)) then
              call aot_ty(as, 0_int64, ast_kid(e_, j_), 0_int64, 0_int64, 0_int64, mv_63, mv_64)
              t0_65 = mv_63
              o0_66 = mv_64
              if (((1_int64 + j_) < m_)) then
                call aot_ty(as, 1_int64, e_, (1_int64 + j_), m_, 0_int64, mv_67, mv_68)
                t1_69 = mv_67
                o1_70 = mv_68
                r1 = t1_69
                r2 = aot_and(o0_66, o1_70)
              else
                r1 = t0_65
                r2 = o0_66
              end if
            else
              r1 = 1_int64
              r2 = 1_int64
            end if
          else
            if ((fl_ == 2_int64)) then
              t_71 = (fl_ == 2_int64)
            else
              t_71 = (fl_ == 6_int64)
            end if
            if (t_71) then
              if ((j_ < m_)) then
                s_72 = (aot_s2(e_) + j_)
                old_73 = aot_raw(as, s_72)
                fresh_74 = (aot_get(as, s_72) == 1_int64)
                call aot_ty(as, 0_int64, ast_kid(e_, j_), 0_int64, 0_int64, 0_int64, mv_75, mv_76)
                t0_77 = mv_75
                o0_78 = mv_76
                call aot_put(as, s_72, t0_77)
                call aot_ty(as, fl_, e_, (1_int64 + j_), m_, 0_int64, mv_79, mv_80)
                t1_81 = mv_79
                o1_82 = mv_80
                call aot_put(as, s_72, old_73)
                r1 = t1_81
                if (fresh_74) then
                  if ((o0_78 == 1_int64)) then
                    t_83 = (o1_82 == 1_int64)
                  else
                    t_83 = .false.
                  end if
                  t_84 = t_83
                else
                  t_84 = .false.
                end if
                if (t_84) then
                  t_85 = 1_int64
                else
                  t_85 = 0_int64
                end if
                r2 = t_85
              else
                if ((fl_ == 2_int64)) then
                  fl_86 = 0_int64
                  e_87 = ast_kid(e_, m_)
                  j_88 = 0_int64
                  m_89 = 0_int64
                  k_90 = 0_int64
                  fl_ = fl_86
                  e_ = e_87
                  j_ = j_88
                  m_ = m_89
                  k_ = k_90
                  cycle
                else
                  b_91 = aot_s2(e_)
                  ocb_92 = as%cb
                  ocn_93 = as%cn
                  if ((ocb_92 >= 0_int64)) then
                    t_94 = (ocb_92 < 1099511627776_int64)
                  else
                    t_94 = .false.
                  end if
                  if (t_94) then
                    if ((ocn_93 >= 0_int64)) then
                      t_95 = (ocn_93 < 1099511627776_int64)
                    else
                      t_95 = .false.
                    end if
                    if (t_95) then
                      t_96 = (.not. (b_91 < (ocb_92 + ocn_93)))
                    else
                      t_96 = .false.
                    end if
                    t_97 = t_96
                  else
                    t_97 = .false.
                  end if
                  dj_98 = t_97
                  call aot_rzero(as, b_91, 0_int64, m_)
                  as%cb = b_91
                  as%cn = m_
                  call aot_ty(as, 5_int64, e_, 0_int64, m_, 0_int64, mv_99, mv_100)
                  t1_101 = mv_99
                  o1_102 = mv_100
                  as%cb = ocb_92
                  as%cn = ocn_93
                  r1 = t1_101
                  if (dj_98) then
                    t_103 = (o1_102 == 1_int64)
                  else
                    t_103 = .false.
                  end if
                  if (t_103) then
                    t_104 = 1_int64
                  else
                    t_104 = 0_int64
                  end if
                  r2 = t_104
                end if
              end if
            else
              select case (fl_)
              case (5_int64)
                b_105 = aot_s2(e_)
                call aot_ty(as, 0_int64, ast_kid(e_, m_), 0_int64, 0_int64, 0_int64, mv_106, mv_107)
                t0_108 = mv_106
                o0_109 = mv_107
                if (aot_settled(as, b_105, 0_int64, m_)) then
                  call aot_lcopy(as, b_105, 0_int64, m_)
                  r1 = t0_108
                  r2 = o0_109
                else
                  if ((4_int64 < k_)) then
                    fl_110 = 8_int64
                    e_111 = e_
                    j_112 = 0_int64
                    m_113 = m_
                    k_114 = k_
                    fl_ = fl_110
                    e_ = e_111
                    j_ = j_112
                    m_ = m_113
                    k_ = k_114
                    cycle
                  else
                    fl_115 = 7_int64
                    e_116 = e_
                    j_117 = 0_int64
                    m_118 = m_
                    k_119 = k_
                    fl_ = fl_115
                    e_ = e_116
                    j_ = j_117
                    m_ = m_118
                    k_ = k_119
                    cycle
                  end if
                end if
              case (7_int64)
                if ((j_ < m_)) then
                  s_120 = (aot_s2(e_) + j_)
                  old_121 = aot_raw(as, s_120)
                  call aot_put(as, s_120, aot_jn(aot_get(as, s_120), aot_rget(as, s_120)))
                  call aot_ty(as, 7_int64, e_, (1_int64 + j_), m_, k_, mv_122, mv_123)
                  t1_124 = mv_122
                  o1_125 = mv_123
                  call aot_put(as, s_120, old_121)
                  r1 = t1_124
                  r2 = o1_125
                else
                  if ((k_ < 5_int64)) then
                    fl_126 = 5_int64
                    e_127 = e_
                    j_128 = 0_int64
                    m_129 = m_
                    k_130 = (1_int64 + k_)
                    fl_ = fl_126
                    e_ = e_127
                    j_ = j_128
                    m_ = m_129
                    k_ = k_130
                    cycle
                  else
                    r1 = 1_int64
                    r2 = 1_int64
                  end if
                end if
              case (8_int64)
                if ((j_ < m_)) then
                  s_131 = (aot_s2(e_) + j_)
                  old_132 = aot_raw(as, s_131)
                  call aot_put(as, s_131, 1_int64)
                  call aot_ty(as, 8_int64, e_, (1_int64 + j_), m_, k_, mv_133, mv_134)
                  t1_135 = mv_133
                  o1_136 = mv_134
                  call aot_put(as, s_131, old_132)
                  r1 = t1_135
                  r2 = o1_136
                else
                  call aot_ty(as, 0_int64, ast_kid(e_, m_), 0_int64, 0_int64, 0_int64, mv_137, mv_138)
                  t0_139 = mv_137
                  o0_140 = mv_138
                  call aot_lcopy(as, aot_s2(e_), 0_int64, m_)
                  r1 = t0_139
                  r2 = o0_140
                end if
              case (3_int64)
                if ((j_ < m_)) then
                  call aot_ty(as, 0_int64, ast_kid(e_, j_), 0_int64, 0_int64, 0_int64, mv_141, mv_142)
                  t0_143 = mv_141
                  o0_144 = mv_142
                  if ((aot_rs(e_) == as%cb)) then
                    t_145 = (j_ < as%cn)
                  else
                    t_145 = .false.
                  end if
                  if (t_145) then
                    call aot_rjn(as, (aot_rs(e_) + j_), t0_143)
                  else
                  end if
                  call aot_ty(as, 3_int64, e_, (1_int64 + j_), m_, 0_int64, mv_146, mv_147)
                  t1_148 = mv_146
                  o1_149 = mv_147
                  r1 = 0_int64
                  r2 = aot_and(o0_144, o1_149)
                else
                  r1 = 0_int64
                  r2 = 1_int64
                end if
              case (4_int64)
                if ((j_ < m_)) then
                  a_150 = ast_kid(e_, j_)
                  h_151 = aot_hop(e_)
                  if ((j_ == 1_int64)) then
                    if ((h_151 == 7_int64)) then
                      t_153 = (h_151 == 7_int64)
                    else
                      if ((h_151 == 8_int64)) then
                        t_152 = (h_151 == 8_int64)
                      else
                        t_152 = (h_151 == 9_int64)
                      end if
                      t_153 = t_152
                    end if
                    if (t_153) then
                      if ((ast_kind(a_150) == 6_int64)) then
                        if ((aot_hop(a_150) == 20_int64)) then
                          t_154 = (.not. (aot_kw(ast_kid(a_150, 2_int64)) == 0_int64))
                        else
                          t_154 = .false.
                        end if
                        t_155 = t_154
                      else
                        t_155 = .false.
                      end if
                      t_156 = t_155
                    else
                      t_156 = .false.
                    end if
                    t_157 = t_156
                  else
                    t_157 = .false.
                  end if
                  cast_158 = t_157
                  call aot_ty(as, 0_int64, a_150, 0_int64, 0_int64, 0_int64, mv_159, mv_160)
                  t0_161 = mv_159
                  o0_162 = mv_160
                  if (cast_158) then
                    t_165 = 1_int64
                  else
                    t_165 = (-1_int64)
                  end if
                  call aot_ty(as, 0_int64, ast_kid(a_150, t_165), 0_int64, 0_int64, 0_int64, mv_163, mv_164)
                  ti_166 = mv_163
                  oi_167 = mv_164
                  if (cast_158) then
                    t_168 = (ti_166 == aot_kw(ast_kid(a_150, 2_int64)))
                  else
                    t_168 = .false.
                  end if
                  d_169 = t_168
                  select case (j_)
                  case (1_int64)
                    if (d_169) then
                      t_170 = ti_166
                    else
                      t_170 = t0_161
                    end if
                    as%a0 = t_170
                    if (d_169) then
                      t_171 = 1_int64
                    else
                      t_171 = 0_int64
                    end if
                    as%ad = t_171
                  case (2_int64)
                    as%a1 = t0_161
                  case (3_int64)
                    as%a2 = t0_161
                  case default
                  end select
                  call aot_ty(as, 4_int64, e_, (1_int64 + j_), m_, 0_int64, mv_172, mv_173)
                  t1_174 = mv_172
                  o1_175 = mv_173
                  r1 = 0_int64
                  r2 = aot_and(o0_162, aot_and(oi_167, o1_175))
                else
                  r1 = 0_int64
                  r2 = 1_int64
                end if
              case default
                r1 = 1_int64
                r2 = 1_int64
              end select
            end if
          end if
        end if
      end if
      exit
    end do
  end subroutine aot_ty
