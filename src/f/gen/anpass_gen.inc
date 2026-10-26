  ! GENERATED from model/anpass.lisp by scripts/acl2-fortran -b anpass. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the analyzer's passes over its tree -- the tail check
  ! (anp_tc), has_fn_recur (anp_hfr), reads_in (anp_rd), liveness (anp_live)
  ! and apply_clears (anp_clears) -- guard-verified, reading the tree through
  ! analyze.inc's ast_* shims. The anpass books prove anp_live computes the live
  ! sets and marks of its meaning (anp-live-spec, anpass-proof.lisp), that no
  ! read marked for clearing is followed by another of its slot in any run
  ! (tr-sound, anp-clears-sound: anpass-sound.lisp), and that a body the
  ! tail check passes recurs only as the last thing it does (tr-tail).
  function anp_nn(x_) result(r)
    type(gc_value), value :: x_
    integer(int64) :: r
    integer(int64) :: m_2
    integer(int64) :: nn_1
    integer(int64) :: t_3
    nn_1 = ast_i2(x_)
    m_2 = ast_nkids(x_)
    if ((nn_1 < m_2)) then
      t_3 = nn_1
    else
      t_3 = m_2
    end if
    r = t_3
    return
  end function anp_nn

  function anp_ch(fl_, x_, i_) result(r)
    integer(int64), value :: fl_
    type(gc_value), value :: x_
    integer(int64), value :: i_
    type(gc_value) :: r
    if ((fl_ == 3_int64)) then
      r = ast_alt(x_, i_)
      return
    else
      r = ast_kid(x_, i_)
      return
    end if
  end function anp_ch

  recursive function anp_tc(fl_, x_, j_, m_, tt_) result(r)
    integer(int64), value :: fl_
    type(gc_value), value :: x_
    integer(int64), value :: j_
    integer(int64), value :: m_
    integer(int64), value :: tt_
    integer(int64) :: r
    integer(int64) :: a_14
    integer(int64) :: a_19
    integer(int64) :: a_22
    integer(int64) :: a_27
    integer(int64) :: a_31
    integer(int64) :: a_50
    integer(int64) :: a_8
    integer(int64) :: b_23
    integer(int64) :: b_28
    integer(int64) :: b_9
    integer(int64) :: k_1
    integer(int64) :: m2_13
    integer(int64) :: nn_18
    integer(int64) :: t_10
    integer(int64) :: t_11
    logical :: t_12
    integer(int64) :: t_15
    integer(int64) :: t_16
    logical :: t_17
    logical :: t_2
    integer(int64) :: t_20
    integer(int64) :: t_21
    integer(int64) :: t_24
    integer(int64) :: t_25
    integer(int64) :: t_26
    integer(int64) :: t_29
    logical :: t_3
    integer(int64) :: t_30
    integer(int64) :: t_32
    logical :: t_33
    logical :: t_34
    logical :: t_35
    logical :: t_36
    logical :: t_37
    integer(int64) :: t_38
    integer(int64) :: t_39
    integer(int64) :: t_4
    integer(int64) :: t_40
    integer(int64) :: t_41
    integer(int64) :: t_42
    integer(int64) :: t_43
    integer(int64) :: t_44
    integer(int64) :: t_45
    integer(int64) :: t_46
    logical :: t_47
    logical :: t_48
    logical :: t_49
    integer(int64) :: t_5
    integer(int64) :: t_51
    integer(int64) :: t_6
    integer(int64) :: t_7
    if ((fl_ == 0_int64)) then
      k_1 = ast_kind(x_)
      if ((k_1 == 16_int64)) then
        if ((tt_ == 0_int64)) then
          t_7 = 1_int64
        else
          if ((tt_ == 3_int64)) then
            t_6 = 2_int64
          else
            if ((tt_ == 1_int64)) then
              t_2 = (ast_rfn(x_) == 0_int64)
            else
              t_2 = .false.
            end if
            if (t_2) then
              t_5 = 1_int64
            else
              if ((tt_ == 2_int64)) then
                t_3 = (.not. (ast_rfn(x_) == 0_int64))
              else
                t_3 = .false.
              end if
              if (t_3) then
                t_4 = 1_int64
              else
                t_4 = anp_tc(1_int64, x_, 0_int64, ast_nkids(x_), 0_int64)
              end if
              t_5 = t_4
            end if
            t_6 = t_5
          end if
          t_7 = t_6
        end if
        t_46 = t_7
      else
        if ((k_1 == 4_int64)) then
          a_8 = anp_tc(0_int64, ast_kid(x_, 0_int64), 0_int64, 0_int64, 0_int64)
          if ((a_8 == 0_int64)) then
            b_9 = anp_tc(0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64, tt_)
            if ((b_9 == 0_int64)) then
              t_10 = anp_tc(0_int64, ast_kid(x_, 2_int64), 0_int64, 0_int64, tt_)
            else
              t_10 = b_9
            end if
            t_11 = t_10
          else
            t_11 = a_8
          end if
          t_45 = t_11
        else
          if ((k_1 == 5_int64)) then
            t_12 = (k_1 == 5_int64)
          else
            t_12 = (k_1 == 11_int64)
          end if
          if (t_12) then
            m2_13 = ast_nkids(x_)
            if ((m2_13 == 0_int64)) then
              t_16 = 0_int64
            else
              a_14 = anp_tc(1_int64, x_, 0_int64, ((-1_int64) + m2_13), 0_int64)
              if ((a_14 == 0_int64)) then
                t_15 = anp_tc(0_int64, ast_kid(x_, ((-1_int64) + m2_13)), 0_int64, 0_int64, tt_)
              else
                t_15 = a_14
              end if
              t_16 = t_15
            end if
            t_44 = t_16
          else
            if ((k_1 == 13_int64)) then
              t_17 = (k_1 == 13_int64)
            else
              t_17 = (k_1 == 12_int64)
            end if
            if (t_17) then
              nn_18 = anp_nn(x_)
              a_19 = anp_tc(1_int64, x_, 0_int64, nn_18, 0_int64)
              if ((a_19 == 0_int64)) then
                if ((k_1 == 12_int64)) then
                  t_20 = 2_int64
                else
                  t_20 = tt_
                end if
                t_21 = anp_tc(0_int64, ast_kid(x_, nn_18), 0_int64, 0_int64, t_20)
              else
                t_21 = a_19
              end if
              t_43 = t_21
            else
              if ((k_1 == 19_int64)) then
                a_22 = anp_tc(0_int64, ast_kid(x_, 0_int64), 0_int64, 0_int64, 0_int64)
                if ((a_22 == 0_int64)) then
                  b_23 = anp_tc(0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64, tt_)
                  if ((b_23 == 0_int64)) then
                    t_24 = anp_tc(3_int64, x_, 0_int64, ast_nalts(x_), tt_)
                  else
                    t_24 = b_23
                  end if
                  t_25 = t_24
                else
                  t_25 = a_22
                end if
                t_42 = t_25
              else
                if ((k_1 == 18_int64)) then
                  if ((tt_ == 0_int64)) then
                    t_26 = 0_int64
                  else
                    t_26 = 3_int64
                  end if
                  a_27 = anp_tc(0_int64, ast_kid(x_, 0_int64), 0_int64, 0_int64, t_26)
                  if ((a_27 == 0_int64)) then
                    b_28 = anp_tc(3_int64, x_, 0_int64, ast_nalts(x_), 0_int64)
                    if ((b_28 == 0_int64)) then
                      t_29 = anp_tc(0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64, 0_int64)
                    else
                      t_29 = b_28
                    end if
                    t_30 = t_29
                  else
                    t_30 = a_27
                  end if
                  t_41 = t_30
                else
                  if ((k_1 == 10_int64)) then
                    a_31 = anp_tc(1_int64, x_, 0_int64, ast_nkids(x_), 0_int64)
                    if ((a_31 == 0_int64)) then
                      t_32 = anp_tc(0_int64, ast_s3(x_), 0_int64, 0_int64, 0_int64)
                    else
                      t_32 = a_31
                    end if
                    t_40 = t_32
                  else
                    if ((k_1 == 20_int64)) then
                      t_39 = anp_tc(3_int64, x_, 0_int64, ast_nalts(x_), 0_int64)
                    else
                      if ((k_1 == 0_int64)) then
                        t_37 = (k_1 == 0_int64)
                      else
                        if ((k_1 == 2_int64)) then
                          t_36 = (k_1 == 2_int64)
                        else
                          if ((k_1 == 1_int64)) then
                            t_35 = (k_1 == 1_int64)
                          else
                            if ((k_1 == 3_int64)) then
                              t_34 = (k_1 == 3_int64)
                            else
                              if ((k_1 == 14_int64)) then
                                t_33 = (k_1 == 14_int64)
                              else
                                t_33 = (k_1 == 15_int64)
                              end if
                              t_34 = t_33
                            end if
                            t_35 = t_34
                          end if
                          t_36 = t_35
                        end if
                        t_37 = t_36
                      end if
                      if (t_37) then
                        t_38 = 0_int64
                      else
                        t_38 = anp_tc(1_int64, x_, 0_int64, ast_nkids(x_), 0_int64)
                      end if
                      t_39 = t_38
                    end if
                    t_40 = t_39
                  end if
                  t_41 = t_40
                end if
                t_42 = t_41
              end if
              t_43 = t_42
            end if
            t_44 = t_43
          end if
          t_45 = t_44
        end if
        t_46 = t_45
      end if
      r = t_46
      return
    else
      if ((.not. (ast_kind(x_) == 0_int64))) then
        if ((j_ >= 0_int64)) then
          if (.true.) then
            t_47 = (j_ < m_)
          else
            t_47 = .false.
          end if
          t_48 = t_47
        else
          t_48 = .false.
        end if
        t_49 = t_48
      else
        t_49 = .false.
      end if
      if (t_49) then
        a_50 = anp_tc(0_int64, anp_ch(fl_, x_, j_), 0_int64, 0_int64, tt_)
        if ((a_50 == 0_int64)) then
          t_51 = anp_tc(fl_, x_, (1_int64 + j_), m_, tt_)
        else
          t_51 = a_50
        end if
        r = t_51
        return
      else
        r = 0_int64
        return
      end if
    end if
  end function anp_tc

  recursive function anp_hfr(fl_, x_, j_, m_) result(r)
    integer(int64), value :: fl_
    type(gc_value), value :: x_
    integer(int64), value :: j_
    integer(int64), value :: m_
    logical :: r
    integer(int64) :: fl_21
    integer(int64) :: j_23
    integer(int64) :: k_1
    integer(int64) :: m_24
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
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    type(gc_value) :: x_22
    do
      if ((fl_ == 0_int64)) then
        k_1 = ast_kind(x_)
        if ((k_1 == 16_int64)) then
          if ((ast_rfn(x_) == 0_int64)) then
            t_2 = anp_hfr(1_int64, x_, 0_int64, ast_nkids(x_))
          else
            t_2 = .true.
          end if
          t_17 = t_2
        else
          if ((k_1 == 18_int64)) then
            if (anp_hfr(0_int64, ast_kid(x_, 0_int64), 0_int64, 0_int64)) then
              t_4 = .true.
            else
              if (anp_hfr(3_int64, x_, 0_int64, ast_nalts(x_))) then
                t_3 = .true.
              else
                t_3 = anp_hfr(0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64)
              end if
              t_4 = t_3
            end if
            t_16 = t_4
          else
            if ((k_1 == 19_int64)) then
              if (anp_hfr(3_int64, x_, 0_int64, ast_nalts(x_))) then
                t_5 = .true.
              else
                t_5 = anp_hfr(1_int64, x_, 0_int64, ast_nkids(x_))
              end if
              t_15 = t_5
            else
              if ((k_1 == 10_int64)) then
                if (anp_hfr(0_int64, ast_s3(x_), 0_int64, 0_int64)) then
                  t_6 = .true.
                else
                  t_6 = anp_hfr(1_int64, x_, 0_int64, ast_nkids(x_))
                end if
                t_14 = t_6
              else
                if ((k_1 == 20_int64)) then
                  t_13 = anp_hfr(3_int64, x_, 0_int64, ast_nalts(x_))
                else
                  if ((k_1 == 0_int64)) then
                    t_11 = (k_1 == 0_int64)
                  else
                    if ((k_1 == 2_int64)) then
                      t_10 = (k_1 == 2_int64)
                    else
                      if ((k_1 == 1_int64)) then
                        t_9 = (k_1 == 1_int64)
                      else
                        if ((k_1 == 3_int64)) then
                          t_8 = (k_1 == 3_int64)
                        else
                          if ((k_1 == 14_int64)) then
                            t_7 = (k_1 == 14_int64)
                          else
                            t_7 = (k_1 == 15_int64)
                          end if
                          t_8 = t_7
                        end if
                        t_9 = t_8
                      end if
                      t_10 = t_9
                    end if
                    t_11 = t_10
                  end if
                  if (t_11) then
                    t_12 = .false.
                  else
                    t_12 = anp_hfr(1_int64, x_, 0_int64, ast_nkids(x_))
                  end if
                  t_13 = t_12
                end if
                t_14 = t_13
              end if
              t_15 = t_14
            end if
            t_16 = t_15
          end if
          t_17 = t_16
        end if
        r = t_17
        return
      else
        if ((.not. (ast_kind(x_) == 0_int64))) then
          if ((j_ >= 0_int64)) then
            if (.true.) then
              t_18 = (j_ < m_)
            else
              t_18 = .false.
            end if
            t_19 = t_18
          else
            t_19 = .false.
          end if
          t_20 = t_19
        else
          t_20 = .false.
        end if
        if (t_20) then
          if (anp_hfr(0_int64, anp_ch(fl_, x_, j_), 0_int64, 0_int64)) then
            r = .true.
            return
          else
            fl_21 = fl_
            x_22 = x_
            j_23 = (1_int64 + j_)
            m_24 = m_
            fl_ = fl_21
            x_ = x_22
            j_ = j_23
            m_ = m_24
            cycle
          end if
        else
          r = .false.
          return
        end if
      end if
    end do
  end function anp_hfr

  pure function anp_get(ps, i_) result(r)
    type(anp_state), intent(in) :: ps
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ps%lv, kind=int64))
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = ps%lv(i_)
      return
    else
      r = 0_int64
      return
    end if
  end function anp_get

  subroutine anp_put(ps, i_, v_)
    type(anp_state), intent(inout) :: ps
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ps%lv, kind=int64))
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      i_3 = i_
      v_4 = v_
      ps%lv(i_3) = v_4
    else
      ps%err = 1_int64
    end if
  end subroutine anp_put

  subroutine anp_copy(ps, k_, n_, from_, to_)
    type(anp_state), intent(inout) :: ps
    integer(int64), value :: k_
    integer(int64), value :: n_
    integer(int64), value :: from_
    integer(int64), value :: to_
    integer(int64) :: from_5
    integer(int64) :: k_3
    integer(int64) :: n_4
    logical :: t_1
    logical :: t_2
    integer(int64) :: to_6
    do
      if ((k_ >= 0_int64)) then
        if ((n_ >= 0_int64)) then
          t_1 = (k_ < n_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        call anp_put(ps, (to_ + k_), anp_get(ps, (from_ + k_)))
        k_3 = (1_int64 + k_)
        n_4 = n_
        from_5 = from_
        to_6 = to_
        k_ = k_3
        n_ = n_4
        from_ = from_5
        to_ = to_6
        cycle
      else
      end if
      exit
    end do
  end subroutine anp_copy

  subroutine anp_or(ps, k_, n_, from_, to_)
    type(anp_state), intent(inout) :: ps
    integer(int64), value :: k_
    integer(int64), value :: n_
    integer(int64), value :: from_
    integer(int64), value :: to_
    integer(int64) :: from_6
    integer(int64) :: k_4
    integer(int64) :: n_5
    logical :: t_1
    logical :: t_2
    integer(int64) :: t_3
    integer(int64) :: to_7
    do
      if ((k_ >= 0_int64)) then
        if ((n_ >= 0_int64)) then
          t_1 = (k_ < n_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        if ((anp_get(ps, (from_ + k_)) == 0_int64)) then
          t_3 = anp_get(ps, (to_ + k_))
        else
          t_3 = 1_int64
        end if
        call anp_put(ps, (to_ + k_), t_3)
        k_4 = (1_int64 + k_)
        n_5 = n_
        from_6 = from_
        to_7 = to_
        k_ = k_4
        n_ = n_5
        from_ = from_6
        to_ = to_7
        cycle
      else
      end if
      exit
    end do
  end subroutine anp_or

  subroutine anp_zero(ps, k_, n_)
    type(anp_state), intent(inout) :: ps
    integer(int64), value :: k_
    integer(int64), value :: n_
    integer(int64) :: k_3
    integer(int64) :: n_4
    logical :: t_1
    logical :: t_2
    do
      if ((k_ >= 0_int64)) then
        if ((n_ >= 0_int64)) then
          t_1 = (k_ < n_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        call anp_put(ps, k_, 0_int64)
        k_3 = (1_int64 + k_)
        n_4 = n_
        k_ = k_3
        n_ = n_4
        cycle
      else
      end if
      exit
    end do
  end subroutine anp_zero

  subroutine anp_set(ps, s_, b_, n_)
    type(anp_state), intent(inout) :: ps
    integer(int64), value :: s_
    integer(int64), value :: b_
    integer(int64), value :: n_
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (s_ < 0_int64))) then
        t_1 = (s_ < n_)
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      call anp_put(ps, (b_ + s_), 1_int64)
    else
    end if
  end subroutine anp_set

  subroutine anp_mark(ps, x_)
    type(anp_state), intent(inout) :: ps
    type(gc_value), value :: x_
    integer(int64) :: i_5
    integer(int64) :: k_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    type(gc_value) :: v_6
    k_1 = ps%nmk
    if (.true.) then
      if ((.not. (k_1 < 0_int64))) then
        if ((k_1 < size(ps%mk, kind=int64))) then
          t_2 = (k_1 < 1099511627776_int64)
        else
          t_2 = .false.
        end if
        t_3 = t_2
      else
        t_3 = .false.
      end if
      t_4 = t_3
    else
      t_4 = .false.
    end if
    if (t_4) then
      i_5 = k_1
      v_6 = x_
      ps%mk(i_5) = v_6
      ps%nmk = (1_int64 + k_1)
    else
      ps%err = 1_int64
    end if
  end subroutine anp_mark

  subroutine anp_local(ps, x_, b_, n_)
    type(anp_state), intent(inout) :: ps
    type(gc_value), value :: x_
    integer(int64), value :: b_
    integer(int64), value :: n_
    integer(int64) :: s_1
    logical :: t_2
    logical :: t_3
    s_1 = ast_i2(x_)
    if (.true.) then
      if ((.not. (s_1 < 0_int64))) then
        t_2 = (s_1 < n_)
      else
        t_2 = .false.
      end if
      t_3 = t_2
    else
      t_3 = .false.
    end if
    if (t_3) then
      if ((anp_get(ps, (b_ + s_1)) == 0_int64)) then
        call anp_mark(ps, x_)
      else
      end if
      call anp_put(ps, (b_ + s_1), 1_int64)
    else
    end if
  end subroutine anp_local

  subroutine anp_caps(ps, x_, i_, k_, b_, n_)
    type(anp_state), intent(inout) :: ps
    type(gc_value), value :: x_
    integer(int64), value :: i_
    integer(int64), value :: k_
    integer(int64), value :: b_
    integer(int64), value :: n_
    integer(int64) :: b_6
    integer(int64) :: i_4
    integer(int64) :: k_5
    integer(int64) :: n_7
    logical :: t_1
    logical :: t_2
    type(gc_value) :: x_3
    do
      if ((i_ >= 0_int64)) then
        if ((k_ >= 0_int64)) then
          t_1 = (i_ < k_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        call anp_set(ps, ast_cap(x_, i_), b_, n_)
        x_3 = x_
        i_4 = (1_int64 + i_)
        k_5 = k_
        b_6 = b_
        n_7 = n_
        x_ = x_3
        i_ = i_4
        k_ = k_5
        b_ = b_6
        n_ = n_7
        cycle
      else
      end if
      exit
    end do
  end subroutine anp_caps

  subroutine anp_fncaps(ps, x_, i_, k_, b_, n_)
    type(anp_state), intent(inout) :: ps
    type(gc_value), value :: x_
    integer(int64), value :: i_
    integer(int64), value :: k_
    integer(int64), value :: b_
    integer(int64), value :: n_
    integer(int64) :: b_7
    type(gc_value) :: c_3
    integer(int64) :: i_5
    integer(int64) :: k_6
    integer(int64) :: n_8
    logical :: t_1
    logical :: t_2
    type(gc_value) :: x_4
    do
      if ((i_ >= 0_int64)) then
        if (.true.) then
          t_1 = (i_ < k_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        c_3 = ast_kid(x_, i_)
        call anp_caps(ps, c_3, 0_int64, ast_ncaps(c_3), b_, n_)
        x_4 = x_
        i_5 = (1_int64 + i_)
        k_6 = k_
        b_7 = b_
        n_8 = n_
        x_ = x_4
        i_ = i_5
        k_ = k_6
        b_ = b_7
        n_ = n_8
        cycle
      else
      end if
      exit
    end do
  end subroutine anp_fncaps

  recursive subroutine anp_rd(ps, fl_, x_, j_, m_, b_, n_)
    type(anp_state), intent(inout) :: ps
    integer(int64), value :: fl_
    type(gc_value), value :: x_
    integer(int64), value :: j_
    integer(int64), value :: m_
    integer(int64), value :: b_
    integer(int64), value :: n_
    integer(int64) :: b_13
    integer(int64) :: b_19
    integer(int64) :: b_25
    integer(int64) :: b_31
    integer(int64) :: b_40
    integer(int64) :: b_7
    integer(int64) :: fl_15
    integer(int64) :: fl_21
    integer(int64) :: fl_27
    integer(int64) :: fl_3
    integer(int64) :: fl_36
    integer(int64) :: fl_9
    integer(int64) :: j_11
    integer(int64) :: j_17
    integer(int64) :: j_23
    integer(int64) :: j_29
    integer(int64) :: j_38
    integer(int64) :: j_5
    integer(int64) :: k_1
    integer(int64) :: m_12
    integer(int64) :: m_18
    integer(int64) :: m_24
    integer(int64) :: m_30
    integer(int64) :: m_39
    integer(int64) :: m_6
    integer(int64) :: n_14
    integer(int64) :: n_20
    integer(int64) :: n_26
    integer(int64) :: n_32
    integer(int64) :: n_41
    integer(int64) :: n_8
    logical :: t_2
    logical :: t_33
    logical :: t_34
    logical :: t_35
    type(gc_value) :: x_10
    type(gc_value) :: x_16
    type(gc_value) :: x_22
    type(gc_value) :: x_28
    type(gc_value) :: x_37
    type(gc_value) :: x_4
    do
      if ((fl_ == 0_int64)) then
        k_1 = ast_kind(x_)
        if ((k_1 == 0_int64)) then
        else
          if ((k_1 == 2_int64)) then
            call anp_set(ps, ast_i2(x_), b_, n_)
          else
            if ((k_1 == 14_int64)) then
              t_2 = (k_1 == 14_int64)
            else
              t_2 = (k_1 == 15_int64)
            end if
            if (t_2) then
              call anp_caps(ps, x_, 0_int64, ast_ncaps(x_), b_, n_)
            else
              select case (k_1)
              case (20_int64)
                fl_3 = 3_int64
                x_4 = x_
                j_5 = 0_int64
                m_6 = ast_nalts(x_)
                b_7 = b_
                n_8 = n_
                fl_ = fl_3
                x_ = x_4
                j_ = j_5
                m_ = m_6
                b_ = b_7
                n_ = n_8
                cycle
              case (18_int64)
                call anp_rd(ps, 0_int64, ast_kid(x_, 0_int64), 0_int64, 0_int64, b_, n_)
                call anp_rd(ps, 3_int64, x_, 0_int64, ast_nalts(x_), b_, n_)
                fl_9 = 0_int64
                x_10 = ast_kid(x_, 1_int64)
                j_11 = 0_int64
                m_12 = 0_int64
                b_13 = b_
                n_14 = n_
                fl_ = fl_9
                x_ = x_10
                j_ = j_11
                m_ = m_12
                b_ = b_13
                n_ = n_14
                cycle
              case (19_int64)
                call anp_rd(ps, 0_int64, ast_kid(x_, 0_int64), 0_int64, 0_int64, b_, n_)
                call anp_rd(ps, 0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64, b_, n_)
                fl_15 = 3_int64
                x_16 = x_
                j_17 = 0_int64
                m_18 = ast_nalts(x_)
                b_19 = b_
                n_20 = n_
                fl_ = fl_15
                x_ = x_16
                j_ = j_17
                m_ = m_18
                b_ = b_19
                n_ = n_20
                cycle
              case (10_int64)
                call anp_rd(ps, 0_int64, ast_s3(x_), 0_int64, 0_int64, b_, n_)
                fl_21 = 1_int64
                x_22 = x_
                j_23 = 0_int64
                m_24 = ast_nkids(x_)
                b_25 = b_
                n_26 = n_
                fl_ = fl_21
                x_ = x_22
                j_ = j_23
                m_ = m_24
                b_ = b_25
                n_ = n_26
                cycle
              case default
                fl_27 = 1_int64
                x_28 = x_
                j_29 = 0_int64
                m_30 = ast_nkids(x_)
                b_31 = b_
                n_32 = n_
                fl_ = fl_27
                x_ = x_28
                j_ = j_29
                m_ = m_30
                b_ = b_31
                n_ = n_32
                cycle
              end select
            end if
          end if
        end if
      else
        if ((.not. (ast_kind(x_) == 0_int64))) then
          if ((j_ >= 0_int64)) then
            if (.true.) then
              t_33 = (j_ < m_)
            else
              t_33 = .false.
            end if
            t_34 = t_33
          else
            t_34 = .false.
          end if
          t_35 = t_34
        else
          t_35 = .false.
        end if
        if (t_35) then
          call anp_rd(ps, 0_int64, anp_ch(fl_, x_, j_), 0_int64, 0_int64, b_, n_)
          fl_36 = fl_
          x_37 = x_
          j_38 = (1_int64 + j_)
          m_39 = m_
          b_40 = b_
          n_41 = n_
          fl_ = fl_36
          x_ = x_37
          j_ = j_38
          m_ = m_39
          b_ = b_40
          n_ = n_41
          cycle
        else
        end if
      end if
      exit
    end do
  end subroutine anp_rd

  recursive subroutine anp_live(ps, fl_, x_, j_, m_, b_, top_, n_)
    type(anp_state), intent(inout) :: ps
    integer(int64), value :: fl_
    type(gc_value), value :: x_
    integer(int64), value :: j_
    integer(int64), value :: m_
    integer(int64), value :: b_
    integer(int64), value :: top_
    integer(int64), value :: n_
    integer(int64) :: b_16
    integer(int64) :: b_23
    integer(int64) :: b_30
    integer(int64) :: b_39
    integer(int64) :: b_47
    integer(int64) :: b_54
    integer(int64) :: b_61
    integer(int64) :: b_7
    integer(int64) :: b_71
    integer(int64) :: b_81
    type(gc_value) :: bd_34
    integer(int64) :: fl_12
    integer(int64) :: fl_19
    integer(int64) :: fl_26
    integer(int64) :: fl_3
    integer(int64) :: fl_35
    integer(int64) :: fl_43
    integer(int64) :: fl_50
    integer(int64) :: fl_57
    integer(int64) :: fl_67
    integer(int64) :: fl_77
    integer(int64) :: j_14
    integer(int64) :: j_21
    integer(int64) :: j_28
    integer(int64) :: j_37
    integer(int64) :: j_45
    integer(int64) :: j_5
    integer(int64) :: j_52
    integer(int64) :: j_59
    integer(int64) :: j_69
    integer(int64) :: j_79
    integer(int64) :: k_1
    integer(int64) :: m_15
    integer(int64) :: m_22
    integer(int64) :: m_29
    integer(int64) :: m_38
    integer(int64) :: m_46
    integer(int64) :: m_53
    integer(int64) :: m_6
    integer(int64) :: m_60
    integer(int64) :: m_70
    integer(int64) :: m_80
    integer(int64) :: n_18
    integer(int64) :: n_25
    integer(int64) :: n_32
    integer(int64) :: n_41
    integer(int64) :: n_49
    integer(int64) :: n_56
    integer(int64) :: n_63
    integer(int64) :: n_73
    integer(int64) :: n_83
    integer(int64) :: n_9
    integer(int64) :: nn_33
    integer(int64) :: nn_42
    logical :: t_10
    logical :: t_11
    logical :: t_2
    logical :: t_64
    logical :: t_65
    logical :: t_66
    logical :: t_74
    logical :: t_75
    logical :: t_76
    integer(int64) :: top_17
    integer(int64) :: top_24
    integer(int64) :: top_31
    integer(int64) :: top_40
    integer(int64) :: top_48
    integer(int64) :: top_55
    integer(int64) :: top_62
    integer(int64) :: top_72
    integer(int64) :: top_8
    integer(int64) :: top_82
    type(gc_value) :: x_13
    type(gc_value) :: x_20
    type(gc_value) :: x_27
    type(gc_value) :: x_36
    type(gc_value) :: x_4
    type(gc_value) :: x_44
    type(gc_value) :: x_51
    type(gc_value) :: x_58
    type(gc_value) :: x_68
    type(gc_value) :: x_78
    do
      if ((.not. (ps%err == 0_int64))) then
      else
        if ((fl_ == 0_int64)) then
          k_1 = ast_kind(x_)
          if ((k_1 == 0_int64)) then
          else
            if ((k_1 == 2_int64)) then
              call anp_local(ps, x_, b_, n_)
            else
              if ((k_1 == 14_int64)) then
                t_2 = (k_1 == 14_int64)
              else
                t_2 = (k_1 == 15_int64)
              end if
              if (t_2) then
                call anp_caps(ps, x_, 0_int64, ast_ncaps(x_), b_, n_)
              else
                if ((k_1 == 20_int64)) then
                  fl_3 = 3_int64
                  x_4 = x_
                  j_5 = 0_int64
                  m_6 = ast_nalts(x_)
                  b_7 = b_
                  top_8 = top_
                  n_9 = n_
                  fl_ = fl_3
                  x_ = x_4
                  j_ = j_5
                  m_ = m_6
                  b_ = b_7
                  top_ = top_8
                  n_ = n_9
                  cycle
                else
                  if ((k_1 == 4_int64)) then
                    t_11 = (k_1 == 4_int64)
                  else
                    if ((k_1 == 19_int64)) then
                      t_10 = (k_1 == 19_int64)
                    else
                      t_10 = (k_1 == 18_int64)
                    end if
                    t_11 = t_10
                  end if
                  if (t_11) then
                    if (((top_ + (3_int64 * n_)) < 1099511627776_int64)) then
                      if ((k_1 == 4_int64)) then
                        call anp_copy(ps, 0_int64, n_, b_, top_)
                        call anp_live(ps, 0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64, top_, (top_ + n_), n_)
                        call anp_live(ps, 0_int64, ast_kid(x_, 2_int64), 0_int64, 0_int64, b_, (top_ + n_), n_)
                        call anp_or(ps, 0_int64, n_, top_, b_)
                        fl_12 = 0_int64
                        x_13 = ast_kid(x_, 0_int64)
                        j_14 = 0_int64
                        m_15 = 0_int64
                        b_16 = b_
                        top_17 = top_
                        n_18 = n_
                        fl_ = fl_12
                        x_ = x_13
                        j_ = j_14
                        m_ = m_15
                        b_ = b_16
                        top_ = top_17
                        n_ = n_18
                        cycle
                      else
                        if ((k_1 == 19_int64)) then
                          call anp_copy(ps, 0_int64, n_, b_, top_)
                          call anp_live(ps, 2_int64, x_, 0_int64, ast_nalts(x_), b_, top_, n_)
                          call anp_live(ps, 0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64, b_, (top_ + n_), n_)
                          call anp_or(ps, 0_int64, n_, top_, b_)
                          fl_19 = 0_int64
                          x_20 = ast_kid(x_, 0_int64)
                          j_21 = 0_int64
                          m_22 = 0_int64
                          b_23 = b_
                          top_24 = top_
                          n_25 = n_
                          fl_ = fl_19
                          x_ = x_20
                          j_ = j_21
                          m_ = m_22
                          b_ = b_23
                          top_ = top_24
                          n_ = n_25
                          cycle
                        else
                          call anp_live(ps, 0_int64, ast_kid(x_, 1_int64), 0_int64, 0_int64, b_, top_, n_)
                          call anp_copy(ps, 0_int64, n_, b_, top_)
                          call anp_live(ps, 2_int64, x_, 0_int64, ast_nalts(x_), b_, top_, n_)
                          call anp_copy(ps, 0_int64, n_, top_, b_)
                          fl_26 = 0_int64
                          x_27 = ast_kid(x_, 0_int64)
                          j_28 = 0_int64
                          m_29 = 0_int64
                          b_30 = b_
                          top_31 = top_
                          n_32 = n_
                          fl_ = fl_26
                          x_ = x_27
                          j_ = j_28
                          m_ = m_29
                          b_ = b_30
                          top_ = top_31
                          n_ = n_32
                          cycle
                        end if
                      end if
                    else
                      ps%err = 1_int64
                    end if
                  else
                    select case (k_1)
                    case (12_int64)
                      nn_33 = anp_nn(x_)
                      bd_34 = ast_kid(x_, nn_33)
                      call anp_rd(ps, 0_int64, bd_34, 0_int64, 0_int64, b_, n_)
                      call anp_live(ps, 0_int64, bd_34, 0_int64, 0_int64, b_, top_, n_)
                      fl_35 = 1_int64
                      x_36 = x_
                      j_37 = 0_int64
                      m_38 = nn_33
                      b_39 = b_
                      top_40 = top_
                      n_41 = n_
                      fl_ = fl_35
                      x_ = x_36
                      j_ = j_37
                      m_ = m_38
                      b_ = b_39
                      top_ = top_40
                      n_ = n_41
                      cycle
                    case (13_int64)
                      nn_42 = anp_nn(x_)
                      call anp_live(ps, 0_int64, ast_kid(x_, nn_42), 0_int64, 0_int64, b_, top_, n_)
                      call anp_fncaps(ps, x_, 0_int64, nn_42, b_, n_)
                      fl_43 = 1_int64
                      x_44 = x_
                      j_45 = 0_int64
                      m_46 = nn_42
                      b_47 = b_
                      top_48 = top_
                      n_49 = n_
                      fl_ = fl_43
                      x_ = x_44
                      j_ = j_45
                      m_ = m_46
                      b_ = b_47
                      top_ = top_48
                      n_ = n_49
                      cycle
                    case (10_int64)
                      call anp_live(ps, 0_int64, ast_s3(x_), 0_int64, 0_int64, b_, top_, n_)
                      fl_50 = 1_int64
                      x_51 = x_
                      j_52 = 0_int64
                      m_53 = ast_nkids(x_)
                      b_54 = b_
                      top_55 = top_
                      n_56 = n_
                      fl_ = fl_50
                      x_ = x_51
                      j_ = j_52
                      m_ = m_53
                      b_ = b_54
                      top_ = top_55
                      n_ = n_56
                      cycle
                    case default
                      fl_57 = 1_int64
                      x_58 = x_
                      j_59 = 0_int64
                      m_60 = ast_nkids(x_)
                      b_61 = b_
                      top_62 = top_
                      n_63 = n_
                      fl_ = fl_57
                      x_ = x_58
                      j_ = j_59
                      m_ = m_60
                      b_ = b_61
                      top_ = top_62
                      n_ = n_63
                      cycle
                    end select
                  end if
                end if
              end if
            end if
          end if
        else
          if ((fl_ == 2_int64)) then
            if ((.not. (ast_kind(x_) == 0_int64))) then
              if ((j_ >= 0_int64)) then
                if (.true.) then
                  t_64 = (j_ < m_)
                else
                  t_64 = .false.
                end if
                t_65 = t_64
              else
                t_65 = .false.
              end if
              t_66 = t_65
            else
              t_66 = .false.
            end if
            if (t_66) then
              if (((top_ + (3_int64 * n_)) < 1099511627776_int64)) then
                call anp_copy(ps, 0_int64, n_, b_, (top_ + n_))
                call anp_live(ps, 0_int64, ast_alt(x_, j_), 0_int64, 0_int64, (top_ + n_), (top_ + (2_int64 * n_)), n_)
                call anp_or(ps, 0_int64, n_, (top_ + n_), top_)
                fl_67 = 2_int64
                x_68 = x_
                j_69 = (1_int64 + j_)
                m_70 = m_
                b_71 = b_
                top_72 = top_
                n_73 = n_
                fl_ = fl_67
                x_ = x_68
                j_ = j_69
                m_ = m_70
                b_ = b_71
                top_ = top_72
                n_ = n_73
                cycle
              else
                ps%err = 1_int64
              end if
            else
            end if
          else
            if ((.not. (ast_kind(x_) == 0_int64))) then
              if ((j_ >= 0_int64)) then
                if (.true.) then
                  t_74 = (j_ < m_)
                else
                  t_74 = .false.
                end if
                t_75 = t_74
              else
                t_75 = .false.
              end if
              t_76 = t_75
            else
              t_76 = .false.
            end if
            if (t_76) then
              call anp_live(ps, 0_int64, anp_ch(fl_, x_, ((-1_int64) + m_)), 0_int64, 0_int64, b_, top_, n_)
              fl_77 = fl_
              x_78 = x_
              j_79 = j_
              m_80 = ((-1_int64) + m_)
              b_81 = b_
              top_82 = top_
              n_83 = n_
              fl_ = fl_77
              x_ = x_78
              j_ = j_79
              m_ = m_80
              b_ = b_81
              top_ = top_82
              n_ = n_83
              cycle
            else
            end if
          end if
        end if
      end if
      exit
    end do
  end subroutine anp_live

  subroutine anp_clears(ps, x_, n_)
    type(anp_state), intent(inout) :: ps
    type(gc_value), value :: x_
    integer(int64), value :: n_
    ps%err = 0_int64
    ps%nmk = 0_int64
    if (anp_hfr(0_int64, x_, 0_int64, 0_int64)) then
    else
      if ((size(ps%lv, kind=int64) < n_)) then
        ps%err = 1_int64
      else
        call anp_zero(ps, 0_int64, n_)
        call anp_live(ps, 0_int64, x_, 0_int64, 0_int64, 0_int64, n_, n_)
      end if
    end if
  end subroutine anp_clears
