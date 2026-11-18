  ! GENERATED from model/aot.lisp by scripts/acl2-fortran -b aot. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the ahead-of-time compiler's eligibility scan (aot_sc: some
  ! node of a kind compiler.cljf does not emit has a recur under it, aot_fr, not
  ! past a loop, fn or lazy seq), guard-verified, reading the tree through
  ! analyze.inc's ast_* shims and Eval.f90's aot_nbods, aot_bod. B_AOTSCAN
  ! (clotran-aot-scan) answers it to decline-reason. aot-proof.lisp proves a node
  ! with no such recur makes none in any run (aot-handed-norec), that a passing
  ! scan leaves none (aot-sc-sound, aot-scan-norec), and counts it (aot-sc-steps-bound).
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
