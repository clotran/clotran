  ! GENERATED from model/exec.lisp by scripts/acl2-fortran -b exec. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the tree evaluator's turn for its core kinds -- a constant, a
  ! local, a Var, if, do, let*, loop*, recur, fn, a call, throw and try -- what
  ! run_loop does with the top record (ex_act), which child it takes (ex_kid),
  ! the record's pc and i after (ex_pc, ex_i), whether k_finish restarts it
  ! (ex_fin), what k_unwind does with the record under a throw (ex_unw), the arity a call's count picks (ex_arfit: the fixed one, else
  ! the variadic one) and how it enters its callee or throws the arity error
  ! (ex_entry), and apply: its way (ex_apentry) and how far its walk takes the
  ! seq (ex_apstep) and how far it reads it (ex_aplook), and each step over a
  ! seq by its kind (sk_step, model/seqk.lisp), B_APPLY the walk -- guard-verified.
  ! exec.inc's exec_core does what they decide. exec-proof.lisp proves the
  ! machine they drive answers each node's meaning, exec-vm.lisp that the
  ! meaning is the VM's; exec-cost.lisp counts the turns.
  pure function ex_act(k_, pc_, i_, nk_, n2_, tv_) result(r)
    integer(int64), value :: k_
    integer(int64), value :: pc_
    integer(int64), value :: i_
    integer(int64), value :: nk_
    integer(int64), value :: n2_
    integer(int64), value :: tv_
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
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    select case (k_)
    case (1_int64)
      r = 1_int64
      return
    case (2_int64)
      r = 2_int64
      return
    case (4_int64)
      if ((pc_ == 0_int64)) then
        r = 3_int64
        return
      else
        if ((tv_ == 1_int64)) then
          r = 4_int64
          return
        else
          if (.true.) then
            t_1 = (2_int64 < nk_)
          else
            t_1 = .false.
          end if
          if (t_1) then
            r = 4_int64
            return
          else
            r = 5_int64
            return
          end if
        end if
      end if
    case (5_int64)
      if (.true.) then
        t_2 = (0_int64 < nk_)
      else
        t_2 = .false.
      end if
      if ((.not. t_2)) then
        r = 5_int64
        return
      else
        if (.true.) then
          t_3 = (i_ < ((-1_int64) + nk_))
        else
          t_3 = .false.
        end if
        if (t_3) then
          r = 3_int64
          return
        else
          r = 4_int64
          return
        end if
      end if
    case default
      if ((k_ == 11_int64)) then
        t_5 = (k_ == 11_int64)
      else
        if ((k_ == 12_int64)) then
          t_4 = (k_ == 12_int64)
        else
          t_4 = (k_ == 13_int64)
        end if
        t_5 = t_4
      end if
      if (t_5) then
        if ((pc_ == 1_int64)) then
          r = 6_int64
          return
        else
          if (.true.) then
            if (.true.) then
              t_6 = (i_ < n2_)
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
            if ((k_ == 12_int64)) then
              r = 7_int64
              return
            else
              if ((k_ == 13_int64)) then
                r = 28_int64
                return
              else
                r = 4_int64
                return
              end if
            end if
          end if
        end if
      else
        select case (k_)
        case (16_int64)
          if ((pc_ == 0_int64)) then
            r = 8_int64
            return
          else
            if ((pc_ == 2_int64)) then
              r = 9_int64
              return
            else
              if (.true.) then
                if (.true.) then
                  t_8 = (i_ < nk_)
                else
                  t_8 = .false.
                end if
                t_9 = t_8
              else
                t_9 = .false.
              end if
              if (t_9) then
                r = 3_int64
                return
              else
                r = 10_int64
                return
              end if
            end if
          end if
        case (3_int64)
          r = 11_int64
          return
        case (14_int64)
          r = 12_int64
          return
        case (17_int64)
          if ((pc_ == 0_int64)) then
            r = 3_int64
            return
          else
            r = 18_int64
            return
          end if
        case (19_int64)
          if ((pc_ == 0_int64)) then
            r = 3_int64
            return
          else
            r = 24_int64
            return
          end if
        case (18_int64)
          if ((pc_ == 0_int64)) then
            r = 3_int64
            return
          else
            if ((pc_ == 1_int64)) then
              t_10 = (pc_ == 1_int64)
            else
              t_10 = (pc_ == 3_int64)
            end if
            if (t_10) then
              if (.true.) then
                t_11 = (1_int64 < nk_)
              else
                t_11 = .false.
              end if
              if (t_11) then
                r = 20_int64
                return
              else
                r = 19_int64
                return
              end if
            else
              if ((pc_ == 2_int64)) then
                r = 21_int64
                return
              else
                if ((pc_ == 4_int64)) then
                  r = 22_int64
                  return
                else
                  r = 0_int64
                  return
                end if
              end if
            end if
          end if
        case (6_int64)
          select case (pc_)
          case (0_int64)
            r = 13_int64
            return
          case (1_int64)
            if ((tv_ == 1_int64)) then
              r = 14_int64
              return
            else
              r = 23_int64
              return
            end if
          case (2_int64)
            if (.true.) then
              if (.true.) then
                t_12 = (i_ < nk_)
              else
                t_12 = .false.
              end if
              t_13 = t_12
            else
              t_13 = .false.
            end if
            if (t_13) then
              r = 3_int64
              return
            else
              r = 15_int64
              return
            end if
          case (3_int64)
            r = 9_int64
            return
          case (4_int64)
            r = 16_int64
            return
          case (5_int64)
            r = 17_int64
            return
          case default
            r = 0_int64
            return
          end select
        case default
          if ((k_ == 7_int64)) then
            t_20 = (k_ == 7_int64)
          else
            if ((k_ == 8_int64)) then
              t_19 = (k_ == 8_int64)
            else
              if ((k_ == 9_int64)) then
                t_18 = (k_ == 9_int64)
              else
                if ((k_ == 22_int64)) then
                  t_17 = (k_ == 22_int64)
                else
                  if ((k_ == 23_int64)) then
                    t_16 = (k_ == 23_int64)
                  else
                    if ((k_ == 10_int64)) then
                      t_15 = (k_ == 10_int64)
                    else
                      if ((k_ == 20_int64)) then
                        t_14 = (k_ == 20_int64)
                      else
                        t_14 = (k_ == 24_int64)
                      end if
                      t_15 = t_14
                    end if
                    t_16 = t_15
                  end if
                  t_17 = t_16
                end if
                t_18 = t_17
              end if
              t_19 = t_18
            end if
            t_20 = t_19
          end if
          if (t_20) then
            if ((pc_ == 0_int64)) then
              r = 25_int64
              return
            else
              if ((pc_ == 3_int64)) then
                r = 26_int64
                return
              else
                if (.true.) then
                  if (.true.) then
                    t_21 = (i_ < nk_)
                  else
                    t_21 = .false.
                  end if
                  t_22 = t_21
                else
                  t_22 = .false.
                end if
                if (t_22) then
                  r = 3_int64
                  return
                else
                  r = 27_int64
                  return
                end if
              end if
            end if
          else
            r = 0_int64
            return
          end if
        end select
      end if
    end select
  end function ex_act

  pure function ex_kid(k_, pc_, i_, nk_, n2_, tv_) result(r)
    integer(int64), value :: k_
    integer(int64), value :: pc_
    integer(int64), value :: i_
    integer(int64), value :: nk_
    integer(int64), value :: n2_
    integer(int64), value :: tv_
    integer(int64) :: r
    logical :: t_1
    logical :: t_10
    logical :: t_11
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    if ((k_ == 4_int64)) then
      if ((pc_ == 0_int64)) then
        r = 0_int64
        return
      else
        if ((tv_ == 1_int64)) then
          r = 1_int64
          return
        else
          r = 2_int64
          return
        end if
      end if
    else
      if ((k_ == 5_int64)) then
        if (.true.) then
          if (.true.) then
            t_1 = (i_ < ((-1_int64) + nk_))
          else
            t_1 = .false.
          end if
          t_2 = t_1
        else
          t_2 = .false.
        end if
        if (t_2) then
          r = i_
          return
        else
          if ((nk_ >= 0_int64)) then
            t_3 = (nk_ < 1099511627776_int64)
          else
            t_3 = .false.
          end if
          if (t_3) then
            t_4 = (0_int64 < nk_)
          else
            t_4 = .false.
          end if
          if (t_4) then
            r = ((-1_int64) + nk_)
            return
          else
            r = 0_int64
            return
          end if
        end if
      else
        if ((k_ == 11_int64)) then
          t_6 = (k_ == 11_int64)
        else
          if ((k_ == 12_int64)) then
            t_5 = (k_ == 12_int64)
          else
            t_5 = (k_ == 13_int64)
          end if
          t_6 = t_5
        end if
        if (t_6) then
          if (.true.) then
            if (.true.) then
              t_7 = (i_ < n2_)
            else
              t_7 = .false.
            end if
            t_8 = t_7
          else
            t_8 = .false.
          end if
          if (t_8) then
            r = i_
            return
          else
            if ((n2_ >= 0_int64)) then
              t_9 = (n2_ < 1099511627776_int64)
            else
              t_9 = .false.
            end if
            if (t_9) then
              r = n2_
              return
            else
              r = 0_int64
              return
            end if
          end if
        else
          if ((k_ == 18_int64)) then
            if ((pc_ == 1_int64)) then
              t_10 = (pc_ == 1_int64)
            else
              t_10 = (pc_ == 3_int64)
            end if
            if (t_10) then
              r = 1_int64
              return
            else
              r = 0_int64
              return
            end if
          else
            if ((i_ >= 0_int64)) then
              t_11 = (i_ < 1099511627776_int64)
            else
              t_11 = .false.
            end if
            if (t_11) then
              r = i_
              return
            else
              r = 0_int64
              return
            end if
          end if
        end if
      end if
    end if
  end function ex_kid

  pure function ex_pc(k_, pc_, i_, nk_, n2_, tv_) result(r)
    integer(int64), value :: k_
    integer(int64), value :: pc_
    integer(int64), value :: i_
    integer(int64), value :: nk_
    integer(int64), value :: n2_
    integer(int64), value :: tv_
    integer(int64) :: r
    logical :: t_1
    logical :: t_10
    logical :: t_11
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_15
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    select case (k_)
    case (4_int64)
      r = 1_int64
      return
    case (17_int64)
      r = 1_int64
      return
    case (19_int64)
      r = 1_int64
      return
    case (18_int64)
      if ((pc_ == 0_int64)) then
        r = 1_int64
        return
      else
        if ((pc_ == 1_int64)) then
          t_1 = (pc_ == 1_int64)
        else
          t_1 = (pc_ == 3_int64)
        end if
        if (t_1) then
          r = 2_int64
          return
        else
          if ((pc_ == 4_int64)) then
            r = 5_int64
            return
          else
            r = pc_
            return
          end if
        end if
      end if
    case default
      if ((k_ == 11_int64)) then
        t_3 = (k_ == 11_int64)
      else
        if ((k_ == 12_int64)) then
          t_2 = (k_ == 12_int64)
        else
          t_2 = (k_ == 13_int64)
        end if
        t_3 = t_2
      end if
      if (t_3) then
        if ((pc_ == 1_int64)) then
          r = 0_int64
          return
        else
          r = 1_int64
          return
        end if
      else
        if ((k_ == 16_int64)) then
          if ((pc_ == 1_int64)) then
            r = 2_int64
            return
          else
            r = 1_int64
            return
          end if
        else
          if ((k_ == 6_int64)) then
            select case (pc_)
            case (0_int64)
              r = 1_int64
              return
            case (1_int64)
              r = 2_int64
              return
            case (2_int64)
              if (.true.) then
                if (.true.) then
                  t_4 = (i_ < nk_)
                else
                  t_4 = .false.
                end if
                t_5 = t_4
              else
                t_5 = .false.
              end if
              if (t_5) then
                r = 3_int64
                return
              else
                r = 4_int64
                return
              end if
            case (3_int64)
              r = 2_int64
              return
            case (4_int64)
              r = 5_int64
              return
            case default
              r = pc_
              return
            end select
          else
            if ((k_ == 7_int64)) then
              t_12 = (k_ == 7_int64)
            else
              if ((k_ == 8_int64)) then
                t_11 = (k_ == 8_int64)
              else
                if ((k_ == 9_int64)) then
                  t_10 = (k_ == 9_int64)
                else
                  if ((k_ == 22_int64)) then
                    t_9 = (k_ == 22_int64)
                  else
                    if ((k_ == 23_int64)) then
                      t_8 = (k_ == 23_int64)
                    else
                      if ((k_ == 10_int64)) then
                        t_7 = (k_ == 10_int64)
                      else
                        if ((k_ == 20_int64)) then
                          t_6 = (k_ == 20_int64)
                        else
                          t_6 = (k_ == 24_int64)
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
              t_12 = t_11
            end if
            if (t_12) then
              if ((pc_ == 0_int64)) then
                t_13 = (pc_ == 0_int64)
              else
                t_13 = (pc_ == 3_int64)
              end if
              if (t_13) then
                r = 2_int64
                return
              else
                if (.true.) then
                  if (.true.) then
                    t_14 = (i_ < nk_)
                  else
                    t_14 = .false.
                  end if
                  t_15 = t_14
                else
                  t_15 = .false.
                end if
                if (t_15) then
                  r = 3_int64
                  return
                else
                  r = pc_
                  return
                end if
              end if
            else
              r = 0_int64
              return
            end if
          end if
        end if
      end if
    end select
  end function ex_pc

  pure function ex_i(k_, pc_, i_, nk_, n2_, tv_) result(r)
    integer(int64), value :: k_
    integer(int64), value :: pc_
    integer(int64), value :: i_
    integer(int64), value :: nk_
    integer(int64), value :: n2_
    integer(int64), value :: tv_
    integer(int64) :: r
    integer(int64) :: i1_3
    logical :: t_1
    integer(int64) :: t_10
    logical :: t_11
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_15
    logical :: t_16
    logical :: t_17
    integer(int64) :: t_18
    integer(int64) :: t_19
    integer(int64) :: t_2
    integer(int64) :: t_20
    integer(int64) :: t_21
    integer(int64) :: t_22
    integer(int64) :: t_23
    integer(int64) :: t_24
    logical :: t_4
    logical :: t_5
    integer(int64) :: t_6
    integer(int64) :: t_7
    integer(int64) :: t_8
    integer(int64) :: t_9
    if ((i_ >= 0_int64)) then
      t_1 = (i_ < 1099511627776_int64)
    else
      t_1 = .false.
    end if
    if (t_1) then
      t_2 = (i_ + 1_int64)
    else
      t_2 = 0_int64
    end if
    i1_3 = t_2
    if ((k_ == 5_int64)) then
      t_24 = i1_3
    else
      if ((k_ == 11_int64)) then
        t_5 = (k_ == 11_int64)
      else
        if ((k_ == 12_int64)) then
          t_4 = (k_ == 12_int64)
        else
          t_4 = (k_ == 13_int64)
        end if
        t_5 = t_4
      end if
      if (t_5) then
        if ((pc_ == 1_int64)) then
          t_6 = i1_3
        else
          t_6 = i_
        end if
        t_23 = t_6
      else
        if ((k_ == 16_int64)) then
          if ((pc_ == 0_int64)) then
            t_8 = 0_int64
          else
            if ((pc_ == 2_int64)) then
              t_7 = i1_3
            else
              t_7 = i_
            end if
            t_8 = t_7
          end if
          t_22 = t_8
        else
          if ((k_ == 6_int64)) then
            if ((pc_ == 1_int64)) then
              t_10 = 1_int64
            else
              if ((pc_ == 3_int64)) then
                t_9 = i1_3
              else
                t_9 = i_
              end if
              t_10 = t_9
            end if
            t_21 = t_10
          else
            if ((k_ == 7_int64)) then
              t_17 = (k_ == 7_int64)
            else
              if ((k_ == 8_int64)) then
                t_16 = (k_ == 8_int64)
              else
                if ((k_ == 9_int64)) then
                  t_15 = (k_ == 9_int64)
                else
                  if ((k_ == 22_int64)) then
                    t_14 = (k_ == 22_int64)
                  else
                    if ((k_ == 23_int64)) then
                      t_13 = (k_ == 23_int64)
                    else
                      if ((k_ == 10_int64)) then
                        t_12 = (k_ == 10_int64)
                      else
                        if ((k_ == 20_int64)) then
                          t_11 = (k_ == 20_int64)
                        else
                          t_11 = (k_ == 24_int64)
                        end if
                        t_12 = t_11
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
            if (t_17) then
              if ((pc_ == 0_int64)) then
                t_19 = 0_int64
              else
                if ((pc_ == 3_int64)) then
                  t_18 = i1_3
                else
                  t_18 = i_
                end if
                t_19 = t_18
              end if
              t_20 = t_19
            else
              t_20 = i_
            end if
            t_21 = t_20
          end if
          t_22 = t_21
        end if
        t_23 = t_22
      end if
      t_24 = t_23
    end if
    r = t_24
    return
  end function ex_i

  pure function ex_fin(rf_, mk_) result(r)
    integer(int64), value :: rf_
    integer(int64), value :: mk_
    integer(int64) :: r
    logical :: t_1
    if ((rf_ == 1_int64)) then
      t_1 = (mk_ == 1_int64)
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
  end function ex_fin

  pure function ex_unw(k_, pc_, mt_, fin_) result(r)
    integer(int64), value :: k_
    integer(int64), value :: pc_
    integer(int64), value :: mt_
    integer(int64), value :: fin_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    if ((k_ == 18_int64)) then
      if ((pc_ == 1_int64)) then
        t_1 = (mt_ == 1_int64)
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = 1_int64
      return
    else
      if ((k_ == 18_int64)) then
        if ((pc_ == 1_int64)) then
          t_3 = (pc_ == 1_int64)
        else
          t_3 = (pc_ == 3_int64)
        end if
        if (t_3) then
          t_4 = (fin_ == 1_int64)
        else
          t_4 = .false.
        end if
        t_5 = t_4
      else
        t_5 = .false.
      end if
      if (t_5) then
        r = 2_int64
        return
      else
        if ((k_ == 6_int64)) then
          t_6 = (pc_ == 5_int64)
        else
          t_6 = .false.
        end if
        if (t_6) then
          r = 5_int64
          return
        else
          r = 3_int64
          return
        end if
      end if
    end if
  end function ex_unw

  pure function ex_arfit(pass_, nf_, vr_, m_) result(r)
    integer(int64), value :: pass_
    integer(int64), value :: nf_
    integer(int64), value :: vr_
    integer(int64), value :: m_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    if ((pass_ == 0_int64)) then
      if ((vr_ == 0_int64)) then
        if (.true.) then
          t_1 = (nf_ == m_)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      t_3 = t_2
    else
      t_3 = .false.
    end if
    if (t_3) then
      r = 1_int64
      return
    else
      if ((pass_ == 1_int64)) then
        if ((vr_ == 1_int64)) then
          if (.true.) then
            if (.true.) then
              if ((.not. (nf_ < 0_int64))) then
                t_4 = (.not. (m_ < nf_))
              else
                t_4 = .false.
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
        t_8 = t_7
      else
        t_8 = .false.
      end if
      if (t_8) then
        r = 1_int64
        return
      else
        r = 0_int64
        return
      end if
    end if
  end function ex_arfit

  pure function ex_entry(cl_, fit_) result(r)
    integer(int64), value :: cl_
    integer(int64), value :: fit_
    integer(int64) :: r
    if ((.not. (cl_ == 1_int64))) then
      r = 0_int64
      return
    else
      if ((fit_ == 1_int64)) then
        r = 1_int64
        return
      else
        r = 2_int64
        return
      end if
    end if
  end function ex_entry

  pure function ex_apentry(ap_, n_, fk_, sq_) result(r)
    integer(int64), value :: ap_
    integer(int64), value :: n_
    integer(int64), value :: fk_
    integer(int64), value :: sq_
    integer(int64) :: r
    logical :: t_1
    if ((.not. (ap_ == 1_int64))) then
      r = 0_int64
      return
    else
      if (.true.) then
        t_1 = (.not. (n_ < 2_int64))
      else
        t_1 = .false.
      end if
      if ((.not. t_1)) then
        r = 2_int64
        return
      else
        if ((.not. (fk_ == 1_int64))) then
          r = 0_int64
          return
        else
          if ((.not. (sq_ == 1_int64))) then
            r = 3_int64
            return
          else
            r = 1_int64
            return
          end if
        end if
      end if
    end if
  end function ex_apentry

  pure function ex_apstep(req_, k_, more_) result(r)
    integer(int64), value :: req_
    integer(int64), value :: k_
    integer(int64), value :: more_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    if (.true.) then
      if ((.not. (req_ < 0_int64))) then
        t_1 = .true.
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if ((.not. t_2)) then
      r = 3_int64
      return
    else
      if ((k_ < req_)) then
        t_3 = (more_ == 1_int64)
      else
        t_3 = .false.
      end if
      if (t_3) then
        r = 1_int64
        return
      else
        if ((req_ < k_)) then
          t_4 = (req_ < k_)
        else
          t_4 = (more_ == 1_int64)
        end if
        if (t_4) then
          r = 2_int64
          return
        else
          r = 3_int64
          return
        end if
      end if
    end if
  end function ex_apstep

  pure function ex_aplook(req_, k_) result(r)
    integer(int64), value :: req_
    integer(int64), value :: k_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    if (.true.) then
      if ((.not. (req_ < 0_int64))) then
        if (.true.) then
          if ((.not. (req_ < k_))) then
            t_1 = (.not. (req_ < k_))
          else
            t_1 = (((-1_int64) + k_) == req_)
          end if
          t_2 = t_1
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
      r = 1_int64
      return
    else
      r = 0_int64
      return
    end if
  end function ex_aplook

  pure function sk_step(kd_, i_, cnt_) result(r)
    integer(int64), value :: kd_
    integer(int64), value :: i_
    integer(int64), value :: cnt_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    select case (kd_)
    case (1_int64)
      r = 1_int64
      return
    case (2_int64)
      if (.true.) then
        if (.true.) then
          if ((.not. (i_ < 0_int64))) then
            t_1 = (i_ < cnt_)
          else
            t_1 = .false.
          end if
          t_2 = t_1
        else
          t_2 = .false.
        end if
        t_3 = t_2
      else
        t_3 = .false.
      end if
      if (t_3) then
        r = 2_int64
        return
      else
        r = 0_int64
        return
      end if
    case (3_int64)
      r = 3_int64
      return
    case (5_int64)
      r = 5_int64
      return
    case (0_int64)
      r = 0_int64
      return
    case default
      r = 4_int64
      return
    end select
  end function sk_step
