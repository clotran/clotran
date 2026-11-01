  ! GENERATED from model/exec.lisp by scripts/acl2-fortran -b exec. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the tree evaluator's turn for its core kinds -- a constant, a
  ! local, if, do, let*, loop* and recur -- what run_loop does with the top
  ! record (ex_act), which child it takes (ex_kid), the record's pc and i after
  ! (ex_pc, ex_i), and whether k_finish restarts it (ex_fin) -- guard-verified.
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
    logical :: t_2
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
        t_4 = (k_ == 11_int64)
      else
        t_4 = (k_ == 12_int64)
      end if
      if (t_4) then
        if ((pc_ == 1_int64)) then
          r = 6_int64
          return
        else
          if (.true.) then
            if (.true.) then
              t_5 = (i_ < n2_)
            else
              t_5 = .false.
            end if
            t_6 = t_5
          else
            t_6 = .false.
          end if
          if (t_6) then
            r = 3_int64
            return
          else
            if ((k_ == 12_int64)) then
              r = 7_int64
              return
            else
              r = 4_int64
              return
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
                  t_7 = (i_ < nk_)
                else
                  t_7 = .false.
                end if
                t_8 = t_7
              else
                t_8 = .false.
              end if
              if (t_8) then
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
        case (6_int64)
          select case (pc_)
          case (0_int64)
            r = 13_int64
            return
          case (1_int64)
            r = 14_int64
            return
          case (2_int64)
            if (.true.) then
              if (.true.) then
                t_9 = (i_ < nk_)
              else
                t_9 = .false.
              end if
              t_10 = t_9
            else
              t_10 = .false.
            end if
            if (t_10) then
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
          r = 0_int64
          return
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
          t_5 = (k_ == 11_int64)
        else
          t_5 = (k_ == 12_int64)
        end if
        if (t_5) then
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
            r = i_
            return
          else
            if ((n2_ >= 0_int64)) then
              t_8 = (n2_ < 1099511627776_int64)
            else
              t_8 = .false.
            end if
            if (t_8) then
              r = n2_
              return
            else
              r = 0_int64
              return
            end if
          end if
        else
          if ((i_ >= 0_int64)) then
            t_9 = (i_ < 1099511627776_int64)
          else
            t_9 = .false.
          end if
          if (t_9) then
            r = i_
            return
          else
            r = 0_int64
            return
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
    logical :: t_2
    logical :: t_3
    if ((k_ == 4_int64)) then
      r = 1_int64
      return
    else
      if ((k_ == 11_int64)) then
        t_1 = (k_ == 11_int64)
      else
        t_1 = (k_ == 12_int64)
      end if
      if (t_1) then
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
                  t_2 = (i_ < nk_)
                else
                  t_2 = .false.
                end if
                t_3 = t_2
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
            r = 0_int64
            return
          end if
        end if
      end if
    end if
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
    integer(int64) :: t_11
    integer(int64) :: t_12
    integer(int64) :: t_13
    integer(int64) :: t_2
    logical :: t_4
    integer(int64) :: t_5
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
      t_13 = i1_3
    else
      if ((k_ == 11_int64)) then
        t_4 = (k_ == 11_int64)
      else
        t_4 = (k_ == 12_int64)
      end if
      if (t_4) then
        if ((pc_ == 1_int64)) then
          t_5 = i1_3
        else
          t_5 = i_
        end if
        t_12 = t_5
      else
        if ((k_ == 16_int64)) then
          if ((pc_ == 0_int64)) then
            t_7 = 0_int64
          else
            if ((pc_ == 2_int64)) then
              t_6 = i1_3
            else
              t_6 = i_
            end if
            t_7 = t_6
          end if
          t_11 = t_7
        else
          if ((k_ == 6_int64)) then
            if ((pc_ == 1_int64)) then
              t_9 = 1_int64
            else
              if ((pc_ == 3_int64)) then
                t_8 = i1_3
              else
                t_8 = i_
              end if
              t_9 = t_8
            end if
            t_10 = t_9
          else
            t_10 = i_
          end if
          t_11 = t_10
        end if
        t_12 = t_11
      end if
      t_13 = t_12
    end if
    r = t_13
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
