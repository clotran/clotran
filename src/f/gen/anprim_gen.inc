  ! GENERATED from model/anprim.lisp by scripts/acl2-fortran -b anprim. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the analyzer's primitive kinds -- a Numbers op's kind folded
  ! over its operands (apk_arith), a loop local's widening (apk_loop), a let or
  ! loop local's kind or refusal (apk_let), a hinted return's refusal (apk_ret),
  ! a recur argument's match (apk_recur_ok), an array hint's element kind
  ! (apk_elem) -- guard-verified, reading a node's kind through analyze.inc's
  ! apk_kid. anprim-proof.lisp proves each is clj's rule and that a hint changes
  ! no value; anprim-cost.lisp counts the steps.
  pure function apk_int_p(k_) result(r)
    integer(int64), value :: k_
    logical :: r
    select case (k_)
    case (1_int64)
      r = (k_ == 1_int64)
      return
    case (3_int64)
      r = (k_ == 3_int64)
      return
    case (6_int64)
      r = (k_ == 6_int64)
      return
    case (7_int64)
      r = (k_ == 7_int64)
      return
    case default
      r = (k_ == 8_int64)
      return
    end select
  end function apk_int_p

  pure function apk_float_p(k_) result(r)
    integer(int64), value :: k_
    logical :: r
    if ((k_ == 2_int64)) then
      r = (k_ == 2_int64)
      return
    else
      r = (k_ == 5_int64)
      return
    end if
  end function apk_float_p

  pure function apk_num(a_) result(r)
    integer(int64), value :: a_
    integer(int64) :: r
    if (apk_int_p(a_)) then
      r = 1_int64
      return
    else
      if ((a_ == 5_int64)) then
        r = 2_int64
        return
      else
        r = a_
        return
      end if
    end if
  end function apk_num

  pure function apk_step(how_, k_, a_) result(r)
    integer(int64), value :: how_
    integer(int64), value :: k_
    integer(int64), value :: a_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    if ((how_ == 5_int64)) then
      if ((k_ == a_)) then
        r = k_
        return
      else
        r = (-1_int64)
        return
      end if
    else
      if ((how_ == 3_int64)) then
        if ((k_ == (-1_int64))) then
          t_1 = (k_ == (-1_int64))
        else
          t_1 = (a_ == (-1_int64))
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        r = (-1_int64)
        return
      else
        if ((k_ == 2_int64)) then
          t_3 = (k_ == 2_int64)
        else
          t_3 = (a_ == 2_int64)
        end if
        if (t_3) then
          r = 2_int64
          return
        else
          if ((k_ == (-1_int64))) then
            t_4 = (k_ == (-1_int64))
          else
            t_4 = (a_ == (-1_int64))
          end if
          if (t_4) then
            r = (-1_int64)
            return
          else
            if ((how_ == 2_int64)) then
              r = (-1_int64)
              return
            else
              r = k_
              return
            end if
          end if
        end if
      end if
    end if
  end function apk_step

  recursive function apk_fold(kids_, sc_, how_, i_, n_, k_) result(r)
    type(gc_value), value :: kids_
    type(gc_value), value :: sc_
    integer(int64), value :: how_
    integer(int64), value :: i_
    integer(int64), value :: n_
    integer(int64), value :: k_
    integer(int64) :: r
    integer(int64) :: a_4
    integer(int64) :: a_6
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_5
    integer(int64) :: t_7
    integer(int64) :: t_8
    if ((i_ >= 0_int64)) then
      if ((n_ >= 0_int64)) then
        if ((i_ < n_)) then
          t_1 = (n_ < 1099511627776_int64)
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
      a_4 = apk_kid(kids_, sc_, i_)
      if ((a_4 == 0_int64)) then
        t_5 = (a_4 == 0_int64)
      else
        t_5 = (a_4 == 4_int64)
      end if
      if (t_5) then
        t_8 = 0_int64
      else
        a_6 = apk_num(a_4)
        if ((i_ == 1_int64)) then
          t_7 = a_6
        else
          t_7 = apk_step(how_, k_, a_6)
        end if
        t_8 = apk_fold(kids_, sc_, how_, (1_int64 + i_), n_, t_7)
      end if
      r = t_8
      return
    else
      r = k_
      return
    end if
  end function apk_fold

  function apk_arith(kids_, sc_, how_, n_) result(r)
    type(gc_value), value :: kids_
    type(gc_value), value :: sc_
    integer(int64), value :: how_
    integer(int64), value :: n_
    integer(int64) :: r
    integer(int64) :: k_1
    logical :: t_2
    logical :: t_3
    integer(int64) :: t_4
    k_1 = apk_fold(kids_, sc_, how_, 1_int64, n_, 0_int64)
    if ((how_ == 6_int64)) then
      if ((.not. (k_1 == 2_int64))) then
        t_2 = (.not. (k_1 == 0_int64))
      else
        t_2 = .false.
      end if
      t_3 = t_2
    else
      t_3 = .false.
    end if
    if (t_3) then
      t_4 = (-1_int64)
    else
      t_4 = k_1
    end if
    r = t_4
    return
  end function apk_arith

  pure function apk_loop(pk_) result(r)
    integer(int64), value :: pk_
    integer(int64) :: r
    if ((pk_ == 3_int64)) then
      r = 1_int64
      return
    else
      if ((pk_ == 5_int64)) then
        r = 2_int64
        return
      else
        r = pk_
        return
      end if
    end if
  end function apk_loop

  pure function apk_let(pk_, hinted_, loopp_, rk_) result(r)
    integer(int64), value :: pk_
    integer(int64), value :: hinted_
    integer(int64), value :: loopp_
    integer(int64), value :: rk_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((0_int64 < pk_)) then
        t_1 = (hinted_ == 1_int64)
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = (-2_int64)
      return
    else
      if ((.not. (loopp_ == 1_int64))) then
        r = pk_
        return
      else
        if ((rk_ == (-100_int64))) then
          r = apk_loop(pk_)
          return
        else
          if ((rk_ == 0_int64)) then
            r = (-1_int64)
            return
          else
            r = rk_
            return
          end if
        end if
      end if
    end if
  end function apk_let

  pure function apk_ret(ret_, bk_) result(r)
    integer(int64), value :: ret_
    integer(int64), value :: bk_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    if (.true.) then
      if ((0_int64 < ret_)) then
        if (.true.) then
          if ((0_int64 < bk_)) then
            if ((.not. (bk_ == ret_))) then
              if ((ret_ == 1_int64)) then
                t_1 = (bk_ == 3_int64)
              else
                t_1 = .false.
              end if
              if ((.not. t_1)) then
                if ((ret_ == 2_int64)) then
                  t_2 = (bk_ == 5_int64)
                else
                  t_2 = .false.
                end if
                t_3 = (.not. t_2)
              else
                t_3 = .false.
              end if
              t_4 = t_3
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
  end function apk_ret

  pure function apk_recur_ok(p_, k_) result(r)
    integer(int64), value :: p_
    integer(int64), value :: k_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      t_1 = (0_int64 < p_)
    else
      t_1 = .false.
    end if
    if ((.not. t_1)) then
      r = 1_int64
      return
    else
      if ((k_ == 0_int64)) then
        r = 1_int64
        return
      else
        if ((p_ == 1_int64)) then
          t_2 = apk_int_p(k_)
        else
          t_2 = .false.
        end if
        if (t_2) then
          r = 1_int64
          return
        else
          if ((p_ == 2_int64)) then
            t_3 = apk_float_p(k_)
          else
            t_3 = .false.
          end if
          if (t_3) then
            r = 1_int64
            return
          else
            r = 0_int64
            return
          end if
        end if
      end if
    end if
  end function apk_recur_ok

  pure function apk_elem(i_) result(r)
    integer(int64), value :: i_
    integer(int64) :: r
    select case (i_)
    case (0_int64)
      r = 2_int64
      return
    case (1_int64)
      r = 1_int64
      return
    case (2_int64)
      r = 3_int64
      return
    case (3_int64)
      r = 5_int64
      return
    case (4_int64)
      r = 6_int64
      return
    case (5_int64)
      r = 7_int64
      return
    case (6_int64)
      r = 8_int64
      return
    case (7_int64)
      r = 4_int64
      return
    case default
      r = (-1_int64)
      return
    end select
  end function apk_elem
