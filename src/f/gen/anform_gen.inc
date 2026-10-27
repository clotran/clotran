  ! GENERATED from model/anform.lisp by scripts/acl2-fortran -b anform. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the analyzer's special forms -- what each is refused for,
  ! as clj's Compiler refuses it (anf_if, anf_def, anf_quote, anf_throw, the
  ! try's clause walk anf_try_step and anf_catch, anf_set, anf_set_target,
  ! anf_dot, anf_dot_member, anf_new), and where a def's init and docstring are --
  ! guard-verified, reading forms through analyze.inc's frf_* shims.
  ! anform-proof.lisp proves each refuses exactly what its specification says
  ! and that the analyzer they drive builds a tree anpass's reads decode;
  ! anform-cost.lisp counts the steps.
  pure function anf_if(n_) result(r)
    integer(int64), value :: n_
    integer(int64) :: r
    if ((4_int64 < n_)) then
      r = 21_int64
      return
    else
      if ((n_ < 3_int64)) then
        r = 22_int64
        return
      else
        r = 0_int64
        return
      end if
    end if
  end function anf_if

  function anf_def(f_, w_) result(r)
    type(gc_value), value :: f_
    integer(int64), value :: w_
    integer(int64) :: r
    integer(int64) :: doc_4
    integer(int64) :: m_6
    integer(int64) :: n_1
    type(gc_value) :: s_7
    integer(int64) :: t_10
    integer(int64) :: t_11
    integer(int64) :: t_12
    integer(int64) :: t_13
    integer(int64) :: t_14
    integer(int64) :: t_15
    integer(int64) :: t_16
    integer(int64) :: t_17
    logical :: t_2
    integer(int64) :: t_3
    integer(int64) :: t_5
    integer(int64) :: t_8
    integer(int64) :: t_9
    n_1 = frf_len(f_)
    if ((n_1 == 4_int64)) then
      t_2 = (frf_kind(frf_nth(f_, 2_int64)) == 4_int64)
    else
      t_2 = .false.
    end if
    if (t_2) then
      t_3 = 1_int64
    else
      t_3 = 0_int64
    end if
    doc_4 = t_3
    if ((doc_4 == 1_int64)) then
      t_5 = 3_int64
    else
      t_5 = n_1
    end if
    m_6 = t_5
    s_7 = frf_nth(f_, 1_int64)
    if ((w_ == 1_int64)) then
      if ((doc_4 == 1_int64)) then
        t_9 = 3_int64
      else
        if ((m_6 == 3_int64)) then
          t_8 = 2_int64
        else
          t_8 = 0_int64
        end if
        t_9 = t_8
      end if
      t_17 = t_9
    else
      if ((w_ == 2_int64)) then
        if ((doc_4 == 1_int64)) then
          t_10 = 2_int64
        else
          t_10 = 0_int64
        end if
        t_16 = t_10
      else
        if ((3_int64 < m_6)) then
          t_15 = 23_int64
        else
          if ((m_6 < 2_int64)) then
            t_14 = 24_int64
          else
            if ((.not. (frm_kind(s_7) == 2_int64))) then
              t_13 = 25_int64
            else
              if ((frf_defvar(s_7) == 1_int64)) then
                t_12 = 26_int64
              else
                if ((frf_defvar(s_7) == 2_int64)) then
                  t_11 = 27_int64
                else
                  t_11 = 0_int64
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
    r = t_17
    return
  end function anf_def

  pure function anf_quote(n_) result(r)
    integer(int64), value :: n_
    integer(int64) :: r
    if ((n_ == 2_int64)) then
      r = 0_int64
      return
    else
      r = 28_int64
      return
    end if
  end function anf_quote

  pure function anf_throw(n_) result(r)
    integer(int64), value :: n_
    integer(int64) :: r
    if ((n_ < 2_int64)) then
      r = 29_int64
      return
    else
      if ((2_int64 < n_)) then
        r = 30_int64
        return
      else
        r = 0_int64
        return
      end if
    end if
  end function anf_throw

  function anf_try_op(f_) result(r)
    type(gc_value), value :: f_
    integer(int64) :: r
    logical :: t_1
    if ((frf_kind(f_) == 3_int64)) then
      t_1 = (0_int64 < frf_len(f_))
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = frf_word(frf_nth(f_, 0_int64))
      return
    else
      r = 0_int64
      return
    end if
  end function anf_try_op

  function anf_try_step(st_, f_, lastp_, w_) result(r)
    integer(int64), value :: st_
    type(gc_value), value :: f_
    integer(int64), value :: lastp_
    integer(int64), value :: w_
    integer(int64) :: r
    integer(int64) :: op_1
    integer(int64) :: t_2
    integer(int64) :: t_3
    integer(int64) :: t_4
    integer(int64) :: t_5
    integer(int64) :: t_6
    integer(int64) :: t_7
    integer(int64) :: t_8
    op_1 = anf_try_op(f_)
    if ((w_ == 1_int64)) then
      t_8 = op_1
    else
      if ((w_ == 2_int64)) then
        if ((op_1 == 1_int64)) then
          t_2 = 1_int64
        else
          t_2 = st_
        end if
        t_7 = t_2
      else
        if ((op_1 == 0_int64)) then
          if ((st_ == 1_int64)) then
            t_3 = 31_int64
          else
            t_3 = 0_int64
          end if
          t_6 = t_3
        else
          if ((op_1 == 2_int64)) then
            if ((lastp_ == 1_int64)) then
              t_4 = 0_int64
            else
              t_4 = 32_int64
            end if
            t_5 = t_4
          else
            t_5 = 0_int64
          end if
          t_6 = t_5
        end if
        t_7 = t_6
      end if
      t_8 = t_7
    end if
    r = t_8
    return
  end function anf_try_step

  function anf_catch(f_) result(r)
    type(gc_value), value :: f_
    integer(int64) :: r
    if ((frf_class(frf_nth(f_, 1_int64)) == 0_int64)) then
      r = 33_int64
      return
    else
      r = anl_name_code(frf_nth(f_, 2_int64))
      return
    end if
  end function anf_catch

  pure function anf_set(n_) result(r)
    integer(int64), value :: n_
    integer(int64) :: r
    if ((n_ == 3_int64)) then
      r = 0_int64
      return
    else
      r = 34_int64
      return
    end if
  end function anf_set

  function anf_set_target(x_) result(r)
    type(gc_value), value :: x_
    integer(int64) :: r
    integer(int64) :: k_1
    logical :: t_2
    logical :: t_3
    integer(int64) :: t_4
    integer(int64) :: t_5
    k_1 = frf_kind(x_)
    if ((k_1 == 2_int64)) then
      t_5 = 0_int64
    else
      if ((k_1 == 3_int64)) then
        if ((0_int64 < frf_len(x_))) then
          t_2 = (frm_kind(frf_nth(x_, 0_int64)) == 2_int64)
        else
          t_2 = .false.
        end if
        t_3 = t_2
      else
        t_3 = .false.
      end if
      if (t_3) then
        t_4 = 0_int64
      else
        t_4 = 35_int64
      end if
      t_5 = t_4
    end if
    r = t_5
    return
  end function anf_set_target

  function anf_dot(f_) result(r)
    type(gc_value), value :: f_
    integer(int64) :: r
    if ((frf_len(f_) < 3_int64)) then
      r = 36_int64
      return
    else
      r = 0_int64
      return
    end if
  end function anf_dot

  function anf_dot_member(n_, m_) result(r)
    integer(int64), value :: n_
    type(gc_value), value :: m_
    integer(int64) :: r
    logical :: t_1
    if ((n_ == 3_int64)) then
      t_1 = (frm_kind(m_) == 2_int64)
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = 0_int64
      return
    else
      if ((frf_kind(m_) == 3_int64)) then
        if ((frm_kind(frf_nth(m_, 0_int64)) == 2_int64)) then
          r = 0_int64
          return
        else
          r = 37_int64
          return
        end if
      else
        if ((frm_kind(m_) == 2_int64)) then
          r = 0_int64
          return
        else
          r = 37_int64
          return
        end if
      end if
    end if
  end function anf_dot_member

  function anf_new(f_) result(r)
    type(gc_value), value :: f_
    integer(int64) :: r
    if ((frf_len(f_) < 2_int64)) then
      r = 38_int64
      return
    else
      if ((frf_class(frf_nth(f_, 1_int64)) == 0_int64)) then
        r = 33_int64
        return
      else
        r = 0_int64
        return
      end if
    end if
  end function anf_new
