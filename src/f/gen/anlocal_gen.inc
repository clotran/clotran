  ! GENERATED from model/anlocal.lisp by scripts/acl2-fortran -b anlocal. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the analyzer's locals -- the binding-form checks clj's
  ! Compiler makes (anl_shape, anl_name_code, anl_params, anl_arity), the
  ! scopes (anl_new_fn, anl_child, anl_reserve, anl_bind), name resolution with
  ! its captures (anl_lookup) and what the analyzer reads back (anl_env,
  ! anl_caps_of, anl_names_of) -- guard-verified, reading forms through
  ! analyze.inc's frm_* shims. anlocal-proof.lisp proves a name resolves to
  ! its innermost binding and a fn captures exactly the names it uses from
  ! outside; anlocal-cost.lisp counts the steps.
  pure function anl_odd(n_) result(r)
    integer(int64), value :: n_
    integer(int64) :: r
    integer(int64) :: n_1
    do
      if ((n_ <= 0_int64)) then
        r = 0_int64
        return
      else
        if ((n_ == 1_int64)) then
          r = 1_int64
          return
        else
          n_1 = ((-2_int64) + n_)
          n_ = n_1
          cycle
        end if
      end if
    end do
  end function anl_odd

  function anl_shape(bv_) result(r)
    type(gc_value), value :: bv_
    integer(int64) :: r
    if ((.not. (frm_kind(bv_) == 1_int64))) then
      r = 1_int64
      return
    else
      if ((anl_odd(frm_count(bv_)) == 1_int64)) then
        r = 2_int64
        return
      else
        r = 0_int64
        return
      end if
    end if
  end function anl_shape

  function anl_name_code(x_) result(r)
    type(gc_value), value :: x_
    integer(int64) :: r
    if ((.not. (frm_kind(x_) == 2_int64))) then
      r = 3_int64
      return
    else
      if ((frm_qual(x_) == 1_int64)) then
        r = 4_int64
        return
      else
        r = 0_int64
        return
      end if
    end if
  end function anl_name_code

  pure function anl_pans(w_, code_, i_, nreq_, rest_) result(r)
    integer(int64), value :: w_
    integer(int64), value :: code_
    integer(int64), value :: i_
    integer(int64), value :: nreq_
    integer(int64), value :: rest_
    integer(int64) :: r
    select case (w_)
    case (0_int64)
      r = code_
      return
    case (1_int64)
      r = i_
      return
    case (2_int64)
      r = nreq_
      return
    case default
      r = rest_
      return
    end select
  end function anl_pans

  recursive function anl_pw(pv_, i_, n_, st_, nreq_, rest_, w_) result(r)
    type(gc_value), value :: pv_
    integer(int64), value :: i_
    integer(int64), value :: n_
    integer(int64), value :: st_
    integer(int64), value :: nreq_
    integer(int64), value :: rest_
    integer(int64), value :: w_
    integer(int64) :: r
    type(gc_value) :: p_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: t_4
    integer(int64) :: t_5
    integer(int64) :: t_6
    integer(int64) :: t_7
    integer(int64) :: t_8
    integer(int64) :: t_9
    if ((i_ >= 0_int64)) then
      if ((n_ >= 0_int64)) then
        t_1 = (i_ < n_)
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      p_3 = frm_nth(pv_, i_)
      if ((.not. (frm_kind(p_3) == 2_int64))) then
        t_9 = anl_pans(w_, 5_int64, i_, nreq_, rest_)
      else
        if ((frm_qual(p_3) == 1_int64)) then
          t_8 = anl_pans(w_, 6_int64, i_, nreq_, rest_)
        else
          if ((frm_amp(p_3) == 1_int64)) then
            if ((st_ == 0_int64)) then
              t_4 = anl_pw(pv_, (1_int64 + i_), n_, 1_int64, nreq_, rest_, w_)
            else
              t_4 = anl_pans(w_, 7_int64, i_, nreq_, rest_)
            end if
            t_7 = t_4
          else
            if ((st_ == 0_int64)) then
              t_6 = anl_pw(pv_, (1_int64 + i_), n_, 0_int64, (1_int64 + nreq_), rest_, w_)
            else
              if ((st_ == 1_int64)) then
                t_5 = anl_pw(pv_, (1_int64 + i_), n_, 2_int64, nreq_, 1_int64, w_)
              else
                t_5 = anl_pans(w_, 8_int64, i_, nreq_, rest_)
              end if
              t_6 = t_5
            end if
            t_7 = t_6
          end if
          t_8 = t_7
        end if
        t_9 = t_8
      end if
      r = t_9
      return
    else
      if ((20_int64 < max(0_int64, nreq_))) then
        r = anl_pans(w_, 9_int64, i_, nreq_, rest_)
        return
      else
        r = anl_pans(w_, 0_int64, i_, nreq_, rest_)
        return
      end if
    end if
  end function anl_pw

  function anl_params(pv_, w_) result(r)
    type(gc_value), value :: pv_
    integer(int64), value :: w_
    integer(int64) :: r
    r = anl_pw(pv_, 0_int64, frm_count(pv_), 0_int64, 0_int64, 0_int64, w_)
    return
  end function anl_params

  pure function anl_g_fctr(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nf)) then
          t_1 = (i_ < size(ls%fctr, kind=int64))
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
      r = ls%fctr(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_fctr

  subroutine anl_s_fctr(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%fctr, kind=int64))
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
      ls%fctr(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_fctr

  pure function anl_g_fout(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nf)) then
          t_1 = (i_ < size(ls%fout, kind=int64))
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
      r = ls%fout(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_fout

  subroutine anl_s_fout(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%fout, kind=int64))
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
      ls%fout(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_fout

  pure function anl_g_fcap(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nf)) then
          t_1 = (i_ < size(ls%fcap, kind=int64))
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
      r = ls%fcap(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_fcap

  subroutine anl_s_fcap(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%fcap, kind=int64))
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
      ls%fcap(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_fcap

  pure function anl_g_fvar(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nf)) then
          t_1 = (i_ < size(ls%fvar, kind=int64))
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
      r = ls%fvar(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_fvar

  subroutine anl_s_fvar(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%fvar, kind=int64))
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
      ls%fvar(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_fvar

  pure function anl_g_fah(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nf)) then
          t_1 = (i_ < size(ls%fah, kind=int64))
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
      r = ls%fah(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_fah

  subroutine anl_s_fah(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%fah, kind=int64))
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
      ls%fah(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_fah

  pure function anl_g_fnl(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nf)) then
          t_1 = (i_ < size(ls%fnl, kind=int64))
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
      r = ls%fnl(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_fnl

  subroutine anl_s_fnl(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%fnl, kind=int64))
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
      ls%fnl(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_fnl

  pure function anl_g_bpar(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nb)) then
          t_1 = (i_ < size(ls%bpar, kind=int64))
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
      r = ls%bpar(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_bpar

  subroutine anl_s_bpar(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%bpar, kind=int64))
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
      ls%bpar(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_bpar

  pure function anl_g_bfn(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nb)) then
          t_1 = (i_ < size(ls%bfn, kind=int64))
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
      r = ls%bfn(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_bfn

  subroutine anl_s_bfn(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%bfn, kind=int64))
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
      ls%bfn(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_bfn

  pure function anl_g_bhead(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nb)) then
          t_1 = (i_ < size(ls%bhead, kind=int64))
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
      r = ls%bhead(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_bhead

  subroutine anl_s_bhead(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%bhead, kind=int64))
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
      ls%bhead(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_bhead

  pure function anl_g_xnm(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nx)) then
          t_1 = (i_ < size(ls%xnm, kind=int64))
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
      r = ls%xnm(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_xnm

  subroutine anl_s_xnm(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%xnm, kind=int64))
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
      ls%xnm(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_xnm

  pure function anl_g_xsl(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nx)) then
          t_1 = (i_ < size(ls%xsl, kind=int64))
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
      r = ls%xsl(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_xsl

  subroutine anl_s_xsl(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%xsl, kind=int64))
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
      ls%xsl(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_xsl

  pure function anl_g_xblk(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nx)) then
          t_1 = (i_ < size(ls%xblk, kind=int64))
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
      r = ls%xblk(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_xblk

  subroutine anl_s_xblk(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%xblk, kind=int64))
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
      ls%xblk(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_xblk

  pure function anl_g_xnext(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nx)) then
          t_1 = (i_ < size(ls%xnext, kind=int64))
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
      r = ls%xnext(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_xnext

  subroutine anl_s_xnext(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%xnext, kind=int64))
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
      ls%xnext(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_xnext

  pure function anl_g_cnm(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nc)) then
          t_1 = (i_ < size(ls%cnm, kind=int64))
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
      r = ls%cnm(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_cnm

  subroutine anl_s_cnm(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%cnm, kind=int64))
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
      ls%cnm(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_cnm

  pure function anl_g_cout(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nc)) then
          t_1 = (i_ < size(ls%cout, kind=int64))
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
      r = ls%cout(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_cout

  subroutine anl_s_cout(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%cout, kind=int64))
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
      ls%cout(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_cout

  pure function anl_g_cin(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nc)) then
          t_1 = (i_ < size(ls%cin, kind=int64))
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
      r = ls%cin(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_cin

  subroutine anl_s_cin(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%cin, kind=int64))
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
      ls%cin(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_cin

  pure function anl_g_cbx(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nc)) then
          t_1 = (i_ < size(ls%cbx, kind=int64))
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
      r = ls%cbx(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_cbx

  subroutine anl_s_cbx(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%cbx, kind=int64))
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
      ls%cbx(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_cbx

  pure function anl_g_cnext(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nc)) then
          t_1 = (i_ < size(ls%cnext, kind=int64))
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
      r = ls%cnext(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_cnext

  subroutine anl_s_cnext(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%cnext, kind=int64))
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
      ls%cnext(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_cnext

  pure function anl_g_nsl(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nn)) then
          t_1 = (i_ < size(ls%nsl, kind=int64))
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
      r = ls%nsl(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_nsl

  subroutine anl_s_nsl(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%nsl, kind=int64))
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
      ls%nsl(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_nsl

  pure function anl_g_nnm(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nn)) then
          t_1 = (i_ < size(ls%nnm, kind=int64))
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
      r = ls%nnm(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_nnm

  subroutine anl_s_nnm(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%nnm, kind=int64))
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
      ls%nnm(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_nnm

  pure function anl_g_nnext(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nn)) then
          t_1 = (i_ < size(ls%nnext, kind=int64))
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
      r = ls%nnext(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_nnext

  subroutine anl_s_nnext(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%nnext, kind=int64))
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
      ls%nnext(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_nnext

  pure function anl_g_an(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%na)) then
          t_1 = (i_ < size(ls%an, kind=int64))
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
      r = ls%an(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_an

  subroutine anl_s_an(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%an, kind=int64))
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
      ls%an(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_an

  pure function anl_g_anext(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%na)) then
          t_1 = (i_ < size(ls%anext, kind=int64))
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
      r = ls%anext(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_anext

  subroutine anl_s_anext(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%anext, kind=int64))
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
      ls%anext(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_anext

  pure function anl_g_ev(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nev)) then
          t_1 = (i_ < size(ls%ev, kind=int64))
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
      r = ls%ev(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_ev

  subroutine anl_s_ev(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%ev, kind=int64))
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
      ls%ev(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_ev

  pure function anl_g_es(ls, i_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        if ((i_ < ls%nev)) then
          t_1 = (i_ < size(ls%es, kind=int64))
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
      r = ls%es(i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_g_es

  subroutine anl_s_es(ls, i_, v_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: i_
    integer(int64), value :: v_
    integer(int64) :: i_3
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    if (.true.) then
      if ((.not. (i_ < 0_int64))) then
        t_1 = (i_ < size(ls%es, kind=int64))
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
      ls%es(i_3) = v_4
    else
      ls%err = 1_int64
    end if
  end subroutine anl_s_es

  subroutine anl_grow_f(ls, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: n_
    integer(int64) :: n_1
    integer(int64) :: n_2
    integer(int64) :: n_3
    integer(int64) :: n_4
    integer(int64) :: n_5
    integer(int64) :: n_6
    if ((n_ < size(ls%fctr, kind=int64))) then
    else
      n_1 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%fctr, n_1)
    end if
    if ((n_ < size(ls%fout, kind=int64))) then
    else
      n_2 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%fout, n_2)
    end if
    if ((n_ < size(ls%fcap, kind=int64))) then
    else
      n_3 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%fcap, n_3)
    end if
    if ((n_ < size(ls%fvar, kind=int64))) then
    else
      n_4 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%fvar, n_4)
    end if
    if ((n_ < size(ls%fah, kind=int64))) then
    else
      n_5 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%fah, n_5)
    end if
    if ((n_ < size(ls%fnl, kind=int64))) then
    else
      n_6 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%fnl, n_6)
    end if
  end subroutine anl_grow_f

  subroutine anl_grow_b(ls, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: n_
    integer(int64) :: n_1
    integer(int64) :: n_2
    integer(int64) :: n_3
    if ((n_ < size(ls%bpar, kind=int64))) then
    else
      n_1 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%bpar, n_1)
    end if
    if ((n_ < size(ls%bfn, kind=int64))) then
    else
      n_2 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%bfn, n_2)
    end if
    if ((n_ < size(ls%bhead, kind=int64))) then
    else
      n_3 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%bhead, n_3)
    end if
  end subroutine anl_grow_b

  subroutine anl_grow_x(ls, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: n_
    integer(int64) :: n_1
    integer(int64) :: n_2
    integer(int64) :: n_3
    integer(int64) :: n_4
    if ((n_ < size(ls%xnm, kind=int64))) then
    else
      n_1 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%xnm, n_1)
    end if
    if ((n_ < size(ls%xsl, kind=int64))) then
    else
      n_2 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%xsl, n_2)
    end if
    if ((n_ < size(ls%xblk, kind=int64))) then
    else
      n_3 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%xblk, n_3)
    end if
    if ((n_ < size(ls%xnext, kind=int64))) then
    else
      n_4 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%xnext, n_4)
    end if
  end subroutine anl_grow_x

  subroutine anl_grow_c(ls, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: n_
    integer(int64) :: n_1
    integer(int64) :: n_2
    integer(int64) :: n_3
    integer(int64) :: n_4
    integer(int64) :: n_5
    if ((n_ < size(ls%cnm, kind=int64))) then
    else
      n_1 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%cnm, n_1)
    end if
    if ((n_ < size(ls%cout, kind=int64))) then
    else
      n_2 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%cout, n_2)
    end if
    if ((n_ < size(ls%cin, kind=int64))) then
    else
      n_3 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%cin, n_3)
    end if
    if ((n_ < size(ls%cbx, kind=int64))) then
    else
      n_4 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%cbx, n_4)
    end if
    if ((n_ < size(ls%cnext, kind=int64))) then
    else
      n_5 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%cnext, n_5)
    end if
  end subroutine anl_grow_c

  subroutine anl_grow_a(ls, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: n_
    integer(int64) :: n_1
    integer(int64) :: n_2
    if ((n_ < size(ls%an, kind=int64))) then
    else
      n_1 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%an, n_1)
    end if
    if ((n_ < size(ls%anext, kind=int64))) then
    else
      n_2 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%anext, n_2)
    end if
  end subroutine anl_grow_a

  subroutine anl_grow_n(ls, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: n_
    integer(int64) :: n_1
    integer(int64) :: n_2
    integer(int64) :: n_3
    if ((n_ < size(ls%nsl, kind=int64))) then
    else
      n_1 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%nsl, n_1)
    end if
    if ((n_ < size(ls%nnm, kind=int64))) then
    else
      n_2 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%nnm, n_2)
    end if
    if ((n_ < size(ls%nnext, kind=int64))) then
    else
      n_3 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%nnext, n_3)
    end if
  end subroutine anl_grow_n

  subroutine anl_grow_e(ls, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: n_
    integer(int64) :: n_1
    integer(int64) :: n_2
    if ((n_ < size(ls%ev, kind=int64))) then
    else
      n_1 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%ev, n_1)
    end if
    if ((n_ < size(ls%es, kind=int64))) then
    else
      n_2 = (16_int64 + (2_int64 * n_))
      call rt_resize_int(ls%es, n_2)
    end if
  end subroutine anl_grow_e

  subroutine anl_new_fn(ls, o_, r)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: o_
    integer(int64), intent(out) :: r
    integer(int64) :: b_2
    integer(int64) :: f_1
    logical :: t_3
    logical :: t_4
    logical :: t_5
    f_1 = ls%nf
    b_2 = ls%nb
    if ((f_1 >= 0_int64)) then
      if ((f_1 < ((-1_int64) + 1099511627776_int64))) then
        if ((b_2 >= 0_int64)) then
          t_3 = (b_2 < ((-1_int64) + 1099511627776_int64))
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
    if (t_5) then
      call anl_grow_f(ls, f_1)
      call anl_grow_b(ls, b_2)
      call anl_s_fctr(ls, f_1, 0_int64)
      call anl_s_fout(ls, f_1, o_)
      call anl_s_fcap(ls, f_1, (-1_int64))
      call anl_s_fvar(ls, f_1, (-1_int64))
      call anl_s_fah(ls, f_1, (-1_int64))
      call anl_s_fnl(ls, f_1, (-1_int64))
      ls%nf = (1_int64 + f_1)
      call anl_s_bpar(ls, b_2, (-1_int64))
      call anl_s_bfn(ls, b_2, f_1)
      call anl_s_bhead(ls, b_2, (-1_int64))
      ls%nb = (1_int64 + b_2)
      r = b_2
    else
      ls%err = 1_int64
      r = (-1_int64)
    end if
  end subroutine anl_new_fn

  subroutine anl_child(ls, p_, r)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: p_
    integer(int64), intent(out) :: r
    integer(int64) :: b_2
    integer(int64) :: f_1
    logical :: t_3
    logical :: t_4
    f_1 = anl_g_bfn(ls, p_)
    b_2 = ls%nb
    if ((f_1 >= 0_int64)) then
      if ((b_2 >= 0_int64)) then
        t_3 = (b_2 < ((-1_int64) + 1099511627776_int64))
      else
        t_3 = .false.
      end if
      t_4 = t_3
    else
      t_4 = .false.
    end if
    if (t_4) then
      call anl_grow_b(ls, b_2)
      call anl_s_bpar(ls, b_2, p_)
      call anl_s_bfn(ls, b_2, f_1)
      call anl_s_bhead(ls, b_2, (-1_int64))
      ls%nb = (1_int64 + b_2)
      r = b_2
    else
      ls%err = 1_int64
      r = (-1_int64)
    end if
  end subroutine anl_child

  pure function anl_nslots(ls, b_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: b_
    integer(int64) :: r
    r = anl_g_fctr(ls, anl_g_bfn(ls, b_))
    return
  end function anl_nslots

  subroutine anl_reserve(ls, b_, n_, r)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    integer(int64), value :: n_
    integer(int64), intent(out) :: r
    integer(int64) :: f_1
    integer(int64) :: k_2
    logical :: t_3
    logical :: t_4
    f_1 = anl_g_bfn(ls, b_)
    k_2 = anl_g_fctr(ls, f_1)
    if ((k_2 >= 0_int64)) then
      if ((n_ >= 0_int64)) then
        t_3 = ((k_2 + n_) < 1099511627776_int64)
      else
        t_3 = .false.
      end if
      t_4 = t_3
    else
      t_4 = .false.
    end if
    if (t_4) then
      call anl_s_fctr(ls, f_1, (k_2 + n_))
      r = k_2
    else
      ls%err = 1_int64
      r = (-1_int64)
    end if
  end subroutine anl_reserve

  recursive pure function anl_cin_has(ls, c_, k_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: c_
    integer(int64), value :: k_
    logical :: r
    integer(int64) :: j_2
    logical :: t_1
    logical :: t_3
    logical :: t_4
    if ((c_ >= 0_int64)) then
      t_1 = (c_ < ls%nc)
    else
      t_1 = .false.
    end if
    if (t_1) then
      if ((anl_g_cin(ls, c_) == k_)) then
        r = .true.
        return
      else
        j_2 = anl_g_cnext(ls, c_)
        if ((j_2 >= 0_int64)) then
          t_3 = (j_2 < c_)
        else
          t_3 = .false.
        end if
        if (t_3) then
          t_4 = anl_cin_has(ls, j_2, k_)
        else
          t_4 = .false.
        end if
        r = t_4
        return
      end if
    else
      r = .false.
      return
    end if
  end function anl_cin_has

  subroutine anl_push_n(ls, f_, s_, k_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: f_
    integer(int64), value :: s_
    integer(int64), value :: k_
    integer(int64) :: n_1
    logical :: t_2
    n_1 = ls%nn
    if ((n_1 >= 0_int64)) then
      t_2 = (n_1 < ((-1_int64) + 1099511627776_int64))
    else
      t_2 = .false.
    end if
    if (t_2) then
      call anl_grow_n(ls, n_1)
      call anl_s_nsl(ls, n_1, k_)
      call anl_s_nnm(ls, n_1, s_)
      call anl_s_nnext(ls, n_1, anl_g_fnl(ls, f_))
      ls%nn = (1_int64 + n_1)
      call anl_s_fnl(ls, f_, n_1)
    else
      ls%err = 1_int64
    end if
  end subroutine anl_push_n

  subroutine anl_bind(ls, b_, s_, k_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    integer(int64), value :: s_
    integer(int64), value :: k_
    integer(int64) :: f_1
    integer(int64) :: n_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    f_1 = anl_g_bfn(ls, b_)
    n_2 = ls%nx
    if ((f_1 >= 0_int64)) then
      if ((k_ >= 0_int64)) then
        if ((k_ < anl_g_fctr(ls, f_1))) then
          if ((.not. anl_cin_has(ls, anl_g_fcap(ls, f_1), k_))) then
            if ((n_2 >= 0_int64)) then
              t_3 = (n_2 < ((-1_int64) + 1099511627776_int64))
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
    if (t_7) then
      call anl_grow_x(ls, n_2)
      call anl_s_xnm(ls, n_2, s_)
      call anl_s_xsl(ls, n_2, k_)
      call anl_s_xblk(ls, n_2, b_)
      call anl_s_xnext(ls, n_2, anl_g_bhead(ls, b_))
      ls%nx = (1_int64 + n_2)
      call anl_s_bhead(ls, b_, n_2)
      call anl_push_n(ls, f_1, s_, k_)
    else
      ls%err = 2_int64
    end if
  end subroutine anl_bind

  recursive pure function anl_xfind(ls, x_, s_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: x_
    integer(int64), value :: s_
    integer(int64) :: r
    integer(int64) :: j_2
    logical :: t_1
    logical :: t_3
    integer(int64) :: t_4
    if ((x_ >= 0_int64)) then
      t_1 = (x_ < ls%nx)
    else
      t_1 = .false.
    end if
    if (t_1) then
      if ((anl_g_xnm(ls, x_) == s_)) then
        r = x_
        return
      else
        j_2 = anl_g_xnext(ls, x_)
        if ((j_2 >= 0_int64)) then
          t_3 = (j_2 < x_)
        else
          t_3 = .false.
        end if
        if (t_3) then
          t_4 = anl_xfind(ls, j_2, s_)
        else
          t_4 = (-1_int64)
        end if
        r = t_4
        return
      end if
    else
      r = (-1_int64)
      return
    end if
  end function anl_xfind

  recursive pure function anl_chain_find(ls, b_, s_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: b_
    integer(int64), value :: s_
    integer(int64) :: r
    integer(int64) :: p_3
    logical :: t_1
    logical :: t_4
    integer(int64) :: t_5
    integer(int64) :: t_6
    integer(int64) :: x_2
    if ((b_ >= 0_int64)) then
      t_1 = (b_ < ls%nb)
    else
      t_1 = .false.
    end if
    if (t_1) then
      x_2 = anl_xfind(ls, anl_g_bhead(ls, b_), s_)
      if ((.not. (x_2 < 0_int64))) then
        t_6 = x_2
      else
        p_3 = anl_g_bpar(ls, b_)
        if ((p_3 >= 0_int64)) then
          t_4 = (p_3 < b_)
        else
          t_4 = .false.
        end if
        if (t_4) then
          t_5 = anl_chain_find(ls, p_3, s_)
        else
          t_5 = (-1_int64)
        end if
        t_6 = t_5
      end if
      r = t_6
      return
    else
      r = (-1_int64)
      return
    end if
  end function anl_chain_find

  recursive pure function anl_cfind(ls, c_, s_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: c_
    integer(int64), value :: s_
    integer(int64) :: r
    integer(int64) :: j_2
    logical :: t_1
    logical :: t_3
    integer(int64) :: t_4
    if ((c_ >= 0_int64)) then
      t_1 = (c_ < ls%nc)
    else
      t_1 = .false.
    end if
    if (t_1) then
      if ((anl_g_cnm(ls, c_) == s_)) then
        r = c_
        return
      else
        j_2 = anl_g_cnext(ls, c_)
        if ((j_2 >= 0_int64)) then
          t_3 = (j_2 < c_)
        else
          t_3 = .false.
        end if
        if (t_3) then
          t_4 = anl_cfind(ls, j_2, s_)
        else
          t_4 = (-1_int64)
        end if
        r = t_4
        return
      end if
    else
      r = (-1_int64)
      return
    end if
  end function anl_cfind

  subroutine anl_push_c(ls, f_, s_, k_, slot_, bx_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: f_
    integer(int64), value :: s_
    integer(int64), value :: k_
    integer(int64), value :: slot_
    integer(int64), value :: bx_
    integer(int64) :: c_1
    logical :: t_2
    c_1 = ls%nc
    if ((c_1 >= 0_int64)) then
      t_2 = (c_1 < ((-1_int64) + 1099511627776_int64))
    else
      t_2 = .false.
    end if
    if (t_2) then
      call anl_grow_c(ls, c_1)
      call anl_s_cnm(ls, c_1, s_)
      call anl_s_cout(ls, c_1, k_)
      call anl_s_cin(ls, c_1, slot_)
      call anl_s_cbx(ls, c_1, bx_)
      call anl_s_cnext(ls, c_1, anl_g_fcap(ls, f_))
      ls%nc = (1_int64 + c_1)
      call anl_s_fcap(ls, f_, c_1)
      call anl_push_n(ls, f_, s_, slot_)
    else
      ls%err = 1_int64
    end if
  end subroutine anl_push_c

  recursive subroutine anl_lookup(ls, b_, s_, r1, r2)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    integer(int64), value :: s_
    integer(int64), intent(out) :: r1
    integer(int64), intent(out) :: r2
    integer(int64) :: bx_11
    integer(int64) :: c_7
    integer(int64) :: f_2
    integer(int64) :: k_10
    integer(int64) :: mv_8
    integer(int64) :: mv_9
    integer(int64) :: o_3
    integer(int64) :: slot_12
    logical :: t_13
    logical :: t_4
    logical :: t_5
    logical :: t_6
    integer(int64) :: x_1
    x_1 = anl_chain_find(ls, b_, s_)
    if ((.not. (x_1 < 0_int64))) then
      r1 = anl_g_xsl(ls, x_1)
      r2 = x_1
    else
      f_2 = anl_g_bfn(ls, b_)
      o_3 = anl_g_fout(ls, f_2)
      if ((b_ >= 0_int64)) then
        if ((o_3 >= 0_int64)) then
          if ((o_3 < b_)) then
            t_4 = (anl_g_bfn(ls, o_3) < f_2)
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
      if (t_6) then
        c_7 = anl_cfind(ls, anl_g_fcap(ls, f_2), s_)
        if ((.not. (c_7 < 0_int64))) then
          r1 = anl_g_cin(ls, c_7)
          r2 = anl_g_cbx(ls, c_7)
        else
          call anl_lookup(ls, o_3, s_, mv_8, mv_9)
          k_10 = mv_8
          bx_11 = mv_9
          if ((bx_11 < 0_int64)) then
            r1 = (-1_int64)
            r2 = (-1_int64)
          else
            slot_12 = anl_g_fctr(ls, f_2)
            if ((slot_12 >= 0_int64)) then
              t_13 = (slot_12 < ((-1_int64) + 1099511627776_int64))
            else
              t_13 = .false.
            end if
            if (t_13) then
              call anl_s_fctr(ls, f_2, (1_int64 + slot_12))
              call anl_push_c(ls, f_2, s_, k_10, slot_12, bx_11)
              r1 = slot_12
              r2 = bx_11
            else
              ls%err = 1_int64
              r1 = (-1_int64)
              r2 = (-1_int64)
            end if
          end if
        end if
      else
        r1 = (-1_int64)
        r2 = (-1_int64)
      end if
    end if
  end subroutine anl_lookup

  recursive pure function anl_has_fixed(ls, a_, n_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: a_
    integer(int64), value :: n_
    logical :: r
    integer(int64) :: j_2
    logical :: t_1
    logical :: t_3
    logical :: t_4
    if ((a_ >= 0_int64)) then
      t_1 = (a_ < ls%na)
    else
      t_1 = .false.
    end if
    if (t_1) then
      if ((anl_g_an(ls, a_) == n_)) then
        r = .true.
        return
      else
        j_2 = anl_g_anext(ls, a_)
        if ((j_2 >= 0_int64)) then
          t_3 = (j_2 < a_)
        else
          t_3 = .false.
        end if
        if (t_3) then
          t_4 = anl_has_fixed(ls, j_2, n_)
        else
          t_4 = .false.
        end if
        r = t_4
        return
      end if
    else
      r = .false.
      return
    end if
  end function anl_has_fixed

  recursive pure function anl_gt_fixed(ls, a_, n_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: a_
    integer(int64), value :: n_
    logical :: r
    integer(int64) :: j_2
    logical :: t_1
    logical :: t_3
    logical :: t_4
    if ((a_ >= 0_int64)) then
      t_1 = (a_ < ls%na)
    else
      t_1 = .false.
    end if
    if (t_1) then
      if ((n_ < anl_g_an(ls, a_))) then
        r = .true.
        return
      else
        j_2 = anl_g_anext(ls, a_)
        if ((j_2 >= 0_int64)) then
          t_3 = (j_2 < a_)
        else
          t_3 = .false.
        end if
        if (t_3) then
          t_4 = anl_gt_fixed(ls, j_2, n_)
        else
          t_4 = .false.
        end if
        r = t_4
        return
      end if
    else
      r = .false.
      return
    end if
  end function anl_gt_fixed

  subroutine anl_push_a(ls, f_, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: f_
    integer(int64), value :: n_
    integer(int64) :: a_1
    logical :: t_2
    a_1 = ls%na
    if ((a_1 >= 0_int64)) then
      t_2 = (a_1 < ((-1_int64) + 1099511627776_int64))
    else
      t_2 = .false.
    end if
    if (t_2) then
      call anl_grow_a(ls, a_1)
      call anl_s_an(ls, a_1, n_)
      call anl_s_anext(ls, a_1, anl_g_fah(ls, f_))
      ls%na = (1_int64 + a_1)
      call anl_s_fah(ls, f_, a_1)
    else
      ls%err = 1_int64
    end if
  end subroutine anl_push_a

  subroutine anl_arity(ls, b_, nreq_, rest_, r)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    integer(int64), value :: nreq_
    integer(int64), value :: rest_
    integer(int64), intent(out) :: r
    integer(int64) :: f_1
    f_1 = anl_g_bfn(ls, b_)
    if ((.not. (f_1 >= 0_int64))) then
      ls%err = 1_int64
      r = 0_int64
    else
      if ((rest_ == 1_int64)) then
        if ((.not. (anl_g_fvar(ls, f_1) < 0_int64))) then
          r = 10_int64
        else
          call anl_s_fvar(ls, f_1, nreq_)
          r = 0_int64
        end if
      else
        if (anl_has_fixed(ls, anl_g_fah(ls, f_1), nreq_)) then
          r = 11_int64
        else
          call anl_push_a(ls, f_1, nreq_)
          r = 0_int64
        end if
      end if
    end if
  end subroutine anl_arity

  pure function anl_arity_end(ls, b_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: b_
    integer(int64) :: r
    integer(int64) :: f_1
    logical :: t_3
    integer(int64) :: t_4
    integer(int64) :: v_2
    f_1 = anl_g_bfn(ls, b_)
    v_2 = anl_g_fvar(ls, f_1)
    if ((.not. (v_2 < 0_int64))) then
      t_3 = anl_gt_fixed(ls, anl_g_fah(ls, f_1), v_2)
    else
      t_3 = .false.
    end if
    if (t_3) then
      t_4 = 12_int64
    else
      t_4 = 0_int64
    end if
    r = t_4
    return
  end function anl_arity_end

  pure function anl_ev_find(ls, i_, s_) result(r)
    type(anl_state), intent(in) :: ls
    integer(int64), value :: i_
    integer(int64), value :: s_
    integer(int64) :: r
    integer(int64) :: i_3
    integer(int64) :: s_4
    logical :: t_1
    logical :: t_2
    do
      if ((i_ >= 0_int64)) then
        if ((ls%nev >= 0_int64)) then
          t_1 = (i_ < ls%nev)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        if ((anl_g_ev(ls, i_) == s_)) then
          r = i_
          return
        else
          i_3 = (1_int64 + i_)
          s_4 = s_
          i_ = i_3
          s_ = s_4
          cycle
        end if
      else
        r = (-1_int64)
        return
      end if
    end do
  end function anl_ev_find

  subroutine anl_push_e(ls, s_, k_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: s_
    integer(int64), value :: k_
    integer(int64) :: n_1
    logical :: t_2
    n_1 = ls%nev
    if ((n_1 >= 0_int64)) then
      t_2 = (n_1 < ((-1_int64) + 1099511627776_int64))
    else
      t_2 = .false.
    end if
    if (t_2) then
      call anl_grow_e(ls, n_1)
      call anl_s_ev(ls, n_1, s_)
      call anl_s_es(ls, n_1, k_)
      ls%nev = (1_int64 + n_1)
    else
      ls%err = 1_int64
    end if
  end subroutine anl_push_e

  subroutine anl_env_put(ls, s_, k_, lo_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: s_
    integer(int64), value :: k_
    integer(int64), value :: lo_
    integer(int64) :: i_1
    i_1 = anl_ev_find(ls, 0_int64, s_)
    if ((i_1 < 0_int64)) then
      call anl_push_e(ls, s_, k_)
    else
      if ((.not. (i_1 < lo_))) then
        call anl_s_es(ls, i_1, k_)
      else
      end if
    end if
  end subroutine anl_env_put

  recursive subroutine anl_env_x(ls, x_, lo_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: x_
    integer(int64), value :: lo_
    integer(int64) :: j_2
    logical :: t_1
    logical :: t_3
    if ((x_ >= 0_int64)) then
      t_1 = (x_ < ls%nx)
    else
      t_1 = .false.
    end if
    if (t_1) then
      j_2 = anl_g_xnext(ls, x_)
      if ((j_2 >= 0_int64)) then
        t_3 = (j_2 < x_)
      else
        t_3 = .false.
      end if
      if (t_3) then
        call anl_env_x(ls, j_2, lo_)
      else
      end if
      call anl_env_put(ls, anl_g_xnm(ls, x_), anl_g_xsl(ls, x_), lo_)
    else
    end if
  end subroutine anl_env_x

  recursive subroutine anl_env_c(ls, c_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: c_
    integer(int64) :: j_2
    integer(int64) :: s_4
    logical :: t_1
    logical :: t_3
    if ((c_ >= 0_int64)) then
      t_1 = (c_ < ls%nc)
    else
      t_1 = .false.
    end if
    if (t_1) then
      j_2 = anl_g_cnext(ls, c_)
      if ((j_2 >= 0_int64)) then
        t_3 = (j_2 < c_)
      else
        t_3 = .false.
      end if
      if (t_3) then
        call anl_env_c(ls, j_2)
      else
      end if
      s_4 = anl_g_cnm(ls, c_)
      if ((.not. (anl_ev_find(ls, 0_int64, s_4) < 0_int64))) then
      else
        call anl_push_e(ls, s_4, anl_g_cin(ls, c_))
      end if
    else
    end if
  end subroutine anl_env_c

  subroutine anl_env_b(ls, b_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    integer(int64) :: b_4
    integer(int64) :: p_2
    logical :: t_1
    logical :: t_3
    do
      if ((b_ >= 0_int64)) then
        t_1 = (b_ < ls%nb)
      else
        t_1 = .false.
      end if
      if (t_1) then
        call anl_env_x(ls, anl_g_bhead(ls, b_), ls%nev)
        p_2 = anl_g_bpar(ls, b_)
        if ((p_2 >= 0_int64)) then
          t_3 = (p_2 < b_)
        else
          t_3 = .false.
        end if
        if (t_3) then
          b_4 = p_2
          b_ = b_4
          cycle
        else
        end if
      else
      end if
      exit
    end do
  end subroutine anl_env_b

  subroutine anl_env_from(ls, b_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    integer(int64) :: b_6
    integer(int64) :: f_1
    integer(int64) :: o_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    do
      call anl_env_b(ls, b_)
      f_1 = anl_g_bfn(ls, b_)
      call anl_env_c(ls, anl_g_fcap(ls, f_1))
      o_2 = anl_g_fout(ls, f_1)
      if ((b_ >= 0_int64)) then
        if ((o_2 >= 0_int64)) then
          if ((o_2 < b_)) then
            t_3 = (anl_g_bfn(ls, o_2) < f_1)
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
      if (t_5) then
        b_6 = o_2
        b_ = b_6
        cycle
      else
      end if
      exit
    end do
  end subroutine anl_env_from

  subroutine anl_env(ls, b_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    ls%nev = 0_int64
    call anl_env_from(ls, b_)
  end subroutine anl_env

  subroutine anl_caps_c(ls, c_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: c_
    integer(int64) :: c_4
    integer(int64) :: j_2
    logical :: t_1
    logical :: t_3
    do
      if ((c_ >= 0_int64)) then
        t_1 = (c_ < ls%nc)
      else
        t_1 = .false.
      end if
      if (t_1) then
        call anl_push_e(ls, anl_g_cout(ls, c_), anl_g_cin(ls, c_))
        j_2 = anl_g_cnext(ls, c_)
        if ((j_2 >= 0_int64)) then
          t_3 = (j_2 < c_)
        else
          t_3 = .false.
        end if
        if (t_3) then
          c_4 = j_2
          c_ = c_4
          cycle
        else
        end if
      else
      end if
      exit
    end do
  end subroutine anl_caps_c

  subroutine anl_caps_of(ls, b_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    integer(int64) :: c_1
    c_1 = anl_g_fcap(ls, anl_g_bfn(ls, b_))
    ls%nev = 0_int64
    call anl_caps_c(ls, c_1)
  end subroutine anl_caps_of

  subroutine anl_names_n(ls, n_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: n_
    integer(int64) :: j_2
    integer(int64) :: n_4
    logical :: t_1
    logical :: t_3
    do
      if ((n_ >= 0_int64)) then
        t_1 = (n_ < ls%nn)
      else
        t_1 = .false.
      end if
      if (t_1) then
        call anl_push_e(ls, anl_g_nnm(ls, n_), anl_g_nsl(ls, n_))
        j_2 = anl_g_nnext(ls, n_)
        if ((j_2 >= 0_int64)) then
          t_3 = (j_2 < n_)
        else
          t_3 = .false.
        end if
        if (t_3) then
          n_4 = j_2
          n_ = n_4
          cycle
        else
        end if
      else
      end if
      exit
    end do
  end subroutine anl_names_n

  subroutine anl_names_of(ls, b_)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b_
    integer(int64) :: n_1
    n_1 = anl_g_fnl(ls, anl_g_bfn(ls, b_))
    ls%nev = 0_int64
    call anl_names_n(ls, n_1)
  end subroutine anl_names_of
