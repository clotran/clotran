  ! GENERATED from model/vmrt.lisp by scripts/acl2-fortran -b vmrt. Do not edit:
  ! change the model, prove it, and generate again. Included in VmRuntime.f90's
  ! contains part: what the VM's runtime operations answer on clotran's values,
  ! guard-verified, reading GC.f90's pools through its accessors and writing
  ! nothing. vmrt.lisp proves each agrees with the machine's rt-* (model/vmg.lisp,
  ! vmic.lisp) on the value decoded: vrt-truthy-agrees, vrt-throwp-agrees,
  ! vrt-clop-agrees, vrt-capt-agrees and the rest.
  pure function vrt_oiv(vx, j_) result(r)
    type(vrt_aux), intent(in) :: vx
    integer(int64), value :: j_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (j_ < 0_int64))) then
        t_1 = (j_ < hp_n_oslot())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_oival(j_)
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_oiv

  pure function vrt_oi2(vx, o_) result(r)
    type(vrt_aux), intent(in) :: vx
    integer(int64), value :: o_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (o_ < 0_int64))) then
        t_1 = (o_ < hp_n_obj())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_oi2(o_)
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_oi2

  pure function vrt_voff(hs, v_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: v_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (v_ < 0_int64))) then
        t_1 = (v_ < hp_n_vec())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_voff(v_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function vrt_voff

  pure function vrt_vlen(hs, v_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: v_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (v_ < 0_int64))) then
        t_1 = (v_ < hp_n_vec())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_vlen(v_)
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_vlen

  pure function vrt_at(hs, j_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: j_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (j_ < 0_int64))) then
        t_1 = (j_ < hp_n_arena())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_atag(j_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function vrt_at

  pure function vrt_av(hs, j_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: j_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (j_ < 0_int64))) then
        t_1 = (j_ < hp_n_arena())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_aival(j_)
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_av

  pure function hpg_ot(hs, j_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: j_
    integer(int64) :: r
    logical :: t_1
    if ((.not. (j_ < 0_int64))) then
      t_1 = (j_ < hp_n_oslot())
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = hp_otag(j_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function hpg_ot

  pure function hpg_or(hs, j_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: j_
    integer(int64) :: r
    logical :: t_1
    if ((.not. (j_ < 0_int64))) then
      t_1 = (j_ < hp_n_oslot())
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = hp_oref(j_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function hpg_or

  pure function hpg_okd(hs, o_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: o_
    integer(int64) :: r
    logical :: t_1
    if ((.not. (o_ < 0_int64))) then
      t_1 = (o_ < hp_n_obj())
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = hp_okind(o_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function hpg_okd

  pure function hpg_oi(hs, o_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: o_
    integer(int64) :: r
    logical :: t_1
    if ((.not. (o_ < 0_int64))) then
      t_1 = (o_ < hp_n_obj())
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = hp_oi1(o_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function hpg_oi

  pure function hpg_obj_at(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    logical :: r
    if ((tag_ == 8_int64)) then
      if ((0_int64 < ref_)) then
        if ((ref_ < 1099511627776_int64)) then
          if (((4_int64 + (5_int64 * ref_)) < hp_n_oslot())) then
            r = ((4_int64 + (5_int64 * ref_)) < hp_n_oslot())
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
  end function hpg_obj_at

  pure function vrt_truthy(tag_, ival_) result(r)
    integer(int64), value :: tag_
    integer(int64), value :: ival_
    logical :: r
    logical :: t_1
    logical :: t_2
    if ((tag_ == 0_int64)) then
      t_2 = (tag_ == 0_int64)
    else
      if ((tag_ == 1_int64)) then
        t_1 = (ival_ == 0_int64)
      else
        t_1 = .false.
      end if
      t_2 = t_1
    end if
    r = (.not. t_2)
    return
  end function vrt_truthy

  pure function vrt_nat(tag_, ival_) result(r)
    integer(int64), value :: tag_
    integer(int64), value :: ival_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if ((tag_ == 2_int64)) then
      if ((.not. (ival_ < 0_int64))) then
        t_1 = (ival_ < 2147483648_int64)
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = ival_
      return
    else
      r = (-1_int64)
      return
    end if
  end function vrt_nat

  pure function vrt_ifix(tag_, ival_) result(r)
    integer(int64), value :: tag_
    integer(int64), value :: ival_
    integer(int64) :: r
    if ((tag_ == 2_int64)) then
      r = ival_
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_ifix

  pure function vrt_lt(ta_, ia_, tb_, ib_) result(r)
    integer(int64), value :: ta_
    integer(int64), value :: ia_
    integer(int64), value :: tb_
    integer(int64), value :: ib_
    logical :: r
    r = (vrt_ifix(ta_, ia_) < vrt_ifix(tb_, ib_))
    return
  end function vrt_lt

  pure function vrt_add_fits(a_, b_) result(r)
    integer(int64), value :: a_
    integer(int64), value :: b_
    logical :: r
    if ((0_int64 < b_)) then
      r = (.not. ((9223372036854775807_int64 + (-b_)) < a_))
      return
    else
      r = (.not. (a_ < ((-9223372036854775807_int64) + (-(b_ + 1_int64)))))
      return
    end if
  end function vrt_add_fits

  pure function vrt_add(ta_, ia_, tb_, ib_) result(r)
    integer(int64), value :: ta_
    integer(int64), value :: ia_
    integer(int64), value :: tb_
    integer(int64), value :: ib_
    integer(int64) :: r
    integer(int64) :: a_1
    integer(int64) :: b_2
    integer(int64) :: t_3
    a_1 = vrt_ifix(ta_, ia_)
    b_2 = vrt_ifix(tb_, ib_)
    if (vrt_add_fits(a_1, b_2)) then
      t_3 = (a_1 + b_2)
    else
      t_3 = 0_int64
    end if
    r = t_3
    return
  end function vrt_add

  pure function vrt_lcount(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if (hpg_obj_at(hs, tag_, ref_)) then
        t_1 = (hpg_okd(hs, ref_) == 1_int64)
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hpg_oi(hs, ref_)
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_lcount

  pure function vrt_consp(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    logical :: r
    r = (0_int64 < vrt_lcount(hs, tag_, ref_))
    return
  end function vrt_consp

  pure function vrt_len(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    integer(int64) :: n_1
    integer(int64) :: t_2
    n_1 = vrt_lcount(hs, tag_, ref_)
    if ((0_int64 < n_1)) then
      t_2 = n_1
    else
      t_2 = 0_int64
    end if
    r = t_2
    return
  end function vrt_len

  pure function vrt_car_place(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    if (vrt_consp(hs, tag_, ref_)) then
      r = (5_int64 * ref_)
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_car_place

  pure function vrt_cdr_place(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    if ((1_int64 < vrt_lcount(hs, tag_, ref_))) then
      r = (1_int64 + (5_int64 * ref_))
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_cdr_place

  pure function vrt_car_at(hs, w_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: w_
    integer(int64) :: r
    if ((.not. (w_ < 5_int64))) then
      r = vrt_car_place(hs, hpg_ot(hs, w_), hpg_or(hs, w_))
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_car_at

  pure function vrt_cdr_at(hs, w_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: w_
    integer(int64) :: r
    if ((.not. (w_ < 5_int64))) then
      r = vrt_cdr_place(hs, hpg_ot(hs, w_), hpg_or(hs, w_))
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_cdr_at

  pure function vrt_same_at(hs, w_, htag_, href_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: w_
    integer(int64), value :: htag_
    integer(int64), value :: href_
    logical :: r
    if ((.not. (w_ < 5_int64))) then
      if ((hpg_ot(hs, w_) == htag_)) then
        r = (hpg_or(hs, w_) == href_)
        return
      else
        r = .false.
        return
      end if
    else
      r = .false.
      return
    end if
  end function vrt_same_at

  pure function vrt_throwp(hs, tag_, ref_, ttag_, tref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64), value :: ttag_
    integer(int64), value :: tref_
    logical :: r
    if ((vrt_lcount(hs, tag_, ref_) == 2_int64)) then
      r = vrt_same_at(hs, vrt_car_place(hs, tag_, ref_), ttag_, tref_)
      return
    else
      r = .false.
      return
    end if
  end function vrt_throwp

  pure function vrt_clol(hs, tag_, ref_, ctag_, cref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64), value :: ctag_
    integer(int64), value :: cref_
    logical :: r
    if ((vrt_lcount(hs, tag_, ref_) == 3_int64)) then
      r = vrt_same_at(hs, vrt_car_place(hs, tag_, ref_), ctag_, cref_)
      return
    else
      r = .false.
      return
    end if
  end function vrt_clol

  pure function vrt_cadr_place(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    r = vrt_car_at(hs, vrt_cdr_place(hs, tag_, ref_))
    return
  end function vrt_cadr_place

  pure function vrt_caddr_place(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    r = vrt_car_at(hs, vrt_cdr_at(hs, vrt_cdr_place(hs, tag_, ref_)))
    return
  end function vrt_caddr_place

  pure function vrt_thrown_place(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    r = vrt_cadr_place(hs, tag_, ref_)
    return
  end function vrt_thrown_place

  pure function vrt_walk(hs, i_, w_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: i_
    integer(int64), value :: w_
    integer(int64) :: r
    integer(int64) :: i_1
    integer(int64) :: w_2
    do
      if ((i_ <= 0_int64)) then
        r = vrt_car_at(hs, w_)
        return
      else
        i_1 = ((-1_int64) + i_)
        w_2 = vrt_cdr_at(hs, w_)
        i_ = i_1
        w_ = w_2
        cycle
      end if
    end do
  end function vrt_walk

  pure function vrt_unmeta_k(hs, tag_, ref_, k_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64), value :: k_
    integer(int64) :: r
    integer(int64) :: k_4
    integer(int64) :: ref_3
    logical :: t_1
    integer(int64) :: tag_2
    do
      if (.true.) then
        t_1 = hpg_obj_at(hs, tag_, ref_)
      else
        t_1 = .false.
      end if
      if ((.not. t_1)) then
        r = 0_int64
        return
      else
        if ((k_ <= 0_int64)) then
          r = 0_int64
          return
        else
          if ((hpg_okd(hs, ref_) == 8_int64)) then
            tag_2 = hpg_ot(hs, (5_int64 * ref_))
            ref_3 = hpg_or(hs, (5_int64 * ref_))
            k_4 = ((-1_int64) + k_)
            tag_ = tag_2
            ref_ = ref_3
            k_ = k_4
            cycle
          else
            r = ref_
            return
          end if
        end if
      end if
    end do
  end function vrt_unmeta_k

  pure function vrt_nobj(hs) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64) :: r
    integer(int64) :: n_1
    integer(int64) :: t_2
    n_1 = hp_n_obj()
    if ((n_1 < 1099511627776_int64)) then
      t_2 = n_1
    else
      t_2 = 1099511627776_int64
    end if
    r = t_2
    return
  end function vrt_nobj

  pure function vrt_unmeta(hs, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    r = vrt_unmeta_k(hs, tag_, ref_, vrt_nobj(hs))
    return
  end function vrt_unmeta

  pure function vrt_env_at(hs, w_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: w_
    logical :: r
    if ((hpg_ot(hs, w_) == 8_int64)) then
      if ((0_int64 < hpg_or(hs, w_))) then
        r = (hpg_okd(hs, hpg_or(hs, w_)) == 7_int64)
        return
      else
        r = .false.
        return
      end if
    else
      r = .false.
      return
    end if
  end function vrt_env_at

  pure function vrt_ctab(hs, vx, r_) result(r)
    type(vrt_heap), intent(in) :: hs
    type(vrt_aux), intent(in) :: vx
    integer(int64), value :: r_
    integer(int64) :: r
    integer(int64) :: i2_4
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_5
    integer(int64) :: t_6
    if (.true.) then
      if ((0_int64 < r_)) then
        if ((r_ < 1099511627776_int64)) then
          t_1 = (hpg_okd(hs, r_) == 4_int64)
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
      i2_4 = vrt_oi2(vx, r_)
      if ((0_int64 < i2_4)) then
        t_5 = (.not. vrt_env_at(hs, (2_int64 + (5_int64 * r_))))
      else
        t_5 = .false.
      end if
      if (t_5) then
        t_6 = i2_4
      else
        t_6 = 0_int64
      end if
      r = t_6
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_ctab

  pure function vrt_reg(hs, ct_, k_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: ct_
    integer(int64), value :: k_
    integer(int64) :: r
    integer(int64) :: off_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    integer(int64) :: t_8
    off_1 = vrt_voff(hs, ct_)
    if (.true.) then
      if (.true.) then
        if ((0_int64 < ct_)) then
          if ((0_int64 < off_1)) then
            if ((off_1 < 1099511627776_int64)) then
              if ((0_int64 < k_)) then
                t_2 = (k_ < 1099511627776_int64)
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
      t_8 = (off_1 + ((-1_int64) + k_))
    else
      t_8 = (-1_int64)
    end if
    r = t_8
    return
  end function vrt_reg

  pure function vrt_reg_int(hs, ct_, k_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: ct_
    integer(int64), value :: k_
    integer(int64) :: r
    integer(int64) :: j_1
    integer(int64) :: t_2
    j_1 = vrt_reg(hs, ct_, k_)
    if ((.not. (j_1 < 0_int64))) then
      t_2 = vrt_av(hs, j_1)
    else
      t_2 = 0_int64
    end if
    r = t_2
    return
  end function vrt_reg_int

  pure function vrt_reg_tag(hs, ct_, k_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: ct_
    integer(int64), value :: k_
    integer(int64) :: r
    integer(int64) :: j_1
    integer(int64) :: t_2
    j_1 = vrt_reg(hs, ct_, k_)
    if ((.not. (j_1 < 0_int64))) then
      t_2 = vrt_at(hs, j_1)
    else
      t_2 = (-1_int64)
    end if
    r = t_2
    return
  end function vrt_reg_tag

  pure function vrt_tab_ok(hs, ct_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: ct_
    logical :: r
    integer(int64) :: kk_2
    integer(int64) :: nc_1
    logical :: t_3
    logical :: t_4
    logical :: t_5
    nc_1 = vrt_reg_int(hs, ct_, 3_int64)
    kk_2 = vrt_reg_int(hs, ct_, 4_int64)
    if ((.not. (nc_1 < 0_int64))) then
      if ((nc_1 < 2147483648_int64)) then
        if ((.not. (kk_2 < 0_int64))) then
          t_3 = (kk_2 < 2147483648_int64)
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
    r = t_5
    return
  end function vrt_tab_ok

  pure function vrt_fid_of(hs, ct_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: ct_
    integer(int64) :: r
    integer(int64) :: j_10
    integer(int64) :: kk_6
    integer(int64) :: nc_5
    integer(int64) :: off_1
    integer(int64) :: t_11
    integer(int64) :: t_12
    integer(int64) :: t_13
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_7
    logical :: t_8
    logical :: t_9
    off_1 = vrt_voff(hs, ct_)
    if (.true.) then
      if ((0_int64 < ct_)) then
        if ((0_int64 < off_1)) then
          t_2 = (off_1 < 1099511627776_int64)
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
      nc_5 = vrt_av(hs, (off_1 + 2_int64))
      kk_6 = vrt_av(hs, (off_1 + 3_int64))
      if ((.not. (nc_5 < 0_int64))) then
        if ((nc_5 < 2147483648_int64)) then
          if ((.not. (kk_6 < 0_int64))) then
            t_7 = (kk_6 < 2147483648_int64)
          else
            t_7 = .false.
          end if
          t_8 = t_7
        else
          t_8 = .false.
        end if
        t_9 = t_8
      else
        t_9 = .false.
      end if
      if (t_9) then
        j_10 = (off_1 + (4_int64 + ((4_int64 * (1_int64 + kk_6)) + nc_5)))
        if ((vrt_at(hs, j_10) == 2_int64)) then
          t_11 = vrt_av(hs, j_10)
        else
          t_11 = (-1_int64)
        end if
        t_12 = t_11
      else
        t_12 = (-1_int64)
      end if
      t_13 = t_12
    else
      t_13 = (-1_int64)
    end if
    r = t_13
    return
  end function vrt_fid_of

  pure function vrt_cfid(hs, vx, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    type(vrt_aux), intent(in) :: vx
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    integer(int64) :: ct_1
    integer(int64) :: f_2
    integer(int64) :: t_3
    integer(int64) :: t_4
    ct_1 = vrt_ctab(hs, vx, vrt_unmeta(hs, tag_, ref_))
    if ((0_int64 < ct_1)) then
      f_2 = vrt_fid_of(hs, ct_1)
      if ((.not. (f_2 < 0_int64))) then
        t_3 = f_2
      else
        t_3 = (-1_int64)
      end if
      t_4 = t_3
    else
      t_4 = (-1_int64)
    end if
    r = t_4
    return
  end function vrt_cfid

  pure function vrt_cncap(hs, vx, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    type(vrt_aux), intent(in) :: vx
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    r = vrt_reg_int(hs, vrt_ctab(hs, vx, vrt_unmeta(hs, tag_, ref_)), 3_int64)
    return
  end function vrt_cncap

  pure function vrt_clop(hs, vx, tag_, ref_, ctag_, cref_) result(r)
    type(vrt_heap), intent(in) :: hs
    type(vrt_aux), intent(in) :: vx
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64), value :: ctag_
    integer(int64), value :: cref_
    logical :: r
    if ((.not. (vrt_cfid(hs, vx, tag_, ref_) < 0_int64))) then
      r = (.not. (vrt_cfid(hs, vx, tag_, ref_) < 0_int64))
      return
    else
      r = vrt_clol(hs, tag_, ref_, ctag_, cref_)
      return
    end if
  end function vrt_clop

  pure function vrt_clo_f(hs, vx, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    type(vrt_aux), intent(in) :: vx
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    integer(int64) :: f_1
    logical :: t_3
    integer(int64) :: t_4
    integer(int64) :: t_5
    integer(int64) :: w_2
    f_1 = vrt_cfid(hs, vx, tag_, ref_)
    if ((.not. (f_1 < 0_int64))) then
      t_5 = f_1
    else
      w_2 = vrt_cadr_place(hs, tag_, ref_)
      if ((.not. (w_2 < 5_int64))) then
        t_3 = (hpg_ot(hs, w_2) == 2_int64)
      else
        t_3 = .false.
      end if
      if (t_3) then
        t_4 = vrt_oiv(vx, w_2)
      else
        t_4 = (-1_int64)
      end if
      t_5 = t_4
    end if
    r = t_5
    return
  end function vrt_clo_f

  pure function vrt_capt_place(hs, vx, i_, tag_, ref_) result(r)
    type(vrt_heap), intent(in) :: hs
    type(vrt_aux), intent(in) :: vx
    integer(int64), value :: i_
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: r
    integer(int64) :: n_1
    integer(int64) :: off_6
    integer(int64) :: r_2
    logical :: t_10
    logical :: t_11
    integer(int64) :: t_12
    integer(int64) :: t_13
    integer(int64) :: t_14
    integer(int64) :: t_15
    integer(int64) :: t_16
    integer(int64) :: t_17
    logical :: t_3
    logical :: t_7
    logical :: t_8
    logical :: t_9
    integer(int64) :: v_5
    integer(int64) :: w_4
    if ((.not. (vrt_cfid(hs, vx, tag_, ref_) < 0_int64))) then
      n_1 = vrt_cncap(hs, vx, tag_, ref_)
      r_2 = vrt_unmeta(hs, tag_, ref_)
      if ((n_1 < i_)) then
        t_17 = 0_int64
      else
        if ((i_ == n_1)) then
          t_16 = 1_int64
        else
          if ((0_int64 < r_2)) then
            t_3 = (r_2 < 1099511627776_int64)
          else
            t_3 = .false.
          end if
          if ((.not. t_3)) then
            t_15 = 0_int64
          else
            if ((2_int64 < n_1)) then
              w_4 = (1_int64 + (5_int64 * r_2))
              v_5 = hpg_or(hs, w_4)
              off_6 = vrt_voff(hs, v_5)
              if ((hpg_ot(hs, w_4) == 9_int64)) then
                if ((0_int64 < v_5)) then
                  if ((i_ < vrt_vlen(hs, v_5))) then
                    if ((0_int64 < off_6)) then
                      if ((off_6 < 1099511627776_int64)) then
                        t_7 = (i_ < 1099511627776_int64)
                      else
                        t_7 = .false.
                      end if
                      t_8 = t_7
                    else
                      t_8 = .false.
                    end if
                    t_9 = t_8
                  else
                    t_9 = .false.
                  end if
                  t_10 = t_9
                else
                  t_10 = .false.
                end if
                t_11 = t_10
              else
                t_11 = .false.
              end if
              if (t_11) then
                t_12 = ((-1_int64) + (-(off_6 + i_)))
              else
                t_12 = 0_int64
              end if
              t_14 = t_12
            else
              if ((i_ == 0_int64)) then
                t_13 = (1_int64 + (5_int64 * r_2))
              else
                t_13 = (3_int64 + (5_int64 * r_2))
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
      r = vrt_walk(hs, i_, vrt_caddr_place(hs, tag_, ref_))
      return
    end if
  end function vrt_capt_place

  pure function vrt_prim_kind(hs, tag_, ref_, karg_, kar_, kder_, kcw_, kinv_, kinvm_) result(r)
    type(vrt_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64), value :: karg_
    integer(int64), value :: kar_
    integer(int64), value :: kder_
    integer(int64), value :: kcw_
    integer(int64), value :: kinv_
    integer(int64), value :: kinvm_
    integer(int64) :: r
    integer(int64) :: k_2
    logical :: t_1
    integer(int64) :: t_3
    integer(int64) :: t_4
    logical :: t_5
    if ((tag_ == 8_int64)) then
      t_1 = (0_int64 < ref_)
    else
      t_1 = .false.
    end if
    if (t_1) then
      k_2 = hpg_okd(hs, ref_)
      if ((k_2 == 30_int64)) then
        t_4 = 6_int64
      else
        if ((k_2 == 13_int64)) then
          t_3 = 8_int64
        else
          t_3 = 7_int64
        end if
        t_4 = t_3
      end if
      r = t_4
      return
    else
      if ((.not. (tag_ == 7_int64))) then
        r = 7_int64
        return
      else
        if ((ref_ == karg_)) then
          r = 1_int64
          return
        else
          if ((ref_ == kar_)) then
            r = 2_int64
            return
          else
            if ((ref_ == kder_)) then
              r = 3_int64
              return
            else
              if ((ref_ == kcw_)) then
                r = 4_int64
                return
              else
                if ((ref_ == kinv_)) then
                  t_5 = (ref_ == kinv_)
                else
                  t_5 = (ref_ == kinvm_)
                end if
                if (t_5) then
                  r = 5_int64
                  return
                else
                  r = 7_int64
                  return
                end if
              end if
            end if
          end if
        end if
      end if
    end if
  end function vrt_prim_kind

  pure function vrt_arg_slot(n_, tag_, ival_, rb_, len_) result(r)
    integer(int64), value :: n_
    integer(int64), value :: tag_
    integer(int64), value :: ival_
    integer(int64), value :: rb_
    integer(int64), value :: len_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    if ((n_ == 1_int64)) then
      if ((tag_ == 2_int64)) then
        if ((.not. (ival_ < 0_int64))) then
          if ((.not. (rb_ < 0_int64))) then
            if ((len_ < 1099511627776_int64)) then
              if ((ival_ < len_)) then
                if ((rb_ < len_)) then
                  t_1 = ((rb_ + ival_) < len_)
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
      r = (rb_ + (ival_ + 1_int64))
      return
    else
      r = 0_int64
      return
    end if
  end function vrt_arg_slot
