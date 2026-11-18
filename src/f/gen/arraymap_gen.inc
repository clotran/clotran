  ! GENERATED from model/arraymapg.lisp by scripts/acl2-fortran -b arraymapg. Do not
  ! edit: change the model, prove it, and generate again. Included in
  ! PersistentArrayMap.f90's contains part: the array map's reads -- index_of's
  ! scan, get, the positional reads -- and the writes assoc and dissoc make into
  ! the runs they allocate (copy_run's loop, dissoc's close-up or swap, the value
  ! set or the pair appended), guard-verified, through GC.f90's hp_* accessors.
  ! arraymapg.lisp proves each is arraymap's on the map the heap holds
  ! (amg-index-refines, amg-get-refines, amg-contains-refines, amg-at-refines,
  ! amg-assoc-fill-refines, amg-dissoc-fill-refines), gc_equal named (amg-keq-ok),
  ! the allocation named (amg-fresh: the shim's gc_vec), the barrier the shim's.
  pure function hpg_ot(hs, j_) result(r)
    type(amg_heap), intent(in) :: hs
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
    type(amg_heap), intent(in) :: hs
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
    type(amg_heap), intent(in) :: hs
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
    type(amg_heap), intent(in) :: hs
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
    type(amg_heap), intent(in) :: hs
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

  pure function amg_voff(hs, v_) result(r)
    type(amg_heap), intent(in) :: hs
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
  end function amg_voff

  pure function amg_vlen(hs, v_) result(r)
    type(amg_heap), intent(in) :: hs
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
  end function amg_vlen

  pure function amg_wt(hs, w_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: w_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((0_int64 < w_)) then
        t_1 = (w_ < hp_n_arena())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_atag(w_)
      return
    else
      r = 0_int64
      return
    end if
  end function amg_wt

  pure function amg_wr(hs, w_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: w_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((0_int64 < w_)) then
        t_1 = (w_ < hp_n_arena())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_aref(w_)
      return
    else
      r = 0_int64
      return
    end if
  end function amg_wr

  pure function amg_wv(hs, w_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: w_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((0_int64 < w_)) then
        t_1 = (w_ < hp_n_arena())
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = hp_aival(w_)
      return
    else
      r = 0_int64
      return
    end if
  end function amg_wv

  pure function amg_roff(hs, s_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: s_
    integer(int64) :: r
    if ((hpg_ot(hs, s_) == 9_int64)) then
      r = amg_voff(hs, hpg_or(hs, s_))
      return
    else
      r = 0_int64
      return
    end if
  end function amg_roff

  pure function amg_rlen(hs, s_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: s_
    integer(int64) :: r
    if ((hpg_ot(hs, s_) == 9_int64)) then
      r = amg_vlen(hs, hpg_or(hs, s_))
      return
    else
      r = 0_int64
      return
    end if
  end function amg_rlen

  function amg_kat(hs, kt_, kr_, kv_, off_, len_, i_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: kt_
    integer(int64), value :: kr_
    integer(int64), value :: kv_
    integer(int64), value :: off_
    integer(int64), value :: len_
    integer(int64), value :: i_
    logical :: r
    integer(int64) :: w_1
    w_1 = amg_w(off_, len_, i_)
    r = am_keq(kt_, kr_, kv_, amg_wt(hs, w_1), amg_wr(hs, w_1), amg_wv(hs, w_1))
    return
  end function amg_kat

  pure function amg_w(off_, len_, i_) result(r)
    integer(int64), value :: off_
    integer(int64), value :: len_
    integer(int64), value :: i_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if ((i_ < len_)) then
      if ((0_int64 < off_)) then
        t_1 = (off_ < 1099511627776_int64)
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = (off_ + i_)
      return
    else
      r = (-1_int64)
      return
    end if
  end function amg_w

  pure function amg_place(w_) result(r)
    integer(int64), value :: w_
    integer(int64) :: r
    if ((w_ < 0_int64)) then
      r = 0_int64
      return
    else
      r = ((-1_int64) + (-w_))
      return
    end if
  end function amg_place

  pure function amg_map(hs, tag_, ref_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    logical :: r
    if (hpg_obj_at(hs, tag_, ref_)) then
      r = (hpg_okd(hs, ref_) == 3_int64)
      return
    else
      r = .false.
      return
    end if
  end function amg_map

  function amg_index_from(hs, kt_, kr_, kv_, off_, len_, i_, n_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: kt_
    integer(int64), value :: kr_
    integer(int64), value :: kv_
    integer(int64), value :: off_
    integer(int64), value :: len_
    integer(int64), value :: i_
    integer(int64), value :: n_
    integer(int64) :: r
    integer(int64) :: i_8
    integer(int64) :: kr_4
    integer(int64) :: kt_3
    integer(int64) :: kv_5
    integer(int64) :: len_7
    integer(int64) :: n_9
    integer(int64) :: off_6
    logical :: t_1
    logical :: t_2
    do
      if ((i_ >= 0_int64)) then
        if ((i_ < n_)) then
          t_1 = (i_ < 1099511627776_int64)
        else
          t_1 = .false.
        end if
        t_2 = t_1
      else
        t_2 = .false.
      end if
      if (t_2) then
        if (amg_kat(hs, kt_, kr_, kv_, off_, len_, i_)) then
          r = (1_int64 + i_)
          return
        else
          kt_3 = kt_
          kr_4 = kr_
          kv_5 = kv_
          off_6 = off_
          len_7 = len_
          i_8 = (1_int64 + i_)
          n_9 = n_
          kt_ = kt_3
          kr_ = kr_4
          kv_ = kv_5
          off_ = off_6
          len_ = len_7
          i_ = i_8
          n_ = n_9
          cycle
        end if
      else
        r = 0_int64
        return
      end if
    end do
  end function amg_index_from

  function amg_index(hs, tag_, ref_, kt_, kr_, kv_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64), value :: kt_
    integer(int64), value :: kr_
    integer(int64), value :: kv_
    integer(int64) :: r
    integer(int64) :: s_1
    if (amg_map(hs, tag_, ref_)) then
      s_1 = (5_int64 * ref_)
      r = amg_index_from(hs, kt_, kr_, kv_, amg_roff(hs, s_1), amg_rlen(hs, s_1), 0_int64, hpg_oi(hs, ref_))
      return
    else
      r = 0_int64
      return
    end if
  end function amg_index

  pure function amg_at(hs, tag_, ref_, k_, i_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64), value :: k_
    integer(int64), value :: i_
    integer(int64) :: r
    integer(int64) :: s_6
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    if (amg_map(hs, tag_, ref_)) then
      if ((0_int64 < i_)) then
        if ((.not. (hpg_oi(hs, ref_) < i_))) then
          if ((.not. (1099511627776_int64 < i_))) then
            if ((k_ == 0_int64)) then
              t_1 = (k_ == 0_int64)
            else
              t_1 = (k_ == 1_int64)
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
    if (t_5) then
      s_6 = (k_ + (5_int64 * ref_))
      r = amg_place(amg_w(amg_roff(hs, s_6), amg_rlen(hs, s_6), ((-1_int64) + i_)))
      return
    else
      r = 0_int64
      return
    end if
  end function amg_at

  function amg_get(hs, tag_, ref_, kt_, kr_, kv_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64), value :: kt_
    integer(int64), value :: kr_
    integer(int64), value :: kv_
    integer(int64) :: r
    integer(int64) :: at_1
    integer(int64) :: t_2
    at_1 = amg_index(hs, tag_, ref_, kt_, kr_, kv_)
    if ((at_1 == 0_int64)) then
      t_2 = 0_int64
    else
      t_2 = amg_at(hs, tag_, ref_, 1_int64, at_1)
    end if
    r = t_2
    return
  end function amg_get

  pure function amg_in(hs, w_) result(r)
    type(amg_heap), intent(in) :: hs
    integer(int64), value :: w_
    logical :: r
    if ((0_int64 < w_)) then
      if ((w_ < hp_n_arena())) then
        if ((w_ < hp_n_arena())) then
          r = (w_ < hp_n_arena())
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
  end function amg_in

  subroutine amg_put(hs, off_, len_, i_, wt_, wr_, wv_)
    type(amg_heap), intent(inout) :: hs
    integer(int64), value :: off_
    integer(int64), value :: len_
    integer(int64), value :: i_
    integer(int64), value :: wt_
    integer(int64), value :: wr_
    integer(int64), value :: wv_
    integer(int64) :: i_2
    integer(int64) :: i_4
    integer(int64) :: i_6
    integer(int64) :: v_3
    integer(int64) :: v_5
    integer(int64) :: v_7
    integer(int64) :: w_1
    w_1 = amg_w(off_, len_, i_)
    if (amg_in(hs, w_1)) then
      i_2 = w_1
      v_3 = wt_
      call hp_set_atag(i_2, v_3)
      i_4 = w_1
      v_5 = wr_
      call hp_set_aref(i_4, v_5)
      i_6 = w_1
      v_7 = wv_
      call hp_set_aival(i_6, v_7)
    else
    end if
  end subroutine amg_put

  subroutine amg_mv(hs, soff_, slen_, j_, doff_, dlen_, i_)
    type(amg_heap), intent(inout) :: hs
    integer(int64), value :: soff_
    integer(int64), value :: slen_
    integer(int64), value :: j_
    integer(int64), value :: doff_
    integer(int64), value :: dlen_
    integer(int64), value :: i_
    integer(int64) :: w_1
    w_1 = amg_w(soff_, slen_, j_)
    call amg_put(hs, doff_, dlen_, i_, amg_wt(hs, w_1), amg_wr(hs, w_1), amg_wv(hs, w_1))
  end subroutine amg_mv

  subroutine amg_copy(hs, soff_, slen_, doff_, dlen_, d_, i_, n_)
    type(amg_heap), intent(inout) :: hs
    integer(int64), value :: soff_
    integer(int64), value :: slen_
    integer(int64), value :: doff_
    integer(int64), value :: dlen_
    integer(int64), value :: d_
    integer(int64), value :: i_
    integer(int64), value :: n_
    integer(int64) :: d_9
    integer(int64) :: dlen_8
    integer(int64) :: doff_7
    integer(int64) :: i_10
    integer(int64) :: n_11
    integer(int64) :: slen_6
    integer(int64) :: soff_5
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    do
      if ((i_ >= 0_int64)) then
        if ((i_ < n_)) then
          if ((n_ < 1099511627776_int64)) then
            if ((d_ == 0_int64)) then
              t_1 = (d_ == 0_int64)
            else
              t_1 = (d_ == 1_int64)
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
        call amg_mv(hs, soff_, slen_, (i_ + d_), doff_, dlen_, i_)
        soff_5 = soff_
        slen_6 = slen_
        doff_7 = doff_
        dlen_8 = dlen_
        d_9 = d_
        i_10 = (1_int64 + i_)
        n_11 = n_
        soff_ = soff_5
        slen_ = slen_6
        doff_ = doff_7
        dlen_ = dlen_8
        d_ = d_9
        i_ = i_10
        n_ = n_11
        cycle
      else
      end if
      exit
    end do
  end subroutine amg_copy

  subroutine amg_assoc_w(hs, ko_, kl_, vo_, vl_, nko_, nkl_, nvo_, nvl_, n_, at_, kt_, kr_, kv_, vt_, vr_, vv_)
    type(amg_heap), intent(inout) :: hs
    integer(int64), value :: ko_
    integer(int64), value :: kl_
    integer(int64), value :: vo_
    integer(int64), value :: vl_
    integer(int64), value :: nko_
    integer(int64), value :: nkl_
    integer(int64), value :: nvo_
    integer(int64), value :: nvl_
    integer(int64), value :: n_
    integer(int64), value :: at_
    integer(int64), value :: kt_
    integer(int64), value :: kr_
    integer(int64), value :: kv_
    integer(int64), value :: vt_
    integer(int64), value :: vr_
    integer(int64), value :: vv_
    logical :: t_1
    call amg_copy(hs, ko_, kl_, nko_, nkl_, 0_int64, 0_int64, n_)
    call amg_copy(hs, vo_, vl_, nvo_, nvl_, 0_int64, 0_int64, n_)
    if ((at_ == 0_int64)) then
      call amg_put(hs, nko_, nkl_, n_, kt_, kr_, kv_)
      call amg_put(hs, nvo_, nvl_, n_, vt_, vr_, vv_)
    else
      if ((0_int64 < at_)) then
        t_1 = (.not. (n_ < at_))
      else
        t_1 = .false.
      end if
      if (t_1) then
        call amg_put(hs, nvo_, nvl_, ((-1_int64) + at_), vt_, vr_, vv_)
      else
      end if
    end if
  end subroutine amg_assoc_w

  subroutine amg_assoc_fill(hs, ref_, at_, kt_, kr_, kv_, vt_, vr_, vv_, kq_, vq_)
    type(amg_heap), intent(inout) :: hs
    integer(int64), value :: ref_
    integer(int64), value :: at_
    integer(int64), value :: kt_
    integer(int64), value :: kr_
    integer(int64), value :: kv_
    integer(int64), value :: vt_
    integer(int64), value :: vr_
    integer(int64), value :: vv_
    integer(int64), value :: kq_
    integer(int64), value :: vq_
    integer(int64) :: n_1
    integer(int64) :: s_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    n_1 = hpg_oi(hs, ref_)
    s_2 = (5_int64 * ref_)
    if ((.not. (ref_ < 0_int64))) then
      if ((ref_ < 1099511627776_int64)) then
        if ((.not. (n_1 < 0_int64))) then
          t_3 = ((1_int64 + n_1) < 1099511627776_int64)
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
      call amg_assoc_w(hs, amg_roff(hs, s_2), amg_rlen(hs, s_2), amg_roff(hs, (1_int64 + s_2)), amg_rlen(hs, (1_int64 + s_2)), amg_voff(hs, kq_), amg_vlen(hs, kq_), amg_voff(hs, vq_), amg_vlen(hs, vq_), n_1, at_, kt_, kr_, kv_, vt_, vr_, vv_)
    else
    end if
  end subroutine amg_assoc_fill

  subroutine amg_dissoc_w(hs, ko_, kl_, vo_, vl_, nko_, nkl_, nvo_, nvl_, n_, at_, sw_)
    type(amg_heap), intent(inout) :: hs
    integer(int64), value :: ko_
    integer(int64), value :: kl_
    integer(int64), value :: vo_
    integer(int64), value :: vl_
    integer(int64), value :: nko_
    integer(int64), value :: nkl_
    integer(int64), value :: nvo_
    integer(int64), value :: nvl_
    integer(int64), value :: n_
    integer(int64), value :: at_
    integer(int64), value :: sw_
    call amg_copy(hs, ko_, kl_, nko_, nkl_, 0_int64, 0_int64, ((-1_int64) + n_))
    call amg_copy(hs, vo_, vl_, nvo_, nvl_, 0_int64, 0_int64, ((-1_int64) + n_))
    if ((.not. (sw_ == 0_int64))) then
      if ((at_ == n_)) then
      else
        call amg_mv(hs, ko_, kl_, ((-1_int64) + n_), nko_, nkl_, ((-1_int64) + at_))
        call amg_mv(hs, vo_, vl_, ((-1_int64) + n_), nvo_, nvl_, ((-1_int64) + at_))
      end if
    else
      call amg_copy(hs, ko_, kl_, nko_, nkl_, 1_int64, ((-1_int64) + at_), ((-1_int64) + n_))
      call amg_copy(hs, vo_, vl_, nvo_, nvl_, 1_int64, ((-1_int64) + at_), ((-1_int64) + n_))
    end if
  end subroutine amg_dissoc_w

  subroutine amg_dissoc_fill(hs, ref_, at_, sw_, kq_, vq_)
    type(amg_heap), intent(inout) :: hs
    integer(int64), value :: ref_
    integer(int64), value :: at_
    integer(int64), value :: sw_
    integer(int64), value :: kq_
    integer(int64), value :: vq_
    integer(int64) :: n_1
    integer(int64) :: s_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    n_1 = hpg_oi(hs, ref_)
    s_2 = (5_int64 * ref_)
    if ((.not. (ref_ < 0_int64))) then
      if ((ref_ < 1099511627776_int64)) then
        if ((0_int64 < at_)) then
          if ((.not. (n_1 < at_))) then
            t_3 = ((1_int64 + n_1) < 1099511627776_int64)
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
    if (t_6) then
      call amg_dissoc_w(hs, amg_roff(hs, s_2), amg_rlen(hs, s_2), amg_roff(hs, (1_int64 + s_2)), amg_rlen(hs, (1_int64 + s_2)), amg_voff(hs, kq_), amg_vlen(hs, kq_), amg_voff(hs, vq_), amg_vlen(hs, vq_), n_1, at_, sw_)
    else
    end if
  end subroutine amg_dissoc_fill
