  ! GENERATED from model/heapg.lisp by scripts/acl2-fortran -b heapg. Do not edit:
  ! change the model, prove it, and generate again (PLAN step 33). Included in
  ! GC.f90's contains part: the collector's marking, guard-verified, on GC's
  ! pools through its accessors. heapg-proof's hpg-drain-closed: a drain that
  ! empties its stack with no overflow leaves the mark set closed.
  pure function hpg_add(n_, k_) result(r)
    integer(int64), value :: n_
    integer(int64), value :: k_
    integer(int64) :: r
    integer(int64) :: s_1
    integer(int64) :: t_2
    s_1 = (max(0_int64, n_) + max(0_int64, k_))
    if ((s_1 < 1099511627776_int64)) then
      t_2 = s_1
    else
      t_2 = 1099511627776_int64
    end if
    r = t_2
    return
  end function hpg_add

  pure function hpg_text_tag(tag_) result(r)
    integer(int64), value :: tag_
    logical :: r
    if ((tag_ == 5_int64)) then
      r = (tag_ == 5_int64)
      return
    else
      if ((tag_ == 6_int64)) then
        r = (tag_ == 6_int64)
        return
      else
        if ((tag_ == 7_int64)) then
          r = (tag_ == 7_int64)
          return
        else
          if ((tag_ == 11_int64)) then
            r = (tag_ == 11_int64)
            return
          else
            if ((tag_ == 12_int64)) then
              r = (tag_ == 12_int64)
              return
            else
              if ((tag_ == 13_int64)) then
                r = (tag_ == 13_int64)
                return
              else
                r = (tag_ == 15_int64)
                return
              end if
            end if
          end if
        end if
      end if
    end if
  end function hpg_text_tag

  subroutine hpg_spush(hs, tag_, ref_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: i_2
    integer(int64) :: i_4
    integer(int64) :: sp_1
    integer(int64) :: v_3
    integer(int64) :: v_5
    sp_1 = hs%msp
    if ((sp_1 < size(hs%mtag, kind=int64))) then
      i_2 = sp_1
      v_3 = tag_
      hs%mtag(i_2) = v_3
      i_4 = sp_1
      v_5 = ref_
      hs%mref(i_4) = v_5
      hs%msp = (1_int64 + sp_1)
    else
      hs%err = 1_int64
    end if
  end subroutine hpg_spush

  subroutine hpg_push(hs, tag_, ref_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: tag_
    integer(int64), value :: ref_
    integer(int64) :: i_11
    integer(int64) :: i_2
    integer(int64) :: i_6
    integer(int64) :: n_8
    logical :: t_1
    integer(int64) :: t_10
    logical :: t_4
    logical :: t_5
    logical :: t_9
    integer(int64) :: v_12
    integer(int64) :: v_3
    integer(int64) :: v_7
    if ((.not. (0_int64 < ref_))) then
    else
      if ((tag_ == 8_int64)) then
        if ((ref_ < hp_n_obj())) then
          t_1 = (hp_omark(ref_) == 0_int64)
        else
          t_1 = .false.
        end if
        if (t_1) then
          i_2 = ref_
          v_3 = 1_int64
          call hp_set_omark(i_2, v_3)
          hs%nobj = hpg_add(hs%nobj, 1_int64)
          call hpg_spush(hs, tag_, ref_)
        else
        end if
      else
        if ((tag_ == 9_int64)) then
          if ((ref_ < hp_n_vec())) then
            if ((ref_ < hp_n_vec())) then
              t_4 = (hp_vmark(ref_) == 0_int64)
            else
              t_4 = .false.
            end if
            t_5 = t_4
          else
            t_5 = .false.
          end if
          if (t_5) then
            i_6 = ref_
            v_7 = 1_int64
            call hp_set_vmark(i_6, v_7)
            hs%nvec = hpg_add(hs%nvec, 1_int64)
            n_8 = hp_vlen(ref_)
            if ((.not. (n_8 < 0_int64))) then
              t_9 = (.not. (1099511627776_int64 < n_8))
            else
              t_9 = .false.
            end if
            if (t_9) then
              t_10 = n_8
            else
              t_10 = 0_int64
            end if
            hs%alive = hpg_add(hs%alive, t_10)
            call hpg_spush(hs, tag_, ref_)
          else
          end if
        else
          if (hpg_text_tag(tag_)) then
            if ((ref_ < hp_n_str())) then
              i_11 = ref_
              v_12 = 1_int64
              call hp_set_smark(i_11, v_12)
              hs%nstr = hpg_add(hs%nstr, 1_int64)
            else
            end if
          else
          end if
        end if
      end if
    end if
  end subroutine hpg_push

  subroutine hpg_scan_obj(hs, i_, k_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64), value :: k_
    integer(int64) :: i_4
    integer(int64) :: j_2
    integer(int64) :: k_5
    logical :: t_1
    logical :: t_3
    do
      if ((.not. (k_ >= 0_int64))) then
        t_1 = (.not. (k_ >= 0_int64))
      else
        t_1 = (.not. (k_ < 5_int64))
      end if
      if (t_1) then
      else
        j_2 = ((5_int64 * i_) + k_)
        if ((j_2 < hp_n_oslot())) then
          t_3 = (j_2 < hp_n_oslot())
        else
          t_3 = .false.
        end if
        if (t_3) then
          call hpg_push(hs, hp_otag(j_2), hp_oref(j_2))
          i_4 = i_
          k_5 = (1_int64 + k_)
          i_ = i_4
          k_ = k_5
          cycle
        else
        end if
      end if
      exit
    end do
  end subroutine hpg_scan_obj

  subroutine hpg_scan_run(hs, j_, e_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: j_
    integer(int64), value :: e_
    integer(int64) :: e_5
    integer(int64) :: j_4
    logical :: t_1
    logical :: t_2
    logical :: t_3
    do
      if ((.not. (j_ >= 0_int64))) then
        t_2 = (.not. (j_ >= 0_int64))
      else
        if ((.not. (e_ >= 0_int64))) then
          t_1 = (.not. (e_ >= 0_int64))
        else
          t_1 = (.not. (j_ < e_))
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        if ((j_ < hp_n_arena())) then
          t_3 = (j_ < hp_n_arena())
        else
          t_3 = .false.
        end if
        if (t_3) then
          call hpg_push(hs, hp_atag(j_), hp_aref(j_))
          j_4 = (1_int64 + j_)
          e_5 = e_
          j_ = j_4
          e_ = e_5
          cycle
        else
        end if
      end if
      exit
    end do
  end subroutine hpg_scan_run

  subroutine hpg_scan_vec(hs, i_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: n_3
    integer(int64) :: off_2
    logical :: t_1
    logical :: t_4
    logical :: t_5
    if ((i_ < hp_n_vec())) then
      t_1 = (i_ < hp_n_vec())
    else
      t_1 = .false.
    end if
    if (t_1) then
      off_2 = max(0_int64, hp_voff(i_))
      n_3 = max(0_int64, hp_vlen(i_))
      if ((.not. (1099511627776_int64 < off_2))) then
        if ((.not. (1099511627776_int64 < n_3))) then
          t_4 = (.not. (1099511627776_int64 < (off_2 + n_3)))
        else
          t_4 = .false.
        end if
        t_5 = t_4
      else
        t_5 = .false.
      end if
      if (t_5) then
        call hpg_scan_run(hs, off_2, (off_2 + n_3))
      else
      end if
    else
    end if
  end subroutine hpg_scan_vec

  subroutine hpg_drain(hs, fuel_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: fuel_
    integer(int64) :: fuel_9
    integer(int64) :: ref_5
    integer(int64) :: sp_3
    logical :: t_1
    logical :: t_2
    logical :: t_6
    logical :: t_7
    logical :: t_8
    integer(int64) :: tag_4
    do
      if ((fuel_ <= 0_int64)) then
        t_2 = (fuel_ <= 0_int64)
      else
        if ((hs%msp <= 0_int64)) then
          t_1 = (hs%msp <= 0_int64)
        else
          t_1 = (.not. (hs%err == 0_int64))
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        sp_3 = (-1_int64 + hs%msp)
        tag_4 = hs%mtag(sp_3)
        ref_5 = hs%mref(sp_3)
        hs%msp = sp_3
        if ((tag_4 == 8_int64)) then
          if ((0_int64 < ref_5)) then
            t_6 = (ref_5 < 1099511627776_int64)
          else
            t_6 = .false.
          end if
          t_7 = t_6
        else
          t_7 = .false.
        end if
        if (t_7) then
          call hpg_scan_obj(hs, ref_5, 0_int64)
        else
          if ((tag_4 == 9_int64)) then
            t_8 = (0_int64 < ref_5)
          else
            t_8 = .false.
          end if
          if (t_8) then
            call hpg_scan_vec(hs, ref_5)
          else
          end if
        end if
        fuel_9 = (-1_int64 + fuel_)
        fuel_ = fuel_9
        cycle
      end if
      exit
    end do
  end subroutine hpg_drain
