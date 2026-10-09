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

  pure function hpg_s64(x_) result(r)
    integer(int64), value :: x_
    integer(int64) :: r
    logical :: t_1
    logical :: t_2
    if (.true.) then
      if ((.not. (x_ < (-huge(0_int64) - 1_int64)))) then
        t_1 = .true.
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      r = x_
      return
    else
      r = 0_int64
      return
    end if
  end function hpg_s64

  pure function hpg_n40(x_) result(r)
    integer(int64), value :: x_
    integer(int64) :: r
    logical :: t_1
    if ((x_ >= 0_int64)) then
      t_1 = (.not. (1099511627776_int64 < x_))
    else
      t_1 = .false.
    end if
    if (t_1) then
      r = x_
      return
    else
      r = 0_int64
      return
    end if
  end function hpg_n40

  pure function hpg_size_class(n_, c_, p_) result(r)
    integer(int64), value :: n_
    integer(int64), value :: c_
    integer(int64), value :: p_
    integer(int64) :: r
    integer(int64) :: c_7
    integer(int64) :: n_6
    integer(int64) :: p_8
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    do
      if ((.not. (p_ >= 0_int64))) then
        t_5 = (.not. (p_ >= 0_int64))
      else
        if ((p_ < 1_int64)) then
          t_4 = (p_ < 1_int64)
        else
          if ((.not. (p_ < n_))) then
            t_3 = (.not. (p_ < n_))
          else
            if ((1099511627776_int64 < p_)) then
              t_2 = (1099511627776_int64 < p_)
            else
              if ((.not. (c_ >= 0_int64))) then
                t_1 = (.not. (c_ >= 0_int64))
              else
                t_1 = (.not. (c_ < 64_int64))
              end if
              t_2 = t_1
            end if
            t_3 = t_2
          end if
          t_4 = t_3
        end if
        t_5 = t_4
      end if
      if (t_5) then
        r = c_
        return
      else
        n_6 = n_
        c_7 = (1_int64 + c_)
        p_8 = (2_int64 * p_)
        n_ = n_6
        c_ = c_7
        p_ = p_8
        cycle
      end if
    end do
  end function hpg_size_class

  subroutine hpg_free_obj(hs, i_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: i_1
    integer(int64) :: i_3
    integer(int64) :: i_5
    integer(int64) :: i_7
    integer(int64) :: v_2
    integer(int64) :: v_4
    integer(int64) :: v_6
    integer(int64) :: v_8
    i_1 = i_
    v_2 = 1_int64
    call hp_finalize(i_1, v_2)
    i_3 = i_
    v_4 = 0_int64
    call hp_set_okind(i_3, v_4)
    i_5 = i_
    v_6 = 1_int64
    call hp_set_ofree(i_5, v_6)
    i_7 = i_
    v_8 = hpg_s64(hp_ohead())
    call hp_set_onext(i_7, v_8)
    call hp_set_ohead(i_)
    hs%nswo = hpg_add(hs%nswo, 1_int64)
  end subroutine hpg_free_obj

  subroutine hpg_slab_free(hs, i_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: c_3
    integer(int64) :: i_11
    integer(int64) :: i_13
    integer(int64) :: i_15
    integer(int64) :: i_17
    integer(int64) :: i_7
    integer(int64) :: i_9
    integer(int64) :: len_1
    integer(int64) :: off_2
    logical :: t_4
    logical :: t_5
    logical :: t_6
    integer(int64) :: v_10
    integer(int64) :: v_12
    integer(int64) :: v_14
    integer(int64) :: v_16
    integer(int64) :: v_18
    integer(int64) :: v_8
    len_1 = hpg_n40(hp_vlen(i_))
    if ((0_int64 < len_1)) then
      off_2 = hpg_n40(hp_voff(i_))
      c_3 = hpg_size_class(len_1, 1_int64, 1_int64)
      if ((off_2 < hp_n_arena())) then
        if ((off_2 < hp_n_arena())) then
          if ((off_2 < hp_n_arena())) then
            t_4 = (c_3 < hp_n_chead())
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
        i_7 = off_2
        v_8 = 0_int64
        call hp_set_atag(i_7, v_8)
        i_9 = off_2
        v_10 = 0_int64
        call hp_set_aref(i_9, v_10)
        i_11 = off_2
        v_12 = hpg_s64(hp_chead(c_3))
        call hp_set_aival(i_11, v_12)
        i_13 = c_3
        v_14 = off_2
        call hp_set_chead(i_13, v_14)
        i_15 = i_
        v_16 = 0_int64
        call hp_set_voff(i_15, v_16)
        i_17 = i_
        v_18 = 0_int64
        call hp_set_vlen(i_17, v_18)
      else
      end if
    else
    end if
  end subroutine hpg_slab_free

  subroutine hpg_free_vec(hs, i_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: i_2
    integer(int64) :: i_4
    integer(int64) :: len_1
    integer(int64) :: v_3
    integer(int64) :: v_5
    len_1 = hp_vlen(i_)
    hs%afree = hpg_add(hs%afree, hpg_n40(len_1))
    call hpg_slab_free(hs, i_)
    i_2 = i_
    v_3 = 1_int64
    call hp_set_vfree(i_2, v_3)
    i_4 = i_
    v_5 = hpg_s64(hp_vhead())
    call hp_set_vnext(i_4, v_5)
    call hp_set_vhead(i_)
    hs%nswv = hpg_add(hs%nswv, 1_int64)
  end subroutine hpg_free_vec

  subroutine hpg_free_str(hs, i_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: i_1
    integer(int64) :: i_3
    integer(int64) :: i_5
    integer(int64) :: v_2
    integer(int64) :: v_4
    integer(int64) :: v_6
    i_1 = i_
    v_2 = 1_int64
    call hp_release_str(i_1, v_2)
    i_3 = i_
    v_4 = 1_int64
    call hp_set_sfree(i_3, v_4)
    i_5 = i_
    v_6 = hpg_s64(hp_shead())
    call hp_set_snext(i_5, v_6)
    call hp_set_shead(i_)
    hs%nsws = hpg_add(hs%nsws, 1_int64)
  end subroutine hpg_free_str

  subroutine hpg_sweep_objs(hs, i_, n_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64), value :: n_
    integer(int64) :: i_9
    integer(int64) :: n_10
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    do
      if ((.not. (i_ >= 0_int64))) then
        t_2 = (.not. (i_ >= 0_int64))
      else
        if ((.not. (n_ >= 0_int64))) then
          t_1 = (.not. (n_ >= 0_int64))
        else
          t_1 = (n_ < i_)
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        if ((i_ < hp_n_obj())) then
          if ((i_ < hp_n_obj())) then
            if ((i_ < hp_n_obj())) then
              if ((i_ < hp_n_obj())) then
                if ((i_ < hp_n_obj())) then
                  if ((hp_omark(i_) == 0_int64)) then
                    t_3 = (hp_ofree(i_) == 0_int64)
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
          call hpg_free_obj(hs, i_)
        else
        end if
        i_9 = (1_int64 + i_)
        n_10 = n_
        i_ = i_9
        n_ = n_10
        cycle
      end if
      exit
    end do
  end subroutine hpg_sweep_objs

  subroutine hpg_sweep_vecs(hs, i_, n_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64), value :: n_
    integer(int64) :: i_9
    integer(int64) :: n_10
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    do
      if ((.not. (i_ >= 0_int64))) then
        t_2 = (.not. (i_ >= 0_int64))
      else
        if ((.not. (n_ >= 0_int64))) then
          t_1 = (.not. (n_ >= 0_int64))
        else
          t_1 = (n_ < i_)
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        if ((i_ < hp_n_vec())) then
          if ((i_ < hp_n_vec())) then
            if ((i_ < hp_n_vec())) then
              if ((i_ < hp_n_vec())) then
                if ((i_ < hp_n_vec())) then
                  if ((hp_vmark(i_) == 0_int64)) then
                    t_3 = (hp_vfree(i_) == 0_int64)
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
          call hpg_free_vec(hs, i_)
        else
        end if
        i_9 = (1_int64 + i_)
        n_10 = n_
        i_ = i_9
        n_ = n_10
        cycle
      end if
      exit
    end do
  end subroutine hpg_sweep_vecs

  subroutine hpg_sweep_strs(hs, i_, n_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64), value :: n_
    integer(int64) :: i_8
    integer(int64) :: n_9
    logical :: t_1
    logical :: t_2
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    do
      if ((.not. (i_ >= 0_int64))) then
        t_2 = (.not. (i_ >= 0_int64))
      else
        if ((.not. (n_ >= 0_int64))) then
          t_1 = (.not. (n_ >= 0_int64))
        else
          t_1 = (n_ < i_)
        end if
        t_2 = t_1
      end if
      if (t_2) then
      else
        if ((i_ < hp_n_str())) then
          if ((i_ < hp_n_str())) then
            if ((i_ < hp_n_str())) then
              if ((i_ < hp_n_str())) then
                if ((hp_smark(i_) == 0_int64)) then
                  t_3 = (hp_sfree(i_) == 0_int64)
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
          call hpg_free_str(hs, i_)
        else
        end if
        i_8 = (1_int64 + i_)
        n_9 = n_
        i_ = i_8
        n_ = n_9
        cycle
      end if
      exit
    end do
  end subroutine hpg_sweep_strs

  subroutine hpg_obj_take(hs, r)
    type(heap_state), intent(inout) :: hs
    integer(int64), intent(out) :: r
    integer(int64) :: h_1
    logical :: t_2
    integer(int64) :: u_3
    h_1 = hp_ohead()
    if ((0_int64 < h_1)) then
      t_2 = (h_1 < hp_n_obj())
    else
      t_2 = .false.
    end if
    if (t_2) then
      call hp_set_ohead(hpg_s64(hp_onext(h_1)))
      r = h_1
    else
      if ((hp_oused() < hp_ocap())) then
        u_3 = (1_int64 + hp_oused())
        call hp_set_oused(u_3)
        r = u_3
      else
        r = 0_int64
      end if
    end if
  end subroutine hpg_obj_take

  subroutine hpg_obj_use(hs, i_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: i_1
    integer(int64) :: i_3
    integer(int64) :: v_2
    integer(int64) :: v_4
    i_1 = i_
    v_2 = 0_int64
    call hp_set_ofree(i_1, v_2)
    i_3 = i_
    v_4 = 0_int64
    call hp_set_omark(i_3, v_4)
  end subroutine hpg_obj_use

  subroutine hpg_obj_fill_list(hs)
    type(heap_state), intent(inout) :: hs
    integer(int64) :: h_1
    integer(int64) :: i_3
    integer(int64) :: n_2
    integer(int64) :: v_4
    h_1 = hp_ohead()
    n_2 = (1_int64 + hp_nob())
    i_3 = n_2
    v_4 = h_1
    call hp_set_ob(i_3, v_4)
    call hp_set_nob(n_2)
    call hp_set_ohead(hpg_s64(hp_onext(h_1)))
  end subroutine hpg_obj_fill_list

  subroutine hpg_obj_fill_end(hs)
    type(heap_state), intent(inout) :: hs
    integer(int64) :: i_2
    integer(int64) :: i_5
    integer(int64) :: n_4
    integer(int64) :: u_1
    integer(int64) :: v_3
    integer(int64) :: v_6
    u_1 = (1_int64 + hp_oused())
    call hp_set_oused(u_1)
    i_2 = u_1
    v_3 = 1_int64
    call hp_set_ofree(i_2, v_3)
    n_4 = (1_int64 + hp_nob())
    i_5 = n_4
    v_6 = u_1
    call hp_set_ob(i_5, v_6)
    call hp_set_nob(n_4)
  end subroutine hpg_obj_fill_end

  subroutine hpg_obj_fill(hs, fuel_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: fuel_
    integer(int64) :: fuel_3
    integer(int64) :: fuel_6
    logical :: t_1
    logical :: t_2
    logical :: t_4
    logical :: t_5
    do
      if ((fuel_ <= 0_int64)) then
        t_1 = (fuel_ <= 0_int64)
      else
        t_1 = (.not. ((1_int64 + hp_nob()) < hp_n_ob()))
      end if
      if (t_1) then
      else
        if ((0_int64 < hp_ohead())) then
          t_2 = (hp_ohead() < hp_n_obj())
        else
          t_2 = .false.
        end if
        if (t_2) then
          call hpg_obj_fill_list(hs)
          fuel_3 = (-1_int64 + fuel_)
          fuel_ = fuel_3
          cycle
        else
          if ((hp_oused() < hp_ocap())) then
            if (((1_int64 + hp_oused()) < hp_n_obj())) then
              t_4 = ((1_int64 + hp_oused()) < hp_n_obj())
            else
              t_4 = .false.
            end if
            t_5 = t_4
          else
            t_5 = .false.
          end if
          if (t_5) then
            call hpg_obj_fill_end(hs)
            fuel_6 = (-1_int64 + fuel_)
            fuel_ = fuel_6
            cycle
          else
          end if
        end if
      end if
      exit
    end do
  end subroutine hpg_obj_fill

  subroutine hpg_obj_pop(hs, r)
    type(heap_state), intent(inout) :: hs
    integer(int64), intent(out) :: r
    integer(int64) :: i_3
    integer(int64) :: n_1
    logical :: t_2
    n_1 = hp_nob()
    if ((0_int64 < n_1)) then
      t_2 = (n_1 < hp_n_ob())
    else
      t_2 = .false.
    end if
    if (t_2) then
      i_3 = hp_ob(n_1)
      call hp_set_nob((-1_int64 + n_1))
      r = i_3
    else
      r = 0_int64
    end if
  end subroutine hpg_obj_pop

  subroutine hpg_vec_take(hs, r)
    type(heap_state), intent(inout) :: hs
    integer(int64), intent(out) :: r
    integer(int64) :: h_1
    logical :: t_2
    integer(int64) :: u_3
    h_1 = hp_vhead()
    if ((0_int64 < h_1)) then
      t_2 = (h_1 < hp_n_vec())
    else
      t_2 = .false.
    end if
    if (t_2) then
      call hp_set_vhead(hpg_s64(hp_vnext(h_1)))
      r = h_1
    else
      if ((hp_vused() < hp_vcap())) then
        u_3 = (1_int64 + hp_vused())
        call hp_set_vused(u_3)
        r = u_3
      else
        r = 0_int64
      end if
    end if
  end subroutine hpg_vec_take

  subroutine hpg_vec_use(hs, i_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: i_1
    integer(int64) :: i_3
    integer(int64) :: v_2
    integer(int64) :: v_4
    i_1 = i_
    v_2 = 0_int64
    call hp_set_vfree(i_1, v_2)
    i_3 = i_
    v_4 = 0_int64
    call hp_set_vmark(i_3, v_4)
  end subroutine hpg_vec_use

  subroutine hpg_vec_fill_list(hs)
    type(heap_state), intent(inout) :: hs
    integer(int64) :: h_1
    integer(int64) :: i_3
    integer(int64) :: n_2
    integer(int64) :: v_4
    h_1 = hp_vhead()
    n_2 = (1_int64 + hp_nvb())
    i_3 = n_2
    v_4 = h_1
    call hp_set_vb(i_3, v_4)
    call hp_set_nvb(n_2)
    call hp_set_vhead(hpg_s64(hp_vnext(h_1)))
  end subroutine hpg_vec_fill_list

  subroutine hpg_vec_fill_end(hs)
    type(heap_state), intent(inout) :: hs
    integer(int64) :: i_2
    integer(int64) :: i_5
    integer(int64) :: n_4
    integer(int64) :: u_1
    integer(int64) :: v_3
    integer(int64) :: v_6
    u_1 = (1_int64 + hp_vused())
    call hp_set_vused(u_1)
    i_2 = u_1
    v_3 = 1_int64
    call hp_set_vfree(i_2, v_3)
    n_4 = (1_int64 + hp_nvb())
    i_5 = n_4
    v_6 = u_1
    call hp_set_vb(i_5, v_6)
    call hp_set_nvb(n_4)
  end subroutine hpg_vec_fill_end

  subroutine hpg_vec_fill(hs, fuel_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: fuel_
    integer(int64) :: fuel_3
    integer(int64) :: fuel_6
    logical :: t_1
    logical :: t_2
    logical :: t_4
    logical :: t_5
    do
      if ((fuel_ <= 0_int64)) then
        t_1 = (fuel_ <= 0_int64)
      else
        t_1 = (.not. ((1_int64 + hp_nvb()) < hp_n_ob()))
      end if
      if (t_1) then
      else
        if ((0_int64 < hp_vhead())) then
          t_2 = (hp_vhead() < hp_n_vec())
        else
          t_2 = .false.
        end if
        if (t_2) then
          call hpg_vec_fill_list(hs)
          fuel_3 = (-1_int64 + fuel_)
          fuel_ = fuel_3
          cycle
        else
          if ((hp_vused() < hp_vcap())) then
            if (((1_int64 + hp_vused()) < hp_n_vec())) then
              t_4 = ((1_int64 + hp_vused()) < hp_n_vec())
            else
              t_4 = .false.
            end if
            t_5 = t_4
          else
            t_5 = .false.
          end if
          if (t_5) then
            call hpg_vec_fill_end(hs)
            fuel_6 = (-1_int64 + fuel_)
            fuel_ = fuel_6
            cycle
          else
          end if
        end if
      end if
      exit
    end do
  end subroutine hpg_vec_fill

  subroutine hpg_vec_pop(hs, r)
    type(heap_state), intent(inout) :: hs
    integer(int64), intent(out) :: r
    integer(int64) :: i_3
    integer(int64) :: n_1
    logical :: t_2
    n_1 = hp_nvb()
    if ((0_int64 < n_1)) then
      t_2 = (n_1 < hp_n_ob())
    else
      t_2 = .false.
    end if
    if (t_2) then
      i_3 = hp_vb(n_1)
      call hp_set_nvb((-1_int64 + n_1))
      r = i_3
    else
      r = 0_int64
    end if
  end subroutine hpg_vec_pop

  subroutine hpg_str_take(hs, r)
    type(heap_state), intent(inout) :: hs
    integer(int64), intent(out) :: r
    integer(int64) :: h_1
    logical :: t_2
    integer(int64) :: u_3
    h_1 = hp_shead()
    if ((0_int64 < h_1)) then
      t_2 = (h_1 < hp_n_str())
    else
      t_2 = .false.
    end if
    if (t_2) then
      call hp_set_shead(hpg_s64(hp_snext(h_1)))
      r = h_1
    else
      if ((hp_sused() < hp_scap())) then
        u_3 = (1_int64 + hp_sused())
        call hp_set_sused(u_3)
        r = u_3
      else
        r = 0_int64
      end if
    end if
  end subroutine hpg_str_take

  subroutine hpg_str_use(hs, i_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: i_
    integer(int64) :: i_1
    integer(int64) :: i_3
    integer(int64) :: v_2
    integer(int64) :: v_4
    i_1 = i_
    v_2 = 0_int64
    call hp_set_sfree(i_1, v_2)
    i_3 = i_
    v_4 = 0_int64
    call hp_set_smark(i_3, v_4)
  end subroutine hpg_str_use

  subroutine hpg_str_fill_list(hs)
    type(heap_state), intent(inout) :: hs
    integer(int64) :: h_1
    integer(int64) :: i_3
    integer(int64) :: n_2
    integer(int64) :: v_4
    h_1 = hp_shead()
    n_2 = (1_int64 + hp_nsb())
    i_3 = n_2
    v_4 = h_1
    call hp_set_sb(i_3, v_4)
    call hp_set_nsb(n_2)
    call hp_set_shead(hpg_s64(hp_snext(h_1)))
  end subroutine hpg_str_fill_list

  subroutine hpg_str_fill_end(hs)
    type(heap_state), intent(inout) :: hs
    integer(int64) :: i_2
    integer(int64) :: i_5
    integer(int64) :: n_4
    integer(int64) :: u_1
    integer(int64) :: v_3
    integer(int64) :: v_6
    u_1 = (1_int64 + hp_sused())
    call hp_set_sused(u_1)
    i_2 = u_1
    v_3 = 1_int64
    call hp_set_sfree(i_2, v_3)
    n_4 = (1_int64 + hp_nsb())
    i_5 = n_4
    v_6 = u_1
    call hp_set_sb(i_5, v_6)
    call hp_set_nsb(n_4)
  end subroutine hpg_str_fill_end

  subroutine hpg_str_fill(hs, fuel_)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: fuel_
    integer(int64) :: fuel_3
    integer(int64) :: fuel_6
    logical :: t_1
    logical :: t_2
    logical :: t_4
    logical :: t_5
    do
      if ((fuel_ <= 0_int64)) then
        t_1 = (fuel_ <= 0_int64)
      else
        t_1 = (.not. ((1_int64 + hp_nsb()) < hp_n_ob()))
      end if
      if (t_1) then
      else
        if ((0_int64 < hp_shead())) then
          t_2 = (hp_shead() < hp_n_str())
        else
          t_2 = .false.
        end if
        if (t_2) then
          call hpg_str_fill_list(hs)
          fuel_3 = (-1_int64 + fuel_)
          fuel_ = fuel_3
          cycle
        else
          if ((hp_sused() < hp_scap())) then
            if (((1_int64 + hp_sused()) < hp_n_str())) then
              t_4 = ((1_int64 + hp_sused()) < hp_n_str())
            else
              t_4 = .false.
            end if
            t_5 = t_4
          else
            t_5 = .false.
          end if
          if (t_5) then
            call hpg_str_fill_end(hs)
            fuel_6 = (-1_int64 + fuel_)
            fuel_ = fuel_6
            cycle
          else
          end if
        end if
      end if
      exit
    end do
  end subroutine hpg_str_fill

  subroutine hpg_str_pop(hs, r)
    type(heap_state), intent(inout) :: hs
    integer(int64), intent(out) :: r
    integer(int64) :: i_3
    integer(int64) :: n_1
    logical :: t_2
    n_1 = hp_nsb()
    if ((0_int64 < n_1)) then
      t_2 = (n_1 < hp_n_ob())
    else
      t_2 = .false.
    end if
    if (t_2) then
      i_3 = hp_sb(n_1)
      call hp_set_nsb((-1_int64 + n_1))
      r = i_3
    else
      r = 0_int64
    end if
  end subroutine hpg_str_pop
