  ! GENERATED from model/vmtrg.lisp by scripts/acl2-fortran -b vmtrg. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the VM's translation of a constant, a local, if, do, let*,
  ! loop, recur, throw and a builtin's call (vtg_tr; every other kind vm.inc's vm_tr, through vtg_other) --
  ! guard-verified, reading the tree through vm.inc's vtg_* reads and building
  ! the expression on the value stack through its vtg_* shims. vmtrg.lisp
  ! proves it pushes exactly exec-vmtr's ex-tr on a tree of these kinds
  ! (vtg-tr-ex-tr); vtg_lind: whether a loop's inits read none before them
  ! (ex-lind). vtg_tlr: whether a clause's body recurs to the fn (its
  ! loop's test in vm_clause), exec-vmtr's ex-tlr (vtg-tlr-ex-tlr). vtg_clause:
  ! vm_clause's clause of one arity, exec-vmtr's ex-clause (vmtrcl.lisp's
  ! vtg-clause-ex-clause); vtg_arcl: vm_compile_fn's arity-error clause (ex-arcl).
  recursive function vtg_rd(flg_, e_, i_, lo_, hi_) result(r)
    integer(int64), value :: flg_
    type(gc_value), value :: e_
    integer(int64), value :: i_
    integer(int64), value :: lo_
    integer(int64), value :: hi_
    logical :: r
    integer(int64) :: i_1
    integer(int64) :: k_4
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
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    if ((flg_ == 1_int64)) then
      i_1 = max(0_int64, i_)
      if ((i_1 < vtg_nk(e_))) then
        if (vtg_rd(0_int64, vtg_kid(e_, i_1), 0_int64, lo_, hi_)) then
          t_2 = .true.
        else
          t_2 = vtg_rd(1_int64, e_, (1_int64 + i_1), lo_, hi_)
        end if
        t_3 = t_2
      else
        t_3 = .false.
      end if
      r = t_3
      return
    else
      k_4 = vtg_kind(e_)
      if ((k_4 == 1_int64)) then
        t_5 = (k_4 == 1_int64)
      else
        t_5 = (k_4 == 3_int64)
      end if
      if (t_5) then
        t_22 = .false.
      else
        if ((k_4 == 2_int64)) then
          if ((.not. (vtg_i2(e_) < lo_))) then
            t_6 = (vtg_i2(e_) < hi_)
          else
            t_6 = .false.
          end if
          t_21 = t_6
        else
          if ((k_4 == 14_int64)) then
            t_7 = (k_4 == 14_int64)
          else
            t_7 = (k_4 == 15_int64)
          end if
          if (t_7) then
            t_20 = vtg_rdcap(e_, lo_, hi_)
          else
            if ((k_4 == 4_int64)) then
              t_18 = (k_4 == 4_int64)
            else
              if ((k_4 == 5_int64)) then
                t_17 = (k_4 == 5_int64)
              else
                if ((k_4 == 17_int64)) then
                  t_16 = (k_4 == 17_int64)
                else
                  if ((k_4 == 7_int64)) then
                    t_15 = (k_4 == 7_int64)
                  else
                    if ((k_4 == 8_int64)) then
                      t_14 = (k_4 == 8_int64)
                    else
                      if ((k_4 == 9_int64)) then
                        t_13 = (k_4 == 9_int64)
                      else
                        if ((k_4 == 22_int64)) then
                          t_12 = (k_4 == 22_int64)
                        else
                          if ((k_4 == 21_int64)) then
                            t_11 = (k_4 == 21_int64)
                          else
                            if ((k_4 == 6_int64)) then
                              t_10 = (k_4 == 6_int64)
                            else
                              if ((k_4 == 11_int64)) then
                                t_9 = (k_4 == 11_int64)
                              else
                                if ((k_4 == 12_int64)) then
                                  t_8 = (k_4 == 12_int64)
                                else
                                  t_8 = (k_4 == 16_int64)
                                end if
                                t_9 = t_8
                              end if
                              t_10 = t_9
                            end if
                            t_11 = t_10
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
              t_18 = t_17
            end if
            if (t_18) then
              t_19 = vtg_rd(1_int64, e_, 0_int64, lo_, hi_)
            else
              t_19 = .true.
            end if
            t_20 = t_19
          end if
          t_21 = t_20
        end if
        t_22 = t_21
      end if
      r = t_22
      return
    end if
  end function vtg_rd

  recursive function vtg_lind(e_, i_) result(r)
    type(gc_value), value :: e_
    integer(int64), value :: i_
    logical :: r
    integer(int64) :: i_1
    logical :: t_2
    logical :: t_3
    i_1 = max(0_int64, i_)
    if ((i_1 < vtg_i2(e_))) then
      if (vtg_rd(0_int64, vtg_kid(e_, i_1), 0_int64, vtg_s2(e_), (vtg_s2(e_) + i_1))) then
        t_2 = .false.
      else
        t_2 = vtg_lind(e_, (1_int64 + i_1))
      end if
      t_3 = t_2
    else
      t_3 = .true.
    end if
    r = t_3
    return
  end function vtg_lind

  subroutine vtg_locs(tb, s_, j_, n_)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s_
    integer(int64), value :: j_
    integer(int64), value :: n_
    integer(int64) :: j_1
    integer(int64) :: j_3
    integer(int64) :: n_4
    integer(int64) :: s_2
    do
      j_1 = max(0_int64, j_)
      if ((j_1 < max(0_int64, n_))) then
        call vtg_local(tb, (s_ + j_1))
        s_2 = s_
        j_3 = (1_int64 + j_1)
        n_4 = n_
        s_ = s_2
        j_ = j_3
        n_ = n_4
        cycle
      else
      end if
      exit
    end do
  end subroutine vtg_locs

  recursive subroutine vtg_tr(tb, flg_, e_, i_)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: flg_
    type(gc_value), value :: e_
    integer(int64), value :: i_
    type(gc_value) :: e_19
    type(gc_value) :: e_22
    type(gc_value) :: e_25
    type(gc_value) :: e_4
    type(gc_value) :: e_9
    integer(int64) :: flg_18
    integer(int64) :: flg_21
    integer(int64) :: flg_24
    integer(int64) :: flg_3
    integer(int64) :: flg_8
    integer(int64) :: i_10
    integer(int64) :: i_13
    integer(int64) :: i_16
    integer(int64) :: i_2
    integer(int64) :: i_20
    integer(int64) :: i_23
    integer(int64) :: i_26
    integer(int64) :: i_5
    integer(int64) :: i_6
    integer(int64) :: k_17
    integer(int64) :: nk_7
    logical :: t_1
    logical :: t_11
    logical :: t_12
    logical :: t_14
    integer(int64) :: t_15
    logical :: t_27
    do
      select case (flg_)
      case (1_int64)
        if ((vtg_kind(e_) == 11_int64)) then
          t_1 = (vtg_kind(e_) == 11_int64)
        else
          t_1 = (vtg_kind(e_) == 12_int64)
        end if
        if (t_1) then
          i_2 = max(0_int64, i_)
          if ((i_2 < vtg_i2(e_))) then
            call vtg_tr(tb, 0_int64, vtg_kid(e_, i_2), 0_int64)
            call vtg_save(tb)
            call vtg_blank(tb, vtg_kid(e_, i_2))
            call vtg_bind(tb, (vtg_s2(e_) + i_2))
            call vtg_tr(tb, 1_int64, e_, (1_int64 + i_2))
            call vtg_restore(tb)
            call vtg_node(tb, 2_int64, 2_int64)
          else
            if ((vtg_kind(e_) == 12_int64)) then
              call vtg_locs(tb, vtg_s2(e_), 0_int64, vtg_i2(e_))
              call vtg_node(tb, 0_int64, vtg_i2(e_))
              call vtg_save(tb)
              call vtg_binds(tb, vtg_s2(e_), vtg_i2(e_))
              call vtg_tr(tb, 0_int64, vtg_kid(e_, vtg_i2(e_)), 0_int64)
              call vtg_restore(tb)
              call vtg_node(tb, 4_int64, 2_int64)
            else
              flg_3 = 0_int64
              e_4 = vtg_kid(e_, vtg_i2(e_))
              i_5 = 0_int64
              flg_ = flg_3
              e_ = e_4
              i_ = i_5
              cycle
            end if
          end if
        else
          call vtg_other(tb, e_)
        end if
      case (2_int64)
        if ((vtg_kind(e_) == 5_int64)) then
          i_6 = max(0_int64, i_)
          nk_7 = vtg_nk(e_)
          if ((nk_7 <= 0_int64)) then
            call vtg_nil(tb)
          else
            if ((i_6 < ((-1_int64) + nk_7))) then
              call vtg_tr(tb, 0_int64, vtg_kid(e_, i_6), 0_int64)
              call vtg_save(tb)
              call vtg_blank(tb, vtg_kid(e_, i_6))
              call vtg_dead(tb)
              call vtg_tr(tb, 2_int64, e_, (1_int64 + i_6))
              call vtg_restore(tb)
              call vtg_node(tb, 2_int64, 2_int64)
            else
              flg_8 = 0_int64
              e_9 = vtg_kid(e_, ((-1_int64) + nk_7))
              i_10 = 0_int64
              flg_ = flg_8
              e_ = e_9
              i_ = i_10
              cycle
            end if
          end if
        else
          call vtg_other(tb, e_)
        end if
      case (3_int64)
        if ((vtg_kind(e_) == 12_int64)) then
          t_12 = (vtg_kind(e_) == 12_int64)
        else
          if ((vtg_kind(e_) == 16_int64)) then
            t_11 = (vtg_kind(e_) == 16_int64)
          else
            t_11 = (vtg_kind(e_) == 6_int64)
          end if
          t_12 = t_11
        end if
        if (t_12) then
          i_13 = max(0_int64, i_)
          if ((vtg_kind(e_) == 16_int64)) then
            t_14 = (vtg_kind(e_) == 16_int64)
          else
            t_14 = (vtg_kind(e_) == 6_int64)
          end if
          if (t_14) then
            t_15 = vtg_nk(e_)
          else
            t_15 = vtg_i2(e_)
          end if
          if ((i_13 < t_15)) then
            call vtg_tr(tb, 0_int64, vtg_kid(e_, i_13), 0_int64)
            call vtg_save(tb)
            call vtg_blank(tb, vtg_kid(e_, i_13))
            call vtg_tr(tb, 3_int64, e_, (1_int64 + i_13))
            call vtg_restore(tb)
          else
          end if
        else
          call vtg_other(tb, e_)
        end if
      case (5_int64)
        if ((vtg_kind(e_) == 12_int64)) then
          i_16 = max(0_int64, i_)
          if ((i_16 < vtg_i2(e_))) then
            call vtg_save(tb)
            call vtg_blank(tb, vtg_kid(e_, i_16))
            call vtg_tr(tb, 5_int64, e_, (1_int64 + i_16))
            call vtg_restore(tb)
          else
            call vtg_save(tb)
            call vtg_binds(tb, vtg_s2(e_), vtg_i2(e_))
            call vtg_tr(tb, 0_int64, vtg_kid(e_, vtg_i2(e_)), 0_int64)
            call vtg_restore(tb)
          end if
        else
          call vtg_other(tb, e_)
        end if
      case default
        k_17 = vtg_kind(e_)
        select case (k_17)
        case (1_int64)
          call vtg_const(tb, vtg_c(e_))
        case (3_int64)
          call vtg_deref(tb, e_)
        case (2_int64)
          call vtg_local(tb, vtg_i2(e_))
        case (4_int64)
          call vtg_tr(tb, 0_int64, vtg_kid(e_, 0_int64), 0_int64)
          call vtg_save(tb)
          call vtg_blank(tb, vtg_kid(e_, 0_int64))
          call vtg_tr(tb, 0_int64, vtg_kid(e_, 1_int64), 0_int64)
          if ((2_int64 < vtg_nk(e_))) then
            call vtg_tr(tb, 0_int64, vtg_kid(e_, 2_int64), 0_int64)
          else
            call vtg_nil(tb)
          end if
          call vtg_restore(tb)
          call vtg_node(tb, 1_int64, 3_int64)
        case (17_int64)
          call vtg_tr(tb, 0_int64, vtg_kid(e_, 0_int64), 0_int64)
          call vtg_node(tb, 3_int64, 1_int64)
        case (11_int64)
          flg_18 = 1_int64
          e_19 = e_
          i_20 = 0_int64
          flg_ = flg_18
          e_ = e_19
          i_ = i_20
          cycle
        case (5_int64)
          flg_21 = 2_int64
          e_22 = e_
          i_23 = 0_int64
          flg_ = flg_21
          e_ = e_22
          i_ = i_23
          cycle
        case (12_int64)
          if (vtg_lind(e_, 1_int64)) then
            call vtg_tr(tb, 3_int64, e_, 0_int64)
            call vtg_node(tb, 0_int64, vtg_i2(e_))
            call vtg_tr(tb, 5_int64, e_, 0_int64)
            call vtg_node(tb, 4_int64, 2_int64)
          else
            flg_24 = 1_int64
            e_25 = e_
            i_26 = 0_int64
            flg_ = flg_24
            e_ = e_25
            i_ = i_26
            cycle
          end if
        case (16_int64)
          call vtg_tr(tb, 3_int64, e_, 0_int64)
          call vtg_node(tb, 5_int64, vtg_nk(e_))
        case default
          if ((k_17 == 6_int64)) then
            t_27 = vtg_bip(e_)
          else
            t_27 = .false.
          end if
          if (t_27) then
            call vtg_hd(tb, e_)
            call vtg_tr(tb, 3_int64, e_, 1_int64)
            call vtg_node(tb, 6_int64, vtg_nk(e_))
          else
            call vtg_other(tb, e_)
          end if
        end select
      end select
      exit
    end do
  end subroutine vtg_tr

  recursive function vtg_tlr(e_) result(r)
    type(gc_value), value :: e_
    logical :: r
    integer(int64) :: k_1
    integer(int64) :: nk_2
    logical :: t_10
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    k_1 = vtg_kind(e_)
    nk_2 = vtg_nk(e_)
    if ((k_1 == 16_int64)) then
      t_10 = .true.
    else
      if ((k_1 == 4_int64)) then
        if (vtg_tlr(vtg_kid(e_, 1_int64))) then
          t_4 = .true.
        else
          if ((2_int64 < nk_2)) then
            t_3 = vtg_tlr(vtg_kid(e_, 2_int64))
          else
            t_3 = .false.
          end if
          t_4 = t_3
        end if
        t_9 = t_4
      else
        if ((k_1 == 5_int64)) then
          if ((nk_2 <= 0_int64)) then
            t_5 = .false.
          else
            t_5 = vtg_tlr(vtg_kid(e_, ((-1_int64) + nk_2)))
          end if
          t_8 = t_5
        else
          if ((k_1 == 11_int64)) then
            t_6 = (k_1 == 11_int64)
          else
            t_6 = (k_1 == 13_int64)
          end if
          if (t_6) then
            t_7 = vtg_tlr(vtg_kid(e_, vtg_i2(e_)))
          else
            t_7 = .false.
          end if
          t_8 = t_7
        end if
        t_9 = t_8
      end if
      t_10 = t_9
    end if
    r = t_10
    return
  end function vtg_tlr

  subroutine vtg_clause(tb, nf_, var_, s_, body_, tm_, sl_, m_)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: nf_
    integer(int64), value :: var_
    integer(int64), value :: s_
    type(gc_value), value :: body_
    type(gc_value), value :: tm_
    integer(int64), value :: sl_
    integer(int64), value :: m_
    integer(int64) :: np_2
    integer(int64) :: t_1
    if ((var_ == 0_int64)) then
      t_1 = nf_
    else
      t_1 = (1_int64 + nf_)
    end if
    np_2 = t_1
    call vtg_num(tb, nf_)
    if ((sl_ == 0_int64)) then
    else
      call vtg_self(tb, tm_, m_)
    end if
    if (vtg_tlr(body_)) then
      call vtg_locs(tb, s_, 0_int64, np_2)
      call vtg_node(tb, 0_int64, np_2)
      call vtg_save(tb)
      call vtg_binds(tb, s_, np_2)
      call vtg_tr(tb, 0_int64, body_, 0_int64)
      call vtg_restore(tb)
      call vtg_node(tb, 4_int64, 2_int64)
    else
      call vtg_tr(tb, 0_int64, body_, 0_int64)
    end if
    if ((sl_ == 0_int64)) then
    else
      call vtg_node(tb, 2_int64, 2_int64)
    end if
    if ((var_ == 0_int64)) then
      call vtg_node(tb, 0_int64, 2_int64)
    else
      call vtg_key(tb, 0_int64)
      call vtg_node(tb, 0_int64, 3_int64)
    end if
  end subroutine vtg_clause

  subroutine vtg_arcl(tb, name_)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: name_
    call vtg_num(tb, 0_int64)
    call vtg_key(tb, 2_int64)
    call vtg_key(tb, 1_int64)
    call vtg_const(tb, name_)
    call vtg_key(tb, 3_int64)
    call vtg_num(tb, 0_int64)
    call vtg_node(tb, 0_int64, 2_int64)
    call vtg_node(tb, 0_int64, 4_int64)
    call vtg_key(tb, 0_int64)
    call vtg_node(tb, 0_int64, 3_int64)
  end subroutine vtg_arcl
