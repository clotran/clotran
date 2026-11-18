  ! GENERATED from model/vmtrg.lisp by scripts/acl2-fortran -b vmtrg. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the VM's translation of a constant, a local, if, do, let*,
  ! loop, recur, throw, every call, case*, letfn, try, a vector, map, set, new, dot, def, deftype, new of a type or set!, a fn, a lazy seq (vtg_tr; every other kind vm.inc's vm_tr, through vtg_other) --
  ! guard-verified, reading the tree through vm.inc's vtg_* reads and building
  ! the expression on the value stack through its vtg_* shims. vmtrg.lisp
  ! proves it pushes exactly exec-vmtr's ex-tr on a tree of these kinds
  ! (vtg-tr-ex-tr); vtg_lind: whether a loop's inits read none before them
  ! (ex-lind). vtg_tlr: whether a clause's body recurs to the fn (its
  ! loop's test in vm_clause), exec-vmtr's ex-tlr (vtg-tlr-ex-tlr). vtg_clause:
  ! vm_clause's clause of one arity, exec-vmtr's ex-clause (vmtrcl.lisp's
  ! vtg-clause-ex-clause); vtg_arcl: vm_compile_fn's arity-error clause (ex-arcl);
  ! vtg_scope: vm_clause's scope, ex-fbcm or ex-fbcm0 (vtg-scope-fbcm). vtg_scan:
  ! whether the VM takes a body (vm_scan; vtg-scan-frag, vtg-scan-tlr-ok);
  ! vtg_rds: whether a body reads or binds a slot; vtg_sl: vm_clause's sl decision;
  ! vtg_fncl: vm_compile_fn's clause list, each arity's then ex-arcl (vtg-fncl-clauses).
  pure function vtg_coll(k_) result(r)
    integer(int64), value :: k_
    logical :: r
    select case (k_)
    case (7_int64)
      r = (k_ == 7_int64)
      return
    case (8_int64)
      r = (k_ == 8_int64)
      return
    case (9_int64)
      r = (k_ == 9_int64)
      return
    case (21_int64)
      r = (k_ == 21_int64)
      return
    case (22_int64)
      r = (k_ == 22_int64)
      return
    case (10_int64)
      r = (k_ == 10_int64)
      return
    case (20_int64)
      r = (k_ == 20_int64)
      return
    case (23_int64)
      r = (k_ == 23_int64)
      return
    case default
      r = (k_ == 24_int64)
      return
    end select
  end function vtg_coll

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

  subroutine vtg_caps(tb, e_, j_)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: e_
    integer(int64), value :: j_
    type(gc_value) :: e_2
    integer(int64) :: j_1
    integer(int64) :: j_3
    do
      j_1 = max(0_int64, j_)
      if ((j_1 < vtg_ncap(e_))) then
        call vtg_local(tb, vtg_capo(e_, j_1))
        e_2 = e_
        j_3 = (1_int64 + j_1)
        e_ = e_2
        j_ = j_3
        cycle
      else
      end if
      exit
    end do
  end subroutine vtg_caps

  recursive subroutine vtg_tr(tb, flg_, e_, i_)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: flg_
    type(gc_value), value :: e_
    integer(int64), value :: i_
    type(gc_value) :: e_19
    type(gc_value) :: e_25
    type(gc_value) :: e_28
    type(gc_value) :: e_31
    type(gc_value) :: e_37
    type(gc_value) :: e_4
    type(gc_value) :: e_9
    integer(int64) :: flg_18
    integer(int64) :: flg_24
    integer(int64) :: flg_27
    integer(int64) :: flg_3
    integer(int64) :: flg_30
    integer(int64) :: flg_36
    integer(int64) :: flg_8
    integer(int64) :: i_10
    integer(int64) :: i_14
    integer(int64) :: i_16
    integer(int64) :: i_17
    integer(int64) :: i_2
    integer(int64) :: i_20
    integer(int64) :: i_21
    integer(int64) :: i_22
    integer(int64) :: i_26
    integer(int64) :: i_29
    integer(int64) :: i_32
    integer(int64) :: i_38
    integer(int64) :: i_5
    integer(int64) :: i_6
    integer(int64) :: k_23
    integer(int64) :: nk_7
    logical :: t_1
    logical :: t_11
    logical :: t_12
    logical :: t_13
    integer(int64) :: t_15
    logical :: t_33
    logical :: t_34
    logical :: t_35
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
          t_13 = (vtg_kind(e_) == 12_int64)
        else
          if ((vtg_kind(e_) == 16_int64)) then
            t_12 = (vtg_kind(e_) == 16_int64)
          else
            if ((vtg_kind(e_) == 6_int64)) then
              t_11 = (vtg_kind(e_) == 6_int64)
            else
              t_11 = vtg_coll(vtg_kind(e_))
            end if
            t_12 = t_11
          end if
          t_13 = t_12
        end if
        if (t_13) then
          i_14 = max(0_int64, i_)
          if ((vtg_kind(e_) == 12_int64)) then
            t_15 = vtg_i2(e_)
          else
            t_15 = vtg_nk(e_)
          end if
          if ((i_14 < t_15)) then
            call vtg_tr(tb, 0_int64, vtg_kid(e_, i_14), 0_int64)
            call vtg_save(tb)
            call vtg_blank(tb, vtg_kid(e_, i_14))
            call vtg_tr(tb, 3_int64, e_, (1_int64 + i_14))
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
      case (6_int64)
        if ((vtg_kind(e_) == 19_int64)) then
          i_17 = max(0_int64, i_)
          if ((i_17 < vtg_ncs(e_))) then
            call vtg_cstest(tb, e_, i_17)
            call vtg_top(tb)
            call vtg_node(tb, 6_int64, 3_int64)
            call vtg_tr(tb, 0_int64, vtg_cthen(e_, i_17), 0_int64)
            call vtg_tr(tb, 6_int64, e_, (1_int64 + i_17))
            call vtg_node(tb, 1_int64, 3_int64)
          else
            flg_18 = 0_int64
            e_19 = vtg_kid(e_, 1_int64)
            i_20 = 0_int64
            flg_ = flg_18
            e_ = e_19
            i_ = i_20
            cycle
          end if
        else
          call vtg_other(tb, e_)
        end if
      case (7_int64)
        if ((vtg_kind(e_) == 13_int64)) then
          i_21 = max(0_int64, i_)
          if ((i_21 < vtg_i2(e_))) then
            call vtg_lfinit(tb, e_, i_21)
            call vtg_tr(tb, 7_int64, e_, (1_int64 + i_21))
            call vtg_node(tb, 2_int64, 2_int64)
          else
            call vtg_save(tb)
            call vtg_lfbinds(tb, vtg_s2(e_), vtg_i2(e_))
            call vtg_tr(tb, 0_int64, vtg_kid(e_, vtg_i2(e_)), 0_int64)
            call vtg_restore(tb)
          end if
        else
          call vtg_other(tb, e_)
        end if
      case (8_int64)
        if ((vtg_kind(e_) == 18_int64)) then
          i_22 = max(0_int64, i_)
          if ((i_22 < vtg_ncs(e_))) then
            call vtg_catest(tb, e_, i_22)
            call vtg_save(tb)
            call vtg_bind(tb, vtg_cslot(e_, i_22))
            call vtg_tr(tb, 0_int64, vtg_cbody(e_, i_22), 0_int64)
            call vtg_restore(tb)
            call vtg_tr(tb, 8_int64, e_, (1_int64 + i_22))
            call vtg_node(tb, 1_int64, 3_int64)
          else
            call vtg_rethrow(tb, e_)
          end if
        else
          call vtg_other(tb, e_)
        end if
      case default
        k_23 = vtg_kind(e_)
        select case (k_23)
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
          flg_24 = 1_int64
          e_25 = e_
          i_26 = 0_int64
          flg_ = flg_24
          e_ = e_25
          i_ = i_26
          cycle
        case (5_int64)
          flg_27 = 2_int64
          e_28 = e_
          i_29 = 0_int64
          flg_ = flg_27
          e_ = e_28
          i_ = i_29
          cycle
        case (12_int64)
          if (vtg_lind(e_, 1_int64)) then
            call vtg_tr(tb, 3_int64, e_, 0_int64)
            call vtg_node(tb, 0_int64, vtg_i2(e_))
            call vtg_tr(tb, 5_int64, e_, 0_int64)
            call vtg_node(tb, 4_int64, 2_int64)
          else
            flg_30 = 1_int64
            e_31 = e_
            i_32 = 0_int64
            flg_ = flg_30
            e_ = e_31
            i_ = i_32
            cycle
          end if
        case (16_int64)
          call vtg_tr(tb, 3_int64, e_, 0_int64)
          call vtg_node(tb, 5_int64, vtg_nk(e_))
        case default
          if ((k_23 == 6_int64)) then
            t_33 = (vtg_pk(e_) == 4_int64)
          else
            t_33 = .false.
          end if
          if (t_33) then
            call vtg_hd(tb, e_)
            call vtg_tr(tb, 3_int64, e_, 1_int64)
            call vtg_node(tb, 7_int64, vtg_nk(e_))
          else
            if ((k_23 == 6_int64)) then
              t_34 = (vtg_pk(e_) == 3_int64)
            else
              t_34 = .false.
            end if
            if (t_34) then
              call vtg_hd(tb, e_)
              call vtg_tr(tb, 3_int64, e_, 1_int64)
              call vtg_node(tb, 6_int64, (1_int64 + vtg_nk(e_)))
            else
              if ((k_23 == 6_int64)) then
                t_35 = (.not. (vtg_pk(e_) == 0_int64))
              else
                t_35 = .false.
              end if
              if (t_35) then
                call vtg_hd(tb, e_)
                call vtg_tr(tb, 3_int64, e_, 1_int64)
                call vtg_node(tb, 6_int64, vtg_nk(e_))
              else
                select case (k_23)
                case (6_int64)
                  call vtg_tr(tb, 0_int64, vtg_kid(e_, 0_int64), 0_int64)
                  call vtg_save(tb)
                  call vtg_blank(tb, vtg_kid(e_, 0_int64))
                  call vtg_dead(tb)
                  call vtg_cast(tb)
                  call vtg_top(tb)
                  call vtg_tr(tb, 3_int64, e_, 1_int64)
                  call vtg_node(tb, 8_int64, vtg_nk(e_))
                  call vtg_notfn(tb)
                  call vtg_node(tb, 1_int64, 3_int64)
                  call vtg_restore(tb)
                  call vtg_node(tb, 2_int64, 2_int64)
                case (19_int64)
                  call vtg_tr(tb, 0_int64, vtg_kid(e_, 0_int64), 0_int64)
                  call vtg_save(tb)
                  call vtg_blank(tb, vtg_kid(e_, 0_int64))
                  call vtg_dead(tb)
                  call vtg_tr(tb, 6_int64, e_, 0_int64)
                  call vtg_restore(tb)
                  call vtg_node(tb, 2_int64, 2_int64)
                case (13_int64)
                  flg_36 = 7_int64
                  e_37 = e_
                  i_38 = 0_int64
                  flg_ = flg_36
                  e_ = e_37
                  i_ = i_38
                  cycle
                case (18_int64)
                  call vtg_tr(tb, 0_int64, vtg_kid(e_, 0_int64), 0_int64)
                  call vtg_save(tb)
                  call vtg_blank(tb, vtg_kid(e_, 0_int64))
                  call vtg_tr(tb, 8_int64, e_, 0_int64)
                  call vtg_restore(tb)
                  call vtg_node(tb, 9_int64, 2_int64)
                  if ((1_int64 < vtg_nk(e_))) then
                    call vtg_save(tb)
                    call vtg_blank(tb, vtg_kid(e_, 0_int64))
                    call vtg_blankcs(tb, e_)
                    call vtg_save(tb)
                    call vtg_dead(tb)
                    call vtg_tr(tb, 0_int64, vtg_kid(e_, 1_int64), 0_int64)
                    call vtg_restore(tb)
                    call vtg_rethrow(tb, e_)
                    call vtg_rethrow(tb, e_)
                    call vtg_node(tb, 1_int64, 3_int64)
                    call vtg_node(tb, 9_int64, 2_int64)
                    call vtg_save(tb)
                    call vtg_dead(tb)
                    call vtg_tr(tb, 0_int64, vtg_kid(e_, 1_int64), 0_int64)
                    call vtg_top(tb)
                    call vtg_top(tb)
                    call vtg_node(tb, 1_int64, 3_int64)
                    call vtg_restore(tb)
                    call vtg_restore(tb)
                    call vtg_node(tb, 2_int64, 2_int64)
                  else
                  end if
                case default
                  if (vtg_coll(k_23)) then
                    call vtg_cop(tb, e_)
                    call vtg_tr(tb, 3_int64, e_, 0_int64)
                    call vtg_node(tb, 6_int64, (1_int64 + vtg_nk(e_)))
                  else
                    if ((k_23 == 14_int64)) then
                      call vtg_fnhd(tb, e_)
                      call vtg_caps(tb, e_, 0_int64)
                      call vtg_node(tb, 0_int64, (2_int64 + vtg_ncap(e_)))
                    else
                      if ((k_23 == 15_int64)) then
                        call vtg_cop(tb, e_)
                        call vtg_fnhd(tb, e_)
                        call vtg_caps(tb, e_, 0_int64)
                        call vtg_node(tb, 0_int64, (2_int64 + vtg_ncap(e_)))
                        call vtg_node(tb, 6_int64, 2_int64)
                      else
                        call vtg_other(tb, e_)
                      end if
                    end if
                  end if
                end select
              end if
            end if
          end if
        end select
      end select
      exit
    end do
  end subroutine vtg_tr

  recursive function vtg_tlrw(flg_, e_, i_) result(r)
    integer(int64), value :: flg_
    type(gc_value), value :: e_
    integer(int64), value :: i_
    logical :: r
    integer(int64) :: i_1
    integer(int64) :: k_4
    integer(int64) :: nk_5
    logical :: t_10
    logical :: t_11
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_15
    logical :: t_2
    logical :: t_3
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    if ((flg_ == 1_int64)) then
      i_1 = max(0_int64, i_)
      if ((i_1 < vtg_ncs(e_))) then
        if (vtg_tlrw(0_int64, vtg_cthen(e_, i_1), 0_int64)) then
          t_2 = .true.
        else
          t_2 = vtg_tlrw(1_int64, e_, (1_int64 + i_1))
        end if
        t_3 = t_2
      else
        t_3 = .false.
      end if
      r = t_3
      return
    else
      k_4 = vtg_kind(e_)
      nk_5 = vtg_nk(e_)
      if ((k_4 == 16_int64)) then
        t_15 = .true.
      else
        if ((k_4 == 4_int64)) then
          if (vtg_tlrw(0_int64, vtg_kid(e_, 1_int64), 0_int64)) then
            t_7 = .true.
          else
            if ((2_int64 < nk_5)) then
              t_6 = vtg_tlrw(0_int64, vtg_kid(e_, 2_int64), 0_int64)
            else
              t_6 = .false.
            end if
            t_7 = t_6
          end if
          t_14 = t_7
        else
          if ((k_4 == 5_int64)) then
            if ((nk_5 <= 0_int64)) then
              t_8 = .false.
            else
              t_8 = vtg_tlrw(0_int64, vtg_kid(e_, ((-1_int64) + nk_5)), 0_int64)
            end if
            t_13 = t_8
          else
            if ((k_4 == 11_int64)) then
              t_9 = (k_4 == 11_int64)
            else
              t_9 = (k_4 == 13_int64)
            end if
            if (t_9) then
              t_12 = vtg_tlrw(0_int64, vtg_kid(e_, vtg_i2(e_)), 0_int64)
            else
              if ((k_4 == 19_int64)) then
                if (vtg_tlrw(0_int64, vtg_kid(e_, 1_int64), 0_int64)) then
                  t_10 = .true.
                else
                  t_10 = vtg_tlrw(1_int64, e_, 0_int64)
                end if
                t_11 = t_10
              else
                t_11 = .false.
              end if
              t_12 = t_11
            end if
            t_13 = t_12
          end if
          t_14 = t_13
        end if
        t_15 = t_14
      end if
      r = t_15
      return
    end if
  end function vtg_tlrw

  function vtg_tlr(e_) result(r)
    type(gc_value), value :: e_
    logical :: r
    r = vtg_tlrw(0_int64, e_, 0_int64)
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

  subroutine vtg_inrs(tb, tm_, j_)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: tm_
    integer(int64), value :: j_
    integer(int64) :: j_1
    integer(int64) :: j_3
    type(gc_value) :: tm_2
    do
      j_1 = max(0_int64, j_)
      if ((j_1 < vtg_nin(tm_))) then
        call vtg_capin(tb, vtg_inr(tm_, j_1), j_1)
        tm_2 = tm_
        j_3 = (1_int64 + j_1)
        tm_ = tm_2
        j_ = j_3
        cycle
      else
      end if
      exit
    end do
  end subroutine vtg_inrs

  subroutine vtg_scope(tb, s_, np_, self_, sl_, tm_)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s_
    integer(int64), value :: np_
    integer(int64), value :: self_
    integer(int64), value :: sl_
    type(gc_value), value :: tm_
    call vtg_binds(tb, s_, np_)
    call vtg_inrs(tb, tm_, 0_int64)
    if ((sl_ == 0_int64)) then
    else
      call vtg_bind(tb, self_)
    end if
  end subroutine vtg_scope

  recursive function vtg_scan(flg_, e_, i_, hi_) result(r)
    integer(int64), value :: flg_
    type(gc_value), value :: e_
    integer(int64), value :: i_
    integer(int64), value :: hi_
    logical :: r
    integer(int64) :: i_1
    integer(int64) :: k_18
    integer(int64) :: nk_19
    logical :: t_10
    logical :: t_11
    logical :: t_12
    logical :: t_13
    logical :: t_14
    logical :: t_15
    logical :: t_16
    logical :: t_17
    logical :: t_2
    logical :: t_20
    logical :: t_21
    logical :: t_22
    logical :: t_23
    logical :: t_24
    logical :: t_25
    logical :: t_26
    logical :: t_27
    logical :: t_28
    logical :: t_29
    logical :: t_3
    logical :: t_30
    logical :: t_31
    logical :: t_32
    logical :: t_33
    logical :: t_34
    logical :: t_35
    logical :: t_36
    logical :: t_37
    logical :: t_38
    logical :: t_39
    logical :: t_4
    logical :: t_40
    logical :: t_41
    logical :: t_42
    logical :: t_43
    logical :: t_44
    logical :: t_45
    logical :: t_46
    logical :: t_47
    logical :: t_48
    logical :: t_49
    logical :: t_5
    logical :: t_50
    logical :: t_51
    logical :: t_52
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    i_1 = max(0_int64, i_)
    if ((flg_ == 1_int64)) then
      if ((i_1 < vtg_nk(e_))) then
        if (vtg_scan(0_int64, vtg_kid(e_, i_1), 0_int64, hi_)) then
          t_2 = vtg_scan(1_int64, e_, (1_int64 + i_1), hi_)
        else
          t_2 = .false.
        end if
        t_3 = t_2
      else
        t_3 = .true.
      end if
      t_52 = t_3
    else
      if ((flg_ == 2_int64)) then
        if ((i_1 < vtg_ncs(e_))) then
          if (vtg_scan(0_int64, vtg_cthen(e_, i_1), 0_int64, hi_)) then
            t_4 = vtg_scan(2_int64, e_, (1_int64 + i_1), hi_)
          else
            t_4 = .false.
          end if
          t_5 = t_4
        else
          t_5 = .true.
        end if
        t_51 = t_5
      else
        if ((flg_ == 3_int64)) then
          if ((i_1 < vtg_ncs(e_))) then
            if ((vtg_cslot(e_, i_1) < hi_)) then
              if (vtg_scan(0_int64, vtg_cbody(e_, i_1), 0_int64, hi_)) then
                t_6 = vtg_scan(3_int64, e_, (1_int64 + i_1), hi_)
              else
                t_6 = .false.
              end if
              t_7 = t_6
            else
              t_7 = .false.
            end if
            t_8 = t_7
          else
            t_8 = .true.
          end if
          t_50 = t_8
        else
          if ((flg_ == 4_int64)) then
            if ((vtg_kind(e_) == 13_int64)) then
              t_9 = (i_1 < vtg_i2(e_))
            else
              t_9 = .false.
            end if
            if (t_9) then
              if ((i_1 < vtg_nk(e_))) then
                if (vtg_okn(vtg_kid(e_, i_1))) then
                  if ((vtg_kind(vtg_kid(e_, i_1)) == 14_int64)) then
                    if (vtg_scan(5_int64, vtg_kid(e_, i_1), 0_int64, hi_)) then
                      if (((vtg_s2(e_) + i_1) < hi_)) then
                        t_10 = vtg_scan(4_int64, e_, (1_int64 + i_1), hi_)
                      else
                        t_10 = .false.
                      end if
                      t_11 = t_10
                    else
                      t_11 = .false.
                    end if
                    t_12 = t_11
                  else
                    t_12 = .false.
                  end if
                  t_13 = t_12
                else
                  t_13 = .false.
                end if
                t_14 = t_13
              else
                t_14 = .false.
              end if
              t_15 = t_14
            else
              t_15 = .true.
            end if
            t_49 = t_15
          else
            if ((flg_ == 5_int64)) then
              if ((i_1 < vtg_ncap(e_))) then
                if ((vtg_capo(e_, i_1) < hi_)) then
                  t_16 = vtg_scan(5_int64, e_, (1_int64 + i_1), hi_)
                else
                  t_16 = .false.
                end if
                t_17 = t_16
              else
                t_17 = .true.
              end if
              t_48 = t_17
            else
              if (vtg_okn(e_)) then
                if (vtg_hok(e_)) then
                  k_18 = vtg_kind(e_)
                  nk_19 = vtg_nk(e_)
                  if ((k_18 == 1_int64)) then
                    t_20 = (k_18 == 1_int64)
                  else
                    t_20 = (k_18 == 3_int64)
                  end if
                  if (t_20) then
                    t_45 = .true.
                  else
                    if ((k_18 == 2_int64)) then
                      t_44 = (vtg_i2(e_) < hi_)
                    else
                      if ((k_18 == 4_int64)) then
                        if ((.not. (nk_19 < 2_int64))) then
                          t_21 = vtg_scan(1_int64, e_, 0_int64, hi_)
                        else
                          t_21 = .false.
                        end if
                        t_43 = t_21
                      else
                        if ((k_18 == 19_int64)) then
                          if ((.not. (nk_19 < 2_int64))) then
                            if (vtg_scan(1_int64, e_, 0_int64, hi_)) then
                              t_22 = vtg_scan(2_int64, e_, 0_int64, hi_)
                            else
                              t_22 = .false.
                            end if
                            t_23 = t_22
                          else
                            t_23 = .false.
                          end if
                          t_42 = t_23
                        else
                          if ((k_18 == 6_int64)) then
                            t_24 = (k_18 == 6_int64)
                          else
                            t_24 = (k_18 == 17_int64)
                          end if
                          if (t_24) then
                            if ((.not. (nk_19 < 1_int64))) then
                              t_25 = vtg_scan(1_int64, e_, 0_int64, hi_)
                            else
                              t_25 = .false.
                            end if
                            t_41 = t_25
                          else
                            if ((k_18 == 5_int64)) then
                              t_27 = (k_18 == 5_int64)
                            else
                              if ((k_18 == 16_int64)) then
                                t_26 = (k_18 == 16_int64)
                              else
                                t_26 = vtg_coll(k_18)
                              end if
                              t_27 = t_26
                            end if
                            if (t_27) then
                              t_40 = vtg_scan(1_int64, e_, 0_int64, hi_)
                            else
                              if ((k_18 == 11_int64)) then
                                t_28 = (k_18 == 11_int64)
                              else
                                t_28 = (k_18 == 12_int64)
                              end if
                              if (t_28) then
                                if ((vtg_i2(e_) < nk_19)) then
                                  if ((.not. (hi_ < (vtg_s2(e_) + vtg_i2(e_))))) then
                                    t_29 = vtg_scan(1_int64, e_, 0_int64, hi_)
                                  else
                                    t_29 = .false.
                                  end if
                                  t_30 = t_29
                                else
                                  t_30 = .false.
                                end if
                                t_39 = t_30
                              else
                                if ((k_18 == 13_int64)) then
                                  if ((vtg_i2(e_) < nk_19)) then
                                    if (vtg_scan(4_int64, e_, 0_int64, hi_)) then
                                      t_31 = vtg_scan(0_int64, vtg_kid(e_, vtg_i2(e_)), 0_int64, hi_)
                                    else
                                      t_31 = .false.
                                    end if
                                    t_32 = t_31
                                  else
                                    t_32 = .false.
                                  end if
                                  t_38 = t_32
                                else
                                  if ((k_18 == 14_int64)) then
                                    t_33 = (k_18 == 14_int64)
                                  else
                                    t_33 = (k_18 == 15_int64)
                                  end if
                                  if (t_33) then
                                    t_37 = vtg_scan(5_int64, e_, 0_int64, hi_)
                                  else
                                    if ((k_18 == 18_int64)) then
                                      if ((.not. (nk_19 < 1_int64))) then
                                        if (vtg_scan(1_int64, e_, 0_int64, hi_)) then
                                          t_34 = vtg_scan(3_int64, e_, 0_int64, hi_)
                                        else
                                          t_34 = .false.
                                        end if
                                        t_35 = t_34
                                      else
                                        t_35 = .false.
                                      end if
                                      t_36 = t_35
                                    else
                                      t_36 = vtg_refk(e_)
                                    end if
                                    t_37 = t_36
                                  end if
                                  t_38 = t_37
                                end if
                                t_39 = t_38
                              end if
                              t_40 = t_39
                            end if
                            t_41 = t_40
                          end if
                          t_42 = t_41
                        end if
                        t_43 = t_42
                      end if
                      t_44 = t_43
                    end if
                    t_45 = t_44
                  end if
                  t_46 = t_45
                else
                  t_46 = .false.
                end if
                t_47 = t_46
              else
                t_47 = .false.
              end if
              t_48 = t_47
            end if
            t_49 = t_48
          end if
          t_50 = t_49
        end if
        t_51 = t_50
      end if
      t_52 = t_51
    end if
    r = t_52
    return
  end function vtg_scan

  pure function vtg_inr2(s_, lo_, n_) result(r)
    integer(int64), value :: s_
    integer(int64), value :: lo_
    integer(int64), value :: n_
    logical :: r
    if ((.not. (s_ < lo_))) then
      r = (s_ < (lo_ + n_))
      return
    else
      r = .false.
      return
    end if
  end function vtg_inr2

  recursive function vtg_rds(flg_, e_, i_, s_) result(r)
    integer(int64), value :: flg_
    type(gc_value), value :: e_
    integer(int64), value :: i_
    integer(int64), value :: s_
    logical :: r
    integer(int64) :: i_1
    integer(int64) :: k_11
    logical :: t_10
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
    logical :: t_23
    logical :: t_24
    logical :: t_25
    logical :: t_26
    logical :: t_3
    logical :: t_4
    logical :: t_5
    logical :: t_6
    logical :: t_7
    logical :: t_8
    logical :: t_9
    i_1 = max(0_int64, i_)
    if ((flg_ == 1_int64)) then
      if ((i_1 < vtg_nk(e_))) then
        if (vtg_rds(0_int64, vtg_kid(e_, i_1), 0_int64, s_)) then
          t_2 = .true.
        else
          t_2 = vtg_rds(1_int64, e_, (1_int64 + i_1), s_)
        end if
        t_3 = t_2
      else
        t_3 = .false.
      end if
      t_26 = t_3
    else
      if ((flg_ == 2_int64)) then
        if ((i_1 < vtg_ncs(e_))) then
          if (vtg_rds(0_int64, vtg_cthen(e_, i_1), 0_int64, s_)) then
            t_4 = .true.
          else
            t_4 = vtg_rds(2_int64, e_, (1_int64 + i_1), s_)
          end if
          t_5 = t_4
        else
          t_5 = .false.
        end if
        t_25 = t_5
      else
        if ((flg_ == 3_int64)) then
          if ((i_1 < vtg_ncs(e_))) then
            if ((vtg_cslot(e_, i_1) == s_)) then
              t_7 = .true.
            else
              if (vtg_rds(0_int64, vtg_cbody(e_, i_1), 0_int64, s_)) then
                t_6 = .true.
              else
                t_6 = vtg_rds(3_int64, e_, (1_int64 + i_1), s_)
              end if
              t_7 = t_6
            end if
            t_8 = t_7
          else
            t_8 = .false.
          end if
          t_24 = t_8
        else
          if ((flg_ == 5_int64)) then
            if ((i_1 < vtg_ncap(e_))) then
              if ((vtg_capo(e_, i_1) == s_)) then
                t_9 = .true.
              else
                t_9 = vtg_rds(5_int64, e_, (1_int64 + i_1), s_)
              end if
              t_10 = t_9
            else
              t_10 = .false.
            end if
            t_23 = t_10
          else
            k_11 = vtg_kind(e_)
            if ((k_11 == 2_int64)) then
              t_22 = (vtg_i2(e_) == s_)
            else
              if ((k_11 == 14_int64)) then
                t_12 = (k_11 == 14_int64)
              else
                t_12 = (k_11 == 15_int64)
              end if
              if (t_12) then
                t_21 = vtg_rds(5_int64, e_, 0_int64, s_)
              else
                if ((k_11 == 11_int64)) then
                  t_14 = (k_11 == 11_int64)
                else
                  if ((k_11 == 12_int64)) then
                    t_13 = (k_11 == 12_int64)
                  else
                    t_13 = (k_11 == 13_int64)
                  end if
                  t_14 = t_13
                end if
                if (t_14) then
                  if (vtg_inr2(s_, vtg_s2(e_), vtg_i2(e_))) then
                    t_15 = .true.
                  else
                    t_15 = vtg_rds(1_int64, e_, 0_int64, s_)
                  end if
                  t_20 = t_15
                else
                  if ((k_11 == 18_int64)) then
                    if (vtg_rds(1_int64, e_, 0_int64, s_)) then
                      t_16 = .true.
                    else
                      t_16 = vtg_rds(3_int64, e_, 0_int64, s_)
                    end if
                    t_19 = t_16
                  else
                    if ((k_11 == 19_int64)) then
                      if (vtg_rds(1_int64, e_, 0_int64, s_)) then
                        t_17 = .true.
                      else
                        t_17 = vtg_rds(2_int64, e_, 0_int64, s_)
                      end if
                      t_18 = t_17
                    else
                      t_18 = vtg_rds(1_int64, e_, 0_int64, s_)
                    end if
                    t_19 = t_18
                  end if
                  t_20 = t_19
                end if
                t_21 = t_20
              end if
              t_22 = t_21
            end if
            t_23 = t_22
          end if
          t_24 = t_23
        end if
        t_25 = t_24
      end if
      t_26 = t_25
    end if
    r = t_26
    return
  end function vtg_rds

  subroutine vtg_ars(tb, ars_, j_, tm_, ns_, self_)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: ars_
    integer(int64), value :: j_
    type(gc_value), value :: tm_
    integer(int64), value :: ns_
    integer(int64), value :: self_
    type(gc_value) :: ars_2
    integer(int64) :: j_1
    integer(int64) :: j_3
    integer(int64) :: ns_5
    integer(int64) :: self_6
    type(gc_value) :: tm_4
    do
      j_1 = max(0_int64, j_)
      if ((j_1 < vtg_nar(ars_))) then
        call vtg_arity(tb, vtg_ar(ars_, j_1), tm_, ns_, self_)
        ars_2 = ars_
        j_3 = (1_int64 + j_1)
        tm_4 = tm_
        ns_5 = ns_
        self_6 = self_
        ars_ = ars_2
        j_ = j_3
        tm_ = tm_4
        ns_ = ns_5
        self_ = self_6
        cycle
      else
      end if
      exit
    end do
  end subroutine vtg_ars

  subroutine vtg_fncl(tb, ars_, tm_, ns_, self_, name_)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: ars_
    type(gc_value), value :: tm_
    integer(int64), value :: ns_
    integer(int64), value :: self_
    type(gc_value), value :: name_
    call vtg_ars(tb, ars_, 0_int64, tm_, ns_, self_)
    call vtg_arcl(tb, name_)
    call vtg_node(tb, 0_int64, (1_int64 + vtg_nar(ars_)))
  end subroutine vtg_fncl

  function vtg_sl(body_, self_) result(r)
    type(gc_value), value :: body_
    integer(int64), value :: self_
    integer(int64) :: r
    logical :: t_1
    if ((.not. (self_ < 0_int64))) then
      t_1 = vtg_rds(0_int64, body_, 0_int64, self_)
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
  end function vtg_sl
