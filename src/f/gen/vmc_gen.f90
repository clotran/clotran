! GENERATED from model/vmicg.lisp by scripts/acl2-fortran. Do not edit:
! change the model, prove it, and generate again (PLAN step 30).
! Every function here has its guards verified in ACL2: every index in
! bounds, every integer inside 64 bits. vmicg-correct proves that a
! program vmicg_program compiles without an error or an overflow
! answers, run, what it means.
module vmc_gen
  use iso_fortran_env, only: int64
  use vm_runtime
  implicit none
contains
  pure function vmicg_sat(x_) result(r)
    integer(int64), value :: x_
    integer(int64) :: r
    if ((x_ < 1099511627776_int64)) then
      r = x_
      return
    else
      r = 1099511627776_int64
      return
    end if
  end function vmicg_sat

  function vmicg_len_acc(x_, acc_) result(r)
    type(value), value :: x_
    integer(int64), value :: acc_
    integer(int64) :: r
    integer(int64) :: acc_4
    logical :: t_1
    integer(int64) :: var_3
    type(value) :: x_2
    do
      if (rt_consp(x_)) then
        t_1 = (max(0_int64, acc_) < 1099511627776_int64)
      else
        t_1 = .false.
      end if
      if (t_1) then
        x_2 = rt_cdr(x_)
        var_3 = (1_int64 + max(0_int64, acc_))
        acc_4 = var_3
        x_ = x_2
        acc_ = acc_4
        cycle
      else
        r = max(0_int64, acc_)
        return
      end if
    end do
  end function vmicg_len_acc

  function vmicg_len(x_) result(r)
    type(value), value :: x_
    integer(int64) :: r
    r = vmicg_len_acc(x_, 0_int64)
    return
  end function vmicg_len

  recursive function vmicg_size(e_) result(r)
    type(value), value :: e_
    integer(int64) :: r
    type(value) :: op_1
    integer(int64) :: t_13
    integer(int64) :: t_14
    integer(int64) :: t_15
    integer(int64) :: t_16
    integer(int64) :: t_17
    integer(int64) :: t_18
    integer(int64) :: t_19
    integer(int64) :: t_20
    integer(int64) :: t_21
    integer(int64) :: t_22
    logical :: t_4
    integer(int64) :: var_10
    integer(int64) :: var_11
    integer(int64) :: var_12
    integer(int64) :: var_2
    integer(int64) :: var_3
    integer(int64) :: var_5
    integer(int64) :: var_6
    integer(int64) :: var_7
    integer(int64) :: var_8
    integer(int64) :: var_9
    op_1 = rt_car(e_)
    if (rt_is(op_1, rt_keyword("if"))) then
      var_2 = (vmicg_size(rt_car(rt_cdr(e_))) + (1_int64 + (vmicg_size(rt_car(rt_cdr(rt_cdr(e_)))) + (1_int64 + vmicg_size(rt_car(rt_cdr(rt_cdr(rt_cdr(e_)))))))))
      t_22 = vmicg_sat(var_2)
    else
      if (rt_is(op_1, rt_keyword("let"))) then
        var_3 = (vmicg_size(rt_car(rt_cdr(e_))) + (vmicg_size(rt_car(rt_cdr(rt_cdr(e_)))) + 1_int64))
        t_21 = vmicg_sat(var_3)
      else
        if (rt_is(op_1, rt_keyword("add"))) then
          t_4 = rt_is(op_1, rt_keyword("add"))
        else
          t_4 = rt_is(op_1, rt_keyword("lt"))
        end if
        if (t_4) then
          var_5 = (vmicg_size(rt_car(rt_cdr(e_))) + (vmicg_size(rt_car(rt_cdr(rt_cdr(e_)))) + 1_int64))
          t_20 = vmicg_sat(var_5)
        else
          if (rt_is(op_1, rt_keyword("mkclo"))) then
            var_6 = (vmicg_size_args(rt_cdr(rt_cdr(e_))) + 1_int64)
            t_19 = vmicg_sat(var_6)
          else
            if (rt_is(op_1, rt_keyword("callv"))) then
              var_7 = (vmicg_size_args(rt_cdr(rt_cdr(e_))) + (vmicg_size(rt_car(rt_cdr(e_))) + 1_int64))
              t_18 = vmicg_sat(var_7)
            else
              if (rt_is(op_1, rt_keyword("loop"))) then
                var_8 = (vmicg_size_args(rt_car(rt_cdr(e_))) + (vmicg_size(rt_car(rt_cdr(rt_cdr(e_)))) + vmicg_len(rt_car(rt_cdr(e_)))))
                t_17 = vmicg_sat(var_8)
              else
                if (rt_is(op_1, rt_keyword("recur"))) then
                  var_9 = (vmicg_size_args(rt_cdr(e_)) + 1_int64)
                  t_16 = vmicg_sat(var_9)
                else
                  if (rt_is(op_1, rt_keyword("prim"))) then
                    var_10 = (vmicg_size_args(rt_cdr(rt_cdr(e_))) + 1_int64)
                    t_15 = vmicg_sat(var_10)
                  else
                    if (rt_is(op_1, rt_keyword("throw"))) then
                      var_11 = (vmicg_size(rt_car(rt_cdr(e_))) + 1_int64)
                      t_14 = vmicg_sat(var_11)
                    else
                      if (rt_is(op_1, rt_keyword("try"))) then
                        var_12 = (1_int64 + (vmicg_size(rt_car(rt_cdr(e_))) + (2_int64 + (vmicg_size(rt_car(rt_cdr(rt_cdr(e_)))) + 1_int64))))
                        t_13 = vmicg_sat(var_12)
                      else
                        t_13 = 1_int64
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
            t_19 = t_18
          end if
          t_20 = t_19
        end if
        t_21 = t_20
      end if
      t_22 = t_21
    end if
    r = t_22
    return
  end function vmicg_size

  recursive function vmicg_size_args(es_) result(r)
    type(value), value :: es_
    integer(int64) :: r
    integer(int64) :: var_1
    if (rt_consp(es_)) then
      var_1 = (vmicg_size(rt_car(es_)) + vmicg_size_args(rt_cdr(es_)))
      r = vmicg_sat(var_1)
      return
    else
      r = 0_int64
      return
    end if
  end function vmicg_size_args

  recursive function vmicg_size_clauses(cls_) result(r)
    type(value), value :: cls_
    integer(int64) :: r
    integer(int64) :: var_1
    if (rt_consp(cls_)) then
      var_1 = (vmicg_size(rt_car(rt_cdr(rt_car(cls_)))) + (1_int64 + vmicg_size_clauses(rt_cdr(cls_))))
      r = vmicg_sat(var_1)
      return
    else
      r = 0_int64
      return
    end if
  end function vmicg_size_clauses

  recursive function vmicg_size_defs(defs_) result(r)
    type(value), value :: defs_
    integer(int64) :: r
    integer(int64) :: var_1
    if (rt_consp(defs_)) then
      var_1 = (vmicg_size_clauses(rt_cdr(rt_car(defs_))) + vmicg_size_defs(rt_cdr(defs_)))
      r = vmicg_sat(var_1)
      return
    else
      r = 0_int64
      return
    end if
  end function vmicg_size_defs

  recursive function vmicg_nclauses(defs_) result(r)
    type(value), value :: defs_
    integer(int64) :: r
    integer(int64) :: var_1
    if (rt_consp(defs_)) then
      var_1 = (vmicg_len(rt_cdr(rt_car(defs_))) + vmicg_nclauses(rt_cdr(defs_)))
      r = vmicg_sat(var_1)
      return
    else
      r = 0_int64
      return
    end if
  end function vmicg_nclauses

  subroutine vmicg_put(st, pc_, op_, a_, b_, c_, k_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: pc_
    integer(int64), value :: op_
    integer(int64), value :: a_
    integer(int64), value :: b_
    integer(int64), value :: c_
    type(value), value :: k_
    integer(int64) :: i_11
    integer(int64) :: i_14
    integer(int64) :: i_16
    integer(int64) :: i_2
    integer(int64) :: i_5
    integer(int64) :: i_8
    logical :: t_4
    integer(int64) :: v_12
    integer(int64) :: v_15
    type(value) :: v_17
    integer(int64) :: v_6
    integer(int64) :: v_9
    integer(int64) :: var_1
    integer(int64) :: var_10
    integer(int64) :: var_13
    integer(int64) :: var_3
    integer(int64) :: var_7
    var_1 = (4_int64 * max(0_int64, pc_))
    i_2 = var_1
    var_3 = (i_2 + 3_int64)
    if ((var_3 < size(st%code, kind=int64))) then
      t_4 = (max(0_int64, pc_) < size(st%pool, kind=int64))
    else
      t_4 = .false.
    end if
    if (t_4) then
      i_5 = i_2
      v_6 = op_
      st%code(i_5) = v_6
      var_7 = (i_2 + 1_int64)
      i_8 = var_7
      v_9 = a_
      st%code(i_8) = v_9
      var_10 = (i_2 + 2_int64)
      i_11 = var_10
      v_12 = b_
      st%code(i_11) = v_12
      var_13 = (i_2 + 3_int64)
      i_14 = var_13
      v_15 = c_
      st%code(i_14) = v_15
      i_16 = max(0_int64, pc_)
      v_17 = k_
      st%pool(i_16) = v_17
    else
      st%status = 2_int64
    end if
  end subroutine vmicg_put

  subroutine vmicg_fail(ce)
    type(vc_state), intent(inout) :: ce
    ce%err = 1_int64
  end subroutine vmicg_fail

  subroutine vmicg_set(ce, n_, x_)
    type(vc_state), intent(inout) :: ce
    integer(int64), value :: n_
    integer(int64), value :: x_
    integer(int64) :: i_1
    integer(int64) :: v_2
    if ((max(0_int64, n_) < size(ce%env, kind=int64))) then
      i_1 = max(0_int64, n_)
      v_2 = x_
      ce%env(i_1) = v_2
    else
      call vmicg_fail(ce)
    end if
  end subroutine vmicg_set

  pure function vmicg_get(ce, i_) result(r)
    type(vc_state), intent(in) :: ce
    integer(int64), value :: i_
    integer(int64) :: r
    if ((max(0_int64, i_) < size(ce%env, kind=int64))) then
      r = ce%env(max(0_int64, i_))
      return
    else
      r = 0_int64
      return
    end if
  end function vmicg_get

  subroutine vmicg_count(ce, n_, d_, k_)
    type(vc_state), intent(inout) :: ce
    integer(int64), value :: n_
    integer(int64), value :: d_
    integer(int64), value :: k_
    integer(int64) :: d_4
    integer(int64) :: k_5
    integer(int64) :: n_2
    integer(int64) :: var_1
    integer(int64) :: var_3
    do
      if ((k_ <= 0_int64)) then
      else
        call vmicg_set(ce, n_, d_)
        var_1 = (1_int64 + max(0_int64, n_))
        n_2 = var_1
        var_3 = (1_int64 + max(0_int64, d_))
        d_4 = var_3
        k_5 = (-1_int64 + k_)
        n_ = n_2
        d_ = d_4
        k_ = k_5
        cycle
      end if
      exit
    end do
  end subroutine vmicg_count

  subroutine vmicg_slides(st, pc_, k_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: pc_
    integer(int64), value :: k_
    integer(int64) :: k_3
    integer(int64) :: pc_2
    integer(int64) :: var_1
    do
      if ((k_ <= 0_int64)) then
      else
        call vmicg_put(st, pc_, 5_int64, 0_int64, 0_int64, 0_int64, rt_nil())
        var_1 = (1_int64 + max(0_int64, pc_))
        pc_2 = var_1
        k_3 = (-1_int64 + k_)
        pc_ = pc_2
        k_ = k_3
        cycle
      end if
      exit
    end do
  end subroutine vmicg_slides

  recursive subroutine vmicg_compile(st, ce, e_, depth_, n_, self_, pc_, lch_, lcb_, lck_, r)
    type(vm_state), intent(inout) :: st
    type(vc_state), intent(inout) :: ce
    type(value), value :: e_
    integer(int64), value :: depth_
    integer(int64), value :: n_
    integer(int64), value :: self_
    integer(int64), value :: pc_
    integer(int64), value :: lch_
    integer(int64), value :: lcb_
    integer(int64), value :: lck_
    integer(int64), intent(out) :: r
    integer(int64) :: depth_3
    integer(int64) :: f_40
    integer(int64) :: head_52
    integer(int64) :: i_10
    integer(int64) :: i_6
    integer(int64) :: k_43
    integer(int64) :: k_50
    integer(int64) :: mv_14
    integer(int64) :: mv_16
    integer(int64) :: mv_19
    integer(int64) :: mv_23
    integer(int64) :: mv_25
    integer(int64) :: mv_31
    integer(int64) :: mv_33
    integer(int64) :: mv_38
    integer(int64) :: mv_44
    integer(int64) :: mv_46
    integer(int64) :: mv_51
    integer(int64) :: mv_53
    integer(int64) :: mv_58
    integer(int64) :: mv_61
    integer(int64) :: mv_64
    integer(int64) :: mv_67
    integer(int64) :: mv_70
    integer(int64) :: n_4
    type(value) :: op_1
    integer(int64) :: pa_15
    integer(int64) :: pa_24
    integer(int64) :: pa_32
    integer(int64) :: pa_39
    integer(int64) :: pa_45
    integer(int64) :: pa_59
    integer(int64) :: pa_62
    integer(int64) :: pa_65
    integer(int64) :: pb_18
    integer(int64) :: pb_28
    integer(int64) :: pb_35
    integer(int64) :: pb_48
    integer(int64) :: pb_56
    integer(int64) :: pb_69
    integer(int64) :: pc2_21
    integer(int64) :: pc_2
    integer(int64) :: ph_74
    logical :: t_30
    integer(int64) :: t_36
    logical :: t_7
    integer(int64) :: var_11
    integer(int64) :: var_12
    integer(int64) :: var_13
    integer(int64) :: var_17
    integer(int64) :: var_20
    integer(int64) :: var_22
    integer(int64) :: var_26
    integer(int64) :: var_27
    integer(int64) :: var_29
    integer(int64) :: var_34
    integer(int64) :: var_37
    integer(int64) :: var_41
    integer(int64) :: var_42
    integer(int64) :: var_47
    integer(int64) :: var_49
    integer(int64) :: var_5
    integer(int64) :: var_54
    integer(int64) :: var_55
    integer(int64) :: var_57
    integer(int64) :: var_60
    integer(int64) :: var_63
    integer(int64) :: var_66
    integer(int64) :: var_68
    integer(int64) :: var_71
    integer(int64) :: var_72
    integer(int64) :: var_73
    integer(int64) :: var_75
    integer(int64) :: var_76
    integer(int64) :: var_77
    integer(int64) :: var_78
    integer(int64) :: var_79
    integer(int64) :: var_8
    integer(int64) :: var_9
    op_1 = rt_car(e_)
    pc_2 = max(0_int64, pc_)
    depth_3 = max(0_int64, depth_)
    n_4 = max(0_int64, n_)
    if (rt_is(op_1, rt_keyword("const"))) then
      call vmicg_put(st, pc_2, 1_int64, pc_2, 0_int64, 0_int64, rt_car(rt_cdr(e_)))
      var_5 = (1_int64 + pc_2)
      r = var_5
    else
      if (rt_is(op_1, rt_keyword("local"))) then
        i_6 = rt_nat(rt_car(rt_cdr(e_)))
        if ((i_6 < 0_int64)) then
          t_7 = (i_6 < 0_int64)
        else
          t_7 = (.not. (i_6 < n_4))
        end if
        if (t_7) then
          call vmicg_fail(ce)
          var_8 = (1_int64 + pc_2)
          r = var_8
        else
          call vmicg_put(st, pc_2, 2_int64, vmicg_get(ce, i_6), 0_int64, 0_int64, rt_nil())
          var_9 = (1_int64 + pc_2)
          r = var_9
        end if
      else
        if (rt_is(op_1, rt_keyword("capt"))) then
          if ((.not. (self_ < 0_int64))) then
            i_10 = rt_nat(rt_car(rt_cdr(e_)))
            if ((i_10 < 0_int64)) then
              call vmicg_fail(ce)
              var_11 = (1_int64 + pc_2)
              r = var_11
            else
              call vmicg_put(st, pc_2, 9_int64, self_, i_10, 0_int64, rt_nil())
              var_12 = (1_int64 + pc_2)
              r = var_12
            end if
          else
            call vmicg_put(st, pc_2, 1_int64, pc_2, 0_int64, 0_int64, rt_nil())
            var_13 = (1_int64 + pc_2)
            r = var_13
          end if
        else
          if (rt_is(op_1, rt_keyword("if"))) then
            call vmicg_compile(st, ce, rt_car(rt_cdr(e_)), depth_3, n_4, self_, pc_2, -1_int64, 0_int64, 0_int64, mv_14)
            pa_15 = mv_14
            var_17 = (1_int64 + pa_15)
            call vmicg_compile(st, ce, rt_car(rt_cdr(rt_cdr(e_))), depth_3, n_4, self_, var_17, lch_, lcb_, lck_, mv_16)
            pb_18 = mv_16
            var_20 = (1_int64 + pb_18)
            call vmicg_compile(st, ce, rt_car(rt_cdr(rt_cdr(rt_cdr(e_)))), depth_3, n_4, self_, var_20, lch_, lcb_, lck_, mv_19)
            pc2_21 = mv_19
            var_22 = (1_int64 + pb_18)
            call vmicg_put(st, pa_15, 6_int64, var_22, 0_int64, 0_int64, rt_nil())
            call vmicg_put(st, pb_18, 7_int64, pc2_21, 0_int64, 0_int64, rt_nil())
            r = pc2_21
          else
            if (rt_is(op_1, rt_keyword("let"))) then
              call vmicg_compile(st, ce, rt_car(rt_cdr(e_)), depth_3, n_4, self_, pc_2, -1_int64, 0_int64, 0_int64, mv_23)
              pa_24 = mv_23
              call vmicg_set(ce, n_4, depth_3)
              var_26 = (1_int64 + depth_3)
              var_27 = (1_int64 + n_4)
              call vmicg_compile(st, ce, rt_car(rt_cdr(rt_cdr(e_))), var_26, var_27, self_, pa_24, lch_, lcb_, lck_, mv_25)
              pb_28 = mv_25
              call vmicg_put(st, pb_28, 5_int64, 0_int64, 0_int64, 0_int64, rt_nil())
              var_29 = (1_int64 + pb_28)
              r = var_29
            else
              if (rt_is(op_1, rt_keyword("add"))) then
                t_30 = rt_is(op_1, rt_keyword("add"))
              else
                t_30 = rt_is(op_1, rt_keyword("lt"))
              end if
              if (t_30) then
                call vmicg_compile(st, ce, rt_car(rt_cdr(e_)), depth_3, n_4, self_, pc_2, -1_int64, 0_int64, 0_int64, mv_31)
                pa_32 = mv_31
                var_34 = (1_int64 + depth_3)
                call vmicg_compile(st, ce, rt_car(rt_cdr(rt_cdr(e_))), var_34, n_4, self_, pa_32, -1_int64, 0_int64, 0_int64, mv_33)
                pb_35 = mv_33
                if (rt_is(op_1, rt_keyword("add"))) then
                  t_36 = 3_int64
                else
                  t_36 = 4_int64
                end if
                call vmicg_put(st, pb_35, t_36, 0_int64, 0_int64, 0_int64, rt_nil())
                var_37 = (1_int64 + pb_35)
                r = var_37
              else
                if (rt_is(op_1, rt_keyword("mkclo"))) then
                  call vmicg_compile_args(st, ce, rt_cdr(rt_cdr(e_)), depth_3, n_4, self_, pc_2, mv_38)
                  pa_39 = mv_38
                  f_40 = rt_nat(rt_car(rt_cdr(e_)))
                  if ((f_40 < 0_int64)) then
                    call vmicg_fail(ce)
                    var_41 = (1_int64 + pa_39)
                    r = var_41
                  else
                    call vmicg_put(st, pa_39, 8_int64, f_40, rt_len(rt_cdr(rt_cdr(e_))), 0_int64, rt_nil())
                    var_42 = (1_int64 + pa_39)
                    r = var_42
                  end if
                else
                  if (rt_is(op_1, rt_keyword("callv"))) then
                    k_43 = rt_len(rt_cdr(rt_cdr(e_)))
                    call vmicg_compile_args(st, ce, rt_cdr(rt_cdr(e_)), depth_3, n_4, self_, pc_2, mv_44)
                    pa_45 = mv_44
                    var_47 = (depth_3 + k_43)
                    call vmicg_compile(st, ce, rt_car(rt_cdr(e_)), var_47, n_4, self_, pa_45, -1_int64, 0_int64, 0_int64, mv_46)
                    pb_48 = mv_46
                    call vmicg_put(st, pb_48, 10_int64, k_43, 0_int64, 0_int64, rt_nil())
                    var_49 = (1_int64 + pb_48)
                    r = var_49
                  else
                    if (rt_is(op_1, rt_keyword("loop"))) then
                      k_50 = rt_len(rt_car(rt_cdr(e_)))
                      call vmicg_compile_args(st, ce, rt_car(rt_cdr(e_)), depth_3, n_4, self_, pc_2, mv_51)
                      head_52 = mv_51
                      call vmicg_count(ce, n_4, depth_3, k_50)
                      var_54 = (depth_3 + k_50)
                      var_55 = (n_4 + k_50)
                      call vmicg_compile(st, ce, rt_car(rt_cdr(rt_cdr(e_))), var_54, var_55, self_, head_52, head_52, depth_3, k_50, mv_53)
                      pb_56 = mv_53
                      call vmicg_slides(st, pb_56, k_50)
                      var_57 = (pb_56 + k_50)
                      r = var_57
                    else
                      if (rt_is(op_1, rt_keyword("recur"))) then
                        call vmicg_compile_args(st, ce, rt_cdr(e_), depth_3, n_4, self_, pc_2, mv_58)
                        pa_59 = mv_58
                        if ((lch_ < 0_int64)) then
                          call vmicg_put(st, pa_59, 12_int64, 0_int64, 0_int64, 0_int64, rt_nil())
                        else
                          call vmicg_put(st, pa_59, 12_int64, max(0_int64, lck_), max(0_int64, lcb_), max(0_int64, lch_), rt_nil())
                        end if
                        var_60 = (1_int64 + pa_59)
                        r = var_60
                      else
                        if (rt_is(op_1, rt_keyword("prim"))) then
                          call vmicg_compile_args(st, ce, rt_cdr(rt_cdr(e_)), depth_3, n_4, self_, pc_2, mv_61)
                          pa_62 = mv_61
                          call vmicg_put(st, pa_62, 13_int64, pa_62, rt_len(rt_cdr(rt_cdr(e_))), 0_int64, rt_car(rt_cdr(e_)))
                          var_63 = (1_int64 + pa_62)
                          r = var_63
                        else
                          if (rt_is(op_1, rt_keyword("throw"))) then
                            call vmicg_compile(st, ce, rt_car(rt_cdr(e_)), depth_3, n_4, self_, pc_2, -1_int64, 0_int64, 0_int64, mv_64)
                            pa_65 = mv_64
                            call vmicg_put(st, pa_65, 14_int64, 0_int64, 0_int64, 0_int64, rt_nil())
                            var_66 = (1_int64 + pa_65)
                            r = var_66
                          else
                            if (rt_is(op_1, rt_keyword("try"))) then
                              var_68 = (1_int64 + pc_2)
                              call vmicg_compile(st, ce, rt_car(rt_cdr(e_)), depth_3, n_4, self_, var_68, -1_int64, 0_int64, 0_int64, mv_67)
                              pb_69 = mv_67
                              call vmicg_set(ce, n_4, depth_3)
                              var_71 = (1_int64 + depth_3)
                              var_72 = (1_int64 + n_4)
                              var_73 = (pb_69 + 2_int64)
                              call vmicg_compile(st, ce, rt_car(rt_cdr(rt_cdr(e_))), var_71, var_72, self_, var_73, -1_int64, 0_int64, 0_int64, mv_70)
                              ph_74 = mv_70
                              var_75 = (pb_69 + 2_int64)
                              call vmicg_put(st, pc_2, 15_int64, var_75, depth_3, 0_int64, rt_nil())
                              call vmicg_put(st, pb_69, 16_int64, 0_int64, 0_int64, 0_int64, rt_nil())
                              var_76 = (1_int64 + pb_69)
                              var_77 = (1_int64 + ph_74)
                              call vmicg_put(st, var_76, 7_int64, var_77, 0_int64, 0_int64, rt_nil())
                              call vmicg_put(st, ph_74, 5_int64, 0_int64, 0_int64, 0_int64, rt_nil())
                              var_78 = (1_int64 + ph_74)
                              r = var_78
                            else
                              call vmicg_put(st, pc_2, 1_int64, pc_2, 0_int64, 0_int64, rt_nil())
                              var_79 = (1_int64 + pc_2)
                              r = var_79
                            end if
                          end if
                        end if
                      end if
                    end if
                  end if
                end if
              end if
            end if
          end if
        end if
      end if
    end if
  end subroutine vmicg_compile

  recursive subroutine vmicg_compile_args(st, ce, es_, depth_, n_, self_, pc_, r)
    type(vm_state), intent(inout) :: st
    type(vc_state), intent(inout) :: ce
    type(value), value :: es_
    integer(int64), value :: depth_
    integer(int64), value :: n_
    integer(int64), value :: self_
    integer(int64), value :: pc_
    integer(int64), intent(out) :: r
    integer(int64) :: depth_5
    type(value) :: es_3
    integer(int64) :: mv_1
    integer(int64) :: n_6
    integer(int64) :: pa_2
    integer(int64) :: pc_8
    integer(int64) :: self_7
    integer(int64) :: var_4
    do
      if (rt_consp(es_)) then
        call vmicg_compile(st, ce, rt_car(es_), depth_, n_, self_, pc_, -1_int64, 0_int64, 0_int64, mv_1)
        pa_2 = mv_1
        es_3 = rt_cdr(es_)
        var_4 = (1_int64 + max(0_int64, depth_))
        depth_5 = var_4
        n_6 = n_
        self_7 = self_
        pc_8 = pa_2
        es_ = es_3
        depth_ = depth_5
        n_ = n_6
        self_ = self_7
        pc_ = pc_8
        cycle
      else
        r = max(0_int64, pc_)
      end if
      exit
    end do
  end subroutine vmicg_compile_args

  subroutine vmicg_body(st, ce, cl_, pc_, r)
    type(vm_state), intent(inout) :: st
    type(vc_state), intent(inout) :: ce
    type(value), value :: cl_
    integer(int64), value :: pc_
    integer(int64), intent(out) :: r
    integer(int64) :: mv_6
    integer(int64) :: n_1
    integer(int64) :: nl_5
    integer(int64) :: pa_8
    logical :: rest_2
    integer(int64) :: t_4
    integer(int64) :: var_3
    integer(int64) :: var_7
    integer(int64) :: var_9
    n_1 = rt_nat(rt_car(cl_))
    rest_2 = rt_is(rt_car(rt_cdr(rt_cdr(cl_))), rt_keyword("rest"))
    if ((n_1 < 0_int64)) then
      call vmicg_fail(ce)
      r = max(0_int64, pc_)
    else
      if (rest_2) then
        var_3 = (1_int64 + n_1)
        t_4 = var_3
      else
        t_4 = n_1
      end if
      nl_5 = t_4
      call vmicg_count(ce, 0_int64, 0_int64, nl_5)
      var_7 = (1_int64 + nl_5)
      call vmicg_compile(st, ce, rt_car(rt_cdr(cl_)), var_7, nl_5, nl_5, pc_, -1_int64, 0_int64, 0_int64, mv_6)
      pa_8 = mv_6
      call vmicg_put(st, pa_8, 11_int64, 0_int64, 0_int64, 0_int64, rt_nil())
      var_9 = (1_int64 + pa_8)
      r = var_9
    end if
  end subroutine vmicg_body

  subroutine vmicg_clause_entry(st, ci_, n_, pc_, rest_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: ci_
    integer(int64), value :: n_
    integer(int64), value :: pc_
    integer(int64), value :: rest_
    integer(int64) :: i_3
    integer(int64) :: i_5
    integer(int64) :: i_7
    logical :: t_1
    logical :: t_2
    integer(int64) :: v_4
    integer(int64) :: v_6
    integer(int64) :: v_8
    if ((max(0_int64, ci_) < size(st%cln, kind=int64))) then
      if ((max(0_int64, ci_) < size(st%clent, kind=int64))) then
        t_1 = (max(0_int64, ci_) < size(st%clrest, kind=int64))
      else
        t_1 = .false.
      end if
      t_2 = t_1
    else
      t_2 = .false.
    end if
    if (t_2) then
      i_3 = max(0_int64, ci_)
      v_4 = n_
      st%cln(i_3) = v_4
      i_5 = max(0_int64, ci_)
      v_6 = pc_
      st%clent(i_5) = v_6
      i_7 = max(0_int64, ci_)
      v_8 = rest_
      st%clrest(i_7) = v_8
    else
      st%status = 2_int64
    end if
  end subroutine vmicg_clause_entry

  subroutine vmicg_fn_entry(st, f_, ci_, count_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: f_
    integer(int64), value :: ci_
    integer(int64), value :: count_
    integer(int64) :: i_2
    integer(int64) :: i_4
    logical :: t_1
    integer(int64) :: v_3
    integer(int64) :: v_5
    if ((max(0_int64, f_) < size(st%fnfirst, kind=int64))) then
      t_1 = (max(0_int64, f_) < size(st%fncount, kind=int64))
    else
      t_1 = .false.
    end if
    if (t_1) then
      i_2 = max(0_int64, f_)
      v_3 = ci_
      st%fnfirst(i_2) = v_3
      i_4 = max(0_int64, f_)
      v_5 = count_
      st%fncount(i_4) = v_5
    else
      st%status = 2_int64
    end if
  end subroutine vmicg_fn_entry

  subroutine vmicg_clauses(st, ce, cls_, ci_, pc_, r)
    type(vm_state), intent(inout) :: st
    type(vc_state), intent(inout) :: ce
    type(value), value :: cls_
    integer(int64), value :: ci_
    integer(int64), value :: pc_
    integer(int64), intent(out) :: r
    integer(int64) :: ci_8
    type(value) :: cl_1
    type(value) :: cls_6
    integer(int64) :: mv_4
    integer(int64) :: n_2
    integer(int64) :: pa_5
    integer(int64) :: pc_9
    integer(int64) :: t_3
    integer(int64) :: var_7
    do
      if (rt_consp(cls_)) then
        cl_1 = rt_car(cls_)
        n_2 = rt_nat(rt_car(cl_1))
        if (rt_is(rt_car(rt_cdr(rt_cdr(cl_1))), rt_keyword("rest"))) then
          t_3 = 1_int64
        else
          t_3 = 0_int64
        end if
        call vmicg_clause_entry(st, ci_, max(0_int64, n_2), max(0_int64, pc_), t_3)
        call vmicg_body(st, ce, cl_1, pc_, mv_4)
        pa_5 = mv_4
        cls_6 = rt_cdr(cls_)
        var_7 = (1_int64 + max(0_int64, ci_))
        ci_8 = var_7
        pc_9 = pa_5
        cls_ = cls_6
        ci_ = ci_8
        pc_ = pc_9
        cycle
      else
        r = max(0_int64, pc_)
      end if
      exit
    end do
  end subroutine vmicg_clauses

  subroutine vmicg_defs(st, ce, defs_, f_, ci_, pc_, r)
    type(vm_state), intent(inout) :: st
    type(vc_state), intent(inout) :: ce
    type(value), value :: defs_
    integer(int64), value :: f_
    integer(int64), value :: ci_
    integer(int64), value :: pc_
    integer(int64), intent(out) :: r
    integer(int64) :: ci_9
    type(value) :: cls_2
    type(value) :: d_1
    type(value) :: defs_5
    integer(int64) :: f_7
    integer(int64) :: mv_3
    integer(int64) :: pa_4
    integer(int64) :: pc_10
    integer(int64) :: var_6
    integer(int64) :: var_8
    do
      if (rt_consp(defs_)) then
        d_1 = rt_car(defs_)
        cls_2 = rt_cdr(d_1)
        if ((rt_nat(rt_car(d_1)) == max(0_int64, f_))) then
        else
          call vmicg_fail(ce)
        end if
        call vmicg_fn_entry(st, f_, max(0_int64, ci_), rt_len(cls_2))
        call vmicg_clauses(st, ce, cls_2, ci_, pc_, mv_3)
        pa_4 = mv_3
        defs_5 = rt_cdr(defs_)
        var_6 = (1_int64 + max(0_int64, f_))
        f_7 = var_6
        var_8 = (max(0_int64, ci_) + rt_len(cls_2))
        ci_9 = var_8
        pc_10 = pa_4
        defs_ = defs_5
        f_ = f_7
        ci_ = ci_9
        pc_ = pc_10
        cycle
      else
        r = max(0_int64, pc_)
      end if
      exit
    end do
  end subroutine vmicg_defs

  subroutine vmicg_resize(st, n_, nf_, nc_, nstk_, nctl_)
    type(vm_state), intent(inout) :: st
    integer(int64), value :: n_
    integer(int64), value :: nf_
    integer(int64), value :: nc_
    integer(int64), value :: nstk_
    integer(int64), value :: nctl_
    integer(int64) :: n_1
    integer(int64) :: n_10
    integer(int64) :: n_11
    integer(int64) :: n_12
    integer(int64) :: n_13
    integer(int64) :: n_14
    integer(int64) :: n_15
    integer(int64) :: n_16
    integer(int64) :: n_2
    integer(int64) :: n_4
    integer(int64) :: n_5
    integer(int64) :: n_6
    integer(int64) :: n_7
    integer(int64) :: n_8
    integer(int64) :: n_9
    integer(int64) :: var_3
    n_1 = 0_int64
    call rt_resize_val(st%stk, n_1)
    n_2 = 0_int64
    call rt_resize_int(st%ckind, n_2)
    var_3 = (4_int64 * n_)
    n_4 = var_3
    call rt_resize_int(st%code, n_4)
    n_5 = n_
    call rt_resize_val(st%pool, n_5)
    n_6 = nstk_
    call rt_resize_val(st%stk, n_6)
    n_7 = nctl_
    call rt_resize_int(st%ckind, n_7)
    n_8 = nctl_
    call rt_resize_int(st%ca, n_8)
    n_9 = nctl_
    call rt_resize_int(st%cb, n_9)
    n_10 = nctl_
    call rt_resize_int(st%cc, n_10)
    n_11 = nctl_
    call rt_resize_int(st%cprev, n_11)
    n_12 = nf_
    call rt_resize_int(st%fnfirst, n_12)
    n_13 = nf_
    call rt_resize_int(st%fncount, n_13)
    n_14 = nc_
    call rt_resize_int(st%cln, n_14)
    n_15 = nc_
    call rt_resize_int(st%clent, n_15)
    n_16 = nc_
    call rt_resize_int(st%clrest, n_16)
  end subroutine vmicg_resize

  subroutine vmicg_program(st, ce, e_, defs_, nstk_, nctl_)
    type(vm_state), intent(inout) :: st
    type(vc_state), intent(inout) :: ce
    type(value), value :: e_
    type(value), value :: defs_
    integer(int64), value :: nstk_
    integer(int64), value :: nctl_
    integer(int64) :: mv_10
    integer(int64) :: mv_8
    integer(int64) :: n_2
    integer(int64) :: n_7
    integer(int64) :: nc_4
    integer(int64) :: nf_3
    integer(int64) :: pa_9
    integer(int64) :: pb_12
    logical :: t_5
    logical :: t_6
    integer(int64) :: var_1
    integer(int64) :: var_11
    var_1 = (vmicg_size(e_) + (1_int64 + vmicg_size_defs(defs_)))
    n_2 = var_1
    nf_3 = vmicg_len(defs_)
    nc_4 = vmicg_nclauses(defs_)
    if ((.not. (n_2 < 549755813888_int64))) then
      t_6 = (.not. (n_2 < 549755813888_int64))
    else
      if ((.not. (nf_3 < 1099511627776_int64))) then
        t_5 = (.not. (nf_3 < 1099511627776_int64))
      else
        t_5 = (.not. (nc_4 < 1099511627776_int64))
      end if
      t_6 = t_5
    end if
    if (t_6) then
      st%status = 2_int64
    else
      call vmicg_resize(st, n_2, nf_3, nc_4, nstk_, nctl_)
      st%status = 0_int64
      n_7 = 4096_int64
      call rt_resize_int(ce%env, n_7)
      ce%err = 0_int64
      call vmicg_compile(st, ce, e_, 0_int64, 0_int64, -1_int64, 0_int64, -1_int64, 0_int64, 0_int64, mv_8)
      pa_9 = mv_8
      call vmicg_put(st, pa_9, 11_int64, 0_int64, 0_int64, 0_int64, rt_nil())
      var_11 = (1_int64 + pa_9)
      call vmicg_defs(st, ce, defs_, 0_int64, 0_int64, var_11, mv_10)
      pb_12 = mv_10
      st%pc = 0_int64
      st%fb = 0_int64
      st%sp = 0_int64
      st%ctop = 0_int64
      st%hidx = -1_int64
    end if
  end subroutine vmicg_program
end module vmc_gen
