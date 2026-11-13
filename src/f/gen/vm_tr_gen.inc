  ! GENERATED from model/vmtrg.lisp by scripts/acl2-fortran -b vmtrg. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the VM's translation of a constant, a local, if, do, let*
  ! and throw (vtg_tr; every other kind vm.inc's vm_tr, through vtg_other) --
  ! guard-verified, reading the tree through vm.inc's vtg_* reads and building
  ! the expression on the value stack through its vtg_* shims. vmtrg.lisp
  ! proves it pushes exactly exec-vmtr's ex-tr on a tree of these kinds
  ! (vtg-tr-ex-tr).
  recursive subroutine vtg_tr(tb, flg_, e_, i_)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: flg_
    type(gc_value), value :: e_
    integer(int64), value :: i_
    type(gc_value) :: e_12
    type(gc_value) :: e_15
    type(gc_value) :: e_3
    type(gc_value) :: e_8
    integer(int64) :: flg_11
    integer(int64) :: flg_14
    integer(int64) :: flg_2
    integer(int64) :: flg_7
    integer(int64) :: i_1
    integer(int64) :: i_13
    integer(int64) :: i_16
    integer(int64) :: i_4
    integer(int64) :: i_5
    integer(int64) :: i_9
    integer(int64) :: k_10
    integer(int64) :: nk_6
    do
      if ((flg_ == 1_int64)) then
        if ((vtg_kind(e_) == 11_int64)) then
          i_1 = max(0_int64, i_)
          if ((i_1 < vtg_i2(e_))) then
            call vtg_tr(tb, 0_int64, vtg_kid(e_, i_1), 0_int64)
            call vtg_save(tb)
            call vtg_blank(tb, vtg_kid(e_, i_1))
            call vtg_bind(tb, (vtg_s2(e_) + i_1))
            call vtg_tr(tb, 1_int64, e_, (1_int64 + i_1))
            call vtg_restore(tb)
            call vtg_node(tb, 2_int64, 2_int64)
          else
            flg_2 = 0_int64
            e_3 = vtg_kid(e_, vtg_i2(e_))
            i_4 = 0_int64
            flg_ = flg_2
            e_ = e_3
            i_ = i_4
            cycle
          end if
        else
          call vtg_other(tb, e_)
        end if
      else
        if ((flg_ == 2_int64)) then
          if ((vtg_kind(e_) == 5_int64)) then
            i_5 = max(0_int64, i_)
            nk_6 = vtg_nk(e_)
            if ((nk_6 <= 0_int64)) then
              call vtg_nil(tb)
            else
              if ((i_5 < ((-1_int64) + nk_6))) then
                call vtg_tr(tb, 0_int64, vtg_kid(e_, i_5), 0_int64)
                call vtg_save(tb)
                call vtg_blank(tb, vtg_kid(e_, i_5))
                call vtg_dead(tb)
                call vtg_tr(tb, 2_int64, e_, (1_int64 + i_5))
                call vtg_restore(tb)
                call vtg_node(tb, 2_int64, 2_int64)
              else
                flg_7 = 0_int64
                e_8 = vtg_kid(e_, ((-1_int64) + nk_6))
                i_9 = 0_int64
                flg_ = flg_7
                e_ = e_8
                i_ = i_9
                cycle
              end if
            end if
          else
            call vtg_other(tb, e_)
          end if
        else
          k_10 = vtg_kind(e_)
          select case (k_10)
          case (1_int64)
            call vtg_const(tb, vtg_c(e_))
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
            flg_11 = 1_int64
            e_12 = e_
            i_13 = 0_int64
            flg_ = flg_11
            e_ = e_12
            i_ = i_13
            cycle
          case (5_int64)
            flg_14 = 2_int64
            e_15 = e_
            i_16 = 0_int64
            flg_ = flg_14
            e_ = e_15
            i_ = i_16
            cycle
          case default
            call vtg_other(tb, e_)
          end select
        end if
      end if
      exit
    end do
  end subroutine vtg_tr
