  ! GENERATED from model/vmtrg.lisp by scripts/acl2-fortran -b vmtrg. Do not edit:
  ! change the model, prove it, and generate again. Included in Eval.f90's
  ! contains part: the VM's translation of a constant, a local, if, let* and
  ! throw (vtg_tr; every other kind vm.inc's vm_tr, through vtg_other) --
  ! guard-verified, reading the tree through vm.inc's vtg_* reads and building
  ! the expression on the value stack through its vtg_* shims. vmtrg.lisp
  ! proves it pushes exactly exec-vmtr's ex-tr on a tree of these kinds
  ! (vtg-tr-ex-tr).
  recursive subroutine vtg_tr(tb, flg_, e_, i_)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: flg_
    type(gc_value), value :: e_
    integer(int64), value :: i_
    type(gc_value) :: e_3
    type(gc_value) :: e_7
    integer(int64) :: flg_2
    integer(int64) :: flg_6
    integer(int64) :: i_1
    integer(int64) :: i_4
    integer(int64) :: i_8
    integer(int64) :: k_5
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
        k_5 = vtg_kind(e_)
        select case (k_5)
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
          flg_6 = 1_int64
          e_7 = e_
          i_8 = 0_int64
          flg_ = flg_6
          e_ = e_7
          i_ = i_8
          cycle
        case default
          call vtg_other(tb, e_)
        end select
      end if
      exit
    end do
  end subroutine vtg_tr
