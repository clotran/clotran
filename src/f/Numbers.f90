! Numbers: integer arithmetic. Mirrors clojure.lang.Numbers's role.
module Numbers
  use values
  implicit none
  private

  public :: num_add, num_sub, num_mul, num_div, num_lt, num_gt, num_le, num_ge

contains

  function num_add(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    integer :: i
    val%tag = TAG_INT
    val%int_val = 0
    do i = 1, size(args)
       val%int_val = val%int_val + args(i)%int_val
    end do
  end function num_add

  ! (- x) negates; (- x y ...) subtracts left to right.
  function num_sub(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    integer :: i
    val%tag = TAG_INT
    if (size(args) == 0) then
       val%int_val = 0
       return
    end if
    if (size(args) == 1) then
       val%int_val = -args(1)%int_val
       return
    end if
    val%int_val = args(1)%int_val
    do i = 2, size(args)
       val%int_val = val%int_val - args(i)%int_val
    end do
  end function num_sub

  function num_mul(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    integer :: i
    val%tag = TAG_INT
    val%int_val = 1
    do i = 1, size(args)
       val%int_val = val%int_val * args(i)%int_val
    end do
  end function num_mul

  ! (/ x) is 1/x; (/ x y ...) divides left to right. Integer division,
  ! same as mal expects.
  function num_div(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    integer :: i
    val%tag = TAG_INT
    if (size(args) == 0) then
       val%int_val = 1
       return
    end if
    if (size(args) == 1) then
       val%int_val = 1 / args(1)%int_val
       return
    end if
    val%int_val = args(1)%int_val
    do i = 2, size(args)
       val%int_val = val%int_val / args(i)%int_val
    end do
  end function num_div

  function num_lt(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_BOOL
    val%bool_val = args(1)%int_val < args(2)%int_val
  end function num_lt

  function num_gt(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_BOOL
    val%bool_val = args(1)%int_val > args(2)%int_val
  end function num_gt

  function num_le(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_BOOL
    val%bool_val = args(1)%int_val <= args(2)%int_val
  end function num_le

  function num_ge(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_BOOL
    val%bool_val = args(1)%int_val >= args(2)%int_val
  end function num_ge

end module Numbers
