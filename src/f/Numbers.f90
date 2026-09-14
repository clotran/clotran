! Numbers: integer arithmetic. Mirrors clojure.lang.Numbers's role.
module Numbers
  use values
  implicit none
  private

  public :: num_add, num_sub, num_mul, num_div, num_lt, num_gt, num_le, num_ge
  public :: num_bit_and, num_bit_or, num_bit_xor, num_bit_not, num_bit_and_not
  public :: num_quot, num_rem, num_shift_left, num_shift_right, num_ushift_right

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

  ! clojure.lang.Numbers.and/or/xor/not/andNot -- always exactly 2 args
  ! (1 for not) at the native level; core.clj's own bit-and/bit-or/
  ! bit-xor/bit-and-not do the >2-arg reduction themselves in Clojure.
  function num_bit_and(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = iand(args(1)%int_val, args(2)%int_val)
  end function num_bit_and

  function num_bit_or(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = ior(args(1)%int_val, args(2)%int_val)
  end function num_bit_or

  function num_bit_xor(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = ieor(args(1)%int_val, args(2)%int_val)
  end function num_bit_xor

  function num_bit_not(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = not(args(1)%int_val)
  end function num_bit_not

  function num_bit_and_not(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = iand(args(1)%int_val, not(args(2)%int_val))
  end function num_bit_and_not

  ! quotient/remainder and the shifts -- clojure.lang.Numbers names
  ! them quotient/remainder/shiftLeft/shiftRight/unsignedShiftRight
  ! (see clotran.clj); Fortran's own integer / and mod are already
  ! truncate-toward-zero, matching Clojure's quot/rem.
  function num_quot(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = args(1)%int_val / args(2)%int_val
  end function num_quot

  function num_rem(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = mod(args(1)%int_val, args(2)%int_val)
  end function num_rem

  function num_shift_left(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = ishft(args(1)%int_val, args(2)%int_val)
  end function num_shift_left

  ! Arithmetic shift right (sign-preserving), matching Numbers.shiftRight.
  function num_shift_right(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = ishft(args(1)%int_val, -args(2)%int_val)
    if (args(1)%int_val < 0 .and. args(2)%int_val > 0) then
       val%int_val = ior(val%int_val, not(ishft(1, bit_size(val%int_val) - args(2)%int_val) - 1))
    end if
  end function num_shift_right

  ! Logical (zero-filling) shift right, matching unsignedShiftRight.
  function num_ushift_right(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    val%tag = TAG_INT
    val%int_val = ishft(args(1)%int_val, -args(2)%int_val)
  end function num_ushift_right

end module Numbers
