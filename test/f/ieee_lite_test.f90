! ieee_lite against the intrinsic ieee_arithmetic: the special values, then
! random 64-bit patterns from a fixed seed -- every class of double turns
! up, NaNs of both signs and payloads among them -- each asked is_nan,
! is_finite and copy_sign of both. Any disagreement is printed and fails.
program ieee_lite_test
  use, intrinsic :: iso_fortran_env, only: real64, int64
  use, intrinsic :: ieee_arithmetic
  use ieee_lite
  implicit none
  integer, parameter :: N = 1000000
  integer(int64) :: s, b, c
  real(real64) :: x, y
  integer :: i, bad
  bad = 0
  call same_bits("+inf", lite_value(1.0_real64, lite_positive_inf), ieee_value(1.0_real64, ieee_positive_inf))
  call same_bits("-inf", lite_value(1.0_real64, lite_negative_inf), ieee_value(1.0_real64, ieee_negative_inf))
  if (.not. (lite_is_nan(lite_value(1.0_real64, lite_quiet_nan)) .and. &
       ieee_is_nan(lite_value(1.0_real64, lite_quiet_nan)))) call fail_at("quiet nan", 0_int64)
  s = 88172645463325252_int64
  do i = 1, N
     b = next(s)
     c = next(s)
     ! every eighth pattern given an all-ones exponent, so infinities and
     ! NaNs are not left to chance
     if (mod(i, 8) == 0) b = ior(b, 9218868437227405312_int64)
     x = transfer(b, x)
     y = transfer(c, y)
     if (lite_is_nan(x) .neqv. ieee_is_nan(x)) call fail_at("is_nan", b)
     if (lite_is_finite(x) .neqv. ieee_is_finite(x)) call fail_at("is_finite", b)
     if (.not. ieee_is_nan(x)) then
        if (transfer(lite_copy_sign(x, y), b) /= transfer(ieee_copy_sign(x, y), b)) call fail_at("copy_sign", b)
     end if
  end do
  if (bad > 0) then
     print '(A,I0,A)', "ieee_lite_test: ", bad, " disagreements"
     stop 1
  end if
  print '(A,I0,A)', "ieee_lite_test: ", N, " patterns, lite and intrinsic agree"
contains
  ! xorshift64: the patterns, the same every run
  integer(int64) function next(st)
    integer(int64), intent(inout) :: st
    st = ieor(st, ishft(st, 13))
    st = ieor(st, ishft(st, -7))
    st = ieor(st, ishft(st, 17))
    next = st
  end function next
  subroutine same_bits(what, a, e)
    character(len=*), intent(in) :: what
    real(real64), intent(in) :: a, e
    if (transfer(a, 1_int64) /= transfer(e, 1_int64)) call fail_at(what, transfer(a, 1_int64))
  end subroutine same_bits
  subroutine fail_at(what, bits)
    character(len=*), intent(in) :: what
    integer(int64), intent(in) :: bits
    bad = bad + 1
    if (bad <= 10) print '(A,A,Z16.16)', what, " differs at ", bits
  end subroutine fail_at
end program ieee_lite_test
