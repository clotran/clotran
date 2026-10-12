! ieee_lite.f90 -- the part of ieee_arithmetic clotran uses, on the bits
! of a 64-bit real, for a compiler that has no ieee_arithmetic: gfortran
! on aarch64 with musl (Alpine), whose libgfortran is built without its
! IEEE modules. clotran_ieee is this or the intrinsic module, as the
! Makefile chooses (IEEE); test/f/ieee_lite_test.f90 holds the two to
! agreeing, on every compiler that has both. Bit operations, not
! comparisons, so no optimiser's view of NaN can change an answer.
module ieee_lite
  use, intrinsic :: iso_fortran_env, only: real64, int64
  implicit none
  private
  public :: lite_class_type, lite_value, lite_is_nan, lite_is_finite, lite_copy_sign
  public :: lite_positive_inf, lite_negative_inf, lite_quiet_nan

  type :: lite_class_type
     integer :: which = 0
  end type lite_class_type
  type(lite_class_type), parameter :: lite_positive_inf = lite_class_type(1)
  type(lite_class_type), parameter :: lite_negative_inf = lite_class_type(2)
  type(lite_class_type), parameter :: lite_quiet_nan = lite_class_type(3)

  integer(int64), parameter :: EXP_ALL = 9218868437227405312_int64     ! 0x7FF0000000000000
  integer(int64), parameter :: MAG = huge(1_int64)                     ! 0x7FFFFFFFFFFFFFFF
  integer(int64), parameter :: NEG_INF = -4503599627370496_int64       ! 0xFFF0000000000000
  integer(int64), parameter :: QNAN = 9221120237041090560_int64        ! 0x7FF8000000000000

contains

  elemental real(real64) function lite_value(x, c)
    real(real64), intent(in) :: x
    type(lite_class_type), intent(in) :: c
    select case (c%which)
    case (1); lite_value = transfer(EXP_ALL, x)
    case (2); lite_value = transfer(NEG_INF, x)
    case default; lite_value = transfer(QNAN, x)
    end select
  end function lite_value

  ! every exponent bit set and some fraction bit: a NaN
  elemental logical function lite_is_nan(x)
    real(real64), intent(in) :: x
    lite_is_nan = iand(transfer(x, 1_int64), MAG) > EXP_ALL
  end function lite_is_nan

  ! some exponent bit clear: neither infinite nor NaN
  elemental logical function lite_is_finite(x)
    real(real64), intent(in) :: x
    lite_is_finite = iand(transfer(x, 1_int64), MAG) < EXP_ALL
  end function lite_is_finite

  ! x's magnitude with y's sign bit
  elemental real(real64) function lite_copy_sign(x, y)
    real(real64), intent(in) :: x, y
    lite_copy_sign = transfer(ior(iand(transfer(x, 1_int64), MAG), &
         iand(transfer(y, 1_int64), not(MAG))), x)
  end function lite_copy_sign
end module ieee_lite
