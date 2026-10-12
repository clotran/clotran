! clotran_ieee: the IEEE names the host uses, from the intrinsic module.
! Where a compiler has none, src/f/clotran_ieee_lite.f90 stands in (the
! Makefile's IEEE).
module clotran_ieee
  use, intrinsic :: ieee_arithmetic, only: ieee_class_type, ieee_value, ieee_is_nan, &
       ieee_is_finite, ieee_copy_sign, ieee_positive_inf, ieee_negative_inf, ieee_quiet_nan
end module clotran_ieee
