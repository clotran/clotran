! clotran_ieee: the IEEE names the host uses, from ieee_lite, for a
! compiler with no ieee_arithmetic (src/f/ieee_lite.f90 says which).
module clotran_ieee
  use ieee_lite, only: ieee_class_type => lite_class_type, ieee_value => lite_value, &
       ieee_is_nan => lite_is_nan, ieee_is_finite => lite_is_finite, &
       ieee_copy_sign => lite_copy_sign, ieee_positive_inf => lite_positive_inf, &
       ieee_negative_inf => lite_negative_inf, ieee_quiet_nan => lite_quiet_nan
end module clotran_ieee
