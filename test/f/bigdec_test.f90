! Exercises BigDec on its own. Every expected value here came from
! java.math.BigDecimal through `clj` -- the scale rules are the whole
! point of the type, and they are not guessable.
program bigdec_test
  use BigDec
  implicit none

  integer, parameter :: I8 = selected_int_kind(18)
  logical :: all_ok

  all_ok = .true.

  call check_read_print()
  call check_add_sub()
  call check_mul()
  call check_div()
  call check_quot_rem()
  call check_cmp_strip()
  call check_conversions()
  call check_rounding()

  if (all_ok) then
     print *, ""
     print *, "ALL BIGDEC CHECKS PASSED"
  else
     print *, ""
     print *, "BIGDEC CHECKS FAILED"
     stop 1
  end if

contains

  subroutine eq(label, got, expected)
    character(len=*), intent(in) :: label, got, expected
    if (got == expected) then
       print '(A,A,A)', "ok   - ", label, got
    else
       print '(A,A,A,A,A)', "FAIL - ", label, got, "  (expected ", expected // ")"
       all_ok = .false.
    end if
  end subroutine eq

  subroutine eqi(label, got, expected)
    character(len=*), intent(in) :: label
    integer, intent(in) :: got, expected
    character(len=16) :: g, e
    write(g, '(I0)') got
    write(e, '(I0)') expected
    call eq(label, trim(g), trim(e))
  end subroutine eqi

  ! The literal in, the same text out -- a decimal keeps its scale.
  subroutine roundtrip(label, text, expected)
    character(len=*), intent(in) :: label, text, expected
    character(len=:), allocatable :: v
    logical :: ok
    call dec_from_text(text, v, ok)
    if (.not. ok) then
       call eq(label, "<unreadable>", expected)
       return
    end if
    block
       character(len=:), allocatable :: dlr_1
       call dec_to_text(v, s=dlr_1)
       call eq(label, dlr_1, expected)
    end block
  end subroutine roundtrip

  function d(text) result(v)
    character(len=*), intent(in) :: text
    character(len=:), allocatable :: v
    logical :: ok
    call dec_from_text(text, v, ok)
  end function d

  subroutine check_read_print()
    call roundtrip("1a. an integer: ", "1", "1")
    call roundtrip("1b. one place: ", "1.0", "1.0")
    call roundtrip("1c. trailing zeros kept: ", "-3.50", "-3.50")
    call roundtrip("1d. zero: ", "0", "0")
    call roundtrip("1e. zero with scale: ", "0.000", "0.000")
    call roundtrip("1f. a small one: ", "0.001", "0.001")
    ! Java's toString goes scientific when the adjusted exponent is
    ! below -6 or the scale is negative.
    call roundtrip("1g. smaller still: ", "0.0000001", "1E-7")
    call roundtrip("1h. an exponent: ", "1e10", "1E+10")
    call roundtrip("1i. a negative exponent: ", "1.5e-10", "1.5E-10")
    call roundtrip("1j. hundreds: ", "100", "100")
    call roundtrip("1k. exponent with a point: ", "1.0e3", "1.0E+3")
    call roundtrip("1l. leading zeros: ", "007", "7")
    call eqi("1m. the scale of 1.0: ", dec_scale(d("1.0")), 1)
    call eqi("1n. the scale of 1e3: ", dec_scale(d("1e3")), -3)
    block
       character(len=:), allocatable :: dlr_2
       call dec_unscaled(d("-3.50"), u=dlr_2)
       call eq("1o. the unscaled of -3.50: ", dlr_2, "-350")
    end block
  end subroutine check_read_print

  subroutine check_add_sub()
    block
       character(len=:), allocatable :: dlr_3, dlr_4
       call dec_add(d("1.5"), d("2.25"), o=dlr_3)
       call dec_to_text(dlr_3, s=dlr_4)
       call eq("2a. scales differ: ", dlr_4, "3.75")
    end block
    block
       character(len=:), allocatable :: dlr_5, dlr_6
       call dec_add(d("0.1"), d("0.2"), o=dlr_5)
       call dec_to_text(dlr_5, s=dlr_6)
       call eq("2b. tenths: ", dlr_6, "0.3")
    end block
    block
       character(len=:), allocatable :: dlr_7, dlr_8
       call dec_add(d("1"), d("0.5"), o=dlr_7)
       call dec_to_text(dlr_7, s=dlr_8)
       call eq("2c. integer plus decimal: ", dlr_8, "1.5")
    end block
    block
       character(len=:), allocatable :: dlr_9, dlr_10
       call dec_sub(d("1"), d("0.5"), o=dlr_9)
       call dec_to_text(dlr_9, s=dlr_10)
       call eq("2d. subtract: ", dlr_10, "0.5")
    end block
    block
       character(len=:), allocatable :: dlr_11, dlr_12
       call dec_sub(d("1.0"), d("1.0"), o=dlr_11)
       call dec_to_text(dlr_11, s=dlr_12)
       call eq("2e. to zero, scale kept: ", dlr_12, "0.0")
    end block
    block
       character(len=:), allocatable :: dlr_13, dlr_14
       call dec_neg(d("1.5"), o=dlr_13)
       call dec_to_text(dlr_13, s=dlr_14)
       call eq("2f. negate: ", dlr_14, "-1.5")
    end block
    block
       character(len=:), allocatable :: dlr_15, dlr_16
       call dec_neg(d("0"), o=dlr_15)
       call dec_to_text(dlr_15, s=dlr_16)
       call eq("2g. negate zero: ", dlr_16, "0")
    end block
    block
       character(len=:), allocatable :: dlr_17, dlr_18
       call dec_abs(d("-1.5"), o=dlr_17)
       call dec_to_text(dlr_17, s=dlr_18)
       call eq("2h. absolute: ", dlr_18, "1.5")
    end block
  end subroutine check_add_sub

  subroutine check_mul()
    block
       character(len=:), allocatable :: dlr_19, dlr_20
       call dec_mul(d("1.5"), d("2.25"), o=dlr_19)
       call dec_to_text(dlr_19, s=dlr_20)
       call eq("3a. scales add: ", dlr_20, "3.375")
    end block
    block
       character(len=:), allocatable :: dlr_21, dlr_22
       call dec_mul(d("0.1"), d("0.1"), o=dlr_21)
       call dec_to_text(dlr_21, s=dlr_22)
       call eq("3b. a tenth squared: ", dlr_22, "0.01")
    end block
    block
       character(len=:), allocatable :: dlr_23, dlr_24
       call dec_mul(d("1"), d("0.1"), o=dlr_23)
       call dec_to_text(dlr_23, s=dlr_24)
       call eq("3c. one times a tenth: ", dlr_24, "0.1")
    end block
    block
       character(len=:), allocatable :: dlr_25, dlr_26
       call dec_mul(d("1.5"), d("0"), o=dlr_25)
       call dec_to_text(dlr_25, s=dlr_26)
       call eq("3d. by zero: ", dlr_26, "0.0")
    end block
    block
       character(len=:), allocatable :: dlr_27, dlr_28
       call dec_mul(d("99999999999999999999"), d("2"), o=dlr_27)
       call dec_to_text(dlr_27, s=dlr_28)
       call eq("3e. big: ", dlr_28,  "199999999999999999998")
    end block
  end subroutine check_mul

  subroutine check_div()
    character(len=:), allocatable :: q
    logical :: ok
    call dec_div(d("1"), d("8"), q, ok)
    block
       character(len=:), allocatable :: dlr_29
       call dec_to_text(q, s=dlr_29)
       call eq("4a. an eighth: ", dlr_29, "0.125")
    end block
    call dec_div(d("100"), d("4"), q, ok)
    block
       character(len=:), allocatable :: dlr_30
       call dec_to_text(q, s=dlr_30)
       call eq("4b. evenly: ", dlr_30, "25")
    end block
    call dec_div(d("1.0"), d("2"), q, ok)
    block
       character(len=:), allocatable :: dlr_31
       call dec_to_text(q, s=dlr_31)
       call eq("4c. the scale is kept: ", dlr_31, "0.5")
    end block
    call dec_div(d("1"), d("2"), q, ok)
    block
       character(len=:), allocatable :: dlr_32
       call dec_to_text(q, s=dlr_32)
       call eq("4d. a half: ", dlr_32, "0.5")
    end block
    ! 1/3 does not terminate, and BigDecimal.divide THROWS rather than
    ! rounding when no MathContext says how.
    call dec_div(d("1"), d("3"), q, ok)
    call eqi("4e. a third does not divide: ", merge(1, 0, ok), 0)
    call dec_div(d("1"), d("0"), q, ok)
    call eqi("4f. nor does zero: ", merge(1, 0, ok), 0)
  end subroutine check_div

  subroutine check_quot_rem()
    block
       character(len=:), allocatable :: dlr_33, dlr_34
       call dec_quot(d("10.5"), d("3"), o=dlr_33)
       call dec_to_text(dlr_33, s=dlr_34)
       call eq("5a. quot keeps the scale: ", dlr_34, "3.0")
    end block
    block
       character(len=:), allocatable :: dlr_35, dlr_36
       call dec_rem(d("10.5"), d("3"), o=dlr_35)
       call dec_to_text(dlr_35, s=dlr_36)
       call eq("5b. and its remainder: ", dlr_36, "1.5")
    end block
    block
       character(len=:), allocatable :: dlr_37, dlr_38
       call dec_quot(d("10"), d("3"), o=dlr_37)
       call dec_to_text(dlr_37, s=dlr_38)
       call eq("5c. whole numbers: ", dlr_38, "3")
    end block
    block
       character(len=:), allocatable :: dlr_39, dlr_40
       call dec_rem(d("10"), d("3"), o=dlr_39)
       call dec_to_text(dlr_39, s=dlr_40)
       call eq("5d. and theirs: ", dlr_40, "1")
    end block
    block
       character(len=:), allocatable :: dlr_41, dlr_42
       call dec_quot(d("-10"), d("3"), o=dlr_41)
       call dec_to_text(dlr_41, s=dlr_42)
       call eq("5e. negative dividend: ", dlr_42, "-3")
    end block
    block
       character(len=:), allocatable :: dlr_43, dlr_44
       call dec_rem(d("-10"), d("3"), o=dlr_43)
       call dec_to_text(dlr_43, s=dlr_44)
       call eq("5f. its remainder: ", dlr_44, "-1")
    end block
  end subroutine check_quot_rem

  subroutine check_cmp_strip()
    call eqi("6a. equal by value: ", dec_cmp(d("1"), d("1.0")), 0)
    call eqi("6b. less: ", dec_cmp(d("1"), d("2")), -1)
    call eqi("6c. greater: ", dec_cmp(d("2.00"), d("1.999")), 1)
    call eqi("6d. negatives: ", dec_cmp(d("-1"), d("1")), -1)
    block
       character(len=:), allocatable :: dlr_45, dlr_46
       call dec_strip(d("1.0"), o=dlr_45)
       call dec_to_text(dlr_45, s=dlr_46)
       call eq("6e. stripped: ", dlr_46, "1")
    end block
    block
       character(len=:), allocatable :: dlr_47, dlr_48
       call dec_strip(d("-3.50"), o=dlr_47)
       call dec_to_text(dlr_47, s=dlr_48)
       call eq("6f. stripped further: ", dlr_48, "-3.5")
    end block
    block
       character(len=:), allocatable :: dlr_49, dlr_50
       call dec_strip(d("0.000"), o=dlr_49)
       call dec_to_text(dlr_49, s=dlr_50)
       call eq("6g. zero strips to zero: ", dlr_50, "0")
    end block
    block
       character(len=:), allocatable :: dlr_51, dlr_52
       call dec_strip(d("1.25"), o=dlr_51)
       call dec_to_text(dlr_51, s=dlr_52)
       call eq("6h. nothing to strip: ", dlr_52, "1.25")
    end block
  end subroutine check_cmp_strip

  subroutine check_conversions()
    block
       character(len=:), allocatable :: dlr_53, dlr_54
       call dec_from_i64(42_I8, o=dlr_53)
       call dec_to_text(dlr_53, s=dlr_54)
       call eq("7a. from an integer: ", dlr_54, "42")
    end block
    block
       character(len=:), allocatable :: dlr_55, dlr_56
       call dec_from_big("99999999999999999999", o=dlr_55)
       call dec_to_text(dlr_55, s=dlr_56)
       call eq("7b. from a big integer: ", dlr_56,  "99999999999999999999")
    end block
    block
       character(len=:), allocatable :: dlr_57
       call dec_to_big(d("2.5"), o=dlr_57)
       call eq("7c. truncating: ", dlr_57, "2")
    end block
    block
       character(len=:), allocatable :: dlr_58
       call dec_to_big(d("-2.5"), o=dlr_58)
       call eq("7d. truncating a negative: ", dlr_58, "-2")
    end block
    block
       character(len=:), allocatable :: dlr_59
       call dec_to_big(d("42"), o=dlr_59)
       call eq("7e. nothing to truncate: ", dlr_59, "42")
    end block
    block
       character(len=:), allocatable :: dlr_60
       call dec_to_big(d("1e3"), o=dlr_60)
       call eq("7f. an exponent: ", dlr_60, "1000")
    end block
    call eqi("7g. as a double: ", int(dec_to_dbl(d("1.5")) * 2), 3)
    call eqi("7h. zero is zero: ", merge(1, 0, dec_is_zero(d("0.000"))), 1)
    call eqi("7i. and one is not: ", merge(1, 0, dec_is_zero(d("0.001"))), 0)
  end subroutine check_conversions

  ! Every expected value here is what (with-precision n :rounding MODE ...)
  ! answers in real Clojure, which is java.math.BigDecimal.round.
  subroutine check_rounding()
    character(len=:), allocatable :: r
    logical :: ok
    call dec_round(d("4.5555555"), 4, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_61
       call dec_to_text(r, s=dlr_61)
       call eq("8a. four digits: ", dlr_61, "4.556")
    end block
    call dec_round(d("4.5555555"), 6, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_62
       call dec_to_text(r, s=dlr_62)
       call eq("8b. six digits: ", dlr_62, "4.55556")
    end block
    call dec_round(d("4.5555555"), 6, DEC_CEILING, r, ok)
    block
       character(len=:), allocatable :: dlr_63
       call dec_to_text(r, s=dlr_63)
       call eq("8c. ceiling: ", dlr_63, "4.55556")
    end block
    call dec_round(d("4.5555555"), 6, DEC_FLOOR, r, ok)
    block
       character(len=:), allocatable :: dlr_64
       call dec_to_text(r, s=dlr_64)
       call eq("8d. floor: ", dlr_64, "4.55555")
    end block
    call dec_round(d("4.5555555"), 6, DEC_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_65
       call dec_to_text(r, s=dlr_65)
       call eq("8e. up: ", dlr_65, "4.55556")
    end block
    call dec_round(d("4.5555555"), 6, DEC_DOWN, r, ok)
    block
       character(len=:), allocatable :: dlr_66
       call dec_to_text(r, s=dlr_66)
       call eq("8f. down: ", dlr_66, "4.55555")
    end block
    ! a negative goes the other way for CEILING and FLOOR
    call dec_round(d("-4.5555555"), 6, DEC_CEILING, r, ok)
    block
       character(len=:), allocatable :: dlr_67
       call dec_to_text(r, s=dlr_67)
       call eq("8g. ceiling, negative: ", dlr_67, "-4.55555")
    end block
    call dec_round(d("-4.5555555"), 6, DEC_FLOOR, r, ok)
    block
       character(len=:), allocatable :: dlr_68
       call dec_to_text(r, s=dlr_68)
       call eq("8h. floor, negative: ", dlr_68, "-4.55556")
    end block
    ! the half cases differ only on an exact tie
    call dec_round(d("2.5"), 1, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_69
       call dec_to_text(r, s=dlr_69)
       call eq("8i. half up: ", dlr_69, "3")
    end block
    call dec_round(d("2.5"), 1, DEC_HALF_DOWN, r, ok)
    block
       character(len=:), allocatable :: dlr_70
       call dec_to_text(r, s=dlr_70)
       call eq("8j. half down: ", dlr_70, "2")
    end block
    call dec_round(d("2.5"), 1, DEC_HALF_EVEN, r, ok)
    block
       character(len=:), allocatable :: dlr_71
       call dec_to_text(r, s=dlr_71)
       call eq("8k. half even, to even: ", dlr_71, "2")
    end block
    call dec_round(d("3.5"), 1, DEC_HALF_EVEN, r, ok)
    block
       character(len=:), allocatable :: dlr_72
       call dec_to_text(r, s=dlr_72)
       call eq("8l. half even, up: ", dlr_72, "4")
    end block
    ! carrying past the leading digit moves the scale
    call dec_round(d("999.9"), 3, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_73
       call dec_to_text(r, s=dlr_73)
       call eq("8m. carry: ", dlr_73, "1.00E+3")
    end block
    ! nothing to drop
    call dec_round(d("1.5"), 6, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_74
       call dec_to_text(r, s=dlr_74)
       call eq("8n. already short enough: ", dlr_74, "1.5")
    end block
    call dec_round(d("4.5555"), 5, DEC_UNNECESSARY, r, ok)
    call eqi("8o. unnecessary, and it was: ", merge(1, 0, ok), 1)
    call dec_round(d("4.5555555"), 5, DEC_UNNECESSARY, r, ok)
    call eqi("8p. unnecessary, and it was not: ", merge(1, 0, ok), 0)
    ! division that has nowhere to stop without a precision
    call dec_div_mc(d("1"), d("3"), 10, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_75
       call dec_to_text(r, s=dlr_75)
       call eq("8q. a third to ten digits: ", dlr_75, "0.3333333333")
    end block
    call dec_div_mc(d("2"), d("3"), 10, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_76
       call dec_to_text(r, s=dlr_76)
       call eq("8r. two thirds, which rounds up: ", dlr_76, "0.6666666667")
    end block
    call dec_div_mc(d("1"), d("8"), 10, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_77
       call dec_to_text(r, s=dlr_77)
       call eq("8s. one that terminates early: ", dlr_77, "0.125")
    end block
    call dec_div_mc(d("100"), d("4"), 10, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_78
       call dec_to_text(r, s=dlr_78)
       call eq("8t. and one with no fraction: ", dlr_78, "25")
    end block
    call dec_div_mc(d("-1"), d("3"), 5, DEC_HALF_UP, r, ok)
    block
       character(len=:), allocatable :: dlr_79
       call dec_to_text(r, s=dlr_79)
       call eq("8u. negative: ", dlr_79, "-0.33333")
    end block
  end subroutine check_rounding

end program bigdec_test
