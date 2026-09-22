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
    call eq(label, dec_to_text(v), expected)
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
    call eq("1o. the unscaled of -3.50: ", dec_unscaled(d("-3.50")), "-350")
  end subroutine check_read_print

  subroutine check_add_sub()
    call eq("2a. scales differ: ", dec_to_text(dec_add(d("1.5"), d("2.25"))), "3.75")
    call eq("2b. tenths: ", dec_to_text(dec_add(d("0.1"), d("0.2"))), "0.3")
    call eq("2c. integer plus decimal: ", dec_to_text(dec_add(d("1"), d("0.5"))), "1.5")
    call eq("2d. subtract: ", dec_to_text(dec_sub(d("1"), d("0.5"))), "0.5")
    call eq("2e. to zero, scale kept: ", dec_to_text(dec_sub(d("1.0"), d("1.0"))), "0.0")
    call eq("2f. negate: ", dec_to_text(dec_neg(d("1.5"))), "-1.5")
    call eq("2g. negate zero: ", dec_to_text(dec_neg(d("0"))), "0")
    call eq("2h. absolute: ", dec_to_text(dec_abs(d("-1.5"))), "1.5")
  end subroutine check_add_sub

  subroutine check_mul()
    call eq("3a. scales add: ", dec_to_text(dec_mul(d("1.5"), d("2.25"))), "3.375")
    call eq("3b. a tenth squared: ", dec_to_text(dec_mul(d("0.1"), d("0.1"))), "0.01")
    call eq("3c. one times a tenth: ", dec_to_text(dec_mul(d("1"), d("0.1"))), "0.1")
    call eq("3d. by zero: ", dec_to_text(dec_mul(d("1.5"), d("0"))), "0.0")
    call eq("3e. big: ", dec_to_text(dec_mul(d("99999999999999999999"), d("2"))), &
         "199999999999999999998")
  end subroutine check_mul

  subroutine check_div()
    character(len=:), allocatable :: q
    logical :: ok
    call dec_div(d("1"), d("8"), q, ok)
    call eq("4a. an eighth: ", dec_to_text(q), "0.125")
    call dec_div(d("100"), d("4"), q, ok)
    call eq("4b. evenly: ", dec_to_text(q), "25")
    call dec_div(d("1.0"), d("2"), q, ok)
    call eq("4c. the scale is kept: ", dec_to_text(q), "0.5")
    call dec_div(d("1"), d("2"), q, ok)
    call eq("4d. a half: ", dec_to_text(q), "0.5")
    ! 1/3 does not terminate, and BigDecimal.divide THROWS rather than
    ! rounding when no MathContext says how.
    call dec_div(d("1"), d("3"), q, ok)
    call eqi("4e. a third does not divide: ", merge(1, 0, ok), 0)
    call dec_div(d("1"), d("0"), q, ok)
    call eqi("4f. nor does zero: ", merge(1, 0, ok), 0)
  end subroutine check_div

  subroutine check_quot_rem()
    call eq("5a. quot keeps the scale: ", dec_to_text(dec_quot(d("10.5"), d("3"))), "3.0")
    call eq("5b. and its remainder: ", dec_to_text(dec_rem(d("10.5"), d("3"))), "1.5")
    call eq("5c. whole numbers: ", dec_to_text(dec_quot(d("10"), d("3"))), "3")
    call eq("5d. and theirs: ", dec_to_text(dec_rem(d("10"), d("3"))), "1")
    call eq("5e. negative dividend: ", dec_to_text(dec_quot(d("-10"), d("3"))), "-3")
    call eq("5f. its remainder: ", dec_to_text(dec_rem(d("-10"), d("3"))), "-1")
  end subroutine check_quot_rem

  subroutine check_cmp_strip()
    call eqi("6a. equal by value: ", dec_cmp(d("1"), d("1.0")), 0)
    call eqi("6b. less: ", dec_cmp(d("1"), d("2")), -1)
    call eqi("6c. greater: ", dec_cmp(d("2.00"), d("1.999")), 1)
    call eqi("6d. negatives: ", dec_cmp(d("-1"), d("1")), -1)
    call eq("6e. stripped: ", dec_to_text(dec_strip(d("1.0"))), "1")
    call eq("6f. stripped further: ", dec_to_text(dec_strip(d("-3.50"))), "-3.5")
    call eq("6g. zero strips to zero: ", dec_to_text(dec_strip(d("0.000"))), "0")
    call eq("6h. nothing to strip: ", dec_to_text(dec_strip(d("1.25"))), "1.25")
  end subroutine check_cmp_strip

  subroutine check_conversions()
    call eq("7a. from an integer: ", dec_to_text(dec_from_i64(42_I8)), "42")
    call eq("7b. from a big integer: ", dec_to_text(dec_from_big("99999999999999999999")), &
         "99999999999999999999")
    call eq("7c. truncating: ", dec_to_big(d("2.5")), "2")
    call eq("7d. truncating a negative: ", dec_to_big(d("-2.5")), "-2")
    call eq("7e. nothing to truncate: ", dec_to_big(d("42")), "42")
    call eq("7f. an exponent: ", dec_to_big(d("1e3")), "1000")
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
    call eq("8a. four digits: ", dec_to_text(r), "4.556")
    call dec_round(d("4.5555555"), 6, DEC_HALF_UP, r, ok)
    call eq("8b. six digits: ", dec_to_text(r), "4.55556")
    call dec_round(d("4.5555555"), 6, DEC_CEILING, r, ok)
    call eq("8c. ceiling: ", dec_to_text(r), "4.55556")
    call dec_round(d("4.5555555"), 6, DEC_FLOOR, r, ok)
    call eq("8d. floor: ", dec_to_text(r), "4.55555")
    call dec_round(d("4.5555555"), 6, DEC_UP, r, ok)
    call eq("8e. up: ", dec_to_text(r), "4.55556")
    call dec_round(d("4.5555555"), 6, DEC_DOWN, r, ok)
    call eq("8f. down: ", dec_to_text(r), "4.55555")
    ! a negative goes the other way for CEILING and FLOOR
    call dec_round(d("-4.5555555"), 6, DEC_CEILING, r, ok)
    call eq("8g. ceiling, negative: ", dec_to_text(r), "-4.55555")
    call dec_round(d("-4.5555555"), 6, DEC_FLOOR, r, ok)
    call eq("8h. floor, negative: ", dec_to_text(r), "-4.55556")
    ! the half cases differ only on an exact tie
    call dec_round(d("2.5"), 1, DEC_HALF_UP, r, ok)
    call eq("8i. half up: ", dec_to_text(r), "3")
    call dec_round(d("2.5"), 1, DEC_HALF_DOWN, r, ok)
    call eq("8j. half down: ", dec_to_text(r), "2")
    call dec_round(d("2.5"), 1, DEC_HALF_EVEN, r, ok)
    call eq("8k. half even, to even: ", dec_to_text(r), "2")
    call dec_round(d("3.5"), 1, DEC_HALF_EVEN, r, ok)
    call eq("8l. half even, up: ", dec_to_text(r), "4")
    ! carrying past the leading digit moves the scale
    call dec_round(d("999.9"), 3, DEC_HALF_UP, r, ok)
    call eq("8m. carry: ", dec_to_text(r), "1.00E+3")
    ! nothing to drop
    call dec_round(d("1.5"), 6, DEC_HALF_UP, r, ok)
    call eq("8n. already short enough: ", dec_to_text(r), "1.5")
    call dec_round(d("4.5555"), 5, DEC_UNNECESSARY, r, ok)
    call eqi("8o. unnecessary, and it was: ", merge(1, 0, ok), 1)
    call dec_round(d("4.5555555"), 5, DEC_UNNECESSARY, r, ok)
    call eqi("8p. unnecessary, and it was not: ", merge(1, 0, ok), 0)
    ! division that has nowhere to stop without a precision
    call dec_div_mc(d("1"), d("3"), 10, DEC_HALF_UP, r, ok)
    call eq("8q. a third to ten digits: ", dec_to_text(r), "0.3333333333")
    call dec_div_mc(d("2"), d("3"), 10, DEC_HALF_UP, r, ok)
    call eq("8r. two thirds, which rounds up: ", dec_to_text(r), "0.6666666667")
    call dec_div_mc(d("1"), d("8"), 10, DEC_HALF_UP, r, ok)
    call eq("8s. one that terminates early: ", dec_to_text(r), "0.125")
    call dec_div_mc(d("100"), d("4"), 10, DEC_HALF_UP, r, ok)
    call eq("8t. and one with no fraction: ", dec_to_text(r), "25")
    call dec_div_mc(d("-1"), d("3"), 5, DEC_HALF_UP, r, ok)
    call eq("8u. negative: ", dec_to_text(r), "-0.33333")
  end subroutine check_rounding

end program bigdec_test
