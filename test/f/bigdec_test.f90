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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call dec_from_text(text, v, ok)
    if (.not. ok) then
       call eq(label, "<unreadable>", expected)
       return
    end if
    block
       call dec_to_text(v, s=dlt_1)
       call eq(label, dlt_1, expected)
    end block
  end subroutine roundtrip

  function d(text) result(v)
    character(len=*), intent(in) :: text
    character(len=:), allocatable :: v
    logical :: ok
    call dec_from_text(text, v, ok)
  end function d

  subroutine check_read_print()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
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
       call dec_unscaled(d("-3.50"), u=dlt_1)
       call eq("1o. the unscaled of -3.50: ", dlt_1, "-350")
    end block
  end subroutine check_read_print

  subroutine check_add_sub()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    block
       call dec_add(d("1.5"), d("2.25"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("2a. scales differ: ", dlt_2, "3.75")
    end block
    block
       call dec_add(d("0.1"), d("0.2"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("2b. tenths: ", dlt_2, "0.3")
    end block
    block
       call dec_add(d("1"), d("0.5"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("2c. integer plus decimal: ", dlt_2, "1.5")
    end block
    block
       call dec_sub(d("1"), d("0.5"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("2d. subtract: ", dlt_2, "0.5")
    end block
    block
       call dec_sub(d("1.0"), d("1.0"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("2e. to zero, scale kept: ", dlt_2, "0.0")
    end block
    block
       call dec_neg(d("1.5"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("2f. negate: ", dlt_2, "-1.5")
    end block
    block
       call dec_neg(d("0"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("2g. negate zero: ", dlt_2, "0")
    end block
    block
       call dec_abs(d("-1.5"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("2h. absolute: ", dlt_2, "1.5")
    end block
  end subroutine check_add_sub

  subroutine check_mul()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    block
       call dec_mul(d("1.5"), d("2.25"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("3a. scales add: ", dlt_2, "3.375")
    end block
    block
       call dec_mul(d("0.1"), d("0.1"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("3b. a tenth squared: ", dlt_2, "0.01")
    end block
    block
       call dec_mul(d("1"), d("0.1"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("3c. one times a tenth: ", dlt_2, "0.1")
    end block
    block
       call dec_mul(d("1.5"), d("0"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("3d. by zero: ", dlt_2, "0.0")
    end block
    block
       call dec_mul(d("99999999999999999999"), d("2"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("3e. big: ", dlt_2,  "199999999999999999998")
    end block
  end subroutine check_mul

  subroutine check_div()
    character(len=:), allocatable :: q
    logical :: ok
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call dec_div(d("1"), d("8"), q, ok)
    block
       call dec_to_text(q, s=dlt_1)
       call eq("4a. an eighth: ", dlt_1, "0.125")
    end block
    call dec_div(d("100"), d("4"), q, ok)
    block
       call dec_to_text(q, s=dlt_1)
       call eq("4b. evenly: ", dlt_1, "25")
    end block
    call dec_div(d("1.0"), d("2"), q, ok)
    block
       call dec_to_text(q, s=dlt_1)
       call eq("4c. the scale is kept: ", dlt_1, "0.5")
    end block
    call dec_div(d("1"), d("2"), q, ok)
    block
       call dec_to_text(q, s=dlt_1)
       call eq("4d. a half: ", dlt_1, "0.5")
    end block
    ! 1/3 does not terminate, and BigDecimal.divide THROWS rather than
    ! rounding when no MathContext says how.
    call dec_div(d("1"), d("3"), q, ok)
    call eqi("4e. a third does not divide: ", merge(1, 0, ok), 0)
    call dec_div(d("1"), d("0"), q, ok)
    call eqi("4f. nor does zero: ", merge(1, 0, ok), 0)
  end subroutine check_div

  subroutine check_quot_rem()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    block
       call dec_quot(d("10.5"), d("3"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("5a. quot keeps the scale: ", dlt_2, "3.0")
    end block
    block
       call dec_rem(d("10.5"), d("3"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("5b. and its remainder: ", dlt_2, "1.5")
    end block
    block
       call dec_quot(d("10"), d("3"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("5c. whole numbers: ", dlt_2, "3")
    end block
    block
       call dec_rem(d("10"), d("3"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("5d. and theirs: ", dlt_2, "1")
    end block
    block
       call dec_quot(d("-10"), d("3"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("5e. negative dividend: ", dlt_2, "-3")
    end block
    block
       call dec_rem(d("-10"), d("3"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("5f. its remainder: ", dlt_2, "-1")
    end block
  end subroutine check_quot_rem

  subroutine check_cmp_strip()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    call eqi("6a. equal by value: ", dec_cmp(d("1"), d("1.0")), 0)
    call eqi("6b. less: ", dec_cmp(d("1"), d("2")), -1)
    call eqi("6c. greater: ", dec_cmp(d("2.00"), d("1.999")), 1)
    call eqi("6d. negatives: ", dec_cmp(d("-1"), d("1")), -1)
    block
       call dec_strip(d("1.0"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("6e. stripped: ", dlt_2, "1")
    end block
    block
       call dec_strip(d("-3.50"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("6f. stripped further: ", dlt_2, "-3.5")
    end block
    block
       call dec_strip(d("0.000"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("6g. zero strips to zero: ", dlt_2, "0")
    end block
    block
       call dec_strip(d("1.25"), o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("6h. nothing to strip: ", dlt_2, "1.25")
    end block
  end subroutine check_cmp_strip

  subroutine check_conversions()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    block
       call dec_from_i64(42_I8, o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("7a. from an integer: ", dlt_2, "42")
    end block
    block
       call dec_from_big("99999999999999999999", o=dlt_1)
       call dec_to_text(dlt_1, s=dlt_2)
       call eq("7b. from a big integer: ", dlt_2,  "99999999999999999999")
    end block
    block
       call dec_to_big(d("2.5"), o=dlt_1)
       call eq("7c. truncating: ", dlt_1, "2")
    end block
    block
       call dec_to_big(d("-2.5"), o=dlt_1)
       call eq("7d. truncating a negative: ", dlt_1, "-2")
    end block
    block
       call dec_to_big(d("42"), o=dlt_1)
       call eq("7e. nothing to truncate: ", dlt_1, "42")
    end block
    block
       call dec_to_big(d("1e3"), o=dlt_1)
       call eq("7f. an exponent: ", dlt_1, "1000")
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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call dec_round(d("4.5555555"), 4, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8a. four digits: ", dlt_1, "4.556")
    end block
    call dec_round(d("4.5555555"), 6, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8b. six digits: ", dlt_1, "4.55556")
    end block
    call dec_round(d("4.5555555"), 6, DEC_CEILING, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8c. ceiling: ", dlt_1, "4.55556")
    end block
    call dec_round(d("4.5555555"), 6, DEC_FLOOR, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8d. floor: ", dlt_1, "4.55555")
    end block
    call dec_round(d("4.5555555"), 6, DEC_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8e. up: ", dlt_1, "4.55556")
    end block
    call dec_round(d("4.5555555"), 6, DEC_DOWN, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8f. down: ", dlt_1, "4.55555")
    end block
    ! a negative goes the other way for CEILING and FLOOR
    call dec_round(d("-4.5555555"), 6, DEC_CEILING, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8g. ceiling, negative: ", dlt_1, "-4.55555")
    end block
    call dec_round(d("-4.5555555"), 6, DEC_FLOOR, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8h. floor, negative: ", dlt_1, "-4.55556")
    end block
    ! the half cases differ only on an exact tie
    call dec_round(d("2.5"), 1, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8i. half up: ", dlt_1, "3")
    end block
    call dec_round(d("2.5"), 1, DEC_HALF_DOWN, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8j. half down: ", dlt_1, "2")
    end block
    call dec_round(d("2.5"), 1, DEC_HALF_EVEN, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8k. half even, to even: ", dlt_1, "2")
    end block
    call dec_round(d("3.5"), 1, DEC_HALF_EVEN, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8l. half even, up: ", dlt_1, "4")
    end block
    ! carrying past the leading digit moves the scale
    call dec_round(d("999.9"), 3, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8m. carry: ", dlt_1, "1.00E+3")
    end block
    ! nothing to drop
    call dec_round(d("1.5"), 6, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8n. already short enough: ", dlt_1, "1.5")
    end block
    call dec_round(d("4.5555"), 5, DEC_UNNECESSARY, r, ok)
    call eqi("8o. unnecessary, and it was: ", merge(1, 0, ok), 1)
    call dec_round(d("4.5555555"), 5, DEC_UNNECESSARY, r, ok)
    call eqi("8p. unnecessary, and it was not: ", merge(1, 0, ok), 0)
    ! division that has nowhere to stop without a precision
    call dec_div_mc(d("1"), d("3"), 10, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8q. a third to ten digits: ", dlt_1, "0.3333333333")
    end block
    call dec_div_mc(d("2"), d("3"), 10, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8r. two thirds, which rounds up: ", dlt_1, "0.6666666667")
    end block
    call dec_div_mc(d("1"), d("8"), 10, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8s. one that terminates early: ", dlt_1, "0.125")
    end block
    call dec_div_mc(d("100"), d("4"), 10, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8t. and one with no fraction: ", dlt_1, "25")
    end block
    call dec_div_mc(d("-1"), d("3"), 5, DEC_HALF_UP, r, ok)
    block
       call dec_to_text(r, s=dlt_1)
       call eq("8u. negative: ", dlt_1, "-0.33333")
    end block
  end subroutine check_rounding

end program bigdec_test
