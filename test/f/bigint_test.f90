! Exercises BigInt on its own -- no heap, no evaluator. Every value is
! decimal text in and decimal text out, so the whole module can be
! checked against arithmetic anyone can do by hand, and the cases that
! matter are the ones a 64-bit integer cannot reach.
program bigint_test
  use BigInt
  implicit none

  integer, parameter :: I8 = selected_int_kind(18)
  logical :: all_ok
  character(len=:), allocatable :: q, r

  all_ok = .true.

  call check_norm()
  call check_cmp()
  call check_add_sub()
  call check_mul()
  call check_divmod()
  call check_conversions()
  call check_big()

  if (all_ok) then
     print *, ""
     print *, "ALL BIGINT CHECKS PASSED"
  else
     print *, ""
     print *, "BIGINT CHECKS FAILED"
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
    flush(6)
  end subroutine eq

  subroutine eqi(label, got, expected)
    character(len=*), intent(in) :: label
    integer, intent(in) :: got, expected
    character(len=16) :: g, e
    write(g, '(I0)') got
    write(e, '(I0)') expected
    call eq(label, trim(g), trim(e))
  end subroutine eqi

  subroutine check_norm()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call big_norm("007", o=dlt_1)
       call eq("1a. leading zeros: ", dlt_1, "7")
    end block
    block
       call big_norm("0000", o=dlt_1)
       call eq("1b. all zeros: ", dlt_1, "0")
    end block
    block
       call big_norm("-0", o=dlt_1)
       call eq("1c. negative zero is zero: ", dlt_1, "0")
    end block
    block
       call big_norm("-000", o=dlt_1)
       call eq("1d. negative zeros: ", dlt_1, "0")
    end block
    block
       call big_norm("+12", o=dlt_1)
       call eq("1e. a plus sign goes: ", dlt_1, "12")
    end block
    block
       call big_norm("-0042", o=dlt_1)
       call eq("1f. negative, leading zeros: ", dlt_1, "-42")
    end block
    block
       call big_norm("-42", o=dlt_1)
       call eq("1g. already canonical: ", dlt_1, "-42")
    end block
    block
       call big_neg("42", o=dlt_1)
       call eq("1h. negate: ", dlt_1, "-42")
    end block
    block
       call big_neg("-42", o=dlt_1)
       call eq("1i. negate back: ", dlt_1, "42")
    end block
    block
       call big_neg("0", o=dlt_1)
       call eq("1j. negate zero: ", dlt_1, "0")
    end block
    block
       call big_abs("-42", o=dlt_1)
       call eq("1k. abs: ", dlt_1, "42")
    end block
    ! Validity is about SHAPE: what the reader is allowed to hand over.
    call eqi("1l. digits are valid: ", merge(1, 0, big_valid("123")), 1)
    call eqi("1m. a sign is valid: ", merge(1, 0, big_valid("-123")), 1)
    call eqi("1n. a letter is not: ", merge(1, 0, big_valid("12a")), 0)
    call eqi("1o. empty is not: ", merge(1, 0, big_valid("")), 0)
    call eqi("1p. a lone sign is not: ", merge(1, 0, big_valid("-")), 0)
  end subroutine check_norm

  subroutine check_cmp()
    call eqi("2a. equal: ", big_cmp("42", "42"), 0)
    call eqi("2b. by length: ", big_cmp("100", "99"), 1)
    call eqi("2c. by digit: ", big_cmp("123", "124"), -1)
    call eqi("2d. negative is less: ", big_cmp("-1", "1"), -1)
    call eqi("2e. two negatives: ", big_cmp("-100", "-99"), -1)
    call eqi("2f. zero and negative: ", big_cmp("0", "-1"), 1)
    call eqi("2g. long numbers: ", &
         big_cmp("99999999999999999999", "99999999999999999998"), 1)
  end subroutine check_cmp

  subroutine check_add_sub()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call big_add("999", "1", o=dlt_1)
       call eq("3a. carry: ", dlt_1, "1000")
    end block
    block
       call big_sub("1000", "1", o=dlt_1)
       call eq("3b. borrow: ", dlt_1, "999")
    end block
    block
       call big_add("42", "-42", o=dlt_1)
       call eq("3c. to zero: ", dlt_1, "0")
    end block
    block
       call big_sub("1", "2", o=dlt_1)
       call eq("3d. negative result: ", dlt_1, "-1")
    end block
    block
       call big_add("-2", "-3", o=dlt_1)
       call eq("3e. two negatives: ", dlt_1, "-5")
    end block
    block
       call big_sub("-2", "-3", o=dlt_1)
       call eq("3f. minus a negative: ", dlt_1, "1")
    end block
    block
       call big_add("9223372036854775807", "1", o=dlt_1)
       call eq("3g. past 2^63: ", dlt_1, "9223372036854775808")
    end block
    block
       call big_sub("-9223372036854775808", "1", o=dlt_1)
       call eq("3h. below -2^63: ", dlt_1, "-9223372036854775809")
    end block
    block
       call big_add("42", "0", o=dlt_1)
       call eq("3i. adding zero: ", dlt_1, "42")
    end block
    block
       call big_add("1", "99999999999999999999", o=dlt_1)
       call eq("3j. different lengths: ", dlt_1, "100000000000000000000")
    end block
  end subroutine check_add_sub

  subroutine check_mul()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call big_mul("6", "7", o=dlt_1)
       call eq("4a. small: ", dlt_1, "42")
    end block
    block
       call big_mul("99999999999999999999", "0", o=dlt_1)
       call eq("4b. by zero: ", dlt_1, "0")
    end block
    block
       call big_mul("42", "1", o=dlt_1)
       call eq("4c. by one: ", dlt_1, "42")
    end block
    block
       call big_mul("-6", "7", o=dlt_1)
       call eq("4d. signs: ", dlt_1, "-42")
    end block
    block
       call big_mul("-6", "-7", o=dlt_1)
       call eq("4e. both negative: ", dlt_1, "42")
    end block
    block
       call big_mul("4611686018427387904", "4", o=dlt_1)
       call eq("4f. past 2^63: ", dlt_1, "18446744073709551616")
    end block
    ! 99999999999999999999^2, which is (10^20 - 1)^2 = 10^40 - 2*10^20 + 1
    block
       call big_mul("99999999999999999999", "99999999999999999999", o=dlt_1)
       call eq("4g. twenty digits squared: ",  dlt_1,  "9999999999999999999800000000000000000001")
    end block
  end subroutine check_mul

  subroutine check_divmod()
    call big_divmod("10", "3", q, r)
    call eq("5a. quotient: ", q, "3")
    call eq("5b. remainder: ", r, "1")
    ! Truncating toward zero, with the remainder taking the DIVIDEND's
    ! sign -- BigInteger.divide and .remainder, which is what Clojure's
    ! quot and rem answer.
    call big_divmod("-10", "3", q, r)
    call eq("5c. negative dividend, quotient: ", q, "-3")
    call eq("5d. negative dividend, remainder: ", r, "-1")
    call big_divmod("10", "-3", q, r)
    call eq("5e. negative divisor, quotient: ", q, "-3")
    call eq("5f. negative divisor, remainder: ", r, "1")
    call big_divmod("42", "42", q, r)
    call eq("5g. exact, quotient: ", q, "1")
    call eq("5h. exact, remainder: ", r, "0")
    call big_divmod("5", "7", q, r)
    call eq("5i. smaller than the divisor: ", q, "0")
    call eq("5j. and its remainder: ", r, "5")
    call big_divmod("18446744073709551616", "4", q, r)
    call eq("5k. past 2^63: ", q, "4611686018427387904")
    call big_divmod("9999999999999999999800000000000000000001", "99999999999999999999", q, r)
    call eq("5l. forty digits by twenty: ", q, "99999999999999999999")
    call eq("5m. and nothing left: ", r, "0")
  end subroutine check_divmod

  subroutine check_conversions()
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call big_from_i64(42_I8, o=dlt_1)
       call eq("6a. from an integer: ", dlt_1, "42")
    end block
    block
       call big_from_i64(-42_I8, o=dlt_1)
       call eq("6b. from a negative: ", dlt_1, "-42")
    end block
    block
       call big_from_i64(9223372036854775807_I8, o=dlt_1)
       call eq("6c. from the biggest: ", dlt_1, "9223372036854775807")
    end block
    call eqi("6d. it fits: ", merge(1, 0, big_fits_i64("9223372036854775807")), 1)
    call eqi("6e. one more does not: ", merge(1, 0, big_fits_i64("9223372036854775808")), 0)
    call eqi("6f. the smallest fits: ", merge(1, 0, big_fits_i64("-9223372036854775808")), 1)
    call eqi("6g. one less does not: ", merge(1, 0, big_fits_i64("-9223372036854775809")), 0)
    call eqi("6h. a small one fits: ", merge(1, 0, big_fits_i64("0")), 1)
    call eqi("6i. and comes back: ", int(big_to_i64("-42")), -42)
    call eqi("6j. as a double: ", int(big_to_dbl("1024")), 1024)
  end subroutine check_conversions

  ! 20! and 25! -- the first fits in a long, the second does not, which
  ! is exactly where Clojure's (*' ...) starts needing this module.
  subroutine check_big()
    character(len=:), allocatable :: acc
    integer :: i
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    acc = "1"
    do i = 2, 20
       block
          call big_from_i64(int(i, I8), o=dlt_1)
          call big_mul(acc, dlt_1, o=dlt_2)
          acc = dlt_2
       end block
    end do
    call eq("7a. 20 factorial: ", acc, "2432902008176640000")
    call eqi("7b. which still fits: ", merge(1, 0, big_fits_i64(acc)), 1)
    do i = 21, 25
       block
          call big_from_i64(int(i, I8), o=dlt_1)
          call big_mul(acc, dlt_1, o=dlt_2)
          acc = dlt_2
       end block
    end do
    call eq("7c. 25 factorial: ", acc, "15511210043330985984000000")
    call eqi("7d. which does not: ", merge(1, 0, big_fits_i64(acc)), 0)
    ! and back down again, exactly
    do i = 25, 2, -1
       block
          call big_from_i64(int(i, I8), o=dlt_1)
          call big_divmod(acc, dlt_1, q, r)
       end block
       call eq("7e. divides exactly: ", r, "0")
       acc = q
    end do
    call eq("7f. back to one: ", acc, "1")
  end subroutine check_big

end program bigint_test
