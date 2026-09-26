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
    block
       character(len=:), allocatable :: dlr_1
       call big_norm("007", o=dlr_1)
       call eq("1a. leading zeros: ", dlr_1, "7")
    end block
    block
       character(len=:), allocatable :: dlr_2
       call big_norm("0000", o=dlr_2)
       call eq("1b. all zeros: ", dlr_2, "0")
    end block
    block
       character(len=:), allocatable :: dlr_3
       call big_norm("-0", o=dlr_3)
       call eq("1c. negative zero is zero: ", dlr_3, "0")
    end block
    block
       character(len=:), allocatable :: dlr_4
       call big_norm("-000", o=dlr_4)
       call eq("1d. negative zeros: ", dlr_4, "0")
    end block
    block
       character(len=:), allocatable :: dlr_5
       call big_norm("+12", o=dlr_5)
       call eq("1e. a plus sign goes: ", dlr_5, "12")
    end block
    block
       character(len=:), allocatable :: dlr_6
       call big_norm("-0042", o=dlr_6)
       call eq("1f. negative, leading zeros: ", dlr_6, "-42")
    end block
    block
       character(len=:), allocatable :: dlr_7
       call big_norm("-42", o=dlr_7)
       call eq("1g. already canonical: ", dlr_7, "-42")
    end block
    block
       character(len=:), allocatable :: dlr_8
       call big_neg("42", o=dlr_8)
       call eq("1h. negate: ", dlr_8, "-42")
    end block
    block
       character(len=:), allocatable :: dlr_9
       call big_neg("-42", o=dlr_9)
       call eq("1i. negate back: ", dlr_9, "42")
    end block
    block
       character(len=:), allocatable :: dlr_10
       call big_neg("0", o=dlr_10)
       call eq("1j. negate zero: ", dlr_10, "0")
    end block
    block
       character(len=:), allocatable :: dlr_11
       call big_abs("-42", o=dlr_11)
       call eq("1k. abs: ", dlr_11, "42")
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
    block
       character(len=:), allocatable :: dlr_12
       call big_add("999", "1", o=dlr_12)
       call eq("3a. carry: ", dlr_12, "1000")
    end block
    block
       character(len=:), allocatable :: dlr_13
       call big_sub("1000", "1", o=dlr_13)
       call eq("3b. borrow: ", dlr_13, "999")
    end block
    block
       character(len=:), allocatable :: dlr_14
       call big_add("42", "-42", o=dlr_14)
       call eq("3c. to zero: ", dlr_14, "0")
    end block
    block
       character(len=:), allocatable :: dlr_15
       call big_sub("1", "2", o=dlr_15)
       call eq("3d. negative result: ", dlr_15, "-1")
    end block
    block
       character(len=:), allocatable :: dlr_16
       call big_add("-2", "-3", o=dlr_16)
       call eq("3e. two negatives: ", dlr_16, "-5")
    end block
    block
       character(len=:), allocatable :: dlr_17
       call big_sub("-2", "-3", o=dlr_17)
       call eq("3f. minus a negative: ", dlr_17, "1")
    end block
    block
       character(len=:), allocatable :: dlr_18
       call big_add("9223372036854775807", "1", o=dlr_18)
       call eq("3g. past 2^63: ", dlr_18, "9223372036854775808")
    end block
    block
       character(len=:), allocatable :: dlr_19
       call big_sub("-9223372036854775808", "1", o=dlr_19)
       call eq("3h. below -2^63: ", dlr_19, "-9223372036854775809")
    end block
    block
       character(len=:), allocatable :: dlr_20
       call big_add("42", "0", o=dlr_20)
       call eq("3i. adding zero: ", dlr_20, "42")
    end block
    block
       character(len=:), allocatable :: dlr_21
       call big_add("1", "99999999999999999999", o=dlr_21)
       call eq("3j. different lengths: ", dlr_21, "100000000000000000000")
    end block
  end subroutine check_add_sub

  subroutine check_mul()
    block
       character(len=:), allocatable :: dlr_22
       call big_mul("6", "7", o=dlr_22)
       call eq("4a. small: ", dlr_22, "42")
    end block
    block
       character(len=:), allocatable :: dlr_23
       call big_mul("99999999999999999999", "0", o=dlr_23)
       call eq("4b. by zero: ", dlr_23, "0")
    end block
    block
       character(len=:), allocatable :: dlr_24
       call big_mul("42", "1", o=dlr_24)
       call eq("4c. by one: ", dlr_24, "42")
    end block
    block
       character(len=:), allocatable :: dlr_25
       call big_mul("-6", "7", o=dlr_25)
       call eq("4d. signs: ", dlr_25, "-42")
    end block
    block
       character(len=:), allocatable :: dlr_26
       call big_mul("-6", "-7", o=dlr_26)
       call eq("4e. both negative: ", dlr_26, "42")
    end block
    block
       character(len=:), allocatable :: dlr_27
       call big_mul("4611686018427387904", "4", o=dlr_27)
       call eq("4f. past 2^63: ", dlr_27, "18446744073709551616")
    end block
    ! 99999999999999999999^2, which is (10^20 - 1)^2 = 10^40 - 2*10^20 + 1
    block
       character(len=:), allocatable :: dlr_28
       call big_mul("99999999999999999999", "99999999999999999999", o=dlr_28)
       call eq("4g. twenty digits squared: ",  dlr_28,  "9999999999999999999800000000000000000001")
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
    block
       character(len=:), allocatable :: dlr_29
       call big_from_i64(42_I8, o=dlr_29)
       call eq("6a. from an integer: ", dlr_29, "42")
    end block
    block
       character(len=:), allocatable :: dlr_30
       call big_from_i64(-42_I8, o=dlr_30)
       call eq("6b. from a negative: ", dlr_30, "-42")
    end block
    block
       character(len=:), allocatable :: dlr_31
       call big_from_i64(9223372036854775807_I8, o=dlr_31)
       call eq("6c. from the biggest: ", dlr_31, "9223372036854775807")
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
    acc = "1"
    do i = 2, 20
       block
          character(len=:), allocatable :: dlr_32, dlr_33
          call big_from_i64(int(i, I8), o=dlr_32)
          call big_mul(acc, dlr_32, o=dlr_33)
          acc = dlr_33
       end block
    end do
    call eq("7a. 20 factorial: ", acc, "2432902008176640000")
    call eqi("7b. which still fits: ", merge(1, 0, big_fits_i64(acc)), 1)
    do i = 21, 25
       block
          character(len=:), allocatable :: dlr_34, dlr_35
          call big_from_i64(int(i, I8), o=dlr_34)
          call big_mul(acc, dlr_34, o=dlr_35)
          acc = dlr_35
       end block
    end do
    call eq("7c. 25 factorial: ", acc, "15511210043330985984000000")
    call eqi("7d. which does not: ", merge(1, 0, big_fits_i64(acc)), 0)
    ! and back down again, exactly
    do i = 25, 2, -1
       block
          character(len=:), allocatable :: dlr_36
          call big_from_i64(int(i, I8), o=dlr_36)
          call big_divmod(acc, dlr_36, q, r)
       end block
       call eq("7e. divides exactly: ", r, "0")
       acc = q
    end do
    call eq("7f. back to one: ", acc, "1")
  end subroutine check_big

end program bigint_test
