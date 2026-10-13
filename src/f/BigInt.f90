! BigInt -- arbitrary-precision integers, as decimal text.
!
! clotran.host.bigint is a real type in the language, not a host
! artifact: ClojureScript has one too, `1N` reads as one, and `(+' x y)`
! has nowhere to promote into without it (DEVIATIONS 26, 30). So it is
! reproduced here rather than approximated.
!
! A big integer IS its decimal text, canonical: an optional leading
! "-", then digits, with no leading zeros and no "-0". Every function
! here takes and returns that text and nothing else -- no pool, no
! handle, no state -- so the whole module is pure and testable on its
! own (test/f/bigint_test.f90), and GC.f90 can store the text in the
! string pool exactly as it stores a string.
!
! WHY TEXT, not limbs. The arithmetic below is schoolbook, base 10,
! one digit per element: O(n^2) multiplication and division where a
! limb representation in base 10^9 would be ~81x fewer digit
! operations. That trade is deliberate. A BigInt appears in a Clojure
! program where a long overflowed or a literal asked for one, which is
! rare and small -- a factorial, a hash, a counter past 2^63 -- and the
! text is what the reader hands in and what the printer wants back, so
! a limb form would convert at both ends of every operation. If a
! profile ever shows big arithmetic mattering, the change is local to
! this file: the three conversions at the top and the four operations
! below it.
module BigInt
  implicit none
  private

  integer, parameter :: I8 = selected_int_kind(18)

  public :: big_norm, big_valid, big_is_neg, big_neg, big_abs
  public :: big_cmp, big_add, big_sub, big_mul, big_divmod
  public :: big_from_i64, big_fits_i64, big_to_i64, big_to_dbl, big_zero, text_double

contains

  ! ---- shape -----------------------------------------------------

  ! Digits only, with an optional sign, and at least one digit.
  pure function big_valid(s) result(ok)
    character(len=*), intent(in) :: s
    logical :: ok
    integer :: i, start
    ok = .false.
    start = 1
    if (len(s) >= 1) then
       if (s(1:1) == "-" .or. s(1:1) == "+") start = 2
    end if
    if (len(s) < start) return
    do i = start, len(s)
       if (s(i:i) < "0" .or. s(i:i) > "9") return
    end do
    ok = .true.
  end function big_valid

  ! The canonical form: sign dropped when the value is zero, leading
  ! zeros stripped, "+" removed. Everything else here ASSUMES its
  ! arguments are already canonical, and returns canonical.
  pure subroutine big_norm(s, o)
    character(len=*), intent(in) :: s
    character(len=:), allocatable, intent(out) :: o
    integer :: i, start
    logical :: neg
    neg = .false.
    start = 1
    if (len(s) >= 1) then
       if (s(1:1) == "-") then
          neg = .true.
          start = 2
       else if (s(1:1) == "+") then
          start = 2
       end if
    end if
    i = start
    do while (i < len(s) .and. s(min(i, len(s)):min(i, len(s))) == "0")
       i = i + 1
    end do
    if (i > len(s)) then
       o = "0"
       return
    end if
    o = s(i:)
    if (o == "0") return
    if (neg) then
       block
          character(len=:), allocatable :: dlw
          dlw = "-" // o
          call move_alloc(dlw, o)
       end block
    end if
  end subroutine big_norm

  pure subroutine big_zero(o)
    character(len=:), allocatable, intent(out) :: o
    o = "0"
  end subroutine big_zero

  pure function big_is_neg(s) result(yes)
    character(len=*), intent(in) :: s
    logical :: yes
    yes = .false.
    if (len(s) >= 1) yes = (s(1:1) == "-")
  end function big_is_neg

  pure subroutine big_abs(s, o)
    character(len=*), intent(in) :: s
    character(len=:), allocatable, intent(out) :: o
    if (big_is_neg(s)) then
       o = s(2:)
    else
       o = s
    end if
  end subroutine big_abs

  pure subroutine big_neg(s, o)
    character(len=*), intent(in) :: s
    character(len=:), allocatable, intent(out) :: o
    if (s == "0") then
       o = "0"
    else if (big_is_neg(s)) then
       o = s(2:)
    else
       o = "-" // s
    end if
  end subroutine big_neg

  ! ---- comparison ------------------------------------------------

  ! Magnitudes only: -1, 0, 1.
  pure function cmp_abs(a, b) result(c)
    character(len=*), intent(in) :: a, b
    integer :: c, i
    if (len(a) /= len(b)) then
       c = merge(1, -1, len(a) > len(b))
       return
    end if
    do i = 1, len(a)
       if (a(i:i) /= b(i:i)) then
          c = merge(1, -1, a(i:i) > b(i:i))
          return
       end if
    end do
    c = 0
  end function cmp_abs

  pure function big_cmp(a, b) result(c)
    character(len=*), intent(in) :: a, b
    integer :: c
    logical :: na, nb
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    na = big_is_neg(a)
    nb = big_is_neg(b)
    if (na .and. .not. nb) then
       c = -1
    else if (nb .and. .not. na) then
       c = 1
    else if (na) then
       block
          call big_abs(a, o=dlt_1)
          call big_abs(b, o=dlt_2)
          c = -cmp_abs(dlt_1, dlt_2)
       end block
    else
       c = cmp_abs(a, b)
    end if
  end function big_cmp

  ! ---- magnitude arithmetic --------------------------------------
  !
  ! These three take and return UNSIGNED decimal text. The signed
  ! operations below decide which to call.

  pure subroutine add_abs(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    integer :: la, lb, n, i, da, db, s, carry
    character(len=max(len(a), len(b)) + 1) :: buf
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    la = len(a)
    lb = len(b)
    n = max(la, lb) + 1
    carry = 0
    do i = 0, n - 1
       da = 0
       db = 0
       if (i < la) da = ichar(a(la - i:la - i)) - 48
       if (i < lb) db = ichar(b(lb - i:lb - i)) - 48
       s = da + db + carry
       carry = s / 10
       buf(n - i:n - i) = achar(mod(s, 10) + 48)
    end do
    block
       call big_norm(buf(1:n), o=dlt_1)
       o = dlt_1
    end block
  end subroutine add_abs

  ! a - b, where a >= b in magnitude.
  pure subroutine sub_abs(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    integer :: la, lb, i, da, db, s, borrow
    character(len=len(a)) :: buf
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    la = len(a)
    lb = len(b)
    borrow = 0
    do i = 0, la - 1
       da = ichar(a(la - i:la - i)) - 48
       db = 0
       if (i < lb) db = ichar(b(lb - i:lb - i)) - 48
       s = da - db - borrow
       if (s < 0) then
          s = s + 10
          borrow = 1
       else
          borrow = 0
       end if
       buf(la - i:la - i) = achar(s + 48)
    end do
    block
       call big_norm(buf, o=dlt_1)
       o = dlt_1
    end block
  end subroutine sub_abs

  pure subroutine mul_abs(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    integer :: la, lb, i, j, carry, cur
    integer, allocatable :: acc(:)
    character(len=len(a) + len(b)) :: buf
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    la = len(a)
    lb = len(b)
    allocate(acc(la + lb))
    acc = 0
    do i = 0, la - 1
       carry = 0
       do j = 0, lb - 1
          cur = acc(i + j + 1) + (ichar(a(la - i:la - i)) - 48) * (ichar(b(lb - j:lb - j)) - 48) + carry
          acc(i + j + 1) = mod(cur, 10)
          carry = cur / 10
       end do
       j = i + lb
       do while (carry > 0)
          cur = acc(j + 1) + carry
          acc(j + 1) = mod(cur, 10)
          carry = cur / 10
          j = j + 1
       end do
    end do
    do i = 1, la + lb
       buf(la + lb - i + 1:la + lb - i + 1) = achar(acc(i) + 48)
    end do
    block
       call big_norm(buf, o=dlt_1)
       o = dlt_1
    end block
  end subroutine mul_abs

  ! a / b and a mod b, both unsigned, b /= 0. Schoolbook: bring down
  ! one digit at a time and subtract the divisor while it fits, which
  ! is at most nine subtractions per digit.
  pure subroutine divmod_abs(a, b, q, r)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: q, r
    character(len=:), allocatable :: rem
    character(len=len(a)) :: buf
    integer :: i, d
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    rem = "0"
    do i = 1, len(a)
       if (rem == "0") then
          rem = a(i:i)
       else
          rem = rem // a(i:i)
       end if
       block
          call big_norm(rem, o=dlt_1)
          rem = dlt_1
       end block
       d = 0
       do while (cmp_abs(rem, b) >= 0)
          block
             call sub_abs(rem, b, o=dlt_1)
             rem = dlt_1
          end block
          d = d + 1
       end do
       buf(i:i) = achar(d + 48)
    end do
    block
       call big_norm(buf, o=dlt_1)
       q = dlt_1
    end block
    r = rem
  end subroutine divmod_abs

  ! ---- signed arithmetic -----------------------------------------

  pure subroutine big_add(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    integer :: c
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2, dlt_3
    if (big_is_neg(a) .eqv. big_is_neg(b)) then
       block
          call big_abs(a, o=dlt_1)
          call big_abs(b, o=dlt_2)
          call add_abs(dlt_1, dlt_2, o=dlt_3)
          o = dlt_3
       end block
       if (big_is_neg(a)) then
          block
             call big_neg(o, o=dlt_1)
             o = dlt_1
          end block
       end if
    else
       block
          call big_abs(a, o=dlt_1)
          call big_abs(b, o=dlt_2)
          c = cmp_abs(dlt_1, dlt_2)
       end block
       if (c == 0) then
          o = "0"
       else if (c > 0) then
          block
             call big_abs(a, o=dlt_1)
             call big_abs(b, o=dlt_2)
             call sub_abs(dlt_1, dlt_2, o=dlt_3)
             o = dlt_3
          end block
          if (big_is_neg(a)) then
             block
                call big_neg(o, o=dlt_1)
                o = dlt_1
             end block
          end if
       else
          block
             call big_abs(b, o=dlt_1)
             call big_abs(a, o=dlt_2)
             call sub_abs(dlt_1, dlt_2, o=dlt_3)
             o = dlt_3
          end block
          if (big_is_neg(b)) then
             block
                call big_neg(o, o=dlt_1)
                o = dlt_1
             end block
          end if
       end if
    end if
  end subroutine big_add

  pure subroutine big_sub(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    block
       call big_neg(b, o=dlt_1)
       call big_add(a, dlt_1, o=dlt_2)
       o = dlt_2
    end block
  end subroutine big_sub

  pure subroutine big_mul(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2, dlt_3
    block
       call big_abs(a, o=dlt_1)
       call big_abs(b, o=dlt_2)
       call mul_abs(dlt_1, dlt_2, o=dlt_3)
       o = dlt_3
    end block
    if (o /= "0" .and. (big_is_neg(a) .neqv. big_is_neg(b))) then
       block
          call big_neg(o, o=dlt_1)
          o = dlt_1
       end block
    end if
  end subroutine big_mul

  ! TRUNCATING, as BigInteger.divide and .remainder are: the quotient
  ! rounds toward zero and the remainder takes the DIVIDEND's sign, so
  ! (quot -10N 3) is -3N and (rem -10N 3) is -1N. `mod` is Clojure's
  ! own adjustment on top of these, not a third primitive.
  pure subroutine big_divmod(a, b, q, r)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: q, r
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    block
       call big_abs(a, o=dlt_1)
       call big_abs(b, o=dlt_2)
       call divmod_abs(dlt_1, dlt_2, q, r)
    end block
    if (q /= "0" .and. (big_is_neg(a) .neqv. big_is_neg(b))) then
       block
          call big_neg(q, o=dlt_1)
          q = dlt_1
       end block
    end if
    if (r /= "0" .and. big_is_neg(a)) then
       block
          call big_neg(r, o=dlt_1)
          r = dlt_1
       end block
    end if
  end subroutine big_divmod

  ! ---- conversions -----------------------------------------------

  pure subroutine big_from_i64(i, o)
    integer(I8), intent(in) :: i
    character(len=:), allocatable, intent(out) :: o
    character(len=24) :: buf
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    write(buf, '(I0)') i
    block
       call big_norm(trim(buf), o=dlt_1)
       o = dlt_1
    end block
  end subroutine big_from_i64

  ! Whether the value is inside [-2^63, 2^63-1]. Compared as TEXT
  ! against the bounds: reading it into an integer to find out is the
  ! overflow this is asked to prevent.
  pure function big_fits_i64(s) result(ok)
    character(len=*), intent(in) :: s
    logical :: ok
    if (big_is_neg(s)) then
       ok = (big_cmp(s, "-9223372036854775808") >= 0)
    else
       ok = (big_cmp(s, "9223372036854775807") <= 0)
    end if
  end function big_fits_i64

  ! Only meaningful when big_fits_i64 is true.
  pure function big_to_i64(s) result(i)
    character(len=*), intent(in) :: s
    integer(I8) :: i
    integer :: ios
    read(s, *, iostat=ios) i
    if (ios /= 0) i = 0
  end function big_to_i64

  ! The nearest double. Past ~1.8e308 that is infinity, which is what
  ! BigInteger.doubleValue answers too.
  function big_to_dbl(s) result(d)
    character(len=*), intent(in) :: s
    double precision :: d
    logical :: ok
    call text_double(s, d, ok)
    if (.not. ok) d = 0.0d0
  end function big_to_dbl

  ! The double a decimal text denotes, correctly rounded, and whether it
  ! is one. Plain decimal text -- digits, a sign, a point, an exponent --
  ! goes to the C library's strtod, every token of it, not to a Fortran
  ! READ: gfortran's runtime under mingw-w64 reads with __mingw_strtod,
  ! which rounds some 16- and 17-digit decimals to the wrong neighbour
  ! (6.483618076376551E178 read as 6.483618076376552E178), where the C
  ! libraries of macOS, glibc, musl and Windows' UCRT round them
  ! correctly. Anything else -- NaN, Infinity, a d exponent -- is READ as
  ! before, so what is accepted does not change.
  subroutine text_double(t, d, ok)
    use, intrinsic :: iso_c_binding, only: c_char, c_ptr, c_double, c_null_char, c_loc, c_intptr_t
    character(len=*), intent(in) :: t
    double precision, intent(out) :: d
    logical, intent(out) :: ok
    interface
       function c_strtod(s, endp) bind(C, name="strtod") result(r)
         import :: c_char, c_ptr, c_double
         character(kind=c_char), intent(in) :: s(*)
         type(c_ptr), intent(out) :: endp
         real(c_double) :: r
       end function c_strtod
    end interface
    character(kind=c_char), allocatable, target :: buf(:)
    type(c_ptr) :: endp
    integer :: a, z, i, ios
    d = 0.0d0
    ok = .false.
    a = verify(t, " ")
    if (a == 0) return
    z = len_trim(t)
    if (verify(t(a:z), "0123456789+-.eE") == 0) then
       if (scan(t(a:z), "0123456789") == 0) return
       allocate(buf(z - a + 2))
       do i = a, z
          buf(i - a + 1) = t(i:i)
       end do
       buf(z - a + 2) = c_null_char
       d = c_strtod(buf, endp)
       ok = transfer(endp, 0_c_intptr_t) - transfer(c_loc(buf), 0_c_intptr_t) == z - a + 1
       if (.not. ok) d = 0.0d0
    else
       read(t, *, iostat=ios) d
       ok = ios == 0
    end if
  end subroutine text_double

end module BigInt
