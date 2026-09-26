! BigDec -- arbitrary-precision decimals, as an unscaled integer and a
! scale.
!
! java.math.BigDecimal is a type the LANGUAGE has: `1.0M` reads as one,
! `(= 1.0M 1.0)` is FALSE because a decimal is its own equality
! category, and `bigdec` and `with-precision` exist to make them. It is
! reproduced here rather than approximated as a double (DEVIATIONS 30),
! rounding included: `with-precision` is the only way to divide 1M by 3,
! and the eight RoundingModes Java names are at the bottom of this file.
!
! A decimal is UNSCALED x 10^-SCALE: 1.0M is (10, 1), 1M is (1, 0),
! -3.50M is (-350, 2), 1.0E+3M is (10, -2). The unscaled part is a
! BigInt -- decimal text (BigInt.f90) -- and the scale is an ordinary
! integer, so this module is the scale bookkeeping and BigInt does the
! arithmetic.
!
! The two are carried in ONE string, "unscaled|scale", because that is
! what the heap stores: a value is a tag and a string-pool index
! (GC.f90), and a pair would need an object. Every function here takes
! and returns that form, so the pool never holds anything else.
!
! SCALE IS PART OF THE VALUE and never silently dropped: 1.0M prints as
! 1.0M and 1M as 1M, exactly as Java's toString does, which is why
! `(pr-str (* 1M 0.1M))` is 0.1M and not 0.10M. The two are EQUAL all
! the same -- Clojure compares decimals by value -- so equality and
! hashing here go through dec_cmp and dec_strip rather than the text.
module BigDec
  use BigInt
  implicit none
  private

  integer, parameter :: I8 = selected_int_kind(18)

  public :: dec_make, dec_unscaled, dec_scale, dec_is_dec
  public :: dec_from_text, dec_to_text, dec_from_i64, dec_from_big
  public :: dec_add, dec_sub, dec_mul, dec_div, dec_quot, dec_rem
  public :: dec_neg, dec_abs, dec_cmp, dec_strip, dec_to_dbl, dec_to_big
  public :: dec_is_zero
  public :: dec_round, dec_div_mc, dec_mode_of

  ! ---- rounding ---------------------------------------------------
  !
  ! java.math.RoundingMode, as an integer code. `with-precision` is the
  ! only thing that asks for one, and it names them exactly as Java
  ! does; dec_mode_of maps that name.
  integer, parameter, public :: DEC_UP = 1, DEC_DOWN = 2, DEC_CEILING = 3, &
       DEC_FLOOR = 4, DEC_HALF_UP = 5, DEC_HALF_DOWN = 6, DEC_HALF_EVEN = 7, &
       DEC_UNNECESSARY = 8

contains

  pure function dec_mode_of(name) result(m)
    character(len=*), intent(in) :: name
    integer :: m
    select case (name)
    case ("UP");           m = DEC_UP
    case ("DOWN");         m = DEC_DOWN
    case ("CEILING");      m = DEC_CEILING
    case ("FLOOR");        m = DEC_FLOOR
    case ("HALF_UP");      m = DEC_HALF_UP
    case ("HALF_DOWN");    m = DEC_HALF_DOWN
    case ("HALF_EVEN");    m = DEC_HALF_EVEN
    case ("UNNECESSARY");  m = DEC_UNNECESSARY
    case default;          m = 0
    end select
  end function dec_mode_of

  ! Whether the digits being dropped force the kept ones up. `d` is the
  ! first dropped digit, `sticky` says whether anything nonzero follows
  ! it, `neg` is the sign of the whole value, and `last` is the final
  ! kept digit (HALF_EVEN's tie-breaker). These are Java's eight rules
  ! and nothing else; UNNECESSARY is the one that can fail, and it
  ! answers through `ok`.
  pure subroutine round_up_p(mode, d, sticky, neg, last, up, ok)
    integer, intent(in) :: mode, d, last
    logical, intent(in) :: sticky, neg
    logical, intent(out) :: up, ok
    logical :: any
    any = (d > 0 .or. sticky)
    up = .false.
    ok = .true.
    select case (mode)
    case (DEC_UP);        up = any
    case (DEC_DOWN);      up = .false.
    case (DEC_CEILING);   up = (any .and. .not. neg)
    case (DEC_FLOOR);     up = (any .and. neg)
    case (DEC_HALF_UP);   up = (d >= 5)
    case (DEC_HALF_DOWN); up = (d > 5 .or. (d == 5 .and. sticky))
    case (DEC_HALF_EVEN); up = (d > 5 .or. (d == 5 .and. (sticky .or. mod(last, 2) == 1)))
    case (DEC_UNNECESSARY)
       ok = .not. any
    case default;         up = (d >= 5)      ! HALF_UP is the default
    end select
  end subroutine round_up_p

  ! The magnitude `mag` cut to `precision` digits. `sticky0` says
  ! whether digits beyond `mag` itself were already discarded, which is
  ! how division hands over its remainder. `extra` comes back as the
  ! number of digits removed, which the caller takes off the scale.
  pure subroutine round_mag(mag, precision, mode, neg, sticky0, out_mag, extra, ok)
    character(len=*), intent(in) :: mag
    integer, intent(in) :: precision, mode
    logical, intent(in) :: neg, sticky0
    character(len=:), allocatable, intent(out) :: out_mag
    integer, intent(out) :: extra
    logical, intent(out) :: ok
    character(len=:), allocatable :: kept
    integer :: digits, drop, d, last, i
    logical :: sticky, up

    digits = len(mag)
    ok = .true.
    extra = 0
    out_mag = mag
    if (precision <= 0 .or. digits <= precision) then
       ! Nothing is dropped here, but a caller that already dropped
       ! something still has to hear about UNNECESSARY.
       if (sticky0 .and. mode == DEC_UNNECESSARY) ok = .false.
       return
    end if
    drop = digits - precision
    kept = mag(1:precision)
    d = ichar(mag(precision+1:precision+1)) - 48
    sticky = sticky0
    do i = precision + 2, digits
       if (mag(i:i) /= "0") sticky = .true.
    end do
    last = ichar(kept(precision:precision)) - 48
    call round_up_p(mode, d, sticky, neg, last, up, ok)
    if (.not. ok) return
    if (up) then
       block
          character(len=:), allocatable :: dlr_1
          call big_add(kept, "1", o=dlr_1)
          kept = dlr_1
       end block
       ! 999 + 1 is 1000: one digit too many, and the extra one is a
       ! zero, so it comes off and the scale moves with it.
       if (len(kept) > precision) then
          kept = kept(1:precision)
          drop = drop + 1
       end if
    end if
    out_mag = kept
    extra = drop
  end subroutine round_mag

  ! A decimal at no more than `precision` significant digits, rounded
  ! as `mode` says -- BigDecimal.round(MathContext). ok is false only
  ! for UNNECESSARY, which throws rather than rounding.
  pure subroutine dec_round(v, precision, mode, o, ok)
    character(len=*), intent(in) :: v
    integer, intent(in) :: precision, mode
    character(len=:), allocatable, intent(out) :: o
    logical, intent(out) :: ok
    character(len=:), allocatable :: mag, kept
    integer :: extra
    logical :: neg
    o = v
    ok = .true.
    if (precision <= 0) return
    block
       character(len=:), allocatable :: dlr_2
       call dec_unscaled(v, u=dlr_2)
       neg = big_is_neg(dlr_2)
    end block
    block
       character(len=:), allocatable :: dlr_3, dlr_4
       call dec_unscaled(v, u=dlr_3)
       call big_abs(dlr_3, o=dlr_4)
       mag = dlr_4
    end block
    if (mag == "0") return
    call round_mag(mag, precision, mode, neg, .false., kept, extra, ok)
    if (.not. ok) return
    if (neg) kept = "-" // kept
    block
       character(len=:), allocatable :: dlr_5
       call dec_make(kept, dec_scale(v) - extra, o=dlr_5)
       o = dlr_5
    end block
  end subroutine dec_round

  ! Division under a MathContext: the quotient to `precision`
  ! significant digits, rounded. This is the one that makes
  ! (with-precision 10 (/ 1M 3)) answer 0.3333333333M where the exact
  ! division has nowhere to stop.
  pure subroutine dec_div_mc(a, b, precision, mode, o, ok)
    character(len=*), intent(in) :: a, b
    integer, intent(in) :: precision, mode
    character(len=:), allocatable, intent(out) :: o
    logical, intent(out) :: ok
    character(len=:), allocatable :: ua, ub, q, r, kept, limit
    integer :: k, extra, i
    logical :: neg

    ok = .false.
    block
       character(len=:), allocatable :: dlr_6
       call dec_make("0", 0, o=dlr_6)
       o = dlr_6
    end block
    if (precision <= 0) then
       call dec_div(a, b, o, ok)
       return
    end if
    block
       character(len=:), allocatable :: dlr_7, dlr_8
       call dec_unscaled(a, u=dlr_7)
       call big_abs(dlr_7, o=dlr_8)
       ua = dlr_8
    end block
    block
       character(len=:), allocatable :: dlr_9, dlr_10
       call dec_unscaled(b, u=dlr_9)
       call big_abs(dlr_9, o=dlr_10)
       ub = dlr_10
    end block
    if (ub == "0") return
    block
       character(len=:), allocatable :: dlr_11, dlr_12
       call dec_unscaled(a, u=dlr_11)
       call dec_unscaled(b, u=dlr_12)
       neg = (big_is_neg(dlr_11) .neqv. big_is_neg(dlr_12))
    end block
    if (ua == "0") then
       block
          character(len=:), allocatable :: dlr_13
          call dec_make("0", 0, o=dlr_13)
          o = dlr_13
       end block
       ok = .true.
       return
    end if
    ! EXACT FIRST. BigDecimal.divide(d, mc) answers the exact
    ! quotient when it terminates inside the precision -- (/ 1M 8)
    ! under (with-precision 10) is 0.125M, not 0.1250000000M -- and
    ! only rounds when there is no exact answer to give.
    call dec_div(a, b, o, ok)
    if (ok) then
       block
          character(len=:), allocatable :: dlr_14, dlr_15
          call dec_unscaled(o, u=dlr_14)
          call big_abs(dlr_14, o=dlr_15)
          if (len(dlr_15) <= precision) return
       end block
       ok = .false.
    end if
    ! Enough digits to round from: one more than asked for, with the
    ! remainder as the sticky bit.
    limit = "1"
    do i = 1, precision
       limit = limit // "0"
    end do
    k = 0
    do
       block
          character(len=:), allocatable :: dlr_16
          call shift_up(ua, k, o=dlr_16)
          call big_divmod(dlr_16, ub, q, r)
       end block
       if (big_cmp(q, limit) >= 0) exit
       k = k + 1
       if (k > 2 * precision + 64) exit
    end do
    call round_mag(q, precision, mode, neg, r /= "0", kept, extra, ok)
    if (.not. ok) return
    if (neg) kept = "-" // kept
    block
       character(len=:), allocatable :: dlr_17
       call dec_make(kept, dec_scale(a) - dec_scale(b) + k - extra, o=dlr_17)
       o = dlr_17
    end block
    ok = .true.
  end subroutine dec_div_mc

  ! ---- the pair ---------------------------------------------------

  pure subroutine dec_make(unscaled, scale, o)
    character(len=*), intent(in) :: unscaled
    integer, intent(in) :: scale
    character(len=:), allocatable, intent(out) :: o
    character(len=16) :: buf
    write(buf, '(I0)') scale
    block
       character(len=:), allocatable :: dlr_18
       call big_norm(unscaled, o=dlr_18)
       o = dlr_18 // "|" // trim(buf)
    end block
  end subroutine dec_make

  pure function bar_at(v) result(p)
    character(len=*), intent(in) :: v
    integer :: p
    p = index(v, "|")
  end function bar_at

  ! Whether the text has the shape this module makes.
  pure function dec_is_dec(v) result(yes)
    character(len=*), intent(in) :: v
    logical :: yes
    yes = (bar_at(v) > 1)
  end function dec_is_dec

  pure subroutine dec_unscaled(v, u)
    character(len=*), intent(in) :: v
    character(len=:), allocatable, intent(out) :: u
    integer :: p
    p = bar_at(v)
    if (p > 1) then
       u = v(1:p-1)
    else
       u = "0"
    end if
  end subroutine dec_unscaled

  pure function dec_scale(v) result(s)
    character(len=*), intent(in) :: v
    integer :: s, p, ios
    s = 0
    p = bar_at(v)
    if (p > 1 .and. p < len(v)) then
       read(v(p+1:), *, iostat=ios) s
       if (ios /= 0) s = 0
    end if
  end function dec_scale

  pure function dec_is_zero(v) result(yes)
    character(len=*), intent(in) :: v
    logical :: yes
    block
       character(len=:), allocatable :: dlr_19
       call dec_unscaled(v, u=dlr_19)
       yes = (dlr_19 == "0")
    end block
  end function dec_is_zero

  ! ---- reading ----------------------------------------------------

  ! A decimal LITERAL, with the M already taken off: digits, an
  ! optional point, an optional exponent. ok is false if it is not one.
  pure subroutine dec_from_text(s, out, ok)
    character(len=*), intent(in) :: s
    character(len=:), allocatable, intent(out) :: out
    logical, intent(out) :: ok
    character(len=:), allocatable :: digits, esub
    integer :: i, n, scale, epos, ex, ios
    logical :: seen_point, seen_digit
    character :: c

    ok = .false.
    block
       character(len=:), allocatable :: dlr_20
       call dec_make("0", 0, o=dlr_20)
       out = dlr_20
    end block
    n = len(s)
    if (n == 0) return

    ! split off the exponent
    epos = 0
    do i = 1, n
       if (s(i:i) == "e" .or. s(i:i) == "E") then
          epos = i
          exit
       end if
    end do
    ex = 0
    if (epos > 0) then
       if (epos == n) return
       esub = s(epos+1:)
       if (esub(1:1) == "+") esub = esub(2:)
       if (len(esub) == 0) return
       read(esub, *, iostat=ios) ex
       if (ios /= 0) return
       n = epos - 1
       if (n == 0) return
    end if

    digits = ""
    scale = 0
    seen_point = .false.
    seen_digit = .false.
    do i = 1, n
       c = s(i:i)
       if (i == 1 .and. (c == "-" .or. c == "+")) then
          if (c == "-") digits = "-"
          cycle
       end if
       if (c == ".") then
          if (seen_point) return
          seen_point = .true.
          cycle
       end if
       if (c < "0" .or. c > "9") return
       digits = digits // c
       seen_digit = .true.
       if (seen_point) scale = scale + 1
    end do
    if (.not. seen_digit) return
    block
       character(len=:), allocatable :: dlr_21
       call dec_make(digits, scale - ex, o=dlr_21)
       out = dlr_21
    end block
    ok = .true.
  end subroutine dec_from_text

  pure subroutine dec_from_i64(i, o)
    integer(I8), intent(in) :: i
    character(len=:), allocatable, intent(out) :: o
    block
       character(len=:), allocatable :: dlr_22, dlr_23
       call big_from_i64(i, o=dlr_22)
       call dec_make(dlr_22, 0, o=dlr_23)
       o = dlr_23
    end block
  end subroutine dec_from_i64

  pure subroutine dec_from_big(b, o)
    character(len=*), intent(in) :: b
    character(len=:), allocatable, intent(out) :: o
    block
       character(len=:), allocatable :: dlr_24
       call dec_make(b, 0, o=dlr_24)
       o = dlr_24
    end block
  end subroutine dec_from_big

  ! ---- printing ---------------------------------------------------

  ! BigDecimal.toString: plain when the scale is not negative and the
  ! adjusted exponent is at least -6, scientific otherwise. The two
  ! rules are Java's, and they are why 0.001M prints plainly and
  ! 1E-7M does not.
  pure subroutine dec_to_text(v, s)
    character(len=*), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    character(len=:), allocatable :: u, mag, sign
    integer :: scale, prec, adjusted, i
    character(len=16) :: buf

    block
       character(len=:), allocatable :: dlr_25
       call dec_unscaled(v, u=dlr_25)
       u = dlr_25
    end block
    scale = dec_scale(v)
    sign = ""
    mag = u
    if (big_is_neg(u)) then
       sign = "-"
       mag = u(2:)
    end if
    if (scale == 0) then
       s = sign // mag
       return
    end if
    prec = len(mag)
    adjusted = (prec - 1) - scale
    if (scale >= 0 .and. adjusted >= -6) then
       if (prec > scale) then
          s = sign // mag(1:prec-scale) // "." // mag(prec-scale+1:)
       else
          s = sign // "0."
          do i = 1, scale - prec
             block
                character(len=:), allocatable :: dlw
                dlw = s // "0"
                call move_alloc(dlw, s)
             end block
          end do
          block
             character(len=:), allocatable :: dlw
             dlw = s // mag
             call move_alloc(dlw, s)
          end block
       end if
       return
    end if
    ! scientific: one digit, then the rest, then the adjusted exponent
    if (prec == 1) then
       s = sign // mag
    else
       s = sign // mag(1:1) // "." // mag(2:)
    end if
    write(buf, '(I0)') abs(adjusted)
    if (adjusted < 0) then
       block
          character(len=:), allocatable :: dlw
          dlw = s // "E-" // trim(buf)
          call move_alloc(dlw, s)
       end block
    else
       block
          character(len=:), allocatable :: dlw
          dlw = s // "E+" // trim(buf)
          call move_alloc(dlw, s)
       end block
    end if
  end subroutine dec_to_text

  ! ---- scale alignment --------------------------------------------

  ! The unscaled value it would have at a LARGER scale: multiply by a
  ! power of ten, which on decimal text is appending zeros.
  pure subroutine shift_up(u, by, o)
    character(len=*), intent(in) :: u
    integer, intent(in) :: by
    character(len=:), allocatable, intent(out) :: o
    integer :: i
    o = u
    if (by <= 0 .or. u == "0") then
       if (u == "0") o = "0"
       return
    end if
    do i = 1, by
       block
          character(len=:), allocatable :: dlw
          dlw = o // "0"
          call move_alloc(dlw, o)
       end block
    end do
    block
       character(len=:), allocatable :: dlr_26
       call big_norm(o, o=dlr_26)
       o = dlr_26
    end block
  end subroutine shift_up

  ! ---- arithmetic -------------------------------------------------

  ! add and subtract take the LARGER scale, as BigDecimal does.
  pure subroutine dec_add(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    integer :: sa, sb, s
    sa = dec_scale(a)
    sb = dec_scale(b)
    s = max(sa, sb)
    block
       character(len=:), allocatable :: dlr_27, dlr_28, dlr_29, dlr_30, dlr_31, dlr_32
       call dec_unscaled(a, u=dlr_27)
       call shift_up(dlr_27, s - sa, o=dlr_28)
       call dec_unscaled(b, u=dlr_29)
       call shift_up(dlr_29, s - sb, o=dlr_30)
       call big_add(dlr_28,  dlr_30, o=dlr_31)
       call dec_make(dlr_31, s, o=dlr_32)
       o = dlr_32
    end block
  end subroutine dec_add

  pure subroutine dec_sub(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    block
       character(len=:), allocatable :: dlr_33, dlr_34
       call dec_neg(b, o=dlr_33)
       call dec_add(a, dlr_33, o=dlr_34)
       o = dlr_34
    end block
  end subroutine dec_sub

  ! multiply ADDS the scales: 1.5M * 2.25M is 3.375M.
  pure subroutine dec_mul(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    block
       character(len=:), allocatable :: dlr_35, dlr_36, dlr_37, dlr_38
       call dec_unscaled(a, u=dlr_35)
       call dec_unscaled(b, u=dlr_36)
       call big_mul(dlr_35, dlr_36, o=dlr_37)
       call dec_make(dlr_37,  dec_scale(a) + dec_scale(b), o=dlr_38)
       o = dlr_38
    end block
  end subroutine dec_mul

  pure subroutine dec_neg(a, o)
    character(len=*), intent(in) :: a
    character(len=:), allocatable, intent(out) :: o
    block
       character(len=:), allocatable :: dlr_39, dlr_40, dlr_41
       call dec_unscaled(a, u=dlr_39)
       call big_neg(dlr_39, o=dlr_40)
       call dec_make(dlr_40, dec_scale(a), o=dlr_41)
       o = dlr_41
    end block
  end subroutine dec_neg

  pure subroutine dec_abs(a, o)
    character(len=*), intent(in) :: a
    character(len=:), allocatable, intent(out) :: o
    block
       character(len=:), allocatable :: dlr_42, dlr_43, dlr_44
       call dec_unscaled(a, u=dlr_42)
       call big_abs(dlr_42, o=dlr_43)
       call dec_make(dlr_43, dec_scale(a), o=dlr_44)
       o = dlr_44
    end block
  end subroutine dec_abs

  ! EXACT division, as BigDecimal.divide with no MathContext: the
  ! quotient at the smallest scale that divides evenly, and an error
  ! when there is none -- 1M/3 is a non-terminating expansion, which
  ! Java throws on rather than rounding.
  pure subroutine dec_div(a, b, o, ok)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    logical, intent(out) :: ok
    character(len=:), allocatable :: q, r, num
    integer :: k, sa, sb
    ok = .false.
    block
       character(len=:), allocatable :: dlr_45
       call dec_make("0", 0, o=dlr_45)
       o = dlr_45
    end block
    block
       character(len=:), allocatable :: dlr_46
       call dec_unscaled(b, u=dlr_46)
       if (dlr_46 == "0") return
    end block
    sa = dec_scale(a)
    sb = dec_scale(b)
    ! One more digit each round: at most as many as a long double
    ! would carry plus room for a repeating check to fail on.
    do k = 0, 64
       block
          character(len=:), allocatable :: dlr_47, dlr_48
          call dec_unscaled(a, u=dlr_47)
          call shift_up(dlr_47, k, o=dlr_48)
          num = dlr_48
       end block
       block
          character(len=:), allocatable :: dlr_49
          call dec_unscaled(b, u=dlr_49)
          call big_divmod(num, dlr_49, q, r)
       end block
       if (r == "0") then
          block
             character(len=:), allocatable :: dlr_50
             call dec_make(q, sa - sb + k, o=dlr_50)
             o = dlr_50
          end block
          ok = .true.
          return
       end if
    end do
  end subroutine dec_div

  ! divideToIntegralValue: the integer part of the quotient, at the
  ! preferred scale (this scale minus the divisor's, never negative),
  ! so (quot 10.5M 3) is 3.0M.
  pure subroutine dec_quot(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    character(len=:), allocatable :: q, r, ua, ub
    integer :: sa, sb, s
    sa = dec_scale(a)
    sb = dec_scale(b)
    s = max(sa - sb, 0)
    block
       character(len=:), allocatable :: dlr_51
       call dec_unscaled(a, u=dlr_51)
       ua = dlr_51
    end block
    block
       character(len=:), allocatable :: dlr_52
       call dec_unscaled(b, u=dlr_52)
       ub = dlr_52
    end block
    ! bring both to a common scale so the quotient is the integer one
    block
       character(len=:), allocatable :: dlr_53
       call shift_up(ua, max(sb - sa, 0), o=dlr_53)
       ua = dlr_53
    end block
    block
       character(len=:), allocatable :: dlr_54
       call shift_up(ub, max(sa - sb, 0), o=dlr_54)
       ub = dlr_54
    end block
    call big_divmod(ua, ub, q, r)
    block
       character(len=:), allocatable :: dlr_55, dlr_56
       call shift_up(q, s, o=dlr_55)
       call dec_make(dlr_55, s, o=dlr_56)
       o = dlr_56
    end block
  end subroutine dec_quot

  ! a - (quot a b) * b, which is what BigDecimal.remainder is.
  pure subroutine dec_rem(a, b, o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable, intent(out) :: o
    block
       character(len=:), allocatable :: dlr_57, dlr_58, dlr_59
       call dec_quot(a, b, o=dlr_57)
       call dec_mul(dlr_57, b, o=dlr_58)
       call dec_sub(a, dlr_58, o=dlr_59)
       o = dlr_59
    end block
  end subroutine dec_rem

  ! ---- comparison -------------------------------------------------

  ! BY VALUE, not by scale: 1M and 1.0M compare equal, which is what
  ! Clojure's = says about them.
  pure function dec_cmp(a, b) result(c)
    character(len=*), intent(in) :: a, b
    integer :: c, sa, sb, s
    sa = dec_scale(a)
    sb = dec_scale(b)
    s = max(sa, sb)
    block
       character(len=:), allocatable :: dlr_60, dlr_61, dlr_62, dlr_63
       call dec_unscaled(a, u=dlr_60)
       call shift_up(dlr_60, s - sa, o=dlr_61)
       call dec_unscaled(b, u=dlr_62)
       call shift_up(dlr_62, s - sb, o=dlr_63)
       c = big_cmp(dlr_61,  dlr_63)
    end block
  end function dec_cmp

  ! The same value with no trailing zeros -- what equal decimals share,
  ! so hashing can use it and agree with dec_cmp.
  pure subroutine dec_strip(v, o)
    character(len=*), intent(in) :: v
    character(len=:), allocatable, intent(out) :: o
    character(len=:), allocatable :: u
    integer :: scale
    block
       character(len=:), allocatable :: dlr_64
       call dec_unscaled(v, u=dlr_64)
       u = dlr_64
    end block
    scale = dec_scale(v)
    if (u == "0") then
       block
          character(len=:), allocatable :: dlr_65
          call dec_make("0", 0, o=dlr_65)
          o = dlr_65
       end block
       return
    end if
    do while (scale > 0)
       if (u(len(u):len(u)) /= "0") exit
       u = u(1:len(u)-1)
       scale = scale - 1
    end do
    block
       character(len=:), allocatable :: dlr_66
       call dec_make(u, scale, o=dlr_66)
       o = dlr_66
    end block
  end subroutine dec_strip

  ! ---- conversions ------------------------------------------------

  pure function dec_to_dbl(v) result(d)
    character(len=*), intent(in) :: v
    double precision :: d
    integer :: ios
    character(len=:), allocatable :: txt
    ! through a VARIABLE: a function result is not an internal file
    block
       character(len=:), allocatable :: dlr_67
       call dec_to_text(v, s=dlr_67)
       txt = dlr_67
    end block
    read(txt, *, iostat=ios) d
    if (ios /= 0) d = 0.0d0
  end function dec_to_dbl

  ! TRUNCATING toward zero, which is BigDecimal.toBigInteger.
  pure subroutine dec_to_big(v, o)
    character(len=*), intent(in) :: v
    character(len=:), allocatable, intent(out) :: o
    character(len=:), allocatable :: q, r
    integer :: scale
    scale = dec_scale(v)
    if (scale <= 0) then
       block
          character(len=:), allocatable :: dlr_68, dlr_69
          call dec_unscaled(v, u=dlr_68)
          call shift_up(dlr_68, -scale, o=dlr_69)
          o = dlr_69
       end block
    else
       block
          character(len=:), allocatable :: dlr_70, dlr_71
          call dec_unscaled(v, u=dlr_70)
          call shift_up("1", scale, o=dlr_71)
          call big_divmod(dlr_70, dlr_71, q, r)
       end block
       o = q
    end if
  end subroutine dec_to_big

end module BigDec
