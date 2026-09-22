! BigDec -- arbitrary-precision decimals, as an unscaled integer and a
! scale.
!
! java.math.BigDecimal is a type the LANGUAGE has: `1.0M` reads as one,
! `(= 1.0M 1.0)` is FALSE because a decimal is its own equality
! category, and `bigdec` and `with-precision` exist to make them. It is
! reproduced here rather than approximated as a double (DEVIATIONS 30).
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

contains

  ! ---- the pair ---------------------------------------------------

  pure function dec_make(unscaled, scale) result(o)
    character(len=*), intent(in) :: unscaled
    integer, intent(in) :: scale
    character(len=:), allocatable :: o
    character(len=16) :: buf
    write(buf, '(I0)') scale
    o = big_norm(unscaled) // "|" // trim(buf)
  end function dec_make

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

  pure function dec_unscaled(v) result(u)
    character(len=*), intent(in) :: v
    character(len=:), allocatable :: u
    integer :: p
    p = bar_at(v)
    if (p > 1) then
       u = v(1:p-1)
    else
       u = "0"
    end if
  end function dec_unscaled

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
    yes = (dec_unscaled(v) == "0")
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
    out = dec_make("0", 0)
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
    out = dec_make(digits, scale - ex)
    ok = .true.
  end subroutine dec_from_text

  pure function dec_from_i64(i) result(o)
    integer(I8), intent(in) :: i
    character(len=:), allocatable :: o
    o = dec_make(big_from_i64(i), 0)
  end function dec_from_i64

  pure function dec_from_big(b) result(o)
    character(len=*), intent(in) :: b
    character(len=:), allocatable :: o
    o = dec_make(b, 0)
  end function dec_from_big

  ! ---- printing ---------------------------------------------------

  ! BigDecimal.toString: plain when the scale is not negative and the
  ! adjusted exponent is at least -6, scientific otherwise. The two
  ! rules are Java's, and they are why 0.001M prints plainly and
  ! 1E-7M does not.
  pure function dec_to_text(v) result(s)
    character(len=*), intent(in) :: v
    character(len=:), allocatable :: s, u, mag, sign
    integer :: scale, prec, adjusted, i
    character(len=16) :: buf

    u = dec_unscaled(v)
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
             s = s // "0"
          end do
          s = s // mag
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
       s = s // "E-" // trim(buf)
    else
       s = s // "E+" // trim(buf)
    end if
  end function dec_to_text

  ! ---- scale alignment --------------------------------------------

  ! The unscaled value it would have at a LARGER scale: multiply by a
  ! power of ten, which on decimal text is appending zeros.
  pure function shift_up(u, by) result(o)
    character(len=*), intent(in) :: u
    integer, intent(in) :: by
    character(len=:), allocatable :: o
    integer :: i
    o = u
    if (by <= 0 .or. u == "0") then
       if (u == "0") o = "0"
       return
    end if
    do i = 1, by
       o = o // "0"
    end do
    o = big_norm(o)
  end function shift_up

  ! ---- arithmetic -------------------------------------------------

  ! add and subtract take the LARGER scale, as BigDecimal does.
  pure function dec_add(a, b) result(o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable :: o
    integer :: sa, sb, s
    sa = dec_scale(a)
    sb = dec_scale(b)
    s = max(sa, sb)
    o = dec_make(big_add(shift_up(dec_unscaled(a), s - sa), &
                         shift_up(dec_unscaled(b), s - sb)), s)
  end function dec_add

  pure function dec_sub(a, b) result(o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable :: o
    o = dec_add(a, dec_neg(b))
  end function dec_sub

  ! multiply ADDS the scales: 1.5M * 2.25M is 3.375M.
  pure function dec_mul(a, b) result(o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable :: o
    o = dec_make(big_mul(dec_unscaled(a), dec_unscaled(b)), &
                 dec_scale(a) + dec_scale(b))
  end function dec_mul

  pure function dec_neg(a) result(o)
    character(len=*), intent(in) :: a
    character(len=:), allocatable :: o
    o = dec_make(big_neg(dec_unscaled(a)), dec_scale(a))
  end function dec_neg

  pure function dec_abs(a) result(o)
    character(len=*), intent(in) :: a
    character(len=:), allocatable :: o
    o = dec_make(big_abs(dec_unscaled(a)), dec_scale(a))
  end function dec_abs

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
    o = dec_make("0", 0)
    if (dec_unscaled(b) == "0") return
    sa = dec_scale(a)
    sb = dec_scale(b)
    ! One more digit each round: at most as many as a long double
    ! would carry plus room for a repeating check to fail on.
    do k = 0, 64
       num = shift_up(dec_unscaled(a), k)
       call big_divmod(num, dec_unscaled(b), q, r)
       if (r == "0") then
          o = dec_make(q, sa - sb + k)
          ok = .true.
          return
       end if
    end do
  end subroutine dec_div

  ! divideToIntegralValue: the integer part of the quotient, at the
  ! preferred scale (this scale minus the divisor's, never negative),
  ! so (quot 10.5M 3) is 3.0M.
  pure function dec_quot(a, b) result(o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable :: o, q, r, ua, ub
    integer :: sa, sb, s
    sa = dec_scale(a)
    sb = dec_scale(b)
    s = max(sa - sb, 0)
    ua = dec_unscaled(a)
    ub = dec_unscaled(b)
    ! bring both to a common scale so the quotient is the integer one
    ua = shift_up(ua, max(sb - sa, 0))
    ub = shift_up(ub, max(sa - sb, 0))
    call big_divmod(ua, ub, q, r)
    o = dec_make(shift_up(q, s), s)
  end function dec_quot

  ! a - (quot a b) * b, which is what BigDecimal.remainder is.
  pure function dec_rem(a, b) result(o)
    character(len=*), intent(in) :: a, b
    character(len=:), allocatable :: o
    o = dec_sub(a, dec_mul(dec_quot(a, b), b))
  end function dec_rem

  ! ---- comparison -------------------------------------------------

  ! BY VALUE, not by scale: 1M and 1.0M compare equal, which is what
  ! Clojure's = says about them.
  pure function dec_cmp(a, b) result(c)
    character(len=*), intent(in) :: a, b
    integer :: c, sa, sb, s
    sa = dec_scale(a)
    sb = dec_scale(b)
    s = max(sa, sb)
    c = big_cmp(shift_up(dec_unscaled(a), s - sa), &
                shift_up(dec_unscaled(b), s - sb))
  end function dec_cmp

  ! The same value with no trailing zeros -- what equal decimals share,
  ! so hashing can use it and agree with dec_cmp.
  pure function dec_strip(v) result(o)
    character(len=*), intent(in) :: v
    character(len=:), allocatable :: o, u
    integer :: scale
    u = dec_unscaled(v)
    scale = dec_scale(v)
    if (u == "0") then
       o = dec_make("0", 0)
       return
    end if
    do while (scale > 0)
       if (u(len(u):len(u)) /= "0") exit
       u = u(1:len(u)-1)
       scale = scale - 1
    end do
    o = dec_make(u, scale)
  end function dec_strip

  ! ---- conversions ------------------------------------------------

  pure function dec_to_dbl(v) result(d)
    character(len=*), intent(in) :: v
    double precision :: d
    integer :: ios
    character(len=:), allocatable :: txt
    ! through a VARIABLE: a function result is not an internal file
    txt = dec_to_text(v)
    read(txt, *, iostat=ios) d
    if (ios /= 0) d = 0.0d0
  end function dec_to_dbl

  ! TRUNCATING toward zero, which is BigDecimal.toBigInteger.
  pure function dec_to_big(v) result(o)
    character(len=*), intent(in) :: v
    character(len=:), allocatable :: o, q, r
    integer :: scale
    scale = dec_scale(v)
    if (scale <= 0) then
       o = shift_up(dec_unscaled(v), -scale)
    else
       call big_divmod(dec_unscaled(v), shift_up("1", scale), q, r)
       o = q
    end if
  end function dec_to_big

end module BigDec
