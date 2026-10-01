  ! --- exact rationals ---------------------------------------------
  !
  ! A Ratio as Clojure's is: two integers of any size, in lowest terms,
  ! the sign on the numerator (DEVIATIONS 26's removal). One that fits
  ! is IMMEDIATE -- GCT_RATIO, the numerator in ival and the denominator
  ! in ref, so a numerator up to a long and a denominator up to 2^31-1;
  ! any other is BIG -- GCT_BIGRATIO, its "n/d" text in the string
  ! pool, as a BigInt is its digits. A value has exactly one of the two
  ! forms (rat_make decides), so equality is equality of parts.
  !
  ! Before this a denominator past 2^31 wrapped and a numerator past a
  ! long overflowed: (/ 1 3000000000) was 1/-1294967296 and (+
  ! 9223372036854775807 1/2) was -1/2 (scripts/fuzz --fns found them).
  ! The fast path is 128-bit integer arithmetic on immediate operands,
  ! which no product of two immediates overflows; the text path only
  ! runs for what the immediate form cannot hold.

  ! an integer, a BigInt or a Ratio of either form
  logical function rat_exact(v)
    type(gc_value), intent(in) :: v
    rat_exact = v%tag == GCT_INT .or. v%tag == GCT_BIG .or. v%tag == GCT_RATIO .or. v%tag == GCT_BIGRATIO
  end function rat_exact

  ! numerator and denominator as decimal text
  subroutine rat_parts(v, n, d)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: n, d
    character(len=:), allocatable :: t
    integer :: k
    select case (v%tag)
    case (GCT_RATIO)
       call big_from_i64(gc_numerator(v), o=n)
       call big_from_i64(gc_denominator(v), o=d)
    case (GCT_BIGRATIO)
       call gc_bigratio_text(v, s=t)
       k = index(t, "/")
       n = t(1:k - 1)
       d = t(k + 1:)
    case (GCT_BIG)
       call gc_big_text(v, s=n)
       d = "1"
    case default
       call big_from_i64(v%ival, o=n)
       d = "1"
    end select
  end subroutine rat_parts

  ! n/d in its one form: GC.f90's gc_rat_make, which the reader shares
  function rat_make(n0, d0, int_big, roots) result(v)
    character(len=*), intent(in) :: n0, d0
    logical, intent(in) :: int_big
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    v = gc_rat_make(n0, d0, int_big, roots)
  end function rat_make

  ! the decimal text of a 128-bit integer
  subroutine i16_text(x, s)
    integer(i16k), intent(in) :: x
    character(len=:), allocatable, intent(out) :: s
    character(len=48) :: buf
    write(buf, '(I0)') x
    s = trim(buf)
  end subroutine i16_text

  function i16_gcd(a0, b0) result(g)
    integer(i16k), intent(in) :: a0, b0
    integer(i16k) :: g, a, b, t
    a = abs(a0)
    b = abs(b0)
    do while (b /= 0)
       t = mod(a, b)
       a = b
       b = t
    end do
    g = a
  end function i16_gcd

  ! a op b for exact operands; the divisor of a division is not zero
  function rat_op(op, a, b, int_big, roots) result(v)
    integer, intent(in) :: op
    type(gc_value), intent(in) :: a, b
    logical, intent(in) :: int_big
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character(len=:), allocatable :: an, ad, bn, bd, x, y, n, d, sn, sd
    if ((a%tag == GCT_INT .or. a%tag == GCT_RATIO) .and. (b%tag == GCT_INT .or. b%tag == GCT_RATIO)) then
       block
         integer(i16k) :: p, q, r, s, nn, dd, g
         p = gc_numerator(a); q = gc_denominator(a)
         r = gc_numerator(b); s = gc_denominator(b)
         select case (op)
         case (RAT_ADD); nn = p * s + r * q; dd = q * s
         case (RAT_SUB); nn = p * s - r * q; dd = q * s
         case (RAT_MUL); nn = p * r; dd = q * s
         case default;   nn = p * s; dd = q * r
         end select
         if (dd < 0) then
            nn = -nn
            dd = -dd
         end if
         g = i16_gcd(nn, dd)
         if (g > 1) then
            nn = nn / g
            dd = dd / g
         end if
         if (dd == 1 .and. .not. int_big .and. abs(nn) <= int(huge(0_gc_ip), i16k)) then
            v = gc_int(int(nn, gc_ip))
            return
         end if
         if (dd > 1 .and. dd <= 2147483647_i16k .and. nn <= int(huge(0_gc_ip), i16k) &
              .and. nn >= -int(huge(0_gc_ip), i16k) - 1_i16k) then
            v = gc_ratio(int(nn, gc_ip), int(dd, gc_ip))
            return
         end if
         call i16_text(nn, sn)
         call i16_text(dd, sd)
         v = rat_make(sn, sd, int_big, roots)
         return
       end block
    end if
    call rat_parts(a, an, ad)
    call rat_parts(b, bn, bd)
    select case (op)
    case (RAT_ADD, RAT_SUB)
       call big_mul(an, bd, x)
       call big_mul(bn, ad, y)
       if (op == RAT_ADD) then
          call big_add(x, y, n)
       else
          call big_sub(x, y, n)
       end if
       call big_mul(ad, bd, d)
    case (RAT_MUL)
       call big_mul(an, bn, n)
       call big_mul(ad, bd, d)
    case default
       call big_mul(an, bd, n)
       call big_mul(ad, bn, d)
    end select
    v = rat_make(n, d, int_big, roots)
  end function rat_op

  ! -1, 0 or 1 as a < b, a = b, a > b, exactly (denominators positive)
  integer function rat_cmp(a, b)
    type(gc_value), intent(in) :: a, b
    character(len=:), allocatable :: an, ad, bn, bd, x, y
    if ((a%tag == GCT_INT .or. a%tag == GCT_RATIO) .and. (b%tag == GCT_INT .or. b%tag == GCT_RATIO)) then
       block
         integer(i16k) :: l, r
         l = int(gc_numerator(a), i16k) * int(gc_denominator(b), i16k)
         r = int(gc_numerator(b), i16k) * int(gc_denominator(a), i16k)
         rat_cmp = merge(-1, merge(1, 0, l > r), l < r)
       end block
       return
    end if
    call rat_parts(a, an, ad)
    call rat_parts(b, bn, bd)
    call big_mul(an, bd, x)
    call big_mul(bn, ad, y)
    rat_cmp = big_cmp(x, y)
  end function rat_cmp

  ! the integer part, truncated toward zero, as text
  subroutine rat_trunc(v, q)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: q
    character(len=:), allocatable :: n, d, r
    call rat_parts(v, n, d)
    call big_divmod(n, d, q, r)
  end subroutine rat_trunc

  ! as a double: each part converted, then divided -- Fortran's IEEE
  ! quotient (DEVIATIONS 70 says where that differs from clj)
  function rat_dbl(v) result(x)
    type(gc_value), intent(in) :: v
    real(gc_dp) :: x
    character(len=:), allocatable :: n, d
    if (v%tag == GCT_RATIO) then
       x = real(gc_numerator(v), gc_dp) / real(gc_denominator(v), gc_dp)
       return
    end if
    call rat_parts(v, n, d)
    x = big_to_dbl(n) / big_to_dbl(d)
  end function rat_dbl
