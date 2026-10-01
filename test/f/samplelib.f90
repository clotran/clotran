! A library as a Fortran author writes one -- no shims, no manifest --
! for scripts/bind-fortran to bind. The generated shims build into
! build/libsamplelib and the language test calls them through the door.
module samplelib
  implicit none
contains
  subroutine double_it(x, y)
    real(8), intent(in) :: x
    real(8), intent(out) :: y
    y = 2.0d0 * x
  end subroutine double_it

  function sum_arr(a, n) result(s)
    integer, intent(in) :: n
    real(8), intent(in) :: a(n)
    real(8) :: s
    s = sum(a)
  end function sum_arr

  subroutine scale(a, n, k)
    integer, intent(in) :: n
    real(8), intent(inout) :: a(n)
    real(8), intent(in) :: k
    a = a * k
  end subroutine scale

  subroutine divmod(a, b, q, r)
    integer, intent(in) :: a, b
    integer, intent(out) :: q, r
    q = a / b
    r = mod(a, b)
  end subroutine divmod

  function count_chars(s) result(n)
    character(len=*), intent(in) :: s
    integer :: n
    n = len(s)
  end function count_chars

  ! one argument of each scalar kind the door carries, echoed back:
  ! scripts/fuzz-door checks that what crosses is what the model's
  ! `cross` accepts, and that it arrives unchanged
  subroutine echo_kinds(i4, i8, r8, l, oi4, oi8, or8, ol)
    integer(4), intent(in) :: i4
    integer(8), intent(in) :: i8
    real(8), intent(in) :: r8
    logical, intent(in) :: l
    integer(4), intent(out) :: oi4
    integer(8), intent(out) :: oi8
    real(8), intent(out) :: or8
    logical, intent(out) :: ol
    oi4 = i4
    oi8 = i8
    or8 = r8
    ol = l
  end subroutine echo_kinds

  subroutine trace(m, n, t)
    integer, intent(in) :: n
    real(8), intent(in) :: m(n, n)
    real(8), intent(out) :: t
    integer :: i
    t = 0
    do i = 1, n
       t = t + m(i, i)
    end do
  end subroutine trace

end module samplelib
