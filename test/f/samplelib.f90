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
