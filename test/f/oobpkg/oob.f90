! A package with a mistake in it, for make check-profiles: poke writes
! past the end of the array it is given. Under the dev profile gfortran's
! -fcheck=bounds stops it with "above upper bound"; release would let it
! corrupt whatever lies after.
module oob
  implicit none
contains
  subroutine poke(n, x)
    integer, intent(in) :: n
    real(8), intent(inout) :: x(n)
    x(n + 2) = 1.0d0
  end subroutine poke
end module oob
