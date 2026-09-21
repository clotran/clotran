! The package the language test loads through the door (DynLoad.f90):
! three routines, their shims, and a manifest. What scripts/bind-fortran
! will write for a real library, written by hand once so the door and
! the calling convention are proved before the generator exists.
module testpkg
  use iso_c_binding
  implicit none
  character(kind=c_char, len=*), parameter :: manifest = &
       '{:package "testpkg" :routines [' // &
       '{:name "double-it" :symbol "double_it_shim" :args [' // &
       '{:name "x" :type :real8 :intent :in :rank 0} {:name "y" :type :real8 :intent :out :rank 0}]}' // &
       ' {:name "sum-arr" :symbol "sum_arr_shim" :args [{:name "a" :type :real8 :intent :in :rank 1}] :returns :real8}' // &
       ' {:name "scale!" :symbol "scale_shim" :args [{:name "a" :type :real8 :intent :inout :rank 1}' // &
       ' {:name "k" :type :real8 :intent :in :rank 0}]}' // &
       ' {:name "count-chars" :symbol "count_chars_shim" :args [{:name "s" :type :string :intent :in :rank 0}] :returns :int4}' // &
       ' {:name "divmod" :symbol "divmod_shim" :args [{:name "a" :type :int4 :intent :in :rank 0}' // &
       ' {:name "b" :type :int4 :intent :in :rank 0} {:name "q" :type :int4 :intent :out :rank 0}' // &
       ' {:name "r" :type :int4 :intent :out :rank 0}]}]}' // c_null_char
  character(kind=c_char), target, save :: manifest_buf(len(manifest)) = transfer(manifest, [c_char_'a'], len(manifest))
contains
  ! ---- the library's own routines, as a Fortran author writes them
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
  ! ---- what the generator emits: the manifest and one shim per routine
  function clotran_manifest() bind(C, name="clotran_manifest") result(p)
    type(c_ptr) :: p
    p = c_loc(manifest_buf)
  end function clotran_manifest
  subroutine double_it_shim(argc, argv) bind(C, name="double_it_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    real(c_double), pointer :: x, y
    call c_f_pointer(argv(1), x); call c_f_pointer(argv(2), y)
    call double_it(x, y)
  end subroutine double_it_shim
  subroutine sum_arr_shim(argc, argv) bind(C, name="sum_arr_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    integer(c_int), pointer :: n
    real(c_double), pointer :: a(:), s
    call c_f_pointer(argv(2), n)
    call c_f_pointer(argv(1), a, [n]); call c_f_pointer(argv(3), s)
    s = sum_arr(a, n)
  end subroutine sum_arr_shim
  subroutine scale_shim(argc, argv) bind(C, name="scale_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    integer(c_int), pointer :: n
    real(c_double), pointer :: a(:), k
    call c_f_pointer(argv(2), n)
    call c_f_pointer(argv(1), a, [n]); call c_f_pointer(argv(3), k)
    call scale(a, n, k)
  end subroutine scale_shim
  subroutine count_chars_shim(argc, argv) bind(C, name="count_chars_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    integer(c_int), pointer :: out
    character(kind=c_char), pointer :: s(:)
    integer :: n
    ! a string arrives null-terminated; its length is the first null
    call c_f_pointer(argv(1), s, [huge(0)])
    n = 0
    do while (s(n + 1) /= c_null_char)
       n = n + 1
    end do
    call c_f_pointer(argv(2), out)
    out = n
  end subroutine count_chars_shim
  subroutine divmod_shim(argc, argv) bind(C, name="divmod_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    integer(c_int), pointer :: a, b, q, r
    call c_f_pointer(argv(1), a); call c_f_pointer(argv(2), b)
    call c_f_pointer(argv(3), q); call c_f_pointer(argv(4), r)
    call divmod(a, b, q, r)
  end subroutine divmod_shim
end module testpkg
