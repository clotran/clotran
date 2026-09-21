! The BLAS package: netlib's reference dgemm (src/f/blas, vendored,
! unmodified) behind the door (src/f/DynLoad.f90). The manifest names one
! routine; its shim takes the two matrices and the result by pointer,
! each followed by its two extents, checks that the shapes agree, and
! calls DGEMM as the F77 interface declares it: C = A x B, no transposes,
! leading dimensions the row counts, column-major as clotran's arrays are.
module blas_pkg
  use iso_c_binding
  implicit none
  character(kind=c_char, len=*), parameter :: manifest = &
       '{:package "blas.raw" :routines [' // &
       '{:name "dgemm" :symbol "blas_dgemm_shim" :args [' // &
       '{:name "a" :type :real8 :intent :in :rank 2} {:name "b" :type :real8 :intent :in :rank 2}' // &
       ' {:name "c" :type :real8 :intent :inout :rank 2}]}]}' // c_null_char
  character(kind=c_char), target, save :: manifest_buf(len(manifest)) = transfer(manifest, [c_char_'a'], len(manifest))
  interface
     subroutine dgemm(transa, transb, m, n, k, alpha, a, lda, b, ldb, beta, c, ldc)
       character :: transa, transb
       integer :: m, n, k, lda, ldb, ldc
       double precision :: alpha, beta
       double precision :: a(lda, *), b(ldb, *), c(ldc, *)
     end subroutine dgemm
  end interface
contains
  function clotran_manifest() bind(C, name="clotran_manifest") result(p)
    type(c_ptr) :: p
    p = c_loc(manifest_buf)
  end function clotran_manifest

  subroutine blas_dgemm_shim(argc, argv) bind(C, name="blas_dgemm_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    integer(c_int), pointer :: m, k, k2, n, m2, n2
    real(c_double), pointer :: a(:,:), b(:,:), c(:,:)
    call c_f_pointer(argv(2), m); call c_f_pointer(argv(3), k)
    call c_f_pointer(argv(5), k2); call c_f_pointer(argv(6), n)
    call c_f_pointer(argv(8), m2); call c_f_pointer(argv(9), n2)
    ! a shape that does not agree is left alone: blas.cljf has already
    ! refused it by name, so this is the belt to that's braces
    if (k /= k2 .or. m /= m2 .or. n /= n2) return
    call c_f_pointer(argv(1), a, [m, k]); call c_f_pointer(argv(4), b, [k, n]); call c_f_pointer(argv(7), c, [m, n])
    call dgemm('N', 'N', int(m), int(n), int(k), 1.0d0, a, max(1, int(m)), b, max(1, int(k)), 0.0d0, c, max(1, int(m)))
  end subroutine blas_dgemm_shim
end module blas_pkg
