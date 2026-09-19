# Vendored reference BLAS

`dgemm.f`, `lsame.f` and `xerbla.f` are the reference BLAS from netlib,
fetched verbatim on 2026-09-19 from

    https://www.netlib.org/blas/dgemm.f
    https://www.netlib.org/blas/lsame.f
    https://www.netlib.org/blas/xerbla.f

Do not edit them. They are F77 fixed-form source and build with both
gfortran and flang as-is.

`LICENSE` is `https://www.netlib.org/lapack/LICENSE.txt`, the modified
BSD license under which the reference BLAS is distributed with LAPACK;
netlib's BLAS FAQ states the reference BLAS is freely available and may
be included in other software. `NOTICE` at the repository root lists it.

## Why these three, and why vendored

`dgemm` is the first Fortran routine clotran calls (PLAN.md step 6): a
clotran `real8` array is handed to it as the `A(LDA,*)` it declares,
with no copy, no descriptor and no C shim, which is the claim the whole
project rests on. `lsame` and `xerbla` are the two routines `dgemm`
calls. Vendoring rather than linking a system BLAS (Accelerate on
macOS, OpenBLAS elsewhere) means the same source builds the same way
on every machine, which for a proof of the calling convention matters
more than speed. A system BLAS can replace these three files later
without touching anything that calls them.

`xerbla` STOPs the process on a bad argument. clotran checks shapes
before calling, so it never fires; if it ever does, that is a clotran
bug.
