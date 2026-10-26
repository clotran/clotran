! anlocal_check: runs the GENERATED analyzer locals (anlocal_gen.inc, from
! model/anlocal.lisp) on a sequence of operations read from a file,
! through mock frm_* reads that answer what model/anlocal.lisp's frm-*
! answer of the same forms. scripts/fuzz-anlocal-gen writes the cases and
! compares the answers with ACL2's. With the argument `broken`, the reads
! and the names are wrong on purpose (qualified flipped, a lookup asking
! for the next name): the negative control.
!
!   anlocal_check CASEFILE [broken]
!
! CASEFILE: nforms nops, then a line a form, 1..nforms (0 is a form that
! is neither a vector nor a symbol): kind qual amp n child.. ; then a line
! an operation: code a b c. Out: a line an operation, "(k r1 r2 err nf nb
! nx nc na nn nev e1 s1 ..)", the ev / es pairs after env, caps and names.
module anlocal_mock
  use iso_fortran_env, only: int64
  implicit none
  type :: gc_value
     integer :: id = 0
  end type gc_value
  type :: anl_state
     integer(int64), pointer, contiguous :: fctr(:) => null(), fout(:) => null(), fcap(:) => null(), &
          fvar(:) => null(), fah(:) => null(), fnl(:) => null(), bpar(:) => null(), bfn(:) => null(), &
          bhead(:) => null(), xnm(:) => null(), xsl(:) => null(), xblk(:) => null(), xnext(:) => null(), &
          cnm(:) => null(), cout(:) => null(), cin(:) => null(), cbx(:) => null(), cnext(:) => null(), &
          nsl(:) => null(), nnm(:) => null(), nnext(:) => null(), an(:) => null(), anext(:) => null(), &
          ev(:) => null(), es(:) => null()
     integer(int64) :: nf = 0, nb = 0, nx = 0, nc = 0, na = 0, nn = 0, nev = 0, err = 0
  end type anl_state
  integer, allocatable :: fkind(:), fqual(:), famp(:), fn(:), foff(:), fkids(:)
  logical :: broken = .false.
contains
  logical function ok(x)
    type(gc_value), intent(in) :: x
    ok = x%id >= 1 .and. x%id <= size(fkind)
  end function ok

  integer(int64) function frm_kind(x)
    type(gc_value), intent(in) :: x
    frm_kind = 0
    if (ok(x)) frm_kind = fkind(x%id)
  end function frm_kind

  integer(int64) function frm_count(x)
    type(gc_value), intent(in) :: x
    frm_count = 0
    if (ok(x)) then
       if (fkind(x%id) == 1) frm_count = fn(x%id)
    end if
  end function frm_count

  function frm_nth(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e
    e%id = 0
    if (ok(x)) then
       if (fkind(x%id) == 1 .and. i >= 0 .and. i < fn(x%id)) e%id = fkids(foff(x%id) + i)
    end if
  end function frm_nth

  integer(int64) function frm_qual(x)
    type(gc_value), intent(in) :: x
    frm_qual = 0
    if (ok(x)) then
       if (fkind(x%id) == 2) frm_qual = fqual(x%id)
       if (broken .and. fkind(x%id) == 2) frm_qual = 1 - frm_qual
    end if
  end function frm_qual

  integer(int64) function frm_amp(x)
    type(gc_value), intent(in) :: x
    frm_amp = 0
    if (ok(x)) then
       if (fkind(x%id) == 2) frm_amp = famp(x%id)
    end if
  end function frm_amp

  ! the runtime's, as VmRuntime.f90 has it: the elements kept
  subroutine rt_resize_int(a, n)
    integer(int64), pointer, contiguous, intent(inout) :: a(:)
    integer(int64), intent(in) :: n
    integer(int64), pointer, contiguous :: t(:)
    integer(int64) :: m
    allocate(t(0:n-1))
    t = 0
    m = 0
    if (associated(a)) then
       m = min(n, size(a, kind=int64))
       if (m > 0) t(0:m-1) = a(0:m-1)
       deallocate(a)
    end if
    a => t
  end subroutine rt_resize_int

  include "anlocal_gen.inc"
end module anlocal_mock

program anlocal_check
  use iso_fortran_env, only: int64
  use anlocal_mock
  implicit none
  character(len=4096) :: path, arg
  integer :: u, nfm, nops, i, k, cnt, vals(64), tk, op
  integer(int64) :: a, b, c, r1, r2
  type(anl_state) :: ls
  type(gc_value) :: x
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = (trim(arg) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) nfm, nops
  allocate(fkind(nfm), fqual(nfm), famp(nfm), fn(nfm), foff(nfm), fkids(nfm * 64 + 1))
  tk = 1
  do i = 1, nfm
     read(u, *) cnt, vals(1:cnt)
     fkind(i) = vals(1)
     fqual(i) = vals(2)
     famp(i) = vals(3)
     fn(i) = vals(4)
     foff(i) = tk
     fkids(tk:tk + fn(i) - 1) = vals(5:4 + fn(i))
     tk = tk + fn(i)
  end do
  ! the arrays as ACL2's start: there, and empty
  call rt_resize_int(ls%fctr, 0_int64); call rt_resize_int(ls%fout, 0_int64); call rt_resize_int(ls%fcap, 0_int64)
  call rt_resize_int(ls%fvar, 0_int64); call rt_resize_int(ls%fah, 0_int64); call rt_resize_int(ls%fnl, 0_int64)
  call rt_resize_int(ls%bpar, 0_int64); call rt_resize_int(ls%bfn, 0_int64); call rt_resize_int(ls%bhead, 0_int64)
  call rt_resize_int(ls%xnm, 0_int64); call rt_resize_int(ls%xsl, 0_int64); call rt_resize_int(ls%xblk, 0_int64)
  call rt_resize_int(ls%xnext, 0_int64); call rt_resize_int(ls%cnm, 0_int64); call rt_resize_int(ls%cout, 0_int64)
  call rt_resize_int(ls%cin, 0_int64); call rt_resize_int(ls%cbx, 0_int64); call rt_resize_int(ls%cnext, 0_int64)
  call rt_resize_int(ls%nsl, 0_int64); call rt_resize_int(ls%nnm, 0_int64); call rt_resize_int(ls%nnext, 0_int64)
  call rt_resize_int(ls%an, 0_int64); call rt_resize_int(ls%anext, 0_int64); call rt_resize_int(ls%ev, 0_int64)
  call rt_resize_int(ls%es, 0_int64)
  do k = 0, nops - 1
     read(u, *) op, a, b, c
     r1 = 0
     r2 = 0
     x%id = int(a)
     select case (op)
     case (1); call anl_new_fn(ls, a, r1)
     case (2); call anl_child(ls, a, r1)
     case (3); call anl_reserve(ls, a, b, r1)
     case (4); call anl_bind(ls, a, b, c)
     case (5)
        if (broken) b = b + 1
        call anl_lookup(ls, a, b, r1, r2)
     case (6); call anl_arity(ls, a, b, c, r1)
     case (7); r1 = anl_arity_end(ls, a)
     case (8); call anl_env(ls, a)
     case (9); call anl_caps_of(ls, a)
     case (10); call anl_names_of(ls, a)
     case (11); r1 = anl_nslots(ls, a)
     case (15); ls%err = 0
     case (12); r1 = anl_shape(x)
     case (13); r1 = anl_name_code(x)
     case (14); r1 = anl_params(x, b)
     end select
     write(*, '(a, i0, 11(1x, i0))', advance="no") "(", k, r1, r2, ls%err, ls%nf, ls%nb, ls%nx, ls%nc, ls%na, ls%nn, ls%nev
     if (op >= 8 .and. op <= 10) then
        do i = 0, int(ls%nev) - 1
           write(*, '(2(1x, i0))', advance="no") ls%ev(i), ls%es(i)
        end do
     end if
     write(*, '(a)') ")"
  end do
  close(u)
end program anlocal_check
