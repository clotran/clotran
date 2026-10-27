! anform_check: runs the GENERATED special-form checks (anform_gen.inc,
! from model/anform.lisp) on calls read from a file, through mock frm_* and
! frf_* reads that answer what model/anform.lisp's reads answer of the same
! forms, and anlocal's generated anl_name_code (anlocal_gen.inc).
! scripts/fuzz-anform-gen writes the cases and compares the answers with
! ACL2's. With the argument `broken`, the class read is flipped on purpose:
! the negative control.
!
!   anform_check CASEFILE [broken]
!
! CASEFILE: nforms ncalls, then a line a form, 1..nforms (0 is a form of no
! kind): kind qual word class defvar n child.. ; then a line a call: code a
! b c d. Out: a line a call, its answer.
module anform_mock
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
  integer, allocatable :: fkind(:), fqual(:), fword(:), fclass(:), fdefv(:), fn(:), foff(:), fkids(:)
  logical :: broken = .false.
contains
  logical function ok(x)
    type(gc_value), intent(in) :: x
    ok = x%id >= 1 .and. x%id <= size(fkind)
  end function ok

  integer(int64) function frf_kind(x)
    type(gc_value), intent(in) :: x
    frf_kind = 0
    if (ok(x)) frf_kind = fkind(x%id)
  end function frf_kind

  integer(int64) function frm_kind(x)
    type(gc_value), intent(in) :: x
    frm_kind = frf_kind(x)
    if (frm_kind > 2) frm_kind = 0
  end function frm_kind

  integer(int64) function frm_count(x)
    type(gc_value), intent(in) :: x
    frm_count = 0
    if (frm_kind(x) == 1) frm_count = fn(x%id)
  end function frm_count

  integer(int64) function frf_len(x)
    type(gc_value), intent(in) :: x
    frf_len = 0
    if (frf_kind(x) == 3) frf_len = fn(x%id)
  end function frf_len

  function kid(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e
    e%id = 0
    if (i >= 0 .and. i < fn(x%id)) e%id = fkids(foff(x%id) + i)
  end function kid

  function frm_nth(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e
    e%id = 0
    if (frm_kind(x) == 1) e = kid(x, i)
  end function frm_nth

  function frf_nth(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e
    e%id = 0
    if (frf_kind(x) == 3) e = kid(x, i)
  end function frf_nth

  integer(int64) function frm_qual(x)
    type(gc_value), intent(in) :: x
    frm_qual = 0
    if (frm_kind(x) == 2) frm_qual = fqual(x%id)
  end function frm_qual

  integer(int64) function frm_amp(x)
    type(gc_value), intent(in) :: x
    frm_amp = 0
  end function frm_amp

  integer(int64) function frf_word(x)
    type(gc_value), intent(in) :: x
    frf_word = 0
    if (frm_kind(x) == 2) frf_word = fword(x%id)
    if (frf_word < 0 .or. frf_word > 2) frf_word = 0
  end function frf_word

  integer(int64) function frf_class(x)
    type(gc_value), intent(in) :: x
    frf_class = 0
    if (frm_kind(x) == 2) frf_class = fclass(x%id)
    if (broken .and. frm_kind(x) == 2) frf_class = 1 - frf_class
  end function frf_class

  integer(int64) function frf_defvar(x)
    type(gc_value), intent(in) :: x
    frf_defvar = 0
    if (frm_kind(x) == 2) frf_defvar = fdefv(x%id)
    if (frf_defvar < 0 .or. frf_defvar > 2) frf_defvar = 0
  end function frf_defvar

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
  include "anform_gen.inc"
end module anform_mock

program anform_check
  use iso_fortran_env, only: int64
  use anform_mock
  implicit none
  character(len=4096) :: path, arg
  integer :: u, nfm, ncalls, i, k, cnt, vals(64), tk, op
  integer(int64) :: a, b, c, d, r
  type(gc_value) :: x
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = (trim(arg) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) nfm, ncalls
  allocate(fkind(nfm), fqual(nfm), fword(nfm), fclass(nfm), fdefv(nfm), fn(nfm), foff(nfm), fkids(nfm * 64 + 1))
  tk = 1
  do i = 1, nfm
     read(u, *) cnt, vals(1:cnt)
     fkind(i) = vals(1)
     fqual(i) = vals(2)
     fword(i) = vals(3)
     fclass(i) = vals(4)
     fdefv(i) = vals(5)
     fn(i) = vals(6)
     foff(i) = tk
     fkids(tk:tk + fn(i) - 1) = vals(7:6 + fn(i))
     tk = tk + fn(i)
  end do
  do k = 0, ncalls - 1
     read(u, *) op, a, b, c, d
     x%id = int(a)
     r = -1
     select case (op)
     case (1); r = anf_if(a)
     case (2); r = anf_def(x, b)
     case (3); r = anf_quote(a)
     case (4); r = anf_throw(a)
     case (5); r = anf_try_op(x)
     case (6)
        x%id = int(b)
        r = anf_try_step(a, x, c, d)
     case (7); r = anf_catch(x)
     case (8); r = anf_set(a)
     case (9); r = anf_set_target(x)
     case (10); r = anf_dot(x)
     case (12)
        x%id = int(b)
        r = anf_dot_member(a, x)
     case (11); r = anf_new(x)
     end select
     write(*, '(i0)') r
  end do
  close(u)
end program anform_check
