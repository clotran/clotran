! anbuild_check: runs the GENERATED node assembly (anbuild_gen.inc, from
! model/anbuild.lisp) on forms read from a file, with anlocal's and anform's
! generated code (anlocal_gen.inc, anform_gen.inc) under it, through mock
! form reads and builder operations that answer what model/anbuild.lisp's
! answer of the same forms: a subform is analysed by anb_an itself, as
! anb-sub is; the host's analysis (anb_host) leaves N_CONST, or fails on a
! symbol marked so, as the attachment scripts/fuzz-anbuild-gen gives
! anb-host does. scripts/fuzz-anbuild-gen writes the cases and compares the
! answers with ACL2's. With the argument `broken`, a node's children are
! taken in the wrong order on purpose: the negative control.
!
!   anbuild_check CASEFILE [broken]
!
! CASEFILE: nforms root, then a line a form, 1..nforms (0 is a form of no
! kind): kind sid qual word class defvar sp meta n child.. . Out: the
! error code, the locals' record counts, and the builder's stack, each
! node serialised as model's anb-ser does.
module anbuild_mock
  use iso_fortran_env, only: int64
  implicit none
  type :: gc_value
     integer :: id = 0
     integer :: off = 0
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
  type :: anb_state
     integer :: unused = 0
  end type anb_state
  integer, allocatable :: fkind(:), fsid(:), fqual(:), fword(:), fclass(:), fdefv(:), fsp(:), fmeta(:), fn(:), foff(:), fkids(:)
  logical :: broken = .false.
  ! the builder: nodes by number, the stack of them
  integer, parameter :: MAXN = 200000
  integer :: nnodes = 0, top = 0
  integer :: nkind(MAXN), ni2(MAXN), ns3(MAXN), nkid0(MAXN), nnk(MAXN), nalt0(MAXN), nna(MAXN)
  integer :: lists(MAXN * 4), nlist = 0
  integer :: stk(MAXN)
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

  integer function nkids(x)
    type(gc_value), intent(in) :: x
    nkids = 0
    if (ok(x)) nkids = max(0, fn(x%id) - x%off)
  end function nkids

  integer(int64) function frm_count(x)
    type(gc_value), intent(in) :: x
    frm_count = 0
    if (frm_kind(x) == 1) frm_count = nkids(x)
  end function frm_count

  integer(int64) function frf_len(x)
    type(gc_value), intent(in) :: x
    frf_len = 0
    if (frf_kind(x) == 3) frf_len = nkids(x)
  end function frf_len

  function kid(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e
    e%id = 0
    e%off = 0
    if (i >= 0 .and. i < nkids(x)) e%id = fkids(foff(x%id) + x%off + int(i))
  end function kid

  function frm_nth(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e
    e%id = 0
    e%off = 0
    if (frm_kind(x) == 1) e = kid(x, i)
  end function frm_nth

  function frf_nth(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e
    e%id = 0
    e%off = 0
    if (frf_kind(x) == 3) e = kid(x, i)
  end function frf_nth

  function frf_rest(x) result(e)
    type(gc_value), intent(in) :: x
    type(gc_value) :: e
    e%id = 0
    e%off = 0
    if (frf_kind(x) == 3 .and. nkids(x) > 1) then
       e%id = x%id
       e%off = x%off + 1
    end if
  end function frf_rest

  integer(int64) function frm_qual(x)
    type(gc_value), intent(in) :: x
    frm_qual = 0
    if (frm_kind(x) == 2) frm_qual = fqual(x%id)
  end function frm_qual

  integer(int64) function frm_amp(x)
    type(gc_value), intent(in) :: x
    frm_amp = 0
    if (frm_kind(x) == 2) then
       if (fsid(x%id) == 70) frm_amp = 1
    end if
  end function frm_amp

  integer(int64) function frm_sid(x)
    type(gc_value), intent(in) :: x
    frm_sid = 0
    if (frm_kind(x) == 2) frm_sid = fsid(x%id)
  end function frm_sid

  integer(int64) function frm_bid(x)
    type(gc_value), intent(in) :: x
    frm_bid = frm_sid(x)
  end function frm_bid

  integer(int64) function frm_pairs(x)
    type(gc_value), intent(in) :: x
    frm_pairs = frm_count(x) / 2
  end function frm_pairs

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
  end function frf_class

  integer(int64) function frf_defvar(x)
    type(gc_value), intent(in) :: x
    frf_defvar = 0
    if (frm_kind(x) == 2) frf_defvar = fdefv(x%id)
    if (frf_defvar < 0 .or. frf_defvar > 2) frf_defvar = 0
  end function frf_defvar

  integer(int64) function frf_sp(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: h
    frf_sp = 0
    if (frf_len(x) < 1) return
    h = frf_nth(x, 0_int64)
    if (frm_kind(h) == 2) then
       if (fsp(h%id) > 0 .and. fsp(h%id) < 16) frf_sp = fsp(h%id)
    end if
  end function frf_sp

  integer(int64) function frf_meta(x)
    type(gc_value), intent(in) :: x
    frf_meta = 0
    if (frm_kind(x) == 2) then
       if (fmeta(x%id) == 1) frf_meta = 1
    end if
  end function frf_meta

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

  ! ---- the builder, as model/anbuild.lisp's ----
  integer function mk(kind, i2, nk, s3) result(k)
    integer, intent(in) :: kind, i2, nk, s3
    nnodes = nnodes + 1
    k = nnodes
    nkind(k) = kind
    ni2(k) = i2
    ns3(k) = s3
    nkid0(k) = nlist
    nnk(k) = nk
    nalt0(k) = nlist
    nna(k) = 0
  end function mk

  subroutine push(k)
    integer, intent(in) :: k
    top = top + 1
    stk(top) = k
  end subroutine push

  ! a node of kind, its n children the top n, the deepest first (fewer if
  ! the stack has fewer, as anb-popn takes)
  subroutine node_of(kind, i2, n0, s3)
    integer, intent(in) :: kind, i2, n0, s3
    integer :: k, i, n
    n = max(0, min(n0, top))
    k = mk(kind, i2, n, s3)
    nkid0(k) = nlist
    do i = top - n + 1, top
       nlist = nlist + 1
       lists(nlist) = stk(i)
    end do
    if (broken .and. n > 1) then
       i = lists(nlist)
       lists(nlist) = lists(nlist - 1)
       lists(nlist - 1) = i
    end if
    top = top - n
    call push(k)
  end subroutine node_of

  subroutine anb_const(bs, x)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    call push(mk(1, 0, 0, 0))
  end subroutine anb_const

  subroutine anb_local(bs, x, slot)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: slot
    call push(mk(2, int(slot), 0, 0))
  end subroutine anb_local

  subroutine anb_node(bs, kind, i2, n)
    type(anb_state), intent(inout) :: bs
    integer(int64), value :: kind, i2, n
    call node_of(int(kind), int(i2), int(n), 0)
  end subroutine anb_node

  subroutine anb_node_s(bs, kind, i2, n, s)
    type(anb_state), intent(inout) :: bs
    integer(int64), value :: kind, i2, n, s
    call node_of(int(kind), int(i2), int(n), 0)
  end subroutine anb_node_s

  subroutine anb_refuse(bs, code, f)
    type(anb_state), intent(inout) :: bs
    integer(int64), value :: code
    type(gc_value), value :: f
  end subroutine anb_refuse

  subroutine anb_refuse_catch(bs, code, f)
    type(anb_state), intent(inout) :: bs
    integer(int64), value :: code
    type(gc_value), value :: f
  end subroutine anb_refuse_catch

  subroutine anb_hint(bs, x)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
  end subroutine anb_hint

  subroutine anb_defvar(bs, x)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
  end subroutine anb_defvar

  ! the def's node: [init] then [meta] on top
  subroutine anb_def(bs, x, i2, m)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: i2, m
    integer :: md, k
    md = 0
    if (m == 1 .and. top > 0) then
       md = stk(top)
       top = top - 1
    end if
    if (mod(i2, 2_int64) == 1) then
       call node_of(10, int(i2), 1, md)
    else
       k = mk(10, int(i2), 0, md)
       call push(k)
    end if
  end subroutine anb_def

  ! a catch entry: kind -1, its slot, its handler
  subroutine anb_catch(bs, f, slot)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: f
    integer(int64), value :: slot
    integer :: h, k
    h = 0
    if (top > 0) then
       h = stk(top)
       top = top - 1
    end if
    k = mk(-1, int(slot), 0, h)
    call push(k)
  end subroutine anb_catch

  ! the try's node: [fin] on top, the catches under it, the body under them
  subroutine anb_trynode(bs, fin)
    type(anb_state), intent(inout) :: bs
    integer(int64), value :: fin
    integer :: fnd, nc, k, i, body
    fnd = 0
    if (fin == 1 .and. top > 0) then
       fnd = stk(top)
       top = top - 1
    end if
    nc = 0
    do while (top - nc >= 1)
       if (nkind(stk(top - nc)) /= -1) exit
       nc = nc + 1
    end do
    body = 0
    if (top - nc >= 1) body = stk(top - nc)
    k = mk(18, 0, 2, 0)
    nkid0(k) = nlist
    nlist = nlist + 1
    lists(nlist) = body
    nlist = nlist + 1
    lists(nlist) = fnd
    nalt0(k) = nlist
    do i = top - nc + 1, top
       nlist = nlist + 1
       lists(nlist) = ns3(stk(i))
    end do
    nna(k) = nc
    top = max(0, top - nc - 1)
    call push(k)
  end subroutine anb_trynode

  subroutine anb_child(ls, b, r)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b
    integer(int64), intent(out) :: r
    call anl_child(ls, b, r)
  end subroutine anb_child

  ! the host: N_CONST, or an error for a symbol marked so (defvar 3)
  recursive subroutine anb_host(ls, bs, x, b, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: b
    integer(int64), intent(out) :: r
    r = 0
    if (frm_kind(x) == 2) then
       if (fdefv(x%id) == 3) then
          r = 1
          return
       end if
    end if
    call push(mk(1, 0, 0, 0))
  end subroutine anb_host

  recursive subroutine anb_meta(ls, bs, x, b, r1, r2)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: b
    integer(int64), intent(out) :: r1, r2
    r1 = 0
    r2 = 0
    if (frf_meta(frf_nth(x, 1_int64)) == 0 .and. anf_def(x, 2_int64) == 0) return
    call push(mk(1, 0, 0, 0))
    r2 = 1
  end subroutine anb_meta

  recursive subroutine anb_sub(ls, bs, x, b, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: b
    integer(int64), intent(out) :: r
    call anb_an(ls, bs, x, b, r)
  end subroutine anb_sub

  ! the drivers' host reads, as scripts/fuzz-anbuild-gen attaches them in
  ! ACL2: a symbol's raw defvar (fd) and class (fc) fields decide
  integer function fd(x)
    type(gc_value), intent(in) :: x
    fd = 0
    if (frm_kind(x) == 2) fd = fdefv(x%id)
  end function fd
  integer function fc(x)
    type(gc_value), intent(in) :: x
    fc = 0
    if (frm_kind(x) == 2) fc = fclass(x%id)
  end function fc

  integer(int64) function anb_set_kind(x, b) result(k)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: b
    type(gc_value) :: t
    t = frf_nth(x, 1_int64)
    k = 3
    if (frf_kind(t) == 3) then
       k = 1
    else if (frm_kind(t) == 2) then
       k = 0
       if (fc(t) == 1) k = 2
       if (fd(t) == 3) k = 3
    end if
  end function anb_set_kind
  integer(int64) function anb_dot_kind(x, b) result(k)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: b
    type(gc_value) :: t
    t = frf_nth(x, 1_int64)
    k = 0
    if (frm_kind(t) == 2) then
       if (fc(t) == 1) k = 1
       if (fd(t) == 2) k = 2
       if (fd(t) == 3) k = 3
    end if
  end function anb_dot_kind
  integer(int64) function anb_new_kind(x) result(k)
    type(gc_value), intent(in) :: x
    k = 0
    if (fd(frf_nth(x, 1_int64)) == 2) k = 2
  end function anb_new_kind
  integer(int64) function anb_recur_open(x, b) result(k)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: b
    k = 0
    if (frf_len(x) > 3) k = 1
  end function anb_recur_open
  integer(int64) function anb_recur_check(x, b, n) result(k)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: b, n
    k = 0
    if (n == 2) k = 1
  end function anb_recur_check
  integer(int64) function anb_fn_open(x, r, self) result(k)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: r, self
    k = 0
  end function anb_fn_open
  integer(int64) function anb_method_open(m, r, mb, start, nreq, rest) result(k)
    type(gc_value), intent(in) :: m
    integer(int64), intent(in) :: r, mb, start, nreq, rest
    k = 0
    if (nreq == 2) k = 2
    if (nreq == 3) k = 1
  end function anb_method_open
  integer(int64) function anb_method_check(mb) result(k)
    integer(int64), intent(in) :: mb
    k = 0
  end function anb_method_check
  integer(int64) function anb_fn_check(x, r, n) result(k)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: r, n
    k = 0
    if (n == 3) k = 1
  end function anb_fn_check

  ! what the host analyses itself: N_CONST, as the attachment's
  recursive subroutine anb_host2(ls, bs, w, x, b, r)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    integer(int64), value :: w, b
    type(gc_value), value :: x
    integer(int64), intent(out) :: r
    r = 0
    call push(mk(1, 0, 0, 0))
  end subroutine anb_host2

  ! the drivers' nodes, as model/anbuild.lisp defines them
  subroutine anb_setnode(bs, x, n)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: n
    call node_of(24, merge(2, 0, n == 2), int(n), 0)
  end subroutine anb_setnode
  subroutine anb_dotnode(bs, x, k, n)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: k, n
    call node_of(21, 0, int(n), 0)
  end subroutine anb_dotnode
  subroutine anb_newnode(bs, x, n)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: n
    call node_of(22, 0, int(n), 0)
  end subroutine anb_newnode
  subroutine anb_recurnode(bs, x, b, n)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: b, n
    call node_of(16, int(n), int(n), 0)
  end subroutine anb_recurnode
  subroutine anb_arity(bs, m, mb, start, nreq, rest)
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: m
    integer(int64), value :: mb, start, nreq, rest
  end subroutine anb_arity
  subroutine anb_newfn(ls, b, r)
    type(anl_state), intent(inout) :: ls
    integer(int64), value :: b
    integer(int64), intent(out) :: r
    call anl_new_fn(ls, b, r)
  end subroutine anb_newfn
  ! a fn's node: its n bodies taken off (anb-ser writes kind 14 with none)
  subroutine anb_fnclose(ls, bs, x, r, n)
    type(anl_state), intent(inout) :: ls
    type(anb_state), intent(inout) :: bs
    type(gc_value), value :: x
    integer(int64), value :: r, n
    top = max(0, top - int(n))
    call push(mk(14, 0, 0, 0))
  end subroutine anb_fnclose
  function frf_norm(x) result(e)
    type(gc_value), intent(in) :: x
    type(gc_value) :: e
    e = x
  end function frf_norm

  integer(int64) function anb_loop_open(c, start, n)
    integer(int64), intent(in) :: c, start, n
    anb_loop_open = 0
  end function anb_loop_open
  integer(int64) function anb_let_kind(k, c, slot, loopp)
    type(gc_value), intent(in) :: k
    integer(int64), intent(in) :: c, slot, loopp
    anb_let_kind = 0
  end function anb_let_kind
  integer(int64) function anb_let_ret(c, ret)
    integer(int64), intent(in) :: c, ret
    anb_let_ret = 0
  end function anb_let_ret

  ! a node as anb-ser writes it: kind i2 nkids kids.. has-s3 [s3] nalts alts..; 0 for nil
  recursive subroutine ser(k)
    integer, intent(in) :: k
    integer :: i
    if (k == 0) then
       write(*, '(a)', advance='no') " 0"
       return
    end if
    if (nkind(k) == -1) then
       write(*, '(a,i0,a,i0)', advance='no') " -1 ", ni2(k), " ", 0
       call ser(ns3(k))
       return
    end if
    write(*, '(a,i0,a,i0,a,i0)', advance='no') " ", nkind(k), " ", ni2(k), " ", nnk(k)
    do i = 1, nnk(k)
       call ser(lists(nkid0(k) + i))
    end do
    if (ns3(k) /= 0) then
       write(*, '(a)', advance='no') " 1"
       call ser(ns3(k))
    else
       write(*, '(a)', advance='no') " 0"
    end if
    write(*, '(a,i0)', advance='no') " ", nna(k)
    do i = 1, nna(k)
       call ser(lists(nalt0(k) + i))
    end do
  end subroutine ser

  include "anlocal_gen.inc"
  include "anform_gen.inc"
  include "anbuild_gen.inc"
end module anbuild_mock

program anbuild_check
  use iso_fortran_env, only: int64
  use anbuild_mock
  implicit none
  character(len=4096) :: path, arg
  integer :: u, nfm, root, i, cnt, vals(80), tk
  integer(int64) :: e, r
  type(gc_value) :: x
  type(anl_state) :: ls
  type(anb_state) :: bs
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = (trim(arg) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) nfm, root
  allocate(fkind(nfm), fsid(nfm), fqual(nfm), fword(nfm), fclass(nfm), fdefv(nfm), fsp(nfm), fmeta(nfm), fn(nfm), &
       foff(nfm), fkids(nfm * 70 + 1))
  tk = 1
  do i = 1, nfm
     read(u, *) cnt, vals(1:cnt)
     fkind(i) = vals(1)
     fsid(i) = vals(2)
     fqual(i) = vals(3)
     fword(i) = vals(4)
     fclass(i) = vals(5)
     fdefv(i) = vals(6)
     fsp(i) = vals(7)
     fmeta(i) = vals(8)
     fn(i) = vals(9)
     foff(i) = tk
     fkids(tk:tk + fn(i) - 1) = vals(10:9 + fn(i))
     tk = tk + fn(i)
  end do
  close(u)
  ! the arrays made at first use, as analyze.inc's anl_ls makes them
  call rt_resize_int(ls%fctr, 64_int64); call rt_resize_int(ls%fout, 64_int64); call rt_resize_int(ls%fcap, 64_int64)
  call rt_resize_int(ls%fvar, 64_int64); call rt_resize_int(ls%fah, 64_int64); call rt_resize_int(ls%fnl, 64_int64)
  call rt_resize_int(ls%bpar, 64_int64); call rt_resize_int(ls%bfn, 64_int64); call rt_resize_int(ls%bhead, 64_int64)
  call rt_resize_int(ls%xnm, 64_int64); call rt_resize_int(ls%xsl, 64_int64); call rt_resize_int(ls%xblk, 64_int64)
  call rt_resize_int(ls%xnext, 64_int64); call rt_resize_int(ls%cnm, 64_int64); call rt_resize_int(ls%cout, 64_int64)
  call rt_resize_int(ls%cin, 64_int64); call rt_resize_int(ls%cbx, 64_int64); call rt_resize_int(ls%cnext, 64_int64)
  call rt_resize_int(ls%nsl, 64_int64); call rt_resize_int(ls%nnm, 64_int64); call rt_resize_int(ls%nnext, 64_int64)
  call rt_resize_int(ls%an, 64_int64); call rt_resize_int(ls%anext, 64_int64); call rt_resize_int(ls%ev, 64_int64)
  call rt_resize_int(ls%es, 64_int64)
  call anl_new_fn(ls, -1_int64, r)
  x%id = root
  x%off = 0
  call anb_an(ls, bs, x, r, e)
  write(*, '(i0,7(a,i0))', advance='no') e, " ", ls%nf, " ", ls%nb, " ", ls%nx, " ", ls%nc, " ", ls%na, " ", ls%nn, " ", top
  if (e == 0) then
     do i = 1, top
        call ser(stk(i))
     end do
  end if
  write(*, '(a)') ""
end program anbuild_check
