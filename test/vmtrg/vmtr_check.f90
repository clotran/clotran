! vmtr_check: runs the GENERATED translation (vm_tr_gen.inc, from
! model/vmtrg.lisp) on trees read from a file, through mock reads and
! shims that are model/vmtrg.lisp's exactly -- the scope a list of slots
! (blank -1), vtg_blank blanking what exec-vmtr's ex-clr says the node may
! clear, vtg_restore giving back the saved scope, vtg_local ex-pos, the
! output stack strings -- and vtg_other ex-tr's of every other kind the
! cases hold, (:const nil).
! scripts/fuzz-vmtr-gen writes the cases and compares the answers with
! ACL2's ex-tr. With the argument `broken`, a node's items are taken in
! the wrong order on purpose: the negative control. With `tlr` it prints
! vtg_tlr of the root instead (t or nil), against ACL2's ex-tlr. With
! `clause` vtg_clause of an arity whose body is the root (a line `nf var
! start sl` after the case's first; its scope ex-fbcm, or at sl 0
! ex-fbcm0), against ex-clause (at sl 0 ex-clause0);
! with `arcl` vtg_arcl of the root's constant, against ex-arcl.
!
!   vmtr_check CASEFILE [tlr|clause|arcl] [broken]
!
! CASEFILE: per case a line `nnodes np m ncm cm..` (np, m vtb-cs: the
! clause's parameters and captures, a capture read in place), then a line a node, 1..nnodes,
! node 1 the root: kind i2 s2 c mark nk kid.. (c -1 nil; a kid 0 nil).
! Out: a line a case, the translation as ACL2 prints it.
module vmtr_mock
  use iso_fortran_env, only: int64
  implicit none
  type :: gc_value
     integer :: id = 0
  end type gc_value
  type :: str
     character(len=:), allocatable :: s
  end type str
  type :: ivec
     integer(int64), allocatable :: v(:)
  end type ivec
  type :: vtg_state
     type(str), allocatable :: stk(:)
     integer :: top = 0
     integer(int64), allocatable :: cm(:)
     type(ivec), allocatable :: sv(:)
     integer :: nsv = 0
     integer(int64) :: np = 0, m = 0
  end type vtg_state
  integer, allocatable :: nkind(:), ni2(:), ns2(:), nc(:), nmark(:), nnk(:), noff(:), kids(:)
  logical :: broken = .false., tlr = .false., clause = .false., arcl = .false.
contains
  logical function ok(x)
    type(gc_value), intent(in) :: x
    ok = x%id >= 1 .and. x%id <= size(nkind)
  end function ok
  integer(int64) function vtg_kind(x)
    type(gc_value), intent(in) :: x
    vtg_kind = 0
    if (ok(x)) vtg_kind = nkind(x%id)
  end function vtg_kind
  integer(int64) function vtg_i2(x)
    type(gc_value), intent(in) :: x
    vtg_i2 = 0
    if (ok(x)) vtg_i2 = ni2(x%id)
  end function vtg_i2
  integer(int64) function vtg_s2(x)
    type(gc_value), intent(in) :: x
    vtg_s2 = 0
    if (ok(x)) vtg_s2 = ns2(x%id)
  end function vtg_s2
  integer(int64) function vtg_nk(x)
    type(gc_value), intent(in) :: x
    vtg_nk = 0
    if (ok(x)) vtg_nk = nnk(x%id)
    if (vtg_kind(x) == 19) vtg_nk = min(vtg_nk, 2_int64)
  end function vtg_nk
  ! a case (kind 19): its row's kids the test, the default, then each
  ! entry's then; entry j's test 50 + j (the fuzzer writes ACL2's so)
  integer(int64) function vtg_ncs(x)
    type(gc_value), intent(in) :: x
    vtg_ncs = 0
    if (vtg_kind(x) == 19) vtg_ncs = max(0, nnk(x%id) - 2)
  end function vtg_ncs
  function vtg_cthen(x, j) result(k)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: j
    type(gc_value) :: k
    k%id = 0
    if (j >= 0 .and. j < vtg_ncs(x)) k = vtg_kid(x, j + 2)
  end function vtg_cthen
  subroutine vtg_cstest(tb, x, j)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: x
    integer(int64), value :: j
    call push(tb, ':case')
    call push(tb, '(:const ' // itoa(50 + j) // ')')
  end subroutine vtg_cstest
  function vtg_kid(x, j) result(k)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: j
    type(gc_value) :: k
    k%id = 0
    if (ok(x)) then
       if (j >= 0 .and. j < nnk(x%id)) k%id = kids(noff(x%id) + int(j))
    end if
  end function vtg_kid
  ! a constant: its node, read back by vtg_const
  function vtg_c(x) result(v)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    v = x
  end function vtg_c
  function itoa(n) result(s)
    integer(int64), intent(in) :: n
    character(len=:), allocatable :: s
    character(len=24) :: b
    write (b, '(i0)') n
    s = trim(b)
  end function itoa
  subroutine push(tb, s)
    type(vtg_state), intent(inout) :: tb
    character(len=*), intent(in) :: s
    type(str), allocatable :: t(:)
    if (tb%top >= size(tb%stk)) then
       allocate (t(2 * size(tb%stk)))
       t(1:tb%top) = tb%stk(1:tb%top)
       call move_alloc(t, tb%stk)
    end if
    tb%top = tb%top + 1
    tb%stk(tb%top)%s = s
  end subroutine push
  function cstr(x) result(s)
    type(gc_value), intent(in) :: x
    character(len=:), allocatable :: s
    s = '(:const nil)'
    if (ok(x)) then
       if (nc(x%id) >= 0) s = '(:const ' // itoa(int(nc(x%id), int64)) // ')'
    end if
  end function cstr
  subroutine vtg_const(tb, v)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: v
    call push(tb, cstr(v))
  end subroutine vtg_const
  subroutine vtg_deref(tb, x)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: x
    call push(tb, '(:prim :clotran.vm/deref ' // cstr(vtg_c(x)) // ')')
  end subroutine vtg_deref
  ! a call whose head is read at translation (the fuzzer's ACL2 side attaches
  ! prim so that :clotran.vm/builtin says so of a constant of 100 or more, and
  ! :clotran.vm/wraps of a Var's v of 200 or more at n arguments answers
  ! 1000 + v + n): 1 a constant builtin, 2 a direct-linked (i2 1) Var
  ! wrapping one, 3 any other Var wrapping one; vtg_hd the builtin's
  ! number, or :clotran.vm/callw and the Var's constant; 4 a constant or Var
  ! of 300 or more (prim :ifn says an IFn of those): (:callv head args..)
  integer(int64) function vtg_pk(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: h
    h = vtg_kid(x, 0_int64)
    vtg_pk = 0
    if (.not. ok(h)) return
    if (nkind(h%id) == 1 .and. nc(h%id) >= 100 .and. nc(h%id) < 200) vtg_pk = 1
    if (nkind(h%id) == 3 .and. nc(h%id) >= 200 .and. nc(h%id) < 300) vtg_pk = 3
    if (nkind(h%id) == 3 .and. ni2(h%id) == 1 .and. nc(h%id) >= 200 .and. nc(h%id) < 300) vtg_pk = 2
    if ((nkind(h%id) == 1 .or. nkind(h%id) == 3) .and. nc(h%id) >= 300) vtg_pk = 4
  end function vtg_pk
  subroutine vtg_hd(tb, x)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: x
    type(gc_value) :: h
    h = vtg_kid(x, 0_int64)
    if (vtg_pk(x) == 4) then
       if (nkind(h%id) == 1) then
          call push(tb, cstr(h))
       else
          call push(tb, '(:prim :clotran.vm/deref ' // cstr(h) // ')')
       end if
    else if (vtg_pk(x) == 2) then
       call push(tb, itoa(int(1000 + nc(h%id) + nnk(x%id) - 1, int64)))
    else if (vtg_pk(x) == 3) then
       call push(tb, ':clotran.vm/callw')
       call push(tb, cstr(h))
    else
       call push(tb, itoa(int(nc(h%id), int64)))
    end if
  end subroutine vtg_hd
  subroutine vtg_nil(tb)
    type(vtg_state), intent(inout) :: tb
    call push(tb, '(:const nil)')
  end subroutine vtg_nil
  ! ex-pos: the first position holding s, else the scope's length
  subroutine vtg_local(tb, s)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s
    integer :: j
    do j = 1, size(tb%cm)
       if (tb%cm(j) == s) exit
    end do
    call push(tb, cloc(tb, int(j - 1, int64)))
  end subroutine vtg_local
  ! ex-cloc: below np a local, then the captures, past them m lower
  function cloc(tb, p0) result(r)
    type(vtg_state), intent(in) :: tb
    integer(int64), intent(in) :: p0
    character(len=:), allocatable :: r
    integer(int64) :: p
    p = max(0_int64, p0)
    if (p < tb%np) then
       r = '(:local ' // itoa(p) // ')'
    else if (p < tb%np + tb%m) then
       r = '(:capt ' // itoa(p - tb%np) // ')'
    else
       r = '(:local ' // itoa(p - tb%m) // ')'
    end if
  end function cloc
  ! ex-trcall's parts: the scope's last position read, its cast, the refusal
  subroutine vtg_top(tb)
    type(vtg_state), intent(inout) :: tb
    call push(tb, cloc(tb, int(size(tb%cm) - 1, int64)))
  end subroutine vtg_top
  subroutine vtg_cast(tb)
    type(vtg_state), intent(inout) :: tb
    call push(tb, '(:prim :ifn ' // cloc(tb, int(size(tb%cm) - 1, int64)) // ')')
  end subroutine vtg_cast
  subroutine vtg_notfn(tb)
    type(vtg_state), intent(inout) :: tb
    call push(tb, '(:throw (:const :not-fn))')
  end subroutine vtg_notfn
  subroutine vtg_node(tb, op, n)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: op, n
    character(len=:), allocatable :: s
    integer :: j
    select case (op)
    case (0); s = '('
    case (1); s = '(:if'
    case (2); s = '(:let'
    case (4); s = '(:loop'
    case (5); s = '(:recur'
    case (6); s = '(:prim'
    case (7); s = '(:callv'
    case (8); s = '(:applyv'
    case default; s = '(:throw'
    end select
    if (broken) then
       do j = tb%top, tb%top - int(n) + 1, -1
          s = s // ' ' // tb%stk(j)%s
       end do
    else
       do j = tb%top - int(n) + 1, tb%top
          s = s // ' ' // tb%stk(j)%s
       end do
    end if
    tb%top = tb%top - int(n)
    if (op == 0 .and. n == 0) then
       call push(tb, 'nil')
    else if (op == 0) then
       call push(tb, '(' // s(3:) // ')')
    else
       call push(tb, s // ')')
    end if
  end subroutine vtg_node
  subroutine vtg_bind(tb, s)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s
    tb%cm = [tb%cm, s]
  end subroutine vtg_bind
  ! vmtrg's vtg-binds: the loop's slots blanked, then each a new position
  subroutine vtg_binds(tb, s, n)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s, n
    integer(int64) :: j
    do j = 1, size(tb%cm)
       if (tb%cm(j) >= s .and. tb%cm(j) < s + n) tb%cm(j) = -1
    end do
    do j = 0, n - 1
       tb%cm = [tb%cm, s + j]
    end do
  end subroutine vtg_binds
  ! no fn in the cases: no capture
  logical function vtg_rdcap(x, lo, hi)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: lo, hi
    vtg_rdcap = .false.
  end function vtg_rdcap
  subroutine vtg_dead(tb)
    type(vtg_state), intent(inout) :: tb
    tb%cm = [tb%cm, -1_int64]
  end subroutine vtg_dead
  ! exec-vmtr's ex-clr :m: the slots of x's marked reads, for these kinds
  recursive subroutine clr(x, l)
    type(gc_value), intent(in) :: x
    integer(int64), allocatable, intent(inout) :: l(:)
    integer(int64) :: j, m
    if (.not. ok(x)) return
    select case (nkind(x%id))
    case (2)
       if (nmark(x%id) /= 0) l = [l, int(ni2(x%id), int64)]
    case (4)
       m = 2
    case (5)
       m = nnk(x%id) - 1
    case (11, 12)
       m = ni2(x%id)
    case (16)
       m = nnk(x%id) - 1
    case (6)
       m = nnk(x%id) - 1
    case (17)
       m = 0
    case (19)
       m = nnk(x%id) - 1
    case default
       return
    end select
    if (nkind(x%id) == 2) return
    do j = 0, m
       call clr(vtg_kid(x, j), l)
    end do
  end subroutine clr
  subroutine vtg_blank(tb, x)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: x
    integer(int64), allocatable :: l(:)
    integer :: j
    allocate (l(0))
    call clr(x, l)
    do j = 1, size(tb%cm)
       if (any(l == tb%cm(j))) tb%cm(j) = -1
    end do
  end subroutine vtg_blank
  subroutine vtg_save(tb)
    type(vtg_state), intent(inout) :: tb
    type(ivec), allocatable :: t(:)
    if (tb%nsv >= size(tb%sv)) then
       allocate (t(2 * size(tb%sv)))
       t(1:tb%nsv) = tb%sv(1:tb%nsv)
       call move_alloc(t, tb%sv)
    end if
    tb%nsv = tb%nsv + 1
    tb%sv(tb%nsv)%v = tb%cm
  end subroutine vtg_save
  subroutine vtg_restore(tb)
    type(vtg_state), intent(inout) :: tb
    if (tb%nsv <= 0) then
       deallocate (tb%cm)
       allocate (tb%cm(0))
       return
    end if
    tb%cm = tb%sv(tb%nsv)%v
    tb%nsv = tb%nsv - 1
  end subroutine vtg_restore
  ! every other kind: ex-tr's (a Var its value, anything else nil)
  recursive subroutine vtg_other(tb, x)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: x
    call push(tb, '(:const nil)')
  end subroutine vtg_other

  ! vmtrcl's: a number, a keyword, the self let's value (:mkclo tm (:capt 0) ..),
  ! the template printed `tm` (the fuzzer writes ACL2's so)
  subroutine vtg_num(tb, n)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: n
    call push(tb, itoa(n))
  end subroutine vtg_num
  subroutine vtg_key(tb, j)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: j
    select case (j)
    case (0); call push(tb, ':rest')
    case (1); call push(tb, ':clotran.vm/arity')
    case (2); call push(tb, ':prim')
    case default; call push(tb, ':local')
    end select
  end subroutine vtg_key
  subroutine vtg_self(tb, tm, m)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: tm
    integer(int64), value :: m
    character(len=:), allocatable :: s
    integer(int64) :: j
    s = '(:mkclo tm'
    do j = 0, m - 1
       s = s // ' (:capt ' // itoa(j) // ')'
    end do
    call push(tb, s // ')')
  end subroutine vtg_self
  include 'vm_tr_gen.inc'
end module vmtr_mock

program vmtr_check
  use vmtr_mock
  implicit none
  character(len=4096) :: arg
  integer :: u, ios, nn, ncm, j, k, nk, tot
  integer(int64) :: nf, var, st, sl
  integer, allocatable :: row(:)
  type(vtg_state) :: tb
  type(gc_value) :: root
  call get_command_argument(1, arg)
  do j = 2, command_argument_count()
     call get_command_argument(j, arg(2048:))
     if (trim(arg(2048:)) == 'broken') broken = .true.
     if (trim(arg(2048:)) == 'tlr') tlr = .true.
     if (trim(arg(2048:)) == 'clause') clause = .true.
     if (trim(arg(2048:)) == 'arcl') arcl = .true.
  end do
  open (newunit=u, file=trim(arg(1:2047)), status='old', action='read')
  allocate (row(4096))
  do
     read (u, *, iostat=ios) nn, tb%np, tb%m, ncm
     if (ios /= 0) exit
     backspace (u)
     allocate (tb%cm(ncm))
     read (u, *) nn, tb%np, tb%m, ncm, tb%cm
     if (clause) read (u, *) nf, var, st, sl
     allocate (nkind(nn), ni2(nn), ns2(nn), nc(nn), nmark(nn), nnk(nn), noff(nn), kids(64 * nn + 64))
     tot = 1
     do j = 1, nn
        read (u, *) row(1:6)
        nk = row(6)
        backspace (u)
        read (u, *) row(1:6 + nk)
        nkind(j) = row(1); ni2(j) = row(2); ns2(j) = row(3); nc(j) = row(4); nmark(j) = row(5); nnk(j) = nk
        noff(j) = tot
        do k = 1, nk
           kids(tot) = row(6 + k)
           tot = tot + 1
        end do
     end do
     allocate (tb%stk(16), tb%sv(16))
     tb%top = 0
     tb%nsv = 0
     root%id = 1
     if (clause) then
        call vtg_clause(tb, nf, var, st, root, root, sl, tb%m)
        write (*, '(a)') tb%stk(tb%top)%s
     else if (arcl) then
        call vtg_arcl(tb, root)
        write (*, '(a)') tb%stk(tb%top)%s
     else if (tlr) then
        if (vtg_tlr(root)) then
           write (*, '(a)') 't'
        else
           write (*, '(a)') 'nil'
        end if
     else
        call vtg_tr(tb, 0_int64, root, 0_int64)
        write (*, '(a)') tb%stk(tb%top)%s
     end if
     deallocate (nkind, ni2, ns2, nc, nmark, nnk, noff, kids, tb%stk, tb%sv, tb%cm)
  end do
end program vmtr_check
