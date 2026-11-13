! vmtr_check: runs the GENERATED translation (vm_tr_gen.inc, from
! model/vmtrg.lisp) on trees read from a file, through mock reads and
! shims that are model/vmtrg.lisp's exactly -- the scope a list of slots
! (blank -1), vtg_blank blanking what exec-vmtr's ex-clr says the node may
! clear, vtg_restore giving back the saved scope, vtg_local ex-pos, the
! output stack strings -- and vtg_other ex-tr's of every other kind the
! cases hold (a Var, kind 3: (:const c); anything else, (:const nil)).
! scripts/fuzz-vmtr-gen writes the cases and compares the answers with
! ACL2's ex-tr. With the argument `broken`, a node's items are taken in
! the wrong order on purpose: the negative control.
!
!   vmtr_check CASEFILE [broken]
!
! CASEFILE: per case a line `nnodes ncm cm..`, then a line a node, 1..nnodes,
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
  end type vtg_state
  integer, allocatable :: nkind(:), ni2(:), ns2(:), nc(:), nmark(:), nnk(:), noff(:), kids(:)
  logical :: broken = .false.
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
  end function vtg_nk
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
    call push(tb, '(:local ' // itoa(int(j - 1, int64)) // ')')
  end subroutine vtg_local
  subroutine vtg_node(tb, op, n)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: op, n
    character(len=:), allocatable :: s
    integer :: j
    select case (op)
    case (1); s = '(:if'
    case (2); s = '(:let'
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
    call push(tb, s // ')')
  end subroutine vtg_node
  subroutine vtg_bind(tb, s)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s
    tb%cm = [tb%cm, s]
  end subroutine vtg_bind
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
    case (11)
       m = ni2(x%id)
    case (17)
       m = 0
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
    if (vtg_kind(x) == 3) then
       call push(tb, cstr(x))
    else
       call push(tb, '(:const nil)')
    end if
  end subroutine vtg_other

  include 'vm_tr_gen.inc'
end module vmtr_mock

program vmtr_check
  use vmtr_mock
  implicit none
  character(len=4096) :: arg
  integer :: u, ios, nn, ncm, j, k, nk, tot
  integer, allocatable :: row(:)
  type(vtg_state) :: tb
  type(gc_value) :: root
  call get_command_argument(1, arg)
  if (command_argument_count() > 1) then
     call get_command_argument(2, arg(2048:))
     broken = trim(arg(2048:)) == 'broken'
  end if
  open (newunit=u, file=trim(arg(1:2047)), status='old', action='read')
  allocate (row(4096))
  do
     read (u, *, iostat=ios) nn, ncm
     if (ios /= 0) exit
     backspace (u)
     allocate (tb%cm(ncm))
     read (u, *) nn, ncm, tb%cm
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
     call vtg_tr(tb, 0_int64, root, 0_int64)
     write (*, '(a)') tb%stk(tb%top)%s
     deallocate (nkind, ni2, ns2, nc, nmark, nnk, noff, kids, tb%stk, tb%sv, tb%cm)
  end do
end program vmtr_check
