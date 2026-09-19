! ChemSolBind: the ChemSol library (src/f/chemsol, vendored, unmodified)
! reached from clotran.
!
! The shape NOTES.md asked for: a clotran MAP in, unpacked to the
! positional arguments the routine declares, the unmodified routine
! called, the outputs repacked into a map. The unpacking and repacking
! is Eval.f90's job (it knows maps); this module knows the routines and
! the array registry, and nothing else. `cs_args` is the one record
! that crosses between the two, one field per argument of readopt,
! dg_ld and solvout, named as the routines name them.
!
! Arrays cross by POINTER into the registry buffer -- contiguous, so
! `xw(3,*)` and `q(*)` see the bytes a clotran `real8` array owns, and
! what the routine writes into `rpi`, `pcenter`, `vdwc6`, `rp` and
! `iacw` is visible to clotran afterwards. Nothing is copied.
!
! What the library keeps for itself: `readopt` reads unit 44, so the
! binding opens vdw.par on 44 around the call; `solvout` writes unit 6
! and appends to cs.arc on 43, as the original program's did.
module ChemSolBind
  use GC
  use NativeArray
  use chemsol, only: entropy, readopt, dg_ld, solvout
  implicit none
  private
  integer, parameter :: dp = gc_dp

  type, public :: cs_args
     ! scalars, by the routines' names
     integer :: iterld = 0, ndxp = 0, iprint = 0, n_reg1 = 0, itl = 399
     real(dp) :: clgvn = 0, slgvn = 0, tds0 = 0, vdwsl = 0, phobsl = 0
     real(dp) :: ephil1 = 0, ephil2 = 0, rzcut = 0, rg_reg1 = 0, rg = 0
     real(dp) :: rg_inner = 0, rgim = 0, drg = 0, drg_inner = 0, rdcutl = 0, out_cut = 0
     ! dg_ld's results
     real(dp) :: evqdq = 0, elgwa = 0, evdw = 0, elgvn = 0, ephob = 0, etds = 0, ebw = 0
     ! arrays, as registry handles: real8 unless said otherwise
     integer :: vdwc6 = 0, dxp0 = 0, rp = 0, rpi = 0, pcenter = 0
     integer :: xw = 0, q = 0, q_gas = 0, q_mp2 = 0
     integer :: iacw = 0            ! int4
     logical :: do_gas = .false.
     character(len=13) :: molname = ""
     character(len=4) :: ssname = ""
     ! readopt reads the END of the .cs input itself (an optional `rp`
     ! block) from unit 45, positioned where main.f90's reads left it:
     ! the path, and how many lines the caller has already consumed.
     character(len=256) :: input_file = ""
     integer :: input_skip = 0
  end type cs_args

  public :: csb_entropy, csb_readopt, csb_dg_ld, csb_solvout

contains

  real(dp) function csb_entropy(mass)
    real(dp), intent(in) :: mass
    csb_entropy = entropy(mass)
  end function csb_entropy

  ! readopt: vdw.par on unit 44, the input on unit 45 positioned past
  ! the lines the caller read, the routine, both units closed.
  subroutine csb_readopt(a, vdw_path, err)
    type(cs_args), intent(inout) :: a
    character(len=*), intent(in) :: vdw_path
    character(len=:), allocatable, intent(out) :: err
    real(dp), pointer, contiguous :: vdwc6(:), dxp0(:), rp(:), rpi(:), pcenter(:), xw(:), q(:), q_gas(:)
    integer, pointer, contiguous :: iacw(:)
    integer :: ios

    err = ""
    if (.not. (r8(a%vdwc6, vdwc6) .and. r8(a%dxp0, dxp0) .and. r8(a%rp, rp) .and. r8(a%rpi, rpi) &
         .and. r8(a%pcenter, pcenter) .and. r8(a%xw, xw) .and. r8(a%q, q) .and. r8(a%q_gas, q_gas) &
         .and. i4(a%iacw, iacw))) then
       err = "readopt: an array argument is missing or not the right kind"
       return
    end if
    open(44, file=vdw_path, status="old", action="read", iostat=ios)
    if (ios /= 0) then
       err = "readopt: cannot open " // vdw_path
       return
    end if
    open(45, file=trim(a%input_file), status="old", action="read", iostat=ios)
    if (ios /= 0) then
       close(44)
       err = "readopt: cannot open " // trim(a%input_file)
       return
    end if
    block
      integer :: i
      character(len=1) :: dummy
      do i = 1, a%input_skip
         read(45, '(a)', iostat=ios) dummy
         if (ios /= 0) exit
      end do
    end block
    call readopt(a%iterld, vdwc6, dxp0, a%clgvn, a%slgvn, a%tds0, rp, a%vdwsl, a%phobsl, &
         a%ephil1, a%ephil2, a%rzcut, rpi, pcenter, a%rg_reg1, a%rg, a%rg_inner, a%rgim, &
         a%ndxp, iacw, xw, q, q_gas, a%n_reg1, a%drg, a%iprint)
    close(45)
    close(44)
  end subroutine csb_readopt

  ! dg_ld: the calculation. `atom` is character(8) per atom, built by
  ! the caller from the clotran strings; ChemSol reads it for printing.
  subroutine csb_dg_ld(a, atom, err)
    type(cs_args), intent(inout) :: a
    character(len=8), intent(in) :: atom(:)
    character(len=:), allocatable, intent(out) :: err
    real(dp), pointer, contiguous :: vdwc6(:), dxp0(:), rpi(:), pcenter(:), xw(:), q(:), q_gas(:), q_mp2(:)
    integer, pointer, contiguous :: iacw(:)

    err = ""
    if (.not. (r8(a%vdwc6, vdwc6) .and. r8(a%dxp0, dxp0) .and. r8(a%rpi, rpi) &
         .and. r8(a%pcenter, pcenter) .and. r8(a%xw, xw) .and. r8(a%q, q) .and. r8(a%q_gas, q_gas) &
         .and. r8(a%q_mp2, q_mp2) .and. i4(a%iacw, iacw))) then
       err = "dg-ld: an array argument is missing or not the right kind"
       return
    end if
    if (size(atom) < a%n_reg1) then
       err = "dg-ld: fewer atom names than atoms"
       return
    end if
    call dg_ld(a%iterld, a%iprint, a%evqdq, a%elgwa, a%evdw, a%elgvn, a%ephob, a%etds, a%ebw, &
         a%clgvn, dxp0, a%ephil1, a%ephil2, iacw, a%ndxp, pcenter, a%phobsl, q, q_gas, q_mp2, &
         a%rg, a%rg_inner, a%rg_reg1, a%rgim, rpi, a%rzcut, a%slgvn, a%tds0, vdwc6, a%vdwsl, &
         xw, atom, a%n_reg1, a%drg, a%drg_inner, a%rdcutl, a%out_cut, a%itl)
  end subroutine csb_dg_ld

  subroutine csb_solvout(a)
    type(cs_args), intent(in) :: a
    call solvout(a%iterld, a%iprint, a%do_gas, a%evqdq, a%elgwa, a%etds, a%evdw, a%ebw, &
         a%elgvn, a%ephob, a%molname, a%ssname)
  end subroutine csb_solvout

  ! The two shapes an argument takes: a real8 buffer, an int4 buffer.
  logical function r8(h, p)
    integer, intent(in) :: h
    real(dp), pointer, contiguous, intent(out) :: p(:)
    call gcna_real8_ptr(h, p, r8)
  end function r8

  logical function i4(h, p)
    integer, intent(in) :: h
    integer, pointer, contiguous, intent(out) :: p(:)
    call gcna_int4_ptr(h, p, i4)
  end function i4

end module ChemSolBind
