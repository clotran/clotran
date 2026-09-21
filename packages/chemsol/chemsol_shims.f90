! The ChemSol package: the library (src/f/chemsol, vendored, unmodified)
! behind the door (src/f/DynLoad.f90). This file is what
! scripts/bind-fortran will write for a library once it exists: a
! manifest naming each routine's arguments with type, intent and rank,
! and one shim per routine that unpacks argc C pointers to the routine's
! own positional arguments. The three things a generator could not know
! are here too: readopt reads vdw.par on unit 44 and the rest of its
! input on unit 45, so its shim takes the two paths and a line count;
! dg_ld takes atom names as character(8), so its shim takes them as one
! string of 8-character fields; solvout writes unit 6 and cs.arc on 43,
! as the original program did.
!
! Scalars arrive as C pointers to values of their C type, arrays as a
! pointer into clotran's buffer followed by one int4 per extent, strings
! null-terminated. The manifest names the argument :name the map API
! (chemsol.cljf) uses, with hyphens, and the :symbol the shim exports.
module chemsol_pkg
  use iso_c_binding
  use chemsol, only: entropy, readopt, dg_ld, solvout
  implicit none
  character(kind=c_char, len=*), parameter :: manifest = &
       '{:package "chemsol.raw" :routines [' // &
       '{:name "entropy" :symbol "cs_entropy_shim" :args [{:name "mass" :type :real8 :intent :in :rank 0}] :returns :real8}' // &
       ' {:name "readopt" :symbol "cs_readopt_shim" :args [' // &
       '{:name "iterld" :type :int4 :intent :inout :rank 0} {:name "vdwc6" :type :real8 :intent :inout :rank 1}' // &
       ' {:name "dxp0" :type :real8 :intent :inout :rank 1} {:name "clgvn" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "slgvn" :type :real8 :intent :inout :rank 0} {:name "tds0" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "rp" :type :real8 :intent :inout :rank 1} {:name "vdwsl" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "phobsl" :type :real8 :intent :inout :rank 0} {:name "ephil1" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "ephil2" :type :real8 :intent :inout :rank 0} {:name "rzcut" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "rpi" :type :real8 :intent :inout :rank 1} {:name "pcenter" :type :real8 :intent :inout :rank 1}' // &
       ' {:name "rg-reg1" :type :real8 :intent :inout :rank 0} {:name "rg" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "rg-inner" :type :real8 :intent :inout :rank 0} {:name "rgim" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "ndxp" :type :int4 :intent :inout :rank 0} {:name "iacw" :type :int4 :intent :inout :rank 1}' // &
       ' {:name "xw" :type :real8 :intent :in :rank 2} {:name "q" :type :real8 :intent :in :rank 1}' // &
       ' {:name "q-gas" :type :real8 :intent :in :rank 1} {:name "n-reg1" :type :int4 :intent :in :rank 0}' // &
       ' {:name "drg" :type :real8 :intent :in :rank 0} {:name "iprint" :type :int4 :intent :in :rank 0}' // &
       ' {:name "vdw-path" :type :string :intent :in :rank 0} {:name "input-file" :type :string :intent :in :rank 0}' // &
       ' {:name "input-skip" :type :int4 :intent :in :rank 0}]}' // &
       ' {:name "dg-ld" :symbol "cs_dg_ld_shim" :args [' // &
       '{:name "iterld" :type :int4 :intent :in :rank 0} {:name "iprint" :type :int4 :intent :in :rank 0}' // &
       ' {:name "evqdq" :type :real8 :intent :inout :rank 0} {:name "elgwa" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "evdw" :type :real8 :intent :inout :rank 0} {:name "elgvn" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "ephob" :type :real8 :intent :inout :rank 0} {:name "etds" :type :real8 :intent :inout :rank 0}' // &
       ' {:name "ebw" :type :real8 :intent :inout :rank 0} {:name "clgvn" :type :real8 :intent :in :rank 0}' // &
       ' {:name "dxp0" :type :real8 :intent :in :rank 1} {:name "ephil1" :type :real8 :intent :in :rank 0}' // &
       ' {:name "ephil2" :type :real8 :intent :in :rank 0} {:name "iacw" :type :int4 :intent :in :rank 1}' // &
       ' {:name "ndxp" :type :int4 :intent :in :rank 0} {:name "pcenter" :type :real8 :intent :in :rank 1}' // &
       ' {:name "phobsl" :type :real8 :intent :in :rank 0} {:name "q" :type :real8 :intent :in :rank 1}' // &
       ' {:name "q-gas" :type :real8 :intent :in :rank 1} {:name "q-mp2" :type :real8 :intent :in :rank 1}' // &
       ' {:name "rg" :type :real8 :intent :in :rank 0} {:name "rg-inner" :type :real8 :intent :in :rank 0}' // &
       ' {:name "rg-reg1" :type :real8 :intent :in :rank 0} {:name "rgim" :type :real8 :intent :in :rank 0}' // &
       ' {:name "rpi" :type :real8 :intent :in :rank 1} {:name "rzcut" :type :real8 :intent :in :rank 0}' // &
       ' {:name "slgvn" :type :real8 :intent :in :rank 0} {:name "tds0" :type :real8 :intent :in :rank 0}' // &
       ' {:name "vdwc6" :type :real8 :intent :in :rank 1} {:name "vdwsl" :type :real8 :intent :in :rank 0}' // &
       ' {:name "xw" :type :real8 :intent :in :rank 2} {:name "atoms" :type :string :intent :in :rank 0}' // &
       ' {:name "n-reg1" :type :int4 :intent :in :rank 0} {:name "drg" :type :real8 :intent :in :rank 0}' // &
       ' {:name "drg-inner" :type :real8 :intent :in :rank 0} {:name "rdcutl" :type :real8 :intent :in :rank 0}' // &
       ' {:name "out-cut" :type :real8 :intent :in :rank 0} {:name "itl" :type :int4 :intent :in :rank 0}]}' // &
       ' {:name "solvout" :symbol "cs_solvout_shim" :args [' // &
       '{:name "iterld" :type :int4 :intent :in :rank 0} {:name "iprint" :type :int4 :intent :in :rank 0}' // &
       ' {:name "do-gas" :type :logical :intent :in :rank 0} {:name "evqdq" :type :real8 :intent :in :rank 0}' // &
       ' {:name "elgwa" :type :real8 :intent :in :rank 0} {:name "etds" :type :real8 :intent :in :rank 0}' // &
       ' {:name "evdw" :type :real8 :intent :in :rank 0} {:name "ebw" :type :real8 :intent :in :rank 0}' // &
       ' {:name "elgvn" :type :real8 :intent :in :rank 0} {:name "ephob" :type :real8 :intent :in :rank 0}' // &
       ' {:name "molname" :type :string :intent :in :rank 0} {:name "ssname" :type :string :intent :in :rank 0}]}]}' // &
       c_null_char
  character(kind=c_char), target, save :: manifest_buf(len(manifest)) = transfer(manifest, [c_char_'a'], len(manifest))
contains
  function clotran_manifest() bind(C, name="clotran_manifest") result(p)
    type(c_ptr) :: p
    p = c_loc(manifest_buf)
  end function clotran_manifest

  ! a null-terminated string as Fortran text
  function cstr(p) result(s)
    type(c_ptr), intent(in) :: p
    character(len=:), allocatable :: s
    character(kind=c_char), pointer :: c(:)
    integer :: n
    call c_f_pointer(p, c, [huge(0)])
    n = 0
    do while (c(n + 1) /= c_null_char)
       n = n + 1
    end do
    allocate(character(len=n) :: s)
    do n = 1, len(s)
       s(n:n) = c(n)
    end do
  end function cstr

  subroutine cs_entropy_shim(argc, argv) bind(C, name="cs_entropy_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    real(c_double), pointer :: mass, r
    call c_f_pointer(argv(1), mass); call c_f_pointer(argv(2), r)
    r = entropy(mass)
  end subroutine cs_entropy_shim

  subroutine cs_readopt_shim(argc, argv) bind(C, name="cs_readopt_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    integer(c_int), pointer :: iterld, ndxp, n_reg1, iprint, input_skip, nvdwc6, ndxp0, nrp, nrpi, npc, niacw, nq, nqg, xw1, xw2
    real(c_double), pointer :: clgvn, slgvn, tds0, vdwsl, phobsl, ephil1, ephil2, rzcut, rg_reg1, rg, rg_inner, rgim, drg
    real(c_double), pointer :: vdwc6(:), dxp0(:), rp(:), rpi(:), pcenter(:), xw(:,:), q(:), q_gas(:)
    integer(c_int), pointer :: iacw(:)
    character(len=:), allocatable :: vdw_path, input_file
    integer :: ios, i
    character(len=1) :: dummy
    ! argv, in manifest order: a scalar is one slot, an array its pointer then its extents
    call c_f_pointer(argv(1), iterld)
    call c_f_pointer(argv(3), nvdwc6); call c_f_pointer(argv(2), vdwc6, [nvdwc6])
    call c_f_pointer(argv(5), ndxp0);  call c_f_pointer(argv(4), dxp0, [ndxp0])
    call c_f_pointer(argv(6), clgvn); call c_f_pointer(argv(7), slgvn); call c_f_pointer(argv(8), tds0)
    call c_f_pointer(argv(10), nrp);   call c_f_pointer(argv(9), rp, [nrp])
    call c_f_pointer(argv(11), vdwsl); call c_f_pointer(argv(12), phobsl); call c_f_pointer(argv(13), ephil1)
    call c_f_pointer(argv(14), ephil2); call c_f_pointer(argv(15), rzcut)
    call c_f_pointer(argv(17), nrpi);  call c_f_pointer(argv(16), rpi, [nrpi])
    call c_f_pointer(argv(19), npc);   call c_f_pointer(argv(18), pcenter, [npc])
    call c_f_pointer(argv(20), rg_reg1); call c_f_pointer(argv(21), rg); call c_f_pointer(argv(22), rg_inner)
    call c_f_pointer(argv(23), rgim); call c_f_pointer(argv(24), ndxp)
    call c_f_pointer(argv(26), niacw); call c_f_pointer(argv(25), iacw, [niacw])
    call c_f_pointer(argv(28), xw1); call c_f_pointer(argv(29), xw2); call c_f_pointer(argv(27), xw, [xw1, xw2])
    call c_f_pointer(argv(31), nq);    call c_f_pointer(argv(30), q, [nq])
    call c_f_pointer(argv(33), nqg);   call c_f_pointer(argv(32), q_gas, [nqg])
    call c_f_pointer(argv(34), n_reg1); call c_f_pointer(argv(35), drg); call c_f_pointer(argv(36), iprint)
    vdw_path = cstr(argv(37)); input_file = cstr(argv(38))
    call c_f_pointer(argv(39), input_skip)
    ! vdw.par on unit 44, the input on unit 45 positioned past the lines
    ! the caller read; both closed after, as ChemSolBind did
    open(44, file=vdw_path, status="old", action="read", iostat=ios)
    if (ios /= 0) return
    open(45, file=input_file, status="old", action="read", iostat=ios)
    if (ios /= 0) then
       close(44)
       return
    end if
    do i = 1, input_skip
       read(45, '(a)', iostat=ios) dummy
       if (ios /= 0) exit
    end do
    call readopt(iterld, vdwc6, dxp0, clgvn, slgvn, tds0, rp, vdwsl, phobsl, ephil1, ephil2, rzcut, &
         rpi, pcenter, rg_reg1, rg, rg_inner, rgim, ndxp, iacw, xw, q, q_gas, n_reg1, drg, iprint)
    close(45)
    close(44)
  end subroutine cs_readopt_shim

  subroutine cs_dg_ld_shim(argc, argv) bind(C, name="cs_dg_ld_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    integer(c_int), pointer :: iterld, iprint, ndxp, n_reg1, itl, ndxp0, niacw, npc, nq, nqg, nqm, nrpi, nvdwc6, xw1, xw2
    real(c_double), pointer :: evqdq, elgwa, evdw, elgvn, ephob, etds, ebw, clgvn, ephil1, ephil2, phobsl, rg, rg_inner
    real(c_double), pointer :: rg_reg1, rgim, rzcut, slgvn, tds0, vdwsl, drg, drg_inner, rdcutl, out_cut
    real(c_double), pointer :: dxp0(:), pcenter(:), q(:), q_gas(:), q_mp2(:), rpi(:), vdwc6(:), xw(:,:)
    integer(c_int), pointer :: iacw(:)
    character(len=:), allocatable :: names
    character(len=8), allocatable :: atom(:)
    integer :: i, n
    call c_f_pointer(argv(1), iterld); call c_f_pointer(argv(2), iprint)
    call c_f_pointer(argv(3), evqdq); call c_f_pointer(argv(4), elgwa); call c_f_pointer(argv(5), evdw)
    call c_f_pointer(argv(6), elgvn); call c_f_pointer(argv(7), ephob); call c_f_pointer(argv(8), etds)
    call c_f_pointer(argv(9), ebw); call c_f_pointer(argv(10), clgvn)
    call c_f_pointer(argv(12), ndxp0); call c_f_pointer(argv(11), dxp0, [ndxp0])
    call c_f_pointer(argv(13), ephil1); call c_f_pointer(argv(14), ephil2)
    call c_f_pointer(argv(16), niacw); call c_f_pointer(argv(15), iacw, [niacw])
    call c_f_pointer(argv(17), ndxp)
    call c_f_pointer(argv(19), npc); call c_f_pointer(argv(18), pcenter, [npc])
    call c_f_pointer(argv(20), phobsl)
    call c_f_pointer(argv(22), nq); call c_f_pointer(argv(21), q, [nq])
    call c_f_pointer(argv(24), nqg); call c_f_pointer(argv(23), q_gas, [nqg])
    call c_f_pointer(argv(26), nqm); call c_f_pointer(argv(25), q_mp2, [nqm])
    call c_f_pointer(argv(27), rg); call c_f_pointer(argv(28), rg_inner); call c_f_pointer(argv(29), rg_reg1)
    call c_f_pointer(argv(30), rgim)
    call c_f_pointer(argv(32), nrpi); call c_f_pointer(argv(31), rpi, [nrpi])
    call c_f_pointer(argv(33), rzcut); call c_f_pointer(argv(34), slgvn); call c_f_pointer(argv(35), tds0)
    call c_f_pointer(argv(37), nvdwc6); call c_f_pointer(argv(36), vdwc6, [nvdwc6])
    call c_f_pointer(argv(38), vdwsl)
    call c_f_pointer(argv(40), xw1); call c_f_pointer(argv(41), xw2); call c_f_pointer(argv(39), xw, [xw1, xw2])
    names = cstr(argv(42))
    call c_f_pointer(argv(43), n_reg1); call c_f_pointer(argv(44), drg); call c_f_pointer(argv(45), drg_inner)
    call c_f_pointer(argv(46), rdcutl); call c_f_pointer(argv(47), out_cut); call c_f_pointer(argv(48), itl)
    ! the atom names: 8 characters each, n_reg1 of them at least
    n = max(len(names) / 8, int(n_reg1), 1)
    allocate(atom(n))
    atom = ""
    do i = 1, len(names) / 8
       atom(i) = names(8 * i - 7:8 * i)
    end do
    call dg_ld(iterld, iprint, evqdq, elgwa, evdw, elgvn, ephob, etds, ebw, clgvn, dxp0, ephil1, ephil2, iacw, ndxp, &
         pcenter, phobsl, q, q_gas, q_mp2, rg, rg_inner, rg_reg1, rgim, rpi, rzcut, slgvn, tds0, vdwc6, vdwsl, &
         xw, atom, n_reg1, drg, drg_inner, rdcutl, out_cut, itl)
  end subroutine cs_dg_ld_shim

  subroutine cs_solvout_shim(argc, argv) bind(C, name="cs_solvout_shim")
    integer(c_int), value :: argc
    type(c_ptr), dimension(*) :: argv
    integer(c_int), pointer :: iterld, iprint
    logical(c_bool), pointer :: do_gas
    real(c_double), pointer :: evqdq, elgwa, etds, evdw, ebw, elgvn, ephob
    character(len=13) :: molname
    character(len=4) :: ssname
    call c_f_pointer(argv(1), iterld); call c_f_pointer(argv(2), iprint); call c_f_pointer(argv(3), do_gas)
    call c_f_pointer(argv(4), evqdq); call c_f_pointer(argv(5), elgwa); call c_f_pointer(argv(6), etds)
    call c_f_pointer(argv(7), evdw); call c_f_pointer(argv(8), ebw); call c_f_pointer(argv(9), elgvn)
    call c_f_pointer(argv(10), ephob)
    molname = cstr(argv(11)); ssname = cstr(argv(12))
    call solvout(iterld, iprint, logical(do_gas), evqdq, elgwa, etds, evdw, ebw, elgvn, ephob, molname, ssname)
  end subroutine cs_solvout_shim
end module chemsol_pkg
