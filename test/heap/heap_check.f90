! The generated collector's marking (src/f/gen/heap_gen.inc, from
! model/heapg.lisp) on a heap read from a file: scripts/fuzz-heap-gen's
! case, the same one ACL2's hpg-drain marks and hpg-sweep-* sweeps (model/heapsw.lisp).
! Prints the marks, what the sweep freed and wrote, and the counts.
! With a second argument "broken", the negative control: an object's last
! slot reads as no reference.
module heap_check_m
  use iso_fortran_env, only: int64
  implicit none
  type :: heap_state
     integer(int64) :: err = 0, msp = 0, nobj = 0, nvec = 0, nstr = 0, alive = 0
     integer(int64) :: nswo = 0, nswv = 0, nsws = 0, afree = 0
     integer(int64), allocatable :: mtag(:), mref(:)
  end type heap_state
  integer(int64), allocatable :: otag(:), oref(:), omark(:), voff(:), vlen(:), vmark(:), atag(:), aref(:), smark(:)
  integer(int64), allocatable :: okind(:), ofree(:), onext(:), vfree(:), vnext(:), sfree(:), snext(:), aival(:), chead(:)
  integer(int64), allocatable :: ofin(:), srel(:)
  integer(int64) :: ohead = 0, vhead = 0, shead = 0
  integer(int64) :: oused = 0, ocap = 0, nob = 0, vused = 0, vcap = 0, nvb = 0, sused = 0, scap = 0, nsb = 0
  integer(int64), allocatable :: ob(:), vb(:), sb(:)
  logical :: broken = .false.
contains
  integer(int64) function hp_otag(j)
    integer(int64), intent(in) :: j
    hp_otag = otag(j)
  end function hp_otag
  integer(int64) function hp_oref(j)
    integer(int64), intent(in) :: j
    hp_oref = oref(j)
    if (broken .and. mod(j, 5_int64) == 4) hp_oref = 0
  end function hp_oref
  integer(int64) function hp_n_oslot()
    hp_n_oslot = size(otag, kind=int64)
  end function hp_n_oslot
  integer(int64) function hp_omark(i)
    integer(int64), intent(in) :: i
    hp_omark = omark(i)
  end function hp_omark
  subroutine hp_set_omark(i, x)
    integer(int64), intent(in) :: i, x
    omark(i) = x
  end subroutine hp_set_omark
  integer(int64) function hp_n_obj()
    hp_n_obj = size(omark, kind=int64)
  end function hp_n_obj
  integer(int64) function hp_voff(i)
    integer(int64), intent(in) :: i
    hp_voff = voff(i)
  end function hp_voff
  integer(int64) function hp_vlen(i)
    integer(int64), intent(in) :: i
    hp_vlen = vlen(i)
  end function hp_vlen
  integer(int64) function hp_vmark(i)
    integer(int64), intent(in) :: i
    hp_vmark = vmark(i)
  end function hp_vmark
  subroutine hp_set_vmark(i, x)
    integer(int64), intent(in) :: i, x
    vmark(i) = x
  end subroutine hp_set_vmark
  integer(int64) function hp_n_vec()
    hp_n_vec = min(size(voff, kind=int64), size(vlen, kind=int64), size(vmark, kind=int64))
  end function hp_n_vec
  integer(int64) function hp_atag(j)
    integer(int64), intent(in) :: j
    hp_atag = atag(j)
  end function hp_atag
  integer(int64) function hp_aref(j)
    integer(int64), intent(in) :: j
    hp_aref = aref(j)
  end function hp_aref
  integer(int64) function hp_n_arena()
    hp_n_arena = size(atag, kind=int64)
  end function hp_n_arena
  integer(int64) function hp_smark(i)
    integer(int64), intent(in) :: i
    hp_smark = smark(i)
  end function hp_smark
  subroutine hp_set_smark(i, x)
    integer(int64), intent(in) :: i, x
    smark(i) = x
  end subroutine hp_set_smark
  integer(int64) function hp_n_str()
    hp_n_str = size(smark, kind=int64)
  end function hp_n_str

  integer(int64) function hp_okind(i)
    integer(int64), intent(in) :: i
    hp_okind = okind(i)
  end function hp_okind
  subroutine hp_set_okind(i, x)
    integer(int64), intent(in) :: i, x
    okind(i) = x
  end subroutine hp_set_okind
  integer(int64) function hp_ofree(i)
    integer(int64), intent(in) :: i
    hp_ofree = ofree(i)
  end function hp_ofree
  subroutine hp_set_ofree(i, x)
    integer(int64), intent(in) :: i, x
    ofree(i) = x
  end subroutine hp_set_ofree
  integer(int64) function hp_onext(i)
    integer(int64), intent(in) :: i
    hp_onext = onext(i)
  end function hp_onext
  subroutine hp_set_onext(i, x)
    integer(int64), intent(in) :: i, x
    onext(i) = x
  end subroutine hp_set_onext
  subroutine hp_finalize(i, x)
    integer(int64), intent(in) :: i, x
    ofin(i) = x
  end subroutine hp_finalize
  integer(int64) function hp_ohead()
    hp_ohead = ohead
  end function hp_ohead
  subroutine hp_set_ohead(x)
    integer(int64), intent(in) :: x
    ohead = x
  end subroutine hp_set_ohead
  subroutine hp_set_voff(i, x)
    integer(int64), intent(in) :: i, x
    voff(i) = x
  end subroutine hp_set_voff
  subroutine hp_set_vlen(i, x)
    integer(int64), intent(in) :: i, x
    vlen(i) = x
  end subroutine hp_set_vlen
  integer(int64) function hp_vfree(i)
    integer(int64), intent(in) :: i
    hp_vfree = vfree(i)
  end function hp_vfree
  subroutine hp_set_vfree(i, x)
    integer(int64), intent(in) :: i, x
    vfree(i) = x
  end subroutine hp_set_vfree
  integer(int64) function hp_vnext(i)
    integer(int64), intent(in) :: i
    hp_vnext = vnext(i)
  end function hp_vnext
  subroutine hp_set_vnext(i, x)
    integer(int64), intent(in) :: i, x
    vnext(i) = x
  end subroutine hp_set_vnext
  integer(int64) function hp_vhead()
    hp_vhead = vhead
  end function hp_vhead
  subroutine hp_set_vhead(x)
    integer(int64), intent(in) :: x
    vhead = x
  end subroutine hp_set_vhead
  subroutine hp_set_atag(j, x)
    integer(int64), intent(in) :: j, x
    atag(j) = x
  end subroutine hp_set_atag
  subroutine hp_set_aref(j, x)
    integer(int64), intent(in) :: j, x
    aref(j) = x
  end subroutine hp_set_aref
  integer(int64) function hp_aival(j)
    integer(int64), intent(in) :: j
    hp_aival = aival(j)
  end function hp_aival
  subroutine hp_set_aival(j, x)
    integer(int64), intent(in) :: j, x
    aival(j) = x
  end subroutine hp_set_aival
  integer(int64) function hp_chead(c)
    integer(int64), intent(in) :: c
    hp_chead = chead(c)
  end function hp_chead
  subroutine hp_set_chead(c, x)
    integer(int64), intent(in) :: c, x
    chead(c) = x
  end subroutine hp_set_chead
  integer(int64) function hp_n_chead()
    hp_n_chead = size(chead, kind=int64)
  end function hp_n_chead
  integer(int64) function hp_sfree(i)
    integer(int64), intent(in) :: i
    hp_sfree = sfree(i)
  end function hp_sfree
  subroutine hp_set_sfree(i, x)
    integer(int64), intent(in) :: i, x
    sfree(i) = x
  end subroutine hp_set_sfree
  integer(int64) function hp_snext(i)
    integer(int64), intent(in) :: i
    hp_snext = snext(i)
  end function hp_snext
  subroutine hp_set_snext(i, x)
    integer(int64), intent(in) :: i, x
    snext(i) = x
  end subroutine hp_set_snext
  integer(int64) function hp_shead()
    hp_shead = shead
  end function hp_shead
  subroutine hp_set_shead(x)
    integer(int64), intent(in) :: x
    shead = x
  end subroutine hp_set_shead
  subroutine hp_release_str(i, x)
    integer(int64), intent(in) :: i, x
    srel(i) = x
  end subroutine hp_release_str

  integer(int64) function hp_oused()
    hp_oused = oused
  end function hp_oused
  subroutine hp_set_oused(x)
    integer(int64), intent(in) :: x
    oused = x
  end subroutine hp_set_oused
  integer(int64) function hp_ocap()
    hp_ocap = ocap
  end function hp_ocap
  integer(int64) function hp_nob()
    hp_nob = nob
  end function hp_nob
  subroutine hp_set_nob(x)
    integer(int64), intent(in) :: x
    nob = x
  end subroutine hp_set_nob
  integer(int64) function hp_ob(k)
    integer(int64), intent(in) :: k
    hp_ob = ob(k)
  end function hp_ob
  subroutine hp_set_ob(k, x)
    integer(int64), intent(in) :: k, x
    ob(k) = x
  end subroutine hp_set_ob
  integer(int64) function hp_n_ob()
    hp_n_ob = size(ob, kind=int64)
  end function hp_n_ob
  integer(int64) function hp_vused()
    hp_vused = vused
  end function hp_vused
  subroutine hp_set_vused(x)
    integer(int64), intent(in) :: x
    vused = x
  end subroutine hp_set_vused
  integer(int64) function hp_vcap()
    hp_vcap = vcap
  end function hp_vcap
  integer(int64) function hp_nvb()
    hp_nvb = nvb
  end function hp_nvb
  subroutine hp_set_nvb(x)
    integer(int64), intent(in) :: x
    nvb = x
  end subroutine hp_set_nvb
  integer(int64) function hp_vb(k)
    integer(int64), intent(in) :: k
    hp_vb = vb(k)
  end function hp_vb
  subroutine hp_set_vb(k, x)
    integer(int64), intent(in) :: k, x
    vb(k) = x
  end subroutine hp_set_vb
  integer(int64) function hp_sused()
    hp_sused = sused
  end function hp_sused
  subroutine hp_set_sused(x)
    integer(int64), intent(in) :: x
    sused = x
  end subroutine hp_set_sused
  integer(int64) function hp_scap()
    hp_scap = scap
  end function hp_scap
  integer(int64) function hp_nsb()
    hp_nsb = nsb
  end function hp_nsb
  subroutine hp_set_nsb(x)
    integer(int64), intent(in) :: x
    nsb = x
  end subroutine hp_set_nsb
  integer(int64) function hp_sb(k)
    integer(int64), intent(in) :: k
    hp_sb = sb(k)
  end function hp_sb
  subroutine hp_set_sb(k, x)
    integer(int64), intent(in) :: k, x
    sb(k) = x
  end subroutine hp_set_sb

  include "heap_gen.inc"
end module heap_check_m

program heap_check
  use heap_check_m
  implicit none
  type(heap_state) :: hs
  integer :: u, i, nr
  integer(int64) :: no, nv, na, ns, cap, t, r, tk(3), pp(4), k
  character(len=256) :: path, arg2
  call get_command_argument(1, path)
  call get_command_argument(2, arg2)
  broken = trim(arg2) == "broken"
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) no, nv, na, ns, cap
  allocate(otag(0:5 * no - 1), oref(0:5 * no - 1), omark(0:no - 1))
  allocate(voff(0:nv - 1), vlen(0:nv - 1), vmark(0:nv - 1), atag(0:na - 1), aref(0:na - 1), smark(0:ns - 1))
  allocate(hs%mtag(0:cap - 1), hs%mref(0:cap - 1))
  allocate(okind(0:no - 1), ofree(0:no - 1), onext(0:no - 1), ofin(0:no - 1), vfree(0:nv - 1), vnext(0:nv - 1))
  allocate(sfree(0:ns - 1), snext(0:ns - 1), srel(0:ns - 1), aival(0:na - 1), chead(0:30))
  ofin = 0
  srel = 0
  read(u, *) otag
  read(u, *) oref
  read(u, *) omark
  if (nv > 0) read(u, *) voff
  if (nv > 0) read(u, *) vlen
  if (nv > 0) read(u, *) vmark
  if (na > 0) read(u, *) atag
  if (na > 0) read(u, *) aref
  if (ns > 0) read(u, *) smark
  read(u, *) okind
  read(u, *) ofree
  read(u, *) onext
  if (nv > 0) read(u, *) vfree
  if (nv > 0) read(u, *) vnext
  if (ns > 0) read(u, *) sfree
  if (ns > 0) read(u, *) snext
  if (na > 0) read(u, *) aival
  read(u, *) chead
  read(u, *) ohead, vhead, shead
  read(u, *) oused, ocap, vused, vcap, sused, scap
  allocate(ob(0:7), vb(0:7), sb(0:7))
  ob = 0
  vb = 0
  sb = 0
  read(u, *) nr
  do i = 1, nr
     read(u, *) t, r
     call hpg_push(hs, t, r)
  end do
  close(u)
  call hpg_drain(hs, 1000000_int64)
  call hpg_sweep_objs(hs, 1_int64, no - 1)
  call hpg_sweep_vecs(hs, 1_int64, nv - 1)
  call hpg_sweep_strs(hs, 1_int64, ns - 1)
  write(*, '(a, *(1x, i0))') 'omark', omark
  write(*, '(a, *(1x, i0))') 'vmark', vmark
  write(*, '(a, *(1x, i0))') 'smark', smark
  write(*, '(a, 6(1x, i0))') 'regs', hs%err, hs%msp, hs%nobj, hs%nvec, hs%nstr, hs%alive
  write(*, '(a, *(1x, i0))') 'okind', okind
  write(*, '(a, *(1x, i0))') 'ofree', ofree
  write(*, '(a, *(1x, i0))') 'onext', onext
  write(*, '(a, *(1x, i0))') 'ofin', ofin
  write(*, '(a, *(1x, i0))') 'voff', voff
  write(*, '(a, *(1x, i0))') 'vlen', vlen
  write(*, '(a, *(1x, i0))') 'vfree', vfree
  write(*, '(a, *(1x, i0))') 'vnext', vnext
  write(*, '(a, *(1x, i0))') 'atag', atag
  write(*, '(a, *(1x, i0))') 'aref', aref
  write(*, '(a, *(1x, i0))') 'aival', aival
  write(*, '(a, *(1x, i0))') 'chead', chead
  write(*, '(a, *(1x, i0))') 'sfree', sfree
  write(*, '(a, *(1x, i0))') 'snext', snext
  write(*, '(a, *(1x, i0))') 'srel', srel
  write(*, '(a, 7(1x, i0))') 'sweep', ohead, vhead, shead, hs%nswo, hs%nswv, hs%nsws, hs%afree
  do k = 1, 3
     call hpg_obj_take(hs, tk(k))
     if (tk(k) > 0 .and. tk(k) < no) call hpg_obj_use(hs, tk(k))
  end do
  call hpg_obj_fill(hs, 6_int64)
  do k = 1, 4
     call hpg_obj_pop(hs, pp(k))
  end do
  write(*, '(a, 3(1x, i0))') 'takes', tk
  write(*, '(a, 4(1x, i0))') 'pops', pp
  write(*, '(a, *(1x, i0))') 'ob', ob
  write(*, '(a, 4(1x, i0))') 'alloc', nob, oused, ohead, ocap
  write(*, '(a, *(1x, i0))') 'ofree2', ofree
  write(*, '(a, *(1x, i0))') 'omark2', omark
  do k = 1, 3
     call hpg_vec_take(hs, tk(k))
     if (tk(k) > 0 .and. tk(k) < nv) call hpg_vec_use(hs, tk(k))
  end do
  call hpg_vec_fill(hs, 6_int64)
  do k = 1, 4
     call hpg_vec_pop(hs, pp(k))
  end do
  write(*, '(a, 3(1x, i0))') 'vtakes', tk
  write(*, '(a, 4(1x, i0))') 'vpops', pp
  write(*, '(a, *(1x, i0))') 'vb', vb
  write(*, '(a, 4(1x, i0))') 'valloc', nvb, vused, vhead, vcap
  write(*, '(a, *(1x, i0))') 'vfree2', vfree
  write(*, '(a, *(1x, i0))') 'vmark2', vmark
  do k = 1, 3
     call hpg_str_take(hs, tk(k))
     if (tk(k) > 0 .and. tk(k) < ns) call hpg_str_use(hs, tk(k))
  end do
  call hpg_str_fill(hs, 6_int64)
  do k = 1, 4
     call hpg_str_pop(hs, pp(k))
  end do
  write(*, '(a, 3(1x, i0))') 'stakes', tk
  write(*, '(a, 4(1x, i0))') 'spops', pp
  write(*, '(a, *(1x, i0))') 'sb', sb
  write(*, '(a, 4(1x, i0))') 'salloc', nsb, sused, shead, scap
  write(*, '(a, *(1x, i0))') 'sfree2', sfree
  write(*, '(a, *(1x, i0))') 'smark2', smark
end program heap_check
