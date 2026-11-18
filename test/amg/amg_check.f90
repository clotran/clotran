! The generated array map reads (src/f/gen/arraymap_gen.inc, from
! model/arraymapg.lisp) on a heap read from a file: scripts/fuzz-amg-gen's
! case, the same one ACL2 answers. Prints, a line a query, index_of's,
! get's, key_at's and val_at's answers. gc_equal is the words' equality, as
! the ACL2 side attaches it. With a second argument "broken", the negative
! control: a map's count reads one more.
module amg_check_m
  use iso_fortran_env, only: int64
  implicit none
  type :: amg_heap
  end type amg_heap
  type(amg_heap) :: hs
  integer(int64), allocatable :: otag(:), oref(:), okind(:), oi1(:)
  integer(int64), allocatable :: voff(:), vlen(:), atag(:), aref(:), aival(:)
  logical :: broken = .false.
contains
  pure integer(int64) function hp_otag(j)
    integer(int64), intent(in) :: j
    hp_otag = otag(j)
  end function hp_otag
  pure integer(int64) function hp_oref(j)
    integer(int64), intent(in) :: j
    hp_oref = oref(j)
  end function hp_oref
  pure integer(int64) function hp_n_oslot()
    hp_n_oslot = size(otag, kind=int64)
  end function hp_n_oslot
  pure integer(int64) function hp_okind(i)
    integer(int64), intent(in) :: i
    hp_okind = okind(i)
  end function hp_okind
  pure integer(int64) function hp_oi1(i)
    integer(int64), intent(in) :: i
    hp_oi1 = oi1(i)
    if (broken) hp_oi1 = hp_oi1 + 1
  end function hp_oi1
  pure integer(int64) function hp_n_obj()
    hp_n_obj = size(okind, kind=int64)
  end function hp_n_obj
  pure integer(int64) function hp_voff(i)
    integer(int64), intent(in) :: i
    hp_voff = voff(i)
  end function hp_voff
  pure integer(int64) function hp_vlen(i)
    integer(int64), intent(in) :: i
    hp_vlen = vlen(i)
  end function hp_vlen
  pure integer(int64) function hp_n_vec()
    hp_n_vec = size(voff, kind=int64)
  end function hp_n_vec
  pure integer(int64) function hp_atag(j)
    integer(int64), intent(in) :: j
    hp_atag = atag(j)
  end function hp_atag
  pure integer(int64) function hp_aref(j)
    integer(int64), intent(in) :: j
    hp_aref = aref(j)
  end function hp_aref
  pure integer(int64) function hp_aival(j)
    integer(int64), intent(in) :: j
    hp_aival = aival(j)
  end function hp_aival
  pure integer(int64) function hp_n_arena()
    hp_n_arena = size(atag, kind=int64)
  end function hp_n_arena
  logical function am_keq(kt, kr, kv, wt, wr, wv)
    integer(int64), intent(in) :: kt, kr, kv, wt, wr, wv
    am_keq = kt == wt .and. kr == wr .and. kv == wv
  end function am_keq

  include "arraymap_gen.inc"
end module amg_check_m

program amg_check
  use iso_fortran_env, only: int64
  use amg_check_m
  implicit none
  character(len=4096) :: path, arg
  integer :: u, no, nv, na, nq, q
  integer(int64) :: tg, rf, kt, kr, kv, i
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = trim(arg) == "broken"
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) no, nv, na
  allocate(otag(0:5*no-1), oref(0:5*no-1), okind(0:no-1), oi1(0:no-1))
  allocate(voff(0:nv-1), vlen(0:nv-1), atag(0:na-1), aref(0:na-1), aival(0:na-1))
  read(u, *) otag; read(u, *) oref; read(u, *) okind; read(u, *) oi1
  read(u, *) voff; read(u, *) vlen; read(u, *) atag; read(u, *) aref; read(u, *) aival
  read(u, *) nq
  do q = 1, nq
     read(u, *) tg, rf, kt, kr, kv, i
     write(*, '(I0,1X,I0,1X,I0,1X,I0)') amg_index(hs, tg, rf, kt, kr, kv), amg_get(hs, tg, rf, kt, kr, kv), &
          amg_at(hs, tg, rf, 0_int64, i), amg_at(hs, tg, rf, 1_int64, i)
  end do
  close(u)
end program amg_check
