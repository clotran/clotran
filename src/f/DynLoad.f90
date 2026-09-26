! DynLoad: a shared library opened at run time, and a routine in it
! called through the one signature every clotran package exports.
!
! Standard Fortran has no dynamic loading, but dlopen and dlsym are C
! functions, iso_c_binding names them, and c_f_procpointer makes the
! symbol callable -- no C source of clotran's own. A package is a shared
! library that exports
!
!   clotran_manifest            a C string: EDN describing its routines
!   <routine>_shim(argc, argv)  one per routine: argc arguments, each a
!                               C pointer to the value or buffer, unpacked
!                               to the real routine's positional arguments
!
! so that clotran needs exactly one procedure-pointer interface, ever,
! and a package built by any Fortran compiler can be opened by any
! clotran. What the pointers point at -- scalars, registry buffers,
! character arrays -- is Eval.f90's business (B_PKGLOAD, B_PKGCALL);
! this module knows the loader and the calling convention, nothing else.
!
! POSIX only for now: dlopen lives in libSystem on macOS and libdl on
! Linux. Windows is LoadLibrary and GetProcAddress under the same two
! wrappers, a second implementation of this module, not a change to
! its callers.
module DynLoad
  use iso_c_binding
  implicit none
  private
  public :: dl_open, dl_sym, dl_error, dl_c_string, dl_call_shim, dl_manifest, shim_i
  public :: dl_install, install_i

  interface
     function dlopen(path, mode) bind(C, name="dlopen") result(h)
       import :: c_ptr, c_char, c_int
       character(kind=c_char), dimension(*) :: path
       integer(c_int), value :: mode
       type(c_ptr) :: h
     end function dlopen
     function dlsym(h, name) bind(C, name="dlsym") result(p)
       import :: c_ptr, c_char, c_funptr
       type(c_ptr), value :: h
       character(kind=c_char), dimension(*) :: name
       type(c_funptr) :: p
     end function dlsym
     function dlerror() bind(C, name="dlerror") result(s)
       import :: c_ptr
       type(c_ptr) :: s
     end function dlerror
     function strlen(s) bind(C, name="strlen") result(n)
       import :: c_ptr, c_size_t
       type(c_ptr), value :: s
       integer(c_size_t) :: n
     end function strlen
  end interface

  ! What a generated library exports so the loader can find it.
  ! What a generated library exports. The argument is the handle of
  ! the CONSTANT POOL the loader registered for it: a generated
  ! procedure cannot spell a map, a Var or a folded function in
  ! Fortran, so the values live in a vector the driver registers and
  ! the procedures index. The handle is not known when the source is
  ! written, which is why it is passed in rather than baked in.
  abstract interface
     subroutine install_i(pool) bind(C)
       import :: c_int
       integer(c_int), value :: pool
     end subroutine install_i
  end interface

  ! the shim: argc arguments, each a C pointer
  abstract interface
     subroutine shim_i(argc, argv) bind(C)
       import :: c_int, c_ptr
       integer(c_int), value :: argc
       type(c_ptr), dimension(*) :: argv
     end subroutine shim_i
  end interface

  ! the manifest: a function answering the address of a C string
  abstract interface
     function manifest_i() bind(C) result(p)
       import :: c_ptr
       type(c_ptr) :: p
     end function manifest_i
  end interface

  integer(c_int), parameter :: RTLD_NOW = 2

contains

  ! The library, or a null pointer; dl_error then says why.
  function dl_open(path) result(h)
    character(len=*), intent(in) :: path
    type(c_ptr) :: h
    h = dlopen(path // c_null_char, RTLD_NOW)
  end function dl_open

  ! A symbol's address, or null.
  function dl_sym(h, name) result(p)
    type(c_ptr), intent(in) :: h
    character(len=*), intent(in) :: name
    type(c_funptr) :: p
    p = dlsym(h, name // c_null_char)
  end function dl_sym

  subroutine dl_error(s)
    character(len=:), allocatable, intent(out) :: s
    type(c_ptr) :: p
    p = dlerror()
    block
       character(len=:), allocatable :: dlr_1
       call dl_c_string(p, s=dlr_1)
       s = dlr_1
    end block
  end subroutine dl_error

  ! A C string as Fortran text ("" for null).
  subroutine dl_c_string(p, s)
    type(c_ptr), intent(in) :: p
    character(len=:), allocatable, intent(out) :: s
    character(kind=c_char), pointer :: chars(:)
    integer :: n, i
    s = ""
    if (.not. c_associated(p)) return
    n = int(strlen(p))
    if (n <= 0) return
    call c_f_pointer(p, chars, [n])
    deallocate(s)
    allocate(character(len=n) :: s)
    do i = 1, n
       s(i:i) = chars(i)
    end do
  end subroutine dl_c_string

  ! The package's manifest, EDN as text; "" when the library exports none.
  subroutine dl_manifest(h, s)
    type(c_ptr), intent(in) :: h
    character(len=:), allocatable, intent(out) :: s
    type(c_funptr) :: fp
    procedure(manifest_i), pointer :: f
    s = ""
    fp = dl_sym(h, "clotran_manifest")
    if (.not. c_associated(fp)) return
    call c_f_procpointer(fp, f)
    block
       character(len=:), allocatable :: dlr_2
       call dl_c_string(f(), s=dlr_2)
       s = dlr_2
    end block
  end subroutine dl_manifest

  ! One call through the uniform signature.
  ! Opens a COMPILED NAMESPACE and lets it install itself.
  !
  ! A generated library exports one procedure per function plus
  !
  !   subroutine clotran_install() bind(C, name="clotran_install")
  !
  ! which calls clotran_def_fn for each of them. So the loader knows one
  ! symbol, forever, exactly as a package is one shim signature -- and a
  ! library built by any compiler works, because the only thing crossing
  ! the boundary is the C convention.
  !
  ! The library is NEVER CLOSED. A compiled function value names its
  ! procedure through CompiledFn's table, and closing the library while
  ! one is reachable would crash; a recompile loads a new file under a
  ! new name instead and leaks the old (PLAN step 10).
  function dl_install(path, pool, err) result(ok)
    character(len=*), intent(in) :: path
    integer, intent(in) :: pool
    character(len=:), allocatable, intent(out) :: err
    logical :: ok
    type(c_ptr) :: h
    type(c_funptr) :: fp
    procedure(install_i), pointer :: f
    ok = .false.
    err = ""
    h = dl_open(path)
    if (.not. c_associated(h)) then
       block
          character(len=:), allocatable :: dlr_3
          call dl_error(s=dlr_3)
          err = dlr_3
       end block
       if (len(err) == 0) err = "cannot open " // path
       return
    end if
    fp = dl_sym(h, "clotran_install")
    if (.not. c_associated(fp)) then
       err = "no clotran_install in " // path
       return
    end if
    call c_f_procpointer(fp, f)
    call f(int(pool, c_int))
    ok = .true.
  end function dl_install

  subroutine dl_call_shim(fp, argv)
    type(c_funptr), intent(in) :: fp
    type(c_ptr), intent(in) :: argv(:)
    procedure(shim_i), pointer :: f
    call c_f_procpointer(fp, f)
    call f(int(size(argv), c_int), argv)
  end subroutine dl_call_shim

end module DynLoad
