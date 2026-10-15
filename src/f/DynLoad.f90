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
! dlopen lives in libSystem on macOS and libdl on Linux; on Windows
! src/c/win_shim.c writes dlopen and dlsym over LoadLibrary and
! GetProcAddress, so this module is the same everywhere.
module DynLoad
  use iso_c_binding
  use GC, only: gc_state_lock, gc_state_unlock
  implicit none
  private
  public :: dl_open, dl_sym, dl_error, dl_c_string, dl_call_shim, dl_manifest, shim_i
  public :: dl_install, install_i
  public :: dl_log_count, dl_log_get, dl_replay, dl_replaying

  ! EVERY INSTALL, in order: the library and the constant pool it was
  ! given. An image cannot hold a procedure pointer, so it holds this
  ! instead, and a start from the image opens the same libraries in the
  ! same order and calls their clotran_install again (dl_replay): each
  ! registers its procedures in the order it did, so every handle the heap
  ! holds names the same procedure again. While replaying, the Vars are
  ! not defined again -- the heap already has them (ClotranABI).
  type :: install_note
     character(len=:), allocatable :: path
     integer :: pool = 0
  end type install_note
  type(install_note), allocatable, save :: log(:)
  integer, save :: n_log = 0
  logical, save :: dl_replaying = .false.

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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    p = dlerror()
    block
       call dl_c_string(p, s=dlt_1)
       s = dlt_1
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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    s = ""
    fp = dl_sym(h, "clotran_manifest")
    if (.not. c_associated(fp)) return
    call c_f_procpointer(fp, f)
    block
       call dl_c_string(f(), s=dlt_1)
       s = dlt_1
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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    ok = .false.
    err = ""
    h = dl_open(path)
    if (.not. c_associated(h)) then
       block
          call dl_error(s=dlt_1)
          err = dlt_1
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
    if (.not. dl_replaying) call note_install(path, pool)
  end function dl_install

  ! by its real path: an image is read from another directory
  subroutine note_install(path, pool)
    character(len=*), intent(in) :: path
    integer, intent(in) :: pool
    type(install_note), allocatable :: bigger(:)
    integer :: i, k
    interface
       function c_realpath(p, resolved) bind(C, name="realpath") result(r)
         import :: c_char, c_ptr
         character(kind=c_char), intent(in) :: p(*)
         character(kind=c_char), intent(out) :: resolved(*)
         type(c_ptr) :: r
       end function c_realpath
    end interface
    character(kind=c_char) :: buf(4096)
    character(len=:), allocatable :: real
    call gc_state_lock()
    if (.not. allocated(log)) allocate(log(16))
    if (n_log == size(log)) then
       allocate(bigger(2 * size(log)))
       do i = 1, n_log
          call move_alloc(log(i)%path, bigger(i)%path)
          bigger(i)%pool = log(i)%pool
       end do
       call move_alloc(bigger, log)
    end if
    n_log = n_log + 1
    real = path
    if (c_associated(c_realpath(path // c_null_char, buf))) then
       k = 0
       do while (k < size(buf))
          if (buf(k + 1) == c_null_char) exit
          k = k + 1
       end do
       real = repeat(" ", k)
       do i = 1, k
          real(i:i) = buf(i)
       end do
    end if
    log(n_log)%path = real
    log(n_log)%pool = pool
    call gc_state_unlock()
  end subroutine note_install

  integer function dl_log_count()
    dl_log_count = n_log
  end function dl_log_count

  subroutine dl_log_get(i, path, pool)
    integer, intent(in) :: i
    character(len=:), allocatable, intent(out) :: path
    integer, intent(out) :: pool
    path = log(i)%path
    pool = log(i)%pool
  end subroutine dl_log_get

  ! The installs an image recorded, again, in order, from where each
  ! library is now; the log becomes theirs. False, with why, on the
  ! first that fails.
  function dl_replay(paths, pools, err) result(ok)
    character(len=*), intent(in) :: paths(:)
    integer, intent(in) :: pools(:)
    character(len=:), allocatable, intent(out) :: err
    logical :: ok
    integer :: i
    ok = .true.
    err = ""
    dl_replaying = .true.
    do i = 1, size(paths)
       if (.not. dl_install(trim(paths(i)), pools(i), err)) then
          ok = .false.
          exit
       end if
       call note_install(trim(paths(i)), pools(i))
    end do
    dl_replaying = .false.
  end function dl_replay

  subroutine dl_call_shim(fp, argv)
    type(c_funptr), value :: fp   ! by value: see Threads.f90, th_start
    type(c_ptr), intent(in) :: argv(:)
    procedure(shim_i), pointer :: f
    call c_f_procpointer(fp, f)
    call f(int(size(argv), c_int), argv)
  end subroutine dl_call_shim

end module DynLoad
