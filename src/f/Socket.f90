! Socket.f90 -- TCP sockets for clotran, over src/c/socket_shim.c, which
! holds everything that differs between POSIX and Winsock. A socket is an
! integer(8) handle. Every call that can block -- accept, read -- first
! steps out of the running mutators (gc_mutator_leave), so a collection on
! another thread never waits for a thread waiting on the network, and
! steps back in before it returns. Nothing collected is touched meanwhile:
! a read lands in a plain buffer, and the caller builds the string after.
module Socket
  use, intrinsic :: iso_c_binding
  use GC, only: gc_mutator_enter, gc_mutator_leave
  implicit none
  private
  public :: sock_listen, sock_local_port, sock_accept, sock_connect, &
       sock_read, sock_write, sock_close, SOCK_TIMEOUT, SOCK_BUF

  integer(8), parameter :: SOCK_TIMEOUT = -2_8
  integer, parameter :: SOCK_BUF = 65536
  integer, parameter :: ERR_CAP = 256

  interface
     function cs_listen(host, port, backlog, err, errcap) result(h) bind(C, name="cs_listen")
       import :: c_char, c_int32_t, c_int64_t
       character(kind=c_char), intent(in) :: host(*)
       integer(c_int32_t), value :: port, backlog, errcap
       character(kind=c_char), intent(out) :: err(*)
       integer(c_int64_t) :: h
     end function cs_listen
     function cs_local_port(h) result(p) bind(C, name="cs_local_port")
       import :: c_int32_t, c_int64_t
       integer(c_int64_t), value :: h
       integer(c_int32_t) :: p
     end function cs_local_port
     function cs_accept(h, ms, err, errcap) result(c) bind(C, name="cs_accept")
       import :: c_char, c_int32_t, c_int64_t
       integer(c_int64_t), value :: h
       integer(c_int32_t), value :: ms, errcap
       character(kind=c_char), intent(out) :: err(*)
       integer(c_int64_t) :: c
     end function cs_accept
     function cs_connect(host, port, err, errcap) result(h) bind(C, name="cs_connect")
       import :: c_char, c_int32_t, c_int64_t
       character(kind=c_char), intent(in) :: host(*)
       integer(c_int32_t), value :: port, errcap
       character(kind=c_char), intent(out) :: err(*)
       integer(c_int64_t) :: h
     end function cs_connect
     function cs_read(h, buf, cap, ms, err, errcap) result(n) bind(C, name="cs_read")
       import :: c_char, c_int32_t, c_int64_t
       integer(c_int64_t), value :: h
       character(kind=c_char), intent(out) :: buf(*)
       integer(c_int32_t), value :: cap, ms, errcap
       character(kind=c_char), intent(out) :: err(*)
       integer(c_int32_t) :: n
     end function cs_read
     function cs_write(h, buf, len, err, errcap) result(n) bind(C, name="cs_write")
       import :: c_char, c_int32_t, c_int64_t
       integer(c_int64_t), value :: h
       character(kind=c_char), intent(in) :: buf(*)
       integer(c_int32_t), value :: len, errcap
       character(kind=c_char), intent(out) :: err(*)
       integer(c_int32_t) :: n
     end function cs_write
     function cs_close(h) result(r) bind(C, name="cs_close")
       import :: c_int32_t, c_int64_t
       integer(c_int64_t), value :: h
       integer(c_int32_t) :: r
     end function cs_close
  end interface

contains

  ! The message C wrote, up to its NUL.
  subroutine c_message(err, msg)
    character(kind=c_char), intent(in) :: err(ERR_CAP)
    character(len=:), allocatable, intent(out) :: msg
    integer :: i
    msg = ""
    do i = 1, ERR_CAP
       if (err(i) == c_null_char) exit
       msg = msg // err(i)
    end do
  end subroutine c_message

  ! h < 0 on failure, with msg.
  subroutine sock_listen(host, port, backlog, h, msg)
    character(len=*), intent(in) :: host
    integer, intent(in) :: port, backlog
    integer(8), intent(out) :: h
    character(len=:), allocatable, intent(out) :: msg
    character(kind=c_char) :: err(ERR_CAP)
    msg = ""
    h = cs_listen(host // c_null_char, int(port, c_int32_t), int(backlog, c_int32_t), err, int(ERR_CAP, c_int32_t))
    if (h < 0) call c_message(err, msg)
  end subroutine sock_listen

  integer function sock_local_port(h)
    integer(8), intent(in) :: h
    sock_local_port = cs_local_port(h)
  end function sock_local_port

  ! c is the connection, SOCK_TIMEOUT when ms passed first, < 0 an error.
  subroutine sock_accept(h, ms, c, msg)
    integer(8), intent(in) :: h
    integer, intent(in) :: ms
    integer(8), intent(out) :: c
    character(len=:), allocatable, intent(out) :: msg
    character(kind=c_char) :: err(ERR_CAP)
    msg = ""
    call gc_mutator_leave()
    c = cs_accept(h, int(ms, c_int32_t), err, int(ERR_CAP, c_int32_t))
    call gc_mutator_enter()
    if (c < 0 .and. c /= SOCK_TIMEOUT) call c_message(err, msg)
  end subroutine sock_accept

  subroutine sock_connect(host, port, h, msg)
    character(len=*), intent(in) :: host
    integer, intent(in) :: port
    integer(8), intent(out) :: h
    character(len=:), allocatable, intent(out) :: msg
    character(kind=c_char) :: err(ERR_CAP)
    msg = ""
    call gc_mutator_leave()
    h = cs_connect(host // c_null_char, int(port, c_int32_t), err, int(ERR_CAP, c_int32_t))
    call gc_mutator_enter()
    if (h < 0) call c_message(err, msg)
  end subroutine sock_connect

  ! n bytes into buf(1:n); 0 at the end of the stream, SOCK_TIMEOUT, or
  ! < 0 an error. buf ends on a whole UTF-8 character.
  subroutine sock_read(h, ms, buf, n, msg)
    integer(8), intent(in) :: h
    integer, intent(in) :: ms
    character(len=SOCK_BUF), intent(out) :: buf
    integer, intent(out) :: n
    character(len=:), allocatable, intent(out) :: msg
    character(kind=c_char) :: cbuf(SOCK_BUF)
    character(kind=c_char) :: err(ERR_CAP)
    integer :: i
    msg = ""
    call gc_mutator_leave()
    n = cs_read(h, cbuf, int(SOCK_BUF, c_int32_t), int(ms, c_int32_t), err, int(ERR_CAP, c_int32_t))
    call gc_mutator_enter()
    if (n > 0) then
       do i = 1, n
          buf(i:i) = cbuf(i)
       end do
    else if (n < 0 .and. n /= SOCK_TIMEOUT) then
       call c_message(err, msg)
    end if
  end subroutine sock_read

  ! ok false with msg when the peer is gone or the write fails. text is
  ! the caller's own copy: C reads it outside the running mutators.
  subroutine sock_write(h, text, ok, msg)
    integer(8), intent(in) :: h
    character(len=*), intent(in) :: text
    logical, intent(out) :: ok
    character(len=:), allocatable, intent(out) :: msg
    character(kind=c_char) :: err(ERR_CAP)
    integer(c_int32_t) :: n
    msg = ""
    call gc_mutator_leave()
    n = cs_write(h, text, int(len(text), c_int32_t), err, int(ERR_CAP, c_int32_t))
    call gc_mutator_enter()
    ok = n >= 0
    if (.not. ok) call c_message(err, msg)
  end subroutine sock_write

  subroutine sock_close(h)
    integer(8), intent(in) :: h
    integer(c_int32_t) :: r
    r = cs_close(h)
  end subroutine sock_close
end module Socket
