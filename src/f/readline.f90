module mal_readline
  use iso_fortran_env, only: iostat_end
  implicit none
contains
  ! https://stackoverflow.com/questions/31084087/using-a-deferred-length-character-string-to-read-user-input
  !
  ! at_eof distinguishes real end-of-file from an ordinary end-of-record
  ! (a normal line terminator) -- both give a negative iostat from a
  ! non-advancing read, but only iostat_end means "no more input at
  ! all". Without this, a caller can't tell "the user typed an empty
  ! line" from "stdin is closed", which is exactly what let the REPL
  ! loop forever re-prompting after EOF instead of stopping.
  subroutine readline(unit, line, at_eof)
    ! The unit, connected for formatted input, to read the record from.
    integer, intent(in) :: unit
    ! the contents of the record.
    character(:), intent(out), allocatable :: line
    logical, intent(out) :: at_eof

    integer :: stat           ! io statement iostat result.
    character(256) :: buffer  ! buffer to read a piece of the record.
    integer :: size           ! number of characters read from the file.
    !***
    line = ''
    at_eof = .false.
    do
       read (unit, "(a)", advance='no', iostat=stat, size=size) buffer
       if (stat > 0) stop 'error reading file.'
       line = line // buffer(:size)
       if (stat == iostat_end) then
          at_eof = .true.
          return
       end if
       ! an end of record condition stops the loop -- a real line, done.
       if (stat < 0) return
    end do
  end subroutine readline
end module mal_readline
