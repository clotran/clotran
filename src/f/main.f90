module core
  use mal_readline, only: readline
  use values
  use Env, only: env_ref, assignment(=)
  use printer, only: pr_str
  use LispReader, only: read_str
  use Eval, only: eval_top
  implicit none

  integer :: input_unit = 5
  integer :: output_unit = 6

contains

  recursive subroutine interactive_repl(env)
    type(env_ref), intent(in) :: env
    character(len=:), allocatable :: exp
    type(cons_value) :: ast, val
    character(len=:), allocatable :: err
    logical :: ok
    logical :: at_eof

    write(output_unit, "(A)", advance='no') "user> "
    call readline(input_unit, exp, at_eof)
    if (at_eof) stop
    if (exp == "quit" .or. exp == "exit" .or. exp == "(quit)" .or. exp == "(exit)") then
       stop
    end if

    ok = read_str(exp, ast, err)
    if (ok) then
       val = eval_top(ast, env, err)
       if (len(err) > 0) then
          write(output_unit, '(A)') "Error: " // err
       else
          write(output_unit, '(A)') pr_str(val)
       end if
    else if (err /= "empty input") then
       write(output_unit, '(A)') "Error: " // err
    end if

    call interactive_repl(env)
  end subroutine interactive_repl
end module core

program repl
  use core, only: interactive_repl
  use Eval, only: repl_env
  use Env, only: env_ref, assignment(=)
  implicit none
  type(env_ref) :: env
  env = repl_env()
  call interactive_repl(env)
end program repl
