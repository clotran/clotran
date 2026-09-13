! LispReader: tokenizer + recursive-descent parser, text -> cons_value.
! Mirrors clojure.lang.LispReader's role. No exceptions in Fortran, so
! errors thread through module-level has_error/last_error: every routine
! checks has_error after a call that could set it and bails early.
! read_str() resets that state on entry.
module LispReader
  use values
  use PersistentList, only: list_of
  use PersistentVector, only: vector_empty, vector_conj
  use PersistentArrayMap, only: array_map_empty, array_map_assoc
  implicit none
  private

  type :: token_t
     character(len=:), allocatable :: text
  end type token_t

  character(len=:), allocatable :: last_error
  logical :: has_error = .false.

  public :: read_str

contains

  ! ---- character classification (mirrors mal's reader regex) ----

  pure function is_whitespace(c) result(bool)
    character, intent(in) :: c
    logical :: bool
    select case (c)
    case (achar(9), achar(10), achar(11), achar(12), achar(13), achar(32), achar(44)) ! tab,lf,vt,ff,cr,space,comma
       bool = .true.
    case default
       bool = .false.
    end select
  end function is_whitespace

  pure function is_special_char(c) result(bool)
    character, intent(in) :: c
    logical :: bool
    select case (c)
    case ("[", "]", "{", "}", "(", ")", "'", "`", "~", "^", "@")
       bool = .true.
    case default
       bool = .false.
    end select
  end function is_special_char

  pure function is_regular_char(c) result(bool)
    character, intent(in) :: c
    logical :: bool
    bool = .not. (is_whitespace(c) .or. is_special_char(c) .or. c == '"' .or. c == ';')
  end function is_regular_char

  ! ---- tokenizer ----

  function tokenize(expr) result(tokens)
    character(len=*), intent(in) :: expr
    type(token_t), allocatable :: tokens(:)
    type(token_t), allocatable :: buf(:)
    integer :: n, i, len_expr
    character :: c
    character(len=:), allocatable :: cur

    len_expr = len(expr)
    allocate(buf(max(len_expr, 1)))
    n = 0
    i = 1
    do while (i <= len_expr)
       c = expr(i:i)

       if (is_whitespace(c)) then
          i = i + 1
          cycle
       end if

       if (c == ';') then
          do while (i <= len_expr)
             if (expr(i:i) == achar(10)) exit
             i = i + 1
          end do
          cycle
       end if

       if (c == '~' .and. i < len_expr) then
          if (expr(i+1:i+1) == '@') then
             n = n + 1
             buf(n)%text = "~@"
             i = i + 2
             cycle
          end if
       end if

       if (is_special_char(c)) then
          n = n + 1
          buf(n)%text = c
          i = i + 1
          cycle
       end if

       if (c == '"') then
          cur = c
          i = i + 1
          do while (i <= len_expr)
             cur = cur // expr(i:i)
             if (expr(i:i) == '"') then
                i = i + 1
                exit
             end if
             if (expr(i:i) == achar(92) .and. i < len_expr) then ! backslash escape
                i = i + 1
                cur = cur // expr(i:i)
             end if
             i = i + 1
          end do
          n = n + 1
          buf(n)%text = cur
          cycle
       end if

       ! a run of regular characters: a symbol or a number
       cur = ""
       do while (i <= len_expr)
          if (.not. is_regular_char(expr(i:i))) exit
          cur = cur // expr(i:i)
          i = i + 1
       end do
       n = n + 1
       buf(n)%text = cur
    end do

    tokens = buf(1:n)
  end function tokenize

  ! ---- atom recognition ----

  pure function looks_like_int(s) result(bool)
    character(len=*), intent(in) :: s
    logical :: bool
    integer :: i, n, start
    n = len(s)
    bool = .false.
    if (n == 0) return
    start = 1
    if (s(1:1) == '-' .or. s(1:1) == '+') start = 2
    if (start > n) return
    do i = start, n
       if (s(i:i) < '0' .or. s(i:i) > '9') return
    end do
    bool = .true.
  end function looks_like_int

  function parse_int(s) result(i)
    character(len=*), intent(in) :: s
    integer :: i
    read(s, *) i
  end function parse_int

  ! Not part of mal's own spec (mal only has integers), but real
  ! scientific values (e.g. calling into a native Fortran library) need
  ! it: optional sign, digits, a required '.', more digits.
  pure function looks_like_real(s) result(bool)
    character(len=*), intent(in) :: s
    logical :: bool
    integer :: i, n, start, dot_pos
    n = len(s)
    bool = .false.
    start = 1
    if (n > 0) then
       if (s(1:1) == '-' .or. s(1:1) == '+') start = 2
    end if
    dot_pos = 0
    do i = start, n
       if (s(i:i) == '.') then
          if (dot_pos /= 0) return ! a second '.' -- not a number
          dot_pos = i
       else if (s(i:i) < '0' .or. s(i:i) > '9') then
          return
       end if
    end do
    bool = (dot_pos /= 0 .and. dot_pos > start .and. dot_pos < n)
  end function looks_like_real

  function parse_real(s) result(r)
    character(len=*), intent(in) :: s
    real(dp) :: r
    read(s, *) r
  end function parse_real

  pure function is_terminated_string(tok) result(ok)
    character(len=*), intent(in) :: tok
    logical :: ok
    integer :: n, k, bs
    n = len(tok)
    ok = .false.
    if (n < 2) return
    if (tok(n:n) /= '"') return
    bs = 0
    k = n - 1
    do while (k >= 1)
       if (tok(k:k) /= achar(92)) exit
       bs = bs + 1
       k = k - 1
    end do
    ok = (mod(bs, 2) == 0)
  end function is_terminated_string

  function unescape_string(tok) result(s)
    character(len=*), intent(in) :: tok
    character(len=:), allocatable :: s
    integer :: i, n
    n = len(tok)
    s = ""
    i = 2 ! skip opening quote; stop before the closing quote at n
    do while (i <= n - 1)
       if (tok(i:i) == achar(92)) then
          select case (tok(i+1:i+1))
          case ('n')
             s = s // achar(10)
          case default
             s = s // tok(i+1:i+1)
          end select
          i = i + 2
       else
          s = s // tok(i:i)
          i = i + 1
       end if
    end do
  end function unescape_string

  ! ---- cons_value constructors ----

  function mk_symbol(name) result(v)
    character(len=*), intent(in) :: name
    type(cons_value) :: v
    v%tag = TAG_SYMBOL
    v%str_val = name
  end function mk_symbol

  function mk_keyword(name) result(v)
    character(len=*), intent(in) :: name
    type(cons_value) :: v
    v%tag = TAG_KEYWORD
    v%str_val = name
  end function mk_keyword

  function mk_string(text) result(v)
    character(len=*), intent(in) :: text
    type(cons_value) :: v
    v%tag = TAG_STRING
    v%str_val = text
  end function mk_string

  function mk_int(i) result(v)
    integer, intent(in) :: i
    type(cons_value) :: v
    v%tag = TAG_INT
    v%int_val = i
  end function mk_int

  function mk_real(r) result(v)
    real(dp), intent(in) :: r
    type(cons_value) :: v
    v%tag = TAG_REAL
    v%real_val = r
  end function mk_real

  function mk_bool(b) result(v)
    logical, intent(in) :: b
    type(cons_value) :: v
    v%tag = TAG_BOOL
    v%bool_val = b
  end function mk_bool

  function read_atom(tok) result(val)
    character(len=*), intent(in) :: tok
    type(cons_value) :: val
    integer :: n
    n = len(tok)

    if (looks_like_int(tok)) then
       val = mk_int(parse_int(tok))
    else if (looks_like_real(tok)) then
       val = mk_real(parse_real(tok))
    else if (tok == "nil") then
       continue ! val stays the default TAG_NIL
    else if (tok == "true") then
       val = mk_bool(.true.)
    else if (tok == "false") then
       val = mk_bool(.false.)
    else if (n >= 1) then
       if (tok(1:1) == ':') then
          val = mk_keyword(tok(2:n))
       else if (tok(1:1) == '"') then
          if (.not. is_terminated_string(tok)) then
             call reader_error("expected '""', got EOF")
          else
             val = mk_string(unescape_string(tok))
          end if
       else
          val = mk_symbol(tok)
       end if
    else
       val = mk_symbol(tok)
    end if
  end function read_atom

  ! ---- recursive-descent parser ----

  subroutine reader_error(msg)
    character(len=*), intent(in) :: msg
    if (.not. has_error) then ! keep the first error, not a later cascade
       last_error = msg
       has_error = .true.
    end if
  end subroutine reader_error

  recursive function read_wrapped(tokens, pos, sym_name) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    character(len=*), intent(in) :: sym_name
    type(cons_value) :: val
    type(cons_value) :: items(2)

    pos = pos + 1 ! consume the reader-macro token itself
    items(2) = read_form(tokens, pos)
    if (has_error) return
    items(1) = mk_symbol(sym_name)
    val%tag = TAG_LIST
    allocate(val%list_val)
    val%list_val = list_of(items)
  end function read_wrapped

  ! "^META FORM" reads as (with-meta FORM META).
  recursive function read_meta(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val
    type(cons_value) :: items(3)

    pos = pos + 1 ! consume '^'
    items(3) = read_form(tokens, pos)
    if (has_error) return
    items(2) = read_form(tokens, pos)
    if (has_error) return
    items(1) = mk_symbol("with-meta")
    val%tag = TAG_LIST
    allocate(val%list_val)
    val%list_val = list_of(items)
  end function read_meta

  ! Collects the forms between "pos" and "closer" into items(1:n). A
  ! subroutine with intent(out), not a function: items is allocated by a
  ! plain ALLOCATE statement here, never via "=" -- assigning a whole,
  ! not-yet-allocated array of cons_value (impure elemental
  ! assignment(=)) crashes on both compilers, same as rc_test found.
  recursive subroutine read_items(tokens, pos, closer, items, n)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    character(len=*), intent(in) :: closer
    type(cons_value), allocatable, intent(out) :: items(:)
    integer, intent(out) :: n
    integer :: cap

    ! Tokens left is always a safe upper bound on item count.
    cap = max(size(tokens) - pos + 1, 1)
    allocate(items(cap))
    n = 0
    do
       if (pos > size(tokens)) then
          call reader_error("expected '" // closer // "', got EOF")
          return
       end if
       if (tokens(pos)%text == closer) then
          pos = pos + 1
          exit
       end if
       n = n + 1
       items(n) = read_form(tokens, pos)
       if (has_error) return
    end do
  end subroutine read_items

  recursive function read_list(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    integer :: n

    call read_items(tokens, pos, ")", items, n)
    if (has_error) return
    val%tag = TAG_LIST
    allocate(val%list_val)
    val%list_val = list_of(items(1:n))
  end function read_list

  recursive function read_vector(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(vec_t) :: vec
    integer :: n, i

    call read_items(tokens, pos, "]", items, n)
    if (has_error) return
    vec = vector_empty()
    do i = 1, n
       vec = vector_conj(vec, items(i))
    end do
    val%tag = TAG_VECTOR
    allocate(val%vector_val)
    val%vector_val = vec
  end function read_vector

  recursive function read_hashmap(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(array_map_t) :: m
    integer :: n, i

    call read_items(tokens, pos, "}", items, n)
    if (has_error) return
    if (mod(n, 2) /= 0) then
       call reader_error("hash-map literal needs an even number of forms")
       return
    end if
    m = array_map_empty()
    do i = 1, n, 2
       m = array_map_assoc(m, items(i), items(i + 1))
    end do
    val%tag = TAG_HASHMAP
    allocate(val%map_val)
    val%map_val = m
  end function read_hashmap

  recursive function read_form(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val
    character(len=:), allocatable :: t

    if (pos > size(tokens)) then
       call reader_error("unexpected EOF")
       return
    end if

    t = tokens(pos)%text
    select case (t)
    case ("(")
       pos = pos + 1
       val = read_list(tokens, pos)
    case ("[")
       pos = pos + 1
       val = read_vector(tokens, pos)
    case ("{")
       pos = pos + 1
       val = read_hashmap(tokens, pos)
    case (")", "]", "}")
       call reader_error("unexpected '" // t // "'")
    case ("'")
       val = read_wrapped(tokens, pos, "quote")
    case ("`")
       val = read_wrapped(tokens, pos, "quasiquote")
    case ("~")
       val = read_wrapped(tokens, pos, "unquote")
    case ("~@")
       val = read_wrapped(tokens, pos, "splice-unquote")
    case ("@")
       val = read_wrapped(tokens, pos, "deref")
    case ("^")
       val = read_meta(tokens, pos)
    case default
       val = read_atom(t)
       pos = pos + 1
    end select
  end function read_form

  ! Reads the first form out of `input`. error == "empty input" means a
  ! blank/comment-only line, not a real syntax error -- callers usually
  ! just reprompt for that instead of reporting it.
  function read_str(input, ast, error) result(ok)
    character(len=*), intent(in) :: input
    type(cons_value), intent(out) :: ast
    character(len=:), allocatable, intent(out) :: error
    logical :: ok
    type(token_t), allocatable :: tokens(:)
    integer :: pos

    has_error = .false.
    last_error = ""

    tokens = tokenize(input)
    if (size(tokens) == 0) then
       ok = .false.
       error = "empty input"
       return
    end if

    pos = 1
    ast = read_form(tokens, pos)
    if (has_error) then
       ok = .false.
       error = last_error
    else
       ok = .true.
       error = ""
    end if
  end function read_str

end module LispReader
