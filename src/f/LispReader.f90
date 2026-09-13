! LispReader: tokenizer + recursive-descent parser, text -> cons_value.
! Mirrors clojure.lang.LispReader's role. No exceptions in Fortran, so
! errors thread through module-level has_error/last_error: every routine
! checks has_error after a call that could set it and bails early.
! read_str() resets that state on entry.
module LispReader
  use values
  use PersistentList, only: list_of, list_first => first, list_rest => rest, list_count
  use PersistentVector, only: vector_empty, vector_conj, vector_count, vector_nth
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

  ! Builds each token by scanning to find its end first, then slicing
  ! the source ONCE -- not by growing an allocatable string one
  ! character at a time (cur = cur // expr(i:i)). That pattern is both
  ! O(n^2) and a real crash: repeated reallocating assignment on a
  ! long string (a multi-line docstring, confirmed via a full
  ! backtrace into the Fortran runtime's own Assign/AssignTicket) hits
  ! the same reallocating-assignment fragility already catalogued in
  ! NOTES.md, just for a plain character string instead of a
  ! cons_value array this time.
  function tokenize(expr) result(tokens)
    character(len=*), intent(in) :: expr
    type(token_t), allocatable :: tokens(:)
    type(token_t), allocatable :: buf(:)
    integer :: n, i, len_expr, start
    character :: c

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
          start = i
          i = i + 1
          do while (i <= len_expr)
             if (expr(i:i) == '"') then
                i = i + 1
                exit
             end if
             if (expr(i:i) == achar(92) .and. i < len_expr) then ! backslash escape
                i = i + 1
             end if
             i = i + 1
          end do
          n = n + 1
          buf(n)%text = expr(start:i - 1)
          cycle
       end if

       ! a run of regular characters: a symbol or a number
       start = i
       do while (i <= len_expr)
          if (.not. is_regular_char(expr(i:i))) exit
          i = i + 1
       end do
       n = n + 1
       buf(n)%text = expr(start:i - 1)
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

  ! "#?(:key1 form1 :key2 form2 ...)" reads as whichever form's key
  ! matches this host's own feature key (:cljf) or :default, first
  ! match wins -- mirrors real Clojure's reader conditionals (added in
  ! 1.7 for sharing .cljc source across clj/cljs), just with clotran
  ! as a third feature alongside :clj/:cljs rather than a real host
  ! either of those recognize. Splicing conditionals (#?@(...)) aren't
  ! supported -- nothing this project writes needs them yet.
  !
  ! "#?" isn't its own reserved token: '#' has to stay an ordinary
  ! character (not a dispatch-only special char) so a trailing '#' in
  ! an auto-gensym symbol (x#) keeps tokenizing as part of that
  ! symbol, not splitting off. "#?" only means a reader conditional
  ! when it's the WHOLE token, checked here, not via its own case in
  ! is_special_char.
  recursive function read_reader_conditional(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    integer :: n, i

    pos = pos + 1 ! consume '#?'
    if (pos > size(tokens)) then
       call reader_error("expected '(' after #?")
       return
    end if
    if (tokens(pos)%text /= "(") then
       call reader_error("expected '(' after #?")
       return
    end if
    pos = pos + 1 ! consume '('

    call read_items(tokens, pos, ")", items, n)
    if (has_error) return
    if (mod(n, 2) /= 0) then
       call reader_error("reader conditional needs an even number of forms")
       return
    end if
    do i = 1, n, 2
       if (items(i)%tag == TAG_KEYWORD) then
          if (items(i)%str_val == "cljf" .or. items(i)%str_val == "default") then
             val = items(i + 1)
             return
          end if
       end if
    end do
    call reader_error("reader conditional: no matching :cljf/:default branch")
  end function read_reader_conditional

  ! "^META FORM" attaches META directly to FORM's own metadata --
  ! real Clojure's actual reader behavior, not a wrapping (with-meta
  ! FORM META) call to be evaluated later. This matters: def/fn*'s
  ! name position is never evaluated at all (same as real Clojure), so
  ! `(def ^{:doc "..."} x 1)` needs `^{:doc "..."} x` to still read as
  ! the bare symbol x, its metadata riding along invisibly, not as an
  ! unevaluated (with-meta x {...}) list sitting where a symbol is
  ! expected. Whatever META reads as is attached as-is, with no
  ! keyword/symbol shorthand normalizing (real Clojure turns ^:static
  ! into {:static true} and ^Type into {:tag Type}) -- nothing here
  ! inspects specific metadata keys yet, so the raw value is enough.
  recursive function read_meta(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val, meta

    pos = pos + 1 ! consume '^'
    meta = read_form(tokens, pos)
    if (has_error) return
    val = read_form(tokens, pos)
    if (has_error) return
    if (allocated(val%meta_val)) deallocate(val%meta_val)
    allocate(val%meta_val)
    allocate(val%meta_val%ptr)
    val%meta_val%ptr%refcount = 1
    meta_node_total_allocated = meta_node_total_allocated + 1
    val%meta_val%ptr%val = meta
  end function read_meta

  ! Collects the forms between "pos" and "closer" into items(1:n). A
  ! subroutine with intent(out), not a function: items is allocated by a
  ! plain ALLOCATE statement here, never via "=" -- assigning a whole,
  ! not-yet-allocated array of cons_value (impure elemental
  ! assignment(=)) crashes on both compilers, same as rc_test found.
  ! Grows items geometrically (doubling) as needed, starting small --
  ! NOT pre-sized to "every token left in the whole file", which this
  ! used to do. That bound is only safe, never tight: read_items runs
  ! once per collection literal, including every nested one (a params
  ! vector, a metadata map, ...), so a file with many small nested
  ! collections spent most of its time allocating (and mostly
  ! discarding) one huge array per collection -- confirmed as the real
  ! cause of a ~17s startup loading core.clj, not the tokenizer (fixed
  ! separately) or anything evaluation-side. Growing the array here
  ! uses move_alloc, not assignment, to sidestep the reallocating-
  ! assignment fragility already in the gotchas catalog.
  recursive subroutine read_items(tokens, pos, closer, items, n)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    character(len=*), intent(in) :: closer
    type(cons_value), allocatable, intent(out) :: items(:)
    integer, intent(out) :: n
    integer :: cap
    type(cons_value), allocatable :: grown(:)

    cap = 8
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
       if (n == cap) then
          cap = cap * 2
          allocate(grown(cap))
          grown(1:n) = items(1:n)
          call move_alloc(grown, items)
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

  ! "#{a b c}" -- each element mapped to itself, same underlying
  ! storage as a hash-map (see TAG_SET in Values.f90), deduplicating
  ! same as real Clojure's set literal (a later duplicate silently
  ! overwrites, not an error).
  recursive function read_hashset(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(array_map_t) :: m
    integer :: n, i

    ! Both '#' and '{' are already consumed by read_form's dispatch
    ! before calling here -- same convention as read_hashmap, called
    ! only after its own opening '{' is consumed.
    call read_items(tokens, pos, "}", items, n)
    if (has_error) return
    m = array_map_empty()
    do i = 1, n
       m = array_map_assoc(m, items(i), items(i))
    end do
    val%tag = TAG_SET
    allocate(val%map_val)
    val%map_val = m
  end function read_hashset

  function itoa(i) result(s)
    integer, intent(in) :: i
    character(len=:), allocatable :: s
    character(len=20) :: buf
    write(buf, '(I0)') i
    s = trim(buf)
  end function itoa

  ! Recursively walks v looking for %, %N, or %& symbols -- real
  ! Clojure's #(...) anonymous-fn implicit params -- rewriting bare %
  ! to %1 so the same name bound as a param is what the body
  ! references. Tracks the highest N seen and whether %& appears, so
  ! the caller can build the matching params vector. Real Clojure
  ! gensyms fresh names instead; using the literal %1/%2/%& names
  ! directly is simpler and just as correct, since nothing outside one
  ! #(...) body could reference them anyway. Only recurses into lists
  ! and vectors -- a %-reference inside a nested {}/#{} literal within
  ! one #(...) body is vanishingly rare and not handled.
  recursive function rewrite_percent_args(v, max_n, has_amp) result(new_v)
    type(cons_value), intent(in) :: v
    integer, intent(inout) :: max_n
    logical, intent(inout) :: has_amp
    type(cons_value) :: new_v
    type(cons_ref) :: walk
    type(vec_t) :: new_vec
    integer :: i, n, num, ios

    select case (v%tag)
    case (TAG_SYMBOL)
       new_v = v
       if (allocated(v%str_val)) then
          if (v%str_val == "%") then
             new_v%str_val = "%1"
             max_n = max(max_n, 1)
          else if (v%str_val == "%&") then
             has_amp = .true.
          else if (len(v%str_val) >= 2) then
             if (v%str_val(1:1) == "%") then
                read(v%str_val(2:), *, iostat=ios) num
                if (ios == 0) max_n = max(max_n, num)
             end if
          end if
       end if
    case (TAG_LIST)
       new_v = v
       if (allocated(v%list_val)) then
          n = list_count(v%list_val)
          block
            type(cons_value), allocatable :: items(:)
            allocate(items(n))
            walk = v%list_val
            do i = 1, n
               items(i) = rewrite_percent_args(list_first(walk), max_n, has_amp)
               walk = list_rest(walk)
            end do
            new_v%list_val = list_of(items)
          end block
       end if
    case (TAG_VECTOR)
       new_v = v
       if (allocated(v%vector_val)) then
          n = vector_count(v%vector_val)
          new_vec = vector_empty()
          do i = 0, n - 1
             new_vec = vector_conj(new_vec, rewrite_percent_args(vector_nth(v%vector_val, i), max_n, has_amp))
          end do
          new_v%vector_val = new_vec
       end if
    case default
       new_v = v
    end select
  end function rewrite_percent_args

  ! "#(...)" -- (fn* [params] (...)) with implicit numbered params:
  ! bare % means %1, %2/%3/... explicit positions (a higher one
  ! implies the lower ones are params too, even if unused, same as
  ! real Clojure), %& the rest-arg. Nesting (a #(...) inside another)
  ! isn't checked for or rejected -- real Clojure refuses it; this
  ! just doesn't handle it correctly rather than erroring, a low-risk
  ! gap since nothing here writes nested ones.
  recursive function read_anon_fn(tokens, pos) result(val)
    type(token_t), intent(in) :: tokens(:)
    integer, intent(inout) :: pos
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(cons_value) :: body, rewritten_body, fn_sym, params, p, amp_sym, rest_sym
    type(cons_value) :: form_items(3)
    integer :: n, max_n, i
    logical :: has_amp
    type(vec_t) :: params_vec

    ! '#' and '(' are already consumed by read_form's dispatch.
    call read_items(tokens, pos, ")", items, n)
    if (has_error) return
    body%tag = TAG_LIST
    allocate(body%list_val)
    body%list_val = list_of(items(1:n))

    max_n = 0
    has_amp = .false.
    rewritten_body = rewrite_percent_args(body, max_n, has_amp)

    params_vec = vector_empty()
    do i = 1, max_n
       p%tag = TAG_SYMBOL
       p%str_val = "%" // itoa(i)
       params_vec = vector_conj(params_vec, p)
    end do
    if (has_amp) then
       amp_sym%tag = TAG_SYMBOL
       amp_sym%str_val = "&"
       rest_sym%tag = TAG_SYMBOL
       rest_sym%str_val = "%&"
       params_vec = vector_conj(params_vec, amp_sym)
       params_vec = vector_conj(params_vec, rest_sym)
    end if
    params%tag = TAG_VECTOR
    allocate(params%vector_val)
    params%vector_val = params_vec

    fn_sym%tag = TAG_SYMBOL
    fn_sym%str_val = "fn*"

    form_items(1) = fn_sym
    form_items(2) = params
    form_items(3) = rewritten_body
    val%tag = TAG_LIST
    allocate(val%list_val)
    val%list_val = list_of(form_items)
  end function read_anon_fn

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
    case ("#?")
       val = read_reader_conditional(tokens, pos)
    case ("#")
       ! Neither '#{' nor '#(' merge into one token the way '#?' does
       ! ('{'/'(' are special chars, breaking the regular-char run) --
       ! peek ahead.
       if (pos < size(tokens)) then
          if (tokens(pos + 1)%text == "{") then
             pos = pos + 2 ! consume '#' and '{'
             val = read_hashset(tokens, pos)
             return
          else if (tokens(pos + 1)%text == "(") then
             pos = pos + 2 ! consume '#' and '('
             val = read_anon_fn(tokens, pos)
             return
          else if (tokens(pos + 1)%text == "'") then
             ! "#'sym" is real Clojure's (var sym) shorthand -- we have
             ! no separate Var type (see NOTES.md), so this reads as
             ! (quote sym) instead: the closest sensible reader-level
             ! behavior without inventing Var semantics, not a faithful
             ! stand-in for what (var sym) actually does.
             pos = pos + 1 ! consume '#', leaving pos at the quote token
             val = read_wrapped(tokens, pos, "quote")
             return
          end if
       end if
       call reader_error("unsupported '#' syntax")
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
