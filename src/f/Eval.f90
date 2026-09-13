! Eval: the tree-walking interpreter loop (eval/apply) plus def!/let*.
! No exceptions in Fortran, so errors thread through module-level
! has_error/last_error_value, same pattern as LispReader: every routine
! checks has_error after a call that could set it and bails early.
! try/catch (step9) is what actually catches last_error_value; eval_top
! resets state on entry and is the last-resort catch at the top level.
module Eval
  use values
  use Env
  use PersistentList, only: list_first => first, list_rest => rest, list_count, list_of
  use PersistentVector, only: vector_count, vector_nth, vector_conj, vector_empty
  use PersistentArrayMap, only: array_map_empty, array_map_count, array_map_nth_key, &
       array_map_nth_val, array_map_assoc, array_map_contains, array_map_dissoc
  use RT, only: rt_get => get, rt_nth => nth, rt_assoc => assoc, rt_count => count, &
       rt_first => first, rt_rest => rest, rt_cons => cons, rt_conj => conj, rt_equiv => equiv, &
       rt_seq => seq, rt_next => next
  use Numbers, only: num_add, num_sub, num_mul, num_div, num_lt, num_gt, num_le, num_ge
  use printer, only: pr_str
  use Atom, only: atom_new, atom_p, atom_deref, atom_reset
  use LispReader, only: read_str
  use mal_readline, only: sys_readline => readline
  use Namespace, only: ns_ref, assignment(=), CORE_NS, ns_find_or_create, ns_intern, &
       ns_resolve, ns_set_current, ns_current, ns_name_of
  implicit none
  private

  ! Any value can be thrown/caught (a string, a hash-map, anything) --
  ! not just an error message -- so the error state holds a real
  ! cons_value, not a string. Internal errors (symbol not found, etc.)
  ! wrap their message as a TAG_STRING value, matching what catches a
  ! real (throw "msg") would see.
  type(cons_value) :: last_error_value
  logical :: has_error = .false.

  ! Auto-gensym state for one (quasiquote ...) call: every `x#` maps to
  ! the same generated symbol within that one call, reset before each
  ! top-level quasiquote. No nesting-depth tracking (a syntax-quote
  ! inside a syntax-quote doesn't get its own scope, unlike real
  ! Clojure) -- a deliberate simplification, see NOTES.md.
  type :: gensym_entry
     character(len=:), allocatable :: original, generated
  end type gensym_entry
  type(gensym_entry), allocatable :: gensym_table(:)
  integer :: gensym_count = 0
  integer :: gensym_counter = 0

  public :: eval_top, repl_env

contains

  function builtin(name) result(v)
    character(len=*), intent(in) :: name
    type(cons_value) :: v
    v%tag = TAG_BUILTIN
    v%str_val = name
  end function builtin

  ! clotran.native holds every builtin under its own name, alongside
  ! clojure.core -- the direct structural analogue of clojure.lang.RT,
  ! real Clojure's own native layer underneath clojure.core. core.cljc
  ! (importing real clojure/core.clj) needs this: that file's own
  ! `(def first ...)` etc. will redefine clojure.core's binding
  ! entirely once patched, so anything wanting the fast native path
  ! from then on reaches it via clotran.native/first, not first.
  function repl_env() result(env)
    type(env_ref) :: env
    type(ns_ref) :: core, native
    type(cons_value) :: no_args(0)

    env = env_new() ! empty: the top-level lexical frame has no locals

    core = ns_find_or_create(CORE_NS)
    native = ns_find_or_create("clotran.native")
    call reg("+")
    call reg("-")
    call reg("*")
    call reg("/")
    call reg("first")
    call reg("rest")
    call reg("cons")
    call reg("conj")
    call reg("nth")
    call reg("count")
    call reg("get")
    call reg("assoc")
    call reg("list")
    call reg("vector")
    call reg("concat")
    call reg("=")
    call reg(">")
    call reg(">=")
    call reg("<")
    call reg("<=")
    call reg("list?")
    call reg("empty?")
    call reg("prn")
    call reg("read-string")
    call reg("slurp")
    call reg("atom")
    call reg("atom?")
    call reg("deref")
    call reg("reset!")
    call reg("swap!")
    call reg("macroexpand")
    call reg("throw")
    call reg("apply")
    call reg("map")
    call reg("symbol?")
    call reg("nil?")
    call reg("true?")
    call reg("false?")
    call reg("readline")
    call reg("keyword?")
    call reg("vector?")
    call reg("map?")
    call reg("sequential?")
    call reg("symbol")
    call reg("keyword")
    call reg("hash-map")
    call reg("contains?")
    call reg("keys")
    call reg("vals")
    call reg("dissoc")
    call reg("str")
    call reg("pr-str")
    call reg("println")
    call reg("number?")
    call reg("string?")
    call reg("fn?")
    call reg("macro?")
    call reg("seq")
    call reg("time-ms")
    call reg("with-meta")
    call reg("meta")
    call ns_intern(core, "*ARGV*", make_list(no_args))
    block
      type(cons_value) :: host_lang
      host_lang%tag = TAG_STRING
      host_lang%str_val = "Fortran"
      call ns_intern(core, "*host-language*", host_lang)
    end block

    ! The start of a real self-hosted core: not/cond are written in
    ! this language itself (using defmacro/quasiquote), not native
    ! Fortran, exactly like real clojure.core's own cond. Evaluated
    ! into clojure.core directly, matching where the native builtins
    ! above live.
    call ns_set_current(core)
    call eval_core_bootstrap(env)
    call ns_set_current(ns_find_or_create("user"))
  contains
    subroutine reg(name)
      character(len=*), intent(in) :: name
      call ns_intern(core, name, builtin(name))
      call ns_intern(native, name, builtin(name))
    end subroutine reg
  end function repl_env

  ! Real clojure.core lives in src/cljc/core.cljc as an actual file,
  ! not a string literal -- loaded the ordinary way, through load-file
  ! itself. Resolved relative to argv[0]'s own directory, not cwd
  ! (there's no installed-resource concept yet, but this at least
  ! survives a caller changing directories before invoking us, e.g.
  ! the regression suite's --rundir).
  subroutine eval_core_bootstrap(env)
    type(env_ref), intent(in) :: env
    type(cons_value) :: ast, discard
    character(len=:), allocatable :: err, core_path, src
    logical :: ok
    core_path = exe_relative_path("src/cljc/core.cljc")
    src = '(load-file "' // core_path // '")'
    ok = read_str(src, ast, err)
    if (ok) discard = eval_form(ast, env)
    if (has_error) then
       write(*, '(A)') "warning: core.cljc failed to load: " // pr_str(last_error_value)
       has_error = .false.
    end if
  end subroutine eval_core_bootstrap

  ! rel resolved against argv[0]'s own directory (e.g. "../../clotran-bin"
  ! invoked from elsewhere still finds sibling files correctly) rather
  ! than the process's cwd.
  function exe_relative_path(rel) result(full)
    character(len=*), intent(in) :: rel
    character(len=:), allocatable :: full, exe_path
    integer :: n, slash_pos
    call get_command_argument(0, length=n)
    allocate(character(len=n) :: exe_path)
    call get_command_argument(0, exe_path)
    slash_pos = index(exe_path, "/", back=.true.)
    if (slash_pos > 0) then
       full = exe_path(1:slash_pos) // rel
    else
       full = rel
    end if
  end function exe_relative_path

  subroutine eval_error(msg)
    character(len=*), intent(in) :: msg
    type(cons_value) :: v
    if (has_error) return
    v%tag = TAG_STRING
    v%str_val = msg
    call throw_value(v)
  end subroutine eval_error

  ! (throw x): x is already evaluated by the time this runs (throw is
  ! an ordinary builtin, not a special form -- real Clojure's is a
  ! function too, which is exactly what lets it be passed around as a
  ! value, e.g. (map throw (list "err"))).
  subroutine throw_value(v)
    type(cons_value), intent(in) :: v
    if (has_error) return
    last_error_value = v
    has_error = .true.
  end subroutine throw_value

  ! Entry point: resets error state, then evaluates ast in env. error is
  ! "" on success, otherwise the thrown/error value's printed form.
  function eval_top(ast, env, error) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    character(len=:), allocatable, intent(out) :: error
    type(cons_value) :: val
    has_error = .false.
    val = eval_form(ast, env)
    if (has_error) then
       error = pr_str(last_error_value)
    else
       error = ""
    end if
  end function eval_top

  ! The interpreter loop. Tail positions (if's chosen branch, do's last
  ! form, let*'s body, and calling a closure) rebind ast/env and loop
  ! instead of recursing -- so (sum2 10000 0) runs in constant Fortran
  ! stack, not 10000 nested calls. Only non-tail work (argument
  ! expressions, let*'s bindings, if's condition) is a real recursive
  ! eval_form call.
  recursive function eval_form(ast0, env0) result(val)
    type(cons_value), intent(in) :: ast0
    type(env_ref), intent(in) :: env0
    type(cons_value) :: val
    type(cons_value) :: ast, nilv
    type(env_ref) :: env
    type(cons_value) :: head, cond, macro_val
    type(cons_value), allocatable :: args(:)
    type(cons_ref) :: l, forms
    integer :: n, i

    ast = ast0
    env = env0

    do
       select case (ast%tag)
       case (TAG_SYMBOL)
          val = eval_symbol(ast, env)
          return
       case (TAG_VECTOR)
          val = eval_vector(ast, env)
          return
       case (TAG_HASHMAP)
          val = eval_hashmap(ast, env)
          return
       case (TAG_LIST)
          ! handled below
       case default
          val = ast ! self-evaluating: int/real/bool/nil/string/keyword
          return
       end select

       n = 0
       if (allocated(ast%list_val)) n = list_count(ast%list_val)
       if (n == 0) then
          val = ast
          return
       end if

       head = list_first(ast%list_val)
       if (head%tag == TAG_SYMBOL) then
          if (head%str_val == "def!" .or. head%str_val == "def") then
             val = eval_def(ast, env)
             return
          else if (head%str_val == "defmacro") then
             val = eval_defmacro(ast, env)
             return
          else if (head%str_val == "defmacro!") then
             ! Purely a mal-test-suite compatibility shim: mal's own
             ! spec writes (defmacro! name (fn* (params) body)) instead
             ! of real Clojure's (defmacro name [params] body). Not
             ! meaningful Clojure -- just an artifact of the tests.
             val = eval_defmacro_bang(ast, env)
             return
          else if (head%str_val == "quote") then
             val = list_first(list_rest(ast%list_val))
             return
          else if (head%str_val == "fn*") then
             val = eval_fn(ast, env)
             return
          else if (head%str_val == "let*") then
             call eval_let_head(ast, env) ! rebinds ast/env to (child env, body); tail
             if (has_error) return
             cycle
          else if (head%str_val == "if") then
             forms = list_rest(ast%list_val)
             cond = eval_form(list_first(forms), env)
             if (has_error) return
             forms = list_rest(forms)
             if (.not. (cond%tag == TAG_NIL .or. (cond%tag == TAG_BOOL .and. .not. cond%bool_val))) then
                ast = list_first(forms)
             else
                forms = list_rest(forms)
                if (list_count(forms) > 0) then
                   ast = list_first(forms)
                else
                   val = nilv
                   return
                end if
             end if
             cycle
          else if (head%str_val == "do") then
             forms = list_rest(ast%list_val)
             n = list_count(forms)
             if (n == 0) then
                val = nilv
                return
             end if
             do i = 1, n - 1
                val = eval_form(list_first(forms), env)
                if (has_error) return
                forms = list_rest(forms)
             end do
             ast = list_first(forms)
             cycle
          else if (head%str_val == "eval") then
             ! No lexical locals -- eval always resolves symbols purely
             ! through *ns*, ignoring whatever let*/fn* frame this call
             ! happened in. *ns* itself is already global, not part of
             ! env, so there's nothing to "reset" beyond dropping locals.
             ast = eval_form(list_first(list_rest(ast%list_val)), env)
             if (has_error) return
             env = env_new()
             cycle
          else if (head%str_val == "load-file") then
             call eval_load_file_head(ast, env)
             if (has_error) return
             cycle
          else if (head%str_val == "in-ns") then
             val = eval_in_ns(ast, env)
             return
          else if (head%str_val == "quasiquote") then
             call gensym_reset()
             val = qq_expand(list_first(list_rest(ast%list_val)), env)
             return
          else if (head%str_val == "try*" .or. head%str_val == "try") then
             val = eval_try(ast, env)
             return
          else if (resolves_to_macro(head%str_val, macro_val)) then
             ! Macros are namespace-level only, never lexically bound
             ! (real Clojure: macro-ness is Var metadata, never a local),
             ! so this checks *ns* directly, not env. Unevaluated arg
             ! forms in, expansion evaluated in the CALLING env -- tail,
             ! so a recursive macro like cond gets TCO too.
             call eval_macro_head(ast, macro_val)
             if (has_error) return
             cycle
          end if
       end if

       if (allocated(args)) deallocate(args)
       allocate(args(n))
       l = ast%list_val
       do i = 1, n
          args(i) = eval_form(list_first(l), env)
          if (has_error) return
          l = list_rest(l)
       end do
       if (args(1)%tag == TAG_FN) then
          ! tail call into a closure: no Fortran recursion here, loop instead
          env = env_new(args(1)%fn_val%env)
          call bind_params(args(1)%fn_val%params, args(2:n), env)
          ast = args(1)%fn_val%body
          deallocate(args)
          cycle
       else
          val = apply_fn(args(1), args(2:n))
          return
       end if
    end do
  end function eval_form

  ! let*'s env/body computation, factored out of eval_form only because
  ! a function can't rebind its own dummy arguments -- ast/env here are
  ! the caller's locals, passed by reference and mutated in place.
  subroutine eval_let_head(ast, env)
    type(cons_value), intent(inout) :: ast
    type(env_ref), intent(inout) :: env
    type(cons_value) :: bindings, k, v
    integer :: n, i

    bindings = list_first(list_rest(ast%list_val))
    n = binding_count(bindings)
    if (mod(n, 2) /= 0) then
       call eval_error("let* requires an even number of binding forms")
       return
    end if

    env = env_new(env)
    do i = 0, n - 1, 2
       k = binding_nth(bindings, i)
       v = eval_form(binding_nth(bindings, i + 1), env)
       if (has_error) return
       call env_set(env, k, v)
    end do
    ast = list_first(list_rest(list_rest(ast%list_val)))
  end subroutine eval_let_head

  ! (load-file "path"): slurps the file, wraps it in (do ... nil), and
  ! hands off with no lexical locals -- same rule as eval, since
  ! load-file is just eval+read-string+slurp composed.
  subroutine eval_load_file_head(ast, env)
    type(cons_value), intent(inout) :: ast
    type(env_ref), intent(inout) :: env
    type(cons_value) :: fname, contents, wrapped
    character(len=:), allocatable :: src, err
    logical :: ok

    fname = eval_form(list_first(list_rest(ast%list_val)), env)
    if (has_error) return
    contents = builtin_slurp([fname])
    if (has_error) return
    ! A newline (not a space) before the closing "nil)" -- a file ending
    ! in a comment line, with no trailing newline of its own, would
    ! otherwise swallow "nil)" into that comment (real mal's own
    ! load-file does exactly this for the same reason).
    src = "(do " // contents%str_val // achar(10) // "nil)"
    ok = read_str(src, wrapped, err)
    if (.not. ok) then
       call eval_error("load-file: " // err)
       return
    end if
    ast = wrapped
    env = env_new()
  end subroutine eval_load_file_head

  ! (in-ns 'name): switches *ns*, creating it (auto-referring
  ! clojure.core) if it doesn't exist yet. Real Clojure's `ns` macro
  ! (with :require/:import) waits for step8 -- this is the primitive
  ! it's built from.
  function eval_in_ns(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: name

    name = eval_form(list_first(list_rest(ast%list_val)), env)
    if (has_error) return
    call ns_set_current(ns_find_or_create(name%str_val))
    val = name
  end function eval_in_ns

  ! (try body) or (try body (catch e handler)): real Clojure's own
  ! names (mal's try*/catch* also recognized, same as def!/def). Only
  ! one catch clause, catching anything -- no exception-class matching
  ! (we have no class hierarchy to match against). Not tail-cycled:
  ! try/catch isn't the hot recursive path TCO exists for.
  function eval_try(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: body, catch_clause, catch_sym, catch_body
    type(env_ref) :: catch_env

    body = list_first(list_rest(ast%list_val))
    val = eval_form(body, env)
    if (.not. has_error) return
    if (list_count(list_rest(list_rest(ast%list_val))) == 0) return ! no catch: propagate

    catch_clause = list_first(list_rest(list_rest(ast%list_val)))
    catch_sym = list_first(list_rest(catch_clause%list_val))
    catch_body = list_first(list_rest(list_rest(catch_clause%list_val)))

    catch_env = env_new(env)
    call env_set(catch_env, catch_sym, last_error_value)
    has_error = .false. ! caught
    val = eval_form(catch_body, catch_env)
  end function eval_try

  ! (defmacro name [params] body): real Clojure's actual syntax (not
  ! mal's (defmacro! name (fn* (params) body))) -- a macro is an
  ! ordinary closure (TAG_FN) with is_macro set, interned in *ns* under
  ! name, same as def.
  function eval_defmacro(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: name

    name = list_first(list_rest(ast%list_val))
    val%tag = TAG_FN
    allocate(val%fn_val)
    val%fn_val%params = list_first(list_rest(list_rest(ast%list_val)))
    val%fn_val%body = wrap_body(list_rest(list_rest(list_rest(ast%list_val))))
    val%fn_val%env = env
    val%fn_val%is_macro = .true.
    call ns_intern(ns_current(), name%str_val, val)
  end function eval_defmacro

  ! (defmacro! name expr): mal's own calling convention -- expr is
  ! evaluated (typically a (fn* ...) closure) and the result's is_macro
  ! is set, exactly like def! but marking it a macro. A test-suite
  ! compatibility shim, not real Clojure syntax -- see eval_defmacro
  ! above for the actual thing.
  function eval_defmacro_bang(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: name

    name = list_first(list_rest(ast%list_val))
    val = eval_form(list_first(list_rest(list_rest(ast%list_val))), env)
    if (has_error) return
    if (allocated(val%fn_val)) val%fn_val%is_macro = .true.
    call ns_intern(ns_current(), name%str_val, val)
  end function eval_defmacro_bang

  ! Macros are namespace-level constructs only in real Clojure (Var
  ! metadata), never lexically bound -- so this checks *ns* directly,
  ! not the lexical env, unlike ordinary symbol resolution.
  function resolves_to_macro(name, macro_val) result(is_macro)
    character(len=*), intent(in) :: name
    type(cons_value), intent(out) :: macro_val
    logical :: is_macro
    character(len=:), allocatable :: owner
    is_macro = ns_resolve(ns_current(), name, macro_val, owner)
    if (is_macro) is_macro = (macro_val%tag == TAG_FN)
    if (is_macro) is_macro = allocated(macro_val%fn_val)
    if (is_macro) is_macro = macro_val%fn_val%is_macro
  end function resolves_to_macro

  ! Expands one macro call: binds its params to the call's raw,
  ! unevaluated argument forms (in the macro's own captured env, not
  ! the caller's), then evaluates its body to produce the expansion.
  ! Rebinds ast in place -- callers evaluate the expansion themselves
  ! (in eval_form's loop, in the calling env, tail; in macroexpand,
  ! by looping this again).
  subroutine eval_macro_head(ast, macro_val)
    type(cons_value), intent(inout) :: ast
    type(cons_value), intent(in) :: macro_val
    type(cons_value), allocatable :: raw_args(:)
    type(env_ref) :: child
    type(cons_ref) :: l
    integer :: n, i

    n = list_count(ast%list_val) - 1
    allocate(raw_args(n))
    l = list_rest(ast%list_val)
    do i = 1, n
       raw_args(i) = list_first(l)
       l = list_rest(l)
    end do
    child = env_new(macro_val%fn_val%env)
    call bind_params(macro_val%fn_val%params, raw_args, child)
    ast = eval_form(macro_val%fn_val%body, child)
  end subroutine eval_macro_head

  ! (macroexpand form): an ordinary function in real Clojure, not a
  ! special form like mal's -- its argument is evaluated normally, so
  ! callers quote the form themselves ((macroexpand '(unless2 1 2 3))),
  ! same as real Clojure. Expands repeatedly until the head is no
  ! longer a macro call (matching macroexpand, not macroexpand-1).
  recursive function builtin_macroexpand(form0) result(val)
    type(cons_value), intent(in) :: form0
    type(cons_value) :: val
    type(cons_value) :: form, head2, macro_val

    form = form0
    do
       if (form%tag /= TAG_LIST) exit
       if (.not. allocated(form%list_val)) exit
       if (list_count(form%list_val) == 0) exit
       head2 = list_first(form%list_val)
       if (head2%tag /= TAG_SYMBOL) exit
       if (.not. resolves_to_macro(head2%str_val, macro_val)) exit
       call eval_macro_head(form, macro_val)
       if (has_error) exit
    end do
    val = form
  end function builtin_macroexpand

  ! Special-form names never get namespace-qualified or auto-gensym'd
  ! by quasiquote -- they're recognized syntactically here, never
  ! stored in any namespace, so there's nothing to qualify them with.
  function is_special_form(name) result(yes)
    character(len=*), intent(in) :: name
    logical :: yes
    select case (name)
    case ("def!", "def", "defmacro", "defmacro!", "let*", "fn*", "if", "do", "quote", "quasiquote", &
         "unquote", "splice-unquote", "eval", "load-file", "in-ns", "try*", "try", "catch*", "catch")
       yes = .true.
    case default
       yes = .false.
    end select
  end function is_special_form

  function mk_symbol(name) result(v)
    character(len=*), intent(in) :: name
    type(cons_value) :: v
    v%tag = TAG_SYMBOL
    v%str_val = name
  end function mk_symbol

  subroutine gensym_reset()
    if (allocated(gensym_table)) deallocate(gensym_table)
    gensym_count = 0
  end subroutine gensym_reset

  ! Same generated symbol for the same base name within one (quasiquote
  ! ...) call (gensym_table isn't reset in between), a fresh one the
  ! next time -- exactly what macro hygiene needs `x#` for.
  function gensym_for(base) result(sym)
    character(len=*), intent(in) :: base
    type(cons_value) :: sym
    integer :: i
    character(len=20) :: n
    do i = 1, gensym_count
       if (gensym_table(i)%original == base) then
          sym = mk_symbol(gensym_table(i)%generated)
          return
       end if
    end do
    gensym_counter = gensym_counter + 1
    write(n, '(I0)') gensym_counter
    call gensym_push(base, base // "__" // trim(n) // "__auto__")
    sym = mk_symbol(gensym_table(gensym_count)%generated)
  end function gensym_for

  subroutine gensym_push(original, generated)
    character(len=*), intent(in) :: original, generated
    type(gensym_entry), allocatable :: new_table(:)
    integer :: i
    allocate(new_table(gensym_count + 1))
    do i = 1, gensym_count
       new_table(i) = gensym_table(i)
    end do
    new_table(gensym_count + 1)%original = original
    new_table(gensym_count + 1)%generated = generated
    call move_alloc(new_table, gensym_table)
    gensym_count = gensym_count + 1
  end subroutine gensym_push

  ! A bare symbol inside quasiquote: auto-gensym if it ends in '#',
  ! otherwise namespace-qualify it -- using ns_resolve's owner so `+`
  ! from within `user` qualifies as clojure.core/+, not user/+.
  function qq_symbol(sym) result(v)
    type(cons_value), intent(in) :: sym
    type(cons_value) :: v
    character(len=:), allocatable :: name, owner
    type(cons_value) :: resolved
    logical :: found

    name = sym%str_val
    if (is_special_form(name)) then
       v = sym
       return
    end if
    if (len(name) > 1) then
       if (name(len(name):len(name)) == "#") then
          v = gensym_for(name(1:len(name)-1))
          return
       end if
    end if
    if (index(name, "/") > 0) then
       v = sym ! already qualified
       return
    end if
    found = ns_resolve(ns_current(), name, resolved, owner)
    if (found) then
       v = mk_symbol(owner // "/" // name)
    else
       v = mk_symbol(ns_name_of(ns_current()) // "/" // name)
    end if
  end function qq_symbol

  function is_splice_unquote(e) result(yes)
    type(cons_value), intent(in) :: e
    logical :: yes
    type(cons_value) :: h
    yes = .false.
    if (e%tag /= TAG_LIST) return
    if (.not. allocated(e%list_val)) return
    if (list_count(e%list_val) /= 2) return
    h = list_first(e%list_val)
    yes = (h%tag == TAG_SYMBOL .and. h%str_val == "splice-unquote")
  end function is_splice_unquote

  ! Grows items by one, pre-allocating the new array before assigning
  ! into it -- see the refcounting gotchas in NOTES.md for why a naive
  ! `items = [items, v]` on an array of cons_value isn't safe.
  subroutine qq_push(items, n, v)
    type(cons_value), allocatable, intent(inout) :: items(:)
    integer, intent(inout) :: n
    type(cons_value), intent(in) :: v
    type(cons_value), allocatable :: new_items(:)
    integer :: i
    allocate(new_items(n + 1))
    do i = 1, n
       new_items(i) = items(i)
    end do
    new_items(n + 1) = v
    call move_alloc(new_items, items)
    n = n + 1
  end subroutine qq_push

  recursive subroutine qq_append_all(items, n, coll)
    type(cons_value), allocatable, intent(inout) :: items(:)
    integer, intent(inout) :: n
    type(cons_value), intent(in) :: coll
    type(cons_value) :: s
    s = rt_seq(coll)
    do while (s%tag == TAG_LIST)
       call qq_push(items, n, rt_first(s))
       s = rt_next(s)
    end do
  end subroutine qq_append_all

  ! Real Clojure syntax-quote: recursively builds the quoted structure,
  ! evaluating (unquote x) and splicing (splice-unquote x)'s elements
  ! in, qualifying/gensym-ing plain symbols along the way (qq_symbol).
  ! Vectors stay vectors (unlike mal's own reference impls, which
  ! produce a list for a quasiquoted vector -- a known, TODO-marked
  ! limitation in mal's own test suite that a real implementation
  ! doesn't need to inherit).
  recursive function qq_expand(form, env) result(val)
    type(cons_value), intent(in) :: form
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(cons_value) :: no_items(0)
    type(array_map_t) :: m
    type(cons_ref) :: l
    type(cons_value) :: e, head_e
    integer :: n, i, item_count

    select case (form%tag)
    case (TAG_SYMBOL)
       val = qq_symbol(form)
    case (TAG_LIST)
       n = 0
       if (allocated(form%list_val)) n = list_count(form%list_val)
       if (n == 2) then
          head_e = list_first(form%list_val)
          if (head_e%tag == TAG_SYMBOL .and. head_e%str_val == "unquote") then
             val = eval_form(list_first(list_rest(form%list_val)), env)
             return
          end if
       end if
       item_count = 0
       l = form%list_val
       do i = 1, n
          e = list_first(l)
          if (is_splice_unquote(e)) then
             call qq_append_all(items, item_count, eval_form(list_first(list_rest(e%list_val)), env))
          else
             call qq_push(items, item_count, qq_expand(e, env))
          end if
          if (has_error) return
          l = list_rest(l)
       end do
       if (item_count == 0) then
          val = make_list(no_items)
       else
          val = make_list(items(1:item_count))
       end if
    case (TAG_VECTOR)
       n = 0
       if (allocated(form%vector_val)) n = vector_count(form%vector_val)
       item_count = 0
       do i = 0, n - 1
          e = vector_nth(form%vector_val, i)
          if (is_splice_unquote(e)) then
             call qq_append_all(items, item_count, eval_form(list_first(list_rest(e%list_val)), env))
          else
             call qq_push(items, item_count, qq_expand(e, env))
          end if
          if (has_error) return
       end do
       if (item_count == 0) then
          val = make_vector(no_items)
       else
          val = make_vector(items(1:item_count))
       end if
    case (TAG_HASHMAP)
       n = 0
       if (allocated(form%map_val)) n = array_map_count(form%map_val)
       m = array_map_empty()
       do i = 0, n - 1
          m = array_map_assoc(m, qq_expand(array_map_nth_key(form%map_val, i), env), &
               qq_expand(array_map_nth_val(form%map_val, i), env))
          if (has_error) return
       end do
       val%tag = TAG_HASHMAP
       allocate(val%map_val)
       val%map_val = m
    case default
       val = form ! self-evaluating
    end select
  end function qq_expand

  ! Lexical locals (let*/fn* params) first, then namespace resolution
  ! (this namespace's own bindings, falling back to clojure.core) --
  ! def! always lands in the namespace, never the lexical env, so it's
  ! visible here regardless of how deeply nested the lookup site is.
  function eval_symbol(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    logical :: found
    character(len=:), allocatable :: owner
    found = env_find(env, ast, val)
    if (.not. found) found = ns_resolve(ns_current(), ast%str_val, val, owner)
    if (.not. found) call eval_error("'" // ast%str_val // "' not found")
  end function eval_symbol

  recursive function eval_vector(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(vec_t) :: vec
    integer :: i, n

    n = 0
    if (allocated(ast%vector_val)) n = vector_count(ast%vector_val)
    vec = vector_empty()
    do i = 0, n - 1
       vec = vector_conj(vec, eval_form(vector_nth(ast%vector_val, i), env))
       if (has_error) return
    end do
    val%tag = TAG_VECTOR
    allocate(val%vector_val)
    val%vector_val = vec
  end function eval_vector

  ! Keys stay literal; values are evaluated, same as a vector literal.
  recursive function eval_hashmap(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(array_map_t) :: m
    integer :: i, n

    n = 0
    if (allocated(ast%map_val)) n = array_map_count(ast%map_val)
    m = array_map_empty()
    do i = 0, n - 1
       m = array_map_assoc(m, array_map_nth_key(ast%map_val, i), &
            eval_form(array_map_nth_val(ast%map_val, i), env))
       if (has_error) return
    end do
    val%tag = TAG_HASHMAP
    allocate(val%map_val)
    val%map_val = m
  end function eval_hashmap

  ! Keywords, maps, and vectors are callable, same as real Clojure:
  ! (:a m) and (m :a) are both (get m :a); ([1 2 3] 1) is (nth ... 1).
  recursive function apply_fn(f, args) result(val)
    type(cons_value), intent(in) :: f
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val

    select case (f%tag)
    case (TAG_BUILTIN)
       val = call_builtin(f%str_val, args)
    case (TAG_FN)
       val = apply_closure(f, args)
    case (TAG_KEYWORD)
       if (size(args) < 1) then
          call eval_error("keyword invoked with no arguments")
       else
          val = map_lookup(args(1), f, args(2:))
       end if
    case (TAG_HASHMAP)
       if (size(args) < 1) then
          call eval_error("map invoked with no arguments")
       else
          val = map_lookup(f, args(1), args(2:))
       end if
    case (TAG_VECTOR)
       if (size(args) < 1) then
          call eval_error("vector invoked with no arguments")
       else
          val = rt_nth(f, args(1)%int_val)
       end if
    case default
       call eval_error("not a function")
    end select
  end function apply_fn

  function make_list(items) result(val)
    type(cons_value), intent(in) :: items(:)
    type(cons_value) :: val
    val%tag = TAG_LIST
    allocate(val%list_val)
    val%list_val = list_of(items)
  end function make_list

  ! (concat a b ...): every arg's elements, in order, as one list.
  function builtin_concat(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(cons_value) :: no_items(0)
    integer :: item_count, i
    item_count = 0
    do i = 1, size(args)
       call qq_append_all(items, item_count, args(i))
    end do
    if (item_count == 0) then
       val = make_list(no_items)
    else
       val = make_list(items(1:item_count))
    end if
  end function builtin_concat

  ! (apply f a b ... coll): calls f with [a b ... elements-of-coll].
  recursive function builtin_apply(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(cons_value), allocatable :: call_args(:)
    type(cons_value) :: no_items(0)
    integer :: n, item_count, i

    n = size(args)
    item_count = 0
    do i = 2, n - 1
       call qq_push(call_args, item_count, args(i))
    end do
    call qq_append_all(call_args, item_count, args(n))
    if (item_count == 0) then
       val = apply_fn(args(1), no_items)
    else
       val = apply_fn(args(1), call_args(1:item_count))
    end if
  end function builtin_apply

  ! (map f coll): f applied to each element, as one list (eager, same
  ! as the rest of this project's seq handling -- see NOTES.md).
  recursive function builtin_map(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(cons_value) :: no_items(0)
    type(cons_value) :: s, one_arg(1)
    integer :: item_count

    item_count = 0
    s = rt_seq(args(2))
    do while (s%tag == TAG_LIST)
       one_arg(1) = rt_first(s)
       call qq_push(items, item_count, apply_fn(args(1), one_arg))
       if (has_error) return
       s = rt_next(s)
    end do
    if (item_count == 0) then
       val = make_list(no_items)
    else
       val = make_list(items(1:item_count))
    end if
  end function builtin_map

  ! Applies a closure: a fresh child env (outer = the env captured at
  ! (fn* ...) time, not the caller's env), params bound to args, body
  ! evaluated in it.
  function apply_closure(f, args) result(val)
    type(cons_value), intent(in) :: f
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(env_ref) :: child
    child = env_new(f%fn_val%env)
    call bind_params(f%fn_val%params, args, child)
    val = eval_form(f%fn_val%body, child)
  end function apply_closure

  ! Binds params (a list or vector of symbols, optionally ending in
  ! '& rest') to args in child. A missing positional arg binds to nil;
  ! extra args beyond a fixed arity are ignored.
  subroutine bind_params(params, args, child)
    type(cons_value), intent(in) :: params
    type(cons_value), intent(in) :: args(:)
    type(env_ref), intent(in) :: child
    type(cons_value) :: p, nilv
    integer :: n, i, ai

    n = binding_count(params)
    ai = 1
    i = 0
    do while (i < n)
       p = binding_nth(params, i)
       if (p%tag == TAG_SYMBOL .and. p%str_val == "&") then
          p = binding_nth(params, i + 1)
          call env_set(child, p, make_list(args(ai:)))
          return
       end if
       if (ai <= size(args)) then
          call env_set(child, p, args(ai))
       else
          call env_set(child, p, nilv)
       end if
       ai = ai + 1
       i = i + 1
    end do
  end subroutine bind_params

  function make_vector(items) result(val)
    type(cons_value), intent(in) :: items(:)
    type(cons_value) :: val
    type(vec_t) :: vec
    integer :: i
    vec = vector_empty()
    do i = 1, size(items)
       vec = vector_conj(vec, items(i))
    end do
    val%tag = TAG_VECTOR
    allocate(val%vector_val)
    val%vector_val = vec
  end function make_vector

  ! (hash-map k v ...): a map from alternating key/value args.
  ! (assoc m k v ...): variadic -- applies every key/value pair, not just
  ! the first (rt_assoc itself only takes one pair).
  function builtin_assoc(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    integer :: i
    val = args(1)
    do i = 2, size(args), 2
       val = rt_assoc(val, args(i), args(i + 1))
    end do
  end function builtin_assoc

  ! (conj coll x y ...): each extra arg conj'd on in turn, left to right
  ! (rt_conj itself only takes one).
  function builtin_conj(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    integer :: i
    val = args(1)
    do i = 2, size(args)
       val = rt_conj(val, args(i))
    end do
  end function builtin_conj

  function make_hashmap(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(array_map_t) :: m
    integer :: i
    m = array_map_empty()
    do i = 1, size(args), 2
       m = array_map_assoc(m, args(i), args(i + 1))
    end do
    val%tag = TAG_HASHMAP
    allocate(val%map_val)
    val%map_val = m
  end function make_hashmap

  ! (keys m)/(vals m): every key (or value), as a list, in insertion order.
  function builtin_keys(m) result(val)
    type(cons_value), intent(in) :: m
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(cons_value) :: no_items(0)
    integer :: n, i
    n = 0
    if (m%tag == TAG_HASHMAP) then
       if (allocated(m%map_val)) n = array_map_count(m%map_val)
    end if
    if (n == 0) then
       val = make_list(no_items)
       return
    end if
    allocate(items(n))
    do i = 1, n
       items(i) = array_map_nth_key(m%map_val, i - 1)
    end do
    val = make_list(items)
  end function builtin_keys

  function builtin_vals(m) result(val)
    type(cons_value), intent(in) :: m
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:)
    type(cons_value) :: no_items(0)
    integer :: n, i
    n = 0
    if (m%tag == TAG_HASHMAP) then
       if (allocated(m%map_val)) n = array_map_count(m%map_val)
    end if
    if (n == 0) then
       val = make_list(no_items)
       return
    end if
    allocate(items(n))
    do i = 1, n
       items(i) = array_map_nth_val(m%map_val, i - 1)
    end do
    val = make_list(items)
  end function builtin_vals

  ! (dissoc m k ...): a new map with those keys removed.
  function builtin_dissoc(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(array_map_t) :: m
    integer :: i
    m = array_map_empty()
    if (args(1)%tag == TAG_HASHMAP) then
       if (allocated(args(1)%map_val)) m = args(1)%map_val
    end if
    do i = 2, size(args)
       m = array_map_dissoc(m, args(i))
    end do
    val%tag = TAG_HASHMAP
    allocate(val%map_val)
    val%map_val = m
  end function builtin_dissoc

  ! (str x ...): each arg's non-readable ("display") form, concatenated
  ! with no separator, as one string (not printed).
  function builtin_str(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    character(len=:), allocatable :: line
    integer :: i
    line = ""
    do i = 1, size(args)
       line = line // pr_str(args(i), .false.)
    end do
    val%tag = TAG_STRING
    val%str_val = line
  end function builtin_str

  ! (pr-str x ...): each arg's readable form, space-separated, as one
  ! string (not printed).
  function builtin_pr_str(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    character(len=:), allocatable :: line
    integer :: i
    line = ""
    do i = 1, size(args)
       if (i > 1) line = line // " "
       line = line // pr_str(args(i), .true.)
    end do
    val%tag = TAG_STRING
    val%str_val = line
  end function builtin_pr_str

  ! (println x ...): like prn, but non-readable ("display") form.
  function builtin_println(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    character(len=:), allocatable :: line
    integer :: i
    line = ""
    do i = 1, size(args)
       if (i > 1) line = line // " "
       line = line // pr_str(args(i), .false.)
    end do
    write(*, '(A)') line
  end function builtin_println

  ! (time-ms): milliseconds on some monotonic clock -- callers only ever
  ! compare two calls, never the absolute value.
  function time_ms() result(ms)
    integer :: ms
    integer(8) :: count, rate
    call system_clock(count, rate)
    ms = int(count * 1000_8 / rate)
  end function time_ms

  ! (get m key), falling back to an optional not-found default.
  function map_lookup(m, key, default_arg) result(val)
    type(cons_value), intent(in) :: m, key
    type(cons_value), intent(in) :: default_arg(:)
    type(cons_value) :: val
    logical :: found

    found = (m%tag == TAG_HASHMAP .and. allocated(m%map_val))
    if (found) found = array_map_contains(m%map_val, key)
    if (found) then
       val = rt_get(m, key)
    else if (size(default_arg) >= 1) then
       val = default_arg(1)
    end if
  end function map_lookup

  function call_builtin(name, args) result(val)
    character(len=*), intent(in) :: name
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val

    select case (name)
    case ("+")
       val = num_add(args)
    case ("-")
       val = num_sub(args)
    case ("*")
       val = num_mul(args)
    case ("/")
       val = num_div(args)
    case ("first")
       val = rt_first(args(1))
    case ("rest")
       val = rt_rest(args(1))
    case ("cons")
       val = rt_cons(args(1), args(2))
    case ("conj")
       val = builtin_conj(args)
    case ("nth")
       if (args(2)%int_val < 0 .or. args(2)%int_val >= rt_count(args(1))) then
          call eval_error("nth: index out of bounds")
       else
          val = rt_nth(args(1), args(2)%int_val)
       end if
    case ("count")
       val%tag = TAG_INT
       val%int_val = rt_count(args(1))
    case ("get")
       val = map_lookup(args(1), args(2), args(3:))
    case ("assoc")
       val = builtin_assoc(args)
    case ("list")
       val = make_list(args)
    case ("vector")
       val = make_vector(args)
    case ("concat")
       val = builtin_concat(args)
    case ("=")
       val%tag = TAG_BOOL
       val%bool_val = rt_equiv(args(1), args(2))
    case (">")
       val = num_gt(args)
    case (">=")
       val = num_ge(args)
    case ("<")
       val = num_lt(args)
    case ("<=")
       val = num_le(args)
    case ("list?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_LIST)
    case ("empty?")
       val%tag = TAG_BOOL
       val%bool_val = (rt_count(args(1)) == 0)
    case ("prn")
       val = builtin_prn(args)
    case ("read-string")
       val = builtin_read_string(args)
    case ("slurp")
       val = builtin_slurp(args)
    case ("readline")
       val = builtin_readline(args)
    case ("atom")
       val = atom_new(args(1))
    case ("atom?")
       val%tag = TAG_BOOL
       val%bool_val = atom_p(args(1))
    case ("deref")
       val = atom_deref(args(1))
    case ("reset!")
       call atom_reset(args(1), args(2))
       val = args(2)
    case ("swap!")
       val = builtin_swap(args)
    case ("macroexpand")
       val = builtin_macroexpand(args(1))
    case ("throw")
       call throw_value(args(1))
    case ("apply")
       val = builtin_apply(args)
    case ("map")
       val = builtin_map(args)
    case ("symbol?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_SYMBOL)
    case ("nil?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_NIL)
    case ("true?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_BOOL .and. args(1)%bool_val)
    case ("false?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_BOOL .and. .not. args(1)%bool_val)
    case ("keyword?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_KEYWORD)
    case ("vector?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_VECTOR)
    case ("map?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_HASHMAP)
    case ("sequential?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_LIST .or. args(1)%tag == TAG_VECTOR)
    case ("symbol")
       val%tag = TAG_SYMBOL
       val%str_val = args(1)%str_val
    case ("keyword")
       if (args(1)%tag == TAG_KEYWORD) then
          val = args(1)
       else
          val%tag = TAG_KEYWORD
          val%str_val = args(1)%str_val
       end if
    case ("hash-map")
       val = make_hashmap(args)
    case ("contains?")
       val%tag = TAG_BOOL
       val%bool_val = .false.
       if (args(1)%tag == TAG_HASHMAP) then
          if (allocated(args(1)%map_val)) val%bool_val = array_map_contains(args(1)%map_val, args(2))
       end if
    case ("keys")
       val = builtin_keys(args(1))
    case ("vals")
       val = builtin_vals(args(1))
    case ("dissoc")
       val = builtin_dissoc(args)
    case ("str")
       val = builtin_str(args)
    case ("pr-str")
       val = builtin_pr_str(args)
    case ("println")
       val = builtin_println(args)
    case ("number?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_INT .or. args(1)%tag == TAG_REAL)
    case ("string?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_STRING)
    case ("fn?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_BUILTIN)
       if (args(1)%tag == TAG_FN) then
          if (allocated(args(1)%fn_val)) val%bool_val = .not. args(1)%fn_val%is_macro
       end if
    case ("macro?")
       val%tag = TAG_BOOL
       val%bool_val = .false.
       if (args(1)%tag == TAG_FN) then
          if (allocated(args(1)%fn_val)) val%bool_val = args(1)%fn_val%is_macro
       end if
    case ("seq")
       val = rt_seq(args(1))
    case ("time-ms")
       val%tag = TAG_INT
       val%int_val = time_ms()
    case ("with-meta")
       val = args(1)
       if (allocated(val%meta_val)) deallocate(val%meta_val)
       allocate(val%meta_val)
       allocate(val%meta_val%ptr)
       val%meta_val%ptr%refcount = 1
       meta_node_total_allocated = meta_node_total_allocated + 1
       val%meta_val%ptr%val = args(2)
    case ("meta")
       val%tag = TAG_NIL
       if (allocated(args(1)%meta_val)) then
          if (associated(args(1)%meta_val%ptr)) val = args(1)%meta_val%ptr%val
       end if
    case default
       call eval_error("unknown builtin: " // name)
    end select
  end function call_builtin

  ! (prn x ...): prints the readable (pr-str) form of each arg,
  ! space-separated, then a newline. Returns nil.
  function builtin_prn(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    character(len=:), allocatable :: line
    integer :: i
    line = ""
    do i = 1, size(args)
       if (i > 1) line = line // " "
       line = line // pr_str(args(i))
    end do
    write(*, '(A)') line
  end function builtin_prn

  ! (read-string s): parses the first form out of s. A blank/comment-only
  ! string reads as nil, same as a real syntax error would be fatal --
  ! mal's own tests only check that this case doesn't crash.
  function builtin_read_string(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    character(len=:), allocatable :: err
    logical :: ok
    ok = read_str(args(1)%str_val, val, err)
    if (.not. ok .and. err /= "empty input") call eval_error(err)
  end function builtin_read_string

  ! (slurp path): the whole file as one string, read as raw bytes so
  ! newlines land exactly as written.
  function builtin_slurp(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    integer :: unit, ios
    integer(kind=8) :: fsize
    character(len=:), allocatable :: contents

    open(newunit=unit, file=args(1)%str_val, access='stream', form='unformatted', &
         status='old', action='read', iostat=ios)
    if (ios /= 0) then
       call eval_error("slurp: cannot open " // args(1)%str_val)
       return
    end if
    inquire(unit=unit, size=fsize)
    allocate(character(len=fsize) :: contents)
    if (fsize > 0) read(unit) contents
    close(unit)
    val%tag = TAG_STRING
    val%str_val = contents
  end function builtin_slurp

  ! (readline prompt): writes prompt (no newline), reads one line from
  ! stdin. nil at end of input, matching real Clojure/mal -- this is
  ! also why mal_readline's own at_eof distinction exists: without it
  ! there's no way to tell "the user typed nothing" from "no more
  ! input at all".
  function builtin_readline(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    character(len=:), allocatable :: line
    logical :: at_eof

    write(*, "(A)", advance='no') args(1)%str_val
    call sys_readline(5, line, at_eof)
    if (at_eof) return ! nil
    val%tag = TAG_STRING
    val%str_val = line
  end function builtin_readline

  ! (swap! a f & args): resets a to (f @a & args), returns the new value.
  function builtin_swap(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(cons_value), allocatable :: fn_args(:)
    allocate(fn_args(size(args) - 1))
    fn_args(1) = atom_deref(args(1))
    fn_args(2:) = args(3:)
    val = apply_fn(args(2), fn_args)
    if (has_error) return
    call atom_reset(args(1), val)
  end function builtin_swap

  ! (fn* params body): captures env directly -- assignment bumps its
  ! refcount, same closure semantics as real Clojure fns.
  ! (fn* [params] form1 form2 ...): every form after params is the
  ! body, wrapped in an implicit (do ...) same as real Clojure's fn --
  ! fn* itself only ever holds and evaluates ONE body form.
  ! (fn* name [params] form1 ...): an optional leading symbol names the
  ! fn within its own body, for self-recursion without needing an
  ! outer def -- real Clojure's fn* supports this too. Bound via a
  ! throwaway env layer between the closure and its lexical parent,
  ! set to the closure itself only after it's built (env_set mutates
  ! the shared node in place, so the already-captured env sees it).
  function eval_fn(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_ref) :: rest, body_forms
    type(cons_value) :: second, name
    type(env_ref) :: fn_env
    logical :: named

    rest = list_rest(ast%list_val)
    second = list_first(rest)
    named = (second%tag == TAG_SYMBOL)

    val%tag = TAG_FN
    allocate(val%fn_val)
    if (named) then
       name = second
       rest = list_rest(rest)
       fn_env = env_new(env)
    else
       fn_env = env
    end if
    val%fn_val%params = list_first(rest)
    body_forms = list_rest(rest)
    val%fn_val%body = wrap_body(body_forms)
    val%fn_val%env = fn_env
    if (named) call env_set(fn_env, name, val)
  end function eval_fn

  ! Every form after params is the body, wrapped in an implicit
  ! (do ...) same as real Clojure's fn -- fn* itself only ever holds
  ! and evaluates ONE body form.
  function wrap_body(body_forms) result(wrapped)
    type(cons_ref), intent(in) :: body_forms
    type(cons_value) :: wrapped
    type(cons_ref) :: forms
    type(cons_value), allocatable :: items(:)
    type(cons_value) :: do_sym
    integer :: n, i

    forms = body_forms
    n = list_count(forms)
    allocate(items(n + 1))
    do_sym%tag = TAG_SYMBOL
    do_sym%str_val = "do"
    items(1) = do_sym
    do i = 1, n
       items(i + 1) = list_first(forms)
       forms = list_rest(forms)
    end do
    wrapped = make_list(items)
  end function wrap_body

  ! (def! sym expr): evaluates expr, interns it in *ns* (never the
  ! lexical env, even from inside a let*/fn* body -- matches real
  ! Clojure), returns the value.
  function eval_def(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: sym

    sym = list_first(list_rest(ast%list_val))
    val = eval_form(list_first(list_rest(list_rest(ast%list_val))), env)
    if (has_error) return
    call ns_intern(ns_current(), sym%str_val, val)
  end function eval_def

  ! let*'s bindings may be a list or a vector.
  function binding_count(b) result(n)
    type(cons_value), intent(in) :: b
    integer :: n
    n = 0
    if (b%tag == TAG_LIST) then
       if (allocated(b%list_val)) n = list_count(b%list_val)
    else if (b%tag == TAG_VECTOR) then
       if (allocated(b%vector_val)) n = vector_count(b%vector_val)
    end if
  end function binding_count

  function binding_nth(b, i) result(val)
    type(cons_value), intent(in) :: b
    integer, intent(in) :: i
    type(cons_value) :: val
    type(cons_ref) :: l
    integer :: k
    if (b%tag == TAG_VECTOR) then
       val = vector_nth(b%vector_val, i)
    else
       l = b%list_val
       do k = 1, i
          l = list_rest(l)
       end do
       val = list_first(l)
    end if
  end function binding_nth

end module Eval
