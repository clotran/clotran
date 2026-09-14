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
  use PersistentArrayMap, only: array_map_empty, array_map_entries, &
       array_map_assoc, array_map_contains, array_map_dissoc
  use RT, only: rt_get => get, rt_nth => nth, rt_assoc => assoc, rt_count => count, &
       rt_first => first, rt_rest => rest, rt_cons => cons, rt_conj => conj, rt_equiv => equiv, &
       rt_seq => seq, rt_next => next
  use Numbers, only: num_add, num_sub, num_mul, num_div, num_lt, num_gt, num_le, num_ge, &
       num_bit_and, num_bit_or, num_bit_xor, num_bit_not, num_bit_and_not, &
       num_quot, num_rem, num_shift_left, num_shift_right, num_ushift_right
  use printer, only: pr_str
  use Atom, only: atom_new, atom_p, atom_deref, atom_reset, var_dyn_push, var_dyn_pop
  use LispReader, only: read_str, read_top_level_forms
  use mal_readline, only: sys_readline => readline
  use Namespace, only: ns_ref, assignment(=), CORE_NS, ns_find_or_create, ns_exists, ns_intern, &
       ns_resolve, ns_get_own, ns_set_current, ns_current, ns_name_of, ns_resolve_var
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

  ! See eval_macro_head's own comment -- a hard cap on nested macro
  ! expansion, purely a safety net against a known-unresolved runaway
  ! recursion (assert-args/let), not a general limit anything else
  ! should ever approach.
  integer :: macro_expand_depth = 0

  ! See eval_new's clojure.lang.LazySeq case.
  integer :: lazy_force_depth = 0

  ! push-thread-bindings/pop-thread-bindings' own stack of stacks: a
  ! flat run of every Var pushed so far, plus how many the most recent
  ! push touched, so pop undoes exactly that many and no others (binding
  ! forms nest and can touch several Vars in one push). ponytail: one
  ! global stack, not real per-thread storage -- see Atom.f90's
  ! dyn_stack comment; revisit alongside it.
  type(cons_value), allocatable :: binding_stack_vars(:)
  integer, allocatable :: binding_stack_frame_sizes(:)

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
    call reg("next")
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
    call reg("push-thread-bindings")
    call reg("pop-thread-bindings")
    call reg("bit-and")
    call reg("bit-or")
    call reg("bit-xor")
    call reg("bit-not")
    call reg("bit-and-not")
    call reg("quot")
    call reg("rem")
    call reg("bit-shift-left")
    call reg("bit-shift-right")
    call reg("unsigned-bit-shift-right")
    call reg("next-id")
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
    call reg("instance?")
    call reg("vector?")
    call reg("map?")
    call reg("sequential?")
    call reg("symbol")
    call reg("keyword")
    call reg("hash-map")
    call reg("hash-set")
    call reg("disj")
    call reg("set?")
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

  ! src/clj/clotran.clj loads FIRST: it populates the small clojure.
  ! lang.* interop surface (clojure.lang.RT, clojure.lang.PersistentList,
  ! clojure.lang.Util, instance?'s pseudo-classes) that real core.clj's
  ! OWN bootstrap-era definitions call into starting from its very
  ! first few forms (cons, list, fn, ... all resolve straight into
  ! clojure.lang.RT while core.clj is still loading itself, long
  ! before reaching the end of the file) -- see clotran.clj's own
  ! header. Loading it after core.clj (the original order) meant every
  ! one of those calls failed for the entire rest of the file, since
  ! clojure.lang.RT didn't exist yet.
  !
  ! src/clj/clojure/core.clj -- the actual upstream file, byte-for-byte,
  ! never edited (not even additively; see NOTES.md for why reader
  ! conditionals in core.clj itself would be historically inaccurate --
  ! real core.clj has never had any) -- loads second, exactly as Rich
  ! Hickey wrote it, on top of that surface. Every individual top-level
  ! form gets its own independent try (see eval_load_file_head), so the
  ! handful that call real JVM interop clotran doesn't have simply fail
  ! to rebind their name, leaving whatever was bound before in place --
  ! nothing aborts the rest of the file.
  !
  ! Both resolved relative to argv[0]'s own directory, not cwd (no
  ! installed-resource concept yet, but this at least survives a
  ! caller changing directories before invoking us, e.g. the
  ! regression suite's --rundir).
  subroutine eval_core_bootstrap(env)
    type(env_ref), intent(in) :: env
    type(cons_value) :: ast, discard
    character(len=:), allocatable :: err, src
    logical :: ok

    src = '(load-file "' // exe_relative_path("src/clj/clotran.clj") // '")'
    ok = read_str(src, ast, err)
    if (ok) discard = eval_form(ast, env)
    if (has_error) then
       write(*, '(A)') "warning: clotran.clj failed to load: " // pr_str(last_error_value)
       has_error = .false.
    end if

    src = '(load-file "' // exe_relative_path("src/clj/clojure/core.clj") // '")'
    ok = read_str(src, ast, err)
    if (ok) discard = eval_form(ast, env)
    if (has_error) then
       write(*, '(A)') "warning: core.clj failed to load: " // pr_str(last_error_value)
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
    macro_expand_depth = 0
    lazy_force_depth = 0
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
       case (TAG_SET)
          val = eval_set(ast, env)
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
          else if (head%str_val == "var") then
             ! (var sym)/#'sym: resolves to the real Var itself (a
             ! TAG_VAR value, see Namespace.f90), not its current
             ! value -- matches real Clojure (#'+ is the Var, (+ 1 2)
             ! calls through it).
             block
               type(cons_value) :: sym
               character(len=:), allocatable :: owner
               sym = list_first(list_rest(ast%list_val))
               if (.not. ns_resolve_var(ns_current(), sym%str_val, val, owner)) then
                  call eval_error("Unable to resolve var: " // sym%str_val)
               end if
             end block
             return
          else if (head%str_val == ".") then
             val = eval_dot(ast, env)
             return
          else if (len(head%str_val) > 1 .and. head%str_val(1:1) == ".") then
             ! (.method obj args...) sugar for (. obj (method args...))
             ! -- real Clojure's reader-level rewrite for this, done
             ! here at eval time instead since clotran has no separate
             ! macroexpansion pass. Rewrites ast in place and lets the
             ! "." branch above handle it.
             call rewrite_dot_method_sugar(ast)
             cycle
          else if (len(head%str_val) > 1 .and. head%str_val(len(head%str_val):) == ".") then
             ! (ClassName. args...) sugar for (new ClassName args...) --
             ! same reader-level rewrite, done here at eval time instead.
             call rewrite_new_sugar(ast)
             cycle
          else if (head%str_val == "fn*") then
             val = eval_fn(ast, env)
             return
          else if (head%str_val == "let*") then
             call eval_let_head(ast, env) ! rebinds ast/env to (child env, body); tail
             if (has_error) return
             cycle
          else if (head%str_val == "loop*") then
             call eval_loop_head(ast, env) ! rebinds ast/env to (child env, body); tail
             if (has_error) return
             cycle
          else if (head%str_val == "new") then
             val = eval_new(ast, env)
             return
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
          else if (head%str_val == "ns") then
             val = eval_ns(ast, env)
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
          block
            type(cons_value) :: params, body
            call select_clause(args(1), n - 1, params, body)
            if (has_error) return
            env = env_new(args(1)%fn_val%env)
            call bind_params(params, args(2:n), env, is_recur=(head%str_val == "recur"))
            ast = body
          end block
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

  ! loop*: same binding mechanics as let*, plus establishing a recur
  ! target -- built as an ordinary TAG_FN closure (params = the
  ! binding names, body = the loop's own body, env = this loop's env)
  ! bound to the symbol "recur", so a (recur args...) inside the body
  ! is just an ordinary call and falls straight into the ALREADY
  ! existing "tail call into a closure" path in eval_form's main loop
  ! (is_recur=(head%str_val=="recur") there already exists for fn*'s
  ! own recur) -- no separate loop-specific tail machinery needed.
  subroutine eval_loop_head(ast, env)
    type(cons_value), intent(inout) :: ast
    type(env_ref), intent(inout) :: env
    type(cons_value) :: bindings, k, v
    type(cons_value) :: recur_fn, recur_sym
    type(cons_value), allocatable :: names(:)
    integer :: n, i

    bindings = list_first(list_rest(ast%list_val))
    n = binding_count(bindings)
    if (mod(n, 2) /= 0) then
       call eval_error("loop* requires an even number of binding forms")
       return
    end if

    env = env_new(env)
    allocate(names(n/2))
    do i = 0, n - 1, 2
       k = binding_nth(bindings, i)
       v = eval_form(binding_nth(bindings, i + 1), env)
       if (has_error) return
       call env_set(env, k, v)
       names(i/2 + 1) = k
    end do

    recur_fn%tag = TAG_FN
    allocate(recur_fn%fn_val)
    recur_fn%fn_val%params = make_vector(names)
    recur_fn%fn_val%body = wrap_body(list_rest(list_rest(ast%list_val)))
    recur_fn%fn_val%env = env
    recur_sym%tag = TAG_SYMBOL
    recur_sym%str_val = "recur"
    call env_set(env, recur_sym, recur_fn)

    ast = recur_fn%fn_val%body
  end subroutine eval_loop_head

  ! (load-file "path"): slurps the file, reads every top-level form in
  ! it, and evaluates them in sequence with no lexical locals -- same
  ! rule as eval, since load-file is just eval+read-string+slurp
  ! composed, repeated per form.
  !
  ! Each form gets its own independent try: a failure evaluating one
  ! (real, unsupported interop in an unmodified upstream file, say)
  ! doesn't stop the rest of the file from loading. Deliberately more
  ! lenient than real Clojure's own load-file, which stops at the first
  ! exception -- this project imports real upstream source (core.clj)
  ! that isn't 100% supported yet, and wants as much of it to load as
  ! actually can, rather than all-or-nothing. Silent by design (not a
  ! bug): loading core.clj today fails dozens of individual forms one
  ! at a time -- see clotran.clj -- and warning on each would be pure
  ! noise; only a real syntax error (read_top_level_forms itself
  ! failing) or a failure in the file's own LAST form (left for the
  ! caller's normal error handling, below) surfaces at all.
  subroutine eval_load_file_head(ast, env)
    type(cons_value), intent(inout) :: ast
    type(env_ref), intent(inout) :: env
    type(cons_value) :: fname, contents
    type(cons_value), allocatable :: forms(:)
    character(len=:), allocatable :: err
    integer :: n, i
    logical :: ok

    fname = eval_form(list_first(list_rest(ast%list_val)), env)
    if (has_error) return
    contents = builtin_slurp([fname])
    if (has_error) return

    ok = read_top_level_forms(contents%str_val, forms, n, err)
    if (.not. ok) then
       call eval_error("load-file: " // err)
       return
    end if

    env = env_new()
    if (n == 0) then
       ast%tag = TAG_NIL
       return
    end if

    do i = 1, n - 1
       block
         type(cons_value) :: discard
         discard = eval_form(forms(i), env)
       end block
       has_error = .false.
    end do
    ast = forms(n) ! tail position: the trampoline evaluates/reports this one normally
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

  ! (ns name & _clauses): switches *ns* to name, creating it if new --
  ! name is never evaluated, same as def's name position (and same as
  ! how ^{...} metadata already rides along invisibly on it, no
  ! unwrapping needed). Real Clojure's ns is a macro expanding to
  ! in-ns + require + import + refer; this only needs the name switch
  ! so far -- core.clj's own single ns form has no :require/:import
  ! (it IS the root namespace), so any clauses after the name are
  ! silently ignored for now. A real, useful primitive on its own
  ! merits, not a one-off for this file.
  function eval_ns(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: name

    name = list_first(list_rest(ast%list_val))
    call ns_set_current(ns_find_or_create(name%str_val))
    val = name
  end function eval_ns

  ! (.method obj args...) -> (. obj (method args...)). Head symbol
  ! keeps its own leading "." stripped off as the method name; obj and
  ! args carry over unevaluated (eval_dot evaluates them itself).
  subroutine rewrite_dot_method_sugar(ast)
    type(cons_value), intent(inout) :: ast
    type(cons_value) :: obj, method_sym, dot_sym, inner_form, head
    type(cons_value), allocatable :: inner_items(:), outer_items(:)
    type(cons_ref) :: rest_args
    integer :: n, i

    head = list_first(ast%list_val) ! flang can't chain %field off a function result directly
    method_sym%tag = TAG_SYMBOL
    method_sym%str_val = head%str_val(2:)
    obj = list_first(list_rest(ast%list_val))
    rest_args = list_rest(list_rest(ast%list_val))
    n = list_count(rest_args)

    allocate(inner_items(n + 1))
    inner_items(1) = method_sym
    do i = 1, n
       inner_items(i + 1) = list_first(rest_args)
       rest_args = list_rest(rest_args)
    end do
    inner_form = make_list(inner_items)

    dot_sym%tag = TAG_SYMBOL
    dot_sym%str_val = "."
    allocate(outer_items(3))
    outer_items(1) = dot_sym
    outer_items(2) = obj
    outer_items(3) = inner_form
    ast = make_list(outer_items)
  end subroutine rewrite_dot_method_sugar

  ! (ClassName. args...) -- real Clojure's reader-level sugar for
  ! (new ClassName args...), rewritten here at eval time instead since
  ! clotran has no separate macroexpansion pass, same as
  ! rewrite_dot_method_sugar above.
  subroutine rewrite_new_sugar(ast)
    type(cons_value), intent(inout) :: ast
    type(cons_value) :: head, cls, new_sym
    type(cons_value), allocatable :: items(:)
    type(cons_ref) :: rest_args
    integer :: n, i

    head = list_first(ast%list_val) ! flang can't chain %field off a function result directly
    cls%tag = TAG_SYMBOL
    cls%str_val = head%str_val(1:len(head%str_val) - 1)
    rest_args = list_rest(ast%list_val)
    n = list_count(rest_args)

    new_sym%tag = TAG_SYMBOL
    new_sym%str_val = "new"
    allocate(items(n + 2))
    items(1) = new_sym
    items(2) = cls
    do i = 1, n
       items(i + 2) = list_first(rest_args)
       rest_args = list_rest(rest_args)
    end do
    ast = make_list(items)
  end subroutine rewrite_new_sugar

  ! (. X (method args...)) or (. X member) -- real Clojure allows both
  ! a parenthesized method call and a bare-symbol field/no-arg-method
  ! access in the third position (e.g. core.clj's own (. clojure.lang.
  ! PersistentList creator), no parens around creator). Evaluated for
  ! real rather than reader-conditioned away in literal source --
  ! core.clj's own bootstrap (defmacro's macroexpansion, defn's
  ! instance?/Util calls, etc.) constructs and calls these forms
  ! directly, and stays byte-for-byte unmodified (see NOTES.md), so
  ! this has to be real, not patched around.
  !
  ! No general reflection -- clotran has no real classes or objects --
  ! just two narrow, real cases:
  !  - static: X is a bare symbol naming an already-registered
  !    namespace (clojure.lang.RT, clojure.lang.Util, ... -- populated
  !    from src/clj/clotran.clj, not hardcoded here). Resolves member
  !    within that namespace directly (calling it, if it's a fn and
  !    the form supplied args; otherwise just its value); X itself is
  !    never evaluated, same as a real Class isn't a runtime value in
  !    this position.
  !  - instance: anything else. X is evaluated normally, member is
  !    dispatched on (X's tag, member name) -- see eval_instance_call.
  ! Anything neither of these recognizes is a real, clear error, not a
  ! silent no-op -- same as the reader's own unsupported-syntax cases.
  recursive function eval_dot(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: target_form, target, member_form, member_name
    type(cons_value), allocatable :: args(:)
    type(cons_ref) :: l
    integer :: n, i
    logical :: is_method_call

    target_form = list_first(list_rest(ast%list_val))
    member_form = list_first(list_rest(list_rest(ast%list_val)))
    if (member_form%tag == TAG_LIST) then
       member_name = list_first(member_form%list_val)
       n = list_count(member_form%list_val) - 1
       allocate(args(n))
       l = list_rest(member_form%list_val)
       is_method_call = .true.
    else
       ! Flat form: (. target member arg*), real Clojure's own
       ! documented equivalent of (. target (member arg*)) -- core.clj
       ! uses it in 59 places, every bit-op among them (bit-and is
       ! literally `(. clojure.lang.Numbers and x y)`). Treating a
       ! bare-symbol member as ALWAYS field access silently dropped
       ! every one of those args and returned the member itself, which
       ! is what made bit-and return #<builtin bit-and> instead of a
       ! number -- and so even? always false, and so every
       ! [bindings]-style macro fail its own assert-args validation.
       ! With no trailing args it stays field access, as before.
       member_name = member_form
       l = list_rest(list_rest(list_rest(ast%list_val)))
       n = list_count(l)
       allocate(args(n))
       is_method_call = (n > 0)
    end if

    if (target_form%tag == TAG_SYMBOL) then
       if (ns_exists(target_form%str_val)) then
          do i = 1, n
             args(i) = eval_form(list_first(l), env)
             if (has_error) return
             l = list_rest(l)
          end do
          val = eval_static_call(target_form%str_val, member_name%str_val, args, &
               is_call=is_method_call)
          return
       end if
    end if

    target = eval_form(target_form, env)
    if (has_error) return
    do i = 1, n
       args(i) = eval_form(list_first(l), env)
       if (has_error) return
       l = list_rest(l)
    end do
    val = eval_instance_call(target, member_name%str_val, args)
  end function eval_dot

  ! (new ClassName args...): real Clojure constructs a real instance;
  ! clotran has no class/object system, so -- matching how throw/catch
  ! already treat any value as throwable/catchable regardless of a
  ! real type -- this just evaluates the args and returns the first
  ! one (the usual shape for the exception constructors core.clj
  ! itself calls, e.g. (new IllegalArgumentException "msg")), or the
  ! class name itself as a string if there are none. ClassName is
  ! never evaluated, same as `.`'s static-call position.
  recursive function eval_new(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: cls
    type(cons_ref) :: rest

    cls = list_first(list_rest(ast%list_val))
    rest = list_rest(list_rest(ast%list_val))
    if (cls%tag == TAG_SYMBOL .and. cls%str_val == "clojure.lang.Atom") then
       ! core.clj's own (atom x) is literally (new clojure.lang.Atom
       ! x) -- a REAL constructor, unlike the generic exception-message
       ! passthrough below.
       val = call_builtin("atom", [eval_form(list_first(rest), env)])
       return
    end if
    if (cls%tag == TAG_SYMBOL .and. cls%str_val == "clojure.lang.LazySeq") then
       ! core.clj's own `lazy-seq` macro is literally
       ! (new clojure.lang.LazySeq (fn* [] body...)) -- so EVERY lazy
       ! function (map, filter, concat, ...) built one of these, and
       ! the generic passthrough below just handed the thunk itself
       ! back: (map inc [1 2 3]) evaluated to #<fn>.
       !
       ! ponytail: forced immediately -- the thunk is called right
       ! here and its seq returned, so seqs are EAGER, not lazy. Every
       ! finite use is then correct; an infinite one ((range),
       ! (repeat x), (iterate f x), cycle) would recurse until the
       ! stack goes, where real Clojure would stream it. Upgrade path
       ! is a real TAG_LAZYSEQ (thunk + memoized realization, forced
       ! by seq/first/rest/count/pr_str in RT.f90) -- a genuine
       ! feature, not a bug fix, and not needed to get core.clj
       ! loading.
       block
         type(cons_value) :: thunk
         type(cons_value), allocatable :: no_args(:)
         thunk = eval_form(list_first(rest), env)
         if (has_error) return
         allocate(no_args(0))
         ! Depth cap, same idea as macro_expand_depth: forcing is
         ! eager, so an INFINITE lazy seq ((repeatedly f), (iterate f
         ! x), (range)) would realize forever and take the real
         ! Fortran stack with it. core.clj does build one in ordinary
         ! code -- destmap*'s :or handling is
         ! (zipmap (keys defaults) (repeatedly #(gensym "default__"))),
         ! finite only because real Clojure stops pulling. Cap it so
         ! that fails as a catchable error instead of a segfault.
         lazy_force_depth = lazy_force_depth + 1
         if (lazy_force_depth > 64) then
            call eval_error("lazy sequence too deep -- clotran realizes lazy seqs eagerly, " // &
                 "so an infinite one (repeatedly/iterate/range with no bound) can't be built yet")
            lazy_force_depth = lazy_force_depth - 1
            return
         end if
         val = apply_fn(thunk, no_args)
         lazy_force_depth = lazy_force_depth - 1
       end block
       return
    end if
    if (cls%tag == TAG_SYMBOL .and. cls%str_val == "StringBuilder") then
       ! core.clj's own multi-arg `str` is (new StringBuilder (str x))
       ! -- a real, mutable StringBuilder, appended to and read back via
       ! .append/.toString (see eval_instance_call).
       block
         type(cons_value) :: seed
         seed%tag = TAG_STRING
         if (list_count(rest) > 0) then
            seed%str_val = pr_str(eval_form(list_first(rest), env), .false.)
            if (has_error) return
         else
            seed%str_val = ""
         end if
         val = atom_new(seed)
         val%tag = TAG_STRING_BUILDER
       end block
       return
    end if
    if (list_count(rest) > 0) then
       val = eval_form(list_first(rest), env)
    else
       val%tag = TAG_STRING
       val%str_val = cls%str_val
    end if
  end function eval_new

  ! (. Class (method args...)) / (. Class method args...) / (. Class
  ! member) once Class is confirmed to name a real namespace: an
  ! ordinary lookup of whatever's def'd under that name there, exactly
  ! like clojure.lang.Util/equiv (real Clojure's own slash syntax)
  ! already resolves via plain ns_resolve -- this is that same lookup,
  ! just reached through the dot-form's own syntax instead. is_call
  ! tells apart the two shapes that both end up with an empty args
  ! here -- (. Class (member)), a real 0-arg method call, vs
  ! (. Class member), bare-symbol field access -- which the VALUE's own
  ! tag can't: a field can itself hold an IFn (e.g. PersistentList's
  ! own `creator`, a bare-symbol field holding the list-builtin
  ! itself, never meant to be invoked on the spot).
  function eval_static_call(ns_name, member_name, args, is_call) result(val)
    character(len=*), intent(in) :: ns_name, member_name
    type(cons_value), intent(in) :: args(:)
    logical, intent(in) :: is_call
    type(cons_value) :: val
    type(cons_value) :: found_val
    logical :: found

    found = ns_get_own(ns_find_or_create(ns_name), member_name, found_val)
    if (.not. found) then
       call eval_error("'" // trim(ns_name) // "/" // member_name // "' not found")
       return
    end if
    if (.not. is_call) then
       val = found_val
       return
    end if
    val = apply_fn(found_val, args)
  end function eval_static_call

  ! Instance-position (. x (method args...)): dispatch table by
  ! method name (and, where it matters, x's own tag). Grows one entry
  ! at a time as core.clj's own bootstrap turns up the next one it
  ! actually calls -- see NOTES.md.
  !  - setMacro: the original, needed by defmacro's own macroexpansion
  !    -- marks *ns*'s current binding of the symbol x as a macro (the
  !    same effect real Clojure's Var.setMacro() has, without a real
  !    Var) and re-interns it.
  !  - meta/withMeta: needed by core.clj's OWN real `fn` macro
  !    ((.withMeta (cons 'fn* decl) (.meta &form))), which is what's
  !    actually in effect for any (fn ...) written before clotran.clj
  !    gets a chance to override it (clotran.clj only loads after all
  !    of core.clj does) -- just the existing meta/with-meta builtins,
  !    reached through dot-sugar instead of a bare call.
  function eval_instance_call(target, method_name, args) result(val)
    type(cons_value), intent(in) :: target
    character(len=*), intent(in) :: method_name
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(cons_value) :: current
    type(cons_value) :: call_args(2)
    character(len=:), allocatable :: owner
    logical :: found

    if (method_name == "setMacro" .and. target%tag == TAG_VAR) then
       ! (var sym) now resolves to the real Var -- mutate its root
       ! directly, same identity, no need to re-resolve by name.
       current = atom_deref(target)
       if (current%tag == TAG_FN) then
          if (allocated(current%fn_val)) current%fn_val%is_macro = .true.
       end if
       call atom_reset(target, current)
       val%tag = TAG_NIL
       return
    end if
    if (method_name == "setMacro" .and. target%tag == TAG_SYMBOL) then
       found = ns_resolve(ns_current(), target%str_val, current, owner)
       if (.not. found) then
          call eval_error("var " // target%str_val // " does not exist")
          return
       end if
       if (current%tag == TAG_FN) then
          if (allocated(current%fn_val)) current%fn_val%is_macro = .true.
       end if
       call ns_intern(ns_current(), target%str_val, current)
       val%tag = TAG_NIL
       return
    end if
    if (method_name == "meta") then
       val = call_builtin("meta", [target])
       return
    end if
    if (method_name == "withMeta" .and. size(args) >= 1) then
       call_args(1) = target
       call_args(2) = args(1)
       val = call_builtin("with-meta", call_args)
       return
    end if
    if (method_name == "isInstance" .and. size(args) >= 1) then
       ! real core.clj's own instance? is (fn [c x] (. c (isInstance
       ! x))) -- target is c (one of clotran.clj's pseudo-class
       ! keywords), args(1) is x. The native instance? builtin already
       ! takes exactly (c x) in that order, so this is a direct
       ! passthrough -- no separate override of instance? needed.
       call_args(1) = target
       call_args(2) = args(1)
       val = call_builtin("instance?", call_args)
       return
    end if
    if ((method_name == "getName" .or. method_name == "getNamespace") .and. &
         (target%tag == TAG_SYMBOL .or. target%tag == TAG_KEYWORD)) then
       ! Symbols/keywords keep their whole "ns/name" text in str_val,
       ! so these split it: getName is the part after the slash,
       ! getNamespace the part before (nil when unqualified, matching
       ! real Clojure -- core.clj's own :keys/:syms destructuring
       ! branches on exactly that nil).
       block
         integer :: slash
         slash = 0
         if (target%str_val /= "/") slash = index(target%str_val, "/")
         if (method_name == "getName") then
            val%tag = TAG_STRING
            val%str_val = target%str_val
         else
            if (slash > 0) then
               val%tag = TAG_STRING
               val%str_val = target%str_val(1:slash - 1)
            else
               val%tag = TAG_NIL
            end if
         end if
       end block
       return
    end if
    if (target%tag == TAG_STRING) then
       ! java.lang.String's own methods, as core.clj calls them
       ! directly on strings (destructuring's :keys/:syms/:strs
       ! detection uses .startsWith; defn's inline-tag fixup uses
       ! .indexOf). Only the handful core.clj actually reaches for --
       ! same "grows as the walk turns up the next one" rule the rest
       ! of this interop surface follows.
       select case (method_name)
       case ("startsWith")
          val%tag = TAG_BOOL
          val%bool_val = (len(args(1)%str_val) <= len(target%str_val))
          if (val%bool_val) val%bool_val = &
               (target%str_val(1:len(args(1)%str_val)) == args(1)%str_val)
          return
       case ("endsWith")
          val%tag = TAG_BOOL
          val%bool_val = (len(args(1)%str_val) <= len(target%str_val))
          if (val%bool_val) val%bool_val = &
               (target%str_val(len(target%str_val) - len(args(1)%str_val) + 1:) == args(1)%str_val)
          return
       case ("indexOf")
          val%tag = TAG_INT
          val%int_val = index(target%str_val, args(1)%str_val) - 1 ! Java is 0-based, -1 when absent
          return
       case ("lastIndexOf")
          val%tag = TAG_INT
          val%int_val = index(target%str_val, args(1)%str_val, back=.true.) - 1
          return
       case ("length")
          val%tag = TAG_INT
          val%int_val = len(target%str_val)
          return
       case ("substring")
          val%tag = TAG_STRING
          if (size(args) >= 2) then
             val%str_val = target%str_val(args(1)%int_val + 1:args(2)%int_val)
          else
             val%str_val = target%str_val(args(1)%int_val + 1:)
          end if
          return
       case ("toUpperCase", "toLowerCase")
          block
            integer :: ci, cc
            val%tag = TAG_STRING
            val%str_val = target%str_val
            do ci = 1, len(val%str_val)
               cc = iachar(val%str_val(ci:ci))
               if (method_name == "toUpperCase") then
                  if (cc >= 97 .and. cc <= 122) val%str_val(ci:ci) = achar(cc - 32)
               else
                  if (cc >= 65 .and. cc <= 90) val%str_val(ci:ci) = achar(cc + 32)
               end if
            end do
          end block
          return
       case ("trim")
          val%tag = TAG_STRING
          val%str_val = trim(adjustl(target%str_val))
          return
       end select
    end if
    if (method_name == "disjoin" .and. target%tag == TAG_SET .and. size(args) >= 1) then
       ! core.clj's own disj is (. set (disjoin k)).
       call_args(1) = target
       call_args(2) = args(1)
       val = call_builtin("disj", call_args)
       return
    end if
    if ((method_name == "getKey" .or. method_name == "getValue") .and. &
         target%tag == TAG_VECTOR) then
       ! core.clj's own key/val are (. e (getKey))/(. e (getValue)) on
       ! a map entry. clotran has no separate MapEntry type -- seq over
       ! a map yields plain [k v] vectors -- so these are just nth 0/1.
       block
         type(cons_value) :: idx
         idx%tag = TAG_INT
         idx%int_val = 0
         if (method_name == "getValue") idx%int_val = 1
         call_args(1) = target
         call_args(2) = idx
         val = call_builtin("nth", call_args)
       end block
       return
    end if
    if (method_name == "toString" .and. target%tag == TAG_STRING_BUILDER) then
       ! The StringBuilder's own current content, not "(atom ...)" --
       ! pr_str has no special case for TAG_STRING_BUILDER, so this
       ! reads the mutable payload directly instead of falling through
       ! to the generic case below.
       val = atom_deref(target)
       return
    end if
    if (method_name == "append" .and. target%tag == TAG_STRING_BUILDER .and. size(args) >= 1) then
       ! Mutates in place AND returns the same StringBuilder, matching
       ! real Java (chained/recurred on, e.g. core.clj's own `str`).
       block
         type(cons_value) :: cur
         cur = atom_deref(target)
         cur%str_val = cur%str_val // args(1)%str_val
         call atom_reset(target, cur)
       end block
       val = target
       return
    end if
    if (method_name == "toString") then
       ! Real Clojure's Object.toString(), reached via core.clj's own
       ! source (assert-args's error-message building, among others) --
       ! same "display," non-readable rendering as str's own default,
       ! for any value, not just symbols/keywords (unlike getName above).
       val%tag = TAG_STRING
       val%str_val = pr_str(target, .false.)
       return
    end if
    if (method_name == "applyTo" .and. size(args) >= 1) then
       ! real core.clj's own apply is (. f (applyTo (seq args))) --
       ! target is f, args(1) is the already-seq'd/spread argument
       ! list. builtin_apply's own 2-arg case (f, one trailing seq) is
       ! exactly this.
       call_args(1) = target
       call_args(2) = args(1)
       val = call_builtin("apply", call_args)
       return
    end if
    if (method_name == "deref" .and. target%tag == TAG_ATOM) then
       val = call_builtin("deref", [target])
       return
    end if
    if ((method_name == "get" .or. method_name == "deref") .and. target%tag == TAG_VAR) then
       ! var-get/deref on a Var (core.clj's own (defn var-get [x] (. x
       ! (get)))) -- same underlying atom_ref storage as TAG_ATOM, just
       ! reused directly rather than through the atom builtins.
       val = atom_deref(target)
       return
    end if
    if (method_name == "set" .and. target%tag == TAG_VAR .and. size(args) >= 1) then
       call atom_reset(target, args(1))
       val = args(1)
       return
    end if
    if (method_name == "reset" .and. target%tag == TAG_ATOM .and. size(args) >= 1) then
       call_args(1) = target
       call_args(2) = args(1)
       val = call_builtin("reset!", call_args)
       return
    end if
    if (method_name == "swap" .and. target%tag == TAG_ATOM .and. size(args) >= 1) then
       block
         type(cons_value), allocatable :: swap_args(:)
         allocate(swap_args(size(args) + 1))
         swap_args(1) = target
         swap_args(2:) = args
         val = call_builtin("swap!", swap_args)
       end block
       return
    end if
    call eval_error("unsupported interop call: (." // trim(method_name) // " " // pr_str(target) // ")")
  end function eval_instance_call

  ! (try form* (catch ...)?): any number of body forms (an implicit
  ! do), then an optional trailing catch clause, identified
  ! structurally (a trailing list starting with catch/catch*) rather
  ! than by position -- core.clj's own macros (when-class, etc.)
  ! generate a variable number of body forms ahead of catch, not
  ! always exactly one. Only one catch clause. Not tail-cycled:
  ! try/catch isn't the hot recursive path TCO exists for.
  !
  ! Two distinct catch shapes, told apart by which name was used:
  !  - (catch class sym form*): real Clojure's own shape. class is
  !    unevaluated and ignored -- no real exception-class matching (no
  !    class hierarchy to match against), a documented simplification
  !    that catches anything regardless of what class names.
  !  - (catch* sym form*): mal's own shape (no class at all) -- kept
  !    working unchanged for test/regression/'s own borrowed suite,
  !    which uses catch* exclusively and never with a class argument.
  ! (try body* (catch/catch* e ...)? (finally ...)?): a trailing
  ! (finally ...) always runs -- even when the body errors and there's
  ! no catch, even when catch itself errors -- same as real Clojure.
  ! `binding`'s own macroexpansion depends on this: pop-thread-bindings
  ! lives in a finally, so a Var that binding pushed must get unbound
  ! on the way out regardless of how the body finished (see Atom.f90's
  ! dyn_stack). Only one catch clause supported (no class matching),
  ! same simplification as before.
  function eval_try(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_ref) :: forms, l, cl
    type(cons_value) :: form, catch_clause, catch_head, catch_sym, finally_clause
    type(env_ref) :: catch_env
    integer :: n, k, body_n, cn
    logical :: has_catch, has_finally
    logical :: saved_has_error
    type(cons_value) :: saved_error_value

    ! Peel (finally ...) off the end first if present, then
    ! (catch/catch* ...) off whatever's now the end -- real Clojure's
    ! own clause order (body*, then an optional catch, then an
    ! optional finally) always leaves finally last when both appear.
    forms = list_rest(ast%list_val)
    n = list_count(forms)
    has_catch = .false.
    has_finally = .false.
    body_n = n

    if (body_n > 0) then
       form = nth_form(forms, body_n)
       if (clause_head_is(form, "finally")) then
          has_finally = .true.
          finally_clause = form
          body_n = body_n - 1
       end if
    end if
    if (body_n > 0) then
       form = nth_form(forms, body_n)
       if (clause_head_is(form, "catch") .or. clause_head_is(form, "catch*")) then
          has_catch = .true.
          catch_clause = form
          catch_head = list_first(form%list_val)
          body_n = body_n - 1
       end if
    end if

    val%tag = TAG_NIL
    l = forms
    do k = 1, body_n
       val = eval_form(list_first(l), env)
       if (has_error) exit
       l = list_rest(l)
    end do

    if (has_error .and. has_catch) then
       cl = list_rest(catch_clause%list_val) ! drop "catch"/"catch*"
       if (catch_head%str_val == "catch") cl = list_rest(cl) ! drop the (ignored) class
       catch_sym = list_first(cl)
       cl = list_rest(cl)
       cn = list_count(cl)

       catch_env = env_new(env)
       call env_set(catch_env, catch_sym, last_error_value)
       has_error = .false. ! caught
       val%tag = TAG_NIL
       do k = 1, cn
          val = eval_form(list_first(cl), catch_env)
          if (has_error) exit
          cl = list_rest(cl)
       end do
    end if

    if (.not. has_finally) return
    ! Run finally with a clean error state, so its own forms evaluate
    ! normally -- then either finally's own error wins (it masks
    ! whatever the try/catch above produced, same as Java/Clojure), or
    ! the try/catch outcome above is restored exactly as it was.
    saved_has_error = has_error
    saved_error_value = last_error_value
    has_error = .false.
    l = list_rest(finally_clause%list_val)
    n = list_count(l)
    do k = 1, n
       block
         type(cons_value) :: discard
         discard = eval_form(list_first(l), env)
       end block
       if (has_error) return ! finally's own error propagates instead
       l = list_rest(l)
    end do
    has_error = saved_has_error
    last_error_value = saved_error_value
  end function eval_try

  ! The 1-indexed k-th element of a cons_ref list -- eval_try's own
  ! clause-peeling needs random access into the (short) top-level forms
  ! list, which list_first/list_rest alone would need repeated walks
  ! from the front for.
  function nth_form(l0, k) result(form)
    type(cons_ref), intent(in) :: l0
    integer, intent(in) :: k
    type(cons_value) :: form
    type(cons_ref) :: l
    integer :: i
    l = l0
    do i = 2, k
       l = list_rest(l)
    end do
    form = list_first(l)
  end function nth_form

  ! Is form a list whose head is the symbol name -- (catch ...)/
  ! (finally ...) clause detection for eval_try.
  function clause_head_is(form, name) result(yes)
    type(cons_value), intent(in) :: form
    character(len=*), intent(in) :: name
    logical :: yes
    type(cons_value) :: head
    yes = .false.
    if (form%tag /= TAG_LIST) return
    if (.not. allocated(form%list_val)) return
    if (list_count(form%list_val) == 0) return
    head = list_first(form%list_val)
    yes = (head%tag == TAG_SYMBOL .and. head%str_val == name)
  end function clause_head_is

  ! (defmacro name [params] body): real Clojure's actual syntax (not
  ! mal's (defmacro! name (fn* (params) body))) -- a macro is an
  ! ordinary closure (TAG_FN) with is_macro set, interned in *ns* under
  ! name, same as def.
  !
  ! &form/&env are always prepended to whatever params the user wrote,
  ! same as real defmacro's own macroexpansion does (confirmed against
  ! the real `clojure` CLI: even a macro whose params never name them
  ! still receives them as its first two args) -- eval_macro_head
  ! always supplies them to any macro call, so this special form has
  ! to build the same shape of closure real defmacro's expansion would,
  ! not just the user's own bare params.
  function eval_defmacro(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: name
    type(cons_ref) :: rest
    type(cons_value) :: hd

    name = list_first(list_rest(ast%list_val))
    rest = list_rest(list_rest(ast%list_val))
    ! (defmacro name doc-string? attr-map? [params] body...) -- real
    ! Clojure's own defmacro (core.clj line ~454) skips an optional
    ! leading docstring and/or metadata map before the params vector;
    ! clotran's defmacro special form has to match, since plenty of
    ! core.clj's own macros (let, cond, ...) carry both. Without this,
    ! the docstring itself gets mistaken for the params vector and the
    ! real params vector ends up evaluated as a body form instead of
    ! bound as parameter names.
    if (list_count(rest) > 0) then
       hd = list_first(rest)
       if (hd%tag == TAG_STRING) rest = list_rest(rest)
    end if
    if (list_count(rest) > 0) then
       hd = list_first(rest)
       if (hd%tag == TAG_HASHMAP) rest = list_rest(rest)
    end if
    val%tag = TAG_FN
    allocate(val%fn_val)
    ! Multi-arity: (defmacro name ([p1] b1) ([p2] b2) ...) -- same
    ! clause shape (and same "first element of the first clause is
    ! itself a params collection" test) as eval_fn's own multi-arity
    ! detection. Real core.clj's own `or`/`and` are defined exactly
    ! this way; a defmacro special form that only ever handled a
    ! single params vector silently mis-parsed the whole first clause
    ! as params.
    block
      type(cons_value) :: clause, inner_first
      logical :: multi
      integer :: n_clauses, i
      type(cons_ref) :: clauses

      clause = list_first(rest)
      multi = .false.
      if (clause%tag == TAG_LIST) then
         inner_first = list_first(clause%list_val)
         multi = (inner_first%tag == TAG_VECTOR .or. inner_first%tag == TAG_LIST)
      end if
      if (multi) then
         n_clauses = list_count(rest)
         val%fn_val%params = prepend_form_env_params(list_first(clause%list_val))
         val%fn_val%body = pre_expand(wrap_body(list_rest(clause%list_val)))
         if (n_clauses > 1) then
            allocate(val%fn_val%extra)
            allocate(val%fn_val%extra%ptr)
            val%fn_val%extra%ptr%refcount = 1
            arity_clauses_node_total_allocated = arity_clauses_node_total_allocated + 1
            allocate(val%fn_val%extra%ptr%params(n_clauses - 1))
            allocate(val%fn_val%extra%ptr%bodies(n_clauses - 1))
            clauses = list_rest(rest)
            do i = 1, n_clauses - 1
               clause = list_first(clauses)
               val%fn_val%extra%ptr%params(i) = prepend_form_env_params(list_first(clause%list_val))
               val%fn_val%extra%ptr%bodies(i) = pre_expand(wrap_body(list_rest(clause%list_val)))
               clauses = list_rest(clauses)
            end do
         end if
      else
         val%fn_val%params = prepend_form_env_params(list_first(rest))
         val%fn_val%body = pre_expand(wrap_body(list_rest(rest)))
      end if
    end block
    val%fn_val%env = env
    val%fn_val%is_macro = .true.
    call ns_intern(ns_current(), name%str_val, val)
  end function eval_defmacro

  ! &form/&env, prepended to a [params] vector that doesn't already
  ! name them -- shared by eval_defmacro and eval_defmacro_bang, both
  ! of which build a macro closure whose params come from the user's
  ! own (real Clojure or mal-style) source rather than already
  ! including them the way core.clj's own raw (fn* [&form &env & decl]
  ! ...) bootstrap pattern (let/loop/fn) explicitly does.
  function prepend_form_env_params(user_params) result(new_params)
    type(cons_value), intent(in) :: user_params
    type(cons_value) :: new_params
    type(cons_value), allocatable :: items(:)
    type(cons_value) :: form_sym, env_sym
    integer :: n, i

    form_sym%tag = TAG_SYMBOL
    form_sym%str_val = "&form"
    env_sym%tag = TAG_SYMBOL
    env_sym%str_val = "&env"
    ! binding_count/binding_nth (not vector_count/vector_nth directly)
    ! -- mal's own defmacro! convention allows paren params (pred a b),
    ! not just a vector, same dual shape bind_params already accepts.
    n = binding_count(user_params)
    allocate(items(n + 2))
    items(1) = form_sym
    items(2) = env_sym
    do i = 1, n
       items(i + 2) = binding_nth(user_params, i - 1)
    end do
    new_params = make_vector(items)
  end function prepend_form_env_params

  ! (an earlier, narrower version of this gated pre_expand to only a
  ! macro whose own body mentioned its own name, via a contains_symbol
  ! check, to avoid pre-expanding things unnecessarily -- removed once
  ! pre_expand itself was applied unconditionally below instead; see
  ! NOTES.md for why the gate turned out unnecessary.)

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
    if (allocated(val%fn_val)) then
       val%fn_val%is_macro = .true.
       ! Same &form/&env prepending eval_defmacro needs -- the fn*
       ! expr here is written to mal's own convention (no &form/&env
       ! at all), but eval_macro_head always supplies them to any
       ! macro call regardless of how it was defined.
       val%fn_val%params = prepend_form_env_params(val%fn_val%params)
    end if
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
  !
  ! Real Clojure always supplies &form (the whole raw calling form)
  ! and &env (a compile-time locals map) as the first two args to
  ! EVERY macro call -- a property of invocation, not of how the
  ! macro itself was written (confirmed against the real `clojure`
  ! CLI: even a macro whose own params are just [& decl], never
  ! naming &form/&env, receives them as decl's first two elements
  ! anyway). defmacro's own bootstrap only *looks* like it's adding
  ! them itself (its add-implicit-args helper rewrites [params] into
  ! [&form &env params] before defn sees it) -- but that's it
  ! declaring names for what the caller was always going to supply
  ! regardless. Without this, core.clj's own real fn/let/loop/defmacro
  ! (all written expecting exactly this) get every one of their own
  ! params shifted by two and silently misbound. &env has no real
  ! content here (no compile-time locals tracking) -- always nil.
  subroutine eval_macro_head(ast, macro_val)
    type(cons_value), intent(inout) :: ast
    type(cons_value), intent(in) :: macro_val
    type(cons_value), allocatable :: raw_args(:)
    type(cons_value) :: env_placeholder
    type(env_ref) :: child
    type(cons_ref) :: l
    integer :: n, i
    type(cons_value) :: macro_params, macro_body

    n = list_count(ast%list_val) - 1
    allocate(raw_args(n + 2))
    raw_args(1) = ast
    raw_args(2) = env_placeholder ! nil
    l = list_rest(ast%list_val)
    do i = 1, n
       raw_args(i + 2) = list_first(l)
       l = list_rest(l)
    end do
    child = env_new(macro_val%fn_val%env)
    ! Multi-arity macro dispatch: was missing entirely -- this always
    ! used macro_val%fn_val%params/%body directly (the PRIMARY clause
    ! only), the same bug multi-arity fn* calls would have if
    ! apply_closure didn't call select_clause. A multi-arity defmacro
    ! (core.clj's own `or`/`and`) silently ran the wrong clause for
    ! any call whose arg count didn't match the first one -- confirmed:
    ! (or false true) was binding params for the zero-arg clause and
    ! evaluating ITS body regardless of the 2 real args actually given.
    call select_clause(macro_val, size(raw_args), macro_params, macro_body)
    if (has_error) return
    call bind_params(macro_params, raw_args, child)
    if (has_error) return
    ! macro_expand_depth: a hard safety net, not a fix -- some macro
    ! interactions core.clj itself relies on real Clojure's COMPILE-TIME
    ! frozen macro resolution to terminate (assert-args's own internal
    ! `let` reduction, once `let` becomes the real destructuring macro,
    ! validates ITS OWN bindings via assert-args again -- confirmed
    ! genuine, otherwise endless, mutual recursion; see NOTES.md).
    ! Neither resolving `let` fresh each time (clotran's normal,
    ! correct behavior everywhere else) nor pre_expand-freezing it
    ! ahead of time (tried; broke which env `pairs`/`bindings` resolve
    ! in instead) fully resolves this without a real compile-time Var
    ! model clotran doesn't have yet. Until then: cap macro-expansion
    ! depth so a case like this fails cleanly (a catchable error) up
    ! through the trampoline instead of blowing the real call stack.
    macro_expand_depth = macro_expand_depth + 1
    if (macro_expand_depth > 60) then
       call eval_error("macro expansion too deep (possible runaway macro recursion)")
       macro_expand_depth = macro_expand_depth - 1
       return
    end if
    ast = eval_form(macro_body, child)
    macro_expand_depth = macro_expand_depth - 1
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

  ! Real Clojure compiles a fn/macro's body once, at definition time --
  ! any macro call written directly in that body (not inside a
  ! backtick template, which is DATA until spliced and evaluated
  ! later) gets permanently expanded using whatever that name resolves
  ! to RIGHT THEN, baked into the compiled bytecode forever, regardless
  ! of any LATER redefinition of that name. clotran has no separate
  ! compile step -- every eval_form call re-resolves a macro name from
  ! *ns* fresh -- so without this, a macro whose own body uses another
  ! macro (e.g. core.clj's own assert-args uses `let` internally, in
  ! its self-recursive reduction step) keeps re-resolving that name on
  ! every call. That's silently fine right up until the name gets
  ! REDEFINED later in the same file (core.clj's own `let`, at first
  ! just `(cons 'let* decl)`, becomes the real destructuring macro
  ! partway through -- and that real `let` validates ITS OWN bindings
  ! via assert-args, which reduces via `let` again): genuine, endless
  ! mutual recursion between the two, never seen in real Clojure only
  ! because its compiler already froze assert-args's own internal
  ! `let` to the simple one at assert-args's OWN definition time.
  !
  ! Fix: pre_expand walks a macro body ONCE, right after it's built
  ! (see eval_defmacro), expanding every macro call it finds in actual
  ! code position using *ns* as it stands right now -- mirroring real
  ! Clojure's compile-time semantics without needing a real compiler.
  ! Left alone: anything quoted (data), and everything inside a
  ! quasiquote template except its own unquote/splice-unquote
  ! positions (which ARE code, run each time the template is used) --
  ! pre_expand_qq mirrors qq_expand's own traversal for exactly that
  ! distinction. A sub-expansion that errors (e.g. a forward reference
  ! to something not defined yet) is left exactly as written and
  ! picked up normally at actual call time, same as this project's
  ! usual per-form tolerance elsewhere. Applied unconditionally to
  ! every defmacro body, not just ones that look self-referential: an
  ! earlier, narrower attempt tried to gate this to only assert-args
  ! (matching by name) to avoid the cost/risk of expanding everything,
  ! but the risk was never really there -- expanding a nested macro
  ! call is a purely syntactic substitution (the nested call's own
  ! free variables ride along in the substituted AST and resolve
  ! normally wherever that AST ends up actually running later), so
  ! there's nothing narrower to gain by skipping it. eval_fn (fn*/fn,
  ! and so every defn) applies the same pre_expand to its own clause
  ! bodies for exactly this reason: integer?/even? -- ordinary defns,
  ! not macros -- call `or` internally, and without freezing that
  ! call at define time (long before `let` becomes real), every later
  ! call to integer?/even? re-resolves `or`'s own internal `let` fresh
  ! against *ns* as it stands then -- the real, validating `let` --
  ! which validates its own bindings via assert-args, which calls
  ! even?/integer? again to do it: the same mutual recursion as
  ! assert-args/let directly, just reached through `or` instead.
  recursive function pre_expand(form) result(expanded)
    type(cons_value), intent(in) :: form
    type(cons_value) :: expanded
    type(cons_value) :: head, macro_val, inner
    type(cons_value), allocatable :: items(:)
    type(cons_ref) :: l
    integer :: n, i

    if (form%tag == TAG_VECTOR) then
       ! A vector in code position holds CODE (its elements are
       ! evaluated), so it has to be walked like a list -- most
       ! importantly a let*/loop* bindings vector, whose init
       ! expressions are ordinary code. Returning it untouched (as
       ! "not a list") left every one of those unfrozen: core.clj's
       ! own `drop` kept a raw `(fn [n coll] ... (and (pos? n) s) ...)`
       ! in its `step` binding, so calling drop re-expanded `and` at
       ! runtime -> `let` -> assert-args -> destructure -> partition ->
       ! drop, forever. fn*/defn params vectors go through here too and
       ! are unaffected (bare symbols expand to themselves).
       block
         integer :: vn, vi
         type(cons_value), allocatable :: vitems(:)
         vn = 0
         if (allocated(form%vector_val)) vn = vector_count(form%vector_val)
         allocate(vitems(vn))
         do vi = 1, vn
            vitems(vi) = pre_expand(vector_nth(form%vector_val, vi - 1))
            if (has_error) then
               has_error = .false.
               vitems(vi) = vector_nth(form%vector_val, vi - 1)
            end if
         end do
         expanded = make_vector(vitems)
       end block
       return
    end if
    if (form%tag /= TAG_LIST) then
       expanded = form
       return
    end if
    if (.not. allocated(form%list_val)) then
       expanded = form
       return
    end if
    n = list_count(form%list_val)
    if (n == 0) then
       expanded = form
       return
    end if
    head = list_first(form%list_val)
    if (head%tag == TAG_SYMBOL) then
       if (head%str_val == "quote") then
          expanded = form
          return
       end if
       if (head%str_val == "." .and. n == 3) then
          ! (. target (method args...)) / (. target member): eval_dot
          ! never treats the method/member name as code (real
          ! Clojure's dot-call syntax, not a function call) -- only
          ! pre_expand's OWN generic recursion below doesn't know
          ! that, and previously walked straight into a method name
          ! that happened to match a real macro (e.g. bit-and's own
          ! `(. clojure.lang.Numbers (and x y))` -- "and" IS a macro
          ! in clojure.core), corrupting the method-call form entirely.
          block
            type(cons_value) :: target_e, member_e
            target_e = pre_expand(list_first(list_rest(form%list_val)))
            member_e = list_first(list_rest(list_rest(form%list_val)))
            if (member_e%tag == TAG_LIST) then
               member_e = pre_expand_dot_args(member_e)
            end if
            expanded = make_list([head, target_e, member_e])
          end block
          return
       end if
       if (head%str_val == "quasiquote" .and. n == 2) then
          inner = pre_expand_qq(list_first(list_rest(form%list_val)))
          expanded = make_list([head, inner])
          return
       end if
       if (resolves_to_macro(head%str_val, macro_val)) then
          block
            type(cons_value) :: ast_copy
            ast_copy = form
            ! Same cap eval_macro_head uses for its own runtime expansion,
            ! shared here too: pre_expand's OWN recursion (expanding the
            ! result again, below) is a second, independent recursion on
            ! top of eval_macro_head's -- a mutually-recursive macro pair
            ! (assert-args/let; see NOTES.md) blows the real call stack
            ! through THIS loop just as easily, and eval_macro_head's own
            ! internal cap resets before returning here, so it alone
            ! doesn't see this outer loop repeating.
            macro_expand_depth = macro_expand_depth + 1
            if (macro_expand_depth > 60) then
               macro_expand_depth = macro_expand_depth - 1
               expanded = form
               return
            end if
            call eval_macro_head(ast_copy, macro_val)
            if (has_error) then
               has_error = .false.
               macro_expand_depth = macro_expand_depth - 1
               expanded = form
               return
            end if
            expanded = pre_expand(ast_copy)
            if (has_error) then
               ! The recursive pre_expand above found a FURTHER nested
               ! macro call and computing ITS expansion genuinely
               ! failed (not just "not found yet" -- e.g. assert-args
               ! validating a bindings vector pre_expand doesn't have
               ! real runtime values for, since it's walking a
               ! template, not executing it -- a real, if rare, false
               ! positive). Same tolerance as above: leave THIS form
               ! unexpanded rather than letting a nested macro's own
               ! validation abort the whole containing definition.
               has_error = .false.
               expanded = form
            end if
            macro_expand_depth = macro_expand_depth - 1
          end block
          return
       end if
    end if
    allocate(items(n))
    l = form%list_val
    do i = 1, n
       items(i) = pre_expand(list_first(l))
       if (has_error) then
          ! Same tolerance as the direct-macro-call branch above --
          ! this element contains some deeper nested macro call whose
          ! own expansion genuinely failed; leave it exactly as
          ! written rather than aborting the whole containing form.
          has_error = .false.
          items(i) = list_first(l)
       end if
       l = list_rest(l)
    end do
    expanded = make_list(items)
  end function pre_expand

  ! Companion to pre_expand for a (. target (method args...)) form's
  ! own method-call list: pre_expands every arg, but leaves the method
  ! NAME (the list's own head) untouched -- it's never code, even when
  ! it happens to match a real macro's name (see pre_expand's own "."
  ! case).
  function pre_expand_dot_args(form) result(out)
    type(cons_value), intent(in) :: form
    type(cons_value) :: out
    type(cons_value), allocatable :: items(:)
    type(cons_ref) :: l
    integer :: n, i
    n = list_count(form%list_val)
    allocate(items(n))
    l = form%list_val
    items(1) = list_first(l)
    l = list_rest(l)
    do i = 2, n
       items(i) = pre_expand(list_first(l))
       l = list_rest(l)
    end do
    out = make_list(items)
  end function pre_expand_dot_args

  ! Companion to pre_expand for the inside of a quasiquote template --
  ! same shape as qq_expand's own tag dispatch, but pre-expanding
  ! (rather than evaluating) unquote/splice-unquote content and
  ! otherwise copying the literal template structure untouched. No
  ! nesting-depth tracking, matching qq_expand's own documented
  ! simplification.
  recursive function pre_expand_qq(form) result(out)
    type(cons_value), intent(in) :: form
    type(cons_value) :: out
    type(cons_value) :: head_e, inner
    type(cons_value), allocatable :: items(:)
    type(cons_ref) :: l
    integer :: n, i

    select case (form%tag)
    case (TAG_LIST)
       n = 0
       if (allocated(form%list_val)) n = list_count(form%list_val)
       if (n == 0) then
          out = form
          return
       end if
       if (n == 2) then
          head_e = list_first(form%list_val)
          if (head_e%tag == TAG_SYMBOL .and. &
               (head_e%str_val == "unquote" .or. head_e%str_val == "splice-unquote")) then
             inner = pre_expand(list_first(list_rest(form%list_val)))
             out = make_list([head_e, inner])
             return
          end if
       end if
       allocate(items(n))
       l = form%list_val
       do i = 1, n
          items(i) = pre_expand_qq(list_first(l))
          l = list_rest(l)
       end do
       out = make_list(items)
    case (TAG_VECTOR)
       n = 0
       if (allocated(form%vector_val)) n = vector_count(form%vector_val)
       allocate(items(n))
       do i = 1, n
          items(i) = pre_expand_qq(vector_nth(form%vector_val, i - 1))
       end do
       out = make_vector(items)
    case default
       out = form ! symbols, scalars, ... -- literal template data
    end select
  end function pre_expand_qq

  ! Special-form names never get namespace-qualified or auto-gensym'd
  ! by quasiquote -- they're recognized syntactically here, never
  ! stored in any namespace, so there's nothing to qualify them with.
  function is_special_form(name) result(yes)
    character(len=*), intent(in) :: name
    logical :: yes
    select case (name)
    case ("def!", "def", "defmacro", "defmacro!", "let*", "loop*", "fn*", "if", "do", "quote", "quasiquote", &
         "unquote", "splice-unquote", "eval", "load-file", "in-ns", "ns", "var", ".", "new", &
         "try*", "try", "catch*", "catch")
       yes = .true.
    case default
       ! (.method obj args...) sugar for (. obj (method args...)) --
       ! see eval_form's dispatch -- covers any name, not a fixed list.
       yes = (len(name) > 1 .and. name(1:1) == ".")
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
       m = array_map_empty()
       if (allocated(form%map_val)) then
          block
            type(cons_value), allocatable :: mkeys(:), mvals(:)
            type(array_map_t) :: next_m
            call array_map_entries(form%map_val, mkeys, mvals)
            do i = 1, size(mkeys)
               next_m = array_map_assoc(m, qq_expand(mkeys(i), env), qq_expand(mvals(i), env)) ! never m = ...(m, ...)
               m = next_m
               if (has_error) return
            end do
          end block
       end if
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
  !
  ! Last resort, for a bare clojure.lang.* name only: it denotes a host
  ! CLASS in real Clojure's source (`(instance? clojure.lang.ISeq x)`),
  ! and clotran has no Class objects at all, so it denotes itself --
  ! the keyword of the same name, which is exactly what instance?
  ! matches against. clotran.clj had been writing these out by hand,
  ! one `(def clojure.lang.ISeq :clojure.lang.ISeq)` at a time, "as
  ! core.clj's walk turns up the next one it needs"; this is that same
  ! rule, just applied generally instead of by enumeration. Only
  ! clojure.lang.* gets it -- any other unresolved symbol is still a
  ! real error, as before.
  function eval_symbol(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    logical :: found
    character(len=:), allocatable :: owner
    found = env_find(env, ast, val)
    if (.not. found) found = ns_resolve(ns_current(), ast%str_val, val, owner)
    if (found) return
    if (len(ast%str_val) > 13) then
       if (ast%str_val(1:13) == "clojure.lang." .and. index(ast%str_val(14:), "/") == 0) then
          val%tag = TAG_KEYWORD
          val%str_val = ast%str_val
          return
       end if
    end if
    call eval_error("'" // ast%str_val // "' not found")
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

  ! A set literal's elements are evaluated, same as a vector literal's
  ! -- #{'&} has to become a set holding the SYMBOL &, not the form
  ! (quote &). Missing this made every set literal in core.clj hold
  ! unevaluated forms, so destvec*'s own `(some #{'&} b)` rest-arg
  ! check never matched and [params & body] destructuring silently
  ! dropped its bindings.
  recursive function eval_set(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value), allocatable :: elems(:), vals(:)
    type(cons_value), allocatable :: dummy(:)
    integer :: i, n

    n = 0
    if (allocated(ast%map_val)) then
       call array_map_entries(ast%map_val, elems, dummy)
       n = size(elems)
    end if
    allocate(vals(n))
    do i = 1, n
       vals(i) = eval_form(elems(i), env)
       if (has_error) return
    end do
    val = make_hashset(vals)
  end function eval_set

  ! Keys stay literal; values are evaluated, same as a vector literal.
  recursive function eval_hashmap(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(array_map_t) :: m, next_m
    type(cons_value), allocatable :: keys(:), vals(:)
    integer :: i

    m = array_map_empty()
    if (allocated(ast%map_val)) then
       call array_map_entries(ast%map_val, keys, vals)
       do i = 1, size(keys)
          next_m = array_map_assoc(m, keys(i), eval_form(vals(i), env)) ! never m = ...(m, ...) -- see make_hashmap
          m = next_m
          if (has_error) return
       end do
    end if
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
    case (TAG_SET)
       ! A set is a function of its elements in real Clojure --
       ! (#{'&} x) is the membership test core.clj's own fn/destructure
       ! machinery uses. Backed by the same map_val as a hash-map (every
       ! element mapped to itself), so the lookup is literally the same.
       if (size(args) < 1) then
          call eval_error("set invoked with no arguments")
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
       call eval_error("not a function: " // pr_str(f))
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
  ! evaluated in it. Multi-arity (extra_params/extra_bodies) picks the
  ! matching clause by argument count first.
  function apply_closure(f, args) result(val)
    type(cons_value), intent(in) :: f
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(env_ref) :: child
    type(cons_value) :: params, body
    call select_clause(f, size(args), params, body)
    if (has_error) return
    child = env_new(f%fn_val%env)
    call bind_params(params, args, child)
    val = eval_form(body, child)
  end function apply_closure

  ! Does this one arity clause's params vector accept argc args? Fixed
  ! arity: argc must match exactly. Variadic ('& rest'): argc must be
  ! at least the count of params before '&'.
  function arity_accepts(params, argc) result(bool)
    type(cons_value), intent(in) :: params
    integer, intent(in) :: argc
    logical :: bool
    type(cons_value) :: p
    integer :: n, i, required
    logical :: variadic
    n = binding_count(params)
    variadic = .false.
    required = 0
    do i = 0, n - 1
       p = binding_nth(params, i)
       if (p%tag == TAG_SYMBOL .and. p%str_val == "&") then
          variadic = .true.
          exit
       end if
       required = required + 1
    end do
    if (variadic) then
       bool = (argc >= required)
    else
       bool = (argc == required)
    end if
  end function arity_accepts

  ! Picks the (params, body) clause matching argc args: the primary
  ! one, or one of a multi-arity fn*'s extra clauses. eval_error (real
  ! Clojure's ArityException) if none match.
  subroutine select_clause(f, argc, params, body)
    type(cons_value), intent(in) :: f
    integer, intent(in) :: argc
    type(cons_value), intent(out) :: params, body
    integer :: i

    if (arity_accepts(f%fn_val%params, argc)) then
       params = f%fn_val%params
       body = f%fn_val%body
       return
    end if
    if (allocated(f%fn_val%extra)) then
       do i = 1, size(f%fn_val%extra%ptr%params)
          if (arity_accepts(f%fn_val%extra%ptr%params(i), argc)) then
             params = f%fn_val%extra%ptr%params(i)
             body = f%fn_val%extra%ptr%bodies(i)
             return
          end if
       end do
    end if
    call eval_error("wrong number of args (" // stringify_int(argc) // ")")
  end subroutine select_clause

  function stringify_int(i) result(s)
    integer, intent(in) :: i
    character(len=:), allocatable :: s
    character(len=20) :: buf
    write(buf, '(I0)') i
    s = trim(buf)
  end function stringify_int

  ! Binds params (a list or vector of symbols, optionally ending in
  ! '& rest') to args in child. A missing positional arg binds to nil;
  ! extra args beyond a fixed arity are ignored.
  !
  ! is_recur (default false): real Clojure's recur doesn't go through
  ! ordinary invocation -- it's a direct jump back to the top of the
  ! loop that rebinds each local one-to-one, so when recur supplies
  ! exactly one value for a '& rest' slot, that value becomes the rest
  ! binding AS-IS (already a seq or nil), not re-collected into a new
  ! one-element list the way a normal call collects trailing args.
  ! Confirmed against real Clojure: (f 1 2 (list 3 4)) wraps -> xs is
  ! ((3 4)), but recur-ing with those same 3 values doesn't -> xs is
  ! (3 4). Without this, recur into any variadic clause loops forever:
  ! the rest arg keeps getting re-wrapped in a fresh one-element list,
  ! which is always truthy even once the real payload is nil.
  subroutine bind_params(params, args, child, is_recur)
    type(cons_value), intent(in) :: params
    type(cons_value), intent(in) :: args(:)
    type(env_ref), intent(in) :: child
    logical, intent(in), optional :: is_recur
    type(cons_value) :: p, nilv
    integer :: n, i, ai

    n = binding_count(params)
    ai = 1
    i = 0
    do while (i < n)
       p = binding_nth(params, i)
       if (p%tag == TAG_SYMBOL .and. p%str_val == "&") then
          p = binding_nth(params, i + 1)
          if (present(is_recur)) then
             if (is_recur .and. size(args(ai:)) == 1) then
                call env_set(child, p, args(ai))
                return
             end if
          end if
          ! A rest param with nothing left binds NIL, not () -- real
          ! Clojure's own rule, and core.clj leans on it constantly:
          ! if-let's `(nil? oldform)` guard, `(if next ...)`, `(when
          ! more ...)` and friends all nil-pun the rest arg, and an
          ! empty list is TRUTHY, so binding () made every one of
          ! those take the wrong branch ("if-let requires 1 or 2 forms
          ! after binding vector" on a perfectly ordinary if-let).
          if (size(args(ai:)) == 0) then
             call env_set(child, p, nilv)
          else
             call env_set(child, p, make_list(args(ai:)))
          end if
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
    type(array_map_t) :: m, next_m
    integer :: i
    m = array_map_empty()
    do i = 1, size(args), 2
       ! next_m, never m itself -- m = array_map_assoc(m, ...) (the
       ! same variable read inside the call and written by the
       ! assignment) has been confirmed to silently drop the update in
       ! a build this size, on flang, for a type with defined
       ! assignment this involved; see PersistentHashMap.f90's
       ! node_assoc header for the same hazard found there first.
       next_m = array_map_assoc(m, args(i), args(i + 1))
       m = next_m
    end do
    val%tag = TAG_HASHMAP
    allocate(val%map_val)
    val%map_val = m
  end function make_hashmap

  ! (hash-set x ...): a set from every arg, deduplicated.
  function make_hashset(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(array_map_t) :: m, next_m
    integer :: i
    m = array_map_empty()
    do i = 1, size(args)
       next_m = array_map_assoc(m, args(i), args(i)) ! never m = array_map_assoc(m, ...) -- see make_hashmap
       m = next_m
    end do
    val%tag = TAG_SET
    allocate(val%map_val)
    val%map_val = m
  end function make_hashset

  ! (keys m)/(vals m): every key (or value), as a list -- insertion
  ! order for a small map, hash order once promoted (see
  ! PersistentArrayMap.f90), matching real Clojure exactly either way.
  function builtin_keys(m) result(val)
    type(cons_value), intent(in) :: m
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:), discard(:)
    type(cons_value) :: no_items(0)
    if (m%tag == TAG_HASHMAP .and. allocated(m%map_val)) then
       call array_map_entries(m%map_val, items, discard)
    else
       allocate(items(0))
    end if
    if (size(items) == 0) then
       val = make_list(no_items)
    else
       val = make_list(items)
    end if
  end function builtin_keys

  function builtin_vals(m) result(val)
    type(cons_value), intent(in) :: m
    type(cons_value) :: val
    type(cons_value), allocatable :: items(:), discard(:)
    type(cons_value) :: no_items(0)
    if (m%tag == TAG_HASHMAP .and. allocated(m%map_val)) then
       call array_map_entries(m%map_val, discard, items)
    else
       allocate(items(0))
    end if
    if (size(items) == 0) then
       val = make_list(no_items)
    else
       val = make_list(items)
    end if
  end function builtin_vals

  ! (dissoc m k ...): a new map with those keys removed.
  function builtin_dissoc(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(array_map_t) :: m, next_m
    integer :: i
    m = array_map_empty()
    if (args(1)%tag == TAG_HASHMAP) then
       if (allocated(args(1)%map_val)) m = args(1)%map_val
    end if
    do i = 2, size(args)
       next_m = array_map_dissoc(m, args(i)) ! never m = array_map_dissoc(m, ...) -- see make_hashmap
       m = next_m
    end do
    val%tag = TAG_HASHMAP
    allocate(val%map_val)
    val%map_val = m
  end function builtin_dissoc

  ! (disj s x ...): a new set with those elements removed. Mirrors
  ! dissoc for maps -- same underlying array_map_dissoc, since a set
  ! is a map from each element to itself.
  function builtin_disj(args) result(val)
    type(cons_value), intent(in) :: args(:)
    type(cons_value) :: val
    type(array_map_t) :: m, next_m
    integer :: i
    m = array_map_empty()
    if (args(1)%tag == TAG_SET) then
       if (allocated(args(1)%map_val)) m = args(1)%map_val
    end if
    do i = 2, size(args)
       next_m = array_map_dissoc(m, args(i)) ! never m = array_map_dissoc(m, ...) -- see make_hashmap
       m = next_m
    end do
    val%tag = TAG_SET
    allocate(val%map_val)
    val%map_val = m
  end function builtin_disj

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

    found = ((m%tag == TAG_HASHMAP .or. m%tag == TAG_SET) .and. allocated(m%map_val))
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
    case ("bit-and")
       val = num_bit_and(args)
    case ("bit-or")
       val = num_bit_or(args)
    case ("bit-xor")
       val = num_bit_xor(args)
    case ("bit-not")
       val = num_bit_not(args)
    case ("bit-and-not")
       val = num_bit_and_not(args)
    case ("quot")
       val = num_quot(args)
    case ("rem")
       val = num_rem(args)
    case ("bit-shift-left")
       val = num_shift_left(args)
    case ("bit-shift-right")
       val = num_shift_right(args)
    case ("unsigned-bit-shift-right")
       val = num_ushift_right(args)
    case ("next-id")
       ! clojure.lang.RT/nextID -- gensym's own source of uniqueness
       ! (real core.clj: (symbol (str prefix (. clojure.lang.RT
       ! (nextID))))). Shares gensym_counter so a machine-generated
       ! name can never collide with a reader-level x# auto-gensym.
       gensym_counter = gensym_counter + 1
       val%tag = TAG_INT
       val%int_val = gensym_counter
    case ("first")
       val = rt_first(args(1))
    case ("rest")
       val = rt_rest(args(1))
    case ("next")
       val = rt_next(args(1))
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
    case ("push-thread-bindings")
       val = builtin_push_thread_bindings(args(1))
    case ("pop-thread-bindings")
       val = builtin_pop_thread_bindings()
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
    case ("instance?")
       ! Real core.clj's own instance? does (. c (isInstance x)) --
       ! real reflection clotran doesn't have. clotran.clj overrides
       ! it with this instead: c is one of a small, fixed set of
       ! keyword pseudo-classes clotran.clj itself defines (e.g.
       ! (def clojure.lang.Symbol :clojure.lang.Symbol)) so a bare
       ! `clojure.lang.Symbol` in core.clj's own unmodified source
       ! still evaluates to something -- grows one entry at a time as
       ! core.clj's walk turns up the next pseudo-class it needs.
       val%tag = TAG_BOOL
       val%bool_val = .false.
       if (args(1)%tag == TAG_KEYWORD) then
          select case (args(1)%str_val)
          case ("clojure.lang.Symbol")
             val%bool_val = (args(2)%tag == TAG_SYMBOL)
          case ("clojure.lang.Keyword")
             val%bool_val = (args(2)%tag == TAG_KEYWORD)
          case ("clojure.lang.IPersistentVector")
             val%bool_val = (args(2)%tag == TAG_VECTOR)
          case ("clojure.lang.IPersistentMap")
             val%bool_val = (args(2)%tag == TAG_HASHMAP)
          case ("clojure.lang.ISeq")
             val%bool_val = (args(2)%tag == TAG_LIST)
          case ("String")
             val%bool_val = (args(2)%tag == TAG_STRING)
          case ("Boolean")
             val%bool_val = (args(2)%tag == TAG_BOOL)
          case ("clojure.lang.IMeta")
             ! Everything clotran itself supports metadata on --
             ! matches real Clojure's own IMeta implementers (symbols,
             ! collections, fns), excluding keywords/strings/numbers,
             ! which real Clojure also never allows metadata on.
             val%bool_val = (args(2)%tag == TAG_LIST .or. args(2)%tag == TAG_VECTOR .or. &
                  args(2)%tag == TAG_HASHMAP .or. args(2)%tag == TAG_SYMBOL .or. args(2)%tag == TAG_FN)
          case ("clojure.lang.Counted")
             ! Everything clotran can already count in O(1) -- used by
             ! counted?/empty?; nil is deliberately excluded, matching
             ! real Clojure (empty? falls back to (not (seq coll)) for it).
             val%bool_val = (args(2)%tag == TAG_LIST .or. args(2)%tag == TAG_VECTOR .or. &
                  args(2)%tag == TAG_HASHMAP .or. args(2)%tag == TAG_SET .or. args(2)%tag == TAG_STRING)
          case ("clojure.lang.IPersistentList")
             val%bool_val = (args(2)%tag == TAG_LIST)
          case ("clojure.lang.IDeref")
             val%bool_val = (args(2)%tag == TAG_ATOM .or. args(2)%tag == TAG_VAR)
          case ("clojure.lang.Var")
             val%bool_val = (args(2)%tag == TAG_VAR)
          case ("Integer", "Long", "Short", "Byte", "clojure.lang.BigInt", "BigInteger")
             ! clotran has one integer type (TAG_INT), not Java's tower
             ! of Integer/Long/Short/Byte/BigInteger -- every one of
             ! these pseudo-classes matches it, same simplification as
             ! Numbers' own add/minus/etc. not distinguishing them.
             val%bool_val = (args(2)%tag == TAG_INT)
          case ("Double", "Float", "clojure.lang.BigDecimal", "BigDecimal")
             val%bool_val = (args(2)%tag == TAG_REAL)
          case ("Number", "clojure.lang.Ratio")
             val%bool_val = (args(2)%tag == TAG_INT .or. args(2)%tag == TAG_REAL)
          case ("clojure.lang.Sequential")
             val%bool_val = (args(2)%tag == TAG_LIST .or. args(2)%tag == TAG_VECTOR)
          case ("clojure.lang.IPersistentSet", "clojure.lang.APersistentSet", &
               "clojure.lang.PersistentHashSet")
             val%bool_val = (args(2)%tag == TAG_SET)
          case ("clojure.lang.Fn", "clojure.lang.AFn")
             ! A macro's value is a TAG_FN here (is_macro is a flag on
             ! the closure, see Values.f90) but is NOT a function as
             ! far as fn? is concerned -- real Clojure can't even name
             ! a macro in value position.
             val%bool_val = (args(2)%tag == TAG_BUILTIN)
             if (args(2)%tag == TAG_FN) then
                val%bool_val = .true.
                if (allocated(args(2)%fn_val)) val%bool_val = .not. args(2)%fn_val%is_macro
             end if
          case ("clojure.lang.IFn")
             ! Everything callable, matching real Clojure: fns, and the
             ! collections/keywords that are functions of their contents.
             val%bool_val = (args(2)%tag == TAG_FN .or. args(2)%tag == TAG_BUILTIN .or. &
                  args(2)%tag == TAG_KEYWORD .or. args(2)%tag == TAG_HASHMAP .or. &
                  args(2)%tag == TAG_SET .or. args(2)%tag == TAG_VECTOR)
          case ("clojure.lang.IPersistentCollection", "clojure.lang.Seqable")
             val%bool_val = (args(2)%tag == TAG_LIST .or. args(2)%tag == TAG_VECTOR .or. &
                  args(2)%tag == TAG_HASHMAP .or. args(2)%tag == TAG_SET)
          case ("clojure.lang.Associative")
             val%bool_val = (args(2)%tag == TAG_HASHMAP .or. args(2)%tag == TAG_VECTOR)
          case ("clojure.lang.Named")
             val%bool_val = (args(2)%tag == TAG_SYMBOL .or. args(2)%tag == TAG_KEYWORD)
          case ("Character")
             ! No char type here -- the reader makes one-character
             ! strings, and seq over a string yields those.
             val%bool_val = .false.
          case default
             ! A clojure.lang.* interface clotran genuinely has no
             ! analogue for (IChunkedSeq, MultiFn, ...): "no, this
             ! value isn't one of those" is the correct answer, and
             ! the one core.clj's own guards are written to branch on
             ! -- erroring instead turned every such guard into a hard
             ! failure. Anything else (a bare `Foo`) is still a real
             ! missing entry, so it still errors.
             if (len(args(1)%str_val) > 13) then
                if (args(1)%str_val(1:13) == "clojure.lang.") then
                   val%bool_val = .false.
                else
                   call eval_error("instance?: unknown pseudo-class '" // args(1)%str_val // "'")
                end if
             else
                call eval_error("instance?: unknown pseudo-class '" // args(1)%str_val // "'")
             end if
          end select
       else
          call eval_error("instance?: c must be one of clotran.clj's registered pseudo-classes")
       end if
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
       ! (symbol name) and (symbol ns name), same as keyword below.
       val%tag = TAG_SYMBOL
       if (size(args) >= 2) then
          if (args(1)%tag == TAG_NIL) then
             val%str_val = args(2)%str_val
          else
             val%str_val = args(1)%str_val // "/" // args(2)%str_val
          end if
       else
          val%str_val = args(1)%str_val
       end if
    case ("keyword")
       ! (keyword name) and (keyword ns name) -- real Clojure has both,
       ! and clojure.lang.Keyword/intern (which clotran.clj maps here)
       ! is called with two args by destructuring's own :keys handling.
       ! A nil namespace just means unqualified.
       if (size(args) >= 2) then
          val%tag = TAG_KEYWORD
          if (args(1)%tag == TAG_NIL) then
             val%str_val = args(2)%str_val
          else
             val%str_val = args(1)%str_val // "/" // args(2)%str_val
          end if
       else if (args(1)%tag == TAG_KEYWORD) then
          val = args(1)
       else
          val%tag = TAG_KEYWORD
          val%str_val = args(1)%str_val
       end if
    case ("hash-map")
       val = make_hashmap(args)
    case ("hash-set")
       val = make_hashset(args)
    case ("disj")
       val = builtin_disj(args)
    case ("set?")
       val%tag = TAG_BOOL
       val%bool_val = (args(1)%tag == TAG_SET)
    case ("contains?")
       val%tag = TAG_BOOL
       val%bool_val = .false.
       if (args(1)%tag == TAG_HASHMAP .or. args(1)%tag == TAG_SET) then
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

  ! (push-thread-bindings m): m is a map of Var -> new value (real
  ! core.clj's own `binding` builds it via `(hash-map (var x) v ...)`).
  ! Pushes a new dynamic value onto every Var in m, and remembers how
  ! many so the matching pop-thread-bindings undoes exactly this frame
  ! (bindings nest: an inner `binding` on the same Var must pop back to
  ! the outer one, not the root). See Atom.f90's var_dyn_push/dyn_stack.
  function builtin_push_thread_bindings(m) result(val)
    type(cons_value), intent(in) :: m
    type(cons_value) :: val
    type(cons_value), allocatable :: keys(:), vals(:), grown(:)
    integer, allocatable :: grown_sizes(:)
    integer :: i, n, old_n

    val%tag = TAG_NIL
    if (.not. allocated(m%map_val)) return
    call array_map_entries(m%map_val, keys, vals)
    n = size(keys)
    do i = 1, n
       call var_dyn_push(keys(i), vals(i))
    end do

    old_n = 0
    if (allocated(binding_stack_vars)) old_n = size(binding_stack_vars)
    allocate(grown(old_n + n))
    if (old_n > 0) grown(1:old_n) = binding_stack_vars(1:old_n)
    grown(old_n + 1:old_n + n) = keys(1:n)
    call move_alloc(grown, binding_stack_vars)

    old_n = 0
    if (allocated(binding_stack_frame_sizes)) old_n = size(binding_stack_frame_sizes)
    allocate(grown_sizes(old_n + 1))
    if (old_n > 0) grown_sizes(1:old_n) = binding_stack_frame_sizes(1:old_n)
    grown_sizes(old_n + 1) = n
    call move_alloc(grown_sizes, binding_stack_frame_sizes)
  end function builtin_push_thread_bindings

  ! (pop-thread-bindings): undoes the most recent push-thread-bindings.
  function builtin_pop_thread_bindings() result(val)
    type(cons_value) :: val
    type(cons_value), allocatable :: shrunk(:)
    integer, allocatable :: shrunk_sizes(:)
    integer :: i, n, total, frames

    val%tag = TAG_NIL
    if (.not. allocated(binding_stack_frame_sizes)) return
    frames = size(binding_stack_frame_sizes)
    if (frames == 0) return
    n = binding_stack_frame_sizes(frames)
    total = size(binding_stack_vars)
    do i = total - n + 1, total
       call var_dyn_pop(binding_stack_vars(i))
    end do

    if (total - n > 0) then
       allocate(shrunk(total - n))
       shrunk(:) = binding_stack_vars(1:total - n)
       call move_alloc(shrunk, binding_stack_vars)
    else
       deallocate(binding_stack_vars)
    end if

    if (frames - 1 > 0) then
       allocate(shrunk_sizes(frames - 1))
       shrunk_sizes(:) = binding_stack_frame_sizes(1:frames - 1)
       call move_alloc(shrunk_sizes, binding_stack_frame_sizes)
    else
       deallocate(binding_stack_frame_sizes)
    end if
  end function builtin_pop_thread_bindings

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
  ! (fn* name? [params] body...): single arity, as before. (fn* name?
  ! ([p1] b1...) ([p2] b2...) ...): multi-arity -- each clause is
  ! itself a list here, unlike the single-arity shorthand where the
  ! params vector comes straight after the (optional) name. Dispatched
  ! by argument count at call time (select_clause), not expanded away
  ! here -- one runtime closure shape either way.
  !
  ! recur: every fn* (named or not) also binds the symbol "recur" to
  ! itself in this same throwaway layer -- real Clojure's own recur
  ! (inside a plain fn, not a loop) means exactly "tail-call the
  ! enclosing fn again", which is now just an ordinary call to
  ! whatever recur resolves to. Reuses the exact same self-reference
  ! machinery a named fn* already needed, arity dispatch and TCO
  ! included, for free -- no separate special form. Real recur also
  ! enforces (at compile time) that it's only used in tail position
  ! and matches its enclosing clause's own arity exactly; this doesn't
  ! check either, a real but low-risk simplification since a plain
  ! call already dispatches to whichever arity matches, and no
  ! correctly-written recur call would ever mismatch on purpose. loop
  ! (a distinct recur target from a fn) isn't built yet.
  function eval_fn(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_ref) :: rest, body_forms, clauses
    type(cons_value) :: second, name, clause, recur_sym
    type(env_ref) :: fn_env
    logical :: named, multi
    integer :: n_clauses, i

    rest = list_rest(ast%list_val)
    second = list_first(rest)
    named = (second%tag == TAG_SYMBOL)

    val%tag = TAG_FN
    allocate(val%fn_val)
    fn_env = env_new(env)
    if (named) then
       name = second
       rest = list_rest(rest)
    end if

    ! Multi-arity iff this is a list whose OWN first element is itself
    ! a params collection (vector or list) -- not just any list, since
    ! this project (like mal) also allows single-arity params written
    ! with parens, (fn* (a b) body), which is a plain flat list of
    ! symbols, not a list of clauses. A clause's own first element is
    ! never a bare symbol (no destructuring, so every real param is
    ! one), which is what tells the two apart.
    clause = list_first(rest)
    multi = .false.
    if (clause%tag == TAG_LIST) then
       block
         type(cons_value) :: inner_first
         inner_first = list_first(clause%list_val)
         multi = (inner_first%tag == TAG_VECTOR .or. inner_first%tag == TAG_LIST)
       end block
    end if
    if (multi) then
       n_clauses = list_count(rest)
       val%fn_val%params = list_first(clause%list_val)
       val%fn_val%body = wrap_body(list_rest(clause%list_val))
       if (n_clauses > 1) then
          allocate(val%fn_val%extra)
          allocate(val%fn_val%extra%ptr)
          val%fn_val%extra%ptr%refcount = 1
          arity_clauses_node_total_allocated = arity_clauses_node_total_allocated + 1
          allocate(val%fn_val%extra%ptr%params(n_clauses - 1))
          allocate(val%fn_val%extra%ptr%bodies(n_clauses - 1))
          clauses = list_rest(rest)
          do i = 1, n_clauses - 1
             clause = list_first(clauses)
             val%fn_val%extra%ptr%params(i) = list_first(clause%list_val)
             val%fn_val%extra%ptr%bodies(i) = wrap_body(list_rest(clause%list_val))
             clauses = list_rest(clauses)
          end do
       end if
    else
       val%fn_val%params = list_first(rest)
       body_forms = list_rest(rest)
       val%fn_val%body = wrap_body(body_forms)
    end if

    val%fn_val%env = fn_env
    if (named) call env_set(fn_env, name, val)
    recur_sym%tag = TAG_SYMBOL
    recur_sym%str_val = "recur"
    call env_set(fn_env, recur_sym, val)
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
  !
  ! pre_expand happens HERE, on the value form, rather than in eval_fn
  ! on each closure's body: a `def` runs once per definition, but
  ! eval_fn runs once per closure VALUE constructed -- including every
  ! throwaway closure a macro builds while expanding (destructure
  ! alone builds two on every call). Freezing there re-expanded each
  ! body from scratch every time, and since expanding a macro itself
  ! builds more closures, the cost compounded until bootstrap simply
  ! stopped finishing (confirmed: pre_expand -> eval_fn -> pre_expand
  ! -> eval_macro_head -> eval_fn ... all the way down a sampled
  ! stack). Once per def is what a real compiler does anyway, and it's
  ! the same freeze: (def integer? (fn* [n] (or ...))) gets its `or`
  ! (and the `let` that or expands into) resolved against *ns* as it
  ! stands at definition time, so calling integer? later never
  ! re-resolves `let` against the real, validating one -- which would
  ! call even?, which calls integer?, forever.
  function eval_def(ast, env) result(val)
    type(cons_value), intent(in) :: ast
    type(env_ref), intent(in) :: env
    type(cons_value) :: val
    type(cons_value) :: sym

    sym = list_first(list_rest(ast%list_val))
    val = eval_form(pre_expand(list_first(list_rest(list_rest(ast%list_val)))), env)
    if (has_error) return
    call apply_macro_metadata(sym, val)
    call ns_intern(ns_current(), sym%str_val, val)
  end function eval_def

  ! Real Clojure derives macro-ness from the Var's own metadata
  ! (:macro true) -- real core.clj defines let/loop/fn exactly this
  ! way, (def ^{:macro true} name (fn* ...)), before defmacro itself
  ! exists yet to bootstrap with. No separate Var here (see
  ! Namespace.f90), so this translates :macro metadata straight onto
  ! the closure itself instead, at def time -- the same simplification
  ! is_macro already is.
  subroutine apply_macro_metadata(sym, val)
    type(cons_value), intent(in) :: sym
    type(cons_value), intent(inout) :: val
    type(cons_value) :: macro_key, macro_val

    if (val%tag /= TAG_FN) return
    if (.not. allocated(val%fn_val)) return
    if (.not. allocated(sym%meta_val)) return
    if (.not. associated(sym%meta_val%ptr)) return
    if (sym%meta_val%ptr%val%tag /= TAG_HASHMAP) return
    if (.not. allocated(sym%meta_val%ptr%val%map_val)) return

    macro_key%tag = TAG_KEYWORD
    macro_key%str_val = "macro"
    if (.not. array_map_contains(sym%meta_val%ptr%val%map_val, macro_key)) return
    macro_val = rt_get(sym%meta_val%ptr%val, macro_key)
    if (macro_val%tag == TAG_NIL) return
    if (macro_val%tag == TAG_BOOL .and. .not. macro_val%bool_val) return
    val%fn_val%is_macro = .true.
  end subroutine apply_macro_metadata

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
