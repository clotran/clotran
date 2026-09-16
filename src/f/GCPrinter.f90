! GCPrinter: values in the GC heap, back to text.
!
! Built and tested standalone -- nothing uses it yet. See PLAN.md
! 3c-2/3d.
!
! Written now, before the evaluator switch, for two reasons beyond
! eventually needing it:
!
!   1. It is the first thing that walks EVERY structure in the new
!      data layer at once -- list, vector, both map representations,
!      text, immediates. A representation mistake that each module's
!      own tests miss shows up here immediately.
!   2. Debugging the switch without being able to print a value would
!      be miserable.
!
! `readable` mirrors clotran's existing printer (pr-str versus
! print-str): readable escapes strings and prints characters as \a,
! not-readable writes their contents raw. That distinction is real
! Clojure's, and getting it wrong is how (println "a\nb") starts
! printing quotes.
module GCPrinter
  use GC
  use GCList
  use GCVector
  use GCAssoc
  use, intrinsic :: ieee_arithmetic
  implicit none
  private

  ! Realising a lazy seq means CALLING its thunk, and only the
  ! evaluator can call anything -- but the evaluator sits above this
  ! module, so it cannot be called from here directly. The evaluator
  ! hands its forcer down at startup instead, exactly the dependency
  ! inversion clotran's own rt_set_lazy_forcer already uses.
  !
  ! It must be a MODULE procedure, not an internal one: flang
  ! segfaults passing a host-associated internal procedure as a
  ! callback on macOS/ARM64 (NOTES.md), which is also rule 5 of the
  ! native-buffer rules in PLAN.md.
  abstract interface
     subroutine forcer_i(v)
       import :: gc_value
       type(gc_value), intent(in) :: v
     end subroutine forcer_i
  end interface
  procedure(forcer_i), pointer, save :: lazy_forcer => null()

  public :: gcp_str, gcp_set_forcer

contains

  subroutine gcp_set_forcer(f)
    procedure(forcer_i) :: f
    lazy_forcer => f
  end subroutine gcp_set_forcer

  recursive function gcp_str(v, readable) result(s)
    type(gc_value), intent(in) :: v
    logical, intent(in) :: readable
    character(len=:), allocatable :: s
    character(len=32) :: buf

    select case (v%tag)
    case (GCT_NIL)
       s = "nil"
    case (GCT_BOOL)
       if (v%ival /= 0) then
          s = "true"
       else
          s = "false"
       end if
    case (GCT_INT)
       write(buf, '(I0)') v%ival
       s = trim(buf)
    case (GCT_REAL)
       ! The symbolic values print as the reader macro that makes
       ! them, since they have no literal spelling otherwise --
       ! anything else would not read back.
       if (ieee_is_nan(v%rval)) then
          s = "##NaN"
       else if (.not. ieee_is_finite(v%rval)) then
          if (v%rval > 0.0d0) then
             s = "##Inf"
          else
             s = "##-Inf"
          end if
       else
          s = real_str(v%rval)
       end if
    case (GCT_CHAR)
       if (readable) then
          s = char_readable(v%ival)
       else
          s = achar(v%ival)
       end if
    case (GCT_STR)
       if (readable) then
          s = quoted(gc_ref_text(v%ref))
       else
          s = gc_ref_text(v%ref)
       end if
    case (GCT_SYM)
       s = gc_ref_text(v%ref)
    case (GCT_KEY)
       s = ":" // gc_ref_text(v%ref)
    case default
       s = obj_str(v, readable)
    end select
  end function gcp_str

  recursive function obj_str(v, readable) result(s)
    type(gc_value), intent(in) :: v
    logical, intent(in) :: readable
    character(len=:), allocatable :: s
    type(gc_value) :: p
    type(gc_value), allocatable :: keys(:), vals(:)
    integer :: i, n
    type(gc_value) :: none(0)

    select case (gc_kind(v))
    case (OBJ_CONS)
       s = "("
       p = v
       i = 0
       do while (gcl_is(p) .and. gcl_count(p) > 0)
          if (i > 0) s = s // " "
          s = s // gcp_str(gcl_first(p), readable)
          p = gcl_rest(p, none)
          i = i + 1
       end do
       s = s // ")"
    case (OBJ_VECTOR)
       s = "["
       n = gcv_count(v)
       do i = 0, n - 1
          if (i > 0) s = s // " "
          s = s // gcp_str(gcv_nth(v, i), readable)
       end do
       s = s // "]"
    case (OBJ_MAP, OBJ_HAMT)
       ! Both representations print identically -- which is the point
       ! of the promotion being invisible. A map that printed
       ! differently once it crossed 8 entries would be a leak of the
       ! implementation into the language.
       call gca_entries(v, keys, vals)
       s = "{"
       do i = 1, size(keys)
          if (i > 1) s = s // ", "
          s = s // gcp_str(keys(i), readable) // " " // gcp_str(vals(i), readable)
       end do
       s = s // "}"
    case (OBJ_LAZY)
       ! Printing a lazy seq realises it, one cell at a time, which is
       ! what real Clojure does too -- printing is a use, and a use
       ! forces. An unrealised seq with no forcer registered prints as
       ! a marker rather than lying about being empty.
       if (.not. associated(lazy_forcer)) then
          s = "#<lazy>"
          return
       end if
       s = "("
       p = v
       i = 0
       do
          call lazy_forcer(p)
          if (gc_i1(p) /= LAZY_CONS) exit
          if (i > 0) s = s // " "
          s = s // gcp_str(gc_slot(p, 2), readable)
          p = gc_slot(p, 3)
          i = i + 1
          if (.not. (gc_kind(p) == OBJ_LAZY)) then
             ! The tail became a concrete seq: print the rest of it
             ! inside these same parens rather than nesting. Both shapes
             ! a tail can take -- a list, or a VIEW over an indexable --
             ! because (cons 1 "ab") leaves a string view as the tail.
             if (gc_kind(p) == OBJ_CONS) then
                do while (gcl_count(p) > 0)
                   s = s // " " // gcp_str(gcl_first(p), readable)
                   p = gcl_rest(p, none)
                end do
             else if (gc_kind(p) == OBJ_SEQ) then
                s = s // " " // inner_of(gcp_str(p, readable))
             end if
             exit
          end if
       end do
       s = s // ")"
    case (OBJ_SEQ)
       ! A seq VIEW prints as the sequence it denotes, not as the
       ! collection it borrows from: (seq [1 2 3]) is (1 2 3), and
       ! (rest [1 2 3]) is (2 3) rather than [2 3]. Walking it here
       ! directly rather than through the evaluator keeps the printer
       ! below it, which is what lets the printer be built first.
       block
         type(gc_value) :: src
         type(gc_value), allocatable :: ks(:), vls(:)
         integer :: at, total, k
         character(len=:), allocatable :: t
         src = gc_slot(v, 1)
         at = gc_i1(v)
         s = "("
         if (gcv_is(src)) then
            total = gcv_count(src)
            do k = at, total - 1
               if (k > at) s = s // " "
               s = s // gcp_str(gcv_nth(src, k), readable)
            end do
         else if (gca_is(src)) then
            call gca_entries(src, ks, vls)
            do k = at, size(ks) - 1
               if (k > at) s = s // " "
               s = s // "[" // gcp_str(ks(k+1), readable) // " " // &
                    gcp_str(vls(k+1), readable) // "]"
            end do
         else if (gc_kind(src) == OBJ_SET) then
            call gca_entries(gc_slot(src, 1), ks, vls)
            do k = at, size(ks) - 1
               if (k > at) s = s // " "
               s = s // gcp_str(ks(k+1), readable)
            end do
         else if (src%tag == GCT_STR) then
            t = gc_ref_text(src%ref)
            do k = at, len(t) - 1
               if (k > at) s = s // " "
               s = s // gcp_str(gc_char(t(k+1:k+1)), readable)
            end do
         end if
         s = s // ")"
       end block
    case (OBJ_SET)
       ! #{...}, not the backing map's {k v} pairs -- a set that
       ! printed as a map would be the representation leaking out.
       block
         type(gc_value), allocatable :: ks(:), vls(:)
         integer :: k
         call gca_entries(gc_slot(v, 1), ks, vls)
         s = "#{"
         do k = 1, size(ks)
            if (k > 1) s = s // " "
            s = s // gcp_str(ks(k), readable)
         end do
         s = s // "}"
       end block
    case (OBJ_CLOSURE)
       s = "#<fn>"
    case (OBJ_REGEX)
       ! A Pattern prints as its own source text, readable or not --
       ! (str #"a.b") and (pr-str #"a.b") both give #"a.b", which is
       ! what real Clojure's Pattern.toString does too.
       s = '#"' // gcp_str(gc_slot(v, 1), .false.) // '"'
    case (OBJ_MATCHER)
       s = "#<matcher>"
    case (OBJ_WRITER)
       s = "#<writer>"
    case (OBJ_ERR)
       ! The shape Clojure prints a thrown thing in, minus the trace
       ! there is nothing to fill in with.
       block
         type(gc_value) :: dat
         s = "#error {:class " // gcp_str(gc_slot(v, 1), .false.) // &
              ", :message " // gcp_str(gc_slot(v, 2), .true.)
         dat = gc_slot(v, 3)
         if (dat%tag /= GCT_NIL) s = s // ", :data " // gcp_str(dat, .true.)
         s = s // "}"
       end block
    case (OBJ_META)
       ! Metadata is not printed by default -- *print-meta* is false --
       ! so a wrapped value prints as the value. Without this every
       ! hinted form in core.clj printed as #<object>, which made the
       ! load report name forms nobody could identify.
       s = gcp_str(gc_slot(v, 1), readable)
    case (OBJ_SB)
       s = gcp_str(gc_slot(v, 1), readable)
    case (OBJ_TYPE)
       s = gcp_str(gc_slot(v, 1), .false.)
    case (OBJ_INST)
       ! Clojure prints #object[user.Foo 0x1f2e3d "user.Foo@1f2e3d"].
       ! The identity hash is left out: there is no address to print
       ! -- the GC is index-based -- and inventing one would make two
       ! runs of the same program print differently for no reason.
       s = "#object[" // gcp_str(gc_slot(gc_slot(v, 1), 1), .false.) // "]"
    case (OBJ_MULTIFN)
       s = "#<multifn " // gcp_str(gc_slot(v, 1), .false.) // ">"
    case (OBJ_ATOM)
       s = "#<atom " // gcp_str(gc_slot(v, 1), readable) // ">"
    case (OBJ_VAR)
       s = "#'" // gcp_str(gc_slot(v, 4), .false.)
    case (OBJ_NS)
       ! Namespace.toString is its NAME -- (str *ns*) is "clojure.core"
       ! -- and only pr's #object[...] form names the class. Printing
       ! the wrapper for both made namespace-munge, which is
       ! (.replace (str ns) \- \_), hand deftype the class name
       ! "#<ns clojure.core>.Point".
       if (readable) then
          s = "#<ns " // gcp_str(gc_slot(v, 1), .false.) // ">"
       else
          s = gcp_str(gc_slot(v, 1), .false.)
       end if
    case (OBJ_ENV)
       s = "#<env>"
    case default
       s = "#<object>"
    end select
  end function obj_str

  ! The elements of a printed seq, without its parentheses, so a
  ! tail can be spliced into the parens already open rather than
  ! nested inside a second pair.
  function inner_of(t) result(out)
    character(len=*), intent(in) :: t
    character(len=:), allocatable :: out
    out = t
    if (len(t) >= 2) then
       if (t(1:1) == "(" .and. t(len(t):len(t)) == ")") out = t(2:len(t)-1)
    end if
  end function inner_of

  ! Trailing zeros trimmed but always at least one decimal, so a
  ! double prints as 2.0 rather than 2 -- otherwise it reads back as an
  ! integer, which is a round-trip failure rather than a cosmetic one.
  function real_str(r) result(s)
    real(gc_dp), intent(in) :: r
    character(len=:), allocatable :: s
    character(len=32) :: buf
    integer :: i
    write(buf, '(F0.10)') r
    s = trim(buf)
    i = len(s)
    do while (i > 1)
       if (s(i:i) /= "0") exit
       if (s(i-1:i-1) == ".") exit
       i = i - 1
    end do
    s = s(1:i)
    if (s(1:1) == ".") s = "0" // s
  end function real_str

  function quoted(t) result(s)
    character(len=*), intent(in) :: t
    character(len=:), allocatable :: s
    integer :: i
    s = '"'
    do i = 1, len(t)
       select case (t(i:i))
       case ('"');       s = s // '\"'
       case (achar(92)); s = s // achar(92) // achar(92)
       case (achar(10)); s = s // achar(92) // "n"
       case (achar(9));  s = s // achar(92) // "t"
       case default;     s = s // t(i:i)
       end select
    end do
    s = s // '"'
  end function quoted

  ! The named characters, matching real Clojure's reader so what is
  ! printed can be read back.
  function char_readable(code) result(s)
    integer, intent(in) :: code
    character(len=:), allocatable :: s
    select case (code)
    case (10); s = achar(92) // "newline"
    case (32); s = achar(92) // "space"
    case (9);  s = achar(92) // "tab"
    case (13); s = achar(92) // "return"
    case (8);  s = achar(92) // "backspace"
    case (12); s = achar(92) // "formfeed"
    case default; s = achar(92) // achar(code)
    end select
  end function char_readable

end module GCPrinter
