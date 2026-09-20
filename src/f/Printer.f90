! Printer: values in the GC heap, back to text.
!
! Built and tested standalone before the evaluator, for two reasons
! beyond eventually needing it:
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
module Printer
  use GC
  use PersistentList
  use PersistentVector
  use Assoc
  use NativeArray
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
    case (GCT_RATIO)
       ! n/d, the same spelling the reader takes. Always in normal
       ! form, so there is nothing to reduce here.
       block
         character(len=32) :: dbuf
         write(buf, '(I0)') gc_numerator(v)
         write(dbuf, '(I0)') gc_denominator(v)
         s = trim(buf) // "/" // trim(dbuf)
       end block
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
          ! A character is a CODE POINT, which is 32-bit however wide
          ! the integer field is -- narrowing here is exact, not a
          ! truncation.
          s = char_readable(int(v%ival, kind=4))
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
          if (gc_i1(p) == LAZY_DELEG) then
             ! realised into a seq that stays itself (a ChunkedCons):
             ! its elements belong inside these parens
             block
               character(len=:), allocatable :: tl
               tl = inner_of(gcp_str(gc_slot(p, 2), readable))
               if (len(tl) > 0) then
                  if (i > 0) s = s // " "
                  s = s // tl
               end if
             end block
             exit
          end if
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
    case (OBJ_CHUNKSEQ)
       ! A ChunkedCons: its chunk's elements, then whatever follows,
       ! inside the same parens.
       block
         type(gc_value) :: c, b, more
         integer :: k
         character(len=:), allocatable :: tl
         c = gc_slot(v, 1)
         b = gc_slot(c, 1)
         s = "("
         do k = gc_i1(c), gc_i2(c) - 1
            if (k > gc_i1(c)) s = s // " "
            if (b%tag == GCT_VEC) then
               s = s // gcp_str(gc_vec_get(b, k + 1), readable)
            else
               s = s // gcp_str(gcv_nth(b, k), readable)
            end if
         end do
         more = gc_slot(v, 2)
         if (more%tag /= GCT_NIL) then
            tl = inner_of(gcp_str(more, readable))
            if (len(tl) > 0) s = s // " " // tl
         end if
         s = s // ")"
       end block
    case (OBJ_CHUNK)
       s = "#<chunk>"
    case (OBJ_CHUNKBUF)
       s = "#<chunk-buffer>"
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
         else if (gc_kind(src) == OBJ_ARRAY) then
            ! (seq some-array). Without this the walk found no branch
            ! and printed (), while first and nth on the same seq
            ! answered correctly -- a disagreement between reading a
            ! value and showing it.
            total = array_len_for_print(src)
            do k = at, total - 1
               if (k > at) s = s // " "
               s = s // gcp_str(array_elem_for_print(src, k + 1), readable)
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
    case (OBJ_TASK)
       s = "#object[java.util.concurrent.FutureTask]"
    case (OBJ_VOLATILE)
       s = "#<volatile " // gcp_str(gc_slot(v, 1), readable) // ">"
    case (OBJ_DELAY)
       ! Clojure shows #object[clojure.lang.Delay 0x.. {:status :pending,
       ! :val nil}]. Same two facts, in clotran's own #<...> shape.
       if (gc_i1(v) /= 0) then
          s = "#<delay " // gcp_str(gc_slot(v, 2), readable) // ">"
       else
          s = "#<delay pending>"
       end if
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
       ! The PRINT form, for pr, print, prn and any namespace nested in
       ! a collection -- Clojure shows #object[clojure.lang.Namespace
       ! 0x.. user] for all of those, including under `str`, because a
       ! collection's toString goes through the print path.
       !
       ! `str` on a namespace DIRECTLY is the exception, and it is not
       ! this function's business: core.clj's str is (. x (toString)),
       ! so it is handled in B_TOSTRING. Doing it here on *print-readably*
       ! instead made (str *ns*) right and (pr-str *ns*), (print-str *ns*)
       ! and (str [*ns*]) all wrong.
       s = "#<ns " // gcp_str(gc_slot(v, 1), .false.) // ">"
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

  ! Double.toString: the SHORTEST decimal that reads back as this same
  ! double, laid out the way Java lays it out.
  !
  ! The old version wrote (F0.10) into a 32-character buffer, which was
  ! wrong twice over. It TRUNCATED -- 0.479425538604203 printed as
  ! 0.4794255386, which reads back as a different double, so pr-str no
  ! longer round-tripped -- and it overflowed the buffer outright on
  ! Double/MAX_VALUE, whose fixed-point form is 309 digits long.
  !
  ! Shortest-round-trip is found by asking: write the value with p
  ! significant digits, read it back, and take the first p that gives
  ! the same bits. Seventeen always suffices for a double, so the loop
  ! terminates; most values stop at two or three.
  !
  ! Java's layout rule, which is not the same as Fortran's: plain
  ! decimal while 1e-3 <= |d| < 1e7, scientific outside that, and
  ! always at least one digit after the point.
  function real_str(r) result(s)
    real(gc_dp), intent(in) :: r
    character(len=:), allocatable :: s, digits
    character(len=40) :: buf
    character(len=16) :: fmt
    real(gc_dp) :: back
    integer :: p, st, e10, i, dp_at
    logical :: neg

    if (r == 0.0_gc_dp) then
       s = "0.0"
       if (ieee_copy_sign(1.0_gc_dp, r) < 0.0_gc_dp) s = "-0.0"
       return
    end if

    do p = 1, 17
       write(fmt, '(A,I0,A)') "(ES0.", p - 1, "E3)"
       write(buf, fmt) r
       read(buf, *, iostat=st) back
       if (st == 0 .and. back == r) exit
    end do
    if (p > 17) p = 17

    ! buf is now [-]d.ddddE[+-]nnn -- split it into the digit string
    ! and the power of ten the first digit carries.
    s = trim(adjustl(buf))
    neg = (s(1:1) == "-")
    if (neg) s = s(2:)
    i = index(s, "E")
    read(s(i+1:), *) e10
    digits = s(1:1) // s(3:i-1)
    ! Trailing zeros carry no information once the value round-trips.
    i = len(digits)
    do while (i > 1)
       if (digits(i:i) /= "0") exit
       i = i - 1
    end do
    digits = digits(1:i)

    if (e10 >= -3 .and. e10 < 7) then
       ! Plain decimal: the point goes after e10+1 digits.
       dp_at = e10 + 1
       if (dp_at <= 0) then
          s = "0." // repeat("0", -dp_at) // digits
       else if (dp_at >= len(digits)) then
          s = digits // repeat("0", dp_at - len(digits)) // ".0"
       else
          s = digits(1:dp_at) // "." // digits(dp_at+1:)
       end if
    else
       ! Scientific, one digit before the point.
       if (len(digits) == 1) then
          s = digits // ".0"
       else
          s = digits(1:1) // "." // digits(2:)
       end if
       write(buf, '(I0)') e10
       s = s // "E" // trim(buf)
    end if
    if (neg) s = "-" // s
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
  ! An array's own shape, for printing a seq over one. The offset,
  ! stride and extents of a SLICE live in slot 2; a base array has
  ! none and is the degenerate view (0, 1, its own extents). The
  ! evaluator has the same arithmetic against its own helpers -- this
  ! module sits below it and cannot call them.
  function array_len_for_print(v) result(n)
    type(gc_value), intent(in) :: v
    integer :: n
    type(gc_value) :: sl, e
    integer, allocatable :: ext(:)
    n = 0
    sl = gc_slot(v, 2)
    if (gcv_is(sl)) then
       ! Through a local: a function result cannot be the leftmost
       ! part of a data-ref in Fortran.
       if (gcv_count(sl) > 1) then
          e = gcv_nth(sl, 1)
          n = int(e%ival, kind=4)
       end if
    else
       ext = gcna_extents(gc_i1(v))
       if (size(ext) > 0) n = ext(1)
    end if
  end function array_len_for_print

  ! The k-th element (1-based) of an array's own shape.
  function array_elem_for_print(v, k) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: k
    type(gc_value) :: out, sl, e
    integer :: h, at, off, stride
    integer(8) :: iv
    real(gc_dp) :: rv
    logical :: lv, ok
    character(len=:), allocatable :: kn
    out = gc_nil()
    h = gc_i1(v)
    off = 0
    stride = 1
    sl = gc_slot(v, 2)
    if (gcv_is(sl)) then
       off = gc_i2(v)
       if (gcv_count(sl) > 0) then
          e = gcv_nth(sl, 0)
          stride = int(e%ival, kind=4)
       end if
    end if
    at = off + stride * (k - 1) + 1
    kn = gcna_kind(h)
    if (kn == "value") then
       out = gc_vec_get(gc_slot(v, 1), at)
    else if (kn == "logical") then
       call gcna_get_logical(h, at, lv, ok)
       if (ok) out = gc_bool(lv)
    else if (kn == "int4" .or. kn == "int8") then
       call gcna_get_int(h, at, iv, ok)
       if (ok) out = gc_int(iv)
    else
       call gcna_get_real(h, at, rv, ok)
       if (ok) out = gc_real(rv)
    end if
  end function array_elem_for_print

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

end module Printer
