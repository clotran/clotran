! Reader and printer together: read a form, print it, and check the
! input comes back. That is the strongest test the new data layer has
! -- a reader and a printer can only agree if the thing between them
! actually holds what it was given, and every structure is exercised
! against real Clojure text rather than hand-built in a test.
program reader_test
  use GC
  use LispReader
  use Printer
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_atoms()
  call check_collections()
  call check_reader_macros()
  call check_whitespace_and_comments()
  call check_errors()
  call check_invalid_numbers()
  call check_reader_conditionals()
  call check_big_form_under_torture()
  call check_nested_literals_under_torture()

  if (all_ok) then
     print *, ""
     print *, "ALL GCREADER CHECKS PASSED"
  else
     print *, ""
     print *, "GCREADER CHECKS FAILED"
     stop 1
  end if

contains

  subroutine ok(label, condition)
    character(len=*), intent(in) :: label
    logical, intent(in) :: condition
    if (condition) then
       print '(A,A)', "ok   - ", label
    else
       print '(A,A)', "FAIL - ", label
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok

  ! The round trip itself: text in, text out, must match.
  subroutine trip(label, text)
    character(len=*), intent(in) :: label, text
    type(gc_value) :: v
    integer :: base
    character(len=:), allocatable :: got
    base = vs_enter(1)
    v = gcr_read(text, no_roots)
    call vs_set(base + 1, v)
    if (gcr_has_error()) then
       block
          character(len=:), allocatable :: dlr_1
          call gcr_error(s=dlr_1)
          print '(A,A,A,A)', "FAIL - ", label, "read error: ", dlr_1
       end block
       all_ok = .false.
       call vs_leave(base)
       return
    end if
    block
       character(len=:), allocatable :: dlr_2
       call gcp_str(vs_get(base + 1), .true., s=dlr_2)
       got = dlr_2
    end block
    call vs_leave(base)
    if (got == text) then
       print '(A,A,A)', "ok   - ", label, got
    else
       print '(A,A,A,A,A)', "FAIL - ", label, got, "  (expected ", text // ")"
       all_ok = .false.
    end if
    flush(6)
  end subroutine trip

  subroutine check_atoms()
    call gc_init(512)
    call trip("1a. ", "nil")
    call trip("1b. ", "true")
    call trip("1c. ", "false")
    call trip("1d. ", "42")
    call trip("1e. ", "-17")
    call trip("1f. ", "3.5")
    call trip("1g. ", "a-symbol")
    call trip("1h. ", ":a-keyword")
    call trip("1i. ", """a string""")
    call trip("1j. ", "\a")
    call trip("1k. ", "\newline")
    ! A string whose contents would themselves confuse the reader.
    call trip("1l. ", """with \""quotes\"" in""")
    call trip("1m. ", """with a \nnewline""")
  end subroutine check_atoms

  subroutine check_collections()
    call gc_init(512)
    call trip("2a. ", "()")
    call trip("2b. ", "(1 2 3)")
    call trip("2c. ", "[]")
    call trip("2d. ", "[1 2 3]")
    call trip("2e. ", "{}")
    call trip("2f. ", "{:a 1}")
    call trip("2g. ", "(1 [2 3] {:k :v})")
    call trip("2h. ", "((1) ((2)))")
    call trip("2i. ", "[[[1]]]")
    ! Mixed types in one collection, which is where a tag mix-up shows.
    call trip("2j. ", "(nil true 1 2.5 :k sym ""s"")")
  end subroutine check_collections

  subroutine check_reader_macros()
    call gc_init(512)
    ! These read as ordinary forms, so they print as what they expand
    ! to rather than as the shorthand -- same as clotran's reader.
    call trip("3a. ", "(quote x)")
    call trip("3b. ", "(deref a)")
    call trip("3c. ", "(quasiquote (a (unquote b)))")
    call round("3d. '@x reads as nested forms: ", "'@x", "(quote (deref x))")
    call round("3e. ~@x is splice-unquote: ", "~@x", "(splice-unquote x)")
  end subroutine check_reader_macros

  subroutine check_whitespace_and_comments()
    call gc_init(512)
    call round("4a. leading space is skipped: ", "   42", "42")
    call round("4b. commas are whitespace: ", "{:a 1, :b 2}", "{:a 1, :b 2}")
    call round("4c. comments are skipped: ", "; a comment" // achar(10) // "7", "7")
    call round("4d. ...inside a form too: ", &
         "(1 ; here" // achar(10) // " 2)", "(1 2)")
    call round("4e. newlines separate: ", "(1" // achar(10) // "2)", "(1 2)")
  end subroutine check_whitespace_and_comments

  ! A reader that returns a half-built value on bad input is worse
  ! than one that says so.
  ! Clojure's intPat match is EXCLUSIVE -- a token it matches never
  ! reaches floatPat, even when the match captures nothing. So `08`
  ! is an ERROR, not 8.0, and `1e` is an error rather than a symbol,
  ! because LispReader.read sends every digit-initial token to
  ! readNumber and there is no way back. These cannot be checked from
  ! a .clj file: a reader error aborts the whole load, so the
  ! assertion after it would never run.
  subroutine check_invalid_numbers()
    type(gc_value) :: v
    call gc_init(512)
    v = gcr_read("08", no_roots)
    call ok("7a. a leading zero with an 8 is not 8.0: ", gcr_has_error())
    v = gcr_read("09", no_roots)
    call ok("7b. ...nor with a 9: ", gcr_has_error())
    v = gcr_read("0x", no_roots)
    call ok("7c. 0x with no digits is an error: ", gcr_has_error())
    v = gcr_read("0xZ", no_roots)
    call ok("7d. ...and with a non-hex digit: ", gcr_has_error())
    v = gcr_read("2r9", no_roots)
    call ok("7e. a digit outside the radix is an error: ", gcr_has_error())
    v = gcr_read("1r1", no_roots)
    call ok("7f. radix 1 is out of range: ", gcr_has_error())
    v = gcr_read("37r1", no_roots)
    call ok("7g. ...and so is radix 37: ", gcr_has_error())
    v = gcr_read("2r", no_roots)
    call ok("7h. a radix with no digits is an error: ", gcr_has_error())
    v = gcr_read("1e", no_roots)
    call ok("7i. an exponent with no digits is an error, not a symbol: ", &
         gcr_has_error())
    ! The other half of the rule: a token that does NOT begin with a
    ! digit is a name, however numeric it looks. floatPat requires a
    ! digit before the dot, so .5 is a symbol in Clojure too.
    v = gcr_read(".5", no_roots)
    block
       character(len=:), allocatable :: dlr_3
       call gcp_str(v, .true., s=dlr_3)
       call ok("7j. .5 is a symbol, not 0.5: ",  .not. gcr_has_error() .and. dlr_3 == ".5")
    end block
    v = gcr_read("42", no_roots)
    call ok("7k. ...and a good number clears the error: ", .not. gcr_has_error())
  end subroutine check_invalid_numbers

  ! #? and #?@. The feature is :cljf; :clj is the JVM. DEVIATIONS 33.
  subroutine check_reader_conditionals()
    type(gc_value) :: v
    call gc_init(512)
    call round("9a. #? keeps the :cljf branch: ", "#?(:clj 1 :cljf 2)", "2")
    call round("9b. ...or :default: ", "#?(:clj 1 :default 3)", "3")
    call round("9c. :clj is the JVM, not us: ", "(a #?(:clj 1) b)", "(a b)")
    call round("9d. no branch at the end of a list: ", "(a #?(:cljs 1))", "(a)")
    call round("9e. #?@ splices a vector: ", "[1 #?@(:cljf [2 3]) 4]", "[1 2 3 4]")
    call round("9f. ...and a list: ", "(f #?@(:cljf (x y)))", "(f x y)")
    call round("9g. ...and pairs into a map: ", "{#?@(:cljf [:b 2])}", "{:b 2}")
    call round("9h. an unselected branch may hold a tagged literal: ", "#?(:cljs #js {:a 1} :cljf 5)", "5")
    call round("9i. the first match wins: ", "#?(:default 1 :cljf 2)", "1")
    call round("9j. nothing in a set: ", "#{#?(:cljs 1) 2}", "#{2}")
    v = gcr_read("#?(:cljf)", no_roots)
    call ok("9k. an odd body is an error: ", gcr_has_error())
    v = gcr_read("#?(:cljs 1)", no_roots)
    call ok("9l. nothing at the top level is EOF: ", gcr_has_error())
    v = gcr_read("#?@(:cljf [1 2])", no_roots)
    call ok("9m. a splice at the top level is an error: ", gcr_has_error())
    v = gcr_read("'#?(:cljs 1)", no_roots)
    call ok("9n. a quote needs a form: ", gcr_has_error())
    v = gcr_read("#?@(:cljf 1)", no_roots)
    call ok("9o. a splice needs a collection: ", gcr_has_error())
    call round("9p. ...and a good form clears the error: ", "#?(:cljf 7)", "7")
  end subroutine check_reader_conditionals

  subroutine check_errors()
    type(gc_value) :: v
    call gc_init(512)
    v = gcr_read("(1 2", no_roots)
    call ok("5a. an unclosed list is an error: ", gcr_has_error())
    v = gcr_read("[1 2", no_roots)
    call ok("5b. an unclosed vector is an error: ", gcr_has_error())
    v = gcr_read("{:a", no_roots)
    call ok("5c. an odd map literal is an error: ", gcr_has_error())
    v = gcr_read(")", no_roots)
    call ok("5d. a stray closer is an error: ", gcr_has_error())
    v = gcr_read("""unterminated", no_roots)
    call ok("5e. an unterminated string is an error: ", gcr_has_error())
    v = gcr_read("(1 2 3)", no_roots)
    call ok("5f. ...and a good form clears the error: ", .not. gcr_has_error())
  end subroutine check_errors

  ! Reading allocates constantly, so under torture every partially
  ! built form has to stay rooted -- a collection lands between two
  ! elements of a list far more often than it ever would in practice.
  subroutine check_big_form_under_torture()
    character(len=:), allocatable :: text
    character(len=16) :: buf
    integer :: i
    call gc_init(8)
    text = "("
    do i = 1, 60
       write(buf, '(I0)') i
       if (i > 1) text = text // " "
       text = text // trim(buf)
    end do
    text = text // ")"
    gc_torture = .true.
    call trip("6a. a 60-element list under torture: ", text)
    block
       character(len=:), allocatable :: dlr_4
       call gc_check_heap(problem=dlr_4)
       call ok("6b. ...and the heap audits clean: ", dlr_4 == "")
    end block
    gc_torture = .false.
  end subroutine check_big_form_under_torture

  ! The COLLECTION LITERALS under torture, which the flat list above
  ! does not reach -- and that gap is exactly why the bug below lived
  ! here undisturbed.
  !
  ! Reading #{...}, #(...) or ^meta allocates while an enclosing form
  ! is still being built. Those three each dropped the caller's `roots`
  ! on their own allocations: their own values sit on the value stack,
  ! which the collector scans, but the CALLER'S are plain Fortran
  ! locals reachable only through the array it passed in. So a
  ! collection at the wrong moment freed the form being built around
  ! them and the reader answered () -- with no error, which is the
  ! worst shape this project has a rule about.
  !
  ! read_map threaded roots correctly throughout and is the shape the
  ! other three now copy.
  subroutine check_nested_literals_under_torture()
    call gc_init(8)
    gc_torture = .true.
    call trip("6c. a set inside a list: ", "(a #{1} b)")
    call trip("6d. a map inside a list: ", "(a {1 2} b)")
    call trip("6e. a vector inside a list: ", "(a [1 2] b)")
    ! Metadata is not printed by default, so the form comes back
    ! without it -- what matters here is that it comes back at all.
    call round("6f. metadata inside a list: ", "(a ^:m b c)", "(a b c)")
    call round("6g. an anonymous fn inside a list: ", "(a #(+ % 1) b)", &
         "(a (fn* [p1__1#] (+ p1__1# 1)) b)")
    block
       character(len=:), allocatable :: dlr_5
       call gc_check_heap(problem=dlr_5)
       call ok("6h. ...and the heap audits clean: ", dlr_5 == "")
    end block
    gc_torture = .false.
  end subroutine check_nested_literals_under_torture


  ! For cases where input and output deliberately differ.
  subroutine round(label, text, expected)
    character(len=*), intent(in) :: label, text, expected
    type(gc_value) :: v
    integer :: base
    character(len=:), allocatable :: got
    base = vs_enter(1)
    v = gcr_read(text, no_roots)
    call vs_set(base + 1, v)
    block
       character(len=:), allocatable :: dlr_6
       call gcp_str(vs_get(base + 1), .true., s=dlr_6)
       got = dlr_6
    end block
    call vs_leave(base)
    if (got == expected) then
       print '(A,A,A)', "ok   - ", label, got
    else
       print '(A,A,A,A,A)', "FAIL - ", label, got, "  (expected ", expected // ")"
       all_ok = .false.
    end if
    flush(6)
  end subroutine round

end program reader_test
