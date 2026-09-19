! Exercises printing over the GC heap. This is the first thing that
! walks every structure in the new data layer at once, so it doubles
! as an end-to-end check that list, vector, both map representations
! and text all actually hold what they were given.
program printer_test
  use GC
  use PersistentList
  use PersistentVector
  use Assoc
  use Printer
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_immediates()
  call check_text()
  call check_list()
  call check_vector()
  call check_map_both_representations()
  call check_nested()
  call check_under_collection()

  if (all_ok) then
     print *, ""
     print *, "ALL GCPRINTER CHECKS PASSED"
  else
     print *, ""
     print *, "GCPRINTER CHECKS FAILED"
     stop 1
  end if

contains

  subroutine eq(label, got, expected)
    character(len=*), intent(in) :: label, got, expected
    if (got == expected) then
       print '(A,A,A)', "ok   - ", label, got
    else
       print '(A,A,A,A,A)', "FAIL - ", label, got, "  (expected ", expected // ")"
       all_ok = .false.
    end if
    flush(6)
  end subroutine eq

  subroutine check_immediates()
    call gc_init(256)
    call eq("1a. nil: ", gcp_str(gc_nil(), .true.), "nil")
    call eq("1b. true: ", gcp_str(gc_bool(.true.), .true.), "true")
    call eq("1c. false: ", gcp_str(gc_bool(.false.), .true.), "false")
    call eq("1d. an integer: ", gcp_str(gc_int(42), .true.), "42")
    call eq("1e. a negative integer: ", gcp_str(gc_int(-7), .true.), "-7")
    ! A double must not print as an integer, or it reads back wrong.
    call eq("1f. a double keeps its point: ", gcp_str(gc_real(2.0_gc_dp), .true.), "2.0")
    call eq("1g. ...and its fraction: ", gcp_str(gc_real(1.5_gc_dp), .true.), "1.5")
  end subroutine check_immediates

  ! readable vs not is real Clojure's pr-str/print-str distinction,
  ! and getting it wrong is how (println "a") starts printing quotes.
  subroutine check_text()
    type(gc_value) :: s, k, sy, c, roots(1)
    call gc_init(256)
    s = gc_str("hi", no_roots)
    roots(1) = s
    call eq("2a. a string, readably: ", gcp_str(s, .true.), '"hi"')
    call eq("2b. ...and not: ", gcp_str(s, .false.), "hi")
    k = gc_key("kw", roots)
    roots(1) = k
    call eq("2c. a keyword: ", gcp_str(k, .true.), ":kw")
    sy = gc_sym("sym", roots)
    roots(1) = sy
    call eq("2d. a symbol: ", gcp_str(sy, .true.), "sym")
    c = gc_char("a")
    call eq("2e. a character, readably: ", gcp_str(c, .true.), achar(92) // "a")
    call eq("2f. ...and not: ", gcp_str(c, .false.), "a")
    call eq("2g. a named character: ", gcp_str(gc_char(achar(10)), .true.), &
         achar(92) // "newline")
  end subroutine check_text

  subroutine check_list()
    type(gc_value) :: l, roots(1)
    integer :: i
    call gc_init(256)
    l = gcl_empty(no_roots)
    call eq("3a. the empty list: ", gcp_str(l, .true.), "()")
    do i = 3, 1, -1
       roots(1) = l
       l = gcl_cons(gc_int(i), l, roots)
    end do
    call eq("3b. a list, in order: ", gcp_str(l, .true.), "(1 2 3)")
  end subroutine check_list

  subroutine check_vector()
    type(gc_value) :: v, roots(1)
    integer :: i
    call gc_init(256)
    v = gcv_empty(no_roots)
    call eq("4a. the empty vector: ", gcp_str(v, .true.), "[]")
    do i = 1, 3
       roots(1) = v
       v = gcv_conj(v, gc_int(i), roots)
    end do
    call eq("4b. a vector, in order: ", gcp_str(v, .true.), "[1 2 3]")
  end subroutine check_vector

  ! An array map and a trie holding the same one entry must print the
  ! same. A map that printed differently once it crossed 8 entries
  ! would be the implementation leaking into the language.
  subroutine check_map_both_representations()
    type(gc_value) :: m, roots(1)
    integer :: i
    call gc_init(256)
    m = gca_empty(no_roots)
    call eq("5a. the empty map: ", gcp_str(m, .true.), "{}")
    roots(1) = m
    m = gca_assoc(m, gc_key("a", roots), gc_int(1), roots)
    call ok("5b. one entry is an array map: ", gca_is_array_map(m))
    call eq("5c. ...printing plainly: ", gcp_str(m, .true.), "{:a 1}")

    ! Push it over the threshold, then remove everything else, so the
    ! SAME single entry is left in a trie instead.
    do i = 1, 20
       roots(1) = m
       m = gca_assoc(m, gc_int(i), gc_int(i), roots)
    end do
    do i = 1, 20
       roots(1) = m
       m = gca_dissoc(m, gc_int(i), roots)
    end do
    call ok("5d. the same entry is now in a trie: ", .not. gca_is_array_map(m))
    call eq("5e. ...and prints identically: ", gcp_str(m, .true.), "{:a 1}")
  end subroutine check_map_both_representations

  subroutine check_nested()
    type(gc_value) :: v, inner, roots(2)
    call gc_init(256)
    inner = gcv_empty(no_roots)
    roots(1) = inner
    inner = gcv_conj(inner, gc_int(1), roots)
    roots(1) = inner
    inner = gcv_conj(inner, gc_str("x", roots), roots)
    roots(1) = inner
    v = gcl_empty(roots)
    roots(2) = v
    v = gcl_cons(inner, v, roots)
    roots(2) = v
    v = gcl_cons(gc_key("tag", roots), v, roots)
    call eq("6a. nested structures print through: ", gcp_str(v, .true.), &
         '(:tag [1 "x"])')
    call eq("6b. ...and not-readably inside too: ", gcp_str(v, .false.), &
         "(:tag [1 x])")
  end subroutine check_nested

  ! Printing allocates (strings are built as it walks), so under
  ! torture the value being printed must stay rooted throughout.
  subroutine check_under_collection()
    type(gc_value) :: v, roots(1)
    integer :: base, i
    call gc_init(16)
    v = gcv_empty(no_roots)
    do i = 1, 12
       roots(1) = v
       v = gcv_conj(v, gc_int(i), roots)
    end do
    base = vs_enter(1)
    call vs_set(base + 1, v)
    call gc_collect(no_roots)
    call eq("7a. a vector rooted only by the stack prints: ", &
         gcp_str(vs_get(base + 1), .true.), "[1 2 3 4 5 6 7 8 9 10 11 12]")
    call vs_leave(base)
  end subroutine check_under_collection

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

end program printer_test
