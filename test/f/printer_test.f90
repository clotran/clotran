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
    block
       character(len=:), allocatable :: dlr_1
       call gcp_str(gc_nil(), .true., s=dlr_1)
       call eq("1a. nil: ", dlr_1, "nil")
    end block
    block
       character(len=:), allocatable :: dlr_2
       call gcp_str(gc_bool(.true.), .true., s=dlr_2)
       call eq("1b. true: ", dlr_2, "true")
    end block
    block
       character(len=:), allocatable :: dlr_3
       call gcp_str(gc_bool(.false.), .true., s=dlr_3)
       call eq("1c. false: ", dlr_3, "false")
    end block
    block
       character(len=:), allocatable :: dlr_4
       call gcp_str(gc_int(42), .true., s=dlr_4)
       call eq("1d. an integer: ", dlr_4, "42")
    end block
    block
       character(len=:), allocatable :: dlr_5
       call gcp_str(gc_int(-7), .true., s=dlr_5)
       call eq("1e. a negative integer: ", dlr_5, "-7")
    end block
    ! A double must not print as an integer, or it reads back wrong.
    block
       character(len=:), allocatable :: dlr_6
       call gcp_str(gc_real(2.0_gc_dp), .true., s=dlr_6)
       call eq("1f. a double keeps its point: ", dlr_6, "2.0")
    end block
    block
       character(len=:), allocatable :: dlr_7
       call gcp_str(gc_real(1.5_gc_dp), .true., s=dlr_7)
       call eq("1g. ...and its fraction: ", dlr_7, "1.5")
    end block
  end subroutine check_immediates

  ! readable vs not is real Clojure's pr-str/print-str distinction,
  ! and getting it wrong is how (println "a") starts printing quotes.
  subroutine check_text()
    type(gc_value) :: s, k, sy, c, roots(1)
    call gc_init(256)
    s = gc_str("hi", no_roots)
    roots(1) = s
    block
       character(len=:), allocatable :: dlr_8
       call gcp_str(s, .true., s=dlr_8)
       call eq("2a. a string, readably: ", dlr_8, '"hi"')
    end block
    block
       character(len=:), allocatable :: dlr_9
       call gcp_str(s, .false., s=dlr_9)
       call eq("2b. ...and not: ", dlr_9, "hi")
    end block
    k = gc_key("kw", roots)
    roots(1) = k
    block
       character(len=:), allocatable :: dlr_10
       call gcp_str(k, .true., s=dlr_10)
       call eq("2c. a keyword: ", dlr_10, ":kw")
    end block
    sy = gc_sym("sym", roots)
    roots(1) = sy
    block
       character(len=:), allocatable :: dlr_11
       call gcp_str(sy, .true., s=dlr_11)
       call eq("2d. a symbol: ", dlr_11, "sym")
    end block
    c = gc_char("a")
    block
       character(len=:), allocatable :: dlr_12
       call gcp_str(c, .true., s=dlr_12)
       call eq("2e. a character, readably: ", dlr_12, achar(92) // "a")
    end block
    block
       character(len=:), allocatable :: dlr_13
       call gcp_str(c, .false., s=dlr_13)
       call eq("2f. ...and not: ", dlr_13, "a")
    end block
    block
       character(len=:), allocatable :: dlr_14
       call gcp_str(gc_char(achar(10)), .true., s=dlr_14)
       call eq("2g. a named character: ", dlr_14,  achar(92) // "newline")
    end block
  end subroutine check_text

  subroutine check_list()
    type(gc_value) :: l, roots(1)
    integer :: i
    call gc_init(256)
    l = gcl_empty(no_roots)
    block
       character(len=:), allocatable :: dlr_15
       call gcp_str(l, .true., s=dlr_15)
       call eq("3a. the empty list: ", dlr_15, "()")
    end block
    do i = 3, 1, -1
       roots(1) = l
       l = gcl_cons(gc_int(i), l, roots)
    end do
    block
       character(len=:), allocatable :: dlr_16
       call gcp_str(l, .true., s=dlr_16)
       call eq("3b. a list, in order: ", dlr_16, "(1 2 3)")
    end block
  end subroutine check_list

  subroutine check_vector()
    type(gc_value) :: v, roots(1)
    integer :: i
    call gc_init(256)
    v = gcv_empty(no_roots)
    block
       character(len=:), allocatable :: dlr_17
       call gcp_str(v, .true., s=dlr_17)
       call eq("4a. the empty vector: ", dlr_17, "[]")
    end block
    do i = 1, 3
       roots(1) = v
       v = gcv_conj(v, gc_int(i), roots)
    end do
    block
       character(len=:), allocatable :: dlr_18
       call gcp_str(v, .true., s=dlr_18)
       call eq("4b. a vector, in order: ", dlr_18, "[1 2 3]")
    end block
  end subroutine check_vector

  ! An array map and a trie holding the same one entry must print the
  ! same. A map that printed differently once it crossed 8 entries
  ! would be the implementation leaking into the language.
  subroutine check_map_both_representations()
    type(gc_value) :: m, roots(1)
    integer :: i
    call gc_init(256)
    m = gca_empty(no_roots)
    block
       character(len=:), allocatable :: dlr_19
       call gcp_str(m, .true., s=dlr_19)
       call eq("5a. the empty map: ", dlr_19, "{}")
    end block
    roots(1) = m
    m = gca_assoc(m, gc_key("a", roots), gc_int(1), roots)
    call ok("5b. one entry is an array map: ", gca_is_array_map(m))
    block
       character(len=:), allocatable :: dlr_20
       call gcp_str(m, .true., s=dlr_20)
       call eq("5c. ...printing plainly: ", dlr_20, "{:a 1}")
    end block

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
    block
       character(len=:), allocatable :: dlr_21
       call gcp_str(m, .true., s=dlr_21)
       call eq("5e. ...and prints identically: ", dlr_21, "{:a 1}")
    end block
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
    block
       character(len=:), allocatable :: dlr_22
       call gcp_str(v, .true., s=dlr_22)
       call eq("6a. nested structures print through: ", dlr_22,  '(:tag [1 "x"])')
    end block
    block
       character(len=:), allocatable :: dlr_23
       call gcp_str(v, .false., s=dlr_23)
       call eq("6b. ...and not-readably inside too: ", dlr_23,  "(:tag [1 x])")
    end block
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
    block
       character(len=:), allocatable :: dlr_24
       call gcp_str(vs_get(base + 1), .true., s=dlr_24)
       call eq("7a. a vector rooted only by the stack prints: ",  dlr_24, "[1 2 3 4 5 6 7 8 9 10 11 12]")
    end block
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
