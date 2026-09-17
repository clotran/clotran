! Regex: ICU's regex engine, behind exactly the six operations
! core.clj's own re-pattern/re-matcher/re-find/re-matches/re-groups/
! re-seq compile down to -- Pattern/compile, .matcher, .find, .matches,
! .groupCount, .group. See src/c/regex_shim.h for the C side and why it
! is that shape; GCEval.f90's B_RE_* cases are the only caller.
!
! WHY C AT ALL, in a project whose whole rationale is running without
! one (README's rationale section, and no bind(c) anywhere else in
! src/f). Writing a regex engine is not "porting a primitive" the way
! `rest` or `+` were -- it is writing a regex engine, and ICU already is
! one, correctly, for every script Unicode defines. Vendoring ICU's own
! ~30MB of C++ source was rejected as the wrong trade against "modify
! our code the least": this links dynamically against a normal system
! install (Homebrew's icu4c) through the smallest C shim that expresses
! Java's Matcher semantics, which is the one piece of this bridge that
! is genuinely reusable rather than reimplementable.
module Regex
  use, intrinsic :: iso_c_binding
  implicit none
  private

  interface
     function cre_compile_c(pattern, pattern_len, err_buf, err_cap) &
          result(h) bind(C, name="cre_compile")
       import :: c_ptr, c_char, c_int32_t
       character(kind=c_char), dimension(*), intent(in) :: pattern
       integer(c_int32_t), value :: pattern_len
       character(kind=c_char), dimension(*), intent(out) :: err_buf
       integer(c_int32_t), value :: err_cap
       type(c_ptr) :: h
     end function cre_compile_c

     function cre_clone_c(handle) result(h) bind(C, name="cre_clone")
       import :: c_ptr
       type(c_ptr), value :: handle
       type(c_ptr) :: h
     end function cre_clone_c

     subroutine cre_close_c(handle) bind(C, name="cre_close")
       import :: c_ptr
       type(c_ptr), value :: handle
     end subroutine cre_close_c

     function cre_set_text_c(handle, text, text_len, out_buf) result(r) &
          bind(C, name="cre_set_text")
       import :: c_ptr, c_char, c_int32_t
       type(c_ptr), value :: handle
       character(kind=c_char), dimension(*), intent(in) :: text
       integer(c_int32_t), value :: text_len
       type(c_ptr), intent(out) :: out_buf
       integer(c_int32_t) :: r
     end function cre_set_text_c

     subroutine cre_free_text_c(buf) bind(C, name="cre_free_text")
       import :: c_ptr
       type(c_ptr), value :: buf
     end subroutine cre_free_text_c

     function cre_matches_c(handle) result(r) bind(C, name="cre_matches")
       import :: c_ptr, c_int32_t
       type(c_ptr), value :: handle
       integer(c_int32_t) :: r
     end function cre_matches_c

     function cre_find_next_c(handle) result(r) bind(C, name="cre_find_next")
       import :: c_ptr, c_int32_t
       type(c_ptr), value :: handle
       integer(c_int32_t) :: r
     end function cre_find_next_c

     function cre_group_count_c(handle) result(n) bind(C, name="cre_group_count")
       import :: c_ptr, c_int32_t
       type(c_ptr), value :: handle
       integer(c_int32_t) :: n
     end function cre_group_count_c

     function cre_group_span_c(handle, idx, start, endp) result(r) &
          bind(C, name="cre_group_span")
       import :: c_ptr, c_int32_t
       type(c_ptr), value :: handle
       integer(c_int32_t), value :: idx
       integer(c_int32_t), intent(out) :: start, endp
       integer(c_int32_t) :: r
     end function cre_group_span_c
  end interface

  ! Handles are OPAQUE C POINTERS, and gc_value has no room for one --
  ! by design, the same reason a namespace or a Var is looked up by
  ! index rather than held by pointer (GCNamespace.f90). So a handle
  ! lives in this module's own registry, addressed from gc_value by a
  ! plain integer index in i1, exactly like every other native resource
  ! this project keeps outside the heap.
  integer, parameter :: MAX_HANDLES = 4096
  type(c_ptr), save :: registry(MAX_HANDLES) = c_null_ptr
  ! The subject-text buffer each handle was given, if any. OURS to free
  ! -- ICU keeps only a shallow reference and never copies it -- and
  ! kept here rather than asked back from ICU, because a handle that
  ! never had text set answers that question with a pointer we must not
  ! free. A Matcher has one; a compiled Pattern has none.
  type(c_ptr), save :: subject(MAX_HANDLES) = c_null_ptr
  integer, save :: next_slot = 1

  character(len=256), save :: last_error = ""

  public :: regex_compile, regex_clone, regex_set_text, regex_matches, &
       regex_release, regex_live_count, &
       regex_find_next, regex_group_count, regex_group_span, &
       regex_last_error

contains

  ! A free slot, preferring one a collection has released.
  !
  ! This used to hand out next_slot and WRAP when it ran off the end,
  ! on the reasoning that handles are never freed so reuse could only
  ! happen after thousands of distinct regexes. That was two problems:
  ! every handle leaked its ICU object, and on wrapping it would hand
  ! out a slot still in use -- silently, as a live Pattern suddenly
  ! pointing at someone else's compiled regex.
  !
  ! Handles ARE freed now: regex_release, driven by the collector's
  ! finalizer hook. So this scans for an empty slot and only fails
  ! when the table is genuinely full.
  function alloc_slot(h) result(idx)
    type(c_ptr), intent(in) :: h
    integer :: idx, i
    idx = 0
    do i = 1, MAX_HANDLES
       if (.not. c_associated(registry(i))) then
          registry(i) = h
          idx = i
          return
       end if
    end do
    ! Full. Close the handle rather than dropping it on the floor: the
    ! caller reads 0 as failure and will never see it again, so this is
    ! the last place that can.
    call cre_close_c(h)
  end function alloc_slot

  ! Closes one handle and empties its slot. Called by the sweep, via
  ! the finalizer hook, when the Pattern or Matcher holding it is
  ! collected -- which is the only thing that knows the handle is
  ! unreachable.
  !
  ! cre_close frees the subject text too: ICU keeps only a shallow
  ! reference to it, so nothing else can. A clone does NOT share that
  ! text -- uregex_clone's own contract says the input string is not
  ! cloned -- so each handle owns its own and freeing here is safe.
  ! How many handles are open. For the tests: a collection that frees
  ! the Pattern or Matcher must close the ICU object too, and a leak
  ! there is invisible from Clojure -- which is how it went unnoticed.
  integer function regex_live_count()
    integer :: i
    regex_live_count = 0
    do i = 1, MAX_HANDLES
       if (c_associated(registry(i))) regex_live_count = regex_live_count + 1
    end do
  end function regex_live_count

  subroutine regex_release(idx)
    integer, intent(in) :: idx
    if (idx < 1 .or. idx > MAX_HANDLES) return
    if (.not. c_associated(registry(idx))) return
    if (c_associated(subject(idx))) then
       call cre_free_text_c(subject(idx))
       subject(idx) = c_null_ptr
    end if
    call cre_close_c(registry(idx))
    registry(idx) = c_null_ptr
  end subroutine regex_release

  function regex_last_error() result(s)
    character(len=:), allocatable :: s
    s = trim(last_error)
  end function regex_last_error

  ! Compiles a pattern, returning a POSITIVE handle index, or 0 on
  ! failure (with regex_last_error() set).
  function regex_compile(pattern) result(idx)
    character(len=*), intent(in) :: pattern
    integer :: idx
    type(c_ptr) :: h
    character(kind=c_char, len=1) :: errbuf(256)
    integer :: i

    idx = 0
    ! ICU rejects a zero-length pattern outright, but #"" is a legal
    ! Clojure regex that matches the empty string at every position.
    ! (?:) is that same pattern spelled in a way ICU accepts. The
    ! SOURCE text is kept separately by the caller, so #"" still
    ! prints as itself.
    if (len(pattern) == 0) then
       h = cre_compile_c("(?:)" // c_null_char, 4, errbuf, 256_c_int32_t)
    else
       h = cre_compile_c(pattern // c_null_char, len(pattern), errbuf, 256_c_int32_t)
    end if
    if (.not. c_associated(h)) then
       last_error = ""
       do i = 1, 256
          if (errbuf(i) == c_null_char) exit
          last_error = trim(last_error) // errbuf(i)
       end do
       return
    end if
    idx = alloc_slot(h)
  end function regex_compile

  ! An independent handle over the same compiled pattern, for one
  ! Matcher -- see regex_shim.h on why cloning rather than sharing.
  function regex_clone(pattern_idx) result(idx)
    integer, intent(in) :: pattern_idx
    integer :: idx
    type(c_ptr) :: h
    idx = 0
    if (pattern_idx < 1 .or. pattern_idx > MAX_HANDLES) return
    h = cre_clone_c(registry(pattern_idx))
    if (.not. c_associated(h)) return
    idx = alloc_slot(h)
  end function regex_clone

  function regex_set_text(idx, text) result(ok)
    integer, intent(in) :: idx
    character(len=*), intent(in) :: text
    logical :: ok
    integer(c_int32_t) :: r
    type(c_ptr) :: buf
    ok = .false.
    if (idx < 1 .or. idx > MAX_HANDLES) return
    ! Free whatever this handle was holding before: setting text twice
    ! would otherwise strand the first buffer.
    if (c_associated(subject(idx))) then
       call cre_free_text_c(subject(idx))
       subject(idx) = c_null_ptr
    end if
    r = cre_set_text_c(registry(idx), text // c_null_char, len(text), buf)
    ok = (r == 0)
    if (ok) subject(idx) = buf
  end function regex_set_text

  function regex_matches(idx) result(r)
    integer, intent(in) :: idx
    integer :: r
    r = -1
    if (idx < 1 .or. idx > MAX_HANDLES) return
    r = cre_matches_c(registry(idx))
  end function regex_matches

  function regex_find_next(idx) result(r)
    integer, intent(in) :: idx
    integer :: r
    r = -1
    if (idx < 1 .or. idx > MAX_HANDLES) return
    r = cre_find_next_c(registry(idx))
  end function regex_find_next

  function regex_group_count(idx) result(n)
    integer, intent(in) :: idx
    integer :: n
    n = -1
    if (idx < 1 .or. idx > MAX_HANDLES) return
    n = cre_group_count_c(registry(idx))
  end function regex_group_count

  ! Returns .true. and sets start/endp (0-based, endp exclusive -- ready
  ! to slice a Fortran substring as text(start+1:endp)) if group `gnum`
  ! participated in the last match; .false. otherwise (including "no
  ! match yet" and "index out of range").
  function regex_group_span(idx, gnum, start, endp) result(participated)
    integer, intent(in) :: idx, gnum
    integer, intent(out) :: start, endp
    logical :: participated
    integer(c_int32_t) :: r, s, e
    participated = .false.
    start = 0
    endp = 0
    if (idx < 1 .or. idx > MAX_HANDLES) return
    r = cre_group_span_c(registry(idx), gnum, s, e)
    if (r /= 1) return
    start = s
    endp = e
    participated = .true.
  end function regex_group_span

end module Regex
