! RT: generic, type-dispatching operations -- mirrors clojure.lang.RT's
! role. first/rest/next/cons/count work the same whether handed a list
! or a vector; conj is the one that behaves differently per type
! (prepend for list, append for vector). seq is the eager seqable->seq
! conversion (a vector isn't itself a seq, same as real Clojure -- (seq
! v) builds a list view of it; nil in, nil out for an empty collection).
module RT
  use values
  use PersistentList, only: list_empty, list_cons => cons, list_first => first, &
       list_rest => rest, list_count => list_count
  use PersistentVector, only: vector_empty, vector_count, vector_nth, vector_conj, vector_assoc
  use PersistentArrayMap, only: array_map_empty, array_map_count, array_map_get, &
       array_map_assoc, array_map_entries, array_map_contains
  implicit none
  private

  public :: nil_value, first, rest, next, cons, conj, nth, count, seq, get, assoc, equiv

contains

  function nil_value() result(v)
    type(cons_value) :: v
  end function nil_value

  subroutine wrap_list_value(target, l)
    type(cons_value), intent(inout) :: target
    type(cons_ref), intent(in) :: l
    target%tag = TAG_LIST
    allocate(target%list_val)
    target%list_val = l
  end subroutine wrap_list_value

  ! Every element of vec as a list, in order -- one O(n) trie walk
  ! (each leaf's whole items(:) run cons'd on at once), not n separate
  ! O(log32 n) vector_nth calls (that was a real, if modest, quadratic-
  ! ish deviation from real Clojure's O(1)-to-start chunked seq: see
  ! NOTES.md). Walks right-to-left, consing each leaf's run in reverse,
  ! so the result comes out in forward order -- same trick vec_node's
  ! own construction already relies on elsewhere in this codebase.
  recursive subroutine vector_walk_rev(node, shift, l)
    type(node_ref), intent(in) :: node
    integer, intent(in) :: shift
    type(cons_ref), intent(inout) :: l
    integer :: i
    if (.not. associated(node%ptr)) return
    if (shift == 0) then
       do i = size(node%ptr%items), 1, -1
          l = list_cons(node%ptr%items(i), l)
       end do
    else
       do i = size(node%ptr%children), 1, -1
          call vector_walk_rev(node%ptr%children(i), shift - BITS, l)
       end do
    end if
  end subroutine vector_walk_rev

  function vector_to_list(vec) result(l)
    type(vec_t), intent(in) :: vec
    type(cons_ref) :: l
    l = list_empty()
    call vector_walk_rev(vec%root, vec%shift, l)
  end function vector_to_list

  ! Real Clojure's RT.first is seq(x).first() -- anything seqable, not
  ! just lists and vectors. Maps especially: (first {:a 1}) is the
  ! entry [:a 1], and core.clj's own destructuring walks map entries
  ! through first/key/val, so returning nil here made (.getKey nil)
  ! the failure mode for every map destructuring form.
  function first(v) result(val)
    type(cons_value), intent(in) :: v
    type(cons_value) :: val
    type(cons_value) :: s
    select case (v%tag)
    case (TAG_LIST)
       if (allocated(v%list_val)) val = list_first(v%list_val)
    case (TAG_VECTOR)
       if (allocated(v%vector_val)) then
          if (vector_count(v%vector_val) > 0) val = vector_nth(v%vector_val, 0)
       end if
    case (TAG_HASHMAP, TAG_SET, TAG_STRING)
       s = seq(v)
       if (s%tag == TAG_LIST) then
          if (allocated(s%list_val)) val = list_first(s%list_val)
       end if
    end select
  end function first

  ! Always a (possibly empty) list -- never bare nil, matching Clojure's
  ! rest (as opposed to next, which returns nil at the end).
  function rest(v) result(new_v)
    type(cons_value), intent(in) :: v
    type(cons_value) :: new_v
    type(cons_ref) :: tail
    select case (v%tag)
    case (TAG_LIST)
       if (allocated(v%list_val)) tail = list_rest(v%list_val)
    case (TAG_VECTOR)
       if (allocated(v%vector_val)) then
          if (vector_count(v%vector_val) > 1) tail = list_rest(vector_to_list(v%vector_val))
       end if
    case (TAG_HASHMAP, TAG_SET, TAG_STRING)
       block
         type(cons_value) :: s
         s = seq(v) ! same "seq it first" rule as first, above
         if (s%tag == TAG_LIST) then
            if (allocated(s%list_val)) tail = list_rest(s%list_val)
         end if
       end block
    end select
    call wrap_list_value(new_v, tail)
  end function rest

  ! Like rest, but nil once there's nothing left.
  function next(v) result(new_v)
    type(cons_value), intent(in) :: v
    type(cons_value) :: new_v
    type(cons_value) :: r
    r = rest(v)
    if (list_count(r%list_val) > 0) new_v = r
  end function next

  ! (cons x coll) always returns a list, regardless of coll's type.
  function cons(x, coll) result(new_v)
    type(cons_value), intent(in) :: x, coll
    type(cons_value) :: new_v
    type(cons_ref) :: coll_list

    select case (coll%tag)
    case (TAG_LIST)
       if (allocated(coll%list_val)) coll_list = coll%list_val
    case (TAG_VECTOR)
       if (allocated(coll%vector_val)) coll_list = vector_to_list(coll%vector_val)
    end select
    call wrap_list_value(new_v, list_cons(x, coll_list))
  end function cons

  ! (conj coll x): prepend for a list, append for a vector, list-of-one
  ! for nil (or anything else, for now).
  function conj(coll, x) result(new_v)
    type(cons_value), intent(in) :: coll, x
    type(cons_value) :: new_v
    type(cons_ref) :: base

    select case (coll%tag)
    case (TAG_LIST)
       if (allocated(coll%list_val)) base = coll%list_val
       call wrap_list_value(new_v, list_cons(x, base))
    case (TAG_VECTOR)
       new_v%tag = TAG_VECTOR
       allocate(new_v%vector_val)
       if (allocated(coll%vector_val)) then
          new_v%vector_val = vector_conj(coll%vector_val, x)
       else
          new_v%vector_val = vector_conj(vector_empty(), x)
       end if
    case (TAG_SET)
       new_v%tag = TAG_SET
       allocate(new_v%map_val)
       if (allocated(coll%map_val)) then
          new_v%map_val = array_map_assoc(coll%map_val, x, x)
       else
          new_v%map_val = array_map_assoc(array_map_empty(), x, x)
       end if
    case default
       call wrap_list_value(new_v, list_cons(x, list_empty()))
    end select
  end function conj

  function nth(coll, i) result(val)
    type(cons_value), intent(in) :: coll
    integer, intent(in) :: i ! 0-based
    type(cons_value) :: val
    type(cons_ref) :: l
    integer :: k

    select case (coll%tag)
    case (TAG_VECTOR)
       if (allocated(coll%vector_val)) val = vector_nth(coll%vector_val, i)
    case (TAG_LIST)
       if (allocated(coll%list_val)) then
          l = coll%list_val
          do k = 1, i
             l = list_rest(l)
          end do
          val = list_first(l)
       end if
    end select
  end function nth

  function count(coll) result(n)
    type(cons_value), intent(in) :: coll
    integer :: n
    n = 0
    select case (coll%tag)
    case (TAG_LIST)
       if (allocated(coll%list_val)) n = list_count(coll%list_val)
    case (TAG_VECTOR)
       if (allocated(coll%vector_val)) n = vector_count(coll%vector_val)
    case (TAG_STRING)
       if (allocated(coll%str_val)) n = len(coll%str_val)
    case (TAG_HASHMAP, TAG_SET)
       if (allocated(coll%map_val)) n = array_map_count(coll%map_val)
    end select
  end function count

  function get(coll, key) result(val)
    type(cons_value), intent(in) :: coll, key
    type(cons_value) :: val
    if ((coll%tag == TAG_HASHMAP .or. coll%tag == TAG_SET) .and. allocated(coll%map_val)) then
       val = array_map_get(coll%map_val, key)
    end if
  end function get

  ! (assoc coll key val): a real O(log32 n) path-copy for a vector
  ! (key must be an int index, 0 <= key <= count -- real Clojure's own
  ! assoc requires the same, throwing on anything else, which this
  ! doesn't validate either, same as nth above); array-map/hash-trie
  ! assoc (by value, any key) otherwise.
  function assoc(coll, key, val) result(new_v)
    type(cons_value), intent(in) :: coll, key, val
    type(cons_value) :: new_v
    if (coll%tag == TAG_VECTOR .and. allocated(coll%vector_val)) then
       new_v%tag = TAG_VECTOR
       allocate(new_v%vector_val)
       new_v%vector_val = vector_assoc(coll%vector_val, key%int_val, val)
       return
    end if
    new_v%tag = TAG_HASHMAP
    allocate(new_v%map_val)
    if (coll%tag == TAG_HASHMAP .and. allocated(coll%map_val)) then
       new_v%map_val = array_map_assoc(coll%map_val, key, val)
    else
       new_v%map_val = array_map_assoc(array_map_empty(), key, val)
    end if
  end function assoc

  ! Seqable -> seq. A vector is not itself a seq (same as real Clojure);
  ! this builds a list view of it. nil (or an empty collection) -> nil.
  function seq(v) result(new_v)
    type(cons_value), intent(in) :: v
    type(cons_value) :: new_v
    select case (v%tag)
    case (TAG_LIST)
       if (count(v) > 0) new_v = v
    case (TAG_VECTOR)
       if (count(v) > 0) call wrap_list_value(new_v, vector_to_list(v%vector_val))
    case (TAG_HASHMAP)
       if (count(v) > 0) call wrap_list_value(new_v, map_to_entry_list(v%map_val))
    case (TAG_SET)
       if (count(v) > 0) call wrap_list_value(new_v, set_to_element_list(v%map_val))
    case (TAG_STRING)
       if (allocated(v%str_val)) then
          if (len(v%str_val) > 0) call wrap_list_value(new_v, string_to_char_list(v%str_val))
       end if
    end select
  end function seq

  ! "abc" -> ("a" "b" "c"), each a one-character string.
  function string_to_char_list(s) result(l)
    character(len=*), intent(in) :: s
    type(cons_ref) :: l
    integer :: i
    type(cons_value) :: ch
    l = list_empty()
    do i = len(s), 1, -1
       ch%tag = TAG_STRING
       ch%str_val = s(i:i)
       l = list_cons(ch, l)
    end do
  end function string_to_char_list

  ! (=): mirrors clojure.lang.Util.equiv. A list and a vector with the
  ! same elements are equal, same as real Clojure -- both are sequential.
  recursive function equiv(a, b) result(eq)
    type(cons_value), intent(in) :: a, b
    logical :: eq
    type(cons_value) :: sa, sb

    select case (a%tag)
    case (TAG_NIL)
       eq = (b%tag == TAG_NIL)
    case (TAG_BOOL)
       eq = (b%tag == TAG_BOOL) .and. (a%bool_val .eqv. b%bool_val)
    case (TAG_INT)
       eq = (b%tag == TAG_INT) .and. (a%int_val == b%int_val)
    case (TAG_REAL)
       eq = (b%tag == TAG_REAL) .and. (a%real_val == b%real_val)
    case (TAG_STRING, TAG_SYMBOL, TAG_KEYWORD)
       eq = (b%tag == a%tag)
       if (eq) eq = (a%str_val == b%str_val)
    case (TAG_LIST, TAG_VECTOR)
       eq = (b%tag == TAG_LIST .or. b%tag == TAG_VECTOR) .and. (count(a) == count(b))
       if (eq) then
          sa = seq(a)
          sb = seq(b)
          do while (eq .and. sa%tag == TAG_LIST)
             eq = equiv(first(sa), first(sb))
             sa = next(sa)
             sb = next(sb)
          end do
       end if
    case (TAG_HASHMAP, TAG_SET)
       eq = (b%tag == a%tag) .and. allocated(a%map_val) .and. allocated(b%map_val)
       if (eq) eq = (array_map_count(a%map_val) == array_map_count(b%map_val))
       if (eq) then
          block
            integer :: i
            type(cons_value), allocatable :: akeys(:), avals(:)
            call array_map_entries(a%map_val, akeys, avals)
            do i = 1, size(akeys)
               eq = array_map_contains(b%map_val, akeys(i))
               if (eq) eq = equiv(avals(i), array_map_get(b%map_val, akeys(i)))
               if (.not. eq) exit
            end do
          end block
       end if
    case default
       eq = .false.
    end select
  end function equiv

  ! Map entries as a list of [k v] 2-vectors -- insertion order for a
  ! small map, hash order once promoted past 8 entries (see
  ! PersistentArrayMap.f90), matching real Clojure's own ArrayMap vs.
  ! HashMap iteration order exactly.
  function map_to_entry_list(m) result(l)
    type(array_map_t), intent(in) :: m
    type(cons_ref) :: l
    integer :: i
    type(vec_t) :: entry
    type(cons_value), allocatable :: keys(:), vals(:)
    call array_map_entries(m, keys, vals)
    l = list_empty()
    do i = size(keys), 1, -1
       entry = vector_conj(vector_conj(vector_empty(), keys(i)), vals(i))
       block
         type(cons_value) :: entry_val
         entry_val%tag = TAG_VECTOR
         allocate(entry_val%vector_val)
         entry_val%vector_val = entry
         l = list_cons(entry_val, l)
       end block
    end do
  end function map_to_entry_list

  ! A set's elements -- unlike a map's seq, no [k v] entry wrapping,
  ! since a set's "value" at each element is just that element again.
  ! Same insertion-order-then-hash-order-once-promoted rule as above.
  function set_to_element_list(m) result(l)
    type(array_map_t), intent(in) :: m
    type(cons_ref) :: l
    integer :: i
    type(cons_value), allocatable :: keys(:), vals(:)
    call array_map_entries(m, keys, vals)
    l = list_empty()
    do i = size(keys), 1, -1
       l = list_cons(keys(i), l)
    end do
  end function set_to_element_list

end module RT
