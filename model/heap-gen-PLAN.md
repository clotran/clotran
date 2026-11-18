# Modeled -> Generated: the heap and collection rows (handoff item 5)

What scripts/acl2-fortran expresses today: integer +, *, unary -, <,
equal, if, let/lambda, calls, tail recursion as loops, stobj fields and
arrays (GC.f90's pools through its `hp_*` accessors), mv, and a book's
own host reads (`:rt`: hand-written shims on values/integers). It has
no floor, mod, logand or ash; Lemmis's generator proof
(lemmis/model/gen-proof.lisp `*g-prims*`) knows exactly that set, so
adding a primitive means Lemmis learns it too. Nothing generated
allocates except heapal's slot/run takes; building an object (gc_obj,
gc_vec with roots) stays a shim.

| Candidate | Expressible now? | Needs |
|---|---|---|
| heaprt rest: `collect_*` | no model function: heaprt says what survives, not the sequence collect_full runs (finish_pending, merge_batches, census, sweep, aging) | a sequential model of the collection's driver first |
| heaprt: pools' growth (grow_obj/vec/str) | grow-pool is modeled, but the Fortran is allocate + move_alloc over derived types; generated, it would be calls to resize shims | little payoff: the shim is the code |
| heaprt: arg spares (`aspare`, Eval's args_take/args_give) | yes, as spg is | a second spg; the code lives in Eval.f90 (out of this lane) |
| heapmt (batches, pending lists, world stop) | the batch takes are generated already (heapal); the rest is locks and condition waits, the host's | the concurrency stays hand-written by design |
| vector (`gcv_nth`, conj, assoc, pop, subvec) | nth's walk: no -- it needs a digit, `iand(ishft(j,-s),31)` | floor/mod (or ash/logand) in the generator, and in Lemmis's `*g-prims*`; conj/assoc/pop also allocate (shims) |
| hashmap get/assoc | no -- the bitmap needs shifts, masks and a popcount | as the vector, plus popcount |
| arraymap reads: index_of, get, contains, key_at, val_at | YES: a counted scan of a run's words, gc_equal as a host read on two values' words | nothing new: an `:rt` hook, as anpass's ast reads |
| arraymap edits: copy_run's and dissoc's loops | yes, writing arena words through hp_set_*; the new runs' allocation a shim | slice 2, if the budget allows |

Choice: the ARRAY MAP's reads, model/arraymapg.lisp, refined to
arraymap's am-index / am-get / am-contains / am-keys / am-vals. Its
host hook (amg-keq, gc_equal) is named under the hypothesis amg-keq-ok:
on the run's keys it is equality of meaning (false for =, on NaN). The
vector's nth is the next payoff, once the generator and Lemmis learn a
digit (floor by 32 or iand/ishft); hashmap after it.
