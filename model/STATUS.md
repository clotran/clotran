# Model status: start here (lanes read this before exec-PLAN.md)

Keep this file short; update it when a lane lands. Details live in
model/exec-PLAN.md (cited by heading, never copied) and docs/model-coverage.md.

## Tools (cheap navigation)
- `make book-map` -> build/book-map.txt, `book:line event-name` for every
  defun/defthm/defun-sk/defmacro/defconst of every MODEL_BOOKS book. Grep it
  instead of reading books (models are huge; use `grep -n` and `sed -n a,bp`).
- `scripts/dev-try BOOK EVENT` -> PASS/FAIL + key checkpoints in <=60 lines,
  proofs skipped before EVENT. DEV ONLY, not a gate: certify with `make model`.
- `make crosscheck`, `make check-model-ratchet`, `make check-vm-gen` print a
  few lines on success; full logs in build/*.log (failure prints <=20 lines).

## Done
Milestones 1, 1b, 2a-2c, 3a.., 5 (def, letfn, deftype, new, set!, dot) of
exec-PLAN.md "Milestones" are proved and generated; the analyzer, heap, VM,
compiler, and runtime rows of docs/model-coverage.md are Generated or
Modeled. Lane 3 (vmtrg, vmtrcl): vm_tr's const/local/if/do/let*/loop/recur/throw generated;
captures in place, do's dead-local encoding done; vm_clause's clause (vtg_clause =
ex-clause) and the arity-error clause (vtg_arcl = ex-arcl, ex-arcl-mxcl) generated.

## Next lanes, in order (exec-PLAN.md "Lane 3: vm.inc's translation generated", "Next")
1. Entry: DONE. vmtrcl's vtg-clause (vtg-clause-ex-clause: ex-clause at sl 1,
   the scope ex-fbcm the host's) and vtg-arcl (ex-arcl; ex-arcl-mxcl: ex-mxcl's
   :arity throw is the appended clause's prim's) generated into vm_tr_gen.inc,
   fuzzed (fuzz-vmtr-gen, -x); vm_clause's and vm_compile_fn's hand clause code gone.
   Named: vtg_self's value `(:capt m)`, sl 0 when the body reads no self slot.
2. loop/recur: DONE. ex-tr's two loop shapes (ex-lind) and recur proved
   (exec-vmtr..exec-vmok) and generated: vmtrg's vtg-tr kinds 12, 16,
   vtg-lind (vtg-lind-ex), vtg-tlr (vm_clause's loop test); vm_tr's
   hand-written loop/recur gone.
NEXT STEP: item 3 (exec-PLAN Lane 3 "Next" 3/4 and the map's N_CALL row).
3. Calls and Vars: builtin prim / callw as ex-trcall's cases; deref as host prim.
4. try, letfn, case: vm_scan refuses them today.
Cost theorem and fuzz-vmtr-gen are done.

## Owed rows (docs/model-coverage.md, ratchet.edn `:owed 2`; may only shrink)
- "VM runtime: the translation from clotran's tree, the entry, the hooks" (Lane 3 above).
- "Ahead-of-time compiler to Fortran" (compiler.cljf, purefort.cljf; none modeled).

## Deviations
DEVIATIONS.md: 86 numbered entries, 44 not marked RESOLVED. A deviation with no
entry there is a bug.

## Traps
- CERT_SECS (Makefile, default 3600) is CPU seconds per book; use
  `make model CERT_SECS=7200` for books you did not touch (vmg ~1940 s).
- Never kill a process you did not start: other lanes (Lemmis) share the machine.
- Slow books: vmg ~1940 s, vmx2*/vmi/vmg chain, exec-vmok (split into
  exec-vmok1 + exec-vmok; the flag proof ex-vm-agree-flag is most of the time).
- No skip-proofs/defaxiom/defttag in any book; books < 800 lines.
- Changing a book moves its ratchet hash: run `scripts/model-ratchet --stamp`
  then `make check-model-ratchet`. Gates before handing back: make model,
  check-model-ratchet, check-vm-gen, crosscheck.
- A book added/removed must be in MODEL_BOOKS (Makefile) in dependency order.
