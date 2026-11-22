# Release 1.0.0: the checklist

Written 2026-11-22 against `main` at f32a82f3 (149 commits after `v1.0.0-rc.9`, which VERSION still
names). Every result below was run that day in a clean worktree built with `make` (gfortran, macOS
arm64); nothing here is recalled. States: **done**, **open**, **decided-to-stay**. Tagging 1.0.0 is
James's decision (PLAN step 35); this lists what that decision rests on.

## Open

| # | Item | Evidence | Who or what is needed |
|---|---|---|---|
| 1 | `make crosscheck` green on the tree to be tagged | not run here (it takes about 1.5 h and the main session owns it). The last verdict on record, in git log: "crosscheck EXIT 0 on the tree before" cd70177a; 9 commits since (e8b4ff91..f32a82f3), whose gating is not recorded | the main session, at the merge that becomes rc.10 and again at the tag |
| 2 | `make fuzz-all` at full size on a frozen tree | last clean 2026-10-13 on rc.2's tree (PLAN step 35: 22 of 22 macOS, 21 Linux, 21 Windows). Since then `scripts/fuzz-*` grew to 46 scripts and the language, the pure tier and fortran.ops changed | a frozen tree and hours of machine time, on macOS, Linux and Windows (CLAUDE.md asks it of a release candidate); not run here |
| 3 | Linux and Windows gates and artifacts for the tag | rc.9's were run (RELEASE-NOTES, Platforms). Since rc.9 `src/f`, the pure tier and fortran.ops changed; none of `scripts/gate-linux`, `scripts/gate-wsl`, `scripts/dist-check`, `packaging/windows/check.ps1` was run here | James's x86_64 Windows machine for `gate-wsl` and the zip check; Docker for `gate-linux`, `dist-linux`; run at the tag |
| 4 | DEVIATIONS 85 has no kind | `## 85` exists, the table at the top of DEVIATIONS.md has no row for 85 (and none for 84, which reads RESOLVED); RELEASE-NOTES says "none open" only if every entry has a kind | James: classify 85 (it reads like 48: a cast clotran skips, accepting a program clj refuses -- "1.x, staying through 1.0", or "design"); add rows 84 and 85 to the table. DEVIATIONS.md is not this lane's file |
| 5 | DEVIATIONS 91 and 94 are kind 1.x with no recorded decision | 48, 51, 54 and 74 each say "Stays through 1.0 (decided 2026-10-10, PLAN step 35)"; 91 (the pure tier lowers some kinds) and 94 (complex is a record) say what removal takes but not that they stay | James: decide that they stay through 1.0 (then the entry says so), or that something is done first |
| 6 | The version strings the bump touches | `VERSION` and also `install.sh` line 13 (`1.0.0-rc.9`), `install.ps1` line 12, `docs/guide.md` line 25 (`clotran --version`, already stale at rc.8), `docs/status.md` "Versions" section, RELEASE-NOTES.md's first paragraph (drafted for rc.10) | the main session when it bumps; `make check-install` compares `clotran --version` to VERSION |
| 7 | The release itself | `make dist`/`scripts/dist-linux` archives, `SHA256SUMS`, the GitHub release, the tag; the sibling repositories (clotran-deps, clotran-plot, clotran-ui, clotran-vscode, clotran-mode) pointing at a clotran that exists | James |

## Done

| Item | State | Evidence (run 2026-11-22) |
|---|---|---|
| Static checks | done | `make check-static`: EXIT 0 (no static string lengths in clotran-bin, libchemsol, libblas; the text-relocation check is ELF only, not run on macOS) |
| Pure tier against clj | done | `make check-pure`: "pure-check: 525 runs (105 cases x 4 compilers + the library), 525 agree, 0 differ; 42 functions pure in the library" |
| Fortran's types, the second oracle | done | `scripts/ftypes-check`: 349 cases, 321 compared with the compilers, 28 not (the standard leaves them to the processor); gfortran 0 differ, flang 0 differ, clotran 0 differ (349), pure Fortran 0 differ (343 lowered, both compilers); hints 11 pairs 0 differ; elementary functions 163 cases within bound, worst error 1 ulp |
| The oracle against clj | done | `scripts/oracle`: "1402 cases, 1379 agree, 23 expected differences, 0 unexpected" (RELEASE-NOTES said 1,332 / 1,310 / 22 at rc.9; updated) |
| Index of definitions | done | `make check-index`: "INDEX CHECK PASSED" (core.clj 670 definitions, 838 Vars, agree) |
| No JVM names outside upstream/ | done | `upstream/check-names`: EXIT 0, no output |
| Model drift ratchet | done | `make check-model-ratchet`: "ok"; `model/ratchet.edn` :owed 1 |
| The language suite | done | `scripts/run-clojure-tests-parallel test/clj/derived`: "TOTAL tests=312 pass=2719 fail=0 error=0" |
| The libraries on Clojure's own tests | done | `make check-libraries`: tests=141 pass=1001 fail=4 error=4; "8 reports, 8 expected (DEVIATIONS 4, 28, 67), 0 unexpected, 0 stale" |
| Libraries loading | done | 25 of the 25 that load (the five host-bound ones are DEVIATIONS 12), each required and every public var bound but clj's own unbound dynamics (`clojure.test.junit/*depth*`, `*var-context*`: unbound in clj too) |
| README and guide examples | done | `make check-readme`: "readme-check: 8 blocks run (6 evaluated, 2 REPL sessions) of 30, 0 differ" before this lane's README addition; `scripts/readme-check README.md` after it: "3 blocks run (2 evaluated, 1 REPL sessions) of 13, 0 differ", and with one expected value changed on purpose "1 differ", exit 1. `examples/mylib` built and printed `[2.0 4.0 6.0]` and `56.0`. docs/types.md's examples run by hand: each printed the value it claims |
| Ledger: every entry has a kind (but 85) | done but for 4 and 5 | table rows: 93; resolved 43, design 38, host 6, 1.x 6 (48, 51, 54, 74, 91, 94) |
| Language ported whole | done | 719 of 719 top-level forms of core.clj load (RELEASE-NOTES; not re-run here, the derived suite above and the index check exercise it) |
| Windows, Linux, musl, x86_64 at rc.9 | done at rc.9 | RELEASE-NOTES, Platforms. Re-run owed at the tag: item 3 |

## Decided to stay

| Item | Why it is not a 1.0 gate | Where decided |
|---|---|---|
| DEVIATIONS 48 (hints inferred, narrower), 51 ("Divide by zero" wording), 54 (a slash in a namespace), 74 (the nil key's place in a hash walk) | each says what removal takes; the policy says a minor may remove them | PLAN step 35, 2026-10-10 |
| DEVIATIONS 91, 94 | would join this list on James's decision (item 5) | -- |
| Speed: an interpreter, 2x to 17x slower than a warmed clj, 35x to 209x on inline numeric loops | said plainly in RELEASE-NOTES and status.md; compiled-by-default is step 39, after 1.0 | PLAN steps 35, 39 |
| Interop: derived types, optional and pointer dummies listed, not bound | "the first thing in 1.x" | PLAN step 35 |
| The debugger: calls not lines, one level, no socket | said plainly | PLAN step 35 |
| `docs/model-coverage.md` Owed rows | one row is Owed: the ahead-of-time compiler (type inference proved, slices 4d, 4e, 5, arrays and hoisting tested, not proved); the rest is Modeled, Generated or By design. "Ship first, model on demand": no new proof is a gate. Parked items listed in that file (Lemmis stage B, JIT emitter generation, the moving nursery, a concurrency refinement proof) | James, 2026-11-21; PLAN step 38's queue after 1.0 |
| Lemmis, editors, graphics, step 40 | queued after 1.0 | PLAN steps 36-40 |
| Types not yet Fortran's: `logical` and `character(len=n)` as kinds, rank above 1, array sections, arrays of complex, a scalar class for complex | listed in docs/types.md and DEVIATIONS 91, 94 | James, 2026-11-21 (types) |

## What this lane changed

README (Fortran's types, a verified block; the docs list), RELEASE-NOTES.md (rc.10 entry text, counts
re-measured, the install section no longer names rc.5), docs/status.md (five oracles, the types row,
two scorecards re-dated), docs/README.md, docs/building.md (targeted checks, test/ftypes, worktrees),
PLAN.md step 35 (a status line). VERSION is not bumped: the text says rc.10 where it is drafted.
