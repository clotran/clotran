# clotran

Clojure, hosted on Fortran.

The interpreter core (reader, evaluator, persistent data structures,
namespaces) is written in Fortran (`src/f`); the language itself --
`clojure.core` and everything built on top of it -- is meant to grow
as actual Clojure source (`src/clj`, `src/cljc`), loaded at startup,
not hardcoded into the host.

flang is the pinned target compiler; gfortran is used only as a
second, independent cross-check (see `NOTES.md`).

## Layout

- `src/f` -- the Fortran host: value representation, persistent
  list/vector/map, namespaces, reader, evaluator.
- `src/clj`, `src/cljc` -- the language itself, written in itself.
  Currently empty; see `src/cljc/README.md`.
- `test/f` -- unit tests for the Fortran host, one file per module.
- `scripts/clotran` -- the user-facing launcher (see below).

## Build

```
make            # builds clotran(-bin) and every test binary (flang)
make test       # builds and runs every test binary
make FC=gfortran all test   # cross-check on gfortran
```

`clotran-bin` is the raw interpreter, a plain stdin/stdout REPL
with no line editing of its own. `clotran` is what you actually
run -- a thin launcher (`scripts/clotran`) that wraps it in `rlwrap`
when installed, for history and arrow-key editing, exactly the way
real Clojure's own `clj` wraps `clojure`; falls back to the raw
binary with a note if `rlwrap` isn't found.

```
clotran
```

`test/regression/` also carries the official mal per-step test suites
(see `NOTES.md`) -- running those needs mal's own `runtest.py`,
external to this repo (no Python vendored here), against the raw
binary (not the rlwrap-wrapping launcher, same as testing `clojure`
rather than `clj`):

```
python3 ~/jborden/mal/runtest.py --deferrable --rundir test/regression \
    step9_try.mal -- ../../clotran-bin
```

## Status

This code originated as a [mal](https://github.com/kanaka/mal)
implementation -- mal was bootstrap/validation scaffolding to get a
real interpreter working against a real test suite, not the identity
of this project. See `NOTES.md` for the actual design history,
decisions, and what's ahead.
