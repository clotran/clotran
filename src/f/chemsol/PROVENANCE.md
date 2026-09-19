# Vendored ChemSol

`chemsol.f90` and `push_array.f90` are James Borden's ChemSol 2.1
library (Arieh Warshel, Jan Florian, James Borden), copied verbatim on
2026-09-19 from

    ~/jborden/chemsol/src/chemsol.f90
    ~/jborden/chemsol/src/push_array.f90

Do not edit them. `main.f90` from the same directory is deliberately
NOT here: replacing it with clotran code is the point (PLAN.md step 7),
and `examples/chemsol.cljf` is that replacement. `src/f/ChemSolBind.f90` is
the binding, ours.

The reference outputs the driver is checked against are
`~/jborden/chemsol/tests/test{1,2,3}_main.out`, produced by the
original program. On this machine the original program only builds
with `gfortran -std=legacy` (a FORMAT in main.f90 lacks a comma and
libgfortran 16 rejects it at run time) and then reproduces those files
byte for byte; `scripts/chemsol-check` compares against them.

What the library keeps as module state, and what that costs the
binding: `ran2`'s generator state and the `iff` switch are module
variables, so a second calculation in one process does not start from
the same random sequence as a fresh process would. One calculation per
process matches the reference exactly; more than one is a difference
this binding does not hide.
