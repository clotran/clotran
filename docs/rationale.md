# Why host Clojure on Fortran rather than bridge to it

Clojure in clj can already call Fortran, and for linear algebra it
does it well -- core.matrix and Neanderthal reach BLAS/LAPACK through
JNA or Panama, and if what you want is fast matrix math from Clojure,
use those. They are less work than this and they are finished.

They reach *F77*, though, and that is the distinction this project is
built on.

## There is no Fortran ABI above F77

Everything an FFI bridge can call easily is the 1978 subset: scalars
passed by reference, explicit-shape arrays, external (non-module)
procedures, no allocatables, no derived types. BLAS is exactly that
subset, which is why BLAS bindings exist for every language and why
they were never hard to write.

Above that line there is no standard. An assumed-shape array, an
`allocatable`, a `pointer`, a `character(len=:)`, an `optional`
argument, a `class(*)` -- none of these are passed as an address.
They are passed as a *descriptor*, a compiler-private struct whose
layout is not specified by the standard and is not the same between
gfortran, flang, and ifx. Add to that module-symbol mangling, which
is also per-compiler:

```
gfortran   __modname_MOD_procname
flang      modname_procname_
ifx        modname_mp_procname_
```

So "call a modern Fortran library from C" means: know the target
compiler, know its descriptor layout, know its mangling, and redo all
three when the library is rebuilt elsewhere. `ISO_Fortran_binding.h`
is the standard's answer and it is both painful and unevenly
implemented.

[clojure-fortran](https://github.com/memmett/clojure-fortran) shows
the shape of the workaround honestly: mark each routine `bind(c)`,
write a C header for it, run `jextract`, call the generated clj from
Clojure. That works -- but `bind(c)` is precisely a promise *not* to
use assumed-shape arrays, allocatable or optional arguments, derived
types with allocatable components, generic interfaces, or polymorphism.
You get Fortran back only by giving up the parts of Fortran written
after 1990, and you hand-write a wrapper per routine to do it.

Hosting *on* Fortran removes the boundary instead of crossing it.
A clotran array is a Fortran array; handing it to a library is an
ordinary call, with no descriptor to fabricate, no mangling to guess,
and no copy (verified: a contiguous buffer passed as `a(*)` reaches
the callee at the same address).

## The same reason gdb can't show you a Fortran object

Worth noting because it's the identical root cause, not a coincidence.

gdb being written in C/C++ isn't really why -- but the instinct behind
the question is right. Two things are:

1. **There is nothing stable to read.** An allocatable array's bounds,
   allocation status, deferred string length, and dynamic type all
   live in that same compiler-private descriptor. A debugger can't
   decode it directly; it can only follow whatever DWARF says, and the
   attributes needed to describe it indirectly
   (`DW_AT_data_location`, `DW_AT_allocated`, `DW_AT_associated`,
   `DW_TAG_generic_subrange`) only landed properly in DWARF 5, with
   emitter support arriving late and unevenly.

2. **gdb's type model was built for C.** It assumes a type's layout is
   known statically from the debug info. Fortran's interesting types
   describe themselves *at runtime*. That's a genuinely C-shaped
   worldview, and retrofitting it is why `print my_alloc_array` works
   on a good day with one compiler and prints garbage on another.

Both failures -- C can't call it, gdb can't see it -- are the same
missing thing: no ABI for anything Fortran gained after F77.

This is also why clotran's debugger is written in clotran itself
(`clotran-break`, `docs/guide.md`). A debugger written in the language, over a value
representation the host defines, has no descriptor to decode and no
DWARF to depend on.

## What Fortran gives back

- Arrays of any rank and any lower bound, column-major, bit-identical
  to what a Fortran routine expects.
- `class(*), allocatable` -- arbitrary kinds and derived types in one
  component, with the type checked at `select type` rather than
  tracked by hand behind a `void*`.
- Kinds, `complex`, IEEE control, whole-array operations: the reasons
  anyone calls a Fortran library in the first place.
- It runs where Fortran runs. No clj, which matters on the clusters
  where the libraries being called actually live.

## Why the arrays are fast

The old Fortran-beats-C benchmark folklore is mostly one rule:
**dummy arguments may not alias.** If a variable is reachable through
two arguments of the same call, the standard forbids defining it
through one and referencing it through the other. So in

```fortran
subroutine saxpy(n, alpha, x, y)
```

the compiler may assume `x` and `y` do not overlap, and is free to
vectorize, reorder, fuse, and keep values in registers across stores.

C assumes the reverse -- any two pointers may alias -- which is why
`restrict` had to be added in C99. Fortran gets `restrict` on every
argument, everywhere, without anyone remembering to write it and
without the chance of asserting it wrongly.

Two smaller things compound it:

- **Contiguity is in the type.** `contiguous`, explicit-shape and
  assumed-size say so at compile time; a `float *` never does.
- **Whole-array syntax hands the compiler the loop** (`y = y + a*x`)
  rather than making it recover one from pointer arithmetic.

Honest version: modern C with `restrict`, `-ffast-math` and a good
vectorizer closes most of this gap, and the remaining difference on
straight kernels is usually small. What doesn't close is the default
-- the Fortran code is fast without the author doing anything, and the
C code is fast when the author annotates correctly. For a language
host handing arrays to numerical libraries written by other people,
the default is the part that matters.

## And what it costs

C would have been easier for the *interpreter*. C has a real `union`
and real casts, so the tagged value is 16 bytes in one arena instead
of a component per payload kind across several pools; struct
assignment is a plain copy rather than an overloaded `=` with a
`FINAL` attached, so refcounting stays visible at the sites that do
it; and function pointers, sanitizers, and libffi are all first-class.

That's the trade, and it's the right way round: the friction is in the
value representation, which is a solved problem in any language, and
the payoff is at the interop boundary, which is not.
