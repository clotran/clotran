# Types

**clotran's types are Fortran's** (James, 2026-11-21). Clojure's numeric tower stays on
top; its type hints are used where they mean the same thing in Fortran. Where
clojure.core cannot be served that way it differs, and DEVIATIONS.md says why in terms
of types (entries 86-91).

## The kinds

A value's kind is its Fortran kind, by kind number as Fortran writes it. The classes are
clj's Byte, Short, Integer, Long, Float and Double under their Fortran names (the renames
in `upstream/class-names.edn`).

| Fortran | kind | clotran class | constructors | clojure.core cast |
|---|---|---|---|---|
| `integer(1)` | :int1 | `clotran.host.int1` | `(fortran.ops/int1 x)` | `byte` |
| `integer(2)` | :int2 | `clotran.host.int2` | `(fortran.ops/int2 x)` | `short` |
| `integer(4)` | :int4 | `clotran.host.int4` | `(fortran.ops/int4 x)` | `int` |
| `integer(8)` | :int8 | `clotran.host.int8` | `(fortran.ops/int8 x)` | `long`, and every integer literal |
| `real(4)` | :real4 | `clotran.host.real4` | `(fortran.ops/real4 "1.1")` | `float` |
| `real(8)` | :real8 | `clotran.host.real8` | `(fortran.ops/real8 "1.1")` | `double`, and every real literal |

Arrays have the same kinds (`(fortran/make-array "real8" n)`, `int1` .. `int8`, `real4`).
The exact types of the tower -- `BigInt`, `Ratio`, `BigDecimal` -- have no Fortran
intrinsic type; they are library types, the way a Fortran program holds an extended-precision
number as a derived type with defined operators. They are tier B in the compiler's words.

Not there yet: `complex`, `logical` as a kind (a boolean is `true`/`false`),
`character(len=n)` (a string is a string), rank above 1, array sections, and 1-based
indexing of the Clojure array functions (`aget` is 0-based; DEVIATIONS 24).

## Two surfaces over one set of values

- **clojure.core** keeps Clojure's meaning: `(+ (int 5) (int 7))` widens to int8, `(/ 7 2)`
  is a ratio, integer overflow throws.
- **`fortran.ops`** is Fortran's: the result keeps the kind a Fortran result has, `/` on
  integers truncates, `MOD` and `MODULO` differ on negatives, `REAL(i)` is real(4), and a
  result the standard leaves to the processor throws. A front end with Fortran's syntax
  (Lemmis) binds its operators to these.

```
(require '[fortran.ops :as f])
(f/+ (f/int1 100) (f/int4 100000))     ;=> 100100, an int4
(f// (f/int4 -7) (f/int4 2))           ;=> -3
(f/mod (f/int4 -7) (f/int4 3))         ;=> -1
(f/modulo (f/int4 -7) (f/int4 3))      ;=> 2
(f/real (f/int4 7))                    ;=> 7.0, a real4
(f/nint (f/real8 "2.5"))               ;=> 3, an int4
(f/+ (f/int4 2147483647) (f/int4 1))   ;=> throws: undefined: :integer-overflow
```

The operations: `+ - * / **`, `int nint floor ceiling real dble`, `abs sign min max mod modulo
sqrt`, `huge tiny epsilon kind digits`.

## Hints in Fortran's words

A hint says what an argument is. Clojure's spellings work, and so do Fortran's:

| Clojure | Fortran's words |
|---|---|
| `^long`, `^double` | `^int8`, `^real8` |
| `^longs`, `^doubles` | `^int8s`, `^real8s` |
| `^ints`, `^floats` | `^int4s`, `^real4s` |
| `^shorts`, `^bytes` | `^int2s`, `^int1s` |

```
(defn dot ^real8 [^real8s a ^real8s b]
  (loop [i 0 s 0.0] (if (< i (alength a)) (recur (inc i) (+ s (* (aget a i) (aget b i)))) s)))
```

The spelling changes nothing: the same conversions, the same refusal of a wrong kind of array,
the same pure Fortran (checked by `scripts/ftypes-check`). The scalar hints `^real4`, `^int4`,
`^int2` and `^int1` are refused on a fn as `^float`, `^int`, `^short` and `^byte` are, for now
(DEVIATIONS 92).

## What decides what Fortran does

Not clojure.core, and not this file. Three things, in order:

1. **gfortran and flang**, the standard as implemented. Where they disagree the standard
   decides, and the cases are marked `{:undefined ...}` where it leaves the answer to the
   processor.
2. **`test/ftypes/oracle.clj`** -- Fortran's intrinsic types as plain Clojure, run by real
   `clj`. It is the second oracle beside `clj` itself: written once, independent of
   clotran.
3. **`src/clj/fortran/ops.cljf`** -- clotran's own, compared with the oracle.

`scripts/ftypes-check` runs all of it over `test/ftypes/cases.edn`: the oracle against
gfortran and flang (reals bit for bit), then `fortran.ops` against the oracle. Every
case must answer the oracle's value and kind, or, for `{:undefined ...}`, throw. A case
that was undefined and stops being so, or the reverse, fails.

## The compiler

`clotran compile --pure` lowers integer(1), (2), (4), (8), real(4) and real(8) scalars when a
function uses `fortran.ops` (the kinds are Fortran's, the result keeps the kind), arrays of
those kinds as arguments, boolean, strings and records. Inside such a function the kinds are
native: `(f/+ (f/int4 a) (f/int4 b))` is an `integer(int32)` add checked into its kind.
`clojure.core`'s operations widen them as Clojure's do (DEVIATIONS 93). `scripts/ftypes-check`
runs every oracle case through gfortran's and flang's pure builds.

```
(require '[fortran.ops :as f])
(defn mean-sq ^real8 [^real4s a]
  (loop [i 0 s 0.0] (if (< i (alength a)) (recur (inc i) (+ s (* (aget a i) (aget a i)))) (/ s (alength a)))))
```

Not yet lowered: complex, the narrow scalar kinds as parameters or results of a compiled
library function, array results of the narrow kinds, rank above 1 (DEVIATIONS 91).
