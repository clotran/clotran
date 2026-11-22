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
| `complex(4)` | :complex4 | `fortran.ops.Complex` | `(fortran.ops/complex4 "1.5" "2.5")` | -- |
| `complex(8)` | :complex8 | `fortran.ops.Complex` | `(fortran.ops/complex8 "1.5" "2.5")` | -- |

Arrays have the same kinds (`(fortran/make-array "real8" n)`, `int1` .. `int8`, `real4`).
The exact types of the tower -- `BigInt`, `Ratio`, `BigDecimal` -- have no Fortran
intrinsic type; they are library types, the way a Fortran program holds an extended-precision
number as a derived type with defined operators. They are tier B in the compiler's words.

Complex has no scalar class yet: a value is a record, native inside a compiled function
(DEVIATIONS 94). Not there yet: `logical` as a kind (a boolean is `true`/`false`),
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
sqrt`, `huge tiny epsilon kind digits`, for complex `cmplx conjg aimag`, and the elementary functions `exp log log10 sin cos tan asin acos
atan atan2 sinh cosh tanh` (the host libm's, measured against a correctly rounded reference: below, and DEVIATIONS 95), and of a complex `exp log sqrt sin cos abs` (DEVIATIONS 98). `CMPLX(x, y)` is a
complex(4) whatever the arguments' kind, as Fortran's is; a complex product the processor would
round, any complex division and `**`, LOG of zero, and a real to an integer power whose partial powers are not all
exact (`x**2` always is defined) are refused (DEVIATIONS 93, 94). Real arithmetic is IEEE: overflow is
infinity, `x/0.0` infinity, `0.0/0.0` NaN, in both real kinds; a NaN or an infinity has no integer
value (DEVIATIONS 90).

## Accuracy, measured

The standard gives the elementary functions no accuracy. `scripts/ftypes-accuracy` measures it: 4000
arguments per function and real kind (192,000 points with `+ - * / sqrt` and the complex functions; seed 1), half structured (near zero, both
sides of 1, the domain's edges, the overflow and underflow thresholds, every power of two, huge
arguments up to 1.8e308 for sin, cos and tan, values near the first 200 multiples of pi/2 and
near 2**j pi/2, the real(8) argument closest to a multiple of pi/2), half random (uniform, and
log-uniform over the kind's whole exponent range). The reference is `test/ftypes/refmath.clj`,
80 digits rounded once (`+ - * /` and `sqrt`: the exact result rounded once). It checks itself twice: 1
point in 20 is recomputed at 110 digits (9600, 0 differ), and the same points are folded at compile time
by gfortran, whose folding is MPFR's and MPC's, correctly rounded (9249 of them, subnormal arguments and
results left out because gfortran rounds those twice; 0 differ). Each entry is the maximum / the 99.9th percentile of the error in ulps of the
kind (0 means correctly rounded), on this machine (macOS, its libm), gfortran and flang at -O0, the
pure tier compiled at -O2 -ffp-contract=off:

| function | kind | points | gfortran | flang | fortran.ops | pure gfortran | pure flang |
|---|---|---|---|---|---|---|---|
| exp | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| exp | real8 | 4000 | 1 / 0 | 1 / 0 | 1 / 0 | 1 / 0 | 1 / 0 |
| log | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| log | real8 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| log10 | real4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| log10 | real8 | 4000 | 1 / 0 | 1 / 0 | 1 / 0 | 1 / 0 | 1 / 0 |
| sin | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| sin | real8 | 4000 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| cos | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| cos | real8 | 4000 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| tan | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| tan | real8 | 4000 | 2 / 2 | 2 / 2 | 2 / 2 | 2 / 2 | 2 / 2 |
| asin | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| asin | real8 | 4000 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| acos | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| acos | real8 | 4000 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| atan | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| atan | real8 | 4000 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| sinh | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| sinh | real8 | 4000 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| cosh | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| cosh | real8 | 4000 | 1 / 0 | 1 / 0 | 1 / 0 | 1 / 0 | 1 / 0 |
| tanh | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| tanh | real8 | 4000 | 1 / 0 | 1 / 0 | 1 / 0 | 1 / 0 | 1 / 0 |
| atan2 | real4 | 4000 | 1 / 1 | 1 / 1 | 0 / 0 | 0 / 0 | 0 / 0 |
| atan2 | real8 | 4000 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| + | real4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| + | real8 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| - | real4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| - | real8 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| * | real4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| * | real8 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| / | real4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| / | real8 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| sqrt | real4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| sqrt | real8 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |

- real(8): every leg is the same libm, and they agree bit for bit (0 of 52,000 points differ from
  `fortran.ops`). At most 1 ulp, except TAN, 2 ulps (at -2.698607540904404e10 and -3.48e41, for
  example; MPFR agrees with the reference there).
- real(4): `fortran.ops` and the compiled code compute in real(8) and round once (they agree bit for
  bit), and are correctly rounded on all 52,000 points; gfortran's and flang's own real(4)
  intrinsics are 1 ulp off on some (3,030 of 52,000). Rounding twice can still be wrong: the
  exhaustive `--scan-real4` (below) finds 18 arguments in 42.8 billion.
- `+ - * / sqrt`: correctly rounded on every leg and kind; through real(8) first, 0 of the real(4)
  points round differently, as the theorem says (53 >= 2 x 24 + 2).
- `scripts/ftypes-check` runs `scripts/ftypes-accuracy --quick` (16 points per function and kind,
  768 in all) and fails past these maxima, the same for every leg: 1 ulp, TAN of a real(8) 2, `+ - * / sqrt` 0;
  and where the compiled code differs from `fortran.ops` on any real point. A regression that matters
  (a real(8) through a real(4), a lost argument reduction) is millions of ulps, not one more.

### Real(4) through real(8), exhaustively

`scripts/ftypes-accuracy --scan-real4` runs each one-argument function over EVERY real(4) value (2^32 bit
patterns less the non-finite, in its domain; 42.8 billion arguments, 31 s on 7 cores). Rounding the real(8)
value to real(4) can be wrong only where the real(8) value is on a real(4) midpoint or one real(8) ulp from
it; the loop finds those, and refmath decides each (results outside the normal real(4) range are not
scanned):

| function | arguments | near a midpoint | double roundings | fortran.ops wrong |
|---|---|---|---|---|
| exp | 4278190080 | 1 | 0 | 0 |
| log | 2139095039 | 16 | 5 | 5 |
| log10 | 2139095039 | 15 | 1 | 1 |
| sin | 4278190080 | 14 | 2 | 2 |
| cos | 4278190080 | 20 | 4 | 4 |
| tan | 4278190080 | 2 | 0 | 0 |
| asin | 2130706434 | 4 | 0 | 0 |
| acos | 2130706434 | 3 | 2 | 2 |
| atan | 4278190080 | 2 | 2 | 2 |
| sinh | 4278190080 | 2 | 2 | 2 |
| cosh | 4278190080 | 4 | 0 | 0 |
| tanh | 4278190080 | 0 | 0 | 0 |

18 double roundings: the correctly rounded real(8), rounded again, is 1 ulp from the correctly rounded
real(4) (log(9.472636) is 2.2484071, through real(8) 2.2484074; sin(9830.398) is -0.34761325, not
-0.34761328; MPFR agrees). `fortran.ops` and the compiled code are wrong on exactly those 18 and on no
other real(4) argument of these functions. ATAN2 (two arguments) is swept, not scanned.

### Complex

EXP, LOG, SQRT, SIN, COS and ABS of a complex, measured the same way, each PART in ulps of the part kind
(LOG and SQRT principal values; the sign of a zero imaginary part picks the side of the cut):

| function | kind | points | gfortran | flang | fortran.ops | pure gfortran | pure flang |
|---|---|---|---|---|---|---|---|
| exp | complex4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| exp | complex8 | 4000 | 2 / 2 | 2 / 2 | 3 / 2 | 2 / 2 | 2 / 2 |
| log | complex4 | 4000 | 1694574510 / 1684919996 | 1694574510 / 1684919996 | 0 / 0 | 32 / 0 | 32 / 0 |
| log | complex8 | 4000 | 8716560023488369748 / 8711941746245982286 | 8716560023488369748 / 8711941746245982286 | 3 / 2 | 8716560023488369748 / 8711941746245982286 | 8716560023488369748 / 8711941746245982286 |
| sqrt | complex4 | 4000 | 436207616 / 430228120 | 436207616 / 430228120 | 0 / 0 | 0 / 0 | 0 / 0 |
| sqrt | complex8 | 4000 | 6473974912013982395 / 6372751694632527319 | 6473974912013982395 / 6372751694632527319 | 1 / 1 | 6473974912013982395 / 6372751694632527319 | 6473974912013982395 / 6372751694632527319 |
| sin | complex4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| sin | complex8 | 4000 | 3 / 2 | 3 / 2 | 2 / 2 | 3 / 2 | 3 / 2 |
| cos | complex4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| cos | complex8 | 4000 | 2 / 2 | 2 / 2 | 2 / 2 | 2 / 2 | 2 / 2 |
| abs | complex4 | 4000 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| abs | complex8 | 4000 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |

`fortran.ops` (clotran's formulas in real(8)) is correctly rounded on complex(4) and within 3 ulps on
complex(8). The compilers' LOG and SQRT, which the compiled code calls, are not: near |z| = 1 LOG's real part
keeps no relative digits, and SQRT drops a part far below the other (DEVIATIONS 98 has the points).

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

Complex is native inside a function too: `(f/+ z w)` is a `complex(real64)` add, and a complex
leaves the function as `(f/real z)` and `(f/aimag z)`. `exp log sqrt sin cos abs` of a complex are Fortran's intrinsics, the
processor's libm (measured: DEVIATIONS 98). Not yet lowered: arrays of complex,
`/` and `**` of a complex, the narrow scalar kinds and complex as parameters or results of a
compiled library function, array results of the narrow kinds, rank above 1 (DEVIATIONS 91, 94).
