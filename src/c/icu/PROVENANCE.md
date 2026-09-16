# Vendored ICU source

Everything under `source/` is Unicode, Inc.'s official ICU4C release
78.3, unmodified (LICENSE in this directory), fetched from
`github.com/unicode-org/icu/releases/tag/release-78.3` (the
`icu4c-78.3-sources.tgz` asset).

Do not edit it. This exists for exactly one reason: `#"..."` needs a
regex engine, and writing one is not "porting a primitive" the way
`rest` or `+` were -- ICU already is one, correctly, for every script
Unicode defines. See `src/f/Regex.f90` for the six operations Fortran
actually uses and why C is here at all, given the whole rest of this
project's point is not needing it.

## What was trimmed, and why

`source/test` (ICU's own test suite) and the bulk of
`source/test/testdata` are NOT vendored -- together they were 47MB of
fixtures for tests this project never runs. What remains of `test/` is
only the `Makefile.in`/`*.in` template files `./configure` insists on
generating a `Makefile` from (`AC_CONFIG_FILES` in `configure.ac` lists
them unconditionally), plus the one small driver script
(`test/testdata/BUILDRULES.py`) `configure` invokes to emit an (empty,
since there is no real testdata) `test/testdata/rules.mk`. Without
that one file, `./configure` fails outright trying to run it.

`source/samples` (212K) is vendored in full -- too small to bother
trimming and excluding it risked the same kind of `configure` failure
for no real saving.

## How it is built

Nothing here is prebuilt except ICU's own `source/data/in/icudt78l.dat`
-- the FULL Unicode Character Database and locale data, already
compiled into ICU's binary `.dat` format by the ICU project itself, so
the four static libraries below need no CLDR/genrb data build at all.

The top-level Makefile (`ICU_STAMP` target) runs, in ICU's own required
order (`source/Makefile.in`'s `SUBDIRS`):

    ./runConfigureICU <macOS|Linux> --enable-static --disable-shared \
        --disable-extras --disable-icuio --with-data-packaging=static
    make -C stubdata
    make -C common
    make -C i18n
    make -C tools
    make -C data

producing `source/lib/lib{icuuc,icui18n,icudata}.a` -- static, so the
final `clotran-gc` binary needs no ICU install, no dylib/so, no data
file, and no locale directory on the machine that runs it. Everything
`make` produces (the `.a` files, `.o`/`.ao` objects, generated
`Makefile`s, `config.status`) is gitignored; only source is vendored,
same rule as `core.clj`.

`layoutex`, `icuio`, `extra`, `samples` and `test` are never built --
none of it is reachable from `uregex_*`, and `test`/`samples` alone
would be most of the wall-clock cost.

## What is NOT done here

Windows is not wired into this Makefile. ICU's own Windows build goes
through `source/allinone`'s MSVC solution files, which this
POSIX-shaped Makefile does not invoke -- but that source is vendored
here too, so it is available to whoever wires it up, unlike a build
that only ever fetched macOS/Linux binaries.
