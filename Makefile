# gfortran is the default build; flang is the correctness oracle.
#
# Same source, same results, but flang's derived-type copy is 11-36x
# slower on this value type (13.7 ns vs 488 ns scalar, measured), which
# is a 4.5 s bootstrap against 30 s. That tax is paid on every single
# edit-test cycle, so the daily driver is gfortran.
#
# flang is NOT dropped: it has twice caught real mistakes in this code
# that gfortran accepted silently at -Wall -Wextra, and on every actual
# compiler bug this project has hit, flang came out ahead. So the rule
# is both compilers before every commit -- `make crosscheck`. See
# NOTES.md.
FC = gfortran
# Everything the build makes goes under build/: objects, .mod files,
# the test binaries. The one artifact that stays in the root is the
# clotran binary itself. -g is a COMPILE flag only -- on macOS a -g on
# the link line makes the driver run dsymutil and drop a .dSYM bundle
# beside every binary; the debug info is in the objects either way and
# lldb finds it there.
B = build
.DEFAULT_GOAL := all
# -ffp-contract=off: no fused multiply-add. clj's arithmetic rounds each
# multiply and each add, as clj does, and (rem -46 0.1) is 0.0 there;
# gfortran at -O3 on arm64 fused n - q*d and answered the exact residual,
# 2.55E-15 (scripts/fuzz-num). Both compilers, and clotran compile too.
FCFLAGS = -g -O2 -ffp-contract=off -I$(B) -Isrc/f -J$(B) $(FCFLAGS_$(notdir $(FC)))
LDFLAGS = $(FCFLAGS_$(notdir $(FC)))
TESTLDFLAGS = $(TESTLDFLAGS_$(notdir $(FC)))

# Fortran 2018 made every procedure recursive by default. flang follows
# it; gfortran still defaults to F2008, where a procedure not marked
# RECURSIVE may keep its locals in STATIC storage -- so re-entering one
# silently overwrites the outer invocation's variables.
#
# gfortran rejects DIRECT recursion at compile time, which is why this
# was invisible for so long. Indirect recursion it cannot see: an
# evaluator is mutually recursive everywhere (eval_form -> eval_let_head
# -> eval_form). Those corrupted memory quietly, then died later at an
# unrelated `allocate` with SIGTRAP from libmalloc.
#
# -frecursive forces locals onto the stack, which IS the F2018/flang
# semantics this source is written against. -std=f2018 does NOT do it
# (checked on gfortran 16).
#
# -flto because a profile said so: two thirds of a hot loop's time
# was one-line accessors in GC.f90 (vs_get, vs_set, gc_slot,
# gc_kind) called out of line from Eval.f90, which no compiler can
# inline across files without link-time optimisation. Measured on
# 2026-09-23: 13% on the interpreter, 21% on compiled code.
#
# But ONLY clotran-bin needs it, and it is where the build's time went:
# one optimised link of the evaluator took 34 s, and `make` did four
# (clotran-bin, eval_test, abi_test, the embed example) plus one per
# small test. So (2026-09-28): =auto runs the link-time optimiser on
# every core -- 10.7 s, and fib, reduce and into ran at the same speed
# to the millisecond -- and -ffat-lto-objects keeps ordinary code in
# each object beside the optimiser's, so the tests (TESTLDFLAGS) link
# that in under a second. Without LTO the same three forms were 11 to
# 24% slower, which is why clotran-bin keeps it.
#
# flang gets NONE: its build is the correctness oracle (make crosscheck),
# never the binary anyone runs for speed, and its LTO objects are LLVM
# bitcode that link only through the optimiser -- one link of the
# evaluator took over two minutes, four of them per gate.
#
# -O3 on top of the -O2 in FCFLAGS (the later flag wins): measured
# 2026-09-28 on the interpreter, an empty loop 1959 -> 1617 ms, a lazy
# take 2330 -> 1909, a call 1052 -> 813 -- the inlining of the one-line
# accessors that -O2 left out of line. Raising the inline parameters
# further changed nothing.
# -fstack-arrays: an array temporary on the stack, not the heap. The
# roots lists passed to every allocation -- [roots, x] -- are such
# temporaries, grown element by element with malloc and realloc and
# freed after, on every call: malloc, realloc and free were a tenth of
# a lazy walk's time, and a lazy cell cost 287 ns to make, now 134.
#
# The --param limits, because even with LTO those accessors stayed out of
# line in flat_run: GCC stops inlining into a function past
# large-function-insns, and the executor is one very large function.
# Measured 2026-10-01: the lazy sum 1272 -> 1167 ms, a call 146 -> 139
# ns; a full build 12 s longer.
FCFLAGS_gfortran = -frecursive -flto=auto -ffat-lto-objects -O3 -fstack-arrays \
	--param large-function-insns=200000 --param large-function-growth=2000 --param inline-unit-growth=400
# flang is the correctness oracle, and optimised it checks the same code
# in half the time (measured 2026-10-03: the oracle 71 s unoptimised)
FCFLAGS_flang = -O2
# -fno-lto, not merely no -flto: gfortran sees the optimiser's code in a
# fat object and runs it anyway -- 12 s an abi_test link, 0.1 s without
TESTLDFLAGS_gfortran = -frecursive -fno-lto
TESTLDFLAGS_flang =

# Pinned, not just "whatever's on PATH": subtle compiler-specific
# behaviour (FINAL, defined assignment, unlimited polymorphic) means a
# different major.minor can behave differently. Bump deliberately,
# after re-running the suite on both.
REQUIRED_gfortran = 16
REQUIRED_flang = 23.1
FCNAME := $(notdir $(FC))
REQUIRED := $(REQUIRED_$(FCNAME))
ACTUAL := $(shell $(FC) -dumpversion 2>/dev/null | cut -d. -f1,2)
ifneq ($(REQUIRED),)
ifneq ($(ACTUAL),$(REQUIRED))
$(warning $(FCNAME) version is $(ACTUAL), this project is pinned to $(REQUIRED) -- `brew upgrade $(FCNAME)`)
endif
endif

S = src/f
T = test/f

# --- ICU (regex) -----------------------------------------------------
#
# Vendored, not a system dependency: src/c/icu is the OFFICIAL ICU
# source release, unmodified (src/c/icu/LICENSE), built into four
# static libraries the first time anything needs them. No brew, no
# apt, no system ICU install anywhere -- see Regex.f90 for why a
# regex engine is the one piece of this bridge that gets vendored
# rather than ported, in a project whose whole point is not needing
# a C toolchain for anything else.
#
# Platform-detected rather than hardcoded to macOS, since the goal is
# to build the same way on Linux -- ICU's own runConfigureICU already
# has a profile for each. Windows is NOT wired here: that build goes
# through ICU's own MSVC solution files (src/c/icu/source/allinone),
# vendored but not invoked by this POSIX-shaped Makefile.
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
ICU_PLATFORM = macOS
LIBCXX = -lc++
SOEXT = dylib
PKGMOD = $(B)/pkgmod
LIBDL =
# A COMPILED NAMESPACE resolves clotran_* against the running binary
# at dlopen time, so those symbols have to be in its dynamic symbol
# table. Without this the library loads and every call is undefined.
EXPORTDYN = -Wl,-export_dynamic
# sysconf's name for the online processor count: an int whose VALUE is
# the platform's (the macOS SDK's unistd.h). Threads.f90 reads it from
# $(B)/osconst.inc, generated below.
SC_NPROCESSORS_ONLN = 58
# pthread_key_t: unsigned long (sys/_pthread/_pthread_types.h)
PTHREAD_KEY_KIND = c_long
else
ICU_PLATFORM = Linux
LIBCXX = -lstdc++
SOEXT = so
PKGMOD = $(B)/pkgmod
LIBDL = -ldl
EXPORTDYN = -rdynamic
# glibc's bits/confname.h (an enum; its _SC_IOV_MAX is an alias) and
# musl's unistd.h agree: 84
SC_NPROCESSORS_ONLN = 84
# pthread_key_t: unsigned int in glibc's bits/pthreadtypes.h, unsigned
# in musl's alltypes.h.in
PTHREAD_KEY_KIND = c_int
endif

# The platform's constants Threads.f90 needs, as Fortran: the OS seam's
# one generated file (PACKAGES.md). Rewritten only when a value changes.
$(B)/osconst.inc: Makefile | $(B)
	printf '  integer(c_int), parameter :: SC_NPROCESSORS_ONLN = %s\n' $(SC_NPROCESSORS_ONLN) > $@.new
	printf '  integer, parameter :: PTHREAD_KEY_KIND = %s\n' $(PTHREAD_KEY_KIND) >> $@.new
	cmp -s $@.new $@ || mv $@.new $@
	rm -f $@.new
$(B)/Threads.o: $(B)/osconst.inc

CC ?= cc
ICU_SRC = src/c/icu/source
ICU_STAMP = $(ICU_SRC)/.built
ICU_LIBS = $(ICU_SRC)/lib/libicui18n.a $(ICU_SRC)/lib/libicuuc.a $(ICU_SRC)/lib/libicudata.a
ICU_INC = -I$(ICU_SRC)/common -I$(ICU_SRC)/i18n

# One recipe, several output files -- old GNU Make (3.81, macOS's
# default) has no grouped-target syntax for that, hence the stamp file
# every .a depends on instead. The five `make -C` calls are ICU's own
# required build order (source/Makefile.in's SUBDIRS), stopping short
# of layoutex/icuio/extra/samples/test: none of it is reachable from
# uregex_*, and test/samples alone are most of the wall-clock cost.
#
# --with-data-packaging=static bakes ICU's PREBUILT Unicode data
# (source/data/in/icudt78l.dat, already compiled -- no genrb/CLDR
# build needed) directly into libicudata.a, so the built binary needs
# no data file and no locale directory at runtime, anywhere.
$(ICU_STAMP):
	cd $(ICU_SRC) && ./runConfigureICU $(ICU_PLATFORM) --enable-static --disable-shared \
		--disable-extras --disable-icuio --with-data-packaging=static
	mkdir -p $(ICU_SRC)/bin $(ICU_SRC)/lib
	for d in stubdata common i18n tools data; do $(MAKE) -C $(ICU_SRC)/$$d || exit 1; done
	touch $(ICU_STAMP)

$(ICU_LIBS): $(ICU_STAMP)

$(B)/seqlock.o: src/c/seqlock.c | $(B) $(FCSTAMP)
	$(CC) -O2 -c $< -o $@

$(B)/socket_shim.o: src/c/socket_shim.c src/c/socket_shim.h | $(B) $(FCSTAMP)
	$(CC) -O2 -c $< -o $@

$(B)/fs_shim.o: src/c/fs_shim.c | $(B) $(FCSTAMP)
	$(CC) -O2 -c $< -o $@

$(B)/regex_shim.o: src/c/regex_shim.c src/c/regex_shim.h | $(B) $(FCSTAMP)
	$(CC) -c $(ICU_INC) $< -o $@

# --- the host ----------------------------------------------------------

S = src/f
T = test/f
BT = $(B)/test

unit-tests = gc_test persistent_vector_test persistent_list_test persistent_array_map_test \
	persistent_hash_map_test env_test assoc_test printer_test reader_test eval_test bigint_test \
	bigdec_test abi_test native_array_test threads_test gc_mt_test
test-bins = $(addprefix $(BT)/,$(unit-tests))

.PHONY: all crosscheck crosscheck-here clean compiled-core embed image install uninstall
all: clotran-bin $(test-bins) $(B)/core.image $(B)/fc

$(B) $(BT):
	mkdir -p $@

# The build directory belongs to ONE compiler: .mod files are not
# portable between them, and a crosscheck interrupted between its two
# halves left flang's behind for gfortran to choke on ("not a GNU
# Fortran module file"). The stamp names the owner; building with the
# other compiler empties the directory first. Every object and test
# binary depends on it, order-only, so nothing is compiled against a
# module the other compiler wrote.
#
# The emptying happens while the Makefile is READ, not in a recipe. As
# a recipe it ran after make had already judged the objects up to date,
# so the first build after a compiler switch deleted bigint.mod and then
# compiled BigDec against it ("Cannot open module file"); the second
# build worked. Done here, make judges an empty directory.
FCSTAMP = $(B)/.built-with-$(FCNAME)
ifeq ($(filter clean,$(MAKECMDGOALS)),)
ifeq ($(wildcard $(FCSTAMP)),)
$(shell rm -rf $(B)/*.o $(B)/*.mod $(B)/.built-with-* $(BT); mkdir -p $(BT); touch $(FCSTAMP))
endif
endif
$(FCSTAMP): | $(B)
	mkdir -p $(BT)
	touch $@

# One rule compiles every module; the lines below it say which .mod
# files each one needs first (a `use` is a compile-time dependency).
$(B)/%.o: $(S)/%.f90 | $(B) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $< -o $@

$(B)/BigDec.o: $(B)/BigInt.o
$(B)/GC.o: $(B)/BigInt.o $(B)/BigDec.o
$(B)/PersistentVector.o $(B)/PersistentList.o $(B)/PersistentArrayMap.o $(B)/NativeArray.o: $(B)/GC.o
$(B)/PersistentHashMap.o $(B)/Env.o: $(B)/GC.o $(B)/PersistentArrayMap.o
$(B)/Assoc.o: $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o
$(B)/Namespace.o: $(B)/GC.o $(B)/Assoc.o $(B)/PersistentVector.o
$(B)/Printer.o: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentList.o $(B)/PersistentVector.o $(B)/Assoc.o $(B)/NativeArray.o
# LispReader depends on Regex: #"..." compiles a pattern at READ time,
# matching real Clojure's own regex literal (LispReader compiles
# straight to a Pattern, not to a string). See Regex.f90.
$(B)/LispReader.o: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentList.o $(B)/PersistentVector.o $(B)/Assoc.o $(B)/Regex.o $(B)/Printer.o
# The C-callable runtime surface. Linked into clotran-bin so that a
# compiled namespace -- loaded through the door, or linked in -- and an
# embedder both find the same symbols. It is the LAST module: it sits
# on top of Eval, nothing sits on it.
$(B)/ClotranABI.o: $(B)/GC.o $(B)/PersistentVector.o $(B)/Namespace.o $(B)/CompiledFn.o $(B)/NativeArray.o $(B)/Eval.o

$(B)/Eval.o: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentList.o $(B)/PersistentVector.o $(B)/Assoc.o $(B)/Env.o \
	$(B)/Namespace.o $(B)/Printer.o $(B)/LispReader.o $(B)/Regex.o $(B)/NativeArray.o $(B)/DynLoad.o $(B)/Threads.o $(B)/CompiledFn.o $(B)/Socket.o $(S)/analyze.inc $(S)/exec.inc $(S)/rational.inc $(S)/flat.inc $(S)/repl.inc $(S)/tasks.inc $(S)/sorted.inc $(S)/hosttable.inc

# The reference BLAS (src/f/blas/PROVENANCE.md), F77 fixed form, as a
# PACKAGE beside its Clojure in packages/blas, opened at run time; the
# base binary links no BLAS.
# Its shims and manifest are GENERATED from the F77 sources by scripts/bind-fortran.
blas-sources = $(S)/blas/dgemm.f $(S)/blas/lsame.f $(S)/blas/xerbla.f
packages/blas/blas_bind.f90: $(blas-sources) scripts/bind-fortran
	scripts/bind-fortran --package blas --out $@ $(blas-sources)
packages/blas/libblas.$(SOEXT): $(blas-sources) packages/blas/blas_bind.f90 | $(B) $(FCSTAMP)
	mkdir -p $(PKGMOD)
	$(FC) $(filter-out -frecursive -J$(B),$(FCFLAGS)) -J$(PKGMOD) -shared -fPIC -o $@ $^

# ChemSol (src/f/chemsol/PROVENANCE.md), unmodified, as a PACKAGE: a
# shared library beside its Clojure in packages/chemsol, opened at run
# time (src/f/DynLoad.f90), never linked into clotran-bin. chemsol.f90
# is built without -frecursive: dg_ld declares 400 MB of fixed-size
# locals, which the original build keeps in static storage and
# -frecursive would put on an 8 MB stack -- SIGILL on the first call.
PKGMOD = $(B)/pkgmod
packages/chemsol/libchemsol.$(SOEXT): $(S)/chemsol/push_array.f90 $(S)/chemsol/chemsol.f90 packages/chemsol/chemsol_shims.f90 | $(B) $(FCSTAMP)
	mkdir -p $(PKGMOD)
	$(FC) $(filter-out -frecursive -J$(B),$(FCFLAGS)) -J$(PKGMOD) -shared -fPIC -o $@ $^
packages: packages/chemsol/libchemsol.$(SOEXT) packages/blas/libblas.$(SOEXT)

data-objects = $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(B)/Assoc.o \
	$(B)/PersistentList.o $(B)/PersistentVector.o $(B)/NativeArray.o $(B)/Printer.o
reader-objects = $(B)/LispReader.o $(B)/Regex.o $(B)/regex_shim.o
$(B)/Regex.o: $(B)/Threads.o
# The table a compiled namespace registers its procedures in. No
# dependency of its own, and both Eval (to call) and ClotranABI (to
# register) need it, so it sits below them.
compiled-objects = $(B)/CompiledFn.o
$(B)/DynLoad.o: $(B)/GC.o
$(B)/CompiledFn.o: $(B)/GC.o $(B)/PersistentVector.o $(B)/DynLoad.o
# TCP sockets: the shim holds what differs between POSIX and Winsock
socket-objects = $(B)/Socket.o $(B)/socket_shim.o $(B)/fs_shim.o
$(B)/Socket.o: $(B)/GC.o
eval-objects = $(data-objects) $(B)/Env.o $(B)/Namespace.o $(reader-objects) $(B)/DynLoad.o $(compiled-objects) $(socket-objects) $(B)/Eval.o \
	$(B)/ClotranABI.o
LINK_ICU = $(ICU_LIBS) $(LIBCXX) -lpthread

# The build's identity, for main.f90: a stamp an image is tied to, and
# what the REPL's banner says -- VERSION, the pins the deriver recorded
# (test/clj/derived/PROVENANCE.md), and the machine.
clotran-bin: $(eval-objects) $(S)/main.f90 $(ICU_LIBS) VERSION test/clj/derived/PROVENANCE.md
	printf 'character(len=*), parameter :: BUILD_STAMP = "%s"\n' "$$(date +%s)-$$$$" > $(B)/stamp.inc
	printf 'character(len=*), parameter :: CLOTRAN_VERSION = "%s"\n' "$$(cat VERSION)" >> $(B)/stamp.inc
	printf 'character(len=*), parameter :: CLOJURE_PIN = "%s"\n' "$$(sed -n 's/^clojure //p' test/clj/derived/PROVENANCE.md)" >> $(B)/stamp.inc
	printf 'character(len=*), parameter :: CLJS_PIN = "%s"\n' "$$(sed -n 's/^clojurescript //p' test/clj/derived/PROVENANCE.md)" >> $(B)/stamp.inc
	printf 'character(len=*), parameter :: BUILD_ARCH = "%s"\n' "$$(uname -m)-$$(uname -s | tr A-Z a-z)" >> $(B)/stamp.inc
	$(FC) $(FCFLAGS) -c $(S)/main.f90 -o $(B)/main.o
	$(FC) $(LDFLAGS) $(EXPORTDYN) -o $@ $(eval-objects) $(B)/main.o $(LINK_ICU) $(LIBDL)

# Test binaries: each links exactly the modules it exercises, so a
# module's test cannot pass by accident through something above it.
$(BT)/bigint_test: $(B)/BigInt.o $(T)/bigint_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/bigint_test.f90 -o $(BT)/bigint_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(BT)/bigint_test.o
$(BT)/bigdec_test: $(B)/BigInt.o $(B)/BigDec.o $(T)/bigdec_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/bigdec_test.f90 -o $(BT)/bigdec_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(BT)/bigdec_test.o
$(BT)/native_array_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/NativeArray.o $(T)/native_array_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/native_array_test.f90 -o $(BT)/native_array_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/NativeArray.o $(BT)/native_array_test.o
$(BT)/gc_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(T)/gc_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/gc_test.f90 -o $(BT)/gc_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(BT)/gc_test.o
$(BT)/persistent_vector_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentVector.o $(T)/persistent_vector_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/persistent_vector_test.f90 -o $(BT)/persistent_vector_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentVector.o $(BT)/persistent_vector_test.o
$(BT)/persistent_list_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentList.o $(T)/persistent_list_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/persistent_list_test.f90 -o $(BT)/persistent_list_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentList.o $(BT)/persistent_list_test.o
$(BT)/persistent_array_map_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(T)/persistent_array_map_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/persistent_array_map_test.f90 -o $(BT)/persistent_array_map_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(BT)/persistent_array_map_test.o
$(BT)/persistent_hash_map_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(T)/persistent_hash_map_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/persistent_hash_map_test.f90 -o $(BT)/persistent_hash_map_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(BT)/persistent_hash_map_test.o
$(BT)/env_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/Env.o $(T)/env_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/env_test.f90 -o $(BT)/env_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/Env.o $(BT)/env_test.o
$(BT)/assoc_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(B)/Assoc.o $(T)/assoc_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/assoc_test.f90 -o $(BT)/assoc_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(B)/Assoc.o $(BT)/assoc_test.o
$(BT)/printer_test: $(data-objects) $(T)/printer_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/printer_test.f90 -o $(BT)/printer_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(data-objects) $(BT)/printer_test.o
$(BT)/reader_test: $(data-objects) $(reader-objects) $(T)/reader_test.f90 $(ICU_LIBS) | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/reader_test.f90 -o $(BT)/reader_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(data-objects) $(reader-objects) $(BT)/reader_test.o $(LINK_ICU)
$(BT)/eval_test: $(eval-objects) $(T)/eval_test.f90 $(ICU_LIBS) | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/eval_test.f90 -o $(BT)/eval_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(eval-objects) $(BT)/eval_test.o $(LINK_ICU)

# threads_test: the Threads module on its own -- OS threads for tasks
# (PLAN.md step 11, stage 1), pthreads through iso_c_binding.
$(BT)/threads_test: $(B)/Threads.o $(T)/threads_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/threads_test.f90 -o $(BT)/threads_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/Threads.o $(BT)/threads_test.o -lpthread

# gc_mt_test: the collector with several threads allocating at once
# (PLAN.md step 14c), torture on, every allocation stopping the others.
$(BT)/gc_mt_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(T)/gc_mt_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/gc_mt_test.f90 -o $(BT)/gc_mt_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/seqlock.o $(B)/GC.o $(BT)/gc_mt_test.o -lpthread

# abi_test declares every entry point itself and uses no clotran
# module, which is the point of it -- so it compiles with -I nowhere
# near build/. It still LINKS the objects, the way a generated
# namespace linked into a binary will.
$(BT)/abi_test: $(eval-objects) $(T)/abi_test.f90 $(ICU_LIBS) | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/abi_test.f90 -o $(BT)/abi_test.o && $(FC) $(TESTLDFLAGS) -o $@ $(eval-objects) $(BT)/abi_test.o $(LINK_ICU)

# An EMBEDDER (examples/embed): a Fortran program that owns main and
# its time loop, boots the runtime through the C surface, loads core.clj
# and runs its control strategy from Clojure on its own grid -- one
# array, both sides. Linked from the same objects as clotran-bin.
examples/embed/heat: $(eval-objects) examples/embed/heat.f90 $(ICU_LIBS) | $(FCSTAMP)
	$(FC) $(FCFLAGS) -c examples/embed/heat.f90 -o $(B)/embed_heat.o && $(FC) $(TESTLDFLAGS) -o $@ $(eval-objects) $(B)/embed_heat.o $(LINK_ICU)
embed: examples/embed/heat

# The gate. Three layers (CLAUDE.md): the host tests, the host-level
# checks that need core.clj loaded, and the differential oracle against
# real Clojure. clotran is built here so main.f90 and its link line are
# inside the gate under both compilers.
# The package the language test loads through the door (DynLoad.f90):
# a shared library with a manifest and shims, built like any package.
$(B)/libtestpkg.$(SOEXT): $(T)/testpkg.f90 | $(B) $(FCSTAMP)
	$(FC) $(FCFLAGS) -shared -fPIC -o $@ $<

# and the same library bound by the GENERATOR: scripts/bind-fortran writes
# the shims and manifest for test/f/samplelib.f90, a library written with
# no thought of clotran, and the language test calls them through the door.
$(B)/samplelib_shims.f90: $(T)/samplelib.f90 scripts/bind-fortran | $(B)
	scripts/bind-fortran --package samplelib --out $@ $<
$(B)/libsamplelib.$(SOEXT): $(T)/samplelib.f90 $(B)/samplelib_shims.f90 | $(B) $(FCSTAMP)
	mkdir -p $(PKGMOD)
	$(FC) $(filter-out -frecursive -J$(B),$(FCFLAGS)) -J$(PKGMOD) -shared -fPIC -o $@ $^

# The checks are separate targets so `make -j test` runs them side by
# side; each writes only its own files, and each grep reads a FILE the
# run wrote rather than a pipe -- grep -q leaves at its first match and
# a clotran still writing then dies of EPIPE with "fatal Fortran runtime
# error" in the log (the library runner and
# pure-check under build/, the autocompile pair in build/autocache, one
# after the other within its target). Plain `make test` runs them in
# order, as before.
# The fuzz checks draw from SEED, a new one each make (PLAN 29: the
# same seed every run tests the same cases every run). A failure prints
# the seed; `make test SEED=n` runs those cases again. crosscheck hands
# one seed to both halves, so the two compilers judge the same cases.
ifndef SEED
SEED := $(shell od -An -N4 -tu4 /dev/urandom | tr -d ' \n')
endif
export SEED

TEST_DEPS = $(test-bins) clotran-bin $(B)/core.image $(B)/libtestpkg.$(SOEXT) $(B)/libsamplelib.$(SOEXT) packages examples/embed/heat
# THE GATE'S CHECKS, in three groups (James, 2026-10-03: the gate had
# grown to 15 minutes, every fuzzer run under both compilers):
#   FIXED   the same every run -- unit, language, oracle, every regression
#           a fuzzer ever found -- under BOTH compilers, every commit
#   FUZZ    the language core's fuzzers at a fresh seed, under gfortran
#           only: a random case finds the same bug under either
#   NIGHTLY the slow and specialised fuzzers, make test-nightly; and
#           make fuzz-all, every fuzzer at full size, for a release
TEST_FIXED = check-unit check-embed check-embed-repl check-path check-install check-new check-program check-language check-tree check-banner check-torture check-threads \
	check-autocompile check-break check-libraries check-oracle check-oracle-gc check-pure check-static check-costs check-seed check-fuzz-regressions
TEST_FUZZ = check-fuzz check-fuzz-num check-fuzz-str check-fuzz-coll check-fuzz-macro check-fuzz-fn check-fuzz-read check-fuzz-print
TEST_NIGHTLY = check-fuzz-shrink check-frames check-fuzz-spec check-fuzz-threads check-fuzz-pure check-fuzz-gc check-fuzz-net check-fuzz-deps check-fuzz-bind
ifeq ($(notdir $(FC)),gfortran)
TEST_CHECKS = $(TEST_FIXED) $(TEST_FUZZ)
else
TEST_CHECKS = $(TEST_FIXED)
endif
.PHONY: test test-nightly $(TEST_FIXED) $(TEST_FUZZ) $(TEST_NIGHTLY)
test: $(TEST_CHECKS)
test-nightly: $(TEST_FIXED) $(TEST_FUZZ) $(TEST_NIGHTLY)
$(TEST_FIXED) $(TEST_FUZZ) $(TEST_NIGHTLY): $(TEST_DEPS)
check-unit:
	for t in $(unit-tests); do echo "--- $$t ---"; $(BT)/$$t || exit 1; done
check-embed:
	@echo "--- a Fortran solver with clotran embedded, its strategy in Clojure on its own grid (examples/embed) ---"
	examples/embed/heat | grep -v "^note:" | diff - examples/embed/expected.txt
check-path:
	@echo "--- CLOTRAN_PATH: source roots a package manager adds (PACKAGES.md) ---"
	@mkdir -p $(B)/cp1/cpt $(B)/cp2/cpt
	@echo "(ns cpt.one) (def v :one)" > $(B)/cp1/cpt/one.cljf
	@echo "(ns cpt.two) (def v :two)" > $(B)/cp2/cpt/two.cljc
	@echo "(require (quote cpt.one) (quote cpt.two)) (println :path-says cpt.one/v cpt.two/v)" > $(B)/cpt.clj
	CLOTRAN_PATH=$(B)/cp1:$(B)/cp2 ./clotran-bin src/clj/clojure/core.clj $(B)/cpt.clj </dev/null 2>&1 | grep -q ":path-says :one :two"
check-install:
	@echo "--- make install into a scratch prefix, run from outside the tree, make uninstall ---"
	@rm -rf $(B)/inst $(B)/outside && mkdir -p $(B)/outside
	@$(MAKE) -s install PREFIX=$(CURDIR)/$(B)/inst >/dev/null
	@echo "(require (quote [clojure.set :as set])) (println :installed-says (set/union #{1} #{2}) (clojure-version))" > $(B)/outside/t.cljf
	cd $(B)/outside && $(CURDIR)/$(B)/inst/bin/clotran t.cljf </dev/null 2>&1 | grep -q ":installed-says #{1 2}"
	@$(MAKE) -s uninstall PREFIX=$(CURDIR)/$(B)/inst
	@test -z "$$(find $(B)/inst -type f)"
check-new:
	@echo "--- clotran new: a project whose own test passes, and a name refused ---"
	@rm -rf $(B)/new && mkdir -p $(B)/new
	cd $(B)/new && $(CURDIR)/clotran new my-app >/dev/null
	cd $(B)/new/my-app && CLOTRAN_PATH=src:test $(CURDIR)/clotran test </dev/null 2>&1 | grep -q "^0 failures, 0 errors"
	cd $(B)/new && ! $(CURDIR)/clotran new Hello 2>/dev/null
check-program: $(B)/core.image
	@echo "--- a program: a script's *command-line-args*, -m NS's -main, status 1 on an error, clotran test's status (PLAN step 22) ---"
	@rm -rf $(B)/program && mkdir -p $(B)/program/src/p $(B)/program/test/p
	@printf '(prn *command-line-args*)\n' > $(B)/program/s.cljf
	@printf '(ns p.core (:gen-class))\n(defn -main [& args] (prn :main args) (when (= "boom" (first args)) (/ 1 0)) (when (= "how" (first args)) (println (pr-str p.core/-main))))\n' > $(B)/program/src/p/core.cljf
	@printf '(ns p.core-test (:require [clojure.test :refer [deftest is]]))\n(deftest t (is (= 1 2)))\n' > $(B)/program/test/p/core_test.cljf
	cd $(B)/program && $(CURDIR)/clotran s.cljf a "b c" </dev/null | grep -qx '("a" "b c")'
	cd $(B)/program && $(CURDIR)/clotran s.cljf </dev/null | grep -qx 'nil'
	cd $(B)/program && CLOTRAN_PATH=src $(CURDIR)/clotran -m p.core x </dev/null | grep -qx ':main ("x")'
	cd $(B)/program && ! CLOTRAN_PATH=src $(CURDIR)/clotran -m p.core boom </dev/null >/dev/null 2>err.txt && grep -q 'Divide by zero' err.txt
	cd $(B)/program && ! CLOTRAN_PATH=src:test $(CURDIR)/clotran test </dev/null >/dev/null 2>&1
	@echo "--- clotran build: one executable that runs where there are no sources (PLAN step 22) ---"
	cd $(B)/program && CLOTRAN_CACHE=$(CURDIR)/$(B)/program/cache CLOTRAN_PATH=src $(CURDIR)/clotran build -m p.core -o prog >/dev/null
	mkdir -p $(B)/program/elsewhere && mv $(B)/program/prog $(B)/program/elsewhere/
	cd $(B)/program/elsewhere && env -i TMPDIR=$(CURDIR)/$(B)/program ./prog y </dev/null | grep -qx ':main ("y")'
	cd $(B)/program/elsewhere && ! env -i TMPDIR=$(CURDIR)/$(B)/program ./prog boom </dev/null >/dev/null 2>&1
	cd $(B)/program/elsewhere && env -i TMPDIR=$(CURDIR)/$(B)/program ./prog how </dev/null | grep -q '#<compiled p.core/-main>'
	@rm -f $(B)/program/elsewhere/prog
check-embed-repl:
	@echo "--- a REPL into the running solver: read its grid, write it, stop it (PLAN step 21) ---"
	scripts/embed-repl-check
check-language:
	@echo "--- language_test (with core.clj, loaded from source: the one run without the image) ---"
	CLOTRAN_IMAGE=0 ./clotran-bin src/clj/clojure/core.clj test/clj/language_test.clj </dev/null > $(B)/language_test.out 2>&1; \
	  grep -q "^LANGUAGE TESTS PASSED" $(B)/language_test.out || { grep -E "FAIL|FAILED" $(B)/language_test.out | head -20; exit 1; }
check-tree:
	@echo "--- language_test with every body a tree (CLOTRAN_FLAT=0): the walker the flat form stands beside ---"
	CLOTRAN_FLAT=0 ./clotran-bin src/clj/clojure/core.clj test/clj/language_test.clj </dev/null > $(B)/language_tree.out 2>&1; \
	  grep -q "^LANGUAGE TESTS PASSED" $(B)/language_tree.out || { grep -E "FAIL|FAILED" $(B)/language_tree.out | head -20; exit 1; }
check-banner:
	@echo "--- the REPL's banner is for a terminal only: a pipe must never see it ---"
	! (printf '(+ 1 2)\n' | ./clotran-bin src/clj/clojure/core.clj 2>&1 | grep -q 'based on Clojure')
check-torture:
	@echo "--- a few forms with a collection at every object allocation: the read-string shape included ---"
	CLOTRAN_GC_EVERY=1 ./clotran-bin src/clj/clojure/core.clj test/clj/torture_check.clj </dev/null > $(B)/torture_check.out 2>&1; grep -q "^TORTURE CHECK PASSED" $(B)/torture_check.out
check-threads:
	@echo "--- eight futures allocating at once, the heap checked at every young collection (step 14d) ---"
	CLOTRAN_GC_VERIFY=1 ./clotran-bin src/clj/clojure/core.clj test/clj/threads_heap.clj </dev/null > $(B)/threads_heap.out 2>&1; \
	  grep -q "^THREADS HEAP PASSED" $(B)/threads_heap.out
check-autocompile:
	@echo "--- a loaded namespace built into a cache and installed from it (clotran.loader) ---"
	rm -rf $(B)/autocache
	AUTOCOMPILE_STEP=build CLOTRAN_AUTOCOMPILE=use CLOTRAN_CACHE=$(B)/autocache \
	  ./clotran-bin src/clj/clojure/core.clj test/clj/autocompile_test.clj </dev/null > $(B)/autocompile1.out 2>&1; grep -q "^AUTOCOMPILE PASSED" $(B)/autocompile1.out
	AUTOCOMPILE_STEP=cached CLOTRAN_AUTOCOMPILE=use CLOTRAN_CACHE=$(B)/autocache \
	  ./clotran-bin src/clj/clojure/core.clj test/clj/autocompile_test.clj </dev/null > $(B)/autocompile2.out 2>&1; grep -q "^AUTOCOMPILE PASSED" $(B)/autocompile2.out
	@echo "--- the same file by another path finds the same build ---"
	AUTOCOMPILE_SRC=./test/clj/../clj/autocompile_demo.cljf AUTOCOMPILE_STEP=cached CLOTRAN_AUTOCOMPILE=use CLOTRAN_CACHE=$(B)/autocache \
	  ./clotran-bin src/clj/clojure/core.clj test/clj/autocompile_test.clj </dev/null > $(B)/autocompile2b.out 2>&1; grep -q "^AUTOCOMPILE PASSED" $(B)/autocompile2b.out
	@echo "--- compile-now while the load's own background build of the file is running: it waits for that build ---"
	rm -rf $(B)/autocache
	AUTOCOMPILE_STEP=build CLOTRAN_AUTOCOMPILE=1 CLOTRAN_CACHE=$(B)/autocache \
	  ./clotran-bin src/clj/clojure/core.clj test/clj/autocompile_test.clj </dev/null > $(B)/autocompile3.out 2>&1; grep -q "^AUTOCOMPILE PASSED" $(B)/autocompile3.out
check-break:
	@echo "--- a break pauses into a nested REPL, and clotran-resume answers it ---"
	printf '((fn [x] (clotran-break)) 1)\n(clotran-resume {:continue (* 42 (get (:env (first (:frames (clotran-last-break)))) (quote x)))})\n' \
	  | ./clotran-bin src/clj/clojure/core.clj > $(B)/break_check.out 2>&1; grep -q '42$$' $(B)/break_check.out
check-libraries:
	@echo "--- the portable libraries, on Clojure's OWN tests, verbatim ---"
	scripts/run-library-tests
check-oracle:
	@echo "--- oracle (the same forms through clj and clotran) ---"
	scripts/oracle
# One half of the crosscheck is enough: a value the collector frees
# early is the runtime's mistake, not a compiler's, and this is the
# gate's longest check under flang.
check-oracle-gc:
ifeq ($(notdir $(FC)),gfortran)
	@echo "--- the oracle's script collecting every 97 allocations, against itself (PLAN step 20) ---"
	ORACLE_GC=97 scripts/oracle
else
	@echo "--- oracle-gc: run in the gfortran half ---"
endif
check-pure:
	@echo "--- pure Fortran (tier A through gfortran and flang, against clj) ---"
	scripts/pure-check
check-seed:
	@echo "--- the fuzz checks' seed: $(SEED) (make test SEED=$(SEED) runs the same cases) ---"
check-fuzz-regressions:
	@echo "--- every case a fuzzer has found (test/clj/fuzz-regressions.edn), through clj and clotran's flat, tree and compiled modes ---"
	scripts/fuzz -f test/clj/fuzz-regressions.edn > $(B)/fuzz-regressions.out 2>&1; s=$$?; cat $(B)/fuzz-regressions.out; exit $$s
check-fuzz:
	@echo "--- the fuzzer (PLAN 26.9): 300 generated programs and 4 calls of each spec'd function, each through clj and clotran's flat, tree and compiled modes ---"
	scripts/fuzz -n 300 -s $(SEED) --shrink-budget 60 > $(B)/fuzz.out 2>&1 && scripts/fuzz --fns 4 -s $(SEED) >> $(B)/fuzz.out 2>&1; s=$$?; cat $(B)/fuzz.out; exit $$s
check-fuzz-shrink:
	@echo "--- the fuzzer's shrinker (PLAN 31a): a planted bug, found, every case shrunk no larger and still failing, one strictly smaller ---"
	scripts/fuzz -n 150 -s 2 --control-shrink > $(B)/fuzz-shrink.out 2>&1; s=$$?; tail -1 $(B)/fuzz-shrink.out; exit $$s
check-fuzz-macro:
	@echo "--- core macros (PLAN 29): generated destructuring, checked against core.specs, and threading and conditional macros, through clj and every mode ---"
	scripts/fuzz-macro -n 150 -s $(SEED) -o $(B)/fuzz-macro.edn > $(B)/fuzz-macro.out 2>&1; s=$$?; cat $(B)/fuzz-macro.out; exit $$s
check-fuzz-fn:
	@echo "--- typed functions (PLAN 29): generated defns with ^long and ^double parameters, primitive locals and loops, compiled in compiled mode, called with arguments directly and through apply ---"
	scripts/fuzz-fn -n 30 -k 4 -s $(SEED) -o $(B)/fuzz-fn.edn > $(B)/fuzz-fn.out 2>&1; s=$$?; cat $(B)/fuzz-fn.out; exit $$s
check-fuzz-read:
	@echo "--- the reader on malformed text (PLAN 29): generated source, mutated, read by clj and clotran: the value, or the error by class and message ---"
	scripts/fuzz-read -n 400 -s $(SEED) > $(B)/fuzz-read.out 2>&1; s=$$?; cat $(B)/fuzz-read.out; exit $$s
check-fuzz-threads:
	@echo "--- threads (PLAN 29): futures contending on an atom, two refs and an agent; final values and invariants against clj ---"
	scripts/fuzz-threads -n 20 -s $(SEED) -o $(B)/fuzz-threads.edn > $(B)/fuzz-threads.out 2>&1; s=$$?; cat $(B)/fuzz-threads.out; exit $$s
check-fuzz-pure:
	@echo "--- the tier-A compiler (PLAN 29): generated functions as pure Fortran, gfortran and flang, against the interpreter and clj ---"
	scripts/fuzz-pure -n 30 -s $(SEED) > $(B)/fuzz-pure.out 2>&1; s=$$?; cat $(B)/fuzz-pure.out; exit $$s
check-fuzz-gc:
	@echo "--- the collector and the image (PLAN 29): every generator collecting every 3, 17 and 1009 allocations, and from source ---"
	scripts/fuzz-gc -n 10 -s $(SEED) > $(B)/fuzz-gc.out 2>&1; s=$$?; cat $(B)/fuzz-gc.out; exit $$s
check-fuzz-deps:
	@echo "--- the package manager (PLAN 29): generated dependency graphs, local and git, conflicts and jars, through clotran-deps against a model of its rules, and loaded ---"
	scripts/fuzz-deps -n 20 -s $(SEED) > $(B)/fuzz-deps.out 2>&1; s=$$?; cat $(B)/fuzz-deps.out; exit $$s
check-fuzz-bind:
	@echo "--- packages from generated Fortran (PLAN 29): bind-fortran, gfortran and flang, every routine called through the door ---"
	scripts/fuzz-bind -n 12 -s $(SEED) > $(B)/fuzz-bind.out 2>&1; s=$$?; cat $(B)/fuzz-bind.out; exit $$s
check-fuzz-net:
	@echo "--- sockets and the REPL over one (PLAN 29): random payloads echoed, generated forms through io-prepl against clj ---"
	scripts/fuzz-net -n 20 -s $(SEED) > $(B)/fuzz-net.out 2>&1; s=$$?; cat $(B)/fuzz-net.out; exit $$s
check-fuzz-coll:
	@echo "--- the collections (PLAN 29): random operation sequences on every kind, across the size boundaries, through clj and every mode, GC torture too ---"
	scripts/fuzz-coll -n 120 -s $(SEED) -m flat,tree,compiled,torture -o $(B)/fuzz-coll.edn > $(B)/fuzz-coll.out 2>&1; s=$$?; cat $(B)/fuzz-coll.out; exit $$s
check-fuzz-str:
	@echo "--- strings and regex (PLAN 29): generated strings and patterns, case, trim, search, split, replace, re-find/re-seq/re-matches, through clj and every mode, GC torture too ---"
	scripts/fuzz-str -n 300 -s $(SEED) -m flat,tree,compiled,torture -o $(B)/fuzz-str.edn > $(B)/fuzz-str.out 2>&1; s=$$?; cat $(B)/fuzz-str.out; exit $$s
check-fuzz-num:
	@echo "--- the numeric tower (PLAN 29): one operation on generated longs, doubles, ratios, BigInts and BigDecimals, value and class, through clj and every mode, GC torture too ---"
	scripts/fuzz-num -n 300 -s $(SEED) -m flat,tree,compiled,torture -o $(B)/fuzz-num.edn > $(B)/fuzz-num.out 2>&1; s=$$?; cat $(B)/fuzz-num.out; exit $$s
check-fuzz-print:
	@echo "--- the reader and the printer (PLAN 29): generated values read as literals, printed, read back, through clj and every mode, GC torture too ---"
	scripts/fuzz-print -n 60 -s $(SEED) -o $(B)/fuzz-print.edn > $(B)/fuzz-print.out 2>&1; s=$$?; cat $(B)/fuzz-print.out; exit $$s
check-fuzz-spec:
	@echo "--- spec itself (PLAN 29): generated spec forms and values, valid?/conform/unform/explain-data/form, through clj and every mode, GC torture too ---"
	scripts/fuzz-spec -n 20 -k 2 -s $(SEED) -o $(B)/fuzz-spec.edn > $(B)/fuzz-spec.out 2>&1; s=$$?; cat $(B)/fuzz-spec.out; exit $$s
check-frames:
	@echo "--- frames (PLAN 29): names, locals and lines of breaks and traces, generated, against clj and the generator, through a reload and a recompile; compiled breaks wait for the debug build ---"
	scripts/fuzz-frames -n 40 -s $(SEED) --modes flat,tree > $(B)/frames.out 2>&1 && scripts/fuzz-frames -n 40 -s $(SEED) --modes compiled --leaves throw >> $(B)/frames.out 2>&1; s=$$?; cat $(B)/frames.out; exit $$s
check-costs:
	@echo "--- the cost model: objects allocated per element, against test/costs.edn (PLAN step 26) ---"
	scripts/cost-model > $(B)/costs.out 2>&1; s=$$?; cat $(B)/costs.out; exit $$s
check-static:
	@echo "--- state inventory (every module variable classified, PLAN step 14a) ---"
	scripts/state-inventory
	@echo "--- the builtins that may reuse an argument vector (argsafe.inc) are current ---"
	scripts/argsafe --check
	@echo "--- src/clj/clojure and test/clj/clojure are what upstream/derive writes; upstream's class names stay in upstream/ ---"
	upstream/derive --check
	upstream/check-names
	@echo "--- every procedure given roots passes them to what it allocates (PLAN step 20) ---"
	scripts/root-check
	@echo "--- no static string lengths (gfortran slen: shared by every thread, step 14f) ---"
	scripts/no-static-slen clotran-bin packages/chemsol/libchemsol.$(SOEXT) packages/blas/libblas.$(SOEXT)

# What runs before every commit. Ends on the default compiler so the
# tree is left with the build you actually use.
# The gate runs in a PRIVATE COPY of the sources (XC_DIR), never in this
# tree: it cleans and builds twice, and in the working tree that deleted
# the clotran-bin a REPL was about to start and collided with any `make`
# run meanwhile -- one compiler's .mod files under the other's build,
# twice in one day. rsync copies what changed since the last gate, and
# the verdict is the same EXIT line.
XC_DIR ?= $(or $(TMPDIR),/tmp)/clotran-crosscheck
#
# The two halves run AT ONCE, each in a copy of its own (XC_DIR/flang,
# XC_DIR/gfortran), each building and testing with -j; each half's
# output is its own log, printed whole once both have finished, and the
# gate fails if either did.
XC_JOBS ?= 4
XC_SYNC = rsync -a --delete --exclude .git --exclude /build --exclude /clotran-bin \
	  --exclude /clotran-bin.dSYM --exclude /examples/embed/heat ./
crosscheck:
	mkdir -p $(XC_DIR)/flang $(XC_DIR)/gfortran
	$(XC_SYNC) $(XC_DIR)/flang/
	$(XC_SYNC) $(XC_DIR)/gfortran/
	echo "crosscheck: fuzz seed $(SEED) (make crosscheck SEED=$(SEED) repeats it)"; \
	( $(MAKE) -C $(XC_DIR)/flang crosscheck-here FC=flang SEED=$(SEED) > $(XC_DIR)/flang.log 2>&1; echo $$? > $(XC_DIR)/flang.rc ) & \
	( $(MAKE) -C $(XC_DIR)/gfortran crosscheck-here FC=gfortran SEED=$(SEED) > $(XC_DIR)/gfortran.log 2>&1; echo $$? > $(XC_DIR)/gfortran.rc ) & \
	wait; \
	echo "======== flang ========"; cat $(XC_DIR)/flang.log; \
	echo "======== gfortran ========"; cat $(XC_DIR)/gfortran.log; \
	echo "flang: exit $$(cat $(XC_DIR)/flang.rc), gfortran: exit $$(cat $(XC_DIR)/gfortran.rc)"; \
	[ "$$(cat $(XC_DIR)/flang.rc)" = 0 ] && [ "$$(cat $(XC_DIR)/gfortran.rc)" = 0 ]
crosscheck-here:
	$(MAKE) clean && $(MAKE) -j$(XC_JOBS) FC=$(FC) test

# THE IMAGE (main.f90, image_save): the heap after core.clj and spec
# have loaded, written once and read back by every start in place of
# loading them -- 1.4 s a process. Tied to this build of the binary and
# to the sources it holds; CLOTRAN_IMAGE=0 loads from source instead.
$(B)/core.image: clotran-bin $(wildcard src/clj/*.clj) $(wildcard src/clj/clojure/*.clj) $(wildcard src/clj/clojure/*/*.clj) $(wildcard src/clj/clotran/*.cljf)
	CLOTRAN_IMAGE=0 CLOTRAN_IMAGE_SAVE=$@ ./clotran-bin src/clj/clojure/core.clj </dev/null
image: $(B)/core.image

# INSTALL. clotran and nothing else, under $(PREFIX)/lib/clotran in the
# repository's own layout -- the binary finds its home, image and sources
# from its own path (main.f90 home_dir): the binary, the heap image
# (rebuilt THERE, so it matches the sources beside it), src/clj -- the
# vendored Clojure and clotran's own libraries, which load on first use
# -- and the launcher; and $(PREFIX)/bin/clotran, which runs the launcher.
# Packages (blas, chemsol, anything else) are not part of it: a project
# names them in its deps.edn (PACKAGES.md).
#
#   make install                     ~/.local (bin/clotran on PATH on most Linux)
#   sudo make install PREFIX=/usr/local
#   make uninstall                   the same PREFIX
#
# On Windows (MSYS2 make) PREFIX defaults to %LOCALAPPDATA%\Programs\clotran;
# the Windows build itself is untested until CI runs it (PLAN step 21).
# Built for this machine's architecture only (uname -m), not universal.
ifneq ($(filter MINGW% MSYS% CYGWIN%,$(UNAME_S)),)
PREFIX ?= $(subst \,/,$(LOCALAPPDATA))/Programs/clotran
else
PREFIX ?= $(HOME)/.local
endif
CLOTRAN_LIB = $(PREFIX)/lib/clotran
CLOTRAN_BIN = $(PREFIX)/bin

# the Fortran compiler this build uses, by absolute path: `clotran compile`
# falls back to it where gfortran is not on PATH (an Emacs from the Dock)
$(B)/fc: Makefile | $(B)
	command -v $(FC) > $@

install: clotran-bin $(B)/fc
	@echo "--- installing clotran into $(CLOTRAN_LIB), the command into $(CLOTRAN_BIN) ---"
	rm -rf "$(CLOTRAN_LIB).new"
	mkdir -p "$(CLOTRAN_LIB).new/src" "$(CLOTRAN_LIB).new/build" "$(CLOTRAN_BIN)"
	cp clotran-bin clotran "$(CLOTRAN_LIB).new/"
	cp -R src/clj "$(CLOTRAN_LIB).new/src/"
	cp $(B)/fc "$(CLOTRAN_LIB).new/build/fc"
	cd "$(CLOTRAN_LIB).new" && CLOTRAN_IMAGE=0 CLOTRAN_IMAGE_SAVE=build/core.image ./clotran-bin src/clj/clojure/core.clj </dev/null >/dev/null
	rm -rf "$(CLOTRAN_LIB)"
	mv "$(CLOTRAN_LIB).new" "$(CLOTRAN_LIB)"
	printf '#!/bin/sh\n# clotran, installed by make install: the launcher in its home\nexec "%s/clotran" "$$@"\n' "$(CLOTRAN_LIB)" > "$(CLOTRAN_BIN)/clotran"
	chmod +x "$(CLOTRAN_BIN)/clotran"
	@case ":$$PATH:" in *":$(CLOTRAN_BIN):"*) echo "clotran is installed: $(CLOTRAN_BIN)/clotran" ;; \
	  *) echo "clotran is installed: $(CLOTRAN_BIN)/clotran -- $(CLOTRAN_BIN) is not on your PATH; add it" ;; esac

uninstall:
	rm -rf "$(CLOTRAN_LIB)" "$(CLOTRAN_LIB).new" "$(CLOTRAN_BIN)/clotran"

# clojure.core, compiled (clotran compile). Opt-in: generating it takes
# about 100 s, and `clean` -- so the gate -- removes it. When present,
# every load of core.clj installs it (clotran.loader); a clotran whose
# analysis has changed since refuses it with a note until it is rebuilt.
compiled-core: clotran-bin
	mkdir -p $(B)/compiled/clojure
	./clotran compile src/clj/clojure/core.clj $(B)/compiled/clojure/core.$(SOEXT)

clean:
	rm -rf $(B) clotran-bin clotran-bin.dSYM examples/embed/heat examples/embed/heat.dSYM

# --- docs: the north star, generated from markdown ---------------------

# The formal model (PLAN steps 27-28): ACL2 certifies each book, and a
# book that does not certify fails. ACL2 is built on SBCL outside the
# tree (its arithmetic-5 book certified once); ACL2=/path overrides.
# Not in the gate yet: ACL2 is not on every machine the gate runs on.
#
# Each book's certificate is a target after the certificates of the
# books it includes ($(B)/model-deps.mk, read from its include-book
# lines), so only what changed re-proves and `make -j model` certifies
# independent books side by side. ACL2 checks an included book's
# certificate against its source too, so a stale one fails rather than
# passes. `make model-full` re-proves every book from nothing.
ACL2 ?= $(HOME)/jborden/acl2/saved_acl2
.PHONY: model model-full
MODEL_BOOKS = boundary vector string hashseq btree vm vm-loop vm-call vm-call-proof vm-stack vm-stack-proof vm-cost vm-call-opt vm-call-opt-proof lazy-cell vm-closure vm-closure-proof vm-closure-correct vm-closure-stack-proof vm-closure-stack-correct vm-closure-cost vm-closure-rooted jit jit-proof jit-correct jit2 jit2-proof jit2-correct jit3 jit3-proof jit3-correct alloc alloc-old pool vmx vmx-proof vmx-cost vmx2 vmx2-proof vmx2-cost vmi vmi-proof vmg vmg-correct vmic
MODEL_CERTS = $(MODEL_BOOKS:%=model/%.cert)
model: $(MODEL_CERTS)
model/%.cert: model/%.lisp
	@mkdir -p $(B)
	@rm -f $@
	@(cd model && printf '(certify-book "%s")\n(good-bye)\n' $* | "$(ACL2)" > ../$(B)/model-$*.log 2>&1); \
	  test -f $@ || { echo "model: $* did not certify"; grep -E "ACL2 Error|FAILED" $(B)/model-$*.log; exit 1; }; \
	  echo "model: $* certified"
$(B)/model-deps.mk: $(MODEL_BOOKS:%=model/%.lisp)
	@mkdir -p $(B)
	@for b in $(MODEL_BOOKS); do \
	  for d in $$(sed -n 's/^(include-book "\([^"]*\)")$$/\1/p' model/$$b.lisp); do \
	    echo "model/$$b.cert: model/$$d.cert"; \
	  done; \
	done > $@
ifneq ($(wildcard model/vm.lisp),)
-include $(B)/model-deps.mk
endif
model-full:
	rm -f $(MODEL_CERTS)
	$(MAKE) model

# The package door against the model: every scalar value the fuzzer
# makes must cross or be refused exactly as model/boundary.lisp's
# `cross` says, and cross unchanged. Needs ACL2, as `model` does.
.PHONY: fuzz-all
# Every fuzzer, many times make test's sizes, one after another with a
# deadline each, and a scorecard (PLAN step 29). Hours, not minutes.
fuzz-all: clotran-bin $(B)/libsamplelib.$(SOEXT)
	scripts/fuzz-all --size full

# A fuzzer's case to the debugger (PLAN 31a): clj's answer and clotran's,
# and with DEBUG=1 clotran under lldb or gdb stopped at the first throw.
#   make fuzz-repro CASE='(form)' [MODE=tree] [DEBUG=1]
.PHONY: fuzz-repro
fuzz-repro: export CASE := $(CASE)
fuzz-repro: clotran-bin
	scripts/fuzz-repro $(if $(MODE),-m $(MODE)) $(if $(DEBUG),--debug) "$$CASE"

# Clojure's own tests as a speed census: every derived deftest timed
# warm through clj and clotran, the ratio, and what grew since the last
# run (build/bench-suite/). Timing is noisy: a census, never a gate.
.PHONY: bench-suite
bench-suite: clotran-bin
	scripts/bench-suite

.PHONY: fuzz-door
fuzz-door: model clotran-bin $(B)/libsamplelib.$(SOEXT)
	scripts/fuzz-door -n 500 -s 1

# The VM models against their meaning: random programs through the three
# machines (PLAN step 28), and through the closure call (PLAN step 30),
# whose negative control must catch a broken machine. Needs ACL2, as
# `model` does.
.PHONY: fuzz-model
fuzz-model: model
	scripts/fuzz-vm-model -n 300 -s 1
	scripts/fuzz-vm-closure -n 300 -s 1
	scripts/fuzz-vm-closure -n 100 -s 2 -k
	scripts/fuzz-vm-closure -n 100 -s 3 -w
	scripts/fuzz-vm-closure -n 40 -s 5 -j
	scripts/fuzz-vm-closure -n 40 -s 6 -d
	scripts/fuzz-vm-closure -n 40 -s 7 -r
	scripts/fuzz-vmx -n 300 -s 1
	scripts/fuzz-vmx -n 100 -s 2 -x
	scripts/fuzz-vmx2 -n 300 -s 1 -i
	scripts/fuzz-vmx2 -n 100 -s 2 -x
	scripts/fuzz-vmx2 -n 100 -s 2 -xi
	scripts/fuzz-vmx2 -n 100 -s 3 -xc
	scripts/fuzz-alloc -n 300 -s 1
	scripts/fuzz-alloc -n 400 -s 2 -k
	scripts/fuzz-alloc -n 300 -s 4 -m
	$(MAKE) check-vm-gen

# The VM's Fortran is GENERATED from the proved ACL2 (PLAN step 30):
# scripts/acl2-fortran translates model/vmg.lisp, whose guards are
# verified, into src/f/gen/vm_gen.f90. Nobody edits that file; change the
# model, prove it, `make gen-vm`. check-vm-gen says the checked-in file is
# what the model generates, and runs it against ACL2 step for step under
# both compilers, with a negative control.
.PHONY: gen-vm check-vm-gen
gen-vm: model
	scripts/acl2-fortran
check-vm-gen: model | $(B)
	scripts/acl2-fortran -o $(B)/vm_gen.f90
	@cmp -s $(B)/vm_gen.f90 src/f/gen/vm_gen.f90 || { echo "src/f/gen/vm_gen.f90 is not what model/vmg.lisp generates: make gen-vm"; exit 1; }
	scripts/fuzz-vm-gen -n 300 -s 1
	scripts/fuzz-vm-gen -n 100 -s 2 --fc flang
	scripts/fuzz-vm-gen -n 100 -s 2 -x
# pandoc writes HTML; a headless Chrome or Chromium prints it to PDF. No
# LaTeX. CHROME=/path/to/it overrides the browser found here.
CHROME ?= $(shell for c in "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" google-chrome chromium chromium-browser chrome; do \
  command -v "$$c" >/dev/null 2>&1 && { echo "$$c"; break; }; done)
.PHONY: docs
docs: docs/whitepaper.pdf docs/pitch-deck.pdf
docs/%.html: docs/%.md docs/deck.css docs/paper.css
	pandoc -s --section-divs -t html5 --css $(if $(findstring deck,$<),deck.css,paper.css) $< -o $@
docs/whitepaper.pdf: docs/whitepaper.html
	"$(CHROME)" --headless=new --disable-gpu --no-pdf-header-footer --print-to-pdf=$(abspath $@) $(abspath $<) 2>/dev/null
docs/pitch-deck.pdf: docs/deck.html
	"$(CHROME)" --headless=new --disable-gpu --no-pdf-header-footer --print-to-pdf=$(abspath $@) $(abspath $<) 2>/dev/null
