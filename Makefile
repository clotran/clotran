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
FCFLAGS = -g -O2 -I$(B) -Isrc/f -J$(B) $(FCFLAGS_$(notdir $(FC)))
LDFLAGS = $(FCFLAGS_$(notdir $(FC)))

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
FCFLAGS_gfortran = -frecursive -flto
FCFLAGS_flang = -flto

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

$(B)/regex_shim.o: src/c/regex_shim.c src/c/regex_shim.h | $(B) $(FCSTAMP)
	$(CC) -c $(ICU_INC) $< -o $@

# --- the host ----------------------------------------------------------

S = src/f
T = test/f
BT = $(B)/test

unit-tests = gc_test persistent_vector_test persistent_list_test persistent_array_map_test \
	persistent_hash_map_test env_test assoc_test printer_test reader_test eval_test bigint_test \
	bigdec_test abi_test native_array_test threads_test
test-bins = $(addprefix $(BT)/,$(unit-tests))

.PHONY: all test crosscheck clean compiled-core
all: clotran-bin $(test-bins)

$(B) $(BT):
	mkdir -p $@

# The build directory belongs to ONE compiler: .mod files are not
# portable between them, and a crosscheck interrupted between its two
# halves left flang's behind for gfortran to choke on ("not a GNU
# Fortran module file"). The stamp names the owner; building with the
# other compiler empties the directory first. Every object and test
# binary depends on it, order-only, so nothing is compiled against a
# module the other compiler wrote.
FCSTAMP = $(B)/.built-with-$(FCNAME)
$(FCSTAMP): | $(B)
	rm -rf $(B)/*.o $(B)/*.mod $(B)/.built-with-* $(BT)
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
$(B)/Printer.o: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentList.o $(B)/PersistentVector.o $(B)/Assoc.o $(B)/NativeArray.o
# LispReader depends on Regex: #"..." compiles a pattern at READ time,
# matching real Clojure's own regex literal (LispReader compiles
# straight to a Pattern, not to a string). See Regex.f90.
$(B)/LispReader.o: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentList.o $(B)/PersistentVector.o $(B)/Assoc.o $(B)/Regex.o
# The C-callable runtime surface. Linked into clotran-bin so that a
# compiled namespace -- loaded through the door, or linked in -- and an
# embedder both find the same symbols. It is the LAST module: it sits
# on top of Eval, nothing sits on it.
$(B)/ClotranABI.o: $(B)/GC.o $(B)/PersistentVector.o $(B)/Namespace.o $(B)/CompiledFn.o $(B)/NativeArray.o $(B)/Eval.o

$(B)/Eval.o: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentList.o $(B)/PersistentVector.o $(B)/Assoc.o $(B)/Env.o \
	$(B)/Namespace.o $(B)/Printer.o $(B)/Regex.o $(B)/NativeArray.o $(B)/DynLoad.o $(B)/Threads.o $(B)/CompiledFn.o $(S)/analyze.inc $(S)/exec.inc $(S)/repl.inc $(S)/tasks.inc $(S)/sorted.inc $(S)/hosttable.inc

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

data-objects = $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(B)/Assoc.o \
	$(B)/PersistentList.o $(B)/PersistentVector.o $(B)/NativeArray.o $(B)/Printer.o
reader-objects = $(B)/LispReader.o $(B)/Regex.o $(B)/regex_shim.o
# The table a compiled namespace registers its procedures in. No
# dependency of its own, and both Eval (to call) and ClotranABI (to
# register) need it, so it sits below them.
compiled-objects = $(B)/CompiledFn.o
$(B)/CompiledFn.o: $(B)/GC.o $(B)/PersistentVector.o
eval-objects = $(data-objects) $(B)/Env.o $(B)/Namespace.o $(reader-objects) $(B)/DynLoad.o $(compiled-objects) $(B)/Eval.o \
	$(B)/ClotranABI.o
LINK_ICU = $(ICU_LIBS) $(LIBCXX) -lpthread

clotran-bin: $(eval-objects) $(S)/main.f90 $(ICU_LIBS)
	$(FC) $(FCFLAGS) -c $(S)/main.f90 -o $(B)/main.o
	$(FC) $(LDFLAGS) $(EXPORTDYN) -o $@ $(eval-objects) $(B)/main.o $(LINK_ICU) $(LIBDL)

# Test binaries: each links exactly the modules it exercises, so a
# module's test cannot pass by accident through something above it.
$(BT)/bigint_test: $(B)/BigInt.o $(T)/bigint_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/bigint_test.f90 -o $(BT)/bigint_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(BT)/bigint_test.o
$(BT)/bigdec_test: $(B)/BigInt.o $(B)/BigDec.o $(T)/bigdec_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/bigdec_test.f90 -o $(BT)/bigdec_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(BT)/bigdec_test.o
$(BT)/native_array_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/NativeArray.o $(T)/native_array_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/native_array_test.f90 -o $(BT)/native_array_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/NativeArray.o $(BT)/native_array_test.o
$(BT)/gc_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(T)/gc_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/gc_test.f90 -o $(BT)/gc_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(BT)/gc_test.o
$(BT)/persistent_vector_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentVector.o $(T)/persistent_vector_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/persistent_vector_test.f90 -o $(BT)/persistent_vector_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentVector.o $(BT)/persistent_vector_test.o
$(BT)/persistent_list_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentList.o $(T)/persistent_list_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/persistent_list_test.f90 -o $(BT)/persistent_list_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentList.o $(BT)/persistent_list_test.o
$(BT)/persistent_array_map_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(T)/persistent_array_map_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/persistent_array_map_test.f90 -o $(BT)/persistent_array_map_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(BT)/persistent_array_map_test.o
$(BT)/persistent_hash_map_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(T)/persistent_hash_map_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/persistent_hash_map_test.f90 -o $(BT)/persistent_hash_map_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(BT)/persistent_hash_map_test.o
$(BT)/env_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/Env.o $(T)/env_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/env_test.f90 -o $(BT)/env_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/Env.o $(BT)/env_test.o
$(BT)/assoc_test: $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(B)/Assoc.o $(T)/assoc_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/assoc_test.f90 -o $(BT)/assoc_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/BigInt.o $(B)/BigDec.o $(B)/Threads.o $(B)/GC.o $(B)/PersistentArrayMap.o $(B)/PersistentHashMap.o $(B)/Assoc.o $(BT)/assoc_test.o
$(BT)/printer_test: $(data-objects) $(T)/printer_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/printer_test.f90 -o $(BT)/printer_test.o && $(FC) $(LDFLAGS) -o $@ $(data-objects) $(BT)/printer_test.o
$(BT)/reader_test: $(data-objects) $(reader-objects) $(T)/reader_test.f90 $(ICU_LIBS) | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/reader_test.f90 -o $(BT)/reader_test.o && $(FC) $(LDFLAGS) -o $@ $(data-objects) $(reader-objects) $(BT)/reader_test.o $(LINK_ICU)
$(BT)/eval_test: $(eval-objects) $(T)/eval_test.f90 $(ICU_LIBS) | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/eval_test.f90 -o $(BT)/eval_test.o && $(FC) $(LDFLAGS) -o $@ $(eval-objects) $(BT)/eval_test.o $(LINK_ICU)

# threads_test: the Threads module on its own -- OS threads for tasks
# (PLAN.md step 11, stage 1), pthreads through iso_c_binding.
$(BT)/threads_test: $(B)/Threads.o $(T)/threads_test.f90 | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/threads_test.f90 -o $(BT)/threads_test.o && $(FC) $(LDFLAGS) -o $@ $(B)/Threads.o $(BT)/threads_test.o -lpthread

# abi_test declares every entry point itself and uses no clotran
# module, which is the point of it -- so it compiles with -I nowhere
# near build/. It still LINKS the objects, the way a generated
# namespace linked into a binary will.
$(BT)/abi_test: $(eval-objects) $(T)/abi_test.f90 $(ICU_LIBS) | $(BT) $(FCSTAMP)
	$(FC) $(FCFLAGS) -c $(T)/abi_test.f90 -o $(BT)/abi_test.o && $(FC) $(LDFLAGS) -o $@ $(eval-objects) $(BT)/abi_test.o $(LINK_ICU)

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

test: $(test-bins) clotran-bin $(B)/libtestpkg.$(SOEXT) $(B)/libsamplelib.$(SOEXT) packages
	for t in $(unit-tests); do echo "--- $$t ---"; $(BT)/$$t || exit 1; done
	@echo "--- language_test (with core.clj) ---"
	./clotran-bin src/clj/clojure/core.clj test/clj/language_test.clj </dev/null \
	  | tee /dev/stderr | grep -q "^LANGUAGE TESTS PASSED"
	@echo "--- a break pauses into a nested REPL, and clotran-resume answers it ---"
	printf '((fn [x] (clotran-break)) 1)\n(clotran-resume {:continue (* 42 (get (:env (first (:frames (clotran-last-break)))) (quote x)))})\n' \
	  | ./clotran-bin src/clj/clojure/core.clj | grep -q '42$$'
	@echo "--- the portable libraries, on Clojure's OWN tests, verbatim ---"
	scripts/run-library-tests
	@echo "--- oracle (the same forms through clj and clotran) ---"
	scripts/oracle
	@echo "--- pure Fortran (tier A through gfortran and flang, against clj) ---"
	scripts/pure-check
	@echo "--- state inventory (every module variable classified, PLAN step 14a) ---"
	scripts/state-inventory

# What runs before every commit. Ends on the default compiler so the
# tree is left with the build you actually use.
crosscheck:
	$(MAKE) clean && $(MAKE) FC=flang test
	$(MAKE) clean && $(MAKE) test

# clojure.core, compiled (clotran compile). Opt-in: generating it takes
# about 100 s, and `clean` -- so the gate -- removes it. When present,
# every load of core.clj installs it (clotran.loader); a clotran whose
# analysis has changed since refuses it with a note until it is rebuilt.
compiled-core: clotran-bin
	mkdir -p $(B)/compiled/clojure
	./clotran compile src/clj/clojure/core.clj $(B)/compiled/clojure/core.$(SOEXT)

clean:
	rm -rf $(B) clotran-bin clotran-bin.dSYM
