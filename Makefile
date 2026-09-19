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
FCFLAGS = -g -Isrc/f -Jsrc/f $(FCFLAGS_$(notdir $(FC)))

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
FCFLAGS_gfortran = -frecursive

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
else
ICU_PLATFORM = Linux
LIBCXX = -lstdc++
endif

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

src/c/regex_shim.o: src/c/regex_shim.c src/c/regex_shim.h
	$(CC) -c $(ICU_INC) $< -o $@

$(S)/Regex.o: $(S)/Regex.f90
	$(FC) $(FCFLAGS) -c $< -o $@

# --- the host ----------------------------------------------------------

unit-tests = gc_test gc_vector_test gc_list_test gc_map_test gc_hamt_test gc_env_test \
	gc_assoc_test gc_printer_test gc_reader_test gc_eval_test
executables = clotran clotran-gc $(unit-tests)

.PHONY: all test crosscheck clean
all: $(executables)

$(S)/GC.o: $(S)/GC.f90
	$(FC) $(FCFLAGS) -c $< -o $@

gc_test: $(S)/GC.o $(T)/gc_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(T)/gc_test.f90

gcp-objects = $(S)/GC.o $(S)/GCMap.o $(S)/GCHamt.o $(S)/GCAssoc.o $(S)/GCList.o \
	$(S)/GCVector.o $(S)/GCNativeArray.o $(S)/GCPrinter.o

$(S)/GCNamespace.o: $(S)/GCNamespace.f90 $(S)/GC.o $(S)/GCAssoc.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/GCNativeArray.o: $(S)/GCNativeArray.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/GCEval.o: $(S)/GCEval.f90 $(S)/GC.o $(S)/GCList.o $(S)/GCVector.o \
	$(S)/GCAssoc.o $(S)/GCEnv.o $(S)/GCNamespace.o $(S)/GCPrinter.o $(S)/Regex.o \
	$(S)/GCNativeArray.o
	$(FC) $(FCFLAGS) -c $< -o $@

# GCReader depends on Regex: #"..." compiles a pattern at READ time,
# matching real Clojure's own regex literal (LispReader compiles
# straight to a Pattern, not to a string). See Regex.f90.
gc-reader-objects = $(S)/GCReader.o $(S)/Regex.o src/c/regex_shim.o

eval-objects = $(gcp-objects) $(S)/GCEnv.o $(S)/GCNamespace.o $(gc-reader-objects) $(S)/GCEval.o

clotran-gc: $(eval-objects) $(S)/gc_main.f90 $(ICU_LIBS)
	$(FC) $(FCFLAGS) -o $@ $(eval-objects) $(S)/gc_main.f90 $(ICU_LIBS) $(LIBCXX) -lpthread

gc_eval_test: $(eval-objects) $(T)/gc_eval_test.f90 $(ICU_LIBS)
	$(FC) $(FCFLAGS) -o $@ $(eval-objects) $(T)/gc_eval_test.f90 $(ICU_LIBS) $(LIBCXX) -lpthread

$(S)/GCReader.o: $(S)/GCReader.f90 $(S)/GC.o $(S)/GCList.o $(S)/GCVector.o $(S)/GCAssoc.o $(S)/Regex.o
	$(FC) $(FCFLAGS) -c $< -o $@

gc_reader_test: $(gcp-objects) $(gc-reader-objects) $(T)/gc_reader_test.f90 $(ICU_LIBS)
	$(FC) $(FCFLAGS) -o $@ $(gcp-objects) $(gc-reader-objects) $(T)/gc_reader_test.f90 $(ICU_LIBS) $(LIBCXX) -lpthread

$(S)/GCPrinter.o: $(S)/GCPrinter.f90 $(S)/GC.o $(S)/GCList.o $(S)/GCVector.o $(S)/GCAssoc.o $(S)/GCNativeArray.o
	$(FC) $(FCFLAGS) -c $< -o $@

gc_printer_test: $(gcp-objects) $(T)/gc_printer_test.f90
	$(FC) $(FCFLAGS) -o $@ $(gcp-objects) $(T)/gc_printer_test.f90

$(S)/GCAssoc.o: $(S)/GCAssoc.f90 $(S)/GC.o $(S)/GCMap.o $(S)/GCHamt.o
	$(FC) $(FCFLAGS) -c $< -o $@

gc_assoc_test: $(S)/GC.o $(S)/GCMap.o $(S)/GCHamt.o $(S)/GCAssoc.o $(T)/gc_assoc_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/GCMap.o $(S)/GCHamt.o $(S)/GCAssoc.o $(T)/gc_assoc_test.f90

$(S)/GCEnv.o: $(S)/GCEnv.f90 $(S)/GC.o $(S)/GCMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

gc_env_test: $(S)/GC.o $(S)/GCMap.o $(S)/GCEnv.o $(T)/gc_env_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/GCMap.o $(S)/GCEnv.o $(T)/gc_env_test.f90

$(S)/GCHamt.o: $(S)/GCHamt.f90 $(S)/GC.o $(S)/GCMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

gc_hamt_test: $(S)/GC.o $(S)/GCMap.o $(S)/GCHamt.o $(T)/gc_hamt_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/GCMap.o $(S)/GCHamt.o $(T)/gc_hamt_test.f90

$(S)/GCMap.o: $(S)/GCMap.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

gc_map_test: $(S)/GC.o $(S)/GCMap.o $(T)/gc_map_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/GCMap.o $(T)/gc_map_test.f90

$(S)/GCList.o: $(S)/GCList.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

gc_list_test: $(S)/GC.o $(S)/GCList.o $(T)/gc_list_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/GCList.o $(T)/gc_list_test.f90

$(S)/GCVector.o: $(S)/GCVector.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

gc_vector_test: $(S)/GC.o $(S)/GCVector.o $(T)/gc_vector_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/GCVector.o $(T)/gc_vector_test.f90

# The user-facing entry point: scripts/clotran wraps clotran-gc in
# rlwrap when it's installed, exactly like real Clojure's own clj
# wraps clojure (see NOTES.md) -- not a build product itself, just
# installed alongside the binary it wraps.
clotran: scripts/clotran clotran-gc
	cp scripts/clotran $@
	chmod +x $@

# clotran-gc is a prerequisite but NOT run here: scripts/run-clojure-tests
# drives it. It is listed so that `make clean && make test` leaves the
# binary you actually use, and so that gc_main.f90 and the link line are
# inside the gate under both compilers -- gc_eval_test covers the
# modules, not the program.
test: $(unit-tests) clotran-gc
	for t in $(unit-tests); do echo "--- $$t ---"; ./$$t || exit 1; done
	@echo "--- language_test (with core.clj) ---"
	./clotran-gc src/clj/clojure/core.clj test/clj/language_test.clj </dev/null \
	  | tee /dev/stderr | grep -q "^LANGUAGE TESTS PASSED"

# What runs before every commit. Ends on the default compiler so the
# tree is left with the build you actually use.
crosscheck:
	$(MAKE) clean && $(MAKE) FC=flang test
	$(MAKE) clean && $(MAKE) test

clean:
	rm -rf $(S)/*.o $(S)/*.mod $(executables) *.dSYM
