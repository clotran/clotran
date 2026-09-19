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

unit-tests = gc_test persistent_vector_test persistent_list_test persistent_array_map_test persistent_hash_map_test env_test \
	assoc_test printer_test reader_test eval_test
executables = clotran $(unit-tests)

.PHONY: all test crosscheck clean
all: $(executables)

$(S)/GC.o: $(S)/GC.f90
	$(FC) $(FCFLAGS) -c $< -o $@

gc_test: $(S)/GC.o $(T)/gc_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(T)/gc_test.f90

data-objects = $(S)/GC.o $(S)/PersistentArrayMap.o $(S)/PersistentHashMap.o $(S)/Assoc.o $(S)/PersistentList.o \
	$(S)/PersistentVector.o $(S)/NativeArray.o $(S)/Printer.o

$(S)/Namespace.o: $(S)/Namespace.f90 $(S)/GC.o $(S)/Assoc.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/NativeArray.o: $(S)/NativeArray.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/Eval.o: $(S)/Eval.f90 $(S)/GC.o $(S)/PersistentList.o $(S)/PersistentVector.o \
	$(S)/Assoc.o $(S)/Env.o $(S)/Namespace.o $(S)/Printer.o $(S)/Regex.o \
	$(S)/NativeArray.o
	$(FC) $(FCFLAGS) -c $< -o $@

# LispReader depends on Regex: #"..." compiles a pattern at READ time,
# matching real Clojure's own regex literal (LispReader compiles
# straight to a Pattern, not to a string). See Regex.f90.
reader-objects = $(S)/LispReader.o $(S)/Regex.o src/c/regex_shim.o

eval-objects = $(data-objects) $(S)/Env.o $(S)/Namespace.o $(reader-objects) $(S)/Eval.o

clotran: $(eval-objects) $(S)/main.f90 $(ICU_LIBS)
	$(FC) $(FCFLAGS) -o $@ $(eval-objects) $(S)/main.f90 $(ICU_LIBS) $(LIBCXX) -lpthread

eval_test: $(eval-objects) $(T)/eval_test.f90 $(ICU_LIBS)
	$(FC) $(FCFLAGS) -o $@ $(eval-objects) $(T)/eval_test.f90 $(ICU_LIBS) $(LIBCXX) -lpthread

$(S)/LispReader.o: $(S)/LispReader.f90 $(S)/GC.o $(S)/PersistentList.o $(S)/PersistentVector.o $(S)/Assoc.o $(S)/Regex.o
	$(FC) $(FCFLAGS) -c $< -o $@

reader_test: $(data-objects) $(reader-objects) $(T)/reader_test.f90 $(ICU_LIBS)
	$(FC) $(FCFLAGS) -o $@ $(data-objects) $(reader-objects) $(T)/reader_test.f90 $(ICU_LIBS) $(LIBCXX) -lpthread

$(S)/Printer.o: $(S)/Printer.f90 $(S)/GC.o $(S)/PersistentList.o $(S)/PersistentVector.o $(S)/Assoc.o $(S)/NativeArray.o
	$(FC) $(FCFLAGS) -c $< -o $@

printer_test: $(data-objects) $(T)/printer_test.f90
	$(FC) $(FCFLAGS) -o $@ $(data-objects) $(T)/printer_test.f90

$(S)/Assoc.o: $(S)/Assoc.f90 $(S)/GC.o $(S)/PersistentArrayMap.o $(S)/PersistentHashMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

assoc_test: $(S)/GC.o $(S)/PersistentArrayMap.o $(S)/PersistentHashMap.o $(S)/Assoc.o $(T)/assoc_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/PersistentArrayMap.o $(S)/PersistentHashMap.o $(S)/Assoc.o $(T)/assoc_test.f90

$(S)/Env.o: $(S)/Env.f90 $(S)/GC.o $(S)/PersistentArrayMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

env_test: $(S)/GC.o $(S)/PersistentArrayMap.o $(S)/Env.o $(T)/env_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/PersistentArrayMap.o $(S)/Env.o $(T)/env_test.f90

$(S)/PersistentHashMap.o: $(S)/PersistentHashMap.f90 $(S)/GC.o $(S)/PersistentArrayMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_hash_map_test: $(S)/GC.o $(S)/PersistentArrayMap.o $(S)/PersistentHashMap.o $(T)/persistent_hash_map_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/PersistentArrayMap.o $(S)/PersistentHashMap.o $(T)/persistent_hash_map_test.f90

$(S)/PersistentArrayMap.o: $(S)/PersistentArrayMap.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_array_map_test: $(S)/GC.o $(S)/PersistentArrayMap.o $(T)/persistent_array_map_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/PersistentArrayMap.o $(T)/persistent_array_map_test.f90

$(S)/PersistentList.o: $(S)/PersistentList.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_list_test: $(S)/GC.o $(S)/PersistentList.o $(T)/persistent_list_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/PersistentList.o $(T)/persistent_list_test.f90

$(S)/PersistentVector.o: $(S)/PersistentVector.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_vector_test: $(S)/GC.o $(S)/PersistentVector.o $(T)/persistent_vector_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/PersistentVector.o $(T)/persistent_vector_test.f90

# clotran is a prerequisite but NOT run as a unit test: it is listed so
# that `make clean && make test` leaves the binary you actually use, and
# so that main.f90 and the link line are inside the gate under both
# compilers -- eval_test covers the modules, not the program.
# scripts/clotran wraps the binary in rlwrap, the way clj wraps clojure.
test: $(unit-tests) clotran
	for t in $(unit-tests); do echo "--- $$t ---"; ./$$t || exit 1; done
	@echo "--- language_test (with core.clj) ---"
	./clotran src/clj/clojure/core.clj test/clj/language_test.clj </dev/null \
	  | tee /dev/stderr | grep -q "^LANGUAGE TESTS PASSED"

# What runs before every commit. Ends on the default compiler so the
# tree is left with the build you actually use.
crosscheck:
	$(MAKE) clean && $(MAKE) FC=flang test
	$(MAKE) clean && $(MAKE) test

clean:
	rm -rf $(S)/*.o $(S)/*.mod $(executables) *.dSYM
