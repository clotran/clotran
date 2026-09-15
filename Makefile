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
# -> eval_form), and so is refcounting (release -> deallocate -> final
# -> release). Those corrupted memory quietly, then died later at an
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

executables = clotran clotran-bin rc_test atom_test persistent_vector_test \
	persistent_list_test persistent_hash_map_test rt_test persistent_array_map_test env_test namespace_test eval_test native_test gc_test

unit-tests = rc_test atom_test persistent_vector_test persistent_list_test \
	persistent_hash_map_test rt_test persistent_array_map_test env_test \
	namespace_test eval_test native_test gc_test

.PHONY: all test crosscheck clean
all: $(executables)

$(S)/rc.o: $(S)/rc.f90
	$(FC) $(FCFLAGS) -c $< -o $@

rc_test: $(S)/rc.o $(T)/rc_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/rc.o $(T)/rc_test.f90

$(S)/Values.o: $(S)/Values.f90 $(S)/GC.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/GC.o: $(S)/GC.f90
	$(FC) $(FCFLAGS) -c $< -o $@

gc_test: $(S)/GC.o $(T)/gc_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(T)/gc_test.f90

$(S)/NativeArray.o: $(S)/NativeArray.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/Atom.o: $(S)/Atom.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

atom_test: $(S)/Atom.o $(T)/atom_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/Atom.o $(T)/atom_test.f90

$(S)/PersistentVector.o: $(S)/PersistentVector.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_vector_test: $(S)/PersistentVector.o $(T)/persistent_vector_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/PersistentVector.o $(T)/persistent_vector_test.f90

$(S)/PersistentList.o: $(S)/PersistentList.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_list_test: $(S)/PersistentList.o $(T)/persistent_list_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/PersistentList.o $(T)/persistent_list_test.f90

native_test: $(S)/PersistentList.o $(T)/native_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/PersistentList.o $(T)/native_test.f90

$(S)/PersistentHashMap.o: $(S)/PersistentHashMap.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_hash_map_test: $(S)/PersistentHashMap.o $(T)/persistent_hash_map_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/PersistentHashMap.o $(T)/persistent_hash_map_test.f90

$(S)/PersistentArrayMap.o: $(S)/PersistentArrayMap.f90 $(S)/Values.o $(S)/PersistentHashMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_array_map_test: $(S)/PersistentArrayMap.o $(T)/persistent_array_map_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/PersistentHashMap.o $(S)/PersistentArrayMap.o $(T)/persistent_array_map_test.f90

$(S)/RT.o: $(S)/RT.f90 $(S)/PersistentList.o $(S)/PersistentVector.o $(S)/PersistentArrayMap.o \
	$(S)/NativeArray.o
	$(FC) $(FCFLAGS) -c $< -o $@

rt_test: $(S)/RT.o $(T)/rt_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/NativeArray.o $(S)/PersistentList.o $(S)/PersistentVector.o \
		$(S)/PersistentHashMap.o $(S)/PersistentArrayMap.o $(S)/RT.o $(T)/rt_test.f90

$(S)/Env.o: $(S)/Env.f90 $(S)/PersistentArrayMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

env_test: $(S)/Env.o $(T)/env_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/PersistentHashMap.o $(S)/PersistentArrayMap.o $(S)/Env.o $(T)/env_test.f90

$(S)/Namespace.o: $(S)/Namespace.f90 $(S)/PersistentArrayMap.o $(S)/Atom.o
	$(FC) $(FCFLAGS) -c $< -o $@

namespace_test: $(S)/Namespace.o $(T)/namespace_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/GC.o $(S)/Values.o $(S)/Atom.o $(S)/PersistentHashMap.o $(S)/PersistentArrayMap.o $(S)/Namespace.o $(T)/namespace_test.f90

$(S)/printer.o: $(S)/printer.f90 $(S)/RT.o $(S)/PersistentArrayMap.o $(S)/Atom.o $(S)/NativeArray.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/LispReader.o: $(S)/LispReader.f90 $(S)/PersistentList.o $(S)/PersistentVector.o $(S)/PersistentArrayMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/Numbers.o: $(S)/Numbers.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/readline.o: $(S)/readline.f90
	$(FC) $(FCFLAGS) -c $< -o $@

eval-objects = $(S)/GC.o $(S)/Values.o $(S)/Atom.o $(S)/NativeArray.o $(S)/PersistentList.o $(S)/PersistentVector.o \
	$(S)/PersistentHashMap.o $(S)/PersistentArrayMap.o $(S)/Env.o $(S)/Namespace.o $(S)/Numbers.o $(S)/Eval.o \
	$(S)/RT.o $(S)/printer.o $(S)/LispReader.o $(S)/readline.o

$(S)/Eval.o: $(S)/Eval.f90 $(S)/Env.o $(S)/Namespace.o $(S)/PersistentList.o $(S)/PersistentVector.o \
	$(S)/Numbers.o $(S)/printer.o $(S)/Atom.o $(S)/NativeArray.o $(S)/LispReader.o $(S)/readline.o
	$(FC) $(FCFLAGS) -c $< -o $@

eval_test: $(eval-objects) $(T)/eval_test.f90
	$(FC) $(FCFLAGS) -o $@ $(eval-objects) $(T)/eval_test.f90

# The raw interpreter (src/f/main.f90 -- the same driver that carried
# mal's step2 through stepA test names there; nothing left to name
# per-step now that this stands on its own).
clotran-bin: $(eval-objects) $(S)/main.f90
	$(FC) $(FCFLAGS) -o $@ $(eval-objects) $(S)/main.f90

# The user-facing entry point: scripts/clotran wraps clotran-bin in
# rlwrap when it's installed, exactly like real Clojure's own clj
# wraps clojure (see NOTES.md) -- not a build product itself, just
# installed alongside the binary it wraps.
clotran: scripts/clotran clotran-bin
	cp scripts/clotran $@
	chmod +x $@

# clotran-bin is a prerequisite but NOT run here: scripts/run-clojure-tests
# drives it. It is listed because `make clean && make test` used to leave
# no binary at all, and that script then reported every namespace as
# CRASHED -- a missing binary looking exactly like a real regression.
test: $(unit-tests) clotran-bin
	for t in $(unit-tests); do echo "--- $$t ---"; ./$$t || exit 1; done

# What runs before every commit. Ends on the default compiler so the
# tree is left with the build you actually use.
crosscheck:
	$(MAKE) clean && $(MAKE) FC=flang test
	$(MAKE) clean && $(MAKE) test

clean:
	rm -rf $(S)/*.o $(S)/*.mod $(executables) *.dSYM
