FC = flang
FCFLAGS = -g -Isrc/f -Jsrc/f

# Pinned, not just "whatever's on PATH": subtle compiler-specific behavior
# (FINAL, defined assignment, unlimited polymorphic) means a different
# major.minor could behave differently. See NOTES.md for why flang, not
# gfortran (gfortran stays a cross-check oracle only). Bump deliberately,
# after re-running the test suite on both.
REQUIRED_FLANG = 23.1
ACTUAL_FLANG := $(shell $(FC) -dumpversion 2>/dev/null | cut -d. -f1,2)
ifneq ($(ACTUAL_FLANG),$(REQUIRED_FLANG))
$(warning flang version is $(ACTUAL_FLANG), this project is pinned to $(REQUIRED_FLANG) -- `brew upgrade flang`)
endif

S = src/f
T = test/f

executables = clotran clotran-bin rc_test atom_test persistent_vector_test \
	persistent_list_test rt_test persistent_array_map_test env_test namespace_test eval_test

.PHONY: all test clean
all: $(executables)

$(S)/rc.o: $(S)/rc.f90
	$(FC) $(FCFLAGS) -c $< -o $@

rc_test: $(S)/rc.o $(T)/rc_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/rc.o $(T)/rc_test.f90

$(S)/Values.o: $(S)/Values.f90
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/Atom.o: $(S)/Atom.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

atom_test: $(S)/Atom.o $(T)/atom_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/Values.o $(S)/Atom.o $(T)/atom_test.f90

$(S)/PersistentVector.o: $(S)/PersistentVector.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_vector_test: $(S)/PersistentVector.o $(T)/persistent_vector_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/Values.o $(S)/PersistentVector.o $(T)/persistent_vector_test.f90

$(S)/PersistentList.o: $(S)/PersistentList.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_list_test: $(S)/PersistentList.o $(T)/persistent_list_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/Values.o $(S)/PersistentList.o $(T)/persistent_list_test.f90

$(S)/PersistentArrayMap.o: $(S)/PersistentArrayMap.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

persistent_array_map_test: $(S)/PersistentArrayMap.o $(T)/persistent_array_map_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/Values.o $(S)/PersistentArrayMap.o $(T)/persistent_array_map_test.f90

$(S)/RT.o: $(S)/RT.f90 $(S)/PersistentList.o $(S)/PersistentVector.o $(S)/PersistentArrayMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

rt_test: $(S)/RT.o $(T)/rt_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/Values.o $(S)/PersistentList.o $(S)/PersistentVector.o \
		$(S)/PersistentArrayMap.o $(S)/RT.o $(T)/rt_test.f90

$(S)/Env.o: $(S)/Env.f90 $(S)/PersistentArrayMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

env_test: $(S)/Env.o $(T)/env_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/Values.o $(S)/PersistentArrayMap.o $(S)/Env.o $(T)/env_test.f90

$(S)/Namespace.o: $(S)/Namespace.f90 $(S)/PersistentArrayMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

namespace_test: $(S)/Namespace.o $(T)/namespace_test.f90
	$(FC) $(FCFLAGS) -o $@ $(S)/Values.o $(S)/PersistentArrayMap.o $(S)/Namespace.o $(T)/namespace_test.f90

$(S)/printer.o: $(S)/printer.f90 $(S)/RT.o $(S)/PersistentArrayMap.o $(S)/Atom.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/LispReader.o: $(S)/LispReader.f90 $(S)/PersistentList.o $(S)/PersistentVector.o $(S)/PersistentArrayMap.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/Numbers.o: $(S)/Numbers.f90 $(S)/Values.o
	$(FC) $(FCFLAGS) -c $< -o $@

$(S)/readline.o: $(S)/readline.f90
	$(FC) $(FCFLAGS) -c $< -o $@

eval-objects = $(S)/Values.o $(S)/Atom.o $(S)/PersistentList.o $(S)/PersistentVector.o \
	$(S)/PersistentArrayMap.o $(S)/Env.o $(S)/Namespace.o $(S)/Numbers.o $(S)/Eval.o \
	$(S)/RT.o $(S)/printer.o $(S)/LispReader.o $(S)/readline.o

$(S)/Eval.o: $(S)/Eval.f90 $(S)/Env.o $(S)/Namespace.o $(S)/PersistentList.o $(S)/PersistentVector.o \
	$(S)/Numbers.o $(S)/printer.o $(S)/Atom.o $(S)/LispReader.o $(S)/readline.o
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

test: rc_test atom_test persistent_vector_test persistent_list_test \
	rt_test persistent_array_map_test env_test namespace_test eval_test
	for t in $^; do echo "--- $$t ---"; ./$$t || exit 1; done

clean:
	rm -rf $(S)/*.o $(S)/*.mod $(executables) *.dSYM
