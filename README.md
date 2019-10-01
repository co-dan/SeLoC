# SeLoC: Relational separation logic for non-interference

This is the Coq development for SeLoC: a relational separation logic for proving non-interference of concurrent stateful programs.

# Installation instructions

This version is known to compile with:
- Coq 8.9
- Iris 3.2.0
- Equations 1.2

If you use [opam](https://opam.ocaml.org/), then you can install all the dependencies by running the following commands from the root directory:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install .
```

Otherwise you can manually install all the dependencies and run `make && make install`.

# Directory structure

All the Coq modules are in the subfolders of the `theories` folder:

- `program_logic`: the definition of double weakest preconditions and the core logic rules.
- `proofmode`: tactics that ease symbolic execution proofs.
- `logrel`: contains the type system and its interpretation.
- `examples`: examples studied in the paper.
- `heap_lang`: operational semantics for HeapLang with deterministic allocation and its adequacy result (see more on that below).

## Material from the paper

- Rules from Figure 2 are in `program_logic/dwp.v`, `program_logic/lifting.v` and `program_logic/heap_lang_lifting.v`.
- Proposition 3 is proved in `examples/rand.v`.
- Proposition 5 is proved in `examples/value_sensitivity_3.v`.
- The types are defined in `logrel/types.v`, the model for the type system and the compatibility rules are in `logrel/interp.v`.
The typing rules and the fundamental property are in `logrel/typing.v`.
- Proposition 9 is proved in `examples/various.v`.
- The modular specifications for dynamically classified references are given in `examples/value_dep.v`. The example clients that use those specification are in `examples/value_sensitivity_2.v` and `examples/value_sensitivity_4.v`.
- The bisimulation is constructed in `program_logic/dwp_adequacy.v`.

# Differences with the paper

There are some differences between the Coq formalization and the
presentation in the paper.

First of all, to be compatible with the existing version of HeapLang
in Iris, we define double weakest preconditions on top of a language with non-deterministic
allocation semantics. However, to have well-defined probabilistic
semantics of thread-pools, we require the allocation to be
deterministic. We formalize HeapLang with deterministic allocation in
`heap_lang/lang_det.v` (the language is parameterized by an allocation
oracle). We prove the following adequacy statement: if we have a double weakest precondition for a
program under the standard non-deterministic semantics, we can also
have adouble weakest precondition for the same program under the deterministic semantics with
an allocator.

Secondly, our type system (and its interpretation) is parameterized by
an attacker level `ξ`, and you can see that throughout the code.

Lastly, In Coq, we do not use the AWP proposition for atomic
weakest preconditions we used in the paper. Rather, in the rule
`dwp-awp` (in the formalization:
`dwp_atomic_lift_wp`) we require the expressions `e1` and `e2` to be
/atomic/ and produce no forked off threads. Then, we fall back onto
the total weakest precondition from Iris. This allows us to reuse a
lot of lemmas and tactics about total weakest preconditions from Iris.
