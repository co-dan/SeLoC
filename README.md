# SeLoC: Relational separation logic for non-interference

This is the Coq development for SeLoC: a relational separation logic for proving non-interference of concurrent stateful programs.

See [the paper](https://arxiv.org/abs/1910.00905) for more details.

# Installation instructions

This version is known to compile with:
- Coq 8.12 or later
- Iris developement version [96191ed7ef792478c86890a0ebdbbbea0dc9c9ab](https://gitlab.mpi-sws.org/iris/iris/tree/96191ed7ef792478c86890a0ebdbbbea0dc9c9ab)
- Equations 1.2.3 or later

If you use [opam](https://opam.ocaml.org/), then you can install all the dependencies by running the following commands from the root directory:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
opam install .
```

Otherwise you can manually install all the dependencies and run `make && make install`.

# Directory structure

All the Coq modules are in the subfolders of the `theories` folder:

- [program_logic](theories/program_logic): the definition of double weakest preconditions and the core logic rules, as well as the soundness proof.
- [proofmode](theories/proofmode): tactics that ease symbolic execution proofs.
- [logrel](theories/logrel): the type system and its interpretation.
- [examples](theories/examples): examples studied in the paper.
- [heap_lang](theories/heap_lang): operational semantics for HeapLang with deterministic allocation and its adequacy result (see more on that below).

## Material from the paper

- The set data structure from Section II.A is in [examples/set.v](theories/examples/set.v).
The safe arrays from Section II.B are defined and verified in [examples/array.v](theories/array.v).
- Rules from Figure 3 are in [program_logic/dwp.v](theories/program_logic/dwp.v), [program_logic/lifting.v](theories/program_logic/lifting.v) and [program_logic/heap_lang_lifting.v](theories/program_logic/heap_lang_lifting.v).
- Proposition 4 is proved in [examples/rand.v](theories/examples/rand.v).
- Proposition 6 is proved in [examples/value_sensitivity_3.v](theories/examples/value_sensitivity_3.v).
- The types are defined in [logrel/types.v](theories/logrel/types.v), the model for the type system and the compatibility rules are in [logrel/interp.v](theories/logrel/interp.v).
The typing rules and the fundamental property are in [logrel/typing.v](theories/logrel/typing.v).
- Proposition 10 is proved in [examples/various.v](theories/examples/various.v).
- The modular specifications for dynamically classified references are given in [examples/value_dep.v](theories/examples/value_dep.v). The example clients that use those specification are in [examples/value_sensitivity_2.v](theories/examples/value_sensitivity_2.v) and [examples/value_sensitivity_4.v](theories/examples/value_sensitivity_4.v).
- The bisimulation is constructed in [program_logic/dwp_adequacy.v](theories/program_logic/dwp_adequacy.v).

# Differences with the paper

There are some differences between the Coq formalization and the presentation in the paper.

First of all, to be compatible with the existing version of HeapLang in Iris, we define double weakest preconditions on top of a language with non-deterministic allocation semantics.
However, to have well-defined probabilistic semantics of thread-pools, we require the allocation to be deterministic. We formalize HeapLang with deterministic allocation in [heap_lang/lang_det.v](theories/heap_lang/lang_det.v) (the language is parameterized by an allocation oracle).
We prove the following adequacy statement: if we have a double weakest precondition for a program under the standard non-deterministic semantics, we can also have adouble weakest precondition for the same program under the deterministic semantics with an allocator.

Secondly, our type system (and its interpretation) is parameterized by an attacker level `ξ`, and you can see that throughout the code.
In our type system we also have an option type for integers.
It is denoted as `toption il l` where `il` is the sensitivity label of the underlying integer, and `l` is the label for the option type (whether it is `SOME` or `NONE`); thus it roughly corresponds to `option^l (int^il)`.
In the future work we would like to extend the typing rules to arbitrary sum types.

Lastly, In Coq, we do not use the AWP proposition for atomic weakest preconditions we used in the paper.
Rather, in the rule `dwp-awp` (in the formalization: `dwp_atomic_lift_wp`) we require the expressions `e1` and `e2` to be _atomic_ and produce no forked off threads.
Then, we fall back onto the total weakest precondition from Iris.
This allows us to reuse a lot of lemmas and tactics about total weakest preconditions from Iris.
