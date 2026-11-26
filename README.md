# Sagitta: the computational arrow of time, in Lean

This is the Lean 4 artifact of the essay *The Computational Arrow of Time: Locating the Second Law
of Computation*. It formalizes one chain of reasoning, and nothing else:

```
decisions  →  laws  →  localization  →  second law  →  consequences for NP
```

The essay asks where the asymmetry between the two directions of a search lives: going forward,
from a witness to the answer "yes", is easy; going backward, from "yes" to a witness, seems hard.
The formalization answers: **not** in the dynamics (reversible dynamics goes back at the same
cost), **not** in the state while it is kept whole (with the full boundary going back is one
verification), but **only** in the erasure of the boundary down to one bit, where the asymmetry is
*exactly* the question `P` versus `NP`. The second law says that the asymmetry is real; it is a
named hypothesis, never an axiom.

## The central hypothesis: the decision hypothesis

The central hypothesis is not stated as `P ≠ NP` but at the place where the localization says the
asymmetry lives. **The decision hypothesis (HD):** *the symmetry of time is broken by the decision
question; reducing the final state to one bit is the boundary condition that breaks the symmetry,
and that breaking has a cost.* Formally: for some polynomial-time verifier, no polynomial-time
procedure reconstructs a witness from the instance alone, that is, from the one bit "a witness
exists" (`Model.DecisionHypothesis` in the core, `TM.DecisionHypothesis` for Turing machines).

```
HD  --(localization, part 3)-->  arrow (P ≠ NP)  -->  SAT, 3-SAT, ISING ∉ P; an NP-intermediate problem
```

* **Equivalence, not strength.** `decisionHypothesis_iff_arrow` proves HD ↔ arrow in both layers,
  by the localization, part (3). HD is the conceptual formulation of `P ≠ NP` (worst case), not a
  stronger hypothesis.
* **The parallel with physics.** The past hypothesis plus reversible dynamics give the second law
  of thermodynamics; here HD plus Bennett's reversible simulation give the arrow and locate it
  (`TM.decision_bennett`): the verifier runs on a reversible machine, and still the arrow holds,
  because it is in the bit, not in the dynamics.
* **Three senses of "decision".** The decision problem (a yes/no question), the erasure of the
  boundary down to that bit, and the choice of a witness that going back has to make again.
* **Not an axiom.** HD is a definition of type `Prop`, taken as `(h : DecisionHypothesis)`. The end
  of `TM/Decision.lean` checks that it is a definition, runs `#print axioms` on every theorem that
  uses it, and contains a mutant (the consequence without `h`) that must fail to elaborate.

## Two readings

The project has two layers, and both are default build targets.

* **The argument is independent of the model** (`Sagitta/Arrow/Core`, library `SagittaCore`,
  only Mathlib). `P` and `NP` are any classes with a few closure properties (reductions compose,
  efficient procedures may call efficient subroutines, every `NP` problem is the domain of a search
  problem, search reduces to deciding prefixes): the structure `Sagitta.Arrow.Model`. The laws, the
  localization and the second law are proved for every such model.
* **For Turing machines it is verified end to end** (`Sagitta/Arrow/TM`, library `SagittaTM`). The
  multi-tape Turing machines of cslib, with the classes of cslib-frontier, form a model
  (`Sagitta.Arrow.TM.tmModel`); every closure property is a theorem of cslib-frontier, used with its
  proof. Every theorem of the core then holds for real machines, and the consequences (SAT, 3-SAT
  and ISING not in `P`, an `NP`-intermediate problem) use the vendored proofs of the Cook–Levin
  theorem, Ladner's theorem, search-to-decision and the `NP`-completeness of MAX-CUT. None of
  them is a hypothesis.

## The chain

| Node | File | Main theorem | Hypothesis |
|---|---|---|---|
| Model | `Core/Base.lean` | `Model` (the closure properties) | none |
| Zeroth law | `Core/LawZero.lean`, `TM/Instance.lean` | `Model.lawZero`, `TM.lawZero` | none |
| First law | `Core/FirstLaw.lean` | `conservation`, `free_table_breaks` | none |
| Localization (1): reversible dynamics | `Core/Reversible.lean` | `ReversibleDynamics.back_iterate_step_iterate`, `history_recovers` | none |
| Localization (2): full boundary, interpolation | `Core/Boundary.lean` | `full_boundary`, `interpolation`, `boundary_lower_bound` | none |
| Localization (3): one bit | `Core/Localization.lean`, `TM/Instance.lean` | `Model.searchEasy_iff_peqNP`, `TM.oneBit` | none |
| Localization theorem | `Core/Localization.lean`, `TM/Consequences.lean` | `localization`, `TM.localizationTM` | none |
| **Decision hypothesis (central)** | `Core/Decision.lean`, `TM/Decision.lean` | `Model.DecisionHypothesis`, `TM.DecisionHypothesis`, `decisionHypothesis_iff_arrow`, `decisionHypothesis_on_boundary` | defines HD |
| Second law 2.1 (Kelvin) | `Core/SecondLaw.lean`, `TM/Instance.lean` | `Model.Arrow`, `Model.kelvin`, `TM.kelvin`, `arrow_independent` | defines `Arrow` |
| Second law 2.2 | `TM/Law22.lean` | `Law22`, `Law22.arrow` (2.2 implies 2.1) | defines `Law22` |
| Bennett | `TM/Instance.lean` | `Bennett`, `reversible_verifier`, `IsReversible.runFrom_injective` | `Bennett` |
| SAT, 3-SAT not in P | `TM/Consequences.lean` | `SAT_notMem_P`, `ThreeSAT_notMem_P` | `Arrow` |
| An NP-intermediate problem | `TM/Consequences.lean` | `exists_intermediate` (Ladner) | `Arrow` |
| ISING not in P | `TM/Ising.lean`, `TM/Consequences.lean` | `Ising.ISING_npComplete`, `ISING_notMem_P` | `Arrow` |
| Consequences from HD | `TM/Decision.lean` | `SAT_notMem_P_of_decision`, `ThreeSAT_notMem_P_of_decision`, `exists_intermediate_of_decision`, `ISING_notMem_P_of_decision` | HD |
| HD and Bennett | `TM/Decision.lean` | `decision_bennett` | HD, `Bennett` |
| 3-SAT not in TIME(2^(n^(1-ε))) | `TM/Consequences.lean` | `ThreeSAT_notMem_TIME` | `Law22` |

### The laws, as stated in the essay

* **Zeroth law.** Reductions are transitive: if `A ≤ₚ B` and `B ≤ₚ C` then `A ≤ₚ C`.
* **First law.** In a closed system, what is hard is neither created nor destroyed: it is only moved
  around; it changes only if information enters from outside. (In a black box: what the query phase
  does not pay, the filling phase paid; with advice from outside, the bound fails.)
* **Second law, 2.1 (Kelvin).** It is impossible to have an efficient process whose only effect is
  to convert a "yes" into its witness. Formally `P ≠ NP`, worst-case version (`Arrow`).
* **Second law, 2.2.** The weak exponential-time hypothesis, equivalently Stearns and Hunt's SH
  (arXiv 2611.02650, Theorem 2.4): 3-SAT is not in `TIME(2^(n^(1−ε)))` for any `ε > 0` (`Law22`).
  It implies 2.1 (`Law22.arrow`, proved).

### The hypotheses

There are exactly four named hypotheses, and all four are definitions of type `Prop`, taken as
explicit arguments `(h : DecisionHypothesis)`, `(h : Arrow)`, `(h : Law22)`, `(hB : Bennett)`. The
first two are equivalent (`decisionHypothesis_iff_arrow`); HD is the central one, the arrow its
statement as `P ≠ NP`. None is a Lean `axiom`. The end of
`TM/Consequences.lean` runs `#print axioms` on every main theorem under `#guard_msgs`, so the build
fails if any of them depends on anything other than `propext`, `Classical.choice` and
`Quot.sound`. The core also proves that the arrow is independent of the closure properties
(`arrow_independent`: one model satisfies them with `P = NP`, another with `P ≠ NP`), and that
without the arrow the consequences fail (`consequences_need_arrow`); the same holds for HD (`decisionHypothesis_independent`,
`consequences_need_decisionHypothesis`).

`Bennett` (every polynomial-time function is computed in polynomial time and space by a reversible
multi-tape machine, whose step is injective on running configurations) is not proved for cslib's
machines: that needs Bennett's construction (compute with a history tape, copy the output,
uncompute) as a cslib machine with injective transitions, with its time analysis. Its abstract
shadow is proved in the core (`historyDynamics`, `history_simulates`, `history_recovers`).

Not here, on purpose: the Boolean dichotomy (Schaefer), whose formalization rests on further
assumptions, and the other companion material of the essay.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.36.0-rc2`)
and Mathlib (`bbff2954`) are the ones cslib-frontier `99f02811` uses.

```sh
lake exe cache get   # prebuilt Mathlib; Mathlib is never compiled here
lake build
```

A clean `lake build` compiles 345 vendored modules (312 from cslib-frontier, 33 from cslib) and 15
modules of this project, and no Mathlib module. On an Apple M1 Pro with `LEAN_NUM_THREADS=3` it
takes 5 min 47 s of wall-clock time (measured on 25 November 2026, before the two modules of the decision hypothesis, which add
about 45 s); the modules of this project
take about 2 min of that, mostly loading the environment of cslib-frontier.

## Vendored code

The project does not depend on cslib-frontier or cslib as packages. It contains only the import
closure of the modules it uses (about 2% of cslib-frontier), copied without modification, with
their licenses, NOTICE and copyright headers. See [`VENDORED.md`](VENDORED.md).

## AI assistance

The Lean code, the docstrings and this README were written with the help of Claude (Anthropic), an
AI model, under the direction of the author, who chose the statements, the hypotheses and the
structure. Every proof is checked by Lean.

## License

Copyright 2026 Jose-de-Jesus Ulate-Cardenas. Licensed under the Apache License, Version 2.0
([`LICENSE`](LICENSE)). See [`NOTICE.md`](NOTICE.md) for the third-party code and dependencies.
