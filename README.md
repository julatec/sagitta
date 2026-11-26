# Sagitta: the computational arrow of time, in Lean

[![Lean build](https://github.com/julatec/sagitta/actions/workflows/lean.yml/badge.svg)](https://github.com/julatec/sagitta/actions/workflows/lean.yml)

This is the Lean 4 artifact of the essay *The Computational Arrow of Time: Locating the Second Law
of Computation* (in preparation). It formalizes one chain of reasoning, and nothing else:

```
decisions  →  laws  →  localization  →  second law  →  consequences for NP
```

The essay asks where the asymmetry between the two directions of a search lives: going forward,
from a witness to the answer "yes", is easy; going backward, from "yes" to a witness, seems hard.
The essay's reading of the formalization: **not** in the dynamics (reversible dynamics goes back at the same
cost), **not** in the state while it is kept whole (with the full boundary going back is one
verification), but **only** in the erasure of the boundary down to one bit, where the asymmetry is
*exactly* the question `P` versus `NP`. The second law says that the asymmetry is real; it is a
named hypothesis, never an axiom.

## Fidelity notes: what is and is not proved (read first)

An independent audit compared every central statement with the literature (40 statements: 33
faithful, 2 weaker, 5 different). One of the two weaker ones, Bennett, has since been fixed. The
differences, stated plainly:

* **Bennett requires clean tapes.** `Bennett` (`TM/Instance.lean`, proved as `bennett_holds`)
  requires what Bennett (1973) adds to Lecerf (1963): when the reversible machine halts, the output
  is on the output tape, every work head is on cell `0`, and every work tape is blank except a copy
  of the input and a constant mark, with the same role for every input (`ComputesCleanly`): nothing
  that depends on the run, such as a history, remains. Time and space are linear in `n + t(n)`, as
  in Bennett, not just polynomial. The old proposition, without clean tapes, is kept as the mutant
  `BennettWeak`: the Lecerf–Landauer machine `histOnlyTM` (history, emit, stop) proves it
  (`bennett_of_history_only`) and fails the clean requirement (`history_only_not_clean`). The exact
  time is `2n + 4t + 6|y| + 21` (`revTM_correct_clean`; n = input length, t = steps of the simulated
  machine, y = output); the `4t` matches Bennett's count. Remaining differences with Bennett's
  setting, not with his theorem: cslib's input tape is read-only, so the input is copied once to a
  work tape and that copy (with its one-cell mark) stays, playing the role of Bennett's
  reconstructed input, and the input head ends on the blank after the input; cslib's actions write
  and move in one step (quintuples), Bennett's are quadruples; the space is `(k + 3 + h)(2T + 1)`
  with `h` one-hot history tapes, a large constant against Bennett's three tapes.
* **ISING.** `ISING_npComplete` is NP-completeness on arbitrary graphs with integer couplings
  written in binary (via MAX-CUT). Barahona (1982) proves the much stronger result on 3D lattices
  with couplings in {−1, 0, 1}; that is not formalized here.
* **Law22.** It measures `n` in bits of the CNF encoding (the size form of SH), not in variables.
  It is equivalent to the weak ETH (n variables) only by Theorem 2.4 of arXiv 2611.02650, which is
  not formalized here.
* **Localization.** `localization` and `localization_one(_tm)` are conjunctions of the proved
  facts. The words "only" and "neither symmetry decides the arrow" are the essay's reading, not a
  formal statement; `arrow_independent` uses models without dynamics. In the abstract core, the
  equality of the cost back and forward is definitional; for Turing machines there is no general
  costed inverse.
* **`decision_bennett_holds`.** Its conclusion follows from HD alone; Bennett adds the reversible
  verifier, not the arrow.

### Equivalences with independent statements (`Sagitta/Fidelity`)

`Fidelity/Blind.lean` states five results from the literature without reading this project;
`Fidelity/Equiv.lean` compares them with ours, in Lean.

| Literature (blind statement) | Ours | Result |
|---|---|---|
| Goldreich, Thm. 2.6: `PC ⊆ PF ↔ P = NP` (`GoldreichThm2_6`) | `FNP_subset_FPSearch_iff`, `DecisionHypothesis` | **Proved** (`goldreichThm2_6`); HD is exactly `PC ⊄ PF` (`decisionHypothesis_iff_not_PC_subset_PF`) |
| Ladner, Arora–Barak form with Karp reductions (`Ladner`) | `exists_intermediate` | **Proved equivalent** (`ladner`, `ladner_iff`); Ladner's stronger form with Turing reductions is not stated |
| ISING decision problem is NP-complete (`IsingNPComplete`) | `ISING_npComplete` | **Proved equivalent** (`isingNPComplete_iff`); neither is Barahona's lattice theorem |
| Bennett with the input head back at the origin (`BennettPoly`, `BennettLinear`) | `Bennett` | **One direction only, and the blind one is false** (`not_bennettPoly`, `not_bennettLinear`, `bennett_not_imp_bennettPoly`): a reversible cslib machine cannot move its input head off a blank, so it cannot both return it to the origin and compute the identity. Documented difference: ours leaves the head on the blank after the input, which is Bennett's own final state on a read-only input |
| Weak ETH (`n` variables) and its size form (`WeakETH`, `WeakETHSize`) | `Law22` | **Documented difference, no implication proved**: `n` in bits against variables, all formulas against 3CNF inputs without repetitions, and a defect of the blind size form at the empty formula (`numVars_single`, `length_encCNF_single`, `weakETHSize_bound_nil`) |

### The battery (`Sagitta/Fidelity.lean`, a default build target)

* **Consequences the literature derives come out of our statements.** Bennett gives a reversible,
  garbage-free verifier for every `NP` problem (`reversible_verifier_of_bennett`); Cook–Levin gives
  the classical reductions (`reduces_to_SAT`, `SAT_reduces_ThreeSAT`, `SAT_reduces_ISING`,
  `P_eq_NP_iff_SAT_mem_P`); SAT is self-reducible (`SAT_selfReducible`: SAT ∈ P iff its search
  problem is in `FPSearch`).
* **Mutants: every definition broken on purpose is caught by a sanity check.** `P` without
  uniformity contains every set (`PNonUniform_eq_univ`) and, at the level of functions, a function
  with exponentially long outputs that no polynomial-time machine computes
  (`expOut_mem_FPNonUniform`, `not_computableInPolyTime_expOut`); "reversible" only on reachable
  configurations accepts a machine that erases (`eraseTM_isReversibleReachable`), which the real
  definition rejects (`eraseTM_not_isReversible`); an exponential bound in place of the polynomial
  one accepts `2 ^ n` (`expBounded_two_pow`), which the real one rejects
  (`not_polynomiallyBounded_two_pow`); Bennett without clean tapes holds for the history-only
  simulation, which fails `ComputesCleanly` (`historyOnly_haltsNow_not_clean`). No mutant passed.
* **Non-vacuity of the named hypotheses.** HD and Law 2.2 each imply `P ≠ NP`, so no model of them
  for Turing machines can be built in Lean. What is proved: HD holds in a model of the core axioms
  and fails in another (`decisionHypothesis_has_model`); for Turing machines HD is exactly
  `P ≠ NP` on `{0,1}*` (`decisionHypothesis_iff_P_ne_NP`); the three hypotheses together say no more
  than Law 2.2 alone (`law22_and_rest_iff`); and Law 2.2 is not empty: for every `ε ≥ 1` its
  instance is a theorem (`law22_of_one_le`: no machine decides 3-SAT in constant time, by a
  locality argument on the input head), so only the `0 < ε < 1` part is a hypothesis.
* **Sanity checks.** A machine that erases is not reversible; one that copies between two tapes is,
  one that copies a tape onto itself is not, and the machine that halts at once is; small ISING and
  SAT instances are checked by `decide`.

## The first localization, complete: neither symmetry of time decides the arrow

The first localization ("the dynamics does not carry the arrow") is stated with the **two
symmetries of time** that a dynamics can have, and the Noether charge of each
(`Core/Dynamics.lean`, and `TM/Dynamics.lean` for cslib's machines).

* **Time reversal: the information is conserved.** Discrete Noether: for a reversible step, a
  quantity is conserved if and only if it is constant on the orbits of the group of steps
  (`conserved_iff_const_on_orbits`), and, in Koopman's form, if and only if its phases commute with
  the operator `φ ↦ φ ∘ f` (`koopman_noether`). Koopman's operator is unitary if and only if the step
  is bijective (`koopman_isometry_iff`), so a reversible dynamics neither creates nor destroys
  information (`ReversibleDynamics.card_image_iterate`, `ReversibleDynamics.koopman_isometry`,
  `entropy_pushforward`); erasure is not unitary (`erasure_not_isometry`).
* **Time translation: the system does not know the time (the CHT).** A homogeneous automaton has no
  step counter. Two runs that reach the same state continue identically (`noether_charge`,
  `does_not_know_the_time`). A clock is paid in memory: a clocked automaton is a homogeneous one on
  `σ × κ`, `|σ| · 2^c` states for `c` bits (`homogenize_run`, `card_clock_bits`). The cube law
  `N ≤ 2^L · 2^s · min (t + 1) 2^(S − 1)` (`cube_law`, `cube_law_general`, `cube_law_clock`, with the
  exact price of the clock in `clock_price_control`); halt or cycle (`halt_or_cycle`), so `S` bits
  halt before `2^S` (`halts_before_two_pow`, `cht_time`, `clock_in_memory`).
* **For cslib's machines** (`TM/Dynamics.lean`): a multi-tape machine with space `S` is a homogeneous
  automaton of at most `2^spaceBits` states (`toAutomaton`, `run_toAutomaton`, `card_states_bits`,
  with the counting of cslib's `ConfigBound`), so it does not know the time
  (`does_not_know_the_time_tm`), obeys the cube law (`cube_law_tm`), halts or cycles
  (`halt_or_cycle_tm`) and, if it halts, halts within `2^spaceBits` steps (`halts_soon_tm`).
* **The CHT tower, piece 1.** Homogeneity with polynomial memory gives the `PSPACE` bound, `2^poly`
  steps (`cht_pspace`), and not a polynomial one: a counter of `n + 1` bits answers within the CHT
  budget and not in `2^n − 1` queries (`cht_exponential_not_polynomial`).
* **The conclusion** (`Dynamics.localization_one`, `TM.localization_one_tm`): these facts are
  theorems with no hypothesis, true in every model, while the arrow holds in one model with the
  closure properties and fails in another; neither symmetry of time decides it. With the decision
  hypothesis (`irreversibility_without_loss`, `TM.irreversibility_without_loss_tm`): the information
  is not lost (Noether, a theorem), yet from one bit it is not recovered cheaply (HD, a hypothesis).
  The irreversibility is **without loss of information**.

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
  (`TM.decision_bennett_holds`): the verifier runs on a reversible machine, and still the arrow
  holds, because it is in the bit, not in the dynamics. A reversible simulation is a theorem for
  cslib's machines, with clean tapes (`TM.bennett_holds`), so only HD is assumed.
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
| Localization (1): time reversal, Noether | `Core/Dynamics.lean` | `koopman_noether`, `koopman_isometry_iff`, `ReversibleDynamics.card_image_iterate` | none |
| Localization (1): time translation, CHT | `Core/Dynamics.lean`, `TM/Dynamics.lean` | `noether_charge`, `does_not_know_the_time`, `homogenize_run`, `cube_law_clock`, `cht_time`, `does_not_know_the_time_tm`, `halts_soon_tm` | none |
| CHT tower, piece 1 | `Core/Dynamics.lean`, `TM/Dynamics.lean` | `cht_exponential_not_polynomial`, `cht_pspace` | none |
| **Localization (1), complete** | `Core/Dynamics.lean`, `TM/Dynamics.lean` | `localization_one`, `TM.localization_one_tm` | none |
| Irreversibility without loss | `Core/Dynamics.lean`, `TM/Dynamics.lean` | `irreversibility_without_loss`, `TM.irreversibility_without_loss_tm` | HD |
| Localization (2): full boundary, interpolation | `Core/Boundary.lean` | `full_boundary`, `interpolation`, `boundary_lower_bound` | none |
| Localization (3): one bit | `Core/Localization.lean`, `TM/Instance.lean` | `Model.searchEasy_iff_peqNP`, `TM.oneBit` | none |
| Localization theorem | `Core/Localization.lean`, `TM/Consequences.lean` | `localization`, `TM.localizationTM` | none |
| **Decision hypothesis (central)** | `Core/Decision.lean`, `TM/Decision.lean` | `Model.DecisionHypothesis`, `TM.DecisionHypothesis`, `decisionHypothesis_iff_arrow`, `decisionHypothesis_on_boundary` | defines HD |
| Second law 2.1 (Kelvin) | `Core/SecondLaw.lean`, `TM/Instance.lean` | `Model.Arrow`, `Model.kelvin`, `TM.kelvin`, `arrow_independent` | defines `Arrow` |
| Second law 2.2 | `TM/Law22.lean` | `Law22`, `Law22.arrow` (2.2 implies 2.1) | defines `Law22` |
| Bennett's reversible simulation, linear time, clean tapes | `TM/Instance.lean`, `TM/Bennett/*.lean` | `Bennett`, `ComputesCleanly`, `bennett_holds`, `revTM_correct_clean`, `reversible_verifier_holds`, `IsReversible.runFrom_injective`; mutant `BennettWeak`, `bennett_of_history_only`, `history_only_not_clean` | none |
| SAT, 3-SAT not in P | `TM/Consequences.lean` | `SAT_notMem_P`, `ThreeSAT_notMem_P` | `Arrow` |
| An NP-intermediate problem | `TM/Consequences.lean` | `exists_intermediate` (Ladner) | `Arrow` |
| ISING not in P (arbitrary graphs, binary weights; not Barahona's lattices) | `TM/Ising.lean`, `TM/Consequences.lean` | `Ising.ISING_npComplete`, `ISING_notMem_P` | `Arrow` |
| Consequences from HD | `TM/Decision.lean` | `SAT_notMem_P_of_decision`, `ThreeSAT_notMem_P_of_decision`, `exists_intermediate_of_decision`, `ISING_notMem_P_of_decision` | HD |
| HD and Bennett | `TM/Decision.lean`, `TM/Bennett/Discharge.lean` | `decision_bennett_holds` (and `decision_bennett`, with `Bennett` as an argument) | HD |
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

The only named hypotheses are HD (equivalently, the arrow) and law 2.2: definitions of type `Prop`,
taken as explicit arguments `(h : DecisionHypothesis)`, `(h : Arrow)`, `(h : Law22)`. The first two
are equivalent (`decisionHypothesis_iff_arrow`); HD is the central one, the arrow its statement as
`P ≠ NP`. None is a Lean `axiom`. `Bennett` used to be a fourth one; it is now a theorem
(`bennett_holds`, below), and the statements that take `(hB : Bennett)` (`reversible_verifier`,
`decision_bennett`) are kept, with versions without it (`reversible_verifier_holds`,
`decision_bennett_holds`). The end of
`TM/Consequences.lean` runs `#print axioms` on every main theorem under `#guard_msgs`, so the build
fails if any of them depends on anything other than `propext`, `Classical.choice` and
`Quot.sound`. The core also proves that the arrow is independent of the closure properties
(`arrow_independent`: one model satisfies them with `P = NP`, another with `P ≠ NP`), and that
without the arrow the consequences fail (`consequences_need_arrow`); the same holds for HD (`decisionHypothesis_independent`,
`consequences_need_decisionHypothesis`).

**Bennett's theorem is proved for cslib's machines** (`TM.bennett_holds : Bennett`, in
`TM/Bennett/Discharge.lean`): every function computed by a machine in time `t` is computed in time
and space linear in `n + t(n)` by a multi-tape machine with finitely many states whose step is
injective on **every** running configuration, not only the reachable ones, and which halts with
clean work tapes (`ComputesCleanly`: blank except a copy of the input and a constant mark, heads on
cell `0`). The construction, one file per step of the plan (`BENNETT.md`):

* `History.lean`: the machine with a history tape (a record per step, written on blank cells; a
  sink for the configurations no run reaches). A reversible machine never moves its input head off
  a blank (`IsReversible.staysOnBlank`), and that condition is necessary.
* `Copy.lean`: copying a word with the swap of the blank and the symbol (Bennett's XOR), and
  emitting it to the output tape.
* `Inverse.lean`, `Uncompute.lean`: the reversible inverse of the history machine, `3 t + 2` steps
  for `t`.
* `Compose.lean`: cslib's sequential composition keeps reversibility when the hand-off is
  distinguishable (and the condition is necessary).
* `Machine.lean`: Bennett's machine, compute, emit, uncompute, in `4 t + 2 |w| + 6` steps, with
  every work tape blank at the end.
* `Prepare.lean`, `Normal.lean`: a reversible machine writes the input on a virtual input tape
  (cslib's `inputFromTape`, used unchanged), and every machine has a normal form that never moves
  nor reads its input head and leaves its result on a work tape (cslib's `outputToTape` and
  `rewindWork`, used unchanged).
* `Discharge.lean`: the two together, with the final configuration exactly (`revTM_correct_clean`,
  in `2 n + 4 t + 6 |y| + 21` steps; at most `2 n + 10 t(n) + 21` for a machine running in time
  `t`), and the space linear in the time. Also the mutant: the same machine without the
  uncomputation (`histOnlyTM`) is reversible and correct but leaves its history, so it proves the
  old `BennettWeak` and not `Bennett`.

The abstract shadow of the construction is also proved in the core (`historyDynamics`,
`history_simulates`, `history_recovers`). Every file of `TM/Bennett` ends with `#print axioms`
under `#guard_msgs` and one mutant per central theorem.

The end of `TM/Dynamics.lean` does the same for the 37 central theorems of the complete first
localization (both layers), and contains one mutant per central theorem (18 in all: a hypothesis
dropped or a conclusion strengthened), each under `fail_if_success`, so the build fails if any of
them starts to elaborate.

Not here, on purpose: the Boolean dichotomy (Schaefer), whose formalization rests on further
assumptions, and the other companion material of the essay.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.36.0-rc2`)
and Mathlib (`bbff2954`) are the ones cslib-frontier `99f02811` uses.

```sh
lake exe cache get   # prebuilt Mathlib; Mathlib is never compiled here
lake build
```

A clean `lake build` compiles 345 vendored modules (312 from cslib-frontier, 33 from cslib) and 29
modules of this project (nine of them the proof of Bennett's theorem, three the fidelity battery), and no Mathlib module. On an Apple M1 Pro with `LEAN_NUM_THREADS=3` it
takes 5 min 47 s of wall-clock time (measured on 25 November 2026, before the two modules of the
decision hypothesis, which add about 45 s, and the two of the complete first localization, which add
about 1 min 10 s); the modules of this project
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
