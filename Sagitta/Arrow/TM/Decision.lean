/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.Decision
import Sagitta.Arrow.TM.Consequences

/-!
# The decision hypothesis, for Turing machines

The central hypothesis of the project, for the multi-tape Turing machines of cslib (see
`Sagitta/Arrow/Core/Decision.lean` for the discussion).

**The decision hypothesis (HD).** *The decision question breaks the symmetry of time: reducing the
final state to one bit is the boundary condition that breaks it, and that breaking has a cost.*
Here: there is a polynomial-time verifier `V` with certificates of length `p` such that no
polynomial-time machine, given only an instance `a` (whose one observable bit is
`a ∈ searchDomain (verifierSearch enc p V)`), returns a certificate whenever one exists.

## The chain

```
HD  --(localization, part 3: FNP_subset_FPSearch_iff)-->  Arrow  -->  SAT, 3-SAT, ISING ∉ P;
                                                                       an NP-intermediate problem
```

* `DecisionHypothesis`: HD, stated with a verifier and a solver, not with `P` and `NP`.
* `decisionHypothesis_iff_arrow`: HD is equivalent to the arrow. HD gives the arrow because the
  search problem of a verifier is in `FNP` (`verifierSearch_mem_FNP`) and the localization, part
  (3), turns a failure of search into `P ≠ NP`; the arrow gives HD because a problem in
  `NP \ P` has a verifier, and a solver of its search problem would decide it
  (`searchDomain_mem_P`).
* The consequences, re-stated from HD: `SAT_notMem_P_of_decision`,
  `ThreeSAT_notMem_P_of_decision`, `exists_intermediate_of_decision`,
  `ISING_notMem_P_of_decision`, `not_searchEasy_of_decision`. The versions with the arrow stay in
  `TM/Consequences.lean`.
* `decision_bennett`: HD and Bennett together, the analogue of the past hypothesis and reversible
  dynamics giving the second law: the verifier of every `NP` problem runs on a reversible machine
  (no arrow in the dynamics), and still the arrow holds (it is in the bit).

## Honesty

HD is *equivalent* to the arrow, and so to `P ≠ NP` (worst case). It is the conceptual formulation
of the same open problem, not a stronger hypothesis. It is a `Prop` taken as an explicit argument,
never a Lean axiom: the `#print axioms` at the end of this file show it, and the mutant shows that
without `h` the consequence does not go through.
-/

namespace Sagitta.Arrow.TM

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Cslib.Logic.PL

/-- **The decision hypothesis (HD), for Turing machines**, stated at the boundary: for some
encoding `enc`, some polynomial `p` and some polynomial-time verifier `V`, no polynomial-time
function reconstructs, from the instance alone, a certificate accepted by `V` whenever there is
one. The negation of efficient search from one bit. A HYPOTHESIS: a `Prop` taken as an explicit
argument, never an axiom. -/
def DecisionHypothesis : Prop :=
  ∃ (α : Type) (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      ¬∃ f : α → Option (List Bool), ComputableInPolyTime f enc (encOption encBits) ∧
        SolvesSearch (verifierSearch enc p V) f

/-- **HD is equivalent to the arrow**, by the localization, part (3). -/
theorem decisionHypothesis_iff_arrow : DecisionHypothesis ↔ Arrow := by
  constructor
  · rintro ⟨α, enc, p, V, hV, hno⟩
    refine kelvin.2 fun hall => hno ?_
    exact (hall enc (verifierSearch_mem_FNP hV)).2
  · intro h
    rw [arrow_iff] at h
    by_contra hD
    refine h fun {α} enc A hA => ?_
    obtain ⟨p, V, hV, hAV⟩ := hA
    by_contra hnA
    refine hD ⟨α, enc, p, V, hV, ?_⟩
    rintro ⟨f, hf, hs⟩
    exact hnA (hAV.searchDomain_eq ▸ searchDomain_mem_P ⟨verifierSearch_mem_FNP hV, f, hf, hs⟩)

/-- **HD gives the arrow.** -/
theorem DecisionHypothesis.arrow (h : DecisionHypothesis) : Arrow :=
  decisionHypothesis_iff_arrow.1 h

/-- The two formulations of HD agree: the one stated with verifiers and solvers, and the core's,
for `tmModel`. -/
theorem decisionHypothesis_iff_model : DecisionHypothesis ↔ tmModel.DecisionHypothesis :=
  decisionHypothesis_iff_arrow.trans Model.decisionHypothesis_iff_arrow.symm

/-! ## Consequences, from HD -/

/-- **With HD, SAT is not in `P`.** -/
theorem SAT_notMem_P_of_decision (h : DecisionHypothesis) : SAT ∉ P encCNF :=
  SAT_notMem_P h.arrow

/-- **With HD, 3-SAT is not in `P`.** -/
theorem ThreeSAT_notMem_P_of_decision (h : DecisionHypothesis) : ThreeSAT ∉ P encCNF :=
  ThreeSAT_notMem_P h.arrow

/-- **With HD, there is an `NP`-intermediate problem** (Ladner). -/
theorem exists_intermediate_of_decision (h : DecisionHypothesis) :
    ∃ L : Set (List Bool), L ∈ NP encBits ∧ L ∉ P encBits ∧ ¬NPComplete encBits L :=
  exists_intermediate h.arrow

/-- The same, in the vocabulary of the core. -/
theorem exists_intermediate_model_of_decision (h : DecisionHypothesis) :
    ∃ A, tmModel.Intermediate A :=
  exists_intermediate_model h.arrow

/-- **With HD, the Ising ground state is not in `P`.** -/
theorem ISING_notMem_P_of_decision (h : DecisionHypothesis) : Ising.ISING ∉ P Ising.encIsing :=
  ISING_notMem_P h.arrow

/-- **With HD, some `FNP` search problem is not in `FPSearch`** (Kelvin's form). -/
theorem not_searchEasy_of_decision (h : DecisionHypothesis) :
    ¬∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc :=
  not_searchEasy h.arrow

/-- **Law 2.2 implies HD**, through the arrow. -/
theorem decisionHypothesis_of_law22 (h : Law22) : DecisionHypothesis :=
  decisionHypothesis_iff_arrow.2 (arrow_of_law22 h)

/-- **HD and Bennett: the boundary condition and the reversible dynamics.** As the past hypothesis
and reversible dynamics give the second law, HD and Bennett give the arrow and locate it: every
`NP` problem has a verifier run by a reversible machine in polynomial time and space (the dynamics
carries no arrow), and still `P ≠ NP` (the arrow is in the reduction to one bit). The arrow itself
already follows from HD alone; Bennett says where it is not. -/
theorem decision_bennett (h : DecisionHypothesis) (hB : Bennett) :
    Arrow ∧
      ∀ {α : Type} {enc : α ↪ List Bool} {A : Set α}, A ∈ NP enc →
        ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool), IsVerifier enc p V A ∧
          ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State)
            (t s : ℕ → ℕ),
            IsReversible tm ∧ PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
              tm.ComputesFunInTimeAndSpace (encPair enc encBits) encBool V
                (fun a => t ((encPair enc encBits) a).length)
                (fun a => s ((encPair enc encBits) a).length) :=
  ⟨h.arrow, fun hA => reversible_verifier hB hA⟩

end Sagitta.Arrow.TM

/-! ## HD is not an axiom

Three checks, each under `#guard_msgs`, so the build fails if any of them changes.

1. `DecisionHypothesis` (in both layers) is a *definition* in the environment, not an `axiom`
   declaration.
2. `#print axioms` on the equivalence and on every consequence lists only `propext`,
   `Classical.choice` and `Quot.sound`: neither HD nor the arrow is among them, because the
   theorems take them as arguments.
3. **The mutant**: the same consequence without the hypothesis `h` does not elaborate; Lean is
   left with the goal `DecisionHypothesis`, which nothing in the environment proves. -/

open Lean in
/-- Fails unless the constant is a definition (and so not an axiom). -/
def checkIsDefinition (n : Name) : CoreM Unit := do
  match (← getConstInfo n) with
  | .defnInfo _ => logInfo m!"{n} is a definition, not an axiom"
  | _ => throwError m!"{n} is not a definition"

/-- info: Sagitta.Arrow.TM.DecisionHypothesis is a definition, not an axiom -/
#guard_msgs in
#eval checkIsDefinition `Sagitta.Arrow.TM.DecisionHypothesis
/-- info: Sagitta.Arrow.Model.DecisionHypothesis is a definition, not an axiom -/
#guard_msgs in
#eval checkIsDefinition `Sagitta.Arrow.Model.DecisionHypothesis

/-! `#print axioms` on HD itself: a definition depends on the axioms used to *state* it (here the
classical ones behind the encodings), and on nothing else. Its own name is not an axiom. -/

/-- info: 'Sagitta.Arrow.TM.DecisionHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.DecisionHypothesis
/-- info: 'Sagitta.Arrow.Model.DecisionHypothesis' does not depend on any axioms -/
#guard_msgs in
#print axioms Sagitta.Arrow.Model.DecisionHypothesis

/-- info: 'Sagitta.Arrow.Model.decisionHypothesis_iff_not_searchEasy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Model.decisionHypothesis_iff_not_searchEasy
/-- info: 'Sagitta.Arrow.Model.decisionHypothesis_iff_arrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Model.decisionHypothesis_iff_arrow
/-- info: 'Sagitta.Arrow.Model.not_InP_of_NPComplete_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Model.not_InP_of_NPComplete_of_decision
/-- info: 'Sagitta.Arrow.Model.not_searchEasy_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Model.not_searchEasy_of_decision
/-- info: 'Sagitta.Arrow.Model.not_reduces_of_InP_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Model.not_reduces_of_InP_of_decision
/-- info: 'Sagitta.Arrow.decisionHypothesis_on_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.decisionHypothesis_on_boundary
/-- info: 'Sagitta.Arrow.decisionHypothesis_independent' does not depend on any axioms -/
#guard_msgs in
#print axioms Sagitta.Arrow.decisionHypothesis_independent
/-- info: 'Sagitta.Arrow.consequences_need_decisionHypothesis' does not depend on any axioms -/
#guard_msgs in
#print axioms Sagitta.Arrow.consequences_need_decisionHypothesis
/-- info: 'Sagitta.Arrow.TM.decisionHypothesis_iff_arrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.decisionHypothesis_iff_arrow
/-- info: 'Sagitta.Arrow.TM.decisionHypothesis_iff_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.decisionHypothesis_iff_model
/-- info: 'Sagitta.Arrow.TM.SAT_notMem_P_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.SAT_notMem_P_of_decision
/-- info: 'Sagitta.Arrow.TM.ThreeSAT_notMem_P_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.ThreeSAT_notMem_P_of_decision
/-- info: 'Sagitta.Arrow.TM.exists_intermediate_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.exists_intermediate_of_decision
/-- info: 'Sagitta.Arrow.TM.exists_intermediate_model_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.exists_intermediate_model_of_decision
/-- info: 'Sagitta.Arrow.TM.ISING_notMem_P_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.ISING_notMem_P_of_decision
/-- info: 'Sagitta.Arrow.TM.not_searchEasy_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.not_searchEasy_of_decision
/-- info: 'Sagitta.Arrow.TM.decisionHypothesis_of_law22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.decisionHypothesis_of_law22
/-- info: 'Sagitta.Arrow.TM.decision_bennett' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.decision_bennett

section Mutant

open Cslib.Complexity

/-- error: Tactic `assumption` failed

⊢ Sagitta.Arrow.TM.DecisionHypothesis -/
#guard_msgs in
example : SAT ∉ P encCNF := Sagitta.Arrow.TM.SAT_notMem_P_of_decision (by assumption)

end Mutant
