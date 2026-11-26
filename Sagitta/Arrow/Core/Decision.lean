/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.Consequences

/-!
# The decision hypothesis: the central hypothesis

**The decision hypothesis (HD).** *The symmetry of time is broken by the decision question.
Reducing the final state to one bit is the boundary condition that breaks the symmetry, and that
breaking has a cost.* Formally: for some search problem with efficiently checkable solutions (a
polynomial verifier), observing only the bit "this instance has a solution" does not let an
efficient procedure reconstruct a solution.

## The chain

```
HD  --(localization, part 3)-->  arrow (P ≠ NP)  -->  consequences
```

HD is stated at the *boundary*, not as `P ≠ NP`. In the core, a search problem `R` with
`M.InFNP R` is the forward process (a witness is checked by an efficient verifier), and its
domain `M.domain R` is what is left once the boundary is erased down to one bit
(`Core/Boundary.lean`: with the full boundary, going back costs one verification,
`full_boundary`; with `m` of `n` bits, `2 ^ (n - m)`, `interpolation`, tight in a black box,
`boundary_lower_bound`). HD says that at the end `m = 0` of that interpolation, going back is
not efficient for every verifier. The localization, part (3) (`Model.searchEasy_iff_peqNP`), turns
that statement into the arrow, and the consequences follow from the arrow.

## The parallel with physics

In statistical mechanics, the second law is not a consequence of the dynamics, which is
reversible. It follows from the reversible dynamics *together with* a boundary condition, the
past hypothesis (the universe started in a state of low entropy). Here the roles are the same:
Bennett's hypothesis (`Sagitta.Arrow.TM.Bennett`) makes the dynamics of verification reversible,
so it carries no arrow (localization, part 1), and the decision hypothesis is the boundary
condition. HD plus Bennett give the arrow, and they also say *where* it is: not in the dynamics,
only in the reduction of the final state to one bit. Formally the arrow already follows from HD
alone (`decisionHypothesis_iff_arrow`); Bennett's role is to rule out the other places.

## The three senses of "decision"

1. **The decision problem**: the question has a yes/no answer, "does `a` have a solution?", the
   domain `M.domain R`.
2. **The erasure of the boundary**: deciding is reducing the final state of the forward process,
   which still contained the witness, to that one bit. This is the boundary condition.
3. **The choice of the bit**: which witness produced the "yes" is forgotten; going back has to
   choose again among all the candidates, and HD says that this choice cannot be made
   efficiently.

## Honesty

HD is *equivalent* to the arrow (`decisionHypothesis_iff_arrow`), and so to `P ≠ NP` in its
worst-case version. It is not a stronger hypothesis and not a weaker one: it is the conceptual
formulation of the same open problem, stated where the localization theorem says that the
asymmetry lives. Like the arrow, it is a `Prop` taken as an explicit argument `(h : ...)`, never a
Lean axiom, and it is independent of the closure properties of a `Model`
(`decisionHypothesis_independent`).
-/

namespace Sagitta.Arrow.Model

universe u

variable (M : Model.{u})

/-- **The decision hypothesis (HD)**, stated at the boundary: some search problem `R` with
efficiently checkable solutions (`M.InFNP R`, a polynomial verifier) cannot be solved
efficiently from its instances alone, that is, from the one bit "the instance is in
`M.domain R`" no efficient procedure reconstructs a witness (`¬M.InFP R`). A HYPOTHESIS: a `Prop`
that every theorem depending on it takes as an explicit argument. It is not an axiom. -/
def DecisionHypothesis : Prop := ∃ R, M.InFNP R ∧ ¬M.InFP R

variable {M}

/-- HD is the negation of efficient search from one bit. -/
theorem decisionHypothesis_iff_not_searchEasy : M.DecisionHypothesis ↔ ¬M.SearchEasy := by
  unfold DecisionHypothesis SearchEasy
  constructor
  · rintro ⟨R, hR, hnR⟩ h
    exact hnR (h R hR)
  · intro h
    by_contra hne
    exact h fun R hR => by
      by_contra hnR
      exact hne ⟨R, hR, hnR⟩

/-- **HD is equivalent to the arrow**, by the localization, part (3)
(`Model.searchEasy_iff_peqNP`, through Kelvin's form `Model.kelvin`). -/
theorem decisionHypothesis_iff_arrow : M.DecisionHypothesis ↔ M.Arrow :=
  decisionHypothesis_iff_not_searchEasy.trans kelvin.symm

/-- **HD gives the arrow.** -/
theorem DecisionHypothesis.arrow (h : M.DecisionHypothesis) : M.Arrow :=
  decisionHypothesis_iff_arrow.1 h

/-! ### Consequences, from HD -/

/-- **With HD, no `NP`-complete problem is in `P`.** -/
theorem not_InP_of_NPComplete_of_decision (h : M.DecisionHypothesis) {B : M.Problem}
    (hB : M.NPComplete B) : ¬M.InP B :=
  not_InP_of_NPComplete h.arrow hB

/-- **With HD, going back from "yes" is not always cheap.** -/
theorem not_searchEasy_of_decision (h : M.DecisionHypothesis) : ¬M.SearchEasy :=
  not_searchEasy h.arrow

/-- With HD, an `NP`-complete problem does not reduce to a problem in `P`. -/
theorem not_reduces_of_InP_of_decision (h : M.DecisionHypothesis) {B C : M.Problem}
    (hB : M.NPComplete B) (hC : M.InP C) : ¬M.Reduces B C :=
  not_reduces_of_InP h.arrow hB hC

end Sagitta.Arrow.Model

namespace Sagitta.Arrow

/-- **Where HD lives, on the boundary.** The two ends of the interpolation of `Core/Boundary.lean`
and the decision hypothesis at the second one:

1. with the full boundary (the whole witness kept), going back is one verification;
2. with nothing but the bit (`m = 0`), a black-box search over the `2 ^ k` completions asks about
   all of them in the worst case;
3. whether a non-black-box procedure does better from that bit, for every verifier, is what HD
   denies, and HD is the arrow. -/
theorem decisionHypothesis_on_boundary (M : Model) :
    (∀ (V : List Bool → Bool) (w : List Bool), V w = true → complete V w 0 = (some w, 1)) ∧
    (∀ (k : ℕ) (t : QueryTree (List.Vector Bool k)), QueryTree.DecidesExists t →
        2 ^ k ≤ QueryTree.cost t (fun _ => false)) ∧
    (M.DecisionHypothesis ↔ M.Arrow) :=
  ⟨full_boundary, boundary_lower_bound, Model.decisionHypothesis_iff_arrow⟩

/-- **HD is independent of the closure properties**, like the arrow: it fails in
`collapsedModel` and holds in `separatedModel`. -/
theorem decisionHypothesis_independent :
    ¬collapsedModel.DecisionHypothesis ∧ separatedModel.DecisionHypothesis :=
  ⟨fun ⟨_, _, hn⟩ => hn trivial, ⟨true, trivial, fun h => Bool.noConfusion h⟩⟩

/-- **Control: the consequences need HD.** In `collapsedModel` HD fails, and the only problem is
`NP`-complete and in `P`. -/
theorem consequences_need_decisionHypothesis :
    ¬collapsedModel.DecisionHypothesis ∧ collapsedModel.NPComplete () ∧ collapsedModel.InP () :=
  ⟨decisionHypothesis_independent.1, consequences_need_arrow.1, consequences_need_arrow.2.1⟩

end Sagitta.Arrow
