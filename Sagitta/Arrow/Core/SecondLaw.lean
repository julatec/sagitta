/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.Localization

/-!
# The second law (law 2.1): the arrow is a hypothesis

**Second law, Kelvin's form (law 2.1).** *It is impossible to have an efficient process whose only
effect is to convert a "yes" into its witness.*

The localization theorem shows that the only place left for an asymmetry is the erasure of the
boundary down to one bit, and that there the asymmetry is exactly `P ≠ NP`. The second law states
that the asymmetry is real. It is **not proved**: it is the open problem `P ≠ NP` (worst-case
version). Here it is the definition `Model.Arrow`, a `Prop`, and every theorem that depends on it
takes it as an explicit argument `(h : M.Arrow)`. It is never a Lean axiom.

* `Model.Arrow`: `P ≠ NP` in the model.
* `Model.kelvin`: the arrow is equivalent to Kelvin's form: not every search problem with
  efficiently checkable solutions can be solved efficiently.
* `Model.arrow_iff_not_InP`: with any `NP`-complete problem `B`, the arrow says `B ∉ P`.
* `arrow_independent`: the closure properties of a `Model` decide nothing about the arrow. A
  one-problem model satisfies them with `P = NP` (`collapsedModel`), a two-problem model satisfies
  them with `P ≠ NP` (`separatedModel`). So the second law is not a consequence of the first laws
  and the localization: it is a genuine extra hypothesis.

Law 2.2 (the weak exponential-time hypothesis, equivalently Stearns and Hunt's SH) is a
statement about running times, so it is stated for Turing machines:
`Sagitta.Arrow.TM.Law22`.
-/

namespace Sagitta.Arrow.Model

universe u

variable (M : Model.{u})

set_option linter.dupNamespace false in
/-- **The arrow (law 2.1): `P ≠ NP`**, in its worst-case version. This is a HYPOTHESIS: a `Prop`
that every theorem depending on it takes as an explicit argument. It is not an axiom. -/
def Arrow : Prop := ¬M.PeqNP

variable {M}

/-- **Kelvin's form of the second law.** The arrow holds exactly when it is impossible to have an
efficient process whose only effect is to convert a "yes" into its witness: some search problem
with efficiently checkable solutions has no efficient solver. -/
theorem kelvin : M.Arrow ↔ ¬M.SearchEasy :=
  not_congr M.searchEasy_iff_peqNP.symm

/-- With the arrow, an `NP`-complete problem is not in `P`. -/
theorem arrow_iff_not_InP {B : M.Problem} (hB : M.NPComplete B) : M.Arrow ↔ ¬M.InP B :=
  not_congr hB.InP_iff.symm

end Sagitta.Arrow.Model

namespace Sagitta.Arrow

/-! ### The arrow is independent of the closure properties -/

/-- A model with a single problem, in `P`: the closure properties hold and `P = NP`. -/
def collapsedModel : Model.{0} where
  Problem := Unit
  Search := Unit
  Reduces _ _ := True
  reduces_refl _ := trivial
  reduces_trans _ _ := trivial
  InP _ := True
  InNP _ := True
  P_subset_NP _ := trivial
  InP_of_reduces _ _ := trivial
  InFNP _ := True
  InFP _ := True
  domain _ := ()
  domain_NP _ := trivial
  domain_P _ := trivial
  exists_search _ := ⟨(), trivial, rfl⟩
  prefixProblem _ := ()
  prefix_NP _ := trivial
  search_of_prefix _ _ := trivial

/-- A model with two problems, an easy one (`false`) and a hard one (`true`): the closure
properties hold and `P ≠ NP`. A problem reduces to another when it is at most as hard. -/
def separatedModel : Model.{0} where
  Problem := Bool
  Search := Bool
  Reduces A B := B = false → A = false
  reduces_refl _ := id
  reduces_trans hAB hBC := hAB ∘ hBC
  InP A := A = false
  InNP _ := True
  P_subset_NP _ := trivial
  InP_of_reduces hAB hB := hAB hB
  InFNP _ := True
  InFP R := R = false
  domain := id
  domain_NP _ := trivial
  domain_P h := h
  exists_search {A} _ := ⟨A, trivial, rfl⟩
  prefixProblem := id
  prefix_NP _ := trivial
  search_of_prefix _ h := h

/-- **The arrow is independent of the closure properties**: they hold in a model without the
arrow and in a model with it. -/
theorem arrow_independent : ¬collapsedModel.Arrow ∧ separatedModel.Arrow :=
  ⟨fun h => h fun _ _ => trivial, fun h => Bool.true_eq_false_eq_False (h true trivial)⟩

end Sagitta.Arrow
