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
