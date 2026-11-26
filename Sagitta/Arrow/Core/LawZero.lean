/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.Base

/-!
# The zeroth law: reductions are transitive

**Zeroth law.** *If `A` reduces to `B` and `B` reduces to `C`, then `A` reduces to `C`.* It plays
the role of the zeroth law of thermodynamics (thermal equilibrium is transitive): it is what makes
"being as hard as" a preorder, so that hardness can be compared at all.

In the abstract model it is the closure property `Model.reduces_trans`; for Turing machines it is
cslib-frontier's `Cslib.Complexity.PolyTimeReducible.trans` (see `Sagitta.Arrow.TM.lawZero`).
Its consequences used later: `NP`-completeness propagates along reductions, and a reduction to an
efficiently decidable problem gives an efficient decider.
-/

namespace Sagitta.Arrow.Model

universe u

variable {M : Model.{u}}

/-- **Zeroth law** (transitivity of `≤ₚ`): if `A ≤ B` and `B ≤ C`, then `A ≤ C`. -/
theorem lawZero {A B C : M.Problem} (hAB : M.Reduces A B) (hBC : M.Reduces B C) :
    M.Reduces A C :=
  M.reduces_trans hAB hBC

/-- `NP`-completeness propagates along reductions that stay inside `NP`. -/
theorem NPComplete.of_reduces {B C : M.Problem} (hB : M.NPComplete B) (hBC : M.Reduces B C)
    (hC : M.InNP C) : M.NPComplete C :=
  ⟨hC, fun A hA => lawZero (hB.2 A hA) hBC⟩

/-- **An `NP`-complete problem in `P` gives `P = NP`.** -/
theorem NPComplete.peqNP_of_InP {B : M.Problem} (hB : M.NPComplete B) (h : M.InP B) : M.PeqNP :=
  fun A hA => M.InP_of_reduces (hB.2 A hA) h

/-- An `NP`-complete problem is in `P` exactly when `P = NP`. -/
theorem NPComplete.InP_iff {B : M.Problem} (hB : M.NPComplete B) : M.InP B ↔ M.PeqNP :=
  ⟨hB.peqNP_of_InP, fun h => h B hB.1⟩

end Sagitta.Arrow.Model
