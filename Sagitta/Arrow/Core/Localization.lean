/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.LawZero
import Sagitta.Arrow.Core.Reversible
import Sagitta.Arrow.Core.Boundary

/-!
# Locating the arrow

Where is the asymmetry between going forward (from a witness to "yes") and going backward (from
"yes" to a witness)? The **localization theorem** (`localization`) answers in three parts.

1. **Not in the dynamics.** A reversible dynamics goes back at the same cost as it goes forward
   (`ReversibleDynamics.back_iterate_step_iterate`, `ReversibleDynamics.costBack_eq_costForward`),
   and any dynamics becomes reversible once it keeps its history (`history_recovers`). This part is
   completed in `Core/Dynamics.lean` (and `TM/Dynamics.lean` for cslib's machines) with the two
   symmetries of time and their Noether charges: time reversal conserves the information (discrete
   Noether, Koopman), time translation makes the system blind to the clock and charges the clock to
   memory (the CHT, the cube law, `2^S`). Neither decides the arrow
   (`Dynamics.localization_one`, `TM.localization_one_tm`).
2. **Not with the full boundary.** If the whole witness is kept, going back is one verification
   (`full_boundary`); with `m` of `n` bits kept, at most `2 ^ (n - m)` verifications
   (`interpolation`), tight in a black box (`boundary_lower_bound`).
3. **Only in the erasure down to one bit.** When all that is kept is the bit "yes", going back
   cheaply for every search problem is *equivalent* to `P = NP` (`Model.searchEasy_iff_peqNP`).
   This is proved here from the closure properties of an abstract `Model`; for Turing machines it
   is cslib-frontier's `Cslib.Complexity.FNP_subset_FPSearch_iff`.

In words: *the arrow is not in the laws of motion, nor in the state as long as it is kept whole; it
lives entirely in forgetting the boundary, and its strength there is exactly the question
`P` versus `NP`.*
-/

namespace Sagitta.Arrow

namespace Model

universe u

variable (M : Model.{u})

/-- **Part (3): with one bit, going back is cheap exactly when `P = NP`.** Search reduces to
decision through the prefix problem, and decision reduces to search through the domain. -/
theorem searchEasy_iff_peqNP : M.SearchEasy ↔ M.PeqNP := by
  constructor
  · intro h A hA
    obtain ⟨R, hR, rfl⟩ := M.exists_search hA
    exact M.domain_P (h R hR)
  · intro h R hR
    exact M.search_of_prefix hR (h _ (M.prefix_NP hR))

end Model

/-- **The localization theorem.** The conjunction of the three parts:

1. a reversible dynamics, run back from its final state, recovers the initial state at the same
   cost as running it forward;
2. with the full boundary (the whole witness) going back is one verification, and with `m` of the
   `n` bits it is at most `2 ^ (n - m)` verifications;
3. with one bit (only the answer "yes") going back is cheap for every search problem if and only if
   `P = NP`.
-/
theorem localization (M : Model) :
    (∀ (σ : Type) (D : ReversibleDynamics σ) (n : ℕ) (x : σ),
        D.back^[n] (D.step^[n] x) = x ∧ D.costBack n = D.costForward n) ∧
    (∀ (V : List Bool → Bool) (w : List Bool), V w = true → complete V w 0 = (some w, 1)) ∧
    (∀ (V : List Bool → Bool) (n : ℕ) (u : List Bool), u.length ≤ n →
        (∃ s : List Bool, u.length + s.length = n ∧ V (u ++ s) = true) →
        (∃ w, (complete V u (n - u.length)).1 = some w ∧ V w = true) ∧
          (complete V u (n - u.length)).2 ≤ 2 ^ (n - u.length)) ∧
    (M.SearchEasy ↔ M.PeqNP) := by
  refine ⟨fun σ D n x => ⟨D.back_iterate_step_iterate n x, D.costBack_eq_costForward n⟩,
    full_boundary, fun V n u hm hex => ?_, M.searchEasy_iff_peqNP⟩
  obtain ⟨⟨w, hw, hV, -⟩, -⟩ := interpolation V n u hm hex 1
  exact ⟨⟨w, hw, hV⟩, complete_calls_le V _ u⟩

end Sagitta.Arrow
