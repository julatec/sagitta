/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.FirstLaw
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# The boundary: how much of the witness is kept

The forward process goes from a witness `w` of `n` bits to the bit "yes" (`V w = true`). Going
backwards means recovering a witness from what is left. This file measures the cost of going back
as a function of how much of the witness survives, the **boundary** that was kept.

* `complete V u k` searches for a witness that extends the known bits `u` by `k` unknown bits,
  calling the verifier `V` on candidates; it returns the witness found and the number of calls.
  It is sound (`complete_sound`), finds a witness whenever one exists (`complete_isSome`), and
  makes at most `2 ^ k` calls (`complete_calls_le`).
* **The full boundary** (`full_boundary`): when all `n` bits are kept, one call suffices.
* **The interpolation** (`interpolation`): with `m` of the `n` bits kept, at most
  `2 ^ (n - m)` calls, that is, cost `≤ 2 ^ (n - m) · (cost of the verifier)`.
* **And it is tight in a black box** (`boundary_lower_bound`): by the first law, any query
  algorithm that decides whether the known bits can be completed asks, in the worst case, about all
  `2 ^ k` completions.

The two ends: with the full boundary, going back costs one verification; with nothing but the bit
"yes" (`m = 0`), the black-box cost is `2 ^ n`, and whether a non-black-box algorithm can do better
is exactly the question `P = NP` (`Sagitta.Arrow.Model.searchEasy_iff_peqNP`).
-/

namespace Sagitta.Arrow

/-- **Complete the known bits `u` by `k` more bits**, trying `false` before `true` and stopping at
the first witness. Returns the witness found (if any) and the number of calls to `V`. -/
def complete (V : List Bool → Bool) (u : List Bool) : ℕ → Option (List Bool) × ℕ
  | 0 => (if V u then some u else none, 1)
  | k + 1 =>
    match complete V (u ++ [false]) k with
    | (some w, c) => (some w, c)
    | (none, c) => ((complete V (u ++ [true]) k).1, c + (complete V (u ++ [true]) k).2)

/-- **At most `2 ^ k` calls.** -/
theorem complete_calls_le (V : List Bool → Bool) : ∀ (k : ℕ) (u : List Bool),
    (complete V u k).2 ≤ 2 ^ k
  | 0, u => by simp [complete]
  | k + 1, u => by
    have h0 := complete_calls_le V k (u ++ [false])
    have h1 := complete_calls_le V k (u ++ [true])
    simp only [complete]
    split <;> simp_all [pow_succ] <;> omega

/-- **Sound**: what is found is a witness extending `u` by exactly `k` bits. -/
theorem complete_sound (V : List Bool → Bool) : ∀ (k : ℕ) (u w : List Bool),
    (complete V u k).1 = some w → V w = true ∧ ∃ s : List Bool, s.length = k ∧ w = u ++ s
  | 0, u, w, h => by
    simp only [complete] at h
    split at h
    · cases h; exact ⟨by assumption, [], rfl, by simp⟩
    · cases h
  | k + 1, u, w, h => by
    simp only [complete] at h
    rcases hr : complete V (u ++ [false]) k with ⟨_ | w', c⟩ <;> simp only [hr, Option.some.injEq] at h
    · obtain ⟨hV, s, hs, rfl⟩ := complete_sound V k (u ++ [true]) w h
      exact ⟨hV, true :: s, by simp [hs], by simp⟩
    · subst h
      obtain ⟨hV, s, hs, rfl⟩ := complete_sound V k (u ++ [false]) w' (by rw [hr])
      exact ⟨hV, false :: s, by simp [hs], by simp⟩

/-- **Complete**: if some extension of `u` by `k` bits is a witness, one is found. -/
theorem complete_isSome (V : List Bool → Bool) : ∀ (k : ℕ) (u : List Bool),
    (∃ s : List Bool, s.length = k ∧ V (u ++ s) = true) → ((complete V u k).1).isSome
  | 0, u, ⟨s, hs, hV⟩ => by
    rw [List.length_eq_zero_iff] at hs
    subst hs
    simp only [List.append_nil] at hV
    simp [complete, hV]
  | k + 1, u, ⟨s, hs, hV⟩ => by
    obtain ⟨b, s, rfl⟩ : ∃ b s', s = b :: s' := by
      cases s with
      | nil => simp at hs
      | cons b s' => exact ⟨b, s', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hs
    simp only [complete]
    rcases hr : complete V (u ++ [false]) k with ⟨_ | w', c⟩
    · cases b
      · have := complete_isSome V k (u ++ [false]) ⟨s, hs, by simpa using hV⟩
        rw [hr] at this
        simp at this
      · simpa using complete_isSome V k (u ++ [true]) ⟨s, hs, by simpa using hV⟩
    · simp

/-- **The full boundary**: when the whole witness is kept, going back is one verification. -/
theorem full_boundary (V : List Bool → Bool) (w : List Bool) (hw : V w = true) :
    complete V w 0 = (some w, 1) := by
  simp [complete, hw]

/-- **The interpolation**: with `m` of the `n` bits of the witness kept (the prefix `u`), going
back finds a witness with at most `2 ^ (n - m)` calls to the verifier, so with cost at most
`2 ^ (n - m) · c` when one call costs `c`. -/
theorem interpolation (V : List Bool → Bool) (n : ℕ) (u : List Bool) (hm : u.length ≤ n)
    (hex : ∃ s : List Bool, u.length + s.length = n ∧ V (u ++ s) = true) (c : ℕ) :
    (∃ w, (complete V u (n - u.length)).1 = some w ∧ V w = true ∧ w.length = n ∧ u <+: w) ∧
      (complete V u (n - u.length)).2 * c ≤ 2 ^ (n - u.length) * c := by
  refine ⟨?_, Nat.mul_le_mul_right c (complete_calls_le V _ u)⟩
  obtain ⟨s, hs, hV⟩ := hex
  have hsome := complete_isSome V (n - u.length) u ⟨s, by omega, hV⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hVw, s', hs', rfl⟩ := complete_sound V _ u w hw
  exact ⟨u ++ s', hw, hVw, by simp [hs']; omega, List.prefix_append u s'⟩

/-- **The interpolation is tight in a black box.** Any query algorithm over the `2 ^ k` possible
completions that decides whether one of them is good asks, on the all-`false` oracle, about all
`2 ^ k`. -/
theorem boundary_lower_bound (k : ℕ) (t : QueryTree (List.Vector Bool k))
    (ht : QueryTree.DecidesExists t) : 2 ^ k ≤ QueryTree.cost t (fun _ => false) := by
  classical
  have := QueryTree.cost_adversary t ht
  rwa [card_vector, Fintype.card_bool] at this

end Sagitta.Arrow
