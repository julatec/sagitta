/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Instance
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Law 2.2: the weak exponential-time hypothesis

**Law 2.2.** *3-SAT is not in `TIME(2 ^ (n ^ (1 - ε)))` for any `ε > 0`*: the weak
exponential-time hypothesis, equivalent to the hypothesis SH of Stearns and Hunt (arXiv 2611.02650,
Theorem 2.4). It quantifies the arrow: not only is going back from "yes" not polynomial, it is not
even subexponential in this sense.

* `InTIME`, `subexpBound`, `Law22`: the definitions. `Law22` is a HYPOTHESIS, never an axiom.
* `Law22.arrow`: law 2.2 implies law 2.1, because a polynomial is eventually below
  `2 ^ (n ^ (1/2))` (`poly_le_subexp`).
-/

namespace Sagitta.Arrow.TM

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Cslib.Logic.PL Filter


/-- `A` is decidable within time `T` up to a constant factor, `TIME(T)`: some machine decides it
within `C · T(n) + C` steps on inputs of length `n`, with any space. -/
def InTIME {α : Type} (A : Set α) (enc : α ↪ List Bool) (T : ℕ → ℕ) : Prop :=
  ∃ (C : ℕ) (s : α → ℕ),
    DecidableInTimeAndSpace A enc (fun a => C * T (enc a).length + C) s

/-- The time bound `2 ^ (n ^ (1 - ε))`, rounded up. -/
noncomputable def subexpBound (ε : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ ((n : ℝ) ^ (1 - ε))⌉₊

/-- **Law 2.2: the weak exponential-time hypothesis**, equivalently SH of Stearns and Hunt
(arXiv 2611.02650, Theorem 2.4): for every `ε > 0`, 3-SAT is not in `TIME(2 ^ (n ^ (1 - ε)))`.
A HYPOTHESIS: a `Prop`, never an axiom. -/
def Law22 : Prop := ∀ ε : ℝ, 0 < ε → ¬InTIME ThreeSAT encCNF (subexpBound ε)

/-- **A polynomial bound is below `2 ^ (n ^ (1/2))` up to a constant.** -/
theorem poly_le_subexp {t : ℕ → ℕ} (ht : PolynomiallyBounded t) :
    ∃ C : ℕ, ∀ n, t n ≤ C * subexpBound (1 / 2) n + C := by
  obtain ⟨d, hd⟩ := ht
  -- `x ^ (2d) ≤ exp (log 2 * x)` for large `x`, then `x = √n`.
  have hlo := isLittleO_pow_exp_pos_mul_atTop (2 * d) (Real.log_pos one_lt_two)
  have hev : ∀ᶠ x : ℝ in atTop, x ^ (2 * d) ≤ Real.exp (Real.log 2 * x) := by
    filter_upwards [hlo.bound one_pos, eventually_ge_atTop 0] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_nonneg hx0,
      abs_of_pos (Real.exp_pos _), one_mul] at hx
    exact hx
  have hsqrt : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - 1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev' : ∀ᶠ n : ℕ in atTop, t n ≤ subexpBound (1 / 2) n := by
    filter_upwards [hd, hsqrt.eventually hev] with n hn hx
    have hpow : ((n : ℝ) ^ (1 - 1 / 2 : ℝ)) ^ (2 * d) = (n : ℝ) ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
        show (1 - 1 / 2 : ℝ) * ((2 * d : ℕ) : ℝ) = (d : ℝ) by push_cast; ring, Real.rpow_natCast]
    have h2 : Real.exp (Real.log 2 * (n : ℝ) ^ (1 - 1 / 2 : ℝ)) =
        (2 : ℝ) ^ ((n : ℝ) ^ (1 - 1 / 2 : ℝ)) := by
      rw [Real.rpow_def_of_pos two_pos]
    rw [hpow, h2] at hx
    have htn : (t n : ℝ) ≤ (n : ℝ) ^ d := by exact_mod_cast hn
    have : (t n : ℝ) ≤ (subexpBound (1 / 2) n : ℝ) :=
      htn.trans (hx.trans (Nat.le_ceil _))
    exact_mod_cast this
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev'
  refine ⟨1 + ∑ i ∈ Finset.range N, t i, fun n => ?_⟩
  rcases lt_or_ge n N with h | h
  · have : t n ≤ ∑ i ∈ Finset.range N, t i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 h)
    nlinarith [Nat.zero_le (subexpBound (1 / 2) n)]
  · have := hN n h
    nlinarith [Nat.zero_le (∑ i ∈ Finset.range N, t i), Nat.zero_le (subexpBound (1 / 2) n)]

/-- **Law 2.2 implies law 2.1.** If `P = NP`, 3-SAT is decided in polynomial time, hence in time
`C · 2 ^ (n ^ (1/2)) + C`, which law 2.2 forbids with `ε = 1/2`. -/
theorem Law22.arrow (h : Law22) : Arrow := by
  rw [arrow_iff]
  intro hall
  obtain ⟨t, s, ht, -, hdec⟩ :=
    mem_P_iff_exists_decidableInTimeAndSpace.1 (hall encCNF ThreeSAT.mem_NP)
  obtain ⟨C, hC⟩ := poly_le_subexp ht
  exact h (1 / 2) (by norm_num) ⟨C, _, ComputableInTimeAndSpace.mono hdec
    (fun φ => hC _) (fun _ => le_rfl)⟩

end Sagitta.Arrow.TM
