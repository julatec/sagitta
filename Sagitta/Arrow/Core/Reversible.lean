/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic

/-!
# Reversible dynamics does not carry the arrow

The first place where the arrow is **not**: the step-by-step dynamics.

* A **reversible dynamics** (`ReversibleDynamics σ`) is a step `step : σ → σ` together with an
  inverse step `back` that undoes it (`back (step x) = x`), computable at the **same cost per
  step**. Going back `n` steps undoes going forward `n` steps (`back_iterate_step_iterate`), and
  it costs exactly the same (`costBack_eq_costForward`). The dynamics has no preferred direction.
* An **irreversible** step (one that merges two states) has no inverse step at all
  (`no_back_of_not_injective`): a step has an inverse exactly when it is injective
  (`injective_iff_exists_back`).
* **Landauer's embedding** (`historyDynamics`, `history_simulates`). Any dynamics `f : σ → σ`,
  reversible or not, becomes reversible once it keeps its history: on `σ × List σ`, the step
  `(x, h) ↦ (f x, x :: h)` is undone by popping the history, with overhead one step per step. This
  is the abstract shadow of Bennett's theorem (1973): the price of reversibility is space, not
  time. For Turing machines the corresponding statement, with polynomial overhead, is the named
  hypothesis `Sagitta.Arrow.TM.Bennett`.

The lesson for the localization theorem: the cost of going backwards is not in the dynamics. It is
in how much of the final state one keeps (`Sagitta.Arrow.Boundary`).
-/

namespace Sagitta.Arrow

/-- **A reversible dynamics**: a step, an inverse step computable at the same cost, and that
cost. -/
structure ReversibleDynamics (σ : Type*) where
  /-- One step forward. -/
  step : σ → σ
  /-- One step backward. -/
  back : σ → σ
  /-- The backward step undoes the forward step. -/
  back_step : ∀ x, back (step x) = x
  /-- The cost of one step, the same in both directions. -/
  stepCost : ℕ

namespace ReversibleDynamics

variable {σ : Type*} (D : ReversibleDynamics σ)

/-- The cost of `n` steps forward. -/
def costForward (n : ℕ) : ℕ := n * D.stepCost

/-- The cost of `n` steps backward. -/
def costBack (n : ℕ) : ℕ := n * D.stepCost

/-- **Going back `n` steps undoes going forward `n` steps.** -/
theorem back_iterate_step_iterate (n : ℕ) (x : σ) : D.back^[n] (D.step^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', D.back_step, ih]

/-- **And it costs the same**: the reversible dynamics has no arrow. -/
theorem costBack_eq_costForward (n : ℕ) : D.costBack n = D.costForward n := rfl

/-- The forward step of a reversible dynamics is injective. -/
theorem step_injective : Function.Injective D.step := fun x y h => by
  rw [← D.back_step x, h, D.back_step]

end ReversibleDynamics

/-- **An irreversible step has no inverse step**: if two states merge, nothing undoes the step. -/
theorem no_back_of_not_injective {σ : Type*} {f : σ → σ} (hf : ¬Function.Injective f) :
    ¬∃ g : σ → σ, ∀ x, g (f x) = x := by
  rintro ⟨g, hg⟩
  exact hf fun x y h => by rw [← hg x, h, hg y]

/-- A step has an inverse step exactly when it is injective. -/
theorem injective_iff_exists_back {σ : Type*} [Nonempty σ] (f : σ → σ) :
    Function.Injective f ↔ ∃ g : σ → σ, ∀ x, g (f x) = x :=
  ⟨fun h => ⟨Function.invFun f, Function.leftInverse_invFun h⟩,
    fun ⟨g, hg⟩ x y hxy => by rw [← hg x, hxy, hg y]⟩

/-! ### Landauer's embedding: keeping the history makes any dynamics reversible -/

/-- Pop the history: the inverse of `(x, h) ↦ (f x, x :: h)`. -/
def popHistory {σ : Type*} : σ × List σ → σ × List σ
  | (y, []) => (y, [])
  | (_, x :: h) => (x, h)

/-- **Landauer's embedding**: any dynamics `f`, made reversible by keeping its history, with one
step per step. -/
def historyDynamics {σ : Type*} (f : σ → σ) : ReversibleDynamics (σ × List σ) where
  step p := (f p.1, p.1 :: p.2)
  back := popHistory
  back_step _ := rfl
  stepCost := 1

/-- **The reversible dynamics simulates `f`** without overhead: after `n` steps, the first
component is `f^[n] x`, and the history has length `n`. -/
theorem history_simulates {σ : Type*} (f : σ → σ) (n : ℕ) (x : σ) (h : List σ) :
    ((historyDynamics f).step^[n] (x, h)).1 = f^[n] x ∧
      ((historyDynamics f).step^[n] (x, h)).2.length = n + h.length := by
  induction n generalizing x h with
  | zero => simp
  | succ n ih =>
    have e : (historyDynamics f).step (x, h) = (f x, x :: h) := rfl
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, e]
    obtain ⟨h1, h2⟩ := ih (f x) (x :: h)
    refine ⟨h1, ?_⟩
    rw [h2, List.length_cons]
    omega

/-- **From the full final state, going back is free of search**: `n` pops recover the initial
state of `f`, at the cost of `n` steps, the same as going forward. -/
theorem history_recovers {σ : Type*} (f : σ → σ) (n : ℕ) (x : σ) :
    ((historyDynamics f).back^[n] ((historyDynamics f).step^[n] (x, []))).1 = x := by
  rw [ReversibleDynamics.back_iterate_step_iterate]

end Sagitta.Arrow
