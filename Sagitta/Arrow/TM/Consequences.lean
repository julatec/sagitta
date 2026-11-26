/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Instance
import Sagitta.Arrow.TM.Ising
import CslibFrontier.Computability.Complexity.Classes.Ladner
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT

/-!
# Consequences of the arrow, for Turing machines

Every theorem here takes the arrow as an explicit HYPOTHESIS `(h : Arrow)` (or law 2.2 as
`(h : Law22)`). Everything else is proved, over the multi-tape Turing machines of cslib, with the
proofs of cslib-frontier: the Cook–Levin theorem, Ladner's theorem, the `NP`-completeness of
MAX-CUT (from `Partition`) and search-to-decision.

* `SAT_notMem_P`, `ThreeSAT_notMem_P`: SAT and 3-SAT are not in `P`.
* `exists_intermediate`: there is an `NP`-intermediate problem (Ladner), also in the core's
  vocabulary (`exists_intermediate_model`).
* `ISING_notMem_P`: the Ising ground state is not in `P`.
* `not_searchEasy`: some `FNP` search problem is not in `FPSearch` (Kelvin's form).
* `Law22`: law 2.2, the weak exponential-time hypothesis (equivalently SH of Stearns and Hunt), and
  `ThreeSAT_notMem_TIME`, which is its unfolding.
* `localizationTM`: the localization theorem of the core, for Turing machines.

The final `#print axioms` shows that only `propext`, `Classical.choice` and `Quot.sound` are used:
the arrow is a hypothesis, not an axiom.

The Boolean dichotomy (Schaefer, 1978) is not here: its formalization rests on further
assumptions (Post's lattice, the easy side of 2-SAT and affine CSPs) and stays in the companion
project.
-/

namespace Sagitta.Arrow.TM

open Cslib.Complexity Turing Turing.MultiTapeTM Cslib.Logic.PL

/-! ## The arrow -/

/-- **With the arrow, SAT is not in `P`.** -/
theorem SAT_notMem_P (h : Arrow) : SAT ∉ P encCNF :=
  arrow_iff_SAT.1 h

/-- **With the arrow, 3-SAT is not in `P`.** -/
theorem ThreeSAT_notMem_P (h : Arrow) : ThreeSAT ∉ P encCNF := fun h3 =>
  SAT_notMem_P h (polyTimeReducible_SAT_ThreeSAT.mem_P h3)

/-- **With the arrow, there is an `NP`-intermediate problem** (Ladner's theorem, with the proof of
cslib-frontier): in `NP`, not in `P`, and not `NP`-complete. -/
theorem exists_intermediate (h : Arrow) :
    ∃ L : Set (List Bool), L ∈ NP encBits ∧ L ∉ P encBits ∧ ¬NPComplete encBits L := by
  obtain ⟨α, enc, hne⟩ := arrow_iff_exists.1 h
  exact Ladner.exists_NP_not_P_not_npComplete (enc := enc) hne

/-- The same, in the vocabulary of the core: the model has an intermediate problem. -/
theorem exists_intermediate_model (h : Arrow) : ∃ A, tmModel.Intermediate A := by
  obtain ⟨L, hNP, hP, hC⟩ := exists_intermediate h
  exact ⟨⟨List Bool, encBits, L⟩, hNP, hP, fun hc => hC (npComplete_iff.1 hc)⟩

/-- **With the arrow, the Ising ground state is not in `P`.** -/
theorem ISING_notMem_P (h : Arrow) : Ising.ISING ∉ P Ising.encIsing := fun hI =>
  SAT_notMem_P h (Ising.ISING_mem_P_iff_SAT_mem_P.1 hI)

/-- **With the arrow, going back from "yes" is not always cheap** (Kelvin's form): some search
problem in `FNP` is not in `FPSearch`. -/
theorem not_searchEasy (h : Arrow) :
    ¬∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc :=
  kelvin.1 h

/-- **The localization theorem, for Turing machines**: the core's `localization` applied to
`tmModel`, with part (3) in cslib's vocabulary. -/
theorem localizationTM :
    (∀ (σ : Type) (D : ReversibleDynamics σ) (n : ℕ) (x : σ),
        D.back^[n] (D.step^[n] x) = x ∧ D.costBack n = D.costForward n) ∧
    (∀ (V : List Bool → Bool) (w : List Bool), V w = true → complete V w 0 = (some w, 1)) ∧
    (∀ (V : List Bool → Bool) (n : ℕ) (u : List Bool), u.length ≤ n →
        (∃ s : List Bool, u.length + s.length = n ∧ V (u ++ s) = true) →
        (∃ w, (complete V u (n - u.length)).1 = some w ∧ V w = true) ∧
          (complete V u (n - u.length)).2 ≤ 2 ^ (n - u.length)) ∧
    ((∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc) ↔
      ∀ {α : Type} (enc : α ↪ List Bool), NP enc ⊆ P enc) := by
  obtain ⟨h1, h2, h3, -⟩ := localization tmModel
  exact ⟨h1, h2, h3, oneBit⟩

/-! ## Law 2.2 -/

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

/-- **With law 2.2, 3-SAT is not in `TIME(2 ^ (n ^ (1 - ε)))`**: the definition, unfolded. -/
theorem ThreeSAT_notMem_TIME (h : Law22) (ε : ℝ) (hε : 0 < ε) :
    ¬∃ (C : ℕ) (s : CNF ℕ → ℕ), DecidableInTimeAndSpace ThreeSAT encCNF
      (fun φ => C * ⌈(2 : ℝ) ^ (((encCNF φ).length : ℝ) ^ (1 - ε))⌉₊ + C) s :=
  h ε hε

end Sagitta.Arrow.TM
