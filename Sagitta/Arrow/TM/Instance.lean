/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.Consequences
import CslibFrontier.Computability.Complexity.Classes.TFNP.SearchToDecision
import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# The Turing-machine instance

This file proves that the multi-tape Turing machines of cslib, with the classes of
cslib-frontier, satisfy the axioms of the abstract `Sagitta.Arrow.Model`:

* a decision problem is a set `A : Set α` with an encoding `enc : α ↪ List Bool`
  (`Sagitta.Arrow.TM.Problem`), and a search problem is a relation with an encoding
  (`Sagitta.Arrow.TM.SearchProblem`);
* `Reduces` is `Cslib.Complexity.PolyTimeReducible`, `InP` and `InNP` are `Cslib.Complexity.P` and
  `Cslib.Complexity.NP`, `InFNP` and `InFP` are `Cslib.Complexity.FNP` and
  `Cslib.Complexity.FPSearch`;
* every closure property is a theorem of cslib-frontier, used with its proof (nothing here is a
  hypothesis): `PolyTimeReducible.trans`, `PolyTimeReducible.mem_P`, `P_subset_NP`,
  `searchDomain_mem_NP`, `searchDomain_mem_P`, `mem_NP_iff_exists_FNP`, `prefixSearch_mem_FNP`
  and `mem_FPSearch_of_prefixSearch_mem_P`.

The result is `tmModel`, and every theorem of the core holds for it. This file also states the
zeroth law, the arrow and the one-bit part of the localization in the vocabulary of cslib, and the
statement `Bennett` (a reversible simulation with linear overhead that leaves no garbage, proved
in `Sagitta.Arrow.TM.Bennett.Discharge`) with what it gives.
-/

namespace Sagitta.Arrow.TM

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-- A decision problem for Turing machines: a set of instances and their binary encoding. -/
structure Problem where
  /-- The type of instances. -/
  α : Type
  /-- The binary encoding of instances. -/
  enc : α ↪ List Bool
  /-- The "yes" instances. -/
  set : Set α

/-- A search problem for Turing machines: a relation between instances and binary words, and the
binary encoding of instances. -/
structure SearchProblem where
  /-- The type of instances. -/
  α : Type
  /-- The binary encoding of instances. -/
  enc : α ↪ List Bool
  /-- `rel a w`: `w` is a solution of `a`. -/
  rel : α → List Bool → Prop

/-- **Turing machines form a model.** Every field is a theorem of cslib-frontier. -/
def tmModel : Model.{1} where
  Problem := Problem
  Search := SearchProblem
  Reduces A B := PolyTimeReducible A.enc B.enc A.set B.set
  reduces_refl A := PolyTimeReducible.refl A.enc A.set
  reduces_trans hAB hBC := PolyTimeReducible.trans hAB hBC
  InP A := A.set ∈ P A.enc
  InNP A := A.set ∈ NP A.enc
  P_subset_NP h := P_subset_NP h
  InP_of_reduces hAB hB := hAB.mem_P hB
  InFNP R := R.rel ∈ FNP R.enc
  InFP R := R.rel ∈ FPSearch R.enc
  domain R := ⟨R.α, R.enc, searchDomain R.rel⟩
  domain_NP h := searchDomain_mem_NP h
  domain_P h := searchDomain_mem_P h
  exists_search {A} h := by
    obtain ⟨R, hR, hRA⟩ := mem_NP_iff_exists_FNP.1 h
    exact ⟨⟨A.α, A.enc, R⟩, hR, by cases A; dsimp only at hRA ⊢; rw [hRA]⟩
  prefixProblem R := ⟨R.α × List Bool, encPair R.enc encBits, searchDomain (prefixSearch R.rel)⟩
  prefix_NP h := searchDomain_mem_NP (prefixSearch_mem_FNP h)
  search_of_prefix h hP := mem_FPSearch_of_prefixSearch_mem_P h hP

/-! ## The zeroth law -/

/-- **Zeroth law, for Turing machines**: polynomial-time many-one reductions compose
(cslib-frontier's `PolyTimeReducible.trans`, through the core's `Model.lawZero`). -/
theorem lawZero {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {A : Set α} {B : Set β} {C : Set γ}
    (hAB : PolyTimeReducible encA encB A B) (hBC : PolyTimeReducible encB encC B C) :
    PolyTimeReducible encA encC A C :=
  Model.lawZero (M := tmModel) (A := ⟨α, encA, A⟩) (B := ⟨β, encB, B⟩) (C := ⟨γ, encC, C⟩) hAB hBC

/-! ## `NP`-completeness in the two vocabularies -/

/-- The core's `NP`-completeness is cslib's `NPComplete`. -/
theorem npComplete_iff {β : Type} {enc : β ↪ List Bool} {B : Set β} :
    tmModel.NPComplete ⟨β, enc, B⟩ ↔ NPComplete enc B := by
  constructor
  · rintro ⟨hB, hard⟩
    exact ⟨hB, fun α encA A hA => hard ⟨α, encA, A⟩ hA⟩
  · rintro ⟨hB, hard⟩
    exact ⟨hB, fun A hA => hard A.enc A.set hA⟩

/-! ## The arrow for Turing machines -/

set_option linter.dupNamespace false in
/-- **The arrow (law 2.1) for Turing machines: `P ≠ NP`.** A HYPOTHESIS, never an axiom: it is
`tmModel.Arrow`, and every theorem that uses it takes `(h : Arrow)` as an argument. -/
def Arrow : Prop := tmModel.Arrow

/-- The arrow, unfolded in cslib's vocabulary: not every `NP` problem is in `P`, for every
encoding. -/
theorem arrow_iff : Arrow ↔ ¬∀ {α : Type} (enc : α ↪ List Bool), NP enc ⊆ P enc := by
  unfold Arrow Model.Arrow Model.PeqNP
  constructor
  · intro h hall
    exact h fun A hA => hall A.enc hA
  · intro h hall
    exact h fun enc A hA => hall ⟨_, enc, A⟩ hA

/-- The arrow says that `P ≠ NP` for some encoding of instances. -/
theorem arrow_iff_exists : Arrow ↔ ∃ (α : Type) (enc : α ↪ List Bool), P enc ≠ NP enc := by
  rw [arrow_iff]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact h fun enc => (hne _ enc).ge
  · rintro ⟨α, enc, hne⟩ hall
    exact hne (P_subset_NP.antisymm (hall enc))

/-- The arrow is `SAT ∉ P`, through the Cook–Levin theorem of cslib-frontier. -/
theorem arrow_iff_SAT : Arrow ↔ SAT ∉ P encCNF := by
  rw [arrow_iff, SAT_mem_P_iff]
  constructor
  · intro h hall
    exact h fun enc => (hall enc).ge
  · intro h hall
    exact h fun enc => P_subset_NP.antisymm (hall enc)

/-! ## Localization, part (3), for Turing machines -/

/-- The core's `SearchEasy` is cslib's `FNP ⊆ FPSearch` for every encoding. -/
theorem searchEasy_iff : tmModel.SearchEasy ↔
    ∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc := by
  constructor
  · intro h α enc R hR
    exact h ⟨α, enc, R⟩ hR
  · intro h R hR
    exact h R.enc hR

/-- **With one bit, going back is cheap exactly when `P = NP`**, for Turing machines. This is
cslib-frontier's `FNP_subset_FPSearch_iff`, with its proof; the core proves the same statement
(`Model.searchEasy_iff_peqNP`) from the closure properties alone. -/
theorem oneBit :
    (∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc) ↔
      ∀ {α : Type} (enc : α ↪ List Bool), NP enc ⊆ P enc :=
  FNP_subset_FPSearch_iff

/-- **Kelvin's form, for Turing machines.** With the arrow, some search problem in `FNP` (for some
encoding) is not in `FPSearch`: no efficient machine converts every "yes" into its witness. -/
theorem kelvin : Arrow ↔ ¬∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc := by
  rw [arrow_iff, oneBit]

/-! ## Bennett's hypothesis -/

/-- A machine is **reversible** when its step is injective on running configurations: every
running configuration has at most one running predecessor. -/
def IsReversible {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) : Prop :=
  ∀ (input : List Bool) (c c' : Cfg k Bool State input), ¬c.Halted → ¬c'.Halted →
    tm.step c = tm.step c' → c = c'

/-- What a work tape may hold when a garbage-free run ends: nothing, a copy of the input from cell
`0` on (Bennett's reconstructed input), or the single mark `true` at cell `-1`, which is the same for
every input and so carries no information. -/
inductive Residue where
  /-- A blank tape. -/
  | blank
  /-- The input, from cell `0` on. -/
  | input
  /-- The mark `true` at cell `-1`, blank elsewhere. -/
  | mark
  deriving DecidableEq

/-- The tape that a residue stands for, on the input `x`. -/
def Residue.tape (x : List Bool) : Residue → ℤ → Option Bool
  | .blank => fun _ => none
  | .input => Turing.tapeOfList x
  | .mark => Function.update (fun _ => none) (-1) (some true)

/-- **A clean computation of `f`** (Bennett's "no garbage"): on every input `a`, by time `t a` the
machine has halted with `encOut (f a)` on the output tape, every work head back on cell `0`, the
input head on the blank after the input, and every work tape holding what a fixed role
(`role : Fin k → Residue`, the same for every input) says: blank, a copy of the input, or a
constant mark. Nothing that depends on the computation itself (a history, an intermediate result)
is left. The input of cslib is read-only, so it is intact by construction. -/
def ComputesCleanly {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) {α β : Type}
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β) (t : α → ℕ) : Prop :=
  ∃ role : Fin k → Residue, ∀ a,
    tm.runFrom (tm.initCfg (encIn a)) (t a) =
      ⟨none, Fin.last _, fun i => (role i).tape (encIn a), fun _ => 0, encOut (f a)⟩

/-- **Bennett's theorem** (Bennett, 1973, *Logical reversibility of computation*, for the machines
of cslib): for every machine computing `f` in time `t` there is a **reversible** machine (with
finitely many states) that computes `f` in time and space **linear** in `n + t(n)` and leaves **no
garbage**: when it halts, the output is on the output tape, the input is intact, and every work tape
is blank except for copies of the input and constant marks (`ComputesCleanly`). Bennett's final
configuration is "history tape blank, input reconstructed, output written"; a history simulation
that never uncomputes (Lecerf 1963, Landauer 1961) does **not** satisfy this statement (see
`BennettWeak` and `histOnlyTM_not_computesCleanly`). It is proved in
`Sagitta.Arrow.TM.Bennett.Discharge` (`bennett_holds`) by Bennett's construction (compute keeping a
history, copy the output, uncompute). -/
def Bennett : Prop :=
  ∀ {α β : Type} (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (t s : ℕ → ℕ),
    ComputableInTimeAndSpaceOfLength f encIn encOut t s →
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (c : ℕ),
      IsReversible tm ∧
        tm.ComputesFunInTimeAndSpace encIn encOut f
          (fun a => c * ((encIn a).length + t (encIn a).length + 1))
          (fun a => c * ((encIn a).length + t (encIn a).length + 1)) ∧
        ComputesCleanly tm encIn encOut f
          (fun a => c * ((encIn a).length + t (encIn a).length + 1))

/-- **The old, weaker statement**, kept as a documented mutant: a reversible machine computes `f`
in polynomial time and space, with **nothing said about the work tapes at the end**. A history
simulation that never uncomputes (Lecerf–Landauer) already satisfies it
(`Sagitta.Arrow.TM.bennett_of_history_only`), so it does not express Bennett's theorem. -/
def BennettWeak : Prop :=
  ∀ {α β : Type} (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool),
    ComputableInPolyTime f encIn encOut →
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (t s : ℕ → ℕ),
      IsReversible tm ∧ PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
        tm.ComputesFunInTimeAndSpace encIn encOut f (fun a => t (encIn a).length)
          (fun a => s (encIn a).length)

/-- **A reversible machine can be traced back**: if two runs of `n` steps never halt before the
end and reach the same configuration, they started from the same configuration. Going back needs
no search. -/
theorem IsReversible.runFrom_injective {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    (hrev : IsReversible tm) {input : List Bool} :
    ∀ (n : ℕ) (c c' : Cfg k Bool State input),
      (∀ i < n, ¬(tm.runFrom c i).Halted) → (∀ i < n, ¬(tm.runFrom c' i).Halted) →
      tm.runFrom c n = tm.runFrom c' n → c = c'
  | 0, c, c', _, _, h => h
  | n + 1, c, c', hc, hc', h => by
    have hstep : tm.step c = tm.step c' := by
      refine hrev.runFrom_injective n (tm.step c) (tm.step c') (fun i hi => ?_) (fun i hi => ?_) ?_
      · have := hc (i + 1) (by omega)
        rwa [MultiTapeTM.runFrom, Function.iterate_succ_apply] at this
      · have := hc' (i + 1) (by omega)
        rwa [MultiTapeTM.runFrom, Function.iterate_succ_apply] at this
      · simpa only [MultiTapeTM.runFrom, Function.iterate_succ_apply] using h
    exact hrev input c c' (hc 0 (by omega)) (hc' 0 (by omega)) hstep

/-- **With Bennett, every `NP` verifier runs on a reversible machine without garbage.** For every
problem in `NP` there is a verifier computed in polynomial time and space by a reversible machine
that ends with clean work tapes (`ComputesCleanly`): the dynamics of checking a witness carries no
arrow and leaves no trace of the check. -/
theorem reversible_verifier (hB : Bennett) {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ NP enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool), IsVerifier enc p V A ∧
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (t s : ℕ → ℕ),
        IsReversible tm ∧ PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
          tm.ComputesFunInTimeAndSpace (encPair enc encBits) encBool V
            (fun a => t ((encPair enc encBits) a).length)
            (fun a => s ((encPair enc encBits) a).length) ∧
          ComputesCleanly tm (encPair enc encBits) encBool V
            (fun a => t ((encPair enc encBits) a).length) := by
  obtain ⟨p, V, ⟨tV, sV, htV, -, hV⟩, hAV⟩ := hA
  obtain ⟨k, S, hS, tm, c, hrev, hcomp, hclean⟩ := hB V _ _ tV sV hV
  have hp : PolynomiallyBounded fun n => c * (n + tV n + 1) :=
    (PolynomiallyBounded.const c).mul
      ((PolynomiallyBounded.id.add htV).add (PolynomiallyBounded.const 1))
  exact ⟨p, V, hAV, k, S, hS, tm, _, _, hrev, hp, hp, hcomp, hclean⟩

end Sagitta.Arrow.TM
