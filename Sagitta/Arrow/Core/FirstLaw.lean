/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Function.Basic

/-!
# The first law: conservation of work in a black box

**First law.** *In a closed system, what is hard is neither created nor destroyed: it is only moved
around; it changes only if information enters from outside.*

The closed system is a black box: an oracle `f : α → Bool` over a finite set `α` of options, that
can only be read by asking it. The task is to decide whether some option is good (`∃ i, f i`).

* A **query algorithm** is a decision tree (`QueryTree α`): it asks the oracle about an option and
  branches on the answer. Its **cost** is the number of questions it asks (`QueryTree.cost`).
* **The adversary** (`QueryTree.cost_adversary`): a tree that decides the question asks, on the
  all-`false` oracle, about every option, so it costs at least `|α|`.
* **Moving the work around** (`conservation`). Split the process into a *filling* phase that
  produces a table `T` from what it asks, and a *query* phase that reads `T` for free and keeps
  asking. If the table depends only on what was asked (`DependsOnlyOnAsked`), the questions of the
  two phases together still number at least `|α|`: what the query phase does not pay was paid by
  the filling phase.
* **The control: information from outside** (`free_table_breaks`). If the table is built by
  looking at the whole oracle without paying (non-uniform advice: information entering from
  outside), the query phase costs `0` and the bound fails. The hypothesis `DependsOnlyOnAsked` is
  exactly the closedness of the system.

The argument of the adversary relativizes (Baker, Gill and Solovay, 1975): it says nothing about a
formula given by its text, which can be read without asking. That is why the first law is a law of
black boxes and the second law (`Sagitta.Arrow.Model.Arrow`) has to be a hypothesis.
-/

namespace Sagitta.Arrow

/-- **A query algorithm**: a decision tree over the options `α`. -/
inductive QueryTree (α : Type) : Type
  | answer (b : Bool) : QueryTree α
  | ask (i : α) (next : Bool → QueryTree α) : QueryTree α

namespace QueryTree

variable {α : Type}

/-- The answer of the algorithm with the oracle `f`. -/
def run : QueryTree α → (α → Bool) → Bool
  | answer b, _ => b
  | ask i next, f => run (next (f i)) f

/-- The options that the algorithm asks about with the oracle `f`, in order. -/
def asked : QueryTree α → (α → Bool) → List α
  | answer _, _ => []
  | ask i next, f => i :: asked (next (f i)) f

/-- **The cost**: how many questions the algorithm asks with the oracle `f`. -/
def cost (t : QueryTree α) (f : α → Bool) : ℕ := (asked t f).length

/-- What is not asked does not matter: two oracles that agree on the asked options give the same
answer. -/
theorem run_congr : ∀ (t : QueryTree α) (f g : α → Bool), (∀ i ∈ asked t f, f i = g i) →
    run t f = run t g
  | answer _, _, _, _ => rfl
  | ask i next, f, g, h => by
    have hi : f i = g i := h i List.mem_cons_self
    simp only [run]
    rw [← hi]
    exact run_congr (next (f i)) f g (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- The tree decides "is some option good?". -/
def DecidesExists (t : QueryTree α) : Prop := ∀ f : α → Bool, run t f = true ↔ ∃ i, f i = true

/-- **The adversary.** A tree that decides whether some option is good asks, on the all-`false`
oracle, about **every** option: if it left one out, the adversary would make it good and the tree
would not notice. -/
theorem adversary [DecidableEq α] (t : QueryTree α) (h : DecidesExists t) (i : α) :
    i ∈ asked t (fun _ => false) := by
  by_contra hi
  let g : α → Bool := Function.update (fun _ => false) i true
  have hcon : run t (fun _ => false) = run t g :=
    run_congr t _ g fun j hj => by
      have hji : j ≠ i := fun e => hi (e ▸ hj)
      simp [g, Function.update_of_ne hji]
  have h0 : run t (fun _ => false) = false := by
    cases hc : run t (fun _ => false)
    · rfl
    · obtain ⟨j, hj⟩ := (h _).1 hc
      simp at hj
  have h1 : run t g = true := (h g).2 ⟨i, by simp [g]⟩
  rw [← hcon, h0] at h1
  exact Bool.false_ne_true h1

/-- **The adversary bound**: deciding whether some option is good costs at least `|α|`. -/
theorem cost_adversary [Fintype α] [DecidableEq α] (t : QueryTree α) (h : DecidesExists t) :
    Fintype.card α ≤ cost t (fun _ => false) := by
  have hsub : (Finset.univ : Finset α) ⊆ (asked t (fun _ => false)).toFinset :=
    fun i _ => List.mem_toFinset.2 (adversary t h i)
  calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
    _ ≤ (asked t (fun _ => false)).toFinset.card := Finset.card_le_card hsub
    _ ≤ cost t (fun _ => false) := List.toFinset_card_le _

end QueryTree

open QueryTree

variable {α τ : Type}

/-- **The table depends only on what was asked**: two oracles that agree on the options asked
while filling (with the first oracle) give the same table. This is the closedness of the system:
no information enters except through questions. -/
def DependsOnlyOnAsked (fill : (α → Bool) → τ) (askedFill : (α → Bool) → Finset α) : Prop :=
  ∀ f g : α → Bool, (∀ i ∈ askedFill f, f i = g i) → fill f = fill g

/-- **First law: work is conserved in a black box.** A filling phase produces a table `fill f`,
asking the options `askedFill f`; a query phase `Q (fill f)` reads the table for free and keeps
asking. If the table depends only on what was asked and the two phases together decide whether some
option is good, then, on the all-`false` oracle, the questions of the two phases cover all the
options: *what is hard is neither created nor destroyed, it is only moved around.* -/
theorem conservation [Fintype α] (fill : (α → Bool) → τ) (askedFill : (α → Bool) → Finset α)
    (hdep : DependsOnlyOnAsked fill askedFill) (Q : τ → QueryTree α)
    (hdec : ∀ f, run (Q (fill f)) f = true ↔ ∃ i, f i = true) :
    Fintype.card α ≤ (askedFill (fun _ => false)).card + cost (Q (fill (fun _ => false)))
      (fun _ => false) := by
  classical
  set f0 : α → Bool := fun _ => false
  have hcov : (Finset.univ : Finset α) ⊆ askedFill f0 ∪ (asked (Q (fill f0)) f0).toFinset := by
    intro i _
    by_contra hi
    simp only [Finset.mem_union, List.mem_toFinset, not_or] at hi
    obtain ⟨hp, hv⟩ := hi
    let g : α → Bool := Function.update f0 i true
    have hfg : ∀ j, j ≠ i → f0 j = g j := fun j hj => by simp [g, Function.update_of_ne hj]
    have hT : fill f0 = fill g := hdep f0 g fun j hj => hfg j fun e => hp (e ▸ hj)
    have hc : run (Q (fill f0)) f0 = run (Q (fill f0)) g :=
      run_congr _ f0 g fun j hj => hfg j fun e => hv (e ▸ hj)
    have h0 : run (Q (fill f0)) f0 = false := by
      cases hc0 : run (Q (fill f0)) f0
      · rfl
      · obtain ⟨j, hj⟩ := (hdec f0).1 hc0; simp [f0] at hj
    have h1 : run (Q (fill g)) g = true := (hdec g).2 ⟨i, by simp [g]⟩
    rw [← hT, ← hc, h0] at h1
    exact Bool.false_ne_true h1
  calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
    _ ≤ (askedFill f0 ∪ (asked (Q (fill f0)) f0).toFinset).card := Finset.card_le_card hcov
    _ ≤ (askedFill f0).card + (asked (Q (fill f0)) f0).toFinset.card := Finset.card_union_le _ _
    _ ≤ (askedFill f0).card + cost (Q (fill f0)) f0 :=
      Nat.add_le_add_left (List.toFinset_card_le _) _

/-! ### The control: information entering from outside -/

/-- **The query with advice**: if the table is the whole oracle, answer without asking. -/
def freeQuery [Fintype α] (T : α → Bool) : QueryTree α := .answer (decide (∃ i, T i = true))

/-- **With a free table the query phase decides and costs `0`.** The table is the oracle itself,
read without paying. -/
theorem free_table [Fintype α] :
    (∀ f : α → Bool, run (freeQuery (id f)) f = true ↔ ∃ i, f i = true) ∧
      ∀ f : α → Bool, cost (freeQuery (id f)) f = 0 := by
  refine ⟨fun f => ?_, fun f => rfl⟩
  simp [freeQuery, run]

/-- **That table does not depend only on what was asked**: the system is not closed. -/
theorem free_table_not_closed [Nonempty α] :
    ¬DependsOnlyOnAsked (id : (α → Bool) → α → Bool) (fun _ => ∅) := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty α›
  have := congrFun (h (fun _ => false) (fun _ => true) (by simp)) i
  simp at this

/-- **And without closedness the first law fails**: with the free table, nothing asked while
filling and nothing while querying, the total is `0 < |α|`. -/
theorem free_table_breaks [Fintype α] [Nonempty α] :
    ¬Fintype.card α ≤ ((fun _ => ∅ : (α → Bool) → Finset α) (fun _ => false)).card +
        cost (freeQuery (id (fun _ : α => false))) (fun _ => false) := by
  have := Fintype.card_pos (α := α)
  simp [freeQuery, cost, asked]

end Sagitta.Arrow
