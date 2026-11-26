/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.History

/-!
# Bennett, step 3: copying a tape onto a clean tape, reversibly

`copyTM src dst` copies the word under the head of the work tape `src` onto the work tape `dst`,
and brings both heads back to where they started.

* **Forward** (state `fwd`): while `src` reads a symbol `b`, it swaps the blank and `b` in the cell
  under the head of `dst` (`Equiv.swap none (some b)`) and moves both heads right. On a clean
  destination the swap writes `b`; on any other cell it is still a bijection, so nothing is
  forgotten. When `src` reads a blank, it moves both heads left and goes to `back`.
* **Back** (state `back`): while `src` reads a symbol, it moves both heads left. On a blank (the
  cell before the word) it moves both heads right and halts.

## Main results

* `copyTM_isReversible`: for `src ≠ dst`, `copyTM src dst` is reversible (`IsReversible`), on every
  running configuration, not only the reachable ones. The swap makes a guard unnecessary: the
  successor tells the state, the symbol of `src` (which is never written) and, through the swap,
  the old symbol of `dst`. The hypothesis is necessary: `copyTM_self_not_isReversible`.
* `copyTM_correct`: started in `fwd` with a word `w` under the head of `src`, a blank before it and
  after it, and the `|w|` cells of `dst` from its head blank, after `2 |w| + 2` steps the machine
  has halted, `dst` holds `w` from its head on (`copyTape`), and everything else (the heads, the
  other tapes, the input and the output) is as it was.

## The output tape

The output of cslib is append-only and `ComputesFunInTimeAndSpace` reads it. In Bennett's
construction the machine with a history must keep the simulated output on a work tape, and the
copy is what reaches the real output: `emitTM src` (below) is the same machine with the output tape
as destination, the clean tape being the empty output of the initial configuration
(`emitTM_isReversible`, `emitTM_correct`).
-/

namespace Sagitta.Arrow.TM.Bennett

open Turing Turing.MultiTapeTM

/-- The two phases of the copying machine. -/
inductive CopyState
  | fwd
  | back
  deriving DecidableEq

instance : Finite CopyState :=
  Finite.of_injective (fun s => match s with | .fwd => false | .back => true)
    (by intro a b; cases a <;> cases b <;> simp)

variable {k : ℕ}

/-! ## The machine -/

/-- The actions of the copying machine: the input head stays, `src` is never written, both heads
move by `m`, `dst` gets `wr`, nothing else changes. -/
def moveAct (src dst : Fin k) (wr : Option (Option Bool)) (m : SignType) (o : Option Bool)
    (q : Option CopyState) : Action k Bool CopyState :=
  ⟨0, fun i => if i = dst then (wr, m) else if i = src then (none, m) else (none, 0), o, q⟩

theorem moveAct_write {src dst : Fin k} {wr : Option (Option Bool)} {m : SignType}
    {o : Option Bool} {q : Option CopyState} (i : Fin k) :
    ((moveAct src dst wr m o q).workTapes i).1 = if i = dst then wr else none := by
  simp only [moveAct]; split_ifs <;> rfl

theorem moveAct_move {src dst : Fin k} {wr : Option (Option Bool)} {m : SignType}
    {o : Option Bool} {q : Option CopyState} (i : Fin k) :
    ((moveAct src dst wr m o q).workTapes i).2 = if i = src ∨ i = dst then m else 0 := by
  simp only [moveAct]; split_ifs <;> simp_all

/-- The swap of the blank and `b`: what the forward phase does to a cell of the destination. -/
abbrev swapCell (b : Bool) : Equiv.Perm (Option Bool) := Equiv.swap none (some b)

/-- The transition function of the copying machine. -/
def copyTr (src dst : Fin k) :
    CopyState → Option Bool → (Fin k → Option Bool) → Action k Bool CopyState
  | .fwd, _, w => match w src with
    | some b => moveAct src dst (some (swapCell b (w dst))) 1 none (some .fwd)
    | none => moveAct src dst none (-1) none (some .back)
  | .back, _, w => match w src with
    | some _ => moveAct src dst none (-1) none (some .back)
    | none => moveAct src dst none 1 none none

/-- **The copying machine**: copies the word under the head of `src` onto `dst`. -/
def copyTM (src dst : Fin k) : MultiTapeTM k Bool CopyState :=
  ofTr .fwd (copyTr src dst)

/-! ## Reversibility -/

section Lemmas

variable {State : Type} {input : List Bool}

/-- Two actions with the same moves and the same result started from the same head positions. -/
theorem workTapePos_eq_of_apply {A A' : Action k Bool State} {c c' : Cfg k Bool State input}
    (hm : ∀ i, (A.workTapes i).2 = (A'.workTapes i).2) (h : A.apply c = A'.apply c') :
    c.workTapePos = c'.workTapePos := by
  funext i
  have := congrFun (congrArg Cfg.workTapePos h) i
  simp only [Action.apply_workTapePos, hm i] at this
  exact add_right_cancel this

/-- A tape that neither action writes was the same before. -/
theorem workTapes_eq_of_apply {A A' : Action k Bool State} {c c' : Cfg k Bool State input}
    {i : Fin k} (hA : (A.workTapes i).1 = none) (hA' : (A'.workTapes i).1 = none)
    (h : A.apply c = A'.apply c') : c.workTapes i = c'.workTapes i := by
  have := congrFun (congrArg Cfg.workTapes h) i
  simpa only [Action.apply_workTapes, hA, hA'] using this

end Lemmas

/-- **The copying machine is reversible** when the source and the destination are different tapes.
-/
theorem copyTM_isReversible {src dst : Fin k} (hsd : src ≠ dst) :
    IsReversible (copyTM src dst) := by
  intro input c c' hc hc' hstep
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  rw [step_of_state hq, step_of_state hq', copyTM, tr_ofTr, tr_ofTr] at hstep
  have hsrc : ∀ {wr wr' m m' o o' r r'},
      ((moveAct src dst wr m o r).apply c = (moveAct src dst wr' m' o' r').apply c') →
        c.workTapes src = c'.workTapes src := fun h =>
    workTapes_eq_of_apply (by simp [moveAct_write, hsd]) (by simp [moveAct_write, hsd]) h
  have hpos : ∀ {wr wr' m o o' r r'},
      ((moveAct src dst wr m o r).apply c = (moveAct src dst wr' m o' r').apply c') →
        c.workTapePos = c'.workTapePos := fun h =>
    workTapePos_eq_of_apply (fun i => by rw [moveAct_move, moveAct_move]) h
  -- the symbol read on `src` is the same on both sides once the heads agree
  have hsym : ∀ {wr wr' m o o' r r'},
      ((moveAct src dst wr m o r).apply c = (moveAct src dst wr' m o' r').apply c') →
        c.workTapeSymbols src = c'.workTapeSymbols src := fun h => by
    simp only [Cfg.workTapeSymbols, hsrc h, hpos h]
  have hst := congrArg Cfg.state hstep
  rcases q with _ | _ <;> rcases q' with _ | _ <;>
    rcases hs : c.workTapeSymbols src with _ | b <;>
    rcases hs' : c'.workTapeSymbols src with _ | b' <;>
    simp only [copyTr, hs, hs'] at hstep hst <;>
    simp only [moveAct, Action.apply_state, reduceCtorEq, Option.some.injEq] at hst
  -- fwd, blank / fwd, blank
  · exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl)
      (fun i => Or.inl (by rw [moveAct_write]; split_ifs <;> rfl)) hstep
  -- fwd, symbol / fwd, symbol
  · have hb : b = b' := by
      have := hsym hstep
      rw [hs, hs'] at this
      exact Option.some.inj this
    subst hb
    have hd : c.workTapeSymbols dst = c'.workTapeSymbols dst := by
      have := congrFun (congrFun (congrArg Cfg.workTapes hstep) dst) (c.workTapePos dst)
      simp only [Action.apply_workTapes, moveAct_write, ↓reduceIte] at this
      rw [Function.update_self, hpos hstep, Function.update_self] at this
      exact (swapCell b).injective this
    rw [← hd] at hstep
    refine apply_injective _ (hq.trans hq'.symm) (Or.inl rfl) (fun i => ?_) hstep
    by_cases hi : i = dst
    · exact Or.inr (hi ▸ hd)
    · exact Or.inl (by simp [moveAct_write, hi])
  -- fwd, blank / back, symbol: `src` tells them apart
  · have := hsym hstep
    rw [hs, hs'] at this
    exact absurd this (by simp)
  -- back, symbol / fwd, blank
  · have := hsym hstep
    rw [hs, hs'] at this
    exact absurd this (by simp)
  -- back, blank / back, blank
  · exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl)
      (fun i => Or.inl (by rw [moveAct_write]; split_ifs <;> rfl)) hstep
  -- back, symbol / back, symbol
  · exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl)
      (fun i => Or.inl (by rw [moveAct_write]; split_ifs <;> rfl)) hstep

/-- **The hypothesis is necessary**: copying a tape onto itself is not reversible. A cell holding
either symbol is swapped to a blank, and the symbol is lost. -/
theorem copyTM_self_not_isReversible (i : Fin k) : ¬IsReversible (copyTM i i) := by
  intro hrev
  let c : Bool → Cfg k Bool CopyState [] := fun b =>
    ⟨some .fwd, 1, fun j z => if j = i ∧ z = 0 then some b else none, fun _ => 0, []⟩
  have hsym (b : Bool) : (c b).workTapeSymbols i = some b := by simp [c, Cfg.workTapeSymbols]
  have hstep : (copyTM i i).step (c false) = (copyTM i i).step (c true) := by
    rw [step_of_state (q := .fwd) rfl, step_of_state (q := .fwd) rfl, copyTM, tr_ofTr, tr_ofTr]
    simp only [copyTr, hsym]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp only [Action.apply_workTapes, moveAct_write]
      split_ifs with hj
      · simp only [swapCell, Equiv.swap_apply_right, Function.update_apply, c]
        split_ifs <;> simp_all
      · simp [c, hj]
    · rfl
    · rfl
  have := congrFun (congrFun (congrArg Cfg.workTapes (hrev [] _ _ (by simp [c]) (by simp [c])
    hstep)) i) 0
  simp [c] at this

/-! ## Correctness -/

/-- **The copy of a word onto a tape**: `g` with the word `w` written from the cell `d` on. -/
def copyTape (g : ℤ → Option Bool) (d : ℤ) (w : List Bool) : ℤ → Option Bool :=
  fun z => if d ≤ z ∧ z < d + w.length then w[(z - d).toNat]? else g z

/-- The moves of the two heads: `n` cells on `src` and `dst`, none elsewhere. -/
def shift (src dst : Fin k) (n : ℤ) : Fin k → ℤ := fun i => if i = src ∨ i = dst then n else 0

section Correct

variable {src dst : Fin k} {input : List Bool}

theorem copyTape_step (g : ℤ → Option Bool) (d : ℤ) (w : List Bool) (n : ℕ) (hn : n < w.length) :
    Function.update (copyTape g d (w.take n)) (d + n) (some w[n]) =
      copyTape g d (w.take (n + 1)) := by
  funext z
  simp only [copyTape, List.length_take, Function.update_apply, List.getElem?_take]
  rw [min_eq_left hn.le, min_eq_left (by omega : n + 1 ≤ w.length)]
  split_ifs with h1 <;> try omega
  all_goals try rfl
  subst h1
  rw [show (d + n - d).toNat = n by omega, List.getElem?_eq_getElem hn]

theorem copyTape_nil (g : ℤ → Option Bool) (d : ℤ) : copyTape g d [] = g := by
  funext z; simp [copyTape]

/-- The forward phase: after `n ≤ |w|` steps, the first `n` symbols are copied and both heads are
`n` cells to the right. -/
theorem copy_fwd (hsd : src ≠ dst) (c : Cfg k Bool CopyState input) (w : List Bool)
    (hst : c.state = some .fwd)
    (hsrc : ∀ i : ℕ, i ≤ w.length → c.workTapes src (c.workTapePos src + i) = w[i]?)
    (hdst : ∀ i : ℕ, i < w.length → c.workTapes dst (c.workTapePos dst + i) = none)
    (n : ℕ) (hn : n ≤ w.length) :
    (copyTM src dst).runFrom c n =
      { c with
        workTapes := Function.update c.workTapes dst
          (copyTape (c.workTapes dst) (c.workTapePos dst) (w.take n))
        workTapePos := c.workTapePos + shift src dst n } := by
  induction n with
  | zero =>
    apply Cfg.ext <;> simp [runFrom, copyTape_nil]
    funext i; simp [shift]
  | succ n ih =>
    have hlt : n < w.length := by omega
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega)]
    set c₁ : Cfg k Bool CopyState input := { c with
        workTapes := Function.update c.workTapes dst
          (copyTape (c.workTapes dst) (c.workTapePos dst) (w.take n))
        workTapePos := c.workTapePos + shift src dst n } with hc₁
    have hs : c₁.workTapeSymbols src = some w[n] := by
      simp only [hc₁, Cfg.workTapeSymbols, Function.update_of_ne hsd, Pi.add_apply, shift,
        true_or, ↓reduceIte]
      rw [hsrc n hlt.le, List.getElem?_eq_getElem hlt]
    have hd : c₁.workTapeSymbols dst = none := by
      simp only [hc₁, Cfg.workTapeSymbols, Function.update_self, Pi.add_apply, shift, or_true,
        ↓reduceIte, copyTape, List.length_take, min_eq_left hlt.le]
      split_ifs with h
      · omega
      · exact hdst n hlt
    rw [step_of_state (q := .fwd) hst, copyTM, tr_ofTr]
    simp only [copyTr, hs, hd]
    apply Cfg.ext
    · simp [moveAct, hst]
    · simp [moveAct, hc₁]
    · funext i
      simp only [Action.apply_workTapes, moveAct_write]
      by_cases hi : i = dst
      · subst hi
        simp only [↓reduceIte, hc₁, Function.update_self, Pi.add_apply, shift, or_true,
          swapCell, Equiv.swap_apply_left]
        exact copyTape_step _ _ w n hlt
      · simp [hi, hc₁]
    · funext i
      simp only [Action.apply_workTapePos, moveAct_move, hc₁, Pi.add_apply, shift]
      split_ifs <;> simp; ring
    · simp [moveAct, hc₁]

/-- The back phase: over `n` symbols of `src`, both heads move `n` cells to the left. -/
theorem copy_back (c : Cfg k Bool CopyState input) (hst : c.state = some .back) (n : ℕ)
    (hsym : ∀ i : ℕ, i < n → c.workTapes src (c.workTapePos src - i) ≠ none) :
    (copyTM src dst).runFrom c n = { c with workTapePos := c.workTapePos + shift src dst (-n) } := by
  induction n with
  | zero =>
    apply Cfg.ext <;> simp [runFrom]
    funext i; simp [shift]
  | succ n ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom,
      ih (fun i hi => hsym i (by omega))]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (hsym n (by omega))
    have hs : ({ c with workTapePos := c.workTapePos + shift src dst (-n) } :
        Cfg k Bool CopyState input).workTapeSymbols src = some b := by
      simp only [Cfg.workTapeSymbols, Pi.add_apply, shift, true_or, ↓reduceIte]
      rw [← hb]; ring_nf
    rw [step_of_state (q := .back) hst, copyTM, tr_ofTr]
    simp only [copyTr, hs]
    apply Cfg.ext
    · simp [moveAct, hst]
    · simp [moveAct]
    · funext i
      simp [Action.apply_workTapes, moveAct_write]
    · funext i
      simp only [Action.apply_workTapePos, moveAct_move, Pi.add_apply, shift]
      split_ifs <;> simp; ring
    · simp [moveAct]

/-- **The copying machine is correct.** Started in `fwd` with the word `w` on `src` from its head
on, a blank before and after it, and `|w|` blank cells on `dst` from its head on, after
`2 |w| + 2` steps it has halted with `w` copied onto `dst` from its head on, and nothing else
changed: the heads are back, `src` and the other tapes, the input and the output are untouched. -/
theorem copyTM_correct (hsd : src ≠ dst) (c : Cfg k Bool CopyState input) (w : List Bool)
    (hst : c.state = some .fwd)
    (hsrc : ∀ i : ℕ, i ≤ w.length → c.workTapes src (c.workTapePos src + i) = w[i]?)
    (hleft : c.workTapes src (c.workTapePos src - 1) = none)
    (hdst : ∀ i : ℕ, i < w.length → c.workTapes dst (c.workTapePos dst + i) = none) :
    (copyTM src dst).runFrom c (2 * w.length + 2) =
      { c with
        state := none
        workTapes := Function.update c.workTapes dst
          (copyTape (c.workTapes dst) (c.workTapePos dst) w) } := by
  set T := Function.update c.workTapes dst (copyTape (c.workTapes dst) (c.workTapePos dst) w)
    with hT
  have hTsrc : T src = c.workTapes src := by simp [hT, Function.update_of_ne hsd]
  -- forward
  have h1 := copy_fwd hsd c w hst hsrc hdst w.length le_rfl
  rw [List.take_length] at h1
  -- the turn
  have h2 : (copyTM src dst).step ((copyTM src dst).runFrom c w.length) =
      ({ c with
        state := some CopyState.back
        workTapes := T
        workTapePos := c.workTapePos + shift src dst ((w.length : ℤ) - 1) } :
        Cfg k Bool CopyState input) := by
    rw [h1, step_of_state (q := .fwd) hst, copyTM, tr_ofTr]
    have hs : ({ c with
        workTapes := T
        workTapePos := c.workTapePos + shift src dst w.length } :
          Cfg k Bool CopyState input).workTapeSymbols src = none := by
      simp only [Cfg.workTapeSymbols, Pi.add_apply, shift, true_or, ↓reduceIte, hTsrc]
      rw [hsrc _ le_rfl]; simp
    rw [← hT]
    simp only [copyTr, hs]
    apply Cfg.ext
    · simp [moveAct]
    · simp [moveAct]
    · funext i
      simp [Action.apply_workTapes, moveAct_write]
    · funext i
      simp only [Action.apply_workTapePos, moveAct_move, Pi.add_apply, shift]
      split_ifs <;> simp; ring
    · simp [moveAct]
  -- back
  have h3 := copy_back (src := src) (dst := dst)
    ({ c with
        state := some CopyState.back
        workTapes := T
        workTapePos := c.workTapePos + shift src dst ((w.length : ℤ) - 1) } :
      Cfg k Bool CopyState input) rfl w.length (fun i hi => by
        simp only [Pi.add_apply, shift, true_or, ↓reduceIte, hTsrc]
        have := hsrc (w.length - 1 - i) (by omega)
        rw [show c.workTapePos src + ((w.length : ℤ) - 1) - i =
          c.workTapePos src + ((w.length - 1 - i : ℕ) : ℤ) by push_cast [Nat.sub_sub]; omega, this]
        simp; omega)
  -- the halt
  dsimp only at h3
  have e : ∀ (x : Cfg k Bool CopyState input) (n : ℕ),
      (copyTM src dst).step^[n] x = (copyTM src dst).runFrom x n := fun _ _ => rfl
  rw [show 2 * w.length + 2 = 1 + (w.length + (1 + w.length)) by ring, runFrom,
    Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_one, e c, h2, e, h3]
  have hs : ({ c with
        state := some CopyState.back
        workTapes := T
        workTapePos := c.workTapePos + shift src dst ((w.length : ℤ) - 1) +
          shift src dst (-(w.length : ℤ)) } :
      Cfg k Bool CopyState input).workTapeSymbols src = none := by
    simp only [Cfg.workTapeSymbols, Pi.add_apply, shift, true_or, ↓reduceIte, hTsrc]
    rw [← hleft]; ring_nf
  rw [step_of_state (q := .back) rfl, copyTM, tr_ofTr]
  simp only [copyTr, hs]
  apply Cfg.ext
  · simp [moveAct]
  · simp [moveAct]
  · funext i
    simp [Action.apply_workTapes, moveAct_write]
  · funext i
    simp only [Action.apply_workTapePos, moveAct_move, Pi.add_apply, shift]
    split_ifs <;> simp; ring
  · simp [moveAct]

end Correct

/-! ## Copying onto the output tape -/

/-- The actions of the emitting machine: only the head of `src` moves, by `m`, nothing is written,
and `o` is appended to the output. -/
def emitAct (src : Fin k) (m : SignType) (o : Option Bool) (q : Option CopyState) :
    Action k Bool CopyState :=
  ⟨0, fun i => if i = src then (none, m) else (none, 0), o, q⟩

theorem emitAct_write {src : Fin k} {m : SignType} {o : Option Bool} {q : Option CopyState}
    (i : Fin k) : ((emitAct src m o q).workTapes i).1 = none := by
  simp only [emitAct]; split_ifs <;> rfl

theorem emitAct_move {src : Fin k} {m : SignType} {o : Option Bool} {q : Option CopyState}
    (i : Fin k) : ((emitAct src m o q).workTapes i).2 = if i = src then m else 0 := by
  simp only [emitAct]; split_ifs <;> rfl

/-- The transition function of the emitting machine. -/
def emitTr (src : Fin k) :
    CopyState → Option Bool → (Fin k → Option Bool) → Action k Bool CopyState
  | .fwd, _, w => match w src with
    | some b => emitAct src 1 (some b) (some .fwd)
    | none => emitAct src (-1) none (some .back)
  | .back, _, w => match w src with
    | some _ => emitAct src (-1) none (some .back)
    | none => emitAct src 1 none none

/-- **The emitting machine**: appends the word under the head of `src` to the output tape, and
brings the head back. -/
def emitTM (src : Fin k) : MultiTapeTM k Bool CopyState :=
  ofTr .fwd (emitTr src)

/-- **The emitting machine is reversible.** -/
theorem emitTM_isReversible (src : Fin k) : IsReversible (emitTM src) := by
  intro input c c' hc hc' hstep
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  rw [step_of_state hq, step_of_state hq', emitTM, tr_ofTr, tr_ofTr] at hstep
  have hsym : ∀ {m o o' r r'},
      ((emitAct src m o r).apply c = (emitAct src m o' r').apply c') →
        c.workTapeSymbols src = c'.workTapeSymbols src := fun h => by
    simp only [Cfg.workTapeSymbols,
      workTapes_eq_of_apply (i := src) (emitAct_write _) (emitAct_write _) h,
      workTapePos_eq_of_apply (fun i => by rw [emitAct_move, emitAct_move]) h]
  have hst := congrArg Cfg.state hstep
  rcases q with _ | _ <;> rcases q' with _ | _ <;>
    rcases hs : c.workTapeSymbols src with _ | b <;>
    rcases hs' : c'.workTapeSymbols src with _ | b' <;>
    simp only [emitTr, hs, hs'] at hstep hst <;>
    simp only [emitAct, Action.apply_state, reduceCtorEq, Option.some.injEq] at hst
  · exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl)
      (fun i => Or.inl (emitAct_write i)) hstep
  · have hb : b = b' := by
      have := hsym hstep
      rw [hs, hs'] at this
      exact Option.some.inj this
    subst hb
    exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl)
      (fun i => Or.inl (emitAct_write i)) hstep
  · have := hsym hstep
    rw [hs, hs'] at this
    exact absurd this (by simp)
  · have := hsym hstep
    rw [hs, hs'] at this
    exact absurd this (by simp)
  · exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl)
      (fun i => Or.inl (emitAct_write i)) hstep
  · exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl)
      (fun i => Or.inl (emitAct_write i)) hstep

/-- The move of the head of `src` alone. -/
def shift1 (src : Fin k) (n : ℤ) : Fin k → ℤ := fun i => if i = src then n else 0

section Emit

variable {src : Fin k} {input : List Bool}

/-- The forward phase of the emitting machine. -/
theorem emit_fwd (c : Cfg k Bool CopyState input) (w : List Bool) (hst : c.state = some .fwd)
    (hsrc : ∀ i : ℕ, i ≤ w.length → c.workTapes src (c.workTapePos src + i) = w[i]?)
    (n : ℕ) (hn : n ≤ w.length) :
    (emitTM src).runFrom c n =
      { c with
        workTapePos := c.workTapePos + shift1 src n
        output := c.output ++ w.take n } := by
  induction n with
  | zero =>
    apply Cfg.ext <;> simp [runFrom]
    funext i; simp [shift1]
  | succ n ih =>
    have hlt : n < w.length := by omega
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega)]
    have hs : ({ c with
        workTapePos := c.workTapePos + shift1 src n
        output := c.output ++ w.take n } : Cfg k Bool CopyState input).workTapeSymbols src =
          some w[n] := by
      simp only [Cfg.workTapeSymbols, Pi.add_apply, shift1, ↓reduceIte]
      rw [hsrc n hlt.le, List.getElem?_eq_getElem hlt]
    rw [step_of_state (q := .fwd) hst, emitTM, tr_ofTr]
    simp only [emitTr, hs]
    apply Cfg.ext
    · simp [emitAct, hst]
    · simp [emitAct]
    · funext i
      simp [Action.apply_workTapes, emitAct_write]
    · funext i
      simp only [Action.apply_workTapePos, emitAct_move, Pi.add_apply, shift1]
      split_ifs <;> simp; ring
    · simp only [Action.apply_output, emitAct, Option.toList_some]
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, List.append_assoc]
      rfl

/-- The back phase of the emitting machine. -/
theorem emit_back (c : Cfg k Bool CopyState input) (hst : c.state = some .back) (n : ℕ)
    (hsym : ∀ i : ℕ, i < n → c.workTapes src (c.workTapePos src - i) ≠ none) :
    (emitTM src).runFrom c n = { c with workTapePos := c.workTapePos + shift1 src (-n) } := by
  induction n with
  | zero =>
    apply Cfg.ext <;> simp [runFrom]
    funext i; simp [shift1]
  | succ n ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom,
      ih (fun i hi => hsym i (by omega))]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (hsym n (by omega))
    have hs : ({ c with workTapePos := c.workTapePos + shift1 src (-n) } :
        Cfg k Bool CopyState input).workTapeSymbols src = some b := by
      simp only [Cfg.workTapeSymbols, Pi.add_apply, shift1, ↓reduceIte]
      rw [← hb]; ring_nf
    rw [step_of_state (q := .back) hst, emitTM, tr_ofTr]
    simp only [emitTr, hs]
    apply Cfg.ext
    · simp [emitAct, hst]
    · simp [emitAct]
    · funext i
      simp [Action.apply_workTapes, emitAct_write]
    · funext i
      simp only [Action.apply_workTapePos, emitAct_move, Pi.add_apply, shift1]
      split_ifs <;> simp; ring
    · simp [emitAct]

/-- **The emitting machine is correct.** Started in `fwd` with the word `w` on `src` from its head
on and a blank before and after it, after `2 |w| + 2` steps it has halted with `w` appended to the
output, and nothing else changed. From the initial output `[]`, the output is `w`. -/
theorem emitTM_correct (c : Cfg k Bool CopyState input) (w : List Bool)
    (hst : c.state = some .fwd)
    (hsrc : ∀ i : ℕ, i ≤ w.length → c.workTapes src (c.workTapePos src + i) = w[i]?)
    (hleft : c.workTapes src (c.workTapePos src - 1) = none) :
    (emitTM src).runFrom c (2 * w.length + 2) =
      { c with
        state := none
        output := c.output ++ w } := by
  have h1 := emit_fwd c w hst hsrc w.length le_rfl
  rw [List.take_length] at h1
  have h2 : (emitTM src).step ((emitTM src).runFrom c w.length) =
      ({ c with
        state := some CopyState.back
        workTapePos := c.workTapePos + shift1 src ((w.length : ℤ) - 1)
        output := c.output ++ w } : Cfg k Bool CopyState input) := by
    rw [h1, step_of_state (q := .fwd) hst, emitTM, tr_ofTr]
    have hs : ({ c with
        workTapePos := c.workTapePos + shift1 src w.length
        output := c.output ++ w } : Cfg k Bool CopyState input).workTapeSymbols src = none := by
      simp only [Cfg.workTapeSymbols, Pi.add_apply, shift1, ↓reduceIte]
      rw [hsrc _ le_rfl]; simp
    simp only [emitTr, hs]
    apply Cfg.ext
    · simp [emitAct]
    · simp [emitAct]
    · funext i
      simp [Action.apply_workTapes, emitAct_write]
    · funext i
      simp only [Action.apply_workTapePos, emitAct_move, Pi.add_apply, shift1]
      split_ifs <;> simp; ring
    · simp [emitAct]
  have h3 := emit_back (src := src)
    ({ c with
        state := some CopyState.back
        workTapePos := c.workTapePos + shift1 src ((w.length : ℤ) - 1)
        output := c.output ++ w } : Cfg k Bool CopyState input) rfl w.length (fun i hi => by
        simp only [Pi.add_apply, shift1, ↓reduceIte]
        have := hsrc (w.length - 1 - i) (by omega)
        rw [show c.workTapePos src + ((w.length : ℤ) - 1) - i =
          c.workTapePos src + ((w.length - 1 - i : ℕ) : ℤ) by push_cast [Nat.sub_sub]; omega, this]
        simp; omega)
  dsimp only at h3
  have e : ∀ (x : Cfg k Bool CopyState input) (n : ℕ),
      (emitTM src).step^[n] x = (emitTM src).runFrom x n := fun _ _ => rfl
  rw [show 2 * w.length + 2 = 1 + (w.length + (1 + w.length)) by ring, runFrom,
    Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_one, e c, h2, e, h3]
  have hs : ({ c with
        state := some CopyState.back
        workTapePos := c.workTapePos + shift1 src ((w.length : ℤ) - 1) +
          shift1 src (-(w.length : ℤ))
        output := c.output ++ w } : Cfg k Bool CopyState input).workTapeSymbols src = none := by
    simp only [Cfg.workTapeSymbols, Pi.add_apply, shift1, ↓reduceIte]
    rw [← hleft]; ring_nf
  rw [step_of_state (q := .back) rfl, emitTM, tr_ofTr]
  simp only [emitTr, hs]
  apply Cfg.ext
  · simp [emitAct]
  · simp [emitAct]
  · funext i
    simp [Action.apply_workTapes, emitAct_write]
  · funext i
    simp only [Action.apply_workTapePos, emitAct_move, Pi.add_apply, shift1]
    split_ifs <;> simp; ring
  · simp [emitAct]

end Emit

/-! ## Checks: the axioms, and one mutant per central theorem -/

/-- info: 'Sagitta.Arrow.TM.Bennett.copyTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.copyTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.copyTM_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.copyTM_correct
/-- info: 'Sagitta.Arrow.TM.Bennett.copyTM_self_not_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.copyTM_self_not_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.emitTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.emitTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.emitTM_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.emitTM_correct

section Mutants

set_option linter.unusedVariables false
set_option linter.unreachableTactic false

/-- Mutant of `copyTM_isReversible`: without `src ≠ dst` (copying a tape onto itself forgets). -/
example (src dst : Fin k) : True := by
  fail_if_success
    have : IsReversible (copyTM src dst) := copyTM_isReversible (by assumption)
  trivial

/-- Mutant of `copyTM_self_not_isReversible`: two different tapes. -/
example (src dst : Fin k) : True := by
  fail_if_success
    have : ¬IsReversible (copyTM src dst) := copyTM_self_not_isReversible src
  trivial

/-- Mutant of `copyTM_correct`: without a clean destination. -/
example {input : List Bool} (src dst : Fin k) (hsd : src ≠ dst) (c : Cfg k Bool CopyState input)
    (w : List Bool) (hst : c.state = some .fwd)
    (hsrc : ∀ i : ℕ, i ≤ w.length → c.workTapes src (c.workTapePos src + i) = w[i]?)
    (hleft : c.workTapes src (c.workTapePos src - 1) = none) : True := by
  fail_if_success
    have := copyTM_correct hsd c w hst hsrc hleft (by assumption)
  trivial

/-- Mutant of `emitTM_isReversible`: injective on halted configurations too. -/
example {input : List Bool} (src : Fin k) : True := by
  fail_if_success
    have : ∀ c c' : Cfg k Bool CopyState input, (emitTM src).step c = (emitTM src).step c' →
        c = c' := fun c c' h => emitTM_isReversible src input c c' (by assumption)
          (by assumption) h
  trivial

/-- Mutant of `emitTM_correct`: one step earlier. -/
example {input : List Bool} (src : Fin k) (c : Cfg k Bool CopyState input) (w : List Bool)
    (hst : c.state = some .fwd)
    (hsrc : ∀ i : ℕ, i ≤ w.length → c.workTapes src (c.workTapePos src + i) = w[i]?)
    (hleft : c.workTapes src (c.workTapePos src - 1) = none) : True := by
  fail_if_success
    have : (emitTM src).runFrom c (2 * w.length + 1) =
        { c with state := none, output := c.output ++ w } := emitTM_correct c w hst hsrc hleft
  trivial

end Mutants

end Sagitta.Arrow.TM.Bennett
