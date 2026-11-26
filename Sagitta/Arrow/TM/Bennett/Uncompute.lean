/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.Inverse

/-!
# Bennett, step 4 (continued): a reversible inverse

`invTM` (in `Inverse.lean`) undoes the history machine, but it is not itself reversible, and step 5
needs to compose `M₁`, the copy and `M₁⁻¹` into **one reversible machine**. This file builds
`uncTM tm code`, an inverse that is reversible (`uncTM_isReversible`, with no hypothesis) and
correct (`uncTM_correct`).

## Two obstructions, and how they shape the machine

* **The inverse must carry the forward state.** `invTM` erases a record and keeps nothing of the
  state of the forward machine: two different records can lead to the same configuration, so its
  step is not injective. Here the inverse is in the state `back q` exactly when the forward machine
  was in `q` (`q = none` when it had halted). Then erasing the record `(q, r, w)` loses nothing:
  `q` is in the state, and `r` and `w` are the symbols under the heads once the step is undone.
* **The inverse cannot move the input head.** The inverse of a forward step that moved the input
  head onto a blank (the end of the input) moves it *off* a blank, and a reversible machine never
  does that (`IsReversible.staysOnBlank`). So `uncTM` never moves the input head, and its
  correctness assumes that `tm` never does either (`InputFixed`). In Bennett's construction this is
  the normal form of step 2b: copy the input to a work tape first, then simulate on the copy; the
  copy of the input is not undone.

The configurations that no run reaches (a record that does not match the tapes, a state that does
not match the record) go, as in the history machine, to a **sink** `.inr s` that remembers the
state `s`: the first step appends `false` to the output, the sink appends `true` forever.

## The machine

* `back q`: move the history heads one cell left, onto the last record; go to `peek q`.
* `peek q`: read the record `rec = (q₁, r, w)`. If the forward step it records led to `q`
  (`(tm.tr q₁ r w).state = q`), erase it, move the work heads back by the opposite of the move of
  that step, and go to `restore rec`. If there is no record and `q` is the initial state, move the
  history heads back right and **halt**. Otherwise, the sink.
* `restore (q₁, r, w)`: if the input head reads `r` and every work head reads what the step left
  there (`expected`), write back `w` and go to `back (some q₁)`. Otherwise, the sink.

`t` forward steps are undone in `3 t + 2` steps.

## Results

* `uncTM_isReversible`: the inverse is reversible, for every `tm` and every `code`.
* `uncTM_back`: from a clean running configuration `c` of the history machine, three steps of the
  inverse take the mirror of the step (`mirror`) back to the mirror of `c`.
* `uncTM_correct`: from the configuration of the history machine after `t` running steps, in the
  state `back` of its own state, the inverse reaches the initial configuration, halted, in
  `3 t + 2` steps, with the output untouched.
* `uncompute`: both, packaged with the one-hot code.
-/

namespace Sagitta.Arrow.TM.Bennett

open Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type}

/-- A machine that **never moves its input head**. -/
def InputFixed (tm : MultiTapeTM k Bool State) : Prop :=
  ∀ (q : State) (r : Option Bool) (w : Fin k → Option Bool), (tm.tr q r w).inputTape = 0

theorem InputFixed.staysOnBlank {tm : MultiTapeTM k Bool State} (h : InputFixed tm) :
    StaysOnBlank tm := fun q w => h q none w

/-- The states of the reversible inverse (outside the sink). -/
inductive UncState (k : ℕ) (State : Type)
  /-- The forward machine was in `q`: move onto the last record. -/
  | back (q : Option State)
  /-- Read the record, check it against `q`, erase it and move back. -/
  | peek (q : Option State)
  /-- Check and write back the symbols that the step read. -/
  | restore (rec : Record k State)

instance [Finite State] : Finite (UncState k State) :=
  Finite.of_injective (β := Option State ⊕ Option State ⊕ Record k State)
    (fun s => match s with
      | .back q => .inl q
      | .peek q => .inr (.inl q)
      | .restore rec => .inr (.inr rec))
    (by intro a b; cases a <;> cases b <;> simp)

/-- What a step leaves under work head `i`: the symbol written, or the symbol read. -/
noncomputable def expected (tm : MultiTapeTM k Bool State) (rec : Record k State) (i : Fin k) :
    Option Bool :=
  ((tm.tr rec.1 rec.2.1 rec.2.2).workTapes i).1.getD (rec.2.2 i)

section Machine

variable {h : ℕ}

/-- No move and no write. -/
def idleMoves : Fin (k + h) → Option (Option Bool) × SignType := fun _ => (none, 0)

/-- The first step into the sink: append `false`. -/
def uFail (s : UncState k State) : Action (k + h) Bool (UncState k State ⊕ UncState k State) :=
  ⟨0, idleMoves, some false, some (.inr s)⟩

/-- The sink: append `true`, stay. -/
def uSink (s : UncState k State) : Action (k + h) Bool (UncState k State ⊕ UncState k State) :=
  ⟨0, idleMoves, some true, some (.inr s)⟩

/-- Move the history heads onto the last record. -/
def uBack (q : Option State) : Action (k + h) Bool (UncState k State ⊕ UncState k State) :=
  ⟨0, histMoves h (-1), none, some (.inl (.peek q))⟩

/-- Move the history heads back right, and halt. -/
def uFinish : Action (k + h) Bool (UncState k State ⊕ UncState k State) :=
  ⟨0, histMoves h 1, none, none⟩

/-- Erase the record and move the work heads back. -/
noncomputable def uUndo (tm : MultiTapeTM k Bool State) (rec : Record k State) :
    Action (k + h) Bool (UncState k State ⊕ UncState k State) :=
  ⟨0, Fin.addCases (motive := fun _ => Option (Option Bool) × SignType)
      (fun i => (none, -((tm.tr rec.1 rec.2.1 rec.2.2).workTapes i).2)) (fun _ => (some none, 0)),
    none, some (.inl (.restore rec))⟩

/-- Write back the symbols read. -/
def uRestore (rec : Record k State) : Action (k + h) Bool (UncState k State ⊕ UncState k State) :=
  ⟨0, Fin.addCases (motive := fun _ => Option (Option Bool) × SignType)
      (fun i => (some (rec.2.2 i), 0)) (fun _ => (none, 0)),
    none, some (.inl (.back (some rec.1)))⟩

open Classical in
/-- The action in the state `peek q`, after reading the record (if any). -/
noncomputable def uPeek (tm : MultiTapeTM k Bool State) (q : Option State) :
    Option (Record k State) → Action (k + h) Bool (UncState k State ⊕ UncState k State)
  | some rec => if (tm.tr rec.1 rec.2.1 rec.2.2).state = q then uUndo tm rec else uFail (.peek q)
  | none => if q = some tm.q₀ then uFinish else uFail (.peek q)

open Classical in
/-- The transition function of the reversible inverse. -/
noncomputable def uncTr (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool) :
    UncState k State ⊕ UncState k State → Option Bool → (Fin (k + h) → Option Bool) →
      Action (k + h) Bool (UncState k State ⊕ UncState k State)
  | .inl (.back q), _, _ => uBack q
  | .inl (.peek q), _, v => uPeek tm q (decode code fun j => v (histTape k j))
  | .inl (.restore rec), r, v =>
    if r = rec.2.1 ∧ ∀ i, v (mainTape h i) = expected tm rec i then uRestore rec
    else uFail (.restore rec)
  | .inr s, _, _ => uSink s

/-- **The reversible inverse of the machine with a history.** -/
noncomputable def uncTM (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool) :
    MultiTapeTM (k + h) Bool (UncState k State ⊕ UncState k State) :=
  ofTr (.inl (.back none)) (uncTr tm code)

end Machine

/-! ## Reading a record back -/

theorem decode_some {h : ℕ} {code : Record k State → Fin h → Bool} {v : Fin h → Option Bool}
    {rec : Record k State} (hd : decode code v = some rec) : v = fun j => some (code rec j) := by
  unfold decode at hd
  split_ifs at hd with hv
  · rw [← Option.some.inj hd]
    exact hv.choose_spec.symm


/-! ## The inverse is reversible -/

theorem uncTM_isReversible {h : ℕ} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) : IsReversible (uncTM tm code) := by
  intro input c c' hc hc' hstep
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.mp hc'
  revert hstep
  rw [step_of_state hs, step_of_state hs', uncTM, tr_ofTr, tr_ofTr]
  rcases s with (q | q | rec) | u <;> rcases s' with (q' | q' | rec') | u' <;>
    simp only [uncTr, uPeek] <;> (repeat' split) <;> intro hstep <;>
    have hst := congrArg Cfg.state hstep <;> have hout := congrArg Cfg.output hstep <;>
    simp only [Action.apply_state, Action.apply_output, uBack, uUndo, uFinish, uRestore, uFail,
      uSink, reduceCtorEq, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq, UncState.back.injEq,
      UncState.peek.injEq, UncState.restore.injEq, Option.toList] at hst hout <;>
    try first
      | (have := congrArg List.getLast? hout; simp at this; done)
      | (try subst hst
         refine apply_injective _ ?_ (Or.inl rfl) ?_ hstep
         · simp_all
         · intro i
           left
           induction i using Fin.addCases <;>
             simp [uBack, uFinish, uFail, uSink, histMoves, idleMoves])
  · -- two undo steps: the record is in the state, and the history cells held its code
    rename_i _ r1 hd1 g1 _ r2 hd2 g2
    subst hst
    obtain rfl : q = q' := g1.symm.trans g2
    refine apply_injective _ (hs.trans hs'.symm) (Or.inl rfl) ?_ hstep
    intro i
    induction i using Fin.addCases with
    | left i => left; simp [uUndo]
    | right j =>
      right
      exact (congrFun (decode_some hd1) j).trans (congrFun (decode_some hd2) j).symm
  · -- two restore steps: the target tells the record, and the guards the symbols overwritten
    rename_i g1 g2
    have hip : c.inputPos = c'.inputPos := by
      simpa [uRestore] using congrArg Cfg.inputPos hstep
    have hsym : c.inputSymbol = c'.inputSymbol := by
      simp only [Cfg.inputSymbol, hip]
    have hpos (i : Fin k) : c.workTapePos (mainTape h i) = c'.workTapePos (mainTape h i) := by
      simpa [uRestore] using congrFun (congrArg Cfg.workTapePos hstep) (mainTape h i)
    have hw (i : Fin k) : rec.2.2 i = rec'.2.2 i := by
      have := congrFun (congrFun (congrArg Cfg.workTapes hstep) (mainTape h i))
        (c.workTapePos (mainTape h i))
      simpa [uRestore, hpos i] using this
    obtain rfl : rec = rec' := by
      obtain ⟨q1, r1, w1⟩ := rec
      obtain ⟨q2, r2, w2⟩ := rec'
      simp only at hst hw g1 g2
      subst hst
      have : r1 = r2 := g1.1.symm.trans (hsym.trans g2.1)
      subst this
      have : w1 = w2 := funext hw
      subst this
      rfl
    refine apply_injective _ (hs.trans hs'.symm) (Or.inl rfl) ?_ hstep
    intro i
    induction i using Fin.addCases with
    | left i => right; exact (g1.2 i).trans (g2.2 i).symm
    | right j => left; simp [uRestore]


/-! ## The inverse is correct -/

/-- The **mirror** of a configuration of the history machine: the inverse in the state `back` of
the state of the forward machine (`none` if it halted), with the same tapes and heads and the
output `out`. -/
def mirror {h : ℕ} {input : List Bool} (c : Cfg (k + h) Bool (State ⊕ State) input)
    (out : List Bool) : Cfg (k + h) Bool (UncState k State ⊕ UncState k State) input :=
  ⟨some (.inl (.back (c.state.bind Sum.getLeft?))), c.inputPos, c.workTapes, c.workTapePos, out⟩

/-- The same tapes and heads, halted, with the output `out`. -/
def halted {h : ℕ} {input : List Bool} (c : Cfg (k + h) Bool (State ⊕ State) input)
    (out : List Bool) : Cfg (k + h) Bool (UncState k State ⊕ UncState k State) input :=
  ⟨none, c.inputPos, c.workTapes, c.workTapePos, out⟩

theorem inputSymbol_congr {k' : ℕ} {S : Type} {input : List Bool} {c : Cfg k' Bool S input}
    {S' : Type} {d : Cfg k' Bool S' input} (h : c.inputPos = d.inputPos) :
    c.inputSymbol = d.inputSymbol := by
  simp only [Cfg.inputSymbol, h]

section Correctness

variable {h : ℕ} {tm : MultiTapeTM k Bool State} {code : Record k State → Fin h → Bool}
  {input : List Bool}

/-- **Three steps of the inverse undo one step of the history machine**, from the mirror of the
step to the mirror of a clean running configuration. -/
theorem uncTM_back (hfix : InputFixed tm) (hcode : Function.Injective code)
    {c : Cfg (k + h) Bool (State ⊕ State) input} (hc : Clean c) {q : State}
    (hq : c.state = some (.inl q)) (out : List Bool) :
    (uncTM tm code).runFrom (mirror ((histTM tm code).step c) out) 3 = mirror c out := by
  set r := c.inputSymbol with hr
  set ws : Fin k → Option Bool := fun i => c.workTapeSymbols (mainTape h i) with hws
  set rec : Record k State := (q, r, ws) with hrec
  set a := tm.tr q r ws with ha
  have ha0 : a.inputTape = 0 := hfix q r ws
  rw [histTM_step_good hc hq]
  set c' := (goodAction tm code q r ws).apply c with hc'
  have hst' : c'.state.bind Sum.getLeft? = a.state := by
    simp only [hc', Action.apply_state, goodAction]
    cases a.state <;> rfl
  have h1 : (uncTM tm code).step (mirror c' out) = (uBack a.state).apply (mirror c' out) := by
    rw [step_of_state (q := .inl (.back a.state)) (by simp only [mirror, hst']), uncTM, tr_ofTr,
      uncTr]
  set d1 := (uBack (h := h) a.state).apply (mirror c' out) with hd1
  have hread : (decode code fun j => d1.workTapeSymbols (histTape k j)) = some rec := by
    have : (fun j => d1.workTapeSymbols (histTape k j)) = fun j => some (code rec j) := by
      funext j
      simp [hd1, mirror, Cfg.workTapeSymbols, hc', goodAction, uBack, histMoves]
      rfl
    rw [this, decode_code hcode]
  have h2 : (uncTM tm code).step d1 = (uUndo tm rec).apply d1 := by
    rw [step_of_state (q := .inl (.peek a.state)) rfl, uncTM, tr_ofTr, uncTr, hread, uPeek,
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  set d2 := (uUndo (h := h) tm rec).apply d1 with hd2
  have hip : d2.inputPos = c.inputPos := by
    simp [hd2, hd1, uUndo, uBack, mirror, hc', goodAction, ← ha, ha0]
  have hguard : d2.inputSymbol = rec.2.1 ∧
      ∀ i, d2.workTapeSymbols (mainTape h i) = expected tm rec i := by
    refine ⟨inputSymbol_congr hip, fun i => ?_⟩
    simp only [Cfg.workTapeSymbols, hd2, hd1, Action.apply_workTapes, Action.apply_workTapePos,
      uUndo, uBack, histMoves, mirror, hc', goodAction, Fin.addCases_left, expected, hrec,
      signType_cast_zero, add_zero, signType_cast_neg, add_neg_cancel_right]
    rcases hw : ((tm.tr q r ws).workTapes i).1 with _ | s
    · rfl
    · simp
  have h3 : (uncTM tm code).step d2 = (uRestore rec).apply d2 := by
    rw [step_of_state (q := .inl (.restore rec)) rfl, uncTM, tr_ofTr, uncTr, ite_eq_left_of_eq_true _ _ (eq_true hguard)]
  have hrun : (uncTM tm code).runFrom (mirror c' out) 3 = (uRestore rec).apply d2 := by
    rw [runFrom, Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one,
      h1, h2, h3]
  rw [hrun]
  apply Cfg.ext
  · simp [uRestore, mirror, hq, hrec]
  · simpa [uRestore, mirror] using hip
  · funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [Action.apply_workTapes, Action.apply_workTapePos, uRestore, hd2, hd1, uUndo,
        uBack, histMoves, mirror, hc', goodAction, Fin.addCases_left, hrec, signType_cast_zero,
        add_zero, signType_cast_neg, add_neg_cancel_right]
      rcases hw : ((tm.tr q r ws).workTapes i).1 with _ | s
      · exact Function.update_eq_self_iff.mpr rfl
      · simp only [Function.update_idem]
        exact Function.update_eq_self_iff.mpr rfl
    | right j =>
      simp only [Action.apply_workTapes, Action.apply_workTapePos, uRestore, hd2, hd1, uUndo,
        uBack, histMoves, mirror, hc', goodAction, Fin.addCases_right, signType_cast_neg,
        signType_cast_one, add_neg_cancel_right, Function.update_idem]
      exact Function.update_eq_self_iff.mpr (hc.2 j _ le_rfl).symm
  · funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [Action.apply_workTapePos, uRestore, hd2, hd1, uUndo, uBack, histMoves, mirror,
        hc', goodAction, Fin.addCases_left, hrec, signType_cast_zero, add_zero, signType_cast_neg,
        add_neg_cancel_right]
    | right j =>
      simp only [Action.apply_workTapePos, uRestore, hd2, hd1, uUndo, uBack, histMoves, mirror,
        hc', goodAction, Fin.addCases_right, signType_cast_zero, add_zero, signType_cast_neg,
        signType_cast_one, add_neg_cancel_right]
  · simp [uRestore, hd2, hd1, uUndo, uBack, mirror]


/-- **The last two steps of the inverse.** From the mirror of a configuration in the initial state
whose history cells to the left of the heads are blank, the inverse moves onto them, finds no
record, moves back and halts. -/
theorem uncTM_finish (hh : 0 < h) {c : Cfg (k + h) Bool (State ⊕ State) input}
    (hq : c.state = some (.inl tm.q₀))
    (hb : ∀ j : Fin h, c.workTapes (histTape k j) (c.workTapePos (histTape k j) - 1) = none)
    (out : List Bool) :
    (uncTM tm code).runFrom (mirror c out) 2 = halted c out := by
  have hs : (mirror (h := h) c out).state = some (.inl (.back (some tm.q₀))) := by
    simp [mirror, hq]
  have h1 : (uncTM tm code).step (mirror c out) = (uBack (some tm.q₀)).apply (mirror c out) := by
    rw [step_of_state hs, uncTM, tr_ofTr, uncTr]
  set d1 := (uBack (h := h) (some tm.q₀)).apply (mirror c out) with hd1
  have hread : (decode code fun j => d1.workTapeSymbols (histTape k j)) = none := by
    have : (fun j => d1.workTapeSymbols (histTape k j)) = fun _ => none := by
      funext j
      simpa [hd1, mirror, Cfg.workTapeSymbols, uBack, histMoves, sub_eq_add_neg] using hb j
    rw [this, decode_blank code hh]
  have h2 : (uncTM tm code).step d1 = uFinish.apply d1 := by
    rw [step_of_state (q := .inl (.peek (some tm.q₀))) rfl, uncTM, tr_ofTr, uncTr, hread, uPeek,
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rw [runFrom, Function.iterate_succ_apply', Function.iterate_one, h1, h2]
  apply Cfg.ext
  · rfl
  · simp [hd1, uFinish, uBack, mirror, halted]
  · funext i
    induction i using Fin.addCases <;> simp [hd1, uFinish, uBack, mirror, halted, histMoves]
  · funext i
    induction i using Fin.addCases <;> simp [hd1, uFinish, uBack, mirror, halted, histMoves]
  · simp [hd1, uFinish, uBack, mirror, halted]

/-- **The inverse undoes a run**: along `t` running steps of the history machine from a clean
configuration, `3 t` steps of the inverse go back. -/
theorem uncTM_runBack (hfix : InputFixed tm) (hcode : Function.Injective code)
    {c₀ : Cfg (k + h) Bool (State ⊕ State) input} (hc₀ : Clean c₀) (out : List Bool) :
    ∀ t : ℕ, (∀ i < t, ¬((histTM tm code).runFrom c₀ i).Halted) →
      (uncTM tm code).runFrom (mirror ((histTM tm code).runFrom c₀ t) out) (3 * t) =
        mirror c₀ out
  | 0, _ => rfl
  | t + 1, hrun => by
    have hc := (runFrom_clean (tm := tm) (code := code) hc₀ t).2
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (hrun t (by omega))
    rcases x with q | q
    · have e1 : (histTM tm code).runFrom c₀ (t + 1) =
          (histTM tm code).step ((histTM tm code).runFrom c₀ t) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : ∀ x : Cfg (k + h) Bool (UncState k State ⊕ UncState k State) input,
          (uncTM tm code).runFrom x (3 * (t + 1)) =
            (uncTM tm code).runFrom ((uncTM tm code).runFrom x 3) (3 * t) := fun x =>
        Function.iterate_add_apply _ _ _ _
      rw [e1, e2, uncTM_back hfix hcode hc hx out]
      exact uncTM_runBack hfix hcode hc₀ out t fun i hi => hrun i (by omega)
    · exact absurd hx (hc.1 q)

/-- **Correctness of the reversible inverse.** If the history machine runs `t` steps from the
initial configuration without halting before, the inverse, started on the mirror of the
configuration reached, reaches in `3 t + 2` steps the initial configuration, halted, with the
output `out` untouched. -/
theorem uncTM_correct (hfix : InputFixed tm) (hcode : Function.Injective code) (hh : 0 < h)
    (t : ℕ) (hrun : ∀ i < t, ¬((histTM tm code).runFrom ((histTM tm code).initCfg input) i).Halted)
    (out : List Bool) :
    (uncTM tm code).runFrom (mirror ((histTM tm code).runFrom ((histTM tm code).initCfg input) t) out)
        (3 * t + 2) =
      halted ((histTM tm code).initCfg input) out := by
  have hc₀ : Clean ((histTM tm code).initCfg input) := init_clean tm.q₀
  have e : ∀ x : Cfg (k + h) Bool (UncState k State ⊕ UncState k State) input,
      (uncTM tm code).runFrom x (3 * t + 2) =
        (uncTM tm code).runFrom ((uncTM tm code).runFrom x (3 * t)) 2 := fun x =>
    (congrArg (fun n => (uncTM tm code).step^[n] x) (add_comm (3 * t) 2)).trans
      (Function.iterate_add_apply _ _ _ _)
  rw [e, uncTM_runBack hfix hcode hc₀ out t hrun]
  exact uncTM_finish hh rfl (fun j => rfl) out

/-- **Correctness, from the machine simulated**: the hypothesis on `tm` instead of the history
machine. -/
theorem uncTM_correct_of_tm (hfix : InputFixed tm) (hcode : Function.Injective code) (hh : 0 < h)
    (t : ℕ) (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted) (out : List Bool) :
    (uncTM tm code).runFrom (mirror ((histTM tm code).runFrom ((histTM tm code).initCfg input) t) out)
        (3 * t + 2) =
      halted ((histTM tm code).initCfg input) out :=
  uncTM_correct hfix hcode hh t (fun i hi => (histTM_halted_iff i).not.mpr (hrun i hi)) out

end Correctness

/-- **Step 4 of Bennett's construction, reversible.** For a machine with finitely many states that
never moves its input head, the history machine with the one-hot code has an inverse with finitely
many states that is **reversible** and, from the mirror of the configuration reached after `t`
running steps of `tm`, goes back to the initial configuration (halted) in `3 t + 2` steps. -/
theorem uncompute [Finite State] (tm : MultiTapeTM k Bool State) (hfix : InputFixed tm) :
    IsReversible (uncTM tm (oneHot (Record k State))) ∧
      ∀ (input : List Bool) (t : ℕ), (∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted) →
        ∀ out : List Bool,
          (uncTM tm (oneHot (Record k State))).runFrom
              (mirror ((histTM tm (oneHot (Record k State))).runFrom
                ((histTM tm (oneHot (Record k State))).initCfg input) t) out) (3 * t + 2) =
            halted ((histTM tm (oneHot (Record k State))).initCfg input) out :=
  ⟨uncTM_isReversible tm _, fun _ t hrun out =>
    uncTM_correct_of_tm hfix (oneHot_injective _) (oneHot_pos tm.q₀) t hrun out⟩


/-! ## Checks: the axioms, and one mutant per central theorem -/

/-- info: 'Sagitta.Arrow.TM.Bennett.uncTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.uncTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.uncTM_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.uncTM_back
/-- info: 'Sagitta.Arrow.TM.Bennett.uncTM_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.uncTM_finish
/-- info: 'Sagitta.Arrow.TM.Bennett.uncTM_runBack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.uncTM_runBack
/-- info: 'Sagitta.Arrow.TM.Bennett.uncTM_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.uncTM_correct
/-- info: 'Sagitta.Arrow.TM.Bennett.uncTM_correct_of_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.uncTM_correct_of_tm
/-- info: 'Sagitta.Arrow.TM.Bennett.uncompute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.uncompute

section Mutants

set_option linter.unusedVariables false

/-- Mutant of `uncTM_isReversible`: the simple inverse `invTM` in its place. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool) : True := by
  fail_if_success
    have : IsReversible (invTM tm code) := uncTM_isReversible tm code
  trivial

/-- Mutant of `uncTM_back`: two steps of the inverse instead of three. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hfix : InputFixed tm) (hcode : Function.Injective code) {input : List Bool}
    (c : Cfg (k + h) Bool (State ⊕ State) input) (hc : Clean c) (q : State)
    (hq : c.state = some (.inl q)) (out : List Bool) : True := by
  fail_if_success
    have : (uncTM tm code).runFrom (mirror ((histTM tm code).step c) out) 2 = mirror c out :=
      uncTM_back hfix hcode hc hq out
  trivial

/-- Mutant of `uncTM_finish`: without the blank history cells. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hh : 0 < h) {input : List Bool} (c : Cfg (k + h) Bool (State ⊕ State) input)
    (hq : c.state = some (.inl tm.q₀)) (out : List Bool) : True := by
  fail_if_success
    have : (uncTM tm code).runFrom (mirror c out) 2 = halted c out :=
      uncTM_finish hh hq (by assumption) out
  trivial

/-- Mutant of `uncTM_runBack`: only "stays on a blank" instead of "never moves the input head". -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hstay : StaysOnBlank tm) (hcode : Function.Injective code) {input : List Bool}
    (c₀ : Cfg (k + h) Bool (State ⊕ State) input) (hc₀ : Clean c₀) (out : List Bool) : True := by
  fail_if_success
    have := uncTM_runBack (code := code) (by assumption) hcode hc₀ out
  trivial

/-- Mutant of `uncTM_correct`: one step fewer. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hfix : InputFixed tm) (hcode : Function.Injective code) (hh : 0 < h) (input : List Bool)
    (t : ℕ)
    (hrun : ∀ i < t, ¬((histTM tm code).runFrom ((histTM tm code).initCfg input) i).Halted)
    (out : List Bool) : True := by
  fail_if_success
    have : (uncTM tm code).runFrom
        (mirror ((histTM tm code).runFrom ((histTM tm code).initCfg input) t) out) (3 * t + 1) =
        halted ((histTM tm code).initCfg input) out :=
      uncTM_correct hfix hcode hh t hrun out
  trivial

/-- Mutant of `uncTM_correct_of_tm`: without a history tape (`0 < h`). -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hfix : InputFixed tm) (hcode : Function.Injective code) (input : List Bool) (t : ℕ)
    (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted) (out : List Bool) : True := by
  fail_if_success
    have := uncTM_correct_of_tm hfix hcode (by assumption) t hrun out
  trivial

/-- Mutant of `uncompute`: only "stays on a blank". -/
example [Finite State] (tm : MultiTapeTM k Bool State) (hstay : StaysOnBlank tm) : True := by
  fail_if_success
    have := uncompute tm (by assumption)
  trivial

end Mutants

end Sagitta.Arrow.TM.Bennett
