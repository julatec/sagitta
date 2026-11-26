/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.History

/-!
# Bennett, step 4: the inverse of the machine with a history

The machine with a history `histTM tm code` (step 2) keeps, for every step, the record of what the
step forgot. This file builds the machine `invTM tm code` that **undoes its steps**, reading the
records back from the history, and proves that from the final configuration of a run of the
history machine it reaches the initial one.

## Why not the general lemma

The plan asked first for the general lemma: every reversible machine has an inverse machine. In
cslib's model it is expensive, for a reason that shapes the construction here. An action of cslib
**writes under the heads and then moves them**; to undo it, a machine has to move the heads back
first and only then rewrite the cells, so one step of the forward machine costs at least two steps
of the inverse. And to know what to rewrite, the inverse needs the symbols that the forward step
read, which `IsReversible` (injectivity of the step on all running configurations) determines only
globally: turning that into a finite table of local transitions is the quadruple normal form of
Bennett, a construction of its own. For the machine with a history none of this is needed: the
record on the history tapes *is* the local information, written by the machine itself. So the
inverse is built only for `histTM`, which is the one Bennett's construction uses (`M₁⁻¹`).

## The inverse machine

Three kinds of states (`InvState`):

* `rewind`: the first step, moving the history heads one cell left, onto the last record.
* `read`: read the record `(q, r, w)` under the history heads (`decode`). With it the inverse knows
  the action `a = tm.tr q r w` of the forward step: it erases the record and moves every head back
  by the opposite of the move of `a`, and goes to `restore (q, r, w)`. If the history cells hold no
  record (blanks: the history is exhausted), it moves the history heads back right and halts.
* `restore (q, r, w)`: write back the symbols `w` that the forward step read (where `a` wrote
  nothing this rewrites the same symbol), and move the history heads one cell left, onto the
  previous record.

So `t` forward steps are undone in `2 t + 2` steps: one to start, two per step, one to stop.

## Results

* `invTM_back`: from a clean running configuration `c`, two steps of the inverse take the
  configuration "pending" after the step of the history machine (`pending`: the history heads one
  cell to the left) back to the one pending at `c`.
* `invTM_runBack`: the same along any run of `t` steps from a clean configuration: `2 t` steps.
* `invTM_correct`: **the correctness lemma.** From the configuration of the history machine after
  `t` running steps from the initial configuration, put in the state `rewind`, the inverse reaches
  in `2 t + 2` steps the initial configuration (halted), with every tape, head and the input head
  back, and the output untouched (`atRest`). `invTM_correct_of_tm` states the hypothesis on `tm`.

The output tape of cslib can only grow, so no machine undoes it: the inverse never writes on it,
and leaves it as the forward run left it. In Bennett's construction this is why the simulated
output goes to a work tape (step 2c of the log) and only the copy reaches the real output.

## Not done here

* The **reversibility of the inverse**, which step 5 needs to compose `M₁`, the copy and `M₁⁻¹`
  into one reversible machine. `invTM` is not built for it: it forgets the state of the forward
  machine. The reversible inverse is `uncTM`, in `Uncompute.lean`.
* The general lemma (above).
-/

namespace Sagitta.Arrow.TM.Bennett

open Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type}

/-! ## Two facts on moves -/

/-- The opposite move. -/
theorem signType_cast_neg (m : SignType) : ((-m : SignType) : ℤ) = -(m : ℤ) := by
  cases m <;> rfl

/-- No move. -/
theorem signType_cast_zero : ((0 : SignType) : ℤ) = 0 := rfl

/-- The move to the right. -/
theorem signType_cast_one : ((1 : SignType) : ℤ) = 1 := rfl

/-- **Moving the input head back.** A move followed by the opposite move returns the head, unless
the first move was clamped at the boundary; it is not when the head moves from the interior. -/
theorem moveInputPos_neg {n : ℕ} (p : Fin (n + 2)) (m : SignType)
    (h : m = 0 ∨ (p.val ≠ 0 ∧ p.val ≠ n + 1)) : moveInputPos (moveInputPos p m) (-m) = p := by
  apply Fin.ext
  have e1 := val_moveInputPos_eq p m
  have e2 := val_moveInputPos_eq (moveInputPos p m) (-m)
  have hlt := p.isLt
  rw [signType_cast_neg] at e2
  have hz : (m : ℤ) = 0 ∨ (m : ℤ) = 1 ∨ (m : ℤ) = -1 := by rcases m with _ | _ | _ <;> simp
  have h' : (m : ℤ) = 0 ∨ (p.val ≠ 0 ∧ p.val ≠ n + 1) := h.imp_left fun h0 => by simp [h0]
  generalize (m : ℤ) = z at *
  generalize moveInputPos p m = p' at *
  omega

/-! ## The inverse machine -/

/-- The states of the inverse machine. -/
inductive InvState (k : ℕ) (State : Type)
  /-- The first step: move the history heads onto the last record. -/
  | rewind
  /-- Read the record under the history heads and undo the moves of its step. -/
  | read
  /-- Write back the symbols that the step read, and move to the previous record. -/
  | restore (rec : Record k State)

instance [Finite State] : Finite (InvState k State) :=
  Finite.of_injective (β := Option (Option (Record k State)))
    (fun s => match s with
      | .rewind => none
      | .read => some none
      | .restore rec => some (some rec))
    (by intro a b; cases a <;> cases b <;> simp)

/-- **Reading a record**: the record whose code is written on the history cells, if any. -/
noncomputable def decode {h : ℕ} (code : Record k State → Fin h → Bool)
    (v : Fin h → Option Bool) : Option (Record k State) :=
  open Classical in
  if hv : ∃ rec, (fun j => some (code rec j)) = v then some hv.choose else none

theorem decode_code {h : ℕ} {code : Record k State → Fin h → Bool}
    (hcode : Function.Injective code) (rec : Record k State) :
    decode code (fun j => some (code rec j)) = some rec := by
  unfold decode
  split_ifs with hv
  · congr 1
    apply hcode
    funext j
    exact Option.some.inj (congrFun hv.choose_spec j)
  · exact absurd ⟨rec, rfl⟩ hv

theorem decode_blank {h : ℕ} (code : Record k State → Fin h → Bool) (hh : 0 < h) :
    decode code (fun _ => none) = none := by
  unfold decode
  split_ifs with hv
  · obtain ⟨rec, hrec⟩ := hv
    simpa using congrFun hrec ⟨0, hh⟩
  · rfl

/-- Work-tape moves that touch only the history heads, by `m`. -/
def histMoves (h : ℕ) (m : SignType) : Fin (k + h) → Option (Option Bool) × SignType :=
  Fin.addCases (motive := fun _ => Option (Option Bool) × SignType) (fun _ => (none, 0))
    (fun _ => (none, m))

/-- The first step: the history heads move one cell left. -/
def rewindAction (h : ℕ) : Action (k + h) Bool (InvState k State) :=
  ⟨0, histMoves h (-1), none, some .read⟩

/-- The last step: the history heads move back right, and the inverse halts. -/
def finishAction (h : ℕ) : Action (k + h) Bool (InvState k State) :=
  ⟨0, histMoves h 1, none, none⟩

/-- **Undoing the moves of a step.** With the record `rec` of the step, the action `a` that it took
is known: erase the record and move every head back by the opposite of its move in `a`. -/
noncomputable def undoAction {h : ℕ} (tm : MultiTapeTM k Bool State) (rec : Record k State) :
    Action (k + h) Bool (InvState k State) :=
  ⟨-(tm.tr rec.1 rec.2.1 rec.2.2).inputTape,
    Fin.addCases (motive := fun _ => Option (Option Bool) × SignType)
      (fun i => (none, -((tm.tr rec.1 rec.2.1 rec.2.2).workTapes i).2)) (fun _ => (some none, 0)),
    none, some (.restore rec)⟩

/-- **Restoring the symbols read.** Write back the symbols that the step read and move the history
heads onto the previous record. -/
def restoreAction (h : ℕ) (rec : Record k State) : Action (k + h) Bool (InvState k State) :=
  ⟨0, Fin.addCases (motive := fun _ => Option (Option Bool) × SignType)
      (fun i => (some (rec.2.2 i), 0)) (fun _ => (none, -1)),
    none, some .read⟩

/-- The action in the state `read`: undo the step whose record was read, or stop. -/
noncomputable def readAction {h : ℕ} (tm : MultiTapeTM k Bool State) :
    Option (Record k State) → Action (k + h) Bool (InvState k State)
  | some rec => undoAction tm rec
  | none => finishAction h

/-- The transition function of the inverse machine. -/
noncomputable def invTr {h : ℕ} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) :
    InvState k State → Option Bool → (Fin (k + h) → Option Bool) →
      Action (k + h) Bool (InvState k State)
  | .rewind, _, _ => rewindAction h
  | .read, _, v => readAction tm (decode code fun j => v (histTape k j))
  | .restore rec, _, _ => restoreAction h rec

/-- **The inverse of the machine with a history** (`M₁⁻¹`). -/
noncomputable def invTM {h : ℕ} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) : MultiTapeTM (k + h) Bool (InvState k State) :=
  ofTr .rewind (invTr tm code)

/-! ## The configurations of the inverse -/

/-- A configuration of the history machine **at rest** for the inverse: the same tapes and heads,
the state `s` of the inverse and the output `out`. -/
def atRest {h : ℕ} {input : List Bool} (c : Cfg (k + h) Bool (State ⊕ State) input)
    (s : Option (InvState k State)) (out : List Bool) : Cfg (k + h) Bool (InvState k State) input :=
  ⟨s, c.inputPos, c.workTapes, c.workTapePos, out⟩

/-- At rest with its own output is `Cfg.withState`. -/
theorem atRest_output {h : ℕ} {input : List Bool} (c : Cfg (k + h) Bool (State ⊕ State) input)
    (s : Option (InvState k State)) : atRest c s c.output = c.withState s := rfl

/-- A configuration of the history machine **pending** for the inverse: the same tapes and heads,
except the history heads, one cell to the left (on the last record); the state `read` and the
output `out`. -/
def pending {h : ℕ} {input : List Bool} (c : Cfg (k + h) Bool (State ⊕ State) input)
    (out : List Bool) : Cfg (k + h) Bool (InvState k State) input :=
  ⟨some .read, c.inputPos, c.workTapes,
    Fin.addCases (motive := fun _ => ℤ) (fun i => c.workTapePos (mainTape h i))
      (fun j => c.workTapePos (histTape k j) - 1), out⟩

section Correctness

variable {h : ℕ} {tm : MultiTapeTM k Bool State} {code : Record k State → Fin h → Bool}
  {input : List Bool}

/-- A clean running step of the history machine is its good action. -/
theorem histTM_step_good {c : Cfg (k + h) Bool (State ⊕ State) input} (hc : Clean c) {q : State}
    (hq : c.state = some (.inl q)) :
    (histTM tm code).step c =
      (goodAction tm code q c.inputSymbol (fun i => c.workTapeSymbols (mainTape h i))).apply c := by
  have hguard : ∀ j : Fin h, c.workTapeSymbols (histTape k j) = none :=
    fun j => hc.2 j _ le_rfl
  rw [step_of_state hq, histTM, tr_ofTr, histTr, ite_eq_left_of_eq_true _ _ (eq_true hguard)]

/-- **The first step of the inverse** moves the history heads onto the last record. -/
theorem invTM_start (c : Cfg (k + h) Bool (State ⊕ State) input) (out : List Bool) :
    (invTM tm code).step (atRest c (some .rewind) out) = pending c out := by
  rw [step_of_state (q := .rewind) rfl, invTM, tr_ofTr, invTr]
  apply Cfg.ext
  · rfl
  · simp [atRest, pending, rewindAction]
  · funext i
    induction i using Fin.addCases <;> simp [atRest, pending, rewindAction, histMoves]
  · funext i
    induction i using Fin.addCases with
    | left i => simp [atRest, pending, rewindAction, histMoves]
    | right j =>
      simp [atRest, pending, rewindAction, histMoves]
      ring
  · simp [atRest, pending, rewindAction]

/-- **The last step of the inverse.** When the history cells to the left of the heads are blank,
the inverse moves the history heads back and halts. -/
theorem invTM_finish (hh : 0 < h) {c : Cfg (k + h) Bool (State ⊕ State) input}
    (hb : ∀ j : Fin h, c.workTapes (histTape k j) (c.workTapePos (histTape k j) - 1) = none)
    (out : List Bool) :
    (invTM tm code).step (pending c out) = atRest c none out := by
  rw [step_of_state (q := .read) rfl, invTM, tr_ofTr, invTr]
  have hd : (decode code fun j => (pending c out).workTapeSymbols (histTape k j)) = none := by
    have : (fun j => (pending c out).workTapeSymbols (histTape k j)) = fun _ => none := by
      funext j
      simpa [pending, Cfg.workTapeSymbols] using hb j
    rw [this, decode_blank code hh]
  rw [hd, readAction]
  apply Cfg.ext
  · rfl
  · simp [atRest, pending, finishAction]
  · funext i
    induction i using Fin.addCases <;> simp [atRest, pending, finishAction, histMoves]
  · funext i
    induction i using Fin.addCases <;> simp [atRest, pending, finishAction, histMoves]
  · simp [atRest, pending, finishAction]

/-- **Two steps of the inverse undo one step of the history machine.** From a clean running
configuration `c`, the configuration pending after the step goes back, in two steps of the inverse
(read the record and move back; restore the symbols read), to the one pending at `c`. -/
theorem invTM_back (hstay : StaysOnBlank tm) (hcode : Function.Injective code)
    {c : Cfg (k + h) Bool (State ⊕ State) input} (hc : Clean c) {q : State}
    (hq : c.state = some (.inl q)) (out : List Bool) :
    (invTM tm code).runFrom (pending ((histTM tm code).step c) out) 2 = pending c out := by
  set r := c.inputSymbol with hr
  set ws : Fin k → Option Bool := fun i => c.workTapeSymbols (mainTape h i) with hws
  set rec : Record k State := (q, r, ws) with hrec
  set a := tm.tr q r ws with ha
  rw [histTM_step_good hc hq]
  set c' := (goodAction tm code q r ws).apply c with hc'
  -- the first step reads the record and undoes the moves
  have hread : (decode code fun j => (pending c' out).workTapeSymbols (histTape k j)) = some rec := by
    have : (fun j => (pending c' out).workTapeSymbols (histTape k j)) =
        fun j => some (code rec j) := by
      funext j
      simp [pending, Cfg.workTapeSymbols, hc', goodAction]
      rfl
    rw [this, decode_code hcode]
  have h1 : (invTM tm code).step (pending c' out) = (undoAction tm rec).apply (pending c' out) := by
    rw [step_of_state (q := .read) rfl, invTM, tr_ofTr, invTr, hread, readAction]
  have h2 : ∀ d : Cfg (k + h) Bool (InvState k State) input, d.state = some (.restore rec) →
      (invTM tm code).step d = (restoreAction h rec).apply d := by
    intro d hd
    rw [step_of_state hd, invTM, tr_ofTr, invTr]
  have hrun : (invTM tm code).runFrom (pending c' out) 2 =
      (restoreAction h rec).apply ((undoAction tm rec).apply (pending c' out)) := by
    rw [runFrom, Function.iterate_succ_apply', Function.iterate_one, h1, h2 _ rfl]
  rw [hrun]
  -- the input head comes back: it moved only from the interior
  have hin : a.inputTape = 0 ∨
      (c.inputPos.val ≠ 0 ∧ c.inputPos.val ≠ input.length + 1) := by
    rcases hr0 : r with _ | b
    · left
      rw [ha, hr0]
      exact hstay q ws
    · right
      exact interior_of_inputSymbol (by rw [← hr, hr0]; simp)
  apply Cfg.ext
  · rfl
  · simp only [Action.apply_inputPos, restoreAction, moveInputPos_zero, undoAction, pending, hc',
      goodAction]
    exact moveInputPos_neg _ _ hin
  · funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [Action.apply_workTapes, restoreAction, undoAction, pending, hc', goodAction,
        Action.apply_workTapePos, Fin.addCases_left]
      rw [add_assoc, signType_cast_neg, add_neg_cancel, add_zero]
      rcases hw : (a.workTapes i).1 with _ | s
      · simp only
        exact Function.update_eq_self_iff.mpr rfl
      · simp only [Function.update_idem]
        exact Function.update_eq_self_iff.mpr rfl
    | right j =>
      simp only [Action.apply_workTapes, restoreAction, undoAction, pending, hc', goodAction,
        Action.apply_workTapePos, Fin.addCases_right, signType_cast_one, add_sub_cancel_right,
        Function.update_idem]
      rw [Function.update_eq_self_iff]
      exact (hc.2 j _ le_rfl).symm
  · funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [Action.apply_workTapePos, restoreAction, undoAction, pending, hc', goodAction,
        Fin.addCases_left]
      rw [signType_cast_zero, add_zero, signType_cast_neg]
      exact add_neg_cancel_right _ _
    | right j =>
      simp only [Action.apply_workTapePos, restoreAction, undoAction, pending, hc', goodAction,
        Fin.addCases_right]
      rw [signType_cast_one, signType_cast_zero, signType_cast_neg, signType_cast_one]
      ring
  · simp [restoreAction, undoAction, pending]

/-- **The inverse undoes a run.** Along a run of `t` running steps of the history machine from a
clean configuration `c₀`, the inverse goes back in `2 t` steps. -/
theorem invTM_runBack (hstay : StaysOnBlank tm) (hcode : Function.Injective code)
    {c₀ : Cfg (k + h) Bool (State ⊕ State) input} (hc₀ : Clean c₀) (out : List Bool) :
    ∀ t : ℕ, (∀ i < t, ¬((histTM tm code).runFrom c₀ i).Halted) →
      (invTM tm code).runFrom (pending ((histTM tm code).runFrom c₀ t) out) (2 * t) =
        pending c₀ out
  | 0, _ => rfl
  | t + 1, hrun => by
    have hc := (runFrom_clean (tm := tm) (code := code) hc₀ t).2
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (hrun t (by omega))
    rcases x with q | q
    · have e1 : (histTM tm code).runFrom c₀ (t + 1) =
          (histTM tm code).step ((histTM tm code).runFrom c₀ t) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : ∀ x : Cfg (k + h) Bool (InvState k State) input,
          (invTM tm code).runFrom x (2 * (t + 1)) =
            (invTM tm code).runFrom ((invTM tm code).runFrom x 2) (2 * t) := fun x =>
        Function.iterate_add_apply _ _ _ _
      rw [e1, e2, invTM_back hstay hcode hc hx out]
      exact invTM_runBack hstay hcode hc₀ out t fun i hi => hrun i (by omega)
    · exact absurd hx (hc.1 q)

/-- **Correctness of the inverse (`M₁⁻¹`).** If the history machine runs `t` steps from the
initial configuration without halting before, then the inverse, started on the configuration it
reached (in the state `rewind`), reaches in `2 t + 2` steps the initial configuration, halted: the
input head, every tape and every head back where they started. The output is left as it was. -/
theorem invTM_correct (hstay : StaysOnBlank tm) (hcode : Function.Injective code) (hh : 0 < h)
    (t : ℕ) (hrun : ∀ i < t, ¬((histTM tm code).runFrom ((histTM tm code).initCfg input) i).Halted)
    (out : List Bool) :
    (invTM tm code).runFrom
        (atRest ((histTM tm code).runFrom ((histTM tm code).initCfg input) t) (some .rewind) out)
        (2 * t + 2) =
      atRest ((histTM tm code).initCfg input) none out := by
  have e : ∀ x : Cfg (k + h) Bool (InvState k State) input,
      (invTM tm code).runFrom x (2 * t + 2) =
        (invTM tm code).step ((invTM tm code).runFrom ((invTM tm code).step x) (2 * t)) :=
    fun x => (Function.iterate_succ_apply' _ _ _).trans
      (congrArg _ (Function.iterate_succ_apply _ _ _))
  have hc₀ : Clean ((histTM tm code).initCfg input) := init_clean tm.q₀
  rw [e, invTM_start, invTM_runBack hstay hcode hc₀ out t hrun]
  exact invTM_finish hh (fun j => rfl) out

/-- **Correctness of the inverse, from the machine simulated.** If `tm` runs `t` steps from its
initial configuration without halting before (for instance, it halts exactly at `t`), the inverse
takes the configuration of the history machine at `t`, with its own output, back to the initial
configuration in `2 t + 2` steps. -/
theorem invTM_correct_of_tm (hstay : StaysOnBlank tm) (hcode : Function.Injective code)
    (hh : 0 < h) (t : ℕ) (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted) :
    (invTM tm code).runFrom
        (((histTM tm code).runFrom ((histTM tm code).initCfg input) t).withState (some .rewind))
        (2 * t + 2) =
      atRest ((histTM tm code).initCfg input) none
        ((histTM tm code).runFrom ((histTM tm code).initCfg input) t).output := by
  rw [← atRest_output]
  exact invTM_correct hstay hcode hh t (fun i hi => (histTM_halted_iff i).not.mpr (hrun i hi)) _

end Correctness

/-! ## With the one-hot code -/

/-- The one-hot code has at least one bit. -/
theorem oneHot_pos [Finite State] (q₀ : State) : 0 < Nat.card (Record k State) := by
  have : Nonempty (Record k State) := ⟨(q₀, none, fun _ => none)⟩
  exact Nat.card_pos

/-- **Step 4 of Bennett's construction, packaged.** For a machine with finitely many states that
stays on a blank of its input, the history machine with the one-hot code has an inverse with
finitely many states that, from the configuration reached after `t` running steps of `tm`, goes
back to the initial configuration in `2 t + 2` steps. -/
theorem inverse [Finite State] (tm : MultiTapeTM k Bool State) (hstay : StaysOnBlank tm)
    (input : List Bool) (t : ℕ) (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted) :
    (invTM tm (oneHot (Record k State))).runFrom
        (((histTM tm (oneHot (Record k State))).runFrom
          ((histTM tm (oneHot (Record k State))).initCfg input) t).withState (some .rewind))
        (2 * t + 2) =
      atRest ((histTM tm (oneHot (Record k State))).initCfg input) none
        ((histTM tm (oneHot (Record k State))).runFrom
          ((histTM tm (oneHot (Record k State))).initCfg input) t).output :=
  invTM_correct_of_tm hstay (oneHot_injective _) (oneHot_pos tm.q₀) t hrun

/-! ## Checks: the axioms, and one mutant per central theorem -/

/-- info: 'Sagitta.Arrow.TM.Bennett.moveInputPos_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.moveInputPos_neg
/-- info: 'Sagitta.Arrow.TM.Bennett.invTM_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.invTM_back
/-- info: 'Sagitta.Arrow.TM.Bennett.invTM_runBack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.invTM_runBack
/-- info: 'Sagitta.Arrow.TM.Bennett.invTM_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.invTM_correct
/-- info: 'Sagitta.Arrow.TM.Bennett.invTM_correct_of_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.invTM_correct_of_tm
/-- info: 'Sagitta.Arrow.TM.Bennett.inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.inverse

section Mutants

set_option linter.unusedVariables false

/-- Mutant of `moveInputPos_neg`: without the condition (a clamped move does not come back). -/
example {n : ℕ} (p : Fin (n + 2)) (m : SignType) : True := by
  fail_if_success
    have : moveInputPos (moveInputPos p m) (-m) = p := moveInputPos_neg p m (by assumption)
  trivial

/-- Mutant of `invTM_back`: one step of the inverse instead of two. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hstay : StaysOnBlank tm) (hcode : Function.Injective code) {input : List Bool}
    (c : Cfg (k + h) Bool (State ⊕ State) input) (hc : Clean c) (q : State)
    (hq : c.state = some (.inl q)) (out : List Bool) : True := by
  fail_if_success
    have : (invTM tm code).runFrom (pending ((histTM tm code).step c) out) 1 = pending c out :=
      invTM_back hstay hcode hc hq out
  trivial

/-- Mutant of `invTM_runBack`: without the injective code. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hstay : StaysOnBlank tm) {input : List Bool} (c₀ : Cfg (k + h) Bool (State ⊕ State) input)
    (hc₀ : Clean c₀) (out : List Bool) : True := by
  fail_if_success
    have := invTM_runBack (code := code) hstay (by assumption) hc₀ out
  trivial

/-- Mutant of `invTM_correct`: without a history tape (`0 < h`). -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hstay : StaysOnBlank tm) (hcode : Function.Injective code) (input : List Bool) (t : ℕ)
    (hrun : ∀ i < t, ¬((histTM tm code).runFrom ((histTM tm code).initCfg input) i).Halted)
    (out : List Bool) : True := by
  fail_if_success
    have := invTM_correct hstay hcode (by assumption) t hrun out
  trivial

/-- Mutant of `invTM_correct_of_tm`: the inverse restores the output too. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hstay : StaysOnBlank tm) (hcode : Function.Injective code) (hh : 0 < h) (input : List Bool)
    (t : ℕ) (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted) : True := by
  fail_if_success
    have : (invTM tm code).runFrom
        (((histTM tm code).runFrom ((histTM tm code).initCfg input) t).withState (some .rewind))
        (2 * t + 2) = atRest ((histTM tm code).initCfg input) none [] :=
      invTM_correct_of_tm hstay hcode hh t hrun
  trivial

/-- Mutant of `inverse`: without "stays on a blank". -/
example [Finite State] (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ)
    (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted) : True := by
  fail_if_success
    have := inverse tm (by assumption) input t hrun
  trivial

end Mutants

end Sagitta.Arrow.TM.Bennett
