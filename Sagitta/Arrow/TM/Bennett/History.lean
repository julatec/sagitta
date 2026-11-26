/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Instance

/-!
# Bennett, steps 1 and 2: the model, and the machine with a history

The first two steps towards proving the hypothesis `Sagitta.Arrow.TM.Bennett` (Bennett, 1973) on
the multi-tape machines of cslib.

## Step 1: what reversibility means in cslib's model

A machine of cslib (`Turing.MultiTapeTM`) has a total transition function: every running
configuration takes the action `tm.tr q r w` chosen by its state `q`, the input symbol `r` and the
work symbols `w` (`MultiTapeTM.step_of_state`). The action (`Turing.Action.apply`) moves the input
head with clamping (`moveInputPos`), writes or not on each work tape, moves the work heads, appends
at most one symbol to the output and changes state. `IsReversible` asks the step to be injective on
**all** running configurations, not only the reachable ones, and the configuration includes the
output tape.

Two facts of that model shape the construction:

* **The input head cannot move off a blank** (`IsReversible.staysOnBlank`). On the empty input the
  positions `0` and `1` both read a blank, and any move sends them to the same position. So a
  reversible machine never moves its input head while it reads a blank: once it steps off its input,
  it stays there. The history construction needs this of the simulated machine (`StaysOnBlank`);
  it is not true of every machine, and making it true (copying the input to a work tape first) is a
  separate step.
* **The history needs a guard, and the guard a sink.** Writing the record of a step over a cell
  forgets the cell, so the history is written only on blank cells. On a running configuration whose
  history cells are not blank, which no run from the initial configuration reaches, the machine
  must still step injectively. The step cannot halt there (the state would be lost) nor loop in
  place (the configuration could be the image of a legitimate step). It goes to a **sink** state
  that appends `false` to the output once, and the sink appends `true` forever. Appending is
  injective, and the last symbol of the output tells which of the two steps was taken.

## Step 2: the machine with a history

`histTM tm code` has the `k` work tapes of `tm` and `h` more, the history. In state `.inl q`, when
the cells under the history heads are blank, it performs the action of `tm` on the first `k` tapes
and writes the code of the **record** of the step (`Record`: the state and the symbols read) on the
history tapes, one bit per tape, moving their heads right. `code` is any injective map
`Record k State → Fin h → Bool`; `oneHot` is one, with `h = Nat.card (Record k State)`.

* `histTM_isReversible`: if `tm` never moves its input head off a blank and `code` is injective,
  `histTM tm code` is reversible (`IsReversible`).
* `histTM_simulates`: after `t` steps from the initial configuration, `histTM tm code` projects
  (`proj`: forget the history tapes) to `tm` after `t` steps. This needs no hypothesis.
* `history`: both together, for a machine with finitely many states.

## Not done here

The history machine leaves its history on the tapes: copying the output (step 3), running the
inverse machine (step 4) and composing (step 5) remain. Nor is the time and space accounted.
-/

namespace Sagitta.Arrow.TM.Bennett

open Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type}

/-! ## The input head and blanks -/

/-- A machine **stays on a blank** of its input: it never moves its input head while it reads a
blank (the boundary positions). -/
def StaysOnBlank (tm : MultiTapeTM k Bool State) : Prop :=
  ∀ (q : State) (w : Fin k → Option Bool), (tm.tr q none w).inputTape = 0

/-- **A reversible machine stays on a blank of its input.** On the empty input the positions `0`
and `1` both read a blank; two configurations that differ only there take the same action, and a
move sends both to the same position. -/
theorem _root_.Sagitta.Arrow.TM.IsReversible.staysOnBlank {tm : MultiTapeTM k Bool State}
    (hrev : IsReversible tm) : StaysOnBlank tm := by
  intro q w
  by_contra hm
  let c : Fin 2 → Cfg k Bool State [] := fun p => ⟨some q, p, fun i _ => w i, fun _ => 0, []⟩
  have hsym (p : Fin 2) : (c p).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (by have := p.isLt; simp [c]; omega)
  have hwork (p : Fin 2) : (c p).workTapeSymbols = w := rfl
  have hstep : tm.step (c 0) = tm.step (c 1) := by
    rw [step_of_state (q := q) rfl, step_of_state (q := q) rfl, hsym 0, hsym 1, hwork 0, hwork 1]
    apply Cfg.ext
    · rfl
    · simp only [Action.apply_inputPos, c]
      revert hm
      generalize (tm.tr q none w).inputTape = m
      intro hm
      cases m <;> simp_all <;> decide
    · rfl
    · rfl
    · rfl
  have := congrArg Cfg.inputPos (hrev [] (c 0) (c 1) (by simp [c]) (by simp [c]) hstep)
  simp [c] at this

/-! ## One action is locally reversible -/

/-- Moving the input head is injective away from the boundary. -/
theorem moveInputPos_injOn {n : ℕ} {p p' : Fin (n + 2)} (m : SignType) (hp : p.val ≠ 0)
    (hp1 : p.val ≠ n + 1) (hp' : p'.val ≠ 0) (hp1' : p'.val ≠ n + 1)
    (h : moveInputPos p m = moveInputPos p' m) : p = p' := by
  have e := val_moveInputPos_eq p m
  have e' := val_moveInputPos_eq p' m
  rw [h] at e
  have hlt := p.isLt
  have hlt' := p'.isLt
  apply Fin.ext
  rcases m with _ | _ | _ <;> simp [SignType.cast] at e e' <;> omega

/-- The symbol read on the input is not a blank only away from the boundary. -/
theorem interior_of_inputSymbol {input : List Bool} {c : Cfg k Bool State input}
    (h : c.inputSymbol ≠ none) : c.inputPos.val ≠ 0 ∧ c.inputPos.val ≠ input.length + 1 := by
  constructor <;> intro e <;> exact h (inputSymbol_eq_none_of_boundary (by omega))

/-- **One action is locally reversible.** Two configurations in the same state that take the same
action and reach the same configuration are equal, as long as they read the same symbols where the
action writes and the input head does not move off a blank. -/
theorem apply_injective {k' : ℕ} {State' : Type} {input : List Bool} (A : Action k' Bool State')
    {c c' : Cfg k' Bool State' input} (hs : c.state = c'.state)
    (hin : A.inputTape = 0 ∨ (c.inputSymbol ≠ none ∧ c'.inputSymbol ≠ none))
    (hw : ∀ i, (A.workTapes i).1 = none ∨ c.workTapeSymbols i = c'.workTapeSymbols i)
    (h : A.apply c = A.apply c') : c = c' := by
  have hpos : c.workTapePos = c'.workTapePos := by
    funext i
    have := congrFun (congrArg Cfg.workTapePos h) i
    simp only [Action.apply_workTapePos] at this
    exact add_right_cancel this
  apply Cfg.ext
  · exact hs
  · have := congrArg Cfg.inputPos h
    simp only [Action.apply_inputPos] at this
    rcases hin with h0 | ⟨hc, hc'⟩
    · simpa [h0] using this
    · obtain ⟨a, b⟩ := interior_of_inputSymbol hc
      obtain ⟨a', b'⟩ := interior_of_inputSymbol hc'
      exact moveInputPos_injOn _ a b a' b' this
  · funext i
    have ht := congrFun (congrArg Cfg.workTapes h) i
    simp only [Action.apply_workTapes] at ht
    rcases hai : (A.workTapes i).1 with _ | s
    · simpa [hai] using ht
    · simp only [hai] at ht
      funext z
      by_cases hz : z = c.workTapePos i
      · rcases hw i with hn | hr
        · simp [hai] at hn
        · subst hz
          simpa [Cfg.workTapeSymbols, hpos] using hr
      · have := congrFun ht z
        rwa [Function.update_of_ne hz, Function.update_of_ne (by rwa [← hpos])] at this
  · exact hpos
  · have := congrArg Cfg.output h
    simp only [Action.apply_output] at this
    exact List.append_cancel_right this

/-! ## The machine with a history -/

/-- **The record of a step**: what a step of the machine forgets and its history keeps, the state
and the symbols read. -/
abbrev Record (k : ℕ) (State : Type) := State × Option Bool × (Fin k → Option Bool)

/-- The action of the sink: no move, no write, append `b`, stay in (or go to) the sink `.inr q`. -/
def sinkAction {k' : ℕ} (b : Bool) (q : State) : Action k' Bool (State ⊕ State) :=
  ⟨0, fun _ => (none, 0), some b, some (.inr q)⟩

/-- The tape `i` of `tm` among the `k + h` tapes of the history machine. -/
abbrev mainTape (h : ℕ) (i : Fin k) : Fin (k + h) := Fin.castAdd h i

/-- The history tape `j`. -/
abbrev histTape (k : ℕ) {h : ℕ} (j : Fin h) : Fin (k + h) := Fin.natAdd k j

/-- The good action of the history machine in state `q`: the action of `tm` on the first `k`
tapes, and the code of the record written on the history tapes, whose heads move right. -/
noncomputable def goodAction {h : ℕ} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) (q : State) (r : Option Bool)
    (ws : Fin k → Option Bool) : Action (k + h) Bool (State ⊕ State) :=
  ⟨(tm.tr q r ws).inputTape,
    Fin.addCases (motive := fun _ => Option (Option Bool) × SignType)
      (fun i => (tm.tr q r ws).workTapes i) (fun j => (some (some (code (q, r, ws) j)), 1)),
    (tm.tr q r ws).output, (tm.tr q r ws).state.map .inl⟩

/-- The transition function of the history machine. -/
noncomputable def histTr {h : ℕ} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) :
    State ⊕ State → Option Bool → (Fin (k + h) → Option Bool) → Action (k + h) Bool (State ⊕ State)
  | .inl q, r, w =>
    open Classical in
    if ∀ j : Fin h, w (histTape k j) = none then goodAction tm code q r (fun i => w (mainTape h i))
    else sinkAction false q
  | .inr q, _, _ => sinkAction true q

/-- **The machine with a history**: `tm` on the first `k` tapes, the record of each step on `h`
more. -/
noncomputable def histTM {h : ℕ} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) : MultiTapeTM (k + h) Bool (State ⊕ State) :=
  ofTr (.inl tm.q₀) (histTr tm code)

/-- **The projection**: forget the history tapes (and the sink). -/
def proj {h : ℕ} {input : List Bool} (c : Cfg (k + h) Bool (State ⊕ State) input) :
    Cfg k Bool State input :=
  ⟨c.state.bind Sum.getLeft?, c.inputPos, fun i => c.workTapes (mainTape h i),
    fun i => c.workTapePos (mainTape h i), c.output⟩

/-- A configuration of the history machine is **clean** when it is not in the sink and the history
tapes are blank from their heads on. -/
def Clean {h : ℕ} {input : List Bool} (c : Cfg (k + h) Bool (State ⊕ State) input) : Prop :=
  (∀ q, c.state ≠ some (.inr q)) ∧
    ∀ (j : Fin h) (z : ℤ), c.workTapePos (histTape k j) ≤ z → c.workTapes (histTape k j) z = none

section Simulation

variable {h : ℕ} {tm : MultiTapeTM k Bool State} {code : Record k State → Fin h → Bool}
  {input : List Bool}

theorem proj_inputSymbol (c : Cfg (k + h) Bool (State ⊕ State) input) :
    (proj c).inputSymbol = c.inputSymbol := rfl

theorem proj_workTapeSymbols (c : Cfg (k + h) Bool (State ⊕ State) input) :
    (proj c).workTapeSymbols = fun i => c.workTapeSymbols (mainTape h i) := rfl

/-- **One step of the simulation**: from a clean configuration, the history machine steps to a
clean configuration that projects to the step of `tm`. -/
theorem step_clean {c : Cfg (k + h) Bool (State ⊕ State) input} (hc : Clean c) :
    proj ((histTM tm code).step c) = tm.step (proj c) ∧ Clean ((histTM tm code).step c) := by
  obtain ⟨hns, hblank⟩ := hc
  rcases hst : c.state with _ | q | q
  · have hp : (proj c).state = none := by simp [proj, hst]
    rw [step_of_halt hst, step_of_halt hp]
    exact ⟨rfl, hns, hblank⟩
  · have hp : (proj c).state = some q := by simp [proj, hst]
    have hguard : ∀ j : Fin h, c.workTapeSymbols (histTape k j) = none :=
      fun j => hblank j _ le_rfl
    have hA : (histTM tm code).step c =
        (goodAction tm code q c.inputSymbol (fun i => c.workTapeSymbols (mainTape h i))).apply c := by
      rw [step_of_state hst, histTM, tr_ofTr, histTr, ite_eq_left_of_eq_true _ _ (eq_true hguard)]
    rw [step_of_state hp, hA, proj_inputSymbol, proj_workTapeSymbols]
    refine ⟨?_, ?_, ?_⟩
    · apply Cfg.ext
      · simp only [proj, Action.apply_state, goodAction]
        cases (tm.tr q _ _).state <;> rfl
      · rfl
      · funext i
        simp only [proj, Action.apply_workTapes, goodAction, Fin.addCases_left]
      · funext i
        simp only [proj, Action.apply_workTapePos, goodAction, Fin.addCases_left]
      · rfl
    · intro q'
      simp only [Action.apply_state, goodAction]
      cases (tm.tr q _ _).state <;> simp
    · intro j z hz
      simp only [Action.apply_workTapePos, Action.apply_workTapes, goodAction,
        Fin.addCases_right] at hz ⊢
      rw [Function.update_of_ne (by simp at hz; omega)]
      exact hblank j z (by simp at hz; omega)
  · exact absurd hst (hns q)

/-- The history machine starts clean. -/
theorem init_clean (q₀ : State) : Clean (Cfg.init (k := k + h) (.inl q₀ : State ⊕ State) input) :=
  ⟨by simp, by simp⟩

/-- The initial configuration projects to the initial configuration. -/
theorem proj_init (q₀ : State) :
    proj (Cfg.init (k := k + h) (.inl q₀ : State ⊕ State) input) = Cfg.init q₀ input := by
  apply Cfg.ext <;> rfl

/-- The simulation from any clean configuration. -/
theorem runFrom_clean {c : Cfg (k + h) Bool (State ⊕ State) input} (hc : Clean c) (t : ℕ) :
    proj ((histTM tm code).runFrom c t) = tm.runFrom (proj c) t ∧
      Clean ((histTM tm code).runFrom c t) := by
  induction t with
  | zero => exact ⟨rfl, hc⟩
  | succ t ih =>
    simp only [runFrom, Function.iterate_succ_apply'] at ih ⊢
    obtain ⟨e, hc'⟩ := step_clean (tm := tm) (code := code) ih.2
    exact ⟨e.trans (congrArg tm.step ih.1), hc'⟩

/-- **The simulation lemma**: after `t` steps from the initial configuration, the history machine
projects to `tm` after `t` steps. -/
theorem histTM_simulates (t : ℕ) :
    proj ((histTM tm code).runFrom ((histTM tm code).initCfg input) t) =
      tm.runFrom (tm.initCfg input) t := by
  have := (runFrom_clean (tm := tm) (code := code) (init_clean (h := h) (input := input) tm.q₀) t).1
  rwa [proj_init] at this

/-- The history machine halts exactly when `tm` does. -/
theorem histTM_halted_iff (t : ℕ) :
    ((histTM tm code).runFrom ((histTM tm code).initCfg input) t).Halted ↔
      (tm.runFrom (tm.initCfg input) t).Halted := by
  have hc := (runFrom_clean (tm := tm) (code := code) (init_clean (h := h) (input := input)
    tm.q₀) t).2
  rw [← histTM_simulates (tm := tm) (code := code) t]
  simp only [Cfg.Halted, proj]
  rcases hs : ((histTM tm code).runFrom ((histTM tm code).initCfg input) t).state with _ | q | q
  · simp
  · simp
  · exact absurd hs (hc.1 q)

end Simulation

/-! ## The history machine is reversible -/

section Reversible

variable {h : ℕ} {tm : MultiTapeTM k Bool State} {code : Record k State → Fin h → Bool}

/-- **The machine with a history is reversible**, if `tm` stays on a blank of its input and the
code of the records is injective. Two running configurations with the same successor took the
same kind of step (the state and the last symbol of the output tell); two good steps wrote the same
code, hence the same record, hence the same action on the same symbols, which is locally
reversible (`apply_injective`). -/
theorem histTM_isReversible (hstay : StaysOnBlank tm) (hcode : Function.Injective code) :
    IsReversible (histTM tm code) := by
  intro input c c' hc hc' hstep
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  rw [step_of_state hq, step_of_state hq', histTM, tr_ofTr, tr_ofTr] at hstep
  have hst := congrArg Cfg.state hstep
  have hout := congrArg Cfg.output hstep
  rcases q with a | a <;> rcases q' with a' | a' <;> simp only [histTr] at hstep hst hout
  · split_ifs at hstep hst hout with hg hg'
    · -- two good steps: the history tells the record
      have hrec : (a, c.inputSymbol, fun i => c.workTapeSymbols (mainTape h i)) =
          (a', c'.inputSymbol, fun i => c'.workTapeSymbols (mainTape h i)) := by
        apply hcode
        funext j
        have hp := congrFun (congrArg Cfg.workTapePos hstep) (histTape k j)
        simp only [Action.apply_workTapePos, goodAction, Fin.addCases_right] at hp
        have hp' : c.workTapePos (histTape k j) = c'.workTapePos (histTape k j) :=
          add_right_cancel hp
        have ht := congrFun (congrFun (congrArg Cfg.workTapes hstep) (histTape k j))
          (c.workTapePos (histTape k j))
        simp only [Action.apply_workTapes, goodAction, Fin.addCases_right] at ht
        rw [Function.update_self, hp', Function.update_self] at ht
        simpa using ht
      simp only [Prod.mk.injEq] at hrec
      obtain ⟨rfl, hr, hws⟩ := hrec
      rw [← hr, ← hws] at hstep
      refine apply_injective _ (hq.trans hq'.symm) ?_ ?_ hstep
      · rcases hr0 : c.inputSymbol with _ | b
        · exact Or.inl (hstay _ _)
        · exact Or.inr ⟨by simp, by rw [← hr, hr0]; simp⟩
      · intro i
        right
        induction i using Fin.addCases with
        | left i => exact congrFun hws i
        | right j => exact (hg j).trans (hg' j).symm
    · simp [sinkAction, goodAction] at hst
    · simp [sinkAction, goodAction] at hst
    · simp only [sinkAction, Action.apply_state, Option.some.injEq, Sum.inr.injEq] at hst
      subst hst
      exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl) (fun _ => Or.inl rfl) hstep
  · split_ifs at hstep hst hout with hg
    · simp [sinkAction, goodAction] at hst
    · simp [sinkAction] at hout
  · split_ifs at hstep hst hout with hg
    · simp [sinkAction, goodAction] at hst
    · simp [sinkAction] at hout
  · simp only [sinkAction, Action.apply_state, Option.some.injEq, Sum.inr.injEq] at hst
    subst hst
    exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl) (fun _ => Or.inl rfl) hstep

/-- **The hypothesis is necessary.** For an injective code, the history machine is reversible
exactly when `tm` stays on a blank of its input: when the history cells are blank, the history
machine moves its input head as `tm` does. -/
theorem histTM_isReversible_iff (hcode : Function.Injective code) :
    IsReversible (histTM tm code) ↔ StaysOnBlank tm := by
  refine ⟨fun hrev q w => ?_, fun hs => histTM_isReversible hs hcode⟩
  have := hrev.staysOnBlank (.inl q) (Fin.addCases (motive := fun _ => Option Bool) w fun _ => none)
  rw [histTM, tr_ofTr, histTr, ite_eq_left_of_eq_true _ _ (eq_true fun j => by simp)] at this
  simpa [goodAction] using this

end Reversible

/-! ## A code, and the history machine of any machine that stays on a blank -/

/-- **The one-hot code**: `Nat.card α` bits, one of them set. -/
noncomputable def oneHot (α : Type) [Finite α] (a : α) : Fin (Nat.card α) → Bool :=
  fun j => decide (j = Finite.equivFin α a)

theorem oneHot_injective (α : Type) [Finite α] : Function.Injective (oneHot α) := by
  intro a b hab
  have := congrFun hab (Finite.equivFin α a)
  simp only [oneHot, decide_true] at this
  exact (Finite.equivFin α).injective (of_decide_eq_true this.symm)

/-- **Step 2 of Bennett's construction.** A machine with finitely many states that stays on a blank
of its input has a reversible machine with `h` more tapes and finitely many states that, after `t`
steps from the initial configuration, projects to it after `t` steps. -/
theorem history [Finite State] (tm : MultiTapeTM k Bool State) (hstay : StaysOnBlank tm) :
    ∃ (h : ℕ) (State₁ : Type) (_ : Finite State₁) (tm₁ : MultiTapeTM (k + h) Bool State₁)
      (π : ∀ {input : List Bool}, Cfg (k + h) Bool State₁ input → Cfg k Bool State input),
      IsReversible tm₁ ∧ ∀ (input : List Bool) (t : ℕ),
        π (tm₁.runFrom (tm₁.initCfg input) t) = tm.runFrom (tm.initCfg input) t :=
  ⟨_, State ⊕ State, inferInstance, histTM tm (oneHot (Record k State)), proj,
    histTM_isReversible hstay (oneHot_injective _), fun _ t => histTM_simulates t⟩

/-! ## Checks: the axioms, and one mutant per central theorem

`#print axioms` on the central theorems, under `#guard_msgs`. Then one mutant per central theorem:
a weakened hypothesis or a strengthened conclusion, which must **fail** to elaborate
(`fail_if_success`). -/

/-- info: 'Sagitta.Arrow.TM.IsReversible.staysOnBlank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.IsReversible.staysOnBlank
/-- info: 'Sagitta.Arrow.TM.Bennett.apply_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.apply_injective
/-- info: 'Sagitta.Arrow.TM.Bennett.histTM_simulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histTM_simulates
/-- info: 'Sagitta.Arrow.TM.Bennett.histTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.histTM_isReversible_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histTM_isReversible_iff
/-- info: 'Sagitta.Arrow.TM.Bennett.history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.history

section Mutants

set_option linter.unusedVariables false

/-- Mutant of `IsReversible.staysOnBlank`: the input head never moves, even on a symbol. -/
example (tm : MultiTapeTM k Bool State) (hrev : IsReversible tm) (q : State) (b : Bool)
    (w : Fin k → Option Bool) : True := by
  fail_if_success
    have : (tm.tr q (some b) w).inputTape = 0 := hrev.staysOnBlank q w
  trivial

/-- Mutant of `apply_injective`: without the condition on the input head. -/
example {input : List Bool} (A : Action k Bool State) (c c' : Cfg k Bool State input)
    (hs : c.state = c'.state)
    (hw : ∀ i, (A.workTapes i).1 = none ∨ c.workTapeSymbols i = c'.workTapeSymbols i)
    (h : A.apply c = A.apply c') : True := by
  fail_if_success
    have : c = c' := apply_injective A hs (by assumption) hw h
  trivial

/-- Mutant of `histTM_simulates`: one step ahead of `tm`. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (input : List Bool) (t : ℕ) : True := by
  fail_if_success
    have : proj ((histTM tm code).runFrom ((histTM tm code).initCfg input) t) =
        tm.runFrom (tm.initCfg input) (t + 1) := histTM_simulates t
  trivial

/-- Mutant of `histTM_isReversible`: without "stays on a blank". -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hcode : Function.Injective code) : True := by
  fail_if_success
    have : IsReversible (histTM tm code) := histTM_isReversible (by assumption) hcode
  trivial

/-- Mutant of `histTM_isReversible_iff`: without the injective code. -/
example {h : ℕ} (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool) :
    True := by
  fail_if_success
    have : IsReversible (histTM tm code) ↔ StaysOnBlank tm :=
      histTM_isReversible_iff (by assumption)
  trivial

/-- Mutant of `history`: without "stays on a blank". -/
example [Finite State] (tm : MultiTapeTM k Bool State) : True := by
  fail_if_success
    have := history tm (by assumption)
  trivial

end Mutants

end Sagitta.Arrow.TM.Bennett
