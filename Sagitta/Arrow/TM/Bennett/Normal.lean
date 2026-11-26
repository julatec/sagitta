/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.Compose
import Sagitta.Arrow.TM.Bennett.Prepare
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

/-!
# Bennett, steps 2b and 2c: the normal form of a machine

Bennett's machine of step 6 needs a machine that never moves its input head (`InputFixed`) and
leaves its result on a work tape, from the head on. Every machine of cslib has such a form, built
from cslib's own redirections, used unchanged:

* `Turing.MultiTapeTM.outputToTape` writes what the machine outputs on a fresh work tape
  (`outTape`), with the head at the end of the word;
* `Turing.MultiTapeTM.inputFromTape` reads the input from a virtual input tape, with a flag tape
  marking the cell before it, and never touches the real input head;
* `Turing.MultiTapeTM.rewindWork`, placed on `outTape` with `Turing.MultiTapeTM.extendTapes`, brings
  the head back to the start of the word;
* a first step that does nothing (`nopTM`), so that no transition re-enters the initial state
  (`NoReentry`), which the hand-off from the preparing machine needs.

`normTM tm` is the composite. It never moves its input head and never reads it (`InputBlind`),
so it runs the same wherever the input head is (`runFrom_setInputPos`): after the reversible
preparing machine of `Prepare.lean` the input head rests on the blank after the input.

* `normTM_inputFixed`, `normTM_inputBlind`, `normTM_noReentry`.
* `normTM_run`: started on the tapes the preparing machine leaves (`prepTapes`), wherever the input
  head is, if `tm` halts by time `t` with output `y`, then `normTM tm` halts by time
  `1 + (t + (|y| + 2))` with `y` on `outTape` from the head on and nothing on the real output.
-/

namespace Sagitta.Arrow.TM.Bennett

open Turing Turing.MultiTapeTM

variable {k : ℕ}

/-! ## Machines that ignore their input head -/

/-- A machine is **blind to its input**: no transition depends on the symbol under the input
head. -/
def InputBlind {S : Type} (tm : MultiTapeTM k Bool S) : Prop :=
  ∀ (q : S) (r r' : Option Bool) (w : Fin k → Option Bool), tm.tr q r w = tm.tr q r' w

section SetPos

variable {S : Type} {tm : MultiTapeTM k Bool S} {input : List Bool}

/-- A machine that never moves nor reads its input head steps the same wherever the head is. -/
theorem step_setInputPos (hfix : InputFixed tm) (hb : InputBlind tm) (c : Cfg k Bool S input)
    (p : Fin (input.length + 2)) :
    tm.step { c with inputPos := p } = { tm.step c with inputPos := p } := by
  rcases Option.eq_none_or_eq_some c.state with hq | ⟨q, hq⟩
  · have hq' : ({ c with inputPos := p } : Cfg k Bool S input).state = none := hq
    rw [step_of_halt hq', step_of_halt hq]
  · have hq' : ({ c with inputPos := p } : Cfg k Bool S input).state = some q := hq
    have hw : ({ c with inputPos := p } : Cfg k Bool S input).workTapeSymbols =
      c.workTapeSymbols := rfl
    rw [step_of_state hq', step_of_state hq, hb q _ c.inputSymbol, hw]
    apply Cfg.ext <;> simp [hfix q]

/-- **Runs ignore the input head**, for a machine that never moves nor reads it. -/
theorem runFrom_setInputPos (hfix : InputFixed tm) (hb : InputBlind tm) (c : Cfg k Bool S input)
    (p : Fin (input.length + 2)) (t : ℕ) :
    tm.runFrom { c with inputPos := p } t = { tm.runFrom c t with inputPos := p } := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [runFrom, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, step_setInputPos hfix hb]

end SetPos

/-! ## No re-entry through composition -/

/-- If no transition of `tm₀` re-enters its initial state, the same holds for `tm₀.seq tm₁`. -/
theorem seq_noReentry {S₀ S₁ : Type} {tm₀ : MultiTapeTM k Bool S₀} {tm₁ : MultiTapeTM k Bool S₁}
    (h₀ : NoReentry tm₀) : NoReentry (tm₀.seq tm₁) := by
  intro q r w
  rw [seq_q₀]
  rcases q with q | q
  · rw [seq_tr_inl]
    rcases hs : (tm₀.tr q r w).state with _ | q'
    · simp [handOver]
    · have := h₀ q r w
      rw [hs] at this
      simpa [handOver] using this
  · rw [seq_tr_inr]
    rcases (tm₁.tr q r w).state <;> simp

/-- The machine with a history does not re-enter its initial state if `tm` does not. -/
theorem histTM_noReentry {State : Type} {h : ℕ} {tm : MultiTapeTM k Bool State}
    (code : Record k State → Fin h → Bool) (h₀ : NoReentry tm) : NoReentry (histTM tm code) := by
  intro q r w
  simp only [histTM, tr_ofTr, q₀_ofTr]
  rcases q with q | q
  · simp only [histTr]
    split_ifs
    · simp only [goodAction]
      have := h₀ q r (fun i => w (mainTape h i))
      rcases hs : (tm.tr q r fun i => w (mainTape h i)).state with _ | q'
      · simp
      · rw [hs] at this; simpa using this
    · simp [sinkAction]
  · simp [histTr, sinkAction]

/-- **Bennett's machine does not re-enter its initial state** if `tm` does not. -/
theorem bennettTM_noReentry {State : Type} {h : ℕ} {tm : MultiTapeTM k Bool State}
    (code : Record k State → Fin h → Bool) (h₀ : NoReentry tm) (src : Fin k) :
    NoReentry (((histTM tm code).seq (gateTM (mainTape h src) |>.seq
      (emitTM (mainTape h src)))).seq (uncTM tm code)) :=
  seq_noReentry (seq_noReentry (histTM_noReentry code h₀))

/-! ## The normal form -/

/-- The machine that does nothing: it halts at once. -/
def nopTM (k : ℕ) : MultiTapeTM k Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩

theorem nopTM_noReentry : NoReentry (nopTM k) := by
  intro q r w
  simp [nopTM]

/-- The work tape where the normal form leaves its result. -/
abbrev outTape (k : ℕ) : Fin (k + 1 + 2) := Fin.castAdd 2 (Fin.last k)

/-- The virtual input tape of the normal form. -/
abbrev vipTape (k : ℕ) : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 0

/-- The flag tape of the normal form. -/
abbrev flagTape (k : ℕ) : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 1

theorem vipTape_ne_flagTape : vipTape k ≠ flagTape k := by
  simp [vipTape, flagTape, Fin.ext_iff]

/-- The rewinding machine of cslib on `outTape`. -/
noncomputable def rewindOut (k : ℕ) : MultiTapeTM (k + 1 + 2) Bool RewindWorkState :=
  (rewindWork Bool).extendTapes (tapeEmb (outTape k))

/-- **The normal form of `tm`**: do nothing, then run `tm` with its input read from the virtual
input tape and its output redirected to `outTape`, then rewind `outTape`. -/
noncomputable def normTM {S : Type} (tm : MultiTapeTM k Bool S) :
    MultiTapeTM (k + 1 + 2) Bool (Unit ⊕ (S ⊕ RewindWorkState)) :=
  (nopTM _).seq (tm.outputToTape.inputFromTape.seq (rewindOut k))

section Props

variable {S : Type} (tm : MultiTapeTM k Bool S)

theorem normTM_inputFixed : InputFixed (normTM tm) := by
  intro q r w
  rcases q with u | q | q
  · simp [normTM, seq_tr_inl, nopTM]
  · simp [normTM, seq_tr_inr, seq_tr_inl, inputFromTape, adapt, adaptedTr]
  · simp only [normTM, seq_tr_inr, rewindOut, extendTapes, adapt, adaptedTr, tr_ofTr,
      rewindWork]
    split <;> rfl

theorem normTM_inputBlind : InputBlind (normTM tm) := by
  intro q r r' w
  rcases q with u | q | q
  · simp [normTM, seq_tr_inl, nopTM]
  · simp [normTM, seq_tr_inr, seq_tr_inl, inputFromTape, adapt, adaptedTr]
  · simp only [normTM, seq_tr_inr, rewindOut, extendTapes, adapt, adaptedTr, tr_ofTr,
      rewindWork]

theorem normTM_noReentry : NoReentry (normTM tm) :=
  seq_noReentry nopTM_noReentry

end Props

/-! ## The run of the normal form -/

/-- The tapes the preparing machine leaves, as the normal form reads them: the input on the
virtual input tape from cell `0`, the mark `true` at cell `-1` of the flag tape, every other tape
blank. -/
def prepTapes (k : ℕ) (input : List Bool) : Fin (k + 1 + 2) → ℤ → Option Bool :=
  Function.update (Function.update (fun _ _ => none) (vipTape k) (tapeOfList input)) (flagTape k)
    (Function.update (fun _ => none) (-1) (some true))

section Run

variable {S : Type} {tm : MultiTapeTM k Bool S} {input : List Bool}

/-- The initial configuration of `tm`, as the redirected machine sees it, is the prepared one. -/
theorem inCfg_outCfg_initCfg :
    inCfg true (outCfg (tm.initCfg input)) input =
      ⟨some tm.q₀, 1, prepTapes k input, fun _ => 0, []⟩ := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    induction i using Fin.addCases with
    | left j =>
      induction j using Fin.lastCases with
      | last =>
        simp [prepTapes, Function.update_apply, Fin.ext_iff, outCfg, tapeOfList_nil]; omega
      | cast j =>
        simp [prepTapes, Function.update_apply, Fin.ext_iff, outCfg, MultiTapeNTM.initCfg,
          Cfg.init]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    | right j =>
      fin_cases j
      · simp [prepTapes, vipTape, flagTape, Fin.ext_iff]
      · simp [prepTapes, vipTape, flagTape]
  · funext i
    induction i using Fin.addCases with
    | left j =>
      induction j using Fin.lastCases with
      | last => simp [MultiTapeNTM.initCfg, Cfg.init]
      | cast j => simp [MultiTapeNTM.initCfg, Cfg.init]
    | right j => simp [outCfg, MultiTapeNTM.initCfg, Cfg.init]
  · rfl

/-- The redirected machine: `tm` reading the virtual input tape and writing on `outTape`. -/
noncomputable abbrev redirTM (tm : MultiTapeTM k Bool S) : MultiTapeTM (k + 1 + 2) Bool S :=
  tm.outputToTape.inputFromTape

theorem redirTM_inputFixed : InputFixed (redirTM tm) := by
  intro q r w; simp [inputFromTape, adapt, adaptedTr]

theorem redirTM_inputBlind : InputBlind (redirTM tm) := by
  intro q r r' w; simp [inputFromTape, adapt, adaptedTr]

/-- **The run of the redirected machine** from the prepared tapes, wherever the input head is: it
is the run of `tm`, through cslib's two configuration maps. -/
theorem redirTM_run (p : Fin (input.length + 2)) (t : ℕ) :
    (redirTM tm).runFrom ⟨some tm.q₀, p, prepTapes k input, fun _ => 0, []⟩ t =
      { inCfg true (outCfg (tm.runFrom (tm.initCfg input) t)) input with inputPos := p } := by
  have e : (⟨some tm.q₀, p, prepTapes k input, fun _ => 0, []⟩ : Cfg (k + 1 + 2) Bool S input) =
      { inCfg true (outCfg (tm.initCfg input)) input with inputPos := p } := by
    rw [inCfg_outCfg_initCfg]
  rw [e, runFrom_setInputPos redirTM_inputFixed redirTM_inputBlind]
  have h1 := runFrom_map (inCfgHom tm.outputToTape true input) (outCfg (tm.initCfg input)) t
  have h2 := runFrom_map (outCfgHom tm) (tm.initCfg input) t
  simp only [inCfgHom_apply, outCfgHom_apply] at h1 h2
  rw [h1, h2]

/-- **The run of the normal form.** Started on the prepared tapes, wherever the input head is: if
`tm` has halted by time `t` with output `y`, the normal form has halted by time
`1 + (t + (|y| + 2))` with `y` on `outTape` from cell `0`, its head at `0`, and nothing on the real
output. -/
theorem normTM_run (p : Fin (input.length + 2)) (t : ℕ)
    (hhalt : (tm.runFrom (tm.initCfg input) t).Halted) :
    ((normTM tm).runFrom ⟨some (normTM tm).q₀, p, prepTapes k input, fun _ => 0, []⟩
        (1 + (t + ((tm.runFrom (tm.initCfg input) t).output.length + 2)))).Halted ∧
      ((normTM tm).runFrom ⟨some (normTM tm).q₀, p, prepTapes k input, fun _ => 0, []⟩
        (1 + (t + ((tm.runFrom (tm.initCfg input) t).output.length + 2)))).output = [] ∧
      ((normTM tm).runFrom ⟨some (normTM tm).q₀, p, prepTapes k input, fun _ => 0, []⟩
        (1 + (t + ((tm.runFrom (tm.initCfg input) t).output.length + 2)))).workTapes
          (outTape k) = tapeOfList (tm.runFrom (tm.initCfg input) t).output ∧
      ((normTM tm).runFrom ⟨some (normTM tm).q₀, p, prepTapes k input, fun _ => 0, []⟩
        (1 + (t + ((tm.runFrom (tm.initCfg input) t).output.length + 2)))).workTapePos
          (outTape k) = 0 := by
  set e := tm.runFrom (tm.initCfg input) t with he
  set y := e.output with hy
  set E : Cfg (k + 1 + 2) Bool S input := { inCfg true (outCfg e) input with inputPos := p }
    with hE
  have hrun : (redirTM tm).runFrom ⟨some tm.q₀, p, prepTapes k input, fun _ => 0, []⟩ t = E :=
    redirTM_run p t
  have hEh : E.Halted := hhalt
  -- the rewinding machine
  set F : Cfg (k + 1 + 2) Bool RewindWorkState input :=
    ⟨none, p, E.workTapes, Function.update E.workTapePos (outTape k) 0, []⟩ with hF
  have hR : (rewindOut k).runFrom (E.withState (some (rewindOut k).q₀)) (y.length + 2) = F := by
    unfold rewindOut
    have h1 : oneTapeCfg (outTape k)
        (E.withState (some ((rewindWork Bool).extendTapes (tapeEmb (outTape k))).q₀)) =
        ⟨some (rewindWork Bool).q₀, p, fun _ => tapeOfList y, fun _ => ((y.length : ℕ) : ℤ),
          []⟩ :=
      Cfg.ext rfl rfl (by funext; simp [oneTapeCfg, hE, outTape, hy])
        (by funext; simp [oneTapeCfg, hE, outTape, hy]) rfl
    rw [runFrom_tapeEmb, h1, runFrom_rewindWork_none p (tapeOfList y) [] rfl le_rfl,
      embed_tapeEmb]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i = outTape k
      · subst hi; simp [hE, hF, hy]
      · simp [hi, hF]; rfl
    · rfl
    · rfl
  have hFh : F.Halted := rfl
  -- the redirected machine, then the rewinding machine
  set X := (redirTM tm).seq (rewindOut k) with hX
  have hXrun : X.runFrom (⟨some (.inl tm.q₀), p, prepTapes k input, fun _ => 0, []⟩ :
      Cfg (k + 1 + 2) Bool (S ⊕ RewindWorkState) input) (t + (y.length + 2)) =
      F.mapState (Option.map .inr) := by
    have := seq_runFrom_of_le (tm₀ := redirTM tm) (tm₁ := rewindOut k)
      (⟨some tm.q₀, p, prepTapes k input, fun _ => 0, []⟩ : Cfg (k + 1 + 2) Bool S input)
      (t₀ := t) (t₁ := y.length + 2) (by rw [hrun]; exact hEh)
      (by rw [hrun, hR])
      le_rfl
    rw [hrun, hR] at this
    exact this
  -- the first step that does nothing
  have hnop : (nopTM (k + 1 + 2)).runFrom
      (⟨some (), p, prepTapes k input, fun _ => 0, []⟩ : Cfg (k + 1 + 2) Bool Unit input) 1 =
      ⟨none, p, prepTapes k input, fun _ => 0, []⟩ := by
    rw [runFrom, Function.iterate_one, step_of_state rfl]
    apply Cfg.ext <;> simp [nopTM]
  have hXq : (⟨none, p, prepTapes k input, fun _ => 0, []⟩ :
      Cfg (k + 1 + 2) Bool Unit input).withState (some X.q₀) =
      (⟨some (.inl tm.q₀), p, prepTapes k input, fun _ => 0, []⟩ :
        Cfg (k + 1 + 2) Bool (S ⊕ RewindWorkState) input) := rfl
  have hW := seq_runFrom_of_le (tm₀ := nopTM (k + 1 + 2)) (tm₁ := X)
    (⟨some (), p, prepTapes k input, fun _ => 0, []⟩ : Cfg (k + 1 + 2) Bool Unit input)
    (t₀ := 1) (t₁ := t + (y.length + 2)) (by rw [hnop])
    (by rw [hnop, hXq, hXrun]; rfl) le_rfl
  rw [hnop] at hW
  have hstart : (⟨some (normTM tm).q₀, p, prepTapes k input, fun _ => 0, []⟩ :
      Cfg (k + 1 + 2) Bool (Unit ⊕ (S ⊕ RewindWorkState)) input) =
      (⟨some (), p, prepTapes k input, fun _ => 0, []⟩ : Cfg (k + 1 + 2) Bool Unit input).mapState
        (handOver X.q₀) := rfl
  rw [hstart, normTM, ← hX, hW, hXq, hXrun]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show E.workTapes (outTape k) = tapeOfList y
    simp [hE, hy, outTape]
  · show Function.update E.workTapePos (outTape k) 0 (outTape k) = 0
    simp

end Run

/-! ## Checks: the axioms, and one mutant per central theorem -/

/-- info: 'Sagitta.Arrow.TM.Bennett.runFrom_setInputPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.runFrom_setInputPos
/-- info: 'Sagitta.Arrow.TM.Bennett.seq_noReentry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.seq_noReentry
/-- info: 'Sagitta.Arrow.TM.Bennett.histTM_noReentry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histTM_noReentry
/-- info: 'Sagitta.Arrow.TM.Bennett.normTM_inputFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.normTM_inputFixed
/-- info: 'Sagitta.Arrow.TM.Bennett.normTM_inputBlind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.normTM_inputBlind
/-- info: 'Sagitta.Arrow.TM.Bennett.normTM_noReentry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.normTM_noReentry
/-- info: 'Sagitta.Arrow.TM.Bennett.inCfg_outCfg_initCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.inCfg_outCfg_initCfg
/-- info: 'Sagitta.Arrow.TM.Bennett.redirTM_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.redirTM_run
/-- info: 'Sagitta.Arrow.TM.Bennett.normTM_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.normTM_run

section Mutants

set_option linter.unusedVariables false

/-- Mutant of `runFrom_setInputPos`: without blindness to the input. -/
example {S : Type} (tm : MultiTapeTM k Bool S) (hfix : InputFixed tm) {input : List Bool}
    (c : Cfg k Bool S input) (p : Fin (input.length + 2)) (t : ℕ) : True := by
  fail_if_success
    have := runFrom_setInputPos hfix (by assumption) c p t
  trivial

/-- Mutant of `seq_noReentry`: without the hypothesis on the first machine. -/
example {S₀ S₁ : Type} (tm₀ : MultiTapeTM k Bool S₀) (tm₁ : MultiTapeTM k Bool S₁) : True := by
  fail_if_success
    have : NoReentry (tm₀.seq tm₁) := seq_noReentry (by assumption)
  trivial

/-- Mutant of `histTM_noReentry`: without the hypothesis on `tm`. -/
example {State : Type} {h : ℕ} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) : True := by
  fail_if_success
    have : NoReentry (histTM tm code) := histTM_noReentry code (by assumption)
  trivial

/-- Mutant of `normTM_inputFixed`: the redirected machine alone is not claimed for the input head
of `tm`; `tm` itself may move it. -/
example {S : Type} (tm : MultiTapeTM k Bool S) : True := by
  fail_if_success
    have : InputFixed tm := normTM_inputFixed tm
  trivial

/-- Mutant of `normTM_inputBlind`: `tm` itself may read its input. -/
example {S : Type} (tm : MultiTapeTM k Bool S) : True := by
  fail_if_success
    have : InputBlind tm := normTM_inputBlind tm
  trivial

/-- Mutant of `normTM_noReentry`: `tm` itself may re-enter its initial state. -/
example {S : Type} (tm : MultiTapeTM k Bool S) : True := by
  fail_if_success
    have : NoReentry tm := normTM_noReentry tm
  trivial

/-- Mutant of `inCfg_outCfg_initCfg`: the input head is at `1`, not at the end. -/
example {S : Type} (tm : MultiTapeTM k Bool S) (input : List Bool) : True := by
  fail_if_success
    have : inCfg true (outCfg (tm.initCfg input)) input =
        ⟨some tm.q₀, Fin.last _, prepTapes k input, fun _ => 0, []⟩ := inCfg_outCfg_initCfg
  trivial

/-- Mutant of `redirTM_run`: the virtual input is not the empty word. -/
example {S : Type} (tm : MultiTapeTM k Bool S) (input : List Bool) (p : Fin (input.length + 2))
    (t : ℕ) : True := by
  fail_if_success
    have : (redirTM tm).runFrom ⟨some tm.q₀, p, prepTapes k [], fun _ => 0, []⟩ t =
        { inCfg true (outCfg (tm.runFrom (tm.initCfg input) t)) input with inputPos := p } :=
      redirTM_run p t
  trivial

/-- Mutant of `normTM_run`: without the halting of `tm`. -/
example {S : Type} (tm : MultiTapeTM k Bool S) (input : List Bool) (p : Fin (input.length + 2))
    (t : ℕ) : True := by
  fail_if_success
    have := normTM_run (tm := tm) p t (by assumption)
  trivial

end Mutants

end Sagitta.Arrow.TM.Bennett
