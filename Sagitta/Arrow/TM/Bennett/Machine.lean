/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.Compose

/-!
# Bennett, step 6: the machine, reversible, with its run

Bennett's machine (1973) for a machine `tm` of cslib, assembled with cslib's sequential
composition (`Turing.MultiTapeTM.seq`):

1. `histTM tm code`: run `tm`, keeping the record of every step on `h` history tapes;
2. `emitStage`: the gate (`gateTM`) and the emitting machine (`emitTM`), which append the word left
   by `tm` on its work tape `src` to the output tape and bring the head back;
3. `uncTM tm code`: the reversible inverse, which undoes the run of `tm` step by step and erases the
   history.

* `bennettTM_isReversible`: if `tm` never moves its input head off a blank and `code` is injective,
  the machine is **reversible**.
* `bennettTM_correct`: if `tm` never moves its input head and halts at time `t` with the word `w` on
  its work tape `src` (from the head on, a blank before and after), Bennett's machine has halted
  by time `4 t + 2 |w| + 6` with **every work tape blank**, every head where it started, and the
  output of `tm` followed by `w` on the output tape. The time is Bennett's `4 t + 2 |w| + O(1)`.

## Not done here

* A sharper space bound. `bennettTM_computesInTimeAndSpace` gives `(k + h) (2 T + 1)` with
  `T = 4 t + 2 |w| + 6` (a head moves one cell per step), which is `O(T)`; that the extra space is
  only the `h` history tapes over `t` cells is not stated.
* Reducing an arbitrary machine to these hypotheses: a machine that never moves its input head
  (copy the input to a work tape first, step 2b in `BENNETT.md`) and that leaves its result on a work
  tape instead of the output (step 2c). Without them, the hypothesis `Bennett` of
  `Sagitta.Arrow.TM.Instance` is not discharged yet (step 7).
-/

namespace Sagitta.Arrow.TM.Bennett

open Turing Turing.MultiTapeTM

variable {k h : ℕ} {State : Type}

/-- **The emitting stage**: the gate, then the emitting machine. -/
noncomputable def emitStage (src : Fin k) : MultiTapeTM k Bool (GateState ⊕ CopyState) :=
  (gateTM src).seq (emitTM src)

/-- **Bennett's machine**: compute with a history, emit the result, uncompute. -/
noncomputable def bennettTM (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (src : Fin k) :
    MultiTapeTM (k + h) Bool
      (((State ⊕ State) ⊕ (GateState ⊕ CopyState)) ⊕ (UncState k State ⊕ UncState k State)) :=
  ((histTM tm code).seq (emitStage (mainTape h src))).seq (uncTM tm code)

/-- **Bennett's machine is reversible.** -/
theorem bennettTM_isReversible {tm : MultiTapeTM k Bool State}
    {code : Record k State → Fin h → Bool} (hstay : StaysOnBlank tm)
    (hcode : Function.Injective code) (src : Fin k) : IsReversible (bennettTM tm code src) :=
  seq_isReversible
    (seq_isReversible (histTM_isReversible hstay hcode)
      (seq_isReversible (gateTM_isReversible _) (emitTM_isReversible _) (gate_emit_handOff _))
      (HandOff.of_noReentry (gate_emit_noReentry _)))
    (uncTM_isReversible tm code) (HandOff.of_noReentry (uncTM_noReentry tm code))

section Correctness

variable {tm : MultiTapeTM k Bool State} {code : Record k State → Fin h → Bool} {input : List Bool}

/-- The emitting stage on a configuration with `w` under the head of `src`. -/
theorem emitStage_run {src : Fin k} {S : Type} (x : Cfg k Bool S input) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length → x.workTapes src (x.workTapePos src + i) = w[i]?)
    (hleft : x.workTapes src (x.workTapePos src - 1) = none) {T : ℕ}
    (hT : 2 + (2 * w.length + 2) ≤ T) :
    (emitStage src).runFrom (x.withState (some (emitStage src).q₀)) T =
      { x.withState (State' := GateState ⊕ CopyState) none with output := x.output ++ w } := by
  set y : Cfg k Bool GateState input := x.withState (some .start)
  have hy : x.withState (some (emitStage src).q₀) = y.mapState (handOver (emitTM src).q₀) :=
    Cfg.ext rfl rfl rfl rfl rfl
  have hg := gateTM_run (src := src) y rfl hleft
  set z : Cfg k Bool CopyState input := x.withState (some .fwd)
  have hz : ((gateTM src).runFrom y 2).withState (some (emitTM src).q₀) = z := by
    rw [hg]; exact Cfg.ext rfl rfl rfl rfl rfl
  have he := emitTM_correct (src := src) z w rfl hsrc hleft
  rw [hy, emitStage, seq_runFrom_of_le y (by rw [hg]) (by rw [hz, he]) hT, hz, he]
  exact Cfg.ext rfl rfl rfl rfl rfl

/-- **Bennett's machine is correct.** If `tm` never moves its input head and halts at time `t`
with the word `w` on its work tape `src`, from the head on, with a blank before and after, then
Bennett's machine has halted by time `4 t + 2 |w| + 6`, with every work tape blank, every head
where it started, and the output of `tm` followed by `w` on the output tape. -/
theorem bennettTM_correct (hfix : InputFixed tm) (hcode : Function.Injective code) (hh : 0 < h)
    (src : Fin k) (t : ℕ) (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted)
    (hhalt : (tm.runFrom (tm.initCfg input) t).Halted) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length →
      (tm.runFrom (tm.initCfg input) t).workTapes src
        ((tm.runFrom (tm.initCfg input) t).workTapePos src + i) = w[i]?)
    (hleft : (tm.runFrom (tm.initCfg input) t).workTapes src
      ((tm.runFrom (tm.initCfg input) t).workTapePos src - 1) = none)
    {T : ℕ} (hT : 4 * t + 2 * w.length + 6 ≤ T) :
    (bennettTM tm code src).runFrom ((bennettTM tm code src).initCfg input) T =
      ⟨none, 1, fun _ _ => none, fun _ => 0, (tm.runFrom (tm.initCfg input) t).output ++ w⟩ := by
  set e := tm.runFrom (tm.initCfg input) t with he
  set H := histTM tm code
  set E := emitStage (k := k + h) (mainTape h src)
  set U := uncTM tm code
  set x := H.runFrom (H.initCfg input) t with hx
  have hproj : proj x = e := histTM_simulates t
  have hxhalt : x.Halted := (histTM_halted_iff t).mpr hhalt
  have hxs : x.state = none := hxhalt
  have hxt : x.workTapes (mainTape h src) = e.workTapes src := by
    rw [← hproj]; rfl
  have hxp : x.workTapePos (mainTape h src) = e.workTapePos src := by
    rw [← hproj]; rfl
  have hxo : x.output = e.output := by rw [← hproj]; rfl
  -- the emitting stage
  have hE : E.runFrom (x.withState (some E.q₀)) (2 + (2 * w.length + 2)) =
      { x.withState (State' := GateState ⊕ CopyState) none with output := x.output ++ w } :=
    emitStage_run x w (by rw [hxt, hxp]; exact hsrc) (by rw [hxt, hxp]; exact hleft) le_rfl
  -- compute, then emit
  have hHE : ∀ T' ≥ t + (2 + (2 * w.length + 2)),
      (H.seq E).runFrom ((H.initCfg input).mapState (handOver E.q₀)) T' =
        ({ x.withState (State' := GateState ⊕ CopyState) none with output := x.output ++ w } :
          Cfg (k + h) Bool (GateState ⊕ CopyState) input).mapState (Option.map .inr) := by
    intro T' hT'
    rw [seq_runFrom_of_le (H.initCfg input) hxhalt (by rw [hE]; rfl) hT', hE]
  -- then uncompute
  have hmirror : (((H.seq E).runFrom ((H.initCfg input).mapState (handOver E.q₀))
      (t + (2 + (2 * w.length + 2)))).withState (some U.q₀)) = mirror x (x.output ++ w) := by
    rw [hHE _ le_rfl]
    exact Cfg.ext (by simp [mirror, hxs, U, uncTM]) rfl rfl rfl rfl
  have hU := uncTM_correct_of_tm (code := code) hfix hcode hh t hrun (x.output ++ w)
  have hT₂ : t + (2 + (2 * w.length + 2)) + (3 * t + 2) ≤ T := by omega
  rw [bennettTM, seq_initCfg, seq_initCfg,
    seq_runFrom_of_le ((H.initCfg input).mapState (handOver E.q₀))
      (by rw [hHE _ le_rfl]; rfl) (by rw [hmirror, hU]; rfl) hT₂, hmirror, hU]
  exact Cfg.ext rfl rfl rfl rfl (by simp [halted, hxo])

end Correctness

/-! ## Time and space -/

section Space

variable {S : Type} {input : List Bool}

/-- A head moves at most one cell per step: after `n` steps from the initial configuration, every
work head is within `n` cells of the origin. -/
theorem natAbs_workTapePos_runFrom_le (tm : MultiTapeTM k Bool S) (n : ℕ) (i : Fin k) :
    ((tm.runFrom (tm.initCfg input) n).workTapePos i).natAbs ≤ n := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    rcases hq : (tm.runFrom (tm.initCfg input) n).state with _ | q
    · rw [step_of_halt hq]; omega
    · rw [step_of_state hq]
      have := workTapePos_apply_le (tm.tr q (tm.runFrom (tm.initCfg input) n).inputSymbol
        (tm.runFrom (tm.initCfg input) n).workTapeSymbols) (tm.runFrom (tm.initCfg input) n) i
      rw [abs_le] at this
      omega

/-- **A machine that halts by time `T` runs in space `k (2 T + 1)`**: its heads never leave the
window `[-T, T]`. -/
theorem runsInSpace_of_halted (tm : MultiTapeTM k Bool S) {T : ℕ}
    (hT : (tm.runFrom (tm.initCfg input) T).Halted) : tm.RunsInSpace input (k * (2 * T + 1)) := by
  intro p
  apply MultiTapeNTM.RunPath.InWindow.space_le
  rintro _ ⟨n, rfl⟩ i
  rw [runPath_apply_eq_runFrom, p.head_eq, mem_window]
  rcases le_or_gt n.val T with h | h
  · exact (natAbs_workTapePos_runFrom_le tm _ i).trans h
  · rw [runFrom_eq_of_halt tm _ h.le hT]
    exact natAbs_workTapePos_runFrom_le tm _ i

end Space

/-- **Step 6, in cslib's vocabulary.** Under the hypotheses of `bennettTM_correct`, Bennett's
machine computes the output of `tm` followed by `w` in time `T = 4 t + 2 |w| + 6` and space
`(k + h) (2 T + 1)`, linear in `T`; it is reversible (`bennettTM_isReversible`) and leaves every
work tape blank (`bennettTM_correct`). -/
theorem bennettTM_computesInTimeAndSpace {tm : MultiTapeTM k Bool State}
    {code : Record k State → Fin h → Bool} {input : List Bool} (hfix : InputFixed tm)
    (hcode : Function.Injective code) (hh : 0 < h) (src : Fin k) (t : ℕ)
    (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted)
    (hhalt : (tm.runFrom (tm.initCfg input) t).Halted) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length →
      (tm.runFrom (tm.initCfg input) t).workTapes src
        ((tm.runFrom (tm.initCfg input) t).workTapePos src + i) = w[i]?)
    (hleft : (tm.runFrom (tm.initCfg input) t).workTapes src
      ((tm.runFrom (tm.initCfg input) t).workTapePos src - 1) = none) :
    (bennettTM tm code src).ComputesInTimeAndSpace input
      ((tm.runFrom (tm.initCfg input) t).output ++ w) (4 * t + 2 * w.length + 6)
      ((k + h) * (2 * (4 * t + 2 * w.length + 6) + 1)) := by
  have e := bennettTM_correct (code := code) hfix hcode hh src t hrun hhalt w hsrc hleft le_rfl
  have hH : ((bennettTM tm code src).runFrom ((bennettTM tm code src).initCfg input)
      (4 * t + 2 * w.length + 6)).Halted := by rw [e]
  exact ⟨⟨_, hH, by rw [e]⟩, runsInTime_of_halted hH, runsInSpace_of_halted _ hH⟩

/-! ## Checks: the axioms, and one mutant per central theorem -/

/-- info: 'Sagitta.Arrow.TM.Bennett.bennettTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.bennettTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.bennettTM_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.bennettTM_correct
/-- info: 'Sagitta.Arrow.TM.Bennett.emitStage_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.emitStage_run
/-- info: 'Sagitta.Arrow.TM.Bennett.runsInSpace_of_halted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.runsInSpace_of_halted
/-- info: 'Sagitta.Arrow.TM.Bennett.bennettTM_computesInTimeAndSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.bennettTM_computesInTimeAndSpace

section Mutants

set_option linter.unusedVariables false

/-- Mutant of `bennettTM_isReversible`: without "stays on a blank". -/
example (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hcode : Function.Injective code) (src : Fin k) : True := by
  fail_if_success
    have := bennettTM_isReversible (tm := tm) (by assumption) hcode src
  trivial

/-- Mutant of `emitStage_run`: one step before the bound. -/
example {src : Fin k} {S : Type} {input : List Bool} (x : Cfg k Bool S input) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length → x.workTapes src (x.workTapePos src + i) = w[i]?)
    (hleft : x.workTapes src (x.workTapePos src - 1) = none) : True := by
  fail_if_success
    have := emitStage_run x w hsrc hleft (T := 2 * w.length + 3) (by omega)
  trivial

/-- Mutant of `bennettTM_correct`: one step before Bennett's bound. -/
example (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hfix : InputFixed tm) (hcode : Function.Injective code) (hh : 0 < h) (src : Fin k)
    {input : List Bool} (t : ℕ) (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted)
    (hhalt : (tm.runFrom (tm.initCfg input) t).Halted) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length →
      (tm.runFrom (tm.initCfg input) t).workTapes src
        ((tm.runFrom (tm.initCfg input) t).workTapePos src + i) = w[i]?)
    (hleft : (tm.runFrom (tm.initCfg input) t).workTapes src
      ((tm.runFrom (tm.initCfg input) t).workTapePos src - 1) = none) : True := by
  fail_if_success
    have := bennettTM_correct (code := code) hfix hcode hh src t hrun hhalt w hsrc hleft
      (T := 4 * t + 2 * w.length + 5) (by omega)
  trivial

/-- Mutant of `runsInSpace_of_halted`: a window of `T - 1` cells on each side. -/
example (tm : MultiTapeTM k Bool State) {input : List Bool} {T : ℕ}
    (hT : (tm.runFrom (tm.initCfg input) T).Halted) : True := by
  fail_if_success
    have : tm.RunsInSpace input (k * (2 * (T - 1) + 1)) := runsInSpace_of_halted tm hT
  trivial

/-- Mutant of `bennettTM_computesInTimeAndSpace`: without the history tape (`0 < h`). -/
example (tm : MultiTapeTM k Bool State) (code : Record k State → Fin h → Bool)
    (hfix : InputFixed tm) (hcode : Function.Injective code) (src : Fin k)
    {input : List Bool} (t : ℕ) (hrun : ∀ i < t, ¬(tm.runFrom (tm.initCfg input) i).Halted)
    (hhalt : (tm.runFrom (tm.initCfg input) t).Halted) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length →
      (tm.runFrom (tm.initCfg input) t).workTapes src
        ((tm.runFrom (tm.initCfg input) t).workTapePos src + i) = w[i]?)
    (hleft : (tm.runFrom (tm.initCfg input) t).workTapes src
      ((tm.runFrom (tm.initCfg input) t).workTapePos src - 1) = none) : True := by
  fail_if_success
    have := bennettTM_computesInTimeAndSpace (code := code) hfix hcode (by assumption) src t hrun
      hhalt w hsrc hleft
  trivial

end Mutants

end Sagitta.Arrow.TM.Bennett
