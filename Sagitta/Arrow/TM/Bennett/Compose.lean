/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.Uncompute
import Sagitta.Arrow.TM.Bennett.Copy
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Bennett, step 5: sequential composition keeps reversibility

cslib already has sequential composition, `Turing.MultiTapeTM.seq`: the first machine runs until
its halting step, which is redirected to the initial state of the second (no extra step). This file
reuses it unchanged and proves when it keeps **reversibility** (`IsReversible`, injectivity of the
step on every running configuration).

## When it does

Inside each machine the composite steps exactly as that machine, its states relabeled
injectively, so injectivity can only fail across the two: the **hand-off** of the first machine (a
halting step, redirected to `tm₁.q₀`) against a step of the second machine **into** `tm₁.q₀`.

* `seq_isReversible`: if both machines are reversible and no hand-off configuration is also the
  image of a running step of the second machine (`HandOff`), the composite is reversible.
* `HandOff.of_noReentry`: that holds when no transition of the second machine enters its initial
  state (`NoReentry`). The inverse `uncTM` has this (`uncTM_noReentry`).
* `seq_not_isReversible`: the hypothesis is necessary: a clash gives two running configurations
  with the same successor.

The emitting machine of step 3 loops on its initial state, so it does not have `NoReentry`. A gate
in front of it (`gateTM`: look one cell left on the source tape, check that it is blank, come
back) makes the hand-off distinguishable: after the gate the cell left of the source head is blank,
after a forward step of `emitTM` it holds the symbol just emitted (`gate_emit_handOff`).

## Runs

* `seq_runFrom_left`, `seq_runFrom_right`, `seq_runFrom`: a run of the composite is a run of the
  first machine up to its halting, then a run of the second from where the first stopped.
-/

namespace Sagitta.Arrow.TM.Bennett

open Turing Turing.MultiTapeTM

variable {k : ℕ} {S₀ S₁ : Type} {input : List Bool}

/-! ## The steps of the composite -/

section Steps

variable {tm₀ : MultiTapeTM k Bool S₀} {tm₁ : MultiTapeTM k Bool S₁}

theorem seq_tr_inl (q : S₀) (r : Option Bool) (w : Fin k → Option Bool) :
    (tm₀.seq tm₁).tr (.inl q) r w =
      { tm₀.tr q r w with state := handOver tm₁.q₀ (tm₀.tr q r w).state } := by
  simp only [seq, combine, tr_ofTr, Sum.elim_inl, adaptedTr]
  rfl

theorem seq_tr_inr (q : S₁) (r : Option Bool) (w : Fin k → Option Bool) :
    (tm₀.seq tm₁).tr (.inr q) r w =
      { tm₁.tr q r w with state := (tm₁.tr q r w).state.map .inr } := by
  simp only [seq, combine, tr_ofTr, Sum.elim_inr, adaptedTr]
  rfl

/-- Relabeling the state of an action and of a configuration commutes with applying it. -/
theorem apply_relabel {S S' : Type} (A : Action k Bool S) (φ : Option S → Option S')
    (ψ : Option S → Option S') (c : Cfg k Bool S input) :
    ({ A with state := φ A.state } : Action k Bool S').apply (c.mapState ψ) =
      (A.apply c).mapState φ :=
  Cfg.ext rfl rfl rfl rfl rfl

/-- A running step of `tm₀` inside the composite. -/
theorem seq_step_left {c : Cfg k Bool S₀ input} {q : S₀} (hq : c.state = some q) :
    (tm₀.seq tm₁).step (c.mapState (handOver tm₁.q₀)) =
      (tm₀.step c).mapState (handOver tm₁.q₀) := by
  rw [step_of_state (q := .inl q) (by simp [hq]), step_of_state hq, seq_tr_inl]
  exact apply_relabel _ _ _ c

/-- Every step of `tm₁` inside the composite. -/
theorem seq_step_right (c : Cfg k Bool S₁ input) :
    (tm₀.seq tm₁).step (c.mapState (Option.map .inr)) = (tm₁.step c).mapState (Option.map .inr) := by
  rcases hq : c.state with _ | q
  · rw [step_of_halt hq, step_of_halt (by simp [hq])]
  · rw [step_of_state (q := .inr q) (by simp [hq]), step_of_state hq, seq_tr_inr]
    exact apply_relabel _ _ _ c

theorem handOver_injective (q₁ : S₁) : Function.Injective (handOver (State₀ := S₀) q₁) := by
  intro a b h
  rcases a with _ | a <;> rcases b with _ | b <;> simp_all [handOver]

theorem mapState_injective {S S' : Type} {φ : Option S → Option S'} (hφ : Function.Injective φ) :
    Function.Injective (Cfg.mapState (k := k) (input := input) φ) := by
  intro c c' h
  have hs := congrArg Cfg.state h
  simp only [Cfg.mapState_state] at hs
  have h1 := congrArg (fun x : Cfg k Bool S' input => x.inputPos) h
  have h2 := congrArg (fun x : Cfg k Bool S' input => x.workTapes) h
  have h3 := congrArg (fun x : Cfg k Bool S' input => x.workTapePos) h
  have h4 := congrArg (fun x : Cfg k Bool S' input => x.output) h
  exact Cfg.ext (hφ hs) h1 h2 h3 h4

/-- A configuration of the composite in a state of `tm₀` is the image of one of `tm₀`. -/
theorem eq_mapState_left {d : Cfg k Bool (S₀ ⊕ S₁) input} {q : S₀} (hd : d.state = some (.inl q)) :
    d = (d.withState (some q)).mapState (handOver tm₁.q₀) :=
  Cfg.ext (by simp [hd]) rfl rfl rfl rfl

/-- A configuration of the composite in a state of `tm₁` is the image of one of `tm₁`. -/
theorem eq_mapState_right {d : Cfg k Bool (S₀ ⊕ S₁) input} {q : S₁} (hd : d.state = some (.inr q)) :
    d = (d.withState (some q)).mapState (Option.map .inr) :=
  Cfg.ext (by simp [hd]) rfl rfl rfl rfl

end Steps

/-! ## Reversibility -/

/-- **The hand-off is distinguishable**: no running step of `tm₁` reaches a configuration where a
halting step of `tm₀` hands over to `tm₁`. -/
def HandOff (tm₀ : MultiTapeTM k Bool S₀) (tm₁ : MultiTapeTM k Bool S₁) : Prop :=
  ∀ (input : List Bool) (c : Cfg k Bool S₀ input) (c' : Cfg k Bool S₁ input), ¬c.Halted →
    ¬c'.Halted → (tm₀.step c).Halted → tm₁.step c' ≠ (tm₀.step c).withState (some tm₁.q₀)

/-- No transition of the machine enters its initial state. -/
def NoReentry (tm : MultiTapeTM k Bool S₁) : Prop :=
  ∀ (q : S₁) (r : Option Bool) (w : Fin k → Option Bool), (tm.tr q r w).state ≠ some tm.q₀

theorem HandOff.of_noReentry {tm₀ : MultiTapeTM k Bool S₀} {tm₁ : MultiTapeTM k Bool S₁}
    (h : NoReentry tm₁) : HandOff tm₀ tm₁ := by
  intro input c c' _ hc' _ he
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  have := congrArg Cfg.state he
  rw [step_of_state hq'] at this
  exact h q' _ _ this

variable {tm₀ : MultiTapeTM k Bool S₀} {tm₁ : MultiTapeTM k Bool S₁}

/-- **Sequential composition keeps reversibility** when the hand-off is distinguishable. -/
theorem seq_isReversible (h₀ : IsReversible tm₀) (h₁ : IsReversible tm₁)
    (hoff : HandOff tm₀ tm₁) : IsReversible (tm₀.seq tm₁) := by
  -- one clash, in one order
  have cross : ∀ {input : List Bool} (c : Cfg k Bool S₀ input) (c' : Cfg k Bool S₁ input)
      (q : S₀) (q' : S₁), c.state = some q → c'.state = some q' →
        (tm₀.seq tm₁).step (c.mapState (handOver tm₁.q₀)) ≠
          (tm₀.seq tm₁).step (c'.mapState (Option.map .inr)) := by
    intro input c c' q q' hq hq' he
    rw [seq_step_left hq, seq_step_right] at he
    have hs := congrArg Cfg.state he
    simp only [Cfg.mapState_state] at hs
    rcases h0 : (tm₀.step c).state with _ | p
    · rw [h0] at hs
      rcases h1 : (tm₁.step c').state with _ | p'
      · rw [h1] at hs; simp [handOver] at hs
      · rw [h1] at hs
        simp only [handOver, Option.elim_none, Option.map_some, Option.some.injEq,
          Sum.inr.injEq] at hs
        refine hoff input c c' (by simp [hq]) (by simp [hq']) h0 (Cfg.ext ?_ ?_ ?_ ?_ ?_)
        · rw [h1, ← hs]; rfl
        · exact (show (tm₀.step c).inputPos = (tm₁.step c').inputPos from
            congrArg Cfg.inputPos he).symm
        · exact (show (tm₀.step c).workTapes = (tm₁.step c').workTapes from
            congrArg Cfg.workTapes he).symm
        · exact (show (tm₀.step c).workTapePos = (tm₁.step c').workTapePos from
            congrArg Cfg.workTapePos he).symm
        · exact (show (tm₀.step c).output = (tm₁.step c').output from
            congrArg Cfg.output he).symm
    · rw [h0] at hs
      rcases h1 : (tm₁.step c').state with _ | p' <;> rw [h1] at hs <;> simp [handOver] at hs
  intro input d d' hd hd' he
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hd
  obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.mp hd'
  rcases s with q | q <;> rcases s' with q' | q'
  · rw [eq_mapState_left (tm₁ := tm₁) hs, eq_mapState_left (tm₁ := tm₁) hs'] at he ⊢
    rw [seq_step_left rfl, seq_step_left rfl] at he
    have := h₀ input _ _ (by simp) (by simp) (mapState_injective (handOver_injective _) he)
    rw [this]
  · rw [eq_mapState_left (tm₁ := tm₁) hs, eq_mapState_right hs'] at he
    exact absurd he (cross _ _ q q' rfl rfl)
  · rw [eq_mapState_right hs, eq_mapState_left (tm₁ := tm₁) hs'] at he
    exact absurd he.symm (cross _ _ q' q rfl rfl)
  · rw [eq_mapState_right hs, eq_mapState_right hs'] at he ⊢
    rw [seq_step_right, seq_step_right] at he
    have := h₁ input _ _ (by simp) (by simp)
      (mapState_injective (Option.map_injective Sum.inr_injective) he)
    rw [this]

/-- **The hypothesis is necessary**: a clash at the hand-off breaks reversibility. -/
theorem seq_not_isReversible {input : List Bool} {c : Cfg k Bool S₀ input}
    {c' : Cfg k Bool S₁ input} (hc : ¬c.Halted) (hc' : ¬c'.Halted) (hhalt : (tm₀.step c).Halted)
    (he : tm₁.step c' = (tm₀.step c).withState (some tm₁.q₀)) : ¬IsReversible (tm₀.seq tm₁) := by
  intro hrev
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  have hstep : (tm₀.seq tm₁).step (c.mapState (handOver tm₁.q₀)) =
      (tm₀.seq tm₁).step (c'.mapState (Option.map .inr)) := by
    rw [seq_step_left hq, seq_step_right, he]
    exact Cfg.ext (by simp [handOver, show (tm₀.step c).state = none from hhalt])
      rfl rfl rfl rfl
  have := congrArg Cfg.state (hrev input _ _ (by simp [hq]) (by simp [hq']) hstep)
  simp [hq, hq', handOver] at this

/-! ## Runs of the composite -/

theorem seq_runFrom_left (c : Cfg k Bool S₀ input) (t : ℕ)
    (hrun : ∀ i < t, ¬(tm₀.runFrom c i).Halted) :
    (tm₀.seq tm₁).runFrom (c.mapState (handOver tm₁.q₀)) t =
      (tm₀.runFrom c t).mapState (handOver tm₁.q₀) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply'] at ih ⊢
    rw [ih fun i hi => hrun i (by omega)]
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hrun t (by omega))
    exact seq_step_left hq

theorem seq_runFrom_right (c : Cfg k Bool S₁ input) (t : ℕ) :
    (tm₀.seq tm₁).runFrom (c.mapState (Option.map .inr)) t =
      (tm₁.runFrom c t).mapState (Option.map .inr) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, seq_step_right]

/-- **A run of the composite**: `t₀` steps of `tm₀` up to its halting, then `t₁` steps of `tm₁`
from where `tm₀` stopped. -/
theorem seq_runFrom (c : Cfg k Bool S₀ input) (t₀ t₁ : ℕ)
    (hrun : ∀ i < t₀, ¬(tm₀.runFrom c i).Halted) (hhalt : (tm₀.runFrom c t₀).Halted) :
    (tm₀.seq tm₁).runFrom (c.mapState (handOver tm₁.q₀)) (t₀ + t₁) =
      (tm₁.runFrom ((tm₀.runFrom c t₀).withState (some tm₁.q₀)) t₁).mapState (Option.map .inr) := by
  rw [add_comm t₀ t₁, MultiTapeTM.runFrom, Function.iterate_add_apply, ← MultiTapeTM.runFrom,
    ← MultiTapeTM.runFrom, seq_runFrom_left c t₀ hrun, ← seq_runFrom_right]
  congr 1
  exact Cfg.ext (by simp [show (tm₀.runFrom c t₀).state = none from hhalt, handOver]) rfl rfl rfl
    rfl

theorem seq_initCfg : (tm₀.seq tm₁).initCfg input = (tm₀.initCfg input).mapState (handOver tm₁.q₀) :=
  rfl


/-- **A run of the composite, up to a time bound.** If `tm₀` has halted by `t₀` and `tm₁`, started
where `tm₀` stopped, has halted by `t₁`, the composite has halted by `t₀ + t₁` in the image of the
final configuration of `tm₁` (it switches at the first halting of `tm₀`, possibly earlier). -/
theorem seq_runFrom_of_le (c : Cfg k Bool S₀ input) {t₀ t₁ : ℕ}
    (hhalt : (tm₀.runFrom c t₀).Halted)
    (hhalt₁ : (tm₁.runFrom ((tm₀.runFrom c t₀).withState (some tm₁.q₀)) t₁).Halted)
    {T : ℕ} (hT : t₀ + t₁ ≤ T) :
    (tm₀.seq tm₁).runFrom (c.mapState (handOver tm₁.q₀)) T =
      (tm₁.runFrom ((tm₀.runFrom c t₀).withState (some tm₁.q₀)) t₁).mapState (Option.map .inr) := by
  classical
  have hex : ∃ i, (tm₀.runFrom c i).Halted := ⟨t₀, hhalt⟩
  set τ := Nat.find hex
  have hτ : τ ≤ t₀ := Nat.find_min' hex hhalt
  have hrun : ∀ i < τ, ¬(tm₀.runFrom c i).Halted := fun i hi => Nat.find_min hex hi
  have hsame : tm₀.runFrom c t₀ = tm₀.runFrom c τ := runFrom_eq_of_halt _ _ hτ (Nat.find_spec hex)
  have e := seq_runFrom (tm₁ := tm₁) c τ t₁ hrun (Nat.find_spec hex)
  rw [← hsame] at e
  rw [runFrom_eq_of_halt _ _ (by omega : τ + t₁ ≤ T) (by rw [e]; simp [hhalt₁]), e]

theorem seq_q₀ : (tm₀.seq tm₁).q₀ = .inl tm₀.q₀ := rfl

/-! ## The inverse has no re-entry -/

/-- No transition of the reversible inverse enters its initial state `back none`. -/
theorem uncTM_noReentry {h : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) : NoReentry (uncTM tm code) := by
  intro q r w
  simp only [uncTM, tr_ofTr, q₀_ofTr]
  rcases q with (q | q | rec) | s
  · simp [uncTr, uBack]
  · simp only [uncTr]
    generalize decode code (fun j => w (histTape k j)) = o
    rcases o with _ | rec <;> simp only [uPeek] <;> split_ifs <;> simp [uFinish, uFail, uUndo]
  · simp only [uncTr]; split_ifs <;> simp [uRestore, uFail]
  · simp [uncTr, uSink]

/-! ## The gate in front of the emitting machine -/

/-- The states of the gate. -/
inductive GateState
  /-- Move the source head one cell left. -/
  | start
  /-- Check that the cell is blank and move back (and halt). -/
  | check
  /-- The cell was not blank: append `true` forever. -/
  | sink
  deriving DecidableEq

instance : Finite GateState :=
  Finite.of_injective (β := Fin 3)
    (fun s => match s with | .start => 0 | .check => 1 | .sink => 2)
    (by intro a b; cases a <;> cases b <;> simp)

/-- The actions of the gate: only the head of `src` moves, by `m`, nothing is written, and `o` is
appended to the output. -/
def gateAct (src : Fin k) (m : SignType) (o : Option Bool) (q : Option GateState) :
    Action k Bool GateState :=
  ⟨0, fun i => if i = src then (none, m) else (none, 0), o, q⟩

theorem gateAct_write {src : Fin k} {m : SignType} {o : Option Bool} {q : Option GateState}
    (i : Fin k) : ((gateAct src m o q).workTapes i).1 = none := by
  simp only [gateAct]; split_ifs <;> rfl

theorem gateAct_move {src : Fin k} {m : SignType} {o : Option Bool} {q : Option GateState}
    (i : Fin k) : ((gateAct src m o q).workTapes i).2 = if i = src then m else 0 := by
  simp only [gateAct]; split_ifs <;> rfl

/-- The transition function of the gate. -/
def gateTr (src : Fin k) :
    GateState → Option Bool → (Fin k → Option Bool) → Action k Bool GateState
  | .start, _, _ => gateAct src (-1) none (some .check)
  | .check, _, w => match w src with
    | none => gateAct src 1 none none
    | some _ => gateAct src 0 (some false) (some .sink)
  | .sink, _, _ => gateAct src 0 (some true) (some .sink)

/-- **The gate**: checks that the cell left of the head of `src` is blank, and comes back. -/
def gateTM (src : Fin k) : MultiTapeTM k Bool GateState :=
  ofTr .start (gateTr src)

/-- **The gate is reversible.** -/
theorem gateTM_isReversible (src : Fin k) : IsReversible (gateTM src) := by
  intro input c c' hc hc' hstep
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  rw [step_of_state hq, step_of_state hq', gateTM, tr_ofTr, tr_ofTr] at hstep
  rcases q with _ | _ | _ <;> rcases q' with _ | _ | _ <;>
    rcases hs : c.workTapeSymbols src with _ | b <;>
    rcases hs' : c'.workTapeSymbols src with _ | b' <;>
    simp only [gateTr, hs, hs'] at hstep <;>
    first
    | exact apply_injective _ (hq.trans hq'.symm) (Or.inl rfl) (fun i => Or.inl (gateAct_write i))
        hstep
    | (have h2 := congrArg Cfg.state hstep; simp [gateAct] at h2; done)
    | (have h2 := congrArg (fun x => x.output.getLast?) hstep; simp [gateAct] at h2)


/-- **The gate is correct**: from `start`, with a blank left of the head of `src`, it halts after
two steps with nothing changed. -/
theorem gateTM_run {src : Fin k} (c : Cfg k Bool GateState input) (hst : c.state = some .start)
    (hleft : c.workTapes src (c.workTapePos src - 1) = none) :
    (gateTM src).runFrom c 2 = { c with state := none } := by
  have h1 : (gateTM src).runFrom c 1 = (gateAct src (-1) none (some .check)).apply c := by
    rw [runFrom, Function.iterate_one, step_of_state hst, gateTM, tr_ofTr]; rfl
  have hs : ((gateAct src (-1) none (some .check)).apply c).workTapeSymbols src = none := by
    simp only [Cfg.workTapeSymbols, Action.apply_workTapes, Action.apply_workTapePos, gateAct_write,
      gateAct_move, ↓reduceIte]
    simpa [sub_eq_add_neg] using hleft
  rw [show 2 = 1 + 1 from rfl, runFrom, Function.iterate_succ_apply', ← runFrom, h1,
    step_of_state (q := .check) (by simp [gateAct]), gateTM, tr_ofTr]
  simp only [gateTr, hs]
  apply Cfg.ext
  · simp [gateAct]
  · simp [gateAct, moveInputPos]
  · funext i; simp [Action.apply_workTapes, gateAct_write]
  · funext i
    simp only [Action.apply_workTapePos, gateAct_move]
    split_ifs <;> simp
  · simp [gateAct]

/-- **The hand-off from the gate to the emitting machine is distinguishable**: after the gate the
cell left of the head of `src` is blank, after a forward step of `emitTM` it holds a symbol. -/
theorem gate_emit_handOff (src : Fin k) : HandOff (gateTM src) (emitTM src) := by
  intro input c c' hc hc' hhalt he
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  rw [step_of_state hq, gateTM, tr_ofTr] at hhalt he
  rw [step_of_state hq', emitTM, tr_ofTr] at he
  have ht := congrFun (congrArg Cfg.workTapes he) src
  have hp := congrFun (congrArg Cfg.workTapePos he) src
  have hst := congrArg Cfg.state he
  rcases q with _ | _ | _ <;> rcases q' with _ | _ <;>
    rcases hs : c.workTapeSymbols src with _ | b <;>
    rcases hs' : c'.workTapeSymbols src with _ | b' <;>
    simp only [gateTr, emitTr, hs, hs'] at hhalt ht hp hst <;>
    simp [gateAct, emitAct, Cfg.Halted] at hhalt hst
  -- the one case left: the gate halts reading a blank, `emitTM` steps forward reading `b'`
  simp only [Action.apply_workTapes, Action.apply_workTapePos, Cfg.withState, gateAct_write,
    emitAct_write, gateAct_move, emitAct_move, ↓reduceIte] at ht hp
  have hp' : c'.workTapePos src = c.workTapePos src := by simpa using hp
  have : c'.workTapeSymbols src = c.workTapeSymbols src := by
    simp only [Cfg.workTapeSymbols, ht, hp']
  rw [hs, hs'] at this
  exact absurd this (by simp)

/-- The gate followed by the emitting machine never re-enters its initial state. -/
theorem gate_emit_noReentry (src : Fin k) : NoReentry ((gateTM src).seq (emitTM src)) := by
  intro q r w
  rw [seq_q₀]
  rcases q with q | q
  · rw [seq_tr_inl]
    simp only [gateTM, tr_ofTr, q₀_ofTr]
    rcases q with _ | _ | _ <;> simp only [gateTr] <;> (try split) <;> simp [gateAct, handOver]
  · rw [seq_tr_inr]
    generalize ((emitTM src).tr q r w).state = o
    rcases o with _ | o <;> simp

/-- **The emitting machine re-enters its initial state** (a forward step goes back to `fwd`), so
it needs the gate. -/
theorem emitTM_not_noReentry (src : Fin k) : ¬NoReentry (emitTM src) := by
  intro h
  exact h .fwd none (fun _ => some true) (by simp [emitTM, emitTr, emitAct])

/-! ## Checks: the axioms, and one mutant per central theorem -/

/-- info: 'Sagitta.Arrow.TM.Bennett.seq_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.seq_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.seq_not_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.seq_not_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.HandOff.of_noReentry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.HandOff.of_noReentry
/-- info: 'Sagitta.Arrow.TM.Bennett.seq_runFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.seq_runFrom
/-- info: 'Sagitta.Arrow.TM.Bennett.seq_runFrom_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.seq_runFrom_of_le
/-- info: 'Sagitta.Arrow.TM.Bennett.uncTM_noReentry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.uncTM_noReentry
/-- info: 'Sagitta.Arrow.TM.Bennett.emitTM_not_noReentry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.emitTM_not_noReentry
/-- info: 'Sagitta.Arrow.TM.Bennett.gateTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.gateTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.gateTM_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.gateTM_run
/-- info: 'Sagitta.Arrow.TM.Bennett.gate_emit_handOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.gate_emit_handOff
/-- info: 'Sagitta.Arrow.TM.Bennett.gate_emit_noReentry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.gate_emit_noReentry

section Mutants

set_option linter.unusedVariables false

/-- Mutant of `seq_isReversible`: without the hand-off hypothesis. -/
example (tm₀ : MultiTapeTM k Bool S₀) (tm₁ : MultiTapeTM k Bool S₁) (h₀ : IsReversible tm₀)
    (h₁ : IsReversible tm₁) : True := by
  fail_if_success
    have : IsReversible (tm₀.seq tm₁) := seq_isReversible h₀ h₁ (by assumption)
  trivial

/-- Mutant of `seq_not_isReversible`: the first step does not halt. -/
example (tm₀ : MultiTapeTM k Bool S₀) (tm₁ : MultiTapeTM k Bool S₁) {input : List Bool}
    (c : Cfg k Bool S₀ input) (c' : Cfg k Bool S₁ input) (hc : ¬c.Halted) (hc' : ¬c'.Halted)
    (he : tm₁.step c' = (tm₀.step c).withState (some tm₁.q₀)) : True := by
  fail_if_success
    have : ¬IsReversible (tm₀.seq tm₁) := seq_not_isReversible hc hc' (by assumption) he
  trivial

/-- Mutant of `HandOff.of_noReentry`: no re-entry of the first machine instead of the second. -/
example (tm₀ : MultiTapeTM k Bool S₀) (tm₁ : MultiTapeTM k Bool S₁) (h : NoReentry tm₀) :
    True := by
  fail_if_success
    have : HandOff tm₀ tm₁ := HandOff.of_noReentry h
  trivial

/-- Mutant of `seq_runFrom`: without the running hypothesis on `tm₀`. -/
example (tm₀ : MultiTapeTM k Bool S₀) (tm₁ : MultiTapeTM k Bool S₁) {input : List Bool}
    (c : Cfg k Bool S₀ input) (t₀ t₁ : ℕ) (hhalt : (tm₀.runFrom c t₀).Halted) : True := by
  fail_if_success
    have := seq_runFrom (tm₁ := tm₁) c t₀ t₁ (by assumption) hhalt
  trivial

/-- Mutant of `seq_runFrom_of_le`: one step before the bound. -/
example (tm₀ : MultiTapeTM k Bool S₀) (tm₁ : MultiTapeTM k Bool S₁) {input : List Bool}
    (c : Cfg k Bool S₀ input) (t₀ t₁ : ℕ) (hhalt : (tm₀.runFrom c t₀).Halted)
    (hhalt₁ : (tm₁.runFrom ((tm₀.runFrom c t₀).withState (some tm₁.q₀)) t₁).Halted)
    (hpos : 0 < t₀ + t₁) : True := by
  fail_if_success
    have := seq_runFrom_of_le c hhalt hhalt₁ (T := t₀ + t₁ - 1) (by omega)
  trivial

/-- Mutant of `uncTM_noReentry`: the emitting machine in its place. -/
example (src : Fin k) : True := by
  fail_if_success
    have : NoReentry (emitTM src) := uncTM_noReentry (h := 0) (emitTM src) (fun _ => Fin.elim0)
  trivial

/-- Mutant of `emitTM_not_noReentry`: the gate in its place. -/
example (src : Fin k) : True := by
  fail_if_success
    have : ¬NoReentry (gateTM src) := emitTM_not_noReentry src
  trivial

/-- Mutant of `gateTM_isReversible`: the copying machine onto its own source. -/
example (src : Fin k) : True := by
  fail_if_success
    have : IsReversible (copyTM src src) := gateTM_isReversible src
  trivial

/-- Mutant of `gateTM_run`: without the blank to the left. -/
example (src : Fin k) {input : List Bool} (c : Cfg k Bool GateState input)
    (hst : c.state = some .start) : True := by
  fail_if_success
    have := gateTM_run (src := src) c hst (by assumption)
  trivial

/-- Mutant of `gate_emit_handOff`: the emitting machine without the gate. -/
example (src : Fin k) : True := by
  fail_if_success
    have : HandOff (emitTM src) (emitTM src) := gate_emit_handOff src
  trivial

/-- Mutant of `gate_emit_noReentry`: the emitting machine alone. -/
example (src : Fin k) : True := by
  fail_if_success
    have : NoReentry (emitTM src) := gate_emit_noReentry src
  trivial

end Mutants

end Sagitta.Arrow.TM.Bennett
