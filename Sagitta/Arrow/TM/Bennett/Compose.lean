/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.Uncompute
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

end Sagitta.Arrow.TM.Bennett
