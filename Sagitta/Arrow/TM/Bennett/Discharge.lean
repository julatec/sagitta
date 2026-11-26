/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.Machine
import Sagitta.Arrow.TM.Bennett.Normal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Sagitta.Arrow.TM.Decision

/-!
# Bennett, step 7: the hypothesis is a theorem

Every function computable in polynomial time by a machine of cslib is computed in polynomial time
and space by a **reversible** machine with finitely many states (`bennett_holds : Bennett`). The
machine, for a machine `M` computing `f`, is

`(prepTM vip flag).seq (bennettTM (normTM M) code outTape)`:

1. `prepTM` (`Prepare.lean`) writes the input on a virtual input tape and marks the cell before it,
   reversibly; the input head ends on the blank after the input and stays there;
2. `bennettTM` (step 6) on the normal form `normTM M` (`Normal.lean`), which never moves nor reads
   the input head, reads the virtual input and leaves `encOut (f a)` on `outTape`: compute with a
   history, emit, uncompute.

Bennett's machine of step 6 was stated from the initial configuration; here it starts where the
preparing machine stopped (`bennettTM_correct_from`, the same proof from any clean configuration
with blank history tapes). The hand-off between the two machines is distinguishable because the
normal form never re-enters its initial state (`bennettTM_noReentry'`).

The run is exact (`revTM_correct_clean`): by time `2 n + 4 t + 6 |y| + 21` the machine has halted
with the output `y`, every work head on cell `0`, and every work tape blank except the copy of the
input and the flag's mark, so the history is erased (Bennett's "no garbage", `ComputesCleanly`).
This is at most `2 n + 10 t(n) + 21` for a machine that runs in time `t`, and the space is linear
in the time: `bennett_holds` gives time and space linear in `n + t(n)`.

The mutant: `histOnlyTM` is the same machine without the uncomputation (the Lecerf–Landauer
simulation). It is reversible and correct, so it proves the old, weaker statement
(`bennett_of_history_only : BennettWeak`), but its history heads end off cell `0`, so it is never
clean (`histOnlyTM_not_computesCleanly`): the statement `Bennett` tells the two apart.
-/

namespace Sagitta.Arrow.TM.Bennett

open Cslib Turing Turing.MultiTapeTM

variable {k h : ℕ} {State : Type}

/-! ## Bennett's machine from a clean configuration -/

section From

variable {tm : MultiTapeTM k Bool State} {code : Record k State → Fin h → Bool} {input : List Bool}

/-- **Bennett's machine is correct from any clean start**: the configuration `c₀` in the initial
state of `tm`, with blank history tapes, plays the role of the initial configuration. -/
theorem bennettTM_correct_from (hfix : InputFixed tm) (hcode : Function.Injective code)
    (hh : 0 < h) (src : Fin k) (c₀ : Cfg (k + h) Bool (State ⊕ State) input)
    (hq₀ : c₀.state = some (.inl tm.q₀))
    (hblank : ∀ (j : Fin h) (z : ℤ), c₀.workTapes (histTape k j) z = none) (t : ℕ)
    (hrun : ∀ i < t, ¬(tm.runFrom (proj c₀) i).Halted)
    (hhalt : (tm.runFrom (proj c₀) t).Halted) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length →
      (tm.runFrom (proj c₀) t).workTapes src ((tm.runFrom (proj c₀) t).workTapePos src + i) =
        w[i]?)
    (hleft : (tm.runFrom (proj c₀) t).workTapes src
      ((tm.runFrom (proj c₀) t).workTapePos src - 1) = none)
    {T : ℕ} (hT : 4 * t + 2 * w.length + 6 ≤ T) :
    (bennettTM tm code src).runFrom
        ((c₀.mapState (handOver (emitStage (k := k + h) (mainTape h src)).q₀)).mapState
          (handOver (uncTM tm code).q₀)) T =
      ⟨none, c₀.inputPos, c₀.workTapes, c₀.workTapePos,
        (tm.runFrom (proj c₀) t).output ++ w⟩ := by
  have hc₀ : Clean c₀ := ⟨fun q => by rw [hq₀]; simp, fun j z _ => hblank j z⟩
  set e := tm.runFrom (proj c₀) t with he
  set H := histTM tm code
  set E := emitStage (k := k + h) (mainTape h src)
  set U := uncTM tm code
  set x := H.runFrom c₀ t with hx
  have hsim := runFrom_clean (tm := tm) (code := code) hc₀
  have hproj : proj x = e := (hsim t).1
  have hxs : x.state = none := by
    have h1 : (proj x).state = none := by rw [hproj]; exact hhalt
    rcases hs : x.state with _ | q | q
    · rfl
    · simp [proj, hs] at h1
    · exact absurd hs ((hsim t).2.1 q)
  have hxhalt : x.Halted := hxs
  have hrunH : ∀ i < t, ¬(H.runFrom c₀ i).Halted := by
    intro i hi hH
    apply hrun i hi
    rw [← (hsim i).1]
    simp [Cfg.Halted, proj, show (H.runFrom c₀ i).state = none from hH]
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
      (H.seq E).runFrom (c₀.mapState (handOver E.q₀)) T' =
        ({ x.withState (State' := GateState ⊕ CopyState) none with output := x.output ++ w } :
          Cfg (k + h) Bool (GateState ⊕ CopyState) input).mapState (Option.map .inr) := by
    intro T' hT'
    rw [seq_runFrom_of_le c₀ hxhalt (by rw [hE]; rfl) hT', hE]
  -- then uncompute
  have hmirror : (((H.seq E).runFrom (c₀.mapState (handOver E.q₀))
      (t + (2 + (2 * w.length + 2)))).withState (some U.q₀)) = mirror x (x.output ++ w) := by
    rw [hHE _ le_rfl]
    exact Cfg.ext (by simp [mirror, hxs, U, uncTM]) rfl rfl rfl rfl
  have hU : U.runFrom (mirror x (x.output ++ w)) (3 * t + 2) = halted c₀ (x.output ++ w) := by
    have e3 : ∀ y : Cfg (k + h) Bool (UncState k State ⊕ UncState k State) input,
        U.runFrom y (3 * t + 2) = U.runFrom (U.runFrom y (3 * t)) 2 := fun y =>
      (congrArg (fun n => U.step^[n] y) (add_comm (3 * t) 2)).trans
        (Function.iterate_add_apply _ _ _ _)
    rw [e3, uncTM_runBack hfix hcode hc₀ _ t hrunH]
    exact uncTM_finish hh hq₀ (fun j => hblank j _) _
  have hT₂ : t + (2 + (2 * w.length + 2)) + (3 * t + 2) ≤ T := by omega
  rw [bennettTM, seq_runFrom_of_le (c₀.mapState (handOver E.q₀))
      (by rw [hHE _ le_rfl]; rfl) (by rw [hmirror, hU]; rfl) hT₂, hmirror, hU]
  exact Cfg.ext rfl rfl rfl rfl (by simp [halted, hxo])

/-- **The history heads advance one cell per step**: on a clean run that has not halted, each
history head has moved `t` cells to the right after `t` steps. This is the trace that a history
simulation leaves when it does not uncompute. -/
theorem histTM_histPos {c : Cfg (k + h) Bool (State ⊕ State) input} (hc : Clean c) (j : Fin h) :
    ∀ t : ℕ, (∀ i < t, ¬(tm.runFrom (proj c) i).Halted) →
      ((histTM tm code).runFrom c t).workTapePos (histTape k j) =
        c.workTapePos (histTape k j) + t
  | 0, _ => by simp [runFrom]
  | t + 1, hr => by
    have ih := histTM_histPos hc j t fun i hi => hr i (by omega)
    have hsim := runFrom_clean (tm := tm) (code := code) hc t
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    set d := (histTM tm code).runFrom c t with hd
    rcases hst : d.state with _ | q | q
    · exact absurd (by rw [← hsim.1]; simp [Cfg.Halted, proj, hst]) (hr t (by omega))
    · have hguard : ∀ j : Fin h, d.workTapeSymbols (histTape k j) = none :=
        fun j => hsim.2.2 j _ le_rfl
      rw [step_of_state hst, histTM, tr_ofTr, histTr,
        ite_eq_left_of_eq_true _ _ (eq_true hguard)]
      simp only [Action.apply_workTapePos, goodAction, Fin.addCases_right, SignType.coe_one]
      rw [ih]
      push_cast
      ring
    · exact absurd hst (hsim.2.1 q)

/-- **Compute with a history and emit, without uncomputing** (the Lecerf–Landauer simulation): from
a clean start, the history machine followed by the emitting stage halts with the output of `tm`
followed by `w`, and leaves the history machine's final configuration (history included) on the
work tapes. -/
theorem histEmit_correct_from (src : Fin k) (c₀ : Cfg (k + h) Bool (State ⊕ State) input)
    (hq₀ : c₀.state = some (.inl tm.q₀))
    (hblank : ∀ (j : Fin h) (z : ℤ), c₀.workTapes (histTape k j) z = none) (t : ℕ)
    (hhalt : (tm.runFrom (proj c₀) t).Halted) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length →
      (tm.runFrom (proj c₀) t).workTapes src ((tm.runFrom (proj c₀) t).workTapePos src + i) =
        w[i]?)
    (hleft : (tm.runFrom (proj c₀) t).workTapes src
      ((tm.runFrom (proj c₀) t).workTapePos src - 1) = none)
    {T : ℕ} (hT : t + 2 * w.length + 4 ≤ T) :
    ((histTM tm code).seq (emitStage (k := k + h) (mainTape h src))).runFrom
        (c₀.mapState (handOver (emitStage (k := k + h) (mainTape h src)).q₀)) T =
      ({ ((histTM tm code).runFrom c₀ t).withState (State' := GateState ⊕ CopyState) none with
          output := (tm.runFrom (proj c₀) t).output ++ w } :
        Cfg (k + h) Bool (GateState ⊕ CopyState) input).mapState (Option.map .inr) := by
  have hc₀ : Clean c₀ := ⟨fun q => by rw [hq₀]; simp, fun j z _ => hblank j z⟩
  set e := tm.runFrom (proj c₀) t with he
  set H := histTM tm code
  set E := emitStage (k := k + h) (mainTape h src)
  set x := H.runFrom c₀ t with hx
  have hsim := runFrom_clean (tm := tm) (code := code) hc₀
  have hproj : proj x = e := (hsim t).1
  have hxs : x.state = none := by
    have h1 : (proj x).state = none := by rw [hproj]; exact hhalt
    rcases hs : x.state with _ | q | q
    · rfl
    · simp [proj, hs] at h1
    · exact absurd hs ((hsim t).2.1 q)
  have hxhalt : x.Halted := hxs
  have hxt : x.workTapes (mainTape h src) = e.workTapes src := by
    rw [← hproj]; rfl
  have hxp : x.workTapePos (mainTape h src) = e.workTapePos src := by
    rw [← hproj]; rfl
  have hxo : x.output = e.output := by rw [← hproj]; rfl
  have hE : E.runFrom (x.withState (some E.q₀)) (2 + (2 * w.length + 2)) =
      { x.withState (State' := GateState ⊕ CopyState) none with output := x.output ++ w } :=
    emitStage_run x w (by rw [hxt, hxp]; exact hsrc) (by rw [hxt, hxp]; exact hleft) le_rfl
  rw [seq_runFrom_of_le c₀ hxhalt (by rw [hE]; rfl)
    (show t + (2 + (2 * w.length + 2)) ≤ T by omega), hE, hxo]

/-- **Bennett's machine does not re-enter its initial state** if `tm` does not. -/
theorem bennettTM_noReentry' (h₀ : NoReentry tm) (src : Fin k) :
    NoReentry (bennettTM tm code src) :=
  seq_noReentry (seq_noReentry (histTM_noReentry code h₀))

end From

/-! ## The reversible machine for any machine -/

/-- The states of the normal form of a machine with states `S`. -/
abbrev NState (S : Type) : Type := Unit ⊕ (S ⊕ RewindWorkState)

/-- The number of history tapes: one per record of the normal form (the one-hot code). -/
noncomputable abbrev histCount (k : ℕ) (S : Type) [Finite S] : ℕ :=
  Nat.card (Record (k + 1 + 2) (NState S))

/-- **The reversible machine for `M`**: prepare the virtual input, then Bennett's machine on the
normal form of `M`. -/
noncomputable def revTM {S : Type} [Finite S] (M : MultiTapeTM k Bool S) :=
  (prepTM (mainTape (histCount k S) (vipTape k)) (mainTape (histCount k S) (flagTape k))).seq
    (bennettTM (normTM M) (oneHot (Record (k + 1 + 2) (NState S))) (outTape k))

section Rev

variable {S : Type} [Finite S] (M : MultiTapeTM k Bool S)

theorem mainTape_vip_ne_flag : mainTape (histCount k S) (vipTape k) ≠
    mainTape (histCount k S) (flagTape k) := fun e =>
  vipTape_ne_flagTape (Fin.castAdd_injective _ _ e)

/-- **The machine is reversible.** -/
theorem revTM_isReversible : IsReversible (revTM M) :=
  seq_isReversible (prepTM_isReversible mainTape_vip_ne_flag)
    (bennettTM_isReversible (normTM_inputFixed M).staysOnBlank (oneHot_injective _) (outTape k))
    (HandOff.of_noReentry (bennettTM_noReentry' (normTM_noReentry M) (outTape k)))

/-- The work tapes that the reversible machine leaves on the input `x`: the copy of `x` on the
virtual input tape, the mark at cell `-1` of the flag tape, every other tape (the history tapes
among them) blank. -/
def revTapes (k h : ℕ) (x : List Bool) : Fin (k + 1 + 2 + h) → ℤ → Option Bool :=
  Function.update (Function.update (fun _ _ => none) (mainTape h (vipTape k)) (tapeOfList x))
    (mainTape h (flagTape k)) (Function.update (fun _ => none) (-1) (some true))

/-- The role of each work tape at the end: the flag tape holds the mark, the virtual input tape the
input, every other tape is blank. It does not depend on the input. -/
def revRole (k h : ℕ) (i : Fin (k + 1 + 2 + h)) : Residue :=
  if i = mainTape h (flagTape k) then .mark
  else if i = mainTape h (vipTape k) then .input else .blank

theorem revTapes_eq_role (h : ℕ) (x : List Bool) :
    revTapes k h x = fun i => (revRole k h i).tape x := by
  funext i
  simp only [revTapes, revRole]
  by_cases hF : i = mainTape h (flagTape k)
  · subst hF
    simp [Residue.tape]
  · by_cases hV : i = mainTape h (vipTape k)
    · subst hV
      simp [Residue.tape, hF]
    · simp [Residue.tape, hF, hV]

/-- **The machine is correct and clean, with its exact time.** If `M` has halted by time `t` on
`x` with output `y`, then by time `2 |x| + 4 t + 6 |y| + 21` the reversible machine has halted with
output `y`, every work head on cell `0`, the input head on the blank after the input, and every work
tape blank except the copy of `x` and the flag's mark (`revTapes`): the history is erased. The
count: `2 |x| + 3` to copy the input; `4 t'` for the history run, the emission's gate and the
uncomputation of the normal form, which runs `t' = 1 + t + |y| + 2` steps; `2 |y| + 6` to emit. -/
theorem revTM_correct_clean (x : List Bool) (t : ℕ) (hhalt : (M.runFrom (M.initCfg x) t).Halted)
    {T : ℕ} (hT : 2 * x.length + 4 * t + 6 * (M.runFrom (M.initCfg x) t).output.length + 21 ≤ T) :
    (revTM M).runFrom ((revTM M).initCfg x) T =
      ⟨none, Fin.last _, revTapes k (histCount k S) x, fun _ => 0,
        (M.runFrom (M.initCfg x) t).output⟩ := by
  classical
  set y := (M.runFrom (M.initCfg x) t).output with hy
  set hN := histCount k S
  set V := mainTape hN (vipTape k)
  set F := mainTape hN (flagTape k)
  set P := prepTM V F
  set N := normTM M
  set B := bennettTM N (oneHot (Record (k + 1 + 2) (NState S))) (outTape k)
  -- the preparing machine
  have hD := prepTM_correct (input := x) mainTape_vip_ne_flag (P.initCfg x) rfl
    (by simp [MultiTapeNTM.initCfg, Cfg.init]) rfl rfl rfl rfl
  set c₀ : Cfg (k + 1 + 2 + hN) Bool (NState S ⊕ NState S) x :=
    ⟨some (.inl N.q₀), Fin.last _,
      Function.update (Function.update (fun _ _ => none) V (tapeOfList x)) F
        (Function.update (fun _ => none) (-1) (some true)), fun _ => 0, []⟩ with hc₀
  have hblank : ∀ (j : Fin hN) (z : ℤ), c₀.workTapes (histTape (k + 1 + 2) j) z = none := by
    intro j z
    simp only [hc₀]
    rw [Function.update_of_ne, Function.update_of_ne]
    · simp [V, Fin.ext_iff]; omega
    · simp [F, Fin.ext_iff]; omega
  have hproj : proj c₀ = ⟨some N.q₀, Fin.last _, prepTapes k x, fun _ => 0, []⟩ := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i z
      simp only [proj, hc₀, prepTapes, V, F]
      simp only [Function.update_apply, Fin.castAdd_inj]
    · rfl
    · rfl
  -- the normal form, and its first halting time
  obtain ⟨n1, n2, n3, n4⟩ := normTM_run (tm := M) (input := x) (Fin.last _) t hhalt
  rw [← hy] at n1 n2 n3 n4
  set t' := 1 + (t + (y.length + 2))
  have hex : ∃ i, (N.runFrom (proj c₀) i).Halted := ⟨t', by rw [hproj]; exact n1⟩
  set τ := Nat.find hex
  have hτ : τ ≤ t' := Nat.find_min' hex (by rw [hproj]; exact n1)
  have hsame : N.runFrom (proj c₀) τ = N.runFrom (proj c₀) t' :=
    (runFrom_eq_of_halt N _ hτ (Nat.find_spec hex)).symm
  have hB := bennettTM_correct_from (code := oneHot (Record (k + 1 + 2) (NState S)))
    (normTM_inputFixed M) (oneHot_injective _) (oneHot_pos (k := k + 1 + 2) N.q₀) (outTape k) c₀
    rfl hblank τ (fun i hi => Nat.find_min hex hi) (Nat.find_spec hex) y
    (fun i hi => by
      rw [hsame, hproj, n3, n4, zero_add]
      exact tapeOfList_ofNat y i)
    (by rw [hsame, hproj, n3, n4]; rfl) (T := 4 * τ + 2 * y.length + 6) le_rfl
  have hout : (N.runFrom (proj c₀) τ).output = [] := by rw [hsame, hproj, n2]
  rw [hout, List.nil_append] at hB
  -- the hand-off
  have hstart : (P.runFrom (P.initCfg x) (2 * x.length + 3)).withState (some B.q₀) =
      (c₀.mapState (handOver (emitStage (k := k + 1 + 2 + hN) (mainTape hN (outTape k))).q₀)).mapState
        (handOver (uncTM N (oneHot (Record (k + 1 + 2) (NState S)))).q₀) := by
    rw [hD]
    apply Cfg.ext
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have hall := seq_runFrom_of_le (tm₀ := P) (tm₁ := B) (P.initCfg x)
    (t₀ := 2 * x.length + 3) (t₁ := 4 * τ + 2 * y.length + 6) (by rw [hD])
    (by rw [hstart]; unfold B; rw [hB]) (T := T) (by omega)
  rw [show (revTM M).initCfg x = (P.initCfg x).mapState (handOver B.q₀) from rfl]
  unfold revTM
  rw [hall, hstart]
  unfold B
  rw [hB]
  rfl

/-- **The machine is correct.** If `M` has halted by time `t` on `x` with output `y`, the
reversible machine has halted with output `y` by time
`2 |x| + 3 + 4 (1 + t + |y| + 2) + 2 |y| + 6 = 2 |x| + 4 t + 6 |y| + 21`. -/
theorem revTM_correct (x : List Bool) (t : ℕ) (hhalt : (M.runFrom (M.initCfg x) t).Halted)
    {T : ℕ} (hT : 2 * x.length + 3 +
      (4 * (1 + (t + ((M.runFrom (M.initCfg x) t).output.length + 2))) +
        2 * (M.runFrom (M.initCfg x) t).output.length + 6) ≤ T) :
    ((revTM M).runFrom ((revTM M).initCfg x) T).Halted ∧
      ((revTM M).runFrom ((revTM M).initCfg x) T).output = (M.runFrom (M.initCfg x) t).output := by
  rw [revTM_correct_clean M x t hhalt (T := T) (by omega)]
  exact ⟨rfl, rfl⟩

/-! ## The mutant: a history simulation that never uncomputes -/

/-- **The Lecerf–Landauer machine for `M`**: prepare the virtual input, run the normal form of `M`
keeping a history, emit the output, and stop, **without uncomputing**. It is reversible and computes
what `M` computes, but leaves the history on its work tapes. -/
noncomputable def histOnlyTM :=
  (prepTM (mainTape (histCount k S) (vipTape k)) (mainTape (histCount k S) (flagTape k))).seq
    ((histTM (normTM M) (oneHot (Record (k + 1 + 2) (NState S)))).seq
      (emitStage (k := k + 1 + 2 + histCount k S) (mainTape (histCount k S) (outTape k))))

/-- The Lecerf–Landauer machine is reversible. -/
theorem histOnlyTM_isReversible : IsReversible (histOnlyTM M) :=
  seq_isReversible (prepTM_isReversible mainTape_vip_ne_flag)
    (seq_isReversible
      (histTM_isReversible (normTM_inputFixed M).staysOnBlank (oneHot_injective _))
      (seq_isReversible (gateTM_isReversible _) (emitTM_isReversible _) (gate_emit_handOff _))
      (HandOff.of_noReentry (gate_emit_noReentry _)))
    (HandOff.of_noReentry (seq_noReentry (histTM_noReentry _ (normTM_noReentry M))))

/-- **The Lecerf–Landauer machine computes `M`'s output and leaves its history.** If `M` has halted
by time `t` on `x` with output `y`, then by time `2 |x| + t + 3 |y| + 10` the machine has halted
with output `y`, and every history head has moved off cell `0` (the history tapes hold the records
of the run). -/
theorem histOnlyTM_run (x : List Bool) (t : ℕ) (hhalt : (M.runFrom (M.initCfg x) t).Halted)
    {T : ℕ} (hT : 2 * x.length + t + 3 * (M.runFrom (M.initCfg x) t).output.length + 10 ≤ T) :
    ((histOnlyTM M).runFrom ((histOnlyTM M).initCfg x) T).Halted ∧
      ((histOnlyTM M).runFrom ((histOnlyTM M).initCfg x) T).output =
        (M.runFrom (M.initCfg x) t).output ∧
      ∀ j : Fin (histCount k S),
        0 < ((histOnlyTM M).runFrom ((histOnlyTM M).initCfg x) T).workTapePos
          (histTape (k + 1 + 2) j) := by
  classical
  set y := (M.runFrom (M.initCfg x) t).output with hy
  set hN := histCount k S
  set V := mainTape hN (vipTape k)
  set F := mainTape hN (flagTape k)
  set P := prepTM V F
  set N := normTM M
  set B := bennettTM N (oneHot (Record (k + 1 + 2) (NState S))) (outTape k)
  -- the preparing machine
  have hD := prepTM_correct (input := x) mainTape_vip_ne_flag (P.initCfg x) rfl
    (by simp [MultiTapeNTM.initCfg, Cfg.init]) rfl rfl rfl rfl
  set c₀ : Cfg (k + 1 + 2 + hN) Bool (NState S ⊕ NState S) x :=
    ⟨some (.inl N.q₀), Fin.last _,
      Function.update (Function.update (fun _ _ => none) V (tapeOfList x)) F
        (Function.update (fun _ => none) (-1) (some true)), fun _ => 0, []⟩ with hc₀
  have hblank : ∀ (j : Fin hN) (z : ℤ), c₀.workTapes (histTape (k + 1 + 2) j) z = none := by
    intro j z
    simp only [hc₀]
    rw [Function.update_of_ne, Function.update_of_ne]
    · simp [V, Fin.ext_iff]; omega
    · simp [F, Fin.ext_iff]; omega
  have hproj : proj c₀ = ⟨some N.q₀, Fin.last _, prepTapes k x, fun _ => 0, []⟩ := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i z
      simp only [proj, hc₀, prepTapes, V, F]
      simp only [Function.update_apply, Fin.castAdd_inj]
    · rfl
    · rfl
  -- the normal form, and its first halting time
  obtain ⟨n1, n2, n3, n4⟩ := normTM_run (tm := M) (input := x) (Fin.last _) t hhalt
  rw [← hy] at n1 n2 n3 n4
  set t' := 1 + (t + (y.length + 2))
  have hex : ∃ i, (N.runFrom (proj c₀) i).Halted := ⟨t', by rw [hproj]; exact n1⟩
  set τ := Nat.find hex
  have hτ : τ ≤ t' := Nat.find_min' hex (by rw [hproj]; exact n1)
  have hsame : N.runFrom (proj c₀) τ = N.runFrom (proj c₀) t' :=
    (runFrom_eq_of_halt N _ hτ (Nat.find_spec hex)).symm
  have hτ1 : 0 < τ := Nat.pos_of_ne_zero fun h0 => by
    have hs := Nat.find_spec hex
    rw [show Nat.find hex = 0 from h0, hproj] at hs
    simp [MultiTapeTM.runFrom, Cfg.Halted] at hs
  set HE := (histTM N (oneHot (Record (k + 1 + 2) (NState S)))).seq
    (emitStage (k := k + 1 + 2 + hN) (mainTape hN (outTape k)))
  have hE := histEmit_correct_from (code := oneHot (Record (k + 1 + 2) (NState S))) (outTape k) c₀
    rfl hblank τ (Nat.find_spec hex) y
    (fun i hi => by
      rw [hsame, hproj, n3, n4, zero_add]
      exact tapeOfList_ofNat y i)
    (by rw [hsame, hproj, n3, n4]; rfl) (T := τ + 2 * y.length + 4) le_rfl
  have hout : (N.runFrom (proj c₀) τ).output = [] := by rw [hsame, hproj, n2]
  rw [hout, List.nil_append] at hE
  have hpos := histTM_histPos (tm := N) (code := oneHot (Record (k + 1 + 2) (NState S)))
    (input := x) (c := c₀) ⟨fun q h => by simp [hc₀] at h, fun j z _ => hblank j z⟩
  have hstart : (P.runFrom (P.initCfg x) (2 * x.length + 3)).withState (some HE.q₀) =
      c₀.mapState (handOver (emitStage (k := k + 1 + 2 + hN) (mainTape hN (outTape k))).q₀) := by
    rw [hD]
    apply Cfg.ext
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have hall := seq_runFrom_of_le (tm₀ := P) (tm₁ := HE) (P.initCfg x)
    (t₀ := 2 * x.length + 3) (t₁ := τ + 2 * y.length + 4) (by rw [hD])
    (by rw [hstart]; unfold HE; rw [hE]; rfl) (T := T) (by omega)
  rw [show (histOnlyTM M).initCfg x = (P.initCfg x).mapState (handOver HE.q₀) from rfl]
  unfold histOnlyTM
  rw [hall, hstart]
  unfold HE
  rw [hE]
  refine ⟨rfl, rfl, fun j => ?_⟩
  show 0 < ((histTM N _).runFrom c₀ τ).workTapePos (histTape (k + 1 + 2) j)
  rw [hpos j τ fun i hi => Nat.find_min hex hi]
  simp only [hc₀]
  omega

/-- **The Lecerf–Landauer machine is not clean**: on any input where `M` halts, it does not end
in the configuration that `ComputesCleanly` asks for, at any time. -/
theorem histOnlyTM_not_computesCleanly {α β : Type} (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (f : α → β) (T : α → ℕ) (a : α)
    (hM : ∃ t, (M.runFrom (M.initCfg (encIn a)) t).Halted) :
    ¬ComputesCleanly (histOnlyTM M) encIn encOut f T := by
  rintro ⟨role, hclean⟩
  obtain ⟨t, ht⟩ := hM
  set x := encIn a
  set B := 2 * x.length + t + 3 * (M.runFrom (M.initCfg x) t).output.length + 10
  have e := hclean a
  have hhalt : ((histOnlyTM M).runFrom ((histOnlyTM M).initCfg x) (T a)).state = none := by
    rw [e]
  have hsame := runFrom_eq_of_halt (histOnlyTM M) ((histOnlyTM M).initCfg x)
    (le_max_left (T a) B) hhalt
  obtain ⟨-, -, hpos⟩ := histOnlyTM_run M x t ht (T := max (T a) B) (le_max_right _ _)
  have h0 := hpos ⟨0, oneHot_pos (k := k + 1 + 2) ((normTM M).q₀)⟩
  rw [hsame, e] at h0
  exact lt_irrefl _ h0

end Rev

end Sagitta.Arrow.TM.Bennett

namespace Sagitta.Arrow.TM

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Bennett

/-- A machine that runs in time `t` on an input has halted at time `t`. -/
theorem halted_of_runsInTime {k : ℕ} {S : Type} {M : MultiTapeTM k Bool S} {x : List Bool}
    {t : ℕ} (h : M.RunsInTime x t) : (M.runFrom (M.initCfg x) t).Halted :=
  h (MultiTapeNTM.ComputationPath.ofDeterministic M x t) le_rfl

/-- What a machine that computes `y` from `x` in time `t` gives: it has halted at time `t`, with
output `y`, and `y` is no longer than `t`. -/
theorem halted_output_of_computes {k : ℕ} {S : Type} {M : MultiTapeTM k Bool S} {x y : List Bool}
    {t s : ℕ} (h : M.ComputesInTimeAndSpace x y t s) :
    (M.runFrom (M.initCfg x) t).Halted ∧ (M.runFrom (M.initCfg x) t).output = y ∧
      (M.runFrom (M.initCfg x) t).output.length ≤ t := by
  obtain ⟨⟨u, hu, hout⟩, htime, -⟩ := h
  have hhalt : (M.runFrom (M.initCfg x) t).Halted := halted_of_runsInTime htime
  have heq : M.runFrom (M.initCfg x) t = M.runFrom (M.initCfg x) u := by
    rcases le_total u t with hle | hle
    · exact runFrom_eq_of_halt M _ hle hu
    · exact (runFrom_eq_of_halt M _ hle hhalt).symm
  have hy : (M.runFrom (M.initCfg x) t).output = y := by rw [heq, hout]
  refine ⟨hhalt, hy, ?_⟩
  have := length_output_runFrom_le M (M.initCfg x) t
  simpa [MultiTapeNTM.initCfg, Cfg.init] using this

/-- **Bennett's theorem (1973), for the machines of cslib.** For every machine computing `f` in time
`t`, the reversible machine `revTM` computes `f` in time and space linear in `n + t(n)`, and halts
with the work tapes clean: the history erased, the input intact (and copied once), the output on
the output tape. The statement `Bennett` of `Sagitta.Arrow.TM.Instance` is a theorem. -/
theorem bennett_holds : Bennett := by
  intro α β f encIn encOut tB sB hf
  obtain ⟨k, S, hS, M, hM⟩ := hf
  set K := k + 1 + 2 + histCount k S with hK
  have key : ∀ a, 2 * (encIn a).length + 10 * tB (encIn a).length + 21 ≤
        43 * K * ((encIn a).length + tB (encIn a).length + 1) ∧
      K * (2 * (2 * (encIn a).length + 10 * tB (encIn a).length + 21) + 1) ≤
        43 * K * ((encIn a).length + tB (encIn a).length + 1) := by
    intro a
    set n := (encIn a).length
    set t := tB n
    have h1 : 43 * (n + t + 1) ≤ 43 * K * (n + t + 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : 43 * K * (n + t + 1) = K * (43 * (n + t + 1)) := by ring
    refine ⟨by omega, ?_⟩
    rw [h2]
    exact Nat.mul_le_mul_left _ (by omega)
  refine ⟨K, _, inferInstance, revTM M, 43 * K, revTM_isReversible M, fun a => ?_,
    revRole k (histCount k S), fun a => ?_⟩
  · have hMa := hM a
    beta_reduce at hMa
    obtain ⟨hhalt, hy, hlen⟩ := halted_output_of_computes hMa
    set x := encIn a
    have e := revTM_correct_clean M x (tB x.length) hhalt
      (T := 2 * x.length + 10 * tB x.length + 21) (by omega)
    have hH : ((revTM M).runFrom ((revTM M).initCfg x)
        (2 * x.length + 10 * tB x.length + 21)).Halted := by rw [e]
    refine ⟨⟨_, hH, by rw [e, hy]⟩, (runsInTime_of_halted hH).mono (key a).1,
      (runsInSpace_of_halted _ hH).mono (key a).2⟩
  · beta_reduce
    have hMa := hM a
    beta_reduce at hMa
    obtain ⟨hhalt, hy, hlen⟩ := halted_output_of_computes hMa
    have h1 := (key a).1
    set x := encIn a
    rw [revTM_correct_clean M x (tB x.length) hhalt (by omega), hy, revTapes_eq_role]

/-- **The old statement holds for a history simulation that never uncomputes.** The Lecerf–Landauer
machine `histOnlyTM` (compute with a history, emit, stop) is reversible and computes every function
computable in polynomial time, in polynomial time and space: `BennettWeak`, the statement before the
clean tapes were required, does not tell Bennett's construction from Lecerf's. -/
theorem bennett_of_history_only : BennettWeak := by
  intro α β f encIn encOut hf
  obtain ⟨tB, sB, htB, -, k, S, hS, M, hM⟩ := hf
  set T : ℕ → ℕ := fun n => 2 * n + 4 * tB n + 10 with hT
  have hTp : PolynomiallyBounded T :=
    (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
      ((PolynomiallyBounded.const 4).mul htB)).add (PolynomiallyBounded.const 10)
  refine ⟨k + 1 + 2 + histCount k S, _, inferInstance, histOnlyTM M, T,
    fun n => (k + 1 + 2 + histCount k S) * (2 * T n + 1), histOnlyTM_isReversible M, hTp,
    (PolynomiallyBounded.const _).mul
      (((PolynomiallyBounded.const 2).mul hTp).add (PolynomiallyBounded.const 1)), fun a => ?_⟩
  have hMa := hM a
  beta_reduce at hMa
  obtain ⟨hhalt, hy, hlen⟩ := halted_output_of_computes hMa
  set x := encIn a
  obtain ⟨hH, hO, -⟩ := histOnlyTM_run M x (tB x.length) hhalt (T := T x.length)
    (by simp only [hT]; omega)
  rw [hy] at hO
  exact ⟨⟨_, hH, hO⟩, runsInTime_of_halted hH, runsInSpace_of_halted _ hH⟩

/-- **The mutant is not Bennett's theorem**: the machine that proves `BennettWeak` above does not
satisfy the clean-tapes requirement of `Bennett`, for any function, encoding or time bound, as soon
as the machine it simulates halts on one input. -/
theorem history_only_not_clean {α β : Type} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) {k : ℕ} {S : Type} [Finite S] (M : MultiTapeTM k Bool S) (a : α)
    (hM : ∃ t, (M.runFrom (M.initCfg (encIn a)) t).Halted) (T : α → ℕ) :
    IsReversible (histOnlyTM M) ∧ ¬ComputesCleanly (histOnlyTM M) encIn encOut f T :=
  ⟨histOnlyTM_isReversible M, histOnlyTM_not_computesCleanly M encIn encOut f T a hM⟩

/-- **Every `NP` verifier runs on a reversible machine without garbage**, with no hypothesis:
`reversible_verifier` with Bennett's theorem. -/
theorem reversible_verifier_holds {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ NP enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool), IsVerifier enc p V A ∧
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (t s : ℕ → ℕ),
        IsReversible tm ∧ PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
          tm.ComputesFunInTimeAndSpace (encPair enc encBits) encBool V
            (fun a => t ((encPair enc encBits) a).length)
            (fun a => s ((encPair enc encBits) a).length) ∧
          ComputesCleanly tm (encPair enc encBits) encBool V
            (fun a => t ((encPair enc encBits) a).length) :=
  reversible_verifier bennett_holds hA

/-- **HD and the reversible dynamics**, with Bennett now a theorem: from HD alone, the arrow holds
and every `NP` verifier runs on a reversible machine in polynomial time and space, without garbage.
The two parts are independent: the arrow follows from HD, the reversible verifier from Bennett. -/
theorem decision_bennett_holds (h : DecisionHypothesis) :
    Arrow ∧
      ∀ {α : Type} {enc : α ↪ List Bool} {A : Set α}, A ∈ NP enc →
        ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool), IsVerifier enc p V A ∧
          ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State)
            (t s : ℕ → ℕ),
            IsReversible tm ∧ PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
              tm.ComputesFunInTimeAndSpace (encPair enc encBits) encBool V
                (fun a => t ((encPair enc encBits) a).length)
                (fun a => s ((encPair enc encBits) a).length) ∧
              ComputesCleanly tm (encPair enc encBits) encBool V
                (fun a => t ((encPair enc encBits) a).length) :=
  decision_bennett h bennett_holds


/-! ## Checks: the axioms, and one mutant per central theorem -/

/-- info: 'Sagitta.Arrow.TM.Bennett.bennettTM_correct_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.bennettTM_correct_from
/-- info: 'Sagitta.Arrow.TM.Bennett.bennettTM_noReentry'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.bennettTM_noReentry'
/-- info: 'Sagitta.Arrow.TM.Bennett.revTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.revTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.revTM_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.revTM_correct
/-- info: 'Sagitta.Arrow.TM.Bennett.revTM_correct_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.revTM_correct_clean
/-- info: 'Sagitta.Arrow.TM.Bennett.revTapes_eq_role' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.revTapes_eq_role
/-- info: 'Sagitta.Arrow.TM.Bennett.histTM_histPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histTM_histPos
/-- info: 'Sagitta.Arrow.TM.Bennett.histEmit_correct_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histEmit_correct_from
/-- info: 'Sagitta.Arrow.TM.Bennett.histOnlyTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histOnlyTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.histOnlyTM_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histOnlyTM_run
/-- info: 'Sagitta.Arrow.TM.Bennett.histOnlyTM_not_computesCleanly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.histOnlyTM_not_computesCleanly
/-- info: 'Sagitta.Arrow.TM.halted_output_of_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.halted_output_of_computes
/-- info: 'Sagitta.Arrow.TM.bennett_of_history_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.bennett_of_history_only
/-- info: 'Sagitta.Arrow.TM.history_only_not_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.history_only_not_clean
/-- info: 'Sagitta.Arrow.TM.halted_of_runsInTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.halted_of_runsInTime
/-- info: 'Sagitta.Arrow.TM.bennett_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.bennett_holds
/-- info: 'Sagitta.Arrow.TM.reversible_verifier_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.reversible_verifier_holds
/-- info: 'Sagitta.Arrow.TM.decision_bennett_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.decision_bennett_holds

section Mutants

set_option linter.unusedVariables false

open Sagitta.Arrow.TM.Bennett

/-- Mutant of `bennettTM_correct_from`: without blank history tapes. -/
example {k h : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) (hfix : InputFixed tm)
    (hcode : Function.Injective code) (hh : 0 < h) (src : Fin k) {input : List Bool}
    (c₀ : Cfg (k + h) Bool (State ⊕ State) input) (hq₀ : c₀.state = some (.inl tm.q₀)) (t : ℕ)
    (hrun : ∀ i < t, ¬(tm.runFrom (proj c₀) i).Halted)
    (hhalt : (tm.runFrom (proj c₀) t).Halted) (w : List Bool)
    (hsrc : ∀ i : ℕ, i ≤ w.length →
      (tm.runFrom (proj c₀) t).workTapes src ((tm.runFrom (proj c₀) t).workTapePos src + i) =
        w[i]?)
    (hleft : (tm.runFrom (proj c₀) t).workTapes src
      ((tm.runFrom (proj c₀) t).workTapePos src - 1) = none) : True := by
  fail_if_success
    have := bennettTM_correct_from (code := code) hfix hcode hh src c₀ hq₀ (by assumption) t hrun
      hhalt w hsrc hleft le_rfl
  trivial

/-- Mutant of `bennettTM_noReentry'`: without the hypothesis on `tm`. -/
example {k h : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (code : Record k State → Fin h → Bool) (src : Fin k) : True := by
  fail_if_success
    have : NoReentry (bennettTM tm code src) := bennettTM_noReentry' (by assumption) src
  trivial

/-- Mutant of `revTM_isReversible`: the machine `M` itself is not claimed reversible. -/
example {k : ℕ} {S : Type} [Finite S] (M : MultiTapeTM k Bool S) : True := by
  fail_if_success
    have : IsReversible M := revTM_isReversible M
  trivial

/-- Mutant of `revTM_correct`: without the halting of `M`. -/
example {k : ℕ} {S : Type} [Finite S] (M : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ) :
    True := by
  fail_if_success
    have := revTM_correct M x t (by assumption) le_rfl
  trivial

/-- Mutant of `halted_of_runsInTime`: without the time bound. -/
example {k : ℕ} {S : Type} (M : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ) : True := by
  fail_if_success
    have := halted_of_runsInTime (M := M) (x := x) (t := t) (by assumption)
  trivial

/-- Mutant of `bennett_holds`: a function not known to be computable. -/
example {α β : Type} (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (t s : ℕ → ℕ) :
    True := by
  fail_if_success
    have := bennett_holds f encIn encOut t s (by assumption)
  trivial

/-- Mutant of `revTM_correct_clean`: one step before the exact time. -/
example {k : ℕ} {S : Type} [Finite S] (M : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ)
    (hhalt : (M.runFrom (M.initCfg x) t).Halted) : True := by
  fail_if_success
    have := revTM_correct_clean M x t hhalt
      (T := 2 * x.length + 4 * t + 6 * (M.runFrom (M.initCfg x) t).output.length + 20) le_rfl
  trivial

/-- Mutant of `histOnlyTM_not_computesCleanly`: without an input on which `M` halts. -/
example {α β : Type} (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) {k : ℕ}
    {S : Type} [Finite S] (M : MultiTapeTM k Bool S) (T : α → ℕ) (a : α) : True := by
  fail_if_success
    have := histOnlyTM_not_computesCleanly M encIn encOut f T a (by assumption)
  trivial

/-- Mutant of `reversible_verifier_holds`: a set not known to be in `NP`. -/
example {α : Type} (enc : α ↪ List Bool) (A : Set α) : True := by
  fail_if_success
    have := reversible_verifier_holds (enc := enc) (A := A) (by assumption)
  trivial

/-- Mutant of `decision_bennett_holds`: without HD. -/
example : True := by
  fail_if_success
    have := decision_bennett_holds (by assumption)
  trivial

end Mutants

end Sagitta.Arrow.TM
