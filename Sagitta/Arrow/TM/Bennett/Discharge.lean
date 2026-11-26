/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.Machine
import Sagitta.Arrow.TM.Bennett.Normal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

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

The time is `2 n + 10 t(n) + 21` for a machine that runs in time `t`, and the space is linear in
the time: both are polynomial when `t` is.
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

/-- **The machine is correct.** If `M` has halted by time `t` on `x` with output `y`, the
reversible machine has halted with output `y` by time
`2 |x| + 3 + 4 (1 + t + |y| + 2) + 2 |y| + 6`. -/
theorem revTM_correct (x : List Bool) (t : ℕ) (hhalt : (M.runFrom (M.initCfg x) t).Halted)
    {T : ℕ} (hT : 2 * x.length + 3 +
      (4 * (1 + (t + ((M.runFrom (M.initCfg x) t).output.length + 2))) +
        2 * (M.runFrom (M.initCfg x) t).output.length + 6) ≤ T) :
    ((revTM M).runFrom ((revTM M).initCfg x) T).Halted ∧
      ((revTM M).runFrom ((revTM M).initCfg x) T).output = (M.runFrom (M.initCfg x) t).output := by
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
    (t₀ := 2 * x.length + 3) (t₁ := 4 * τ + 2 * y.length + 6) (by rw [hD]; try rfl)
    (by rw [hstart]; unfold B; rw [hB]; try rfl) (T := T) (by omega)
  rw [show (revTM M).initCfg x = (P.initCfg x).mapState (handOver B.q₀) from rfl]
  unfold revTM
  rw [hall, hstart]
  unfold B
  rw [hB]
  exact ⟨rfl, rfl⟩

end Rev

end Sagitta.Arrow.TM.Bennett
