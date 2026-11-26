/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Fidelity.Blind
import Sagitta.Fidelity.Equiv
import Sagitta.Arrow.TM.Bennett.Copy
import Sagitta.Arrow.TM.Bennett.Discharge
import Sagitta.Arrow.TM.Dynamics
import Sagitta.Arrow.Core.Decision

/-!
# The fidelity battery

`Sagitta.Fidelity.Blind` states five results from the literature without looking at this project,
and `Sagitta.Fidelity.Equiv` compares them with ours. This file adds the rest of the battery that
an audit of the statements asks for. Its purpose is not new mathematics but evidence that the
definitions mean what the README says they mean.

1. **Consequences.** What the literature derives from a theorem must come out of our statement of
   it: Bennett gives a reversible, garbage-free verifier for every `NP` problem; Cook–Levin gives
   the classical reductions (every `NP` problem to SAT, SAT to 3-SAT and to ISING, and
   `P = NP ↔ SAT ∈ P`); and SAT is self-reducible (deciding SAT in polynomial time gives its search
   problem in polynomial time).
2. **Mutants.** Each definition is broken on purpose, and some sanity check tells the broken
   version from the real one:
   * `P` without uniformity (a machine per input) contains every set, so it would settle
     `P = NP` by unfolding (`PNonUniform_eq_univ`); at the level of functions it contains a
     function with exponentially long outputs, which no polynomial-time machine computes
     (`not_computableInPolyTime_exp`, `exp_mem_FPNonUniform`);
   * "reversible" only on reachable configurations is satisfied by a machine that erases
     (`eraseTM_isReversibleReachable`), which the real definition rejects
     (`eraseTM_not_isReversible`);
   * the polynomial bound replaced by an exponential one accepts `2 ^ n`
     (`expBounded_two_pow`), which the real one rejects (`not_polynomiallyBounded_two_pow`);
   * Bennett without the clean tapes (`BennettWeak`) is satisfied by the history simulation that
     never uncomputes (`bennett_of_history_only`), which `ComputesCleanly` rejects on a concrete
     machine (`historyOnly_haltsNow_not_clean`).
   No mutant passes every check.
3. **Non-vacuity.** The named hypotheses HD and Law 2.2 cannot be given a Turing-machine model in
   Lean: each implies `P ≠ NP`. What can be proved is proved: HD holds in a model of the core
   axioms (`separatedModel`), HD for Turing machines is exactly `P ≠ NP`
   (`decisionHypothesis_iff_P_ne_NP`), the three hypotheses together say no more than Law 2.2 alone
   (`law22_and_rest_iff`), and Law 2.2 is not empty: its instance at every `ε ≥ 1` is a theorem
   (`law22_of_one_le`, no machine decides 3-SAT in constant time).
4. **Sanity checks.** A machine that erases is not reversible; a machine that copies is; the
   machine that halts at once is; small instances of ISING and SAT are checked by `decide`.
-/

namespace Sagitta.Fidelity

open Turing Turing.MultiTapeTM Cslib Cslib.Complexity Cslib.Logic.PL Filter
open Sagitta.Arrow.TM

/-! ## 1. Consequences that must follow from our statements -/

section Consequences

/-- **Bennett ⟹ every `NP` problem has a reversible verifier without garbage.** The derivation
uses only the statement `Bennett`, not its proof. -/
theorem reversible_verifier_of_bennett (hB : Bennett) {α : Type} {enc : α ↪ List Bool}
    {A : Set α} (hA : A ∈ NP enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool), IsVerifier enc p V A ∧
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (t s : ℕ → ℕ),
        IsReversible tm ∧ PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
          tm.ComputesFunInTimeAndSpace (encPair enc encBits) encBool V
            (fun a => t ((encPair enc encBits) a).length)
            (fun a => s ((encPair enc encBits) a).length) ∧
          ComputesCleanly tm (encPair enc encBits) encBool V
            (fun a => t ((encPair enc encBits) a).length) :=
  reversible_verifier hB hA

/-- **Cook–Levin ⟹ every `NP` problem reduces to SAT.** -/
theorem reduces_to_SAT {α : Type} (enc : α ↪ List Bool) {A : Set α} (hA : A ∈ NP enc) :
    PolyTimeReducible enc encCNF A SAT :=
  CookLevin.SAT_npComplete.2 enc A hA

/-- **SAT reduces to 3-SAT** (the classical clause splitting, through 3-SAT's completeness). -/
theorem SAT_reduces_ThreeSAT : PolyTimeReducible encCNF encCNF SAT ThreeSAT :=
  ThreeSAT_npComplete.2 encCNF SAT SAT.mem_NP

/-- **SAT reduces to ISING** (through MAX-CUT and Partition). -/
theorem SAT_reduces_ISING : PolyTimeReducible encCNF Ising.encIsing SAT Ising.ISING :=
  Ising.ISING_npComplete.2 encCNF SAT SAT.mem_NP

/-- **Cook–Levin ⟹ `P = NP` exactly when SAT is in `P`.** -/
theorem P_eq_NP_iff_SAT_mem_P :
    (∀ {α : Type} (enc : α ↪ List Bool), NP enc ⊆ P enc) ↔ SAT ∈ P encCNF := by
  have h := (arrow_iff.symm.trans arrow_iff_SAT).not
  simpa only [not_not] using h

/-- The search problem of SAT: certificates of SAT's verifier. -/
def SATSearch : CNF ℕ → List Bool → Prop := verifierSearch encCNF Polynomial.X SAT.verifier

/-- **Self-reducibility of SAT**: deciding SAT in polynomial time gives a polynomial-time
procedure that finds a satisfying certificate whenever there is one, and conversely. -/
theorem SAT_selfReducible : SAT ∈ P encCNF ↔ SATSearch ∈ FPSearch encCNF := by
  constructor
  · intro h
    have hall : ∀ {α : Type} (enc : α ↪ List Bool), NP enc ⊆ P enc := P_eq_NP_iff_SAT_mem_P.2 h
    have hFNP : SATSearch ∈ FNP encCNF := verifierSearch_mem_FNP SAT.computableInPolyTime_verifier
    exact (oneBit.2 @hall) encCNF hFNP
  · intro h
    exact SAT.isVerifier.searchDomain_eq ▸ searchDomain_mem_P h

end Consequences

/-! ## 2. Mutants of the definitions

Each mutant is a definition broken on purpose. Next to it is a sanity check that the real
definition passes and the mutant fails. -/

section Mutants

/-! ### (a) `P` without uniformity -/

/-- **Mutant**: `P` without uniformity. For each input separately some polynomial-time function
answers correctly; nothing forces one machine to answer every input. -/
def PNonUniform {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∀ a, ∃ f : α → Bool, ComputableInPolyTime f enc encBool ∧ (a ∈ A ↔ f a = true)}

/-- The real `P` is inside the mutant. -/
theorem P_subset_PNonUniform {α : Type} (enc : α ↪ List Bool) : P enc ⊆ PNonUniform enc :=
  fun _ ⟨f, hf, hA⟩ a => ⟨f, hf, hA a⟩

/-- **The mutant contains every set**: a constant answer is right on its own input. -/
theorem PNonUniform_eq_univ {α : Type} (enc : α ↪ List Bool) : PNonUniform enc = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun A a => ⟨fun _ => decide (a ∈ A), ComputableInPolyTime.const _,
    by simp⟩
  
/-- So the mutant settles `P = NP` by unfolding: with it, the arrow would be refutable. -/
theorem NP_subset_PNonUniform {α : Type} (enc : α ↪ List Bool) : NP enc ⊆ PNonUniform enc := by
  rw [PNonUniform_eq_univ]
  exact Set.subset_univ _

/-- **Mutant**, at the level of functions: polynomial-time computable, input by input. -/
def FPNonUniform {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Set (α → β) :=
  {f | ∀ a, ∃ g : α → β, ComputableInPolyTime g encIn encOut ∧ g a = f a}

theorem FPNonUniform_eq_univ {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) :
    FPNonUniform encIn encOut = Set.univ :=
  Set.eq_univ_of_forall fun f a => ⟨fun _ => f a, ComputableInPolyTime.const _, rfl⟩

/-- A function with exponentially long outputs. -/
def expOut (x : List Bool) : List Bool := List.replicate (2 ^ x.length) true

/-- **Sanity check on the bound**: `2 ^ n` is not polynomially bounded. -/
theorem not_polynomiallyBounded_two_pow : ¬PolynomiallyBounded fun n => 2 ^ n := by
  rintro ⟨d, hd⟩
  have hlo := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (by norm_num : (1 : ℝ) < 2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hlo.bound (by norm_num : (0 : ℝ) < 1 / 2)).and hd)
  obtain ⟨h1, h2⟩ := hN N le_rfl
  have h2' : (2 : ℝ) ^ N ≤ (N : ℝ) ^ d := by exact_mod_cast h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at h1
  have : (0 : ℝ) < 2 ^ N := by positivity
  linarith

/-- **Sanity check that rejects the mutant**: no polynomial-time machine computes `expOut`, since
a machine writes at most one output symbol per step. -/
theorem not_computableInPolyTime_expOut : ¬ComputableInPolyTime expOut encBits encBits := by
  rintro ⟨t, s, ht, -, k, S, -, tm, htm⟩
  refine not_polynomiallyBounded_two_pow ?_
  obtain ⟨d, hd⟩ := ht
  refine ⟨d, hd.mono fun n hn => le_trans ?_ hn⟩
  obtain ⟨-, hout, hlen⟩ := halted_output_of_computes (htm (List.replicate n false))
  rw [hout] at hlen
  simpa [expOut] using hlen

/-- **The mutant accepts `expOut`.** -/
theorem expOut_mem_FPNonUniform : expOut ∈ FPNonUniform encBits encBits := by
  rw [FPNonUniform_eq_univ]
  trivial

/-! ### (b) Reversible only on reachable configurations -/

/-- **Mutant**: injectivity of the step only on running configurations reachable from an initial
configuration. -/
def IsReversibleReachable {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) : Prop :=
  ∀ (input : List Bool) (i j : ℕ), ¬(tm.runFrom (tm.initCfg input) i).Halted →
    ¬(tm.runFrom (tm.initCfg input) j).Halted →
    tm.step (tm.runFrom (tm.initCfg input) i) = tm.step (tm.runFrom (tm.initCfg input) j) →
    tm.runFrom (tm.initCfg input) i = tm.runFrom (tm.initCfg input) j

/-- The real definition implies the mutant. -/
theorem IsReversible.reachable {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State}
    (h : IsReversible tm) : IsReversibleReachable tm :=
  fun input _ _ hi hj hs => h input _ _ hi hj hs

/-- **A machine that erases**: one state; it blanks the cell under the head of its only work tape
and halts. Landauer's canonical irreversible operation. -/
noncomputable def eraseTM : MultiTapeTM 1 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ => ⟨0, fun _ => (some none, 0), none, none⟩

theorem eraseTM_halted_one (input : List Bool) :
    (eraseTM.runFrom (eraseTM.initCfg input) 1).Halted := by
  rw [runFrom_one, step_of_state (q := ()) rfl]
  simp only [eraseTM, tr_ofTr]
  rfl

theorem eraseTM_running {input : List Bool} {i : ℕ}
    (h : ¬(eraseTM.runFrom (eraseTM.initCfg input) i).Halted) : i = 0 := by
  rcases i with _ | i
  · rfl
  · exact absurd (by
      rw [runFrom_eq_of_halt eraseTM _ (Nat.succ_le_succ (Nat.zero_le i)) (eraseTM_halted_one input)]
      exact eraseTM_halted_one input) h

/-- **The mutant accepts the eraser**: from an initial configuration only one configuration is
running, so injectivity on reachable configurations is vacuous. -/
theorem eraseTM_isReversibleReachable : IsReversibleReachable eraseTM :=
  fun _ _ _ hi hj _ => by rw [eraseTM_running hi, eraseTM_running hj]

/-- **Sanity check (Landauer): a machine that erases is not reversible.** Two running
configurations that differ only in the erased cell have the same successor. -/
theorem eraseTM_not_isReversible : ¬IsReversible eraseTM := by
  intro hrev
  let c : Option Bool → Cfg 1 Bool Unit [] := fun b =>
    ⟨some (), 0, fun _ z => if z = 0 then b else none, fun _ => 0, []⟩
  have hstep : eraseTM.step (c none) = eraseTM.step (c (some true)) := by
    rw [step_of_state (q := ()) rfl, step_of_state (q := ()) rfl]
    simp only [eraseTM, tr_ofTr]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp only [Action.apply_workTapes, c]
      by_cases hz : z = 0 <;> simp [hz]
    · rfl
    · rfl
  have := congrFun (congrFun (congrArg Cfg.workTapes
    (hrev [] _ _ (by simp [c, Cfg.Halted]) (by simp [c, Cfg.Halted]) hstep)) 0) 0
  simp [c] at this

/-- **The mutant is strictly weaker**: it does not imply reversibility. -/
theorem isReversibleReachable_not_imp : ¬∀ {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State),
    IsReversibleReachable tm → IsReversible tm :=
  fun h => eraseTM_not_isReversible (h _ eraseTM_isReversibleReachable)

/-! ### (c) The polynomial bound replaced by an exponential one -/

/-- **Mutant** of `PolynomiallyBounded`: eventually below `2 ^ (n ^ d)`. -/
def ExpBounded (f : ℕ → ℕ) : Prop := ∃ d : ℕ, f ≤ᶠ[atTop] fun n => 2 ^ (n ^ d)

/-- The real bound implies the mutant. -/
theorem expBounded_of_polynomiallyBounded {f : ℕ → ℕ} (h : PolynomiallyBounded f) : ExpBounded f :=
  let ⟨d, hd⟩ := h
  ⟨d, hd.mono fun _ hn => hn.trans Nat.lt_two_pow_self.le⟩

/-- **The mutant accepts `2 ^ n`**, which the sanity check `not_polynomiallyBounded_two_pow`
rejects. -/
theorem expBounded_two_pow : ExpBounded fun n => 2 ^ n :=
  ⟨1, Eventually.of_forall fun _ => by simp⟩

/-- **Mutant** of `P` with the exponential bound. -/
def PExp {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (t s : ℕ → ℕ), ExpBounded t ∧ ExpBounded s ∧
    ComputableInTimeAndSpaceOfLength f enc encBool t s ∧ ∀ a, a ∈ A ↔ f a = true}

theorem P_subset_PExp {α : Type} (enc : α ↪ List Bool) : P enc ⊆ PExp enc :=
  fun _ ⟨f, ⟨t, s, ht, hs, h⟩, hA⟩ => ⟨f, t, s, expBounded_of_polynomiallyBounded ht,
    expBounded_of_polynomiallyBounded hs, h, fun a => hA a⟩

/-! ### (d) Bennett without the clean tapes -/

/-- **Mutant**: `BennettWeak`, Bennett without the clean tapes, holds for the history simulation
that never uncomputes (Lecerf–Landauer). -/
theorem bennettWeak_holds_for_history_only : BennettWeak := bennett_of_history_only

/-- **Sanity check that rejects the mutant**: on a concrete machine (the one that halts at once)
the history-only simulation is reversible but leaves garbage, for every time bound, so it does not
meet `ComputesCleanly`, which `Bennett` asks for. -/
theorem historyOnly_haltsNow_not_clean :
    IsReversible (Bennett.histOnlyTM haltsNow) ∧
      ∀ T : List Bool → ℕ, ¬ComputesCleanly (Bennett.histOnlyTM haltsNow) encBits encBits id T :=
  ⟨(history_only_not_clean id encBits encBits haltsNow [] ⟨1, (haltsNow_control _).2.1.1⟩
    fun _ => 0).1,
   fun T => (history_only_not_clean id encBits encBits haltsNow [] ⟨1, (haltsNow_control _).2.1.1⟩
    T).2⟩

end Mutants

/-! ## 3. Non-vacuity of the named hypotheses

`DecisionHypothesis` (HD) and `Law22` are about Turing machines and each implies `P ≠ NP`
(`DecisionHypothesis.arrow`, `Law22.arrow`), so a model of either in Lean would be a proof of
`P ≠ NP`; and Lean cannot prove its own consistency, so "not contradictory" cannot be proved
outright either. What is proved here is the most that can be: HD holds in a model of the core
axioms, the hypotheses do not interact (together they say no more than Law 2.2), and HD says
exactly the arrow, so its consistency is that of `P ≠ NP`. -/

section NonVacuity

/-- **HD has a model**: in `separatedModel`, a model of every axiom of the core, HD holds (and in
`collapsedModel` it fails). -/
theorem decisionHypothesis_has_model : Sagitta.Arrow.separatedModel.DecisionHypothesis ∧
    ¬Sagitta.Arrow.collapsedModel.DecisionHypothesis :=
  ⟨Sagitta.Arrow.decisionHypothesis_independent.2, Sagitta.Arrow.decisionHypothesis_independent.1⟩

/-- **HD for Turing machines is exactly `P ≠ NP`** (for languages over `{0,1}`): it is consistent
exactly when `P ≠ NP` is. -/
theorem decisionHypothesis_iff_P_ne_NP : DecisionHypothesis ↔ P encBits ≠ NP encBits :=
  decisionHypothesis_iff_arrow.trans Equiv.arrow_iff_bits

/-- **The named hypotheses are not contradictory with one another**: assuming all of them is the
same as assuming Law 2.2 alone, so any contradiction among them is already in Law 2.2. -/
theorem law22_and_rest_iff : (Law22 ∧ DecisionHypothesis ∧ Arrow) ↔ Law22 :=
  ⟨fun h => h.1, fun h => ⟨h, decisionHypothesis_of_law22 h, arrow_of_law22 h⟩⟩

/-! ### Law 2.2 is not empty at the top

For `ε ≥ 1` the bound of Law 2.2 is at most `2`, so the instance of Law 2.2 at such an `ε` says that
no machine decides 3-SAT in constant time. That is a real lower bound, and it is proved here: a
machine that runs for `u` steps never reads past the first `u` cells of its input, and a satisfiable
formula and an unsatisfiable one can share an arbitrarily long prefix. So Law 2.2 is not a statement
whose every instance is false (or trivially true): its `ε ≥ 1` part holds, its `0 < ε < 1` part is
the open hypothesis. -/

section Locality

variable {k : ℕ} {S : Type} {R : MultiTapeTM k Bool S}

/-- A configuration on `x`, seen on `x ++ y`. -/
def liftCfg {x : List Bool} (y : List Bool) (c : Cfg k Bool S x) : Cfg k Bool S (x ++ y) :=
  ⟨c.state, Fin.castLE (by simp) c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Away from the right end of `x`, the head reads the same symbol on `x` and on `x ++ y`. -/
theorem inputSymbol_liftCfg {x y : List Bool} (c : Cfg k Bool S x)
    (h : c.inputPos.val ≤ x.length) : (liftCfg y c).inputSymbol = c.inputSymbol := by
  rcases Nat.eq_zero_or_pos c.inputPos.val with h0 | hpos
  · rw [inputSymbol_eq_none_of_boundary (Or.inl h0),
      inputSymbol_eq_none_of_boundary (Or.inl (by simpa [liftCfg] using h0))]
  · obtain ⟨p, hp⟩ : ∃ p, c.inputPos.val = 1 + p := ⟨c.inputPos.val - 1, by omega⟩
    have hpx : p < x.length := by omega
    rw [inputSymbolInner p hp hpx,
      inputSymbolInner (cfg := liftCfg y c) p (by simpa [liftCfg] using hp) (by simp; omega),
      List.getElem_append_left hpx]

/-- Away from the right end of `x`, one step commutes with `liftCfg`. -/
theorem step_liftCfg {x y : List Bool} (c : Cfg k Bool S x) (h : c.inputPos.val ≤ x.length) :
    R.step (liftCfg y c) = liftCfg y (R.step c) := by
  cases hs : c.state with
  | none =>
    rw [step_of_halt hs, step_of_halt (by simp [liftCfg, hs])]
  | some q =>
    have hs' : (liftCfg y c).state = some q := by simp [liftCfg, hs]
    have hsym := inputSymbol_liftCfg (y := y) c h
    have hw : (liftCfg y c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [step_of_state hs', step_of_state hs, hsym, hw]
    generalize R.tr q c.inputSymbol c.workTapeSymbols = act
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      have e1 := val_moveInputPos_eq (liftCfg y c).inputPos act.inputTape
      have e2 := val_moveInputPos_eq c.inputPos act.inputTape
      simp only [Action.apply_inputPos, liftCfg, Fin.val_castLE] at e1 e2 ⊢
      simp only [List.length_append] at e1
      have hmc : (act.inputTape.cast : ℤ) = -1 ∨ (act.inputTape.cast : ℤ) = 0 ∨
          (act.inputTape.cast : ℤ) = 1 := by
        rcases act.inputTape with _ | _ | _ <;> simp [SignType.cast]
      simp only [max_def, min_def] at e1 e2
      split_ifs at e1 e2 <;> omega
    · rfl
    · rfl
    · rfl

/-- **Locality**: for `i ≤ |x|` steps, the run on `x ++ y` is the run on `x`, lifted. -/
theorem runFrom_liftCfg (x y : List Bool) :
    ∀ i, i ≤ x.length →
      R.runFrom (R.initCfg (x ++ y)) i = liftCfg y (R.runFrom (R.initCfg x) i) ∧
        (R.runFrom (R.initCfg x) i).inputPos.val ≤ i + 1
  | 0, _ => ⟨rfl, by
    change (R.initCfg x).inputPos.val ≤ 0 + 1
    simp [MultiTapeNTM.initCfg, Cfg.init]⟩
  | i + 1, hi => by
    obtain ⟨ih, hpos⟩ := runFrom_liftCfg x y i (by omega)
    refine ⟨?_, ?_⟩
    · rw [Equiv.runFrom_succ', ih, step_liftCfg _ (by omega), Equiv.runFrom_succ']
    · rw [Equiv.runFrom_succ']
      cases hs : (R.runFrom (R.initCfg x) i).state with
      | none => rw [step_of_halt hs]; omega
      | some q =>
        rw [step_of_state hs, Action.apply_inputPos]
        have := val_moveInputPos_le (R.runFrom (R.initCfg x) i).inputPos
          (R.tr q (R.runFrom (R.initCfg x) i).inputSymbol
            (R.runFrom (R.initCfg x) i).workTapeSymbols).inputTape
        omega

end Locality

section Law22Top

/-- For `ε ≥ 1`, the bound `⌈2 ^ (n ^ (1 - ε))⌉` is at most `2`. -/
theorem subexpBound_le_two {ε : ℝ} (hε : 1 ≤ ε) (n : ℕ) : subexpBound ε n ≤ 2 := by
  unfold subexpBound
  have hexp : (n : ℝ) ^ (1 - ε) ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using Real.zero_rpow_le_one (1 - ε)
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  have : (2 : ℝ) ^ ((n : ℝ) ^ (1 - ε)) ≤ 2 := by
    calc (2 : ℝ) ^ ((n : ℝ) ^ (1 - ε)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 2 := by norm_num
  exact Nat.ceil_le.2 (by exact_mod_cast this)

/-- `m` copies of the clause `x₀`: satisfiable, width `1`. -/
def manyX (m : ℕ) : CNF ℕ := List.replicate m [(0, true)]

theorem manyX_mem (m : ℕ) : manyX m ∈ ThreeSAT :=
  ⟨fun c hc => by simp [List.eq_of_mem_replicate hc], fun _ => true, by
    simp [manyX, CNF.eval, Clause.eval, Literal.eval]⟩

/-- Adding the clause `¬x₀` makes it unsatisfiable. -/
theorem manyX_append_not_mem (m : ℕ) : manyX (m + 1) ++ [[(0, false)]] ∉ ThreeSAT := by
  rintro ⟨-, σ, hσ⟩
  cases h : σ 0 <;> simp [manyX, CNF.eval, Clause.eval, Literal.eval, h, List.replicate_succ] at hσ

theorem length_encCNF_manyX (m : ℕ) : m ≤ (encCNF (manyX m)).length := by
  have := SAT.length_vars_le (manyX m)
  simpa [CNF.length_vars, manyX] using this

/-- **No machine decides 3-SAT in constant time.** -/
theorem not_decides_ThreeSAT_const (B : ℕ) :
    ¬∃ s : CNF ℕ → ℕ, DecidableInTimeAndSpace ThreeSAT encCNF (fun _ => B) s := by
  rintro ⟨s, k, S, -, R, hR⟩
  set φ := manyX (B + 1)
  set ψ := manyX (B + 1) ++ [[(0, false)]]
  have hψ : encCNF ψ = encCNF φ ++ encCNF [[(0, false)]] := by
    simp [ψ, φ, encCNF, encList, List.flatMap_append]
  obtain ⟨h1, o1, -⟩ := halted_output_of_computes (hR φ)
  obtain ⟨h2, o2, -⟩ := halted_output_of_computes (hR ψ)
  have hlen : B ≤ (encCNF φ).length := (Nat.le_succ B).trans (length_encCNF_manyX _)
  obtain ⟨hl, -⟩ := runFrom_liftCfg (R := R) (encCNF φ) (encCNF [[(0, false)]]) B hlen
  rw [hψ] at o2
  rw [hl] at o2
  have hout : (liftCfg (encCNF [[(0, false)]]) (R.runFrom (R.initCfg (encCNF φ)) B)).output =
      (R.runFrom (R.initCfg (encCNF φ)) B).output := rfl
  rw [hout, o1] at o2
  have i1 : MultiTapeTM.indicator ThreeSAT φ = true := by
    simp [MultiTapeTM.indicator, φ, manyX_mem]
  have i2 : MultiTapeTM.indicator ThreeSAT ψ = false := by
    simp [MultiTapeTM.indicator, ψ, manyX_append_not_mem]
  simp [i1, i2] at o2

/-- **Law 2.2 holds for every `ε ≥ 1`**: its bound is then constant, and 3-SAT is not decided in
constant time. -/
theorem law22_of_one_le (ε : ℝ) (hε : 1 ≤ ε) : ¬InTIME ThreeSAT encCNF (subexpBound ε) := by
  rintro ⟨C, s, h⟩
  refine not_decides_ThreeSAT_const (3 * C) ⟨s, ?_⟩
  obtain ⟨k, S, hS, R, hR⟩ := h
  refine ⟨k, S, hS, R, ComputesFunInTimeAndSpace.mono hR (fun φ => ?_) (fun _ => le_rfl)⟩
  have := subexpBound_le_two hε (encCNF φ).length
  nlinarith

end Law22Top

end NonVacuity

/-! ## 4. Sanity checks of the audit -/

section Sanity

/-- **A machine that copies is reversible** (between two different tapes). -/
example : IsReversible (Bennett.copyTM (k := 2) 0 1) := Bennett.copyTM_isReversible (by decide)

/-- **A machine that copies a tape onto itself is not** (it swaps a symbol for a blank). -/
example : ¬IsReversible (Bennett.copyTM (k := 1) 0 0) := Bennett.copyTM_self_not_isReversible 0

/-- **The machine that halts at once is reversible**: a running configuration is determined by
its successor (only the state changes, and there is one state). -/
theorem haltsNow_isReversible : IsReversible haltsNow := by
  intro input c c' hc hc' h
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  rw [step_of_state hq, step_of_state hq'] at h
  simp only [haltsNow, tr_ofTr] at h
  apply Cfg.ext_zero_tapes
  · rw [hq, hq']
  · simpa using congrArg Cfg.inputPos h
  · simpa using congrArg Cfg.output h

/-- An antiferromagnetic triangle is frustrated: the configuration `+ - -` has energy `-1`. -/
example : Ising.energy [⟨0, 1, -1⟩, ⟨1, 2, -1⟩, ⟨0, 2, -1⟩] (fun v => v == 0) = -1 := by decide

/-- ... and no configuration of the triangle goes below `-1` (not `-3`). -/
example : ∀ s : Fin 8, -1 ≤ Ising.energy [⟨0, 1, -1⟩, ⟨1, 2, -1⟩, ⟨0, 2, -1⟩]
    (fun v => s.val.testBit v) := by decide

/-- ISING has members and non-members. -/
example : (⟨[], 0⟩ : Ising.IsingInstance) ∈ Ising.ISING := ⟨∅, by decide⟩

example : (⟨[], -1⟩ : Ising.IsingInstance) ∉ Ising.ISING := by
  rintro ⟨S, hS⟩
  simp [Ising.energy] at hS

/-- SAT's verifier accepts a satisfying certificate and rejects a falsifying one. -/
example : SAT.verifier ([[(0, true)]], [true]) = true := by decide

example : SAT.verifier ([[(0, true)]], [false]) = false := by decide

/-- `x ∧ ¬x` is not satisfiable; `x` is. -/
example : [[(0, true)], [(0, false)]] ∉ SAT := by
  rintro ⟨σ, hσ⟩
  cases h : σ 0 <;> simp [CNF.eval, Clause.eval, Literal.eval, h] at hσ

example : [[(0, true)]] ∈ SAT := ⟨fun _ => true, by decide⟩

end Sanity

/-! ## Axioms -/

/-- info: 'Sagitta.Fidelity.SAT_selfReducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SAT_selfReducible

/-- info: 'Sagitta.Fidelity.not_computableInPolyTime_expOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_computableInPolyTime_expOut

/-- info: 'Sagitta.Fidelity.eraseTM_not_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eraseTM_not_isReversible

/-- info: 'Sagitta.Fidelity.isReversibleReachable_not_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isReversibleReachable_not_imp

/-- info: 'Sagitta.Fidelity.historyOnly_haltsNow_not_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms historyOnly_haltsNow_not_clean

/-- info: 'Sagitta.Fidelity.law22_and_rest_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms law22_and_rest_iff

/-- info: 'Sagitta.Fidelity.law22_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms law22_of_one_le

/-- info: 'Sagitta.Fidelity.haltsNow_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms haltsNow_isReversible

end Sagitta.Fidelity
