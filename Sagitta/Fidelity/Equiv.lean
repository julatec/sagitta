/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Fidelity.Blind
import Sagitta.Arrow.TM.Bennett.History
import Sagitta.Arrow.TM.Consequences
import Sagitta.Arrow.TM.Decision
import Sagitta.Arrow.TM.Ising
import Sagitta.Arrow.TM.Law22
import Sagitta.Arrow.TM.Bennett.Discharge
import CslibFrontier.Computability.Complexity.Classes.Ladner

/-!
# Our statements against the blind ones

`Sagitta.Fidelity.Blind` renders five statements from the literature without looking at this
project. Here each one is compared with the statement the project proves. Where the two agree the
agreement is a theorem; where they do not, the difference is located, and when the blind statement is
the one at fault it is said and left as it is.

* **(a) Bennett: the blind statement is false** (`not_bennettPoly`, `not_bennettLinear`). It asks the
  reversible machine to halt with *every head back at the origin*, the input head included. In cslib
  the input tape is read-only and a reversible machine cannot move its input head off a blank
  (`IsReversible.staysOnBlank`), so a reversible machine that ends with its input head on the first
  cell never sees where a one-symbol input ends and cannot compute the identity. The project's
  `Bennett` leaves the input head on the blank after the input and allows a copy of the input on a
  work tape: that is Bennett's own final state ("input reconstructed", on a work tape of his
  three-tape machine). So `Bennett` does not imply the blind statement
  (`bennett_not_imp_bennettPoly`), and the blind statement, not ours, is the one to fix.
* **(b) Goldreich, Theorem 2.6: holds** (`goldreichThm2_6`), from cslib's `FNP_subset_FPSearch_iff`
  and the dictionary `PC = FNP` (`PC_eq`), `PF ∩ PC = FPSearch` (`mem_PF_iff`), `P_Gold = P`
  (`PGold_eq`), `NP_Gold = NP` (`NPGold_eq`: certificates of length at most against exactly
  `p(|x|)`). The project's `DecisionHypothesis` is exactly `PC ⊄ PF`
  (`decisionHypothesis_iff_not_PC_subset_PF`).
* **(c) Ladner: holds, and the statements are the same** (`ladner`, `ladner_iff`): `NP`-completeness
  among languages is cslib's `NPComplete encBits` (`npCompleteLang_iff`), and the arrow is
  `P ≠ NP` for languages (`arrow_iff_bits`). Both are the Arora–Barak form (Karp reductions), not
  Ladner's stronger one with Turing reductions.
* **(d) ISING: the same statement** (`isingNPComplete_iff`): same words, same Hamiltonian. Neither
  is Barahona's lattice theorem.
* **(e) Law 2.2 against Weak ETH: no implication proved.** See the section: the `n` differs
  (bits against variables), the domain differs (all formulas against 3CNF inputs without
  repetitions), and the blind size form has a defect at the empty formula. Only the obstructions
  are proved (`numVars_single`, `length_encCNF_single`, `weakETHSize_bound_nil`).
-/

namespace Sagitta.Fidelity.Equiv

open Turing Turing.MultiTapeTM Cslib Cslib.Complexity

/-! ## (a) Bennett -/

section Bennett

variable {k : ℕ} {S : Type} {R : MultiTapeTM k Bool S}

/-- The blind reversibility is the project's. -/
theorem isReversible_iff : Blind.IsReversible R ↔ Sagitta.Arrow.TM.IsReversible R := by
  unfold Blind.IsReversible Sagitta.Arrow.TM.IsReversible
  simp only [Cfg.Halted, Option.isSome_iff_ne_none]

theorem runFrom_succ' {x : List Bool} (c : Cfg k Bool S x) (i : ℕ) :
    R.runFrom c (i + 1) = R.step (R.runFrom c i) :=
  Function.iterate_succ_apply' _ _ _

theorem runFrom_runFrom {x : List Bool} (c : Cfg k Bool S x) (i u : ℕ) :
    R.runFrom (R.runFrom c i) u = R.runFrom c (u + i) :=
  (Function.iterate_add_apply _ _ _ _).symm

/-- On a blank of the input (either end) a reversible machine leaves its input head in place. -/
theorem step_inputPos_of_boundary (hrev : Sagitta.Arrow.TM.IsReversible R) {x : List Bool}
    (c : Cfg k Bool S x) (hb : c.inputPos.val = 0 ∨ c.inputPos.val = x.length + 1) :
    (R.step c).inputPos = c.inputPos := by
  cases hs : c.state with
  | none => rw [step_of_halt hs]
  | some q =>
    rw [step_inputPos_of_state hs, inputSymbol_eq_none_of_boundary hb, hrev.staysOnBlank q,
      moveInputPos_zero]

/-- Once on a blank of the input, a reversible machine keeps its input head there forever. -/
theorem runFrom_inputPos_of_boundary (hrev : Sagitta.Arrow.TM.IsReversible R) {x : List Bool}
    (c : Cfg k Bool S x) (hb : c.inputPos.val = 0 ∨ c.inputPos.val = x.length + 1) :
    ∀ j, (R.runFrom c j).inputPos = c.inputPos
  | 0 => rfl
  | j + 1 => by
    have ih := runFrom_inputPos_of_boundary hrev c hb j
    rw [runFrom_succ', step_inputPos_of_boundary hrev _ (by rw [ih]; exact hb), ih]

/-- A configuration on the input `[false]` seen on the input `[false, false]`: same everything,
the input head on the same cell. -/
def lift (c : Cfg k Bool S [false]) : Cfg k Bool S [false, false] :=
  ⟨c.state, Fin.castLE (by decide) c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- On the first cell, the two inputs read the same symbol, so the step commutes with `lift`. -/
theorem step_lift (c : Cfg k Bool S [false]) (h1 : c.inputPos = 1) :
    R.step (lift c) = lift (R.step c) := by
  cases hs : c.state with
  | none =>
    rw [step_of_halt hs, step_of_halt (by simp [lift, hs])]
  | some q =>
    have hs' : (lift c).state = some q := by simp [lift, hs]
    have hsym : (lift c).inputSymbol = c.inputSymbol := by
      simp [Cfg.inputSymbol, lift, h1]
    have hw : (lift c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [step_of_state hs', step_of_state hs, hsym, hw]
    generalize R.tr q c.inputSymbol c.workTapeSymbols = act
    apply Cfg.ext
    · rfl
    · simp only [Action.apply_inputPos, lift, h1]
      apply Fin.ext
      cases act.inputTape <;> decide
    · rfl
    · rfl
    · rfl

/-- **A reversible machine that ends with its input head where it started never reads the end of a
one-symbol input**, so on `[false, false]` it runs exactly as on `[false]`, and the two outputs
agree. No machine computing the identity can do that: Bennett's clean final configuration, with the
input head back at the origin, is out of reach for a reversible machine of cslib, whose input tape
is read-only and whose input head cannot leave a blank (`IsReversible.staysOnBlank`). -/
theorem not_clean_and_computes (hrev : Blind.IsReversible R)
    (hclean : ∃ u, Blind.CleanHalt R [false] [false] (R.runFrom (R.initCfg [false]) u))
    (hcomp : R.Computes [false, false] [false, false]) : False := by
  rw [isReversible_iff] at hrev
  obtain ⟨u, hu⟩ := hclean
  unfold Blind.CleanHalt at hu
  have hHalt : (R.runFrom (R.initCfg [false]) u).state = none := by rw [hu]
  have hOut : (R.runFrom (R.initCfg [false]) u).output = [false] := by rw [hu]
  have hPos : (R.runFrom (R.initCfg [false]) u).inputPos = 1 := by rw [hu]; rfl
  -- the input head never leaves the first cell
  have inv : ∀ i, (R.runFrom (R.initCfg [false]) i).inputPos = 1 := by
    intro i
    by_contra hne
    have hb : (R.runFrom (R.initCfg [false]) i).inputPos.val = 0 ∨
        (R.runFrom (R.initCfg [false]) i).inputPos.val = [false].length + 1 := by
      have := (R.runFrom (R.initCfg [false]) i).inputPos.isLt
      have h1 : (R.runFrom (R.initCfg [false]) i).inputPos.val ≠ 1 := fun h =>
        hne (Fin.ext h)
      simp only [List.length_singleton] at this ⊢
      omega
    have hstay := runFrom_inputPos_of_boundary hrev _ hb u
    rw [runFrom_runFrom, runFrom_eq_of_halt R _ (Nat.le_add_right u i) hHalt, hPos] at hstay
    exact hne hstay.symm
  -- so the run on `[false, false]` is the lifted run on `[false]`
  have hrun : ∀ i, R.runFrom (R.initCfg [false, false]) i =
      lift (R.runFrom (R.initCfg [false]) i) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [runFrom_succ', ih, step_lift _ (inv i), runFrom_succ']
  obtain ⟨u', hu', hout'⟩ := hcomp
  have hHalt2 : (R.runFrom (R.initCfg [false, false]) u).state = none := by
    rw [hrun]; exact hHalt
  have e1 := runFrom_eq_of_halt R (R.initCfg [false, false]) (Nat.le_add_right u u') hHalt2
  have e2 := runFrom_eq_of_halt R (R.initCfg [false, false]) (Nat.le_add_left u' u) hu'
  have : (R.runFrom (R.initCfg [false, false]) u).output = [false, false] := by
    rw [← e1, e2, hout']
  rw [hrun] at this
  have h2 : (lift (R.runFrom (R.initCfg [false]) u)).output = [false] := hOut
  rw [h2] at this
  simp at this

/-- **`Blind.BennettPoly` is false.** The identity on `List Bool` is computable in polynomial time,
and no reversible machine computes it with the clean halt that the blind statement asks for. -/
theorem not_bennettPoly : ¬Blind.BennettPoly := by
  intro h
  obtain ⟨k, S, _, R, t, s, -, -, hrev, hall⟩ :=
    h encBits encBits id (ComputableInPolyTime.of_eq fun _ => rfl)
  exact not_clean_and_computes hrev (hall [false]).2 (hall [false, false]).1.1

/-- **`Blind.BennettLinear` is false**, for the same reason, starting from the copy machine. -/
theorem not_bennettLinear : ¬Blind.BennettLinear := by
  intro h
  obtain ⟨k, S, hS, M, hM⟩ := computableInTimeAndSpace_id (enc := encBits)
  obtain ⟨k', S', _, R, C, hrev, hall⟩ := h encBits encBits id M _ _ hM
  exact not_clean_and_computes hrev (hall [false]).2 (hall [false, false]).1.1

/-- **The project's `Bennett` does not imply the blind one**: the first is a theorem
(`bennett_holds`), the second is false. Where they differ: the blind `CleanHalt` asks for the input
head back on cell `1` and every work tape blank; the project's `ComputesCleanly` leaves the input head
on the blank after the input (where a reversible machine must leave it once it has read the whole
input) and allows a work tape to hold a copy of the input or a constant mark, the same for every
input (Bennett's "input reconstructed"). The time bounds differ too: the blind `BennettLinear` asks
`O(t)` for the per-input time `t` of the given machine, the project `O(n + t(n))` for a bound `t` on
the length, the `n` paying for copying the read-only input. -/
theorem bennett_not_imp_bennettPoly : ¬(Sagitta.Arrow.TM.Bennett → Blind.BennettPoly) :=
  fun h => not_bennettPoly (h Sagitta.Arrow.TM.bennett_holds)

end Bennett

/-! ## A language version of SAT

Both the Goldreich and the Ladner comparisons need to move between "every encoding" (cslib) and
"languages over `{0,1}`" (the blind statements). The bridge is SAT padded by a single `1`, the
language `padSAT (fun _ => 0)` of cslib's Ladner construction with exponent `0`: it is in `NP` as a
language, and SAT reduces to it. -/

section SATBits

open Ladner Logic.PL

/-- SAT as a language: `pad (encCNF φ) 1` for `φ` satisfiable. -/
def SATBits : Set (List Bool) := padSAT fun _ => 0

/-- Its verifier: unpad, decode, evaluate. -/
noncomputable def satBitsVerifier (x : List Bool × List Bool) : Bool :=
  (padCheck (fun _ => 0) x.1).elim false fun φ => SAT.verifier (φ, x.2)

theorem computableInPolyTime_satBitsVerifier :
    ComputableInPolyTime satBitsVerifier (encPair encBits encBits) encBool := by
  have hH : ComputableInPolyTime (fun _ : (List Bool × List Bool) × ℕ => (0 : ℕ))
      (encPair (encPair encBits encBits) encUnary) encUnary := by fun_prop
  unfold satBitsVerifier
  fun_prop

theorem isVerifier_satBits : IsVerifier encBits Polynomial.X satBitsVerifier SATBits := by
  intro y
  simp only [Polynomial.eval_X, encBits_apply, satBitsVerifier]
  constructor
  · intro hy
    obtain ⟨φ, hφ, hsat⟩ := mem_padSAT_iff.mp hy
    obtain ⟨w, hw, hv⟩ := (SAT.isVerifier φ).mp hsat
    rw [Polynomial.eval_X] at hw
    have hlen := congrArg List.length (padCheck_eq_some_iff.mp hφ)
    rw [length_pad] at hlen
    refine ⟨w ++ List.replicate (y.length - w.length) false,
      by rw [List.length_append, List.length_replicate]; omega, ?_⟩
    rw [hφ, Option.elim_some]
    simpa only [SAT.verifier, assignment_append_replicate] using hv
  · rintro ⟨w, -, hv⟩
    cases hφ : padCheck (fun _ => 0) y with
    | none => simp [hφ] at hv
    | some φ =>
      rw [hφ, Option.elim_some] at hv
      exact mem_padSAT_iff.mpr ⟨φ, hφ, _, hv⟩

/-- SAT as a language is in `NP`. -/
theorem SATBits_mem_NP : SATBits ∈ NP encBits :=
  ⟨Polynomial.X, satBitsVerifier, computableInPolyTime_satBitsVerifier, isVerifier_satBits⟩

/-- SAT reduces to SAT as a language. -/
theorem SAT_reducible_SATBits : PolyTimeReducible encCNF encBits SAT SATBits := by
  refine ⟨fun φ => pad (encCNF φ) 1, by fun_prop [pad], fun φ => ?_⟩
  rw [SATBits, pad_mem_padSAT_iff]
  simp

/-- **`NP ⊆ P` for languages is `NP ⊆ P` for every encoding.** -/
theorem NP_subset_P_bits_iff :
    NP encBits ⊆ P encBits ↔ ∀ {α : Type} (enc : α ↪ List Bool), NP enc ⊆ P enc := by
  refine ⟨fun h α enc => ?_, fun h => h encBits⟩
  have hSAT : SAT ∈ P encCNF := SAT_reducible_SATBits.mem_P (h SATBits_mem_NP)
  exact (P_eq_NP_of_SAT_mem_P hSAT enc).symm.subset

/-- The arrow is `P ≠ NP` for languages over `{0,1}`. -/
theorem arrow_iff_bits : Sagitta.Arrow.TM.Arrow ↔ P encBits ≠ NP encBits := by
  rw [Sagitta.Arrow.TM.arrow_iff, ← NP_subset_P_bits_iff]
  exact ⟨fun h he => h he.symm.subset, fun h hs => h (P_subset_NP.antisymm hs)⟩

end SATBits

/-! ## (b) Goldreich, Theorem 2.6, against `FNP_subset_FPSearch_iff`

Goldreich's `PC` is cslib's `FNP` for languages, and `PF ∩ PC` is cslib's `FPSearch` (Goldreich's
`PF` alone is larger: it does not ask that membership of pairs be decidable). His `P` is cslib's
`P encBits`, and his `NP`, with certificates of length **at most** `p(|x|)` and a verifier that
rejects every certificate of a non-member, is cslib's `NP encBits`, with certificates of length
**exactly** `p(|x|)`. With these, the blind Theorem 2.6 follows from cslib's
`FNP_subset_FPSearch_iff`, and the project's `DecisionHypothesis` is exactly `PC ⊄ PF`. -/

section Goldreich

theorem PC_eq : Blind.PC = FNP encBits := by
  ext R
  constructor
  · rintro ⟨⟨p, hp⟩, A, hA, hAR⟩
    exact ⟨⟨p, fun a w h => by simpa using hp a w h⟩, A, hA, fun a w => (hAR a w).symm⟩
  · rintro ⟨⟨p, hp⟩, V, hV, hRV⟩
    exact ⟨⟨p, fun a w h => by simpa using hp a w h⟩, V, hV, fun a w => (hRV a w).symm⟩

/-- On `PC`, Goldreich's `PF` is cslib's `FPSearch`. -/
theorem mem_PF_iff {R : List Bool → List Bool → Prop} (hR : R ∈ Blind.PC) :
    R ∈ Blind.PF ↔ R ∈ FPSearch encBits := by
  have hFNP : R ∈ FNP encBits := PC_eq ▸ hR
  constructor
  · rintro ⟨-, A, hA, hsolve⟩
    refine ⟨hFNP, A, hA, fun x => ⟨fun w hw => ?_, fun hn hx => ?_⟩⟩
    · by_cases hex : ∃ y, R x y
      · obtain ⟨y, hy, hRy⟩ := (hsolve x).1 hex
        rw [hw] at hy
        cases hy
        exact hRy
      · rw [(hsolve x).2 hex] at hw
        cases hw
    · obtain ⟨y, hy, -⟩ := (hsolve x).1 hx
      rw [hn] at hy
      cases hy
  · rintro ⟨-, f, hf, hsolve⟩
    refine ⟨hR.1, f, hf, fun x => ⟨fun hex => ?_, fun hex => ?_⟩⟩
    · cases hfx : f x with
      | none => exact absurd hex ((hsolve x).2 hfx)
      | some w => exact ⟨w, rfl, (hsolve x).1 w hfx⟩
    · cases hfx : f x with
      | none => rfl
      | some w => exact absurd ⟨w, (hsolve x).1 w hfx⟩ hex

theorem PC_subset_PF_iff : Blind.PC ⊆ Blind.PF ↔ FNP encBits ⊆ FPSearch encBits := by
  constructor
  · intro h R hR
    have hPC : R ∈ Blind.PC := PC_eq ▸ hR
    exact (mem_PF_iff hPC).1 (h hPC)
  · intro h R hR
    exact (mem_PF_iff hR).2 (h (PC_eq ▸ hR))

theorem PGold_eq : Blind.PGold = P encBits := by
  ext S
  constructor
  · rintro ⟨A, hA, hAS⟩
    exact ⟨A, hA, fun x => (hAS x).symm⟩
  · rintro ⟨A, hA, hAS⟩
    exact ⟨A, hA, fun x => (hAS x).symm⟩

/-- Goldreich's `NP` (certificates of length at most `p(|x|)`, sound for every certificate) is
cslib's `NP` for languages (certificates of length exactly `p(|x|)`). -/
theorem NPGold_eq : Blind.NPGold = NP encBits := by
  ext S
  constructor
  · rintro ⟨p, V, hV, hc, hs⟩
    have hmem := mem_NP_of_witness (enc := encBits) (p := p) Decoder.bits (check := V)
      (R := fun x y => V (x, y) = true) hV (fun _ _ => Iff.rfl) (fun a b hb => by
        have ha : a ∈ S := by
          by_contra ha
          rw [hs a ha b] at hb
          cases hb
        obtain ⟨y, hy, hVy⟩ := hc a ha
        exact ⟨y, hVy, by simpa using hy⟩)
    have hS : {x | ∃ y, V (x, y) = true} = S := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        by_contra hx
        rw [hs x hx y] at hy
        cases hy
      · intro hx
        obtain ⟨y, -, hy⟩ := hc x hx
        exact ⟨y, hy⟩
    exact hS ▸ hmem
  · intro hS
    obtain ⟨R, ⟨⟨p, hp⟩, V, hV, hRV⟩, hdom⟩ := mem_NP_iff_exists_FNP.1 hS
    refine ⟨p, V, hV, fun x hx => ?_, fun x hx y => ?_⟩
    · rw [← hdom] at hx
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, by simpa using hp x w hw, (hRV x w).1 hw⟩
    · cases hVy : V (x, y) with
      | false => rfl
      | true => exact absurd (hdom ▸ ⟨y, (hRV x y).2 hVy⟩ : x ∈ S) hx

/-- Search is easy for languages exactly when `P = NP` for languages. -/
theorem FNP_subset_FPSearch_bits_iff : FNP encBits ⊆ FPSearch encBits ↔ P encBits = NP encBits := by
  constructor
  · intro h
    have hNP : NP encBits ⊆ P encBits := fun A hA => by
      obtain ⟨R, hR, hdom⟩ := mem_NP_iff_exists_FNP.1 hA
      exact hdom ▸ searchDomain_mem_P (h hR)
    exact P_subset_NP.antisymm hNP
  · intro h
    exact FNP_subset_FPSearch_iff.2 (fun {_} enc => NP_subset_P_bits_iff.1 h.symm.subset enc)
      encBits

/-- **The blind Goldreich 2.6 holds**, from cslib's `FNP_subset_FPSearch_iff`. -/
theorem goldreichThm2_6 : Blind.GoldreichThm2_6 := by
  unfold Blind.GoldreichThm2_6
  rw [PC_subset_PF_iff, PGold_eq, NPGold_eq]
  exact FNP_subset_FPSearch_bits_iff

/-- **The project's decision hypothesis is Goldreich's `PC ⊄ PF`.** -/
theorem decisionHypothesis_iff_not_PC_subset_PF :
    Sagitta.Arrow.TM.DecisionHypothesis ↔ ¬Blind.PC ⊆ Blind.PF := by
  rw [Sagitta.Arrow.TM.decisionHypothesis_iff_arrow, arrow_iff_bits, PC_subset_PF_iff,
    FNP_subset_FPSearch_bits_iff]

end Goldreich

/-! ## (c) Ladner

The blind statement asks for a language that is not `NP`-complete **among languages** (every
language in `NP` Karp-reduces to it); cslib's `NPComplete encBits` asks every problem in `NP`, with
any encoding, to reduce to it. Through SAT as a language the two notions coincide, the hypotheses
coincide (`arrow_iff_bits`), and the project's `exists_intermediate` gives the blind statement. -/

section Ladner

theorem npCompleteLang_iff (L : Set (List Bool)) :
    Blind.NPCompleteLang L ↔ NPComplete encBits L := by
  constructor
  · rintro ⟨hL, hard⟩
    refine ⟨hL, fun {α} enc A hA => ?_⟩
    exact ((CookLevin.SAT_npComplete.2 enc A hA).trans SAT_reducible_SATBits).trans
      (hard SATBits SATBits_mem_NP)
  · rintro ⟨hL, hard⟩
    exact ⟨hL, fun A hA => hard encBits A hA⟩

/-- **The blind Ladner statement follows from the project's `exists_intermediate`.** -/
theorem ladner : Blind.Ladner := by
  intro hne
  obtain ⟨L, hNP, hP, hC⟩ := Sagitta.Arrow.TM.exists_intermediate (arrow_iff_bits.2 hne)
  exact ⟨L, hNP, hP, fun h => hC ((npCompleteLang_iff L).1 h)⟩

/-- The two statements have the same hypothesis and the same conclusion. -/
theorem ladner_iff : Blind.Ladner ↔
    (Sagitta.Arrow.TM.Arrow →
      ∃ L : Set (List Bool), L ∈ NP encBits ∧ L ∉ P encBits ∧ ¬NPComplete encBits L) := by
  unfold Blind.Ladner
  rw [arrow_iff_bits]
  simp only [npCompleteLang_iff]

end Ladner

/-! ## (d) ISING

The blind instance type is `List (ℕ × ℕ × ℤ) × ℤ` with spins `σ : ℕ → Bool`; the project's is the
structure `IsingInstance` with configurations given by a `Finset ℕ` of sites at `+1`. The two
encodings are the same words (the structure encoding is the framed tuple of its fields), the
Hamiltonians are the same, and a configuration matters only on the endpoints, so the two problems
are the same problem and `NP`-completeness transfers in both directions. Neither is Barahona's
theorem (planar with a field, or the two-layer cubic lattice with `J ∈ {-1, 0, 1}`): both are
`NP`-completeness on arbitrary graphs with couplings in binary. -/

section Ising

/-- `NP`-completeness moves along a bijection of instances that preserves the encoded words. -/
theorem npComplete_of_equiv {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (e : α ≃ β) (henc : ∀ a, encB (e a) = encA a)
    (hmem : ∀ a, a ∈ A ↔ e a ∈ B) (h : NPComplete encA A) : NPComplete encB B := by
  have hred : PolyTimeReducible encA encB A B := ⟨e, ComputableInPolyTime.of_eq henc, hmem⟩
  refine ⟨?_, h.2.trans hred⟩
  have henc' : ∀ b, encB b = encA (e.symm b) := fun b => by
    rw [← henc, Equiv.apply_symm_apply]
  have hmem' : ∀ b, b ∈ B ↔ e.symm b ∈ A := fun b => by
    rw [hmem, Equiv.apply_symm_apply]
  obtain ⟨p, V, ⟨t, s, ht, hs, k, St, hfin, tm, htm⟩, hver⟩ := h.1
  refine ⟨p, fun z => V (e.symm z.1, z.2), ⟨t, s, ht, hs, k, St, hfin, tm, fun z => ?_⟩, ?_⟩
  · have hz : encPair encB encBits z = encPair encA encBits (e.symm z.1, z.2) := by
      simp [henc']
    have h' := htm (e.symm z.1, z.2)
    simp only [] at h' ⊢
    rw [hz]
    exact h'
  · intro b
    rw [hmem', hver (e.symm b), henc']

/-- The project's instances as blind instances. -/
def toBlind : Arrow.TM.Ising.IsingInstance ≃ Blind.IsingInstance where
  toFun x := (x.couplings.map fun c => (c.u, c.v, c.J), x.t)
  invFun y := ⟨y.1.map fun e => ⟨e.1, e.2.1, e.2.2⟩, y.2⟩
  left_inv x := by
    cases x
    simp [Function.comp_def]
  right_inv y := by
    simp [Function.comp_def]

theorem encList_map {γ δ : Type} {e₁ : γ ↪ List Bool} {e₂ : δ ↪ List Bool} (g : γ → δ)
    (hg : ∀ c, e₂ (g c) = e₁ c) (l : List γ) : encList e₂ (l.map g) = encList e₁ l := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [hg, ih]

theorem encIsing_toBlind (x : Arrow.TM.Ising.IsingInstance) :
    Blind.encIsing (toBlind x) = Arrow.TM.Ising.encIsing x := by
  rw [Arrow.TM.Ising.encIsing_apply]
  simp only [Blind.encIsing, toBlind, Equiv.coe_fn_mk, encPair_apply]
  congr 2
  exact encList_map _ (fun c => by rw [Arrow.TM.Ising.encCoupling_apply]) _

theorem isingEnergy_toBlind (x : Arrow.TM.Ising.IsingInstance) (σ : ℕ → Bool) :
    Blind.isingEnergy (toBlind x).1 σ = Arrow.TM.Ising.energy x.couplings σ := by
  simp [Blind.isingEnergy, Arrow.TM.Ising.energy, toBlind, Blind.spin, Arrow.TM.Ising.spin,
    Function.comp_def]

theorem mem_ISING_iff (x : Arrow.TM.Ising.IsingInstance) :
    x ∈ Arrow.TM.Ising.ISING ↔ toBlind x ∈ Blind.IsingLE := by
  classical
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨fun v => decide (v ∈ S), by rw [isingEnergy_toBlind]; exact hS⟩
  · rintro ⟨σ, hσ⟩
    rw [isingEnergy_toBlind] at hσ
    refine ⟨(Arrow.TM.Ising.endpoints x.couplings).toFinset.filter fun v => σ v = true, ?_⟩
    rw [Arrow.TM.Ising.energy_congr (side' := σ) fun v hv => by simp [hv]]
    exact hσ

/-- **The project's `ISING_npComplete` gives the blind statement.** -/
theorem isingNPComplete : Blind.IsingNPComplete :=
  npComplete_of_equiv toBlind encIsing_toBlind mem_ISING_iff Arrow.TM.Ising.ISING_npComplete

/-- **And conversely**: the two statements are the same. -/
theorem isingNPComplete_iff :
    Blind.IsingNPComplete ↔ NPComplete Arrow.TM.Ising.encIsing Arrow.TM.Ising.ISING := by
  refine ⟨fun h => npComplete_of_equiv toBlind.symm (fun y => ?_) (fun y => ?_) h,
    npComplete_of_equiv toBlind encIsing_toBlind mem_ISING_iff⟩
  · rw [← encIsing_toBlind, Equiv.apply_symm_apply]
  · rw [mem_ISING_iff, Equiv.apply_symm_apply]

end Ising

/-! ## (e) Law 2.2 against Weak ETH

**Not proved, in either direction, and not provable here without new machines.** The project's
`Law22` and the blind `WeakETH` and `WeakETHSize` differ in three places:

1. **What `n` is.** `Law22` measures `n = (encCNF φ).length`, the bit length of the formula.
   `WeakETH` measures the number of variables, `numVars φ` (one more than the largest index), and
   `WeakETHSize` measures `numVars φ + φ.length`. The number of variables is **not** bounded by any
   function of the bit length that would carry `2 ^ (n ^ (1 - ε))` across: one clause with the
   variable `2 ^ j` has `2 ^ j + 1` variables and `8 j + 19` bits (`numVars_single`,
   `length_encCNF_single`), so an algorithm in time `2 ^ (numVars ^ (1 - ε))` may take
   doubly-exponential time in the bit length, and a counterexample to `WeakETH` says nothing about
   `Law22`. In the other direction, on inputs without repeated clauses the bit length is polynomial
   in `numVars` (up to `n³` clauses), not `n^{1+o(1)}`, so a counterexample to `Law22` says nothing
   about `WeakETH` either. The bridge in arXiv:2611.02650 is Theorem 2.4 (SH ⟺ Weak ETH), through
   quantitative sparsification, which is not formalized here. Against `WeakETHSize` the bit length is
   `O((n + m) log n)` on 3CNF inputs, which would give `WeakETHSize ⟹ Law22`, except for the second
   and third points.
2. **The domain.** The blind hypotheses only ask the algorithm to be right on 3CNF inputs without
   repeated literals or clauses (`Is3CNFInput`, footnote 2 of the preprint); `Law22` asks it to
   decide `ThreeSAT` on every formula, including ones with repeated clauses and ones of larger width.
   Turning an algorithm of one kind into one of the other needs a polynomial-time preprocessing
   machine (remove duplicates, rename the variables to `0, …, n - 1`): it exists, but it is not built
   in this project.
3. **A defect of the blind size form at the empty formula.** `WeakETHSize` writes the bound as
   `2 ^ (C · (n + m) ^ (1 - ε))`, with the `O` inside the exponent, as the preprint does. On the empty
   formula (`n + m = 0`) this is `2 ^ 0 = 1` for every `C` (when `ε ≠ 1`): the blind statement asks a
   counterexample to answer the empty formula within **one** step (`weakETHSize_bound_nil`). The
   preprint's `2^{O(·)}` is asymptotic and does not mean that. It is reported here and **not
   corrected**: it makes `WeakETHSize` (slightly) weaker as a hypothesis than the preprint's, and it
   is one more obstacle to deriving `Law22` from it without changing machines.

So `Law22` is the preprint's size form of SH for 3SAT (Lemma 2.1, `k = 3`), with the size counted in
bits and the inputs unrestricted; its equivalence with Weak ETH stays an external theorem. -/

section Law22

open Logic.PL

/-- A one-clause formula with the variable `2 ^ j` is a 3CNF input. -/
theorem is3CNFInput_single (j : ℕ) : Blind.Is3CNFInput [[(2 ^ j, true)]] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp

/-- It has `2 ^ j + 1` variables in the sense of Weak ETH. -/
theorem numVars_single (j : ℕ) : Blind.numVars [[(2 ^ j, true)]] = 2 ^ j + 1 := by
  simp [Blind.numVars, CNF.vars]

/-- And `8 j + 19` bits in the sense of `Law22`. -/
theorem length_encCNF_single (j : ℕ) : (encCNF [[(2 ^ j, true)]]).length = 8 * j + 19 := by
  simp [encCNF, length_frame, Nat.size_eq_bits_len, Nat.size_pow]
  ring

/-- The bound of the blind size form on the empty formula is `1`, whatever the constant. -/
theorem weakETHSize_bound_nil (C ε : ℝ) (hε : ε ≠ 1) :
    (2 : ℝ) ^ (C * ((Blind.numVars [] + ([] : CNF ℕ).length : ℕ) : ℝ) ^ (1 - ε)) = 1 := by
  have h : (1 - ε) ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  simp [Blind.numVars, CNF.vars, Real.zero_rpow h]

end Law22

/-! ## Axioms -/

/-- info: 'Sagitta.Fidelity.Equiv.not_bennettPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_bennettPoly

/-- info: 'Sagitta.Fidelity.Equiv.not_bennettLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_bennettLinear

/-- info: 'Sagitta.Fidelity.Equiv.bennett_not_imp_bennettPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bennett_not_imp_bennettPoly

/-- info: 'Sagitta.Fidelity.Equiv.goldreichThm2_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms goldreichThm2_6

/--
info: 'Sagitta.Fidelity.Equiv.decisionHypothesis_iff_not_PC_subset_PF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms decisionHypothesis_iff_not_PC_subset_PF

/-- info: 'Sagitta.Fidelity.Equiv.ladner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladner

/-- info: 'Sagitta.Fidelity.Equiv.ladner_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladner_iff

/-- info: 'Sagitta.Fidelity.Equiv.isingNPComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isingNPComplete

/-- info: 'Sagitta.Fidelity.Equiv.isingNPComplete_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isingNPComplete_iff

/-- info: 'Sagitta.Fidelity.Equiv.length_encCNF_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms length_encCNF_single

/-- info: 'Sagitta.Fidelity.Equiv.weakETHSize_bound_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weakETHSize_bound_nil

end Sagitta.Fidelity.Equiv
