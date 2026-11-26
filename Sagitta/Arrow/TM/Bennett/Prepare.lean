/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.TM.Bennett.Uncompute
import Sagitta.Arrow.TM.Bennett.Copy
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Bennett, step 2b: preparing the virtual input, reversibly

A reversible machine cannot move its input head off a blank (`IsReversible.staysOnBlank`), so the
reversible inverse of Bennett's construction never moves it (`uncTM` needs `InputFixed`). cslib
already reads the input of a machine from a work tape: `Turing.MultiTapeTM.inputFromTape` reads a
*virtual input tape*, the input written from cell `0`, with a *flag tape* marking the cell `-1`, and
never touches the real input head. What is missing is a **reversible** machine that writes these two
tapes. This file builds it, `prepTM vip flag`:

* `fwd` (initial): while the input head reads a symbol `b`, swap the cell of `vip` with `b` (the
  blank becomes `b`; the swap is a bijection, so nothing is forgotten) and move the input head and
  the head of `vip` right. On the blank at the end of the input, check that the cell of `vip` is
  blank (if not, go to the sink) and move the head of `vip` left.
* `back`: move the head of `vip` left over symbols. On the blank before the word, move it right
  and move the head of `flag` left.
* `mark`: swap the cell of `flag` with `true` and move the head right; halt.
* `sink`: append `true` forever (it is entered appending `false`).

The input head ends on the blank after the input and stays there: a reversible machine cannot bring
it back, and nothing needs it after this.

* `prepTM_isReversible`: `vip ≠ flag` gives a reversible machine (on every running configuration).
* `prepTM_correct`: from blank `vip` and `flag` tapes with their heads at `0`, after
  `2 |input| + 3` steps the machine has halted with the input on `vip` from cell `0`
  (`tapeOfList input`), the mark at cell `-1` of `flag`, both heads back at `0`, the input head on
  the final blank, and nothing else changed.
-/

namespace Sagitta.Arrow.TM.Bennett

open Turing Turing.MultiTapeTM

/-- The states of the preparing machine. -/
inductive PrepState
  | fwd
  | back
  | mark
  | sink
  deriving DecidableEq

/-- An injection of the states into `Fin 4`. -/
def PrepState.toFin : PrepState → Fin 4
  | .fwd => 0
  | .back => 1
  | .mark => 2
  | .sink => 3

instance : Finite PrepState :=
  Finite.of_injective PrepState.toFin (by intro a b; cases a <;> cases b <;> simp [PrepState.toFin])

variable {k : ℕ}

/-! ## The machine -/

/-- The actions of the preparing machine: the input head moves by `mi`, `vip` gets `wv` and moves
by `mv`, `flag` gets `wf` and moves by `mf`, nothing else changes, `o` is appended. -/
def prepAct (vip flag : Fin k) (mi : SignType) (wv : Option (Option Bool)) (mv : SignType)
    (wf : Option (Option Bool)) (mf : SignType) (o : Option Bool) (q : Option PrepState) :
    Action k Bool PrepState :=
  ⟨mi, fun i => if i = vip then (wv, mv) else if i = flag then (wf, mf) else (none, 0), o, q⟩

/-- The transition function of the preparing machine. -/
def prepTr (vip flag : Fin k) :
    PrepState → Option Bool → (Fin k → Option Bool) → Action k Bool PrepState
  | .fwd, some b, w => prepAct vip flag 1 (some (swapCell b (w vip))) 1 none 0 none (some .fwd)
  | .fwd, none, w => match w vip with
    | none => prepAct vip flag 0 none (-1) none 0 none (some .back)
    | some _ => prepAct vip flag 0 none 0 none 0 (some false) (some .sink)
  | .back, _, w => match w vip with
    | some _ => prepAct vip flag 0 none (-1) none 0 none (some .back)
    | none => prepAct vip flag 0 none 1 none (-1) none (some .mark)
  | .mark, _, w => prepAct vip flag 0 none 0 (some (swapCell true (w flag))) 1 none none
  | .sink, _, _ => prepAct vip flag 0 none 0 none 0 (some true) (some .sink)

/-- **The preparing machine**: writes the input on `vip` and the left mark on `flag`. -/
def prepTM (vip flag : Fin k) : MultiTapeTM k Bool PrepState :=
  ofTr .fwd (prepTr vip flag)

theorem prepAct_write_vip {vip flag : Fin k} {mi : SignType} {wv : Option (Option Bool)}
    {mv : SignType} {wf : Option (Option Bool)} {mf : SignType} {o : Option Bool}
    {q : Option PrepState} :
    ((prepAct vip flag mi wv mv wf mf o q).workTapes vip).1 = wv := by
  simp [prepAct]

theorem prepAct_write_flag {vip flag : Fin k} (hvf : vip ≠ flag) {mi : SignType}
    {wv : Option (Option Bool)} {mv : SignType} {wf : Option (Option Bool)} {mf : SignType}
    {o : Option Bool} {q : Option PrepState} :
    ((prepAct vip flag mi wv mv wf mf o q).workTapes flag).1 = wf := by
  simp [prepAct, hvf.symm]

theorem prepAct_write_other {vip flag : Fin k} {mi : SignType} {wv : Option (Option Bool)}
    {mv : SignType} {wf : Option (Option Bool)} {mf : SignType} {o : Option Bool}
    {q : Option PrepState} {i : Fin k} (hv : i ≠ vip) (hf : i ≠ flag) :
    ((prepAct vip flag mi wv mv wf mf o q).workTapes i).1 = none := by
  simp [prepAct, hv, hf]

/-! ## Reversibility -/

/-- Two `mark` steps with the same result: the flag cell tells the symbol swapped. -/
theorem prep_mark_inj {vip flag : Fin k} (hvf : vip ≠ flag) {input : List Bool}
    {c c' : Cfg k Bool PrepState input} (hs : c.state = c'.state)
    (hstep : (prepAct vip flag 0 none 0 (some (swapCell true (c.workTapeSymbols flag))) 1 none
        none).apply c =
      (prepAct vip flag 0 none 0 (some (swapCell true (c'.workTapeSymbols flag))) 1 none
        none).apply c') : c = c' := by
  have hpf := congrFun (congrArg Cfg.workTapePos hstep) flag
  simp only [Action.apply_workTapePos, prepAct, hvf.symm, ↓reduceIte] at hpf
  have hpf' := add_right_cancel hpf
  have hcell := congrFun (congrFun (congrArg Cfg.workTapes hstep) flag) (c.workTapePos flag)
  simp only [Action.apply_workTapes, prepAct, hvf.symm, ↓reduceIte, Function.update_self] at hcell
  rw [hpf', Function.update_self] at hcell
  have hfs := (swapCell true).injective hcell
  rw [← hfs] at hstep
  exact apply_injective _ hs (Or.inl rfl) (fun i => by
    by_cases hi : i = flag
    · exact Or.inr (hi ▸ hfs)
    · left
      by_cases hiv : i = vip
      · simp [prepAct, hiv]
      · simp [prepAct, hiv, hi]) hstep

/-- Two forward steps over symbols with the same result: the input head was at the same place,
so it read the same symbol, and the swap tells the cell of `vip`. -/
theorem prep_fwd_inj {vip flag : Fin k} {input : List Bool} {c c' : Cfg k Bool PrepState input}
    (hs : c.state = c'.state) {b b' : Bool} {X X' : Option Bool}
    (hstep : (prepAct vip flag 1 (some (swapCell b X)) 1 none 0 none (some .fwd)).apply c =
      (prepAct vip flag 1 (some (swapCell b' X')) 1 none 0 none (some .fwd)).apply c')
    (hr : c.inputSymbol = some b) (hr' : c'.inputSymbol = some b')
    (hv : c.workTapeSymbols vip = X) (hv' : c'.workTapeSymbols vip = X') : c = c' := by
  have hip := congrArg Cfg.inputPos hstep
  simp only [Action.apply_inputPos, prepAct] at hip
  have hp : c.inputPos = c'.inputPos := by
    obtain ⟨a1, a2⟩ := interior_of_inputSymbol (c := c) (by rw [hr]; simp)
    obtain ⟨a1', a2'⟩ := interior_of_inputSymbol (c := c') (by rw [hr']; simp)
    exact moveInputPos_injOn _ a1 a2 a1' a2' hip
  have hb : b = b' := by
    have := inputSymbol_congr (d := c') hp
    rw [hr, hr'] at this
    exact Option.some.inj this
  subst hb
  have hpv := congrFun (congrArg Cfg.workTapePos hstep) vip
  simp only [Action.apply_workTapePos, prepAct, ↓reduceIte] at hpv
  have hpv' := add_right_cancel hpv
  have hcell := congrFun (congrFun (congrArg Cfg.workTapes hstep) vip) (c.workTapePos vip)
  simp only [Action.apply_workTapes, prepAct, ↓reduceIte, Function.update_self] at hcell
  rw [hpv', Function.update_self] at hcell
  have hx := (swapCell b).injective hcell
  subst hx
  exact apply_injective _ hs (Or.inr ⟨by rw [hr]; simp, by rw [hr']; simp⟩)
    (fun i => by
      by_cases hi : i = vip
      · exact Or.inr (by rw [hi, hv, hv'])
      · left
        by_cases hif : i = flag
        · subst hif; simp [prepAct, hi]
        · simp [prepAct, hi]) hstep

/-- **The preparing machine is reversible** when `vip` and `flag` are different tapes. -/
theorem prepTM_isReversible {vip flag : Fin k} (hvf : vip ≠ flag) :
    IsReversible (prepTM vip flag) := by
  intro input c c' hc hc' hstep
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hc'
  rw [step_of_state hq, step_of_state hq', prepTM, tr_ofTr, tr_ofTr] at hstep
  -- no writes anywhere: local reversibility
  have hnone : ∀ {mv mf : SignType} {o : Option Bool} {r : Option PrepState},
      c.state = c'.state → (prepAct vip flag 0 none mv none mf o r).apply c =
        (prepAct vip flag 0 none mv none mf o r).apply c' → c = c' := fun hs h =>
    apply_injective _ hs (Or.inl rfl)
      (fun i => Or.inl (by simp only [prepAct]; split_ifs <;> rfl)) h
  -- equal moves give equal head positions, and an unwritten `vip` reads the same
  have hvip : ∀ {mv mf mf' : SignType} {o o' : Option Bool} {r r' : Option PrepState},
      (prepAct vip flag 0 none mv none mf o r).apply c =
        (prepAct vip flag 0 none mv none mf' o' r').apply c' →
        c.workTapeSymbols vip = c'.workTapeSymbols vip := fun h => by
    have hp := congrFun (congrArg Cfg.workTapePos h) vip
    have ht := congrFun (congrArg Cfg.workTapes h) vip
    simp only [Action.apply_workTapePos, Action.apply_workTapes, prepAct_write_vip] at hp ht
    simp only [prepAct, ↓reduceIte] at hp
    simp only [Cfg.workTapeSymbols, ht, add_right_cancel hp]
  have hst := congrArg Cfg.state hstep
  have hout := congrArg Cfg.output hstep
  rcases q with _ | _ | _ | _ <;> rcases q' with _ | _ | _ | _ <;>
    rcases hr : c.inputSymbol with _ | b <;> rcases hr' : c'.inputSymbol with _ | b' <;>
    rcases hv : c.workTapeSymbols vip with _ | v <;>
    rcases hv' : c'.workTapeSymbols vip with _ | v' <;>
    simp only [prepTr, hr, hr', hv, hv'] at hstep hst hout <;>
    simp only [prepAct, Action.apply_state, Action.apply_output, reduceCtorEq,
      Option.some.injEq, Option.toList_some, Option.toList_none] at hst hout <;>
    try first
    | exact hnone (hq.trans hq'.symm) hstep
    | (exfalso; have := hvip hstep; rw [hv, hv'] at this; simp at this; done)
    | (exfalso; have := List.append_inj' hout rfl; simp at this; done)
  all_goals first
    | exact prep_mark_inj hvf (hq.trans hq'.symm) hstep
    | exact prep_fwd_inj (hq.trans hq'.symm) hstep hr hr' hv hv'

/-! ## Correctness -/

section Correct

variable {vip flag : Fin k} {input : List Bool}

/-- The forward phase: after `n ≤ |input|` steps the first `n` symbols are on `vip` and both heads
moved `n` cells. -/
theorem prep_fwd (c : Cfg k Bool PrepState input) (hst : c.state = some .fwd)
    (hip : (c.inputPos : ℕ) = 1) (hv : c.workTapes vip = fun _ => none)
    (hpv : c.workTapePos vip = 0) (n : ℕ) (hn : n ≤ input.length) :
    (prepTM vip flag).runFrom c n =
      { c with
        inputPos := ⟨1 + n, by omega⟩
        workTapes := Function.update c.workTapes vip (tapeOfList (input.take n))
        workTapePos := Function.update c.workTapePos vip n } := by
  induction n with
  | zero =>
    apply Cfg.ext
    · rfl
    · exact Fin.ext (by simp [runFrom, hip])
    · funext i
      by_cases hi : i = vip
      · subst hi; simp [runFrom, hv, tapeOfList_nil]
      · simp [runFrom, hi]
    · funext i
      by_cases hi : i = vip
      · subst hi; simp [runFrom, hpv]
      · simp [runFrom, hi]
    · rfl
  | succ n ih =>
    have hlt : n < input.length := by omega
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega)]
    set d : Cfg k Bool PrepState input := { c with
        inputPos := ⟨1 + n, by omega⟩
        workTapes := Function.update c.workTapes vip (tapeOfList (input.take n))
        workTapePos := Function.update c.workTapePos vip n } with hd
    have hr : d.inputSymbol = some input[n] := inputSymbolInner n rfl hlt
    have hvs : d.workTapeSymbols vip = none := by
      simp [hd, Cfg.workTapeSymbols]
    rw [step_of_state (q := .fwd) hst, prepTM, tr_ofTr]
    simp only [prepTr, hr, hvs]
    apply Cfg.ext
    · simp [prepAct, hst]
    · apply Fin.ext
      simp only [Action.apply_inputPos, prepAct, hd]
      have := val_moveInputPos_eq (⟨1 + n, by omega⟩ : Fin (input.length + 2)) 1
      simp only [SignType.cast] at this
      omega
    · funext i
      simp only [Action.apply_workTapes, prepAct]
      by_cases hi : i = vip
      · subst hi
        simp only [↓reduceIte, hd, Function.update_self, swapCell, Equiv.swap_apply_left]
        rw [List.take_succ_eq_append_getElem hlt, tapeOfList_append_single,
          List.length_take, min_eq_left hlt.le]
      · simp [hi, hd]
    · funext i
      simp only [Action.apply_workTapePos, prepAct]
      by_cases hi : i = vip
      · subst hi; simp [hd]
      · simp [hi, hd]
    · simp [prepAct, hd]

/-- The back phase: over `j` symbols of `vip`, its head moves `j` cells left. -/
theorem prep_back (d : Cfg k Bool PrepState input) (hst : d.state = some .back) (j : ℕ)
    (hsym : ∀ i : ℕ, i < j → d.workTapes vip (d.workTapePos vip - i) ≠ none) :
    (prepTM vip flag).runFrom d j =
      { d with workTapePos := Function.update d.workTapePos vip (d.workTapePos vip - j) } := by
  induction j with
  | zero =>
    apply Cfg.ext <;> simp [runFrom]
  | succ j ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (fun i hi => hsym i (by omega))]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (hsym j (by omega))
    have hs : ({ d with
        workTapePos := Function.update d.workTapePos vip (d.workTapePos vip - j) } :
          Cfg k Bool PrepState input).workTapeSymbols vip = some b := by
      simp [Cfg.workTapeSymbols, hb]
    rw [step_of_state (q := .back) hst, prepTM, tr_ofTr]
    simp only [prepTr, hs]
    apply Cfg.ext
    · simp [prepAct, hst]
    · simp [prepAct]
    · funext i
      simp only [Action.apply_workTapes, prepAct]
      split_ifs <;> rfl
    · funext i
      simp only [Action.apply_workTapePos, prepAct]
      by_cases hi : i = vip
      · subst hi; simp; ring
      · simp [hi]
    · simp [prepAct]

/-- **The preparing machine is correct.** From blank `vip` and `flag` tapes with their heads at
`0` and the input head at its start, after `2 |input| + 3` steps it has halted with the input on
`vip` from cell `0`, the mark `true` at cell `-1` of `flag`, both heads back at `0`, the input head
on the blank after the input, and nothing else changed. -/
theorem prepTM_correct (hvf : vip ≠ flag) (c : Cfg k Bool PrepState input)
    (hst : c.state = some .fwd) (hip : (c.inputPos : ℕ) = 1) (hv : c.workTapes vip = fun _ => none)
    (hf : c.workTapes flag = fun _ => none) (hpv : c.workTapePos vip = 0)
    (hpf : c.workTapePos flag = 0) :
    (prepTM vip flag).runFrom c (2 * input.length + 3) =
      { c with
        state := none
        inputPos := Fin.last _
        workTapes := Function.update (Function.update c.workTapes vip (tapeOfList input)) flag
          (Function.update (fun _ => none) (-1) (some true)) } := by
  obtain ⟨n, hn⟩ : ∃ n, n = input.length := ⟨_, rfl⟩
  have h1 := prep_fwd (flag := flag) c hst hip hv hpv n (by omega)
  rw [List.take_of_length_le (by omega)] at h1
  set d₁ : Cfg k Bool PrepState input := { c with
        inputPos := ⟨1 + n, by omega⟩
        workTapes := Function.update c.workTapes vip (tapeOfList input)
        workTapePos := Function.update c.workTapePos vip n } with hd₁
  -- the turn
  set d₂ : Cfg k Bool PrepState input := { d₁ with
        state := some .back
        workTapePos := Function.update c.workTapePos vip ((n : ℤ) - 1) } with hd₂
  have h2 : (prepTM vip flag).step d₁ = d₂ := by
    have hr : d₁.inputSymbol = none :=
      inputSymbol_eq_none_of_boundary (.inr (by simp [hd₁, hn]; omega))
    have hvs : d₁.workTapeSymbols vip = none := by
      simp [hd₁, Cfg.workTapeSymbols]; omega
    rw [step_of_state (q := .fwd) hst, prepTM, tr_ofTr]
    simp only [prepTr, hr, hvs]
    apply Cfg.ext
    · simp [prepAct, hd₂]
    · simp [prepAct, hd₂]
    · funext i
      simp only [Action.apply_workTapes, prepAct]
      split_ifs <;> rfl
    · funext i
      simp only [Action.apply_workTapePos, prepAct, hd₂, hd₁]
      by_cases hi : i = vip
      · subst hi; simp; ring
      · simp [hi]
    · simp [prepAct, hd₂]
  -- back over the word
  have h3 := prep_back (vip := vip) (flag := flag) d₂ rfl n (fun i hi => by
    simp only [hd₂, hd₁, Function.update_self]
    rw [show (n : ℤ) - 1 - i = ((n - 1 - i : ℕ) : ℤ) by omega, tapeOfList_ofNat]
    simp; omega)
  set d₃ : Cfg k Bool PrepState input := { d₂ with
    workTapePos := Function.update d₂.workTapePos vip (d₂.workTapePos vip - n) } with hd₃
  have hp₃ : d₃.workTapePos vip = -1 := by simp [hd₃, hd₂]
  -- the end of the word
  set d₄ : Cfg k Bool PrepState input := { d₃ with
    state := some .mark
    workTapePos := Function.update (Function.update c.workTapePos vip 0) flag (-1) } with hd₄
  have h4 : (prepTM vip flag).step d₃ = d₄ := by
    have hvs : d₃.workTapeSymbols vip = none := by
      simp [Cfg.workTapeSymbols, hd₃, hd₂, hd₁]; rfl
    rw [step_of_state (q := .back) rfl, prepTM, tr_ofTr]
    simp only [prepTr, hvs]
    apply Cfg.ext
    · simp [prepAct, hd₄]
    · simp [prepAct, hd₄]
    · funext i
      simp only [Action.apply_workTapes, prepAct]
      split_ifs <;> rfl
    · funext i
      simp only [Action.apply_workTapePos, prepAct, hd₄, hd₃, hd₂, hd₁]
      by_cases hi : i = vip
      · subst hi; simp [hvf]
      · by_cases hfl : i = flag
        · subst hfl; simp [hi, hpf]
        · simp [hi, hfl]
    · simp [prepAct, hd₄]
  -- the mark
  have h5 : (prepTM vip flag).step d₄ = { c with
        state := none
        inputPos := Fin.last _
        workTapes := Function.update (Function.update c.workTapes vip (tapeOfList input)) flag
          (Function.update (fun _ => none) (-1) (some true)) } := by
    have hfs : d₄.workTapeSymbols flag = none := by
      simp [Cfg.workTapeSymbols, hd₄, hd₃, hd₂, hd₁, Function.update_of_ne hvf.symm, hf]
    rw [step_of_state (q := .mark) rfl, prepTM, tr_ofTr]
    simp only [prepTr, hfs]
    apply Cfg.ext
    · simp [prepAct]
    · apply Fin.ext; simp [prepAct, hd₄, hd₃, hd₂, hd₁]; omega
    · funext i
      simp only [Action.apply_workTapes, prepAct]
      by_cases hi : i = vip
      · subst hi; simp [hd₄, hd₃, hd₂, hd₁, hvf]
      · by_cases hfl : i = flag
        · subst hfl
          simp [hi, hd₄, hd₃, hd₂, hd₁, hf, swapCell]
        · simp [hi, hfl, hd₄, hd₃, hd₂, hd₁]
    · funext i
      simp only [Action.apply_workTapePos, prepAct, hd₄, hd₃, hd₂, hd₁]
      by_cases hi : i = vip
      · subst hi; simp [hvf, hpv]
      · by_cases hfl : i = flag
        · subst hfl; simp [hi, hpf]
        · simp [hi, hfl]
    · simp [prepAct, hd₄, hd₃, hd₂, hd₁]
  rw [show 2 * input.length + 3 = 1 + (1 + (n + (1 + n))) by omega]
  simp only [runFrom, Function.iterate_add_apply, Function.iterate_one]
  rw [show (prepTM vip flag).step^[n] c = (prepTM vip flag).runFrom c n from rfl, h1, h2,
    show (prepTM vip flag).step^[n] d₂ = (prepTM vip flag).runFrom d₂ n from rfl, h3, h4, h5]

end Correct

/-! ## Checks: the axioms, and one mutant per central theorem -/

/-- info: 'Sagitta.Arrow.TM.Bennett.prepTM_isReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.prepTM_isReversible
/-- info: 'Sagitta.Arrow.TM.Bennett.prepTM_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.Bennett.prepTM_correct

section Mutants

set_option linter.unusedVariables false

/-- Mutant of `prepTM_isReversible`: without `vip ≠ flag`. -/
example (vip flag : Fin k) : True := by
  fail_if_success
    have := prepTM_isReversible (vip := vip) (flag := flag) (by assumption)
  trivial

/-- Mutant of `prepTM_correct`: without a blank flag tape. -/
example (vip flag : Fin k) (hvf : vip ≠ flag) {input : List Bool} (c : Cfg k Bool PrepState input)
    (hst : c.state = some .fwd) (hip : (c.inputPos : ℕ) = 1) (hv : c.workTapes vip = fun _ => none)
    (hpv : c.workTapePos vip = 0) (hpf : c.workTapePos flag = 0) : True := by
  fail_if_success
    have := prepTM_correct hvf c hst hip hv (by assumption) hpv hpf
  trivial

end Mutants

end Sagitta.Arrow.TM.Bennett
