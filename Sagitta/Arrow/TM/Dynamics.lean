/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.Dynamics
import Sagitta.Arrow.TM.Decision
import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
import Cslib.Computability.Machines.Turing.MultiTape.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# The first localization for Turing machines: the space of cslib and the cube

The symmetries of `Core/Dynamics.lean` are stated for an abstract homogeneous `Automaton` with
`|σ| ≤ 2^S` states. This file is the bridge with the **space** of the multi-tape Turing machines of
cslib (`Turing.MultiTapeTM`, with `RunsInSpace`: the cells of the work tapes visited, summed over the
tapes), so that the time-translation half of the first localization holds for real machines.

## What is already in cslib (and is not repeated)

The counting: a storage (state and work tapes) whose non-blank cells and heads fit in windows takes
at most `storageBound Γ Q k s = (|Q| + 1) · (2s + 1)^k · (|Γ| + 1)^(2s + k)` values
(`MultiTapeTM.card_boundedStorage_le`), and that is `≤ base · 2^(exp · s)`
(`MultiTapeTM.storageBound_le_base_mul_pow`).

## The bridge

1. **The window** (`ofBounded`, `ofBounded_toBounded`): the storage restricted to the uniform window
   `[-S, S]` on every tape (`BoundedStorage`, a finite type) can be extended back, exactly on the
   storages that fit. A machine with `RunsInSpace input S` fits in that window at every instant
   (`fitsIn_window`).
2. **The machine is an `Automaton`** (`toAutomaton`): states `Fin (n + 2) × BoundedStorage` (input
   head and storage in the window); the **query is the position of the input head** and the
   **answer is the symbol of the input there** (`symbolAt`): the input plays the verifier. The run is
   the machine's (`run_toAutomaton`, `run_toAutomaton_none`).
3. **The size, with the constant in view** (`card_states_bits`): `|σ| ≤ 2^spaceBits`, with
   `spaceBits = ⌈log₂(n + 2)⌉ + ⌈log₂ base⌉ + exp · k · S`.

## What then holds for cslib's machines

* **The machine is homogeneous in time** (`step_toAutomaton`), so it does not know the time
  (`does_not_know_the_time_tm`): if a core (`Cfg.core`) repeats before halting, everything repeats.
* **The cube law** (`cube_law_tm`), with the input as an informative verifier.
* **Halt or cycle** (`halt_or_cycle_tm`), and **space `S` gives time `2^O(S)`** (`halts_soon_tm`).
* **The CHT tower, piece 1** (`cht_pspace`): a machine with polynomial space that halts, halts
  within `2^b(n)` steps for a polynomial `b`: the `PSPACE` bound. That it is not a polynomial bound
  is the counter of `Core/Dynamics.lean` (`Dynamics.cht_exponential_not_polynomial`).

## The first localization, complete, for Turing machines

`localization_one_tm`: the core statement (`Dynamics.localization_one`) for `tmModel`, the bridge
facts for every cslib machine, and the decision hypothesis for Turing machines, equivalent to the
arrow. Neither symmetry of time of the dynamics decides the arrow; HD, which is about the bit, does.

## Not proved here

* **The output tape.** The core of a configuration does not include the output tape (the machine
  never reads it). The output of the automaton is a reading of the state and work tapes when the
  machine halts.
* **Windows per tape.** The uniform window `[-S, S]` on each of the `k` tapes makes the exponent
  `exp · k · S` instead of `exp · S`. For `O(S)` it does not matter.
* Nothing about `P` versus `NP`: the bridge carries the symmetries, which do not decide it.
-/

namespace Sagitta.Arrow.TM

open Turing Turing.MultiTapeTM
open Sagitta.Arrow.Dynamics

variable {k : ℕ} {Symbol State : Type}

/-! ## 1. The window -/

/-- The uniform window: `S` cells on each side of the origin, on each of the `k` tapes. -/
abbrev uniformWindow (k S : ℕ) : Fin k → ℕ := fun _ => S

/-- **Back from the window to the whole tape**: blank outside the window. -/
def ofBounded {w : Fin k → ℕ} (b : BoundedStorage Symbol State w) : Storage Symbol State k :=
  ⟨b.1, fun j z => if h : z ∈ window (w j) then b.2.1 j ⟨z, h⟩ else none, fun j => (b.2.2 j : ℤ)⟩

/-- **The way back is exact on what fits.** -/
theorem ofBounded_toBounded {w : Fin k → ℕ} {x : Storage Symbol State k} (h : x.FitsIn w) :
    ofBounded (x.toBounded w) = x := by
  apply Storage.ext
  · rfl
  · funext j z
    simp only [ofBounded, Storage.toBounded]
    split_ifs with hz
    · rfl
    · by_contra hne
      exact hz (mem_window.mpr (h.cell_le j z fun e => hne e.symm))
  · funext j
    simp only [ofBounded, Storage.toBounded]
    rw [dite_eq_left_of_eq_true (eq_true (mem_window.mpr (h.pos_le j)))]

/-- So restricting to the window is injective on what fits. -/
theorem toBounded_inj {w : Fin k → ℕ} {x y : Storage Symbol State k} (hx : x.FitsIn w)
    (hy : y.FitsIn w) (h : x.toBounded w = y.toBounded w) : x = y := by
  rw [← ofBounded_toBounded hx, ← ofBounded_toBounded hy, h]

/-! ## 2. The step on the core -/

section CoreStep

variable (tm : MultiTapeTM k Symbol State)

/-- **The next core**: from the input head, the storage and the symbol read. It is `Action.apply`
without the output tape. -/
noncomputable def coreStep {n : ℕ} (x : Fin (n + 2) × Storage Symbol State k) (r : Option Symbol) :
    Fin (n + 2) × Storage Symbol State k :=
  match x.2.state with
  | none => x
  | some q =>
    (moveInputPos x.1 (tm.tr q r fun i => x.2.workTapes i (x.2.workTapePos i)).inputTape,
      ⟨(tm.tr q r fun i => x.2.workTapes i (x.2.workTapePos i)).state,
        fun i => match ((tm.tr q r fun i => x.2.workTapes i (x.2.workTapePos i)).workTapes i).1 with
          | none => x.2.workTapes i
          | some s => Function.update (x.2.workTapes i) (x.2.workTapePos i) s,
        fun i => x.2.workTapePos i +
          ((tm.tr q r fun i => x.2.workTapes i (x.2.workTapePos i)).workTapes i).2⟩)

/-- The symbol of the input `w` under the input head at `i` (shifted by one: `0` and `|w| + 1` are
blank). -/
def symbolAt (w : List Symbol) (i : ℕ) : Option Symbol := if i = 0 then none else w[i - 1]?

variable {tm}

theorem inputSymbol_eq {input : List Symbol} (c : Cfg k Symbol State input) :
    c.inputSymbol = symbolAt input c.inputPos.val := by
  unfold Cfg.inputSymbol symbolAt
  have hlt := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have e : c.inputPos = 0 := Fin.ext h0
    simp [e]
  · have e : c.inputPos ≠ 0 := fun e => h0 (by simp [e])
    simp only [e, h0, dite_false, ite_false]
    by_cases h1 : c.inputPos.val = input.length + 1
    · simp only [h1, dite_true]
      exact (List.getElem?_eq_none (by omega)).symm
    · simp only [h1, dite_false]
      exact (List.getElem?_eq_getElem (by omega)).symm

/-- **The step of the machine, seen on the core**, depends only on the core and the symbol read. -/
theorem core_step {input : List Symbol} (c : Cfg k Symbol State input) :
    (tm.step c).core = coreStep tm c.core c.inputSymbol := by
  rcases c with ⟨q, i, w, p, o⟩
  cases q with
  | none => rw [step_of_halt rfl]; rfl
  | some q => rw [step_of_state rfl]; rfl

end CoreStep

/-! ## 3. The machine as an automaton -/

/-- The states of the automaton: the input head and the storage in the window. A finite type. -/
abbrev States (Symbol State : Type) (k n S : ℕ) :=
  Fin (n + 2) × BoundedStorage Symbol State (uniformWindow k S)

/-- The storage at the start: the initial state, blank tapes, heads at `0`. -/
def initialStorage (q₀ : State) : Storage Symbol State k := ⟨some q₀, fun _ _ => none, fun _ => 0⟩

variable (tm : MultiTapeTM k Symbol State)

/-- **The cslib machine as a homogeneous `Automaton`.** It asks for the position of its input head
and hears the symbol of the input there; it takes one step of the machine on the storage in the
window; when the state is the halting one, it returns the `reading` of the state. -/
noncomputable def toAutomaton {Y : Type} (n S : ℕ) (reading : States Symbol State k n S → Y) :
    Automaton (States Symbol State k n S) ℕ (Option Symbol) Y where
  start := (1, (initialStorage tm.q₀).toBounded (uniformWindow k S))
  query x := x.1.val
  δ x r := ((coreStep tm (x.1, ofBounded x.2) r).1,
    (coreStep tm (x.1, ofBounded x.2) r).2.toBounded (uniformWindow k S))
  output x := if x.2.1.isNone then some (reading x) else none

/-- The configuration seen in the window, with the length of the input fixed to `n`. -/
def inWindow {input : List Symbol} {n : ℕ} (h : input.length = n) (S : ℕ)
    (c : Cfg k Symbol State input) : States Symbol State k n S :=
  (Fin.cast (by rw [h]) c.inputPos, c.storage.toBounded (uniformWindow k S))

variable {tm}

/-- **With space `S`, the machine fits in the window at every instant.** -/
theorem fitsIn_window {input : List Symbol} {S : ℕ} (hs : tm.RunsInSpace input S) (t : ℕ) :
    (tm.runFrom (tm.initCfg input) t).storage.FitsIn (uniformWindow k S) := by
  let p := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  have hp := p.storage_fitsIn
  refine Storage.FitsIn_mono (fun j => ?_) hp
  calc p.spaceUsedByTape j ≤ ∑ i, p.spaceUsedByTape i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ S := hs p

theorem start_toAutomaton {Y : Type} {input : List Symbol} {n : ℕ} (h : input.length = n) (S : ℕ)
    (reading : States Symbol State k n S → Y) :
    (toAutomaton tm n S reading).start = inWindow h S (tm.initCfg input) := by
  subst h
  rfl

/-- **One step of the automaton is one step of the machine**, while the storage fits the window. -/
theorem δ_toAutomaton {Y : Type} {input : List Symbol} {n : ℕ} (h : input.length = n) {S : ℕ}
    (reading : States Symbol State k n S → Y) {c : Cfg k Symbol State input}
    (hc : c.storage.FitsIn (uniformWindow k S)) :
    (toAutomaton tm n S reading).δ (inWindow h S c)
        (symbolAt input ((toAutomaton tm n S reading).query (inWindow h S c))) =
      inWindow h S (tm.step c) := by
  subst h
  have e1 : ofBounded (c.storage.toBounded (uniformWindow k S)) = c.storage := ofBounded_toBounded hc
  have e2 := core_step (tm := tm) c
  rw [inputSymbol_eq] at e2
  simp only [toAutomaton, inWindow, Fin.cast_eq_self, e1]
  have e3 : ((c.inputPos, c.storage) : Fin (input.length + 2) × Storage Symbol State k) = c.core := rfl
  rw [e3, ← e2]
  rfl

/-! ## 4. The run of the automaton is the run of the machine -/

section Run

variable {input : List Symbol} {n S : ℕ} (h : input.length = n)

theorem output_inWindow {Y : Type} (reading : States Symbol State k n S → Y)
    (c : Cfg k Symbol State input) :
    (toAutomaton tm n S reading).output (inWindow h S c) =
      if c.state.isNone then some (reading (inWindow h S c)) else none := rfl

theorem output_running {Y : Type} (reading : States Symbol State k n S → Y)
    {c : Cfg k Symbol State input} (hc : ¬ c.Halted) :
    (toAutomaton tm n S reading).output (inWindow h S c) = none := by
  rw [output_inWindow]
  cases hst : c.state with
  | none => exact absurd hst hc
  | some q => rfl

/-- **Step by step**: the automaton, with the input as verifier, follows the machine. -/
theorem step_inWindow {Y : Type} (reading : States Symbol State k n S → Y)
    (hs : tm.RunsInSpace input S) (j : ℕ) :
    (toAutomaton tm n S reading).δ (inWindow h S (tm.runFrom (tm.initCfg input) j))
        (symbolAt input ((toAutomaton tm n S reading).query
          (inWindow h S (tm.runFrom (tm.initCfg input) j)))) =
      inWindow h S (tm.runFrom (tm.initCfg input) (j + 1)) := by
  rw [δ_toAutomaton h reading (fitsIn_window hs j), runFrom_succ]

/-- **The automaton returns what the machine leaves when it halts.** If the machine halts at step
`u ≤ t`, the automaton with budget `t` returns the reading of the configuration of step `u`. -/
theorem run_toAutomaton {Y : Type} (reading : States Symbol State k n S → Y)
    (hs : tm.RunsInSpace input S) {u t : ℕ} (hu : tm.HaltsAt (tm.initCfg input) u) (ht : u ≤ t) :
    (toAutomaton tm n S reading).run (symbolAt input) t (toAutomaton tm n S reading).start =
      some (reading (inWindow h S (tm.runFrom (tm.initCfg input) u))) := by
  have aux : ∀ m j, j ≤ u → u ≤ j + m →
      (toAutomaton tm n S reading).run (symbolAt input) m
          (inWindow h S (tm.runFrom (tm.initCfg input) j)) =
        some (reading (inWindow h S (tm.runFrom (tm.initCfg input) u))) := by
    intro m
    induction m with
    | zero =>
      intro j hj hjm
      obtain rfl : j = u := by omega
      rw [Automaton.run_zero, output_inWindow, hu.halted]
      rfl
    | succ m ih =>
      intro j hj hjm
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · refine Automaton.run_some ?_ _
        rw [output_inWindow, hu.halted]
        rfl
      · have hno := output_running (tm := tm) h reading (hu.not_halted hlt)
        rw [Automaton.run_none hno, step_inWindow h reading hs]
        exact ih (j + 1) (by omega) (by omega)
  rw [start_toAutomaton h]
  exact aux t 0 (Nat.zero_le _) (by omega)

include h in
/-- **If the machine does not halt in `t` steps, the automaton returns nothing in `t` queries.** -/
theorem run_toAutomaton_none {Y : Type} (reading : States Symbol State k n S → Y)
    (hs : tm.RunsInSpace input S) {t : ℕ}
    (hno : ∀ j ≤ t, ¬ (tm.runFrom (tm.initCfg input) j).Halted) :
    (toAutomaton tm n S reading).run (symbolAt input) t (toAutomaton tm n S reading).start = none := by
  have aux : ∀ m j, j + m ≤ t →
      (toAutomaton tm n S reading).run (symbolAt input) m
        (inWindow h S (tm.runFrom (tm.initCfg input) j)) = none := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Automaton.run_zero]
      exact output_running (tm := tm) h reading (hno j (by omega))
    | succ m ih =>
      intro j hj
      have hn := output_running (tm := tm) h reading (hno j (by omega))
      rw [Automaton.run_none hn, step_inWindow h reading hs]
      exact ih (j + 1) (by omega)
  rw [start_toAutomaton h]
  exact aux t 0 (by omega)

end Run

/-! ## 5. The size of the automaton -/

section Size

variable [Fintype Symbol] [Fintype State]

/-- **The bits of effective memory** of a machine of `k` tapes with space `S` on inputs of length
`n`: `⌈log₂(n + 2)⌉ + ⌈log₂ base⌉ + exp · k · S`. -/
def spaceBits (Symbol State : Type) [Fintype Symbol] [Fintype State] (k n S : ℕ) : ℕ :=
  Nat.clog 2 (n + 2) + Nat.clog 2 (storageBoundBase Symbol State k) +
    storageBoundExp Symbol k * (k * S)

/-- **The count**: `|σ| ≤ (n + 2) · storageBound Γ Q k (k·S)`, cslib's with the uniform window. -/
theorem card_states (n S : ℕ) :
    Fintype.card (States Symbol State k n S) ≤ (n + 2) * storageBound Symbol State k (k * S) := by
  rw [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (card_boundedStorage_le (by simp))

/-- **In bits**: `|σ| ≤ 2^spaceBits`. -/
theorem card_states_bits (n S : ℕ) :
    Fintype.card (States Symbol State k n S) ≤ 2 ^ spaceBits Symbol State k n S := by
  refine (card_states n S).trans ?_
  unfold spaceBits
  rw [pow_add, pow_add, mul_assoc]
  exact Nat.mul_le_mul (Nat.le_pow_clog one_lt_two _)
    ((storageBound_le_base_mul_pow _).trans (Nat.mul_le_mul_right _ (Nat.le_pow_clog one_lt_two _)))

/-- **With polynomial space, the bits of memory are polynomial.** -/
theorem spaceBits_poly {s : ℕ → ℕ} (hs : Cslib.PolynomiallyBounded s) :
    Cslib.PolynomiallyBounded fun n => spaceBits Symbol State k n (s n) := by
  refine Cslib.PolynomiallyBounded.mono_of_le
    (((Cslib.PolynomiallyBounded.id.add (.const 2)).add
      (.const (Nat.clog 2 (storageBoundBase Symbol State k)))).add
      ((Cslib.PolynomiallyBounded.const (storageBoundExp Symbol k * k)).mul hs)) fun n => ?_
  have h1 : Nat.clog 2 (n + 2) ≤ n + 2 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  simp only [spaceBits, mul_assoc]
  omega

end Size

/-! ## 6. The cube law for cslib's machines -/

/-- **The cube law for cslib machines with space `S`.** Machines `M p c` of `k` tapes, indexed by
`|P| ≤ 2^L` programs and `|C| ≤ 2^s` advice strings, that with space `S` find every `y` of `Y`
reading its encoding `enc y` (of length `n`) and halting within `t` steps, with the answer in the
final state: then `|Y| ≤ 2^L · 2^s · min 2^(b t) 2^spaceBits`, with `|Γ| + 1 ≤ 2^b`. -/
theorem cube_law_tm {P C Y : Type} [Fintype P] [Fintype C] [Fintype Y] [Fintype Symbol]
    [Fintype State] {L s b n S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hR : Fintype.card Symbol + 1 ≤ 2 ^ b) (M : P → C → MultiTapeTM k Symbol State)
    (reading : P → C → States Symbol State k n S → Y) (enc : Y → List Symbol)
    (hlen : ∀ y, (enc y).length = n)
    (h : ∀ y, ∃ p c u, u ≤ t ∧ (M p c).RunsInSpace (enc y) S ∧
      (M p c).HaltsAt ((M p c).initCfg (enc y)) u ∧
      reading p c (inWindow (hlen y) S ((M p c).runFrom ((M p c).initCfg (enc y)) u)) = y) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (2 ^ (b * t)) (2 ^ spaceBits Symbol State k n S) := by
  refine cube_law_general hP hC (card_states_bits n S) (by rwa [Fintype.card_option])
    (fun y => symbolAt (enc y)) (fun p c => toAutomaton (M p c) n S (reading p c)) (fun y => ?_)
  obtain ⟨p, c, u, hut, hs, hu, hl⟩ := h y
  exact ⟨p, c, (run_toAutomaton (hlen y) (reading p c) hs hu hut).trans (congrArg some hl)⟩

/-! ## 7. Halt or cycle, and space `S` gives time `2^O(S)` -/

section System

variable (tm) in
/-- **The machine with its input as a deterministic system on a finite type**: one step of the
automaton with the input fixed; `none` when the next state is the halting one. -/
noncomputable def tmSystem (n S : ℕ) (input : List Symbol) :
    States Symbol State k n S → Option (States Symbol State k n S) := fun x =>
  if ((toAutomaton tm n S fun _ => ()).δ x (symbolAt input x.1.val)).2.1.isNone then none
  else some ((toAutomaton tm n S fun _ => ()).δ x (symbolAt input x.1.val))

variable {input : List Symbol} {S : ℕ}

/-- **The trace of the system is the run of the machine.** -/
theorem trace_tmSystem (hs : tm.RunsInSpace input S) (m : ℕ) :
    trace (tmSystem tm input.length S input) (inWindow rfl S (tm.initCfg input)) m =
      if (tm.runFrom (tm.initCfg input) m).state.isNone then none
      else some (inWindow rfl S (tm.runFrom (tm.initCfg input) m)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [trace, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]
    by_cases hm : (tm.runFrom (tm.initCfg input) m).state.isNone
    · have e : tm.runFrom (tm.initCfg input) (m + 1) = tm.runFrom (tm.initCfg input) m := by
        rw [runFrom_succ, step_of_halt (Option.isNone_iff_eq_none.mp hm)]
      rw [ite_eq_left hm, e, ite_eq_left hm]
      rfl
    · rw [ite_eq_right hm]
      have hp : (toAutomaton tm input.length S fun _ => ()).δ
          (inWindow rfl S (tm.runFrom (tm.initCfg input) m))
          (symbolAt input (inWindow rfl S (tm.runFrom (tm.initCfg input) m)).1.val) =
            inWindow rfl S (tm.runFrom (tm.initCfg input) (m + 1)) :=
        step_inWindow rfl (fun _ => ()) hs m
      change tmSystem tm input.length S input (inWindow rfl S (tm.runFrom (tm.initCfg input) m)) = _
      unfold tmSystem
      rw [hp]
      rfl

theorem trace_tmSystem_none_iff (hs : tm.RunsInSpace input S) (m : ℕ) :
    trace (tmSystem tm input.length S input) (inWindow rfl S (tm.initCfg input)) m = none ↔
      (tm.runFrom (tm.initCfg input) m).Halted := by
  rw [trace_tmSystem hs]
  by_cases hm : (tm.runFrom (tm.initCfg input) m).state.isNone
  · simp only [ite_eq_left hm, true_iff]; exact Option.isNone_iff_eq_none.mp hm
  · simp only [ite_eq_right hm, reduceCtorEq, false_iff]
    exact fun e => hm (Option.isNone_iff_eq_none.mpr e)

variable [Fintype Symbol] [Fintype State]

/-- **Halt or cycle, for cslib machines with space `S`.** Either the machine halts within
`N = (n + 2) · storageBound Γ Q k (k·S)` steps, or it never halts and the sequence of its cores
(input head, state and work tapes) is eventually periodic, with preperiod plus period at most
`N + 1`. -/
theorem halt_or_cycle_tm (hs : tm.RunsInSpace input S) :
    (∃ m ≤ (input.length + 2) * storageBound Symbol State k (k * S),
        (tm.runFrom (tm.initCfg input) m).Halted) ∨
    ((∀ m, ¬ (tm.runFrom (tm.initCfg input) m).Halted) ∧
      ∃ i p, 0 < p ∧ i + p ≤ (input.length + 2) * storageBound Symbol State k (k * S) + 1 ∧
        ∀ m, i ≤ m →
          (tm.runFrom (tm.initCfg input) (m + p)).core = (tm.runFrom (tm.initCfg input) m).core) := by
  have hc := card_states (Symbol := Symbol) (State := State) (k := k) input.length S
  rcases halt_or_cycle (tmSystem tm input.length S input) (inWindow rfl S (tm.initCfg input)) with
    ⟨m, hm, e⟩ | ⟨hno, i, p, hp, hip, hper⟩
  · exact Or.inl ⟨m, hm.trans hc, (trace_tmSystem_none_iff hs m).mp e⟩
  · refine Or.inr ⟨fun m hm => hno m ((trace_tmSystem_none_iff hs m).mpr hm), i, p, hp, by omega,
      fun m hm => ?_⟩
    have e := hper m hm
    rw [trace_tmSystem hs, trace_tmSystem hs] at e
    have h1 : ¬ (tm.runFrom (tm.initCfg input) (m + p)).state.isNone := fun h =>
      hno (m + p) ((trace_tmSystem_none_iff hs _).mpr (Option.isNone_iff_eq_none.mp h))
    have h2 : ¬ (tm.runFrom (tm.initCfg input) m).state.isNone := fun h =>
      hno m ((trace_tmSystem_none_iff hs _).mpr (Option.isNone_iff_eq_none.mp h))
    rw [ite_eq_right h1, ite_eq_right h2, Option.some_inj] at e
    simp only [inWindow, Fin.cast_eq_self, Prod.mk.injEq] at e
    exact Prod.ext e.1 (toBounded_inj (fitsIn_window hs _) (fitsIn_window hs _) e.2)

/-- **Space `S` gives time `2^O(S)`.** A cslib machine with space `S` that halts, halts within
`2^spaceBits` steps. -/
theorem halts_soon_tm (hs : tm.RunsInSpace input S)
    (hhalt : ∃ t, (tm.runFrom (tm.initCfg input) t).Halted) :
    ∃ m ≤ 2 ^ spaceBits Symbol State k input.length S, (tm.runFrom (tm.initCfg input) m).Halted := by
  obtain ⟨t, ht⟩ := hhalt
  obtain ⟨m, hm, e⟩ := halts_before_two_pow (tmSystem tm input.length S input)
    (inWindow rfl S (tm.initCfg input)) (card_states_bits input.length S)
    ⟨t, (trace_tmSystem_none_iff hs t).mpr ht⟩
  exact ⟨m, hm, (trace_tmSystem_none_iff hs m).mp e⟩

end System

/-! ## 8. The CHT tower, piece 1, for cslib's machines -/

/-- **The CHT tower, piece 1: homogeneity with polynomial memory gives the `PSPACE` bound.** A cslib
machine (homogeneous in time, `step_toAutomaton`) that runs in polynomial space `s` halts, whenever it
halts, within `2^b(n)` steps, for a polynomial `b`. The time bound that homogeneity and memory give is
exponential; it is not a polynomial (`Dynamics.cht_exponential_not_polynomial`). The gap between `P`
and `PSPACE` lives between `2^S` and `poly(n)`, and nothing in the homogeneity of time closes it. -/
theorem cht_pspace [Fintype Symbol] [Fintype State] (tm : MultiTapeTM k Symbol State) {s : ℕ → ℕ}
    (hs : Cslib.PolynomiallyBounded s) (hsp : ∀ input, tm.RunsInSpace input (s input.length)) :
    ∃ b : ℕ → ℕ, Cslib.PolynomiallyBounded b ∧ ∀ input : List Symbol,
      (∃ t, (tm.runFrom (tm.initCfg input) t).Halted) →
        ∃ m ≤ 2 ^ b input.length, (tm.runFrom (tm.initCfg input) m).Halted :=
  ⟨fun n => spaceBits Symbol State k n (s n), spaceBits_poly hs,
    fun input hhalt => halts_soon_tm (hsp input) hhalt⟩

/-! ## 9. Time translation: the machine is a homogeneous automaton -/

section Homogeneous

variable {input : List Symbol} {n S : ℕ}

/-- **The homogeneous step follows the machine**, also after it halts. -/
theorem step_toAutomaton (h : input.length = n) {Y : Type} (reading : States Symbol State k n S → Y)
    (hs : tm.RunsInSpace input S) (t : ℕ) :
    ((toAutomaton tm n S reading).step (symbolAt input))^[t] (inWindow h S (tm.initCfg input)) =
      inWindow h S (tm.runFrom (tm.initCfg input) t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    exact step_inWindow h reading hs t

/-- **A cslib machine does not know the time** (the CHT, by the bridge): if the core of step `j`
repeats that of step `i ≤ j` and the machine did not halt before `j`, the automaton returns the same
with `i + t` and with `j + t` queries. -/
theorem does_not_know_the_time_tm (h : input.length = n) {Y : Type}
    (reading : States Symbol State k n S → Y) (hs : tm.RunsInSpace input S) {i j : ℕ} (hij : i ≤ j)
    (hj : ∀ m < j, ¬ (tm.runFrom (tm.initCfg input) m).Halted)
    (hcore : (tm.runFrom (tm.initCfg input) i).core = (tm.runFrom (tm.initCfg input) j).core)
    (t : ℕ) :
    (toAutomaton tm n S reading).run (symbolAt input) (i + t) (toAutomaton tm n S reading).start =
      (toAutomaton tm n S reading).run (symbolAt input) (j + t) (toAutomaton tm n S reading).start := by
  rw [start_toAutomaton h]
  refine does_not_know_the_time _ _ (fun m hm => ?_) hij ?_ t
  · rw [step_toAutomaton h reading hs]
    exact output_running (tm := tm) h reading (hj m hm)
  · rw [step_toAutomaton h reading hs, step_toAutomaton h reading hs]
    have e1 : (tm.runFrom (tm.initCfg input) i).inputPos = (tm.runFrom (tm.initCfg input) j).inputPos :=
      congrArg Prod.fst hcore
    have e2 : (tm.runFrom (tm.initCfg input) i).storage = (tm.runFrom (tm.initCfg input) j).storage :=
      congrArg Prod.snd hcore
    simp only [inWindow, e1, e2]

end Homogeneous

/-! ## 10. Controls -/

section Controls

/-- **Control of the window**: without `FitsIn`, the way back from the window loses cells. -/
theorem window_control : ¬ ∀ x : Storage Unit Unit 1, ofBounded (x.toBounded (uniformWindow 1 0)) = x := by
  intro h
  have := congrArg (fun y => y.workTapes 0 1)
    (h ⟨none, fun _ z => if z = 1 then some () else none, fun _ => 0⟩)
  simp [ofBounded, Storage.toBounded, window] at this

/-- **Control of the input head**: without the term `⌈log₂(n + 2)⌉` the bound in bits is false. -/
theorem input_head_control : ¬ Fintype.card (States Empty Empty 0 0 0) ≤
    2 ^ (Nat.clog 2 (storageBoundBase Empty Empty 0) + storageBoundExp Empty 0 * (0 * 0)) := by
  simp [States, BoundedStorage, storageBoundBase, storageBoundExp]

/-- A machine without work tapes that halts at the first step. -/
noncomputable def haltsNow : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ => ⟨0, fun i => i.elim0, none, none⟩

/-- **Positive control**: the hypotheses of the bridge hold for a real machine. `haltsNow` runs in
space `0`, halts at step `1`, and the corollary gives the cut `2^spaceBits`. -/
theorem haltsNow_control (input : List Bool) :
    haltsNow.RunsInSpace input 0 ∧ haltsNow.HaltsAt (haltsNow.initCfg input) 1 ∧
      ∃ m ≤ 2 ^ spaceBits Bool Unit 0 input.length 0,
        (haltsNow.runFrom (haltsNow.initCfg input) m).Halted := by
  have hs : haltsNow.RunsInSpace input 0 := MultiTapeNTM.runsInSpace_zero_tapes _ _ _
  have h1 : (haltsNow.runFrom (haltsNow.initCfg input) 1).Halted := by
    rw [runFrom_one, step_of_state (q := ()) rfl]
    simp only [haltsNow, tr_ofTr]
    rfl
  refine ⟨hs, ⟨h1, fun s hs1 => ?_⟩, halts_soon_tm hs ⟨1, h1⟩⟩
  obtain rfl : s = 0 := by omega
  simp [runFrom, Cfg.Halted]

end Controls

/-! ## 11. The first localization, complete, for Turing machines -/

/-- **The first localization, complete, for Turing machines: the dynamics does not carry the
arrow.**

1. **The abstract statement** (`Dynamics.localization_one`) for the model of cslib's machines: time
   reversal conserves the information (discrete Noether, Koopman unitarity ⟺ bijectivity, reversible
   dynamics keep the size of every set), time translation makes a homogeneous system blind to the
   clock and charges the clock to memory, and the CHT bounds by `2^S` the time of a system of `S`
   bits; the arrow is independent of the closure properties.
2. **For every cslib machine with space `S`**: it does not know the time (if a core repeats before
   it halts, the run repeats), and whenever it halts it halts within `2^spaceBits` steps.
3. **The CHT tower, piece 1**: with polynomial space the bound is `2^poly`, the `PSPACE` bound, and
   homogeneity with its memory gives no better: the counter of `n + 1` bits uses `2^n` queries.
4. **What decides the arrow is not the dynamics but the bit**: the decision hypothesis for Turing
   machines is equivalent to the arrow. -/
theorem localization_one_tm :
    ((∀ (σ : Type) [Fintype σ] (f : σ → σ) (Q : σ → ℝ), (Q ∘ f = Q ↔
        ∀ θ : ℝ, (koopman f).comp (mult (phase θ Q)) = (mult (phase θ Q)).comp (koopman f))) ∧
      (∀ (σ : Type) [Fintype σ] (f : σ → σ),
        (∀ φ, norm2 (koopman f φ) = norm2 φ) ↔ Function.Bijective f) ∧
      (∀ (σ : Type) [DecidableEq σ] (D : ReversibleDynamics σ) (n : ℕ) (S : Finset σ),
        (S.image D.step^[n]).card = S.card) ∧
      (∀ (σ Q R Y : Type) (a : Automaton σ Q R Y) (O : Q → R) (x : σ) (i j t : ℕ),
        (∀ k < j, a.output ((a.step O)^[k] x) = none) → i ≤ j →
        (a.step O)^[i] x = (a.step O)^[j] x → a.run O (i + t) x = a.run O (j + t) x) ∧
      (∀ (κ σ Q R Y : Type) (a : ClockedAutomaton κ σ Q R Y) (O : Q → R) (t : ℕ) (k : κ) (x : σ),
        a.homogenize.run O t (x, k) = a.run O t k x) ∧
      (∀ (σ Q R Y : Type) [Fintype σ] (a : Automaton σ Q R Y) (O : Q → R) (S t : ℕ) (x : σ) (y : Y),
        Fintype.card σ ≤ 2 ^ S → a.run O t x = some y → ∃ m < 2 ^ S, a.run O m x = some y) ∧
      (¬collapsedModel.Arrow ∧ separatedModel.Arrow) ∧
      (tmModel.DecisionHypothesis ↔ tmModel.Arrow)) ∧
    (∀ (k : ℕ) (State : Type) [Fintype State] (tm : MultiTapeTM k Bool State) (input : List Bool)
        (S : ℕ), tm.RunsInSpace input S →
        (∀ (i j t : ℕ), i ≤ j → (∀ m < j, ¬ (tm.runFrom (tm.initCfg input) m).Halted) →
          (tm.runFrom (tm.initCfg input) i).core = (tm.runFrom (tm.initCfg input) j).core →
          (toAutomaton tm input.length S fun _ => ()).run (symbolAt input) (i + t)
              (toAutomaton tm input.length S fun _ => ()).start =
            (toAutomaton tm input.length S fun _ => ()).run (symbolAt input) (j + t)
              (toAutomaton tm input.length S fun _ => ()).start) ∧
        ((∃ t, (tm.runFrom (tm.initCfg input) t).Halted) →
          ∃ m ≤ 2 ^ spaceBits Bool State k input.length S,
            (tm.runFrom (tm.initCfg input) m).Halted)) ∧
    (∀ (k : ℕ) (State : Type) [Fintype State] (tm : MultiTapeTM k Bool State) (s : ℕ → ℕ),
        Cslib.PolynomiallyBounded s → (∀ input, tm.RunsInSpace input (s input.length)) →
        ∃ b : ℕ → ℕ, Cslib.PolynomiallyBounded b ∧ ∀ input : List Bool,
          (∃ t, (tm.runFrom (tm.initCfg input) t).Halted) →
            ∃ m ≤ 2 ^ b input.length, (tm.runFrom (tm.initCfg input) m).Halted) ∧
    (∀ n, 1 ≤ n → (counter n).run (fun _ => false) (2 ^ n - 1) (counter n).start = none ∧
        Fintype.card (Fin (2 ^ n + 2)) ≤ 2 ^ (n + 1)) ∧
    (DecisionHypothesis ↔ Arrow) :=
  ⟨localization_one tmModel,
    fun _ _ _ tm _ _ hs => ⟨fun _ _ t hij hj hcore =>
      does_not_know_the_time_tm (tm := tm) rfl (fun _ => ()) hs hij hj hcore t,
      fun hhalt => halts_soon_tm hs hhalt⟩,
    fun _ _ _ tm _ hs hsp => cht_pspace tm hs hsp,
    fun n hn => ⟨counter_not_before n, card_counter hn⟩,
    decisionHypothesis_iff_arrow⟩

/-- **Irreversibility without loss of information, for Turing machines.** Under the decision
hypothesis, a reversible dynamics loses no information (a theorem), and yet some search problem with
a polynomial verifier is not solved in polynomial time from its instances alone (HD, a hypothesis):
SAT is not in `P`. -/
theorem irreversibility_without_loss_tm (h : DecisionHypothesis) :
    (∀ (σ : Type) [DecidableEq σ] (D : ReversibleDynamics σ) (n : ℕ) (S : Finset σ),
        (S.image D.step^[n]).card = S.card) ∧
    (∀ (σ : Type) [Fintype σ] (D : ReversibleDynamics σ) (φ : σ → ℂ),
        norm2 (koopman D.step φ) = norm2 φ) ∧
    ¬tmModel.SearchEasy ∧ Cslib.Complexity.SAT ∉ Cslib.Complexity.P Cslib.Complexity.encCNF :=
  ⟨(irreversibility_without_loss (decisionHypothesis_iff_model.1 h)).1,
    (irreversibility_without_loss (decisionHypothesis_iff_model.1 h)).2.1,
    (irreversibility_without_loss (decisionHypothesis_iff_model.1 h)).2.2,
    SAT_notMem_P_of_decision h⟩

end Sagitta.Arrow.TM

/-! ## Checks: the axioms, and one mutant per central theorem

`#print axioms` on every central theorem of the first localization (both layers), under
`#guard_msgs`: only `propext`, `Classical.choice` and `Quot.sound` (or none). Then one mutant per
central theorem: a weakened hypothesis or a strengthened conclusion, which must **fail** to
elaborate (`fail_if_success`); the build breaks if any of them starts to succeed. -/

/-- info: 'Sagitta.Arrow.Dynamics.conserved_iff_const_on_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.conserved_iff_const_on_orbits
/-- info: 'Sagitta.Arrow.Dynamics.koopman_noether' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.koopman_noether
/-- info: 'Sagitta.Arrow.Dynamics.koopman_isometry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.koopman_isometry_iff
/-- info: 'Sagitta.Arrow.ReversibleDynamics.card_image_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.ReversibleDynamics.card_image_iterate
/-- info: 'Sagitta.Arrow.ReversibleDynamics.koopman_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.ReversibleDynamics.koopman_isometry
/-- info: 'Sagitta.Arrow.Dynamics.entropy_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.entropy_pushforward
/-- info: 'Sagitta.Arrow.Dynamics.erasure_not_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.erasure_not_isometry
/-- info: 'Sagitta.Arrow.Dynamics.noether_charge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.noether_charge
/-- info: 'Sagitta.Arrow.Dynamics.does_not_know_the_time' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.does_not_know_the_time
/-- info: 'Sagitta.Arrow.Dynamics.ClockedAutomaton.homogenize_run' does not depend on any axioms -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.ClockedAutomaton.homogenize_run
/-- info: 'Sagitta.Arrow.Dynamics.card_clock_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.card_clock_bits
/-- info: 'Sagitta.Arrow.Dynamics.cube_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.cube_law
/-- info: 'Sagitta.Arrow.Dynamics.cube_law_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.cube_law_general
/-- info: 'Sagitta.Arrow.Dynamics.cube_law_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.cube_law_clock
/-- info: 'Sagitta.Arrow.Dynamics.clock_price_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.clock_price_control
/-- info: 'Sagitta.Arrow.Dynamics.clock_leaves_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.clock_leaves_trace
/-- info: 'Sagitta.Arrow.Dynamics.halt_or_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.halt_or_cycle
/-- info: 'Sagitta.Arrow.Dynamics.halts_before_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.halts_before_two_pow
/-- info: 'Sagitta.Arrow.Dynamics.cht_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.cht_time
/-- info: 'Sagitta.Arrow.Dynamics.clock_in_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.clock_in_memory
/-- info: 'Sagitta.Arrow.Dynamics.counter_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.counter_decides
/-- info: 'Sagitta.Arrow.Dynamics.counter_not_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.counter_not_before
/-- info: 'Sagitta.Arrow.Dynamics.cht_exponential_not_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.cht_exponential_not_polynomial
/-- info: 'Sagitta.Arrow.Dynamics.localization_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.localization_one
/-- info: 'Sagitta.Arrow.Dynamics.irreversibility_without_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.Dynamics.irreversibility_without_loss
/-- info: 'Sagitta.Arrow.TM.card_states_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.card_states_bits
/-- info: 'Sagitta.Arrow.TM.spaceBits_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.spaceBits_poly
/-- info: 'Sagitta.Arrow.TM.run_toAutomaton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.run_toAutomaton
/-- info: 'Sagitta.Arrow.TM.cube_law_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.cube_law_tm
/-- info: 'Sagitta.Arrow.TM.halt_or_cycle_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.halt_or_cycle_tm
/-- info: 'Sagitta.Arrow.TM.halts_soon_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.halts_soon_tm
/-- info: 'Sagitta.Arrow.TM.cht_pspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.cht_pspace
/-- info: 'Sagitta.Arrow.TM.does_not_know_the_time_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.does_not_know_the_time_tm
/-- info: 'Sagitta.Arrow.TM.window_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.window_control
/-- info: 'Sagitta.Arrow.TM.haltsNow_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.haltsNow_control
/-- info: 'Sagitta.Arrow.TM.localization_one_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.localization_one_tm
/-- info: 'Sagitta.Arrow.TM.irreversibility_without_loss_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sagitta.Arrow.TM.irreversibility_without_loss_tm

section Mutants

open Turing Sagitta.Arrow Sagitta.Arrow.TM Sagitta.Arrow.Dynamics

set_option linter.unusedVariables false

/-! ### Mutants of the core (`Core/Dynamics.lean`) -/

/-- Mutant of `koopman_isometry_iff`: unitarity without bijectivity. -/
example (f : Bool → Bool) (φ : Bool → ℂ) : True := by
  fail_if_success
    have : norm2 (koopman f φ) = norm2 φ := (koopman_isometry_iff f).2 (by assumption) φ
  trivial

/-- Mutant of `koopman_noether`: conservation from a single phase (`θ = 0`) instead of all. -/
example (f : Bool → Bool) (Q : Bool → ℝ) : True := by
  fail_if_success
    have : Q ∘ f = Q ↔ (koopman f).comp (mult (phase 0 Q)) = (mult (phase 0 Q)).comp (koopman f) :=
      koopman_noether f Q
  trivial

/-- Mutant of `ReversibleDynamics.card_image_iterate`: information conserved by any step. -/
example (f : Bool → Bool) (S : Finset Bool) : True := by
  fail_if_success
    have : (S.image f).card = S.card := Finset.card_image_of_injective _ (by assumption)
  trivial

/-- Mutant of `does_not_know_the_time`: without "it did not stop before `j`". -/
example {σ Q R Y : Type} (a : Automaton σ Q R Y) (O : Q → R) (x : σ) (i j t : ℕ) (hij : i ≤ j)
    (h : (a.step O)^[i] x = (a.step O)^[j] x) : True := by
  fail_if_success
    have : a.run O (i + t) x = a.run O (j + t) x := does_not_know_the_time a O (by assumption) hij h t
  trivial

/-- Mutant of `ClockedAutomaton.homogenize_run`: the homogeneous run forgets the clock value. -/
example {κ σ Q R Y : Type} (a : ClockedAutomaton κ σ Q R Y) (O : Q → R) (t : ℕ) (k : κ) (x : σ) :
    True := by
  fail_if_success
    have : a.homogenize.run O t (x, k) = a.run O t a.clock0 x := a.homogenize_run O t k x
  trivial

/-- Mutant of `cube_law`: one bit of space less, `2^(S − 2)`. -/
example {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (A : P → C → Automaton σ Y Bool Y) (h : Solves equalTo A t) :
    True := by
  fail_if_success
    have : Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S - 2)) := cube_law hP hC hσ A h
  trivial

/-- Mutant of `cube_law_clock`: the clock not charged, `2^(S − 1)` instead of `2^(S + c − 1)`
(`clock_price_control` refutes it on the clocked sweep). -/
example {P C κ σ Y : Type} [Fintype P] [Fintype C] [Fintype κ] [Fintype σ] [Fintype Y]
    [DecidableEq Y] {L s S c t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (hκ : Fintype.card κ ≤ 2 ^ c)
    (A : P → C → ClockedAutomaton κ σ Y Bool Y)
    (h : ∀ y, ∃ p c, (A p c).run (equalTo y) t (A p c).clock0 (A p c).start = some y) : True := by
  fail_if_success
    have : Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S - 1)) := cube_law_clock hP hC hσ hκ A h
  trivial

/-- Mutant of `halt_or_cycle`: halting within `|σ| − 1` steps. -/
example {σ : Type} [Fintype σ] (δ : σ → Option σ) (s : σ) : True := by
  fail_if_success
    have : (∃ n ≤ Fintype.card σ - 1, trace δ s n = none) ∨
        ((∀ n, trace δ s n ≠ none) ∧ ∃ i p, 0 < p ∧ i + p ≤ Fintype.card σ + 1 ∧
          ∀ n, i ≤ n → trace δ s (n + p) = trace δ s n) := halt_or_cycle δ s
  trivial

/-- Mutant of `cht_time`: answering in fewer than `2^S − 1` queries (`counter_not_before` refutes
the analogous bound for the counter). -/
example {σ Q R Y : Type} [Fintype σ] (a : Automaton σ Q R Y) (O : Q → R) {S t : ℕ} {x : σ} {y : Y}
    (hσ : Fintype.card σ ≤ 2 ^ S) (h : a.run O t x = some y) : True := by
  fail_if_success
    have : ∃ m < 2 ^ S - 1, a.run O m x = some y := cht_time a O hσ h
  trivial

/-- Mutant of `cht_exponential_not_polynomial`: the counter answering in `2^n − 1` queries. -/
example (n : ℕ) : True := by
  fail_if_success
    have : (counter n).run (fun _ => false) (2 ^ n - 1) (counter n).start = some false :=
      counter_not_before n
  trivial

/-- Mutant of `localization_one`: the symmetries of the dynamics deciding the arrow in any model. -/
example (M : Model) : True := by
  fail_if_success
    have : M.Arrow := (localization_one M).2.2.2.2.2.2.1.2
  trivial

/-- Mutant of `irreversibility_without_loss`: without the decision hypothesis. -/
example (M : Model) : True := by
  fail_if_success
    have : ¬M.SearchEasy := (irreversibility_without_loss (M := M) (by assumption)).2.2
  trivial

/-! ### Mutants of the Turing-machine layer -/

/-- Mutant of `halts_soon_tm`: without `RunsInSpace`. -/
example {k : ℕ} {State : Type} [Fintype State] (tm : MultiTapeTM k Bool State) (input : List Bool)
    (S : ℕ) (hhalt : ∃ t, (tm.runFrom (tm.initCfg input) t).Halted) : True := by
  fail_if_success
    have : ∃ m ≤ 2 ^ spaceBits Bool State k input.length S,
        (tm.runFrom (tm.initCfg input) m).Halted := halts_soon_tm (by assumption) hhalt
  trivial

/-- Mutant of `cht_pspace`: without polynomial space. -/
example {k : ℕ} {State : Type} [Fintype State] (tm : MultiTapeTM k Bool State) (s : ℕ → ℕ)
    (hsp : ∀ input, tm.RunsInSpace input (s input.length)) : True := by
  fail_if_success
    have := cht_pspace tm (by assumption) hsp
  trivial

/-- Mutant of `does_not_know_the_time_tm`: without "it did not halt before `j`". -/
example {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) (input : List Bool) (S i j t : ℕ)
    (hs : tm.RunsInSpace input S) (hij : i ≤ j)
    (hcore : (tm.runFrom (tm.initCfg input) i).core = (tm.runFrom (tm.initCfg input) j).core) :
    True := by
  fail_if_success
    have := does_not_know_the_time_tm (tm := tm) rfl (fun _ => ()) hs hij (by assumption) hcore t
  trivial

/-- Mutant of `cube_law_tm`: one bit of memory less, `2^(spaceBits − 1)`. -/
example {k : ℕ} {Symbol State P C Y : Type} [Fintype P] [Fintype C] [Fintype Y] [Fintype Symbol]
    [Fintype State] {L s b n S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hR : Fintype.card Symbol + 1 ≤ 2 ^ b) (M : P → C → MultiTapeTM k Symbol State)
    (reading : P → C → States Symbol State k n S → Y) (enc : Y → List Symbol)
    (hlen : ∀ y, (enc y).length = n)
    (h : ∀ y, ∃ p c u, u ≤ t ∧ (M p c).RunsInSpace (enc y) S ∧
      (M p c).HaltsAt ((M p c).initCfg (enc y)) u ∧
      reading p c (inWindow (hlen y) S ((M p c).runFrom ((M p c).initCfg (enc y)) u)) = y) :
    True := by
  fail_if_success
    have : Fintype.card Y ≤
        2 ^ L * 2 ^ s * min (2 ^ (b * t)) (2 ^ (spaceBits Symbol State k n S - 1)) :=
      cube_law_tm hP hC hR M reading enc hlen h
  trivial

/-- Mutant of `localization_one_tm`: the first localization deciding the arrow for Turing machines. -/
example : True := by
  fail_if_success
    have : Arrow := localization_one_tm.1.2.2.2.2.2.2.1.2
  trivial

/-- Mutant of `irreversibility_without_loss_tm`: SAT outside `P` without the decision hypothesis. -/
example : True := by
  fail_if_success
    have := (irreversibility_without_loss_tm (by assumption)).2.2.2
  trivial

end Mutants
