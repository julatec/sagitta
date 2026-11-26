/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.Decision
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Option

/-!
# The dynamics does not carry the arrow: the two symmetries of time and their charges

The first localization says that the arrow is **not** in the dynamics. `Core/Reversible.lean`
proves it for one property, reversibility. This file completes it with the **two symmetries of time**
that a dynamics can have, and the conserved quantity (the *Noether charge*) of each.

## 1. Time reversal: the information is conserved (Noether, Koopman form)

* **Discrete Noether** (`conserved_iff_const_on_orbits`): for a reversible step `f : Equiv.Perm σ`,
  a quantity `Q` is conserved (`Q ∘ f = Q`) if and only if it is constant on every orbit of the
  group `⟨f⟩ ≅ ℤ` (the steps forward and backward).
* **Koopman form** (`koopman_noether`): `koopman f φ = φ ∘ f` is linear even when `f` is not, and
  `Q ∘ f = Q` holds if and only if every phase `exp (iθQ)` commutes with `koopman f`. This holds for
  every `f`, reversible or not.
* **What reversibility conserves: information.** `koopman f` preserves the `ℓ²` norm if and only if
  `f` is bijective (`koopman_isometry_iff`); on indicators the squared norm is the size
  (`norm2_indicator`), so unitarity conserves `log₂ |S|`. A permutation never changes the size of a
  set (`card_image_zpow`) nor the Shannon entropy of a distribution (`entropy_pushforward`); a
  reversible dynamics of `Core/Reversible.lean` neither creates nor destroys information
  (`ReversibleDynamics.card_image_iterate`, `ReversibleDynamics.koopman_isometry`). The control
  (`erasure_not_isometry`): the constant map on `Bool` is not unitary.

*Honesty.* Noether's theorem proper is about continuous symmetries of a Lagrangian. Here the group is
`ℤ`, there is no Lagrangian, and the statement is close to a tautology: it is the discrete form, not
the theorem. Koopman's operator is Koopman's (PNAS 17, 1931); the discrete variational Noether is
Marsden and West's (Acta Numerica, 2001); Noether for Markov processes is Baez and Fong's (J. Math.
Phys., 2013).

## 2. Time translation: the system does not know the time (the CHT)

A system is **homogeneous in time** when its rule does not depend on the step: an `Automaton`
consults, moves and answers from its state alone, with no step counter. That is the conservation of
the homogeneity of time (CHT).

* **The charge** (`noether_charge`, `does_not_know_the_time`): two runs of a homogeneous automaton
  that reach the same state, at times `i` and `j`, continue identically. Time leaves no trace outside
  the state.
* **The clock is paid in memory** (`ClockedAutomaton`, `homogenize`, `homogenize_run`,
  `card_clock_bits`): an automaton whose rule reads a clock `κ` is a homogeneous automaton on
  `σ × κ` with the same runs; with a clock of `c` bits it has `|σ| · 2^c` states.
* **The control** (`clock_leaves_trace`, `clock_price_control`): a two-state automaton with a
  two-bit clock finds 4 candidates in 3 queries; the cube law without the clock fails, with the clock
  counted it holds with equality.

## 3. The cube law, and halt or cycle in `2^S`

* **The cube law** (`cube_law`): `N ≤ 2^L · 2^s · min (t + 1) 2^(S − 1)` candidates are found by
  `2^L` programs with `2^s` advice strings driving automata of `2^S` states for `t` yes/no queries;
  with an informative verifier of `b` bits, `N ≤ 2^L · 2^s · min 2^(b t) 2^S`
  (`cube_law_general`). With the clock (`cube_law_clock`) the clock adds `c` to the space axis.
* **Halt or cycle** (`halt_or_cycle`, `halts_before_two_pow`): a deterministic step on a finite set
  of states either halts within `|σ|` steps or never halts and is eventually periodic. With `S`
  bits, halting means halting before `2^S`.

## 4. The CHT tower, piece 1: homogeneity with its costs gives `2^S`, not a polynomial

* `cht_time`: a homogeneous automaton of `S` bits that answers, answers in fewer than `2^S` queries;
  with a clock of `c` bits, in fewer than `2^(S + c)` (`clock_in_memory`).
* `counter_decides`, `counter_not_before`: the bound is attained. A counter of `n + 1` bits decides
  whether one of `2^n` candidates is accepted in `2^n` queries, and not in `2^n − 1`. Homogeneity
  with polynomial memory guarantees exponential time, the corner `PSPACE`; nothing in it brings the
  time down to a polynomial.

## 5. The first localization, complete

`localization_one`: neither symmetry of time of the dynamics decides the arrow. Time reversal
conserves the information (a theorem); time translation makes the system blind to the clock and
charges the clock to memory (theorems); both hold in every model, and the arrow holds in one model
satisfying the closure properties and fails in another (`arrow_independent`). Together with the
decision hypothesis (`irreversibility_without_loss`): the information is not lost (Noether, a
theorem), yet from one bit it is not recovered cheaply (HD, a hypothesis). The irreversibility is
*without loss of information*.
-/

namespace Sagitta.Arrow.Dynamics

open Finset

/-! ## 1. Time reversal: discrete Noether and Koopman -/

section Noether

variable {σ β : Type*}

/-- The steps forward and backward of a reversible step are the elements of the group it
generates. -/
theorem zpow_mem_zpowers (f : Equiv.Perm σ) (n : ℤ) : f ^ n ∈ Subgroup.zpowers f :=
  Subgroup.zpow_mem_zpowers f n

/-- **The orbits are the cycles.** -/
theorem mem_orbit_iff_sameCycle (f : Equiv.Perm σ) (x y : σ) :
    y ∈ MulAction.orbit (Subgroup.zpowers f) x ↔ f.SameCycle x y := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨f ^ k, zpow_mem_zpowers f k⟩, rfl⟩

/-- What is conserved by one step is conserved by all of them, forward and backward. -/
theorem conserved_zpow (f : Equiv.Perm σ) (Q : σ → β) (h : Q ∘ f = Q) (n : ℤ) (x : σ) :
    Q ((f ^ n) x) = Q x := by
  have h1 : ∀ y, Q (f y) = Q y := fun y => congrFun h y
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ih, h1]
  | pred k ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    simpa using (h1 (f⁻¹ x)).symm

/-- **Discrete Noether.** A quantity is conserved by a reversible step if and only if it is constant
on every orbit of the group of the steps. -/
theorem conserved_iff_const_on_orbits (f : Equiv.Perm σ) (Q : σ → β) :
    Q ∘ f = Q ↔ ∀ x y, y ∈ MulAction.orbit (Subgroup.zpowers f) x → Q y = Q x := by
  constructor
  · intro h x y hy
    obtain ⟨k, rfl⟩ := (mem_orbit_iff_sameCycle f x y).mp hy
    exact conserved_zpow f Q h k x
  · intro h
    funext x
    exact h x (f x) ((mem_orbit_iff_sameCycle f x (f x)).mpr ⟨1, by simp⟩)

/-- **Koopman's operator**: `φ ↦ φ ∘ f`, linear even when `f` is not. -/
noncomputable def koopman (f : σ → σ) : (σ → ℂ) →ₗ[ℂ] (σ → ℂ) := LinearMap.funLeft ℂ ℂ f

/-- Multiplication by `φ`. -/
noncomputable def mult (φ : σ → ℂ) : (σ → ℂ) →ₗ[ℂ] (σ → ℂ) := LinearMap.mulLeft ℂ φ

@[simp] theorem koopman_apply (f : σ → σ) (φ : σ → ℂ) : koopman f φ = φ ∘ f := rfl
@[simp] theorem mult_apply (φ ψ : σ → ℂ) : mult φ ψ = φ * ψ := rfl

/-- A multiplication commutes with Koopman's operator if and only if its function is invariant. -/
theorem commutes_iff (f : σ → σ) (φ : σ → ℂ) :
    (koopman f).comp (mult φ) = (mult φ).comp (koopman f) ↔ φ ∘ f = φ := by
  constructor
  · intro h
    have := LinearMap.congr_fun h 1
    simpa [koopman_apply, mult_apply] using this
  · intro h
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.comp_apply, koopman_apply, mult_apply]
    funext x
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [← congrFun h x]
    rfl

/-- The phase `exp (iθQ)`. -/
noncomputable def phase (θ : ℝ) (Q : σ → ℝ) : σ → ℂ :=
  fun x => Complex.exp (((θ * Q x : ℝ) : ℂ) * Complex.I)

/-- If the phases agree for every `θ`, the values agree (`θ = π / (a − b)` suffices). -/
theorem eq_of_phases (a b : ℝ)
    (h : ∀ θ : ℝ, Complex.exp (((θ * a : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((θ * b : ℝ) : ℂ) * Complex.I)) : a = b := by
  by_contra hab
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  set θ := Real.pi / (a - b)
  have hθ : θ * a = θ * b + Real.pi := by
    simp only [θ]; field_simp; ring
  have := h θ
  rw [hθ, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at this
  have : (2 : ℂ) * Complex.exp (((θ * b : ℝ) : ℂ) * Complex.I) = 0 := by linear_combination -this
  simp at this

/-- **Discrete Noether, Koopman form.** `Q` is conserved if and only if all its phases `exp (iθQ)`
commute with Koopman's operator. It holds for every `f`, reversible or not: the phase symmetry and
its charge do not see reversibility. -/
theorem koopman_noether (f : σ → σ) (Q : σ → ℝ) :
    Q ∘ f = Q ↔
      ∀ θ : ℝ, (koopman f).comp (mult (phase θ Q)) = (mult (phase θ Q)).comp (koopman f) := by
  simp only [commutes_iff]
  constructor
  · intro h θ
    funext x
    change Complex.exp (((θ * Q (f x) : ℝ) : ℂ) * Complex.I) = _
    rw [show Q (f x) = Q x from congrFun h x]
    rfl
  · intro h
    funext x
    exact eq_of_phases _ _ (fun θ => congrFun (h θ) x)

variable [Fintype σ]

/-- The squared `ℓ²` norm. -/
noncomputable def norm2 (φ : σ → ℂ) : ℝ := ∑ x, Complex.normSq (φ x)

/-- The indicator of a predicate. -/
noncomputable def ind (p : σ → Prop) [DecidablePred p] : σ → ℂ := fun x => if p x then 1 else 0

theorem norm2_ind (p : σ → Prop) [DecidablePred p] : norm2 (ind p) = (univ.filter p).card := by
  simp [norm2, ind, apply_ite Complex.normSq, sum_boole]

/-- On an indicator, the squared norm is the size: the information of a set. -/
theorem norm2_indicator [DecidableEq σ] (S : Finset σ) : norm2 (ind (· ∈ S)) = S.card := by
  rw [norm2_ind]; simp

/-- **Unitarity is reversibility**: Koopman's operator preserves the `ℓ²` norm if and only if the
step is bijective. -/
theorem koopman_isometry_iff (f : σ → σ) :
    (∀ φ, norm2 (koopman f φ) = norm2 φ) ↔ Function.Bijective f := by
  classical
  constructor
  · intro h
    have hfib : ∀ y, (univ.filter (fun x => f x = y)).card = 1 := by
      intro y
      have := h (ind (· = y))
      have e : koopman f (ind (· = y)) = ind (fun x => f x = y) := rfl
      have hy : (univ.filter (fun x : σ => x = y)).card = 1 :=
        card_eq_one.mpr ⟨y, by ext; simp⟩
      rw [e, norm2_ind, norm2_ind, hy] at this
      exact_mod_cast this
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · obtain ⟨c, hc⟩ := card_eq_one.mp (hfib (f b))
      have ha : a ∈ univ.filter (fun x => f x = f b) := by simp [hab]
      have hb : b ∈ univ.filter (fun x => f x = f b) := by simp
      rw [hc, mem_singleton] at ha hb
      rw [ha, hb]
    · obtain ⟨c, hc⟩ := card_eq_one.mp (hfib y)
      have : c ∈ univ.filter (fun x => f x = y) := by rw [hc]; exact mem_singleton_self c
      exact ⟨c, (mem_filter.mp this).2⟩
  · intro hf φ
    exact Equiv.sum_comp (Equiv.ofBijective f hf) (fun y => Complex.normSq (φ y))

end Noether

section Information

/-- **A permutation conserves information**: it never changes the size of a set, in any number of
steps forward or backward. -/
theorem card_image_zpow {σ : Type*} [DecidableEq σ] (f : Equiv.Perm σ) (n : ℤ) (S : Finset σ) :
    (S.image (f ^ n)).card = S.card :=
  card_image_of_injective _ (f ^ n).injective

/-- **And the Shannon entropy**: the push-forward of a distribution by a permutation is the same list
of weights. -/
theorem entropy_pushforward {σ : Type*} [Fintype σ] (f : Equiv.Perm σ) (μ : σ → ℝ) :
    ∑ y, Real.negMulLog (μ (f.symm y)) = ∑ x, Real.negMulLog (μ x) :=
  Equiv.sum_comp f.symm (fun x => Real.negMulLog (μ x))

/-- **A reversible dynamics neither creates nor destroys information**: `n` steps forward keep the
size of every set of states. -/
theorem _root_.Sagitta.Arrow.ReversibleDynamics.card_image_iterate {σ : Type*} [DecidableEq σ] (D : ReversibleDynamics σ)
    (n : ℕ) (S : Finset σ) : (S.image D.step^[n]).card = S.card :=
  card_image_of_injective _ (D.step_injective.iterate n)

/-- **A reversible dynamics on finitely many states is unitary** in Koopman's picture. -/
theorem _root_.Sagitta.Arrow.ReversibleDynamics.koopman_isometry {σ : Type*} [Fintype σ] (D : ReversibleDynamics σ)
    (φ : σ → ℂ) : norm2 (koopman D.step φ) = norm2 φ :=
  (koopman_isometry_iff D.step).2 (Finite.injective_iff_bijective.1 D.step_injective) φ

/-- **Control: erasure is not unitary.** The constant step on `Bool` merges two states, and Koopman's
operator does not preserve the norm. -/
theorem erasure_not_isometry : ¬∀ φ : Bool → ℂ, norm2 (koopman (fun _ => false) φ) = norm2 φ := by
  rw [koopman_isometry_iff]
  rintro ⟨hi, -⟩
  exact Bool.false_ne_true (hi (rfl : (fun _ : Bool => false) false = (fun _ => false) true))

end Information

/-! ## 2. Homogeneous automata -/

/-- **An automaton that consults a verifier, homogeneous in time.** States `σ` (the working memory:
`S` bits if `|σ| ≤ 2^S`), an initial state, the query of each state, the transition on the answer and
the output (`some y`: return `y` and stop). **There is no step counter**: whatever the automaton knows
about how long it has run is what it keeps in `σ`, and it pays for it in states. -/
structure Automaton (σ Q R Y : Type) where
  /-- The initial state. -/
  start : σ
  /-- What the automaton asks in each state. -/
  query : σ → Q
  /-- The transition on the answer. -/
  δ : σ → R → σ
  /-- `some y`: return `y` and stop; `none`: keep asking. -/
  output : σ → Option Y

namespace Automaton

variable {σ Q R Y : Type} (a : Automaton σ Q R Y)

/-- **The run with at most `t` queries**, from the state `x`, against the verifier `O`. -/
def run (O : Q → R) : ℕ → σ → Option Y
  | 0, x => a.output x
  | t + 1, x =>
    match a.output x with
    | some y => some y
    | none => run O t (a.δ x (O (a.query x)))

variable {a}

theorem run_zero (O : Q → R) (x : σ) : a.run O 0 x = a.output x := rfl

theorem run_some {O : Q → R} {x : σ} {y : Y} (h : a.output x = some y) : ∀ t, a.run O t x = some y
  | 0 => h
  | t + 1 => by simp [run, h]

theorem run_none {O : Q → R} {x : σ} (h : a.output x = none) (t : ℕ) :
    a.run O (t + 1) x = a.run O t (a.δ x (O (a.query x))) := by
  simp [run, h]

/-- More budget does not change what was already returned. -/
theorem run_mono {O : Q → R} {y : Y} :
    ∀ {t : ℕ} {x : σ} (u : ℕ), a.run O t x = some y → a.run O (t + u) x = some y
  | 0, x, u, h => run_some h _
  | t + 1, x, u, h => by
      cases hs : a.output x with
      | some z =>
          rw [run_some hs (O := O)] at h
          rw [← h]; exact run_some hs _
      | none =>
          rw [run_none hs] at h
          rw [show t + 1 + u = (t + u) + 1 by omega, run_none hs]
          exact run_mono u h

/-- What is returned comes from some state that stops with it. -/
theorem run_output {O : Q → R} {y : Y} :
    ∀ {t : ℕ} {x : σ}, a.run O t x = some y → ∃ x', a.output x' = some y
  | 0, x, h => ⟨x, h⟩
  | t + 1, x, h => by
      cases hs : a.output x with
      | some z => exact ⟨x, by rw [hs, ← run_some hs (O := O) (t + 1), h]⟩
      | none => rw [run_none hs] at h; exact run_output h

/-- One step of the homogeneous run, without looking at whether it stops. -/
def step (a : Automaton σ Q R Y) (O : Q → R) (x : σ) : σ := a.δ x (O (a.query x))

/-- **Splitting a run**: if it did not stop in its first `i` states, running `i + t` is running `t`
from the state at time `i`. -/
theorem run_split (a : Automaton σ Q R Y) (O : Q → R) :
    ∀ (i t : ℕ) (x : σ), (∀ k < i, a.output ((a.step O)^[k] x) = none) →
      a.run O (i + t) x = a.run O t ((a.step O)^[i] x)
  | 0, t, x, _ => by simp
  | i + 1, t, x, h => by
      have h0 : a.output x = none := h 0 (by omega)
      rw [show i + 1 + t = (i + t) + 1 by omega, run_none h0, Function.iterate_succ_apply]
      exact run_split a O i t _ fun k hk => by
        have := h (k + 1) (by omega); rwa [Function.iterate_succ_apply] at this

end Automaton

open Automaton

/-- The yes/no verifier of `y`. -/
def equalTo {Y : Type} [DecidableEq Y] (y : Y) : Y → Bool := fun z => decide (z = y)

/-- **A family of automata solves in time `t`**: for every hidden `y` some program `p` and advice
`c` drive an automaton that, against the verifier of `y`, returns `y` within `t` queries. -/
def Solves {P C σ Q R Y : Type} (O : Y → Q → R) (A : P → C → Automaton σ Q R Y) (t : ℕ) : Prop :=
  ∀ y, ∃ p c, (A p c).run (O y) t (A p c).start = some y

/-- **The pigeonhole of solvers**: if every index finds at most `K` instances and every instance is
found by some index, there are at most `|ι| · K` instances. -/
theorem cover {ι Y : Type} [Fintype ι] [Fintype Y] (good : ι → Y → Prop)
    [∀ i y, Decidable (good i y)] (K : ℕ) (hK : ∀ i, (univ.filter (good i)).card ≤ K)
    (h : ∀ y, ∃ i, good i y) : Fintype.card Y ≤ Fintype.card ι * K := by
  classical
  calc Fintype.card Y = (univ : Finset Y).card := card_univ.symm
    _ ≤ (univ.biUnion fun i => univ.filter (good i)).card := by
        apply card_le_card
        intro y _
        obtain ⟨i, hi⟩ := h y
        exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, hi⟩⟩
    _ ≤ ∑ i, (univ.filter (good i)).card := card_biUnion_le
    _ ≤ ∑ _i : ι, K := sum_le_sum fun i _ => hK i
    _ = Fintype.card ι * K := by simp

/-! ## 3. The cube law -/

namespace Automaton

section NoTrajectory

variable {σ Y : Type} [DecidableEq Y] (a : Automaton σ Y Bool Y)

/-- **The trajectory of "no"**: the state after `j` answers "no", from `x`. -/
def trajNo (x : σ) (j : ℕ) : σ := (fun z => a.δ z false)^[j] x

/-- What a state contributes: if it stops, what it returns; if not, what it asks. -/
def contribution (x : σ) : Y := (a.output x).getD (a.query x)

variable {a}

omit [DecidableEq Y] in
theorem trajNo_succ (x : σ) (j : ℕ) : a.trajNo x (j + 1) = a.trajNo (a.δ x false) j :=
  Function.iterate_succ_apply _ _ _

/-- **Where a solution is found**: on the trajectory of "no", at some `j ≤ t`, either returned or
asked by a state that does not stop. -/
theorem found_on_trajNo (y : Y) : ∀ (t : ℕ) (x : σ), a.run (equalTo y) t x = some y →
    ∃ j ≤ t, (∀ i < j, a.output (a.trajNo x i) = none) ∧
      (a.output (a.trajNo x j) = some y ∨
        (a.output (a.trajNo x j) = none ∧ a.query (a.trajNo x j) = y))
  | 0, x, h => ⟨0, le_rfl, fun _ hi => absurd hi (Nat.not_lt_zero _), Or.inl h⟩
  | t + 1, x, h => by
      cases hs : a.output x with
      | some z =>
          rw [run_some hs] at h
          exact ⟨0, Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _),
            Or.inl (by rw [← h]; exact hs)⟩
      | none =>
          by_cases hq : a.query x = y
          · exact ⟨0, Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _), Or.inr ⟨hs, hq⟩⟩
          · have hf : equalTo y (a.query x) = false := by simp [equalTo, hq]
            rw [run_none hs, hf] at h
            obtain ⟨j, hj, hpre, hfin⟩ := found_on_trajNo y t _ h
            refine ⟨j + 1, by omega, fun i hi => ?_, by rwa [trajNo_succ]⟩
            cases i with
            | zero => exact hs
            | succ i => rw [trajNo_succ]; exact hpre i (by omega)

end NoTrajectory

section Found

variable {σ Y : Type} [DecidableEq Y] [Fintype Y] (a : Automaton σ Y Bool Y)

/-- The solutions the automaton finds within `t` queries. -/
def found (t : ℕ) : Finset Y := univ.filter fun y => a.run (equalTo y) t a.start = some y

variable {a}

/-- **The bound of time**: at most `t + 1` solutions. -/
theorem found_le_time (t : ℕ) : (a.found t).card ≤ t + 1 := by
  calc (a.found t).card ≤ ((range (t + 1)).image fun j => a.contribution (a.trajNo a.start j)).card := by
        apply card_le_card
        intro y hy
        obtain ⟨j, hj, -, hfin⟩ := found_on_trajNo y t a.start (mem_filter.1 hy).2
        refine mem_image.2 ⟨j, mem_range.2 (by omega), ?_⟩
        rcases hfin with h | ⟨h, hq⟩
        · simp [contribution, h]
        · simp [contribution, h, hq]
    _ ≤ (range (t + 1)).card := card_image_le
    _ = t + 1 := card_range _

omit [DecidableEq Y] [Fintype Y] in
/-- The first stop on the trajectory of "no" is one. -/
theorem first_stop_unique {x : σ} {y y' : Y} {j j' : ℕ}
    (h1 : ∀ i < j, a.output (a.trajNo x i) = none) (h2 : a.output (a.trajNo x j) = some y)
    (h1' : ∀ i < j', a.output (a.trajNo x i) = none) (h2' : a.output (a.trajNo x j') = some y') :
    y = y' := by
  rcases lt_trichotomy j j' with h | rfl | h
  · rw [h1' j h] at h2; cases h2
  · rw [h2] at h2'; exact Option.some.inj h2'
  · rw [h1 j' h] at h2'; cases h2'

/-- **The bound of space**: `2 · |found| ≤ |σ| + 1`. Every solution found needs a state that returns
it, and all but one (the first stop of the trajectory of "no") need also a state that does not stop
and asks it. -/
theorem found_le_space [Fintype σ] (t : ℕ) : 2 * (a.found t).card ≤ Fintype.card σ + 1 := by
  classical
  set F := a.found t
  let stop : Y → Prop := fun y => ∃ j, (∀ i < j, a.output (a.trajNo a.start i) = none) ∧
    a.output (a.trajNo a.start j) = some y
  have hA : (F.filter stop).card ≤ 1 := by
    refine card_le_one.2 fun y hy y' hy' => ?_
    obtain ⟨j, h1, h2⟩ := (mem_filter.1 hy).2
    obtain ⟨j', h1', h2'⟩ := (mem_filter.1 hy').2
    exact first_stop_unique h1 h2 h1' h2'
  have hB : (F.filter fun y => ¬ stop y).card ≤ (univ.filter fun x : σ => a.output x = none).card := by
    calc _ ≤ ((univ.filter fun x : σ => a.output x = none).image a.query).card := by
          apply card_le_card
          intro y hy
          obtain ⟨hyF, hna⟩ := mem_filter.1 hy
          obtain ⟨j, -, hpre, hfin⟩ := found_on_trajNo y t a.start (mem_filter.1 hyF).2
          rcases hfin with h | ⟨h, hq⟩
          · exact absurd ⟨j, hpre, h⟩ hna
          · exact mem_image.2 ⟨_, mem_filter.2 ⟨mem_univ _, h⟩, hq⟩
      _ ≤ _ := card_image_le
  have hC : F.card ≤ (univ.filter fun x : σ => ¬ a.output x = none).card := by
    have hex : ∀ y ∈ F, ∃ x, a.output x = some y := fun y hy => run_output (mem_filter.1 hy).2
    let f : Y → σ := fun y => if h : ∃ x, a.output x = some y then h.choose else a.start
    have hf : ∀ y ∈ F, a.output (f y) = some y := fun y hy => by
      simp only [f, dite_eq_left_of_eq_true (eq_true (hex y hy))]; exact (hex y hy).choose_spec
    refine card_le_card_of_injOn f (fun y hy => ?_) (fun y hy y' hy' he => ?_)
    · simp [hf y hy]
    · have := hf y hy; rw [he, hf y' hy'] at this; exact (Option.some.inj this).symm
  have hsplit := card_filter_add_card_filter_not (s := F) stop
  have hsig := card_filter_add_card_filter_not (s := (univ : Finset σ)) (fun x => a.output x = none)
  rw [card_univ] at hsig
  omega

/-- With `|σ| ≤ 2^S`, at most `min (t + 1) 2^(S − 1)` solutions. -/
theorem found_le_bits [Fintype σ] {S : ℕ} (hσ : Fintype.card σ ≤ 2 ^ S) (t : ℕ) :
    (a.found t).card ≤ min (t + 1) (2 ^ (S - 1)) := by
  refine le_min (found_le_time t) ?_
  have h := found_le_space (a := a) t
  cases S with
  | zero => simp at hσ ⊢; omega
  | succ S => rw [pow_succ] at hσ; simp; omega

end Found

section General

variable {σ Q R Y : Type} [DecidableEq Y] [Fintype Y] {a : Automaton σ Q R Y}

/-- With any verifier, at most `|σ|` solutions: each one is returned by a different state. -/
theorem found_general_le_states [Fintype σ] (O : Y → Q → R) (t : ℕ) :
    (univ.filter fun y => a.run (O y) t a.start = some y).card ≤ Fintype.card σ := by
  classical
  have hex : ∀ y ∈ univ.filter (fun y => a.run (O y) t a.start = some y), ∃ x, a.output x = some y :=
    fun y hy => run_output (mem_filter.1 hy).2
  let f : Y → σ := fun y => if h : ∃ x, a.output x = some y then h.choose else a.start
  have hf : ∀ y ∈ univ.filter (fun y => a.run (O y) t a.start = some y), a.output (f y) = some y :=
    fun y hy => by
      simp only [f, dite_eq_left_of_eq_true (eq_true (hex y hy))]; exact (hex y hy).choose_spec
  calc _ ≤ (univ : Finset σ).card := card_le_card_of_injOn f (fun _ _ => mem_univ _)
          (fun y hy y' hy' he => by
            have := hf y hy; rw [he, hf y' hy'] at this; exact (Option.some.inj this).symm)
    _ = Fintype.card σ := card_univ

omit [Fintype Y] in
/-- With answers of `b` bits, at most `(2^b)^t` solutions. -/
theorem found_general [Fintype R] {b : ℕ} (hR : Fintype.card R ≤ 2 ^ b) (O : Y → Q → R) :
    ∀ (t : ℕ) (x : σ) (T : Finset Y), (T.filter fun y => a.run (O y) t x = some y).card ≤ (2 ^ b) ^ t
  | 0, x, T => by
      calc _ ≤ ((a.output x).toFinset).card := card_le_card fun y hy => by
              rw [mem_filter] at hy; simp [← hy.2, run_zero]
        _ ≤ 1 := by rw [Option.card_toFinset]; cases a.output x <;> simp
        _ ≤ _ := Nat.one_le_pow _ _ (by positivity)
  | t + 1, x, T => by
      classical
      cases hs : a.output x with
      | some z =>
          calc _ ≤ ({z} : Finset Y).card := card_le_card fun y hy => by
                  rw [mem_filter, run_some hs] at hy; simp [Option.some.inj hy.2]
            _ = 1 := card_singleton z
            _ ≤ _ := Nat.one_le_pow _ _ (by positivity)
      | none =>
          calc _ ≤ (univ.biUnion fun r : R => (T.filter fun y => O y (a.query x) = r).filter
                  fun y => a.run (O y) t (a.δ x r) = some y).card := by
                apply card_le_card
                intro y hy
                rw [mem_filter, run_none hs] at hy
                simp only [mem_biUnion, mem_univ, true_and, mem_filter]
                exact ⟨_, ⟨hy.1, rfl⟩, hy.2⟩
            _ ≤ ∑ r : R, ((T.filter fun y => O y (a.query x) = r).filter
                  fun y => a.run (O y) t (a.δ x r) = some y).card := card_biUnion_le
            _ ≤ ∑ _r : R, (2 ^ b) ^ t := sum_le_sum fun r _ => found_general hR O t _ _
            _ = Fintype.card R * (2 ^ b) ^ t := by simp
            _ ≤ 2 ^ b * (2 ^ b) ^ t := Nat.mul_le_mul_right _ hR
            _ = (2 ^ b) ^ (t + 1) := (pow_succ' _ _).symm

end General

end Automaton

/-- **The cube law** (yes/no verifier): with `|P| ≤ 2^L` programs, `|C| ≤ 2^s` advice strings and
automata of `|σ| ≤ 2^S` states that solve in `t` queries, `N ≤ 2^L · 2^s · min (t + 1) 2^(S − 1)`.
Time without memory to count it does not pay. -/
theorem cube_law {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (A : P → C → Automaton σ Y Bool Y) (h : Solves equalTo A t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S - 1)) := by
  have hc := cover (ι := P × C)
    (fun pc y => (A pc.1 pc.2).run (equalTo y) t (A pc.1 pc.2).start = some y)
    (min (t + 1) (2 ^ (S - 1)))
    (fun pc => Automaton.found_le_bits hσ t) (fun y => by obtain ⟨p, c, hy⟩ := h y; exact ⟨(p, c), hy⟩)
  rw [Fintype.card_prod] at hc
  calc Fintype.card Y ≤ Fintype.card P * Fintype.card C * min (t + 1) (2 ^ (S - 1)) := hc
    _ ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S - 1)) := by gcongr

/-- **The cube law with a verifier of `b` bits**: `N ≤ 2^L · 2^s · min 2^(b t) 2^S`. -/
theorem cube_law_general {P C σ Q R Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype R]
    [Fintype Y] {L s S b t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (hR : Fintype.card R ≤ 2 ^ b) (O : Y → Q → R)
    (A : P → C → Automaton σ Q R Y) (h : Solves O A t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (2 ^ (b * t)) (2 ^ S) := by
  classical
  have hc := cover (ι := P × C)
    (fun pc y => (A pc.1 pc.2).run (O y) t (A pc.1 pc.2).start = some y) (min (2 ^ (b * t)) (2 ^ S))
    (fun pc => le_min (by rw [pow_mul]; exact Automaton.found_general hR O t _ _)
      ((Automaton.found_general_le_states O t).trans hσ))
    (fun y => by obtain ⟨p, c, hy⟩ := h y; exact ⟨(p, c), hy⟩)
  rw [Fintype.card_prod] at hc
  calc Fintype.card Y ≤ Fintype.card P * Fintype.card C * min (2 ^ (b * t)) (2 ^ S) := hc
    _ ≤ _ := by gcongr

/-! ## 4. Time translation: the charge, and the clock paid in memory -/

/-- **An automaton with a clock**: query, transition and output read also a time register `κ`,
which starts at `clock0` and advances with `tick`. -/
structure ClockedAutomaton (κ σ Q R Y : Type) where
  /-- The initial state. -/
  start : σ
  /-- The initial value of the clock. -/
  clock0 : κ
  /-- The clock advances with each query (it may look at the state). -/
  tick : κ → σ → κ
  /-- The query, which may read the clock. -/
  query : κ → σ → Q
  /-- The transition, which may read the clock. -/
  δ : κ → σ → R → σ
  /-- The output, which may read the clock. -/
  output : κ → σ → Option Y

namespace ClockedAutomaton

variable {κ σ Q R Y : Type}

/-- The run with at most `t` queries, from the clock value `k` and the state `x`. -/
def run (a : ClockedAutomaton κ σ Q R Y) (O : Q → R) : ℕ → κ → σ → Option Y
  | 0, k, x => a.output k x
  | t + 1, k, x =>
    match a.output k x with
    | some y => some y
    | none => run a O t (a.tick k x) (a.δ k x (O (a.query k x)))

/-- **Homogenize**: the clock becomes part of the state. States `σ × κ`. -/
def homogenize (a : ClockedAutomaton κ σ Q R Y) : Automaton (σ × κ) Q R Y where
  start := (a.start, a.clock0)
  query := fun z => a.query z.2 z.1
  δ := fun z r => (a.δ z.2 z.1 r, a.tick z.2 z.1)
  output := fun z => a.output z.2 z.1

/-- **The clock is paid in memory**: the homogeneous run from `(x, k)` is the clocked run from the
clock `k` and the state `x`. -/
theorem homogenize_run (a : ClockedAutomaton κ σ Q R Y) (O : Q → R) :
    ∀ (t : ℕ) (k : κ) (x : σ), (homogenize a).run O t (x, k) = a.run O t k x
  | 0, k, x => rfl
  | t + 1, k, x => by
      simp only [run, Automaton.run, homogenize]
      cases a.output k x with
      | some y => rfl
      | none => exact homogenize_run a O t _ _

end ClockedAutomaton

/-- The clock of `c` bits: the step modulo `2^c`. -/
def tickMod (c : ℕ) (k : Fin (2 ^ c)) : Fin (2 ^ c) := ⟨(k.val + 1) % 2 ^ c, Nat.mod_lt _ (by positivity)⟩

/-- The price of a clock of `c` bits: `|σ × Fin (2^c)| = |σ| · 2^c`. -/
theorem card_clock_bits (σ : Type) [Fintype σ] (c : ℕ) :
    Fintype.card (σ × Fin (2 ^ c)) = Fintype.card σ * 2 ^ c := by
  simp

/-- **The cube law with a clock**: with `|σ| ≤ 2^S` and a clock of `|κ| ≤ 2^c` values,
`N ≤ 2^L · 2^s · min (t + 1) 2^(S + c − 1)`. The clock enters the space axis. -/
theorem cube_law_clock {P C κ σ Y : Type} [Fintype P] [Fintype C] [Fintype κ] [Fintype σ]
    [Fintype Y] [DecidableEq Y] {L s S c t : ℕ} (hP : Fintype.card P ≤ 2 ^ L)
    (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S) (hκ : Fintype.card κ ≤ 2 ^ c)
    (A : P → C → ClockedAutomaton κ σ Y Bool Y)
    (h : ∀ y, ∃ p c, (A p c).run (equalTo y) t (A p c).clock0 (A p c).start = some y) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S + c - 1)) := by
  have hσκ : Fintype.card (σ × κ) ≤ 2 ^ (S + c) := by
    rw [Fintype.card_prod, pow_add]; exact Nat.mul_le_mul hσ hκ
  refine cube_law hP hC hσκ (fun p c => (A p c).homogenize) fun y => ?_
  obtain ⟨p, c, hy⟩ := h y
  exact ⟨p, c, (ClockedAutomaton.homogenize_run (A p c) (equalTo y) t _ _).trans hy⟩

section Charge

variable {σ Q R Y : Type}

/-- **The Noether charge of time translation.** Two runs of a homogeneous automaton against the same
verifier that reach the same state, one at time `i` and the other at time `j`, without having
stopped, continue identically: the output with any remaining budget, and all later states. -/
theorem noether_charge (a : Automaton σ Q R Y) (O : Q → R) {x x' : σ} {i j : ℕ}
    (hi : ∀ k < i, a.output ((a.step O)^[k] x) = none)
    (hj : ∀ k < j, a.output ((a.step O)^[k] x') = none)
    (h : (a.step O)^[i] x = (a.step O)^[j] x') (t : ℕ) :
    a.run O (i + t) x = a.run O (j + t) x' ∧ (a.step O)^[i + t] x = (a.step O)^[j + t] x' := by
  refine ⟨by rw [run_split a O i t x hi, run_split a O j t x' hj, h], ?_⟩
  rw [add_comm i, add_comm j, Function.iterate_add_apply, Function.iterate_add_apply, h]

/-- **A homogeneous run does not know the time**: if it comes back at time `j` to the state it had
at time `i`, without having stopped, it continues from `i` and from `j` in the same way. -/
theorem does_not_know_the_time (a : Automaton σ Q R Y) (O : Q → R) {x : σ} {i j : ℕ}
    (hj : ∀ k < j, a.output ((a.step O)^[k] x) = none) (hij : i ≤ j)
    (h : (a.step O)^[i] x = (a.step O)^[j] x) (t : ℕ) : a.run O (i + t) x = a.run O (j + t) x :=
  (noether_charge a O (fun k hk => hj k (by omega)) hj h t).1

end Charge

/-! ### The control: the price of the clock is exact -/

/-- The clock with cap `T`: the step saturated at `T`. -/
def tickCap (T : ℕ) (k : Fin (T + 1)) : Fin (T + 1) := ⟨min (k.val + 1) T, by omega⟩

/-- **A sweep with two states and a clock of two bits**: the state says whether it has heard "yes";
the clock says what to ask and what to return. -/
def clockedSweep : ClockedAutomaton (Fin 4) Bool (Fin 4) Bool (Fin 4) where
  start := false
  clock0 := 0
  tick := fun k _ => tickCap 3 k
  query := fun k _ => k
  δ := fun _ b r => b || r
  output := fun k b => if b then some (k - 1) else if k = 3 then some 3 else none

theorem clockedSweep_solves :
    ∀ y : Fin 4, clockedSweep.run (equalTo y) 3 clockedSweep.clock0 clockedSweep.start = some y := by
  decide

/-- **The price of the clock, exact.** The clocked sweep (2 states, `S = 1`) finds 4 candidates in 3
queries. The cube law without the clock asks `4 ≤ 1` and fails; with the 2 bits of the clock it asks
`4 ≤ min 4 2^(1 + 2 − 1) = 4`, which holds (and follows from `cube_law_clock`); with one bit of clock
less it would ask `4 ≤ 2`. -/
theorem clock_price_control :
    ¬ (Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (3 + 1) (2 ^ (1 - 1))) ∧
      Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (3 + 1) (2 ^ (1 + 2 - 1)) ∧
      ¬ (Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (3 + 1) (2 ^ (1 + 1 - 1))) := by
  refine ⟨by simp, ?_, by simp⟩
  exact cube_law_clock (P := Unit) (C := Unit) (κ := Fin 4) (L := 0) (s := 0) (S := 1) (c := 2)
    (by simp) (by simp) (by simp) (by simp) (fun _ _ => clockedSweep)
    (fun y => ⟨(), (), clockedSweep_solves y⟩)

/-- **With a clock, time leaves a trace.** In the homogenized sweep against the verifier of `3`, the
state without the clock is `false` at step `0` and again at step `3`, but at step `0` it returns
nothing and at step `3` it returns `3`: what the homogeneous charge forbids happens here because the
clock is kept in the state, `(false, 0) ≠ (false, 3)`. -/
theorem clock_leaves_trace :
    ((clockedSweep.homogenize.step (equalTo 3))^[0] clockedSweep.homogenize.start).1 = false ∧
      ((clockedSweep.homogenize.step (equalTo 3))^[3] clockedSweep.homogenize.start).1 = false ∧
      clockedSweep.homogenize.run (equalTo 3) 0
          ((clockedSweep.homogenize.step (equalTo 3))^[0] clockedSweep.homogenize.start) = none ∧
      clockedSweep.homogenize.run (equalTo 3) 0
          ((clockedSweep.homogenize.step (equalTo 3))^[3] clockedSweep.homogenize.start) = some 3 := by
  decide

/-! ## 5. Bounded memory: halt or cycle -/

section Orbit

variable {β : Type*} [Fintype β] (f : β → β) (x : β)

/-- **Pigeonhole**: in the first `card β + 1` steps the orbit repeats a value. -/
theorem orbit_repeats : ∃ i j, i < j ∧ j ≤ Fintype.card β ∧ f^[i] x = f^[j] x := by
  have hc : Fintype.card β < Fintype.card (Fin (Fintype.card β + 1)) := by simp
  obtain ⟨a, b, hab, he⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card β + 1) => f^[k] x) hc
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact ⟨a, b, h, Nat.lt_succ_iff.1 b.2, he⟩
  · exact ⟨b, a, h, Nat.lt_succ_iff.1 a.2, he.symm⟩

/-- **The orbit is eventually periodic**, with preperiod plus period at most `card β`. -/
theorem eventually_periodic :
    ∃ i p, 0 < p ∧ i + p ≤ Fintype.card β ∧ ∀ n, i ≤ n → f^[n + p] x = f^[n] x := by
  obtain ⟨i, j, hij, hj, he⟩ := orbit_repeats f x
  refine ⟨i, j - i, by omega, by omega, fun n hn => ?_⟩
  have e1 : n + (j - i) = (n - i) + j := by omega
  have e2 : n = (n - i) + i := by omega
  rw [e1, Function.iterate_add_apply, ← he, ← Function.iterate_add_apply, ← e2]

/-- Every value of the orbit already appeared in the first `card β` steps. -/
theorem orbit_in_prefix (k : ℕ) : ∃ k' < Fintype.card β, f^[k] x = f^[k'] x := by
  obtain ⟨i, p, hp, hip, hper⟩ := eventually_periodic f x
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < i + p
    · exact ⟨k, by omega, rfl⟩
    · obtain ⟨k', hk', e⟩ := ih (k - p) (by omega)
      refine ⟨k', hk', ?_⟩
      rw [← e, ← hper (k - p) (by omega), show k - p + p = k by omega]

end Orbit

section Halting

variable {σ : Type*}

/-- One step of a system that may halt: `δ s = none` is the halt; `none` stays `none`. -/
def haltStep (δ : σ → Option σ) : Option σ → Option σ := fun c => c.bind δ

/-- The trace from the state `s`. -/
def trace (δ : σ → Option σ) (s : σ) : ℕ → Option σ := fun n => (haltStep δ)^[n] (some s)

theorem iterate_haltStep_none (δ : σ → Option σ) : ∀ m, (haltStep δ)^[m] none = none
  | 0 => rfl
  | m + 1 => by rw [Function.iterate_succ_apply]; exact iterate_haltStep_none δ m

variable [Fintype σ]

/-- **With finite memory, halting is halting soon**: within the first `card σ + 1` steps. -/
theorem halts_iff_bounded (δ : σ → Option σ) (s : σ) :
    (∃ n, trace δ s n = none) ↔ ∃ n < Fintype.card σ + 1, trace δ s n = none := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨k', hk', e⟩ := orbit_in_prefix (haltStep δ) (some s) k
    refine ⟨k', by simpa using hk', ?_⟩
    simp only [trace] at hk ⊢
    rw [← e, hk]
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

/-- **Halt or cycle**: either the system halts within `|σ|` steps, or it never halts and its trace
is eventually periodic, with preperiod plus period at most `|σ| + 1`. -/
theorem halt_or_cycle (δ : σ → Option σ) (s : σ) :
    (∃ n ≤ Fintype.card σ, trace δ s n = none) ∨
    ((∀ n, trace δ s n ≠ none) ∧
      ∃ i p, 0 < p ∧ i + p ≤ Fintype.card σ + 1 ∧ ∀ n, i ≤ n → trace δ s (n + p) = trace δ s n) := by
  by_cases h : ∃ n, trace δ s n = none
  · obtain ⟨n, hn, e⟩ := (halts_iff_bounded δ s).1 h
    exact Or.inl ⟨n, by omega, e⟩
  · refine Or.inr ⟨fun n hn => h ⟨n, hn⟩, ?_⟩
    obtain ⟨i, p, hp, hip, hper⟩ := eventually_periodic (haltStep δ) (some s)
    rw [Fintype.card_option] at hip
    exact ⟨i, p, hp, hip, fun n hn => hper n hn⟩

/-- **With `S` bits, halting is halting before `2^S`.** -/
theorem halts_before_two_pow (δ : σ → Option σ) (s₀ : σ) {S : ℕ} (hc : Fintype.card σ ≤ 2 ^ S)
    (hp : ∃ n, trace δ s₀ n = none) : ∃ n ≤ 2 ^ S, trace δ s₀ n = none := by
  obtain ⟨n, hn, e⟩ := (halts_iff_bounded δ s₀).1 hp
  exact ⟨n, by omega, e⟩

end Halting

/-! ## 6. The CHT tower, piece 1: homogeneity with its costs gives `2^S` -/

section Tower

variable {σ Q R Y : Type}

/-- **A homogeneous automaton with its verifier fixed, as a deterministic system**: `none` once the
state answers. -/
def system (a : Automaton σ Q R Y) (O : Q → R) : σ → Option σ := fun x =>
  match a.output x with
  | some _ => none
  | none => some (a.δ x (O (a.query x)))

/-- The trace of the system goes out at `n + 1` exactly when the automaton answers with budget `n`. -/
theorem trace_system (a : Automaton σ Q R Y) (O : Q → R) :
    ∀ (n : ℕ) (x : σ), trace (system a O) x (n + 1) = none ↔ (a.run O n x).isSome
  | 0, x => by
    change system a O x = none ↔ (a.output x).isSome
    unfold system
    cases a.output x <;> simp
  | n + 1, x => by
    have e : trace (system a O) x (n + 1 + 1) = (haltStep (system a O))^[n + 1] (system a O x) := by
      simp only [trace, Function.iterate_succ_apply]; rfl
    rw [e]
    cases hs : a.output x with
    | some y =>
      simp only [system, hs, iterate_haltStep_none, Automaton.run_some hs, Option.isSome_some]
    | none =>
      simp only [system, hs, Automaton.run_none hs]
      exact trace_system a O n _

/-- **The CHT with its costs**: a homogeneous automaton of `S` bits (`|σ| ≤ 2^S`) that answers,
answers in fewer than `2^S` queries. If it has not answered by then it repeats a state, and by the
Noether charge it never answers. -/
theorem cht_time [Fintype σ] (a : Automaton σ Q R Y) (O : Q → R) {S : ℕ}
    (hσ : Fintype.card σ ≤ 2 ^ S) {t : ℕ} {x : σ} {y : Y} (h : a.run O t x = some y) :
    ∃ m < 2 ^ S, a.run O m x = some y := by
  have hp : ∃ n, trace (system a O) x n = none := ⟨t + 1, (trace_system a O t x).2 (by simp [h])⟩
  obtain ⟨n, hn, e⟩ := halts_before_two_pow (system a O) x hσ hp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => simp [trace] at e
    | succ m => exact ⟨m, rfl⟩
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 ((trace_system a O m x).1 e)
  have h1 := Automaton.run_mono (a := a) t hy'
  have h2 := Automaton.run_mono (a := a) m h
  rw [Nat.add_comm, h2] at h1
  cases h1
  exact ⟨m, by omega, hy'⟩

/-- **The clock is paid in memory, and the CHT charges the total**: a clocked automaton with
`|κ| ≤ 2^c` clock values and `|σ| ≤ 2^S` states that answers, answers in fewer than `2^(S + c)`
queries. With `c = O(log n)` the factor is a polynomial: a logarithmic clock does not change the
class. -/
theorem clock_in_memory {κ : Type} [Fintype κ] [Fintype σ] (a : ClockedAutomaton κ σ Q R Y)
    (O : Q → R) {S c : ℕ} (hσ : Fintype.card σ ≤ 2 ^ S) (hκ : Fintype.card κ ≤ 2 ^ c) {t : ℕ} {y : Y}
    (h : a.run O t a.clock0 a.start = some y) :
    ∃ m < 2 ^ (S + c), a.run O m a.clock0 a.start = some y := by
  have hσκ : Fintype.card (σ × κ) ≤ 2 ^ (S + c) := by
    rw [Fintype.card_prod, pow_add]; exact Nat.mul_le_mul hσ hκ
  rw [← ClockedAutomaton.homogenize_run] at h
  obtain ⟨m, hm, e⟩ := cht_time a.homogenize O hσκ h
  exact ⟨m, hm, (ClockedAutomaton.homogenize_run a O m _ _).symm.trans e⟩

end Tower

section Counter

/-- **The counter**: states `0, …, 2^n − 1` (the candidate it tries), `2^n` (none) and `2^n + 1`
(found). It asks the verifier about candidate `x`; on "yes" it returns `true`, on "no" it moves on. -/
def counter (n : ℕ) : Automaton (Fin (2 ^ n + 2)) (Fin (2 ^ n)) Bool Bool where
  start := ⟨0, by positivity⟩
  query x := ⟨x.val % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
  δ x r := if r then ⟨2 ^ n + 1, by omega⟩
    else ⟨min (x.val + 1) (2 ^ n), Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩
  output x := if x.val = 2 ^ n then some false else if x.val = 2 ^ n + 1 then some true else none

theorem counter_output {n i : ℕ} (hi : i < 2 ^ n) : (counter n).output ⟨i, by omega⟩ = none := by
  have h1 : i ≠ 2 ^ n := by omega
  have h2 : i ≠ 2 ^ n + 1 := by omega
  simp [counter, h1, h2]

theorem counter_run {n : ℕ} (O : Fin (2 ^ n) → Bool) :
    ∀ (m i : ℕ) (hi : i + m = 2 ^ n), (counter n).run O m ⟨i, by omega⟩ =
      some (decide (∃ k : Fin (2 ^ n), i ≤ k.val ∧ O k = true))
  | 0, i, hi => by
    simp only [Automaton.run_zero, counter, show i = 2 ^ n by omega, ite_true, Option.some.injEq]
    symm; simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro k hk; exact absurd k.isLt (by omega)
  | m + 1, i, hi => by
    have hs : (counter n).output ⟨i, by omega⟩ = none := counter_output (by omega)
    rw [Automaton.run_none hs]
    have hq : (counter n).query ⟨i, by omega⟩ = ⟨i, by omega⟩ := by
      simp only [counter, Fin.mk.injEq]; exact Nat.mod_eq_of_lt (by omega)
    rw [hq]
    cases hO : O ⟨i, by omega⟩
    · have hd : (counter n).δ ⟨i, by omega⟩ false = ⟨i + 1, by omega⟩ := by
        simp only [counter, Bool.false_eq_true, ite_false, Fin.mk.injEq]; omega
      rw [hd, counter_run O m (i + 1) (by omega)]
      congr 1
      apply decide_eq_decide.2
      constructor
      · rintro ⟨k, hk, hk'⟩; exact ⟨k, by omega, hk'⟩
      · rintro ⟨k, hk, hk'⟩
        refine ⟨k, ?_, hk'⟩
        rcases Nat.eq_or_lt_of_le hk with e | e
        · exfalso; have : k = ⟨i, by omega⟩ := Fin.ext e.symm
          rw [this, hO] at hk'; exact Bool.false_ne_true hk'
        · omega
    · have hd : (counter n).δ ⟨i, by omega⟩ true = ⟨2 ^ n + 1, by omega⟩ := by simp [counter]
      rw [hd, Automaton.run_some (y := true) (by simp [counter]) m]
      simp only [Option.some.injEq]
      symm; simp only [decide_eq_true_eq]
      exact ⟨⟨i, by omega⟩, le_rfl, hO⟩

/-- **The counter decides in `2^n` queries** whether one of the `2^n` candidates is accepted. -/
theorem counter_decides {n : ℕ} (O : Fin (2 ^ n) → Bool) :
    (counter n).run O (2 ^ n) (counter n).start = some (decide (∃ k, O k = true)) := by
  rw [show (counter n).start = ⟨0, by positivity⟩ from rfl, counter_run O (2 ^ n) 0 (by omega)]
  simp

theorem counter_slow (n : ℕ) : ∀ (m i : ℕ) (hi : i + m < 2 ^ n),
    (counter n).run (fun _ => false) m ⟨i, by omega⟩ = none
  | 0, i, hi => by
    rw [Automaton.run_zero]; exact counter_output (by omega)
  | m + 1, i, hi => by
    have hs : (counter n).output ⟨i, by omega⟩ = none := counter_output (by omega)
    rw [Automaton.run_none hs]
    have hd : (counter n).δ ⟨i, by omega⟩ false = ⟨i + 1, by omega⟩ := by
      simp only [counter, Bool.false_eq_true, ite_false, Fin.mk.injEq]; omega
    rw [hd]
    exact counter_slow n m (i + 1) (by omega)

/-- **And not before**: against the verifier that always says "no", `2^n − 1` queries are not
enough. The counter spends all the time that the CHT allows its memory. -/
theorem counter_not_before (n : ℕ) :
    (counter n).run (fun _ => false) (2 ^ n - 1) (counter n).start = none :=
  counter_slow n _ 0 (by have := Nat.one_le_two_pow (n := n); omega)

/-- **The memory of the counter**: `n + 1` bits (for `n ≥ 1`). -/
theorem card_counter {n : ℕ} (hn : 1 ≤ n) : Fintype.card (Fin (2 ^ n + 2)) ≤ 2 ^ (n + 1) := by
  simp only [Fintype.card_fin, pow_succ]
  have : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- **The CHT gives exponential time and no less.** For every `n ≥ 1` there is a homogeneous automaton
with `n + 1` bits of memory that answers within the CHT budget `2^(n + 1)`, but that does not answer
in `2^n − 1` queries: homogeneity with its memory bounds the time by `2^S`, and the bound is not a
polynomial in `S`. -/
theorem cht_exponential_not_polynomial (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (Fin (2 ^ n + 2)) ≤ 2 ^ (n + 1) ∧
      (∀ O, ∃ b, ∃ m < 2 ^ (n + 1), (counter n).run O m (counter n).start = some b) ∧
      (counter n).run (fun _ => false) (2 ^ n - 1) (counter n).start = none := by
  refine ⟨card_counter hn, fun O => ?_, counter_not_before n⟩
  exact ⟨_, cht_time (counter n) O (card_counter hn) (counter_decides O)⟩

end Counter

/-! ## 7. The first localization, complete -/

/-- **The first localization, complete: the dynamics does not carry the arrow.**

The dynamics has two symmetries of time, and neither decides the arrow.

1. **Time reversal and its charge, information.** For any step `f` on a finite set, a quantity is
   conserved if and only if its phases commute with Koopman's operator (discrete Noether), and
   Koopman's operator is unitary if and only if `f` is bijective. A reversible dynamics keeps the size
   of every set of states: it neither creates nor destroys information.
2. **Time translation and its charge, blindness to the clock.** A homogeneous automaton that comes
   back to a state does not know the time: it continues identically. A clock is paid in memory: the
   clocked automaton is a homogeneous one on `σ × κ`, with the same runs. With `S` bits of memory,
   whatever is answered is answered in fewer than `2^S` steps (the CHT with its costs), and the
   exponential bound is attained.
3. **Neither decides the arrow.** These facts hold in every model and need no hypothesis, while the
   arrow holds in one model with the closure properties and fails in another
   (`arrow_independent`). In `M`, the arrow is equivalent to the decision hypothesis, which is about
   erasing the boundary down to one bit, not about the dynamics. -/
theorem localization_one (M : Model) :
    (∀ (σ : Type) [Fintype σ] (f : σ → σ) (Q : σ → ℝ), (Q ∘ f = Q ↔
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
    (M.DecisionHypothesis ↔ M.Arrow) :=
  ⟨fun _ _ f Q => koopman_noether f Q, fun _ _ f => koopman_isometry_iff f,
    fun _ _ D n S => D.card_image_iterate n S,
    fun _ _ _ _ a O _ _ _ t hj hij h => does_not_know_the_time a O hj hij h t,
    fun _ _ _ _ _ a O t k x => a.homogenize_run O t k x,
    fun _ _ _ _ _ a O _ _ _ _ hσ h => cht_time a O hσ h,
    arrow_independent, Model.decisionHypothesis_iff_arrow⟩

/-- **Irreversibility without loss of information.** Under the decision hypothesis, both hold at once:
a reversible dynamics loses no information (Noether, a theorem: it keeps the size of every set of
states, and in Koopman's picture it is unitary), and yet from the one bit "a witness exists" the
witness is not recovered cheaply for every search problem (HD, a hypothesis). The irreversibility
lives in the bit, not in the dynamics. -/
theorem irreversibility_without_loss {M : Model} (h : M.DecisionHypothesis) :
    (∀ (σ : Type) [DecidableEq σ] (D : ReversibleDynamics σ) (n : ℕ) (S : Finset σ),
        (S.image D.step^[n]).card = S.card) ∧
    (∀ (σ : Type) [Fintype σ] (D : ReversibleDynamics σ) (φ : σ → ℂ),
        norm2 (koopman D.step φ) = norm2 φ) ∧
    ¬M.SearchEasy :=
  ⟨fun _ _ D n S => D.card_image_iterate n S, fun _ _ D φ => D.koopman_isometry φ,
    Model.not_searchEasy_of_decision h⟩

end Sagitta.Arrow.Dynamics
