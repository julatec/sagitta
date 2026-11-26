/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import CslibFrontier.Computability.Complexity.Problems.MaxCut
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The Ising ground state is `NP`-complete

The physics of the arrow: **`P = NP` if and only if deciding whether an Ising spin glass has a
configuration of energy at most `t` is in `P`** (`P_eq_NP_iff_ISING_mem_P`). The ground state of
the Ising model without field is MAX-CUT under another name (F. Barahona, *On the computational
complexity of Ising spin glass models*, J. Phys. A 15 (1982)).

## The problem

* An instance (`IsingInstance`) is a list of **couplings** `(u, v, J)`, with sites `u, v : ℕ` and
  `J : ℤ`, and a **threshold** `t : ℤ`. Integers are encoded in signed binary (`encIntBin` of
  cslib-frontier), naturals in binary (`encNat`), the list framed (`encList`): the style of
  `MaxCutInstance`.
* A configuration is a set `S` of sites: `σ_v = +1` if `v ∈ S`, `−1` if not. The **energy** is
  `H_J(σ) = −Σ_e J_e σ_u σ_v` (`energy`). No external field.
* **`ISING`**: the instances with some `S` of energy `≤ t`.

## Results

* `energy_eq` (Barahona's identity): `H(σ) = −Σ J + 2 · cut_J(σ)`.
* `ISING_mem_NP`: the certificate is `S`, as a mask over the endpoints (`subsetVerifier`).
* `maxCut_iff_ising`, `polyTimeReducible_MaxCut_ISING`: with antiferromagnetic couplings
  `J_e = −w_e`, there is a cut of weight `≥ k` iff some `σ` has `H(σ) ≤ W − 2k`.
* `ISING_npComplete`: from `MaxCut_npComplete` of cslib-frontier (Karp, from `Partition`).
* `P_eq_NP_iff_ISING_mem_P` and `ISING_mem_P_iff_SAT_mem_P`.
-/

namespace Sagitta.Arrow.TM.Ising

open Turing.MultiTapeTM Cslib.Complexity ComputableInPolyTime

/-! ## 1. The problem -/

/-- A coupling `J` between the sites `u` and `v`. -/
structure Coupling where
  /-- One site. -/
  u : ℕ
  /-- The other site. -/
  v : ℕ
  /-- The coupling constant (positive: ferromagnetic). -/
  J : ℤ
  deriving DecidableEq, Repr

/-- Couplings are encoded as `(u, v, J)`, all in binary (`J` in sign and magnitude). -/
enc_structure encCoupling : Coupling where
  u : encNat, v : encNat, J : encIntBin

attribute [fun_prop] encCoupling_u_polyTime encCoupling_v_polyTime encCoupling_J_polyTime
  encCoupling_mk_polyTime

/-- An instance of ISING: the couplings and the energy threshold. -/
structure IsingInstance where
  /-- The couplings. -/
  couplings : List Coupling
  /-- The threshold `t`. -/
  t : ℤ
  deriving DecidableEq, Repr

/-- The framed list of couplings followed by the threshold, in binary. -/
enc_structure encIsing : IsingInstance where
  couplings : (encList encCoupling), t : encIntBin

attribute [fun_prop] encIsing_couplings_polyTime encIsing_t_polyTime encIsing_mk_polyTime

/-- The spin of a site: `+1` on the side `true`, `−1` otherwise. -/
def spin (b : Bool) : ℤ := if b then 1 else -1

/-- **The Ising Hamiltonian without field**: `H_J(σ) = −Σ_e J_e σ_u σ_v`. -/
def energy (E : List Coupling) (side : ℕ → Bool) : ℤ :=
  -(E.map fun e => e.J * spin (side e.u) * spin (side e.v)).sum

/-- **ISING** (ground state, decision version): some configuration has energy at most `t`. -/
def ISING : Set IsingInstance :=
  {x | ∃ S : Finset ℕ, energy x.couplings (fun v => decide (v ∈ S)) ≤ x.t}

/-! ## 2. Barahona's identity -/

/-- The coupling `e` crosses the cut `side`. -/
def crosses (side : ℕ → Bool) (e : Coupling) : Bool := side e.u != side e.v

/-- The sum of the couplings: `Σ J`. -/
def totalWeight (E : List Coupling) : ℤ := (E.map Coupling.J).sum

/-- The cut weighted by `J`: the sum of the couplings that cross. -/
def cutJ (E : List Coupling) (side : ℕ → Bool) : ℤ :=
  ((E.filter fun e => crosses side e).map Coupling.J).sum

/-- **Barahona's identity**: `H(σ) = −Σ J + 2 · cut_J(σ)`. A coupling that does not cross
contributes `−J`; one that crosses, `+J = −J + 2J`. -/
theorem energy_eq (E : List Coupling) (side : ℕ → Bool) :
    energy E side = -totalWeight E + 2 * cutJ E side := by
  induction E with
  | nil => simp [energy, totalWeight, cutJ]
  | cons e E ih =>
    have hc : cutJ (e :: E) side = (if crosses side e then e.J else 0) + cutJ E side := by
      unfold cutJ
      rw [List.filter_cons]
      split <;> simp [*]
    have hp : totalWeight (e :: E) = e.J + totalWeight E := by simp [totalWeight]
    have he : energy (e :: E) side =
        -(e.J * spin (side e.u) * spin (side e.v)) + energy E side := by
      simp only [energy, List.map_cons, List.sum_cons]
      ring
    have key : e.J * spin (side e.u) * spin (side e.v) =
        e.J - 2 * (if crosses side e then e.J else 0) := by
      cases hu : side e.u <;> cases hv : side e.v <;> simp [crosses, spin, hu, hv] <;> ring
    rw [he, hc, hp, ih, key]
    ring

/-- The endpoints of the couplings: the energy depends only on their sides. -/
def endpoints (E : List Coupling) : List ℕ := E.flatMap fun e => [e.u, e.v]

theorem length_endpoints (E : List Coupling) : (endpoints E).length = 2 * E.length := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    simp only [endpoints, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem energy_congr {E : List Coupling} {side side' : ℕ → Bool}
    (h : ∀ v ∈ endpoints E, side v = side' v) : energy E side = energy E side' := by
  unfold energy
  congr 2
  refine List.map_congr_left fun e he => ?_
  have h₁ : e.u ∈ endpoints E := List.mem_flatMap.2 ⟨e, he, by simp⟩
  have h₂ : e.v ∈ endpoints E := List.mem_flatMap.2 ⟨e, he, by simp⟩
  rw [h _ h₁, h _ h₂]

/-! ## 3. ISING is in NP -/

/-- Check a configuration, given as the list of sites at `+1`: the energy, computed by Barahona's
identity, does not exceed the threshold. -/
def check (x : IsingInstance) (S : List ℕ) : Bool :=
  decide (-totalWeight x.couplings + (cutJ x.couplings (fun v => decide (v ∈ S)) +
    cutJ x.couplings (fun v => decide (v ∈ S))) ≤ x.t)

theorem check_eq (x : IsingInstance) (S : List ℕ) :
    check x S = decide (energy x.couplings (fun v => decide (v ∈ S)) ≤ x.t) := by
  rw [check, energy_eq, two_mul]

/-- The verifier: choose `S` among the endpoints with a mask and check the energy. -/
def verifier : IsingInstance × List Bool → Bool :=
  subsetVerifier (fun x => endpoints x.couplings) (Function.uncurry check)

theorem computableInPolyTime_check :
    ComputableInPolyTime (Function.uncurry check) (encPair encIsing (encList encNat))
      encBool := by
  unfold Function.uncurry check totalWeight cutJ crosses
  fun_prop

/-- **Computing the energy is polynomial**: the verifier of ISING runs in polynomial time. -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encIsing encBits) encBool :=
  computableInPolyTime_subsetVerifier (encγ := encNat)
    (by unfold endpoints; fun_prop) computableInPolyTime_check

theorem mem_ISING_iff_endpoints {x : IsingInstance} :
    x ∈ ISING ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ endpoints x.couplings) ∧
      energy x.couplings (fun v => decide (v ∈ S)) ≤ x.t := by
  classical
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S.filter (· ∈ endpoints x.couplings), fun v hv => (Finset.mem_filter.1 hv).2, ?_⟩
    rwa [energy_congr (side' := fun v => decide (v ∈ S)) fun v hv => by
      simp [Finset.mem_filter, hv]]
  · rintro ⟨S, -, hS⟩
    exact ⟨S, hS⟩

theorem isVerifier : IsVerifier encIsing (2 * Polynomial.X) verifier ISING := by
  have hset : ISING = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ endpoints x.couplings) ∧
      energy x.couplings (fun v => decide (v ∈ S)) ≤ x.t} :=
    Set.ext fun _ => mem_ISING_iff_endpoints
  rw [hset]
  refine isVerifier_subsetVerifier (fun x => ?_) fun x l hl _ => ?_
  · rw [encIsing_apply]
    have : x.couplings.length ≤ (encIsingFields (x.couplings, x.t)).length :=
      (length_le_length_encList _ _).trans (length_le_encPair_left _ _ (x.couplings, x.t))
    simp only [length_endpoints, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  · simp only [Function.uncurry_apply_pair, check_eq, decide_eq_true_eq, List.mem_toFinset]

/-- **ISING ∈ NP**: the certificate is the configuration. -/
theorem ISING_mem_NP : ISING ∈ NP encIsing :=
  ⟨2 * Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

/-! ## 4. MAX-CUT reduces to ISING -/

/-- **Barahona's reduction**: every edge of weight `w` becomes an antiferromagnetic coupling
`J = −w`, and the threshold is `W − 2k`, with `W` the total weight and `k` the cut bound. -/
def ofMaxCut (x : MaxCutInstance) : IsingInstance :=
  ⟨x.edges.map fun e => ⟨e.u, e.v, -(e.weight : ℤ)⟩,
    ((x.edges.map MaxCut.WeightedEdge.weight).sum : ℤ) - (x.bound : ℤ) - (x.bound : ℤ)⟩

/-- With antiferromagnetic couplings, `H(σ) = W − 2 · cut_w(σ)`. -/
theorem energy_ofMaxCut (E : List MaxCut.WeightedEdge) (side : ℕ → Bool) :
    energy (E.map fun e => (⟨e.u, e.v, -(e.weight : ℤ)⟩ : Coupling)) side =
      ((E.map MaxCut.WeightedEdge.weight).sum : ℤ) - 2 * (MaxCut.cutWeight E side : ℤ) := by
  induction E with
  | nil => simp [energy, MaxCut.cutWeight]
  | cons e E ih =>
    simp only [energy, MaxCut.cutWeight, List.map_cons, List.sum_cons, List.filter_cons,
      List.map_map] at ih ⊢
    cases hu : side e.u <;> cases hv : side e.v <;>
      simp [MaxCut.crosses, hu, hv, spin, Function.comp_def] at ih ⊢ <;>
      linarith

/-- **Barahona, as an equivalence of decision problems**: a cut of weight `≥ k` exists iff a
configuration of energy `≤ W − 2k` exists. -/
theorem maxCut_iff_ising (x : MaxCutInstance) : x ∈ MaxCut ↔ ofMaxCut x ∈ ISING := by
  simp only [MaxCut, ISING, ofMaxCut, Set.mem_ofPred_eq, energy_ofMaxCut]
  refine exists_congr fun S => ?_
  omega

theorem computableInPolyTime_ofMaxCut :
    ComputableInPolyTime ofMaxCut encMaxCut encIsing := by
  unfold ofMaxCut
  fun_prop

/-- MAX-CUT reduces to ISING in polynomial time. -/
theorem polyTimeReducible_MaxCut_ISING : PolyTimeReducible encMaxCut encIsing MaxCut ISING :=
  ⟨ofMaxCut, computableInPolyTime_ofMaxCut, maxCut_iff_ising⟩

/-- **ISING is `NP`-hard.** -/
theorem ISING_npHard : NPHard encIsing ISING :=
  MaxCut_npHard.trans polyTimeReducible_MaxCut_ISING

/-- **ISING is `NP`-complete** (Barahona 1982). -/
theorem ISING_npComplete : NPComplete encIsing ISING :=
  ⟨ISING_mem_NP, ISING_npHard⟩

/-! ## 5. The theorem -/

/-- **`P` versus `NP`, in physics**: `P = NP` (for every encoding, as cslib states it) if and only
if the decision problem of the Ising ground state is in `P`. -/
theorem P_eq_NP_iff_ISING_mem_P :
    (∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc) ↔ ISING ∈ P encIsing := by
  constructor
  · intro h
    rw [h encIsing]
    exact ISING_mem_NP
  · intro h α enc
    exact ISING_npComplete.P_eq_NP_of_mem_P h enc

/-- ISING and SAT stand or fall together: both are `NP`-complete. -/
theorem ISING_mem_P_iff_SAT_mem_P : ISING ∈ P encIsing ↔ SAT ∈ P encCNF :=
  ISING_npComplete.mem_P_iff_mem_P CookLevin.SAT_npComplete

end Sagitta.Arrow.TM.Ising
