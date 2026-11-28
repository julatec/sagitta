import Sagitta.Map.Informacion.Transferencia
import CslibFrontier.Computability.Complexity.Problems.MaxCut
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# El hamiltoniano y P contra NP

La tercera torre. Las dos primeras ya tienen su traducción probada: la aritmética
(`npDistintoCoNP_iff_formulas`, en `SigmaFagin/Palabras`) y el tiempo con la información (`sat_enP_iff_kt`, en
`Informacion/BuscarPolinomial`). Esta es la de la física: **`P = NP` si y solo si decidir si un vidrio de
Ising tiene un estado de energía a lo sumo `t` está en `P`.** La física bajo la tesis de Church–Turing tiene su
`P` contra `NP`, y es el mismo problema: el estado fundamental de Ising sin campo es MAX-CUT con otro nombre
(Barahona 1982, `barahona1982ising`).

## El problema

* Una instancia (`IsingInstancia`) es una lista de **acoples** `(u, v, J)` con `u, v` naturales (los sitios) y
  `J` entero, y un **umbral** `t` entero. Los enteros van en binario con signo y magnitud (`encIntBin` de
  cslib), los naturales en binario (`encNat`), la lista enmarcada (`encList`): el mismo estilo que
  `MaxCutInstance`.
* Una configuración es un conjunto `S` de sitios: `σ_v = +1` si `v ∈ S`, `−1` si no.
  La **energía** es `H_J(σ) = −Σ_e J_e σ_u σ_v` (`energia`).
* **`ISING`**: las instancias con un `S` de energía `≤ t`.

Respecto de la forma «`n`, `J` sobre los pares `i < j`, `t`» del enunciado, lo que cambió es solo la
representación de `J`: una lista dispersa de acoples en lugar de la matriz triangular. Los pares que no
aparecen tienen `J = 0`, un par repetido suma sus acoples y un lazo `(v, v, J)` aporta la constante `−J`
(`σ_v² = 1`). La matriz se escribe como lista en tiempo polinomial y al revés; con la lista la reducción
desde el `MaxCut` de cslib es una copia campo por campo. **Sin campo externo**: es el caso de Barahona,
el que es MAX-CUT; un campo `h_v` se simula con un sitio fantasma acoplado con `J = h_v`, y no hace falta aquí.

## Lo que se prueba

* **`energia_eq`** (la identidad de Barahona, sobre la lista): `H(σ) = −Σ J + 2 · corte_J(σ)`, con
  `corte_J` la suma de los acoples que cruzan. Es la misma identidad que `ising_eq_corte` de
  `Informacion/Transferencia`, pero sobre una lista de acoples enteros con sitios naturales en vez de una
  matriz real sobre `Fin n`: aquí se vuelve a probar en la forma que calza con la codificación.
* **`ISING_mem_NP`**: el certificado es `S` (una máscara sobre los extremos de los acoples, el
  `subsetVerifier` de cslib, como en `MaxCut.mem_NP`); calcular `H` por la identidad es una suma de enteros
  binarios, polinomial por `fun_prop` (`ComputableInPolyTime`).
* **`maxCut_iff_ising`** y **`polyTimeReducible_MaxCut_ISING`**: con los acoples antiferromagnéticos
  `J_e = −w_e`, **hay un corte de peso `≥ k` si y solo si hay un `σ` con `H(σ) ≤ −Σ J − 2k`**
  (`= W − 2k`, con `W` el peso total). El signo: `−2k`, no `+2k`, porque `J = −w` cambia el signo del
  corte en la identidad.
* **`ISING_npComplete`**: por `MaxCut_npComplete` de cslib (Karp, desde `Partition`) y la transitividad.
* **`P_eq_NP_iff_ISING_mem_P`**: `(∀ α enc, P enc = NP enc) ↔ ISING ∈ P encIsing`, con las definiciones de
  cslib; `⇐` porque un NP-completo en `P` arrastra a todo `NP` (`NPComplete.P_eq_NP_of_mem_P`, la misma
  que usa `Ladner.P_eq_NP_of_SAT_mem_P`), `⇒` porque `ISING ∈ NP`. Y **`ISING_mem_P_iff_SAT_mem_P`**.

## Lo que NO se prueba

* Nada sobre si `P = NP`. Se cierra una equivalencia: la física estadística del estado fundamental no da un
  atajo ni un obstáculo que la teoría de la complejidad no tenga ya.
* Las instancias planares (Barahona: polinomiales sin campo) no se tratan; la NP-completitud que se usa es la
  del grafo general, con pesos en binario.
-/

namespace Sagitta.Map.Informacion.Hamiltoniano

open Turing.MultiTapeTM Cslib.Complexity ComputableInPolyTime

/-! ## 1. El problema ISING -/

/-- Un acople `J` entre los sitios `u` y `v`. -/
structure Acople where
  /-- Un sitio. -/
  u : ℕ
  /-- El otro sitio. -/
  v : ℕ
  /-- La constante de acople (positiva: ferromagnética). -/
  J : ℤ
  deriving DecidableEq, Repr

/-- Los acoples se codifican como `(u, v, J)`, todo en binario (`J` con signo y magnitud). -/
enc_structure encAcople : Acople where
  u : encNat, v : encNat, J : encIntBin

attribute [fun_prop] encAcople_u_polyTime encAcople_v_polyTime encAcople_J_polyTime
  encAcople_mk_polyTime

/-- Una instancia de ISING: los acoples y el umbral de energía. -/
structure IsingInstancia where
  /-- Los acoples. -/
  acoples : List Acople
  /-- El umbral `t`. -/
  t : ℤ
  deriving DecidableEq, Repr

/-- La lista enmarcada de acoples seguida del umbral, en binario. -/
enc_structure encIsing : IsingInstancia where
  acoples : (encList encAcople), t : encIntBin

attribute [fun_prop] encIsing_acoples_polyTime encIsing_t_polyTime encIsing_mk_polyTime

/-- El espín de un sitio: `+1` si está en el lado `true`, `−1` si no. -/
def espin (b : Bool) : ℤ := if b then 1 else -1

/-- **El hamiltoniano de Ising sin campo**: `H_J(σ) = −Σ_e J_e σ_u σ_v`. -/
def energia (E : List Acople) (lado : ℕ → Bool) : ℤ :=
  -(E.map fun e => e.J * espin (lado e.u) * espin (lado e.v)).sum

/-- **ISING** (estado fundamental, versión de decisión): hay una configuración de energía a lo sumo `t`. -/
def ISING : Set IsingInstancia :=
  {x | ∃ S : Finset ℕ, energia x.acoples (fun v => decide (v ∈ S)) ≤ x.t}

/-! ## 2. La identidad de Barahona -/

/-- El acople `e` cruza el corte `lado`. -/
def cruza (lado : ℕ → Bool) (e : Acople) : Bool := lado e.u != lado e.v

/-- La suma de los acoples: `Σ J`. -/
def pesoTotal (E : List Acople) : ℤ := (E.map Acople.J).sum

/-- El corte pesado por `J`: la suma de los acoples que cruzan. -/
def corteJ (E : List Acople) (lado : ℕ → Bool) : ℤ := ((E.filter fun e => cruza lado e).map Acople.J).sum

/-- **Identidad de Barahona**: `H(σ) = −Σ J + 2 · corte_J(σ)`. Un acople que no cruza aporta `−J`; uno que
cruza, `+J = −J + 2J`. -/
theorem energia_eq (E : List Acople) (lado : ℕ → Bool) :
    energia E lado = -pesoTotal E + 2 * corteJ E lado := by
  induction E with
  | nil => simp [energia, pesoTotal, corteJ]
  | cons e E ih =>
    have hc : corteJ (e :: E) lado = (if cruza lado e then e.J else 0) + corteJ E lado := by
      unfold corteJ
      rw [List.filter_cons]
      split <;> simp [*]
    have hp : pesoTotal (e :: E) = e.J + pesoTotal E := by simp [pesoTotal]
    have he : energia (e :: E) lado =
        -(e.J * espin (lado e.u) * espin (lado e.v)) + energia E lado := by
      simp only [energia, List.map_cons, List.sum_cons]
      ring
    have key : e.J * espin (lado e.u) * espin (lado e.v) =
        e.J - 2 * (if cruza lado e then e.J else 0) := by
      cases hu : lado e.u <;> cases hv : lado e.v <;> simp [cruza, espin, hu, hv] <;> ring
    rw [he, hc, hp, ih, key]
    ring

/-- La energía depende solo de los lados de los extremos de los acoples. -/
def extremos (E : List Acople) : List ℕ := E.flatMap fun e => [e.u, e.v]

theorem length_extremos (E : List Acople) : (extremos E).length = 2 * E.length := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    simp only [extremos, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem energia_congr {E : List Acople} {lado lado' : ℕ → Bool}
    (h : ∀ v ∈ extremos E, lado v = lado' v) : energia E lado = energia E lado' := by
  unfold energia
  congr 2
  refine List.map_congr_left fun e he => ?_
  have h₁ : e.u ∈ extremos E := List.mem_flatMap.2 ⟨e, he, by simp⟩
  have h₂ : e.v ∈ extremos E := List.mem_flatMap.2 ⟨e, he, by simp⟩
  rw [h _ h₁, h _ h₂]

/-! ### El puente con `Transferencia`: la matriz `J` sobre `Fin n` es una lista de acoples -/

section Puente

variable {n : ℕ}

/-- La matriz triangular `J_ij`, `i < j`, como lista de acoples (los pares de `Transferencia.pares`). -/
noncomputable def acoplesDe (J : Fin n → Fin n → ℤ) : List Acople :=
  (Transferencia.pares n).toList.map fun p => ⟨p.1, p.2, J p.1 p.2⟩

/-- El lado `+1` de una configuración `σ : Fin n → ℤˣ`, como función de los sitios naturales. -/
def ladoDe (σ : Fin n → ℤˣ) (v : ℕ) : Bool := if h : v < n then decide (σ ⟨v, h⟩ = 1) else false

theorem espin_ladoDe (σ : Fin n → ℤˣ) (i : Fin n) :
    ((espin (ladoDe σ i) : ℤ) : ℝ) = Transferencia.esp (σ i) := by
  have h : (-1 : ℤˣ) ≠ 1 := by decide
  simp only [ladoDe, i.isLt, dite_true, Fin.eta]
  rcases Int.units_eq_one_or (σ i) with hi | hi <;> simp [hi, h, espin, Transferencia.esp]

/-- **El hamiltoniano de la lista es el de `Transferencia`**: con la matriz entera vista en `ℝ`, la energía
de `acoplesDe J` en el lado `+1` de `σ` es `Transferencia.ising J σ`. Así la identidad de este archivo y
`ising_eq_corte` hablan del mismo número. -/
theorem energia_acoplesDe (J : Fin n → Fin n → ℤ) (σ : Fin n → ℤˣ) :
    ((energia (acoplesDe J) (ladoDe σ) : ℤ) : ℝ) = Transferencia.ising (fun i j => (J i j : ℝ)) σ := by
  simp only [energia, acoplesDe, List.map_map, Function.comp_def, Transferencia.ising]
  rw [Finset.sum_map_toList (Transferencia.pares n)
    (fun p => J p.1 p.2 * espin (ladoDe σ p.1) * espin (ladoDe σ p.2))]
  push_cast
  simp only [espin_ladoDe]

end Puente

/-! ## 3. ISING está en NP -/

/-- La comprobación de una configuración, dada como lista de sitios en `+1`: la energía, calculada por la
identidad de Barahona, no pasa del umbral. -/
def comprobar (x : IsingInstancia) (S : List ℕ) : Bool :=
  decide (-pesoTotal x.acoples + (corteJ x.acoples (fun v => decide (v ∈ S)) +
    corteJ x.acoples (fun v => decide (v ∈ S))) ≤ x.t)

theorem comprobar_eq (x : IsingInstancia) (S : List ℕ) :
    comprobar x S = decide (energia x.acoples (fun v => decide (v ∈ S)) ≤ x.t) := by
  rw [comprobar, energia_eq, two_mul]

/-- El verificador: elige `S` entre los extremos con una máscara y comprueba la energía. -/
def verificador : IsingInstancia × List Bool → Bool :=
  subsetVerifier (fun x => extremos x.acoples) (Function.uncurry comprobar)

theorem computableInPolyTime_comprobar :
    ComputableInPolyTime (Function.uncurry comprobar) (encPair encIsing (encList encNat))
      encBool := by
  unfold Function.uncurry comprobar pesoTotal corteJ cruza
  fun_prop

/-- **Calcular la energía es polinomial**: el verificador de ISING está en tiempo polinomial. -/
theorem computableInPolyTime_verificador :
    ComputableInPolyTime verificador (encPair encIsing encBits) encBool :=
  computableInPolyTime_subsetVerifier (encγ := encNat)
    (by unfold extremos; fun_prop) computableInPolyTime_comprobar

theorem mem_ISING_iff_extremos {x : IsingInstancia} :
    x ∈ ISING ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ extremos x.acoples) ∧
      energia x.acoples (fun v => decide (v ∈ S)) ≤ x.t := by
  classical
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S.filter (· ∈ extremos x.acoples), fun v hv => (Finset.mem_filter.1 hv).2, ?_⟩
    rwa [energia_congr (lado' := fun v => decide (v ∈ S)) fun v hv => by
      simp [Finset.mem_filter, hv]]
  · rintro ⟨S, -, hS⟩
    exact ⟨S, hS⟩

theorem isVerifier : IsVerifier encIsing (2 * Polynomial.X) verificador ISING := by
  have hset : ISING = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ extremos x.acoples) ∧
      energia x.acoples (fun v => decide (v ∈ S)) ≤ x.t} :=
    Set.ext fun _ => mem_ISING_iff_extremos
  rw [hset]
  refine isVerifier_subsetVerifier (fun x => ?_) fun x l hl _ => ?_
  · rw [encIsing_apply]
    have : x.acoples.length ≤ (encIsingFields (x.acoples, x.t)).length :=
      (length_le_length_encList _ _).trans (length_le_encPair_left _ _ (x.acoples, x.t))
    simp only [length_extremos, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  · simp only [Function.uncurry_apply_pair, comprobar_eq, decide_eq_true_eq, List.mem_toFinset]

/-- **ISING ∈ NP**: el certificado es la configuración. -/
theorem ISING_mem_NP : ISING ∈ NP encIsing :=
  ⟨2 * Polynomial.X, verificador, computableInPolyTime_verificador, isVerifier⟩

/-! ## 4. MAX-CUT se reduce a ISING -/

/-- **La reducción de Barahona**: cada arista de peso `w` es un acople antiferromagnético `J = −w`, y el
umbral es `W − 2k`, con `W` el peso total y `k` la cota del corte. -/
def desdeMaxCut (x : MaxCutInstance) : IsingInstancia :=
  ⟨x.edges.map fun e => ⟨e.u, e.v, -(e.weight : ℤ)⟩,
    ((x.edges.map MaxCut.WeightedEdge.weight).sum : ℤ) - (x.bound : ℤ) - (x.bound : ℤ)⟩

/-- Con los acoples antiferromagnéticos, `H(σ) = W − 2 · corte_w(σ)`. -/
theorem energia_desdeMaxCut (E : List MaxCut.WeightedEdge) (lado : ℕ → Bool) :
    energia (E.map fun e => (⟨e.u, e.v, -(e.weight : ℤ)⟩ : Acople)) lado =
      ((E.map MaxCut.WeightedEdge.weight).sum : ℤ) - 2 * (MaxCut.cutWeight E lado : ℤ) := by
  induction E with
  | nil => simp [energia, MaxCut.cutWeight]
  | cons e E ih =>
    simp only [energia, MaxCut.cutWeight, List.map_cons, List.sum_cons, List.filter_cons,
      List.map_map] at ih ⊢
    cases hu : lado e.u <;> cases hv : lado e.v <;>
      simp [MaxCut.crosses, hu, hv, espin, Function.comp_def] at ih ⊢ <;>
      linarith

/-- **Barahona, como equivalencia de decisión**: hay un corte de peso `≥ k` si y solo si hay una
configuración de energía `≤ −Σ J − 2k` (con `J = −w`, `−Σ J = W`). -/
theorem maxCut_iff_ising (x : MaxCutInstance) : x ∈ MaxCut ↔ desdeMaxCut x ∈ ISING := by
  simp only [MaxCut, ISING, desdeMaxCut, Set.mem_ofPred_eq, energia_desdeMaxCut]
  refine exists_congr fun S => ?_
  omega

theorem computableInPolyTime_desdeMaxCut :
    ComputableInPolyTime desdeMaxCut encMaxCut encIsing := by
  unfold desdeMaxCut
  fun_prop

/-- MAX-CUT se reduce a ISING en tiempo polinomial. -/
theorem polyTimeReducible_MaxCut_ISING : PolyTimeReducible encMaxCut encIsing MaxCut ISING :=
  ⟨desdeMaxCut, computableInPolyTime_desdeMaxCut, maxCut_iff_ising⟩

/-- **ISING es NP-difícil.** -/
theorem ISING_npHard : NPHard encIsing ISING :=
  MaxCut_npHard.trans polyTimeReducible_MaxCut_ISING

/-- **ISING es NP-completo** (Barahona 1982). -/
theorem ISING_npComplete : NPComplete encIsing ISING :=
  ⟨ISING_mem_NP, ISING_npHard⟩

/-! ## 5. El teorema -/

/-- **P contra NP, en la física**: `P = NP` (para toda codificación, como lo dice cslib) si y solo si el
problema de decisión del estado fundamental de Ising está en `P`. -/
theorem P_eq_NP_iff_ISING_mem_P :
    (∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc) ↔ ISING ∈ P encIsing := by
  constructor
  · intro h
    rw [h encIsing]
    exact ISING_mem_NP
  · intro h α enc
    exact ISING_npComplete.P_eq_NP_of_mem_P h enc

/-- ISING y SAT caen juntos: los dos son NP-completos. -/
theorem ISING_mem_P_iff_SAT_mem_P : ISING ∈ P encIsing ↔ SAT ∈ P encCNF :=
  ISING_npComplete.mem_P_iff_mem_P CookLevin.SAT_npComplete

end Sagitta.Map.Informacion.Hamiltoniano
