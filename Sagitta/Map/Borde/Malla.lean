import Mathlib.Combinatorics.Nullstellensatz
import Sagitta.Map.Borde.BasuraEnElCubo

/-!
# La malla: coincidir como función en `Sⁿ` es coincidir como polinomio, si el grado individual es `< |S|`

La pregunta de José (25 nov 2026): ¿por qué el cubo booleano y no una malla de naturales? El control de `x² − x`
(`BasuraEnElCubo`) muestra que el cubo `{0,1}ⁿ` no ve la parte del polinomio que lee el método de VP ≠ VNP. La malla
`Sⁿ`, con `|S|` mayor que el grado individual, sí la ve: es el Nullstellensatz combinatorio de Alon, que en Mathlib es
`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` (`Mathlib/Combinatorics/Nullstellensatz.lean`: si `P` tiene grado
`< |S i|` en cada variable `i` y se anula en `∏ᵢ S i`, entonces `P = 0`, sobre un dominio). En la literatura de
cotas inferiores es la observación 1.5 de Forbes, Kumar y Saptharishi (CCC 2016, arXiv:1605.04207), ya citada en
las notas del proyecto.

## Lo que se prueba

* **`unicidad_en_la_malla`**: si `p` y `q` tienen grado individual `< |S i|` en cada variable y coinciden en
  `∏ᵢ S i`, entonces `p = q`. Su caso de una sola `S`, `unicidad_en_la_malla'`.
* **`unicidad_en_el_cubo`**: el cubo es el caso extremo, `S = {0,1}` y polinomios multilineales.
* **`contraste`** (el teorema central): el polinomio `p = (x₀₀² − x₀₀)·∏_{a≠0} x_{a,0}` del artículo se anula en el
  cubo, tiene grado individual `2` en `x₀₀` (así que el cubo no está obligado a verlo), grado individual `≤ 2` en todas
  y **no** se anula en la malla `{0,1,2}ⁿ`. Y `parteLineal_funcional_en_la_malla`: para polinomios de grado individual
  `≤ 2`, la parte lineal por bloques sí es función de los valores en `{0,1,2}ⁿ`.
* **La escalera** (`escalera`, `funcional_en_la_clase`): con `|S| = k + 1`, cualquier cantidad formal (una cota de
  tamaño, la parte lineal, lo que sea) es función de los valores en `Sⁿ` dentro de la clase de grado individual `≤ k`.
  Una cota formal para `f` en esa clase vale para todo `g` de la clase que coincida con `f` en `Sⁿ`.
* **`basura_en_la_malla`**: por qué esto no da nada nuevo para circuitos generales. Para cada malla finita `S` hay un
  polinomio no nulo que se anula en `Sⁿ` (`∏_{s ∈ S} (xᵢ − s)`, el `x² − x` de la malla), y por Alon su grado individual
  es `≥ |S|`. El grado individual de un circuito de tamaño `s` puede llegar a `2ˢ` (cuadrar `s` veces): ninguna malla
  fija cubre a todos los circuitos, así que la cota funcional en `Sⁿ` es cota formal solo para circuitos de grado
  individual acotado, que es un modelo restringido (en FKS, los de grado individual bajo), no `VP`.
-/

open MvPolynomial

namespace Sagitta.Map.Borde.Malla

/-! ## La unicidad -/

section Unicidad

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R]

/-- **Coincidir en la malla es coincidir como polinomio** (Alon, Nullstellensatz combinatorio). -/
theorem unicidad_en_la_malla (p q : MvPolynomial σ R) (S : σ → Finset R)
    (hp : ∀ i, p.degreeOf i < (S i).card) (hq : ∀ i, q.degreeOf i < (S i).card)
    (h : ∀ x : σ → R, (∀ i, x i ∈ S i) → eval x p = eval x q) : p = q := by
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_zero_at_prod_finset (p - q) S (fun i => ?_) (fun x hx => ?_)
  · exact lt_of_le_of_lt (degreeOf_sub_le i p q) (max_lt (hp i) (hq i))
  · rw [map_sub, h x hx, sub_self]

/-- La misma, con una sola `S` para todas las variables: la malla `Sⁿ`. -/
theorem unicidad_en_la_malla' (p q : MvPolynomial σ R) (S : Finset R)
    (hp : ∀ i, p.degreeOf i < S.card) (hq : ∀ i, q.degreeOf i < S.card)
    (h : ∀ x : σ → R, (∀ i, x i ∈ S) → eval x p = eval x q) : p = q :=
  unicidad_en_la_malla p q (fun _ => S) hp hq h

open scoped Classical in
theorem card_cero_uno : (({0, 1} : Finset R)).card = 2 := by
  rw [Finset.card_pair zero_ne_one]

open scoped Classical in
/-- **El cubo como caso extremo**: `S = {0,1}`, y entonces solo se pueden separar los multilineales. -/
theorem unicidad_en_el_cubo (p q : MvPolynomial σ R)
    (hp : ∀ i, p.degreeOf i ≤ 1) (hq : ∀ i, q.degreeOf i ≤ 1)
    (h : ∀ x : σ → R, (∀ i, x i = 0 ∨ x i = 1) → eval x p = eval x q) : p = q :=
  unicidad_en_la_malla' p q {0, 1} (fun i => by rw [card_cero_uno]; exact Nat.lt_succ_of_le (hp i))
    (fun i => by rw [card_cero_uno]; exact Nat.lt_succ_of_le (hq i)) (fun x hx => h x fun i => by simpa using hx i)

end Unicidad

/-! ## El contraste: el `p` del artículo en el cubo y en la malla `{0,1,2}ⁿ` -/

section Contraste

open Sagitta.Map.Borde.BasuraEnElCubo

variable {R : Type*} [CommRing R] {k r : ℕ}

/-- La malla `{0,1,2}`. -/
def malla3 (R : Type*) [CommRing R] [DecidableEq R] : Finset R := {0, 1, 2}

theorem card_malla3 [DecidableEq R] [IsDomain R] [CharZero R] : (malla3 R).card = 3 := by
  have h01 : (0 : R) ≠ 1 := zero_ne_one
  have h02 : (0 : R) ≠ 2 := (two_ne_zero).symm
  have h12 : (1 : R) ≠ 2 := by
    intro h; simp at h
  simp [malla3, Finset.card_insert_of_notMem, h01, h02, h12]

theorem s2_apply (i : Var k r) : (s2 (k := k) (r := r)) i = (if i = (0, 0) then 1 else 0) + (if i.2 = 0 then 1 else 0) := by
  classical
  obtain ⟨a, j⟩ := i
  simp only [s2, Finsupp.add_apply, Finsupp.single_apply, mono_apply, Finset.mem_univ, true_and]
  by_cases ha : a = 0 <;> by_cases hj : j = 0 <;> simp [ha, hj, eq_comm]

theorem s1_apply (i : Var k r) : (s1 (k := k) (r := r)) i = if i.2 = 0 then 1 else 0 := by
  obtain ⟨a, j⟩ := i
  simp [s1, mono_apply]

theorem coeff_p (s : Var k r →₀ ℕ) [Nontrivial R] :
    (p R k r).coeff s = (if s2 = s then 1 else 0) - (if s1 = s then 1 else 0) := by
  rw [p_eq, coeff_sub, coeff_monomial, coeff_monomial]

/-- El grado individual de `p` es a lo sumo `2` en toda variable. -/
theorem degreeOf_p_le [Nontrivial R] (i : Var k r) : (p R k r).degreeOf i ≤ 2 := by
  have : (p R k r).degreeOf i < 3 := by
    rw [degreeOf_lt_iff (by norm_num)]
    intro m hm
    rw [mem_support_iff, coeff_p] at hm
    by_cases h2 : s2 = m
    · subst h2; rw [s2_apply]; split_ifs <;> omega
    · by_cases h1 : s1 = m
      · subst h1; rw [s1_apply]; split_ifs <;> omega
      · simp [h1, h2] at hm
  omega

/-- **En `x₀₀` es exactamente `2`**: por eso el cubo (que solo obliga a los multilineales) no tiene que verlo. -/
theorem degreeOf_p_cero [Nontrivial R] : (p R k r).degreeOf (0, 0) = 2 := by
  refine le_antisymm (degreeOf_p_le _) ?_
  have hs : s2 ∈ (p R k r).support := by
    rw [mem_support_iff, coeff_p]
    simp [s1_ne_s2]
  have := monomial_le_degreeOf (0, 0) hs
  rw [s2_apply] at this
  simpa using this

/-- En el punto `(2, 2, …, 2)` de la malla, `p` vale `(2² − 2)·2ᵏ = 2ᵏ⁺¹`. -/
theorem eval_p_dos : eval (fun _ => (2 : R)) (p R k r) = 2 ^ (k + 1) := by
  simp only [p, map_mul, map_sub, map_pow, eval_X, map_prod, Finset.prod_const, Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, add_tsub_cancel_right]
  ring

/-- **El contraste.** `p` se anula en el cubo, su grado individual en `x₀₀` es `2` (no `≤ 1`, así que la unicidad
en el cubo no lo obliga a ser `0`), su grado individual es `≤ 2` en todas las variables (así que la malla `{0,1,2}ⁿ`
sí lo obliga) y, en efecto, **no** se anula en `{0,1,2}ⁿ`. -/
theorem contraste [DecidableEq R] [IsDomain R] [CharZero R] :
    (∀ x : Var k r → R, (∀ i, x i = 0 ∨ x i = 1) → eval x (p R k r) = 0) ∧
    (p R k r).degreeOf (0, 0) = 2 ∧
    (∀ i, (p R k r).degreeOf i < (malla3 R).card) ∧
    ∃ x : Var k r → R, (∀ i, x i ∈ malla3 R) ∧ eval x (p R k r) ≠ 0 :=
  ⟨p_cero_en_el_cubo, degreeOf_p_cero, fun i => by rw [card_malla3]; have := degreeOf_p_le (R := R) i; omega,
   fun _ => 2, fun _ => by simp [malla3], by rw [eval_p_dos]; exact pow_ne_zero _ two_ne_zero⟩

/-- Y la malla separa lo que el cubo confunde: `p` y `0` coinciden en el cubo pero no en `{0,1,2}ⁿ`. -/
theorem la_malla_separa [DecidableEq R] [IsDomain R] [CharZero R] :
    (∀ x : Var k r → R, (∀ i, x i = 0 ∨ x i = 1) → eval x (p R k r) = eval x 0) ∧
    ¬ ∀ x : Var k r → R, (∀ i, x i ∈ malla3 R) → eval x (p R k r) = eval x 0 := by
  obtain ⟨hc, -, -, x, hx, hne⟩ := contraste (R := R) (k := k) (r := r)
  exact ⟨fun y hy => by rw [hc y hy, map_zero], fun h => hne (by rw [h x hx, map_zero])⟩

/-- **En la malla, la parte lineal por bloques sí es funcional** para grado individual `≤ 2`: dos polinomios así
que coinciden en `{0,1,2}ⁿ` tienen la misma parte lineal (son iguales). Contrasta con `parteLineal_no_funcional`. -/
theorem parteLineal_funcional_en_la_malla [DecidableEq R] [IsDomain R] [CharZero R]
    (q₁ q₂ : MvPolynomial (Var k r) R) (h₁ : ∀ i, q₁.degreeOf i ≤ 2) (h₂ : ∀ i, q₂.degreeOf i ≤ 2)
    (h : ∀ x : Var k r → R, (∀ i, x i ∈ malla3 R) → eval x q₁ = eval x q₂) :
    parteLineal q₁ = parteLineal q₂ := by
  rw [unicidad_en_la_malla' q₁ q₂ (malla3 R) (fun i => by rw [card_malla3]; have := h₁ i; omega)
    (fun i => by rw [card_malla3]; have := h₂ i; omega) h]

end Contraste

/-! ## La escalera: con `|S| = k + 1`, lo formal es funcional en la clase de grado individual `≤ k` -/

section Escalera

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R]

/-- La clase de los polinomios de grado individual `≤ k` (un circuito cuyo grado individual es `≤ k` calcula uno). -/
def Clase (σ R : Type*) [CommRing R] (k : ℕ) : Set (MvPolynomial σ R) := {g | ∀ i, g.degreeOf i ≤ k}

omit [Finite σ] [IsDomain R] in
theorem clase_mono {k l : ℕ} (h : k ≤ l) : Clase σ R k ⊆ Clase σ R l := fun _ hg i => (hg i).trans h

/-- Coincidir en la malla. -/
def CoincidenEn (S : Finset R) (f g : MvPolynomial σ R) : Prop :=
  ∀ x : σ → R, (∀ i, x i ∈ S) → eval x f = eval x g

theorem igual_de_coinciden {k : ℕ} {S : Finset R} (hS : S.card = k + 1) {f g : MvPolynomial σ R}
    (hf : f ∈ Clase σ R k) (hg : g ∈ Clase σ R k) (h : CoincidenEn S f g) : f = g :=
  unicidad_en_la_malla' f g S (fun i => by rw [hS]; exact Nat.lt_succ_of_le (hf i))
    (fun i => by rw [hS]; exact Nat.lt_succ_of_le (hg i)) h

/-- **La escalera.** Con `|S| = k + 1`: una cota formal (cualquier medida `μ` del polinomio) para `f` en la clase
de grado individual `≤ k` vale para todo `g` de la clase que coincida con `f` en `Sⁿ`. El cubo es el peldaño `k = 1`. -/
theorem escalera {k : ℕ} {S : Finset R} (hS : S.card = k + 1) (μ : MvPolynomial σ R → ℕ) {c : ℕ}
    {f g : MvPolynomial σ R} (hf : f ∈ Clase σ R k) (hg : g ∈ Clase σ R k) (h : CoincidenEn S f g)
    (hc : c ≤ μ f) : c ≤ μ g := by
  rwa [← igual_de_coinciden hS hf hg h]

/-- La tabla de valores en la malla (fuera de la malla, `0`). -/
noncomputable def tabla (S : Finset R) (g : MvPolynomial σ R) : (σ → R) → R := by
  classical exact fun x => if ∀ i, x i ∈ S then eval x g else 0

omit [Finite σ] [IsDomain R] in
theorem coinciden_de_tabla {S : Finset R} {f g : MvPolynomial σ R} (h : tabla S f = tabla S g) :
    CoincidenEn S f g := fun x hx => by
  have := congrFun h x
  simpa [tabla, hx] using this

/-- **Lo formal es funcional en la clase**: toda medida `μ` restringida a la clase de grado individual `≤ k` se
factoriza por la tabla de valores en `Sⁿ`. -/
theorem funcional_en_la_clase {k : ℕ} {S : Finset R} (hS : S.card = k + 1) {β : Type*} (μ : MvPolynomial σ R → β) :
    ∃ F : ((σ → R) → R) → β, ∀ g ∈ Clase σ R k, μ g = F (tabla S g) := by
  classical
  refine ⟨fun t => if h : ∃ g ∈ Clase σ R k, tabla S g = t then μ h.choose else μ 0, fun g hg => ?_⟩
  have h : ∃ g' ∈ Clase σ R k, tabla S g' = tabla S g := ⟨g, hg, rfl⟩
  dsimp only
  split
  · next h' =>
    exact congrArg μ (igual_de_coinciden hS hg h'.choose_spec.1 (coinciden_de_tabla h'.choose_spec.2.symm))
  · exact absurd h ‹_›

end Escalera

/-! ## Por qué no alcanza para circuitos generales -/

section Basura

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R]

/-- **La basura de la malla**: `∏_{s ∈ S} (xᵢ − s)` se anula en `Sⁿ`, no es cero (en un dominio infinito) y por Alon
su grado individual en `xᵢ` es `≥ |S|`. Ninguna malla finita ve todo: se escapa lo de grado individual `≥ |S|`, y un
circuito de tamaño `s` alcanza grado individual `2ˢ`. -/
theorem basura_en_la_malla [Infinite R] (S : Finset R) (i : σ) :
    ∃ q : MvPolynomial σ R, q ≠ 0 ∧ (∀ x : σ → R, (∀ j, x j ∈ S) → eval x q = 0) ∧ S.card ≤ q.degreeOf i := by
  classical
  set q : MvPolynomial σ R := ∏ s ∈ S, (X i - C s) with hq
  have hcero : ∀ x : σ → R, (∀ j, x j ∈ S) → eval x q = 0 := fun x hx => by
    rw [hq, map_prod]
    exact Finset.prod_eq_zero (hx i) (by simp)
  have hne : q ≠ 0 := by
    obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset S
    intro h0
    have := congrArg (eval (fun _ => a)) h0
    rw [hq, map_prod, map_zero] at this
    obtain ⟨s, hs, hz⟩ := Finset.prod_eq_zero_iff.1 this
    simp only [map_sub, eval_X, eval_C, sub_eq_zero] at hz
    exact ha (hz ▸ hs)
  refine ⟨q, hne, hcero, ?_⟩
  by_contra hlt
  replace hlt := not_le.mp hlt
  -- en las otras variables `q` tiene grado `0 < |S|` (S no es vacío, porque `q ≠ 0` y se anula... salvo `S = ∅`)
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS] at hlt
  · apply hne
    refine eq_zero_of_eval_zero_at_prod_finset q (fun _ => S) (fun j => ?_) hcero
    by_cases hj : j = i
    · subst hj; exact hlt
    · calc q.degreeOf j ≤ ∑ s ∈ S, (X i - C s : MvPolynomial σ R).degreeOf j := degreeOf_prod_le _ _ _
        _ = 0 := Finset.sum_eq_zero fun s _ => by
            refine Nat.eq_zero_of_le_zero ((degreeOf_sub_le _ _ _).trans ?_)
            simp [degreeOf_X_of_ne, hj, degreeOf_C]
        _ < S.card := hS.card_pos

/-- La línea, dicha como teorema: para cada malla finita hay dos polinomios distintos que coinciden en ella (la
basura y el `0`). Una cota funcional en `Sⁿ` es formal solo en la clase de grado individual `< |S|`. -/
theorem ninguna_malla_basta [Infinite R] (S : Finset R) (i : σ) :
    ∃ q₁ q₂ : MvPolynomial σ R, q₁ ≠ q₂ ∧ CoincidenEn S q₁ q₂ := by
  obtain ⟨q, hne, hcero, -⟩ := basura_en_la_malla S i
  exact ⟨q, 0, hne, fun x hx => by rw [hcero x hx, map_zero]⟩

end Basura

/- Mutantes probados (25 nov 2026, fuera del repositorio):
* `MutAlon.lean`: en `unicidad_en_la_malla`, pedir grado individual `≤ |S i|` en vez de `<`. No compila: `max_lt`
  ya no da la hipótesis de Alon. Y es falso: `x² − x` y `0` tienen grado `≤ 2 = |{0,1}|` y coinciden en el cubo.
* `MutMalla.lean`: la malla `{0,1}` en vez de `{0,1,2}`. No compila: `card_malla3` (el cardinal es `2`) y `contraste`
  (el punto `(2,…,2)` ya no está en la malla; en el cubo `p` es `0`).
* `MutEscalera.lean`: en `escalera`, `|S| = k` en vez de `k + 1`. No compila: `igual_de_coinciden` necesita un punto
  más que el grado (con `|S| = k`, `∏_{s∈S}(xᵢ − s)` está en la clase y coincide con `0`).
* `MutBasura.lean`: en `basura_en_la_malla`, grado individual `> |S|` en vez de `≥`. No compila: la contradicción con
  Alon da `≥` y no más; es falso, porque `∏_{s∈S}(xᵢ − s)` tiene grado exactamente `|S|`. -/

end Sagitta.Map.Borde.Malla
