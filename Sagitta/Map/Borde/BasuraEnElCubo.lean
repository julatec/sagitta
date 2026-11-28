import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.Ring.Rat

/-!
# El control de `x² − x`: por qué el método de VP ≠ VNP no da cotas funcionales

La lectura del artículo de anthropics/formal-math (carpeta `vp-vnp`, commit `918c8e2`) pide un control barato:
el ejemplo de la sección 2.5 del artículo. Un circuito booleano para un polinomio solo tiene que acertar en las entradas
`0` y `1`, así que puede calcular `g = f + ∑ᵢ (xᵢ² − xᵢ)·hᵢ` en vez de `f`. Dos pasos de la prueba miran **dentro** del
polinomio que calcula el circuito: el lema de descomposición (`lem_balanced`, Lema E.4 del artículo) usa su **parte
lineal en cada bloque**, y el de evaluación (`lem_lowdeg`) su parte de grado bajo. Esa parte no es una función de los
valores en el cubo.

## La definición (sección 2.5 y prueba del Lema E.4 del artículo, leídas en el PDF)

Las variables vienen en `k` bloques de igual tamaño: `x_{a,ρ}`, con `a` el bloque y `ρ` la posición. Aquí
`a : Fin (k+1)` y `ρ : Fin (r+1)` (así hay un bloque `0` y una posición `0`; el artículo pide `k ≥ 2` y eso está
incluido). El **grado de un monomio en el bloque `a`** es la suma de sus exponentes en las variables de ese bloque
(`gradoBloque`). La **parte lineal por bloques** de un polinomio (`parteLineal`) es la suma de sus términos cuyos
monomios tienen grado **exactamente uno en cada bloque**: es el `γ_S` del artículo con `S` = todos los bloques («la parte
de grado uno en cada bloque de `S` y cero en los otros»). Se toma con `Finsupp.filter` sobre los coeficientes.

## Lo que se prueba

* `p k r = (x₀₀² − x₀₀)·∏_{a ≠ 0} x_{a,0}`, el polinomio del artículo (allí `(x₁,₁² − x₁,₁)·x₂,₁ ⋯ x_k,₁`).
* **`p_cero_en_el_cubo`**: sobre cualquier anillo conmutativo, `p` vale `0` en todo punto con coordenadas en `{0, 1}`.
* **`parteLineal_p`**: su parte lineal por bloques es `−∏_a x_{a,0}`, como dice el artículo; **`parteLineal_p_ne`**: no
  es cero (en un anillo no trivial). Y `p_ne_cero`: el polinomio mismo no es cero.
* **`parteLineal_no_funcional`**: hay dos polinomios que coinciden en todo el cubo (`p` y `0`) y tienen partes lineales
  por bloques distintas. Lo que lee `lem_balanced` no se puede calcular a partir de la función booleana.
* Control positivo, `parteLineal_prod`: para el polinomio lineal por bloques `∏_a x_{a,0}` la parte es él mismo; el
  filtro no borra lo que no debe.

## La lectura

Una cota inferior **funcional** (para todo circuito que acierte en el cubo) tendría que valer para `HC + p·h` igual que
para `HC`. El método acota el tamaño a partir de la parte lineal por bloques; sumar `p` (o cualquier `(x² − x)·h`) la
cambia sin cambiar la función en el cubo. Por eso no da cotas para circuitos booleanos.

## Lo que no

* De la parte de grado bajo (`lem_lowdeg`, Lema K.2: la suma de las partes homogéneas de grado `≤ d`) solo se prueba
  el control con `d = k + 1` (`parteGradoBajo_p`, `parteGradoBajo_no_funcional`); el `d` que usa el artículo en el caso
  contractivo no se miró.
* Nada del resto de la prueba de VP ≠ VNP: el Lean del artículo no se compiló aquí.
-/

open MvPolynomial

namespace Sagitta.Map.Borde.BasuraEnElCubo

variable {R : Type*} [CommRing R] {k r : ℕ}

/-- Las variables: bloque `a`, posición `ρ`. -/
abbrev Var (k r : ℕ) := Fin (k + 1) × Fin (r + 1)

/-- El grado de un monomio en el bloque `a`. -/
def gradoBloque (a : Fin (k + 1)) (s : Var k r →₀ ℕ) : ℕ := ∑ j : Fin (r + 1), s (a, j)

/-- El monomio tiene grado exactamente uno en cada bloque. -/
def LinealPorBloques (s : Var k r →₀ ℕ) : Prop := ∀ a, gradoBloque a s = 1

open scoped Classical in
/-- **La parte lineal por bloques**: los términos cuyo monomio tiene grado uno en cada bloque. -/
noncomputable def parteLineal (q : MvPolynomial (Var k r) R) : MvPolynomial (Var k r) R :=
  AddMonoidAlgebra.ofCoeff (Finsupp.filter LinealPorBloques q.coeff)

open scoped Classical in
theorem coeff_parteLineal_pos (q : MvPolynomial (Var k r) R) {s : Var k r →₀ ℕ} (h : LinealPorBloques s) :
    (parteLineal q).coeff s = q.coeff s :=
  Finsupp.filter_apply_pos _ _ h

open scoped Classical in
theorem coeff_parteLineal_neg (q : MvPolynomial (Var k r) R) {s : Var k r →₀ ℕ} (h : ¬ LinealPorBloques s) :
    (parteLineal q).coeff s = 0 :=
  Finsupp.filter_apply_neg _ _ h

/-- El polinomio del artículo: `(x₀₀² − x₀₀) · ∏_{a ≠ 0} x_{a,0}`. -/
noncomputable def p (R : Type*) [CommRing R] (k r : ℕ) : MvPolynomial (Var k r) R :=
  (X (0, 0) ^ 2 - X (0, 0)) * ∏ a ∈ Finset.univ.erase (0 : Fin (k + 1)), X (a, 0)

/-! ## En el cubo vale cero -/

/-- **`p` se anula en todo el cubo `{0,1}ⁿ`.** -/
theorem p_cero_en_el_cubo (x : Var k r → R) (hx : ∀ i, x i = 0 ∨ x i = 1) : eval x (p R k r) = 0 := by
  have h : x (0, 0) ^ 2 - x (0, 0) = 0 := by
    rcases hx (0, 0) with h | h <;> rw [h] <;> ring
  simp only [p, map_mul, map_sub, map_pow, eval_X, h, zero_mul]

/-! ## Su parte lineal por bloques -/

/-- El monomio `∏_{a ∈ t} x_{a,0}`. -/
noncomputable def mono (t : Finset (Fin (k + 1))) : Var k r →₀ ℕ := ∑ a ∈ t, Finsupp.single (a, (0 : Fin (r + 1))) 1

theorem prod_X_eq (t : Finset (Fin (k + 1))) :
    (∏ a ∈ t, X (a, (0 : Fin (r + 1))) : MvPolynomial (Var k r) R) = monomial (mono t) 1 := by
  rw [mono, monomial_sum_one]
  rfl

theorem mono_apply (t : Finset (Fin (k + 1))) (a : Fin (k + 1)) (j : Fin (r + 1)) :
    mono t (a, j) = if a ∈ t ∧ j = 0 then 1 else 0 := by
  classical
  simp only [mono, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq]
  by_cases ha : a ∈ t
  · by_cases hj : j = 0
    · subst hj
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (fun h => absurd ha h)]
      simp [ha]
    · simp [hj, Ne.symm hj]
  · rw [Finset.sum_eq_zero (fun b hb => by
      simp only [ite_eq_right_iff, and_imp]; rintro rfl; exact absurd hb ha)]
    simp [ha]

theorem gradoBloque_mono (t : Finset (Fin (k + 1))) (a : Fin (k + 1)) :
    gradoBloque a (mono (r := r) t) = if a ∈ t then 1 else 0 := by
  classical
  simp only [gradoBloque, mono_apply]
  by_cases ha : a ∈ t
  · simp [ha, Finset.sum_ite_eq']
  · simp [ha]

/-- El monomio de todos los bloques, `∏_a x_{a,0}`. -/
noncomputable def s1 : Var k r →₀ ℕ := mono Finset.univ

/-- El monomio `x₀₀² ∏_{a ≠ 0} x_{a,0}`. -/
noncomputable def s2 : Var k r →₀ ℕ := Finsupp.single (0, 0) 1 + mono Finset.univ

theorem p_eq : p R k r = monomial (s2 (k := k) (r := r)) 1 - monomial s1 1 := by
  classical
  have hmono : (Finsupp.single ((0 : Fin (k + 1)), (0 : Fin (r + 1))) 1 : Var k r →₀ ℕ) +
      mono (Finset.univ.erase 0) = mono Finset.univ := by
    rw [mono, mono, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 1)))]
  rw [p, prod_X_eq, sub_mul, pow_two, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
    add_assoc, hmono]
  simp only [mul_one]
  rfl

theorem lineal_s1 : LinealPorBloques (s1 (k := k) (r := r)) := fun a => by
  rw [s1, gradoBloque_mono]; simp

theorem no_lineal_s2 : ¬ LinealPorBloques (s2 (k := k) (r := r)) := fun h => by
  have h0 := h 0
  have : gradoBloque 0 (s2 (k := k) (r := r)) = 2 := by
    simp only [gradoBloque, s2, Finsupp.add_apply, Finset.sum_add_distrib]
    have := gradoBloque_mono (r := r) (Finset.univ : Finset (Fin (k + 1))) 0
    simp only [gradoBloque, Finset.mem_univ, ↓reduceIte] at this
    rw [this, Finset.sum_eq_single (0 : Fin (r + 1)) (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  omega

theorem s1_ne_s2 : (s1 (k := k) (r := r)) ≠ s2 := fun h => no_lineal_s2 (h ▸ lineal_s1)

/-- **La parte lineal por bloques de `p` es `−∏_a x_{a,0}`**, como dice la sección 2.5 del artículo. -/
theorem parteLineal_p : parteLineal (p R k r) = -∏ a : Fin (k + 1), X (a, 0) := by
  classical
  rw [show (∏ a : Fin (k + 1), X (a, (0 : Fin (r + 1))) : MvPolynomial (Var k r) R) = monomial s1 1 from
    prod_X_eq Finset.univ]
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : LinealPorBloques s
  · rw [coeff_parteLineal_pos _ hs, p_eq, coeff_neg, coeff_sub, coeff_monomial, coeff_monomial]
    have h2 : s2 ≠ s := fun h => no_lineal_s2 (h ▸ hs)
    simp [h2]
  · rw [coeff_parteLineal_neg _ hs, coeff_neg, coeff_monomial]
    have h1 : s1 ≠ s := fun h => hs (h ▸ lineal_s1)
    simp [h1]

/-- **Y no es cero.** -/
theorem parteLineal_p_ne [Nontrivial R] : parteLineal (p R k r) ≠ 0 := by
  rw [parteLineal_p, neg_ne_zero, show (∏ a : Fin (k + 1), X (a, (0 : Fin (r + 1))) : MvPolynomial (Var k r) R) =
    monomial s1 1 from prod_X_eq Finset.univ]
  exact (monomial_eq_zero).not.2 one_ne_zero

theorem parteLineal_cero : parteLineal (0 : MvPolynomial (Var k r) R) = 0 := by
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : LinealPorBloques s
  · rw [coeff_parteLineal_pos _ hs]
  · rw [coeff_parteLineal_neg _ hs]; rfl

/-- El polinomio mismo no es cero, aunque se anula en todo el cubo. -/
theorem p_ne_cero [Nontrivial R] : p R k r ≠ 0 := fun h => parteLineal_p_ne (by rw [h, parteLineal_cero])

/-- **Lo que lee el método no es funcional**: `p` y `0` coinciden en todo el cubo y tienen partes lineales por
bloques distintas. -/
theorem parteLineal_no_funcional [Nontrivial R] :
    ∃ q₁ q₂ : MvPolynomial (Var k r) R, (∀ x : Var k r → R, (∀ i, x i = 0 ∨ x i = 1) → eval x q₁ = eval x q₂) ∧
      parteLineal q₁ ≠ parteLineal q₂ :=
  ⟨p R k r, 0, fun x hx => by rw [p_cero_en_el_cubo x hx, map_zero],
   fun h => parteLineal_p_ne (h.trans parteLineal_cero)⟩

/-! ## La parte de grado bajo (la que mira `lem_lowdeg`)

Es la del artículo (sección 2.2 y Lema K.2, leídos en el PDF): la suma de las partes homogéneas de grado a lo sumo `d`,
o sea los términos de grado total `≤ d`. Con `d = k + 1` (el grado de un monomio lineal por bloques), la parte de `p` es
otra vez `−∏_a x_{a,0}`. La grieta es la misma. -/

open scoped Classical in
/-- Los términos de grado total a lo sumo `d`. -/
noncomputable def parteGradoBajo (d : ℕ) (q : MvPolynomial (Var k r) R) : MvPolynomial (Var k r) R :=
  AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun s : Var k r →₀ ℕ => s.degree ≤ d) q.coeff)

open scoped Classical in
theorem coeff_parteGradoBajo_pos (d : ℕ) (q : MvPolynomial (Var k r) R) {s : Var k r →₀ ℕ} (h : s.degree ≤ d) :
    (parteGradoBajo d q).coeff s = q.coeff s :=
  Finsupp.filter_apply_pos _ _ h

open scoped Classical in
theorem coeff_parteGradoBajo_neg (d : ℕ) (q : MvPolynomial (Var k r) R) {s : Var k r →₀ ℕ} (h : ¬ s.degree ≤ d) :
    (parteGradoBajo d q).coeff s = 0 :=
  Finsupp.filter_apply_neg _ _ h

theorem degree_mono (t : Finset (Fin (k + 1))) : (mono (r := r) t).degree = t.card := by
  simp [mono, map_sum, Finsupp.degree_single]

theorem degree_s1 : (s1 (k := k) (r := r)).degree = k + 1 := by
  rw [s1, degree_mono]; simp

theorem degree_s2 : (s2 (k := k) (r := r)).degree = k + 2 := by
  rw [s2, map_add, Finsupp.degree_single, ← s1, degree_s1]; ring

/-- **La parte de grado `≤ k + 1` de `p` es `−∏_a x_{a,0}`**: tampoco es función del cubo. -/
theorem parteGradoBajo_p : parteGradoBajo (k + 1) (p R k r) = -∏ a : Fin (k + 1), X (a, 0) := by
  classical
  rw [show (∏ a : Fin (k + 1), X (a, (0 : Fin (r + 1))) : MvPolynomial (Var k r) R) = monomial s1 1 from
    prod_X_eq Finset.univ]
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : s.degree ≤ k + 1
  · rw [coeff_parteGradoBajo_pos _ _ hs, p_eq, coeff_neg, coeff_sub, coeff_monomial, coeff_monomial]
    have h2 : s2 ≠ s := fun h => by rw [← h, degree_s2] at hs; omega
    simp [h2]
  · rw [coeff_parteGradoBajo_neg _ _ hs, coeff_neg, coeff_monomial]
    have h1 : s1 ≠ s := fun h => hs (by rw [← h, degree_s1])
    simp [h1]

theorem parteGradoBajo_cero (d : ℕ) : parteGradoBajo d (0 : MvPolynomial (Var k r) R) = 0 := by
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : s.degree ≤ d
  · rw [coeff_parteGradoBajo_pos _ _ hs]
  · rw [coeff_parteGradoBajo_neg _ _ hs]; rfl

/-- **La parte de grado bajo tampoco es funcional.** -/
theorem parteGradoBajo_no_funcional [Nontrivial R] :
    ∃ q₁ q₂ : MvPolynomial (Var k r) R, (∀ x : Var k r → R, (∀ i, x i = 0 ∨ x i = 1) → eval x q₁ = eval x q₂) ∧
      parteGradoBajo (k + 1) q₁ ≠ parteGradoBajo (k + 1) q₂ := by
  refine ⟨p R k r, 0, fun x hx => by rw [p_cero_en_el_cubo x hx, map_zero], fun h => ?_⟩
  rw [parteGradoBajo_p, parteGradoBajo_cero] at h
  rw [← parteLineal_p] at h
  exact parteLineal_p_ne h

/-! ## Controles -/

/-- Control positivo: lo que ya es lineal por bloques queda igual. -/
theorem parteLineal_prod :
    parteLineal (∏ a : Fin (k + 1), X (a, 0) : MvPolynomial (Var k r) R) = ∏ a : Fin (k + 1), X (a, 0) := by
  classical
  rw [prod_X_eq]
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : LinealPorBloques s
  · rw [coeff_parteLineal_pos _ hs]
  · rw [coeff_parteLineal_neg _ hs, coeff_monomial]
    have h1 : mono Finset.univ ≠ s := fun h => hs (h ▸ lineal_s1)
    simp [h1]

/-- El caso del artículo con tres bloques de una variable, sobre `ℚ`: `(x₀² − x₀)·x₁·x₂`. -/
example : parteLineal (p ℚ 2 0) ≠ 0 ∧ ∀ x : Var 2 0 → ℚ, (∀ i, x i = 0 ∨ x i = 1) → eval x (p ℚ 2 0) = 0 :=
  ⟨parteLineal_p_ne, p_cero_en_el_cubo⟩

/-- Y sobre `ZMod 2`, donde el permanente es el determinante: la basura sigue ahí. -/
example : p (ZMod 2) 2 0 ≠ 0 := by
  have : Fact (1 < 2) := ⟨by norm_num⟩
  exact p_ne_cero

/- Mutantes probados (25 nov 2026, fuera del repositorio):
* `MutGrado.lean`: cambiar «grado exactamente uno en cada bloque» por «grado a lo sumo dos» (`gradoBloque a s ≤ 2`). No
  compila: `omega` no cierra `no_lineal_s2` (el monomio `x₀₀²·∏ x_{a,0}` tiene grado 2 en el bloque 0 y ahora pasa el
  filtro), y entonces `parteLineal_p` es falso: la parte sería `p` entero. Lo que hace no nula a la parte es que el
  filtro bote `x₀₀²` y deje `−x₀₀`.
* `MutCubo.lean`: dejar que las coordenadas valgan también `2`. No compila (`p_cero_en_el_cubo` ya no tiene con qué
  anular `x₀₀² − x₀₀`), y es falso: en `x₀₀ = 2` vale `2` por el producto.
* `MutBajo.lean`: en `parteGradoBajo_p`, cortar en grado `k + 2` en vez de `k + 1`. No compila (`rw` no encuentra el
  coeficiente filtrado con la cota vieja), y el enunciado es falso: con `k + 2` entra `x₀₀²·∏ x_{a,0}` y la parte es `p`
  entero. -/

end Sagitta.Map.Borde.BasuraEnElCubo
