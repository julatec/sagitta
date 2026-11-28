import Sagitta.Map.Acotada
import Sagitta.Map.Clases

/-!
# Aritmética acotada, escalón 2: el enunciado del teorema de Buss

Buss (*Bounded Arithmetic*, 1986, cap. 3) probó que las funciones que S¹₂ demuestra totales, con una definición `Σᵇ₁`,
son exactamente las de tiempo polinomial. Aquí se **enuncia**; no se prueba (es el escalón 3).

**Qué es «Σᵇ₁-definible en S¹₂».** Buss, §2.3, p. 33 (cotejado contra el PDF del autor el 22 nov 2026). Una función
`f : ℕ → ℕ` lo es si hay una fórmula `Σᵇ₁` `φ(x, y)` y un término `t(x)` tales que

1. S¹₂ demuestra `∀ x ∃ y ≤ t(x) φ(x, y)`: la salida existe **y está acotada por un término**;
2. S¹₂ demuestra `∀ x ∀ y ∀ z (φ(x, y) ∧ φ(x, z) ⊃ y = z)`: es única;
3. en ℕ, `φ(x, f x)` vale para todo `x`.

La introducción del libro (p. 3) da una versión informal sin la cota, `∀ x ∃ y φ(x, y)`; queda aquí como
`DemuestraTotalSinCota`. La formal implica la informal (`demuestraTotalSinCota_de_cota`, probado). La vuelta es el
teorema de Parikh para S¹₂ (`CotaDeParikh`, abierto): si S¹₂ demuestra `∀ x ∃ y φ` con `φ` acotada, la `y` se puede
acotar por un término. Buss define para varias variables `x⃗`; aquí basta una, porque `f : ℕ → ℕ`.

«S¹₂ demuestra» va por modelos, como `Demuestra` en `Acotada.lean`: vale en todo modelo de S¹₂. Por el teorema de
completitud es lo mismo que la demostrabilidad, que es como lo dice Buss.

**Qué es «de tiempo polinomial».** `EsPolinomial f` de `Clases.lean`: una máquina de Mathlib (`Turing.FinTM2`)
calcula `f` en tiempo polinomial, con los naturales en binario (`Computability.encodeNat`). Es la clase FP.

Lo que se prueba aquí es un control: la identidad está de los dos lados (`definible_id`, `esPolinomial_id`), así que
la definición no es vacía ni pide algo imposible.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-- **S¹₂ demuestra que `φ(x, y)` define una función total**, como en la definición formal de Buss (§2.3, p. 33):
hay un término `t(x)` tal que en todo modelo de S¹₂ cada `x` tiene un `y ≤ t(x)` con `φ(x, y)`, y ese `y` es único. -/
def DemuestraTotal (φ : L.Formula (Fin 2)) : Prop :=
  ∃ t : L.Term (Fin 1), ∀ (M : Type) [L.Structure M], EsModeloS12 M →
    (∀ x : M, ∃ y : M, le y (t.realize ![x]) ∧ φ.Realize ![x, y]) ∧
    (∀ x y z : M, φ.Realize ![x, y] → φ.Realize ![x, z] → y = z)

/-- La versión informal de la introducción de Buss (p. 3): `∀ x ∃ y φ` y la unicidad, sin cota. -/
def DemuestraTotalSinCota (φ : L.Formula (Fin 2)) : Prop :=
  ∀ (M : Type) [L.Structure M], EsModeloS12 M → ∀ x : M, ∃! y : M, φ.Realize ![x, y]

/-- **La formal implica la informal**: si la salida existe por debajo de un término, existe. -/
theorem demuestraTotalSinCota_de_cota {φ : L.Formula (Fin 2)} (h : DemuestraTotal φ) :
    DemuestraTotalSinCota φ := by
  obtain ⟨t, ht⟩ := h
  intro M _ hM x
  obtain ⟨hex, huni⟩ := ht M hM
  obtain ⟨y, -, hy⟩ := hex x
  exact ⟨y, hy, fun z hz => huni x z y hz hy⟩

/-- **Parikh para S¹₂** (Parikh 1971; Buss 1986): la vuelta. Si S¹₂ demuestra `∀ x ∃! y φ` con `φ` en `Σᵇ₁`,
también lo demuestra con la `y` acotada por un término. Abierto aquí; es un teorema conocido. -/
def CotaDeParikh : Prop :=
  ∀ φ : L.Formula (Fin 2), EsSigma1 φ → DemuestraTotalSinCota φ → DemuestraTotal φ

/-- **`f` es `Σᵇ₁`-definible en S¹₂** (Buss, 1986, definición del §2.3, p. 33): una fórmula `Σᵇ₁` `φ(x, y)` que
S¹₂ demuestra total, con la salida acotada por un término, y que en ℕ es el gráfico de `f`. -/
def DefinibleSigma1 (f : ℕ → ℕ) : Prop :=
  ∃ φ : L.Formula (Fin 2), EsSigma1 φ ∧ DemuestraTotal φ ∧ ∀ n : ℕ, φ.Realize ![n, f n]

/-- **Buss, la dirección difícil**: lo que S¹₂ demuestra total con una definición `Σᵇ₁` es de tiempo polinomial
(la «extracción de algoritmos» de las pruebas). Abierto aquí; es un teorema conocido. -/
def DefinibleEsPolinomial : Prop :=
  ∀ f : ℕ → ℕ, DefinibleSigma1 f → EsPolinomial f

/-- **Buss, la otra dirección**: toda función de tiempo polinomial es `Σᵇ₁`-definible en S¹₂. Abierto aquí; es un
teorema conocido (va por la caracterización de Cobham). -/
def PolinomialEsDefinible : Prop :=
  ∀ f : ℕ → ℕ, EsPolinomial f → DefinibleSigma1 f

/-- **El teorema de Buss** (1986): una función es `Σᵇ₁`-definible en S¹₂ si y solo si es de tiempo polinomial. -/
def TeoremaDeBuss : Prop :=
  ∀ f : ℕ → ℕ, DefinibleSigma1 f ↔ EsPolinomial f

/-- Las dos direcciones juntas son el teorema. -/
theorem teoremaDeBuss_iff : TeoremaDeBuss ↔ DefinibleEsPolinomial ∧ PolinomialEsDefinible :=
  ⟨fun h => ⟨fun f hf => (h f).1 hf, fun f hf => (h f).2 hf⟩,
   fun h f => ⟨h.1 f, h.2 f⟩⟩

/-! ## Control: la identidad está de los dos lados -/

/-- La fórmula `y = x`. Es atómica, así que es aguda y por lo tanto `Σᵇ₁`. -/
def grafoId : L.Formula (Fin 2) :=
  BoundedFormula.equal (Term.var (Sum.inl 1)) (Term.var (Sum.inl 0))

theorem esSigma1_grafoId : EsSigma1 grafoId :=
  EsSigma1.aguda (EsAguda.igual _ _)

/-- **La identidad es `Σᵇ₁`-definible en S¹₂**: con la cota `t(x) = x`. En todo modelo, `x ≤ x` (axioma 6 con
`y = x`) y el único `y` con `y = x` es `x`; en ℕ también. -/
theorem definible_id : DefinibleSigma1 id := by
  refine ⟨grafoId, esSigma1_grafoId, ⟨Term.var 0, fun M _ hM => ⟨?_, ?_⟩⟩, ?_⟩
  · intro x
    refine ⟨x, ?_, ?_⟩
    · have := hM.basic.b6 x x
      simpa using this
    · simp [grafoId, Formula.Realize, BoundedFormula.Realize]
  · intro x y z hy hz
    simp [grafoId, Formula.Realize, BoundedFormula.Realize] at hy hz
    rw [hy, hz]
  · intro n
    simp [grafoId, Formula.Realize, BoundedFormula.Realize]

/-- Y es de tiempo polinomial (`esPolinomial_id`): el teorema de Buss vale para ella, como debe. -/
theorem buss_vale_en_id : DefinibleSigma1 id ∧ EsPolinomial (id : ℕ → ℕ) :=
  ⟨definible_id, esPolinomial_id⟩

end Acotada
end Sagitta.Map
