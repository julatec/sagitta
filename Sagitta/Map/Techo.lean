import Sagitta.Map.PrimerFallo
import Sagitta.Map.Cerradura
import Mathlib.SetTheory.Ordinal.Notation

/-!
# El techo de Peano y el enunciado del Teorema 4

**Teorema 4 (Ben-David y Halevi, 1991).** La teoría demuestra `P ≠ NP` si y solo si la tasa de aproximación de SAT
por `P` está dominada por alguna función `F_α`, con `α < ε₀`, de la jerarquía de Wainer.

Este archivo **enuncia** el teorema; no lo demuestra. Lo que usa:

* la tasa `R` es `PrimerFallo.tasa`;
* la jerarquía de Wainer bajo `ε₀` ya está en Mathlib: `ONote.fastGrowing`, sobre las notaciones `ONote` (formas
  normales de Cantor). Mathlib prueba `fastGrowing 1 = fun n => 2 * n` y `fastGrowing 2 = fun n => 2 ^ n * n`, que
  son `F₁` y `F₂` tal como las define el artículo;
* «la teoría demuestra» es un **parámetro** `Demuestra : Prop`. Aquí no hay ninguna teoría formalizada. En el
  artículo es `PA₁`: Peano más todas las afirmaciones `Π₁` verdaderas. Cuando se integre una biblioteca con Peano
  (el proyecto Foundation la tiene), el parámetro se reemplaza por la demostrabilidad de verdad.

Lo único que se prueba es lo que no necesita teoría alguna: que estar bajo el techo implica que la tasa es total, y
por lo tanto que el problema no está en la clase (la parte «semántica» de una de las direcciones); y que el segundo
nivel de la jerarquía ya se sale de lo polinomial, que es el puente con `Cerradura.lean`.
-/

namespace Sagitta.Map
namespace Techo

open PrimerFallo

/-- `f` domina a `g`: desde algún punto en adelante, `g` queda estrictamente por debajo. -/
def Domina (f g : ℕ → ℕ) : Prop := ∃ N, ∀ n ≥ N, g n < f n

/-- **Bajo el techo de Peano.** Una función está dominada por algún nivel `F_α`, `α < ε₀`, de la jerarquía de
Wainer. Las notaciones en forma normal (`ONote.NF`) son exactamente los ordinales menores que `ε₀`. -/
def BajoElTecho (g : ℕ → ℕ) : Prop := ∃ o : ONote, o.NF ∧ Domina (ONote.fastGrowing o) g

variable (M : ℕ → Problema) (L : Problema)

/-- **La tasa, bajo el techo.** Desde algún punto, la tasa está definida y queda por debajo de un mismo nivel de la
jerarquía. Se dice así porque la tasa es una función parcial. -/
def TasaBajoElTecho : Prop :=
  ∃ o : ONote, o.NF ∧ ∃ N, ∀ i ≥ N, ∃ h : (tasa M L i).Dom, (tasa M L i).get h < ONote.fastGrowing o i

/-- **La tasa supera el techo.** Está definida siempre y ningún nivel de la jerarquía la domina. Es lo que tendría
que pasar para que `L ∉ C` fuera verdadera e indemostrable. -/
def TasaSuperaElTecho : Prop := (∀ i, (tasa M L i).Dom) ∧ ¬ TasaBajoElTecho M L

/-- **El enunciado del Teorema 4**, con la demostrabilidad como parámetro. `Demuestra` representa «la teoría
demuestra que `L` no está en la clase enumerada por `M`». No está probado: es una proposición, como `PLSEnFP`. -/
def Teorema4 (Demuestra : Prop) : Prop := Demuestra ↔ TasaBajoElTecho M L

/-! ## Lo que se puede probar sin teoría -/

/-- Si la tasa está definida desde algún punto, está definida siempre: el dominio es cerrado hacia abajo. -/
theorem dom_de_eventual (h : ∃ N, ∀ i ≥ N, (tasa M L i).Dom) (i : ℕ) : (tasa M L i).Dom := by
  obtain ⟨N, hN⟩ := h
  intro j hj
  exact hN (max i N) (le_max_right _ _) j (lt_of_lt_of_le hj (le_max_left _ _))

/-- **Bajo el techo implica total.** -/
theorem total_de_bajoElTecho (h : TasaBajoElTecho M L) (i : ℕ) : (tasa M L i).Dom := by
  obtain ⟨o, -, N, hN⟩ := h
  exact dom_de_eventual M L ⟨N, fun i hi => (hN i hi).1⟩ i

/-- **La mitad semántica.** Si la tasa está bajo el techo, `L` de verdad no está en la clase. Es lo que hace sólida
a la dirección «si» del Teorema 4: lo que la teoría demostraría es cierto. -/
theorem no_en_clase_de_bajoElTecho (h : TasaBajoElTecho M L) : L ∉ Set.range M :=
  (tasa_total_iff M L).mp (total_de_bajoElTecho M L h)

/-- Las dos posibilidades cuando `L` no está en la clase: o la tasa queda bajo el techo, o lo supera. Según el
Teorema 4, la primera es «demostrable» y la segunda «verdadera pero indemostrable». -/
theorem bajo_o_supera (h : L ∉ Set.range M) : TasaBajoElTecho M L ∨ TasaSuperaElTecho M L := by
  by_cases hb : TasaBajoElTecho M L
  · exact Or.inl hb
  · exact Or.inr ⟨(tasa_total_iff M L).mpr h, hb⟩

/-! ## El puente con `Cerradura.lean` -/

/-- El primer nivel de la jerarquía es duplicar: es polinomial. -/
theorem nivel_uno_acotado : Cerradura.Acotada (ONote.fastGrowing 1) := by
  rw [ONote.fastGrowing_one]
  exact Cerradura.duplicar_acotada

/-- **El segundo nivel ya no es polinomial.** `F₂(n) = 2ⁿ · n` no queda bajo ningún polinomio. Toda la teoría de
complejidad vive por debajo de este peldaño; el techo de Peano está al final de la escalera. -/
theorem nivel_dos_no_acotado : ¬ Cerradura.Acotada (ONote.fastGrowing 2) := by
  rw [ONote.fastGrowing_two]
  rintro ⟨p, hp⟩
  apply Cerradura.dos_pow_no_acotada
  refine ⟨p + 1, fun n => ?_⟩
  rw [Polynomial.eval_add, Polynomial.eval_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · exact (Nat.le_mul_of_pos_right _ hn).trans ((hp n).trans (Nat.le_succ _))

end Techo
end Sagitta.Map
