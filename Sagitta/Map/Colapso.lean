import Sagitta.Map.Clases
import Sagitta.Map.Componer
import Sagitta.Map.MaquinasBasicas

/-!
# El colapso del segundo piso: si P = NP, entonces Σ₂ ⊆ P

Es el primer escalón del teorema clásico de Meyer y Stockmeyer (1972; Stockmeyer, 1976): si `P = NP`, toda la
jerarquía polinomial colapsa a `P`. Aquí va solo el paso de uno a dos pisos, como ejercicio. No hay nada nuevo.

La idea, de adentro hacia afuera:

1. el piso interno, «para todo `z` corto, `V (w, z)`», es un problema de coNP;
2. `P` es cerrada bajo negación, así que con `P = NP` ese problema está en `P`;
3. entonces el piso externo tiene un verificador polinomial: es un problema de NP, y por lo tanto de `P`.

No hace falta Cook–Levin: a nivel de clases, «convertir el resolvedor en fórmula» lo absorbe la definición de NP.
El cálculo de lo que cuesta cada piso (el exponente se eleva en cada nivel) está en `Cerradura.lean`:
`piso_iter`, `pisos_fijos`, `pisos_crecientes_rompen`.

## La definición de Σ₂ que se usa, y en qué difiere de la usual

La usual es: `L x ↔ ∃ y corto, ∀ z corto, V (x, y, z)`, con `V` sobre la terna. Aquí el verificador recibe el par
`(x, y)` **ya codificado como una sola cadena**, `w = cod (x, y) = delimita x ++ y`, y aparte `z`:

  `L x ↔ ∃ y, |y| ≤ p(|x|) ∧ ∀ z, |z| ≤ q(|w|) → V (w, z)`.

Es una **variante**, elegida para que el piso interno sea directamente un `Problema` sobre `w` y no haya que
construir una máquina que reasocie pares. Las dos formas se traducen una en la otra con funciones polinomiales
(reasociar `((x, y), z)` y `(x, (y, z))`, y pasar de una cota en `|x|` a una en `|w|`), pero esa equivalencia no
está probada aquí. Tampoco se prueba `NP ⊆ Σ₂`: pediría un verificador definido también sobre cadenas `w` que no
codifican ningún par, y eso es una máquina nueva.
-/

open Computability Turing

namespace Sagitta.Map
namespace Colapso

open CodBits

/-- **Σ₂**, el segundo piso de la jerarquía polinomial, en la variante descrita en la cabecera. -/
def Sigma2 : Clase :=
  {L | ∃ (p q : Polynomial ℕ) (V : List Bool × List Bool → Bool),
      EsPolinomial V ∧
      ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧
        ∀ z : List Bool, z.length ≤ q.eval (cod (x, y)).length → V (cod (x, y), z) = true}

/-! ## P es cerrada bajo negación -/

/-- Negar un problema de `P` da un problema de `P`. -/
theorem p_cerrada_no {L : Problema} (h : L ∈ P) : (fun x => !L x) ∈ P :=
  Componer.esPolinomial_comp L (fun b : Bool => !b) h Basicas.esPolinomial_no

/-- **Si P = NP, entonces coNP ⊆ P.** -/
theorem conp_sub_p (h : PIgualNP) : coNP ⊆ P := by
  intro L hL
  have h1 : (fun x => !L x) ∈ P := by
    rw [show P = NP from h]; exact hL
  have h2 := p_cerrada_no h1
  have e : (fun x => !(fun x => !L x) x) = L := by funext x; simp
  rw [e] at h2
  exact h2

/-! ## Leer un objeto por su codificación

Una máquina que calcula `g` sobre cadenas calcula, sin cambiar nada, `g ∘ cod` sobre cualquier tipo codificado:
la cinta inicial es la misma. -/

theorem esPolinomial_de_cod {α β : Type} [CodBits α] [CodBits β] {g : List Bool → β}
    (hg : EsPolinomial g) : EsPolinomial (fun a : α => g (cod a)) := by
  obtain ⟨m⟩ := hg
  exact ⟨{ tm := m.tm
           inputAlphabet := m.inputAlphabet
           outputAlphabet := m.outputAlphabet
           time := m.time
           outputsFun := fun a => m.outputsFun (cod a) }⟩

/-! ## El piso interno -/

/-- El piso interno: «para todo `z` de largo a lo sumo `q(|w|)`, `V (w, z)`». -/
noncomputable def interno (q : Polynomial ℕ) (V : List Bool × List Bool → Bool) : Problema :=
  fun w => @decide (∀ z : List Bool, z.length ≤ q.eval w.length → V (w, z) = true) (Classical.propDecidable _)

theorem interno_iff (q : Polynomial ℕ) (V : List Bool × List Bool → Bool) (w : List Bool) :
    interno q V w = true ↔ ∀ z : List Bool, z.length ≤ q.eval w.length → V (w, z) = true := by
  simp [interno]

/-- **El piso interno está en coNP**: su negación tiene por certificado un `z` donde `V` falla. -/
theorem interno_en_coNP (q : Polynomial ℕ) {V : List Bool × List Bool → Bool} (hV : EsPolinomial V) :
    interno q V ∈ coNP := by
  refine ⟨q, fun r => !V r, Componer.esPolinomial_comp V (fun b : Bool => !b) hV Basicas.esPolinomial_no, ?_⟩
  intro w
  have h := interno_iff q V w
  change (!interno q V w) = true ↔ ∃ z : List Bool, z.length ≤ q.eval w.length ∧ (!V (w, z)) = true
  constructor
  · intro hno
    have hf : ¬ (interno q V w = true) := by
      intro ht; rw [ht] at hno; simp at hno
    rw [h] at hf
    by_contra hne
    apply hf
    intro z hz
    by_contra hv
    exact hne ⟨z, hz, by simpa using hv⟩
  · rintro ⟨z, hz, hv⟩
    have hf : ¬ (interno q V w = true) := by
      rw [h]; intro hall
      have := hall z hz
      simp [this] at hv
    simpa using hf

/-! ## El teorema -/

/-- **Si P = NP, entonces Σ₂ ⊆ P.** El piso interno cae a `P` por `conp_sub_p`; con eso el piso externo es un
problema de NP, cuyo verificador es el resolvedor del interno leído sobre el par `(x, y)`. -/
theorem sigma2_sub_p (h : PIgualNP) : Sigma2 ⊆ P := by
  rintro L ⟨p, q, V, hV, hL⟩
  have hint : EsPolinomial (interno q V) := conp_sub_p h (interno_en_coNP q hV)
  have hW : EsPolinomial (fun r : List Bool × List Bool => interno q V (cod r)) :=
    esPolinomial_de_cod hint
  have hNP : L ∈ NP := by
    refine ⟨p, fun r => interno q V (cod r), hW, fun x => ?_⟩
    rw [hL x]
    constructor
    · rintro ⟨y, hy, hz⟩
      exact ⟨y, hy, (interno_iff q V _).2 hz⟩
    · rintro ⟨y, hy, hz⟩
      exact ⟨y, hy, (interno_iff q V _).1 hz⟩
  rw [show P = NP from h]
  exact hNP

end Colapso
end Sagitta.Map
