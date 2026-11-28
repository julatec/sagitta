import Sagitta.Map.Clases
import Sagitta.Map.Componer
import Sagitta.Map.Cerradura

/-!
# Sistemas de pruebas (Cook y Reckhow, 1979)

Formalización de las definiciones 1.3 y 1.5 y de las proposiciones 1.4 (una dirección, en su parte lógica) y 1.6 de
S. A. Cook y R. A. Reckhow, «The relative efficiency of propositional proof systems», *Journal of Symbolic Logic*
44 (1979), 36–50. No hay nada propio: es un ejercicio.

* **Definición 1.3.** Un *sistema de pruebas* para un conjunto `L` de cadenas es una función `f` de tiempo
  polinomial cuya imagen es exactamente `L`. Si `f π = y`, la cadena `π` es una *prueba* de `y`. El sistema es
  *polinomialmente acotado* si todo `y ∈ L` tiene una prueba de largo polinomial en el de `y`.
* **Definición 1.5.** `S₂` *p-simula* a `S₁` si hay una traducción de tiempo polinomial de las pruebas de `S₁` a
  pruebas de `S₂` de lo mismo.
* **Proposición 1.4.** `L` está en `NP` si y solo si `L` es vacío o tiene un sistema de pruebas polinomialmente
  acotado. Aquí va la parte lógica de una dirección: un sistema acotado da la forma de `NP`
  (`y ∈ L ↔ existe una prueba corta`).
* **Proposición 1.6.** Si `S₂` p-simula a un sistema acotado, `S₂` es acotado.

## Lo que este archivo no hace

* No prueba `L ∈ NP` con las definiciones de `Clases.lean`: el verificador sería «calcular `f π` y comparar con
  `y`», y la máquina que compara dos cadenas no está construida.
* En `PSimula` la cota de largo de la traducción va como dato. En el artículo sale de que toda función de tiempo
  polinomial alarga su entrada a lo sumo un polinomio; aquí ese hecho no está enunciado por separado.
* No hay nada de sistemas concretos (Frege, Frege extendido), que son el resto del artículo.
-/

namespace Sagitta.Map
namespace SistemaDePruebas

open Polynomial

/-- **Definición 1.3.** Un sistema de pruebas para `L`: una función de tiempo polinomial cuya imagen es `L`. -/
structure Sistema (L : Set (List Bool)) where
  /-- De una prueba, lo que prueba. -/
  f : List Bool → List Bool
  /-- Revisar una prueba es rápido. -/
  rapido : EsPolinomial f
  /-- Corrección: solo se prueban miembros de `L`. -/
  correcto : ∀ π, f π ∈ L
  /-- Completitud: todo miembro de `L` tiene alguna prueba. -/
  completo : ∀ y ∈ L, ∃ π, f π = y

variable {L : Set (List Bool)}

/-- La imagen de un sistema de pruebas es exactamente `L`. -/
theorem imagen (S : Sistema L) : Set.range S.f = L := by
  ext y
  constructor
  · rintro ⟨π, rfl⟩
    exact S.correcto π
  · intro hy
    exact S.completo y hy

/-- **Polinomialmente acotado**, con el polinomio a la vista: todo miembro de `L` tiene una prueba de largo a lo
sumo `p` del suyo. -/
def AcotadoPor (S : Sistema L) (p : Polynomial ℕ) : Prop :=
  ∀ y ∈ L, ∃ π, S.f π = y ∧ π.length ≤ p.eval y.length

/-- **Polinomialmente acotado** (Definición 1.3). -/
def Acotado (S : Sistema L) : Prop := ∃ p : Polynomial ℕ, AcotadoPor S p

/-- **La forma de `NP`** (Proposición 1.4, la parte lógica de una dirección). Con un sistema acotado, estar en `L`
es tener una prueba corta. La prueba es el certificado; revisar es calcular `f`. -/
theorem forma_np (S : Sistema L) {p : Polynomial ℕ} (h : AcotadoPor S p) (y : List Bool) :
    y ∈ L ↔ ∃ π : List Bool, π.length ≤ p.eval y.length ∧ S.f π = y := by
  constructor
  · intro hy
    obtain ⟨π, hπ, hlen⟩ := h y hy
    exact ⟨π, hlen, hπ⟩
  · rintro ⟨π, -, rfl⟩
    exact S.correcto π

/-- **Definición 1.5.** `S₂` p-simula a `S₁`: una traducción de tiempo polinomial `g` lleva cada prueba de `S₁` a
una prueba de `S₂` de lo mismo. La cota `q` del largo de la traducción va como dato. -/
def PSimula (S₂ S₁ : Sistema L) : Prop :=
  ∃ (g : List Bool → List Bool) (q : Polynomial ℕ),
    EsPolinomial g ∧ (∀ π, S₂.f (g π) = S₁.f π) ∧ ∀ π, (g π).length ≤ q.eval π.length

/-- Todo sistema se simula a sí mismo. -/
theorem pSimula_refl (S : Sistema L) : PSimula S S :=
  ⟨id, X, esPolinomial_id, fun _ => rfl, fun π => by simp⟩

/-- La p-simulación es transitiva: las traducciones se componen. -/
theorem pSimula_trans {S₁ S₂ S₃ : Sistema L} (h₃₂ : PSimula S₃ S₂) (h₂₁ : PSimula S₂ S₁) : PSimula S₃ S₁ := by
  obtain ⟨g, q, hg, hgf, hgl⟩ := h₃₂
  obtain ⟨g', q', hg', hgf', hgl'⟩ := h₂₁
  refine ⟨g ∘ g', q.comp q', Componer.esPolinomial_comp g' g hg' hg, fun π => ?_, fun π => ?_⟩
  · rw [Function.comp_apply, hgf, hgf']
  · rw [Function.comp_apply, eval_comp]
    exact (hgl (g' π)).trans (Cerradura.eval_mono q (hgl' π))

/-- **Proposición 1.6.** Si `S₂` p-simula a un sistema polinomialmente acotado, también es polinomialmente
acotado: se traduce la prueba corta, y la traducción la alarga a lo sumo un polinomio. -/
theorem acotado_de_pSimula {S₁ S₂ : Sistema L} (hsim : PSimula S₂ S₁) (h : Acotado S₁) : Acotado S₂ := by
  obtain ⟨g, q, -, hgf, hgl⟩ := hsim
  obtain ⟨p, hp⟩ := h
  refine ⟨q.comp p, fun y hy => ?_⟩
  obtain ⟨π, hπ, hlen⟩ := hp y hy
  refine ⟨g π, by rw [hgf, hπ], ?_⟩
  rw [eval_comp]
  exact (hgl π).trans (Cerradura.eval_mono q hlen)

/-- Dos sistemas que se simulan uno al otro son acotados a la vez. Es lo que permite hablar de «los sistemas de
Frege» como una sola clase. -/
theorem acotado_iff_de_equivalentes {S₁ S₂ : Sistema L} (h₂₁ : PSimula S₂ S₁) (h₁₂ : PSimula S₁ S₂) :
    Acotado S₁ ↔ Acotado S₂ :=
  ⟨acotado_de_pSimula h₂₁, acotado_de_pSimula h₁₂⟩

end SistemaDePruebas
end Sagitta.Map
