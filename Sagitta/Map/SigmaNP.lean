import Sagitta.Map.Acotada
import Sagitta.Map.Clases

/-!
# NP y coNP como clases de fórmulas: `Σᵇ₁` y `Πᵇ₁`

Wrathall (1976) y Stockmeyer (1976): sobre ℕ, las propiedades que se escriben con una fórmula `Σᵇ₁` son exactamente
las de NP. Aquí se **enuncia** (`SigmaIgualNP`), y de ese enunciado se **prueba**, sin nada más:

* `piIgualCoNP_de_sigma`: entonces las `Πᵇ₁` son exactamente coNP. Es dualidad: negar una `Πᵇ₁` da una `Σᵇ₁`
  (cláusula (d) de Buss) y negar un problema de coNP da uno de NP.
* `npDistintoCoNP_iff`: entonces NP ≠ coNP si y solo si hay una propiedad que se escribe con una `Πᵇ₁` y con
  ninguna `Σᵇ₁`. La pregunta de complejidad es una pregunta sobre qué fórmulas alcanzan.

**De cadenas a números.** Un problema de `Clases.lean` decide cadenas de bits; una fórmula habla de números. La
cadena `w` va al número cuyo binario es `1` seguido de `w` (`numeroDe`), que es inyectivo (`numeroDe_inyectiva`):
dos cadenas distintas nunca caen en el mismo número.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-! ## De cadenas a números -/

/-- El número cuyo binario es `1` seguido de `w`, con el primer bit de `w` como el menos significativo. -/
def numeroDe (w : List Bool) : ℕ :=
  w.foldr (fun b n => 2 * n + if b then 1 else 0) 1

@[simp] theorem numeroDe_nil : numeroDe [] = 1 := rfl

@[simp] theorem numeroDe_cons (b : Bool) (w : List Bool) :
    numeroDe (b :: w) = 2 * numeroDe w + if b then 1 else 0 := rfl

theorem uno_le_numeroDe (w : List Bool) : 1 ≤ numeroDe w := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp; omega

/-- **Dos cadenas distintas van a números distintos.** -/
theorem numeroDe_inyectiva : Function.Injective numeroDe := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b w =>
      have := uno_le_numeroDe w
      cases b <;> simp at h <;> omega
  | cons a u ih =>
    intro v h
    cases v with
    | nil =>
      have := uno_le_numeroDe u
      cases a <;> simp at h; omega
    | cons b w =>
      have hu := uno_le_numeroDe u
      have hw := uno_le_numeroDe w
      cases a <;> cases b <;> simp at h
      · exact congrArg _ (ih (by omega))
      · omega
      · omega
      · exact congrArg _ (ih (by omega))

/-! ## Definir un problema con una fórmula -/

/-- **`φ(x)` define el problema `L`**: `w` es un caso «sí» de `L` si y solo si `φ` vale en ℕ para `numeroDe w`. -/
def DefinidoPor (φ : L.Formula (Fin 1)) (P : Problema) : Prop :=
  ∀ w, P w = true ↔ φ.Realize ![numeroDe w]

/-- **Wrathall–Stockmeyer** (1976): NP son exactamente los problemas que define una fórmula `Σᵇ₁`. Abierto aquí; es
un teorema conocido. -/
def SigmaIgualNP : Prop :=
  ∀ P : Problema, P ∈ NP ↔ ∃ φ : L.Formula (Fin 1), EsSigma1 φ ∧ DefinidoPor φ P

/-- coNP son exactamente los problemas que define una fórmula `Πᵇ₁`. -/
def PiIgualCoNP : Prop :=
  ∀ P : Problema, P ∈ coNP ↔ ∃ φ : L.Formula (Fin 1), EsPi1 φ ∧ DefinidoPor φ P

/-- Negar la fórmula define el problema negado. -/
theorem definidoPor_not {φ : L.Formula (Fin 1)} {P : Problema} (h : DefinidoPor φ P) :
    DefinidoPor φ.not (fun x => !P x) := by
  intro w
  have := h w
  simp only [Formula.realize_not]
  cases hP : P w <;> simp_all

/-- Y define el problema original si la negada define el negado. -/
theorem definidoPor_de_not {φ : L.Formula (Fin 1)} {P : Problema} (h : DefinidoPor φ (fun x => !P x)) :
    DefinidoPor φ.not P := by
  intro w
  have := h w
  simp only [Formula.realize_not]
  cases hP : P w <;> simp_all

/-- **Si `Σᵇ₁` es NP, entonces `Πᵇ₁` es coNP.** Por dualidad, sin nada más: un problema está en coNP si su negado
está en NP, y negar una `Σᵇ₁` da una `Πᵇ₁` (y al revés). -/
theorem piIgualCoNP_de_sigma (h : SigmaIgualNP) : PiIgualCoNP := by
  intro P
  constructor
  · intro hP
    obtain ⟨ψ, hψ, hdef⟩ := (h _).1 hP
    exact ⟨ψ.not, EsPi1.no hψ, definidoPor_de_not hdef⟩
  · rintro ⟨φ, hφ, hdef⟩
    exact (h _).2 ⟨φ.not, EsSigma1.no hφ, definidoPor_not hdef⟩

/-- Negar dos veces deja el problema igual. -/
theorem no_no (P : Problema) : (fun x => !(fun x => !P x) x) = P := by
  funext x; simp

/-- **coNP ⊆ NP implica NP ⊆ coNP**: si el negado de todo problema de NP está en NP… es la simetría que hace que
basta una inclusión para la igualdad. -/
theorem np_sub_conp_de_conp_sub_np (h : coNP ⊆ NP) : NP ⊆ coNP := by
  intro P hP
  show (fun x => !P x) ∈ NP
  apply h
  show (fun x => !(fun x => !P x) x) ∈ NP
  rw [no_no]; exact hP

/-- **NP ≠ coNP como pregunta sobre fórmulas.** Si `Σᵇ₁` es NP, entonces NP ≠ coNP si y solo si hay un problema
que una `Πᵇ₁` define y ninguna `Σᵇ₁`. -/
theorem npDistintoCoNP_iff (h : SigmaIgualNP) :
    NPDistintoCoNP ↔ ∃ P : Problema, (∃ φ : L.Formula (Fin 1), EsPi1 φ ∧ DefinidoPor φ P) ∧
      ¬ ∃ ψ : L.Formula (Fin 1), EsSigma1 ψ ∧ DefinidoPor ψ P := by
  have hpi := piIgualCoNP_de_sigma h
  constructor
  · intro hne
    by_contra hno
    apply hne
    have sub : coNP ⊆ NP := by
      intro P hP
      by_contra hnP
      exact hno ⟨P, (hpi P).1 hP, fun hs => hnP ((h P).2 hs)⟩
    exact Set.Subset.antisymm (np_sub_conp_de_conp_sub_np sub) sub
  · rintro ⟨P, hPi, hnoSigma⟩ heq
    apply hnoSigma
    have : P ∈ NP := heq ▸ (hpi P).2 hPi
    exact (h P).1 this

end Acotada
end Sagitta.Map
