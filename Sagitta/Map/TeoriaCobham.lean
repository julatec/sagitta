import Sagitta.Map.Cobham
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Complexity

/-!
# La teoría de las funciones de Cobham (R2)

Segundo paso de la ruta por modelos.

## Qué hay

* **`LC`**: el lenguaje de primer orden de Mathlib con **un símbolo de función por cada programa** de `Cob` y
  ninguna relación aparte de la igualdad.
* **`ℕ` como estructura** de `LC`: cada símbolo se interpreta con su programa.
* **`TC`**: la teoría formada por **todo enunciado universal verdadero en ℕ**. Es universal y tiene modelo.
* **`transferir`**: lo que vale en ℕ sin cuantificadores vale en todo modelo de `TC`, para todos sus elementos,
  también los no estándar. Es por donde pasa todo el arranque de `Cobham.lean`.
* **`cerrar`**: lo que se genera desde una parte de un modelo de `TC` aplicando símbolos es otra vez un modelo de
  `TC`. Es el paso que la prueba de Zambella y la de Avigad usan una y otra vez.

## Una decisión de diseño, mía

Las fuentes trabajan sobre **PV**: un lenguaje así con una lista de axiomas universales, y prueban que esos axiomas
alcanzan. Aquí la teoría es *todo* lo universal verdadero. Para el teorema del testigo da lo mismo: la prueba solo
usa que la teoría es universal, que admite definición por casos y que es verdadera en ℕ. Lo que se pierde es saber
que alcanza la teoría débil, que es un dato de fuerza de la prueba y no del algoritmo. Con esto el arranque de PV,
que ninguna de las dos fuentes demuestra, se vuelve cómputo en ℕ (`Cobham.lean`).

## Qué no hay

* **El modelo saturado de Herbrand** (Avigad, teorema 3.2). Es el paso R3, y el caro.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language

/-- **El lenguaje**: un símbolo de función de aridad `n` por cada programa de `n` argumentos. -/
abbrev LC : Language := ⟨Cob, fun _ => Empty⟩

/-- ℕ, con cada símbolo interpretado por su programa. -/
instance : LC.Structure ℕ where
  funMap c v := c.eval v
  RelMap r _ := Empty.elim r

/-- Aplicar un símbolo en una estructura cualquiera. -/
def ap {M : Type} [LC.Structure M] {n : ℕ} (c : Cob n) (v : Fin n → M) : M := Structure.funMap (L := LC) c v

@[simp] theorem ap_nat {n : ℕ} (c : Cob n) (v : Fin n → ℕ) : ap c v = c.eval v := rfl

/-- **La teoría**: todo enunciado universal verdadero en ℕ. -/
def TC : LC.Theory := {φ | φ.IsUniversal ∧ ℕ ⊨ φ}

instance : TC.IsUniversal := ⟨fun _ h => h.1⟩

instance : ℕ ⊨ TC := ⟨fun _ h => h.2⟩

/-- La teoría tiene modelo: ℕ. -/
theorem TC_satisfacible : TC.IsSatisfiable := ⟨Theory.ModelType.of TC ℕ⟩

/-- Cuantificar universalmente todas las variables de una fórmula universal da una fórmula universal. -/
theorem isUniversal_alls {α : Type} :
    ∀ {n : ℕ} {φ : LC.BoundedFormula α n}, φ.IsUniversal → φ.alls.IsUniversal
  | 0, _, h => h
  | _ + 1, φ, h => by
      change (BoundedFormula.all φ).alls.IsUniversal
      exact isUniversal_alls h.all

/-- **Lo que vale en ℕ sin cuantificadores vale en todo modelo de la teoría**, en todos sus elementos. -/
theorem transferir {M : Type} [LC.Structure M] [M ⊨ TC] {n : ℕ} (φ : LC.BoundedFormula Empty n)
    (hqf : φ.IsQF) (h : ∀ xs : Fin n → ℕ, φ.Realize Empty.elim xs) :
    ∀ xs : Fin n → M, φ.Realize Empty.elim xs := by
  have hσ : φ.alls ∈ TC := ⟨isUniversal_alls hqf.isUniversal, by
    change Formula.Realize φ.alls _
    exact BoundedFormula.realize_alls.mpr fun xs => by convert h xs⟩
  intro xs
  have hM := Theory.realize_sentence_of_mem (M := M) TC hσ
  have := BoundedFormula.realize_alls.mp hM xs
  convert this

/-- El término que aplica un programa a las variables `0, …, n - 1`. -/
def aplicado {n : ℕ} (c : Cob n) : LC.Term (Empty ⊕ Fin n) :=
  Term.func (L := LC) c fun i => Term.var (Sum.inr i)

/-- La ecuación entre dos programas, con sus variables libres. -/
def ecuacion {n : ℕ} (p q : Cob n) : LC.BoundedFormula Empty n :=
  Term.bdEqual (aplicado p) (aplicado q)

theorem realize_ecuacion {M : Type} [LC.Structure M] {n : ℕ} (p q : Cob n) (xs : Fin n → M) :
    (ecuacion p q).Realize Empty.elim xs ↔ ap p xs = ap q xs := by
  simp only [ecuacion, aplicado, BoundedFormula.realize_bdEqual, Term.realize_func, Term.realize_var,
    Sum.elim_inr]
  exact Iff.rfl

/-- **Una identidad entre programas pasa a todo modelo.** Si dos programas dan lo mismo en ℕ, sus símbolos dan
lo mismo en cualquier modelo de la teoría. -/
theorem identidad {M : Type} [LC.Structure M] [M ⊨ TC] {n : ℕ} (p q : Cob n)
    (h : ∀ v, p.eval v = q.eval v) (xs : Fin n → M) : ap p xs = ap q xs :=
  (realize_ecuacion p q xs).mp
    (transferir (ecuacion p q) (BoundedFormula.IsAtomic.equal _ _).isQF
      (fun v => (realize_ecuacion p q v).mpr (by rw [ap_nat, ap_nat]; exact h v)) xs)

/-- **Cerrar da un modelo.** La subestructura generada por una parte de un modelo de la teoría es también un
modelo: la teoría es universal. -/
theorem cerrar {M : Type} [LC.Structure M] [M ⊨ TC] (S : Set M) : (Substructure.closure LC S) ⊨ TC :=
  Substructure.models_of_isUniversal _ TC

/-! ## Un ejemplo del arranque, en un modelo cualquiera

La recursión sobre la notación cumple su ecuación en todo modelo, también en los elementos no estándar: el
símbolo de `buscar f` aplicado a `0` vale lo que el de su caso base. -/

example {M : Type} [LC.Structure M] [M ⊨ TC] {n : ℕ} (f : Cob (n + 1)) (y : Fin n → M) :
    ap (fijar (buscar f) .cero) y =
      ap (c3 .cond (fijar f .cero) .cero uno) y :=
  identidad _ _ (fun v => by rw [eval_fijar, eval_cero]; exact eval_rec_cero _ _ _ v) y

end Cobham
end Sagitta.Map
