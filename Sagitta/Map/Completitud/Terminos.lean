import Sagitta.Map.Completitud.Henkin
import Mathlib.ModelTheory.Quotients

/-!
# Completitud, fase F3: el modelo de términos y el lema de verdad

Tercera fase del teorema de completitud. De un
conjunto maximal de Henkin `T` (F2) sale un modelo: los términos con variables en `ℕ`, identificando `s` con `t` cuando
`s = t` está en `T`. El **lema de verdad** dice que en ese modelo, con la asignación `a ↦ [a]`, una fórmula vale si y
solo si está en `T`.

## Lo que se prueba

* **La altura** de una fórmula (`alt`, cuántos conectivos y cuantificadores) no cambia al sustituir ni al reetiquetar
  (`alt_instanciar`). Es la medida de la inducción: el caso `∀ψ` pasa a `ψ(t)`, que no es una subfórmula.
* **El modelo** (`Modelo hT`): los términos módulo la igualdad de `T`. Es una estructura porque la igualdad de `T` es
  una congruencia (`func_congr`, `rel_congr`), que sale de las reglas de F1.
* **El lema de verdad** (`verdad`): `φ` vale en el modelo con `a ↦ [a]` si y solo si `φ ∈ T`.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-! ## La altura -/

/-- **La altura** de una fórmula: los `→` y los `∀`. -/
def alt {α : Type} : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => alt φ + alt ψ + 1
  | _, .all φ => alt φ + 1

theorem alt_castLE {α : Type} : ∀ {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormula α m), alt (φ.castLE h) = alt φ
  | _, _, _, .falsum => rfl
  | _, _, _, .equal _ _ => rfl
  | _, _, _, .rel _ _ => rfl
  | _, _, h, .imp φ ψ => by simp only [BoundedFormula.castLE, alt, alt_castLE h φ, alt_castLE h ψ]
  | _, _, h, .all φ => by simp only [BoundedFormula.castLE, alt, alt_castLE _ φ]

theorem alt_mapTermRel {α β : Type} {g : ℕ → ℕ} (ft : ∀ n, L.Term (α ⊕ Fin n) → L.Term (β ⊕ Fin (g n)))
    (fr : ∀ n, L.Relations n → L.Relations n) (h : ∀ n, L.BoundedFormula β (g (n + 1)) → L.BoundedFormula β (g n + 1))
    (hh : ∀ n ψ, alt (h n ψ) = alt ψ) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), alt (φ.mapTermRel ft fr h) = alt φ
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp φ ψ => by
    simp only [BoundedFormula.mapTermRel, alt, alt_mapTermRel ft fr h hh φ, alt_mapTermRel ft fr h hh ψ]
  | _, .all φ => by simp only [BoundedFormula.mapTermRel, alt, hh, alt_mapTermRel ft fr h hh φ]

theorem alt_relabel {α β : Type} {n : ℕ} (g : α → β ⊕ Fin n) {k : ℕ} (φ : L.BoundedFormula α k) :
    alt (φ.relabel g) = alt φ :=
  alt_mapTermRel _ _ _ (fun _ _ => alt_castLE _ _) φ

theorem alt_subst {α β : Type} {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) : alt (φ.subst f) = alt φ := by
  unfold BoundedFormula.subst
  exact alt_mapTermRel (g := id) _ _ (fun _ => id) (fun _ _ => rfl) φ

theorem alt_toFormula {α : Type} : ∀ {n : ℕ} (φ : L.BoundedFormula α n), alt φ.toFormula = alt φ
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp φ ψ => by simp only [BoundedFormula.toFormula, alt, alt_toFormula φ, alt_toFormula ψ]
  | _, .all φ => by simp only [BoundedFormula.toFormula, alt, alt_relabel, alt_toFormula φ]

theorem alt_instanciar (ψ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) : alt (instanciar ψ t) = alt ψ := by
  rw [instanciar, alt_subst, alt_toFormula]

/-! ## La igualdad de `T` es una congruencia -/

/-- Los argumentos de `x` hasta antes de `k` cambiados por los de `y`. -/
def mezcla {n : ℕ} (x y : Fin n → L.Term ℕ) (k : ℕ) : Fin n → L.Term ℕ := fun i => if (i : ℕ) < k then y i else x i

theorem mezcla_succ {n : ℕ} (x y : Fin n → L.Term ℕ) {k : ℕ} (hk : k < n) :
    mezcla x y (k + 1) = Function.update (mezcla x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
  funext i
  rw [Function.update_apply]
  unfold mezcla
  by_cases h : i = ⟨k, hk⟩
  · subst h; simp
  · have : (i : ℕ) ≠ k := fun h' => h (Fin.ext h')
    simp only [h, ↓reduceIte]
    split_ifs <;> first | rfl | omega

theorem mezcla_cero {n : ℕ} (x y : Fin n → L.Term ℕ) : mezcla x y 0 = x := by funext i; simp [mezcla]

theorem mezcla_n {n : ℕ} (x y : Fin n → L.Term ℕ) : mezcla x y n = y := by funext i; simp [mezcla, i.isLt]


namespace Maximal

variable {T : Set (L.Formula ℕ)} (hT : Maximal T)
include hT

theorem igual_refl (t : L.Term ℕ) : Term.equal t t ∈ T :=
  hT.cerrado (Γ := []) (by simp) (Der.igualRefl (Γ := []) (Δ := []) t)

theorem igual_simm {s t : L.Term ℕ} (h : Term.equal s t ∈ T) : Term.equal t s ∈ T :=
  hT.cerrado (by simpa using h) (Der.igualSimm s t)

theorem igual_trans {s t u : L.Term ℕ} (h₁ : Term.equal s t ∈ T) (h₂ : Term.equal t u ∈ T) : Term.equal s u ∈ T :=
  hT.cerrado (by intro χ hχ; simp at hχ; rcases hχ with rfl | rfl <;> assumption) (Der.igualTrans s t u)

/-- **Congruencia en las funciones**: argumentos iguales en `T` dan valores iguales en `T`. -/
theorem func_congr {n : ℕ} (f : L.Functions n) {x y : Fin n → L.Term ℕ} (h : ∀ i, Term.equal (x i) (y i) ∈ T) :
    Term.equal (Term.func f x) (Term.func f y) ∈ T := by
  have : ∀ k ≤ n, Term.equal (Term.func f x) (Term.func f (mezcla x y k)) ∈ T := by
    intro k hk
    induction k with
    | zero => rw [mezcla_cero]; exact hT.igual_refl _
    | succ k ih =>
      have hk' : k < n := hk
      rw [mezcla_succ x y hk']
      refine hT.igual_trans (ih (le_of_lt hk')) ?_
      have h1 : Term.equal (mezcla x y k ⟨k, hk'⟩) (y ⟨k, hk'⟩) ∈ T := by
        have : mezcla x y k ⟨k, hk'⟩ = x ⟨k, hk'⟩ := by simp [mezcla]
        rw [this]; exact h _
      exact hT.cerrado (by simpa using h1) (Der.congrFun1 f (mezcla x y k) ⟨k, hk'⟩ (y ⟨k, hk'⟩))
  simpa [mezcla_n] using this n le_rfl

/-- **Congruencia en las relaciones**, en una dirección. -/
theorem rel_congr {n : ℕ} (R : L.Relations n) {x y : Fin n → L.Term ℕ} (h : ∀ i, Term.equal (x i) (y i) ∈ T)
    (hx : R.formula x ∈ T) : R.formula y ∈ T := by
  have : ∀ k ≤ n, R.formula (mezcla x y k) ∈ T := by
    intro k hk
    induction k with
    | zero => rw [mezcla_cero]; exact hx
    | succ k ih =>
      have hk' : k < n := hk
      rw [mezcla_succ x y hk']
      have h1 : Term.equal (mezcla x y k ⟨k, hk'⟩) (y ⟨k, hk'⟩) ∈ T := by
        have : mezcla x y k ⟨k, hk'⟩ = x ⟨k, hk'⟩ := by simp [mezcla]
        rw [this]; exact h _
      exact hT.cerrado (by intro χ hχ; simp at hχ; rcases hχ with rfl | rfl; exacts [h1, ih (le_of_lt hk')])
        (Der.congrRel1 R (mezcla x y k) ⟨k, hk'⟩ (y ⟨k, hk'⟩))
  simpa [mezcla_n] using this n le_rfl

end Maximal

/-! ## El modelo -/

variable {T : Set (L.Formula ℕ)}

/-- La igualdad de `T`, como relación de equivalencia en los términos. -/
def setoide (hT : Maximal T) : Setoid (L.Term ℕ) where
  r s t := Term.equal s t ∈ T
  iseqv := ⟨hT.igual_refl, hT.igual_simm, hT.igual_trans⟩

/-- Los términos como estructura: las funciones construyen términos y las relaciones preguntan a `T`. -/
@[reducible] def estructuraTerminos (T : Set (L.Formula ℕ)) : L.Structure (L.Term ℕ) where
  funMap f ts := Term.func f ts
  RelMap R ts := R.formula ts ∈ T

instance prestructura (hT : Maximal T) : L.Prestructure (setoide hT) where
  toStructure := estructuraTerminos T
  fun_equiv {_ f} _ _ h := hT.func_congr f h
  rel_equiv {_ R} _ _ h := propext ⟨hT.rel_congr R h, hT.rel_congr R fun i => hT.igual_simm (h i)⟩

/-- **El modelo de términos.** -/
abbrev Modelo (hT : Maximal T) : Type := Quotient (setoide hT)

/-- La asignación: cada variable, su clase. -/
def val (hT : Maximal T) : ℕ → Modelo hT := fun a => Quotient.mk (setoide hT) (Term.var a)

theorem realize_term (hT : Maximal T) (t : L.Term ℕ) :
    t.realize (val hT) = Quotient.mk (setoide hT) t := by
  induction t with
  | var a => rfl
  | func f ts ih =>
    simp only [Term.realize, ih]
    exact funMap_quotient_mk' (setoide hT) f ts

theorem equal_mem_iff (hT : Maximal T) (s t : L.Term ℕ) :
    Quotient.mk (setoide hT) s = Quotient.mk (setoide hT) t ↔ Term.equal s t ∈ T :=
  Quotient.eq (r := setoide hT)

theorem relMap_mk (hT : Maximal T) {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term ℕ) :
    Structure.RelMap (M := Modelo hT) R (fun i => Quotient.mk (setoide hT) (ts i)) ↔ R.formula ts ∈ T := by
  exact (relMap_quotient_mk' (L := L) (setoide hT) R ts).trans Iff.rfl

/-! ## El lema de verdad -/

/-- Un término de una fórmula sin ligadas, con las variables en `ℕ`. -/
def baja (t : L.Term (ℕ ⊕ Fin 0)) : L.Term ℕ := t.relabel (Sum.elim id Fin.elim0)

theorem relabel_baja (t : L.Term (ℕ ⊕ Fin 0)) : (baja t).relabel Sum.inl = t := by
  rw [baja, Term.relabel_relabel]
  have : (Sum.inl ∘ Sum.elim id Fin.elim0 : ℕ ⊕ Fin 0 → ℕ ⊕ Fin 0) = id := by
    funext x; rcases x with x | x
    · rfl
    · exact Fin.elim0 x
  rw [this, Term.relabel_id]

theorem realize_baja {M : Type} [L.Structure M] (v : ℕ → M) (xs : Fin 0 → M) (t : L.Term (ℕ ⊕ Fin 0)) :
    t.realize (Sum.elim v xs) = (baja t).realize v := by
  rw [baja, Term.realize_relabel]
  congr 1
  funext x; rcases x with x | x
  · rfl
  · exact Fin.elim0 x

theorem equal_baja (t₁ t₂ : L.Term (ℕ ⊕ Fin 0)) :
    (BoundedFormula.equal t₁ t₂ : L.Formula ℕ) = Term.equal (baja t₁) (baja t₂) := by
  rw [Term.equal, relabel_baja, relabel_baja]; rfl

theorem rel_baja {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (ℕ ⊕ Fin 0)) :
    (BoundedFormula.rel R ts : L.Formula ℕ) = R.formula (fun i => baja (ts i)) := by
  simp only [Relations.formula, relabel_baja]; rfl

/-- **El lema de verdad**: en el modelo de términos, con `a ↦ [a]`, una fórmula vale si y solo si está en `T`. -/
theorem verdad (hT : Maximal T) (φ : L.Formula ℕ) : φ.Realize (val hT) ↔ φ ∈ T := by
  induction hn : alt φ using Nat.strong_induction_on generalizing φ with
  | _ n ih =>
  cases φ with
  | falsum =>
    exact ⟨fun h => (h : False).elim, fun h => absurd h hT.falsum_no⟩
  | equal t₁ t₂ =>
    simp only [Formula.Realize, BoundedFormula.Realize]
    rw [realize_baja, realize_baja, realize_term, realize_term, equal_mem_iff, equal_baja]
  | rel R ts =>
    simp only [Formula.Realize, BoundedFormula.Realize, realize_baja, realize_term]
    rw [relMap_mk, rel_baja]
  | imp φ ψ =>
    have h1 := ih (alt φ) (by simp only [alt] at hn; omega) φ rfl
    have h2 := ih (alt ψ) (by simp only [alt] at hn; omega) ψ rfl
    simp only [Formula.Realize] at h1 h2
    rw [Formula.Realize, BoundedFormula.realize_imp, h1, h2, hT.imp_iff]
  | all ψ =>
    rw [Formula.Realize, BoundedFormula.realize_all, hT.all_iff]
    have key : ∀ t : L.Term ℕ,
        ψ.Realize (val hT) (Fin.snoc default (Quotient.mk (setoide hT) t)) ↔ instanciar ψ t ∈ T := by
      intro t
      have h := ih (alt (instanciar ψ t)) (by rw [alt_instanciar]; simp only [alt] at hn; omega) _ rfl
      have hs : (Fin.snoc default (Quotient.mk (setoide hT) t) : Fin 1 → Modelo hT) =
          fun _ => Quotient.mk (setoide hT) t := by
        funext i; rw [Fin.fin_one_eq_zero i]; rfl
      rw [← h, realize_instanciar, realize_term, hs]
    constructor
    · intro h t; exact (key t).1 (h _)
    · intro h m
      induction m using Quotient.inductionOn with
      | h t => exact (key t).2 (h t)

/-! ## Controles -/

/-- La altura cuenta: `∀x (x = x → ⊥)` tiene altura 2. -/
example : alt (BoundedFormula.all ((BoundedFormula.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0)) :
    L.BoundedFormula ℕ 1).imp BoundedFormula.falsum) : L.Formula ℕ) = 2 := rfl

end Acotada
end Sagitta.Map
