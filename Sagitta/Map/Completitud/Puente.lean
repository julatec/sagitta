import Sagitta.Map.Completitud.Teorema
import Sagitta.Map.DeltaUno
import Sagitta.Map.Parikh
import Sagitta.Map.TiempoCobham

/-!
# Cruzar el puente: lo semántico de los testigos, con pruebas formales

La completitud (`demuestra_iff_deriva`) dice que «S¹₂ demuestra σ» por modelos equivale a `S¹₂ ⊢ σ`: una lista finita
de axiomas de S¹₂ deriva σ en el cálculo `Deriva`. Aquí se usa en dos direcciones.

## 1. Los resultados de testigos, con derivaciones formales

Los enunciados de Buss, de Δᵇ₁ ⊆ P y de Parikh hablan de «S¹₂ demuestra» con fórmulas que tienen variables libres
(`DemuestraDisyuncion`, `DemuestraTotalSinCota`, `DemuestraTotal`). Cada uno es una sentencia: su clausura universal
(`cierre`). Con eso:

* `deriva_formula_iff`: «`χ(x⃗)` vale en todo modelo de S¹₂ para todo `x⃗`» si y solo si `S¹₂ ⊢ ∀x⃗ χ`.
* `deltaUno_en_P_deriva`: si `S¹₂ ⊢ ∀x (φ(x) ∨ ψ(x))`, con `φ`, `ψ` en `Σᵇ₁` y complementarias en ℕ, el
  problema está en `P`.
* `parikh_deriva`: si `S¹₂ ⊢ ∀x ∃!y φ(x, y)` con `φ` en `Σᵇ₁`, hay un término `t` con
  `S¹₂ ⊢ ∀x ∃y ≤ t(x) φ(x, y)` y `S¹₂ ⊢` la unicidad.
* `buss_deriva`: si `S¹₂ ⊢ ∀x ∃!y φ(x, y)` con `φ` en `Σᵇ₁`, y en ℕ `φ` es el gráfico de `f`, entonces `f`
  es de tiempo polinomial.

## 2. Independencia por modelos

* `no_deriva_de_contramodelo`: si hay un modelo de S¹₂ donde σ falla, `S¹₂ ⊬ σ`. Es el método de los contramodelos,
  ahora sobre pruebas formales.
* `no_deriva_iff_numerable`: `S¹₂ ⊬ σ` si y solo si hay un modelo **numerable** de S¹₂ donde σ falla (el modelo de
  términos). Los modelos de DeMillo y Lipton son de esta clase.

La sintaxis de `cierre` usa `Formula.iAlls` de Mathlib, que no se puede calcular (ordena las variables con
`Classical.choice`); aquí no estorba, porque solo se usa su semántica.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-! ## La clausura universal -/

/-- **La clausura universal** de una fórmula con variables libres en `Fin n`. -/
noncomputable def cierre {n : ℕ} (χ : L.Formula (Fin n)) : L.Sentence :=
  Formula.iAlls (Fin n) (χ.relabel (Sum.inr : Fin n → Empty ⊕ Fin n))

theorem realize_cierre {M : Type} [L.Structure M] {n : ℕ} (χ : L.Formula (Fin n)) :
    M ⊨ cierre χ ↔ ∀ xs : Fin n → M, χ.Realize xs := by
  rw [cierre, Sentence.Realize, Formula.realize_iAlls]
  refine forall_congr' fun xs => ?_
  rw [Formula.realize_relabel]
  rfl

/-- **El puente, para fórmulas con variables libres.** -/
theorem deriva_formula_iff {n : ℕ} (χ : L.Formula (Fin n)) :
    (∀ (M : Type) [L.Structure M], EsModeloS12 M → ∀ xs : Fin n → M, χ.Realize xs) ↔ DerivaS12 (cierre χ) := by
  rw [← demuestra_iff_deriva]
  exact ⟨fun h M _ hM => (realize_cierre χ).2 (h M hM), fun h M _ hM => (realize_cierre χ).1 (h M hM)⟩

/-! ## Δᵇ₁ en S¹₂ es P -/

theorem forall_fin1 {M : Type} {P : (Fin 1 → M) → Prop} : (∀ xs : Fin 1 → M, P xs) ↔ ∀ x : M, P ![x] := by
  refine ⟨fun h x => h _, fun h xs => ?_⟩
  have : xs = ![xs 0] := by funext i; rw [Fin.fin_one_eq_zero i]; rfl
  rw [this]; exact h _

theorem demuestraDisyuncion_iff (φ ψ : L.Formula (Fin 1)) :
    DeltaUno.DemuestraDisyuncion φ ψ ↔ DerivaS12 (cierre (φ ⊔ ψ)) := by
  rw [← deriva_formula_iff]
  refine forall_congr' fun M => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [forall_fin1]
  simp only [Formula.Realize, BoundedFormula.realize_sup]

/-- **Δᵇ₁ en P, con derivaciones**: si `S¹₂ ⊢ ∀x (φ(x) ∨ ψ(x))` con `φ`, `ψ` en `Σᵇ₁` que en ℕ definen un problema
y su complemento, el problema está en `P`. -/
theorem deltaUno_en_P_deriva {φ ψ : L.Formula (Fin 1)} (hφ : EsSigma1 φ) (hψ : EsSigma1 ψ)
    (hd : DerivaS12 (cierre (φ ⊔ ψ))) {Pr : Problema} (hP : DefinidoPor φ Pr)
    (hQ : DefinidoPor ψ (fun w => !Pr w)) : Pr ∈ P :=
  DeltaUno.deltaUno_en_P hφ hψ ((demuestraDisyuncion_iff φ ψ).2 hd) hP hQ

/-! ## Parikh y Buss -/

/-- `φ(x, y)` con `x` libre y `y` como la variable a cuantificar. -/
def xy : Fin 2 → Fin 1 ⊕ Fin 1 := ![Sum.inl 0, Sum.inr 0]

/-- **`∃! y φ(x, y)`**, con `x` libre. -/
noncomputable def existeUnico (φ : L.Formula (Fin 2)) : L.Formula (Fin 1) :=
  Formula.iExsUnique (Fin 1) (φ.relabel xy)

/-- **`∃ y ≤ t(x) φ(x, y)`**, con `x` libre. -/
noncomputable def existeAcot (φ : L.Formula (Fin 2)) (t : L.Term (Fin 1)) : L.Formula (Fin 1) :=
  Formula.iExs (Fin 1) (φ.relabel xy ⊓
    Relations.formula (Rel.le : L.Relations 2) ![Term.var (Sum.inr 0), t.relabel Sum.inl])

/-- **La unicidad**: `φ(x, y) ∧ φ(x, z) → y = z`, con `x, y, z` libres. -/
def unicidad (φ : L.Formula (Fin 2)) : L.Formula (Fin 3) :=
  (φ.relabel ![0, 1] ⊓ φ.relabel ![0, 2]).imp (Term.equal (Term.var 1) (Term.var 2))

theorem comp_xy {M : Type} (x y : Fin 1 → M) : (Sum.elim x y ∘ xy) = ![x 0, y 0] := by
  funext i; fin_cases i <;> rfl

theorem existsUnique_fin1 {M : Type} {P : M → Prop} : (∃! i : Fin 1 → M, P (i 0)) ↔ ∃! y : M, P y := by
  constructor
  · rintro ⟨i, hi, hu⟩
    exact ⟨i 0, hi, fun y hy => by have := hu ![y] hy; rw [← this]; rfl⟩
  · rintro ⟨y, hy, hu⟩
    refine ⟨![y], hy, fun i hi => ?_⟩
    funext j; rw [Fin.fin_one_eq_zero j]; exact hu _ hi

theorem demuestraTotalSinCota_iff (φ : L.Formula (Fin 2)) :
    DemuestraTotalSinCota φ ↔ DerivaS12 (cierre (existeUnico φ)) := by
  rw [← deriva_formula_iff]
  refine forall_congr' fun M => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [forall_fin1]
  refine forall_congr' fun x => ?_
  rw [existeUnico, Formula.Realize, BoundedFormula.realize_iExsUnique]
  simp only [Formula.realize_relabel, comp_xy]
  exact existsUnique_fin1.symm

theorem fin1_eq {M : Type} (i : Fin 1 → M) : i = ![i 0] := by funext j; rw [Fin.fin_one_eq_zero j]; rfl

theorem realize_le_t {M : Type} [L.Structure M] (t : L.Term (Fin 1)) (x y : M) :
    Structure.RelMap (L := L) (Rel.le : L.Relations 2)
      (fun j => Term.realize (Sum.elim ![x] ![y]) (![Term.var (Sum.inr 0), t.relabel Sum.inl] j)) ↔
      le y (t.realize ![x]) := by
  unfold le
  apply iff_of_eq; congr 1
  funext j; fin_cases j
  · rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Term.realize_relabel]
    congr 1

theorem realize_existeAcot {M : Type} [L.Structure M] (φ : L.Formula (Fin 2)) (t : L.Term (Fin 1)) (x : M) :
    (existeAcot φ t).Realize ![x] ↔ ∃ y, le y (t.realize ![x]) ∧ φ.Realize ![x, y] := by
  rw [existeAcot, Formula.Realize, BoundedFormula.realize_iExs]
  constructor
  · rintro ⟨i, hi⟩
    rw [fin1_eq i] at hi
    simp only [Formula.realize_inf, Formula.realize_relabel, comp_xy, Formula.realize_rel] at hi
    exact ⟨i 0, (realize_le_t t x (i 0)).1 hi.2, hi.1⟩
  · rintro ⟨y, hle, hy⟩
    refine ⟨![y], ?_⟩
    simp only [Formula.realize_inf, Formula.realize_relabel, comp_xy, Formula.realize_rel]
    exact ⟨hy, (realize_le_t t x y).2 hle⟩

theorem realize_unicidad {M : Type} [L.Structure M] (φ : L.Formula (Fin 2)) (xs : Fin 3 → M) :
    (unicidad φ).Realize xs ↔ (φ.Realize ![xs 0, xs 1] → φ.Realize ![xs 0, xs 2] → xs 1 = xs 2) := by
  have e1 : (xs ∘ ![(0 : Fin 3), 1]) = ![xs 0, xs 1] := by funext i; fin_cases i <;> rfl
  have e2 : (xs ∘ ![(0 : Fin 3), 2]) = ![xs 0, xs 2] := by funext i; fin_cases i <;> rfl
  simp only [unicidad, Formula.realize_imp, Formula.realize_inf, Formula.realize_relabel, e1, e2,
    Formula.realize_equal, Term.realize_var]
  tauto

theorem demuestraTotal_iff (φ : L.Formula (Fin 2)) :
    DemuestraTotal φ ↔ ∃ t : L.Term (Fin 1),
      DerivaS12 (cierre (existeAcot φ t)) ∧ DerivaS12 (cierre (unicidad φ)) := by
  refine exists_congr fun t => ?_
  rw [← deriva_formula_iff, ← deriva_formula_iff]
  constructor
  · intro h
    refine ⟨fun M _ hM => forall_fin1.2 fun x => (realize_existeAcot φ t x).2 ((h M hM).1 x),
      fun M _ hM xs => (realize_unicidad φ xs).2 ((h M hM).2 (xs 0) (xs 1) (xs 2))⟩
  · rintro ⟨h1, h2⟩ M _ hM
    refine ⟨fun x => (realize_existeAcot φ t x).1 (h1 M hM ![x]), fun x y z hy hz => ?_⟩
    exact (realize_unicidad φ ![x, y, z]).1 (h2 M hM ![x, y, z]) hy hz

/-- **Parikh, con derivaciones**: si `S¹₂ ⊢ ∀x ∃!y φ(x, y)` con `φ` en `Σᵇ₁`, la `y` queda acotada por un
término, también con derivaciones. -/
theorem parikh_deriva {φ : L.Formula (Fin 2)} (hφ : EsSigma1 φ) (h : DerivaS12 (cierre (existeUnico φ))) :
    ∃ t : L.Term (Fin 1), DerivaS12 (cierre (existeAcot φ t)) ∧ DerivaS12 (cierre (unicidad φ)) :=
  (demuestraTotal_iff φ).1 (Parikh.parikh φ hφ ((demuestraTotalSinCota_iff φ).2 h))

/-- **Buss, con derivaciones**: si `S¹₂ ⊢ ∀x ∃!y φ(x, y)` con `φ` en `Σᵇ₁` y en ℕ `φ` es el gráfico de
`f`, entonces `f` es de tiempo polinomial. Con Parikh, no hace falta pedir la cota. -/
theorem buss_deriva {f : ℕ → ℕ} {φ : L.Formula (Fin 2)} (hφ : EsSigma1 φ) (h : DerivaS12 (cierre (existeUnico φ)))
    (hg : ∀ n : ℕ, φ.Realize ![n, f n]) : EsPolinomial f :=
  Cobham.definibleEsPolinomial f
    ⟨φ, hφ, (demuestraTotal_iff φ).2 (parikh_deriva hφ h), hg⟩

/-! ## 2. Independencia por modelos -/

/-- **Un contramodelo prueba que no hay derivación.** -/
theorem no_deriva_de_contramodelo {σ : L.Sentence}
    (h : ∃ (M : Type) (_ : L.Structure M), EsModeloS12 M ∧ ¬ M ⊨ σ) : ¬ DerivaS12 σ := by
  rintro hd
  obtain ⟨M, _, hM, hn⟩ := h
  exact hn ((demuestra_iff_deriva σ).2 hd M hM)

/-- **`S¹₂ ⊬ σ` si y solo si hay un modelo numerable de S¹₂ donde σ falla.** -/
theorem no_deriva_iff_numerable (σ : L.Sentence) :
    ¬ DerivaS12 σ ↔ ∃ (M : Type) (_ : L.Structure M), Countable M ∧ EsModeloS12 M ∧ ¬ M ⊨ σ := by
  constructor
  · intro hno
    obtain ⟨T, hT, hM, hV⟩ := contramodelo_teoria S12 (Γ := []) (Δ := [comoFormula σ])
      fun As hAs hd => hno ⟨As, hAs, by simpa using hd⟩
    refine ⟨Modelo hT, inferInstance, inferInstance, (modelo_S12_iff _).1 hM, fun hs => hV fun _ => ?_⟩
    exact ⟨comoFormula σ, List.mem_singleton_self _, (realize_comoFormula σ (val hT)).2 hs⟩
  · rintro ⟨M, _, _, hM, hn⟩
    exact no_deriva_de_contramodelo ⟨M, inferInstance, hM, hn⟩

/-! ## Controles -/

/-- `S¹₂ ⊬ ⊥`, ahora por un contramodelo: ℕ. -/
example : ¬ DerivaS12 ⊥ :=
  no_deriva_de_contramodelo ⟨ℕ, inferInstance, nat_esModeloS12, by simp [Sentence.Realize]⟩

end Acotada
end Sagitta.Map
