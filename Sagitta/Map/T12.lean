import Sagitta.Map.Teoria

/-!
# Aritmética acotada: T¹₂, la inducción de uno en uno

Buss (*Bounded Arithmetic*, 1986, §2.2, p. 32): T^i_2 tiene los axiomas BASIC y la inducción ordinaria Σᵇᵢ-IND,

  `A(0) ∧ ∀ x (A(x) ⊃ A(Sx)) ⊃ ∀ x A(x)`,

donde S^i_2 tiene PIND (de `⌊x/2⌋` a `x`). T¹₂ es el caso `i = 1`; T⁰₂ el de `i = 0`, con la inducción solo para las
fórmulas agudas (`Σᵇ₀`). La diferencia es cuánto baja la inducción por paso: S¹₂ llega al fondo en `|x|` pasos, T¹₂ en
`x`. Buss y Krajíček (1994): lo que T¹₂ demuestra total con una `Σᵇ₁` son los problemas de búsqueda local (PLS), donde
S¹₂ da FP.

Aquí:

1. `EsModeloT12`, `EsModeloT02` en el estilo de `EsModeloS12`, y que ℕ es modelo de las dos (`nat_esModeloT12`).
2. T¹₂ contiene a T⁰₂ (`t02_de_t12`): toda aguda es `Σᵇ₁`. Probado.
3. T¹₂ como teoría de Mathlib (`T12`, con `indAx`), `modelo_T12_iff`, `DemuestraT12` = `T12 ⊨ᵇ σ` y su compacidad.
4. Con nombre: `T12ContieneS12` y `S12ContieneT02`, las dos inclusiones que Buss anuncia en la p. 32
   («T^i_2 ⊢ S^i_2 and S^i_2 ⊢ T^{i-1}_2 where i > 0»). Las dos quedaron **probadas** fuera de este archivo:
   `Arranque.s12ContieneT02` y `Arranque2.t12ContieneS12` (los bits altos de un número, con `1 # w`).
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-! ## T¹₂ y T⁰₂, como en `Acotada.lean` -/

/-- **Un modelo de T¹₂**: cumple BASIC y la inducción ordinaria (IND) para toda fórmula `Σᵇ₁`: si `φ(0)` y
`φ(x) → φ(Sx)`, entonces `φ(x)` para todo `x`. La variable 0 es la de inducción; las demás, parámetros. -/
structure EsModeloT12 (M : Type) [L.Structure M] : Prop where
  basic : EsModeloBASIC M
  ind : ∀ (k : ℕ) (φ : L.Formula (Fin (k + 1))), EsSigma1 φ → ∀ v : Fin k → M,
    φ.Realize (Fin.cons cero v) →
    (∀ x : M, φ.Realize (Fin.cons x v) → φ.Realize (Fin.cons (suc x) v)) →
    ∀ x : M, φ.Realize (Fin.cons x v)

/-- **Un modelo de T⁰₂**: BASIC y la inducción ordinaria solo para las fórmulas agudas (`Σᵇ₀`). -/
structure EsModeloT02 (M : Type) [L.Structure M] : Prop where
  basic : EsModeloBASIC M
  ind : ∀ (k : ℕ) (φ : L.Formula (Fin (k + 1))), EsAguda φ → ∀ v : Fin k → M,
    φ.Realize (Fin.cons cero v) →
    (∀ x : M, φ.Realize (Fin.cons x v) → φ.Realize (Fin.cons (suc x) v)) →
    ∀ x : M, φ.Realize (Fin.cons x v)

/-- **ℕ es un modelo de T¹₂.** La inducción ordinaria vale en ℕ para cualquier propiedad. -/
theorem nat_esModeloT12 : EsModeloT12 ℕ where
  basic := nat_esModeloBASIC
  ind := by
    intro k φ _ v h0 hpaso x
    induction x with
    | zero => exact h0
    | succ n ih => exact hpaso n ih

/-- **T¹₂ contiene a T⁰₂**: toda fórmula aguda es `Σᵇ₁`, así que la inducción de T¹₂ cubre la de T⁰₂. -/
theorem t02_de_t12 {M : Type} [L.Structure M] (h : EsModeloT12 M) : EsModeloT02 M :=
  ⟨h.basic, fun k φ hφ => h.ind k φ (EsSigma1.aguda hφ)⟩

theorem nat_esModeloT02 : EsModeloT02 ℕ := t02_de_t12 nat_esModeloT12

/-- **Buss: T¹₂ demuestra S¹₂** (1986, p. 32, «T^i_2 ⊢ S^i_2»): todo modelo de T¹₂ es modelo de S¹₂. Probado en
`Arranque2.t12ContieneS12`;
es un teorema conocido. -/
def T12ContieneS12 : Prop :=
  ∀ (M : Type) [L.Structure M], EsModeloT12 M → EsModeloS12 M

/-- **Buss: S¹₂ demuestra T⁰₂** (1986, p. 32, «S^i_2 ⊢ T^{i-1}_2»). Probado en `Arranque.s12ContieneT02`. -/
def S12ContieneT02 : Prop :=
  ∀ (M : Type) [L.Structure M], EsModeloS12 M → EsModeloT02 M

/-! ## IND como esquema de sentencias, y T¹₂ como teoría de Mathlib -/

section IND

variable {k : ℕ}

/-- **El axioma IND de `φ`**, como sentencia: para todos los parámetros `v⃗`, si `φ(0, v⃗)` y, para todo `x`,
`φ(x, v⃗) → φ(Sx, v⃗)`, entonces `φ(x, v⃗)` para todo `x`. Es `pindAx` con el sucesor en lugar de la mitad. -/
noncomputable def indAx (φ : L.Formula (Fin (k + 1))) : L.Sentence :=
  let x : L.Term (Fin k ⊕ Fin 1) := Term.var (Sum.inr 0)
  let par : Fin k → L.Term (Fin k ⊕ Fin 1) := fun i => Term.var (Sum.inl i)
  let base : L.Formula (Fin k) := φ.subst (Fin.cons tC (fun i => Term.var i))
  let paso : L.Formula (Fin k) :=
    Formula.iAlls (β := Fin 1) ((φ.subst (Fin.cons x par)).imp (φ.subst (Fin.cons (tSc x) par)))
  let concl : L.Formula (Fin k) := Formula.iAlls (β := Fin 1) (φ.subst (Fin.cons x par))
  let cuerpo : L.Formula (Fin k) := (base ⊓ paso).imp concl
  Formula.iAlls (β := Fin k) (cuerpo.subst (fun i => Term.var (Sum.inr i)) : L.Formula (Empty ⊕ Fin k))

variable {M : Type} [L.Structure M]

/-- **Cumplir IND para `φ` es ser modelo de su sentencia.** -/
theorem realize_indAx (φ : L.Formula (Fin (k + 1))) :
    M ⊨ indAx φ ↔ ∀ v : Fin k → M, Formula.Realize φ (Fin.cons cero v) →
      (∀ x : M, Formula.Realize φ (Fin.cons x v) → Formula.Realize φ (Fin.cons (suc x) v)) →
      ∀ x : M, Formula.Realize φ (Fin.cons x v) := by
  simp only [indAx, Sentence.Realize, Formula.realize_iAlls, formula_realize_subst, Formula.realize_imp,
    Formula.realize_inf, realize_fin_cons, Term.realize_var, Sum.elim_inr, realize_tC, tSc,
    Term.realize_functions_apply₁]
  constructor
  · intro h v h0 hpaso x
    exact h v ⟨h0, fun i => hpaso (i 0)⟩ (fun _ => x)
  · intro h v ⟨h0, hpaso⟩ i
    exact h v h0 (fun x => hpaso (fun _ => x)) (i 0)

end IND

/-- **T¹₂ como teoría de Mathlib**: los 32 axiomas BASIC y el axioma IND de cada fórmula `Σᵇ₁`. -/
noncomputable def T12 : L.Theory :=
  teoriaBASIC ∪ {σ | ∃ (k : ℕ) (φ : L.Formula (Fin (k + 1))), EsSigma1 φ ∧ σ = indAx φ}

/-- **Ser modelo de T¹₂ (`EsModeloT12`) es ser modelo de la teoría `T12`.** -/
theorem modelo_T12_iff (M : Type) [L.Structure M] : M ⊨ T12 ↔ EsModeloT12 M := by
  rw [T12, Theory.model_union_iff, modelo_basic_iff, Theory.model_iff]
  constructor
  · rintro ⟨hb, hi⟩
    refine ⟨hb, fun k φ hφ v h0 hpaso x => ?_⟩
    exact (realize_indAx φ).1 (hi _ ⟨k, φ, hφ, rfl⟩) v h0 hpaso x
  · rintro ⟨hb, hi⟩
    refine ⟨hb, ?_⟩
    rintro σ ⟨k, φ, hφ, rfl⟩
    exact (realize_indAx φ).2 (hi k φ hφ)

/-- **T¹₂ demuestra σ**, por modelos, como `Demuestra` para S¹₂. -/
def DemuestraT12 (σ : L.Sentence) : Prop :=
  ∀ (M : Type) [L.Structure M], EsModeloT12 M → M ⊨ σ

/-- Lo que T¹₂ demuestra es verdadero en ℕ. -/
theorem verdadero_de_demuestraT12 {σ : L.Sentence} (h : DemuestraT12 σ) : ℕ ⊨ σ :=
  h ℕ nat_esModeloT12

/-- **`DemuestraT12 σ` es `T12 ⊨ᵇ σ`.** -/
theorem demuestraT12_iff_models (σ : L.Sentence) :
    DemuestraT12 σ ↔ Theory.ModelsBoundedFormula.{0, 0, 0} T12 σ := by
  constructor
  · intro h M v xs
    have hM : EsModeloT12 M := (modelo_T12_iff M).1 inferInstance
    have := h M hM
    rw [Sentence.Realize, Formula.Realize] at this
    simpa [Unique.eq_default v, Unique.eq_default xs] using this
  · intro h M _ hM
    have : M ⊨ T12 := (modelo_T12_iff M).2 hM
    have : Nonempty M := ⟨cero⟩
    exact (Theory.models_sentence_iff.1 h) (Theory.ModelType.of T12 M)

/-- **Compacidad**: lo que T¹₂ demuestra se sigue de un número finito de sus axiomas. -/
theorem demuestraT12_iff_finito (σ : L.Sentence) :
    DemuestraT12 σ ↔ ∃ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T12 ∧
      Theory.ModelsBoundedFormula.{0, 0, 0} (T0 : L.Theory) σ := by
  rw [demuestraT12_iff_models, Theory.models_iff_finset_models]

/-- **Si T¹₂ demuestra S¹₂, lo que demuestra S¹₂ lo demuestra T¹₂.** Es la forma en que se usa `T12ContieneS12`. -/
theorem demuestraT12_de_demuestra (h : T12ContieneS12) {σ : L.Sentence} (hs : Demuestra σ) : DemuestraT12 σ :=
  fun M _ hM => hs M (h M hM)

end Acotada
end Sagitta.Map
