import Sagitta.Map.Completitud.Terminos

/-!
# Completitud, fase F5: el teorema

Última fase del teorema de completitud. Junta F1–F3:
si un secuente no es derivable a partir de ninguna lista finita de axiomas, los axiomas, el antecedente y las
negaciones del sucedente son consistentes; Lindenbaum (F2) los extiende a un maximal de Henkin, y el modelo de
términos (F3) es un modelo de la teoría donde el secuente falla.

## Lo que se prueba

* `completitud_teoria`: para **cualquier** teoría `Th`, si `Γ ⇒ Δ` vale en todo modelo de `Th` con toda asignación,
  entonces una lista finita `As` de axiomas de `Th` (como fórmulas) deriva `As, Γ ⇒ Δ`.
* `completitud`: lo mismo para S¹₂.
* **`demuestra_iff_deriva`**: «S¹₂ demuestra σ» por modelos (`Demuestra`, `Acotada.lean`) equivale a «S¹₂ ⊢ σ»
  (`DerivaS12`): una lista finita de axiomas de S¹₂ deriva σ en el cálculo `Deriva`. La vuelta es la corrección
  (`Deriva.correcta`). Desaparece la reserva de que «demuestra» era solo semántico.

## Lo que no se prueba aquí

Que cada axioma de S¹₂ se derive **sin hipótesis** en `Deriva`, que tiene los BASIC como iniciales y PIND como regla
(fase F4 del plan). Con eso, `DerivaS12 σ` se volvería `Der [] [σ]`. Es la relación entre dos presentaciones del
mismo sistema (PIND como axioma o como regla), no parte de la completitud. Lo que la complica: el axioma PIND está
escrito con `Formula.iAlls` de Mathlib, que ordena los parámetros con una biyección elegida por `Classical.choice`.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-! ## Las sentencias como fórmulas sin variables libres -/

/-- **Una sentencia como fórmula** con variables en `ℕ` (no tiene ninguna libre). -/
def comoFormula (σ : L.Sentence) : L.Formula ℕ := σ.relabel Empty.elim

theorem realize_comoFormula {M : Type} [L.Structure M] (σ : L.Sentence) (v : ℕ → M) :
    (comoFormula σ).Realize v ↔ M ⊨ σ := by
  rw [comoFormula, Formula.realize_relabel, Sentence.Realize]
  apply iff_of_eq; congr 1; funext x; exact x.elim

theorem varFinsetLeft_relabel_map {α : Type} {m k : ℕ} (f : Fin m → Fin k) (t : L.Term (α ⊕ Fin m))
    [DecidableEq α] : (t.relabel (Sum.map (id : α → α) f)).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var x => rcases x with x | x <;> rfl
  | func g ts ih => simp only [Term.relabel, Term.varFinsetLeft, ih]

theorem freeVarFinset_castLE {α : Type} [DecidableEq α] :
    ∀ {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormula α m), (φ.castLE h).freeVarFinset = φ.freeVarFinset
  | _, _, _, .falsum => rfl
  | _, _, h, .equal t₁ t₂ => by
    simp only [BoundedFormula.castLE, BoundedFormula.freeVarFinset]
    rw [varFinsetLeft_relabel_map (α := α) (Fin.castLE h) t₁, varFinsetLeft_relabel_map (α := α) (Fin.castLE h) t₂]
  | _, _, h, .rel R ts => by
    simp only [BoundedFormula.castLE, BoundedFormula.freeVarFinset, Function.comp_apply]
    congr 1; funext i; exact varFinsetLeft_relabel_map (α := α) (Fin.castLE h) (ts i)
  | _, _, h, .imp φ ψ => by
    simp only [BoundedFormula.castLE, BoundedFormula.freeVarFinset, freeVarFinset_castLE h φ, freeVarFinset_castLE h ψ]
  | _, _, h, .all φ => by
    simp only [BoundedFormula.castLE, BoundedFormula.freeVarFinset, freeVarFinset_castLE _ φ]

theorem varFinsetLeft_relabel_vacio {k : ℕ} (t : L.Term (Empty ⊕ Fin k)) :
    (t.relabel (BoundedFormula.relabelAux (Sum.inl ∘ Empty.elim : Empty → ℕ ⊕ Fin 0) k)).varFinsetLeft = ∅ := by
  induction t with
  | var x =>
    rcases x with x | x
    · exact x.elim
    · rfl
  | func g ts ih =>
    simp only [Term.relabel, Term.varFinsetLeft, ih]
    ext x; simp

theorem freeVarFinset_relabel_vacio :
    ∀ {k : ℕ} (φ : L.BoundedFormula Empty k),
      (φ.relabel (Sum.inl ∘ Empty.elim : Empty → ℕ ⊕ Fin 0)).freeVarFinset = ∅
  | _, .falsum => rfl
  | _, .equal t₁ t₂ => by
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset,
      varFinsetLeft_relabel_vacio, Finset.empty_union]
  | _, .rel R ts => by
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset,
      varFinsetLeft_relabel_vacio]
    ext x; simp
  | _, .imp φ ψ => by
    have h1 := freeVarFinset_relabel_vacio φ
    have h2 := freeVarFinset_relabel_vacio ψ
    simp only [BoundedFormula.relabel] at h1 h2
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset, h1, h2,
      Finset.empty_union]
  | _, .all φ => by
    have h1 := freeVarFinset_relabel_vacio φ
    simp only [BoundedFormula.relabel] at h1
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset,
      freeVarFinset_castLE, h1]

theorem libre_comoFormula (σ : L.Sentence) (a : ℕ) : a ∉ (comoFormula σ).freeVarFinset := by
  have : (comoFormula σ).freeVarFinset = ∅ := freeVarFinset_relabel_vacio σ
  rw [this]; exact Finset.notMem_empty a

theorem cota_le_suma {φ : L.Formula ℕ} : ∀ {l : List (L.Formula ℕ)}, φ ∈ l → cota φ ≤ (l.map cota).sum
  | [], h => absurd h List.not_mem_nil
  | ψ :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := cota_le_suma h; simp; omega

/-! ## Mover negaciones al sucedente -/

theorem mover_neg : ∀ (Δ : List (L.Formula ℕ)) {Ps Ss : List (L.Formula ℕ)},
    Der (Δ.map BoundedFormula.not ++ Ps) Ss → Der Ps (Δ ++ Ss)
  | [], _, _, h => h
  | δ :: Δ, Ps, Ss, h => by
    have h1 : Der (Δ.map BoundedFormula.not ++ Ps) (δ :: Ss) := Der.deNegIzq h
    exact (mover_neg Δ h1).debil (List.Subset.refl _) (by intro x hx; simp at hx ⊢; tauto)

/-! ## El teorema, para una teoría cualquiera -/

/-- **El contramodelo.** Si ninguna lista finita de axiomas de `Th` con `Γ` deriva `Δ`, el modelo de términos de un
maximal es un modelo de `Th` donde `Γ ⇒ Δ` falla, con la asignación `a ↦ [a]`. -/
theorem contramodelo_teoria (Th : L.Theory) {Γ Δ : List (L.Formula ℕ)}
    (hno : ∀ As : List (L.Formula ℕ), (∀ a ∈ As, ∃ σ ∈ Th, a = comoFormula σ) → ¬ Der (As ++ Γ) Δ) :
    ∃ (T : Set (L.Formula ℕ)) (hT : Maximal T), Modelo hT ⊨ Th ∧ ¬ Vale (Modelo hT) (val hT) Γ Δ := by
  classical
  -- Los axiomas, `Γ` y las negaciones de `Δ`.
  let Ax : Set (L.Formula ℕ) := comoFormula '' Th
  let S : Set (L.Formula ℕ) := Ax ∪ {φ | φ ∈ Γ} ∪ {φ | φ ∈ Δ.map BoundedFormula.not}
  have hS : Consis S := by
    rintro ⟨Λ, hΛ, hd⟩
    let As := Λ.filter (fun φ => decide (φ ∈ Ax))
    have hsub : Λ ⊆ Δ.map BoundedFormula.not ++ (As ++ Γ) := by
      intro φ hφ
      rcases hΛ φ hφ with (hA | hG) | hD
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_filter.2 ⟨hφ, by simpa using hA⟩))
      · exact List.mem_append_right _ (List.mem_append_right _ hG)
      · exact List.mem_append_left _ hD
    have h2 := mover_neg Δ (hd.debil hsub (List.Subset.refl _))
    rw [List.append_nil] at h2
    refine hno As (fun a ha => ?_) h2
    obtain ⟨σ, hσ, rfl⟩ := (by simpa using (List.mem_filter.1 ha).2 : a ∈ Ax)
    exact ⟨σ, hσ, rfl⟩
  -- Las variables libres están acotadas: las de `Γ` y `Δ`; los axiomas no tienen.
  let N := (Γ.map cota).sum + (Δ.map cota).sum
  have hb : Acotado S N := by
    intro φ hφ a ha
    rcases hφ with (hA | hG) | hD
    · obtain ⟨σ, _, rfl⟩ := hA
      exact absurd ha (libre_comoFormula σ a)
    · have := cota_le_suma hG
      have := lt_cota ha
      omega
    · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hD
      have h1 := cota_le_suma hδ
      have h2 : a ∈ δ.freeVarFinset := by
        simpa [BoundedFormula.not, BoundedFormula.freeVarFinset] using ha
      have := lt_cota h2
      omega
  obtain ⟨T, hST, hT⟩ := lindenbaum hb hS
  refine ⟨T, hT, ?_, fun hV => ?_⟩
  · refine (Theory.model_iff _).2 fun σ hσ => ?_
    rw [← realize_comoFormula σ (val hT), verdad]
    exact hST (Or.inl (Or.inl ⟨σ, hσ, rfl⟩))
  · obtain ⟨ψ, hψ, hr⟩ := hV fun φ hφ => (verdad hT φ).2 (hST (Or.inl (Or.inr hφ)))
    exact hT.no_ambos ((verdad hT ψ).1 hr) (hST (Or.inr (List.mem_map.2 ⟨ψ, hψ, rfl⟩)))

/-- **Completitud, para una teoría cualquiera.** Si `Γ ⇒ Δ` vale en todo modelo de `Th`, con toda asignación, hay una
lista finita de axiomas de `Th` que con `Γ` deriva `Δ`. -/
theorem completitud_teoria (Th : L.Theory) {Γ Δ : List (L.Formula ℕ)}
    (h : ∀ (M : Type) [L.Structure M], M ⊨ Th → ∀ v : ℕ → M, Vale M v Γ Δ) :
    ∃ As : List (L.Formula ℕ), (∀ a ∈ As, ∃ σ ∈ Th, a = comoFormula σ) ∧ Der (As ++ Γ) Δ := by
  by_contra hno
  push Not at hno
  obtain ⟨T, hT, hM, hV⟩ := contramodelo_teoria Th hno
  exact hV (h (Modelo hT) hM (val hT))

/-- **El modelo de términos es numerable**: es un cociente de los términos, que se pueden enumerar. -/
instance (T : Set (L.Formula ℕ)) (hT : Maximal T) : Countable (Modelo hT) := by
  unfold Modelo; infer_instance

/-! ## Para S¹₂ -/

/-- **Completitud para S¹₂.** -/
theorem completitud {Γ Δ : List (L.Formula ℕ)}
    (h : ∀ (M : Type) [L.Structure M], EsModeloS12 M → ∀ v : ℕ → M, Vale M v Γ Δ) :
    ∃ As : List (L.Formula ℕ), (∀ a ∈ As, ∃ σ ∈ S12, a = comoFormula σ) ∧ Der (As ++ Γ) Δ :=
  completitud_teoria S12 fun M _ hM v => h M ((modelo_S12_iff M).1 hM) v

/-- **`S¹₂ ⊢ σ`**: una lista finita de axiomas de S¹₂ deriva `σ` en el cálculo `Deriva`. -/
def DerivaS12 (σ : L.Sentence) : Prop :=
  ∃ As : List (L.Formula ℕ), (∀ a ∈ As, ∃ τ ∈ S12, a = comoFormula τ) ∧ Der As [comoFormula σ]

/-- **Demostrar por modelos es derivar.** «S¹₂ demuestra σ» (σ vale en todo modelo de S¹₂) si y solo si una lista
finita de axiomas de S¹₂ deriva σ. La ida es la completitud; la vuelta, la corrección. -/
theorem demuestra_iff_deriva (σ : L.Sentence) : Demuestra σ ↔ DerivaS12 σ := by
  constructor
  · intro h
    obtain ⟨As, hAs, hd⟩ := completitud (Γ := []) (Δ := [comoFormula σ]) fun M _ hM v _ =>
      ⟨comoFormula σ, List.mem_singleton_self _, (realize_comoFormula σ v).2 (h M hM)⟩
    exact ⟨As, hAs, by simpa using hd⟩
  · rintro ⟨As, hAs, ⟨d⟩⟩ M _ hM
    have hT : M ⊨ S12 := (modelo_S12_iff M).2 hM
    let v : ℕ → M := fun _ => cero
    obtain ⟨ψ, hψ, hr⟩ := d.correcta hM v fun a ha => by
      obtain ⟨τ, hτ, rfl⟩ := hAs a ha
      exact (realize_comoFormula τ v).2 (Theory.realize_sentence_of_mem S12 hτ)
    rw [List.mem_singleton] at hψ
    subst hψ
    exact (realize_comoFormula σ v).1 hr

/-! ## Controles -/

/-- La vuelta trabaja: un axioma de S¹₂ se deriva de sí mismo, y por eso S¹₂ lo demuestra. -/
example : Demuestra axB3 :=
  (demuestra_iff_deriva axB3).2 ⟨[comoFormula axB3],
    fun a ha => ⟨axB3, Or.inl (by simp [teoriaBASIC]), by simpa using ha⟩, Der.ax _⟩

/-- Y no todo se deriva: `⊥` no, porque `ℕ` es un modelo de S¹₂. -/
example : ¬ DerivaS12 ⊥ := fun h => by
  have := verdadero_de_demuestra ((demuestra_iff_deriva _).2 h)
  simp [Sentence.Realize] at this

end Acotada
end Sagitta.Map
