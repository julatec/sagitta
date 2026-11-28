import Sagitta.Map.SigmaUno
import Sagitta.Map.Definibles

/-!
# El teorema del testigo de Buss, por modelos (R5c)

Último paso de la ruta por modelos.

## Qué hay

* **`esModeloS12_saturado`**: el modelo saturado de `Saturacion.lean`, leído con la estructura de Buss, es un
  modelo de S¹₂ en el sentido de `Acotada.lean` (`EsModeloS12`): cumple BASIC (`EnlaceBuss.lean`) y la inducción por
  bits para toda fórmula Σᵇ₁ (R4 más la representación de R5b).
* **`definible_es_cobham`**: si `f` es Σᵇ₁-definible en S¹₂ (`DefinibleSigma1` de `Definibles.lean`), un programa
  de Cobham la calcula. Es el teorema del testigo de Buss, salvo el paso de Cobham a máquinas (F4b).

## La prueba de `definible_es_cobham`

1. La fórmula `φ(x, y)` se representa con programas fijos (R5b), y «existe `y ≤ t(x)` con `φ`» también: `Δ`, `B`.
2. **Si un programa `G` da siempre un testigo de `Δ` en ℕ**, su primera mitad es un `y` con `φ(x, y)` en ℕ (la
   dirección sana vale en ℕ); por la unicidad que S¹₂ demuestra, ese `y` es `f(x)`.
3. **Si ningún programa sirve**, es consistente tener un `d` sin testigo: lo da Herbrand, y para cada lista finita
   de programas candidatos el contraejemplo está en ℕ (se juntan por casos). Se arma el modelo saturado con ese `d`.
   Es un modelo de S¹₂, así que S¹₂ le da un `y ≤ t(d)` con `φ(d, y)`; la dirección completa lo vuelve testigo de
   `Δ`. Contradicción.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language
open Acotada (Fun Rel)

/-- Una fórmula sin variables ligadas: su valor sobre el vector es su realización. -/
theorem val_formula {M : Type} [LC.Structure M] {a : ℕ} (φ : LB.Formula (Fin a)) (z : Fin (a + 0) → M) :
    Val φ z ↔ @Formula.Realize LB M (estructuraBuss M) _ φ z := by
  unfold Val Formula.Realize
  rw [Subsingleton.elim (z ∘ Fin.natAdd a) default]
  rfl

/-- Pasar `(x, w, y)` de la representación `(x, w)` + testigo al orden de `pind_saturado`, `(x, y, w)`. -/
def alOrdenPind (k : ℕ) : Fin (k + 1 + 1) → Fin (k + 2) :=
  Fin.lastCases 1 fun i => Fin.cases 0 (fun m => m.succ.succ) i

theorem cons_alOrdenPind {M : Type} {k : ℕ} (x y : M) (w : Fin k → M) :
    (Fin.cons x (Fin.cons y w) : Fin (k + 2) → M) ∘ alOrdenPind k = Fin.snoc (Fin.cons x w : Fin (k + 1) → M) y := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Function.comp_apply, alOrdenPind, Fin.lastCases_last, Fin.snoc_last]; rfl
  · simp only [Function.comp_apply, alOrdenPind, Fin.lastCases_castSucc, Fin.snoc_castSucc]
    refine Fin.cases ?_ (fun m => ?_) i
    · simp only [Fin.cases_zero, Fin.cons_zero]
    · simp only [Fin.cases_succ, Fin.cons_succ]

/-- **El modelo saturado es un modelo de S¹₂.** -/
theorem esModeloS12_saturado (R : Realizacion) (hG : Generada R) (hS : Saturada R) :
    @Acotada.EsModeloS12 R.M (estructuraBuss R.M) := by
  let _ : LB.Structure R.M := estructuraBuss R.M
  refine ⟨esModeloBASIC R.M, fun k φ hφ v h0 hpaso x => ?_⟩
  obtain ⟨δ, t, hr⟩ := sigma_representa hφ
  -- La realización, como `Testif` sobre `cons x v`.
  have hR : ∀ y : R.M, φ.Realize (Fin.cons y v) ↔ Val φ (Fin.cons y v : Fin (k + 1 + 0) → R.M) := fun y =>
    (val_formula φ _).symm
  let δ' : Cob (k + 2) := δ.renombrar (alOrdenPind k)
  have hD : ∀ y : R.M, (∃ w, Dt δ' t v y w) ↔ Testif δ t (Fin.cons y v : Fin (k + 1) → R.M) := fun y => by
    simp only [Dt, Testif, δ', ap_renombrar, cons_alOrdenPind]
    exact exists_congr fun w => and_comm
  have hT : ∀ y : R.M, φ.Realize (Fin.cons y v) ↔ ∃ w, Dt δ' t v y w := fun y => by
    rw [hD, hR]
    exact ⟨hr.2.2 R hG hS _, hr.2.1 R.M _⟩
  have h0' : ∃ w, Dt δ' t v (cero0 R.M) w := (hT _).mp h0
  have hpaso' : ∀ y, y ≠ cero0 R.M → (∃ w, Dt δ' t v (mitadM y) w) → ∃ w, Dt δ' t v y w :=
    fun y _ hm => (hT y).mp (hpaso y ((hT _).mpr hm))
  exact (hT x).mpr (pind_saturado R hG hS δ' t v h0' hpaso' x)

/-! ## Las dos lecturas de Buss en ℕ coinciden -/

theorem realizeT_nat_buss {β : Type} (w : β → ℕ) :
    ∀ t : LB.Term β, @Term.realize LB ℕ (estructuraBuss ℕ) _ w t = t.realize w
  | .var _ => rfl
  | .func f ts => by
      simp only [Term.realize]
      rw [show (fun i => @Term.realize LB ℕ (estructuraBuss ℕ) _ w (ts i)) = fun i => (ts i).realize w from
        funext fun i => realizeT_nat_buss w (ts i)]
      exact (compatible_nat.fun_eq f _).symm

/-- **La estructura inducida en ℕ y la estándar de `Acotada.lean` dan lo mismo**, para toda fórmula. -/
theorem realize_nat_buss {α : Type} : ∀ {n : ℕ} (φ : LB.BoundedFormula α n) (v : α → ℕ) (xs : Fin n → ℕ),
    @BoundedFormula.Realize LB ℕ (estructuraBuss ℕ) _ _ φ v xs ↔ φ.Realize v xs
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal t u, v, xs => by
      simp only [BoundedFormula.Realize, realizeT_nat_buss]
  | _, .rel R ts, v, xs => by
      cases R
      change relLe Rel.le _ ↔ _
      simp only [realizeT_nat_buss]
      exact ((compatible_buss ℕ).rel_iff _).trans (compatible_nat.rel_iff _).symm
  | _, .imp φ ψ, v, xs => by
      simp only [BoundedFormula.Realize]
      rw [realize_nat_buss φ v xs, realize_nat_buss ψ v xs]
  | _, .all φ, v, xs => by
      simp only [BoundedFormula.Realize]
      exact forall_congr' fun x => realize_nat_buss φ v _

/-! ## El teorema -/

section Teorema

theorem ap_pEx_iff {M : Type} [LC.Structure M] [M ⊨ TC] {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1))
    (t : Cob A) (z : Fin A → M) (p : M) :
    ap (pEx δ s t) (Fin.snoc z p) = cero0 M ↔
      LeM (ap (pFst t) (Fin.snoc z p)) (ap t z) ∧
      LeM (ap (pSnd t) (Fin.snoc z p)) (ap s (Fin.snoc z (ap (pFst t) (Fin.snoc z p)))) ∧
      ap δ (Fin.snoc (Fin.snoc z (ap (pFst t) (Fin.snoc z p))) (ap (pSnd t) (Fin.snoc z p))) = cero0 M := by
  simp only [pEx, ap_yy, leM_iff, ap_levantar, ap_comp_snoc, ap_primeras, ap_snoc_primeras]

theorem snoc_uno {M : Type} (x y : M) : (Fin.snoc ![x] y : Fin 2 → M) = ![x, y] := by
  funext i; fin_cases i <;> rfl

theorem realize_term_uno {M : Type} [LC.Structure M] [M ⊨ TC] (t : LB.Term (Fin 1)) (x : M) :
    @Term.realize LB M (estructuraBuss M) _ ![x] t = ap (trT (n := 0) id (t.relabel Sum.inl) : Cob 1) ![x] := by
  let _ : LB.Structure M := estructuraBuss M
  have := realize_trT (estructuraBuss M) (compatible_buss M) id ![x] (Fin.elim0 : Fin 0 → M) (t.relabel Sum.inl)
  rw [Term.realize_relabel] at this
  have e : (Fin.append ![x] (Fin.elim0 : Fin 0 → M) : Fin (1 + 0) → M) = ![x] := by funext i; fin_cases i; rfl
  rw [e] at this
  exact this

/-- **El teorema del testigo para búsquedas, por modelos.** Si S¹₂ demuestra que todo `x` tiene un `y ≤ t(x)` con
`φ(x, y)`, con `φ` Σᵇ₁, un programa de Cobham da en ℕ un `y` con `φ`. No pide unicidad: es el problema de búsqueda,
no una función. -/
theorem busqueda_es_cobham (φ : LB.Formula (Fin 2)) (hφ : Acotada.EsSigma1 φ) (t : LB.Term (Fin 1))
    (hex : ∀ (M : Type) [LB.Structure M], Acotada.EsModeloS12 M →
      ∀ x : M, ∃ y : M, Acotada.le y (t.realize ![x]) ∧ φ.Realize ![x, y]) :
    ∃ c : Cob 1, ∀ n : ℕ, φ.Realize ![n, c.eval ![n] ] := by
  classical
  obtain ⟨δ, s, hr⟩ := sigma_representa hφ
  let T : Cob 1 := trT (n := 0) id (t.relabel Sum.inl)
  have mT : Mono T := trT_mono id _
  have hE := repr_existe (A := 1) hr T mT
  let Δ : Cob 2 := pEx δ s T
  let B : Cob 1 := tEx s T
  -- `φ(x, y)` y su valor sobre el vector.
  have hVal : ∀ (M : Type) [LC.Structure M] (x y : M),
      Val φ (Fin.snoc ![x] y : Fin (2 + 0) → M) ↔ @Formula.Realize LB M (estructuraBuss M) _ φ ![x, y] :=
    fun M _ x y => by rw [val_formula]; rw [snoc_uno]
  -- Si un programa da siempre testigos de `Δ` en ℕ, ya está.
  suffices hG : ∃ G : Cob 1, ∀ n : ℕ, LeM (ap G ![n]) (ap B ![n]) ∧ ap Δ (Fin.snoc ![n] (ap G ![n])) = cero0 ℕ by
    obtain ⟨G, hG⟩ := hG
    refine ⟨(pFst T).comp (Fin.snoc (fun i => .proy i) G), fun n => ?_⟩
    obtain ⟨-, hd⟩ := hG n
    obtain ⟨h1, h2, h3⟩ := (ap_pEx_iff δ s T ![n] _).mp hd
    have hv := hr.2.1 ℕ _ ⟨_, h2, h3⟩
    beta_reduce at hv
    rw [hVal] at hv
    have hφn : φ.Realize ![n, ap (pFst T) (Fin.snoc ![n] (ap G ![n]))] := (realize_nat_buss φ _ _).mp hv
    convert hφn using 3
    have := ap_comp_snoc (M := ℕ) (pFst T) (fun i => .proy i) G ![n]
    simp only [ap_nat] at this
    rw [this]
    congr 2
  by_contra hno
  push Not at hno
  -- La condición «`c₀` no tiene testigo».
  let C : Cond1 := ⟨1, no (yy (c2 .resta (ultima 1) (levantar B)) Δ)⟩
  have hCv : ∀ (M : Type) [LC.Structure M] [M ⊨ TC] (ι : ℕ → M), C.cond.Vale ι ↔
      ∀ p, ¬ (LeM p (ap B ![ι 0]) ∧ ap Δ (Fin.snoc ![ι 0] p) = cero0 M) := fun M _ _ ι => by
    rw [Cond1.vale_iff]
    have e : ∀ p : M, (Fin.append (pre ι 1) ![p] : Fin (1 + 1) → M) = Fin.snoc ![ι 0] p := fun p => by
      funext i; fin_cases i <;> rfl
    refine forall_congr' fun p => ?_
    simp only [C, e, ap_no, ne_eq, ap_yy, leM_iff, ap_levantar, ap_ultima]
  -- Es consistente: por Herbrand, y porque cada lista finita de candidatos falla en algún punto de ℕ.
  have hcons : Consistente {D | D ∈ [C.cond]} := by
    by_contra hnc
    have h' : ¬ Consistente (∅ ∪ {C.cond}) := fun h => hnc (h.mono fun D hD => by
      simp only [List.mem_singleton, Set.mem_ofPred_eq] at hD
      exact .inr hD)
    obtain ⟨F, hF⟩ := herbrand ∅ C h'
    let Gq : (Σ N, Cob N) → Cob 1 := fun q => q.2.comp fun _ => .proy 0
    let Tst : Cob 1 → Cob 1 := fun G => yy (c2 .resta G B) (Δ.comp (Fin.snoc (fun i => .proy i) G))
    have hpr : ∀ n : ℕ, (fun i : Fin 1 => ap (Cob.proy i : Cob 1) ![n]) = ![n] := fun n => by
      funext i; fin_cases i; rfl
    have hTst : ∀ (G : Cob 1) (n : ℕ), ap (Tst G) ![n] = cero0 ℕ ↔
        LeM (ap G ![n]) (ap B ![n]) ∧ ap Δ (Fin.snoc ![n] (ap G ![n])) = cero0 ℕ := fun G n => by
      simp only [Tst, ap_yy, leM_iff, ap_comp_snoc, hpr]
    have hT : ∀ (n : ℕ) (G G' : Cob 1), ap G ![n] = ap G' ![n] → ap (Tst G) ![n] = ap (Tst G') ![n] :=
      fun n G G' h => by simp only [Tst, yy, ap_c2, ap_comp_snoc, hpr, h]
    obtain ⟨n0, hn0⟩ := hno (elegir Tst (F.toList.map Gq))
    have hnone : ∀ q ∈ F, ¬ (LeM (ap (Gq q) ![n0]) (ap B ![n0]) ∧
        ap Δ (Fin.snoc ![n0] (ap (Gq q) ![n0])) = cero0 ℕ) := by
      intro q hq hgood
      have h := (hTst _ _).mp (elegir_sirve Tst ![n0] (hT n0) _
        ⟨Gq q, List.mem_map.mpr ⟨q, Finset.mem_toList.mpr hq, rfl⟩, (hTst _ _).mpr hgood⟩)
      exact hn0 h.1 h.2
    refine hF ⟨⟨ℕ, fun _ => n0⟩, fun D hD => ?_⟩
    rcases hD with hD | ⟨q, hq, rfl⟩
    · exact hD.elim
    · rw [Cond1.caso_vale]
      have e : (Fin.append (pre (fun _ => n0) 1) ![ap q.2 (pre (fun _ => n0) q.1)] : Fin (1 + 1) → ℕ) =
          Fin.snoc ![n0] (ap (Gq q) ![n0]) := by
        funext i; fin_cases i
        · rfl
        · simp only [Gq, ap_comp, ap_proy]; rfl
      change ap C.χ _ = cero0 ℕ
      rw [e]
      simp only [C, ap_no, ne_eq, ap_yy, leM_iff, ap_levantar, ap_ultima]
      exact hnone q hq
  -- El modelo saturado con ese `c₀`.
  obtain ⟨R, hR0, hGen, hSat⟩ := existe_saturada ⟨[C.cond], 1⟩ (fun D hD => by
    simp only [List.mem_singleton] at hD; subst hD; exact le_refl _) hcons
  have hC := (hCv R.M R.ι).mp (hR0 C.cond List.mem_cons_self)
  have hS12 := esModeloS12_saturado R hGen hSat
  obtain ⟨y, hy, hφy⟩ := @hex R.M (estructuraBuss R.M) hS12 (R.ι 0)
  have hyT : LeM y (ap T ![R.ι 0]) := by
    have h1 : relLe Rel.le ![y, @Term.realize LB R.M (estructuraBuss R.M) _ ![R.ι 0] t] := hy
    rw [realize_term_uno] at h1
    simpa only [relLe, LeM, restaM, ap_cero] using h1
  have hv : Val φ (Fin.snoc ![R.ι 0] y : Fin (2 + 0) → R.M) := (hVal R.M _ _).mpr hφy
  obtain ⟨p, hp, hd⟩ := (testif_existe δ s hr.1 T ![R.ι 0]).mpr ⟨y, hyT, hr.2.2 R hGen hSat _ hv⟩
  exact hC p ⟨hp, hd⟩

/-- **El teorema del testigo de Buss, por modelos.** Si S¹₂ demuestra, con una fórmula Σᵇ₁, que `f` es total, un
programa de Cobham calcula `f`. Es la búsqueda más la unicidad: el `y` que da el programa es `f(x)`. -/
theorem definible_es_cobham (f : ℕ → ℕ) (hf : Acotada.DefinibleSigma1 f) : ∃ c : Cob 1, ∀ n, c.eval ![n] = f n := by
  obtain ⟨φ, hφ, ⟨t, htot⟩, hgraf⟩ := hf
  obtain ⟨c, hc⟩ := busqueda_es_cobham φ hφ t fun M _ hM => (htot M hM).1
  exact ⟨c, fun n => (htot ℕ Acotada.nat_esModeloS12).2 n _ _ (hc n) (hgraf n)⟩

/-- **Control**: la hipótesis no es vacía. La identidad es Σᵇ₁-definible (`definible_id`, de `Definibles.lean`), y
el teorema da un programa de Cobham que la calcula. -/
example : ∃ c : Cob 1, ∀ n, c.eval ![n] = n := definible_es_cobham id Acotada.definible_id

end Teorema

end Cobham
end Sagitta.Map
