import Sagitta.Map.Representar

/-!
# Toda fórmula Σᵇ₁ de Buss se representa con programas fijos (R5b, parte 5)

## Qué hay

* **`Representa P δ t`**: los programas `δ`, `t` representan `P` en todos los modelos a la vez. La dirección
  «hay testigo ⇒ `P`» vale en **todo** modelo de `TC` (ℕ incluido); la otra, en los saturados.
* **`progEnun`**, **`aguda_unif`**: las fórmulas agudas son un programa, el mismo en todo modelo.
* **`trT_mono`**: los términos de Buss son crecientes.
* **`sigma_representa`**, **`pi_representa`**: toda `EsSigma1` se representa, y la negación de toda `EsPi1` también.
  Por inducción conjunta sobre las dos clases de r.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language
open Acotada (Fun Rel)

/-! ## Enunciados y fórmulas agudas, uniformes -/

/-- El programa de un enunciado. -/
def progEnun {n : ℕ} : Enunciado n → Cob n
  | .ec p q => igual p q
  | .no e => no (progEnun e)
  | .yy e f => yy (progEnun e) (progEnun f)
  | .oo e f => oo (progEnun e) (progEnun f)
  | .entonces e f => oo (no (progEnun e)) (progEnun f)

theorem ap_progEnun {M : Type} [LC.Structure M] [M ⊨ TC] {n : ℕ} :
    ∀ (e : Enunciado n) (v : Fin n → M), ap (progEnun e) v = cero0 M ↔ e.Vale v
  | .ec p q, v => by
      have h := Enunciado.transferir (M := M)
        (.yy (.entonces (.ec (igual p q) .cero) (.ec p q)) (.entonces (.ec p q) (.ec (igual p q) .cero)))
        (fun w => by
          simp only [Enunciado.Vale, ap_nat, eval_cero]
          exact ⟨(igual_vale p q w).mp, (igual_vale p q w).mpr⟩) v
      simp only [Enunciado.Vale, ap_cero] at h
      exact ⟨h.1, h.2⟩
  | .no e, v => by rw [progEnun, ap_no, ne_eq, ap_progEnun e]; rfl
  | .yy e f, v => by rw [progEnun, ap_yy, ap_progEnun e, ap_progEnun f]; rfl
  | .oo e f, v => by rw [progEnun, ap_oo, ap_progEnun e, ap_progEnun f]; rfl
  | .entonces e f, v => by
      rw [progEnun, ap_oo, ap_no, ne_eq, ap_progEnun e, ap_progEnun f]
      exact ⟨fun h₁ h₂ => h₁.elim (fun h₃ => absurd h₂ h₃) id, fun h₁ => (Classical.em _).elim
        (fun h₂ => .inr (h₁ h₂)) .inl⟩

/-- **Toda fórmula aguda es un programa que da 0**, el mismo en todo modelo de `TC`. -/
theorem aguda_unif {a : ℕ} : ∀ {n : ℕ} {φ : LB.BoundedFormula (Fin a) n}, Acotada.EsAguda φ →
    ∃ χ : Cob (a + n), ∀ (M : Type) [LC.Structure M] [M ⊨ TC] (z : Fin (a + n) → M),
      Val φ z ↔ ap χ z = cero0 M := by
  intro n φ h
  induction h with
  | falso =>
    exact ⟨progEnun (trF id (BoundedFormula.falsum : LB.BoundedFormula (Fin a) _)), fun M _ _ z =>
      (val_trF BoundedFormula.IsQF.falsum z).trans (ap_progEnun _ z).symm⟩
  | igual t u =>
    exact ⟨progEnun (trF id (BoundedFormula.equal t u)), fun M _ _ z =>
      (val_trF (BoundedFormula.IsAtomic.equal t u).isQF z).trans (ap_progEnun _ z).symm⟩
  | rel R ts =>
    exact ⟨progEnun (trF id (BoundedFormula.rel R ts)), fun M _ _ z =>
      (val_trF (BoundedFormula.IsAtomic.rel R ts).isQF z).trans (ap_progEnun _ z).symm⟩
  | imp _ _ ih₁ ih₂ =>
    obtain ⟨χ₁, h₁⟩ := ih₁
    obtain ⟨χ₂, h₂⟩ := ih₂
    refine ⟨oo (no χ₁) χ₂, fun M _ _ z => ?_⟩
    rw [val_imp, ap_oo, ap_no, ne_eq, h₁ M z, h₂ M z]
    exact ⟨fun h => (Classical.em _).elim (fun h' => .inr (h h')) .inl,
      fun h h' => h.elim (fun h'' => absurd h' h'') id⟩
  | @todoAgudo n t φ _ ih =>
    obtain ⟨χ, hχ⟩ := ih
    refine ⟨no (c2 .resta (buscarUltima (no χ) (trT id t)) (c1 .largo (trT id t))), fun M _ _ z => ?_⟩
    obtain ⟨h1, h2⟩ := buscarUltima_modelo (no χ) (trT id t) z
    rw [ap_no, ap_c2, ap_c1, ne_eq]
    change Val (BoundedFormula.all _) z ↔ ¬ LeM _ (ap Cob.largo ![ap (trT id t) z])
    rw [val_all]
    simp only [val_imp, val_leF_nueva, hχ M]
    constructor
    · intro h hB
      exact (ap_no χ _).mp (h1 hB) (h _ hB)
    · intro hB x hx
      by_contra hc
      exact hB (h2 x hx ((ap_no χ _).mpr hc))
  | @existeAgudo n t φ _ ih =>
    obtain ⟨χ, hχ⟩ := ih
    refine ⟨c2 .resta (buscarUltima χ (trT id t)) (c1 .largo (trT id t)), fun M _ _ z => ?_⟩
    obtain ⟨h1, h2⟩ := buscarUltima_modelo χ (trT id t) z
    rw [ap_c2, ap_c1]
    change Val (BoundedFormula.ex _) z ↔ LeM _ (ap Cob.largo ![ap (trT id t) z])
    rw [val_ex]
    simp only [val_inf, val_leF_nueva, hχ M]
    constructor
    · rintro ⟨x, hx, hc⟩
      exact h2 x hx hc
    · intro hB
      exact ⟨_, hB, h1 hB⟩

/-! ## Los términos de Buss crecen -/

theorem progFun_mono {n : ℕ} (f : Fun n) : Mono (progFun f) := by
  intro v w h
  cases f with
  | cero => exact le_refl _
  | suc => exact Nat.succ_le_succ (h 0)
  | long => exact Nat.size_le_size (h 0)
  | mitad => exact Nat.div_le_div_right (h 0)
  | suma => exact Nat.add_le_add (h 0) (h 1)
  | prod => exact Nat.mul_le_mul (h 0) (h 1)
  | smash =>
    exact Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul (Nat.size_le_size (h 0)) (Nat.size_le_size (h 1)))

/-- **Los términos de Buss son crecientes** en todas sus variables. -/
theorem trT_mono {α : Type} {a n : ℕ} (ρ : α → Fin a) : ∀ t : LB.Term (α ⊕ Fin n), Mono (trT ρ t)
  | .var (.inl _) => fun _ _ h => h _
  | .var (.inr _) => fun _ _ h => h _
  | .func f ts => fun v w h => progFun_mono f _ _ fun i => trT_mono ρ (ts i) v w h

/-! ## Valores de las formas de Buss -/

section Valores

variable {M : Type} [LC.Structure M] [M ⊨ TC]

/-- `x ≤ t` con `x` la variable recién ligada, para `t` cualquiera. -/
theorem val_leF_gen {a n : ℕ} (t : LB.Term (Fin a ⊕ Fin n)) (z : Fin (a + n) → M) (x : M) :
    Val (Acotada.leF Acotada.nueva (Acotada.sube t)) (Fin.snoc z x : Fin (a + n + 1) → M) ↔
      LeM x (ap (trT id t) z) := by
  have hn : ValT (Acotada.nueva : LB.Term (Fin a ⊕ Fin (n + 1))) (Fin.snoc z x : Fin (a + n + 1) → M) = x := by
    simp only [ValT, Acotada.nueva, Term.realize_var, Sum.elim_inr]
    rw [snoc_natAdd, Fin.snoc_last]
  have hl : ValT (Acotada.sube t) (Fin.snoc z x : Fin (a + n + 1) → M) = ap (trT id t) z := by
    rw [valT_sube, valT_eq]
  change relLe Rel.le (fun i => ValT (![Acotada.nueva, Acotada.sube t] i) _) ↔ _
  have e : (fun i => ValT (![Acotada.nueva, Acotada.sube t] i)
      (Fin.snoc z x : Fin (a + n + 1) → M)) = ![x, ap (trT id t) z] := by
    funext i; fin_cases i
    · exact hn
    · exact hl
  rw [e]
  simp only [relLe, LeM, restaM, ap_cero]

omit [M ⊨ TC] in
theorem val_not {a n : ℕ} (φ : LB.BoundedFormula (Fin a) n) (z : Fin (a + n) → M) :
    Val φ.not z ↔ ¬ Val φ z := Iff.rfl

omit [M ⊨ TC] in
theorem val_sup {a n : ℕ} (φ ψ : LB.BoundedFormula (Fin a) n) (z : Fin (a + n) → M) :
    Val (φ ⊔ ψ) z ↔ Val φ z ∨ Val ψ z := by
  simp only [Val, BoundedFormula.realize_sup]

theorem val_existe {a n : ℕ} (t : LB.Term (Fin a ⊕ Fin n)) (φ : LB.BoundedFormula (Fin a) (n + 1))
    (z : Fin (a + n) → M) :
    Val (Acotada.existeAcotado t φ) z ↔ ∃ x, LeM x (ap (trT id t) z) ∧ Val φ (Fin.snoc z x) := by
  rw [Acotada.existeAcotado, val_ex]
  simp only [val_inf, val_leF_gen]

theorem val_paraTodo {a n : ℕ} (t : LB.Term (Fin a ⊕ Fin n)) (φ : LB.BoundedFormula (Fin a) (n + 1))
    (z : Fin (a + n) → M) :
    Val (Acotada.paraTodoAcotado t φ) z ↔ ∀ x, LeM x (ap (trT id t) z) → Val φ (Fin.snoc z x) := by
  rw [Acotada.paraTodoAcotado, val_all]
  simp only [val_imp, val_leF_gen]

theorem trT_tLong {a n : ℕ} (t : LB.Term (Fin a ⊕ Fin n)) (z : Fin (a + n) → M) :
    ap (trT id (Acotada.tLong t)) z = ap Cob.largo ![ap (trT id t) z] := by
  simp only [Acotada.tLong, trT, ap_comp]
  congr 1; funext i; fin_cases i; rfl

end Valores

/-! ## Representar, con los mismos programas en todos los modelos -/

/-- **`δ` y `t` representan `P`** en todos los modelos: hay testigo ⇒ `P`, en todo modelo de `TC`; y `P` ⇒ hay
testigo, en los saturados. -/
def Representa {A : ℕ} (P : (M : Type) → [LC.Structure M] → (Fin A → M) → Prop) (δ : Cob (A + 1)) (t : Cob A) :
    Prop :=
  Mono t ∧ (∀ (M : Type) [LC.Structure M] [M ⊨ TC] (z : Fin A → M), Testif δ t z → P M z) ∧
    ∀ R : Realizacion, Generada R → Saturada R → ∀ z : Fin A → R.M, P R.M z → Testif δ t z

theorem repr_congr {A : ℕ} {P Q : (M : Type) → [LC.Structure M] → (Fin A → M) → Prop} {δ : Cob (A + 1)}
    {t : Cob A} (h : Representa P δ t)
    (hPQ : ∀ (M : Type) [LC.Structure M] [M ⊨ TC] (z : Fin A → M), P M z ↔ Q M z) : Representa Q δ t :=
  ⟨h.1, fun M _ _ z hz => (hPQ M z).mp (h.2.1 M z hz), fun R hG hS z hz => h.2.2 R hG hS z ((hPQ R.M z).mpr hz)⟩

theorem repr_prog {A : ℕ} {P : (M : Type) → [LC.Structure M] → (Fin A → M) → Prop} (χ : Cob A)
    (h : ∀ (M : Type) [LC.Structure M] [M ⊨ TC] (z : Fin A → M), P M z ↔ ap χ z = cero0 M) :
    Representa P (levantar χ) .cero :=
  ⟨fun _ _ _ => le_refl _, fun M _ _ z hz => (h M z).mpr ((testif_prog χ z).mp hz),
    fun R _ _ z hz => (testif_prog χ z).mpr ((h R.M z).mp hz)⟩

theorem repr_o {A : ℕ} {P Q : (M : Type) → [LC.Structure M] → (Fin A → M) → Prop} {δ₁ δ₂ : Cob (A + 1)}
    {t₁ t₂ : Cob A} (h₁ : Representa P δ₁ t₁) (h₂ : Representa Q δ₂ t₂) :
    Representa (fun M _ z => P M z ∨ Q M z) (pO δ₁ t₁ δ₂ t₂) (c2 .suma t₁ t₂) :=
  ⟨mono_suma h₁.1 h₂.1,
    fun M _ _ z hz => ((testif_o δ₁ t₁ δ₂ t₂ z).mp hz).imp (h₁.2.1 M z) (h₂.2.1 M z),
    fun R hG hS z hz => (testif_o δ₁ t₁ δ₂ t₂ z).mpr (hz.imp (h₁.2.2 R hG hS z) (h₂.2.2 R hG hS z))⟩

/-- «y», en todos los modelos: `Testif` del par es `Testif` de los dos. -/
theorem testif_y2 {M : Type} [LC.Structure M] [M ⊨ TC] {A : ℕ} (δ₁ : Cob (A + 1)) (t₁ : Cob A)
    (δ₂ : Cob (A + 1)) (t₂ : Cob A) (m₂ : Mono t₂) (z : Fin A → M) :
    Testif (pEx (pY (pLev δ₂) δ₁) (levantar t₂) t₁) (tEx (levantar t₂) t₁) z ↔
      Testif δ₁ t₁ z ∧ Testif δ₂ t₂ z := by
  rw [testif_existe _ _ (mono_levantar m₂)]
  simp only [testif_y, testif_lev]
  constructor
  · rintro ⟨y, hy, h₂, h₁⟩; exact ⟨⟨y, hy, h₁⟩, h₂⟩
  · rintro ⟨⟨y, hy, h₁⟩, h₂⟩; exact ⟨y, hy, h₂, h₁⟩

theorem repr_y {A : ℕ} {P Q : (M : Type) → [LC.Structure M] → (Fin A → M) → Prop} {δ₁ δ₂ : Cob (A + 1)}
    {t₁ t₂ : Cob A} (h₁ : Representa P δ₁ t₁) (h₂ : Representa Q δ₂ t₂) :
    Representa (fun M _ z => P M z ∧ Q M z) (pEx (pY (pLev δ₂) δ₁) (levantar t₂) t₁) (tEx (levantar t₂) t₁) :=
  ⟨mono_tEx (mono_levantar h₂.1) h₁.1,
    fun M _ _ z hz => let ⟨a, b⟩ := (testif_y2 δ₁ t₁ δ₂ t₂ h₂.1 z).mp hz; ⟨h₁.2.1 M z a, h₂.2.1 M z b⟩,
    fun R hG hS z hz => (testif_y2 δ₁ t₁ δ₂ t₂ h₂.1 z).mpr ⟨h₁.2.2 R hG hS z hz.1, h₂.2.2 R hG hS z hz.2⟩⟩

theorem repr_existe {A : ℕ} {P : (M : Type) → [LC.Structure M] → (Fin (A + 1) → M) → Prop}
    {δ : Cob (A + 1 + 1)} {s : Cob (A + 1)} (h : Representa P δ s) (t : Cob A) (mt : Mono t) :
    Representa (fun M _ z => ∃ x, LeM x (ap t z) ∧ P M (Fin.snoc z x)) (pEx δ s t) (tEx s t) :=
  ⟨mono_tEx h.1 mt,
    fun M _ _ z hz => let ⟨x, hx, hd⟩ := (testif_existe δ s h.1 t z).mp hz; ⟨x, hx, h.2.1 M _ hd⟩,
    fun R hG hS z hz => let ⟨x, hx, hp⟩ := hz; (testif_existe δ s h.1 t z).mpr ⟨x, hx, h.2.2 R hG hS _ hp⟩⟩

theorem repr_paraTodo {A : ℕ} {P : (M : Type) → [LC.Structure M] → (Fin (A + 1) → M) → Prop}
    {δ : Cob (A + 1 + 1)} {s : Cob (A + 1)} (h : Representa P δ s) (t : Cob A) (mt : Mono t) :
    Representa (fun M _ z => ∀ x, LeM x (ap Cob.largo ![ap t z]) → P M (Fin.snoc z x)) (pPT δ s t) (tPT s t) :=
  ⟨mono_tPT h.1 mt,
    fun M _ _ z hz x hx => h.2.1 M _ (testif_paraTodo_sano δ s t z hz x hx),
    fun R hG hS z hz => testif_paraTodo_completo R hG hS δ s h.1 t mt z fun x hx => h.2.2 R hG hS _ (hz x hx)⟩

/-! ## La inducción conjunta -/

mutual

/-- **Toda fórmula Σᵇ₁ de Buss se representa**, con los mismos programas en todos los modelos. -/
theorem sigma_representa {a : ℕ} : ∀ {n : ℕ} {φ : LB.BoundedFormula (Fin a) n}, Acotada.EsSigma1 φ →
    ∃ (δ : Cob (a + n + 1)) (t : Cob (a + n)), Representa (fun _ _ z => Val φ z) δ t
  | _, _, .aguda h => by
      obtain ⟨χ, hχ⟩ := aguda_unif h
      exact ⟨_, _, repr_prog χ hχ⟩
  | _, _, .existe t h => by
      obtain ⟨δ, s, hr⟩ := sigma_representa h
      exact ⟨_, _, repr_congr (repr_existe hr (trT id t) (trT_mono id t))
        fun M _ _ z => (val_existe t _ z).symm⟩
  | _, _, .todoAgudo t h => by
      obtain ⟨δ, s, hr⟩ := sigma_representa h
      exact ⟨_, _, repr_congr (repr_paraTodo hr (trT id t) (trT_mono id t))
        fun M _ _ z => by rw [val_paraTodo, trT_tLong]⟩
  | _, _, .y h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := sigma_representa h₁
      obtain ⟨δ₂, t₂, r₂⟩ := sigma_representa h₂
      exact ⟨_, _, repr_congr (repr_y r₁ r₂) fun M _ _ z => (val_inf _ _ z).symm⟩
  | _, _, .o h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := sigma_representa h₁
      obtain ⟨δ₂, t₂, r₂⟩ := sigma_representa h₂
      exact ⟨_, _, repr_congr (repr_o r₁ r₂) fun M _ _ z => (val_sup _ _ z).symm⟩
  | _, _, .no h => by
      obtain ⟨δ, t, r⟩ := pi_representa h
      exact ⟨_, _, repr_congr r fun M _ _ z => (val_not _ z).symm⟩
  | _, _, .imp h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := pi_representa h₁
      obtain ⟨δ₂, t₂, r₂⟩ := sigma_representa h₂
      exact ⟨_, _, repr_congr (repr_o r₁ r₂) fun M _ _ z => by
        rw [val_imp]; exact ⟨fun h => h.elim (fun h' h'' => absurd h'' h') (fun h' _ => h'),
          fun h => (Classical.em _).elim (fun h' => .inr (h h')) .inl⟩⟩

/-- **La negación de toda fórmula Πᵇ₁ de Buss se representa.** -/
theorem pi_representa {a : ℕ} : ∀ {n : ℕ} {φ : LB.BoundedFormula (Fin a) n}, Acotada.EsPi1 φ →
    ∃ (δ : Cob (a + n + 1)) (t : Cob (a + n)), Representa (fun _ _ z => ¬ Val φ z) δ t
  | _, _, .aguda h => by
      obtain ⟨χ, hχ⟩ := aguda_unif h
      exact ⟨_, _, repr_prog (no χ) fun M _ _ z => by rw [hχ M z, ap_no]⟩
  | _, _, .todo t h => by
      obtain ⟨δ, s, hr⟩ := pi_representa h
      exact ⟨_, _, repr_congr (repr_existe hr (trT id t) (trT_mono id t)) fun M _ _ z => by
        rw [val_paraTodo]; push Not; rfl⟩
  | _, _, .existeAgudo t h => by
      obtain ⟨δ, s, hr⟩ := pi_representa h
      exact ⟨_, _, repr_congr (repr_paraTodo hr (trT id t) (trT_mono id t)) fun M _ _ z => by
        rw [val_existe, trT_tLong]; push Not; rfl⟩
  | _, _, .y h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := pi_representa h₁
      obtain ⟨δ₂, t₂, r₂⟩ := pi_representa h₂
      exact ⟨_, _, repr_congr (repr_o r₁ r₂) fun M _ _ z => by rw [val_inf]; tauto⟩
  | _, _, .o h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := pi_representa h₁
      obtain ⟨δ₂, t₂, r₂⟩ := pi_representa h₂
      exact ⟨_, _, repr_congr (repr_y r₁ r₂) fun M _ _ z => by rw [val_sup]; tauto⟩
  | _, _, .no h => by
      obtain ⟨δ, t, r⟩ := sigma_representa h
      exact ⟨_, _, repr_congr r fun M _ _ z => by rw [val_not, not_not]⟩
  | _, _, .imp h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := sigma_representa h₁
      obtain ⟨δ₂, t₂, r₂⟩ := pi_representa h₂
      exact ⟨_, _, repr_congr (repr_y r₁ r₂) fun M _ _ z => by rw [val_imp]; tauto⟩

end

end Cobham
end Sagitta.Map
