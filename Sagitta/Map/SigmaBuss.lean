import Sagitta.Map.EnlaceBuss

/-!
# Las fórmulas de Buss en los modelos de la teoría de Cobham (R5b)

Quinto paso de la ruta por modelos, segunda parte.

## Parte 1: las fórmulas agudas son programas

* **`Val`**: el valor de una fórmula de Buss con variables libres `Fin a` y ligadas `Fin n`, como predicado sobre un
  solo vector de `a + n` elementos.
* **`programa_de_enunciado`**: todo `Enunciado` es, en todo modelo de `TC`, «un programa da 0».
* **`buscar_modelo`**: lo que `buscar` cumple en ℕ lo cumple en todo modelo, también con elementos no estándar.
* **`aguda_programa`**: toda fórmula aguda de Buss (`EsAguda`, solo cuantificadores `≤ |t|`) equivale en todo
  modelo de `TC` a «un programa da 0». Los cuantificadores agudos se eliminan con `buscar`.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language
open Acotada (Fun Rel)

section Modelo

variable {M : Type} [LC.Structure M] [M ⊨ TC]

/-- `x ≤ y` en un modelo de `TC`. -/
def LeM (x y : M) : Prop := restaM x y = cero0 M

/-- El valor de una fórmula de Buss con libres `Fin a` y ligadas `Fin n`, sobre un vector de `a + n`. -/
def Val {a n : ℕ} (φ : LB.BoundedFormula (Fin a) n) (z : Fin (a + n) → M) : Prop :=
  @BoundedFormula.Realize LB M (estructuraBuss M) _ _ φ (z ∘ Fin.castAdd n) (z ∘ Fin.natAdd a)

/-- El valor de un término de Buss sobre el mismo vector. -/
def ValT {a n : ℕ} (t : LB.Term (Fin a ⊕ Fin n)) (z : Fin (a + n) → M) : M :=
  @Term.realize LB M (estructuraBuss M) _ (Sum.elim (z ∘ Fin.castAdd n) (z ∘ Fin.natAdd a)) t

omit [LC.Structure M] [M ⊨ TC] in
theorem append_partes {a n : ℕ} (z : Fin (a + n) → M) :
    Fin.append (z ∘ Fin.castAdd n) (z ∘ Fin.natAdd a) = z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]

theorem valT_eq {a n : ℕ} (t : LB.Term (Fin a ⊕ Fin n)) (z : Fin (a + n) → M) :
    ValT t z = ap (trT id t) z := by
  have := realize_trT (estructuraBuss M) (compatible_buss M) id (z ∘ Fin.castAdd n) (z ∘ Fin.natAdd a) t
  rw [append_partes, Function.comp_id] at this
  exact this

/-- **Las fórmulas sin cuantificadores, traducidas.** -/
theorem val_trF {a n : ℕ} {φ : LB.BoundedFormula (Fin a) n} (hφ : φ.IsQF) (z : Fin (a + n) → M) :
    Val φ z ↔ (trF id φ).Vale z := by
  have := realize_trF (estructuraBuss M) (compatible_buss M) id (z ∘ Fin.castAdd n) (z ∘ Fin.natAdd a) hφ
  rw [append_partes, Function.comp_id] at this
  exact this

omit [LC.Structure M] [M ⊨ TC] in
theorem snoc_castAdd {a n : ℕ} (z : Fin (a + n) → M) (x : M) :
    (Fin.snoc z x : Fin (a + n + 1) → M) ∘ Fin.castAdd (n + 1) = z ∘ Fin.castAdd n := by
  funext i
  simp only [Function.comp_apply]
  rw [show (Fin.castAdd (n + 1) i : Fin (a + (n + 1))) = Fin.castSucc (Fin.castAdd n i) from Fin.ext rfl,
    Fin.snoc_castSucc]

omit [LC.Structure M] [M ⊨ TC] in
theorem snoc_natAdd {a n : ℕ} (z : Fin (a + n) → M) (x : M) :
    (Fin.snoc z x : Fin (a + n + 1) → M) ∘ Fin.natAdd a = Fin.snoc (z ∘ Fin.natAdd a) x := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Function.comp_apply, Fin.snoc_last]
    rw [show (Fin.natAdd a (Fin.last n) : Fin (a + (n + 1))) = Fin.last (a + n) from Fin.ext rfl, Fin.snoc_last]
  · simp only [Function.comp_apply, Fin.snoc_castSucc]
    rw [show (Fin.natAdd a (Fin.castSucc j) : Fin (a + (n + 1))) = Fin.castSucc (Fin.natAdd a j) from Fin.ext rfl,
      Fin.snoc_castSucc]

omit [M ⊨ TC] in
/-- **El «para todo»** sobre el vector: agrega el valor al final. -/
theorem val_all {a n : ℕ} (φ : LB.BoundedFormula (Fin a) (n + 1)) (z : Fin (a + n) → M) :
    Val φ.all z ↔ ∀ x, Val φ (Fin.snoc z x : Fin (a + n + 1) → M) := by
  simp only [Val, BoundedFormula.realize_all]
  refine forall_congr' fun x => ?_
  rw [snoc_castAdd, snoc_natAdd]

omit [M ⊨ TC] in
/-- **El «existe»** sobre el vector. -/
theorem val_ex {a n : ℕ} (φ : LB.BoundedFormula (Fin a) (n + 1)) (z : Fin (a + n) → M) :
    Val φ.ex z ↔ ∃ x, Val φ (Fin.snoc z x : Fin (a + n + 1) → M) := by
  simp only [Val, BoundedFormula.realize_ex]
  refine exists_congr fun x => ?_
  rw [snoc_castAdd, snoc_natAdd]

omit [M ⊨ TC] in
theorem valT_sube {a n : ℕ} (t : LB.Term (Fin a ⊕ Fin n)) (z : Fin (a + n) → M) (x : M) :
    ValT (Acotada.sube t) (Fin.snoc z x : Fin (a + n + 1) → M) = ValT t z := by
  simp only [ValT, Acotada.sube, Term.realize_relabel]
  congr 1
  funext v
  rcases v with i | j
  · exact congrFun (snoc_castAdd z x) i
  · have := congrFun (snoc_natAdd z x) (Fin.castSucc j)
    simp only [Function.comp_apply, Fin.snoc_castSucc] at this
    exact this

/-- `x ≤ |t|` con `x` la variable recién ligada. -/
theorem val_leF_nueva {a n : ℕ} (t : LB.Term (Fin a ⊕ Fin n)) (z : Fin (a + n) → M) (x : M) :
    Val (Acotada.leF Acotada.nueva (Acotada.sube (Acotada.tLong t))) (Fin.snoc z x : Fin (a + n + 1) → M) ↔
      LeM x (ap Cob.largo ![ap (trT id t) z]) := by
  have hn : ValT (Acotada.nueva : LB.Term (Fin a ⊕ Fin (n + 1))) (Fin.snoc z x : Fin (a + n + 1) → M) = x := by
    simp only [ValT, Acotada.nueva, Term.realize_var, Sum.elim_inr]
    rw [snoc_natAdd, Fin.snoc_last]
  have hl : ValT (Acotada.sube (Acotada.tLong t)) (Fin.snoc z x : Fin (a + n + 1) → M) =
      ap Cob.largo ![ap (trT id t) z] := by
    rw [valT_sube, ← valT_eq]
    simp only [ValT, Acotada.tLong, Term.realize_func]
    change ap (progFun Fun.long) _ = _
    congr 1; funext i; fin_cases i; rfl
  change relLe Rel.le (fun i => ValT (![Acotada.nueva, Acotada.sube (Acotada.tLong t)] i) _) ↔ _
  have e : (fun i => ValT (![Acotada.nueva, Acotada.sube (Acotada.tLong t)] i)
      (Fin.snoc z x : Fin (a + n + 1) → M)) = ![x, ap Cob.largo ![ap (trT id t) z] ] := by
    funext i; fin_cases i
    · exact hn
    · exact hl
  rw [e]
  simp only [relLe, LeM, restaM, ap_cero]

/-! ## De enunciados a programas -/

/-- **Todo enunciado es un programa que da 0**, en todo modelo de `TC`. -/
theorem programa_de_enunciado {n : ℕ} :
    ∀ e : Enunciado n, ∃ χ : Cob n, ∀ v : Fin n → M, ap χ v = cero0 M ↔ e.Vale v
  | .ec p q => ⟨igual p q, fun v => by
      have h := Enunciado.transferir (M := M)
        (.yy (.entonces (.ec (igual p q) .cero) (.ec p q)) (.entonces (.ec p q) (.ec (igual p q) .cero)))
        (fun w => by
          simp only [Enunciado.Vale, ap_nat, eval_cero]
          exact ⟨(igual_vale p q w).mp, (igual_vale p q w).mpr⟩) v
      simp only [Enunciado.Vale, ap_cero] at h
      exact ⟨h.1, h.2⟩⟩
  | .no e => let ⟨χ, h⟩ := programa_de_enunciado e
      ⟨no χ, fun v => by rw [ap_no, ne_eq, h]; rfl⟩
  | .yy e f => let ⟨χ, h⟩ := programa_de_enunciado e; let ⟨ψ, h'⟩ := programa_de_enunciado f
      ⟨yy χ ψ, fun v => by rw [ap_yy, h, h']; rfl⟩
  | .oo e f => let ⟨χ, h⟩ := programa_de_enunciado e; let ⟨ψ, h'⟩ := programa_de_enunciado f
      ⟨oo χ ψ, fun v => by rw [ap_oo, h, h']; rfl⟩
  | .entonces e f => let ⟨χ, h⟩ := programa_de_enunciado e; let ⟨ψ, h'⟩ := programa_de_enunciado f
      ⟨oo (no χ) ψ, fun v => by
        rw [ap_oo, ap_no, ne_eq, h, h']
        exact ⟨fun h₁ h₂ => h₁.elim (fun h₃ => absurd h₂ h₃) id, fun h₁ => (Classical.em _).elim
          (fun h₂ => .inr (h₁ h₂)) .inl⟩⟩

/-! ## `buscar` en un modelo -/

/-- **Lo que `buscar` cumple en ℕ lo cumple en todo modelo**: si lo que entrega está en el rango, es un cero; y no
se pasa del rango si hay un cero en él. -/
theorem buscar_modelo {m : ℕ} (f : Cob (m + 1)) (t : M) (p : Fin m → M) :
    (LeM (ap (buscar f) (Fin.cons t p)) (ap Cob.largo ![t]) →
      ap f (Fin.cons (ap (buscar f) (Fin.cons t p)) p) = cero0 M) ∧
    ∀ x, LeM x (ap Cob.largo ![t]) → ap f (Fin.cons x p) = cero0 M →
      LeM (ap (buscar f) (Fin.cons t p)) (ap Cob.largo ![t]) := by
  -- Variables: `(x, t, p)`.
  let B : Cob (m + 2) := .comp (buscar f) (Fin.cons (.proy 1) fun i => .proy i.succ.succ)
  let T : Cob (m + 2) := c1 .largo (.proy 1)
  let FB : Cob (m + 2) := .comp f (Fin.cons B fun i => .proy i.succ.succ)
  let FX : Cob (m + 2) := .comp f (Fin.cons (.proy 0) fun i => .proy i.succ.succ)
  have hT : ∀ v : Fin (m + 2) → M, Enunciado.Vale
      (.yy (.entonces (.ec (c2 .resta B T) .cero) (.ec FB .cero))
        (.entonces (.ec (c2 .resta (.proy 0) T) .cero)
          (.entonces (.ec FX .cero) (.ec (c2 .resta B T) .cero)))) v := fun v =>
    Enunciado.transferir _ (fun v => by
      simp only [T, Enunciado.Vale, ap_nat, eval_cero, eval_c2, eval_resta, eval_c1, eval_largo, eval_proy]
      have eB : B.eval v = (buscar f).eval (Fin.cons (v 1) fun i => v i.succ.succ) := by
        simp only [B, Cob.eval]; congr 1; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
      have eFB : FB.eval v = f.eval (Fin.cons (B.eval v) fun i => v i.succ.succ) := by
        simp only [FB, Cob.eval]; congr 1; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
      have eFX : FX.eval v = f.eval (Fin.cons (v 0) fun i => v i.succ.succ) := by
        simp only [FX, Cob.eval]; congr 1; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
      obtain ⟨-, h2, h3⟩ := buscar_spec f (fun i => v i.succ.succ) (v 1)
      rw [eFB, eB]
      refine ⟨fun h => h2 (by omega), fun hx hf => ?_⟩
      have := h3 (v 0) (by omega) (by rw [← eFX]; exact hf)
      omega) v
  have hp : ∀ x : M, (fun i : Fin m => ap (Cob.proy i.succ.succ) (Fin.cons x (Fin.cons t p) : Fin (m + 2) → M)) = p :=
    fun x => funext fun i => by rw [ap_proy]; rfl
  have eB : ∀ x : M, ap B (Fin.cons x (Fin.cons t p)) = ap (buscar f) (Fin.cons t p) := fun x => by
    rw [ap_comp_cons, ap_proy, hp]; rfl
  have eT : ∀ x : M, ap T (Fin.cons x (Fin.cons t p)) = ap Cob.largo ![t] := fun x => by
    rw [ap_c1, ap_proy]; rfl
  refine ⟨fun h => ?_, fun x hx hf => ?_⟩
  · have := (hT (Fin.cons t (Fin.cons t p))).1
    simp only [Enunciado.Vale, ap_c2, ap_cero, eB, eT] at this
    have h' := this h
    simp only [FB, ap_comp_cons, eB, hp] at h'
    exact h'
  · have := (hT (Fin.cons x (Fin.cons t p))).2
    simp only [Enunciado.Vale, ap_c2, ap_cero, eB, eT, ap_proy] at this
    refine this hx ?_
    simp only [FX, ap_comp_cons, ap_proy, Fin.cons_zero]
    exact hf

omit [M ⊨ TC] in
theorem val_imp {a n : ℕ} (φ ψ : LB.BoundedFormula (Fin a) n) (z : Fin (a + n) → M) :
    Val (φ.imp ψ) z ↔ (Val φ z → Val ψ z) := Iff.rfl

omit [M ⊨ TC] in
theorem val_inf {a n : ℕ} (φ ψ : LB.BoundedFormula (Fin a) n) (z : Fin (a + n) → M) :
    Val (φ ⊓ ψ) z ↔ Val φ z ∧ Val ψ z := by
  simp only [Val, BoundedFormula.realize_inf]

/-- Pasar la última variable al frente. -/
def alFrente (k : ℕ) : Fin (k + 1) → Fin (k + 1) := Fin.lastCases 0 fun i => i.succ

omit [LC.Structure M] [M ⊨ TC] in
theorem cons_alFrente {k : ℕ} (z : Fin k → M) (x : M) :
    (Fin.cons x z : Fin (k + 1) → M) ∘ alFrente k = Fin.snoc z x := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Function.comp_apply, alFrente, Fin.lastCases_last, Fin.cons_zero, Fin.snoc_last]
  · simp only [Function.comp_apply, alFrente, Fin.lastCases_castSucc, Fin.cons_succ, Fin.snoc_castSucc]

/-- `buscar` sobre la última variable de `χ`, con el rango `|t|`. -/
def buscarUltima {k : ℕ} (χ : Cob (k + 1)) (t : Cob k) : Cob k :=
  .comp (buscar (χ.renombrar (alFrente k))) (Fin.cons t fun i => .proy i)

theorem ap_buscarUltima {k : ℕ} (χ : Cob (k + 1)) (t : Cob k) (z : Fin k → M) :
    ap (buscarUltima χ t) z = ap (buscar (χ.renombrar (alFrente k))) (Fin.cons (ap t z) z) := by
  rw [buscarUltima, ap_comp_cons]
  congr 2; funext i; rw [ap_proy]

/-- `buscar` en un modelo, para la última variable. -/
theorem buscarUltima_modelo {k : ℕ} (χ : Cob (k + 1)) (t : Cob k) (z : Fin k → M) :
    (LeM (ap (buscarUltima χ t) z) (ap Cob.largo ![ap t z]) →
      ap χ (Fin.snoc z (ap (buscarUltima χ t) z)) = cero0 M) ∧
    ∀ x, LeM x (ap Cob.largo ![ap t z]) → ap χ (Fin.snoc z x) = cero0 M →
      LeM (ap (buscarUltima χ t) z) (ap Cob.largo ![ap t z]) := by
  obtain ⟨h1, h2⟩ := buscar_modelo (χ.renombrar (alFrente k)) (ap t z) z
  simp only [ap_renombrar, cons_alFrente] at h1 h2
  rw [ap_buscarUltima]
  exact ⟨h1, h2⟩

/-- **Toda fórmula aguda es un programa que da 0**, en todo modelo de `TC`. -/
theorem aguda_programa {a : ℕ} : ∀ {n : ℕ} {φ : LB.BoundedFormula (Fin a) n}, Acotada.EsAguda φ →
    ∃ χ : Cob (a + n), ∀ z : Fin (a + n) → M, Val φ z ↔ ap χ z = cero0 M := by
  intro n φ h
  induction h with
  | falso =>
    obtain ⟨χ, hχ⟩ := programa_de_enunciado (M := M) (trF id (BoundedFormula.falsum : LB.BoundedFormula (Fin a) _))
    exact ⟨χ, fun z => (val_trF BoundedFormula.IsQF.falsum z).trans (hχ z).symm⟩
  | igual t u =>
    obtain ⟨χ, hχ⟩ := programa_de_enunciado (M := M) (trF id (BoundedFormula.equal t u))
    exact ⟨χ, fun z => (val_trF (BoundedFormula.IsAtomic.equal t u).isQF z).trans (hχ z).symm⟩
  | rel R ts =>
    obtain ⟨χ, hχ⟩ := programa_de_enunciado (M := M) (trF id (BoundedFormula.rel R ts))
    exact ⟨χ, fun z => (val_trF (BoundedFormula.IsAtomic.rel R ts).isQF z).trans (hχ z).symm⟩
  | imp _ _ ih₁ ih₂ =>
    obtain ⟨χ₁, h₁⟩ := ih₁
    obtain ⟨χ₂, h₂⟩ := ih₂
    refine ⟨oo (no χ₁) χ₂, fun z => ?_⟩
    rw [val_imp, ap_oo, ap_no, ne_eq, h₁, h₂]
    exact ⟨fun h => (Classical.em _).elim (fun h' => .inr (h h')) .inl,
      fun h h' => h.elim (fun h'' => absurd h' h'') id⟩
  | @todoAgudo n t φ _ ih =>
    obtain ⟨χ, hχ⟩ := ih
    let T : Cob (a + n) := trT id t
    let B := buscarUltima (no χ) T
    refine ⟨no (c2 .resta B (c1 .largo T)), fun z => ?_⟩
    obtain ⟨h1, h2⟩ := buscarUltima_modelo (no χ) T z
    rw [ap_no, ap_c2, ap_c1, ne_eq]
    change Val (BoundedFormula.all _) z ↔ ¬ LeM (ap B z) (ap Cob.largo ![ap T z])
    rw [val_all]
    simp only [val_imp, val_leF_nueva, hχ]
    constructor
    · intro h hB
      exact (ap_no χ _).mp (h1 hB) (h _ hB)
    · intro hB x hx
      by_contra hc
      exact hB (h2 x hx ((ap_no χ _).mpr hc))
  | @existeAgudo n t φ _ ih =>
    obtain ⟨χ, hχ⟩ := ih
    let T : Cob (a + n) := trT id t
    let B := buscarUltima χ T
    refine ⟨c2 .resta B (c1 .largo T), fun z => ?_⟩
    obtain ⟨h1, h2⟩ := buscarUltima_modelo χ T z
    rw [ap_c2, ap_c1]
    change Val (BoundedFormula.ex _) z ↔ LeM (ap B z) (ap Cob.largo ![ap T z])
    rw [val_ex]
    simp only [val_inf, val_leF_nueva, hχ]
    constructor
    · rintro ⟨x, hx, hc⟩
      exact h2 x hx hc
    · intro hB
      exact ⟨_, hB, h1 hB⟩

end Modelo

/-! ## Parte 2: lo representable -/

/-- Un programa **creciente** en todos sus argumentos (en ℕ). -/
def Mono {A : ℕ} (t : Cob A) : Prop := ∀ v w : Fin A → ℕ, (∀ i, v i ≤ w i) → t.eval v ≤ t.eval w

/-- **Correr a la derecha** `|u|` bits: `⌊p / 2^|u|⌋`. Los argumentos son `(u, p)`. -/
def correr : Cob 2 := .rn (.proy 0) (c1 .mitad (.proy 1)) (.proy 1)

theorem correr_eval (p : ℕ) : ∀ u : ℕ, correr.eval ![u, p] = p / 2 ^ Nat.size u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  have hv : (![u, p] : Fin 2 → ℕ) = Fin.cons u ![p] := by funext i; fin_cases i <;> rfl
  rw [hv]
  by_cases hu : u = 0
  · subst hu; rw [correr, eval_rec_cero]; simp
  · rw [correr, eval_rec_pos _ _ _ _ hu, ← correr]
    have := ih (u / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hu) (by decide))
    rw [show (Fin.cons (u / 2) ![p] : Fin 2 → ℕ) = ![u / 2, p] by funext i; fin_cases i <;> rfl, this]
    have hs : Nat.size u = Nat.size (u / 2) + 1 := by
      rw [← Acotada.size_mitad hu]
    simp only [eval_c1, eval_mitad, eval_proy, Fin.cons_zero, Fin.cons_one, Matrix.cons_val_zero]
    rw [hs, Nat.pow_succ, ← Nat.div_div_eq_div_mul, min_eq_left (Nat.div_le_self _ _ |>.trans (Nat.div_le_self _ _))]

/-- Lo que el emparejamiento de ancho `|b|` cumple en ℕ: si `x ≤ b`, del par `y · 2^|b| + x` se recuperan `x` e `y`. -/
theorem par_nat (b x y : ℕ) (hx : x ≤ b) :
    (y * 2 ^ Nat.size b + x) / 2 ^ Nat.size b = y ∧
      (y * 2 ^ Nat.size b + x) - (y * 2 ^ Nat.size b + x) / 2 ^ Nat.size b * 2 ^ Nat.size b = x := by
  have hlt : x < 2 ^ Nat.size b := lt_of_le_of_lt hx (Nat.lt_size_self b)
  have hpos : 0 < 2 ^ Nat.size b := Nat.two_pow_pos _
  have hd : (y * 2 ^ Nat.size b + x) / 2 ^ Nat.size b = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  refine ⟨hd, ?_⟩
  rw [hd]; omega

section Modelo2

variable {M : Type} [LC.Structure M] [M ⊨ TC]

/-- **Representable**: `P` equivale a «existe `y ≤ t(z)` con `δ(z, y) = 0`», con `t` creciente. -/
def Rep (M : Type) [LC.Structure M] {A : ℕ} (P : (Fin A → M) → Prop) : Prop :=
  ∃ (δ : Cob (A + 1)) (t : Cob A), Mono t ∧
    ∀ z, P z ↔ ∃ y, LeM y (ap t z) ∧ ap δ (Fin.snoc z y) = cero0 M

/-- Un programa con una variable más al final, que no usa. -/
def levantar {A : ℕ} (t : Cob A) : Cob (A + 1) := t.renombrar Fin.castSucc

/-- La última variable. -/
def ultima (A : ℕ) : Cob (A + 1) := .proy (Fin.last A)

theorem ap_levantar {A : ℕ} (t : Cob A) (z : Fin A → M) (y : M) :
    ap (levantar t) (Fin.snoc z y) = ap t z := by
  rw [levantar, ap_renombrar]; congr 1; funext i; exact Fin.snoc_castSucc _ _ _

theorem ap_ultima {A : ℕ} (z : Fin A → M) (y : M) : ap (ultima A) (Fin.snoc z y) = y := by
  rw [ultima, ap_proy, Fin.snoc_last]

theorem levantar_eval {A : ℕ} (t : Cob A) (v : Fin (A + 1) → ℕ) :
    (levantar t).eval v = t.eval (Fin.init v) := by
  have := ap_levantar (M := ℕ) t (Fin.init v) (v (Fin.last A))
  rw [Fin.snoc_init_self] at this
  exact this

omit [M ⊨ TC] in
theorem rep_congr {A : ℕ} {P Q : (Fin A → M) → Prop} (h : Rep M P) (hPQ : ∀ z, P z ↔ Q z) : Rep M Q := by
  obtain ⟨δ, t, ht, h⟩ := h
  exact ⟨δ, t, ht, fun z => (hPQ z).symm.trans (h z)⟩

/-- `LeM` como un programa que da 0. -/
theorem leM_iff {A : ℕ} (a b : Cob A) (v : Fin A → M) :
    ap (c2 .resta a b) v = cero0 M ↔ LeM (ap a v) (ap b v) := by
  rw [ap_c2]; rfl

/-- **Lo que es un programa es representable**, sin testigo. -/
theorem rep_prog {A : ℕ} (P : (Fin A → M) → Prop) (χ : Cob A) (h : ∀ z, P z ↔ ap χ z = cero0 M) :
    Rep M P := by
  refine ⟨levantar χ, .cero, fun _ _ _ => le_refl _, fun z => ?_⟩
  rw [h]
  -- `0 ≤ 0` en el modelo.
  have h00 : LeM (ap (Cob.cero : Cob A) z) (ap (Cob.cero : Cob A) z) := by
    have := Enunciado.transferir (M := M) (.ec (c2 .resta (Cob.cero : Cob A) .cero) .cero)
      (fun w => by simp [Enunciado.Vale]) z
    exact (leM_iff _ _ z).mp (by simpa only [Enunciado.Vale, ap_cero] using this)
  constructor
  · intro hc; exact ⟨_, h00, by rw [ap_levantar]; exact hc⟩
  · rintro ⟨y, -, hy⟩; rwa [ap_levantar] at hy

/-- **«o»** de representables. -/
theorem rep_o {A : ℕ} {P Q : (Fin A → M) → Prop} (hP : Rep M P) (hQ : Rep M Q) : Rep M (fun z => P z ∨ Q z) := by
  obtain ⟨δ₁, t₁, m₁, h₁⟩ := hP
  obtain ⟨δ₂, t₂, m₂, h₂⟩ := hQ
  let Y := ultima A
  refine ⟨oo (yy (c2 .resta Y (levantar t₁)) δ₁) (yy (c2 .resta Y (levantar t₂)) δ₂), c2 .suma t₁ t₂,
    fun v w hvw => by simp only [eval_c2, eval_suma]; exact Nat.add_le_add (m₁ v w hvw) (m₂ v w hvw),
    fun z => ?_⟩
  -- `y ≤ t₁ → y ≤ t₁ + t₂` y `y ≤ t₂ → y ≤ t₁ + t₂`, en el modelo.
  have hsum := fun y => Enunciado.transferir (M := M)
    (.yy (.entonces (.ec (c2 .resta Y (levantar t₁)) .cero) (.ec (c2 .resta Y (levantar (c2 .suma t₁ t₂))) .cero))
      (.entonces (.ec (c2 .resta Y (levantar t₂)) .cero) (.ec (c2 .resta Y (levantar (c2 .suma t₁ t₂))) .cero)))
    (fun w => by
      simp only [Enunciado.Vale, ap_nat, eval_cero, eval_c2, eval_resta, eval_suma, levantar_eval]
      constructor <;> intro h <;> omega) (Fin.snoc z y)
  simp only [Y, Enunciado.Vale, ap_cero, leM_iff, ap_levantar, ap_ultima] at hsum
  show P z ∨ Q z ↔ _
  rw [h₁, h₂]
  simp only [Y, ap_oo, ap_yy, leM_iff, ap_levantar, ap_ultima]
  constructor
  · rintro (⟨y, hy, hd⟩ | ⟨y, hy, hd⟩)
    · exact ⟨y, (hsum y).1 hy, .inl ⟨hy, hd⟩⟩
    · exact ⟨y, (hsum y).2 hy, .inr ⟨hy, hd⟩⟩
  · rintro ⟨y, -, (⟨hy, hd⟩ | ⟨hy, hd⟩)⟩
    · exact .inl ⟨y, hy, hd⟩
    · exact .inr ⟨y, hy, hd⟩

/-- **«y» con un programa**: si `Q` es un programa, `P ∧ Q` es representable. -/
theorem rep_y_prog {A : ℕ} {P Q : (Fin A → M) → Prop} (hP : Rep M P) (χ : Cob A)
    (hQ : ∀ z, Q z ↔ ap χ z = cero0 M) : Rep M (fun z => P z ∧ Q z) := by
  obtain ⟨δ, t, m, h⟩ := hP
  refine ⟨yy δ (levantar χ), t, m, fun z => ?_⟩
  show P z ∧ Q z ↔ _
  rw [h, hQ]
  simp only [ap_yy, ap_levantar]
  constructor
  · rintro ⟨⟨y, hy, hd⟩, hc⟩; exact ⟨y, hy, hd, hc⟩
  · rintro ⟨y, hy, hd, hc⟩; exact ⟨⟨y, hy, hd⟩, hc⟩

theorem ap_comp_snoc {n m : ℕ} (f : Cob (m + 1)) (gs : Fin m → Cob n) (g : Cob n) (v : Fin n → M) :
    ap (Cob.comp f (Fin.snoc gs g)) v = ap f (Fin.snoc (fun i => ap (gs i) v) (ap g v)) := by
  rw [ap_comp]; congr 1; funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

/-- Las primeras variables, como programas de un vector más largo. -/
def primeras (A : ℕ) : Fin A → Cob (A + 1) := fun i => .proy (Fin.castSucc i)

theorem ap_primeras {A : ℕ} (z : Fin A → M) (y : M) :
    (fun i => ap (primeras A i) (Fin.snoc z y : Fin (A + 1) → M)) = z := by
  funext i; rw [primeras, ap_proy, Fin.snoc_castSucc]

theorem ap_snoc_primeras {A : ℕ} (g : Cob (A + 1)) (z : Fin A → M) (p : M) :
    (fun i => ap (Fin.snoc (α := fun _ => Cob (A + 1)) (primeras A) g i) (Fin.snoc z p : Fin (A + 1) → M)) =
      Fin.snoc z (ap g (Fin.snoc z p)) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc, primeras, ap_proy]

@[simp] theorem cero0_nat : cero0 ℕ = 0 := rfl

/-- `s(z, x)` con `x` dado por un programa de `z`. -/
def enPunto {A : ℕ} (s : Cob (A + 1)) (x : Cob A) : Cob A := .comp s (Fin.snoc (fun i => .proy i) x)

theorem ap_enPunto {A : ℕ} (s : Cob (A + 1)) (x : Cob A) (z : Fin A → M) :
    ap (enPunto s x) z = ap s (Fin.snoc z (ap x z)) := by
  rw [enPunto, ap_comp_snoc]; congr 2; funext i; rw [ap_proy]

/-- **«Existe `x ≤ t`» de un representable es representable.** El testigo nuevo es el par `y · 2^|t| + x`. -/
theorem rep_existe {A : ℕ} {P : (Fin (A + 1) → M) → Prop} (hP : Rep M P) (t : Cob A) (mt : Mono t) :
    Rep M (fun z => ∃ x, LeM x (ap t z) ∧ P (Fin.snoc z x)) := by
  obtain ⟨δ, s, ms, h⟩ := hP
  -- Sobre `z`.
  let POW : Cob A := c2 .smash t uno
  let BND : Cob A := c2 .suma (c2 .prod (enPunto s t) POW) t
  -- Sobre `(z, p)`.
  let SND : Cob (A + 1) := c2 correr (levantar t) (ultima A)
  let FST : Cob (A + 1) := c2 .resta (ultima A) (c2 .prod SND (levantar POW))
  let δ' : Cob (A + 1) :=
    yy (c2 .resta FST (levantar t))
      (yy (c2 .resta SND (.comp s (Fin.snoc (primeras A) FST)))
        (.comp δ (Fin.snoc (Fin.snoc (primeras A) FST) SND)))
  have hPOW : ∀ z : Fin A → ℕ, POW.eval z = 2 ^ Nat.size (t.eval z) := fun z => by
    simp only [POW, eval_c2, eval_uno]
    show 2 ^ (Nat.size (t.eval z) * Nat.size 1) = 2 ^ Nat.size (t.eval z)
    rw [Nat.size_one, Nat.mul_one]
  refine ⟨δ', BND, fun v w hvw => ?_, fun z => ?_⟩
  · -- `BND` es creciente.
    have ht := mt v w hvw
    have hsv : (enPunto s t).eval v ≤ (enPunto s t).eval w := by
      have e : ∀ u : Fin A → ℕ, (enPunto s t).eval u = s.eval (Fin.snoc u (t.eval u)) := fun u => by
        have := ap_enPunto (M := ℕ) s t u; simpa only [ap_nat] using this
      rw [e, e]
      refine ms _ _ fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]; exact ht
      · simp only [Fin.snoc_castSucc]; exact hvw j
    simp only [BND, eval_c2, eval_suma, eval_prod, hPOW]
    exact Nat.add_le_add (Nat.mul_le_mul hsv (Nat.pow_le_pow_right (by decide) (Nat.size_le_size ht))) ht
  · have hδ' : ∀ p : M, ap δ' (Fin.snoc z p) = cero0 M ↔
        LeM (ap FST (Fin.snoc z p)) (ap t z) ∧
        LeM (ap SND (Fin.snoc z p)) (ap s (Fin.snoc z (ap FST (Fin.snoc z p)))) ∧
        ap δ (Fin.snoc (Fin.snoc z (ap FST (Fin.snoc z p))) (ap SND (Fin.snoc z p))) = cero0 M := fun p => by
      simp only [δ', ap_yy, leM_iff, ap_levantar, ap_comp_snoc, ap_primeras, ap_snoc_primeras]
    constructor
    · rintro ⟨x, hx, hPx⟩
      obtain ⟨y, hy, hd⟩ := (h _).mp hPx
      -- Los hechos del par, transferidos de ℕ. Variables `(z, x, y)`.
      let X : Cob (A + 2) := .proy (Fin.castSucc (Fin.last A))
      let Yv : Cob (A + 2) := ultima (A + 1)
      let PAR : Cob (A + 2) := c2 .suma (c2 .prod Yv (levantar (levantar POW))) X
      let Z2 : Fin A → Cob (A + 2) := fun i => .proy (Fin.castSucc (Fin.castSucc i))
      let enPar : Cob (A + 1) → Cob (A + 2) := fun q => .comp q (Fin.snoc Z2 PAR)
      have hT := Enunciado.transferir (M := M)
        (.entonces (.ec (c2 .resta X (levantar (levantar t))) .cero)
          (.entonces (.ec (c2 .resta Yv (levantar s)) .cero)
            (.yy (.ec (c2 .resta PAR (levantar (levantar BND))) .cero)
              (.yy (.ec (enPar FST) X) (.ec (enPar SND) Yv)))))
        (fun w => by
          rw [← Fin.snoc_init_self w, ← Fin.snoc_init_self (Fin.init w)]
          generalize Fin.init (Fin.init w) = u
          generalize (Fin.init w) (Fin.last A) = a
          generalize w (Fin.last (A + 1)) = b
          have eX : ap X (Fin.snoc (Fin.snoc u a) b : Fin (A + 2) → ℕ) = a := by
            simp only [X, ap_proy, Fin.snoc_castSucc, Fin.snoc_last]
          have eZ : (fun i => ap (Z2 i) (Fin.snoc (Fin.snoc u a) b : Fin (A + 2) → ℕ)) = u := by
            funext i; simp only [Z2, ap_proy, Fin.snoc_castSucc]
          have ePAR : ap PAR (Fin.snoc (Fin.snoc u a) b : Fin (A + 2) → ℕ) =
              b * 2 ^ Nat.size (t.eval u) + a := by
            simp only [PAR, ap_c2, Yv, ap_ultima, ap_levantar, eX, ap_nat, hPOW]; rfl
          have eSND : ∀ q, ap SND (Fin.snoc u q : Fin (A + 1) → ℕ) = q / 2 ^ Nat.size (t.eval u) := fun q => by
            simp only [SND, ap_c2, ap_levantar, ap_ultima, ap_nat]; exact correr_eval q (t.eval u)
          have eFST : ∀ q, ap FST (Fin.snoc u q : Fin (A + 1) → ℕ) =
              q - q / 2 ^ Nat.size (t.eval u) * 2 ^ Nat.size (t.eval u) := fun q => by
            simp only [FST, ap_c2, ap_ultima, eSND, ap_levantar, ap_nat, hPOW]; rfl
          have eEn : ∀ q : Cob (A + 1), ap (enPar q) (Fin.snoc (Fin.snoc u a) b : Fin (A + 2) → ℕ) =
              ap q (Fin.snoc u (b * 2 ^ Nat.size (t.eval u) + a)) := fun q => by
            simp only [enPar, ap_comp_snoc, eZ, ePAR]
          simp only [Enunciado.Vale, ap_cero, eX, eEn, eSND, eFST, Yv, ap_ultima, ap_levantar, ap_c2, ap_nat,
            eval_resta, ePAR, cero0_nat]
          intro ha hb
          rw [Nat.sub_eq_zero_iff_le] at ha hb ⊢
          obtain ⟨h1, h2⟩ := par_nat (t.eval u) a b ha
          refine ⟨?_, h2, h1⟩
          have hs : s.eval (Fin.snoc u a) ≤ s.eval (Fin.snoc u (t.eval u)) := ms _ _ fun i => by
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp only [Fin.snoc_last]; exact ha
            · simp only [Fin.snoc_castSucc]; exact le_refl _
          have eB : (BND.eval u) = s.eval (Fin.snoc u (t.eval u)) * 2 ^ Nat.size (t.eval u) + t.eval u := by
            have := ap_enPunto (M := ℕ) s t u
            simp only [ap_nat] at this
            simp only [BND, eval_c2, eval_suma, eval_prod, hPOW, this]
          rw [eB]
          exact Nat.add_le_add (Nat.mul_le_mul_right _ (hb.trans hs)) ha)
        (Fin.snoc (Fin.snoc z x) y)
      have eX : ap X (Fin.snoc (Fin.snoc z x) y : Fin (A + 2) → M) = x := by
        simp only [X, ap_proy, Fin.snoc_castSucc, Fin.snoc_last]
      have eZ : (fun i => ap (Z2 i) (Fin.snoc (Fin.snoc z x) y : Fin (A + 2) → M)) = z := by
        funext i; simp only [Z2, ap_proy, Fin.snoc_castSucc]
      have eEn : ∀ q : Cob (A + 1), ap (enPar q) (Fin.snoc (Fin.snoc z x) y : Fin (A + 2) → M) =
          ap q (Fin.snoc z (ap PAR (Fin.snoc (Fin.snoc z x) y))) := fun q => by
        simp only [enPar, ap_comp_snoc, eZ]
      simp only [Enunciado.Vale, ap_cero, leM_iff, eX, eEn, Yv, ap_ultima, ap_levantar] at hT
      obtain ⟨hB, hF, hS⟩ := hT hx hy
      refine ⟨_, hB, (hδ' _).mpr ⟨?_, ?_, ?_⟩⟩
      · rw [hF]; exact hx
      · rw [hF, hS]; exact hy
      · rw [hF, hS]; exact hd
    · rintro ⟨p, -, hp⟩
      obtain ⟨h1, h2, h3⟩ := (hδ' p).mp hp
      exact ⟨_, h1, (h _).mpr ⟨_, h2, h3⟩⟩

end Modelo2


end Cobham
end Sagitta.Map
