import Sagitta.Map.Coleccion

/-!
# Representar las fórmulas Σᵇ₁ con programas fijos (R5b, parte 4)

`SigmaBuss.lean` y `Coleccion.lean` prueban que lo representable se cierra bajo «o», «existe acotado» y el «para
todo» agudo, pero cada modelo elige sus programas. El teorema final necesita **los mismos programas en todos los
modelos**, y que una dirección valga **también en ℕ**, que no es saturado. Aquí todo se dice sobre `Testif δ t z`,
«hay un `y ≤ t(z)` con `δ(z, y) = 0`», con los programas a la vista:

* cada operación es una equivalencia entre `Testif` del programa nuevo y una combinación de `Testif` de los viejos;
* esas equivalencias valen en **todo** modelo de `TC`, salvo una dirección de la colección, que pide saturación.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language

/-- **Hay testigo**: un `y ≤ t(z)` con `δ(z, y) = 0`. -/
def Testif {M : Type} [LC.Structure M] {A : ℕ} (δ : Cob (A + 1)) (t : Cob A) (z : Fin A → M) : Prop :=
  ∃ y, LeM y (ap t z) ∧ ap δ (Fin.snoc z y) = cero0 M

/-! ## Los programas de cada operación -/

/-- «o». -/
def pO {A : ℕ} (δ₁ : Cob (A + 1)) (t₁ : Cob A) (δ₂ : Cob (A + 1)) (t₂ : Cob A) : Cob (A + 1) :=
  oo (yy (c2 .resta (ultima A) (levantar t₁)) δ₁) (yy (c2 .resta (ultima A) (levantar t₂)) δ₂)

/-- «y» con un programa. -/
def pY {A : ℕ} (δ : Cob (A + 1)) (χ : Cob A) : Cob (A + 1) := yy δ (levantar χ)

/-- Una variable más, antes del testigo, que no se usa. -/
def pLev {A : ℕ} (δ : Cob (A + 1)) : Cob (A + 1 + 1) :=
  δ.renombrar (Fin.lastCases (Fin.last (A + 1)) fun i => Fin.castSucc (Fin.castSucc i))

/-- `2^|t|`. -/
def pPot {A : ℕ} (t : Cob A) : Cob A := c2 .smash t uno

/-- La segunda mitad de un par de ancho `|t|`. -/
def pSnd {A : ℕ} (t : Cob A) : Cob (A + 1) := c2 correr (levantar t) (ultima A)

/-- La primera mitad de un par de ancho `|t|`. -/
def pFst {A : ℕ} (t : Cob A) : Cob (A + 1) := c2 .resta (ultima A) (c2 .prod (pSnd t) (levantar (pPot t)))

/-- «existe `x ≤ t`»: el testigo nuevo es el par `y · 2^|t| + x`. -/
def pEx {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (t : Cob A) : Cob (A + 1) :=
  yy (c2 .resta (pFst t) (levantar t))
    (yy (c2 .resta (pSnd t) (.comp s (Fin.snoc (primeras A) (pFst t))))
      (.comp δ (Fin.snoc (Fin.snoc (primeras A) (pFst t)) (pSnd t))))

/-- La cota del «existe»: `s(z, t) · 2^|t| + t`. -/
def tEx {A : ℕ} (s : Cob (A + 1)) (t : Cob A) : Cob A := c2 .suma (c2 .prod (enPunto s t) (pPot t)) t

/-! ## Crecientes -/

theorem mono_suma {A : ℕ} {t₁ t₂ : Cob A} (m₁ : Mono t₁) (m₂ : Mono t₂) : Mono (c2 .suma t₁ t₂) :=
  fun v w h => by simp only [eval_c2, eval_suma]; exact Nat.add_le_add (m₁ v w h) (m₂ v w h)

theorem mono_levantar {A : ℕ} {t : Cob A} (m : Mono t) : Mono (levantar t) :=
  fun v w h => by rw [levantar_eval, levantar_eval]; exact m _ _ fun i => h _

theorem pPot_eval {A : ℕ} (t : Cob A) (z : Fin A → ℕ) : (pPot t).eval z = 2 ^ Nat.size (t.eval z) := by
  simp only [pPot, eval_c2, eval_uno]
  change 2 ^ (Nat.size (t.eval z) * Nat.size 1) = 2 ^ Nat.size (t.eval z)
  rw [Nat.size_one, Nat.mul_one]

theorem enPunto_eval {A : ℕ} (s : Cob (A + 1)) (t : Cob A) (u : Fin A → ℕ) :
    (enPunto s t).eval u = s.eval (Fin.snoc u (t.eval u)) := by
  have := ap_enPunto (M := ℕ) s t u; simpa only [ap_nat] using this

theorem mono_tEx {A : ℕ} {s : Cob (A + 1)} {t : Cob A} (ms : Mono s) (mt : Mono t) : Mono (tEx s t) := by
  intro v w hvw
  have ht := mt v w hvw
  have hsv : (enPunto s t).eval v ≤ (enPunto s t).eval w := by
    rw [enPunto_eval, enPunto_eval]
    refine ms _ _ fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact ht
    · simp only [Fin.snoc_castSucc]; exact hvw j
  simp only [tEx, eval_c2, eval_suma, eval_prod, pPot_eval]
  exact Nat.add_le_add (Nat.mul_le_mul hsv (Nat.pow_le_pow_right (by decide) (Nat.size_le_size ht))) ht

section Algebra

variable {M : Type} [LC.Structure M] [M ⊨ TC]

/-- **Un programa**: con cota `0`, hay testigo justo cuando el programa da 0. -/
theorem testif_prog {A : ℕ} (χ : Cob A) (z : Fin A → M) :
    Testif (levantar χ) .cero z ↔ ap χ z = cero0 M := by
  have h00 : LeM (ap (Cob.cero : Cob A) z) (ap (Cob.cero : Cob A) z) := by
    have := Enunciado.transferir (M := M) (.ec (c2 .resta (Cob.cero : Cob A) .cero) .cero)
      (fun w => by simp [Enunciado.Vale]) z
    exact (leM_iff _ _ z).mp (by simpa only [Enunciado.Vale, ap_cero] using this)
  constructor
  · rintro ⟨y, -, hy⟩; rwa [ap_levantar] at hy
  · intro hc; exact ⟨_, h00, by rw [ap_levantar]; exact hc⟩

/-- **«o»**. -/
theorem testif_o {A : ℕ} (δ₁ : Cob (A + 1)) (t₁ : Cob A) (δ₂ : Cob (A + 1)) (t₂ : Cob A) (z : Fin A → M) :
    Testif (pO δ₁ t₁ δ₂ t₂) (c2 .suma t₁ t₂) z ↔ Testif δ₁ t₁ z ∨ Testif δ₂ t₂ z := by
  have hsum := fun y => Enunciado.transferir (M := M)
    (.yy (.entonces (.ec (c2 .resta (ultima A) (levantar t₁)) .cero)
        (.ec (c2 .resta (ultima A) (levantar (c2 .suma t₁ t₂))) .cero))
      (.entonces (.ec (c2 .resta (ultima A) (levantar t₂)) .cero)
        (.ec (c2 .resta (ultima A) (levantar (c2 .suma t₁ t₂))) .cero)))
    (fun w => by
      simp only [Enunciado.Vale, ap_nat, eval_cero, eval_c2, eval_resta, eval_suma, levantar_eval]
      constructor <;> intro h <;> omega) (Fin.snoc z y)
  simp only [Enunciado.Vale, ap_cero, leM_iff, ap_levantar, ap_ultima] at hsum
  simp only [Testif, pO, ap_oo, ap_yy, leM_iff, ap_levantar, ap_ultima]
  constructor
  · rintro ⟨y, -, (⟨hy, hd⟩ | ⟨hy, hd⟩)⟩
    · exact .inl ⟨y, hy, hd⟩
    · exact .inr ⟨y, hy, hd⟩
  · rintro (⟨y, hy, hd⟩ | ⟨y, hy, hd⟩)
    · exact ⟨y, (hsum y).1 hy, .inl ⟨hy, hd⟩⟩
    · exact ⟨y, (hsum y).2 hy, .inr ⟨hy, hd⟩⟩

/-- **«y» con un programa**. -/
theorem testif_y {A : ℕ} (δ : Cob (A + 1)) (t : Cob A) (χ : Cob A) (z : Fin A → M) :
    Testif (pY δ χ) t z ↔ Testif δ t z ∧ ap χ z = cero0 M := by
  simp only [Testif, pY, ap_yy, ap_levantar]
  constructor
  · rintro ⟨y, hy, hd, hc⟩; exact ⟨⟨y, hy, hd⟩, hc⟩
  · rintro ⟨⟨y, hy, hd⟩, hc⟩; exact ⟨y, hy, hd, hc⟩

/-- **Una variable más**, que no se usa. -/
theorem testif_lev {A : ℕ} (δ : Cob (A + 1)) (t : Cob A) (z : Fin A → M) (x : M) :
    Testif (pLev δ) (levantar t) (Fin.snoc z x) ↔ Testif δ t z := by
  have e : ∀ y : M, ap (pLev δ) (Fin.snoc (Fin.snoc z x) y) = ap δ (Fin.snoc z y) := fun y => by
    rw [pLev, ap_renombrar]; congr 1; funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Function.comp_apply, Fin.lastCases_last, Fin.snoc_last]
    · simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.snoc_castSucc]
  simp only [Testif, e, ap_levantar]

/-- **«Existe `x ≤ t`»**: hay testigo del par justo cuando hay un `x ≤ t` con testigo. Vale en todo modelo. -/
theorem testif_existe {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (ms : Mono s) (t : Cob A) (z : Fin A → M) :
    Testif (pEx δ s t) (tEx s t) z ↔ ∃ x, LeM x (ap t z) ∧ Testif δ s (Fin.snoc z x) := by
  unfold Testif
  have hδ' : ∀ p : M, ap (pEx δ s t) (Fin.snoc z p) = cero0 M ↔
      LeM (ap (pFst t) (Fin.snoc z p)) (ap t z) ∧
      LeM (ap (pSnd t) (Fin.snoc z p)) (ap s (Fin.snoc z (ap (pFst t) (Fin.snoc z p)))) ∧
      ap δ (Fin.snoc (Fin.snoc z (ap (pFst t) (Fin.snoc z p))) (ap (pSnd t) (Fin.snoc z p))) = cero0 M := fun p => by
    simp only [pEx, ap_yy, leM_iff, ap_levantar, ap_comp_snoc, ap_primeras, ap_snoc_primeras]
  refine Iff.symm ?_
  constructor
  · rintro ⟨x, hx, hPx⟩
    obtain ⟨y, hy, hd⟩ := hPx
    -- Los hechos del par, transferidos de ℕ. Variables `(z, x, y)`.
    let X : Cob (A + 2) := .proy (Fin.castSucc (Fin.last A))
    let Yv : Cob (A + 2) := ultima (A + 1)
    let PAR : Cob (A + 2) := c2 .suma (c2 .prod Yv (levantar (levantar (pPot t)))) X
    let Z2 : Fin A → Cob (A + 2) := fun i => .proy (Fin.castSucc (Fin.castSucc i))
    let enPar : Cob (A + 1) → Cob (A + 2) := fun q => .comp q (Fin.snoc Z2 PAR)
    have hT := Enunciado.transferir (M := M)
      (.entonces (.ec (c2 .resta X (levantar (levantar t))) .cero)
        (.entonces (.ec (c2 .resta Yv (levantar s)) .cero)
          (.yy (.ec (c2 .resta PAR (levantar (levantar (tEx s t)))) .cero)
            (.yy (.ec (enPar (pFst t)) X) (.ec (enPar (pSnd t)) Yv)))))
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
          simp only [PAR, ap_c2, Yv, ap_ultima, ap_levantar, eX, ap_nat, pPot_eval t]; rfl
        have eSND : ∀ q, ap (pSnd t) (Fin.snoc u q : Fin (A + 1) → ℕ) = q / 2 ^ Nat.size (t.eval u) := fun q => by
          simp only [pSnd, ap_c2, ap_levantar, ap_ultima, ap_nat]; exact correr_eval q (t.eval u)
        have eFST : ∀ q, ap (pFst t) (Fin.snoc u q : Fin (A + 1) → ℕ) =
            q - q / 2 ^ Nat.size (t.eval u) * 2 ^ Nat.size (t.eval u) := fun q => by
          simp only [pFst, ap_c2, ap_ultima, eSND, ap_levantar, ap_nat, pPot_eval t]; rfl
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
        have eB : ((tEx s t).eval u) = s.eval (Fin.snoc u (t.eval u)) * 2 ^ Nat.size (t.eval u) + t.eval u := by
          have := ap_enPunto (M := ℕ) s t u
          simp only [ap_nat] at this
          simp only [tEx, eval_c2, eval_suma, eval_prod, pPot_eval t, this]
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
    exact ⟨_, h1, ⟨_, h2, h3⟩⟩

end Algebra

/-! ## La colección, con programas a la vista -/

def zsP (A : ℕ) : Fin A → Cob (A + 2) := fun i => .proy (Fin.castSucc (Fin.castSucc i))
def wP (A : ℕ) : Cob (A + 2) := .proy (Fin.castSucc (Fin.last A))
def xP (A : ℕ) : Cob (A + 2) := .proy (Fin.last (A + 1))

/-- La cota de todos los testigos: `s(z, |t|)`. -/
def pS {A : ℕ} (s : Cob (A + 1)) (t : Cob A) : Cob A := enPunto s (c1 .largo t)

/-- El dígito `x` de `w`. Variables `(z, w, x)`. -/
def pE {A : ℕ} (s : Cob (A + 1)) (t : Cob A) : Cob (A + 2) :=
  .comp leerB ![(pS s t).comp (zsP A), t.comp (zsP A), wP A, xP A]

/-- «El dígito `x` de `w` es testigo en `x`». -/
def pI {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (t : Cob A) : Cob (A + 2) :=
  yy (c2 .resta (pE s t) (.comp s (Fin.snoc (zsP A) (xP A))))
    (.comp δ (Fin.snoc (Fin.snoc (zsP A) (xP A)) (pE s t)))

/-- «Para todo `x ≤ |t|`, el dígito `x` de `w` es testigo en `x`». Variables `(z, w)`. -/
def pPT {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (t : Cob A) : Cob (A + 1) :=
  no (c2 .resta (buscarUltima (no (pI δ s t)) (levantar t)) (c1 .largo (levantar t)))

/-- La cota de la sucesión. -/
def tPT {A : ℕ} (s : Cob (A + 1)) (t : Cob A) : Cob A := .comp cotaB ![pS s t, t]

theorem mono_tPT {A : ℕ} {s : Cob (A + 1)} {t : Cob A} (ms : Mono s) (mt : Mono t) : Mono (tPT s t) := by
  have hSe : ∀ u : Fin A → ℕ, (pS s t).eval u = s.eval (Fin.snoc u (Nat.size (t.eval u))) := fun u => by
    have := ap_enPunto (M := ℕ) s (c1 .largo t) u
    simp only [ap_nat, eval_c1, eval_largo] at this; exact this
  have hmS : Mono (pS s t) := fun v w hvw => by
    rw [hSe, hSe]
    refine ms _ _ fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact Nat.size_le_size (mt v w hvw)
    · simp only [Fin.snoc_castSucc]; exact hvw j
  intro v w hvw
  have e : ∀ u, (fun i => ((![pS s t, t] : Fin 2 → Cob A) i).eval u) = ![(pS s t).eval u, t.eval u] := fun u => by
    funext i; fin_cases i <;> rfl
  simp only [tPT, Cob.eval]
  rw [e, e, cotaB_eval, cotaB_eval]
  calc (2 ^ Nat.size ((pS s t).eval v)) ^ (Nat.size (t.eval v) + 1)
      ≤ (2 ^ Nat.size ((pS s t).eval w)) ^ (Nat.size (t.eval v) + 1) :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (Nat.size_le_size (hmS v w hvw))) _
    _ ≤ (2 ^ Nat.size ((pS s t).eval w)) ^ (Nat.size (t.eval w) + 1) :=
        Nat.pow_le_pow_right Nat.one_le_two_pow (by have := Nat.size_le_size (mt v w hvw); omega)

section ColeccionModelo

variable {M : Type} [LC.Structure M] [M ⊨ TC]

theorem ap_pI {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (t : Cob A) (z : Fin A → M) (w x : M) :
    ap (pI δ s t) (Fin.snoc (Fin.snoc z w) x) = cero0 M ↔
      LeM (ap (pE s t) (Fin.snoc (Fin.snoc z w) x)) (ap s (Fin.snoc z x)) ∧
        ap δ (Fin.snoc (Fin.snoc z x) (ap (pE s t) (Fin.snoc (Fin.snoc z w) x))) = cero0 M := by
  have h1 : (fun i => ap (zsP A i) (Fin.snoc (Fin.snoc z w) x : Fin (A + 2) → M)) = z := by
    funext i; simp [zsP, ap_proy, Fin.snoc_castSucc]
  have h3 : ap (xP A) (Fin.snoc (Fin.snoc z w) x : Fin (A + 2) → M) = x := by simp [xP, ap_proy, Fin.snoc_last]
  simp only [pI, ap_yy, leM_iff, ap_comp_snoc, ap_snoc_fun, h1, h3]

theorem ap_pPT {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (t : Cob A) (z : Fin A → M) (w : M) :
    ap (pPT δ s t) (Fin.snoc z w) = cero0 M ↔
      ∀ x, LeM x (ap Cob.largo ![ap t z]) → ap (pI δ s t) (Fin.snoc (Fin.snoc z w) x) = cero0 M := by
  rw [pPT, paraTodo_prog, ap_levantar]

/-- **La colección, dirección sana**: si hay testigo de la sucesión, hay testigo en cada `x ≤ |t|`. Vale en todo
modelo, también en ℕ. -/
theorem testif_paraTodo_sano {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (t : Cob A) (z : Fin A → M)
    (h : Testif (pPT δ s t) (tPT s t) z) :
    ∀ x, LeM x (ap Cob.largo ![ap t z]) → Testif δ s (Fin.snoc z x) := by
  obtain ⟨w, -, hw⟩ := h
  intro x hx
  have := (ap_pPT δ s t z w).mp hw x hx
  rw [ap_pI] at this
  exact ⟨_, this.1, this.2⟩

end ColeccionModelo

/-- **La colección, dirección completa**, en el modelo saturado: si hay testigo en cada `x ≤ |t|`, hay uno de la
sucesión. -/
theorem testif_paraTodo_completo (R : Realizacion) (hG : Generada R) (hS : Saturada R) {A : ℕ}
    (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (ms : Mono s) (t : Cob A) (mt : Mono t) (z : Fin A → R.M)
    (hall : ∀ x, LeM x (ap Cob.largo ![ap t z]) → Testif δ s (Fin.snoc z x)) :
    Testif (pPT δ s t) (tPT s t) z := by
  classical
  let S : Cob A := pS s t
  let Zs : Fin A → Cob (A + 2) := fun i => .proy (Fin.castSucc (Fin.castSucc i))
  let W : Cob (A + 2) := .proy (Fin.castSucc (Fin.last A))
  let X : Cob (A + 2) := .proy (Fin.last (A + 1))
  let E : Cob (A + 2) := .comp leerB ![S.comp Zs, t.comp Zs, W, X]
  let I : Cob (A + 2) := yy (c2 .resta E (.comp s (Fin.snoc Zs X))) (.comp δ (Fin.snoc (Fin.snoc Zs X) E))
  have hv : ∀ (z : Fin A → R.M) (w x : R.M),
      (fun i => ap (Zs i) (Fin.snoc (Fin.snoc z w) x : Fin (A + 2) → R.M)) = z ∧
      ap W (Fin.snoc (Fin.snoc z w) x) = w ∧ ap X (Fin.snoc (Fin.snoc z w) x) = x := fun z w x => by
    refine ⟨funext fun i => ?_, ?_, ?_⟩ <;> simp [Zs, W, X, ap_proy, Fin.snoc_castSucc, Fin.snoc_last]
  have hE : ∀ (z : Fin A → R.M) (w x : R.M),
      ap E (Fin.snoc (Fin.snoc z w) x) = ap leerB ![ap S z, ap t z, w, x] := fun z w x => by
    obtain ⟨h1, h2, h3⟩ := hv z w x
    rw [ap_comp]; congr 1; funext i; fin_cases i
    · change ap (S.comp Zs) _ = _; rw [ap_comp, h1]; rfl
    · change ap (t.comp Zs) _ = _; rw [ap_comp, h1]; rfl
    · exact h2
    · exact h3
  have hI : ∀ (z : Fin A → R.M) (w x : R.M), ap I (Fin.snoc (Fin.snoc z w) x) = cero0 R.M ↔
      LeM (ap E (Fin.snoc (Fin.snoc z w) x)) (ap s (Fin.snoc z x)) ∧
        ap δ (Fin.snoc (Fin.snoc z x) (ap E (Fin.snoc (Fin.snoc z w) x))) = cero0 R.M := fun z w x => by
    obtain ⟨h1, -, h3⟩ := hv z w x
    simp only [I, ap_yy, leM_iff, ap_comp_snoc, ap_snoc_fun, h1, h3]
  let χ : Cob (A + 1) := no (c2 .resta (buscarUltima (no I) (levantar t)) (c1 .largo (levantar t)))
  have hχ : ∀ (z : Fin A → R.M) (w : R.M), ap χ (Fin.snoc z w) = cero0 R.M ↔
      ∀ x, LeM x (ap Cob.largo ![ap t z]) → ap I (Fin.snoc (Fin.snoc z w) x) = cero0 R.M := fun z w => by
    simp only [χ]; rw [paraTodo_prog, ap_levantar]
  have hSe : ∀ u : Fin A → ℕ, S.eval u = s.eval (Fin.snoc u (Nat.size (t.eval u))) := fun u => by
    have := ap_enPunto (M := ℕ) s (c1 .largo t) u
    simp only [ap_nat, eval_c1, eval_largo] at this; exact this
  have hmS : Mono S := fun v w hvw => by
    rw [hSe, hSe]
    refine ms _ _ fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact Nat.size_le_size (mt v w hvw)
    · simp only [Fin.snoc_castSucc]; exact hvw j
  have hcomp2 : ∀ {n : ℕ} (f : Cob 2) (a b : Cob n) (v : Fin n → R.M),
      ap (Cob.comp f ![a, b]) v = ap f ![ap a v, ap b v] := fun f a b v => by
    rw [ap_comp]; congr 1; funext i; fin_cases i <;> rfl
  unfold Testif
  -- Los parámetros, como programas de las constantes.
  choose Nz Pz hPz using fun i => hG (z i)
  let N := Finset.univ.sup Nz
  have hNz : ∀ i, Nz i ≤ N := fun i => Finset.le_sup (f := Nz) (Finset.mem_univ i)
  let Q : Fin A → Cob N := fun i => (Pz i).renombrar (Fin.castLE (hNz i))
  have hQ : (fun i => ap (Q i) (pre R.ι N)) = z := funext fun i => by rw [ap_renombrar, hPz i]; rfl
  -- El pedido de los testigos, sobre `(c̄, x, y)`.
  let lc : Fin N → Fin (N + 1 + 1) := fun j => Fin.castAdd 1 (Fin.castAdd 1 j)
  let lx : Fin (N + 1 + 1) := Fin.castAdd 1 (Fin.natAdd N 0)
  let ly : Fin (N + 1 + 1) := Fin.natAdd (N + 1) 0
  let Zc : Fin A → Cob (N + 1 + 1) := fun i => (Q i).comp fun j => .proy (lc j)
  let θ : Cob (N + 1 + 1) := oo (no (c2 .resta (.proy lx) (c1 .largo (t.comp Zc))))
    (yy (c2 .resta (.proy ly) (s.comp (Fin.snoc Zc (.proy lx))))
      (δ.comp (Fin.snoc (Fin.snoc Zc (.proy lx)) (.proy ly))))
  have hθ : ∀ x y : R.M, ap θ (Fin.append (Fin.append (pre R.ι N) ![x]) ![y]) = cero0 R.M ↔
      ¬ LeM x (ap Cob.largo ![ap t z]) ∨
        (LeM y (ap s (Fin.snoc z x)) ∧ ap δ (Fin.snoc (Fin.snoc z x) y) = cero0 R.M) := fun x y => by
    have hZ : (fun i => ap (Zc i) (Fin.append (Fin.append (pre R.ι N) ![x]) ![y])) = z := by
      rw [← hQ]; funext i; simp only [Zc, ap_comp, ap_proy, lc, Fin.append_left]
    have hx : ap (Cob.proy lx) (Fin.append (Fin.append (pre R.ι N) ![x]) ![y]) = x := by
      simp only [lx, ap_proy, Fin.append_left, Fin.append_right, Matrix.cons_val_zero]
    have hy : ap (Cob.proy ly) (Fin.append (Fin.append (pre R.ι N) ![x]) ![y]) = y := by
      simp only [ly, ap_proy, Fin.append_right, Matrix.cons_val_zero]
    simp only [θ, ap_oo, ap_no, ap_yy, ne_eq, leM_iff, ap_c1, ap_comp, ap_snoc_fun, hZ, hx, hy]
  obtain ⟨L, G0, hG0⟩ := hS N 1 θ (fun xs => by
    rw [show xs = ![xs 0] from funext fun i => by fin_cases i; rfl]
    by_cases hx : LeM (xs 0) (ap Cob.largo ![ap t z])
    · obtain ⟨y, hy, hd⟩ := hall _ hx
      exact ⟨y, (hθ _ _).mpr (.inr ⟨hy, hd⟩)⟩
    · exact ⟨xs 0, (hθ _ _).mpr (.inl hx)⟩)
  -- Todo sobre las primeras `N'` constantes.
  let N' := max N L
  have hN : N ≤ N' := le_max_left _ _
  have hL : L ≤ N' := le_max_right _ _
  let Q' : Fin A → Cob N' := fun i => (Q i).renombrar (Fin.castLE hN)
  have hQ' : (fun i => ap (Q' i) (pre R.ι N')) = z := by
    rw [← hQ]; funext i; simp only [Q', ap_renombrar]; rfl
  let G1 : Cob (N' + 1) :=
    G0.comp (Fin.append (fun j : Fin L => .proy (Fin.castSucc (Fin.castLE hL j))) ![.proy (Fin.last N')])
  have hG1 : ∀ x : R.M, ap G1 (Fin.snoc (pre R.ι N') x) = ap G0 (Fin.append (pre R.ι L) ![x]) := fun x => by
    simp only [G1, ap_comp]; congr 1; funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, ap_proy, Fin.snoc_castSucc]; rfl
    · fin_cases j; simp [Fin.append_right, ap_proy, Fin.snoc_last]
  let S1 : Cob N' := S.comp Q'
  let T1 : Cob N' := t.comp Q'
  let code : Cob N' := (armar G1 S1).comp (Fin.cons T1 fun i => .proy i)
  have hS1 : ap S1 (pre R.ι N') = ap S z := by simp only [S1, ap_comp, hQ']
  have hT1 : ap T1 (pre R.ι N') = ap t z := by simp only [T1, ap_comp, hQ']
  -- Los hechos de ℕ, transferidos. Variables `(c̄', x)`.
  let Xl := ultima N'
  let Ql : Fin A → Cob (N' + 1) := fun i => levantar (Q' i)
  have hF := fun x => Enunciado.transferir (M := R.M)
    (.yy (.ec (c2 .resta (levantar code) (.comp cotaB ![levantar S1, levantar T1])) .cero)
      (.entonces (.ec (c2 .resta Xl (c1 .largo (levantar T1))) .cero)
        (.yy (.ec (.comp leerB ![levantar S1, levantar T1, levantar code, Xl]) (recorte G1 S1))
          (.entonces (.ec (c2 .resta G1 (s.comp (Fin.snoc Ql Xl))) .cero) (.ec (recorte G1 S1) G1)))))
    (fun v => by
      rw [← Fin.snoc_init_self v]
      generalize Fin.init v = u
      generalize v (Fin.last N') = x
      have e2 : ∀ (f : Cob 2) (a b : Cob (N' + 1)), (Cob.comp f ![a, b]).eval (Fin.snoc u x) =
          f.eval ![a.eval (Fin.snoc u x), b.eval (Fin.snoc u x)] := fun f a b => by
        simp only [Cob.eval]; congr 1; funext i; fin_cases i <;> rfl
      have e4 : ∀ (f : Cob 4) (a b c d : Cob (N' + 1)), (Cob.comp f ![a, b, c, d]).eval (Fin.snoc u x) =
          f.eval ![a.eval (Fin.snoc u x), b.eval (Fin.snoc u x), c.eval (Fin.snoc u x), d.eval (Fin.snoc u x)] :=
        fun f a b c d => by simp only [Cob.eval]; congr 1; funext i; fin_cases i <;> rfl
      have eX : Xl.eval (Fin.snoc u x) = x := by simp only [Xl, ultima, eval_proy, Fin.snoc_last]
      have eQ : (fun i => (Ql i).eval (Fin.snoc u x)) = fun i => (Q' i).eval u := by
        funext i; simp only [Ql, levantar_eval, Fin.init_snoc]
      obtain ⟨c1', c2'⟩ := coleccion_nat G1 S1 T1 u
      simp only [Enunciado.Vale, ap_nat, eval_cero, eval_c2, eval_resta, eval_c1, eval_largo, levantar_eval,
        Fin.init_snoc, e2, e4, eX, comp_snoc_eval, eQ]
      rw [cotaB_eval]
      have c1'' : code.eval u ≤ (cotaArmar S1 T1).eval u := c1'
      rw [cotaArmar_eval] at c1''
      refine ⟨by omega, fun hx => ?_⟩
      have hx' : x ≤ Nat.size (T1.eval u) := by omega
      refine ⟨?_, fun hg => ?_⟩
      · rw [leerB_eval _ _ _ _ hx', recorte_eval, ← c2' x hx', leer_eval _ _ _ _ _ hx']
      · rw [recorte_eval]
        apply min_eq_left
        have hS1e : S1.eval u = s.eval (Fin.snoc (fun i => (Q' i).eval u) (Nat.size (T1.eval u))) := hSe _
        rw [hS1e]
        refine (Nat.sub_eq_zero_iff_le.mp hg).trans (ms _ _ fun i => Fin.lastCases ?_ (fun j => ?_) i)
        · simp only [Fin.snoc_last]; exact hx'
        · simp only [Fin.snoc_castSucc]; exact le_refl _) (Fin.snoc (pre R.ι N') x)
  have ev : ∀ x : R.M, (fun i => ap (Ql i) (Fin.snoc (pre R.ι N') x)) = z := fun x => by
    rw [← hQ']; funext i; simp only [Ql, ap_levantar]
  have eX : ∀ x : R.M, ap Xl (Fin.snoc (pre R.ι N') x) = x := fun x => ap_ultima _ _
  simp only [Enunciado.Vale, ap_cero, leM_iff, ap_levantar, hcomp2, ap_comp, ap_snoc_fun, eX, ev, hS1, hT1,
    ap_c1] at hF
  refine ⟨ap code (pre R.ι N'), ?_, (hχ z _).mpr fun x hx => (hI z _ x).mpr ?_⟩
  · unfold tPT
    rw [hcomp2]
    have := (hF (ap code (pre R.ι N'))).1
    convert this using 2
  · have hθx := (hθ x _).mp (hG0 ![x])
    rcases hθx with hn | ⟨hy, hd⟩
    · exact absurd hx hn
    · rw [← hG1] at hy hd
      have h4 := (hF x).2 hx
      have hE' : ap E (Fin.snoc (Fin.snoc z (ap code (pre R.ι N'))) x) = ap G1 (Fin.snoc (pre R.ι N') x) := by
        rw [hE]
        have e1 : (![ap S z, ap t z, ap code (pre R.ι N'), x] : Fin 4 → R.M) =
            fun i => ap ((![levantar S1, levantar T1, levantar code, Xl] : Fin 4 → Cob (N' + 1)) i)
              (Fin.snoc (pre R.ι N') x) := by
          funext i; fin_cases i <;> simp [ap_levantar, hS1, hT1, eX]
        rw [e1]; exact h4.1.trans (h4.2 hy)
      rw [hE']
      exact ⟨hy, hd⟩

end Cobham
end Sagitta.Map
