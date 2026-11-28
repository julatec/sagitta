import Sagitta.Map.SigmaUno
import Sagitta.Map.Conservacion
import Sagitta.Map.DeltaUno
import Sagitta.Map.AlfabetoFinito

/-!
# Fase D de Σᵇ₁ = NP: lo que define una fórmula `Σᵇ₁` está en NP

Fase D del plan: la vuelta, **`Σᵇ₁ ⊆ NP`** (Wrathall 1976, Kent–Hodgson 1982), sin pasar
por cslib-frontier más allá de lo que ya está compilado (las máquinas de `Clases.lean` y el puente de `TiempoCobham`).

## La ruta

1. **Representar en ℕ.** `SigmaUno.sigma_representa` (sesión R5b) da, para toda `Σᵇ₁`, programas de Cobham fijos
   `δ`, `t` con «hay testigo ⇒ φ» en todo modelo de `TC` y la otra mitad **solo en los modelos saturados**: ℕ no lo es,
   y lo que faltaba en ℕ es la colección aguda. Aquí está (`testif_paraTodo_nat`): si en cada `x ≤ |t(z)|` hay testigo,
   los testigos se guardan como los dígitos de un solo número en base `2^|s(z, |t|)|` (`sucesion_nat`, por `digito`
   de `Coleccion.lean`). Con ella, la misma inducción conjunta de `SigmaUno` da **`sigma_nat`**: en ℕ,
   `φ(z) ↔ ∃ y ≤ t(z), δ(z, y) = 0`, con `δ`, `t` programas de Cobham y `t` creciente. Es la forma normal de NP.
2. **Las máquinas.** El verificador es `V(w, c) = [δ'(numeroDe w, numeroDe c) = 0]`, donde `δ'` lee el testigo como
   `numeroDe c − 1` y comprueba la cota. Es polinomial por `Cobham.cob_polinomial` (todo programa de Cobham es de tiempo
   polinomial, la dirección difícil de Buss que ya estaba) y los puentes de `AlfabetoFinito`.
3. **El largo del certificado.** El testigo `y ≤ t(X)` cabe en `|t(X)|` bits, y `Cobham.crece` acota `|t(X)|` por un
   polinomio en `|X| = |w| + 1`.

## Lo que se prueba

* `sucesion_nat`, **`testif_paraTodo_nat`**: la colección aguda en ℕ, con los programas de `Representar.lean`.
* **`sigma_nat`**, `pi_nat`: toda `Σᵇ₁` (y la negación de toda `Πᵇ₁`) es, en ℕ, «existe `y ≤ t` con `δ = 0`».
* `numeroDe_sobre`: todo `n ≥ 1` es `numeroDe` de una cadena (de largo `|n| − 1`).
* **`sigma_en_NP`**: si una fórmula `Σᵇ₁` define `P` (en el sentido de `SigmaNP.DefinidoPor`), `P ∈ NP`.
* **`sigmaSubNP`**: la mitad `⇐` de `SigmaIgualNP` (`P ∈ NP ⇐ ∃ φ Σᵇ₁ que define P`).

## Lo que no se prueba aquí

* La otra mitad, `NP ⊆ Σᵇ₁` (fase C): pide cada problema de NP de Sagitta como una consulta de la NP de
  cslib-frontier y el teorema de Fagin ordenado de cslib-frontier, que no está compilado en esta máquina.
-/

open FirstOrder FirstOrder.Language
open Computability Turing Turing.MultiTapeTM

namespace Sagitta.Map
namespace SigmaFagin

open Cobham
open Acotada (numeroDe numeroDe_cons DefinidoPor definidoPor_not)

/-! ## La colección aguda en ℕ -/

theorem leM_nat (x y : ℕ) : LeM x y ↔ x ≤ y := by
  change x - y = 0 ↔ _
  omega

/-- **Una sucesión en un número.** En base `D`, los `m + 1` valores `g 0, …, g m` (todos `< D`) son los dígitos de
un `w < D^(m+1)`. -/
theorem sucesion_nat (D : ℕ) (hD : 0 < D) (g : ℕ → ℕ) (hg : ∀ x, g x < D) :
    ∀ m, ∃ w, w < D ^ (m + 1) ∧ ∀ x ≤ m, w / D ^ x % D = g x
  | 0 => ⟨g 0, by simpa using hg 0, fun x hx => by
      obtain rfl : x = 0 := by omega
      simp [Nat.mod_eq_of_lt (hg 0)]⟩
  | m + 1 => by
    obtain ⟨c, hc, hcx⟩ := sucesion_nat D hD g hg m
    refine ⟨c + g (m + 1) * D ^ (m + 1), ?_, fun x hx => ?_⟩
    · have := hg (m + 1)
      rw [Nat.pow_succ D (m + 1)]
      nlinarith
    · rw [digito D (m + 1) c _ x hD hc (hg _) hx]
      split
      · rename_i h; rw [h]
      · exact hcx x (by omega)

theorem zsP_eval {A : ℕ} (z : Fin A → ℕ) (w x : ℕ) :
    (fun i => (zsP A i).eval (Fin.snoc (Fin.snoc z w) x : Fin (A + 2) → ℕ)) = z := by
  funext i; simp [zsP, Fin.snoc_castSucc]

theorem pS_eval {A : ℕ} (s : Cob (A + 1)) (t : Cob A) (z : Fin A → ℕ) :
    (pS s t).eval z = s.eval (Fin.snoc z (Nat.size (t.eval z))) := by
  rw [pS, enPunto_eval]; rfl

theorem pE_eval {A : ℕ} (s : Cob (A + 1)) (t : Cob A) (z : Fin A → ℕ) (w x : ℕ) (hx : x ≤ Nat.size (t.eval z)) :
    (pE s t).eval (Fin.snoc (Fin.snoc z w) x) =
      w / (2 ^ Nat.size ((pS s t).eval z)) ^ x % 2 ^ Nat.size ((pS s t).eval z) := by
  have e : (fun i => ((![(pS s t).comp (zsP A), t.comp (zsP A), wP A, xP A] : Fin 4 → Cob (A + 2)) i).eval
      (Fin.snoc (Fin.snoc z w) x)) = ![(pS s t).eval z, t.eval z, w, x] := by
    funext i; fin_cases i
    · change (pS s t).eval (fun j => (zsP A j).eval _) = _; rw [zsP_eval]; rfl
    · change t.eval (fun j => (zsP A j).eval _) = _; rw [zsP_eval]; rfl
    · simp [wP, Fin.snoc_castSucc, Fin.snoc_last]
    · simp [xP, Fin.snoc_last]
  change leerB.eval _ = _
  rw [e, leerB_eval _ _ _ _ hx]

theorem tPT_eval {A : ℕ} (s : Cob (A + 1)) (t : Cob A) (z : Fin A → ℕ) :
    (tPT s t).eval z = (2 ^ Nat.size ((pS s t).eval z)) ^ (Nat.size (t.eval z) + 1) := by
  have e : (fun i => ((![pS s t, t] : Fin 2 → Cob A) i).eval z) = ![(pS s t).eval z, t.eval z] := by
    funext i; fin_cases i <;> rfl
  simp only [tPT, Cob.eval]
  rw [e, cotaB_eval]

/-- **La colección aguda en ℕ**: si en cada `x ≤ |t(z)|` hay testigo, hay uno solo para todos (la sucesión de los
testigos, como dígitos). Es la mitad de `Representar.testif_paraTodo_completo` que en ℕ no pedía saturación. -/
theorem testif_paraTodo_nat {A : ℕ} (δ : Cob (A + 1 + 1)) (s : Cob (A + 1)) (ms : Mono s) (t : Cob A)
    (z : Fin A → ℕ) (hall : ∀ x, LeM x (ap Cob.largo ![ap t z]) → Testif δ s (Fin.snoc z x)) :
    Testif (pPT δ s t) (tPT s t) z := by
  classical
  set m := Nat.size (t.eval z) with hm
  set S := (pS s t).eval z with hS
  set D := 2 ^ Nat.size S with hD
  have hall' : ∀ x, x ≤ m → ∃ y, y ≤ s.eval (Fin.snoc z x) ∧ δ.eval (Fin.snoc (Fin.snoc z x) y) = 0 :=
    fun x hx => by
      obtain ⟨y, hy, hd⟩ := hall x ((leM_nat _ _).2 hx)
      exact ⟨y, (leM_nat _ _).1 hy, hd⟩
  let g : ℕ → ℕ := fun x => if h : x ≤ m then Classical.choose (hall' x h) else 0
  have hgs : ∀ x (h : x ≤ m), g x ≤ s.eval (Fin.snoc z x) ∧ δ.eval (Fin.snoc (Fin.snoc z x) (g x)) = 0 :=
    fun x h => by simp only [g, h, ↓reduceDIte]; exact Classical.choose_spec (hall' x h)
  have hsS : ∀ x, x ≤ m → s.eval (Fin.snoc z x) ≤ S := fun x hx => by
    rw [hS, pS_eval]
    refine ms _ _ fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact hx
    · simp only [Fin.snoc_castSucc]; exact le_refl _
  have hgD : ∀ x, g x < D := fun x => by
    by_cases h : x ≤ m
    · exact lt_of_le_of_lt ((hgs x h).1.trans (hsS x h)) (Nat.lt_size_self S)
    · simp only [g, h, ↓reduceDIte]; exact Nat.two_pow_pos _
  obtain ⟨w, hw, hdig⟩ := sucesion_nat D (Nat.two_pow_pos _) g hgD m
  refine ⟨w, ?_, ?_⟩
  · rw [ap_nat, leM_nat, tPT_eval]; exact hw.le
  · rw [ap_pPT]
    intro x hx
    rw [ap_nat, ap_nat, leM_nat, eval_largo] at hx
    rw [ap_pI]
    simp only [ap_nat, leM_nat]
    rw [pE_eval s t z w x hx, ← hD, hdig x hx]
    exact hgs x hx

/-! ## Representar en ℕ -/

/-- **`δ` y `t` representan `P` en ℕ**: `P z ↔ ∃ y ≤ t(z), δ(z, y) = 0`, con `t` creciente. -/
def RepN {A : ℕ} (P : (Fin A → ℕ) → Prop) (δ : Cob (A + 1)) (t : Cob A) : Prop :=
  Mono t ∧ ∀ z, P z ↔ Testif δ t z

theorem repN_congr {A : ℕ} {P Q : (Fin A → ℕ) → Prop} {δ : Cob (A + 1)} {t : Cob A} (h : RepN P δ t)
    (hPQ : ∀ z, P z ↔ Q z) : RepN Q δ t :=
  ⟨h.1, fun z => (hPQ z).symm.trans (h.2 z)⟩

theorem repN_prog {A : ℕ} {P : (Fin A → ℕ) → Prop} (χ : Cob A) (h : ∀ z, P z ↔ ap χ z = cero0 ℕ) :
    RepN P (levantar χ) .cero :=
  ⟨fun _ _ _ => le_refl _, fun z => (h z).trans (testif_prog χ z).symm⟩

theorem repN_o {A : ℕ} {P Q : (Fin A → ℕ) → Prop} {δ₁ δ₂ : Cob (A + 1)} {t₁ t₂ : Cob A}
    (h₁ : RepN P δ₁ t₁) (h₂ : RepN Q δ₂ t₂) :
    RepN (fun z => P z ∨ Q z) (pO δ₁ t₁ δ₂ t₂) (c2 .suma t₁ t₂) :=
  ⟨mono_suma h₁.1 h₂.1, fun z => (or_congr (h₁.2 z) (h₂.2 z)).trans (testif_o δ₁ t₁ δ₂ t₂ z).symm⟩

theorem repN_y {A : ℕ} {P Q : (Fin A → ℕ) → Prop} {δ₁ δ₂ : Cob (A + 1)} {t₁ t₂ : Cob A}
    (h₁ : RepN P δ₁ t₁) (h₂ : RepN Q δ₂ t₂) :
    RepN (fun z => P z ∧ Q z) (pEx (pY (pLev δ₂) δ₁) (levantar t₂) t₁) (tEx (levantar t₂) t₁) :=
  ⟨mono_tEx (mono_levantar h₂.1) h₁.1,
    fun z => (and_congr (h₁.2 z) (h₂.2 z)).trans (testif_y2 δ₁ t₁ δ₂ t₂ h₂.1 z).symm⟩

theorem repN_existe {A : ℕ} {P : (Fin (A + 1) → ℕ) → Prop} {δ : Cob (A + 1 + 1)} {s : Cob (A + 1)}
    (h : RepN P δ s) (t : Cob A) (mt : Mono t) :
    RepN (fun z => ∃ x, LeM x (ap t z) ∧ P (Fin.snoc z x)) (pEx δ s t) (tEx s t) :=
  ⟨mono_tEx h.1 mt, fun z => by
    rw [testif_existe δ s h.1 t z]
    exact exists_congr fun x => and_congr Iff.rfl (h.2 _)⟩

theorem repN_paraTodo {A : ℕ} {P : (Fin (A + 1) → ℕ) → Prop} {δ : Cob (A + 1 + 1)} {s : Cob (A + 1)}
    (h : RepN P δ s) (t : Cob A) (mt : Mono t) :
    RepN (fun z => ∀ x, LeM x (ap Cob.largo ![ap t z]) → P (Fin.snoc z x)) (pPT δ s t) (tPT s t) :=
  ⟨mono_tPT h.1 mt, fun z =>
    ⟨fun hz => testif_paraTodo_nat δ s h.1 t z fun x hx => (h.2 _).1 (hz x hx),
      fun hz x hx => (h.2 _).2 (testif_paraTodo_sano δ s t z hz x hx)⟩⟩

mutual

/-- **Toda fórmula `Σᵇ₁` es, en ℕ, «existe `y ≤ t` con `δ = 0`»**, con programas de Cobham. -/
theorem sigma_nat {a : ℕ} : ∀ {n : ℕ} {φ : LB.BoundedFormula (Fin a) n}, Acotada.EsSigma1 φ →
    ∃ (δ : Cob (a + n + 1)) (t : Cob (a + n)), RepN (fun z => Val (M := ℕ) φ z) δ t
  | _, _, .aguda h => by
      obtain ⟨χ, hχ⟩ := aguda_unif h
      exact ⟨_, _, repN_prog χ (hχ ℕ)⟩
  | _, _, .existe t h => by
      obtain ⟨δ, s, hr⟩ := sigma_nat h
      exact ⟨_, _, repN_congr (repN_existe hr (trT id t) (trT_mono id t)) fun z => (val_existe t _ z).symm⟩
  | _, _, .todoAgudo t h => by
      obtain ⟨δ, s, hr⟩ := sigma_nat h
      exact ⟨_, _, repN_congr (repN_paraTodo hr (trT id t) (trT_mono id t)) fun z => by
        rw [val_paraTodo, trT_tLong]⟩
  | _, _, .y h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := sigma_nat h₁
      obtain ⟨δ₂, t₂, r₂⟩ := sigma_nat h₂
      exact ⟨_, _, repN_congr (repN_y r₁ r₂) fun z => (val_inf _ _ z).symm⟩
  | _, _, .o h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := sigma_nat h₁
      obtain ⟨δ₂, t₂, r₂⟩ := sigma_nat h₂
      exact ⟨_, _, repN_congr (repN_o r₁ r₂) fun z => (val_sup _ _ z).symm⟩
  | _, _, .no h => by
      obtain ⟨δ, t, r⟩ := pi_nat h
      exact ⟨_, _, repN_congr r fun z => (val_not _ z).symm⟩
  | _, _, .imp h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := pi_nat h₁
      obtain ⟨δ₂, t₂, r₂⟩ := sigma_nat h₂
      exact ⟨_, _, repN_congr (repN_o r₁ r₂) fun z => by
        rw [val_imp]; exact ⟨fun h => h.elim (fun h' h'' => absurd h'' h') (fun h' _ => h'),
          fun h => (Classical.em _).elim (fun h' => .inr (h h')) .inl⟩⟩

/-- **La negación de toda fórmula `Πᵇ₁` es, en ℕ, «existe `y ≤ t` con `δ = 0`».** -/
theorem pi_nat {a : ℕ} : ∀ {n : ℕ} {φ : LB.BoundedFormula (Fin a) n}, Acotada.EsPi1 φ →
    ∃ (δ : Cob (a + n + 1)) (t : Cob (a + n)), RepN (fun z => ¬ Val (M := ℕ) φ z) δ t
  | _, _, .aguda h => by
      obtain ⟨χ, hχ⟩ := aguda_unif h
      exact ⟨_, _, repN_prog (no χ) fun z => by rw [hχ ℕ z, ap_no]⟩
  | _, _, .todo t h => by
      obtain ⟨δ, s, hr⟩ := pi_nat h
      exact ⟨_, _, repN_congr (repN_existe hr (trT id t) (trT_mono id t)) fun z => by
        rw [val_paraTodo]; push Not; rfl⟩
  | _, _, .existeAgudo t h => by
      obtain ⟨δ, s, hr⟩ := pi_nat h
      exact ⟨_, _, repN_congr (repN_paraTodo hr (trT id t) (trT_mono id t)) fun z => by
        rw [val_existe, trT_tLong]; push Not; rfl⟩
  | _, _, .y h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := pi_nat h₁
      obtain ⟨δ₂, t₂, r₂⟩ := pi_nat h₂
      exact ⟨_, _, repN_congr (repN_o r₁ r₂) fun z => by rw [val_inf]; tauto⟩
  | _, _, .o h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := pi_nat h₁
      obtain ⟨δ₂, t₂, r₂⟩ := pi_nat h₂
      exact ⟨_, _, repN_congr (repN_y r₁ r₂) fun z => by rw [val_sup]; tauto⟩
  | _, _, .no h => by
      obtain ⟨δ, t, r⟩ := sigma_nat h
      exact ⟨_, _, repN_congr r fun z => by rw [val_not, not_not]⟩
  | _, _, .imp h₁ h₂ => by
      obtain ⟨δ₁, t₁, r₁⟩ := sigma_nat h₁
      obtain ⟨δ₂, t₂, r₂⟩ := pi_nat h₂
      exact ⟨_, _, repN_congr (repN_y r₁ r₂) fun z => by rw [val_imp]; tauto⟩

end

/-- **La forma normal de NP, en ℕ.** Para toda fórmula `Σᵇ₁` con una variable libre hay programas de Cobham `δ`
(de dos argumentos) y `t` (de uno, creciente) con `φ(X) ↔ ∃ y ≤ t(X), δ(X, y) = 0`. -/
theorem forma_normal {φ : LB.Formula (Fin 1)} (hφ : Acotada.EsSigma1 φ) :
    ∃ (δ : Cob 2) (t : Cob 1), Mono t ∧
      ∀ X : ℕ, φ.Realize ![X] ↔ ∃ y, y ≤ t.eval ![X] ∧ δ.eval ![X, y] = 0 := by
  obtain ⟨δ, t, ht, h⟩ := sigma_nat (a := 1) (n := 0) hφ
  refine ⟨δ, t, ht, fun X => ?_⟩
  have e1 : φ.Realize ![X] ↔ Testif δ t ![X] := by
    have h1 : Val (M := ℕ) φ ![X] ↔ Testif δ t ![X] := h ![X]
    rw [val_formula] at h1
    unfold Formula.Realize at h1 ⊢
    rwa [realize_nat_buss] at h1
  rw [e1, Testif]
  refine exists_congr fun y => and_congr (leM_nat _ _) ?_
  have e : (Fin.snoc ![X] y : Fin 2 → ℕ) = ![X, y] := by funext i; fin_cases i <;> rfl
  rw [ap_nat, e]; rfl

/-! ## Cadenas y números -/

/-- `|numeroDe w| = |w| + 1`. -/
theorem size_numeroDe (w : List Bool) : Nat.size (numeroDe w) = w.length + 1 := by
  rw [← Nat.size_eq_bits_len, DeltaUno.cod_numeroDe, List.length_append, List.length_singleton]

/-- **Todo `n ≥ 1` es `numeroDe` de una cadena.** -/
theorem numeroDe_sobre : ∀ n : ℕ, 1 ≤ n → ∃ c : List Bool, numeroDe c = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  by_cases h1 : n = 1
  · exact ⟨[], by simp [h1]⟩
  · obtain ⟨c, hc⟩ := ih (n / 2) (by omega) (by omega)
    refine ⟨decide (n % 2 = 1) :: c, ?_⟩
    rw [numeroDe_cons, hc]
    by_cases h : n % 2 = 1 <;> simp [h] <;> omega

/-! ## El verificador -/

/-- El verificador como programa: sobre `(X, u)`, da 0 justo cuando `u − 1 ≤ t(X)` y `δ(X, u − 1) = 0`. El testigo
`y` viaja como la cadena `c` con `numeroDe c = y + 1`. -/
def verifCob (δ : Cob 2) (t : Cob 1) : Cob 2 :=
  yy (c2 .resta (c2 .resta (.proy 1) uno) (t.comp ![.proy 0])) (δ.comp ![.proy 0, c2 .resta (.proy 1) uno])

theorem verifCob_eval (δ : Cob 2) (t : Cob 1) (X u : ℕ) :
    (verifCob δ t).eval ![X, u] = 0 ↔ u - 1 ≤ t.eval ![X] ∧ δ.eval ![X, u - 1] = 0 := by
  have e1 : (t.comp ![.proy 0]).eval ![X, u] = t.eval ![X] := by
    simp only [Cob.eval]; congr 1; funext i; fin_cases i; rfl
  have e2 : (δ.comp ![.proy 0, c2 .resta (.proy 1) uno]).eval ![X, u] = δ.eval ![X, u - 1] := by
    simp only [Cob.eval]; congr 1; funext i; fin_cases i <;> rfl
  have e : (verifCob δ t).eval ![X, u] = (u - 1 - t.eval ![X]) + δ.eval ![X, u - 1] := by
    rw [← e1, ← e2]; rfl
  rw [e]
  omega

theorem incrustar_nat : AlfabetoFinito.incrustar (CodBits.toEncoding (α := ℕ)) = encNat :=
  Function.Embedding.ext fun n => congrFun Cobham.cod_nat_eq n

/-- **El verificador es polinomial**, en el sentido de cslib-frontier. -/
theorem verif_polinomial (χ : Cob 2) :
    ComputableInPolyTime (fun q : List Bool × List Bool => decide (χ.eval ![numeroDe q.1, numeroDe q.2] ≤ 0))
      (encPair encBits encBits) encBool := by
  have hN : ComputableInPolyTime numeroDe encBits encNat := by
    have := AlfabetoFinito.esPolinomial_iff.mp DeltaUno.esPolinomial_numeroDe
    rwa [AlfabetoFinito.incrustar_bits, incrustar_nat] at this
  have hZ : ComputableInPolyTime (fun n : ℕ => decide (n ≤ 0)) encNat encBool := by
    have := AlfabetoFinito.esPolinomial_iff.mp DeltaUno.esPolinomial_esCero
    rwa [incrustar_nat, AlfabetoFinito.incrustar_bool] at this
  have hv : ComputableInPolyTime (fun q : List Bool × List Bool => ![numeroDe q.1, numeroDe q.2])
      (encPair encBits encBits) (encPi encNat) := ComputableInPolyTime.pi fun i => by
    fin_cases i
    · exact hN.comp (ComputableInPolyTime.fst encBits encBits)
    · exact hN.comp (ComputableInPolyTime.snd encBits encBits)
  exact hZ.comp ((Cobham.cob_polinomial χ).comp hv)

/-! ## Σᵇ₁ ⊆ NP -/

/-- **Lo que define una fórmula `Σᵇ₁` está en NP** (Wrathall 1976; Kent–Hodgson 1982). -/
theorem sigma_en_NP {φ : LB.Formula (Fin 1)} (hφ : Acotada.EsSigma1 φ) {P : Problema} (hP : DefinidoPor φ P) :
    P ∈ NP := by
  obtain ⟨δ, t, -, ht⟩ := forma_normal hφ
  obtain ⟨B, ⟨⟨q, hq⟩, -⟩, hB⟩ := Cobham.crece t
  let V : List Bool × List Bool → Bool :=
    fun r => decide ((verifCob δ t).eval ![numeroDe r.1, numeroDe r.2] ≤ 0)
  have hVt : ∀ w c, V (w, c) = true ↔ numeroDe c - 1 ≤ t.eval ![numeroDe w] ∧
      δ.eval ![numeroDe w, numeroDe c - 1] = 0 := fun w c => by
    simp only [V, decide_eq_true_eq, Nat.le_zero]
    exact verifCob_eval δ t _ _
  refine ⟨q.comp (Polynomial.X + 1) + 1, V, ?_, fun w => ?_⟩
  · rw [AlfabetoFinito.esPolinomial_iff, AlfabetoFinito.incrustar_par, AlfabetoFinito.incrustar_bool]
    exact verif_polinomial (verifCob δ t)
  rw [hP w, ht]
  constructor
  · rintro ⟨y, hy, hd⟩
    obtain ⟨c, hc⟩ := numeroDe_sobre (y + 1) (by omega)
    refine ⟨c, ?_, (hVt w c).2 ⟨by omega, by rw [hc, Nat.add_sub_cancel]; exact hd⟩⟩
    have h1 : c.length + 1 ≤ Nat.size (t.eval ![numeroDe w]) + 1 := by
      rw [← size_numeroDe, hc]
      exact (Nat.size_le_size (Nat.succ_le_succ hy)).trans (Cobham.size_succ_le _)
    have h2 : Nat.size (t.eval ![numeroDe w]) ≤ B (w.length + 1) :=
      hB _ _ fun i => by fin_cases i; exact (size_numeroDe w).le
    have h3 := hq (w.length + 1)
    simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_one]
    omega
  · rintro ⟨c, -, hV⟩
    exact ⟨_, ((hVt w c).1 hV).1, ((hVt w c).1 hV).2⟩

/-- **`Σᵇ₁ ⊆ NP`**: la mitad `⇐` de `SigmaNP.SigmaIgualNP`. -/
theorem sigmaSubNP (P : Problema) (h : ∃ φ : LB.Formula (Fin 1), Acotada.EsSigma1 φ ∧ DefinidoPor φ P) : P ∈ NP :=
  let ⟨_, hφ, hP⟩ := h
  sigma_en_NP hφ hP

/-- Y por dualidad, `Πᵇ₁ ⊆ coNP`. -/
theorem piSubCoNP (P : Problema) (h : ∃ φ : LB.Formula (Fin 1), Acotada.EsPi1 φ ∧ DefinidoPor φ P) : P ∈ coNP := by
  obtain ⟨φ, hφ, hP⟩ := h
  exact sigma_en_NP (Acotada.EsSigma1.no hφ) (definidoPor_not hP)

/-- **Lo que queda de Wrathall–Stockmeyer es una sola dirección**: `SigmaIgualNP` equivale a `NP ⊆ Σᵇ₁`. -/
theorem sigmaIgualNP_iff : Acotada.SigmaIgualNP ↔
    ∀ P ∈ NP, ∃ φ : LB.Formula (Fin 1), Acotada.EsSigma1 φ ∧ DefinidoPor φ P :=
  ⟨fun h P hP => (h P).1 hP, fun h P => ⟨h P, sigmaSubNP P⟩⟩

/-! ## Controles -/

example : (verifCob .cero .cero).eval ![5, 1] = 0 := by decide
example : (verifCob .cero .cero).eval ![5, 2] ≠ 0 := by decide

/-! Mutantes (probados fuera del repositorio, 25 nov 2026, continuación):

* `sucesion_nat` con la cota `w < D^m` en lugar de `D^(m+1)`: Lean rechaza el caso `m = 0` (habría que guardar
  `g 0 < D` en un `w < 1`), y con él `testif_paraTodo_nat`. Es falso: `m + 1` testigos piden `m + 1` dígitos.
* `sigma_en_NP` con el polinomio `q` en lugar de `q ∘ (X + 1) + 1`: `omega` no cierra la cota del largo del
  certificado (da un contraejemplo). La cota de `crece` es en `|X| = |w| + 1`, no en `|w|`. -/

end SigmaFagin
end Sagitta.Map
