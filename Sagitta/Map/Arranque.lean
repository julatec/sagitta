import Sagitta.Map.Parikh
import Sagitta.Map.Landau
import Sagitta.Map.T12
import Mathlib.Data.Nat.Size

/-!
# El arranque de S¹₂, parte 1: los largos

Buss (1986, cap. 2) «arranca» S¹₂: define dentro de la teoría funciones que el lenguaje no tiene (resta, los bits
altos de un número, `2ᵘ`) y prueba con su inducción que se portan bien. Es la base de las inclusiones entre T¹₂ y
S¹₂, de la reducción de Cook dentro de S¹₂ y de la dirección fácil del teorema de Buss. Este archivo es la primera
pieza.

**La observación de partida** (José, 23 nov 2026): las operaciones son monótonas en el **valor**, pero lo que cuenta
para el tiempo es el **largo en bits**, `|x| = log₂ x` más o menos. Medidas en bits, crecen mucho menos:

| operación | su largo |
|---|---|
| sucesor, suma | `|x + y| ≤ máx(|x|, |y|) + 1`: suma una constante |
| mitad | `|⌊x/2⌋| = |x| - 1` |
| producto | `|x · y| ≤ |x| + |y|`: los largos se suman |
| smash | `|x # y| = |x| · |y| + 1`: los largos se multiplican |
| largo | `||x|| ≤ |x|` |

Medida en bits, cada operación baja una capa de la cebolla de `Jerarquia.lean`. El smash es la única que multiplica
largos: por eso está en el lenguaje, y por eso **todo término tiene largo polinomial en el largo de sus variables**
(`largo_termino`). Es el contenido de «el segmento de Parikh es la parte polinomial del modelo».

## Qué hay

* La tabla, en ℕ (`size_suma`, `size_prod`, `size_smash`, `size_mitad_le`, `size_long_le`, `size_suc`).
* `largo_termino`: para cada término `t` hay un `p ∈ Pol` con `|t(v)| ≤ p(m)` si las variables miden a lo sumo `m`.

## Hecho también

* `lind`: la inducción sobre el largo, desde PIND (parte 3).
* El reetiquetado conserva las clases (parte 2a), y `pind_pi`: PIND para `Πᵇ₁` (parte 4), sin bits altos.

## Lo que queda para las partes siguientes (anotado también en `README.md`)

* La tabla en todo modelo de S¹₂ (el smash y la mitad salen de BASIC 13 y 31; la suma y el producto piden inducción).
* La resta, los bits altos `⌊a / 2ᵘ⌋` y `2ᵘ` para `u ≤ |a|`, con definiciones `Σᵇ₁` que S¹₂ demuestra totales.
* Encima: `S12ContieneT02` y `T12ContieneS12`.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada
namespace Arranque

open Tiempo Parikh

/-! ## La tabla de largos, en ℕ -/

theorem size_le_iff_lt {x k : ℕ} : Nat.size x ≤ k ↔ x < 2 ^ k := Nat.size_le

theorem lt_pow_size (x : ℕ) : x < 2 ^ Nat.size x := Nat.lt_size_self x

/-- **La suma agrega a lo sumo un bit.** -/
theorem size_suma (x y : ℕ) : Nat.size (x + y) ≤ max (Nat.size x) (Nat.size y) + 1 := by
  rw [Nat.size_le]
  have hx : x < 2 ^ max (Nat.size x) (Nat.size y) :=
    (lt_pow_size x).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hy : y < 2 ^ max (Nat.size x) (Nat.size y) :=
    (lt_pow_size y).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  rw [pow_succ]; omega

/-- **El sucesor agrega a lo sumo un bit.** -/
theorem size_suc (x : ℕ) : Nat.size (x + 1) ≤ Nat.size x + 1 := by
  rw [Nat.size_le, pow_succ]
  have := lt_pow_size x
  have : 1 ≤ 2 ^ Nat.size x := Nat.one_le_two_pow
  omega

/-- **El producto suma los largos.** -/
theorem size_prod (x y : ℕ) : Nat.size (x * y) ≤ Nat.size x + Nat.size y := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (lt_pow_size x) (lt_pow_size y)

/-- **El smash multiplica los largos.** -/
theorem size_smash (x y : ℕ) : Nat.size (2 ^ (Nat.size x * Nat.size y)) = Nat.size x * Nat.size y + 1 :=
  Nat.size_pow

/-- **La mitad quita un bit.** -/
theorem size_mitad_le (x : ℕ) : Nat.size (x / 2) ≤ Nat.size x :=
  Nat.size_le_size (Nat.div_le_self x 2)

/-- **El largo del largo no pasa del largo.** -/
theorem size_long_le (x : ℕ) : Nat.size (Nat.size x) ≤ Nat.size x :=
  Nat.size_le.mpr (Nat.size x).lt_two_pow_self

/-! ## Todo término tiene largo polinomial -/

/-- **El largo de un término es polinomial en el largo de sus variables.** Para cada término `t` hay un `p ∈ Pol`
tal que, si todas las variables miden a lo sumo `m` bits, `t` mide a lo sumo `p(m)`. -/
theorem largo_termino {α : Type} (t : L.Term α) :
    ∃ p ∈ Pol, ∀ (m : ℕ) (v : α → ℕ), (∀ a, Nat.size (v a) ≤ m) → Nat.size (t.realize v) ≤ p m := by
  induction t with
  | var a => exact ⟨fun m => m, pol_id, fun m v hv => hv a⟩
  | func f ts ih =>
    choose p hp hb using ih
    cases f with
    | cero => exact ⟨fun _ => 0, pol_const 0, fun m v _ => by
        show Nat.size (0 : ℕ) ≤ 0; simp⟩
    | suc => exact ⟨fun m => p 0 m + 1, pol_add (hp 0) (pol_const 1), fun m v hv =>
        (size_suc _).trans (Nat.add_le_add_right (hb 0 m v hv) 1)⟩
    | long => exact ⟨p 0, hp 0, fun m v hv => (size_long_le _).trans (hb 0 m v hv)⟩
    | mitad => exact ⟨p 0, hp 0, fun m v hv => (size_mitad_le _).trans (hb 0 m v hv)⟩
    | suma => exact ⟨fun m => p 0 m + p 1 m + 1, pol_add (pol_add (hp 0) (hp 1)) (pol_const 1), fun m v hv => by
        refine (size_suma _ _).trans ?_
        beta_reduce
        have h0 := hb 0 m v hv; have h1 := hb 1 m v hv
        have : max (Nat.size ((ts 0).realize v)) (Nat.size ((ts 1).realize v)) ≤ p 0 m + p 1 m := by omega
        omega⟩
    | prod => exact ⟨fun m => p 0 m + p 1 m, pol_add (hp 0) (hp 1), fun m v hv =>
        (size_prod _ _).trans (Nat.add_le_add (hb 0 m v hv) (hb 1 m v hv))⟩
    | smash => exact ⟨fun m => p 0 m * p 1 m + 1, pol_add (pol_mul (hp 0) (hp 1)) (pol_const 1), fun m v hv => by
        show Nat.size (2 ^ (Nat.size ((ts 0).realize v) * Nat.size ((ts 1).realize v))) ≤ _
        rw [size_smash]
        exact Nat.add_le_add_right (Nat.mul_le_mul (hb 0 m v hv) (hb 1 m v hv)) 1⟩


/-! ## Parte 3: la inducción sobre el largo (LIND) -/

/-- **LIND desde PIND.** En todo modelo de S¹₂, si `φ` es `Σᵇ₁`, `φ(0)` y `φ(x) → φ(Sx)`, entonces `φ(|a|)` para todo
`a`. Se aplica PIND a `φ(|z|)`: `|0| = 0` (BASIC 9) y `|z| = S|⌊z/2⌋|` si `z ≠ 0` (BASIC 31). -/
theorem lind {M : Type} [L.Structure M] (hM : EsModeloS12 M) (k : ℕ) (φ : L.Formula (Fin (k + 1)))
    (hφ : EsSigma1 φ) (v : Fin k → M) (h0 : φ.Realize (Fin.cons cero v))
    (hs : ∀ x : M, φ.Realize (Fin.cons x v) → φ.Realize (Fin.cons (suc x) v)) (a : M) :
    φ.Realize (Fin.cons (long a) v) := by
  have h := hM.basic
  let ψ : L.Formula (Fin (k + 1)) :=
    φ.subst (Fin.cons (α := fun _ => L.Term (Fin (k + 1))) (tLg (Term.var 0)) (fun i => Term.var i.succ))
  have hψ : EsSigma1 ψ := hφ.subst _
  have hr : ∀ z : M, ψ.Realize (Fin.cons z v) ↔ φ.Realize (Fin.cons (long z) v) := by
    intro z
    simp only [ψ, formula_realize_subst]
    apply iff_of_eq; congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, tLg, Term.realize_functions_apply₁, Term.realize_var]; rfl
    · simp only [Fin.cons_succ, Term.realize_var]
  refine (hr a).1 (hM.pind k ψ hψ v ((hr cero).2 (by rw [h.b9]; exact h0)) (fun z hz => ?_) a)
  rw [hr] at hz ⊢
  by_cases hz0 : z = cero
  · subst hz0; rw [h.b9]; exact h0
  · rw [h.b31 z hz0]; exact hs _ hz


/-! ## Parte 2a: reetiquetar conserva las clases

Para meter una fórmula bajo un cuantificador acotado (lo que piden la inducción por mitades para `Πᵇ₁` y las
inclusiones) hay que mandar sus variables libres a variables ligadas: `BoundedFormula.relabel` de Mathlib. Aquí,
que eso no saca a una fórmula de `Σᵇ₁`, `Πᵇ₁` ni de las agudas. -/

section Reetiquetar

open BoundedFormula

variable {α β : Type} {n : ℕ} (g : α → β ⊕ Fin n)

theorem relabel_nueva (k : ℕ) :
    (nueva : L.Term (α ⊕ Fin (k + 1))).relabel (relabelAux g (k + 1)) = (nueva : L.Term (β ⊕ Fin (n + k + 1))) := by
  simp only [nueva, Term.relabel, relabelAux, Function.comp_apply, Sum.map_inr, id,
    Equiv.sumAssoc_apply_inr, finSumFinEquiv_apply_right, Fin.natAdd_last]

theorem relabel_sube {k : ℕ} (t : L.Term (α ⊕ Fin k)) :
    (sube t).relabel (relabelAux g (k + 1)) = sube (t.relabel (relabelAux g k)) := by
  rw [sube, sube, Term.relabel_relabel, Term.relabel_relabel]
  congr 1
  funext x
  rcases x with a | i
  · rcases h : g a with b | j
    · simp [relabelAux, h]
    · simp only [Function.comp_apply, relabelAux, Sum.map_inl, h, Equiv.sumAssoc_apply_inl_inr, Sum.map_inr,
        id, finSumFinEquiv_apply_left]
      congr 1
  · simp only [Function.comp_apply, Sum.map_inr, relabelAux, id, Equiv.sumAssoc_apply_inr,
      finSumFinEquiv_apply_right]
    congr 1

theorem relabel_tLong {γ δ : Type} (f : γ → δ) (t : L.Term γ) : (tLong t).relabel f = tLong (t.relabel f) := by
  show Term.func _ _ = Term.func _ _
  congr 1; funext i; match i with | 0 => rfl

theorem relabel_leF {k : ℕ} (t u : L.Term (α ⊕ Fin k)) :
    (leF t u).relabel g = leF (t.relabel (relabelAux g k)) (u.relabel (relabelAux g k)) := by
  show BoundedFormula.rel _ _ = BoundedFormula.rel _ _
  congr 1; funext i; match i with | 0 => rfl | 1 => rfl

theorem relabel_inf {k : ℕ} (φ ψ : L.BoundedFormula α k) : (φ ⊓ ψ).relabel g = φ.relabel g ⊓ ψ.relabel g := by
  show ((φ.imp ψ.not).not).relabel g = ((φ.relabel g).imp (ψ.relabel g).not).not
  simp only [relabel_not, relabel_imp]

theorem relabel_sup {k : ℕ} (φ ψ : L.BoundedFormula α k) : (φ ⊔ ψ).relabel g = φ.relabel g ⊔ ψ.relabel g := by
  show (φ.not.imp ψ).relabel g = (φ.relabel g).not.imp (ψ.relabel g)
  simp only [relabel_not, relabel_imp]

theorem relabel_paraTodo {k : ℕ} (t : L.Term (α ⊕ Fin k)) (φ : L.BoundedFormula α (k + 1)) :
    (paraTodoAcotado t φ).relabel g = paraTodoAcotado (t.relabel (relabelAux g k)) (φ.relabel g) := by
  rw [paraTodoAcotado, relabel_all, relabel_imp, relabel_leF, relabel_nueva, relabel_sube]
  rfl

theorem relabel_existe {k : ℕ} (t : L.Term (α ⊕ Fin k)) (φ : L.BoundedFormula α (k + 1)) :
    (existeAcotado t φ).relabel g = existeAcotado (t.relabel (relabelAux g k)) (φ.relabel g) := by
  rw [existeAcotado, relabel_ex, relabel_inf, relabel_leF, relabel_nueva, relabel_sube]
  rfl

theorem EsAguda.relabel {k : ℕ} {φ : L.BoundedFormula α k} (hφ : EsAguda φ) : EsAguda (φ.relabel g) := by
  induction hφ with
  | falso => exact .falso
  | igual t u => exact .igual _ _
  | rel R ts => exact .rel _ _
  | imp _ _ ih1 ih2 => rw [relabel_imp]; exact .imp ih1 ih2
  | todoAgudo t _ ih => rw [relabel_paraTodo, relabel_tLong]; exact .todoAgudo _ ih
  | existeAgudo t _ ih => rw [relabel_existe, relabel_tLong]; exact .existeAgudo _ ih

mutual

theorem EsSigma1.relabel : ∀ {k : ℕ} {φ : L.BoundedFormula α k}, EsSigma1 φ → EsSigma1 (φ.relabel g)
  | _, _, .aguda h => .aguda (EsAguda.relabel g h)
  | _, _, .existe t h => by rw [relabel_existe]; exact .existe _ (EsSigma1.relabel h)
  | _, _, .todoAgudo t h => by rw [relabel_paraTodo, relabel_tLong]; exact .todoAgudo _ (EsSigma1.relabel h)
  | _, _, .y h1 h2 => by rw [relabel_inf]; exact .y (EsSigma1.relabel h1) (EsSigma1.relabel h2)
  | _, _, .o h1 h2 => by rw [relabel_sup]; exact .o (EsSigma1.relabel h1) (EsSigma1.relabel h2)
  | _, _, .no h => by rw [relabel_not]; exact .no (EsPi1.relabel h)
  | _, _, .imp h1 h2 => by rw [relabel_imp]; exact .imp (EsPi1.relabel h1) (EsSigma1.relabel h2)

theorem EsPi1.relabel : ∀ {k : ℕ} {φ : L.BoundedFormula α k}, EsPi1 φ → EsPi1 (φ.relabel g)
  | _, _, .aguda h => .aguda (EsAguda.relabel g h)
  | _, _, .todo t h => by rw [relabel_paraTodo]; exact .todo _ (EsPi1.relabel h)
  | _, _, .existeAgudo t h => by rw [relabel_existe, relabel_tLong]; exact .existeAgudo _ (EsPi1.relabel h)
  | _, _, .y h1 h2 => by rw [relabel_inf]; exact .y (EsPi1.relabel h1) (EsPi1.relabel h2)
  | _, _, .o h1 h2 => by rw [relabel_sup]; exact .o (EsPi1.relabel h1) (EsPi1.relabel h2)
  | _, _, .no h => by rw [relabel_not]; exact .no (EsSigma1.relabel h)
  | _, _, .imp h1 h2 => by rw [relabel_imp]; exact .imp (EsSigma1.relabel h1) (EsPi1.relabel h2)

end

end Reetiquetar


/-! ## Parte 4: la inducción por mitades para `Πᵇ₁` -/

theorem realize_tLong {M γ : Type} [L.Structure M] (t : L.Term γ) (v : γ → M) :
    (tLong t).realize v = long (t.realize v) := by
  show Structure.funMap _ _ = Structure.funMap _ _
  congr 1; funext i; match i with | 0 => rfl

section PindPi

variable {M : Type} [L.Structure M]

theorem suma_suc_izq (h : EsModeloBASIC M) (x u : M) : suma (suc x) u = suc (suma x u) := by
  rw [h.b21, h.b23, h.b21]

theorem no_suc_le (h : EsModeloBASIC M) (x : M) : ¬ le (suc x) x := fun hle =>
  ((h.b4 x x).2 hle).2 rfl

/-- **PIND para fórmulas `Πᵇ₁`**, desde la de `Σᵇ₁`. Si `B(a)` fallara, LIND sobre
`C(u) = ∃ w ≤ a (¬B(w) ∧ |w| + u ≤ |a|)` daría un `w` con `|w| + |a| + 1 ≤ |a|`: al bajar de `w` a `⌊w/2⌋` la falla se
conserva (contrarrecíproco del paso) y el largo baja en uno. No hacen falta los bits altos de `a`. -/
theorem pind_pi (hM : EsModeloS12 M) (k : ℕ) (B : L.Formula (Fin (k + 1))) (hB : EsPi1 B) (v : Fin k → M)
    (h0 : B.Realize (Fin.cons cero v))
    (hs : ∀ x : M, B.Realize (Fin.cons (mitad x) v) → B.Realize (Fin.cons x v)) (a : M) :
    B.Realize (Fin.cons a v) := by
  have h := hM.basic
  -- C(u; v, a)
  let g : Fin (k + 1) → Fin (k + 2) ⊕ Fin 1 :=
    Fin.cases (Sum.inr 0) (fun i => Sum.inl (Fin.castSucc (Fin.succ i)))
  let w : L.Term (Fin (k + 2) ⊕ Fin 1) := Term.var (Sum.inr 0)
  let body : L.BoundedFormula (Fin (k + 2)) 1 :=
    (BoundedFormula.relabel g B).not ⊓ leF (tMs (tLong w) (Term.var (Sum.inl 0))) (tLong (Term.var (Sum.inl (Fin.last (k + 1)))))
  let C : L.Formula (Fin (k + 2)) := existeAcotado (Term.var (Sum.inl (Fin.last (k + 1)))) body
  have hC : EsSigma1 C := .existe _ (.y (.no (EsPi1.relabel g hB)) (.aguda (.rel _ _)))
  have hg : ∀ (u z : M), (Sum.elim (Fin.cons u (Fin.snoc v a) : Fin (k + 2) → M)
      ((Fin.snoc (default : Fin 0 → M) z : Fin 1 → M) ∘ Fin.castAdd 0) ∘ g) = Fin.cons z v := by
    intro u z; funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp only [g, Function.comp_apply, Fin.cases_succ, Sum.elim_inl, Fin.cons_succ]
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.snoc_castSucc]
  have hr : ∀ u : M, C.Realize (Fin.cons u (Fin.snoc v a)) ↔
      ∃ z, le z a ∧ ¬ B.Realize (Fin.cons z v) ∧ le (suma (long z) u) (long a) := by
    intro u
    rw [Formula.Realize, Parikh.realize_existe]
    refine exists_congr fun z => ?_
    have ha : (Fin.cons u (Fin.snoc v a) : Fin (k + 2) → M) (Fin.last (k + 1)) = a := by
      rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
    let E := Sum.elim (Fin.cons u (Fin.snoc v a) : Fin (k + 2) → M) (Fin.snoc (default : Fin 0 → M) z)
    have e1 : (Term.var (Sum.inl (Fin.last (k + 1))) : L.Term (Fin (k + 2) ⊕ Fin 0)).realize
        (Sum.elim (Fin.cons u (Fin.snoc v a)) default) = a := ha
    have e2 : (tMs (tLong w) (Term.var (Sum.inl 0))).realize E = suma (long z) u := by
      rw [tMs, Term.realize_functions_apply₂, realize_tLong]; rfl
    have e3 : (tLong (Term.var (Sum.inl (Fin.last (k + 1)))) : L.Term (Fin (k + 2) ⊕ Fin 1)).realize E =
        long a := by
      rw [realize_tLong]; exact congrArg long ha
    have e4 : (BoundedFormula.relabel g B).Realize (Fin.cons u (Fin.snoc v a)) (Fin.snoc default z) ↔
        B.Realize (Fin.cons z v) := by
      rw [BoundedFormula.realize_relabel, hg u z]
      exact iff_of_eq (by congr 1; exact Subsingleton.elim _ _)
    rw [e1]
    simp only [body, BoundedFormula.realize_inf, BoundedFormula.realize_not, e4]
    rw [Parikh.realize_leF]
    change le z a ∧ ¬B.Realize (Fin.cons z v) ∧ le ((tMs (tLong w) (Term.var (Sum.inl 0))).realize E)
      ((tLong (Term.var (Sum.inl (Fin.last (k + 1))))).realize E) ↔ _
    rw [e2, e3]
  by_contra hfalla
  rcases cero_o_uno_le h a with rfl | ha1
  · exact hfalla h0
  have ha0 : a ≠ cero := fun e => by
    subst e; exact no_suc_le h cero (by simpa [uno] using ha1)
  have key := lind hM (k + 1) C hC (Fin.snoc v a) ((hr cero).2 ⟨a, le_refl' h a, hfalla, by
      rw [h.b22]; exact le_refl' h _⟩) (fun u hu => by
      rw [hr] at hu ⊢
      obtain ⟨z, hza, hBz, hle⟩ := hu
      by_cases hz0 : z = cero
      · exact absurd (hz0 ▸ h0) hBz
      refine ⟨mitad z, h.b8 _ _ _ (mitad_le h z) hza, fun hb => hBz (hs z hb), ?_⟩
      rw [h.b31 z hz0, suma_suc_izq h] at hle
      rwa [h.b23]) (doble a)
  rw [hr, (h.b10 a ha0).1] at key
  obtain ⟨z, -, -, hle⟩ := key
  rw [h.b23] at hle
  have h1 : le (long a) (suma (long z) (long a)) := le_suma_der h _ _
  exact no_suc_le h _ (h.b8 _ _ _ (suc_mono h _ _ h1) hle)

end PindPi


/-! ## Encima del arranque: S¹₂ contiene a T⁰₂ -/

section T02

variable {M : Type} [L.Structure M]

theorem realize_fin0 {N γ : Type} [L.Structure N] (φ : L.BoundedFormula γ 0) (V : γ → N) (xs : Fin 0 → N) :
    φ.Realize V xs ↔ Formula.Realize φ V := by
  rw [Subsingleton.elim xs default]; rfl

theorem doble_eq_suma (h : EsModeloBASIC M) (m : M) : doble m = suma m m := by
  rw [doble, h.b28, h.b27, h.b27, h.b26, h.b21 cero m, h.b22]

theorem suma_cero_izq (h : EsModeloBASIC M) (a : M) : suma cero a = a := by
  rw [h.b21, h.b22]

/-- **S¹₂ demuestra la inducción de uno en uno para las fórmulas agudas** (Buss 1986, p. 32: «S^i_2 ⊢ T^{i-1}_2» con
`i = 1`). Se aplica `pind_pi` a `B(z) = ∀ w ≤ a (w + z ≤ a → A(w) → A(w + z))`: el paso de `⌊z/2⌋` a `z` aplica
`B(⌊z/2⌋)` dos veces y, si `z` es impar, una vez el paso de `A`. -/
theorem s12ContieneT02 : S12ContieneT02 := by
  intro M _ hM
  have h := hM.basic
  refine ⟨h, fun k A hA v h0 hs a => ?_⟩
  -- las variables de B: z = 0, los parámetros de A = 1..k, a = k + 1; la ligada w = inr 0
  let W : L.Term (Fin (k + 2) ⊕ Fin 1) := Term.var (Sum.inr 0)
  let Z : L.Term (Fin (k + 2) ⊕ Fin 1) := Term.var (Sum.inl 0)
  let Aa : L.Term (Fin (k + 2) ⊕ Fin 1) := Term.var (Sum.inl (Fin.last (k + 1)))
  let ps : Fin k → L.Term (Fin (k + 2) ⊕ Fin 1) := fun i => Term.var (Sum.inl (Fin.castSucc (Fin.succ i)))
  let A1 : L.Formula (Fin (k + 2) ⊕ Fin 1) := A.subst (Fin.cons (α := fun _ => L.Term _) W ps)
  let A2 : L.Formula (Fin (k + 2) ⊕ Fin 1) := A.subst (Fin.cons (α := fun _ => L.Term _) (tMs W Z) ps)
  let cuerpo : L.BoundedFormula (Fin (k + 2)) 1 :=
    (leF (tMs W Z) Aa).imp ((BoundedFormula.relabel id A1).imp (BoundedFormula.relabel id A2))
  let B : L.Formula (Fin (k + 2)) := paraTodoAcotado (Term.var (Sum.inl (Fin.last (k + 1)))) cuerpo
  have hA1 : EsAguda A1 := EsAguda.mapa (esMapaAcotado_subst _) hA
  have hA2 : EsAguda A2 := EsAguda.mapa (esMapaAcotado_subst _) hA
  have hB : EsPi1 B :=
    .todo _ (.aguda (.imp (.rel _ _) (.imp (EsAguda.relabel id hA1) (EsAguda.relabel id hA2))))
  have ha : ∀ z : M, (Fin.cons z (Fin.snoc v a) : Fin (k + 2) → M) (Fin.last (k + 1)) = a := by
    intro z; rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
  have hps : ∀ (z w : M), (fun i : Fin k => (ps i).realize
      (Sum.elim (Fin.cons z (Fin.snoc v a) : Fin (k + 2) → M) ((Fin.snoc (default : Fin 0 → M) w : Fin 1 → M) ∘
        Fin.castAdd 0))) = v := by
    intro z w; funext i
    simp only [ps, Term.realize_var, Sum.elim_inl]
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.snoc_castSucc]
  have hr : ∀ z : M, B.Realize (Fin.cons z (Fin.snoc v a)) ↔
      ∀ w, le w a → le (suma w z) a → A.Realize (Fin.cons w v) → A.Realize (Fin.cons (suma w z) v) := by
    intro z
    rw [Formula.Realize, Parikh.realize_paraTodo]
    have e1 : (Term.var (Sum.inl (Fin.last (k + 1))) : L.Term (Fin (k + 2) ⊕ Fin 0)).realize
        (Sum.elim (Fin.cons z (Fin.snoc v a)) default) = a := ha z
    rw [e1]
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    let E := Sum.elim (Fin.cons z (Fin.snoc v a) : Fin (k + 2) → M)
      ((Fin.snoc (default : Fin 0 → M) w : Fin 1 → M) ∘ Fin.castAdd 0)
    have eW : W.realize E = w := rfl
    have eZ : Z.realize E = z := rfl
    have eS : (tMs W Z).realize E = suma w z := by rw [tMs, Term.realize_functions_apply₂]; rfl
    have eA : Aa.realize E = a := ha z
    have r1 : (BoundedFormula.relabel id A1).Realize (Fin.cons z (Fin.snoc v a)) (Fin.snoc default w) ↔
        A.Realize (Fin.cons w v) := by
      rw [BoundedFormula.realize_relabel, Function.comp_id]
      rw [realize_fin0, formula_realize_subst]
      apply iff_of_eq; congr 1; funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero, Fin.cons_zero, eW]
      · rw [Fin.cons_succ, Fin.cons_succ]; exact congrFun (hps z w) j
    have r2 : (BoundedFormula.relabel id A2).Realize (Fin.cons z (Fin.snoc v a)) (Fin.snoc default w) ↔
        A.Realize (Fin.cons (suma w z) v) := by
      rw [BoundedFormula.realize_relabel, Function.comp_id]
      rw [realize_fin0, formula_realize_subst]
      apply iff_of_eq; congr 1; funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero, Fin.cons_zero, eS]
      · rw [Fin.cons_succ, Fin.cons_succ]; exact congrFun (hps z w) j
    simp only [cuerpo, BoundedFormula.realize_imp, r1, r2]
    rw [Parikh.realize_leF]
    change le ((tMs W Z).realize E) (Aa.realize E) → _ ↔ _
    rw [eS, eA]
  have key := pind_pi hM (k + 1) B hB (Fin.snoc v a) ((hr cero).2 fun w _ _ hw => by rwa [h.b22]) (fun z hz => by
      rw [hr] at hz ⊢
      intro w hwa hwz hAw
      set m := mitad z
      have hmz : le m z := mitad_le h z
      have hwm : le (suma w m) a := h.b8 _ _ _ (suma_mono h _ _ _ _ (le_refl' h w) hmz) hwz
      have h1 := hz w hwa hwm hAw
      have hdz : le (doble m) z := by
        rcases (h.b32 m z).1 rfl with e | e
        · rw [e]; exact le_refl' h _
        · have := le_suc h (doble m); rw [e] at this; exact this
      have hwd : le (suma (suma w m) m) a := by
        rw [h.b24, ← doble_eq_suma h]
        exact h.b8 _ _ _ (suma_mono h _ _ _ _ (le_refl' h w) hdz) hwz
      have h2 := hz (suma w m) hwm hwd h1
      rw [h.b24, ← doble_eq_suma h] at h2
      rcases (h.b32 m z).1 rfl with e | e
      · rwa [← e]
      · rw [← e, h.b23]; exact hs _ h2) a
  have := (hr a).1 key cero (h.b3 a) (by rw [suma_cero_izq h]; exact le_refl' h a) h0
  rwa [suma_cero_izq h] at this

end T02

end Arranque
end Acotada
end Sagitta.Map
