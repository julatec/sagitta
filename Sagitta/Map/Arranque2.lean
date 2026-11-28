import Sagitta.Map.Arranque

/-!
# El arranque, parte 2b: los bits altos en T¹₂, y T¹₂ contiene a S¹₂

Buss (1986, p. 32) anuncia «T^i_2 ⊢ S^i_2». Para `i = 1`: en todo modelo de T¹₂ (BASIC más la inducción de uno en uno
para `Σᵇ₁`) vale PIND para `Σᵇ₁`. La ruta es la de Buss: bajar por los **bits altos** de `a`, los números `⌊a/2ʲ⌋`,
de uno en uno, desde `0` (que es `⌊a/2^{|a|}⌋`) hasta `a` (que es `⌊a/2⁰⌋`). Cada uno es la mitad del siguiente, así
que el paso de PIND (`φ(⌊x/2⌋) → φ(x)`) es exactamente el paso de una inducción ordinaria sobre `u ≤ |a|`.

**El truco que ahorra la resta y la potencia como funciones nuevas.** El lenguaje ya tiene `2ʲ` para cada `j` que sea
un largo: `1 # w = 2^{|w|}`. Así que «`y` es el número que forman los bits altos de `a` cuando se le quitan `|w|`
bits» se escribe sin definir nada, con una fórmula **sin cuantificadores**:

  `y · (1 # w) ≤ a  ∧  ¬ (Sy · (1 # w) ≤ a)`.

Y la inducción es sobre `u` con la fórmula `Σᵇ₁`

  `u ≤ |a| → ∃ w ≤ a ∃ y ≤ a (|w| + u ≤ |a| ∧ y·(1#w) ≤ a ∧ ¬(Sy·(1#w) ≤ a) ∧ φ(y))`.

Para el paso se cambia `w` por `⌊w/2⌋` y `y` por `2y` o `2y + 1`, el que siga cumpliendo las dos desigualdades. Al
final, `|w| + |a| ≤ |a|` obliga a `w = 0`, `1 # 0 = 1` y entonces `y = a`.

## Qué hay (todo probado, sin `sorry`)

* Aritmética de `1 # w` desde BASIC: `smash_uno_cero` (`1 # 0 = 1`), `smash_uno_uno` (`1 # 1 = 2`, que BASIC no
  trae como axioma: sale de los axiomas 15, 16, 18 y 30), `smash_uno_mitad` (`1 # w = 2 · (1 # ⌊w/2⌋)` si `w ≠ 0`).
* `pind_pi_t12`: en T¹₂ vale PIND para `Πᵇ₁`. Es el argumento de `pind_pi` con IND directa en lugar de LIND.
* `lt_smash_uno`: en T¹₂, `a < 1 # a` (es decir `a < 2^{|a|}`), por `pind_pi_t12` sobre una fórmula aguda.
* `bits_altos_t12`: en T¹₂, para todo `u ≤ |a|` hay `w ≤ a` con `|w| + u ≤ |a|` y un `y ≤ a` que es el bloque de
  bits altos de `a` a esa altura. Es la existencia de los bits altos.
* `bits_altos_unico`: en BASIC, el `y` de las dos desigualdades es único para cada `w`.
* `pind_t12`: en T¹₂ vale PIND para `Σᵇ₁`.
* **`t12ContieneS12 : T12ContieneS12`** (Buss 1986, p. 32, `i = 1`).

## Lo que no está aquí

* La resta truncada y `2ᵘ` como funciones definidas por fórmulas `Σᵇ₁` con su totalidad demostrada: no hicieron falta,
  porque `1 # w` hace de `2^{|w|}` y la cuenta se lleva en `|w| + u ≤ |a|`. La resta truncada quedó después en
  `DefinibleCobham.lean` (`resta_existe`, `resta_definible`, en S¹₂); `2ᵘ` como función sigue abierta.
* El caso `i > 1` (`T^i_2 ⊢ S^i_2`): el mismo argumento pide que la clase sea cerrada por los cuantificadores del
  cuerpo; no se intenta.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada
namespace Arranque

open Tiempo Parikh

/-! ## La aritmética de `1 # w` en BASIC -/

section Smash

variable {M : Type} [L.Structure M] (h : EsModeloBASIC M)
include h

theorem uno_ne_cero : (uno : M) ≠ cero := suc_ne_cero h cero

/-- `1 # 0 = 1`. -/
theorem smash_uno_cero : smash uno (cero : M) = uno := by rw [h.b16, h.b14]

theorem doble_uno : doble (uno : M) = suc (suc cero) := by rw [doble, prod_uno h]

theorem long_doble_uno : long (doble (uno : M)) = suma (long uno) (long uno) := by
  rw [(h.b10 uno (uno_ne_cero h)).1, h.b11, suma_uno h]

/-- **`1 # 1 = 2`.** No es un axioma: `2 # 1 = (1 # 1)·(1 # 1)` (axioma 18, porque `|2| = |1| + |1|`) y
`1 # 2 = 2·(1 # 1)` (axioma 15); el 16 iguala los dos lados y el 30 cancela el factor `1 # 1 ≥ 1`. -/
theorem smash_uno_uno : smash uno (uno : M) = doble uno := by
  set T := smash uno (uno : M) with hTdef
  have e1 : smash (doble uno) uno = prod T T := h.b18 _ _ _ _ (long_doble_uno h)
  have e2 : smash uno (doble uno) = doble T := (h.b15 uno (uno_ne_cero h)).1
  rw [h.b16, e2] at e1
  have hT : le uno T := uno_le_smash h _ _
  have e3 : doble T = prod T (doble uno) := by
    change prod (suc (suc cero)) T = _
    rw [doble_uno h, h.b28]
  have e4 : prod T T = prod T (doble uno) := by rw [← e1, e3]
  refine h.b7 _ _ ((h.b30 T T _ hT).1 ?_) ((h.b30 T _ T hT).1 ?_)
  · rw [e4]; exact le_refl' h _
  · rw [e4]; exact le_refl' h _

/-- **`1 # w = 2 · (1 # ⌊w/2⌋)`** si `w ≠ 0`: el axioma 18 con `|w| = |⌊w/2⌋| + |1|`, y `1 # 1 = 2`. -/
theorem smash_uno_mitad (w : M) (hw : w ≠ cero) : smash uno w = doble (smash uno (mitad w)) := by
  have hl : long w = suma (long (mitad w)) (long uno) := by rw [h.b11, suma_uno h, h.b31 w hw]
  have e := h.b18 w uno (mitad w) uno hl
  rw [h.b16 w uno, h.b16 (mitad w) uno, smash_uno_uno h, doble_uno h] at e
  rw [e]
  change _ = prod (suc (suc cero)) _
  exact h.b28 _ _

theorem no_le_iff {x y : M} : ¬ le y x ↔ (le x y ∧ x ≠ y) := by
  constructor
  · intro hn
    refine ⟨(h.b6 y x).resolve_right hn, fun e => hn (e ▸ le_refl' h x)⟩
  · rintro ⟨hxy, hne⟩ hyx
    exact hne (h.b7 _ _ hxy hyx)

/-- Los bits altos son únicos: si `y·P ≤ a < Sy·P` y `y'·P ≤ a < Sy'·P`, entonces `y = y'`. -/
theorem bits_altos_unico (P a y y' : M) (h1 : le (prod y P) a) (h2 : ¬ le (prod (suc y) P) a)
    (h1' : le (prod y' P) a) (h2' : ¬ le (prod (suc y') P) a) : y = y' := by
  have menor : ∀ y y' : M, le (prod y P) a → ¬ le (prod (suc y') P) a → le y y' := by
    intro y y' h1 h2'
    by_contra hn
    have hs : le (suc y') y := (h.b4 y' y).1 ((no_le_iff h).1 hn)
    have : le (prod (suc y') P) (prod y P) := by
      rw [h.b28 (suc y'), h.b28 y]; exact prod_mono_der h P _ _ hs
    exact h2' (h.b8 _ _ _ this h1)
  exact h.b7 _ _ (menor y y' h1 h2') (menor y' y h1' h2)

end Smash


/-! ## PIND para `Πᵇ₁` en T¹₂ -/

section PindPiT12

variable {M : Type} [L.Structure M]

/-- **PIND para fórmulas `Πᵇ₁` en todo modelo de T¹₂.** El argumento de `pind_pi`, con IND en lugar de LIND: si `B(a)`
fallara, IND sobre `C(u) = ∃ w ≤ a (¬B(w) ∧ |w| + u ≤ |a|)` llega a `u = S|a|`, y `|w| + S|a| ≤ |a|` es imposible. -/
theorem pind_pi_t12 (hM : EsModeloT12 M) (k : ℕ) (B : L.Formula (Fin (k + 1))) (hB : EsPi1 B) (v : Fin k → M)
    (h0 : B.Realize (Fin.cons cero v))
    (hs : ∀ x : M, B.Realize (Fin.cons (mitad x) v) → B.Realize (Fin.cons x v)) (a : M) :
    B.Realize (Fin.cons a v) := by
  have h := hM.basic
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
  have key := hM.ind (k + 1) C hC (Fin.snoc v a) ((hr cero).2 ⟨a, le_refl' h a, hfalla, by
      rw [h.b22]; exact le_refl' h _⟩) (fun u hu => by
      rw [hr] at hu ⊢
      obtain ⟨z, hza, hBz, hle⟩ := hu
      by_cases hz0 : z = cero
      · exact absurd (hz0 ▸ h0) hBz
      refine ⟨mitad z, h.b8 _ _ _ (mitad_le h z) hza, fun hb => hBz (hs z hb), ?_⟩
      rw [h.b31 z hz0, suma_suc_izq h] at hle
      rwa [h.b23]) (suc (long a))
  rw [hr] at key
  obtain ⟨z, -, -, hle⟩ := key
  rw [h.b23] at hle
  have h1 : le (long a) (suma (long z) (long a)) := le_suma_der h _ _
  exact no_suc_le h _ (h.b8 _ _ _ (suc_mono h _ _ h1) hle)

/-- **`a < 2^{|a|}`, es decir `a < 1 # a`, en todo modelo de T¹₂.** Por `pind_pi_t12` sobre la fórmula aguda
`¬ (1 # x ≤ x)`: si `m = ⌊x/2⌋ < 1 # m`, entonces `x ≤ 2m + 1 < 2·(1 # m) = 1 # x` (axioma 20). -/
theorem lt_smash_uno (hM : EsModeloT12 M) (a : M) : ¬ le (smash uno a) a := by
  have h := hM.basic
  let B : L.Formula (Fin 1) :=
    (Relations.formula₂ (Rel.le : L.Relations 2) (tSm tU (Term.var 0)) (Term.var 0)).not
  have hB : EsPi1 B := .aguda (.imp (.rel _ _) .falso)
  have hr : ∀ x : M, B.Realize (Fin.cons x (default : Fin 0 → M)) ↔ ¬ le (smash uno x) x := by
    intro x
    simp only [B, Formula.realize_not, Formula.realize_rel₂, tSm, tU, tSc, Term.realize_functions_apply₂,
      Term.realize_functions_apply₁, Term.realize_var, realize_tC]
    rfl
  have base : ¬ le (smash uno (cero : M)) cero := by
    rw [smash_uno_cero h]
    intro hle
    exact uno_ne_cero h (h.b7 _ _ hle (h.b3 _))
  refine (hr a).1 (pind_pi_t12 hM 0 B hB default ((hr cero).2 base) (fun x hx => ?_) a)
  rw [hr] at hx ⊢
  by_cases hx0 : x = cero
  · subst hx0; exact base
  set m := mitad x
  rw [smash_uno_mitad h x hx0]
  obtain ⟨hmQ, hne⟩ := (no_le_iff h).1 hx
  obtain ⟨h20, h20'⟩ := h.b20 _ _ hmQ hne
  have hx2 : le x (suc (doble m)) := by
    rcases (h.b32 m x).1 rfl with e | e
    · rw [← e]; exact le_suc h _
    · rw [← e]; exact le_refl' h _
  intro hle
  exact h20' (h.b7 _ _ h20 (h.b8 _ _ _ hle hx2))

end PindPiT12


/-! ## Los bits altos y PIND para `Σᵇ₁` en T¹₂ -/

section PindT12

variable {M : Type} [L.Structure M]

theorem suma_suc_conm (h : EsModeloBASIC M) (x u : M) : suma x (suc u) = suma (suc x) u := by
  rw [h.b23, suma_suc_izq h]

/-- **El paso de los bits altos.** Si `y·(2Q) ≤ a < Sy·(2Q)`, alguno de `2y`, `2y + 1` cumple lo mismo con `Q`. -/
theorem paso_bits (h : EsModeloBASIC M) (a y Q : M) (h1 : le (prod y (doble Q)) a)
    (h2 : ¬ le (prod (suc y) (doble Q)) a) :
    ∃ y', mitad y' = y ∧ le (prod y' Q) a ∧ ¬ le (prod (suc y') Q) a := by
  -- y·(2Q) = (2y)·Q y Sy·(2Q) = S(S(2y))·Q, por la distributiva y la conmutativa
  have dQ : doble Q = suma Q Q := doble_eq_suma h Q
  have dy : doble y = suma y y := doble_eq_suma h y
  have e1 : prod y (doble Q) = prod (doble y) Q := by
    rw [dQ, dy, h.b29, h.b28 (suma y y), h.b29, h.b28 Q y]
  have e2 : prod (suc y) (doble Q) = prod (suc (suc (doble y))) Q := by
    rw [h.b28 (suc y), h.b27, h.b28 (suc (suc (doble y))), h.b27, h.b27, h.b28 (doble Q) y, e1,
      h.b28 (doble y) Q, dQ, h.b24]
  rcases em (le (prod (suc (doble y)) Q) a) with hle | hle
  · refine ⟨suc (doble y), ((h.b32 y (suc (doble y))).2 (.inr rfl)).symm, hle, ?_⟩
    rw [← e2]; exact h2
  · refine ⟨doble y, ((h.b32 y (doble y)).2 (.inl rfl)).symm, ?_, hle⟩
    rw [← e1]; exact h1

/-- **Los bits altos existen en T¹₂**, con la invariante de la inducción: para cada `u ≤ |a|` hay `w, y ≤ a` con
`|w| + u ≤ |a|`, `y·(1#w) ≤ a < Sy·(1#w)` y `φ(y)`, si `φ` es `Σᵇ₁`, vale en `0` y pasa de `⌊x/2⌋` a `x`. Con
`φ` verdadera es la existencia de los bits altos de `a` a cada altura. -/
theorem bits_altos_t12 (hM : EsModeloT12 M) (k : ℕ) (φ : L.Formula (Fin (k + 1))) (hφ : EsSigma1 φ) (v : Fin k → M)
    (h0 : φ.Realize (Fin.cons cero v))
    (hs : ∀ x : M, φ.Realize (Fin.cons (mitad x) v) → φ.Realize (Fin.cons x v)) (a u : M)
    (hu : le u (long a)) :
    ∃ w, le w a ∧ ∃ y, le y a ∧ le (suma (long w) u) (long a) ∧ le (prod y (smash uno w)) a ∧
      ¬ le (prod (suc y) (smash uno w)) a ∧ φ.Realize (Fin.cons y v) := by
  have h := hM.basic
  -- variables libres: u = 0, los parámetros de φ = 1..k, a = k + 1; ligadas: w = inr 0, y = inr 1
  let U : L.Term (Fin (k + 2) ⊕ Fin 2) := Term.var (Sum.inl 0)
  let A : L.Term (Fin (k + 2) ⊕ Fin 2) := Term.var (Sum.inl (Fin.last (k + 1)))
  let W : L.Term (Fin (k + 2) ⊕ Fin 2) := Term.var (Sum.inr 0)
  let Y : L.Term (Fin (k + 2) ⊕ Fin 2) := Term.var (Sum.inr 1)
  let g : Fin (k + 1) → Fin (k + 2) ⊕ Fin 2 :=
    Fin.cases (Sum.inr 1) (fun i => Sum.inl (Fin.castSucc (Fin.succ i)))
  let body : L.BoundedFormula (Fin (k + 2)) 2 :=
    leF (tMs (tLong W) U) (tLong A) ⊓ (leF (tPr Y (tSm tU W)) A ⊓
      ((leF (tPr (tSc Y) (tSm tU W)) A).not ⊓ BoundedFormula.relabel g φ))
  let inner : L.BoundedFormula (Fin (k + 2)) 1 := existeAcotado (Term.var (Sum.inl (Fin.last (k + 1)))) body
  let outer : L.Formula (Fin (k + 2)) := existeAcotado (Term.var (Sum.inl (Fin.last (k + 1)))) inner
  let ψ : L.Formula (Fin (k + 2)) :=
    (leF (Term.var (Sum.inl 0)) (tLong (Term.var (Sum.inl (Fin.last (k + 1)))))).imp outer
  have hψ : EsSigma1 ψ :=
    .imp (.aguda (.rel _ _)) (.existe _ (.existe _ (.y (.aguda (.rel _ _)) (.y (.aguda (.rel _ _))
      (.y (.aguda (.imp (.rel _ _) .falso)) (EsSigma1.relabel g hφ))))))
  have ha : ∀ u : M, (Fin.cons u (Fin.snoc v a) : Fin (k + 2) → M) (Fin.last (k + 1)) = a := by
    intro u; rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
  have hg : ∀ (u w y : M), (Sum.elim (Fin.cons u (Fin.snoc v a) : Fin (k + 2) → M)
      ((Fin.snoc (Fin.snoc (default : Fin 0 → M) w) y : Fin 2 → M) ∘ Fin.castAdd 0) ∘ g) = Fin.cons y v := by
    intro u w y; funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp only [g, Function.comp_apply, Fin.cases_succ, Sum.elim_inl, Fin.cons_succ]
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.snoc_castSucc]
  have hr : ∀ u : M, ψ.Realize (Fin.cons u (Fin.snoc v a)) ↔ (le u (long a) →
      ∃ w, le w a ∧ ∃ y, le y a ∧ le (suma (long w) u) (long a) ∧ le (prod y (smash uno w)) a ∧
        ¬ le (prod (suc y) (smash uno w)) a ∧ φ.Realize (Fin.cons y v)) := by
    intro u
    rw [Formula.Realize, BoundedFormula.realize_imp, Parikh.realize_leF, realize_tLong]
    simp only [Term.realize_var, Sum.elim_inl, ha]
    refine imp_congr_right fun _ => ?_
    rw [Parikh.realize_existe]
    simp only [Term.realize_var, Sum.elim_inl, ha]
    refine exists_congr fun w => and_congr_right fun _ => ?_
    rw [Parikh.realize_existe]
    simp only [Term.realize_var, Sum.elim_inl, ha]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    let E := Sum.elim (Fin.cons u (Fin.snoc v a) : Fin (k + 2) → M) (Fin.snoc (Fin.snoc default w) y : Fin 2 → M)
    have eW : W.realize E = w := rfl
    have eY : Y.realize E = y := rfl
    have eU : U.realize E = u := rfl
    have eA : A.realize E = a := ha u
    have eP : (tSm tU W).realize E = smash uno w := by
      simp only [tSm, tU, tSc, Term.realize_functions_apply₂, Term.realize_functions_apply₁, realize_tC, eW]; rfl
    have e1 : (tMs (tLong W) U).realize E = suma (long w) u := by
      rw [tMs, Term.realize_functions_apply₂, realize_tLong, eW, eU]; rfl
    have e2 : (tLong A).realize E = long a := by rw [realize_tLong, eA]
    have e3 : (tPr Y (tSm tU W)).realize E = prod y (smash uno w) := by
      rw [tPr, Term.realize_functions_apply₂, eP, eY]; rfl
    have e4 : (tPr (tSc Y) (tSm tU W)).realize E = prod (suc y) (smash uno w) := by
      rw [tPr, Term.realize_functions_apply₂, eP, tSc, Term.realize_functions_apply₁, eY]; rfl
    have e5 : (BoundedFormula.relabel g φ).Realize (Fin.cons u (Fin.snoc v a))
        (Fin.snoc (Fin.snoc default w) y) ↔ φ.Realize (Fin.cons y v) := by
      rw [BoundedFormula.realize_relabel, hg u w y]
      exact iff_of_eq (by congr 1; exact Subsingleton.elim _ _)
    simp only [body, BoundedFormula.realize_inf, BoundedFormula.realize_not, e5, Parikh.realize_leF]
    change le ((tMs (tLong W) U).realize E) ((tLong A).realize E) ∧ le ((tPr Y (tSm tU W)).realize E) (A.realize E) ∧
      ¬ le ((tPr (tSc Y) (tSm tU W)).realize E) (A.realize E) ∧ _ ↔ _
    rw [e1, e2, e3, e4, eA]
  have key := hM.ind (k + 1) ψ hψ (Fin.snoc v a)
    ((hr cero).2 fun _ => ⟨a, le_refl' h a, cero, h.b3 a, by rw [h.b22]; exact le_refl' h _,
      by rw [prod_cero_izq h]; exact h.b3 a,
      by rw [h.b28]; change ¬ le (prod (smash uno a) uno) a; rw [prod_uno h]; exact lt_smash_uno hM a, h0⟩)
    (fun u hu => by
      rw [hr] at hu ⊢
      intro hSu
      obtain ⟨w, hwa, y, hya, hl, h1, h2, hφy⟩ := hu (h.b8 _ _ _ (le_suc h u) hSu)
      by_cases hw0 : w = cero
      · -- w = 0: ya se llegó a `a`, se queda ahí
        refine ⟨w, hwa, y, hya, ?_, h1, h2, hφy⟩
        rw [hw0, h.b9, suma_cero_izq h]; exact hSu
      · have hl' : le (suma (long (mitad w)) (suc u)) (long a) := by
          rw [suma_suc_conm h, ← h.b31 w hw0]; exact hl
        rw [smash_uno_mitad h w hw0] at h1 h2
        obtain ⟨y', hy', h1', h2'⟩ := paso_bits h a y _ h1 h2
        have hQ : le uno (smash uno (mitad w)) := uno_le_smash h _ _
        have hy'a : le y' a := by
          have : le (prod y' uno) (prod y' (smash uno (mitad w))) := prod_mono_der h _ _ _ hQ
          rw [prod_uno h] at this
          exact h.b8 _ _ _ this h1'
        exact ⟨mitad w, h.b8 _ _ _ (mitad_le h w) hwa, y', hy'a, hl', h1', h2', hs y' (hy' ▸ hφy)⟩) u
  exact (hr u).1 key hu

/-- **PIND para `Σᵇ₁` en todo modelo de T¹₂.** `bits_altos_t12` en `u = |a|` da `w` con `|w| + |a| ≤ |a|`, o sea
`w = 0`, `1 # 0 = 1`, y el `y` con `y ≤ a < Sy` es `a`. -/
theorem pind_t12 (hM : EsModeloT12 M) (k : ℕ) (φ : L.Formula (Fin (k + 1))) (hφ : EsSigma1 φ) (v : Fin k → M)
    (h0 : φ.Realize (Fin.cons cero v))
    (hs : ∀ x : M, φ.Realize (Fin.cons (mitad x) v) → φ.Realize (Fin.cons x v)) (a : M) :
    φ.Realize (Fin.cons a v) := by
  have h := hM.basic
  obtain ⟨w, -, y, hya, hl, -, h2, hφy⟩ :=
    bits_altos_t12 hM k φ hφ v h0 hs a (long a) (le_refl' h _)
  have hlw : long w = cero := by
    have : le (suma (long a) (long w)) (suma (long a) cero) := by rw [h.b21, h.b22]; exact hl
    exact h.b7 _ _ ((h.b25 _ _ _).1 this) (h.b3 _)
  have hw : w = cero := by
    by_contra hw
    exact suc_ne_cero h _ ((h.b31 w hw).symm.trans hlw)
  rw [hw, smash_uno_cero h, prod_uno h] at h2
  have : y = a := by
    by_contra hne
    exact h2 ((h.b4 y a).1 ⟨hya, hne⟩)
  exact this ▸ hφy

/-- **Buss: T¹₂ demuestra S¹₂** (1986, p. 32, «T^i_2 ⊢ S^i_2» con `i = 1`): todo modelo de T¹₂ es modelo de S¹₂. -/
theorem t12ContieneS12 : T12ContieneS12 :=
  fun _ _ hM => ⟨hM.basic, pind_t12 hM⟩

end PindT12

end Arranque
end Acotada
end Sagitta.Map
