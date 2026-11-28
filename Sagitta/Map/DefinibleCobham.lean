import Sagitta.Map.Arranque2
import Sagitta.Map.Parikh
import Sagitta.Map.TiempoCobham

/-!
# La dirección fácil del teorema de Buss: de Cobham a S¹₂, salvo la recursión

Buss (1986) probó que las funciones de tiempo polinomial son exactamente las `Σᵇ₁`-definibles en S¹₂. La dirección
difícil ya está (`Cobham.definibleEsPolinomial`, en `TiempoCobham.lean`). La fácil, `PolinomialEsDefinible`, tiene
dos mitades:

* **(a) máquinas → Cobham**: toda función de tiempo polinomial es un programa de `Cob` (Cobham 1965).
* **(b) Cobham → S¹₂**: todo programa de `Cob` es `Σᵇ₁`-definible en S¹₂, por inducción sobre el programa.

## Lo establecido aquí (sin `sorry`)

* **`DefinibleN n f`**: la definición de Buss (§2.3, p. 33) para `n` argumentos, igual que `DefinibleSigma1` pero con
  `x⃗` en vez de un solo `x`. Para `n = 1` es `DefinibleSigma1` (`definibleSigma1_de_uno`).
* **Términos** (`termino_definible`): toda función que es un término del lenguaje es definible, con la fórmula
  `y = t(x⃗)`. Cubre `0`, las proyecciones, `S`, `+`, `·`, `⌊x/2⌋`, `|x|` y `#`.
* **El condicional** (`cond_definible`), con la cota `x₁ + x₂`.
* **La resta truncada** (`resta_definible`). La existencia de `a ∸ b` en S¹₂ (`resta_existe`) no es inmediata: S¹₂ no
  trae la resta. Sale por LIND sobre los bits altos de `a - b`, con el mismo truco de `Arranque2.lean`: `1 # w` hace de
  `2^{|w|}` y la invariante es `b + d·(1#w) ≤ a < b + Sd·(1#w)`. En el camino, `a < 1 # a` en S¹₂
  (`lt_smash_uno_s12`, por PIND; `Arranque2.lt_smash_uno` es la de T¹₂).
* **La composición** (`comp_definible`): `∃ z⃗ ≤ t⃗(x⃗) (⋀ φ_{gᵢ}(x⃗, zᵢ) ∧ φ_f(z⃗, y))`. La cota es `t_f(t⃗(x⃗))`,
  y que acota hace falta porque los términos son crecientes en todo modelo de S¹₂ (`termino_mono`, de
  `Parikh.monotonas`).
* **`sinRn_definible`**: todo programa de Cobham **sin recursión** es `Σᵇ₁`-definible en S¹₂.
* **`cob_definible`**: con la recursión como hipótesis (`RecursionDefinible`), todos lo son.
* **`polinomialEsDefinible_de`** y **`teoremaDeBuss_de`**: con (a) y la recursión como hipótesis, la dirección fácil
  y el teorema de Buss completo.

## Lo abierto, con nombre

* **`RecursionDefinible`**: que la recursión sobre la notación con tope conserve la definibilidad. Es lo que pide
  codificar en S¹₂ la sucesión de valores intermedios `F(⌊x/2^{|x|-j}⌋)`, `j ≤ |x|`, como un solo número (Buss 1986,
  cap. 2: sucesiones por bits, con `#`), y probar por LIND que la sucesión existe. Es un teorema conocido.
* **`PolinomialEsCobham`**, la mitad (a). Está probada en complexitylib-v1 (S. Schlesinger, licencia Apache 2.0,
  commit `1d31cd7` del 21 oct 2026, teorema `FP_subset_CobhamFP` de `Complexitylib/Classes/P/Cobham.lean`), pero con
  **otra API**: su modelo de máquina es propio (`Complexitylib.Models.TuringMachine.TM k`), no la `FinTM2` de Mathlib
  que mide `EsPolinomial`, y su álgebra de Cobham es sobre cadenas de bits, no sobre números. Adaptarlo pide dos
  puentes que no existen (`FinTM2` → `TM k` y cadenas → `Cob`) además de la prueba misma (~1.650 líneas solo en
  `Classes/P/Cobham*`, sobre una base de máquinas mucho mayor, con Lean 4.35.0-rc3 y otra Mathlib). No se
  vendorizó nada.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada
namespace DefinibleCobham

open Tiempo Parikh Arranque

/-! ## La definición para varios argumentos -/

/-- **`f` de `n` argumentos es `Σᵇ₁`-definible en S¹₂** (Buss 1986, §2.3, p. 33, con `x⃗` de largo `n`): una fórmula
`Σᵇ₁` `φ(x⃗, y)` (la `y` es la última variable) y un término `t(x⃗)` tales que en todo modelo de S¹₂ cada `x⃗` tiene un
`y ≤ t(x⃗)` con `φ(x⃗, y)`, ese `y` es único, y en ℕ `φ(x⃗, f x⃗)`. -/
def DefinibleN (n : ℕ) (f : (Fin n → ℕ) → ℕ) : Prop :=
  ∃ φ : L.Formula (Fin (n + 1)), EsSigma1 φ ∧ ∃ t : L.Term (Fin n),
    (∀ (M : Type) [L.Structure M], EsModeloS12 M →
      (∀ x : Fin n → M, ∃ y : M, le y (t.realize x) ∧ φ.Realize (Fin.snoc x y : Fin (n + 1) → M)) ∧
      (∀ (x : Fin n → M) (y z : M), φ.Realize (Fin.snoc x y : Fin (n + 1) → M) →
        φ.Realize (Fin.snoc x z : Fin (n + 1) → M) → y = z)) ∧
    ∀ v : Fin n → ℕ, φ.Realize (Fin.snoc v (f v) : Fin (n + 1) → ℕ)

/-- La misma función, escrita de otra forma, sigue siendo definible. -/
theorem DefinibleN.congr {n : ℕ} {f g : (Fin n → ℕ) → ℕ} (hg : DefinibleN n g) (e : ∀ v, f v = g v) :
    DefinibleN n f := by
  have : f = g := funext e
  rwa [this]

theorem snoc_uno {β : Type} (x y : β) : (Fin.snoc ![x] y : Fin 2 → β) = ![x, y] := by
  funext i; match i with | 0 => rfl | 1 => rfl

/-- **Para un argumento es la definición de `Definibles.lean`.** -/
theorem definibleSigma1_de_uno {f : ℕ → ℕ} (h : DefinibleN 1 (fun v => f (v 0))) : DefinibleSigma1 f := by
  obtain ⟨φ, hφ, t, hM, hN⟩ := h
  refine ⟨φ, hφ, ⟨t, fun M _ hS => ⟨fun x => ?_, fun x y z hy hz => ?_⟩⟩, fun n => ?_⟩
  · obtain ⟨y, hy, hφy⟩ := (hM M hS).1 ![x]
    exact ⟨y, hy, by rwa [snoc_uno] at hφy⟩
  · exact (hM M hS).2 ![x] y z (by rwa [snoc_uno]) (by rwa [snoc_uno])
  · have := hN ![n]
    rwa [snoc_uno] at this

/-! ## Los términos son crecientes -/

variable {M : Type} [L.Structure M]

/-- **Todo término es creciente** en todo modelo de S¹₂: las seis funciones lo son (`Parikh.monotonas`). -/
theorem termino_mono (hM : EsModeloS12 M) {β : Type} (t : L.Term β) (a b : β → M) (hab : ∀ i, le (a i) (b i)) :
    le (t.realize a) (t.realize b) := by
  induction t with
  | var i => exact hab i
  | func f ts ih => exact fun_mono hM.basic (monotonas hM) f _ _ ih

/-! ## Los términos son definibles -/

/-- La fórmula `y = t(x⃗)`. -/
def grafoTermino {n : ℕ} (t : L.Term (Fin n)) : L.Formula (Fin (n + 1)) :=
  Term.equal (Term.var (Fin.last n)) (t.relabel Fin.castSucc)

theorem realize_grafoTermino {n : ℕ} (t : L.Term (Fin n)) (x : Fin n → M) (y : M) :
    (grafoTermino t).Realize (Fin.snoc x y : Fin (n + 1) → M) ↔ y = t.realize x := by
  simp only [grafoTermino, Formula.realize_equal, Term.realize_var, Fin.snoc_last, Term.realize_relabel]
  rw [Fin.snoc_comp_castSucc]

/-- **Toda función que es un término es definible**, con la fórmula `y = t(x⃗)` y la cota `t`. -/
theorem termino_definible {n : ℕ} (t : L.Term (Fin n)) : DefinibleN n (fun v => t.realize v) := by
  refine ⟨grafoTermino t, .aguda (.igual _ _), t, fun M _ hM => ⟨fun x => ?_, fun x y z hy hz => ?_⟩,
    fun v => (realize_grafoTermino t v _).2 rfl⟩
  · exact ⟨t.realize x, le_refl' hM.basic _, (realize_grafoTermino t x _).2 rfl⟩
  · rw [realize_grafoTermino] at hy hz
    rw [hy, hz]

/-! ## El condicional -/

/-- La variable `i` de `x⃗`, en el contexto de `φ(x⃗, y)`. -/
def vx {n : ℕ} (i : Fin n) : L.Term (Fin (n + 1)) := Term.var (Fin.castSucc i)

/-- La variable `y`, la última. -/
def vy (n : ℕ) : L.Term (Fin (n + 1)) := Term.var (Fin.last n)

@[simp] theorem realize_vx {n : ℕ} (i : Fin n) (x : Fin n → M) (y : M) :
    (vx i).realize (Fin.snoc x y : Fin (n + 1) → M) = x i := by
  simp [vx]

@[simp] theorem realize_vy {n : ℕ} (x : Fin n → M) (y : M) :
    (vy n).realize (Fin.snoc x y : Fin (n + 1) → M) = y := by
  simp [vy]

/-- `(x₀ = 0 ∧ y = x₁) ∨ (x₀ ≠ 0 ∧ y = x₂)`. -/
def grafoCond : L.Formula (Fin 4) :=
  (Term.equal (vx 0) tC ⊓ Term.equal (vy 3) (vx 1)) ⊔
    ((Term.equal (vx 0) tC).not ⊓ Term.equal (vy 3) (vx 2))

theorem esSigma1_grafoCond : EsSigma1 grafoCond :=
  .o (.y (.aguda (.igual _ _)) (.aguda (.igual _ _))) (.y (.aguda (.imp (.igual _ _) .falso)) (.aguda (.igual _ _)))

theorem realize_grafoCond (x : Fin 3 → M) (y : M) :
    grafoCond.Realize (Fin.snoc x y : Fin 4 → M) ↔
      (x 0 = cero ∧ y = x 1) ∨ (x 0 ≠ cero ∧ y = x 2) := by
  simp only [grafoCond, Formula.realize_sup, Formula.realize_inf, Formula.realize_not, Formula.realize_equal,
    realize_tC]
  rw [realize_vx, realize_vx, realize_vx, realize_vy]

/-- **El condicional es definible**: `si x₀ = 0 entonces x₁, si no x₂`, con la cota `x₁ + x₂`. -/
theorem cond_definible : DefinibleN 3 (fun v => if v 0 = 0 then v 1 else v 2) := by
  refine ⟨grafoCond, esSigma1_grafoCond, tMs (Term.var 1) (Term.var 2), fun M _ hM => ⟨fun x => ?_, ?_⟩, ?_⟩
  · have h := hM.basic
    have eT : (tMs (Term.var 1) (Term.var 2) : L.Term (Fin 3)).realize x = suma (x 1) (x 2) := by
      rw [tMs, Term.realize_functions_apply₂]; rfl
    rw [eT]
    by_cases h0 : x 0 = cero
    · exact ⟨x 1, h.b19 _ _, (realize_grafoCond x _).2 (.inl ⟨h0, rfl⟩)⟩
    · exact ⟨x 2, le_suma_der h _ _, (realize_grafoCond x _).2 (.inr ⟨h0, rfl⟩)⟩
  · intro x y z hy hz
    rw [realize_grafoCond] at hy hz
    rcases hy with ⟨h0, rfl⟩ | ⟨h0, rfl⟩ <;> rcases hz with ⟨h0', rfl⟩ | ⟨h0', rfl⟩
    · rfl
    · exact absurd h0 h0'
    · exact absurd h0' h0
    · rfl
  · intro v
    rw [realize_grafoCond]
    by_cases h0 : v 0 = 0
    · exact .inl ⟨h0, by simp [h0]⟩
    · exact .inr ⟨h0, by simp [h0]⟩

/-! ## La resta truncada

S¹₂ no trae la resta: que `b ≤ a` dé un `d` con `b + d = a` hay que demostrarlo. Se arma `d` de arriba abajo, un
bit por vuelta, con LIND sobre `u ≤ |a|`, como los bits altos de `Arranque2.lean`. -/

section Resta

/-- **`a < 1 # a` en todo modelo de S¹₂.** Es `Arranque2.lt_smash_uno` con PIND para `Πᵇ₁` de S¹₂ (`pind_pi`) en
lugar de la de T¹₂. -/
theorem lt_smash_uno_s12 (hM : EsModeloS12 M) (a : M) : ¬ le (smash uno a) a := by
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
  refine (hr a).1 (pind_pi hM 0 B hB default ((hr cero).2 base) (fun x hx => ?_) a)
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

/-- **El paso de la resta.** Si `b + d·(2Q) ≤ a < b + Sd·(2Q)`, alguno de `2d`, `2d + 1` cumple lo mismo con `Q`.
Es `Arranque2.paso_bits` corrido en `b`. -/
theorem paso_resta (h : EsModeloBASIC M) (a b d Q : M) (h1 : le (suma b (prod d (doble Q))) a)
    (h2 : ¬ le (suma b (prod (suc d) (doble Q))) a) :
    ∃ d', le (suma b (prod d' Q)) a ∧ ¬ le (suma b (prod (suc d') Q)) a := by
  have dQ : doble Q = suma Q Q := doble_eq_suma h Q
  have dy : doble d = suma d d := doble_eq_suma h d
  have e1 : prod d (doble Q) = prod (doble d) Q := by
    rw [dQ, dy, h.b29, h.b28 (suma d d), h.b29, h.b28 Q d]
  have e2 : prod (suc d) (doble Q) = prod (suc (suc (doble d))) Q := by
    rw [h.b28 (suc d), h.b27, h.b28 (suc (suc (doble d))), h.b27, h.b27, h.b28 (doble Q) d, e1,
      h.b28 (doble d) Q, dQ, h.b24]
  rcases em (le (suma b (prod (suc (doble d)) Q)) a) with hle | hle
  · exact ⟨suc (doble d), hle, by rw [← e2]; exact h2⟩
  · exact ⟨doble d, by rw [← e1]; exact h1, hle⟩

/-- `b + y = b + z → y = z`, en BASIC (axioma 25 en las dos direcciones). -/
theorem suma_cancela (h : EsModeloBASIC M) {b y z : M} (e : suma b y = suma b z) : y = z :=
  h.b7 _ _ ((h.b25 b y z).1 (e ▸ le_refl' h _)) ((h.b25 b z y).1 (e ▸ le_refl' h _))

/-- **La resta existe en S¹₂**: si `b ≤ a`, hay `d` con `b + d = a`. Por LIND sobre `u ≤ |a|` con la fórmula `Σᵇ₁`
`u ≤ |a| → ∃ w ≤ a ∃ d ≤ a (|w| + u ≤ |a| ∧ b + d·(1#w) ≤ a ∧ ¬(b + Sd·(1#w) ≤ a))`: en `u = 0` sirven `w = a`,
`d = 0` (porque `a < 1 # a`); en cada vuelta `w` pasa a `⌊w/2⌋` y `d` a `2d` o `2d + 1`; en `u = |a|`, `w = 0`,
`1 # 0 = 1`, y `b + d ≤ a < S(b + d)` dice `b + d = a`. -/
theorem resta_existe (hM : EsModeloS12 M) (a b : M) (hb : le b a) : ∃ d, suma b d = a := by
  have h := hM.basic
  -- variables libres: u = 0, a = 1, b = 2; ligadas: w = inr 0, d = inr 1
  let U : L.Term (Fin 3 ⊕ Fin 2) := Term.var (Sum.inl 0)
  let A : L.Term (Fin 3 ⊕ Fin 2) := Term.var (Sum.inl 1)
  let Bt : L.Term (Fin 3 ⊕ Fin 2) := Term.var (Sum.inl 2)
  let W : L.Term (Fin 3 ⊕ Fin 2) := Term.var (Sum.inr 0)
  let D : L.Term (Fin 3 ⊕ Fin 2) := Term.var (Sum.inr 1)
  let body : L.BoundedFormula (Fin 3) 2 :=
    leF (tMs (tLong W) U) (tLong A) ⊓ (leF (tMs Bt (tPr D (tSm tU W))) A ⊓
      (leF (tMs Bt (tPr (tSc D) (tSm tU W))) A).not)
  let inner : L.BoundedFormula (Fin 3) 1 := existeAcotado (Term.var (Sum.inl 1)) body
  let outer : L.Formula (Fin 3) := existeAcotado (Term.var (Sum.inl 1)) inner
  let ψ : L.Formula (Fin 3) := (leF (Term.var (Sum.inl 0)) (tLong (Term.var (Sum.inl 1)))).imp outer
  have hψ : EsSigma1 ψ :=
    .imp (.aguda (.rel _ _)) (.existe _ (.existe _ (.y (.aguda (.rel _ _)) (.y (.aguda (.rel _ _))
      (.aguda (.imp (.rel _ _) .falso))))))
  have hr : ∀ u : M, ψ.Realize (Fin.cons u ![a, b]) ↔ (le u (long a) →
      ∃ w, le w a ∧ ∃ d, le d a ∧ le (suma (long w) u) (long a) ∧
        le (suma b (prod d (smash uno w))) a ∧ ¬ le (suma b (prod (suc d) (smash uno w))) a) := by
    intro u
    have ha : (Fin.cons u ![a, b] : Fin 3 → M) 1 = a := rfl
    rw [Formula.Realize, BoundedFormula.realize_imp, Parikh.realize_leF, realize_tLong]
    simp only [Term.realize_var, Sum.elim_inl, ha]
    refine imp_congr_right fun _ => ?_
    rw [Parikh.realize_existe]
    simp only [Term.realize_var, Sum.elim_inl, ha]
    refine exists_congr fun w => and_congr_right fun _ => ?_
    rw [Parikh.realize_existe]
    simp only [Term.realize_var, Sum.elim_inl, ha]
    refine exists_congr fun d => and_congr_right fun _ => ?_
    let E := Sum.elim (Fin.cons u ![a, b] : Fin 3 → M) (Fin.snoc (Fin.snoc default w) d : Fin 2 → M)
    have eW : W.realize E = w := rfl
    have eD : D.realize E = d := rfl
    have eU : U.realize E = u := rfl
    have eA : A.realize E = a := rfl
    have eB : Bt.realize E = b := rfl
    have eP : (tSm tU W).realize E = smash uno w := by
      simp only [tSm, tU, tSc, Term.realize_functions_apply₂, Term.realize_functions_apply₁, realize_tC, eW]; rfl
    have e1 : (tMs (tLong W) U).realize E = suma (long w) u := by
      rw [tMs, Term.realize_functions_apply₂, realize_tLong, eW, eU]; rfl
    have e2 : (tLong A).realize E = long a := by rw [realize_tLong, eA]
    have e3 : (tMs Bt (tPr D (tSm tU W))).realize E = suma b (prod d (smash uno w)) := by
      rw [tMs, Term.realize_functions_apply₂, tPr, Term.realize_functions_apply₂, eP, eD, eB]; rfl
    have e4 : (tMs Bt (tPr (tSc D) (tSm tU W))).realize E = suma b (prod (suc d) (smash uno w)) := by
      rw [tMs, Term.realize_functions_apply₂, tPr, Term.realize_functions_apply₂, eP, tSc,
        Term.realize_functions_apply₁, eD, eB]; rfl
    simp only [body, BoundedFormula.realize_inf, BoundedFormula.realize_not, Parikh.realize_leF]
    change le ((tMs (tLong W) U).realize E) ((tLong A).realize E) ∧
      le ((tMs Bt (tPr D (tSm tU W))).realize E) (A.realize E) ∧
      ¬ le ((tMs Bt (tPr (tSc D) (tSm tU W))).realize E) (A.realize E) ↔ _
    rw [e1, e2, e3, e4, eA]
  have key := lind hM 2 ψ hψ ![a, b]
    ((hr cero).2 fun _ => ⟨a, le_refl' h a, cero, h.b3 a, by rw [h.b22]; exact le_refl' h _,
      by rw [prod_cero_izq h, h.b22]; exact hb,
      by
        rw [h.b28]
        change ¬ le (suma b (prod (smash uno a) uno)) a
        rw [prod_uno h]
        intro hle
        exact lt_smash_uno_s12 hM a (h.b8 _ _ _ (le_suma_der h _ _) hle)⟩)
    (fun u hu => by
      rw [hr] at hu ⊢
      intro hSu
      obtain ⟨w, hwa, d, hda, hl, h1, h2⟩ := hu (h.b8 _ _ _ (le_suc h u) hSu)
      by_cases hw0 : w = cero
      · refine ⟨w, hwa, d, hda, ?_, h1, h2⟩
        rw [hw0, h.b9, suma_cero_izq h]; exact hSu
      · have hl' : le (suma (long (mitad w)) (suc u)) (long a) := by
          rw [suma_suc_conm h, ← h.b31 w hw0]; exact hl
        rw [smash_uno_mitad h w hw0] at h1 h2
        obtain ⟨d', h1', h2'⟩ := paso_resta h a b d _ h1 h2
        have hQ : le uno (smash uno (mitad w)) := uno_le_smash h _ _
        have hd'a : le d' a := by
          have : le (prod d' uno) (prod d' (smash uno (mitad w))) := prod_mono_der h _ _ _ hQ
          rw [prod_uno h] at this
          exact h.b8 _ _ _ (h.b8 _ _ _ this (le_suma_der h _ _)) h1'
        exact ⟨mitad w, h.b8 _ _ _ (mitad_le h w) hwa, d', hd'a, hl', h1', h2'⟩) a
  obtain ⟨w, -, d, -, hl, h1, h2⟩ := (hr (long a)).1 key (le_refl' h _)
  have hlw : long w = cero := by
    have : le (suma (long a) (long w)) (suma (long a) cero) := by rw [h.b21, h.b22]; exact hl
    exact h.b7 _ _ ((h.b25 _ _ _).1 this) (h.b3 _)
  have hw : w = cero := by
    by_contra hw
    exact suc_ne_cero h _ ((h.b31 w hw).symm.trans hlw)
  rw [hw, smash_uno_cero h, prod_uno h] at h1
  rw [hw, smash_uno_cero h, prod_uno h, h.b23] at h2
  refine ⟨d, ?_⟩
  by_contra hne
  exact h2 ((h.b4 _ _).1 ⟨h1, hne⟩)

/-- `(x₀ ≤ x₁ ∧ y = 0) ∨ x₁ + y = x₀`: el gráfico de `x₀ ∸ x₁`. -/
def grafoResta : L.Formula (Fin 3) :=
  (Relations.formula₂ (Rel.le : L.Relations 2) (vx 0) (vx 1) ⊓ Term.equal (vy 2) tC) ⊔
    Term.equal (tMs (vx 1) (vy 2)) (vx 0)

theorem esSigma1_grafoResta : EsSigma1 grafoResta :=
  .o (.y (.aguda (.rel _ _)) (.aguda (.igual _ _))) (.aguda (.igual _ _))

theorem realize_grafoResta (x : Fin 2 → M) (y : M) :
    grafoResta.Realize (Fin.snoc x y : Fin 3 → M) ↔ (le (x 0) (x 1) ∧ y = cero) ∨ suma (x 1) y = x 0 := by
  simp only [grafoResta, Formula.realize_sup, Formula.realize_inf, Formula.realize_rel₂, Formula.realize_equal,
    realize_tC, tMs, Term.realize_functions_apply₂]
  rw [realize_vx, realize_vx, realize_vy]
  rfl

/-- **La resta truncada es definible**, con la cota `x₀`. -/
theorem resta_definible : DefinibleN 2 (fun v => v 0 - v 1) := by
  refine ⟨grafoResta, esSigma1_grafoResta, Term.var 0, fun M _ hM => ⟨fun x => ?_, ?_⟩, ?_⟩
  · have h := hM.basic
    simp only [Term.realize_var]
    rcases h.b6 (x 1) (x 0) with h10 | h01
    · exact ⟨cero, h.b3 _, (realize_grafoResta x _).2 (.inl ⟨h10, rfl⟩)⟩
    · obtain ⟨d, hd⟩ := resta_existe hM (x 0) (x 1) h01
      exact ⟨d, hd ▸ le_suma_der h _ _, (realize_grafoResta x _).2 (.inr hd)⟩
  · intro x y z hy hz
    have h := hM.basic
    -- si `x₀ ≤ x₁` y `x₁ + z = x₀`, entonces `x₀ = x₁` y `z = 0`
    have cero_de : ∀ z : M, le (x 0) (x 1) → suma (x 1) z = x 0 → z = cero := by
      intro z hle e
      have e' : x 0 = x 1 := h.b7 _ _ hle (e ▸ h.b19 _ _)
      exact suma_cancela h (e.trans (e'.trans (h.b22 _).symm))
    rw [realize_grafoResta] at hy hz
    rcases hy with ⟨hle, rfl⟩ | hy <;> rcases hz with ⟨hle', rfl⟩ | hz
    · rfl
    · exact (cero_de z hle hz).symm
    · exact cero_de y hle' hy
    · exact suma_cancela h (hy.trans hz.symm)
  · intro v
    rw [realize_grafoResta]
    by_cases hle : v 0 ≤ v 1
    · exact .inl ⟨hle, by simp; omega⟩
    · exact .inr (by simp; omega)

end Resta

/-! ## La composición -/

section Composicion

/-- `∃ z₀ ≤ t₀ … ∃ z_{k-1} ≤ t_{k-1}, φ`, con las cotas en las variables libres. -/
def existenAcotados {α : Type} : (k : ℕ) → (Fin k → L.Term α) → L.BoundedFormula α k → L.Formula α
  | 0, _, φ => φ
  | k + 1, ts, φ =>
      existenAcotados k (fun i => ts (Fin.castSucc i)) (existeAcotado ((ts (Fin.last k)).relabel Sum.inl) φ)

theorem esSigma1_existenAcotados {α : Type} :
    ∀ (k : ℕ) (ts : Fin k → L.Term α) {φ : L.BoundedFormula α k}, EsSigma1 φ → EsSigma1 (existenAcotados k ts φ)
  | 0, _, _, h => h
  | k + 1, _, _, h => esSigma1_existenAcotados k _ (.existe _ h)

theorem realize_existenAcotados {α : Type} (v : α → M) :
    ∀ (k : ℕ) (ts : Fin k → L.Term α) (φ : L.BoundedFormula α k),
      (existenAcotados k ts φ).Realize v ↔ ∃ zs : Fin k → M, (∀ i, le (zs i) ((ts i).realize v)) ∧ φ.Realize v zs
  | 0, ts, φ => by
    simp only [existenAcotados, Formula.Realize]
    refine ⟨fun h => ⟨default, fun i => i.elim0, h⟩, fun ⟨zs, _, h⟩ => ?_⟩
    rwa [Subsingleton.elim zs default] at h
  | k + 1, ts, φ => by
    rw [existenAcotados, realize_existenAcotados v k]
    constructor
    · rintro ⟨zs, hzs, hφ⟩
      rw [Parikh.realize_existe] at hφ
      obtain ⟨z, hz, hφ⟩ := hφ
      refine ⟨Fin.snoc zs z, fun i => ?_, hφ⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
        rwa [Term.realize_relabel, Sum.elim_comp_inl] at hz
      · rw [Fin.snoc_castSucc]; exact hzs j
    · rintro ⟨zs, hzs, hφ⟩
      refine ⟨Fin.init zs, fun i => hzs _, ?_⟩
      rw [Parikh.realize_existe]
      refine ⟨zs (Fin.last k), ?_, ?_⟩
      · rw [Term.realize_relabel, Sum.elim_comp_inl]; exact hzs _
      · rwa [Fin.snoc_init_self]

/-- `φ₀ ∧ … ∧ φ_{m-1}`. -/
def conj {α : Type} {k : ℕ} : (m : ℕ) → (Fin m → L.BoundedFormula α k) → L.BoundedFormula α k
  | 0, _ => ⊤
  | m + 1, φs => φs 0 ⊓ conj m (fun i => φs i.succ)

theorem esSigma1_conj {α : Type} {k : ℕ} :
    ∀ (m : ℕ) (φs : Fin m → L.BoundedFormula α k), (∀ i, EsSigma1 (φs i)) → EsSigma1 (conj m φs)
  | 0, _, _ => .aguda (.imp .falso .falso)
  | m + 1, _, h => .y (h 0) (esSigma1_conj m _ fun i => h i.succ)

theorem realize_conj {α : Type} {k : ℕ} (v : α → M) (xs : Fin k → M) :
    ∀ (m : ℕ) (φs : Fin m → L.BoundedFormula α k), (conj m φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs
  | 0, _ => by simp only [conj, BoundedFormula.realize_top, true_iff]; exact fun i => i.elim0
  | m + 1, φs => by
    rw [conj, BoundedFormula.realize_inf, realize_conj v xs m]
    exact ⟨fun ⟨h0, hs⟩ i => Fin.cases h0 hs i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

variable {n m : ℕ}

/-- Las variables de `φ_{gᵢ}(x⃗, y)`, dentro del cuerpo: `x⃗` queda libre, `y` pasa a la ligada `zᵢ`. -/
def relG (i : Fin m) : Fin (n + 1) → Fin (n + 1) ⊕ Fin m :=
  Fin.lastCases (Sum.inr i) (fun j => Sum.inl (Fin.castSucc j))

/-- Las variables de `φ_f(z⃗, y)`, dentro del cuerpo: `z⃗` son las ligadas, `y` la última libre. -/
def relF : Fin (m + 1) → Fin (n + 1) ⊕ Fin m :=
  Fin.lastCases (Sum.inl (Fin.last n)) (fun j => Sum.inr j)

/-- **El gráfico de la composición**: `∃ z⃗ ≤ t⃗(x⃗) (⋀ᵢ φ_{gᵢ}(x⃗, zᵢ) ∧ φ_f(z⃗, y))`. -/
def grafoComp (φf : L.Formula (Fin (m + 1))) (φg : Fin m → L.Formula (Fin (n + 1))) (tg : Fin m → L.Term (Fin n)) :
    L.Formula (Fin (n + 1)) :=
  existenAcotados m (fun i => (tg i).relabel Fin.castSucc)
    (conj m (fun i => BoundedFormula.relabel (relG i) (φg i)) ⊓ BoundedFormula.relabel (relF (n := n)) φf)

theorem esSigma1_grafoComp {φf : L.Formula (Fin (m + 1))} {φg : Fin m → L.Formula (Fin (n + 1))}
    (tg : Fin m → L.Term (Fin n)) (hf : EsSigma1 φf) (hg : ∀ i, EsSigma1 (φg i)) :
    EsSigma1 (grafoComp φf φg tg) :=
  esSigma1_existenAcotados _ _ (.y (esSigma1_conj _ _ fun i => Arranque.EsSigma1.relabel _ (hg i)) (Arranque.EsSigma1.relabel _ hf))

theorem realize_grafoComp (φf : L.Formula (Fin (m + 1))) (φg : Fin m → L.Formula (Fin (n + 1)))
    (tg : Fin m → L.Term (Fin n)) (x : Fin n → M) (y : M) :
    (grafoComp φf φg tg).Realize (Fin.snoc x y : Fin (n + 1) → M) ↔
      ∃ zs : Fin m → M, (∀ i, le (zs i) ((tg i).realize x)) ∧
        (∀ i, (φg i).Realize (Fin.snoc x (zs i) : Fin (n + 1) → M)) ∧
        φf.Realize (Fin.snoc zs y : Fin (m + 1) → M) := by
  rw [grafoComp, realize_existenAcotados]
  refine exists_congr fun zs => ?_
  have et : ∀ i, ((tg i).relabel Fin.castSucc).realize (Fin.snoc x y : Fin (n + 1) → M) = (tg i).realize x := by
    intro i; rw [Term.realize_relabel, Fin.snoc_comp_castSucc]
  simp only [et]
  refine and_congr_right fun _ => ?_
  rw [BoundedFormula.realize_inf, realize_conj]
  refine and_congr ?_ ?_
  · refine forall_congr' fun i => ?_
    rw [BoundedFormula.realize_relabel, Formula.Realize]
    have e : (Sum.elim (Fin.snoc x y : Fin (n + 1) → M) (zs ∘ Fin.castAdd 0) ∘ relG i) =
        (Fin.snoc x (zs i) : Fin (n + 1) → M) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [relG, Function.comp_apply, Fin.lastCases_last, Sum.elim_inr, Fin.snoc_last]; rfl
      · simp only [relG, Function.comp_apply, Fin.lastCases_castSucc, Sum.elim_inl, Fin.snoc_castSucc]
    rw [e]
    exact iff_of_eq (by congr 1; exact Subsingleton.elim _ _)
  · rw [BoundedFormula.realize_relabel, Formula.Realize]
    have e : (Sum.elim (Fin.snoc x y : Fin (n + 1) → M) (zs ∘ Fin.castAdd 0) ∘ relF) =
        (Fin.snoc zs y : Fin (m + 1) → M) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [relF, Function.comp_apply, Fin.lastCases_last, Sum.elim_inl, Fin.snoc_last]
      · simp only [relF, Function.comp_apply, Fin.lastCases_castSucc, Sum.elim_inr, Fin.snoc_castSucc]; rfl
    rw [e]
    exact iff_of_eq (by congr 1; exact Subsingleton.elim _ _)

/-- **La composición conserva la definibilidad.** Con `φ_f`, `t_f` para `f` y `φ_{gᵢ}`, `tᵢ` para cada `gᵢ`, la
composición se define con `grafoComp` y la cota `t_f(t₀(x⃗), …, t_{m-1}(x⃗))`. Que la cota acota es la monotonía de
`t_f` (`termino_mono`). La unicidad: los `zᵢ` son únicos por la de cada `gᵢ`, y entonces `y` por la de `f`. En ℕ, los
`zᵢ` son `gᵢ(x⃗)`, que caben bajo `tᵢ(x⃗)` porque ℕ es modelo de S¹₂. -/
theorem comp_definible {F : (Fin m → ℕ) → ℕ} {G : Fin m → (Fin n → ℕ) → ℕ} (hF : DefinibleN m F)
    (hG : ∀ i, DefinibleN n (G i)) : DefinibleN n (fun v => F (fun i => G i v)) := by
  obtain ⟨φf, hφf, tf, hMf, hNf⟩ := hF
  choose φg hφg tg hMg hNg using hG
  refine ⟨grafoComp φf φg tg, esSigma1_grafoComp tg hφf hφg, tf.subst tg,
    fun M _ hM => ⟨fun x => ?_, fun x y y' hy hy' => ?_⟩, fun v => ?_⟩
  · choose zs hzs hφz using fun i => ((hMg i) M hM).1 x
    obtain ⟨y, hy, hφy⟩ := (hMf M hM).1 zs
    refine ⟨y, ?_, (realize_grafoComp φf φg tg x y).2 ⟨zs, hzs, hφz, hφy⟩⟩
    rw [Term.realize_subst]
    exact hM.basic.b8 _ _ _ hy (termino_mono hM tf _ _ hzs)
  · rw [realize_grafoComp] at hy hy'
    obtain ⟨zs, -, hz, hφ⟩ := hy
    obtain ⟨zs', -, hz', hφ'⟩ := hy'
    have e : zs = zs' := funext fun i => ((hMg i) M hM).2 x _ _ (hz i) (hz' i)
    subst e
    exact (hMf M hM).2 zs y y' hφ hφ'
  · rw [realize_grafoComp]
    refine ⟨fun i => G i v, fun i => ?_, fun i => hNg i v, hNf _⟩
    obtain ⟨z, hz, hφz⟩ := ((hMg i) ℕ nat_esModeloS12).1 v
    have : z = G i v := ((hMg i) ℕ nat_esModeloS12).2 v _ _ hφz (hNg i v)
    rw [this] at hz; exact hz

end Composicion

/-! ## Los programas de Cobham -/

section Programas

open Cobham (Cob)

theorem cero_definible {n : ℕ} : DefinibleN n (Cob.cero : Cob n).eval :=
  (termino_definible (n := n) tC).congr fun _ => rfl

theorem proy_definible {n : ℕ} (i : Fin n) : DefinibleN n (Cob.proy i).eval :=
  (termino_definible (Term.var i)).congr fun _ => rfl

theorem suc_definible : DefinibleN 1 Cob.suc.eval :=
  (termino_definible (tSc (Term.var 0))).congr fun _ => rfl

theorem suma_definible : DefinibleN 2 Cob.suma.eval :=
  (termino_definible (tMs (Term.var 0) (Term.var 1))).congr fun _ => rfl

theorem prod_definible : DefinibleN 2 Cob.prod.eval :=
  (termino_definible (tPr (Term.var 0) (Term.var 1))).congr fun _ => rfl

theorem mitad_definible : DefinibleN 1 Cob.mitad.eval :=
  (termino_definible (tMt (Term.var 0))).congr fun _ => rfl

theorem largo_definible : DefinibleN 1 Cob.largo.eval :=
  (termino_definible (tLg (Term.var 0))).congr fun _ => rfl

theorem smash_definible : DefinibleN 2 Cob.smash.eval :=
  (termino_definible (tSm (Term.var 0) (Term.var 1))).congr fun _ => rfl

/-- **Programas sin recursión**: los que solo usan las básicas y la composición. -/
inductive SinRn : ∀ {n : ℕ}, Cob n → Prop
  | cero {n : ℕ} : SinRn (Cob.cero : Cob n)
  | proy {n : ℕ} (i : Fin n) : SinRn (Cob.proy i)
  | suc : SinRn Cob.suc
  | suma : SinRn Cob.suma
  | resta : SinRn Cob.resta
  | prod : SinRn Cob.prod
  | mitad : SinRn Cob.mitad
  | largo : SinRn Cob.largo
  | smash : SinRn Cob.smash
  | cond : SinRn Cob.cond
  | comp {n m : ℕ} (f : Cob m) (gs : Fin m → Cob n) : SinRn f → (∀ i, SinRn (gs i)) → SinRn (Cob.comp f gs)

/-- **Todo programa de Cobham sin recursión es `Σᵇ₁`-definible en S¹₂.** Las básicas son términos, la resta o el
condicional; la composición conserva la definibilidad. -/
theorem sinRn_definible : ∀ {n : ℕ} {c : Cob n}, SinRn c → DefinibleN n c.eval
  | _, _, .cero => cero_definible
  | _, _, .proy i => proy_definible i
  | _, _, .suc => suc_definible
  | _, _, .suma => suma_definible
  | _, _, .resta => resta_definible
  | _, _, .prod => prod_definible
  | _, _, .mitad => mitad_definible
  | _, _, .largo => largo_definible
  | _, _, .smash => smash_definible
  | _, _, .cond => cond_definible
  | _, _, .comp _ gs hf hg =>
    (comp_definible (G := fun i => (gs i).eval) (sinRn_definible hf) (fun i => sinRn_definible (hg i))).congr
      fun _ => rfl

/-- **La recursión sobre la notación con tope conserva la definibilidad.** Si `g`, `h` y `k` son `Σᵇ₁`-definibles en
S¹₂, también lo es `F(0, ȳ) = g(ȳ)`, `F(x, ȳ) = min (h(x, F(⌊x/2⌋, ȳ), ȳ)) (k(x, ȳ))`. Abierto aquí; es un teorema
conocido (Buss 1986: la recursión limitada sobre la notación, con la sucesión de valores intermedios codificada en
un número por medio de `#`). Lo que falta: codificar en S¹₂ la sucesión `F(⌊x/2^{|x|-j}⌋, ȳ)`, `j ≤ |x|`, como un
solo número acotado por un término (cada valor mide a lo sumo `|k|` bits, así que la sucesión entera mide
`(|x| + 1)·|k|` bits), probar por LIND que existe (con la existencia de cada paso, por la definibilidad de `h` y `k`,
y el `min` por la de la resta) y que es única. -/
def RecursionDefinible : Prop :=
  ∀ {n : ℕ} (g : Cob n) (h : Cob (n + 2)) (k : Cob (n + 1)),
    DefinibleN n g.eval → DefinibleN (n + 2) h.eval → DefinibleN (n + 1) k.eval →
      DefinibleN (n + 1) (Cob.rn g h k).eval

/-- **Con la recursión, todo programa de Cobham es `Σᵇ₁`-definible en S¹₂.** -/
theorem cob_definible (hrn : RecursionDefinible) : ∀ {n : ℕ} (c : Cob n), DefinibleN n c.eval
  | _, .cero => cero_definible
  | _, .proy i => proy_definible i
  | _, .suc => suc_definible
  | _, .suma => suma_definible
  | _, .resta => resta_definible
  | _, .prod => prod_definible
  | _, .mitad => mitad_definible
  | _, .largo => largo_definible
  | _, .smash => smash_definible
  | _, .cond => cond_definible
  | _, .comp f gs =>
    (comp_definible (G := fun i => (gs i).eval) (cob_definible hrn f) (fun i => cob_definible hrn (gs i))).congr
      fun _ => rfl
  | _, .rn g h k => hrn g h k (cob_definible hrn g) (cob_definible hrn h) (cob_definible hrn k)

/-- Un programa de un argumento, definible, da una función `Σᵇ₁`-definible en el sentido de `Definibles.lean`. -/
theorem definibleSigma1_de_cob (c : Cob 1) (hc : DefinibleN 1 c.eval) : DefinibleSigma1 (fun n => c.eval ![n]) :=
  definibleSigma1_de_uno (hc.congr fun v => congrArg c.eval (fin1_eq v).symm)

/-- **El predecesor `n ↦ n ∸ 1` es `Σᵇ₁`-definible en S¹₂**, sin hipótesis. Es un ejemplo que pasa por la resta,
cuya existencia S¹₂ no trae como axioma. -/
theorem definible_pred : DefinibleSigma1 (fun n => n - 1) := by
  let c : Cob 1 := Cobham.c2 Cob.resta (Cob.proy 0) Cobham.uno
  have hc : SinRn c := .comp _ _ .resta fun i => by
    match i with
    | 0 => exact .proy 0
    | 1 => exact .comp _ _ .suc fun j => by match j with | 0 => exact .cero
  have := definibleSigma1_de_cob c (sinRn_definible hc)
  exact this

/-! ## La dirección fácil y el teorema de Buss, con lo abierto como hipótesis -/

/-- **Máquinas → Cobham** (Cobham 1965): toda función `ℕ → ℕ` de tiempo polinomial (en las máquinas de Mathlib, con
los números en binario) es un programa de `Cob`. Abierto aquí; es un teorema conocido. complexitylib-v1 lo prueba
(`FP_subset_CobhamFP`) para cadenas y con su propio modelo de máquina; ver el encabezado del archivo. -/
def PolinomialEsCobham : Prop :=
  ∀ f : ℕ → ℕ, EsPolinomial f → ∃ c : Cob 1, ∀ n : ℕ, c.eval ![n] = f n

/-- **La dirección fácil del teorema de Buss**, con las dos piezas abiertas como hipótesis: máquinas → Cobham
(`PolinomialEsCobham`) y la recursión (`RecursionDefinible`). Todo lo demás está probado. -/
theorem polinomialEsDefinible_de (ha : PolinomialEsCobham) (hrn : RecursionDefinible) : PolinomialEsDefinible := by
  intro f hf
  obtain ⟨c, hc⟩ := ha f hf
  have := definibleSigma1_de_cob c (cob_definible hrn c)
  rwa [show (fun n => c.eval ![n]) = f from funext hc] at this

/-- **El teorema de Buss** (1986), con las mismas dos hipótesis: la dirección difícil está probada
(`Cobham.definibleEsPolinomial`). -/
theorem teoremaDeBuss_de (ha : PolinomialEsCobham) (hrn : RecursionDefinible) : TeoremaDeBuss :=
  teoremaDeBuss_iff.2 ⟨Cobham.definibleEsPolinomial, polinomialEsDefinible_de ha hrn⟩

end Programas

end DefinibleCobham
end Acotada
end Sagitta.Map
