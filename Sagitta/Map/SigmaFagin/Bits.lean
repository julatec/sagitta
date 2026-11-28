import Sagitta.Map.Teoria
import Sagitta.Map.Parikh
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fase A de Σᵇ₁ = NP: el bit como fórmula

Primera fase del plan (cerrar `SigmaIgualNP` por el teorema de Fagin de cslib-frontier).
Para traducir una sentencia existencial de segundo orden a una fórmula `Σᵇ₁` sobre ℕ hace falta, antes que nada,
**leer un bit** y **guardar una relación como un número**. Esto es lo que se prueba aquí, todo en el modelo estándar ℕ.

## Lo que se prueba

* `potF j z` («`z = 2^j`») es **sin cuantificadores**: `z = 1 # ⌊z/2⌋ ∧ |⌊z/2⌋| = j`. El truco es el de `Arranque2.lean`
  (`1 # w = 2^{|w|}`), con `w = ⌊z/2⌋`, que no hay que adivinar. `potF_aguda`, `realize_potF`. Como es aguda, su negación
  también lo es (`aguda_not`): «ser `2^j`» es `Δᵇ₀`.
* `bitF j y` («el bit `j` de `y` es 1») es `Σᵇ₁` (`bitF_sigma`), con las tres cotas iguales al término `y`:
  `∃ p ≤ y (p = 2^j ∧ ∃ q ≤ y ∃ r ≤ y (y = (2q+1)·p + r ∧ r < p))`. `realize_bitF`: significa `y.testBit j = true`.
* `noBitF j y` («el bit `j` de `y` es 0») también es `Σᵇ₁` (`noBitF_sigma`): `|y| ≤ j ∨ ∃ p ≤ y (p = 2^j ∧ ∃ q ≤ y
  ∃ r ≤ y (y = 2q·p + r ∧ r < p))`. `realize_noBitF`: significa `y.testBit j = false`. Así el bit es `Δᵇ₁` sobre ℕ
  (`bitF_delta`: las dos se excluyen y cubren todo). Las versiones con dos variables libres, `bit2` y `noBit2`
  (`realize_bit2 : bit2.Realize ![j, y] ↔ y.testBit j = true`), y `pot2` (`realize_pot2 : pot2.Realize ![j, z] ↔ z = 2^j`).
* Las relaciones como números. `idx n a = a₀ + n·(a₁ + n·(…))` numera las `k`-tuplas de `[0, n)` (`idx_lt`,
  `idx_inj`); `idxT` es el mismo número como término (`realize_idxT`). `codificar`: todo predicado sobre `[0, N)` es el
  conjunto de bits de un `y < 2^N`. **`relacion_codificada`**: toda relación `k`-aria sobre `[0, n)` es un `y < 2^(n^k)`
  con `R a ↔ y.testBit (idx n a)`. `pertF` / `noPertF` son la pertenencia y su negación como fórmulas `Σᵇ₁`
  (`realize_pertF`, `realize_noPertF`).
* La cota por términos. Cuando el universo es `[0, |x|)` (en Fagin sobre palabras, `n` es el largo de la entrada),
  `cotaRel k x = c_k(x) # 1`, con `c₀ = 1` y `c_{k+1} = x # c_k`, acota todo código: `lt_cotaRel`
  (`y < 2^(|x|^k) → y ≤ cotaRel k x`). Con `n = |x|`, **`relacion_acotada`** junta todo: la relación es un `y` que cabe
  debajo de un término y se lee con una fórmula `Σᵇ₁` cuya negación es `Σᵇ₁`.

## Lo que no se prueba

* Nada de esto se demuestra **dentro** de S¹₂: los significados son en ℕ. Para `SigmaIgualNP` basta ℕ (la definición
  de `DefinidoPor` es en el modelo estándar).
* Las fases B (traducir una sentencia ESO de cslib-frontier a `Σᵇ₁` e inducción sobre ella), C y D del plan.
* Si `n` no es un largo, `2^(n^k)` no se acota con un término de `n` (los términos crecen como `2^{poly(|n|)}`): por eso
  la cota se escribe para `n = |x|`. Es la razón de fondo por la que Fagin se usa sobre estructuras de palabra.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace SigmaFagin

open Acotada Acotada.Parikh

variable {α : Type} {m : ℕ}

/-! ## Agudas: negación, conjunción y disyunción -/

theorem aguda_not {φ : L.BoundedFormula α m} (h : EsAguda φ) : EsAguda φ.not :=
  EsAguda.imp h EsAguda.falso

theorem aguda_inf {φ ψ : L.BoundedFormula α m} (h1 : EsAguda φ) (h2 : EsAguda ψ) : EsAguda (φ ⊓ ψ) :=
  aguda_not (EsAguda.imp h1 (aguda_not h2))

theorem aguda_sup {φ ψ : L.BoundedFormula α m} (h1 : EsAguda φ) (h2 : EsAguda ψ) : EsAguda (φ ⊔ ψ) :=
  EsAguda.imp (aguda_not h1) h2

theorem aguda_leF (t u : L.Term (α ⊕ Fin m)) : EsAguda (leF t u) := EsAguda.rel _ _

/-! ## Términos en ℕ -/

section Nat

variable {β : Type} (v : β → ℕ)

@[simp] theorem rn_tC : (tC : L.Term β).realize v = 0 := realize_tC v
@[simp] theorem rn_tSc (t : L.Term β) : (tSc t).realize v = t.realize v + 1 := rfl
@[simp] theorem rn_tLg (t : L.Term β) : (tLg t).realize v = Nat.size (t.realize v) := rfl
@[simp] theorem rn_tMt (t : L.Term β) : (tMt t).realize v = t.realize v / 2 := rfl
@[simp] theorem rn_tMs (t u : L.Term β) : (tMs t u).realize v = t.realize v + u.realize v := rfl
@[simp] theorem rn_tPr (t u : L.Term β) : (tPr t u).realize v = t.realize v * u.realize v := rfl
@[simp] theorem rn_tSm (t u : L.Term β) :
    (tSm t u).realize v = 2 ^ (Nat.size (t.realize v) * Nat.size (u.realize v)) := rfl
@[simp] theorem rn_tU : (tU : L.Term β).realize v = 1 := by simp [tU]

end Nat

theorem realize_igual (t u : L.Term (α ⊕ Fin m)) (v : α → ℕ) (xs : Fin m → ℕ) :
    (BoundedFormula.equal t u).Realize v xs ↔ t.realize (Sum.elim v xs) = u.realize (Sum.elim v xs) := Iff.rfl

theorem realize_leF_nat (t u : L.Term (α ⊕ Fin m)) (v : α → ℕ) (xs : Fin m → ℕ) :
    (leF t u).Realize v xs ↔ t.realize (Sum.elim v xs) ≤ u.realize (Sum.elim v xs) := realize_leF t u v xs

/-! ## La potencia de dos, sin cuantificadores -/

/-- `z = 2^j`, escrito `z = 1 # ⌊z/2⌋ ∧ |⌊z/2⌋| = j`. -/
def potF (j z : L.Term (α ⊕ Fin m)) : L.BoundedFormula α m :=
  BoundedFormula.equal z (tSm tU (tMt z)) ⊓ BoundedFormula.equal (tLg (tMt z)) j

theorem potF_aguda (j z : L.Term (α ⊕ Fin m)) : EsAguda (potF j z) :=
  aguda_inf (EsAguda.igual _ _) (EsAguda.igual _ _)

theorem pot_iff (j z : ℕ) : (z = 2 ^ Nat.size (z / 2) ∧ Nat.size (z / 2) = j) ↔ z = 2 ^ j := by
  constructor
  · rintro ⟨h1, h2⟩; rw [h1, h2]
  · rintro rfl
    rcases j with _ | j
    · simp
    · have : 2 ^ (j + 1) / 2 = 2 ^ j := by rw [pow_succ]; simp
      rw [this, Nat.size_pow]
      exact ⟨rfl, rfl⟩

theorem realize_potF (j z : L.Term (α ⊕ Fin m)) (v : α → ℕ) (xs : Fin m → ℕ) :
    (potF j z).Realize v xs ↔ z.realize (Sum.elim v xs) = 2 ^ j.realize (Sum.elim v xs) := by
  rw [potF, BoundedFormula.realize_inf, realize_igual, realize_igual, ← pot_iff]
  simp [Nat.size_one]

/-! ## La aritmética del bit -/

theorem div_de (y c P r : ℕ) (hP : 0 < P) (h : y = c * P + r) (hr : r < P) : y / P = c := by
  subst h
  rw [show c * P + r = r + P * c by ring, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hr, zero_add]

theorem bit_uno_iff (y j : ℕ) :
    y.testBit j = true ↔ ∃ q r, y = (2 * q + 1) * 2 ^ j + r ∧ r < 2 ^ j := by
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  constructor
  · intro h
    refine ⟨y / 2 ^ j / 2, y % 2 ^ j, ?_, Nat.mod_lt _ hP⟩
    have e1 := Nat.div_add_mod y (2 ^ j)
    have e2 := Nat.div_add_mod (y / 2 ^ j) 2
    rw [h] at e2
    calc y = 2 ^ j * (y / 2 ^ j) + y % 2 ^ j := e1.symm
      _ = 2 ^ j * (2 * (y / 2 ^ j / 2) + 1) + y % 2 ^ j := by rw [e2]
      _ = (2 * (y / 2 ^ j / 2) + 1) * 2 ^ j + y % 2 ^ j := by ring
  · rintro ⟨q, r, h, hr⟩
    rw [div_de y _ _ r hP h hr]
    omega

theorem bit_cero_iff (y j : ℕ) :
    y.testBit j = false ↔ ∃ q r, y = (2 * q) * 2 ^ j + r ∧ r < 2 ^ j := by
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
  constructor
  · intro h
    refine ⟨y / 2 ^ j / 2, y % 2 ^ j, ?_, Nat.mod_lt _ hP⟩
    have e1 := Nat.div_add_mod y (2 ^ j)
    have e2 := Nat.div_add_mod (y / 2 ^ j) 2
    rw [show y / 2 ^ j % 2 = 0 by omega] at e2
    calc y = 2 ^ j * (y / 2 ^ j) + y % 2 ^ j := e1.symm
      _ = 2 ^ j * (2 * (y / 2 ^ j / 2) + 0) + y % 2 ^ j := by rw [e2]
      _ = (2 * (y / 2 ^ j / 2)) * 2 ^ j + y % 2 ^ j := by ring
  · rintro ⟨q, r, h, hr⟩
    rw [div_de y _ _ r hP h hr]
    omega

/-! ## El bit como fórmula `Σᵇ₁` -/

section Bit

variable (j y : L.Term (α ⊕ Fin m))

/-- Las cuatro variables dentro de los tres cuantificadores: `p`, `q`, `r` y los términos subidos. -/
def cuerpoBit (b : ℕ) : L.BoundedFormula α (m + 1 + 1 + 1) :=
  let p : L.Term (α ⊕ Fin (m + 1 + 1 + 1)) := Term.var (Sum.inr (Fin.castSucc (Fin.castSucc (Fin.last m))))
  let q : L.Term (α ⊕ Fin (m + 1 + 1 + 1)) := Term.var (Sum.inr (Fin.castSucc (Fin.last (m + 1))))
  let r : L.Term (α ⊕ Fin (m + 1 + 1 + 1)) := nueva
  let y3 : L.Term (α ⊕ Fin (m + 1 + 1 + 1)) := sube (sube (sube y))
  let dosq : L.Term (α ⊕ Fin (m + 1 + 1 + 1)) := tD q
  let c : L.Term (α ⊕ Fin (m + 1 + 1 + 1)) := if b = 1 then tSc dosq else dosq
  BoundedFormula.equal y3 (tMs (tPr c p) r) ⊓ leF (tSc r) p

/-- `∃ p ≤ y (p = 2^j ∧ ∃ q ≤ y ∃ r ≤ y (y = (2q+b)·p + r ∧ r < p))`. -/
def bloqueBit (b : ℕ) : L.BoundedFormula α m :=
  existeAcotado y (potF (sube j) nueva ⊓
    existeAcotado (sube y) (existeAcotado (sube (sube y)) (cuerpoBit y b)))

/-- «El bit `j` de `y` es 1». -/
def bitF : L.BoundedFormula α m := bloqueBit j y 1

/-- «El bit `j` de `y` es 0». -/
def noBitF : L.BoundedFormula α m := leF (tLg y) j ⊔ bloqueBit j y 0

theorem cuerpoBit_aguda (b : ℕ) : EsAguda (cuerpoBit y b : L.BoundedFormula α (m + 1 + 1 + 1)) :=
  aguda_inf (EsAguda.igual _ _) (aguda_leF _ _)

theorem bloqueBit_sigma (b : ℕ) : EsSigma1 (bloqueBit j y b) :=
  EsSigma1.existe _ (EsSigma1.y (EsSigma1.aguda (potF_aguda _ _))
    (EsSigma1.existe _ (EsSigma1.existe _ (EsSigma1.aguda (cuerpoBit_aguda _ _)))))

theorem bitF_sigma : EsSigma1 (bitF j y) := bloqueBit_sigma j y 1

theorem noBitF_sigma : EsSigma1 (noBitF j y) :=
  EsSigma1.o (EsSigma1.aguda (aguda_leF _ _)) (bloqueBit_sigma j y 0)

variable (v : α → ℕ) (xs : Fin m → ℕ)

theorem realize_bloqueBit (b : ℕ) (hb : b ≤ 1) :
    (bloqueBit j y b).Realize v xs ↔
      ∃ p ≤ y.realize (Sum.elim v xs), p = 2 ^ j.realize (Sum.elim v xs) ∧
        ∃ q ≤ y.realize (Sum.elim v xs), ∃ r ≤ y.realize (Sum.elim v xs),
          y.realize (Sum.elim v xs) = (2 * q + b) * p + r ∧ r < p := by
  simp only [bloqueBit, realize_existe, BoundedFormula.realize_inf, realize_potF, realize_sube, realize_nueva,
    le_nat, cuerpoBit, realize_igual, realize_leF_nat, tD, rn_tMs, rn_tPr, rn_tSc, Term.realize_var, Sum.elim_inr,
    Fin.snoc_castSucc, Fin.snoc_last]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> simp

theorem realize_bitF :
    (bitF j y).Realize v xs ↔ (y.realize (Sum.elim v xs)).testBit (j.realize (Sum.elim v xs)) = true := by
  rw [bitF, realize_bloqueBit j y v xs 1 le_rfl, bit_uno_iff]
  set Y := y.realize (Sum.elim v xs)
  set J := j.realize (Sum.elim v xs)
  have hP : 0 < 2 ^ J := Nat.two_pow_pos J
  constructor
  · rintro ⟨p, -, rfl, q, -, r, -, h, hr⟩
    exact ⟨q, r, h, hr⟩
  · rintro ⟨q, r, h, hr⟩
    have h1 : 2 ^ J ≤ Y := by rw [h]; nlinarith
    have h2 : q ≤ Y := by rw [h]; nlinarith
    exact ⟨2 ^ J, h1, rfl, q, h2, r, by omega, h, hr⟩

theorem realize_noBitF :
    (noBitF j y).Realize v xs ↔ (y.realize (Sum.elim v xs)).testBit (j.realize (Sum.elim v xs)) = false := by
  rw [noBitF, BoundedFormula.realize_sup, realize_leF_nat, realize_bloqueBit j y v xs 0 (by norm_num)]
  simp only [rn_tLg]
  set Y := y.realize (Sum.elim v xs)
  set J := j.realize (Sum.elim v xs)
  have hP : 0 < 2 ^ J := Nat.two_pow_pos J
  rw [Nat.size_le]
  constructor
  · rintro (h | ⟨p, -, rfl, q, -, r, -, h, hr⟩)
    · exact Nat.testBit_lt_two_pow h
    · exact (bit_cero_iff Y J).2 ⟨q, r, by simpa using h, hr⟩
  · intro hb
    by_cases hY : Y < 2 ^ J
    · exact Or.inl hY
    · right
      obtain ⟨q, r, h, hr⟩ := (bit_cero_iff Y J).1 hb
      have h2 : q ≤ Y := by
        rcases Nat.eq_zero_or_pos q with rfl | hq
        · omega
        · rw [h]; nlinarith
      exact ⟨2 ^ J, by omega, rfl, q, h2, r, by omega, by simpa using h, hr⟩

/-- El bit es `Δᵇ₁` sobre ℕ: `bitF` y `noBitF` son `Σᵇ₁` y una es la negación de la otra. -/
theorem bitF_delta :
    EsSigma1 (bitF j y) ∧ EsSigma1 (noBitF j y) ∧ ((noBitF j y).Realize v xs ↔ ¬ (bitF j y).Realize v xs) := by
  refine ⟨bitF_sigma j y, noBitF_sigma j y, ?_⟩
  rw [realize_noBitF, realize_bitF]
  simp

end Bit

/-! ## Con dos variables libres -/

/-- `y.testBit j`, con `j` la variable libre 0 e `y` la 1. -/
def bit2 : L.Formula (Fin 2) := bitF (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))
/-- El bit `j` de `y` es 0. -/
def noBit2 : L.Formula (Fin 2) := noBitF (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))
/-- `z = 2^j`, con `j` la variable libre 0 y `z` la 1. -/
def pot2 : L.Formula (Fin 2) := potF (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))

theorem realize_bit2 (j y : ℕ) : bit2.Realize ![j, y] ↔ y.testBit j = true := by
  unfold bit2 Formula.Realize
  rw [realize_bitF]; rfl

theorem realize_noBit2 (j y : ℕ) : noBit2.Realize ![j, y] ↔ y.testBit j = false := by
  unfold noBit2 Formula.Realize
  rw [realize_noBitF]; rfl

theorem realize_pot2 (j z : ℕ) : pot2.Realize ![j, z] ↔ z = 2 ^ j := by
  unfold pot2 Formula.Realize
  rw [realize_potF]; rfl

theorem bit2_sigma : EsSigma1 bit2 := bitF_sigma _ _
theorem noBit2_sigma : EsSigma1 noBit2 := noBitF_sigma _ _
theorem pot2_aguda : EsAguda pot2 := potF_aguda _ _

/-! ## Las relaciones como números -/

/-- El número de la tupla `a` en base `n`: `a₀ + n·(a₁ + n·(…))`. -/
def idx (n : ℕ) : ∀ {k : ℕ}, (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, a => a 0 + n * idx n (Fin.tail a)

theorem idx_lt (n : ℕ) : ∀ {k : ℕ} (a : Fin k → ℕ), (∀ i, a i < n) → idx n a < n ^ k
  | 0, _, _ => by simp [idx]
  | k + 1, a, h => by
    have h1 := idx_lt n (Fin.tail a) (fun i => h i.succ)
    have h0 := h 0
    simp only [idx, pow_succ]
    nlinarith

theorem idx_inj (n : ℕ) : ∀ {k : ℕ} (a b : Fin k → ℕ), (∀ i, a i < n) → (∀ i, b i < n) →
    idx n a = idx n b → a = b
  | 0, a, b, _, _, _ => funext fun i => i.elim0
  | k + 1, a, b, ha, hb, h => by
    simp only [idx] at h
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (ha 0)
    have e0 : a 0 = b 0 := by
      have := congrArg (· % n) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0), Nat.mod_eq_of_lt (hb 0)] at this
      exact this
    have et : idx n (Fin.tail a) = idx n (Fin.tail b) := by
      have := congrArg (· / n) h
      simp only [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (ha 0), Nat.div_eq_of_lt (hb 0), zero_add] at this
      exact this
    have := idx_inj n (Fin.tail a) (Fin.tail b) (fun i => ha i.succ) (fun i => hb i.succ) et
    funext i
    refine Fin.cases e0 (fun i => ?_) i
    exact congrFun this i

/-- Todo predicado sobre `[0, N)` es el conjunto de bits de un `y < 2^N`. -/
theorem codificar (P : ℕ → Prop) : ∀ N, ∃ y < 2 ^ N, ∀ i < N, (y.testBit i = true ↔ P i)
  | 0 => ⟨0, by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | N + 1 => by
    classical
    obtain ⟨y, hy, h⟩ := codificar P N
    by_cases hN : P N
    · refine ⟨2 ^ N + y, by rw [pow_succ]; omega, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Nat.testBit_two_pow_add_gt hi]; exact h i hi
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy]; simpa using hN
    · refine ⟨y, by rw [pow_succ]; omega, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h i hi
      · rw [Nat.testBit_lt_two_pow hy]; simpa using hN

/-- **Toda relación `k`-aria sobre `[0, n)` es un número** `y < 2^(n^k)`, que se lee con `testBit (idx n a)`. -/
theorem relacion_codificada (n k : ℕ) (R : (Fin k → ℕ) → Prop) :
    ∃ y < 2 ^ (n ^ k), ∀ a : Fin k → ℕ, (∀ i, a i < n) → (y.testBit (idx n a) = true ↔ R a) := by
  obtain ⟨y, hy, h⟩ := codificar (fun i => ∃ a : Fin k → ℕ, (∀ i, a i < n) ∧ idx n a = i ∧ R a) (n ^ k)
  refine ⟨y, hy, fun a ha => ?_⟩
  rw [h _ (idx_lt n a ha)]
  constructor
  · rintro ⟨b, hb, e, hR⟩
    rwa [idx_inj n b a hb ha e] at hR
  · exact fun hR => ⟨a, ha, rfl, hR⟩

/-- `idx` como término. -/
def idxT {β : Type} (nT : L.Term β) : ∀ {k : ℕ}, (Fin k → L.Term β) → L.Term β
  | 0, _ => tC
  | _ + 1, as => tMs (as 0) (tPr nT (idxT nT (Fin.tail as)))

theorem realize_idxT {β : Type} (w : β → ℕ) (nT : L.Term β) :
    ∀ {k : ℕ} (as : Fin k → L.Term β), (idxT nT as).realize w = idx (nT.realize w) (fun i => (as i).realize w)
  | 0, _ => by simp [idxT, idx]
  | k + 1, as => by
    simp only [idxT, idx, rn_tMs, rn_tPr]
    rw [realize_idxT w nT (Fin.tail as)]
    rfl

/-- «La tupla `as` está en la relación de código `y`» (universo `[0, n)`). -/
def pertF {k : ℕ} (yT nT : L.Term (α ⊕ Fin m)) (as : Fin k → L.Term (α ⊕ Fin m)) : L.BoundedFormula α m :=
  bitF (idxT nT as) yT

/-- «La tupla `as` no está en la relación de código `y`». -/
def noPertF {k : ℕ} (yT nT : L.Term (α ⊕ Fin m)) (as : Fin k → L.Term (α ⊕ Fin m)) : L.BoundedFormula α m :=
  noBitF (idxT nT as) yT

theorem pertF_sigma {k : ℕ} (yT nT : L.Term (α ⊕ Fin m)) (as : Fin k → L.Term (α ⊕ Fin m)) :
    EsSigma1 (pertF yT nT as) ∧ EsSigma1 (noPertF yT nT as) :=
  ⟨bitF_sigma _ _, noBitF_sigma _ _⟩

theorem realize_pertF {k : ℕ} (yT nT : L.Term (α ⊕ Fin m)) (as : Fin k → L.Term (α ⊕ Fin m)) (v : α → ℕ)
    (xs : Fin m → ℕ) :
    (pertF yT nT as).Realize v xs ↔ (yT.realize (Sum.elim v xs)).testBit
      (idx (nT.realize (Sum.elim v xs)) (fun i => (as i).realize (Sum.elim v xs))) = true := by
  rw [pertF, realize_bitF, realize_idxT]

theorem realize_noPertF {k : ℕ} (yT nT : L.Term (α ⊕ Fin m)) (as : Fin k → L.Term (α ⊕ Fin m)) (v : α → ℕ)
    (xs : Fin m → ℕ) :
    (noPertF yT nT as).Realize v xs ↔ (yT.realize (Sum.elim v xs)).testBit
      (idx (nT.realize (Sum.elim v xs)) (fun i => (as i).realize (Sum.elim v xs))) = false := by
  rw [noPertF, realize_noBitF, realize_idxT]

/-! ## La cota por términos -/

/-- `c₀ = 1`, `c_{k+1} = x # c_k`. -/
def cotaAux {β : Type} (x : L.Term β) : ℕ → L.Term β
  | 0 => tU
  | k + 1 => tSm x (cotaAux x k)

/-- `cotaRel k x = c_k(x) # 1 = 2^{|c_k(x)|}`. -/
def cotaRel {β : Type} (k : ℕ) (x : L.Term β) : L.Term β := tSm (cotaAux x k) tU

theorem size_cotaAux {β : Type} (w : β → ℕ) (x : L.Term β) :
    ∀ k, Nat.size (x.realize w) ^ k ≤ Nat.size ((cotaAux x k).realize w)
  | 0 => by simp [cotaAux, Nat.size_one]
  | k + 1 => by
    have ih := size_cotaAux w x k
    simp only [cotaAux, rn_tSm, Nat.size_pow, pow_succ]
    nlinarith

/-- **Todo código cabe debajo del término**: si `y < 2^(|x|^k)`, entonces `y ≤ cotaRel k x`. -/
theorem lt_cotaRel {β : Type} (w : β → ℕ) (x : L.Term β) (k y : ℕ) (hy : y < 2 ^ (Nat.size (x.realize w) ^ k)) :
    y ≤ (cotaRel k x).realize w := by
  simp only [cotaRel, rn_tSm, rn_tU, Nat.size_one, mul_one]
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (size_cotaAux w x k)
  omega

/-- **La relación acotada.** Con universo `[0, |x|)`, toda relación `k`-aria es un `y` que cabe debajo del término
`cotaRel k x`; si un término `yT` vale `y`, la pertenencia de una tupla de términos se lee con `pertF yT |x| as` y la
no pertenencia con `noPertF yT |x| as`, las dos `Σᵇ₁`. -/
theorem relacion_acotada {k : ℕ} (x : L.Term (α ⊕ Fin m)) (v : α → ℕ) (xs : Fin m → ℕ)
    (R : (Fin k → ℕ) → Prop) :
    ∃ y ≤ (cotaRel k x).realize (Sum.elim v xs), ∀ yT : L.Term (α ⊕ Fin m), yT.realize (Sum.elim v xs) = y →
      ∀ as : Fin k → L.Term (α ⊕ Fin m),
        (∀ i, (as i).realize (Sum.elim v xs) < Nat.size (x.realize (Sum.elim v xs))) →
          ((pertF yT (tLg x) as).Realize v xs ↔ R (fun i => (as i).realize (Sum.elim v xs))) ∧
          ((noPertF yT (tLg x) as).Realize v xs ↔ ¬ R (fun i => (as i).realize (Sum.elim v xs))) := by
  obtain ⟨y, hy, h⟩ := relacion_codificada (Nat.size (x.realize (Sum.elim v xs))) k R
  refine ⟨y, lt_cotaRel _ x k y hy, fun yT hyT as has => ?_⟩
  have e := h _ has
  rw [realize_pertF, realize_noPertF, hyT, rn_tLg]
  constructor
  · exact e
  · rw [← e]; simp

/-! ## Controles -/

example : bit2.Realize ![1, 2] := (realize_bit2 1 2).2 (by decide)
example : ¬ bit2.Realize ![0, 2] := fun h => by have := (realize_bit2 0 2).1 h; simp at this
example : noBit2.Realize ![0, 2] := (realize_noBit2 0 2).2 (by decide)
example : pot2.Realize ![3, 8] := (realize_pot2 3 8).2 (by norm_num)
example : ¬ pot2.Realize ![3, 9] := fun h => by have := (realize_pot2 3 9).1 h; norm_num at this
example : noBit2.Realize ![10, 2] := (realize_noBit2 10 2).2 (by decide)
example : idx 3 ![2, 1] = 5 := rfl
/-- La cota no es vacía: para `x = 4` (`|x| = 3`) y `k = 2`, el código más grande, `2^9 − 1`, cabe debajo. -/
example : 2 ^ 9 - 1 ≤ (cotaRel 2 (Term.var 0 : L.Term (Fin 1))).realize ![4] :=
  lt_cotaRel ![4] _ 2 _ (by decide)

/-! Mutante (probado en /tmp/claude-noche/MutanteBits.lean, 25 nov 2026): sin la conjunción `|⌊z/2⌋| = j`, `potF`
dice solo «`z` es una potencia de dos», y Lean rechaza `realize_potF` (no hay forma de recuperar `j`) y, con él, todo
lo que depende del bit. La conjunción del largo es la que ata `z` a `j`. -/

end SigmaFagin
end Sagitta.Map
