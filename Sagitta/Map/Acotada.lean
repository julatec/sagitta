import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Nat.Size

/-!
# Aritmética acotada: el sistema S¹₂ de Buss (escalón 1)

El lenguaje, el modelo estándar, los axiomas BASIC, las fórmulas `Σᵇ₁` y la inducción sobre la
longitud (PIND). Sobre la lógica de primer orden de Mathlib (`FirstOrder.Language`).

Mathlib no trae un cálculo de pruebas, así que «S¹₂ demuestra σ» se define por modelos: σ vale en todo
modelo de S¹₂. Por el teorema de completitud es lo mismo que la demostrabilidad. `Teoria.lean` escribe S¹₂ como
teoría de Mathlib y prueba que esto es su consecuencia semántica (`S12 ⊨ᵇ σ`) y que es finita (compacidad).

`L` es `abbrev` (desde el 23 nov 2026) para que las tácticas vean que `Rel.le : Rel 2` es un `L.Relations 2`: con
`def`, los lemas de realización de Mathlib no se aplicaban.

**Cotejado contra la fuente** (22 nov 2026): Buss, *Bounded Arithmetic* (Bibliopolis, 1986), en el PDF que publica
el autor (`mathweb.ucsd.edu/~sbuss/ResearchWeb/BAthesis/`), leyendo las páginas como imagen porque el OCR no trae
las fórmulas.

* El lenguaje y el significado de `|x|` y `#` (§2.1, p. 28): coinciden.
* Los 32 axiomas BASIC (§2.2, pp. 30–31): coinciden uno por uno. Tres van «currificados» (7, 8 y 20: la hipótesis
  `A ∧ B ⊃ C` se escribe `A → B → C`), que es lo mismo.
* La jerarquía de fórmulas (§2.1, pp. 29–30): se corrigió. La primera versión no tenía la cláusula (d) de `Σᵇ₁`
  (negar una `Πᵇ₁`, y `B ⊃ A` con `B` en `Πᵇ₁`) ni el `∃ x ≤ |t|` como cuantificador agudo. Ahora `Σᵇ₁` y `Πᵇ₁` se
  definen juntas, con las cuatro cláusulas del libro.
* PIND y la definición de `S¹₂` (§2.2, p. 31): coinciden.

Que ℕ cumple los 32 axiomas está **probado** aquí (`nat_esModeloBASIC`).
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-! ## El lenguaje -/

/-- Los símbolos de función: `0`, `S`, `|x|`, `⌊x/2⌋`, `+`, `·`, `#`. -/
inductive Fun : ℕ → Type
  | cero : Fun 0
  | suc : Fun 1
  | long : Fun 1
  | mitad : Fun 1
  | suma : Fun 2
  | prod : Fun 2
  | smash : Fun 2

/-- El único símbolo de relación: `≤`. -/
inductive Rel : ℕ → Type
  | le : Rel 2

/-- El lenguaje de la aritmética acotada. -/
abbrev L : Language := ⟨Fun, Rel⟩

/-! ## Las operaciones en una estructura cualquiera -/

section Operaciones

variable {M : Type} [L.Structure M]

/-- `0`. -/
def cero : M := Structure.funMap (L := L) (Fun.cero : L.Functions 0) ![]
/-- El sucesor. -/
def suc (x : M) : M := Structure.funMap (L := L) (Fun.suc : L.Functions 1) ![x]
/-- La longitud `|x|`: cuántos bits tiene `x`. -/
def long (x : M) : M := Structure.funMap (L := L) (Fun.long : L.Functions 1) ![x]
/-- La mitad `⌊x/2⌋`. -/
def mitad (x : M) : M := Structure.funMap (L := L) (Fun.mitad : L.Functions 1) ![x]
/-- La suma. -/
def suma (x y : M) : M := Structure.funMap (L := L) (Fun.suma : L.Functions 2) ![x, y]
/-- El producto. -/
def prod (x y : M) : M := Structure.funMap (L := L) (Fun.prod : L.Functions 2) ![x, y]
/-- El «smash» `x # y = 2^(|x|·|y|)`: lo que permite hablar de longitudes polinomiales. -/
def smash (x y : M) : M := Structure.funMap (L := L) (Fun.smash : L.Functions 2) ![x, y]
/-- El orden. -/
def le (x y : M) : Prop := Structure.RelMap (L := L) (Rel.le : L.Relations 2) ![x, y]
/-- `1 = S0`. -/
def uno : M := suc cero
/-- `2x`, escrito `(SS0)·x`. -/
def doble (x : M) : M := prod (suc (suc cero)) x

end Operaciones

/-! ## Los axiomas BASIC -/

/-- Los 32 axiomas BASIC de Buss, como propiedades de una estructura. -/
structure EsModeloBASIC (M : Type) [L.Structure M] : Prop where
  b1 : ∀ x y : M, le y x → le y (suc x)
  b2 : ∀ x : M, x ≠ suc x
  b3 : ∀ x : M, le cero x
  b4 : ∀ x y : M, (le x y ∧ x ≠ y) ↔ le (suc x) y
  b5 : ∀ x : M, x ≠ cero → doble x ≠ cero
  b6 : ∀ x y : M, le y x ∨ le x y
  b7 : ∀ x y : M, le x y → le y x → x = y
  b8 : ∀ x y z : M, le x y → le y z → le x z
  b9 : long (cero : M) = cero
  b10 : ∀ x : M, x ≠ cero → long (doble x) = suc (long x) ∧ long (suc (doble x)) = suc (long x)
  b11 : long (uno : M) = uno
  b12 : ∀ x y : M, le x y → le (long x) (long y)
  b13 : ∀ x y : M, long (smash x y) = suc (prod (long x) (long y))
  b14 : ∀ y : M, smash cero y = uno
  b15 : ∀ x : M, x ≠ cero →
    smash uno (doble x) = doble (smash uno x) ∧ smash uno (suc (doble x)) = doble (smash uno x)
  b16 : ∀ x y : M, smash x y = smash y x
  b17 : ∀ x y z : M, long x = long y → smash x z = smash y z
  b18 : ∀ x y u v : M, long x = suma (long u) (long v) → smash x y = prod (smash u y) (smash v y)
  b19 : ∀ x y : M, le x (suma x y)
  b20 : ∀ x y : M, le x y → x ≠ y → le (suc (doble x)) (doble y) ∧ suc (doble x) ≠ doble y
  b21 : ∀ x y : M, suma x y = suma y x
  b22 : ∀ x : M, suma x cero = x
  b23 : ∀ x y : M, suma x (suc y) = suc (suma x y)
  b24 : ∀ x y z : M, suma (suma x y) z = suma x (suma y z)
  b25 : ∀ x y z : M, le (suma x y) (suma x z) ↔ le y z
  b26 : ∀ x : M, prod x cero = cero
  b27 : ∀ x y : M, prod x (suc y) = suma (prod x y) x
  b28 : ∀ x y : M, prod x y = prod y x
  b29 : ∀ x y z : M, prod x (suma y z) = suma (prod x y) (prod x z)
  b30 : ∀ x y z : M, le uno x → (le (prod x y) (prod x z) ↔ le y z)
  b31 : ∀ x : M, x ≠ cero → long x = suc (long (mitad x))
  b32 : ∀ x y : M, x = mitad y ↔ (doble x = y ∨ suc (doble x) = y)

/-! ## El modelo estándar -/

/-- La interpretación de las funciones en ℕ. -/
def interpFun : ∀ {n : ℕ}, Fun n → (Fin n → ℕ) → ℕ
  | _, .cero, _ => 0
  | _, .suc, v => v 0 + 1
  | _, .long, v => Nat.size (v 0)
  | _, .mitad, v => v 0 / 2
  | _, .suma, v => v 0 + v 1
  | _, .prod, v => v 0 * v 1
  | _, .smash, v => 2 ^ (Nat.size (v 0) * Nat.size (v 1))

/-- La interpretación de las relaciones en ℕ. -/
def interpRel : ∀ {n : ℕ}, Rel n → (Fin n → ℕ) → Prop
  | _, .le, v => v 0 ≤ v 1

instance : L.Structure ℕ where
  funMap := interpFun
  RelMap := interpRel

@[simp] theorem cero_nat : (cero : ℕ) = 0 := rfl
@[simp] theorem suc_nat (x : ℕ) : suc x = x + 1 := rfl
@[simp] theorem long_nat (x : ℕ) : long x = Nat.size x := rfl
@[simp] theorem mitad_nat (x : ℕ) : mitad x = x / 2 := rfl
@[simp] theorem suma_nat (x y : ℕ) : suma x y = x + y := rfl
@[simp] theorem prod_nat (x y : ℕ) : prod x y = x * y := rfl
@[simp] theorem smash_nat (x y : ℕ) : smash x y = 2 ^ (Nat.size x * Nat.size y) := rfl
@[simp] theorem le_nat (x y : ℕ) : le x y ↔ x ≤ y := Iff.rfl
@[simp] theorem uno_nat : (uno : ℕ) = 1 := rfl
@[simp] theorem doble_nat (x : ℕ) : doble x = 2 * x := rfl

/-- `|x| = |⌊x/2⌋| + 1` para `x ≠ 0`. -/
theorem size_mitad {x : ℕ} (hx : x ≠ 0) : Nat.size x = Nat.size (x / 2) + 1 := by
  have hb : Nat.bit (decide (x % 2 = 1)) (x / 2) = x := by
    rw [Nat.bit_val]
    by_cases h : x % 2 = 1 <;> simp [h] <;> omega
  have h := Nat.size_bit (b := decide (x % 2 = 1)) (n := x / 2) (by rw [hb]; exact hx)
  rw [hb] at h
  exact h

theorem size_doble {x : ℕ} (hx : x ≠ 0) : Nat.size (2 * x) = Nat.size x + 1 := by
  have h := size_mitad (x := 2 * x) (by omega)
  rwa [show 2 * x / 2 = x by omega] at h

theorem size_doble_mas_uno (x : ℕ) : Nat.size (2 * x + 1) = Nat.size x + 1 := by
  have h := size_mitad (x := 2 * x + 1) (by omega)
  rwa [show (2 * x + 1) / 2 = x by omega] at h

/-- **ℕ cumple los 32 axiomas BASIC.** -/
theorem nat_esModeloBASIC : EsModeloBASIC ℕ where
  b1 := by intro x y; simp; omega
  b2 := by intro x; simp
  b3 := by intro x; simp
  b4 := by intro x y; simp; omega
  b5 := by intro x; simp
  b6 := by intro x y; simp; omega
  b7 := by intro x y; simp; omega
  b8 := by intro x y z; simp; omega
  b9 := by simp
  b10 := by
    intro x hx
    simp only [cero_nat] at hx
    simp only [long_nat, doble_nat, suc_nat]
    exact ⟨size_doble hx, size_doble_mas_uno x⟩
  b11 := by simp [Nat.size_one]
  b12 := by intro x y; simp only [le_nat, long_nat]; exact Nat.size_le_size
  b13 := by intro x y; simp [Nat.size_pow]
  b14 := by intro y; simp
  b15 := by
    intro x hx
    simp only [cero_nat] at hx
    simp only [smash_nat, uno_nat, doble_nat, suc_nat, Nat.size_one, one_mul]
    rw [size_doble hx, size_doble_mas_uno, pow_succ]
    constructor <;> exact Nat.mul_comm _ _
  b16 := by intro x y; simp [mul_comm]
  b17 := by intro x y z; simp only [long_nat, smash_nat]; intro h; rw [h]
  b18 := by
    intro x y u v
    simp only [long_nat, suma_nat, smash_nat, prod_nat]
    intro h
    rw [h, add_mul, pow_add]
  b19 := by intro x y; simp
  b20 := by intro x y; simp; omega
  b21 := by intro x y; simp [add_comm]
  b22 := by intro x; simp
  b23 := by intro x y; simp; omega
  b24 := by intro x y z; simp [add_assoc]
  b25 := by intro x y z; simp
  b26 := by intro x; simp
  b27 := by intro x y; simp [Nat.mul_succ]
  b28 := by intro x y; simp [mul_comm]
  b29 := by intro x y z; simp [mul_add]
  b30 := by
    intro x y z
    simp only [le_nat, uno_nat, prod_nat]
    intro hx
    exact Nat.mul_le_mul_left_iff (by omega)
  b31 := by
    intro x hx
    simp only [cero_nat] at hx
    simp only [long_nat, mitad_nat, suc_nat]
    exact size_mitad hx
  b32 := by intro x y; simp; omega

/-! ## Fórmulas acotadas -/

section Formulas

variable {α : Type}

/-- El término `|t|`. -/
def tLong {β : Type} (t : L.Term β) : L.Term β := Term.func (Fun.long : L.Functions 1) ![t]

/-- La fórmula `t ≤ u`. -/
def leF {n : ℕ} (t u : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  BoundedFormula.rel (Rel.le : L.Relations 2) ![t, u]

/-- La variable recién ligada, dentro de un cuantificador. -/
def nueva {n : ℕ} : L.Term (α ⊕ Fin (n + 1)) := Term.var (Sum.inr (Fin.last n))

/-- Lleva un término al contexto con una variable ligada más. -/
def sube {n : ℕ} (t : L.Term (α ⊕ Fin n)) : L.Term (α ⊕ Fin (n + 1)) :=
  t.relabel (Sum.map id Fin.castSucc)

/-- `∀ x ≤ t, φ`. -/
def paraTodoAcotado {n : ℕ} (t : L.Term (α ⊕ Fin n)) (φ : L.BoundedFormula α (n + 1)) :
    L.BoundedFormula α n :=
  (BoundedFormula.imp (leF nueva (sube t)) φ).all

/-- `∃ x ≤ t, φ`. -/
def existeAcotado {n : ℕ} (t : L.Term (α ⊕ Fin n)) (φ : L.BoundedFormula α (n + 1)) :
    L.BoundedFormula α n :=
  (leF nueva (sube t) ⊓ φ).ex

/-- **Fórmulas agudamente acotadas** (`Δᵇ₀ = Σᵇ₀ = Πᵇ₀`): todos los cuantificadores son agudos, de la forma
`∀ x ≤ |t|` o `∃ x ≤ |t|` (Buss, def. de p. 29, cláusula 1). Recorren solo una cantidad polinomial de valores. -/
inductive EsAguda : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | falso {n : ℕ} : EsAguda (BoundedFormula.falsum : L.BoundedFormula α n)
  | igual {n : ℕ} (t u : L.Term (α ⊕ Fin n)) : EsAguda (BoundedFormula.equal t u)
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      EsAguda (BoundedFormula.rel R ts)
  | imp {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsAguda φ → EsAguda ψ → EsAguda (φ.imp ψ)
  | todoAgudo {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsAguda φ → EsAguda (paraTodoAcotado (tLong t) φ)
  | existeAgudo {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsAguda φ → EsAguda (existeAcotado (tLong t) φ)

mutual

/-- **Fórmulas `Σᵇ₁`** (Buss, pp. 29–30, cláusula 2 con `k = 0`). Son a la aritmética acotada lo que NP es a la
complejidad: un «existe» acotado delante de algo fácil de comprobar.

* (a) contiene a las agudas (`Πᵇ₀`);
* (b) se cierra por `∃ x ≤ t` y `∀ x ≤ |t|`;
* (c) se cierra por `∧` y `∨`;
* (d) si `B` es `Πᵇ₁` y `A` es `Σᵇ₁`, entonces `¬B` y `B ⊃ A` son `Σᵇ₁`. -/
inductive EsSigma1 : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | aguda {n : ℕ} {φ : L.BoundedFormula α n} : EsAguda φ → EsSigma1 φ
  | existe {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsSigma1 φ → EsSigma1 (existeAcotado t φ)
  | todoAgudo {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsSigma1 φ → EsSigma1 (paraTodoAcotado (tLong t) φ)
  | y {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsSigma1 φ → EsSigma1 ψ → EsSigma1 (φ ⊓ ψ)
  | o {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsSigma1 φ → EsSigma1 ψ → EsSigma1 (φ ⊔ ψ)
  | no {n : ℕ} {φ : L.BoundedFormula α n} : EsPi1 φ → EsSigma1 φ.not
  | imp {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsPi1 φ → EsSigma1 ψ → EsSigma1 (φ.imp ψ)

/-- **Fórmulas `Πᵇ₁`** (Buss, p. 30, cláusula 3 con `k = 0`): las duales.

* (a) contiene a las agudas (`Σᵇ₀`);
* (b) se cierra por `∀ x ≤ t` y `∃ x ≤ |t|`;
* (c) se cierra por `∧` y `∨`;
* (d) si `B` es `Σᵇ₁` y `A` es `Πᵇ₁`, entonces `¬B` y `B ⊃ A` son `Πᵇ₁`. -/
inductive EsPi1 : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | aguda {n : ℕ} {φ : L.BoundedFormula α n} : EsAguda φ → EsPi1 φ
  | todo {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsPi1 φ → EsPi1 (paraTodoAcotado t φ)
  | existeAgudo {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsPi1 φ → EsPi1 (existeAcotado (tLong t) φ)
  | y {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsPi1 φ → EsPi1 ψ → EsPi1 (φ ⊓ ψ)
  | o {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsPi1 φ → EsPi1 ψ → EsPi1 (φ ⊔ ψ)
  | no {n : ℕ} {φ : L.BoundedFormula α n} : EsSigma1 φ → EsPi1 φ.not
  | imp {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsSigma1 φ → EsPi1 ψ → EsPi1 (φ.imp ψ)

end

end Formulas

/-! ## El sistema S¹₂ -/

/-- **Un modelo de S¹₂**: cumple BASIC y la inducción sobre la longitud (PIND) para toda fórmula `Σᵇ₁`.
PIND: si `φ(0)` y `φ(⌊x/2⌋) → φ(x)`, entonces `φ(x)` para todo `x`. La variable 0 es la de inducción;
las demás son parámetros. -/
structure EsModeloS12 (M : Type) [L.Structure M] : Prop where
  basic : EsModeloBASIC M
  pind : ∀ (k : ℕ) (φ : L.Formula (Fin (k + 1))), EsSigma1 φ → ∀ v : Fin k → M,
    φ.Realize (Fin.cons cero v) →
    (∀ x : M, φ.Realize (Fin.cons (mitad x) v) → φ.Realize (Fin.cons x v)) →
    ∀ x : M, φ.Realize (Fin.cons x v)

/-- **ℕ es un modelo de S¹₂.** PIND vale en ℕ para cualquier propiedad, por inducción fuerte: `⌊x/2⌋ < x`
cuando `x ≠ 0`. Es la buena fundación de ℕ. -/
theorem nat_esModeloS12 : EsModeloS12 ℕ where
  basic := nat_esModeloBASIC
  pind := by
    intro k φ _ v h0 hpaso x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      by_cases hx : x = 0
      · subst hx; exact h0
      · exact hpaso x (ih (x / 2) (by omega))

/-- **S¹₂ demuestra σ**, por modelos: σ vale en todo modelo de S¹₂. -/
def Demuestra (σ : L.Sentence) : Prop :=
  ∀ (M : Type) [L.Structure M], EsModeloS12 M → M ⊨ σ

/-- Lo que S¹₂ demuestra es verdadero en ℕ. -/
theorem verdadero_de_demuestra {σ : L.Sentence} (h : Demuestra σ) : ℕ ⊨ σ :=
  h ℕ nat_esModeloS12

end Acotada
end Sagitta.Map
