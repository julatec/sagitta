import Sagitta.Map.Cerradura
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Las funciones de Cobham sobre los números

Primer paso (R1) de la ruta por modelos hacia el teorema de Buss. La
ruta pide un lenguaje con un símbolo por cada función de tiempo polinomial. Aquí están esas funciones como
programas, sobre ℕ, y el **arranque**: las funciones que después dejan probar, en cualquier modelo, lo que en ℕ se
ve a ojo.

## Qué hay

* **`Cob n`**: programas de `n` argumentos. Básicas: `0`, proyecciones, sucesor, suma, resta truncada, producto,
  `⌊x/2⌋`, `|x|`, `x # y`, y un condicional. Se cierran bajo **composición** y **recursión sobre la notación con
  tope**: `F(0, ȳ) = G(ȳ)` y, si `x ≠ 0`, `F(x, ȳ) = min (H(x, F(⌊x/2⌋, ȳ), ȳ)) (K(x, ȳ))`.
* **`crece`**: lo que un programa entrega mide a lo sumo un polinomio en el largo de sus argumentos.
* **El arranque**:
  - fórmulas sin cuantificadores, como programas que valen `0` justo cuando la fórmula vale (`menorIgual`, `igual`,
    `yy`, `oo`, `no`);
  - **`buscar`**: el menor `z ≤ |t|` en que un programa vale `0`, o `|t| + 1` si no hay. Con él, el «para todo
    `z ≤ |t|`» se vuelve una fórmula sin cuantificadores (`paraTodo_iff`);
  - **`primerFallo`**: el prefijo binario más corto de `b` en que un programa no vale `0`. Es lo que vuelve la
    inducción por bits sin cuantificadores **un enunciado universal** (`pind_abierta`), y por tanto verdadero en
    todo modelo de la teoría.

## Por qué el tope

Sin el tope, la recursión sobre la notación sale de los polinomios: iterar el cuadrado `|x|` veces da un número de
`2^|x|` bits. Con `min … K`, lo que entrega nunca pasa de `K`, que ya es polinomial. Es la recursión *limitada* de
Cobham, escrita para que el programa sea total sin condición aparte.

## Qué no hay

* **Que estos programas corren en tiempo polinomial en una máquina.** Es la fase F4b del plan.
* **Que todo lo de tiempo polinomial es de Cobham.** No hace falta para el teorema del testigo, que va en una
  sola dirección.
-/

namespace Sagitta.Map
namespace Cobham

open Cerradura (Acotada)

/-- **Programas de Cobham** de `n` argumentos. -/
inductive Cob : ℕ → Type
  | cero {n : ℕ} : Cob n
  | proy {n : ℕ} (i : Fin n) : Cob n
  | suc : Cob 1
  | suma : Cob 2
  /-- Resta truncada: `x ∸ y`. -/
  | resta : Cob 2
  | prod : Cob 2
  /-- `⌊x/2⌋`. -/
  | mitad : Cob 1
  /-- `|x|`, el largo en bits. -/
  | largo : Cob 1
  /-- `x # y = 2^(|x|·|y|)`. -/
  | smash : Cob 2
  /-- Si `x = 0` entonces `y`, si no `z`. -/
  | cond : Cob 3
  | comp {n m : ℕ} (f : Cob m) (gs : Fin m → Cob n) : Cob n
  /-- Recursión sobre la notación con tope. El primer argumento es el de la recursión. En `h`, el argumento `0` es
  `x`, el `1` es el valor en `⌊x/2⌋` y los demás son los parámetros. En `k`, el `0` es `x`. -/
  | rn {n : ℕ} (g : Cob n) (h : Cob (n + 2)) (k : Cob (n + 1)) : Cob (n + 1)

/-- La recursión sobre la notación con tope, con combustible para que sea estructural. -/
def notacion (a : ℕ) (H : ℕ → ℕ → ℕ) (K : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => a
  | 0, _ + 1 => a
  | fuel + 1, x + 1 => min (H (x + 1) (notacion a H K fuel ((x + 1) / 2))) (K (x + 1))

/-- **El valor de un programa.** -/
def Cob.eval : {n : ℕ} → Cob n → (Fin n → ℕ) → ℕ
  | _, .cero, _ => 0
  | _, .proy i, v => v i
  | _, .suc, v => v 0 + 1
  | _, .suma, v => v 0 + v 1
  | _, .resta, v => v 0 - v 1
  | _, .prod, v => v 0 * v 1
  | _, .mitad, v => v 0 / 2
  | _, .largo, v => Nat.size (v 0)
  | _, .smash, v => 2 ^ (Nat.size (v 0) * Nat.size (v 1))
  | _, .cond, v => if v 0 = 0 then v 1 else v 2
  | _, .comp f gs, v => f.eval fun i => (gs i).eval v
  | _, .rn g h k, v =>
      notacion (g.eval (Fin.tail v))
        (fun x r => h.eval (Fin.cons x (Fin.cons r (Fin.tail v) : Fin (_ + 1) → ℕ)))
        (fun x => k.eval (Fin.cons x (Fin.tail v) : Fin (_ + 1) → ℕ)) (v 0) (v 0)

/-! ## La recursión, desplegada -/

/-- El combustible no importa mientras alcance. -/
theorem notacion_fuel (a : ℕ) (H : ℕ → ℕ → ℕ) (K : ℕ → ℕ) :
    ∀ f₁ f₂ x : ℕ, x ≤ f₁ → x ≤ f₂ → notacion a H K f₁ x = notacion a H K f₂ x
  | _, _, 0, _, _ => by simp only [notacion]
  | 0, _, _ + 1, h, _ => absurd h (by omega)
  | _, 0, _ + 1, _, h => absurd h (by omega)
  | f₁ + 1, f₂ + 1, x + 1, h₁, h₂ => by
      simp only [notacion]
      rw [notacion_fuel a H K f₁ f₂ ((x + 1) / 2) (by omega) (by omega)]

theorem eval_rec_cero {n : ℕ} (g : Cob n) (h : Cob (n + 2)) (k : Cob (n + 1)) (y : Fin n → ℕ) :
    (Cob.rn g h k).eval (Fin.cons 0 y) = g.eval y := by
  simp only [Cob.eval, Fin.cons_zero, Fin.tail_cons, notacion]

/-- **La ecuación de la recursión.** -/
theorem eval_rec_pos {n : ℕ} (g : Cob n) (h : Cob (n + 2)) (k : Cob (n + 1)) (y : Fin n → ℕ) {x : ℕ}
    (hx : x ≠ 0) :
    (Cob.rn g h k).eval (Fin.cons x y) =
      min (h.eval (Fin.cons x (Fin.cons ((Cob.rn g h k).eval (Fin.cons (x / 2) y)) y)))
        (k.eval (Fin.cons x y)) := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx
  simp only [Cob.eval, Fin.cons_zero, Fin.tail_cons, notacion]
  rw [notacion_fuel _ _ _ x ((x + 1) / 2) ((x + 1) / 2) (by omega) (le_refl _)]

/-- El valor de la recursión es la base, o no pasa del tope. -/
theorem notacion_le (a : ℕ) (H : ℕ → ℕ → ℕ) (K : ℕ → ℕ) (f x : ℕ) :
    notacion a H K f x = a ∨ notacion a H K f x ≤ K x := by
  rcases f with _ | f <;> rcases x with _ | x
  · exact .inl rfl
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr (min_le_right _ _)

/-! ## El crecimiento es polinomial -/

private theorem size_lt {a m : ℕ} (h : Nat.size a ≤ m) : a < 2 ^ m := Nat.size_le.mp h

private theorem size_le_of_lt {a m : ℕ} (h : a < 2 ^ m) : Nat.size a ≤ m := Nat.size_le.mpr h

private theorem size_le_self (a : ℕ) : Nat.size a ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem acotada_const (c : ℕ) : Acotada fun _ => c := ⟨Polynomial.C c, fun _ => by simp⟩

private theorem acotada_id : Acotada fun n => n := ⟨Polynomial.X, fun _ => by simp⟩

private theorem acotada_sum {ι : Type} (s : Finset ι) (B : ι → ℕ → ℕ) (h : ∀ i, Acotada (B i)) :
    Acotada fun m => ∑ i ∈ s, B i m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using acotada_const 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact Cerradura.suma (h i) ih

/-- Una cota buena: polinomial y creciente. -/
def CotaBuena (B : ℕ → ℕ) : Prop := Acotada B ∧ Monotone B

/-- La cota de un programa: si sus argumentos miden a lo sumo `m` bits, su valor mide a lo sumo `B m`. -/
def Acota {n : ℕ} (c : Cob n) (B : ℕ → ℕ) : Prop :=
  ∀ (m : ℕ) (v : Fin n → ℕ), (∀ i, Nat.size (v i) ≤ m) → Nat.size (c.eval v) ≤ B m

private theorem buena_const (c : ℕ) : CotaBuena fun _ => c := ⟨acotada_const c, fun _ _ _ => le_refl _⟩

private theorem buena_lin (a b : ℕ) : CotaBuena fun m => a * m + b :=
  ⟨⟨Polynomial.C (a : ℕ) * Polynomial.X + Polynomial.C b, fun _ => by simp⟩,
    fun _ _ h => Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _⟩

/-- **Lo que un programa entrega mide a lo sumo un polinomio** en el largo de sus argumentos. -/
theorem crece {n : ℕ} (c : Cob n) : ∃ B, CotaBuena B ∧ Acota c B := by
  induction c with
  | cero => exact ⟨_, buena_const 0, fun _ _ _ => by simp [Cob.eval]⟩
  | proy i => exact ⟨_, buena_lin 1 0, fun m v hv => by simpa [Cob.eval] using hv i⟩
  | suc =>
    refine ⟨_, buena_lin 1 1, fun m v hv => size_le_of_lt ?_⟩
    have := size_lt (hv 0)
    simp only [Cob.eval, Nat.pow_succ, Nat.one_mul]; omega
  | suma =>
    refine ⟨_, buena_lin 1 1, fun m v hv => size_le_of_lt ?_⟩
    have := size_lt (hv 0); have := size_lt (hv 1)
    simp only [Cob.eval, Nat.pow_succ, Nat.one_mul]; omega
  | resta =>
    exact ⟨_, buena_lin 1 0, fun m v hv => by
      simp only [Cob.eval]; exact by simpa using (Nat.size_le_size (Nat.sub_le _ _)).trans (hv 0)⟩
  | prod =>
    refine ⟨_, buena_lin 2 0, fun m v hv => size_le_of_lt ?_⟩
    have h0 := size_lt (hv 0); have h1 := size_lt (hv 1)
    simp only [Cob.eval, Nat.add_zero, Nat.two_mul, Nat.pow_add]
    exact Nat.mul_lt_mul'' h0 h1
  | mitad =>
    exact ⟨_, buena_lin 1 0, fun m v hv => by
      simp only [Cob.eval]; simpa using (Nat.size_le_size (Nat.div_le_self _ _)).trans (hv 0)⟩
  | largo =>
    exact ⟨_, buena_lin 1 0, fun m v hv => by
      simp only [Cob.eval]; simpa using (Nat.size_le_size (size_le_self _)).trans (hv 0)⟩
  | smash =>
    refine ⟨fun m => m * m + 1, ⟨⟨Polynomial.X * Polynomial.X + 1, fun _ => by simp⟩,
      fun _ _ h => Nat.succ_le_succ (Nat.mul_le_mul h h)⟩, fun m v hv => ?_⟩
    simp only [Cob.eval, Nat.size_pow]
    exact Nat.succ_le_succ (Nat.mul_le_mul (hv 0) (hv 1))
  | cond =>
    refine ⟨_, buena_lin 1 0, fun m v hv => ?_⟩
    simp only [Cob.eval]
    split
    · simpa using hv 1
    · simpa using hv 2
  | comp f gs ihf ihg =>
    choose B hB hA using ihg
    obtain ⟨Bf, hBf, hAf⟩ := ihf
    refine ⟨fun m => Bf (∑ i, B i m), ⟨Cerradura.composicion hBf.1 (acotada_sum _ _ fun i => (hB i).1),
      fun a b h => hBf.2 (Finset.sum_le_sum fun i _ => (hB i).2 h)⟩, fun m v hv => ?_⟩
    simp only [Cob.eval]
    refine hAf _ _ fun i => (hA i m v hv).trans ?_
    exact Finset.single_le_sum (f := fun i => B i m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  | rn g h k ihg _ ihk =>
    obtain ⟨Bg, hBg, hAg⟩ := ihg
    obtain ⟨Bk, hBk, hAk⟩ := ihk
    refine ⟨fun m => Bg m + Bk m, ⟨Cerradura.suma hBg.1 hBk.1,
      fun a b hab => Nat.add_le_add (hBg.2 hab) (hBk.2 hab)⟩, fun m v hv => ?_⟩
    have hg := hAg m (Fin.tail v) fun i => hv i.succ
    have hk := hAk m v hv
    simp only [Cob.eval]
    rcases notacion_le (g.eval (Fin.tail v))
      (fun x r => h.eval (Fin.cons x (Fin.cons r (Fin.tail v) : Fin (_ + 1) → ℕ)))
      (fun x => k.eval (Fin.cons x (Fin.tail v) : Fin (_ + 1) → ℕ)) (v 0) (v 0) with e | e
    · rw [e]; omega
    · have e' : k.eval (Fin.cons (v 0) (Fin.tail v) : Fin (_ + 1) → ℕ) = k.eval v := by
        rw [Fin.cons_self_tail]
      rw [e'] at e
      have := (Nat.size_le_size e).trans hk
      omega

/-! ## Para escribir programas -/

/-- Componer con un programa de un argumento. -/
def c1 {n : ℕ} (f : Cob 1) (a : Cob n) : Cob n := .comp f ![a]
/-- Componer con un programa de dos argumentos. -/
def c2 {n : ℕ} (f : Cob 2) (a b : Cob n) : Cob n := .comp f ![a, b]
/-- Componer con un programa de tres argumentos. -/
def c3 {n : ℕ} (f : Cob 3) (a b c : Cob n) : Cob n := .comp f ![a, b, c]

/-- Un programa de `n + 1` argumentos, con el primero fijo en `a` y los demás pasados tal cual. -/
def fijar {n : ℕ} (f : Cob (n + 1)) (a : Cob n) : Cob n := .comp f (Fin.cons a fun i => .proy i)

@[simp] theorem eval_cero {n : ℕ} (v : Fin n → ℕ) : (Cob.cero : Cob n).eval v = 0 := rfl
@[simp] theorem eval_proy {n : ℕ} (i : Fin n) (v : Fin n → ℕ) : (Cob.proy i).eval v = v i := rfl

@[simp] theorem eval_c1 {n : ℕ} (f : Cob 1) (a : Cob n) (v : Fin n → ℕ) :
    (c1 f a).eval v = f.eval ![a.eval v] := by
  simp only [c1, Cob.eval]; congr 1; funext i; fin_cases i; rfl

@[simp] theorem eval_c2 {n : ℕ} (f : Cob 2) (a b : Cob n) (v : Fin n → ℕ) :
    (c2 f a b).eval v = f.eval ![a.eval v, b.eval v] := by
  simp only [c2, Cob.eval]; congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem eval_c3 {n : ℕ} (f : Cob 3) (a b c : Cob n) (v : Fin n → ℕ) :
    (c3 f a b c).eval v = f.eval ![a.eval v, b.eval v, c.eval v] := by
  simp only [c3, Cob.eval]; congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem eval_fijar {n : ℕ} (f : Cob (n + 1)) (a : Cob n) (v : Fin n → ℕ) :
    (fijar f a).eval v = f.eval (Fin.cons (a.eval v) v) := by
  simp only [fijar, Cob.eval]; congr 1; funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

@[simp] theorem eval_suc (a : ℕ) : Cob.suc.eval ![a] = a + 1 := rfl
@[simp] theorem eval_suma (a b : ℕ) : Cob.suma.eval ![a, b] = a + b := rfl
@[simp] theorem eval_resta (a b : ℕ) : Cob.resta.eval ![a, b] = a - b := rfl
@[simp] theorem eval_prod (a b : ℕ) : Cob.prod.eval ![a, b] = a * b := rfl
@[simp] theorem eval_mitad (a : ℕ) : Cob.mitad.eval ![a] = a / 2 := rfl
@[simp] theorem eval_largo (a : ℕ) : Cob.largo.eval ![a] = Nat.size a := rfl
@[simp] theorem eval_cond (a b c : ℕ) : Cob.cond.eval ![a, b, c] = if a = 0 then b else c := rfl

/-! ## El arranque: fórmulas sin cuantificadores

La convención: un programa **vale** donde da `0`. -/

/-- El número `1`. -/
def uno {n : ℕ} : Cob n := c1 .suc .cero

/-- `a ≤ b`. -/
def menorIgual {n : ℕ} (a b : Cob n) : Cob n := c2 .resta a b
/-- `a = b`. -/
def igual {n : ℕ} (a b : Cob n) : Cob n := c2 .suma (c2 .resta a b) (c2 .resta b a)
/-- «y». -/
def yy {n : ℕ} (p q : Cob n) : Cob n := c2 .suma p q
/-- «o». -/
def oo {n : ℕ} (p q : Cob n) : Cob n := c2 .prod p q
/-- «no». -/
def no {n : ℕ} (p : Cob n) : Cob n := c3 .cond p uno .cero

@[simp] theorem eval_uno {n : ℕ} (v : Fin n → ℕ) : (uno : Cob n).eval v = 1 := rfl

theorem menorIgual_vale {n : ℕ} (a b : Cob n) (v : Fin n → ℕ) :
    (menorIgual a b).eval v = 0 ↔ a.eval v ≤ b.eval v := by
  simp [menorIgual]; omega

theorem igual_vale {n : ℕ} (a b : Cob n) (v : Fin n → ℕ) :
    (igual a b).eval v = 0 ↔ a.eval v = b.eval v := by
  simp [igual]; omega

theorem yy_vale {n : ℕ} (p q : Cob n) (v : Fin n → ℕ) :
    (yy p q).eval v = 0 ↔ p.eval v = 0 ∧ q.eval v = 0 := by
  simp [yy]

theorem oo_vale {n : ℕ} (p q : Cob n) (v : Fin n → ℕ) :
    (oo p q).eval v = 0 ↔ p.eval v = 0 ∨ q.eval v = 0 := by
  simp [oo]

theorem no_vale {n : ℕ} (p : Cob n) (v : Fin n → ℕ) : (no p).eval v = 0 ↔ p.eval v ≠ 0 := by
  simp only [no, eval_c3, eval_cond, eval_uno, eval_cero]; split <;> simp_all

/-! ## El arranque: el «para todo» sobre un rango pequeño -/

private theorem size_mitad (b : ℕ) (hb : b ≠ 0) : Nat.size b = Nat.size (b / 2) + 1 := by
  have e := Nat.bit_testBit_zero_shiftRight_one b
  have h : Nat.bit (b.testBit 0) (b >>> 1) ≠ 0 := by rw [e]; exact hb
  have hs := Nat.size_bit h
  rw [e, Nat.shiftRight_one] at hs
  exact hs

/-- **Buscar en un rango pequeño.** Con `t` el primer argumento: el menor `z ≤ |t|` en que `f(z, ȳ)` vale, o `|t| + 1`
si no hay. Es una recursión sobre la notación de `t`: cada bit agrega un valor al rango. -/
def buscar {n : ℕ} (f : Cob (n + 1)) : Cob (n + 1) :=
  .rn (c3 .cond (fijar f .cero) .cero uno)
    (c3 .cond (c2 .resta (.proy 1) (c1 .largo (c1 .mitad (.proy 0)))) (.proy 1)
      (c3 .cond (.comp f (Fin.cons (c1 .largo (.proy 0)) fun i => .proy i.succ.succ))
        (c1 .largo (.proy 0)) (c1 .suc (c1 .largo (.proy 0)))))
    (c1 .suc (c1 .largo (.proy 0)))

/-- **Lo que `buscar` entrega**: si está en el rango, es un cero de `f`; y no pasa de ningún cero del rango. -/
theorem buscar_spec {n : ℕ} (f : Cob (n + 1)) (y : Fin n → ℕ) :
    ∀ t : ℕ, let s := (buscar f).eval (Fin.cons t y)
      s ≤ Nat.size t + 1 ∧ (s ≤ Nat.size t → f.eval (Fin.cons s y) = 0) ∧
        ∀ z ≤ Nat.size t, f.eval (Fin.cons z y) = 0 → s ≤ z := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  by_cases ht : t = 0
  · subst ht
    simp only [buscar, eval_rec_cero, eval_c3, eval_fijar, eval_cero, eval_cond, eval_uno, Nat.size_zero]
    split
    · rename_i h0; exact ⟨by omega, fun _ => h0, fun _ _ _ => Nat.zero_le _⟩
    · rename_i h0
      refine ⟨le_refl _, fun h => absurd h (by omega), fun z hz hf => ?_⟩
      obtain rfl : z = 0 := by omega
      exact absurd hf h0
  · have hs := size_mitad t ht
    obtain ⟨ih1, ih2, ih3⟩ := ih (t / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero ht) (by decide))
    rw [buscar, eval_rec_pos _ _ _ _ ht, ← buscar]
    generalize (buscar f).eval (Fin.cons (t / 2) y) = r at ih1 ih2 ih3
    have ef : (Cob.comp f (Fin.cons (c1 .largo (.proy 0)) fun i => .proy i.succ.succ)).eval
        (Fin.cons t (Fin.cons r y) : Fin (n + 2) → ℕ) = f.eval (Fin.cons (Nat.size t) y) := by
      simp only [Cob.eval]; congr 1; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    simp only [eval_c3, eval_c2, eval_c1, eval_cond, eval_resta, eval_largo, eval_mitad, eval_proy,
      eval_suc, ef, Fin.cons_zero, Fin.cons_one]
    by_cases hr : r ≤ Nat.size (t / 2)
    · have hc : r - Nat.size (t / 2) = 0 := by omega
      simp only [hc, ↓reduceIte]
      rw [min_eq_left (by omega)]
      refine ⟨by omega, fun _ => ih2 hr, fun z hz hf => ?_⟩
      by_cases hz' : z ≤ Nat.size (t / 2)
      · exact ih3 z hz' hf
      · omega
    · have hc : r - Nat.size (t / 2) ≠ 0 := by omega
      simp only [hc, ↓reduceIte]
      have nada : ∀ z ≤ Nat.size (t / 2), f.eval (Fin.cons z y) ≠ 0 := fun z hz hf =>
        hr ((ih3 z hz hf).trans hz)
      split
      · rename_i h0
        rw [min_eq_left (by omega)]
        refine ⟨by omega, fun _ => h0, fun z hz hf => ?_⟩
        by_contra hlt
        exact nada z (by omega) hf
      · rename_i h0
        rw [min_eq_left (le_refl _)]
        refine ⟨le_refl _, fun h => absurd h (by omega), fun z hz hf => ?_⟩
        by_cases hz' : z ≤ Nat.size (t / 2)
        · exact absurd hf (nada z hz')
        · obtain rfl : z = Nat.size t := by omega
          exact absurd hf h0

/-- **El «para todo» pequeño, sin cuantificadores.** `f` vale en todo `z ≤ |t|` si y solo si `buscar (no f)` se sale
del rango. -/
theorem paraTodo_iff {n : ℕ} (f : Cob (n + 1)) (t : ℕ) (y : Fin n → ℕ) :
    (∀ z ≤ Nat.size t, f.eval (Fin.cons z y) = 0) ↔ Nat.size t < (buscar (no f)).eval (Fin.cons t y) := by
  obtain ⟨-, h2, h3⟩ := buscar_spec (no f) y t
  constructor
  · intro h
    by_contra hle
    have := (no_vale f _).mp (h2 (by omega))
    exact this (h _ (by omega))
  · intro h z hz
    by_contra hne
    have := h3 z hz ((no_vale f _).mpr hne)
    omega

/-- Y si no vale en todo el rango, `buscar (no f)` da el contraejemplo. Es la función testigo que vuelve universal
la equivalencia. -/
theorem paraTodo_testigo {n : ℕ} (f : Cob (n + 1)) (t : ℕ) (y : Fin n → ℕ)
    (h : (buscar (no f)).eval (Fin.cons t y) ≤ Nat.size t) :
    f.eval (Fin.cons ((buscar (no f)).eval (Fin.cons t y)) y) ≠ 0 :=
  (no_vale f _).mp ((buscar_spec (no f) y t).2.1 h)

/-! ## El arranque: la inducción por bits como enunciado universal -/

/-- **El primer fallo.** Recorre los prefijos binarios de `b`, del más corto al más largo, y entrega `p + 1` con `p`
el primero en que `f` no vale; o `0` si vale en todos. -/
def primerFallo {n : ℕ} (f : Cob (n + 1)) : Cob (n + 1) :=
  .rn (c3 .cond (fijar f .cero) .cero uno)
    (c3 .cond (.proy 1)
      (c3 .cond (.comp f (Fin.cons (.proy 0) fun i => .proy i.succ.succ)) .cero (c1 .suc (.proy 0)))
      (.proy 1))
    (c1 .suc (.proy 0))

theorem primerFallo_spec {n : ℕ} (f : Cob (n + 1)) (y : Fin n → ℕ) :
    ∀ b : ℕ, let R := fun x => (primerFallo f).eval (Fin.cons x y)
      R b ≤ b + 1 ∧ (R b = 0 → f.eval (Fin.cons b y) = 0) ∧
        ∀ p, R b = p + 1 → f.eval (Fin.cons p y) ≠ 0 ∧ (p = 0 ∨ R (p / 2) = 0) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  by_cases hb : b = 0
  · subst hb
    simp only [primerFallo, eval_rec_cero, eval_c3, eval_fijar, eval_cero, eval_cond, eval_uno]
    split
    · rename_i h0; exact ⟨by omega, fun _ => h0, fun p hp => absurd hp (by omega)⟩
    · rename_i h0
      refine ⟨le_refl _, fun h => absurd h (by omega), fun p hp => ?_⟩
      obtain rfl : p = 0 := by omega
      exact ⟨h0, .inl rfl⟩
  · obtain ⟨ih1, ih2, ih3⟩ := ih (b / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide))
    simp only at ih1 ih2 ih3 ⊢
    have eR : (primerFallo f).eval (Fin.cons b y) =
        min ((c3 .cond (.proy 1)
          (c3 .cond (.comp f (Fin.cons (.proy 0) fun i => .proy i.succ.succ)) .cero (c1 .suc (.proy 0)))
          (.proy 1)).eval
            (Fin.cons b (Fin.cons ((primerFallo f).eval (Fin.cons (b / 2) y)) y) : Fin (n + 2) → ℕ))
          (b + 1) := by
      rw [primerFallo, eval_rec_pos _ _ _ _ hb, ← primerFallo]; simp
    have ef : (Cob.comp f (Fin.cons (.proy 0) fun i => .proy i.succ.succ)).eval
        (Fin.cons b (Fin.cons ((primerFallo f).eval (Fin.cons (b / 2) y)) y) : Fin (n + 2) → ℕ) =
          f.eval (Fin.cons b y) := by
      simp only [Cob.eval]; congr 1; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [eR]
    simp only [eval_c3, eval_c1, eval_cond, eval_proy, eval_suc, eval_cero, ef, Fin.cons_zero,
      Fin.cons_one]
    generalize hr : (primerFallo f).eval (Fin.cons (b / 2) y) = r at ih1 ih2 ih3
    by_cases r0 : r = 0
    · simp only [r0, ↓reduceIte]
      split
      · rename_i h0
        rw [min_eq_left (Nat.zero_le _)]
        exact ⟨Nat.zero_le _, fun _ => h0, fun p hp => absurd hp (by omega)⟩
      · rename_i h0
        rw [min_eq_left (le_refl _)]
        refine ⟨le_refl _, fun h => absurd h (by omega), fun p hp => ?_⟩
        obtain rfl : p = b := by omega
        exact ⟨h0, .inr (hr.trans r0)⟩
    · simp only [r0, ↓reduceIte]
      rw [min_eq_left (by omega)]
      refine ⟨by omega, fun h => absurd h r0, fun p hp => ih3 p hp⟩

/-- **La inducción por bits, como enunciado universal.** Si `f` no vale en `b`, entonces o no vale en `0`, o hay un
`p` (que da `primerFallo`) en que el paso de `⌊p/2⌋` a `p` falla. No tiene ningún «existe»: el `p` es un término.
Por eso, en cualquier modelo de la teoría universal verdadera, vale la inducción por bits sin cuantificadores. -/
theorem pind_abierta {n : ℕ} (f : Cob (n + 1)) (y : Fin n → ℕ) (b : ℕ) (hb : f.eval (Fin.cons b y) ≠ 0) :
    f.eval (Fin.cons 0 y) ≠ 0 ∨
      ((primerFallo f).eval (Fin.cons b y) - 1 ≠ 0 ∧
        f.eval (Fin.cons (((primerFallo f).eval (Fin.cons b y) - 1) / 2) y) = 0 ∧
        f.eval (Fin.cons ((primerFallo f).eval (Fin.cons b y) - 1) y) ≠ 0) := by
  obtain ⟨_, h2, h3⟩ := primerFallo_spec f y b
  simp only at h2 h3
  generalize hq : (primerFallo f).eval (Fin.cons b y) = q at h2 h3 ⊢
  have hq0 : q ≠ 0 := fun h => hb (h2 h)
  obtain ⟨hp1, hp2⟩ := h3 (q - 1) (by omega)
  generalize q - 1 = p at hp1 hp2 ⊢
  rcases hp2 with rfl | hp2
  · exact .inl hp1
  · by_cases hp0 : p = 0
    · subst hp0; exact .inl hp1
    · exact .inr ⟨hp0, (primerFallo_spec f y (p / 2)).2.1 hp2, hp1⟩

/-! ## Ejemplos que se ejecutan -/

/-- `x` es par. -/
def par : Cob 1 := c2 .resta (.proy 0) (c2 .prod (c1 .mitad (.proy 0)) (c1 .suc (c1 .suc .cero)))

/-- El menor `z ≤ |13| = 4` que es par, con `z` el único argumento de `par`: es `0`. -/
example : (buscar (n := 0) par).eval ![13] = 0 := by decide

/-- El menor `z ≤ |13|` que no es par: es `1`. -/
example : (buscar (n := 0) (no par)).eval ![13] = 1 := by decide

/-- `13 = 1101₂`: sus prefijos son `0, 1, 3, 6, 13`. El primero que no es par es `1`; `primerFallo` entrega `2`. -/
example : (primerFallo (n := 0) par).eval ![13] = 2 := by decide

end Cobham
end Sagitta.Map
