import Sagitta.Map.Cerradura
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Common

/-!
# El lema del testigo, piloto

Un fragmento mínimo para probar el diseño: primero sin inducción, y después con la regla de inducción por bits. Sigue el método de S. R. Buss,
«First-Order Proof Theory of Arithmetic» (*Handbook of Proof Theory*, 1998), sección 3: de una derivación de
`Γ → Δ` sale una función que convierte testigos de `Γ` en un testigo de alguna fórmula de `Δ`.

## Qué hay

* **Términos con sintaxis** (`Termino`): el lenguaje de Buss (`0`, sucesor, `+`, `·`, `⌊x/2⌋`, `|x|`, `#`).
  Tienen sustitución, y su valor mide a lo sumo un polinomio en el largo de las variables
  (`Termino.largo_val_le`, `Termino.cotaLargo_acotada`).
* **Fórmulas**: átomos con sintaxis (`t ≤ u`, `t = u` y sus negaciones), «y», «o», «existe `x ≤ t`» y «para todo
  `x ≤ |t|`» (el rango pequeño), anidados como se quiera. Son las fórmulas Σᵇ₁ en forma normal de negación. La sintaxis es propia y no usa la teoría de modelos de Mathlib, que define «existe»
  como «no para todo no» y con eso estorba al contar cuantificadores.
* **Testigos**: un árbol (`Arbol`). El de un «existe» es el valor seguido del testigo del cuerpo; el de un «para
  todo» pequeño es la fila de los testigos del cuerpo, uno por cada valor. Revisar un testigo es un cómputo
  (`revisa`).
* **Derivaciones**: un cálculo de secuentes como *dato* (`Deriv` vive en `Type`), con identidad, hechos
  aritméticos entre átomos, reglas de estructura, **corte**, y las dos reglas del «existe» acotado.
* **Inducción por bits** (`Deriv.pind`, la PIND de Buss): de `A(⌊b/2⌋) → A(b)` sale `A(0) → A(t)`. Su extracción es
  un bucle (`lazo`) que da una vuelta por cada bit de `t`, y en cada vuelta usa una vez la función del paso.
* **El «para todo» pequeño** (`Deriv.ptDer`, `Deriv.ptIzq`): a la derecha la extracción es otro bucle corto
  (`barrer`), que junta un testigo por cada valor; a la izquierda busca en la fila el que hace falta.
* **`extraer`**: la función del lema, definida por recursión sobre la derivación. Se ejecuta: no usa el axioma de
  elección ni decide nada, solo arma y desarma listas. El corte se vuelve composición.
* **`teorema_del_testigo`**: de una derivación de «existe `x ≤ t` con `φ`» sale una función que da el `x`.

## Qué no hay

* **Tiempo de máquina.** Lo que hay es una cuenta de *pasos de regla*: `extraerC` devuelve, junto al testigo,
  cuántas reglas ejecutó, y `pasos_le` con `Deriv.cota_acotada` dicen que esa cuenta es polinomial en el largo de
  las entradas. Cada paso evalúa a lo sumo un término, cuyo valor es de largo polinomial. Falta traducir eso a pasos
  de una máquina y enlazarlo con `EsPolinomial` de `Clases.lean`.
* **Derivar todo de los axiomas.** La regla `aritm` acepta cualquier hecho verdadero entre átomos. Los axiomas
  BASIC son casos suyos, y `Basicos.lean` dice cuándo una derivación usa solo esos; los ejemplos de este archivo
  usan hechos más cómodos.
* **Eliminación de cortes.** Aquí no hace falta, ni con la inducción: la sintaxis solo tiene fórmulas de la forma
  permitida, así que toda fórmula de corte y toda fórmula de inducción ya lo es. En la teoría de verdad las
  derivaciones traen fórmulas arbitrarias, y la eliminación de cortes libres es lo que las reduce a este caso.

Las cotas de las reglas del «existe» a la derecha y del «para todo» a la izquierda son premisas del cálculo, no
hechos externos. Partir en casos sobre un átomo es una regla (`Deriv.casos`), y es el único lugar donde la
extracción evalúa un átomo.
-/

namespace Sagitta.Map
namespace Extraccion

open Cerradura (Acotada)

/-- Un entorno da valor a las variables. La variable `0` es la ligada más recientemente. -/
abbrev Entorno := ℕ → ℕ

/-- Agregar un valor al frente del entorno. -/
def ext (a : ℕ) (ρ : Entorno) : Entorno
  | 0 => a
  | i + 1 => ρ i

/-- Quitar la variable del frente. -/
def cola (ρ : Entorno) : Entorno := fun i => ρ (i + 1)

/-- Un entorno es chico si todas sus variables miden a lo sumo `n` bits. -/
def Chico (n : ℕ) (ρ : Entorno) : Prop := ∀ i, Nat.size (ρ i) ≤ n

theorem Chico.mono {n m : ℕ} {ρ : Entorno} (h : Chico n ρ) (hnm : n ≤ m) : Chico m ρ :=
  fun i => Nat.le_trans (h i) hnm

theorem Chico.ext {n m b : ℕ} {ρ : Entorno} (h : Chico n ρ) (hb : Nat.size b ≤ m) : Chico (n + m) (ext b ρ)
  | 0 => Nat.le_trans hb (Nat.le_add_left _ _)
  | i + 1 => Nat.le_trans (h i) (Nat.le_add_right _ _)

/-! ## Términos -/

/-- **Términos.** El lenguaje de la aritmética acotada de Buss. -/
inductive Termino : Type
  | var (i : ℕ)
  | cero
  | suc (t : Termino)
  | suma (t u : Termino)
  | prod (t u : Termino)
  /-- `⌊t/2⌋`. -/
  | mitad (t : Termino)
  /-- `|t|`, el largo en bits. -/
  | largo (t : Termino)
  /-- `t # u = 2^(|t|·|u|)`. -/
  | smash (t u : Termino)

namespace Termino

/-- El valor de un término. -/
def val : Termino → Entorno → ℕ
  | var i, ρ => ρ i
  | cero, _ => 0
  | suc t, ρ => t.val ρ + 1
  | suma t u, ρ => t.val ρ + u.val ρ
  | prod t u, ρ => t.val ρ * u.val ρ
  | mitad t, ρ => t.val ρ / 2
  | largo t, ρ => Nat.size (t.val ρ)
  | smash t u, ρ => 2 ^ (Nat.size (t.val ρ) * Nat.size (u.val ρ))

/-- Sustitución simultánea. -/
def subst (σ : ℕ → Termino) : Termino → Termino
  | var i => σ i
  | cero => cero
  | suc t => suc (t.subst σ)
  | suma t u => suma (t.subst σ) (u.subst σ)
  | prod t u => prod (t.subst σ) (u.subst σ)
  | mitad t => mitad (t.subst σ)
  | largo t => largo (t.subst σ)
  | smash t u => smash (t.subst σ) (u.subst σ)

/-- El entorno que una sustitución induce. -/
def entornoDe (σ : ℕ → Termino) (ρ : Entorno) : Entorno := fun i => (σ i).val ρ

/-- Sustituir y evaluar es evaluar en el entorno inducido. -/
theorem val_subst (σ : ℕ → Termino) (ρ : Entorno) : ∀ t : Termino, (t.subst σ).val ρ = t.val (entornoDe σ ρ)
  | var _ => rfl
  | cero => rfl
  | suc t => by simp [subst, val, val_subst σ ρ t]
  | suma t u => by simp [subst, val, val_subst σ ρ t, val_subst σ ρ u]
  | prod t u => by simp [subst, val, val_subst σ ρ t, val_subst σ ρ u]
  | mitad t => by simp [subst, val, val_subst σ ρ t]
  | largo t => by simp [subst, val, val_subst σ ρ t]
  | smash t u => by simp [subst, val, val_subst σ ρ t, val_subst σ ρ u]

/-- Pasar a un contexto con una variable más al frente. -/
def sube (t : Termino) : Termino := t.subst fun i => var (i + 1)

theorem val_sube (t : Termino) (b : ℕ) (ρ : Entorno) : t.sube.val (ext b ρ) = t.val ρ :=
  val_subst _ _ t

/-- Una sustitución, debajo de un «existe»: la variable ligada se deja en su lugar. -/
def arriba (σ : ℕ → Termino) : ℕ → Termino
  | 0 => var 0
  | i + 1 => (σ i).sube

theorem entornoDe_arriba (σ : ℕ → Termino) (a : ℕ) (ρ : Entorno) :
    entornoDe (arriba σ) (ext a ρ) = ext a (entornoDe σ ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact val_subst _ _ (σ i)

/-- **Cota del largo.** Con variables de a lo sumo `n` bits, el valor del término mide a lo sumo `cotaLargo n`. -/
def cotaLargo : Termino → ℕ → ℕ
  | var _, n => n
  | cero, _ => 0
  | suc t, n => t.cotaLargo n + 1
  | suma t u, n => t.cotaLargo n + u.cotaLargo n + 1
  | prod t u, n => t.cotaLargo n + u.cotaLargo n
  | mitad t, n => t.cotaLargo n
  | largo t, n => t.cotaLargo n
  | smash t u, n => t.cotaLargo n * u.cotaLargo n + 1

private theorem size_de_lt {m n : ℕ} (h : m < 2 ^ n) : Nat.size m ≤ n := Nat.size_le.mpr h

/-- **Los términos no agrandan más que un polinomio.** -/
theorem largo_val_le {n : ℕ} {ρ : Entorno} (h : Chico n ρ) : ∀ t : Termino, Nat.size (t.val ρ) ≤ t.cotaLargo n
  | var i => h i
  | cero => by simp [val, cotaLargo]
  | suc t => by
      have ht := Nat.size_le.mp (largo_val_le h t)
      refine size_de_lt ?_
      simp only [val, cotaLargo, Nat.pow_succ]; omega
  | suma t u => by
      have ht := Nat.size_le.mp (largo_val_le h t)
      have hu := Nat.size_le.mp (largo_val_le h u)
      refine size_de_lt ?_
      have h1 : 2 ^ t.cotaLargo n ≤ 2 ^ (t.cotaLargo n + u.cotaLargo n) :=
        Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
      have h2 : 2 ^ u.cotaLargo n ≤ 2 ^ (t.cotaLargo n + u.cotaLargo n) :=
        Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
      simp only [val, cotaLargo, Nat.pow_succ]; omega
  | prod t u => by
      have ht := Nat.size_le.mp (largo_val_le h t)
      have hu := Nat.size_le.mp (largo_val_le h u)
      refine size_de_lt ?_
      simp only [val, cotaLargo, Nat.pow_add]
      exact Nat.mul_lt_mul'' ht hu
  | mitad t => Nat.le_trans (Nat.size_le_size (Nat.div_le_self _ _)) (largo_val_le h t)
  | largo t =>
      Nat.le_trans (Nat.size_le_size (Nat.size_le.mpr Nat.lt_two_pow_self)) (largo_val_le h t)
  | smash t u => by
      simp only [val, cotaLargo, Nat.size_pow]
      exact Nat.succ_le_succ (Nat.mul_le_mul (largo_val_le h t) (largo_val_le h u))

/-- La cota del largo crece con `n`. -/
theorem cotaLargo_mono : ∀ (t : Termino) {a b : ℕ}, a ≤ b → t.cotaLargo a ≤ t.cotaLargo b
  | var _, _, _, h => h
  | cero, _, _, _ => Nat.le_refl _
  | suc t, _, _, h => Nat.succ_le_succ (cotaLargo_mono t h)
  | suma t u, _, _, h => Nat.succ_le_succ (Nat.add_le_add (cotaLargo_mono t h) (cotaLargo_mono u h))
  | prod t u, _, _, h => Nat.add_le_add (cotaLargo_mono t h) (cotaLargo_mono u h)
  | mitad t, _, _, h => cotaLargo_mono t h
  | largo t, _, _, h => cotaLargo_mono t h
  | smash t u, _, _, h => Nat.succ_le_succ (Nat.mul_le_mul (cotaLargo_mono t h) (cotaLargo_mono u h))

theorem acotada_const (c : ℕ) : Acotada fun _ => c := ⟨Polynomial.C c, fun _ => by simp⟩

theorem acotada_id : Acotada fun n => n := ⟨Polynomial.X, fun _ => by simp⟩

/-- La cota del largo es un polinomio. -/
theorem cotaLargo_acotada : ∀ t : Termino, Acotada t.cotaLargo
  | var _ => acotada_id
  | cero => acotada_const 0
  | suc t => Cerradura.suma (cotaLargo_acotada t) (acotada_const 1)
  | suma t u => Cerradura.suma (Cerradura.suma (cotaLargo_acotada t) (cotaLargo_acotada u)) (acotada_const 1)
  | prod t u => Cerradura.suma (cotaLargo_acotada t) (cotaLargo_acotada u)
  | mitad t => cotaLargo_acotada t
  | largo t => cotaLargo_acotada t
  | smash t u =>
      Cerradura.suma (Cerradura.producto (cotaLargo_acotada t) (cotaLargo_acotada u)) (acotada_const 1)

end Termino

open Termino (entornoDe)

/-! ## Árboles de testigos -/

/-- **El testigo es un árbol.** `nodo a w` es el valor de un «existe» seguido del testigo del cuerpo. `cons v w`
es una fila: el testigo `v` seguido del resto. `hoja` cierra una fila y atestigua un átomo. -/
inductive Arbol : Type
  | hoja
  | nodo (a : ℕ) (w : Arbol)
  | cons (v w : Arbol)
  deriving DecidableEq

/-- Una fila de `k` testigos: el primero es el de `x = k - 1` y el último el de `x = 0`. -/
def Todos (P : ℕ → Arbol → Prop) : ℕ → Arbol → Prop
  | 0, .hoja => True
  | 0, _ => False
  | k + 1, .cons v w => P k v ∧ Todos P k w
  | _ + 1, _ => False

/-- Revisar una fila, como cómputo. -/
def todosB (f : ℕ → Arbol → Bool) : ℕ → Arbol → Bool
  | 0, .hoja => true
  | 0, _ => false
  | k + 1, .cons v w => f k v && todosB f k w
  | _ + 1, _ => false

theorem todosB_iff {f : ℕ → Arbol → Bool} {P : ℕ → Arbol → Prop} (h : ∀ x v, f x v = true ↔ P x v) :
    ∀ (k : ℕ) (w : Arbol), todosB f k w = true ↔ Todos P k w := by
  intro k
  induction k with
  | zero => intro w; cases w <;> simp [todosB, Todos]
  | succ k ih => intro w; cases w <;> simp [todosB, Todos, h, ih]

theorem todos_congr {P Q : ℕ → Arbol → Prop} (h : ∀ x v, P x v ↔ Q x v) :
    ∀ (k : ℕ) (w : Arbol), Todos P k w ↔ Todos Q k w := by
  intro k
  induction k with
  | zero => intro w; cases w <;> simp [Todos]
  | succ k ih => intro w; cases w <;> simp [Todos, h, ih]

/-- Hay fila si y solo si hay testigo para cada valor. -/
theorem todos_existe {P : ℕ → Arbol → Prop} :
    ∀ k : ℕ, (∀ x, x < k → ∃ v, P x v) ↔ ∃ w, Todos P k w := by
  intro k
  induction k with
  | zero => exact ⟨fun _ => ⟨.hoja, trivial⟩, fun _ x hx => absurd hx (Nat.not_lt_zero _)⟩
  | succ k ih =>
    constructor
    · intro h
      obtain ⟨v, hv⟩ := h k (Nat.lt_succ_self k)
      obtain ⟨w, hw⟩ := ih.mp fun x hx => h x (Nat.lt_succ_of_lt hx)
      exact ⟨.cons v w, hv, hw⟩
    · rintro ⟨w, hw⟩ x hx
      cases w with
      | hoja => exact hw.elim
      | nodo _ _ => exact hw.elim
      | cons v w =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | rfl
        · exact ih.mpr ⟨w, hw.2⟩ x h
        · exact ⟨v, hw.1⟩

/-- Sacar de la fila el testigo de un valor. -/
def Todos.dame {P : ℕ → Arbol → Prop} : (k : ℕ) → (w : Arbol) → Todos P k w → (x : ℕ) → x < k → {v // P x v}
  | 0, _, _, _, hx => absurd hx (Nat.not_lt_zero _)
  | _ + 1, .hoja, h, _, _ => h.elim
  | _ + 1, .nodo _ _, h, _, _ => h.elim
  | k + 1, .cons v w, h, x, hx =>
      if e : x = k then ⟨v, e ▸ h.1⟩
      else Todos.dame k w h.2 x (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hx) e)

/-! ## Fórmulas y testigos -/

/-- Las relaciones de los átomos: menor o igual, igual, y sus negaciones. -/
inductive Rel : Type
  | le | eq | nle | neq

/-- El valor de una relación entre dos números. -/
def Rel.vale : Rel → ℕ → ℕ → Bool
  | .le, a, b => decide (a ≤ b)
  | .eq, a, b => decide (a = b)
  | .nle, a, b => !decide (a ≤ b)
  | .neq, a, b => !decide (a = b)

theorem Rel.vale_le {a b : ℕ} : Rel.vale .le a b = true ↔ a ≤ b := by simp [Rel.vale]

theorem Rel.vale_eq {a b : ℕ} : Rel.vale .eq a b = true ↔ a = b := by simp [Rel.vale]

theorem Rel.vale_neq {a b : ℕ} : Rel.vale .neq a b = true ↔ a ≠ b := by simp [Rel.vale]

/-- La relación contraria. -/
def Rel.neg : Rel → Rel
  | .le => .nle | .eq => .neq | .nle => .le | .neq => .eq

/-- **Átomos con sintaxis**: una relación entre dos términos. -/
structure Lit : Type where
  rel : Rel
  izq : Termino
  der : Termino

namespace Lit

def vale (l : Lit) (ρ : Entorno) : Bool := l.rel.vale (l.izq.val ρ) (l.der.val ρ)

def subst (σ : ℕ → Termino) (l : Lit) : Lit := ⟨l.rel, l.izq.subst σ, l.der.subst σ⟩

theorem vale_subst (σ : ℕ → Termino) (l : Lit) (ρ : Entorno) : (l.subst σ).vale ρ = l.vale (entornoDe σ ρ) := by
  simp only [vale, subst, Termino.val_subst]

/-- El átomo contrario. -/
def neg (l : Lit) : Lit := ⟨l.rel.neg, l.izq, l.der⟩

theorem neg_vale_de {l : Lit} {ρ : Entorno} (h : ¬ l.vale ρ = true) : l.neg.vale ρ = true := by
  obtain ⟨r, t, u⟩ := l
  cases r <;> simp_all [vale, neg, Rel.vale, Rel.neg]

end Lit

/-- Fórmulas Σᵇ₁ en forma normal de negación: átomos, «y», «o», «existe» acotado y «para todo» sobre un rango
pequeño. -/
inductive Formula : Type
  | atomo (l : Lit) : Formula
  | conj (φ ψ : Formula) : Formula
  | disy (φ ψ : Formula) : Formula
  /-- «Existe `x ≤ t` tal que `φ`». En `φ`, la variable `0` es `x`. -/
  | ex (t : Termino) (φ : Formula) : Formula
  /-- «Para todo `x ≤ |t|` vale `φ`». El rango es pequeño: tiene tantos valores como bits tiene `t`, más uno. -/
  | pt (t : Termino) (φ : Formula) : Formula

namespace Formula

/-- La verdad de una fórmula en un entorno. -/
def Vale : Formula → Entorno → Prop
  | atomo l, ρ => l.vale ρ = true
  | conj φ ψ, ρ => Vale φ ρ ∧ Vale ψ ρ
  | disy φ ψ, ρ => Vale φ ρ ∨ Vale ψ ρ
  | ex t φ, ρ => ∃ a, a ≤ t.val ρ ∧ Vale φ (ext a ρ)
  | pt t φ, ρ => ∀ x, x ≤ Nat.size (t.val ρ) → Vale φ (ext x ρ)

/-- **El predicado de testigo.**

* átomo: la hoja;
* «y»: el par de los dos testigos;
* «o»: una marca (`0` izquierda, `1` derecha) y el testigo del lado elegido;
* «existe `x ≤ t`»: el valor de `x` y el testigo del cuerpo;
* «para todo `x ≤ |t|`»: la fila de los testigos del cuerpo, uno por cada `x`. -/
def Testigo : Formula → Entorno → Arbol → Prop
  | atomo l, ρ, w => w = .hoja ∧ l.vale ρ = true
  | conj φ ψ, ρ, .cons v w => Testigo φ ρ v ∧ Testigo ψ ρ w
  | conj _ _, _, _ => False
  | disy φ _, ρ, .nodo 0 w => Testigo φ ρ w
  | disy _ ψ, ρ, .nodo 1 w => Testigo ψ ρ w
  | disy _ _, _, _ => False
  | ex t φ, ρ, .nodo a w => a ≤ t.val ρ ∧ Testigo φ (ext a ρ) w
  | ex _ _, _, _ => False
  | pt t φ, ρ, w => Todos (fun x v => Testigo φ (ext x ρ) v) (Nat.size (t.val ρ) + 1) w

/-- Revisar un testigo, como cómputo. -/
def revisa : Formula → Entorno → Arbol → Bool
  | atomo l, ρ, w => decide (w = .hoja) && l.vale ρ
  | conj φ ψ, ρ, .cons v w => revisa φ ρ v && revisa ψ ρ w
  | conj _ _, _, _ => false
  | disy φ _, ρ, .nodo 0 w => revisa φ ρ w
  | disy _ ψ, ρ, .nodo 1 w => revisa ψ ρ w
  | disy _ _, _, _ => false
  | ex t φ, ρ, .nodo a w => decide (a ≤ t.val ρ) && revisa φ (ext a ρ) w
  | ex _ _, _, _ => false
  | pt t φ, ρ, w => todosB (fun x v => revisa φ (ext x ρ) v) (Nat.size (t.val ρ) + 1) w

/-- Revisar es decidir el predicado de testigo. -/
theorem revisa_iff (φ : Formula) : ∀ (ρ : Entorno) (w : Arbol), revisa φ ρ w = true ↔ Testigo φ ρ w := by
  induction φ with
  | atomo l => intro ρ w; simp [revisa, Testigo]
  | conj φ ψ ih₁ ih₂ => intro ρ w; cases w <;> simp [revisa, Testigo, ih₁, ih₂]
  | disy φ ψ ih₁ ih₂ =>
    intro ρ w
    rcases w with _ | ⟨_ | _ | k, w⟩ | ⟨v, w⟩ <;> simp [revisa, Testigo, ih₁, ih₂]
  | ex t φ ih => intro ρ w; cases w <;> simp [revisa, Testigo, ih]
  | pt t φ ih => intro ρ w; exact todosB_iff (fun x v => ih _ _) _ _

/-- **Una fórmula vale si y solo si tiene testigo.** -/
theorem vale_iff_testigo (φ : Formula) : ∀ ρ : Entorno, Vale φ ρ ↔ ∃ w, Testigo φ ρ w := by
  induction φ with
  | atomo l => intro ρ; exact ⟨fun h => ⟨.hoja, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  | conj φ ψ ih₁ ih₂ =>
    intro ρ
    constructor
    · rintro ⟨h₁, h₂⟩
      obtain ⟨v, hv⟩ := (ih₁ _).mp h₁
      obtain ⟨w, hw⟩ := (ih₂ _).mp h₂
      exact ⟨.cons v w, hv, hw⟩
    · rintro ⟨w, hw⟩
      cases w with
      | hoja => exact hw.elim
      | nodo _ _ => exact hw.elim
      | cons v w => exact ⟨(ih₁ _).mpr ⟨v, hw.1⟩, (ih₂ _).mpr ⟨w, hw.2⟩⟩
  | disy φ ψ ih₁ ih₂ =>
    intro ρ
    constructor
    · rintro (h | h)
      · obtain ⟨w, hw⟩ := (ih₁ _).mp h
        exact ⟨.nodo 0 w, hw⟩
      · obtain ⟨w, hw⟩ := (ih₂ _).mp h
        exact ⟨.nodo 1 w, hw⟩
    · rintro ⟨w, hw⟩
      rcases w with _ | ⟨_ | _ | k, w⟩ | ⟨v, w⟩
      · exact hw.elim
      · exact .inl ((ih₁ _).mpr ⟨w, hw⟩)
      · exact .inr ((ih₂ _).mpr ⟨w, hw⟩)
      · exact hw.elim
      · exact hw.elim
  | ex t φ ih =>
    intro ρ
    constructor
    · rintro ⟨a, ha, hv⟩
      obtain ⟨w, hw⟩ := (ih _).mp hv
      exact ⟨.nodo a w, ha, hw⟩
    · rintro ⟨w, hw⟩
      cases w with
      | hoja => exact hw.elim
      | cons _ _ => exact hw.elim
      | nodo a w => exact ⟨a, hw.1, (ih _).mpr ⟨w, hw.2⟩⟩
  | pt t φ ih =>
    intro ρ
    refine Iff.trans ?_ (todos_existe _)
    exact ⟨fun h x hx => (ih _).mp (h x (Nat.le_of_lt_succ hx)),
      fun h x hx => (ih _).mpr (h x (Nat.lt_succ_of_le hx))⟩

/-- Sustitución en una fórmula. -/
def subst : (ℕ → Termino) → Formula → Formula
  | σ, atomo l => atomo (l.subst σ)
  | σ, conj φ ψ => conj (subst σ φ) (subst σ ψ)
  | σ, disy φ ψ => disy (subst σ φ) (subst σ ψ)
  | σ, ex t φ => ex (t.subst σ) (subst (Termino.arriba σ) φ)
  | σ, pt t φ => pt (t.subst σ) (subst (Termino.arriba σ) φ)

/-- Sustituir no cambia los testigos. -/
theorem testigo_subst (φ : Formula) :
    ∀ (σ : ℕ → Termino) (ρ : Entorno) (w : Arbol), Testigo (subst σ φ) ρ w ↔ Testigo φ (entornoDe σ ρ) w := by
  induction φ with
  | atomo l => intro σ ρ w; simp only [subst, Testigo, Lit.vale_subst]
  | conj φ ψ ih₁ ih₂ =>
    intro σ ρ w
    cases w with
    | hoja => exact Iff.rfl
    | nodo _ _ => exact Iff.rfl
    | cons v w => simp only [subst, Testigo, ih₁, ih₂]
  | disy φ ψ ih₁ ih₂ =>
    intro σ ρ w
    rcases w with _ | ⟨_ | _ | k, w⟩ | ⟨v, w⟩
    · exact Iff.rfl
    · exact ih₁ σ ρ w
    · exact ih₂ σ ρ w
    · exact Iff.rfl
    · exact Iff.rfl
  | ex t φ ih =>
    intro σ ρ w
    cases w with
    | hoja => exact Iff.rfl
    | cons _ _ => exact Iff.rfl
    | nodo a w => simp only [subst, Testigo, Termino.val_subst, ih, Termino.entornoDe_arriba]
  | pt t φ ih =>
    intro σ ρ w
    simp only [subst, Testigo, Termino.val_subst]
    exact todos_congr (fun x v => by rw [ih, Termino.entornoDe_arriba]) _ _

/-- Sustituir la variable `0` por el término `s`. -/
def inst (s : Termino) (φ : Formula) : Formula :=
  subst (fun | 0 => s | i + 1 => .var i) φ

/-- Pasar a un contexto con una variable más al frente, que la fórmula no usa. -/
def sube (φ : Formula) : Formula := subst (fun i => .var (i + 1)) φ

/-- Leer la fórmula en la mitad de la variable `0`: de `φ(b)` a `φ(⌊b/2⌋)`. -/
def mitad (φ : Formula) : Formula :=
  subst (fun | 0 => .mitad (.var 0) | i + 1 => .var (i + 1)) φ

theorem testigo_inst (s : Termino) (φ : Formula) (ρ : Entorno) (w : Arbol) :
    Testigo (inst s φ) ρ w ↔ Testigo φ (ext (s.val ρ) ρ) w := by
  have e : entornoDe (fun | 0 => s | i + 1 => .var i) ρ = ext (s.val ρ) ρ := by
    funext i; cases i <;> rfl
  rw [inst, testigo_subst, e]

theorem testigo_sube (φ : Formula) (b : ℕ) (ρ : Entorno) (w : Arbol) :
    Testigo (sube φ) (ext b ρ) w ↔ Testigo φ ρ w := by
  have e : entornoDe (fun i => .var (i + 1)) (ext b ρ) = ρ := by
    funext i; rfl
  rw [sube, testigo_subst, e]

theorem testigo_mitad (φ : Formula) (b : ℕ) (ρ : Entorno) (w : Arbol) :
    Testigo (mitad φ) (ext b ρ) w ↔ Testigo φ (ext (b / 2) ρ) w := by
  have e : entornoDe (fun | 0 => .mitad (.var 0) | i + 1 => .var (i + 1)) (ext b ρ) = ext (b / 2) ρ := by
    funext i; cases i <;> rfl
  rw [mitad, testigo_subst, e]

end Formula

open Formula

/-- El átomo «la variable `0` no pasa de `t`», donde `t` vive en el contexto de afuera. -/
def cota (t : Termino) : Lit := ⟨.le, .var 0, t.sube⟩

theorem cota_vale (t : Termino) (b : ℕ) (ρ : Entorno) : (cota t).vale (ext b ρ) = decide (b ≤ t.val ρ) := by
  simp only [cota, Lit.vale, Rel.vale, Termino.val_sube]; rfl

/-! ## Derivaciones -/

/-- **Derivaciones.** Un cálculo de secuentes `Γ → Δ` como dato. -/
inductive Deriv : List Formula → List Formula → Type
  /-- Identidad. -/
  | id (φ : Formula) : Deriv [φ] [φ]
  /-- Un hecho aritmético entre átomos: si valen los de la izquierda, vale alguno de la derecha. Los axiomas
  BASIC y los de la igualdad son casos de esta regla (`Basicos.lean`). -/
  | aritm (ps qs : List Lit)
      (h : ∀ ρ, (∀ q ∈ ps, q.vale ρ = true) → ∃ q ∈ qs, q.vale ρ = true) : Deriv (ps.map atomo) (qs.map atomo)
  | debilIzq {Γ Δ} (φ : Formula) : Deriv Γ Δ → Deriv (φ :: Γ) Δ
  | debilDer {Γ Δ} (φ : Formula) : Deriv Γ Δ → Deriv Γ (φ :: Δ)
  | contrIzq {Γ Δ φ} : Deriv (φ :: φ :: Γ) Δ → Deriv (φ :: Γ) Δ
  | contrDer {Γ Δ φ} : Deriv Γ (φ :: φ :: Δ) → Deriv Γ (φ :: Δ)
  | cambIzq {Γ Δ φ ψ} : Deriv (φ :: ψ :: Γ) Δ → Deriv (ψ :: φ :: Γ) Δ
  | cambDer {Γ Δ φ ψ} : Deriv Γ (φ :: ψ :: Δ) → Deriv Γ (ψ :: φ :: Δ)
  /-- Corte: usar un lema intermedio. -/
  | corte {Γ Δ} (φ : Formula) : Deriv Γ (φ :: Δ) → Deriv (φ :: Γ) Δ → Deriv Γ Δ
  /-- Partir en casos sobre un átomo: vale o vale su contrario. -/
  | casos {Γ Δ} (l : Lit) : Deriv (atomo l :: Γ) Δ → Deriv (atomo l.neg :: Γ) Δ → Deriv Γ Δ
  | conjDer {Γ Δ φ ψ} : Deriv Γ (φ :: Δ) → Deriv Γ (ψ :: Δ) → Deriv Γ (conj φ ψ :: Δ)
  | conjIzq {Γ Δ φ ψ} : Deriv (φ :: ψ :: Γ) Δ → Deriv (conj φ ψ :: Γ) Δ
  | disyDer {Γ Δ φ ψ} : Deriv Γ (φ :: ψ :: Δ) → Deriv Γ (disy φ ψ :: Δ)
  | disyIzq {Γ Δ φ ψ} : Deriv (φ :: Γ) Δ → Deriv (ψ :: Γ) Δ → Deriv (disy φ ψ :: Γ) Δ
  /-- «Existe» a la derecha: se exhibe el término `s`. Que `s` no pasa de la cota `t` es la primera premisa. -/
  | exDer {Γ Δ} (t s : Termino) (φ : Formula) :
      Deriv Γ [atomo ⟨.le, s, t⟩] → Deriv Γ (inst s φ :: Δ) → Deriv Γ (ex t φ :: Δ)
  /-- «Existe» a la izquierda: se razona con una variable nueva, de la que solo se sabe que cumple `φ` y la cota. -/
  | exIzq {Γ Δ} (t : Termino) (φ : Formula) :
      Deriv (atomo (cota t) :: φ :: Γ.map sube) (Δ.map sube) → Deriv (ex t φ :: Γ) Δ
  /-- «Para todo» pequeño a la derecha: se prueba el cuerpo para una variable nueva, de la que solo se sabe que
  está en el rango. -/
  | ptDer {Γ Δ} (t : Termino) (φ : Formula) :
      Deriv (atomo (cota (.largo t)) :: Γ.map sube) (φ :: Δ.map sube) → Deriv Γ (pt t φ :: Δ)
  /-- «Para todo» pequeño a la izquierda: se usa en el término `s`. Que `s` está en el rango es la primera
  premisa. -/
  | ptIzq {Γ Δ} (t s : Termino) (φ : Formula) :
      Deriv Γ [atomo ⟨.le, s, .largo t⟩] → Deriv (inst s φ :: Γ) Δ → Deriv (pt t φ :: Γ) Δ
  /-- **Inducción por bits** (PIND). En `φ` la variable `0` es la de inducción. La premisa vive en un contexto con
  una variable nueva `b`: de `φ(⌊b/2⌋)` se deriva `φ(b)`. La conclusión: de `φ(0)` se deriva `φ(t)`. -/
  | pind {Γ Δ} (t : Termino) (φ : Formula) :
      Deriv (mitad φ :: Γ.map sube) (φ :: Δ.map sube) → Deriv (inst .cero φ :: Γ) (inst t φ :: Δ)

/-- Testigos de un antecedente: uno por cada fórmula. -/
inductive Ant (ρ : Entorno) : List Formula → Type
  | nil : Ant ρ []
  | cons {φ Γ} (w : Arbol) (h : Testigo φ ρ w) : Ant ρ Γ → Ant ρ (φ :: Γ)

/-- Testigo de un sucedente: de alguna de sus fórmulas, con la marca de cuál. -/
inductive Suc (ρ : Entorno) : List Formula → Type
  | aqui {φ Δ} (w : Arbol) (h : Testigo φ ρ w) : Suc ρ (φ :: Δ)
  | alla {φ Δ} : Suc ρ Δ → Suc ρ (φ :: Δ)

/-- Los testigos de un antecedente sirven igual con una variable más al frente. -/
def Ant.sube {ρ : Entorno} (b : ℕ) : {Γ : List Formula} → Ant ρ Γ → Ant (ext b ρ) (Γ.map Formula.sube)
  | _, .nil => .nil
  | _, .cons w h a => .cons w ((testigo_sube _ b ρ w).mpr h) (Ant.sube b a)

/-- Y un testigo del sucedente con la variable extra baja al contexto original. -/
def Suc.baja {ρ : Entorno} (b : ℕ) : (Δ : List Formula) → Suc (ext b ρ) (Δ.map Formula.sube) → Suc ρ Δ
  | _ :: _, .aqui w h => .aqui w ((testigo_sube _ b ρ w).mp h)
  | _ :: Δ, .alla r => .alla (Suc.baja b Δ r)

/-- De los testigos de una lista de átomos, que todos valen. -/
theorem Ant.atomos {ρ : Entorno} : (ps : List Lit) → Ant ρ (ps.map atomo) → ∀ q ∈ ps, q.vale ρ = true
  | [], _ => fun _ hq => by simp at hq
  | p :: ps, .cons _ h a => fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h.2
      · exact Ant.atomos ps a q hq

/-- De una lista de átomos de la que alguno vale, el primero que vale. Es donde un hecho con varios átomos a la
derecha se vuelve cómputo: hay que evaluarlos. -/
def Suc.primero {ρ : Entorno} : (qs : List Lit) → (∃ q ∈ qs, q.vale ρ = true) → Suc ρ (qs.map atomo)
  | [], h => False.elim (by obtain ⟨_, hq, _⟩ := h; exact List.not_mem_nil hq)
  | l :: ls, h =>
      if hl : l.vale ρ = true then .aqui .hoja ⟨rfl, hl⟩
      else .alla (Suc.primero ls (by
        obtain ⟨q, hq, hv⟩ := h
        rcases List.mem_cons.mp hq with rfl | hq
        · exact absurd hv hl
        · exact ⟨q, hq, hv⟩))

/-- Un hecho con un solo átomo a la derecha. -/
def Deriv.aritm1 (ps : List Lit) (p : Lit) (h : ∀ ρ, (∀ q ∈ ps, q.vale ρ = true) → p.vale ρ = true) :
    Deriv (ps.map atomo) [atomo p] :=
  .aritm ps [p] fun ρ hq => ⟨p, List.mem_cons_self, h ρ hq⟩

/-- De un sucedente que es un solo átomo `s ≤ t`, la desigualdad. -/
theorem Suc.le {ρ : Entorno} {s t : Termino} : Suc ρ [atomo ⟨.le, s, t⟩] → s.val ρ ≤ t.val ρ
  | .aqui _ h => of_decide_eq_true h.2

/-- Del resultado de un bucle (un testigo de la fórmula principal, o la salida por una lateral) al sucedente. -/
def Suc.deSuma {ρ : Entorno} {φ : Formula} {Δ : List Formula} {P : Arbol → Prop}
    (f : ∀ w, P w → Testigo φ ρ w) : {w // P w} ⊕ Suc ρ Δ → Suc ρ (φ :: Δ)
  | .inl v => .aqui v.1 (f v.1 v.2)
  | .inr r => .alla r

/-! ## La extracción, con su cuenta de pasos -/

/-- **El bucle de la inducción por bits.** Lleva un testigo de `φ(0)` hasta uno de `φ(b)`, pasando por los prefijos
binarios de `b`: `⌊b/2ᵏ⌋, …, ⌊b/2⌋, b`. En cada vuelta aplica `paso` una vez. Si alguna vuelta atestigua una fórmula
lateral de `Δ`, se sale con ese testigo. Devuelve también los pasos gastados. El combustible solo sirve para que
la recursión sea estructural. -/
def lazo {ρ : Entorno} {φ : Formula} {Δ : List Formula}
    (base : {w // Testigo φ (ext 0 ρ) w})
    (paso : (b : ℕ) → {w // Testigo φ (ext (b / 2) ρ) w} → Suc (ext b ρ) (φ :: Δ.map Formula.sube) × ℕ) :
    (fuel b : ℕ) → b < 2 ^ fuel → ({w // Testigo φ (ext b ρ) w} ⊕ Suc ρ Δ) × ℕ
  | _, 0, _ => (.inl base, 0)
  | 0, _ + 1, h => absurd h (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le _)))
  | fuel + 1, b + 1, h =>
      match lazo base paso fuel ((b + 1) / 2) (by rw [Nat.pow_succ] at h; omega) with
      | (.inr r, c) => (.inr r, c)
      | (.inl v, c) =>
          match paso (b + 1) v with
          | (.aqui w' h', c') => (.inl ⟨w', h'⟩, c + c' + 1)
          | (.alla r, c') => (.inr (Suc.baja (b + 1) Δ r), c + c' + 1)

/-- Cuántas veces el bucle llama al paso, en el peor caso: una por cada bit. -/
def vueltas : (fuel b : ℕ) → ℕ
  | _, 0 => 0
  | 0, _ + 1 => 0
  | fuel + 1, b + 1 => vueltas fuel ((b + 1) / 2) + 1

/-- El largo de `b` en bits es uno más que el de su mitad. -/
theorem size_mitad (b : ℕ) (hb : b ≠ 0) : Nat.size b = Nat.size (b / 2) + 1 := by
  have e := Nat.bit_testBit_zero_shiftRight_one b
  have h : Nat.bit (b.testBit 0) (b >>> 1) ≠ 0 := by rw [e]; exact hb
  have hs := Nat.size_bit h
  rw [e, Nat.shiftRight_one] at hs
  exact hs

/-- **El bucle es corto.** Da a lo sumo tantas vueltas como bits tiene `b`: lineal en el largo de la entrada, no en
su valor. -/
theorem vueltas_le : ∀ fuel b : ℕ, vueltas fuel b ≤ Nat.size b
  | _, 0 => by simp [vueltas]
  | 0, _ + 1 => by simp [vueltas]
  | fuel + 1, b + 1 => by
      rw [vueltas, size_mitad (b + 1) (by omega)]
      exact Nat.succ_le_succ (vueltas_le fuel _)

/-- **Los pasos del bucle.** Si cada llamada al paso gasta a lo sumo `C`, el bucle gasta a lo sumo `C + 1` por
vuelta. -/
theorem lazo_pasos {ρ : Entorno} {φ : Formula} {Δ : List Formula}
    (base : {w // Testigo φ (ext 0 ρ) w})
    (paso : (b : ℕ) → {w // Testigo φ (ext (b / 2) ρ) w} → Suc (ext b ρ) (φ :: Δ.map Formula.sube) × ℕ)
    (B C : ℕ) (hp : ∀ b v, b ≤ B → (paso b v).2 ≤ C) :
    ∀ (fuel b : ℕ) (h : b < 2 ^ fuel), b ≤ B → (lazo base paso fuel b h).2 ≤ vueltas fuel b * (C + 1)
  | _, 0, _, _ => by simp [lazo]
  | 0, _ + 1, h, _ => absurd h (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le _)))
  | fuel + 1, b + 1, h, hb => by
      have ih := lazo_pasos base paso B C hp fuel ((b + 1) / 2) (by rw [Nat.pow_succ] at h; omega)
        (Nat.le_trans (Nat.div_le_self _ _) hb)
      rw [lazo, vueltas, Nat.add_mul, Nat.one_mul]
      generalize lazo base paso fuel ((b + 1) / 2) _ = r at ih ⊢
      obtain ⟨v | r, c⟩ := r
      · dsimp only at ih ⊢
        have hc := hp (b + 1) v hb
        generalize paso (b + 1) v = q at hc ⊢
        obtain ⟨q, c'⟩ := q
        cases q <;> simp only at ih hc ⊢ <;> omega
      · simp only at ih ⊢; omega

/-- **El bucle del «para todo» pequeño.** Junta la fila de testigos de `φ(0), …, φ(k - 1)`, llamando a `paso` una
vez por valor. Si alguna llamada atestigua una fórmula lateral de `Δ`, se sale con ese testigo. -/
def barrer {ρ : Entorno} {φ : Formula} {Δ : List Formula} (m : ℕ)
    (paso : (x : ℕ) → x ≤ m → Suc (ext x ρ) (φ :: Δ.map Formula.sube) × ℕ) :
    (k : ℕ) → k ≤ m + 1 → ({w // Todos (fun x v => Testigo φ (ext x ρ) v) k w} ⊕ Suc ρ Δ) × ℕ
  | 0, _ => (.inl ⟨.hoja, trivial⟩, 0)
  | k + 1, hk =>
      match barrer m paso k (Nat.le_of_succ_le hk) with
      | (.inr r, c) => (.inr r, c)
      | (.inl ws, c) =>
          match paso k (Nat.le_of_succ_le_succ hk) with
          | (.aqui v h, c') => (.inl ⟨.cons v ws.1, h, ws.2⟩, c + c' + 1)
          | (.alla r, c') => (.inr (Suc.baja k Δ r), c + c' + 1)

/-- **Los pasos del barrido.** Si cada llamada gasta a lo sumo `C`, juntar `k` testigos gasta a lo sumo
`k · (C + 1)`. -/
theorem barrer_pasos {ρ : Entorno} {φ : Formula} {Δ : List Formula} (m : ℕ)
    (paso : (x : ℕ) → x ≤ m → Suc (ext x ρ) (φ :: Δ.map Formula.sube) × ℕ)
    (C : ℕ) (hp : ∀ x hx, (paso x hx).2 ≤ C) :
    ∀ (k : ℕ) (hk : k ≤ m + 1), (barrer m paso k hk).2 ≤ k * (C + 1)
  | 0, _ => by simp [barrer]
  | k + 1, hk => by
      have ih := barrer_pasos m paso C hp k (Nat.le_of_succ_le hk)
      rw [barrer, Nat.add_mul, Nat.one_mul]
      generalize barrer m paso k _ = r at ih ⊢
      obtain ⟨ws | r, c⟩ := r
      · dsimp only at ih ⊢
        have hc := hp k (Nat.le_of_succ_le_succ hk)
        generalize paso k _ = q at hc ⊢
        obtain ⟨q, c'⟩ := q
        cases q <;> simp only at ih hc ⊢ <;> omega
      · simp only at ih ⊢; omega

/-- **El lema del testigo, como función, con su cuenta.** Recorre la derivación. Cada regla es una operación sobre
testigos: el corte compone, «existe» a la derecha agrega el valor del término, «existe» a la izquierda lo saca, la
inducción y el «para todo» pequeño son bucles, y partir en casos evalúa un átomo. El segundo componente cuenta
las reglas ejecutadas. -/
def extraerC : {Γ Δ : List Formula} → Deriv Γ Δ → (ρ : Entorno) → Ant ρ Γ → Suc ρ Δ × ℕ
  | _, _, .id _, _, .cons w h _ => (.aqui w h, 1)
  | _, _, .aritm ps qs hp, ρ, a => (Suc.primero qs (hp ρ (Ant.atomos ps a)), 1)
  | _, _, .debilIzq _ d, ρ, .cons _ _ a => ((extraerC d ρ a).1, (extraerC d ρ a).2 + 1)
  | _, _, .debilDer _ d, ρ, a => (.alla (extraerC d ρ a).1, (extraerC d ρ a).2 + 1)
  | _, _, .contrIzq d, ρ, .cons w h a =>
      ((extraerC d ρ (.cons w h (.cons w h a))).1, (extraerC d ρ (.cons w h (.cons w h a))).2 + 1)
  | _, _, .contrDer d, ρ, a =>
      (match (extraerC d ρ a).1 with
        | .aqui w h => .aqui w h
        | .alla r => r,
       (extraerC d ρ a).2 + 1)
  | _, _, .cambIzq d, ρ, .cons w h (.cons w' h' a) =>
      ((extraerC d ρ (.cons w' h' (.cons w h a))).1, (extraerC d ρ (.cons w' h' (.cons w h a))).2 + 1)
  | _, _, .cambDer d, ρ, a =>
      (match (extraerC d ρ a).1 with
        | .aqui w h => .alla (.aqui w h)
        | .alla (.aqui w h) => .aqui w h
        | .alla (.alla r) => .alla (.alla r),
       (extraerC d ρ a).2 + 1)
  | _, _, .corte _ d₁ d₂, ρ, a =>
      match (extraerC d₁ ρ a).1 with
      | .aqui w h => ((extraerC d₂ ρ (.cons w h a)).1, (extraerC d₁ ρ a).2 + (extraerC d₂ ρ (.cons w h a)).2 + 1)
      | .alla r => (r, (extraerC d₁ ρ a).2 + 1)
  | _, _, .casos l d₁ d₂, ρ, a =>
      if h : l.vale ρ = true then
        ((extraerC d₁ ρ (.cons .hoja ⟨rfl, h⟩ a)).1, (extraerC d₁ ρ (.cons .hoja ⟨rfl, h⟩ a)).2 + 1)
      else
        ((extraerC d₂ ρ (.cons .hoja ⟨rfl, Lit.neg_vale_de h⟩ a)).1,
         (extraerC d₂ ρ (.cons .hoja ⟨rfl, Lit.neg_vale_de h⟩ a)).2 + 1)
  | _, _, .conjDer d₁ d₂, ρ, a =>
      (match (extraerC d₁ ρ a).1, (extraerC d₂ ρ a).1 with
        | .aqui v h, .aqui w h' => .aqui (.cons v w) ⟨h, h'⟩
        | .alla r, _ => .alla r
        | _, .alla r => .alla r,
       (extraerC d₁ ρ a).2 + (extraerC d₂ ρ a).2 + 1)
  | _, _, .conjIzq _, _, .cons .hoja h _ => h.elim
  | _, _, .conjIzq _, _, .cons (.nodo _ _) h _ => h.elim
  | _, _, .conjIzq d, ρ, .cons (.cons v w) h a =>
      ((extraerC d ρ (.cons v h.1 (.cons w h.2 a))).1, (extraerC d ρ (.cons v h.1 (.cons w h.2 a))).2 + 1)
  | _, _, .disyDer d, ρ, a =>
      (match (extraerC d ρ a).1 with
        | .aqui w h => .aqui (.nodo 0 w) h
        | .alla (.aqui w h) => .aqui (.nodo 1 w) h
        | .alla (.alla r) => .alla r,
       (extraerC d ρ a).2 + 1)
  | _, _, .disyIzq _ _, _, .cons .hoja h _ => h.elim
  | _, _, .disyIzq _ _, _, .cons (.cons _ _) h _ => h.elim
  | _, _, .disyIzq d₁ _, ρ, .cons (.nodo 0 w) h a =>
      ((extraerC d₁ ρ (.cons w h a)).1, (extraerC d₁ ρ (.cons w h a)).2 + 1)
  | _, _, .disyIzq _ d₂, ρ, .cons (.nodo 1 w) h a =>
      ((extraerC d₂ ρ (.cons w h a)).1, (extraerC d₂ ρ (.cons w h a)).2 + 1)
  | _, _, .disyIzq _ _, _, .cons (.nodo (_ + 2) _) h _ => h.elim
  | _, _, .exDer _ s φ d₀ d, ρ, a =>
      (match (extraerC d ρ a).1 with
        | .aqui w h => .aqui (.nodo (s.val ρ) w) ⟨(extraerC d₀ ρ a).1.le, (testigo_inst s φ ρ w).mp h⟩
        | .alla r => .alla r,
       (extraerC d₀ ρ a).2 + (extraerC d ρ a).2 + 1)
  | _, _, .exIzq _ _ _, _, .cons .hoja h _ => h.elim
  | _, _, .exIzq _ _ _, _, .cons (.cons _ _) h _ => h.elim
  | _, Δ, .exIzq t _ d, ρ, .cons (.nodo b w) h a =>
      (Suc.baja b Δ
          (extraerC d (ext b ρ)
            (.cons .hoja ⟨rfl, (cota_vale t b ρ).trans (decide_eq_true h.1)⟩ (.cons w h.2 (Ant.sube b a)))).1,
       (extraerC d (ext b ρ)
            (.cons .hoja ⟨rfl, (cota_vale t b ρ).trans (decide_eq_true h.1)⟩ (.cons w h.2 (Ant.sube b a)))).2 + 1)
  | _, _, .ptDer (Δ := Δ) t φ d, ρ, a =>
      (Suc.deSuma (φ := pt t φ) (fun _ h => h) (barrer (Δ := Δ) (φ := φ) (Nat.size (t.val ρ))
          (fun x hx => extraerC d (ext x ρ)
            (.cons .hoja ⟨rfl, (cota_vale (.largo t) x ρ).trans (decide_eq_true hx)⟩ (Ant.sube x a)))
          (Nat.size (t.val ρ) + 1) (Nat.le_refl _)).1,
       (barrer (Δ := Δ) (φ := φ) (Nat.size (t.val ρ))
          (fun x hx => extraerC d (ext x ρ)
            (.cons .hoja ⟨rfl, (cota_vale (.largo t) x ρ).trans (decide_eq_true hx)⟩ (Ant.sube x a)))
          (Nat.size (t.val ρ) + 1) (Nat.le_refl _)).2 + 1)
  | _, _, .ptIzq _ s φ d₀ d, ρ, .cons w h a =>
      ((extraerC d ρ (.cons (Todos.dame _ w h (s.val ρ) (Nat.lt_succ_of_le (extraerC d₀ ρ a).1.le)).1
          ((testigo_inst s φ ρ _).mpr (Todos.dame _ w h (s.val ρ) (Nat.lt_succ_of_le (extraerC d₀ ρ a).1.le)).2)
          a)).1,
       (extraerC d₀ ρ a).2 +
        (extraerC d ρ (.cons (Todos.dame _ w h (s.val ρ) (Nat.lt_succ_of_le (extraerC d₀ ρ a).1.le)).1
          ((testigo_inst s φ ρ _).mpr (Todos.dame _ w h (s.val ρ) (Nat.lt_succ_of_le (extraerC d₀ ρ a).1.le)).2)
          a)).2 + 1)
  | _, _, .pind (Δ := Δ) t φ d, ρ, .cons w h a =>
      (Suc.deSuma (fun v hv => (testigo_inst t φ ρ v).mpr hv) (lazo (Δ := Δ) ⟨w, (testigo_inst .cero φ ρ w).mp h⟩
          (fun b v => extraerC d (ext b ρ) (.cons v.1 ((testigo_mitad φ b ρ v.1).mpr v.2) (Ant.sube b a)))
          (t.val ρ) (t.val ρ) Nat.lt_two_pow_self).1,
       (lazo (Δ := Δ) ⟨w, (testigo_inst .cero φ ρ w).mp h⟩
          (fun b v => extraerC d (ext b ρ) (.cons v.1 ((testigo_mitad φ b ρ v.1).mpr v.2) (Ant.sube b a)))
          (t.val ρ) (t.val ρ) Nat.lt_two_pow_self).2 + 1)

/-- El lema del testigo, sin la cuenta. -/
def extraer {Γ Δ : List Formula} (d : Deriv Γ Δ) (ρ : Entorno) (a : Ant ρ Γ) : Suc ρ Δ := (extraerC d ρ a).1

/-- Los pasos de regla que gasta la extracción. -/
def pasos {Γ Δ : List Formula} (d : Deriv Γ Δ) (ρ : Entorno) (a : Ant ρ Γ) : ℕ := (extraerC d ρ a).2

/-- **La cota de los pasos**, leída de la derivación. Con entradas de a lo sumo `n` bits. Una variable nueva mide lo
que su término de cota permite; la inducción y el «para todo» pequeño multiplican por el largo de su término. -/
def Deriv.cota : {Γ Δ : List Formula} → Deriv Γ Δ → ℕ → ℕ
  | _, _, .id _, _ => 1
  | _, _, .aritm _ _ _, _ => 1
  | _, _, .debilIzq _ d, n => d.cota n + 1
  | _, _, .debilDer _ d, n => d.cota n + 1
  | _, _, .contrIzq d, n => d.cota n + 1
  | _, _, .contrDer d, n => d.cota n + 1
  | _, _, .cambIzq d, n => d.cota n + 1
  | _, _, .cambDer d, n => d.cota n + 1
  | _, _, .corte _ d₁ d₂, n => d₁.cota n + d₂.cota n + 1
  | _, _, .casos _ d₁ d₂, n => d₁.cota n + d₂.cota n + 1
  | _, _, .conjDer d₁ d₂, n => d₁.cota n + d₂.cota n + 1
  | _, _, .conjIzq d, n => d.cota n + 1
  | _, _, .disyDer d, n => d.cota n + 1
  | _, _, .disyIzq d₁ d₂, n => d₁.cota n + d₂.cota n + 1
  | _, _, .exDer _ _ _ d₀ d, n => d₀.cota n + d.cota n + 1
  | _, _, .exIzq t _ d, n => d.cota (n + t.cotaLargo n) + 1
  | _, _, .ptDer t _ d, n => (t.cotaLargo n + 1) * (d.cota (n + t.cotaLargo n) + 1) + 1
  | _, _, .ptIzq _ _ _ d₀ d, n => d₀.cota n + d.cota n + 1
  | _, _, .pind t _ d, n => t.cotaLargo n * (d.cota (n + t.cotaLargo n) + 1) + 1

/-- **La extracción gasta lo que la cota dice.** -/
theorem pasos_le : {Γ Δ : List Formula} → (d : Deriv Γ Δ) → (n : ℕ) → (ρ : Entorno) → (a : Ant ρ Γ) →
    Chico n ρ → (extraerC d ρ a).2 ≤ d.cota n
  | _, _, .id _, _, _, .cons _ _ _, _ => by simp [extraerC, Deriv.cota]
  | _, _, .aritm _ _ _, _, _, _, _ => by simp [extraerC, Deriv.cota]
  | _, _, .debilIzq _ d, n, ρ, .cons _ _ a, hρ => by
      simp only [extraerC, Deriv.cota]; exact Nat.succ_le_succ (pasos_le d n ρ a hρ)
  | _, _, .debilDer _ d, n, ρ, a, hρ => by
      simp only [extraerC, Deriv.cota]; exact Nat.succ_le_succ (pasos_le d n ρ a hρ)
  | _, _, .contrIzq d, n, ρ, .cons w h a, hρ => by
      simp only [extraerC, Deriv.cota]; exact Nat.succ_le_succ (pasos_le d n ρ _ hρ)
  | _, _, .contrDer d, n, ρ, a, hρ => by
      simp only [extraerC, Deriv.cota]; exact Nat.succ_le_succ (pasos_le d n ρ a hρ)
  | _, _, .cambIzq d, n, ρ, .cons w h (.cons w' h' a), hρ => by
      simp only [extraerC, Deriv.cota]; exact Nat.succ_le_succ (pasos_le d n ρ _ hρ)
  | _, _, .cambDer d, n, ρ, a, hρ => by
      simp only [extraerC, Deriv.cota]; exact Nat.succ_le_succ (pasos_le d n ρ a hρ)
  | _, _, .corte _ d₁ d₂, n, ρ, a, hρ => by
      have h₁ := pasos_le d₁ n ρ a hρ
      simp only [extraerC, Deriv.cota]
      split
      · rename_i w h _
        have h₂ := pasos_le d₂ n ρ (.cons w h a) hρ
        simp only; omega
      · simp only; omega
  | _, _, .casos _ d₁ d₂, n, ρ, a, hρ => by
      simp only [extraerC, Deriv.cota]
      split
      · exact Nat.succ_le_succ (Nat.le_trans (pasos_le d₁ n ρ _ hρ) (Nat.le_add_right _ _))
      · exact Nat.succ_le_succ (Nat.le_trans (pasos_le d₂ n ρ _ hρ) (Nat.le_add_left _ _))
  | _, _, .conjDer d₁ d₂, n, ρ, a, hρ => by
      simp only [extraerC, Deriv.cota]
      exact Nat.succ_le_succ (Nat.add_le_add (pasos_le d₁ n ρ a hρ) (pasos_le d₂ n ρ a hρ))
  | _, _, .conjIzq _, _, _, .cons .hoja h _, _ => h.elim
  | _, _, .conjIzq _, _, _, .cons (.nodo _ _) h _, _ => h.elim
  | _, _, .conjIzq d, n, ρ, .cons (.cons v w) h a, hρ => by
      simp only [extraerC, Deriv.cota]; exact Nat.succ_le_succ (pasos_le d n ρ _ hρ)
  | _, _, .disyDer d, n, ρ, a, hρ => by
      simp only [extraerC, Deriv.cota]; exact Nat.succ_le_succ (pasos_le d n ρ a hρ)
  | _, _, .disyIzq _ _, _, _, .cons .hoja h _, _ => h.elim
  | _, _, .disyIzq _ _, _, _, .cons (.cons _ _) h _, _ => h.elim
  | _, _, .disyIzq d₁ _, n, ρ, .cons (.nodo 0 w) h a, hρ => by
      simp only [extraerC, Deriv.cota]
      exact Nat.succ_le_succ (Nat.le_trans (pasos_le d₁ n ρ _ hρ) (Nat.le_add_right _ _))
  | _, _, .disyIzq _ _, _, _, .cons (.nodo (_ + 2) _) h _, _ => h.elim
  | _, _, .disyIzq _ d₂, n, ρ, .cons (.nodo 1 w) h a, hρ => by
      simp only [extraerC, Deriv.cota]
      exact Nat.succ_le_succ (Nat.le_trans (pasos_le d₂ n ρ _ hρ) (Nat.le_add_left _ _))
  | _, _, .exDer _ _ _ d₀ d, n, ρ, a, hρ => by
      simp only [extraerC, Deriv.cota]
      exact Nat.succ_le_succ (Nat.add_le_add (pasos_le d₀ n ρ a hρ) (pasos_le d n ρ a hρ))
  | _, _, .exIzq _ _ _, _, _, .cons .hoja h _, _ => h.elim
  | _, _, .exIzq _ _ _, _, _, .cons (.cons _ _) h _, _ => h.elim
  | _, _, .exIzq t _ d, n, ρ, .cons (.nodo b w) h a, hρ => by
      simp only [extraerC, Deriv.cota]
      refine Nat.succ_le_succ (pasos_le d _ _ _ (hρ.ext ?_))
      exact Nat.le_trans (Nat.size_le_size h.1) (t.largo_val_le hρ)
  | _, _, .ptDer t φ d, n, ρ, a, hρ => by
      simp only [Deriv.cota]
      refine Nat.succ_le_succ ?_
      have hL := t.largo_val_le hρ
      refine Nat.le_trans (barrer_pasos _ _ (d.cota (n + t.cotaLargo n)) ?_ _ _) ?_
      · intro x hx
        refine pasos_le d _ _ _ (hρ.ext (Nat.le_trans (Nat.size_le_size hx) ?_))
        exact Nat.le_trans (Nat.size_le_size (Nat.size_le.mpr Nat.lt_two_pow_self)) hL
      · exact Nat.mul_le_mul_right _ (Nat.succ_le_succ hL)
  | _, _, .ptIzq _ _ _ d₀ d, n, ρ, .cons w h a, hρ => by
      simp only [extraerC, Deriv.cota]
      exact Nat.succ_le_succ (Nat.add_le_add (pasos_le d₀ n ρ a hρ) (pasos_le d n ρ _ hρ))
  | _, _, .pind t φ d, n, ρ, .cons w h a, hρ => by
      simp only [Deriv.cota]
      refine Nat.succ_le_succ ?_
      have hL := t.largo_val_le hρ
      refine Nat.le_trans (lazo_pasos _ _ (t.val ρ) (d.cota (n + t.cotaLargo n)) ?_ _ _ _ (Nat.le_refl _)) ?_
      · intro b v hb
        exact pasos_le d _ _ _ (hρ.ext (Nat.le_trans (Nat.size_le_size hb) hL))
      · exact Nat.mul_le_mul_right _ (Nat.le_trans (vueltas_le _ _) hL)

private theorem ac1 {f : ℕ → ℕ} (h : Acotada f) : Acotada fun n => f n + 1 :=
  Cerradura.suma h (Termino.acotada_const 1)

private theorem ac2 {f g : ℕ → ℕ} (hf : Acotada f) (hg : Acotada g) : Acotada fun n => f n + g n + 1 :=
  ac1 (Cerradura.suma hf hg)

/-- **La cota es un polinomio.** Cada regla la arma con sumas, productos y composiciones, y la derivación es fija:
por eso las inducciones anidadas componen polinomios y no rompen la cerradura. -/
theorem Deriv.cota_acotada : {Γ Δ : List Formula} → (d : Deriv Γ Δ) → Acotada d.cota
  | _, _, .id _ => Termino.acotada_const 1
  | _, _, .aritm _ _ _ => Termino.acotada_const 1
  | _, _, .debilIzq _ d => ac1 d.cota_acotada
  | _, _, .debilDer _ d => ac1 d.cota_acotada
  | _, _, .contrIzq d => ac1 d.cota_acotada
  | _, _, .contrDer d => ac1 d.cota_acotada
  | _, _, .cambIzq d => ac1 d.cota_acotada
  | _, _, .cambDer d => ac1 d.cota_acotada
  | _, _, .corte _ d₁ d₂ => ac2 d₁.cota_acotada d₂.cota_acotada
  | _, _, .casos _ d₁ d₂ => ac2 d₁.cota_acotada d₂.cota_acotada
  | _, _, .conjDer d₁ d₂ => ac2 d₁.cota_acotada d₂.cota_acotada
  | _, _, .conjIzq d => ac1 d.cota_acotada
  | _, _, .disyDer d => ac1 d.cota_acotada
  | _, _, .disyIzq d₁ d₂ => ac2 d₁.cota_acotada d₂.cota_acotada
  | _, _, .exDer _ _ _ d₀ d => ac2 d₀.cota_acotada d.cota_acotada
  | _, _, .exIzq t _ d =>
      ac1 (Cerradura.composicion d.cota_acotada (Cerradura.suma Termino.acotada_id t.cotaLargo_acotada))
  | _, _, .ptDer t _ d =>
      ac1 (Cerradura.producto (ac1 t.cotaLargo_acotada)
        (ac1 (Cerradura.composicion d.cota_acotada (Cerradura.suma Termino.acotada_id t.cotaLargo_acotada))))
  | _, _, .ptIzq _ _ _ d₀ d => ac2 d₀.cota_acotada d.cota_acotada
  | _, _, .pind t _ d =>
      ac1 (Cerradura.producto t.cotaLargo_acotada
        (ac1 (Cerradura.composicion d.cota_acotada (Cerradura.suma Termino.acotada_id t.cotaLargo_acotada))))

/-! ## Lo que se sigue -/

/-- Si valen todas las fórmulas de `Γ`, hay testigos de todas. -/
theorem ant_de_vale (ρ : Entorno) : (Γ : List Formula) → (∀ φ ∈ Γ, Vale φ ρ) → Nonempty (Ant ρ Γ)
  | [], _ => ⟨.nil⟩
  | φ :: Γ, h => by
      obtain ⟨w, hw⟩ := (vale_iff_testigo φ ρ).mp (h φ (List.mem_cons_self))
      obtain ⟨a⟩ := ant_de_vale ρ Γ fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)
      exact ⟨.cons w hw a⟩

/-- Un testigo del sucedente da una fórmula suya que vale. -/
theorem vale_de_suc {ρ : Entorno} : {Δ : List Formula} → Suc ρ Δ → ∃ φ ∈ Δ, Vale φ ρ
  | φ :: _, .aqui w h => ⟨φ, List.mem_cons_self, (vale_iff_testigo φ ρ).mpr ⟨w, h⟩⟩
  | _ :: _, .alla r => by
      obtain ⟨ψ, hψ, hv⟩ := vale_de_suc r
      exact ⟨ψ, List.mem_cons_of_mem _ hψ, hv⟩

/-- **Solidez**, como corolario de la extracción: si se deriva `Γ → Δ` y vale todo `Γ`, vale algo de `Δ`. -/
theorem solidez {Γ Δ : List Formula} (d : Deriv Γ Δ) (ρ : Entorno) (h : ∀ φ ∈ Γ, Vale φ ρ) :
    ∃ φ ∈ Δ, Vale φ ρ := by
  obtain ⟨a⟩ := ant_de_vale ρ Γ h
  exact vale_de_suc (extraer d ρ a)

/-- El testigo que la derivación da para su única fórmula. -/
def testigoExtraido {φ : Formula} (d : Deriv [] [φ]) (ρ : Entorno) : Arbol :=
  match extraer d ρ .nil with
  | .aqui w _ => w

/-- El testigo extraído atestigua. -/
theorem testigoExtraido_vale {φ : Formula} (d : Deriv [] [φ]) (ρ : Entorno) :
    Testigo φ ρ (testigoExtraido d ρ) := by
  unfold testigoExtraido
  match extraer d ρ .nil with
  | .aqui w h => exact h

/-- El valor que la derivación da para el «existe» de afuera. -/
def valorExtraido {t : Termino} {φ : Formula} (d : Deriv [] [ex t φ]) (ρ : Entorno) : ℕ :=
  match extraer d ρ .nil with
  | .aqui (.nodo b _) _ => b
  | .aqui _ _ => 0

/-- **El teorema del testigo, en el piloto.** De una derivación de «existe `x ≤ t` con `φ`», sin hipótesis, sale
una función `valorExtraido` que para cada entorno entrega un `x` bajo la cota y que cumple `φ`. -/
theorem teorema_del_testigo {t : Termino} {φ : Formula} (d : Deriv [] [ex t φ]) (ρ : Entorno) :
    valorExtraido d ρ ≤ t.val ρ ∧ Vale φ (ext (valorExtraido d ρ) ρ) := by
  unfold valorExtraido
  match extraer d ρ .nil with
  | .aqui (.nodo b w) h => exact ⟨h.1, (vale_iff_testigo φ _).mpr ⟨w, h.2⟩⟩
  | .aqui .hoja h => exact h.elim
  | .aqui (.cons _ _) h => exact h.elim

/-- **El costo del testigo.** La función extraída gasta un número polinomial de pasos de regla y entrega un valor
de largo polinomial, las dos cosas medidas en el largo `n` de las entradas. -/
theorem costo_del_testigo {t : Termino} {φ : Formula} (d : Deriv [] [ex t φ]) :
    ∃ p q : Polynomial ℕ, ∀ (n : ℕ) (ρ : Entorno), Chico n ρ →
      pasos d ρ .nil ≤ p.eval n ∧ Nat.size (valorExtraido d ρ) ≤ q.eval n := by
  obtain ⟨p, hp⟩ := d.cota_acotada
  obtain ⟨q, hq⟩ := t.cotaLargo_acotada
  refine ⟨p, q, fun n ρ hρ => ⟨Nat.le_trans (pasos_le d n ρ .nil hρ) (hp n), ?_⟩⟩
  exact Nat.le_trans (Nat.size_le_size (teorema_del_testigo d ρ).1) (Nat.le_trans (t.largo_val_le hρ) (hq n))

/-! ## Ejemplos que se ejecutan -/

private theorem el0 {l : Lit} {ps : List Lit} {ρ : Entorno} (h : ∀ q ∈ l :: ps, q.vale ρ = true) :
    l.vale ρ = true := h _ List.mem_cons_self

private theorem el1 {l l' : Lit} {ps : List Lit} {ρ : Entorno} (h : ∀ q ∈ l :: l' :: ps, q.vale ρ = true) :
    l'.vale ρ = true := h _ (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem el2 {l l' l'' : Lit} {ps : List Lit} {ρ : Entorno}
    (h : ∀ q ∈ l :: l' :: l'' :: ps, q.vale ρ = true) : l''.vale ρ = true :=
  h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- El cuerpo: «existe `y ≤ x + 1` con `y = x + 1`», donde `x` es la variable `0` del contexto. -/
def sucesorA : Formula := ex (.suc (.var 0)) (atomo ⟨.eq, .var 0, .suc (.var 1)⟩)

/-- «Existe `y ≤ a + 1` con `y = a + 1`». Se deriva exhibiendo el término `a + 1`. -/
def ejemplo : Deriv [] [sucesorA] :=
  .exDer _ (.suc (.var 0)) _ (.aritm1 [] _ (fun _ _ => Rel.vale_le.mpr (Nat.le_refl _)))
    (.aritm1 [] _ (fun _ _ => Rel.vale_eq.mpr rfl))

/-- La función extraída da `a + 1`: con `a = 5`, entrega `6`. -/
example : testigoExtraido ejemplo (fun _ => 5) = .nodo 6 .hoja := by decide

/-! ### Con inducción: el largo de un número

`A(b)` dice «existe `y ≤ b` con `y = |b|`», donde `|b|` es el largo de `b` en bits. Se prueba por inducción por bits:
el largo de `b` es uno más que el de `⌊b/2⌋`. El programa extraído cuenta los bits de `b` con un bucle, y en cada
vuelta decide si `b = 0`. -/

/-- `A(b)`: en el contexto, la variable `0` es `b`; dentro del «existe», la `0` es `y` y la `1` es `b`. -/
def largoA : Formula := ex (.var 0) (atomo ⟨.eq, .var 0, .largo (.var 1)⟩)

/-- El paso: de `A(⌊b/2⌋)` a `A(b)`. Con `y'` el largo de la mitad: si `b = 0` se entrega `0`, y si no `y' + 1`. -/
def pasoLargo : Deriv [mitad largoA] [largoA] :=
  .exIzq (Γ := []) (Δ := [largoA]) _ _
    (.casos ⟨.eq, .var 1, .cero⟩
      (.exDer _ .cero _
        (.aritm1 [_, _, _] _ (fun _ _ => Rel.vale_le.mpr (Nat.zero_le _)))
        (.aritm1 [_, _, _] _ (fun ρ h => by
          have h0 := Rel.vale_eq.mp (el0 h)
          change ρ 1 = 0 at h0
          refine Rel.vale_eq.mpr ?_
          change 0 = Nat.size (ρ 1)
          rw [h0]; rfl)))
      (.exDer _ (.suc (.var 0)) _
        (.aritm1 [_, _, _] _ (fun ρ h => by
          have h0 := Rel.vale_neq.mp (el0 h)
          have h1 := Rel.vale_le.mp (el1 h)
          change ρ 1 ≠ 0 at h0
          change ρ 0 ≤ ρ 1 / 2 at h1
          refine Rel.vale_le.mpr ?_
          change ρ 0 + 1 ≤ ρ 1
          omega))
        (.aritm1 [_, _, _] _ (fun ρ h => by
          have h0 := Rel.vale_neq.mp (el0 h)
          have h2 := Rel.vale_eq.mp (el2 h)
          change ρ 1 ≠ 0 at h0
          change ρ 0 = Nat.size (ρ 1 / 2) at h2
          refine Rel.vale_eq.mpr ?_
          change ρ 0 + 1 = Nat.size (ρ 1)
          rw [size_mitad (ρ 1) h0, h2]))))

/-- «Para todo `a` existe `y ≤ a` con `y = |a|`», por inducción por bits hasta `a` (la variable `0`). -/
def ejemploLargo : Deriv [] [inst (.var 0) largoA] :=
  .corte (inst .cero largoA)
    (.cambDer (.debilDer _
      (.exDer _ .cero _ (.aritm1 [] _ (fun _ _ => Rel.vale_le.mpr (Nat.le_refl _)))
        (.aritm1 [] _ (fun _ _ => Rel.vale_eq.mpr rfl)))))
    (.pind (Γ := []) (Δ := []) (.var 0) largoA pasoLargo)

/-- El programa extraído cuenta los bits: `1000` se escribe con `10`. -/
example : testigoExtraido ejemploLargo (fun _ => 1000) = .nodo 10 .hoja := by decide

/-! ### Con el «para todo» pequeño

«Para todo `x ≤ |a|` existe `y ≤ x + 1` con `y = x + 1`». Su testigo es una fila con un valor por cada `x`. -/

/-- Para todo `x ≤ |a|`, con `a` la variable `0`. -/
def ejemploFila : Deriv [] [pt (.var 0) sucesorA] :=
  .ptDer (Γ := []) (Δ := []) _ _ (.debilIzq _ ejemplo)

/-- Con `a = 5`, que mide 3 bits, la fila trae los sucesores de `3, 2, 1, 0`. -/
example : testigoExtraido ejemploFila (fun _ => 5) =
    .cons (.nodo 4 .hoja) (.cons (.nodo 3 .hoja) (.cons (.nodo 2 .hoja) (.cons (.nodo 1 .hoja) .hoja))) := by
  decide

/-- Usar el «para todo»: de la fila se saca el caso `x = 0`, y por corte queda «existe `y ≤ 1` con `y = 1`». -/
def ejemploUso : Deriv [] [inst .cero sucesorA] :=
  .corte (pt (.var 0) sucesorA) (.debilDer _ ejemploFila |> .cambDer)
    (.ptIzq (.var 0) .cero sucesorA (.aritm1 [] _ (fun _ _ => Rel.vale_le.mpr (Nat.zero_le _))) (.id _))

/-- El programa extraído arma la fila y busca en ella: entrega `1`. -/
example : testigoExtraido ejemploUso (fun _ => 5) = .nodo 1 .hoja := by decide

/-! ### Con «y» y «o»

«`a = 0` o `a ≠ 0`, y además `0 ≤ a`». El testigo dice por cuál lado de la «o» se fue. -/

def ejemploLogica : Deriv [] [conj (disy (atomo ⟨.eq, .var 0, .cero⟩) (atomo ⟨.neq, .var 0, .cero⟩))
    (atomo ⟨.le, .cero, .var 0⟩)] :=
  .conjDer
    (.disyDer (.casos ⟨.eq, .var 0, .cero⟩
      (.debilDer _ (.id _) |> .cambDer)
      (.debilDer _ (.id _))))
    (.aritm1 [] _ (fun _ _ => Rel.vale_le.mpr (Nat.zero_le _)))

/-- Con `a = 0` la marca es `0` (lado izquierdo); con `a = 7` es `1`. -/
example : testigoExtraido ejemploLogica (fun _ => 0) = .cons (.nodo 0 .hoja) .hoja := by decide
example : testigoExtraido ejemploLogica (fun _ => 7) = .cons (.nodo 1 .hoja) .hoja := by decide

end Extraccion
end Sagitta.Map
