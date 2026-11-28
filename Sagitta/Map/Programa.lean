import Sagitta.Map.Testigo

/-!
# El programa que sale de la prueba

`Testigo.lean` define la extracción como una función que carga pruebas: cada testigo viaja con la demostración de
que atestigua. Aquí se separa el **programa**: un lenguaje pequeño (`Prog`) que trabaja sobre árboles a secas, sin
ninguna prueba, y un traductor (`Deriv.borrar`) que le quita a una derivación todo lo que no se ejecuta.

## Qué hay

* **`Prog`**: una instrucción por cada regla del cálculo. Lo que queda de cada regla es poco: mover testigos,
  armar y desarmar árboles, evaluar un término, decidir un átomo, y dos bucles.
* **`Prog.correr`**: su intérprete. Recibe el entorno y la lista de testigos del antecedente, y devuelve la
  posición de la fórmula atestiguada en el sucedente y su testigo. Es total: si un testigo no tiene la forma
  esperada, lo lee con valores por omisión y sigue.
* **`correcto`**: correr el programa de una derivación da lo mismo que la extracción, sin las pruebas.
* **`programa_del_testigo`**: el testigo extraído es lo que el programa entrega.

## Qué clase de lenguaje es

Es un álgebra de funciones a la manera de Cobham, pero sobre árboles y no sobre números:

* las funciones básicas son los términos de Buss y las operaciones de árbol;
* la composición es el corte;
* `Prog.pind` es la **recursión sobre la notación**: una vuelta por cada bit de un término;
* `Prog.ptDer` es una iteración de largo `|t| + 1`.

## El límite

En Cobham la recursión sobre la notación lleva una cota explícita del resultado. Aquí también:

* **`peso_le`**: un testigo válido pesa a lo sumo un polinomio en el largo de las entradas (`Formula.cotaPeso`).
  Es lo que hace *limitada* a la recursión: cada valor de un «existe» está bajo su término.
* **`Prog.pind`** lleva esa cota escrita, y el intérprete **recorta** el estado del bucle cuando se pasa. Con
  testigos válidos el recorte nunca ocurre (`correcto`); con entradas basura es lo que impide que el estado crezca.
* **`techo_le`** y **`techo_acotada`**: para toda entrada, válida o no, lo que un programa limitado entrega pesa
  a lo sumo un polinomio en el peso de la entrada. Las instrucciones se componen y el polinomio no se rompe.

## Qué no hay

* **La codificación en números**, que es lo que haría de esto el álgebra de Cobham literal. Es un álgebra de
  Cobham sobre árboles.
* **El entorno es una función `ℕ → ℕ`**, no un dato finito. El intérprete recibe aparte un número `n` que acota
  el largo de sus variables y lo va actualizando.
* **La cota de `Prog.pind` es una función de Lean**, no sintaxis. `Prog.Limitado` pide que sea creciente y
  polinomial.
* **Tiempo.** Aquí se acota el *tamaño* de lo que el programa entrega, no sus pasos. Las premisas de cota de
  `exDer` y `ptIzq` desaparecen del programa, así que la cuenta de pasos de `Testigo.lean`, que sí las recorre,
  es una cota superior del programa y no su costo exacto.
-/

namespace Sagitta.Map
namespace Extraccion

open Formula
open Cerradura (Acotada)

/-! ## El peso de un testigo -/

/-- El peso de un árbol: sus nodos más los bits de sus números. -/
def Arbol.peso : Arbol → ℕ
  | .hoja => 1
  | .nodo a w => Nat.size a + w.peso + 1
  | .cons v w => v.peso + w.peso + 1

theorem Arbol.peso_pos : ∀ w : Arbol, 1 ≤ w.peso
  | .hoja => Nat.le_refl _
  | .nodo _ _ => Nat.succ_le_succ (Nat.zero_le _)
  | .cons _ _ => Nat.succ_le_succ (Nat.zero_le _)

/-- **La cota del peso**, leída de la fórmula. Con variables de a lo sumo `n` bits. -/
def Formula.cotaPeso : Formula → ℕ → ℕ
  | atomo _, _ => 1
  | conj φ ψ, n => φ.cotaPeso n + ψ.cotaPeso n + 1
  | disy φ ψ, n => φ.cotaPeso n + ψ.cotaPeso n + 2
  | ex t φ, n => t.cotaLargo n + φ.cotaPeso (n + t.cotaLargo n) + 1
  | pt t φ, n => (t.cotaLargo n + 1) * (φ.cotaPeso (n + t.cotaLargo n) + 1) + 1

theorem todos_peso {P : ℕ → Arbol → Prop} {C : ℕ} :
    ∀ (k : ℕ) (w : Arbol), (∀ x v, x < k → P x v → v.peso ≤ C) → Todos P k w → w.peso ≤ k * (C + 1) + 1
  | 0, .hoja, _, _ => by simp [Arbol.peso]
  | 0, .nodo _ _, _, h => h.elim
  | 0, .cons _ _, _, h => h.elim
  | _ + 1, .hoja, _, h => h.elim
  | _ + 1, .nodo _ _, _, h => h.elim
  | k + 1, .cons v w, hP, h => by
      have h₁ := hP k v (Nat.lt_succ_self k) h.1
      have h₂ := todos_peso k w (fun x v hx => hP x v (Nat.lt_succ_of_lt hx)) h.2
      simp only [Arbol.peso, Nat.add_mul, Nat.one_mul]
      omega

/-- **Un testigo válido es chico.** Pesa a lo sumo la cota de su fórmula: cada valor de un «existe» está bajo su
término, y cada fila tiene `|t| + 1` testigos. -/
theorem peso_le (φ : Formula) :
    ∀ (n : ℕ) (ρ : Entorno) (w : Arbol), Chico n ρ → Testigo φ ρ w → w.peso ≤ φ.cotaPeso n := by
  induction φ with
  | atomo l => rintro n ρ w - ⟨rfl, -⟩; exact Nat.le_refl _
  | conj φ ψ ih₁ ih₂ =>
    intro n ρ w hρ h
    cases w with
    | hoja => exact h.elim
    | nodo _ _ => exact h.elim
    | cons v w =>
      have h₁ := ih₁ n ρ v hρ h.1
      have h₂ := ih₂ n ρ w hρ h.2
      simp only [Arbol.peso, Formula.cotaPeso]; omega
  | disy φ ψ ih₁ ih₂ =>
    intro n ρ w hρ h
    rcases w with _ | ⟨_ | _ | k, w⟩ | ⟨v, w⟩
    · exact h.elim
    · have h₁ := ih₁ n ρ w hρ h
      simp only [Arbol.peso, Formula.cotaPeso, Nat.size_zero]; omega
    · have h₂ := ih₂ n ρ w hρ h
      simp only [Arbol.peso, Formula.cotaPeso, Nat.zero_add, Nat.size_one]; omega
    · exact h.elim
    · exact h.elim
  | ex t φ ih =>
    intro n ρ w hρ h
    cases w with
    | hoja => exact h.elim
    | cons _ _ => exact h.elim
    | nodo a w =>
      have ha : Nat.size a ≤ t.cotaLargo n := Nat.le_trans (Nat.size_le_size h.1) (t.largo_val_le hρ)
      have hw := ih _ _ w (hρ.ext ha) h.2
      simp only [Arbol.peso, Formula.cotaPeso]; omega
  | pt t φ ih =>
    intro n ρ w hρ h
    have hL := t.largo_val_le hρ
    have hw := todos_peso (C := φ.cotaPeso (n + t.cotaLargo n)) _ w (fun x v hx hv => by
      refine ih _ _ v (hρ.ext ?_) hv
      refine Nat.le_trans (Nat.size_le_size (Nat.le_of_lt_succ hx)) ?_
      exact Nat.le_trans (Nat.size_le_size (Nat.size_le.mpr Nat.lt_two_pow_self)) hL) h
    refine Nat.le_trans hw ?_
    simp only [Formula.cotaPeso]
    exact Nat.succ_le_succ (Nat.mul_le_mul_right _ (Nat.succ_le_succ hL))

theorem Formula.cotaPeso_mono : ∀ (φ : Formula) {a b : ℕ}, a ≤ b → φ.cotaPeso a ≤ φ.cotaPeso b
  | atomo _, _, _, _ => Nat.le_refl _
  | conj φ ψ, _, _, h => Nat.succ_le_succ (Nat.add_le_add (cotaPeso_mono φ h) (cotaPeso_mono ψ h))
  | disy φ ψ, _, _, h => Nat.add_le_add_right (Nat.add_le_add (cotaPeso_mono φ h) (cotaPeso_mono ψ h)) 2
  | ex t φ, _, _, h =>
      Nat.succ_le_succ (Nat.add_le_add (t.cotaLargo_mono h)
        (cotaPeso_mono φ (Nat.add_le_add h (t.cotaLargo_mono h))))
  | pt t φ, _, _, h =>
      Nat.succ_le_succ (Nat.mul_le_mul (Nat.succ_le_succ (t.cotaLargo_mono h))
        (Nat.succ_le_succ (cotaPeso_mono φ (Nat.add_le_add h (t.cotaLargo_mono h)))))

private theorem ac1 {f : ℕ → ℕ} (h : Acotada f) : Acotada fun n => f n + 1 :=
  Cerradura.suma h (Termino.acotada_const 1)

private theorem acDentro {f : ℕ → ℕ} (h : Acotada f) (t : Termino) :
    Acotada fun n => f (n + t.cotaLargo n) :=
  Cerradura.composicion h (Cerradura.suma Termino.acotada_id t.cotaLargo_acotada)

/-- La cota del peso es un polinomio. -/
theorem Formula.cotaPeso_acotada : ∀ φ : Formula, Acotada φ.cotaPeso
  | atomo _ => Termino.acotada_const 1
  | conj φ ψ => ac1 (Cerradura.suma (cotaPeso_acotada φ) (cotaPeso_acotada ψ))
  | disy φ ψ => Cerradura.suma (Cerradura.suma (cotaPeso_acotada φ) (cotaPeso_acotada ψ)) (Termino.acotada_const 2)
  | ex t φ => ac1 (Cerradura.suma t.cotaLargo_acotada (acDentro (cotaPeso_acotada φ) t))
  | pt t φ => ac1 (Cerradura.producto (ac1 t.cotaLargo_acotada) (ac1 (acDentro (cotaPeso_acotada φ) t)))

/-! ## Leer un árbol sin suponer su forma -/

def Arbol.izq : Arbol → Arbol
  | .cons v _ => v
  | _ => .hoja

def Arbol.der : Arbol → Arbol
  | .cons _ w => w
  | _ => .hoja

def Arbol.valor : Arbol → ℕ
  | .nodo b _ => b
  | _ => 0

def Arbol.resto : Arbol → Arbol
  | .nodo _ w => w
  | _ => .hoja

/-- El primer testigo de la lista, o la hoja si no hay. -/
def cabeza (a : List Arbol) : Arbol := a.headD .hoja

/-- El peso de una lista de testigos. -/
def pesoL : List Arbol → ℕ
  | [] => 0
  | w :: a => w.peso + pesoL a

theorem Arbol.izq_le (w : Arbol) : w.izq.peso ≤ w.peso := by
  cases w <;> simp only [Arbol.izq, Arbol.peso] <;> omega

theorem Arbol.der_le (w : Arbol) : w.der.peso ≤ w.peso := by
  cases w <;> simp only [Arbol.der, Arbol.peso] <;> omega

theorem Arbol.valor_resto_le (w : Arbol) : Nat.size w.valor + w.resto.peso ≤ w.peso := by
  cases w <;> simp only [Arbol.valor, Arbol.resto, Arbol.peso, Nat.size_zero] <;> omega

theorem cabeza_le (a : List Arbol) : (cabeza a).peso ≤ pesoL a + 1 := by
  cases a <;> simp only [cabeza, List.headD, pesoL, Arbol.peso] <;> omega

theorem pesoL_tail (a : List Arbol) : pesoL a.tail ≤ pesoL a := by
  cases a <;> simp only [List.tail, pesoL] <;> omega

/-! ## Programas -/

/-- **Programas.** Una instrucción por regla, sin fórmulas ni pruebas. -/
inductive Prog : Type
  /-- Devolver el primer testigo. -/
  | id
  /-- Un hecho entre átomos: entregar la posición del primero que vale. -/
  | hecho (qs : List Lit)
  | debilIzq (p : Prog)
  | debilDer (p : Prog)
  | contrIzq (p : Prog)
  | contrDer (p : Prog)
  | cambIzq (p : Prog)
  | cambDer (p : Prog)
  /-- Composición: el resultado de `p` entra como primer testigo de `q`. -/
  | corte (p q : Prog)
  /-- Decidir un átomo y seguir por una rama. -/
  | casos (l : Lit) (p q : Prog)
  | conjDer (p q : Prog)
  | conjIzq (p : Prog)
  | disyDer (p : Prog)
  | disyIzq (p q : Prog)
  /-- Evaluar el término y ponerlo al frente del testigo. -/
  | exDer (s : Termino) (p : Prog)
  /-- Sacar el valor del testigo y meterlo al entorno. -/
  | exIzq (p : Prog)
  /-- Iterar sobre `x = 0, …, |t|` y juntar los resultados en una fila. -/
  | ptDer (t : Termino) (p : Prog)
  /-- Buscar en una fila de `|t| + 1` testigos el del valor de `s`. -/
  | ptIzq (t s : Termino) (p : Prog)
  /-- **Recursión limitada sobre la notación** de `t`. El estado del bucle no pasa de la cota `k`. -/
  | pind (t : Termino) (k : ℕ → ℕ) (p : Prog)

/-- La posición del primer átomo que vale. -/
def indice : List Lit → Entorno → ℕ
  | [], _ => 0
  | l :: ls, ρ => if l.vale ρ = true then 0 else indice ls ρ + 1

/-- El barrido, sin pruebas. -/
def barrerB (paso : ℕ → ℕ × Arbol) : ℕ → Arbol ⊕ (ℕ × Arbol)
  | 0 => .inl .hoja
  | k + 1 =>
      match barrerB paso k with
      | .inr r => .inr r
      | .inl ws =>
          match paso k with
          | (0, v) => .inl (.cons v ws)
          | (i + 1, w) => .inr (i, w)

/-- Recortar: lo que pese más que la cota se cambia por la hoja. -/
def recortar (K : ℕ) (w : Arbol) : Arbol := if w.peso ≤ K then w else .hoja

/-- El bucle de la recursión limitada sobre la notación, sin pruebas. El estado se recorta a `K` en cada vuelta. -/
def lazoB (K : ℕ) (base : Arbol) (paso : ℕ → Arbol → ℕ × Arbol) : (fuel b : ℕ) → Arbol ⊕ (ℕ × Arbol)
  | _, 0 => .inl (recortar K base)
  | 0, _ + 1 => .inl .hoja
  | fuel + 1, b + 1 =>
      match lazoB K base paso fuel ((b + 1) / 2) with
      | .inr r => .inr r
      | .inl v =>
          match paso (b + 1) v with
          | (0, w) => .inl (recortar K w)
          | (i + 1, w) => .inr (i, w)

/-- Buscar en una fila, sin pruebas. -/
def dameB : ℕ → Arbol → ℕ → Arbol
  | k + 1, .cons v w, x => if x = k then v else dameB k w x
  | _, _, _ => .hoja

/-- Del resultado de un bucle a la posición en el sucedente. -/
def salir : Arbol ⊕ (ℕ × Arbol) → ℕ × Arbol
  | .inl w => (0, w)
  | .inr r => (r.1 + 1, r.2)

/-- **El intérprete.** Recibe una cota `n` del largo de las variables, el entorno y los testigos del antecedente.
Devuelve la posición de la fórmula atestiguada y su testigo. -/
def Prog.correr : Prog → ℕ → Entorno → List Arbol → ℕ × Arbol
  | .id, _, _, a => (0, cabeza a)
  | .hecho qs, _, ρ, _ => (indice qs ρ, .hoja)
  | .debilIzq p, n, ρ, a => p.correr n ρ a.tail
  | .debilDer p, n, ρ, a => ((p.correr n ρ a).1 + 1, (p.correr n ρ a).2)
  | .contrIzq p, n, ρ, a => p.correr n ρ (cabeza a :: a)
  | .contrDer p, n, ρ, a =>
      match p.correr n ρ a with
      | (0, w) => (0, w)
      | (i + 1, w) => (i, w)
  | .cambIzq p, n, ρ, a => p.correr n ρ (cabeza a.tail :: cabeza a :: a.tail.tail)
  | .cambDer p, n, ρ, a =>
      match p.correr n ρ a with
      | (0, w) => (1, w)
      | (1, w) => (0, w)
      | (i + 2, w) => (i + 2, w)
  | .corte p q, n, ρ, a =>
      match p.correr n ρ a with
      | (0, w) => q.correr n ρ (w :: a)
      | (i + 1, w) => (i, w)
  | .casos l p q, n, ρ, a => if l.vale ρ = true then p.correr n ρ (.hoja :: a) else q.correr n ρ (.hoja :: a)
  | .conjDer p q, n, ρ, a =>
      match p.correr n ρ a, q.correr n ρ a with
      | (0, v), (0, w) => (0, .cons v w)
      | (i + 1, r), _ => (i + 1, r)
      | _, (j + 1, r) => (j + 1, r)
  | .conjIzq p, n, ρ, a => p.correr n ρ ((cabeza a).izq :: (cabeza a).der :: a.tail)
  | .disyDer p, n, ρ, a =>
      match p.correr n ρ a with
      | (0, w) => (0, .nodo 0 w)
      | (1, w) => (0, .nodo 1 w)
      | (i + 2, w) => (i + 1, w)
  | .disyIzq p q, n, ρ, a =>
      if (cabeza a).valor = 0 then p.correr n ρ ((cabeza a).resto :: a.tail)
      else q.correr n ρ ((cabeza a).resto :: a.tail)
  | .exDer s p, n, ρ, a =>
      match p.correr n ρ a with
      | (0, w) => (0, .nodo (s.val ρ) w)
      | (i + 1, w) => (i + 1, w)
  | .exIzq p, n, ρ, a =>
      p.correr (n + Nat.size (cabeza a).valor) (ext (cabeza a).valor ρ) (.hoja :: (cabeza a).resto :: a.tail)
  | .ptDer t p, n, ρ, a =>
      salir (barrerB (fun x => p.correr (n + Nat.size x) (ext x ρ) (.hoja :: a)) (Nat.size (t.val ρ) + 1))
  | .ptIzq t s p, n, ρ, a => p.correr n ρ (dameB (Nat.size (t.val ρ) + 1) (cabeza a) (s.val ρ) :: a.tail)
  | .pind t k p, n, ρ, a =>
      salir (lazoB (k (n + Nat.size (t.val ρ))) (cabeza a)
        (fun b v => p.correr (n + Nat.size b) (ext b ρ) (v :: a.tail)) (t.val ρ) (t.val ρ))

/-! ## Quitar las pruebas -/

/-- **De la derivación al programa.** Se va todo lo que no se ejecuta: las fórmulas, las pruebas de los hechos
aritméticos y las premisas que solo acotan. De la fórmula de inducción queda su cota del peso. -/
def Deriv.borrar : {Γ Δ : List Formula} → Deriv Γ Δ → Prog
  | _, _, .id _ => .id
  | _, _, .aritm _ qs _ => .hecho qs
  | _, _, .debilIzq _ d => .debilIzq d.borrar
  | _, _, .debilDer _ d => .debilDer d.borrar
  | _, _, .contrIzq d => .contrIzq d.borrar
  | _, _, .contrDer d => .contrDer d.borrar
  | _, _, .cambIzq d => .cambIzq d.borrar
  | _, _, .cambDer d => .cambDer d.borrar
  | _, _, .corte _ d₁ d₂ => .corte d₁.borrar d₂.borrar
  | _, _, .casos l d₁ d₂ => .casos l d₁.borrar d₂.borrar
  | _, _, .conjDer d₁ d₂ => .conjDer d₁.borrar d₂.borrar
  | _, _, .conjIzq d => .conjIzq d.borrar
  | _, _, .disyDer d => .disyDer d.borrar
  | _, _, .disyIzq d₁ d₂ => .disyIzq d₁.borrar d₂.borrar
  | _, _, .exDer _ s _ _ d => .exDer s d.borrar
  | _, _, .exIzq _ _ d => .exIzq d.borrar
  | _, _, .ptDer t _ d => .ptDer t d.borrar
  | _, _, .ptIzq t s _ _ d => .ptIzq t s d.borrar
  | _, _, .pind t φ d => .pind t φ.cotaPeso d.borrar

/-- Los testigos de un antecedente, sin sus pruebas. -/
def Ant.borrar {ρ : Entorno} : {Γ : List Formula} → Ant ρ Γ → List Arbol
  | _, .nil => []
  | _, .cons w _ a => w :: a.borrar

/-- El testigo de un sucedente, sin su prueba: la posición y el árbol. -/
def Suc.borrar {ρ : Entorno} : {Δ : List Formula} → Suc ρ Δ → ℕ × Arbol
  | _, .aqui w _ => (0, w)
  | _, .alla r => (r.borrar.1 + 1, r.borrar.2)

/-- El resultado de un bucle, sin pruebas. -/
def borrarSum {P : Arbol → Prop} {ρ : Entorno} {Δ : List Formula} :
    {w // P w} ⊕ Suc ρ Δ → Arbol ⊕ (ℕ × Arbol)
  | .inl v => .inl v.1
  | .inr r => .inr r.borrar

theorem Suc.primero_borrar {ρ : Entorno} :
    (qs : List Lit) → (h : ∃ q ∈ qs, q.vale ρ = true) → (Suc.primero qs h).borrar = (indice qs ρ, .hoja)
  | [], h => False.elim (by obtain ⟨_, hq, _⟩ := h; exact List.not_mem_nil hq)
  | l :: ls, h => by
      unfold Suc.primero indice
      split
      · rfl
      · change ((Suc.primero ls _).borrar.1 + 1, (Suc.primero ls _).borrar.2) = _
        rw [Suc.primero_borrar ls]

theorem Ant.sube_borrar {ρ : Entorno} (b : ℕ) : {Γ : List Formula} → (a : Ant ρ Γ) → (a.sube b).borrar = a.borrar
  | _, .nil => rfl
  | _, .cons w h a => by simp only [Ant.sube, Ant.borrar, Ant.sube_borrar b a]

theorem Suc.baja_borrar {ρ : Entorno} (b : ℕ) :
    (Δ : List Formula) → (r : Suc (ext b ρ) (Δ.map Formula.sube)) → (Suc.baja b Δ r).borrar = r.borrar
  | _ :: _, .aqui w h => rfl
  | _ :: Δ, .alla r => by
      change ((Suc.baja b Δ r).borrar.1 + 1, (Suc.baja b Δ r).borrar.2) = (r.borrar.1 + 1, r.borrar.2)
      rw [Suc.baja_borrar b Δ r]

theorem Suc.deSuma_borrar {ρ : Entorno} {φ : Formula} {Δ : List Formula} {P : Arbol → Prop}
    (f : ∀ w, P w → Testigo φ ρ w) (x : {w // P w} ⊕ Suc ρ Δ) :
    (Suc.deSuma f x).borrar = salir (borrarSum x) := by
  cases x <;> rfl

theorem dame_borrar {P : ℕ → Arbol → Prop} :
    ∀ (k : ℕ) (w : Arbol) (h : Todos P k w) (x : ℕ) (hx : x < k), (Todos.dame k w h x hx).1 = dameB k w x
  | 0, _, _, _, hx => absurd hx (Nat.not_lt_zero _)
  | _ + 1, .hoja, h, _, _ => h.elim
  | _ + 1, .nodo _ _, h, _, _ => h.elim
  | k + 1, .cons v w, h, x, hx => by
      rw [Todos.dame, dameB]
      split
      · rfl
      · exact dame_borrar k w h.2 x _

theorem barrer_borrar {ρ : Entorno} {φ : Formula} {Δ : List Formula} (m : ℕ)
    (paso : (x : ℕ) → x ≤ m → Suc (ext x ρ) (φ :: Δ.map Formula.sube) × ℕ)
    (pasoB : ℕ → ℕ × Arbol) (hp : ∀ x hx, pasoB x = (paso x hx).1.borrar) :
    ∀ (k : ℕ) (hk : k ≤ m + 1), borrarSum (barrer m paso k hk).1 = barrerB pasoB k
  | 0, _ => rfl
  | k + 1, hk => by
      have ih := barrer_borrar m paso pasoB hp k (Nat.le_of_succ_le hk)
      rw [barrer, barrerB, ← ih, hp k (Nat.le_of_succ_le_succ hk)]
      generalize barrer m paso k _ = r
      obtain ⟨ws | r, c⟩ := r
      · dsimp only [borrarSum]
        generalize paso k _ = q
        obtain ⟨q, c'⟩ := q
        cases q <;> simp [Suc.borrar, Suc.baja_borrar]
      · simp [borrarSum]

/-- El bucle con pruebas y el bucle a secas dan lo mismo, **y el recorte no actúa**: los testigos del bucle con
pruebas son válidos, así que pesan menos que la cota. -/
theorem lazo_borrar {ρ : Entorno} {φ : Formula} {Δ : List Formula}
    (base : {w // Testigo φ (ext 0 ρ) w})
    (paso : (b : ℕ) → {w // Testigo φ (ext (b / 2) ρ) w} → Suc (ext b ρ) (φ :: Δ.map Formula.sube) × ℕ)
    (pasoB : ℕ → Arbol → ℕ × Arbol) (hp : ∀ b v, pasoB b v.1 = (paso b v).1.borrar)
    (B K : ℕ) (hK : ∀ b, b ≤ B → ∀ v : {w // Testigo φ (ext b ρ) w}, v.1.peso ≤ K) :
    ∀ (fuel b : ℕ) (h : b < 2 ^ fuel), b ≤ B →
      borrarSum (lazo base paso fuel b h).1 = lazoB K base.1 pasoB fuel b
  | _, 0, _, hb => by simp [lazo, lazoB, borrarSum, recortar, hK 0 hb base]
  | 0, _ + 1, h, _ => absurd h (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le _)))
  | fuel + 1, b + 1, h, hb => by
      have ih := lazo_borrar base paso pasoB hp B K hK fuel ((b + 1) / 2)
        (by rw [Nat.pow_succ] at h; omega) (Nat.le_trans (Nat.div_le_self _ _) hb)
      rw [lazo, lazoB, ← ih]
      generalize lazo base paso fuel ((b + 1) / 2) _ = r
      obtain ⟨v | r, c⟩ := r
      · dsimp only [borrarSum]
        rw [hp (b + 1) v]
        generalize paso (b + 1) v = q
        obtain ⟨q, c'⟩ := q
        cases q with
        | aqui w' h' => simp [borrarSum, Suc.borrar, recortar, hK (b + 1) hb ⟨w', h'⟩]
        | alla r => simp [borrarSum, Suc.borrar, Suc.baja_borrar]
      · simp [borrarSum]

/-! ## La corrección -/

/-- **El programa hace lo que la extracción.** Correr el programa de una derivación sobre los testigos a secas da
el testigo extraído, a secas. -/
theorem correcto : {Γ Δ : List Formula} → (d : Deriv Γ Δ) → (n : ℕ) → (ρ : Entorno) → (a : Ant ρ Γ) →
    Chico n ρ → d.borrar.correr n ρ a.borrar = (extraerC d ρ a).1.borrar
  | _, _, .id _, _, _, .cons _ _ _, _ => rfl
  | _, _, .aritm ps qs hp, _, ρ, a, _ => (Suc.primero_borrar qs (hp ρ (Ant.atomos ps a))).symm
  | _, _, .debilIzq _ d, n, ρ, .cons _ _ a, hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar, extraerC]; exact correcto d n ρ a hρ
  | _, _, .debilDer _ d, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC, Suc.borrar, correcto d n ρ a hρ]
  | _, _, .contrIzq d, n, ρ, .cons w h a, hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar, extraerC]
      exact correcto d n ρ (.cons w h (.cons w h a)) hρ
  | _, _, .contrDer d, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC, correcto d n ρ a hρ]
      generalize (extraerC d ρ a).1 = r
      cases r <;> simp [Suc.borrar]
  | _, _, .cambIzq d, n, ρ, .cons w h (.cons w' h' a), hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar, extraerC]
      exact correcto d n ρ (.cons w' h' (.cons w h a)) hρ
  | _, _, .cambDer d, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC, correcto d n ρ a hρ]
      generalize (extraerC d ρ a).1 = r
      rcases r with _ | (_ | _) <;> simp [Suc.borrar]
  | _, _, .corte _ d₁ d₂, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC, correcto d₁ n ρ a hρ]
      generalize (extraerC d₁ ρ a).2 = c
      generalize (extraerC d₁ ρ a).1 = r
      cases r with
      | aqui w h => simp only [Suc.borrar]; exact correcto d₂ n ρ (.cons w h a) hρ
      | alla r => simp [Suc.borrar]
  | _, _, .casos l d₁ d₂, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC]
      by_cases h : l.vale ρ = true
      · simp only [h, ↓reduceIte, ↓reduceDIte]; exact correcto d₁ n ρ (.cons .hoja ⟨rfl, h⟩ a) hρ
      · simp only [h, ↓reduceIte, ↓reduceDIte]
        exact correcto d₂ n ρ (.cons .hoja ⟨rfl, Lit.neg_vale_de h⟩ a) hρ
  | _, _, .conjDer d₁ d₂, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC, correcto d₁ n ρ a hρ, correcto d₂ n ρ a hρ]
      generalize (extraerC d₁ ρ a).1 = r₁
      generalize (extraerC d₂ ρ a).1 = r₂
      cases r₁ <;> cases r₂ <;> simp [Suc.borrar]
  | _, _, .conjIzq _, _, _, .cons .hoja h _, _ => h.elim
  | _, _, .conjIzq _, _, _, .cons (.nodo _ _) h _, _ => h.elim
  | _, _, .conjIzq d, n, ρ, .cons (.cons v w) h a, hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar, extraerC]
      exact correcto d n ρ (.cons v h.1 (.cons w h.2 a)) hρ
  | _, _, .disyDer d, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC, correcto d n ρ a hρ]
      generalize (extraerC d ρ a).1 = r
      rcases r with _ | (_ | _) <;> simp [Suc.borrar]
  | _, _, .disyIzq _ _, _, _, .cons .hoja h _, _ => h.elim
  | _, _, .disyIzq _ _, _, _, .cons (.cons _ _) h _, _ => h.elim
  | _, _, .disyIzq _ _, _, _, .cons (.nodo (_ + 2) _) h _, _ => h.elim
  | _, _, .disyIzq d₁ _, n, ρ, .cons (.nodo 0 w) h a, hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar, extraerC]
      exact correcto d₁ n ρ (.cons w h a) hρ
  | _, _, .disyIzq _ d₂, n, ρ, .cons (.nodo 1 w) h a, hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar, extraerC]
      exact correcto d₂ n ρ (.cons w h a) hρ
  | _, _, .exDer _ s _ d₀ d, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC, correcto d n ρ a hρ]
      generalize (extraerC d ρ a).1 = r
      cases r <;> rfl
  | _, _, .exIzq _ _ _, _, _, .cons .hoja h _, _ => h.elim
  | _, _, .exIzq _ _ _, _, _, .cons (.cons _ _) h _, _ => h.elim
  | _, _, .exIzq t _ d, n, ρ, .cons (.nodo b w) h a, hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar, extraerC, Suc.baja_borrar]
      rw [← Ant.sube_borrar b a]
      refine Eq.trans ?_ (correcto d (n + Nat.size b) (ext b ρ) _ (hρ.ext (Nat.le_refl _)))
      rfl
  | _, _, .ptDer t φ d, n, ρ, a, hρ => by
      simp only [Deriv.borrar, Prog.correr, extraerC]
      refine Eq.trans ?_ (Suc.deSuma_borrar _ _).symm
      refine congrArg salir (barrer_borrar _ _ _ ?_ _ _).symm
      intro x hx
      rw [← Ant.sube_borrar x a]
      refine Eq.trans ?_ (correcto d (n + Nat.size x) (ext x ρ) _ (hρ.ext (Nat.le_refl _)))
      rfl
  | _, _, .ptIzq _ _ _ d₀ d, n, ρ, .cons w h a, hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar, extraerC]
      refine Eq.trans ?_ (correcto d n ρ _ hρ)
      exact congrArg (fun z => d.borrar.correr n ρ (z :: a.borrar)) (dame_borrar _ w h _ _).symm
  | _, _, .pind (Δ := Δ) t φ d, n, ρ, .cons w h a, hρ => by
      simp only [Deriv.borrar, Prog.correr, Ant.borrar]
      refine Eq.trans ?_ (Suc.deSuma_borrar (fun v hv => (testigo_inst t φ ρ v).mpr hv)
        (lazo (Δ := Δ) ⟨w, (testigo_inst .cero φ ρ w).mp h⟩
          (fun b v => extraerC d (ext b ρ) (.cons v.1 ((testigo_mitad φ b ρ v.1).mpr v.2) (Ant.sube b a)))
          (t.val ρ) (t.val ρ) Nat.lt_two_pow_self).1).symm
      refine congrArg salir (Eq.symm ?_)
      refine lazo_borrar _ _ (fun b v => d.borrar.correr (n + Nat.size b) (ext b ρ) (v :: a.borrar)) ?_
        (t.val ρ) _ ?_ _ _ _ (Nat.le_refl _)
      · intro b v
        rw [← Ant.sube_borrar b a]
        refine Eq.trans ?_ (correcto d (n + Nat.size b) (ext b ρ) _ (hρ.ext (Nat.le_refl _)))
        rfl
      · intro b hb v
        exact peso_le φ _ _ _ (hρ.ext (Nat.size_le_size hb)) v.2

/-- **El testigo es lo que el programa entrega.** Para una derivación sin hipótesis y con una sola fórmula, el
programa devuelve la posición `0` y el testigo extraído. -/
theorem programa_del_testigo {φ : Formula} (d : Deriv [] [φ]) {n : ℕ} {ρ : Entorno} (hρ : Chico n ρ) :
    d.borrar.correr n ρ [] = (0, testigoExtraido d ρ) := by
  have h := correcto d n ρ .nil hρ
  unfold testigoExtraido extraer
  simp only [Ant.borrar] at h
  rw [h]
  generalize (extraerC d ρ .nil).1 = r
  cases r with
  | aqui w _ => rfl
  | alla r => cases r

/-- Y por tanto lo que el programa entrega atestigua la fórmula. -/
theorem programa_atestigua {φ : Formula} (d : Deriv [] [φ]) {n : ℕ} {ρ : Entorno} (hρ : Chico n ρ) :
    Testigo φ ρ (d.borrar.correr n ρ []).2 := by
  rw [programa_del_testigo d hρ]; exact testigoExtraido_vale d ρ

/-! ## El programa está limitado, aun con entradas basura -/

/-- Un programa está limitado si las cotas de sus recursiones son crecientes y polinomiales. -/
def Prog.Limitado : Prog → Prop
  | .id => True
  | .hecho _ => True
  | .debilIzq p => p.Limitado
  | .debilDer p => p.Limitado
  | .contrIzq p => p.Limitado
  | .contrDer p => p.Limitado
  | .cambIzq p => p.Limitado
  | .cambDer p => p.Limitado
  | .corte p q => p.Limitado ∧ q.Limitado
  | .casos _ p q => p.Limitado ∧ q.Limitado
  | .conjDer p q => p.Limitado ∧ q.Limitado
  | .conjIzq p => p.Limitado
  | .disyDer p => p.Limitado
  | .disyIzq p q => p.Limitado ∧ q.Limitado
  | .exDer _ p => p.Limitado
  | .exIzq p => p.Limitado
  | .ptDer _ p => p.Limitado
  | .ptIzq _ _ p => p.Limitado
  | .pind _ k p => (∀ a b, a ≤ b → k a ≤ k b) ∧ Acotada k ∧ p.Limitado

/-- El programa de una derivación está limitado: sus cotas son las del peso de las fórmulas de inducción. -/
theorem Deriv.borrar_limitado : {Γ Δ : List Formula} → (d : Deriv Γ Δ) → d.borrar.Limitado
  | _, _, .id _ => trivial
  | _, _, .aritm _ _ _ => trivial
  | _, _, .debilIzq _ d => d.borrar_limitado
  | _, _, .debilDer _ d => d.borrar_limitado
  | _, _, .contrIzq d => d.borrar_limitado
  | _, _, .contrDer d => d.borrar_limitado
  | _, _, .cambIzq d => d.borrar_limitado
  | _, _, .cambDer d => d.borrar_limitado
  | _, _, .corte _ d₁ d₂ => ⟨d₁.borrar_limitado, d₂.borrar_limitado⟩
  | _, _, .casos _ d₁ d₂ => ⟨d₁.borrar_limitado, d₂.borrar_limitado⟩
  | _, _, .conjDer d₁ d₂ => ⟨d₁.borrar_limitado, d₂.borrar_limitado⟩
  | _, _, .conjIzq d => d.borrar_limitado
  | _, _, .disyDer d => d.borrar_limitado
  | _, _, .disyIzq d₁ d₂ => ⟨d₁.borrar_limitado, d₂.borrar_limitado⟩
  | _, _, .exDer _ _ _ _ d => d.borrar_limitado
  | _, _, .exIzq _ _ d => d.borrar_limitado
  | _, _, .ptDer _ _ d => d.borrar_limitado
  | _, _, .ptIzq _ _ _ _ d => d.borrar_limitado
  | _, _, .pind _ φ d => ⟨fun _ _ h => φ.cotaPeso_mono h, φ.cotaPeso_acotada, d.borrar_limitado⟩

/-- **El techo.** Cuánto puede pesar lo que el programa entrega, si el largo de las variables más el peso de los
testigos de entrada no pasa de `N`. -/
def Prog.techo : Prog → ℕ → ℕ
  | .id, N => N + 1
  | .hecho _, _ => 1
  | .debilIzq p, N => p.techo N
  | .debilDer p, N => p.techo N
  | .contrIzq p, N => p.techo (2 * N + 1)
  | .contrDer p, N => p.techo N
  | .cambIzq p, N => p.techo (3 * N + 2)
  | .cambDer p, N => p.techo N
  | .corte p q, N => p.techo N + q.techo (N + p.techo N)
  | .casos _ p q, N => p.techo (N + 1) + q.techo (N + 1)
  | .conjDer p q, N => p.techo N + q.techo N + 1
  | .conjIzq p, N => p.techo (3 * N + 2)
  | .disyDer p, N => p.techo N + 2
  | .disyIzq p q, N => p.techo (2 * N + 1) + q.techo (2 * N + 1)
  | .exDer s p, N => s.cotaLargo N + p.techo N + 1
  | .exIzq p, N => p.techo (2 * N + 2)
  | .ptDer t p, N =>
      (t.cotaLargo N + 1) * (p.techo (N + t.cotaLargo N + 1) + 1) + 1 + p.techo (N + t.cotaLargo N + 1)
  | .ptIzq _ _ p, N => p.techo (2 * N + 1)
  | .pind t k p, N =>
      k (N + t.cotaLargo N) + 1 + p.techo (N + t.cotaLargo N + k (N + t.cotaLargo N) + 1)

/-- El resultado de un bucle está dentro de dos cotas: una para el estado y otra para la salida lateral. -/
def Dentro (bf bs : ℕ) : Arbol ⊕ (ℕ × Arbol) → Prop
  | .inl w => w.peso ≤ bf
  | .inr r => r.2.peso ≤ bs

theorem salir_peso {bf bs : ℕ} {x : Arbol ⊕ (ℕ × Arbol)} (h : Dentro bf bs x) : (salir x).2.peso ≤ bf + bs := by
  cases x with
  | inl w => exact Nat.le_trans h (Nat.le_add_right _ _)
  | inr r => exact Nat.le_trans h (Nat.le_add_left _ _)

theorem recortar_le (K : ℕ) (w : Arbol) : (recortar K w).peso ≤ K + 1 := by
  unfold recortar
  split
  · omega
  · simp only [Arbol.peso]; omega

theorem dameB_le : ∀ (k : ℕ) (w : Arbol) (x : ℕ), (dameB k w x).peso ≤ w.peso
  | 0, w, _ => by simp only [dameB, Arbol.peso]; exact w.peso_pos
  | _ + 1, .hoja, _ => by simp only [dameB, Arbol.peso]; omega
  | _ + 1, .nodo _ _, _ => by simp only [dameB, Arbol.peso]; omega
  | k + 1, .cons v w, x => by
      have h := dameB_le k w x
      simp only [dameB, Arbol.peso]
      split <;> omega

theorem barrerB_peso (paso : ℕ → ℕ × Arbol) (C : ℕ) :
    ∀ k : ℕ, (∀ x, x < k → (paso x).2.peso ≤ C) → Dentro (k * (C + 1) + 1) C (barrerB paso k)
  | 0, _ => by simp [barrerB, Dentro, Arbol.peso]
  | k + 1, hp => by
      have ih := barrerB_peso paso C k fun x hx => hp x (Nat.lt_succ_of_lt hx)
      rw [barrerB]
      generalize barrerB paso k = r at ih ⊢
      cases r with
      | inr r => exact ih
      | inl ws =>
        have hc := hp k (Nat.lt_succ_self k)
        generalize paso k = q at hc ⊢
        obtain ⟨i, v⟩ := q
        cases i with
        | zero =>
          simp only [Dentro, Arbol.peso, Nat.add_mul, Nat.one_mul] at ih hc ⊢
          omega
        | succ i => exact hc

theorem lazoB_peso (K : ℕ) (base : Arbol) (paso : ℕ → Arbol → ℕ × Arbol) (B C : ℕ)
    (hp : ∀ b v, b ≤ B → v.peso ≤ K + 1 → (paso b v).2.peso ≤ C) :
    ∀ fuel b : ℕ, b ≤ B → Dentro (K + 1) C (lazoB K base paso fuel b)
  | _, 0, _ => by simp only [lazoB, Dentro]; exact recortar_le K base
  | 0, _ + 1, _ => by simp only [lazoB, Dentro, Arbol.peso]; omega
  | fuel + 1, b + 1, hb => by
      have ih := lazoB_peso K base paso B C hp fuel ((b + 1) / 2) (Nat.le_trans (Nat.div_le_self _ _) hb)
      rw [lazoB]
      generalize lazoB K base paso fuel ((b + 1) / 2) = r at ih ⊢
      cases r with
      | inr r => exact ih
      | inl v =>
        have hc := hp (b + 1) v hb ih
        dsimp only
        generalize paso (b + 1) v = q at hc ⊢
        obtain ⟨i, w⟩ := q
        cases i with
        | zero => exact recortar_le K w
        | succ i => exact hc

/-- **Lo que un programa limitado entrega no pesa más que su techo**, para toda entrada: los testigos de `a` no
tienen que ser válidos. -/
theorem techo_le : (p : Prog) → p.Limitado → ∀ (n : ℕ) (ρ : Entorno) (a : List Arbol) (N : ℕ),
    Chico n ρ → n + pesoL a ≤ N → (p.correr n ρ a).2.peso ≤ p.techo N
  | .id, _, n, ρ, a, N, _, hN => by
      have := cabeza_le a
      simp only [Prog.correr, Prog.techo]; omega
  | .hecho _, _, _, _, _, _, _, _ => Nat.le_refl _
  | .debilIzq p, hl, n, ρ, a, N, hρ, hN => by
      have := pesoL_tail a
      exact techo_le p hl n ρ a.tail N hρ (by omega)
  | .debilDer p, hl, n, ρ, a, N, hρ, hN => techo_le p hl n ρ a N hρ hN
  | .contrIzq p, hl, n, ρ, a, N, hρ, hN => by
      have := cabeza_le a
      exact techo_le p hl n ρ (cabeza a :: a) (2 * N + 1) hρ (by simp only [pesoL]; omega)
  | .contrDer p, hl, n, ρ, a, N, hρ, hN => by
      have ih := techo_le p hl n ρ a N hρ hN
      simp only [Prog.correr, Prog.techo]
      generalize p.correr n ρ a = r at ih ⊢
      obtain ⟨i, w⟩ := r
      cases i <;> exact ih
  | .cambIzq p, hl, n, ρ, a, N, hρ, hN => by
      have h₁ := cabeza_le a
      have h₂ := cabeza_le a.tail
      have h₃ := pesoL_tail a
      have h₄ := pesoL_tail a.tail
      exact techo_le p hl n ρ _ (3 * N + 2) hρ (by simp only [pesoL]; omega)
  | .cambDer p, hl, n, ρ, a, N, hρ, hN => by
      have ih := techo_le p hl n ρ a N hρ hN
      simp only [Prog.correr, Prog.techo]
      generalize p.correr n ρ a = r at ih ⊢
      obtain ⟨i, w⟩ := r
      rcases i with _ | _ | i <;> exact ih
  | .corte p q, hl, n, ρ, a, N, hρ, hN => by
      have ih := techo_le p hl.1 n ρ a N hρ hN
      simp only [Prog.correr, Prog.techo]
      generalize p.correr n ρ a = r at ih ⊢
      obtain ⟨i, w⟩ := r
      cases i with
      | zero =>
        change w.peso ≤ _ at ih
        exact Nat.le_trans (techo_le q hl.2 n ρ (w :: a) (N + p.techo N) hρ (by simp only [pesoL]; omega))
          (Nat.le_add_left _ _)
      | succ i => exact Nat.le_trans ih (Nat.le_add_right _ _)
  | .casos l p q, hl, n, ρ, a, N, hρ, hN => by
      simp only [Prog.correr, Prog.techo]
      split
      · exact Nat.le_trans (techo_le p hl.1 n ρ _ (N + 1) hρ (by simp only [pesoL, Arbol.peso]; omega))
          (Nat.le_add_right _ _)
      · exact Nat.le_trans (techo_le q hl.2 n ρ _ (N + 1) hρ (by simp only [pesoL, Arbol.peso]; omega))
          (Nat.le_add_left _ _)
  | .conjDer p q, hl, n, ρ, a, N, hρ, hN => by
      have ih₁ := techo_le p hl.1 n ρ a N hρ hN
      have ih₂ := techo_le q hl.2 n ρ a N hρ hN
      simp only [Prog.correr, Prog.techo]
      generalize p.correr n ρ a = r₁ at ih₁ ⊢
      generalize q.correr n ρ a = r₂ at ih₂ ⊢
      obtain ⟨i, v⟩ := r₁
      obtain ⟨j, w⟩ := r₂
      change v.peso ≤ _ at ih₁
      change w.peso ≤ _ at ih₂
      cases i <;> cases j <;> simp only [Arbol.peso] <;> omega
  | .conjIzq p, hl, n, ρ, a, N, hρ, hN => by
      have h₁ := cabeza_le a
      have h₂ := (cabeza a).izq_le
      have h₃ := (cabeza a).der_le
      have h₄ := pesoL_tail a
      exact techo_le p hl n ρ _ (3 * N + 2) hρ (by simp only [pesoL]; omega)
  | .disyDer p, hl, n, ρ, a, N, hρ, hN => by
      have ih := techo_le p hl n ρ a N hρ hN
      simp only [Prog.correr, Prog.techo]
      generalize p.correr n ρ a = r at ih ⊢
      obtain ⟨i, w⟩ := r
      change w.peso ≤ _ at ih
      rcases i with _ | _ | i <;> simp only [Arbol.peso, Nat.size_zero, Nat.zero_add, Nat.size_one] <;> omega
  | .disyIzq p q, hl, n, ρ, a, N, hρ, hN => by
      have h₁ := cabeza_le a
      have h₂ := (cabeza a).valor_resto_le
      have h₃ := pesoL_tail a
      simp only [Prog.correr, Prog.techo]
      split
      · exact Nat.le_trans (techo_le p hl.1 n ρ _ (2 * N + 1) hρ (by simp only [pesoL]; omega))
          (Nat.le_add_right _ _)
      · exact Nat.le_trans (techo_le q hl.2 n ρ _ (2 * N + 1) hρ (by simp only [pesoL]; omega))
          (Nat.le_add_left _ _)
  | .exDer s p, hl, n, ρ, a, N, hρ, hN => by
      have ih := techo_le p hl n ρ a N hρ hN
      have hs := s.largo_val_le (hρ.mono (Nat.le_trans (Nat.le_add_right _ _) hN))
      simp only [Prog.correr, Prog.techo]
      generalize p.correr n ρ a = r at ih ⊢
      obtain ⟨i, w⟩ := r
      change w.peso ≤ _ at ih
      cases i <;> simp only [Arbol.peso] <;> omega
  | .exIzq p, hl, n, ρ, a, N, hρ, hN => by
      have h₁ := cabeza_le a
      have h₂ := (cabeza a).valor_resto_le
      have h₃ := pesoL_tail a
      exact techo_le p hl _ _ _ (2 * N + 2) (hρ.ext (Nat.le_refl _))
        (by simp only [pesoL, Arbol.peso]; omega)
  | .ptDer t p, hl, n, ρ, a, N, hρ, hN => by
      have hL := t.largo_val_le (hρ.mono (Nat.le_trans (Nat.le_add_right _ _) hN))
      have hb := barrerB_peso (fun x => p.correr (n + Nat.size x) (ext x ρ) (.hoja :: a))
        (p.techo (N + t.cotaLargo N + 1)) (Nat.size (t.val ρ) + 1) (fun x hx => by
          have hx' : Nat.size x ≤ Nat.size (t.val ρ) :=
            Nat.le_trans (Nat.size_le_size (Nat.le_of_lt_succ hx))
              (Nat.size_le_size (Nat.size_le.mpr Nat.lt_two_pow_self))
          exact techo_le p hl _ _ _ _ (hρ.ext (Nat.le_refl _)) (by simp only [pesoL, Arbol.peso]; omega))
      have hs := salir_peso hb
      have hm : (Nat.size (t.val ρ) + 1) * (p.techo (N + t.cotaLargo N + 1) + 1) ≤
          (t.cotaLargo N + 1) * (p.techo (N + t.cotaLargo N + 1) + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_succ hL)
      simp only [Prog.correr, Prog.techo]
      omega
  | .ptIzq t s p, hl, n, ρ, a, N, hρ, hN => by
      have h₁ := cabeza_le a
      have h₂ := dameB_le (Nat.size (t.val ρ) + 1) (cabeza a) (s.val ρ)
      have h₃ := pesoL_tail a
      exact techo_le p hl n ρ _ (2 * N + 1) hρ (by simp only [pesoL]; omega)
  | .pind t k p, hl, n, ρ, a, N, hρ, hN => by
      have hL := t.largo_val_le (hρ.mono (Nat.le_trans (Nat.le_add_right _ _) hN))
      have hK : k (n + Nat.size (t.val ρ)) ≤ k (N + t.cotaLargo N) := hl.1 _ _ (by omega)
      have h₃ := pesoL_tail a
      have hb := lazoB_peso (k (n + Nat.size (t.val ρ))) (cabeza a)
        (fun b v => p.correr (n + Nat.size b) (ext b ρ) (v :: a.tail)) (t.val ρ)
        (p.techo (N + t.cotaLargo N + k (N + t.cotaLargo N) + 1)) (fun b v hb hv => by
          have hb' := Nat.size_le_size hb
          exact techo_le p hl.2.2 _ _ _ _ (hρ.ext (Nat.le_refl _)) (by simp only [pesoL]; omega))
        (t.val ρ) (t.val ρ) (Nat.le_refl _)
      have hs := salir_peso hb
      simp only [Prog.correr, Prog.techo]
      omega

private theorem acLin (f : ℕ → ℕ) (h : Acotada f) (c d : ℕ) : Acotada fun N => f (c * N + d) :=
  Cerradura.composicion h ⟨Polynomial.C c * Polynomial.X + Polynomial.C d, fun _ => by simp⟩

private theorem acMas (f : ℕ → ℕ) (h : Acotada f) (c : ℕ) : Acotada fun N => f (N + c) :=
  Cerradura.composicion h (Cerradura.suma Termino.acotada_id (Termino.acotada_const c))

/-- **El techo es un polinomio.** Otra vez: cada instrucción lo arma con sumas, productos y composiciones, y el
programa es fijo. -/
theorem techo_acotada : (p : Prog) → p.Limitado → Acotada p.techo
  | .id, _ => ac1 Termino.acotada_id
  | .hecho _, _ => Termino.acotada_const 1
  | .debilIzq p, hl => techo_acotada p hl
  | .debilDer p, hl => techo_acotada p hl
  | .contrIzq p, hl => acLin _ (techo_acotada p hl) 2 1
  | .contrDer p, hl => techo_acotada p hl
  | .cambIzq p, hl => acLin _ (techo_acotada p hl) 3 2
  | .cambDer p, hl => techo_acotada p hl
  | .corte p q, hl =>
      Cerradura.suma (techo_acotada p hl.1)
        (Cerradura.composicion (techo_acotada q hl.2) (Cerradura.suma Termino.acotada_id (techo_acotada p hl.1)))
  | .casos _ p q, hl => Cerradura.suma (acMas _ (techo_acotada p hl.1) 1) (acMas _ (techo_acotada q hl.2) 1)
  | .conjDer p q, hl => ac1 (Cerradura.suma (techo_acotada p hl.1) (techo_acotada q hl.2))
  | .conjIzq p, hl => acLin _ (techo_acotada p hl) 3 2
  | .disyDer p, hl => Cerradura.suma (techo_acotada p hl) (Termino.acotada_const 2)
  | .disyIzq p q, hl => Cerradura.suma (acLin _ (techo_acotada p hl.1) 2 1) (acLin _ (techo_acotada q hl.2) 2 1)
  | .exDer s p, hl => ac1 (Cerradura.suma s.cotaLargo_acotada (techo_acotada p hl))
  | .exIzq p, hl => acLin _ (techo_acotada p hl) 2 2
  | .ptDer t p, hl =>
      have hC : Acotada fun N => p.techo (N + t.cotaLargo N + 1) :=
        Cerradura.composicion (techo_acotada p hl)
          (ac1 (Cerradura.suma Termino.acotada_id t.cotaLargo_acotada))
      Cerradura.suma (ac1 (Cerradura.producto (ac1 t.cotaLargo_acotada) (ac1 hC))) hC
  | .ptIzq _ _ p, hl => acLin _ (techo_acotada p hl) 2 1
  | .pind t k p, hl =>
      have hg : Acotada fun N => N + t.cotaLargo N := Cerradura.suma Termino.acotada_id t.cotaLargo_acotada
      have hk : Acotada fun N => k (N + t.cotaLargo N) := Cerradura.composicion hl.2.1 hg
      Cerradura.suma (ac1 hk) (Cerradura.composicion (techo_acotada p hl.2.2) (ac1 (Cerradura.suma hg hk)))

/-- **El lema del testigo, con su límite.** De una derivación sale un programa que:

1. sobre testigos válidos entrega el testigo que la extracción da (`correcto`);
2. sobre cualquier entrada, válida o no, entrega algo cuyo peso es polinomial en el largo de las variables más el
   peso de los testigos de entrada. -/
theorem programa_limitado {Γ Δ : List Formula} (d : Deriv Γ Δ) :
    ∃ q : Polynomial ℕ, ∀ (n : ℕ) (ρ : Entorno) (a : List Arbol), Chico n ρ →
      (d.borrar.correr n ρ a).2.peso ≤ q.eval (n + pesoL a) := by
  obtain ⟨q, hq⟩ := techo_acotada d.borrar d.borrar_limitado
  exact ⟨q, fun n ρ a hρ => Nat.le_trans (techo_le d.borrar d.borrar_limitado n ρ a _ hρ (Nat.le_refl _)) (hq _)⟩

/-! ## Los programas de los ejemplos -/

/-- El programa del largo, corrido a secas: cuenta los bits de `1000`. Aquí `10` es el largo de la entrada. -/
example : ejemploLargo.borrar.correr 10 (fun _ => 1000) [] = (0, .nodo 10 .hoja) := by decide

/-- Lo que quedó de la prueba del paso: sacar el valor, decidir si `b = 0`, y entregar `0` o el sucesor. -/
example : pasoLargo.borrar =
    .exIzq (.casos ⟨.eq, .var 1, .cero⟩
      (.exDer .cero (.hecho [⟨.eq, .cero, .largo (.var 1)⟩]))
      (.exDer (.suc (.var 0)) (.hecho [⟨.eq, .suc (.var 0), .largo (.var 1)⟩]))) := rfl

/-- Con entradas basura el programa no se rompe: la recursión sobre un «testigo» que no lo es entrega la hoja. -/
example : (Prog.pind (.var 0) (fun _ => 0) .id).correr 3 (fun _ => 5) [.cons .hoja .hoja] = (0, .hoja) := by
  decide

end Extraccion
end Sagitta.Map
