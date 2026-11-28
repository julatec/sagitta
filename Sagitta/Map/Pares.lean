import Sagitta.Map.Comparar

/-!
# Los pares: la última propiedad de `CierrePolinomial`

Si `f` y `g` son de tiempo polinomial, `fun a => (f a, g a)` también. Se arma por composición de tres piezas:

`(f a, g a) = primero f ∘ intercambiar ∘ primero g ∘ duplicar`

* **duplicar**: `a ↦ (a, a)`. Sobre bits: `u ↦ delimita u ++ u`.
* **intercambiar**: `(a, b) ↦ (b, a)`. Sobre bits: `delimita u ++ w ↦ delimita w ++ u`.
* **primero f**: `(a, c) ↦ (f a, c)`. Desarma el bloque, corre la máquina de `f` sin tocar el resto, y vuelve a
  armar el bloque (`Primero.lean`).

Este archivo tiene las dos primeras, que son máquinas concretas sobre bits, y lo que comparten: escribir un bloque
autodelimitado a partir de una pila que tiene los bits al revés.
-/

open Turing Turing.TM2 Turing.TM2.Stmt

namespace Sagitta.Map
namespace Pares

open Componer (Llega)

/-! ## Escribir un bloque -/

/-- Cada bit `b` pasa a `[true, b]`: un bloque sin su cierre. -/
def pares : List Bool → List Bool
  | [] => []
  | b :: l => true :: b :: pares l

/-- Lo que queda en una pila después de sacar los bits de `t` uno por uno y poner cada uno, con su marca, sobre
`o`. -/
def envolver : List Bool → List Bool → List Bool
  | [], o => o
  | b :: t, o => envolver t (true :: b :: o)

theorem delimita_eq : ∀ u : List Bool, CodBits.delimita u = pares u ++ [false]
  | [] => rfl
  | b :: u => by simp [CodBits.delimita, pares, delimita_eq u]

theorem envolver_append : ∀ (s t o : List Bool), envolver (s ++ t) o = envolver t (envolver s o)
  | [], t, o => rfl
  | b :: s, t, o => by simp [envolver, envolver_append s t]

theorem envolver_reverse : ∀ (u o : List Bool), envolver u.reverse o = pares u ++ o
  | [], o => rfl
  | b :: u, o => by simp [envolver_append, envolver, pares, envolver_reverse u]

/-- Sacar los bits al revés y envolverlos sobre un cierre da el bloque. -/
theorem envolver_bloque (u r : List Bool) : envolver u.reverse (false :: r) = CodBits.delimita u ++ r := by
  rw [envolver_reverse, delimita_eq]
  simp

open Comparar (pilas upd0 upd1 upd2 upd3)

/-- La configuración de las dos máquinas de este archivo. -/
abbrev CP : Type := TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 4) (Option Bool)

/-! ## Duplicar

Cuatro pilas: entrada (0), dos auxiliares (1 y 2) y salida (3).

* **A**: pasa la entrada a la auxiliar 1; queda al revés.
* **B**: pasa la auxiliar 1 a la salida y a la auxiliar 2 a la vez; las dos quedan derechas.
* **C**: pasa la auxiliar 2 a la 1, otra vez al revés, y escribe el cierre del bloque en la salida.
* **D**: saca de la auxiliar 1 y escribe cada bit con su marca.
-/

/-- La máquina que duplica. -/
@[reducible] def maquinaDup : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool
  initialState := none
  m := fun
    | 0 => pop 0 (fun _ o => o)
        (branch (fun v => v.isSome) (push 1 (fun v => v.getD false) (goto fun _ => 0)) (goto fun _ => 1))
    | 1 => pop 1 (fun _ o => o)
        (branch (fun v => v.isSome)
          (push 3 (fun v => v.getD false) (push 2 (fun v => v.getD false) (goto fun _ => 1)))
          (goto fun _ => 2))
    | 2 => pop 2 (fun _ o => o)
        (branch (fun v => v.isSome) (push 1 (fun v => v.getD false) (goto fun _ => 2))
          (push 3 (fun _ => false) (goto fun _ => 3)))
    | 3 => pop 1 (fun _ o => o)
        (branch (fun v => v.isSome)
          (push 3 (fun v => v.getD false) (push 3 (fun _ => true) (goto fun _ => 3))) halt)

namespace Dup

theorem pasoA_bit (v : Option Bool) (c : Bool) (i t x o : List Bool) :
    TM2.step maquinaDup.m (⟨some 0, v, pilas (c :: i) t x o⟩ : CP) =
      some ⟨some 0, some c, pilas i (c :: t) x o⟩ := by
  show some (stepAux (maquinaDup.m 0) v (pilas (c :: i) t x o)) = _
  simp [maquinaDup, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : Option Bool) (t x o : List Bool) :
    TM2.step maquinaDup.m (⟨some 0, v, pilas [] t x o⟩ : CP) = some ⟨some 1, none, pilas [] t x o⟩ := by
  show some (stepAux (maquinaDup.m 0) v (pilas [] t x o)) = _
  simp [maquinaDup, stepAux, pilas, upd0]

theorem bucleA (x o : List Bool) : ∀ (i t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaDup.m) (i.length + 1)
      (⟨some 0, v, pilas i t x o⟩ : CP) ⟨some 1, none, pilas [] (i.reverse ++ t) x o⟩
  | [], t, v => Llega.uno (pasoA_fin v t x o)
  | c :: i, t, v => by
    have := (Llega.uno (pasoA_bit v c i t x o)).trans (bucleA x o i (c :: t) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem pasoB_bit (v : Option Bool) (c : Bool) (t x o : List Bool) :
    TM2.step maquinaDup.m (⟨some 1, v, pilas [] (c :: t) x o⟩ : CP) =
      some ⟨some 1, some c, pilas [] t (c :: x) (c :: o)⟩ := by
  show some (stepAux (maquinaDup.m 1) v (pilas [] (c :: t) x o)) = _
  simp [maquinaDup, stepAux, pilas, upd1, upd2, upd3]

theorem pasoB_fin (v : Option Bool) (x o : List Bool) :
    TM2.step maquinaDup.m (⟨some 1, v, pilas [] [] x o⟩ : CP) = some ⟨some 2, none, pilas [] [] x o⟩ := by
  show some (stepAux (maquinaDup.m 1) v (pilas [] [] x o)) = _
  simp [maquinaDup, stepAux, pilas, upd1]

theorem bucleB : ∀ (t x o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaDup.m) (t.length + 1)
      (⟨some 1, v, pilas [] t x o⟩ : CP) ⟨some 2, none, pilas [] [] (t.reverse ++ x) (t.reverse ++ o)⟩
  | [], x, o, v => Llega.uno (pasoB_fin v x o)
  | c :: t, x, o, v => by
    have := (Llega.uno (pasoB_bit v c t x o)).trans (bucleB t (c :: x) (c :: o) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem pasoC_bit (v : Option Bool) (c : Bool) (t x o : List Bool) :
    TM2.step maquinaDup.m (⟨some 2, v, pilas [] t (c :: x) o⟩ : CP) =
      some ⟨some 2, some c, pilas [] (c :: t) x o⟩ := by
  show some (stepAux (maquinaDup.m 2) v (pilas [] t (c :: x) o)) = _
  simp [maquinaDup, stepAux, pilas, upd1, upd2]

theorem pasoC_fin (v : Option Bool) (t o : List Bool) :
    TM2.step maquinaDup.m (⟨some 2, v, pilas [] t [] o⟩ : CP) =
      some ⟨some 3, none, pilas [] t [] (false :: o)⟩ := by
  show some (stepAux (maquinaDup.m 2) v (pilas [] t [] o)) = _
  simp [maquinaDup, stepAux, pilas, upd2, upd3]

theorem bucleC (o : List Bool) : ∀ (x t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaDup.m) (x.length + 1)
      (⟨some 2, v, pilas [] t x o⟩ : CP) ⟨some 3, none, pilas [] (x.reverse ++ t) [] (false :: o)⟩
  | [], t, v => Llega.uno (pasoC_fin v t o)
  | c :: x, t, v => by
    have := (Llega.uno (pasoC_bit v c t x o)).trans (bucleC o x (c :: t) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem pasoD_bit (v : Option Bool) (c : Bool) (t o : List Bool) :
    TM2.step maquinaDup.m (⟨some 3, v, pilas [] (c :: t) [] o⟩ : CP) =
      some ⟨some 3, some c, pilas [] t [] (true :: c :: o)⟩ := by
  show some (stepAux (maquinaDup.m 3) v (pilas [] (c :: t) [] o)) = _
  simp [maquinaDup, stepAux, pilas, upd1, upd3]

theorem pasoD_fin (v : Option Bool) (o : List Bool) :
    TM2.step maquinaDup.m (⟨some 3, v, pilas [] [] [] o⟩ : CP) = some ⟨none, none, pilas [] [] [] o⟩ := by
  show some (stepAux (maquinaDup.m 3) v (pilas [] [] [] o)) = _
  simp [maquinaDup, stepAux, pilas, upd1]

theorem bucleD : ∀ (t o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaDup.m) (t.length + 1)
      (⟨some 3, v, pilas [] t [] o⟩ : CP) ⟨none, none, pilas [] [] [] (envolver t o)⟩
  | [], o, v => Llega.uno (pasoD_fin v o)
  | c :: t, o, v => (Llega.uno (pasoD_bit v c t o)).trans (bucleD t (true :: c :: o) (some c))

theorem init (inp : List Bool) : (initList maquinaDup inp : CP) = ⟨some 0, none, pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaDup inp).stk⟩ : CP) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) : (haltList maquinaDup out : CP) = ⟨none, none, pilas [] [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaDup out).stk⟩ : CP) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

/-- **La corrida**: de `u` a `delimita u ++ u`, en `4·(|u| + 1)` pasos. -/
theorem corrida (u : List Bool) :
    Llega (TM2.step maquinaDup.m) ((u.length + 1) + ((u.length + 1) + ((u.length + 1) + (u.length + 1))))
      (initList maquinaDup u : CP) (haltList maquinaDup (CodBits.delimita u ++ u)) := by
  have a := bucleA [] [] u [] none
  have b := bucleB (u.reverse ++ []) [] [] none
  have c := bucleC ((u.reverse ++ []).reverse ++ []) ((u.reverse ++ []).reverse ++ []) [] none
  have d := bucleD (((u.reverse ++ []).reverse ++ []).reverse ++ []) (false :: ((u.reverse ++ []).reverse ++ [])) none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at a b c d
  rw [envolver_bloque] at d
  rw [init, halt]
  exact ((a.trans b).trans c).trans d

end Dup

open Polynomial in
/-- Duplicar se calcula en tiempo polinomial. -/
noncomputable def dupComputable {α : Type} [CodBits α] :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := α)).encode
      (CodBits.toEncoding (α := α × α)).encode (fun a : α => (a, a)) where
  tm := maquinaDup
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * X + 4
  outputsFun a := by
    have run := Dup.corrida (CodBits.cod a)
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := α)).encode a) = CodBits.cod a := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := α × α)).encode (a, a)) =
        CodBits.delimita (CodBits.cod a) ++ CodBits.cod a := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := α)).encode a).length = (CodBits.cod a).length := rfl
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_mul, eval_X, eval_ofNat]; omega⟩

theorem esPolinomial_dup {α : Type} [CodBits α] : EsPolinomial (fun a : α => (a, a)) := ⟨dupComputable⟩

/-! ## Intercambiar

De `delimita u ++ w` a `delimita w ++ u`. Usa la entrada (0), una auxiliar (1) y la salida (3).

* **A**: lee el bloque y pasa `u` a la auxiliar; queda al revés.
* **B**: pasa la auxiliar a la salida; `u` queda derecho.
* **C**: pasa lo que queda de la entrada, `w`, a la auxiliar, al revés, y escribe el cierre del bloque.
* **D**: saca de la auxiliar y escribe cada bit con su marca.
-/

/-- La máquina que intercambia. -/
@[reducible] def maquinaSwap : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool
  initialState := none
  m := fun
    | 0 => pop 0 (fun _ o => o)
        (branch (fun v => v == some true)
          (pop 0 (fun _ o => o) (push 1 (fun v => v.getD false) (goto fun _ => 0)))
          (goto fun _ => 1))
    | 1 => pop 1 (fun _ o => o)
        (branch (fun v => v.isSome) (push 3 (fun v => v.getD false) (goto fun _ => 1)) (goto fun _ => 2))
    | 2 => pop 0 (fun _ o => o)
        (branch (fun v => v.isSome) (push 1 (fun v => v.getD false) (goto fun _ => 2))
          (push 3 (fun _ => false) (goto fun _ => 3)))
    | 3 => pop 1 (fun _ o => o)
        (branch (fun v => v.isSome)
          (push 3 (fun v => v.getD false) (push 3 (fun _ => true) (goto fun _ => 3))) halt)

namespace Swap

theorem pasoA_bit (v : Option Bool) (b : Bool) (r t x o : List Bool) :
    TM2.step maquinaSwap.m (⟨some 0, v, pilas (true :: b :: r) t x o⟩ : CP) =
      some ⟨some 0, some b, pilas r (b :: t) x o⟩ := by
  show some (stepAux (maquinaSwap.m 0) v (pilas (true :: b :: r) t x o)) = _
  simp [maquinaSwap, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : Option Bool) (r t x o : List Bool) :
    TM2.step maquinaSwap.m (⟨some 0, v, pilas (false :: r) t x o⟩ : CP) =
      some ⟨some 1, some false, pilas r t x o⟩ := by
  show some (stepAux (maquinaSwap.m 0) v (pilas (false :: r) t x o)) = _
  simp [maquinaSwap, stepAux, pilas, upd0]

theorem bucleA (r x o : List Bool) : ∀ (u t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaSwap.m) (u.length + 1)
      (⟨some 0, v, pilas (CodBits.delimita u ++ r) t x o⟩ : CP)
      ⟨some 1, some false, pilas r (u.reverse ++ t) x o⟩
  | [], t, v => Llega.uno (pasoA_fin v r t x o)
  | b :: u, t, v => by
    have h1 := Llega.uno (pasoA_bit v b (CodBits.delimita u ++ r) t x o)
    have := h1.trans (bucleA r x o u (b :: t) (some b))
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

theorem pasoB_bit (v : Option Bool) (c : Bool) (i t x o : List Bool) :
    TM2.step maquinaSwap.m (⟨some 1, v, pilas i (c :: t) x o⟩ : CP) =
      some ⟨some 1, some c, pilas i t x (c :: o)⟩ := by
  show some (stepAux (maquinaSwap.m 1) v (pilas i (c :: t) x o)) = _
  simp [maquinaSwap, stepAux, pilas, upd1, upd3]

theorem pasoB_fin (v : Option Bool) (i x o : List Bool) :
    TM2.step maquinaSwap.m (⟨some 1, v, pilas i [] x o⟩ : CP) = some ⟨some 2, none, pilas i [] x o⟩ := by
  show some (stepAux (maquinaSwap.m 1) v (pilas i [] x o)) = _
  simp [maquinaSwap, stepAux, pilas, upd1]

theorem bucleB (i x : List Bool) : ∀ (t o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaSwap.m) (t.length + 1)
      (⟨some 1, v, pilas i t x o⟩ : CP) ⟨some 2, none, pilas i [] x (t.reverse ++ o)⟩
  | [], o, v => Llega.uno (pasoB_fin v i x o)
  | c :: t, o, v => by
    have := (Llega.uno (pasoB_bit v c i t x o)).trans (bucleB i x t (c :: o) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem pasoC_bit (v : Option Bool) (c : Bool) (i t x o : List Bool) :
    TM2.step maquinaSwap.m (⟨some 2, v, pilas (c :: i) t x o⟩ : CP) =
      some ⟨some 2, some c, pilas i (c :: t) x o⟩ := by
  show some (stepAux (maquinaSwap.m 2) v (pilas (c :: i) t x o)) = _
  simp [maquinaSwap, stepAux, pilas, upd0, upd1]

theorem pasoC_fin (v : Option Bool) (t x o : List Bool) :
    TM2.step maquinaSwap.m (⟨some 2, v, pilas [] t x o⟩ : CP) =
      some ⟨some 3, none, pilas [] t x (false :: o)⟩ := by
  show some (stepAux (maquinaSwap.m 2) v (pilas [] t x o)) = _
  simp [maquinaSwap, stepAux, pilas, upd0, upd3]

theorem bucleC (x o : List Bool) : ∀ (i t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaSwap.m) (i.length + 1)
      (⟨some 2, v, pilas i t x o⟩ : CP) ⟨some 3, none, pilas [] (i.reverse ++ t) x (false :: o)⟩
  | [], t, v => Llega.uno (pasoC_fin v t x o)
  | c :: i, t, v => by
    have := (Llega.uno (pasoC_bit v c i t x o)).trans (bucleC x o i (c :: t) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem pasoD_bit (v : Option Bool) (c : Bool) (t o : List Bool) :
    TM2.step maquinaSwap.m (⟨some 3, v, pilas [] (c :: t) [] o⟩ : CP) =
      some ⟨some 3, some c, pilas [] t [] (true :: c :: o)⟩ := by
  show some (stepAux (maquinaSwap.m 3) v (pilas [] (c :: t) [] o)) = _
  simp [maquinaSwap, stepAux, pilas, upd1, upd3]

theorem pasoD_fin (v : Option Bool) (o : List Bool) :
    TM2.step maquinaSwap.m (⟨some 3, v, pilas [] [] [] o⟩ : CP) = some ⟨none, none, pilas [] [] [] o⟩ := by
  show some (stepAux (maquinaSwap.m 3) v (pilas [] [] [] o)) = _
  simp [maquinaSwap, stepAux, pilas, upd1]

theorem bucleD : ∀ (t o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaSwap.m) (t.length + 1)
      (⟨some 3, v, pilas [] t [] o⟩ : CP) ⟨none, none, pilas [] [] [] (envolver t o)⟩
  | [], o, v => Llega.uno (pasoD_fin v o)
  | c :: t, o, v => (Llega.uno (pasoD_bit v c t o)).trans (bucleD t (true :: c :: o) (some c))

theorem init (inp : List Bool) : (initList maquinaSwap inp : CP) = ⟨some 0, none, pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaSwap inp).stk⟩ : CP) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) : (haltList maquinaSwap out : CP) = ⟨none, none, pilas [] [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaSwap out).stk⟩ : CP) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

/-- **La corrida**: de `delimita u ++ w` a `delimita w ++ u`. -/
theorem corrida (u w : List Bool) :
    Llega (TM2.step maquinaSwap.m) ((w.length + 1) + ((w.length + 1) + ((u.length + 1) + (u.length + 1))))
      (initList maquinaSwap (CodBits.delimita u ++ w) : CP) (haltList maquinaSwap (CodBits.delimita w ++ u)) := by
  have a := bucleA w [] [] u [] none
  have b := bucleB w [] (u.reverse ++ []) [] (some false)
  have c := bucleC [] ((u.reverse ++ []).reverse ++ []) w [] none
  have d := bucleD (w.reverse ++ []) (false :: ((u.reverse ++ []).reverse ++ [])) none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at a b c d
  rw [envolver_bloque] at d
  rw [init, halt]
  exact ((a.trans b).trans c).trans d

end Swap

open Polynomial in
/-- Intercambiar se calcula en tiempo polinomial. -/
noncomputable def swapComputable {α β : Type} [CodBits α] [CodBits β] :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := α × β)).encode
      (CodBits.toEncoding (α := β × α)).encode (fun q : α × β => (q.2, q.1)) where
  tm := maquinaSwap
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * X + 4
  outputsFun q := by
    have run := Swap.corrida (CodBits.cod q.1) (CodBits.cod q.2)
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := α × β)).encode q) =
        CodBits.delimita (CodBits.cod q.1) ++ CodBits.cod q.2 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := β × α)).encode (q.2, q.1)) =
        CodBits.delimita (CodBits.cod q.2) ++ CodBits.cod q.1 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := α × β)).encode q).length =
        2 * (CodBits.cod q.1).length + 1 + (CodBits.cod q.2).length := by
      show (CodBits.delimita (CodBits.cod q.1) ++ CodBits.cod q.2).length = _
      rw [List.length_append, Basicas.delimita_length]
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_mul, eval_X, eval_ofNat]; omega⟩

theorem esPolinomial_swap {α β : Type} [CodBits α] [CodBits β] :
    EsPolinomial (fun q : α × β => (q.2, q.1)) := ⟨swapComputable⟩

end Pares
end Sagitta.Map
