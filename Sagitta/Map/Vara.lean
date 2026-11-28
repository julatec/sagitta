import Sagitta.Map.ExhaustivoTiempo

/-!
# La vara: una cadena de largo `p(|x|)`

`ExhaustivoTiempo.lean` prueba que el descenso exhaustivo es polinomial dada una **vara**: una función polinomial
`tope` con `|tope x| = p(|x|)`. Aquí se construye para todo polinomio `p`, por inducción:

* **constante `a`**: una cadena de `a` símbolos. Sale de aplicar `a` veces la máquina que pone un bit.
* **suma `p + q`**: concatenar las dos varas.
* **producto `p · X`**: por cada símbolo de la vara de `p`, copiar la entrada.

Con eso, la reducción de NP al problema del algoritmo estándar queda sin condiciones (`np_al_algoritmo_estandar`).
-/

open Computability Turing Turing.TM2 Turing.TM2.Stmt

namespace Sagitta.Map
namespace Vara

open Componer (Llega)
open Comparar (pilas upd0 upd1 upd2 upd3)
open ExhaustivoTiempo (CE)

/-! ## 1. Poner un bit -/

/-- La máquina que pone un `true` delante de su entrada. Tarda un paso. -/
@[reducible] def maquinaPoner : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := push () (fun _ => true) halt

/-- Poner un bit delante se calcula en tiempo polinomial (en un paso). -/
noncomputable def ponerComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool)).encode
      (CodBits.toEncoding (α := List Bool)).encode (fun s : List Bool => true :: s) where
  tm := maquinaPoner
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun s := by
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := List Bool)).encode s) = s := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool)).encode (true :: s)) = true :: s := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    rw [hin, hout]
    refine ⟨⟨1, ?_⟩, by simp⟩
    show some (stepAux (maquinaPoner.m ()) () (initList maquinaPoner s).stk) = some (haltList maquinaPoner _)
    congr 1

theorem esPolinomial_poner : EsPolinomial (fun s : List Bool => true :: s) := ⟨ponerComputable⟩

/-! ## 2. Concatenar

De `delimita u ++ w` a `u ++ w`. La entrada y la salida son la misma pila (0).

* **A**: lee el bloque y pasa `u` a la auxiliar; queda al revés. En la pila 0 queda `w`.
* **B**: devuelve la auxiliar a la pila 0. Al sacar `u` al revés y ponerla encima de `w`, queda `u ++ w`.
-/

/-- La máquina que concatena. -/
@[reducible] def maquinaConcat : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 0
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
    | _ => pop 1 (fun _ o => o)
        (branch (fun v => v.isSome) (push 0 (fun v => v.getD false) (goto fun _ => 1)) halt)

namespace Concat

theorem pasoA_bit (v : Option Bool) (b : Bool) (r t : List Bool) :
    TM2.step maquinaConcat.m (⟨some 0, v, pilas (true :: b :: r) t [] []⟩ : CE) =
      some ⟨some 0, some b, pilas r (b :: t) [] []⟩ := by
  show some (stepAux (maquinaConcat.m 0) v (pilas (true :: b :: r) t [] [])) = _
  simp [maquinaConcat, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : Option Bool) (r t : List Bool) :
    TM2.step maquinaConcat.m (⟨some 0, v, pilas (false :: r) t [] []⟩ : CE) =
      some ⟨some 1, some false, pilas r t [] []⟩ := by
  show some (stepAux (maquinaConcat.m 0) v (pilas (false :: r) t [] [])) = _
  simp [maquinaConcat, stepAux, pilas, upd0]

theorem bucleA (r : List Bool) : ∀ (u t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaConcat.m) (u.length + 1)
      (⟨some 0, v, pilas (CodBits.delimita u ++ r) t [] []⟩ : CE)
      ⟨some 1, some false, pilas r (u.reverse ++ t) [] []⟩
  | [], t, v => Llega.uno (pasoA_fin v r t)
  | b :: u, t, v => by
    have h1 := Llega.uno (pasoA_bit v b (CodBits.delimita u ++ r) t)
    have := h1.trans (bucleA r u (b :: t) (some b))
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

theorem pasoB_bit (v : Option Bool) (c : Bool) (i t : List Bool) :
    TM2.step maquinaConcat.m (⟨some 1, v, pilas i (c :: t) [] []⟩ : CE) =
      some ⟨some 1, some c, pilas (c :: i) t [] []⟩ := by
  show some (stepAux (maquinaConcat.m 1) v (pilas i (c :: t) [] [])) = _
  simp [maquinaConcat, stepAux, pilas, upd0, upd1]

theorem pasoB_fin (v : Option Bool) (i : List Bool) :
    TM2.step maquinaConcat.m (⟨some 1, v, pilas i [] [] []⟩ : CE) = some ⟨none, none, pilas i [] [] []⟩ := by
  show some (stepAux (maquinaConcat.m 1) v (pilas i [] [] [])) = _
  simp [maquinaConcat, stepAux, pilas, upd1]

theorem bucleB : ∀ (t i : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaConcat.m) (t.length + 1)
      (⟨some 1, v, pilas i t [] []⟩ : CE) ⟨none, none, pilas (t.reverse ++ i) [] [] []⟩
  | [], i, v => Llega.uno (pasoB_fin v i)
  | c :: t, i, v => by
    have := (Llega.uno (pasoB_bit v c i t)).trans (bucleB t (c :: i) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem init (inp : List Bool) : (initList maquinaConcat inp : CE) = ⟨some 0, none, pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaConcat inp).stk⟩ : CE) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) : (haltList maquinaConcat out : CE) = ⟨none, none, pilas out [] [] []⟩ := by
  show (⟨_, _, (haltList maquinaConcat out).stk⟩ : CE) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

/-- **La corrida**: de `delimita u ++ w` a `u ++ w`. -/
theorem corrida (u w : List Bool) :
    Llega (TM2.step maquinaConcat.m) ((u.length + 1) + (u.length + 1))
      (initList maquinaConcat (CodBits.delimita u ++ w) : CE) (haltList maquinaConcat (u ++ w)) := by
  have a := bucleA w u [] none
  have b := bucleB (u.reverse ++ []) w (some false)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at a b
  rw [init, halt]
  exact a.trans b

end Concat

open Polynomial in
/-- Concatenar dos cadenas se calcula en tiempo polinomial. -/
noncomputable def concatComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool × List Bool)).encode
      (CodBits.toEncoding (α := List Bool)).encode (fun q : List Bool × List Bool => q.1 ++ q.2) where
  tm := maquinaConcat
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := X + 1
  outputsFun q := by
    have run := Concat.corrida q.1 q.2
    have hin : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool × List Bool)).encode q) = CodBits.delimita q.1 ++ q.2 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool)).encode (q.1 ++ q.2)) = q.1 ++ q.2 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := List Bool × List Bool)).encode q).length =
        2 * q.1.length + 1 + q.2.length := by
      show (CodBits.delimita q.1 ++ q.2).length = _
      rw [List.length_append, Basicas.delimita_length]
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_X, eval_one]; omega⟩

theorem esPolinomial_concat : EsPolinomial (fun q : List Bool × List Bool => q.1 ++ q.2) :=
  ⟨concatComputable⟩

/-! ## 3. Multiplicar largos

De `delimita u ++ w` a una cadena de `|u| · |w|` símbolos. Cuatro pilas: entrada (0), contador (1), reserva (2) y
salida (3).

* **A**: lee el bloque y pasa `u` al contador. En la entrada queda `w`.
* **vuelta** (una por cada símbolo del contador):
  * saca un símbolo del contador;
  * **copia**: pasa `w` de la entrada a la reserva, y por cada símbolo pone uno en la salida;
  * **restaura**: devuelve la reserva a la entrada, para la vuelta siguiente.
* cuando el contador se acaba, **vacía** la entrada.
-/

/-- La configuración de la máquina que multiplica. -/
abbrev CMu : Type := TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 5) (Option Bool)

/-- La máquina que multiplica largos. -/
@[reducible] def maquinaMult : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 5
  main := 0
  σ := Option Bool
  initialState := none
  m := fun
    | 0 => pop 0 (fun _ o => o)
        (branch (fun v => v == some true)
          (pop 0 (fun _ o => o) (push 1 (fun v => v.getD false) (goto fun _ => 0)))
          (goto fun _ => 1))
    | 1 => pop 1 (fun _ o => o) (branch (fun v => v.isSome) (goto fun _ => 2) (goto fun _ => 4))
    | 2 => pop 0 (fun _ o => o)
        (branch (fun v => v.isSome)
          (push 2 (fun v => v.getD false) (push 3 (fun _ => true) (goto fun _ => 2)))
          (goto fun _ => 3))
    | 3 => pop 2 (fun _ o => o)
        (branch (fun v => v.isSome) (push 0 (fun v => v.getD false) (goto fun _ => 3)) (goto fun _ => 1))
    | _ => pop 0 (fun _ o => o) (branch (fun v => v.isSome) (goto fun _ => 4) halt)

namespace Mult

theorem pasoA_bit (v : Option Bool) (b : Bool) (r t : List Bool) :
    TM2.step maquinaMult.m (⟨some 0, v, pilas (true :: b :: r) t [] []⟩ : CMu) =
      some ⟨some 0, some b, pilas r (b :: t) [] []⟩ := by
  show some (stepAux (maquinaMult.m 0) v (pilas (true :: b :: r) t [] [])) = _
  simp [maquinaMult, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : Option Bool) (r t : List Bool) :
    TM2.step maquinaMult.m (⟨some 0, v, pilas (false :: r) t [] []⟩ : CMu) =
      some ⟨some 1, some false, pilas r t [] []⟩ := by
  show some (stepAux (maquinaMult.m 0) v (pilas (false :: r) t [] [])) = _
  simp [maquinaMult, stepAux, pilas, upd0]

theorem bucleA (r : List Bool) : ∀ (u t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaMult.m) (u.length + 1)
      (⟨some 0, v, pilas (CodBits.delimita u ++ r) t [] []⟩ : CMu)
      ⟨some 1, some false, pilas r (u.reverse ++ t) [] []⟩
  | [], t, v => Llega.uno (pasoA_fin v r t)
  | b :: u, t, v => by
    have h1 := Llega.uno (pasoA_bit v b (CodBits.delimita u ++ r) t)
    have := h1.trans (bucleA r u (b :: t) (some b))
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

/-! ### Copiar: de la entrada a la reserva, con un símbolo en la salida por cada uno -/

theorem pasoCopia_bit (v : Option Bool) (c : Bool) (i t x o : List Bool) :
    TM2.step maquinaMult.m (⟨some 2, v, pilas (c :: i) t x o⟩ : CMu) =
      some ⟨some 2, some c, pilas i t (c :: x) (true :: o)⟩ := by
  show some (stepAux (maquinaMult.m 2) v (pilas (c :: i) t x o)) = _
  simp [maquinaMult, stepAux, pilas, upd0, upd2, upd3]

theorem pasoCopia_fin (v : Option Bool) (t x o : List Bool) :
    TM2.step maquinaMult.m (⟨some 2, v, pilas [] t x o⟩ : CMu) = some ⟨some 3, none, pilas [] t x o⟩ := by
  show some (stepAux (maquinaMult.m 2) v (pilas [] t x o)) = _
  simp [maquinaMult, stepAux, pilas, upd0]

theorem rep_cons (n : ℕ) (l : List Bool) :
    List.replicate n true ++ true :: l = List.replicate (n + 1) true ++ l := by
  rw [List.replicate_succ']
  simp

theorem copia (t : List Bool) : ∀ (i x o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaMult.m) (i.length + 1)
      (⟨some 2, v, pilas i t x o⟩ : CMu)
      ⟨some 3, none, pilas [] t (i.reverse ++ x) (List.replicate i.length true ++ o)⟩
  | [], x, o, v => by
    have := Llega.uno (pasoCopia_fin v t x o)
    simpa using this
  | c :: i, x, o, v => by
    have := (Llega.uno (pasoCopia_bit v c i t x o)).trans (copia t i (c :: x) (true :: o) (some c))
    rw [rep_cons] at this
    simpa [List.reverse_cons, List.append_assoc] using this

/-! ### Restaurar: de la reserva a la entrada -/

theorem pasoRest_bit (v : Option Bool) (c : Bool) (i t x o : List Bool) :
    TM2.step maquinaMult.m (⟨some 3, v, pilas i t (c :: x) o⟩ : CMu) =
      some ⟨some 3, some c, pilas (c :: i) t x o⟩ := by
  show some (stepAux (maquinaMult.m 3) v (pilas i t (c :: x) o)) = _
  simp [maquinaMult, stepAux, pilas, upd0, upd2]

theorem pasoRest_fin (v : Option Bool) (i t o : List Bool) :
    TM2.step maquinaMult.m (⟨some 3, v, pilas i t [] o⟩ : CMu) = some ⟨some 1, none, pilas i t [] o⟩ := by
  show some (stepAux (maquinaMult.m 3) v (pilas i t [] o)) = _
  simp [maquinaMult, stepAux, pilas, upd2]

theorem restaura (t o : List Bool) : ∀ (x i : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaMult.m) (x.length + 1)
      (⟨some 3, v, pilas i t x o⟩ : CMu) ⟨some 1, none, pilas (x.reverse ++ i) t [] o⟩
  | [], i, v => Llega.uno (pasoRest_fin v i t o)
  | c :: x, i, v => by
    have := (Llega.uno (pasoRest_bit v c i t x o)).trans (restaura t o x (c :: i) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

/-! ### Una vuelta, y todas -/

theorem pasoVuelta_bit (v : Option Bool) (c : Bool) (i t o : List Bool) :
    TM2.step maquinaMult.m (⟨some 1, v, pilas i (c :: t) [] o⟩ : CMu) =
      some ⟨some 2, some c, pilas i t [] o⟩ := by
  show some (stepAux (maquinaMult.m 1) v (pilas i (c :: t) [] o)) = _
  simp [maquinaMult, stepAux, pilas, upd1]

theorem pasoVuelta_fin (v : Option Bool) (i o : List Bool) :
    TM2.step maquinaMult.m (⟨some 1, v, pilas i [] [] o⟩ : CMu) = some ⟨some 4, none, pilas i [] [] o⟩ := by
  show some (stepAux (maquinaMult.m 1) v (pilas i [] [] o)) = _
  simp [maquinaMult, stepAux, pilas, upd1]

/-- **Una vuelta**: gasta un símbolo del contador, pone `|w|` símbolos en la salida y deja `w` como estaba. -/
theorem vuelta (v : Option Bool) (c : Bool) (w t o : List Bool) :
    Llega (TM2.step maquinaMult.m) ((w.length + 1) + ((w.length + 1) + 1))
      (⟨some 1, v, pilas w (c :: t) [] o⟩ : CMu)
      ⟨some 1, none, pilas w t [] (List.replicate w.length true ++ o)⟩ := by
  have h1 := Llega.uno (pasoVuelta_bit v c w t o)
  have h2 := copia t w [] o (some c)
  have h3 := restaura t (List.replicate w.length true ++ o) (w.reverse ++ []) [] none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h2 h3
  exact (h1.trans h2).trans h3

/-- Cuántos pasos tardan todas las vueltas. -/
def pasosV (w : List Bool) : List Bool → ℕ
  | [] => 1
  | _ :: t => pasosV w t + ((w.length + 1) + ((w.length + 1) + 1))

theorem pasosV_eq (w : List Bool) : ∀ t : List Bool, pasosV w t = t.length * (2 * w.length + 3) + 1
  | [] => by simp [pasosV]
  | _ :: t => by
    have := pasosV_eq w t
    simp only [pasosV, List.length_cons, this]
    ring

/-- **Todas las vueltas**: `|t| · |w|` símbolos en la salida. -/
theorem vueltas (w : List Bool) : ∀ (t o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaMult.m) (pasosV w t)
      (⟨some 1, v, pilas w t [] o⟩ : CMu)
      ⟨some 4, none, pilas w [] [] (List.replicate (t.length * w.length) true ++ o)⟩
  | [], o, v => by
    have := Llega.uno (pasoVuelta_fin v w o)
    simpa [pasosV] using this
  | c :: t, o, v => by
    have := (vuelta v c w t o).trans (vueltas w t (List.replicate w.length true ++ o) none)
    have hrep : List.replicate (t.length * w.length) true ++ (List.replicate w.length true ++ o) =
        List.replicate ((t.length + 1) * w.length) true ++ o := by
      rw [← List.append_assoc, ← List.replicate_add, Nat.succ_mul]
    rw [hrep] at this
    exact this

/-! ### Vaciar la entrada -/

theorem pasoVacia_bit (v : Option Bool) (c : Bool) (i o : List Bool) :
    TM2.step maquinaMult.m (⟨some 4, v, pilas (c :: i) [] [] o⟩ : CMu) =
      some ⟨some 4, some c, pilas i [] [] o⟩ := by
  show some (stepAux (maquinaMult.m 4) v (pilas (c :: i) [] [] o)) = _
  simp [maquinaMult, stepAux, pilas, upd0]

theorem pasoVacia_fin (v : Option Bool) (o : List Bool) :
    TM2.step maquinaMult.m (⟨some 4, v, pilas [] [] [] o⟩ : CMu) = some ⟨none, none, pilas [] [] [] o⟩ := by
  show some (stepAux (maquinaMult.m 4) v (pilas [] [] [] o)) = _
  simp [maquinaMult, stepAux, pilas, upd0]

theorem vacia (o : List Bool) : ∀ (i : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaMult.m) (i.length + 1)
      (⟨some 4, v, pilas i [] [] o⟩ : CMu) ⟨none, none, pilas [] [] [] o⟩
  | [], v => Llega.uno (pasoVacia_fin v o)
  | c :: i, v => (Llega.uno (pasoVacia_bit v c i o)).trans (vacia o i (some c))

theorem init (inp : List Bool) : (initList maquinaMult inp : CMu) = ⟨some 0, none, pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaMult inp).stk⟩ : CMu) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) : (haltList maquinaMult out : CMu) = ⟨none, none, pilas [] [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaMult out).stk⟩ : CMu) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

/-- **La corrida**: de `delimita u ++ w` a `|u| · |w|` símbolos. -/
theorem corrida (u w : List Bool) :
    Llega (TM2.step maquinaMult.m) ((w.length + 1) + (pasosV w u.reverse + (u.length + 1)))
      (initList maquinaMult (CodBits.delimita u ++ w) : CMu)
      (haltList maquinaMult (List.replicate (u.length * w.length) true)) := by
  have a := bucleA w u [] none
  have b := vueltas w (u.reverse ++ []) [] (some false)
  have c := vacia (List.replicate ((u.reverse ++ []).length * w.length) true ++ []) w none
  simp only [List.append_nil, List.length_reverse] at a b c
  rw [init, halt]
  exact (a.trans b).trans c

end Mult

open Polynomial in
/-- Multiplicar los largos de dos cadenas se calcula en tiempo polinomial (cuadrático). -/
noncomputable def multComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool × List Bool)).encode
      (CodBits.toEncoding (α := List Bool)).encode
      (fun q : List Bool × List Bool => List.replicate (q.1.length * q.2.length) true) where
  tm := maquinaMult
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := X ^ 2 + 3 * X + 3
  outputsFun q := by
    have run := Mult.corrida q.1 q.2
    have hin : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool × List Bool)).encode q) = CodBits.delimita q.1 ++ q.2 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool)).encode (List.replicate (q.1.length * q.2.length) true)) =
        List.replicate (q.1.length * q.2.length) true := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := List Bool × List Bool)).encode q).length =
        2 * q.1.length + 1 + q.2.length := by
      show (CodBits.delimita q.1 ++ q.2).length = _
      rw [List.length_append, Basicas.delimita_length]
    have hV := Mult.pasosV_eq q.2 q.1.reverse
    rw [List.length_reverse] at hV
    rw [hin, hout]
    refine ⟨⟨_, run⟩, ?_⟩
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
    rw [hlen, hV]
    nlinarith [Nat.zero_le (q.1.length * q.2.length), Nat.zero_le q.1.length, Nat.zero_le q.2.length,
      Nat.zero_le (q.1.length * q.1.length), Nat.zero_le (q.2.length * q.2.length)]

theorem esPolinomial_mult :
    EsPolinomial (fun q : List Bool × List Bool => List.replicate (q.1.length * q.2.length) true) :=
  ⟨multComputable⟩

/-! ## 4. La vara, por inducción sobre el polinomio -/

/-- `p` tiene vara: una función polinomial cuyo resultado mide `p(|x|)`. -/
def TieneVara (p : Polynomial ℕ) : Prop :=
  ∃ tope : List Bool → List Bool, EsPolinomial tope ∧ ∀ x, (tope x).length = p.eval x.length

/-- Una constante: poner `a` veces un bit sobre la cadena vacía. -/
theorem vara_const : ∀ a : ℕ, TieneVara (Polynomial.C a)
  | 0 => ⟨fun _ => [], ExhaustivoTiempo.esPolinomial_vacia, fun x => by simp⟩
  | a + 1 => by
    obtain ⟨t, ht, hl⟩ := vara_const a
    refine ⟨fun x => true :: t x, Componer.esPolinomial_comp t _ ht esPolinomial_poner, fun x => ?_⟩
    have := hl x
    simp only [Polynomial.eval_C] at this ⊢
    simp [this]

/-- Una suma: concatenar las dos varas. -/
theorem vara_add {p q : Polynomial ℕ} (hp : TieneVara p) (hq : TieneVara q) : TieneVara (p + q) := by
  obtain ⟨t, ht, hl⟩ := hp
  obtain ⟨u, hu, hm⟩ := hq
  refine ⟨fun x => t x ++ u x,
    Componer.esPolinomial_comp (fun x => (t x, u x)) _ (Primero.esPolinomial_pares t u ht hu)
      esPolinomial_concat, fun x => ?_⟩
  simp [hl, hm]

/-- Un producto por `X`: por cada símbolo de la vara, copiar la entrada. -/
theorem vara_mulX {p : Polynomial ℕ} (hp : TieneVara p) : TieneVara (p * Polynomial.X) := by
  obtain ⟨t, ht, hl⟩ := hp
  refine ⟨fun x => List.replicate ((t x).length * x.length) true,
    Componer.esPolinomial_comp (fun x => (t x, x)) _
      (Primero.esPolinomial_pares t (id : List Bool → List Bool) ht esPolinomial_id) esPolinomial_mult,
    fun x => ?_⟩
  simp [hl]

/-- **Todo polinomio tiene vara.** -/
theorem tieneVara (p : Polynomial ℕ) : TieneVara p := by
  induction p using Polynomial.induction_on with
  | C a => exact vara_const a
  | add p q hp hq => exact vara_add hp hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc]
    exact vara_mulX h

/-! ## 5. La reducción de NP, sin condiciones -/

/-- **NP se reduce al problema del algoritmo estándar de un descenso polinomial.** Para todo `L` de NP hay un
verificador polinomial `V` y un descenso con solución inicial, vecino y costo polinomiales, tal que `x ∈ L` si y
solo si `V` acepta el destino de la ruta. Sin hipótesis. -/
theorem np_al_algoritmo_estandar {L : Problema} (hL : L ∈ NP) :
    ∃ (D : DescensoInstancia) (V : List Bool × List Bool → Bool),
      EsPolinomial V ∧ EsPolinomial D.inicial ∧ EsPolinomial D.vecino ∧ EsPolinomial D.costo ∧
        ∀ x, L x = true ↔ V (x, D.destino x) = true := by
  obtain ⟨p, V, hV, hiff⟩ := hL
  obtain ⟨tope, htope, hlargo⟩ := tieneVara p
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ExhaustivoTiempo.np_por_destino_polinomial hV htope hlargo hiff
  exact ⟨ExhaustivoTiempo.exhaustivoVara V tope, V, hV, h1, h2, h3, h4⟩

end Vara
end Sagitta.Map
