import Sagitta.Map.MaquinasBasicas
import Mathlib.Data.Num.Lemmas

/-!
# Comparar dos naturales en tiempo polinomial

La quinta propiedad de `CierrePolinomial`: `fun q : ℕ × ℕ => decide (q.1 ≤ q.2)` es de tiempo polinomial.

Mathlib codifica un natural en binario con el bit menos significativo primero y sin ceros de más: el último bit es
`true`, y el cero es la lista vacía.

**El algoritmo** (`mayor`). Recorre los dos números a la vez desde el bit menos significativo, llevando un bit: «hasta
aquí, el primero es mayor». Cada posición donde difieren lo reemplaza, porque los bits altos mandan. Si uno se acaba
antes, el más largo es el mayor.

**El archivo** tiene dos partes: que el algoritmo, sobre listas, decide la comparación (`mayor_encodeNat`); y la
máquina que lo ejecuta, con su tiempo.
-/

open Computability

namespace Sagitta.Map
namespace Comparar

/-! ## 1. El algoritmo sobre listas -/

/-- El número que representa una lista, con el primer bit como el menos significativo. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * val l

/-- Sin ceros de más: vacía, o con el último bit en `true`. -/
def canon : List Bool → Prop
  | [] => True
  | [b] => b = true
  | _ :: c :: l => canon (c :: l)

/-- El bit «el primero es mayor», después de comparar una posición más. -/
def nuevo (g a b : Bool) : Bool := if a = b then g else a && !b

/-- ¿El primer número es mayor que el segundo? `g` es la respuesta para los bits ya vistos. -/
def mayor : List Bool → List Bool → Bool → Bool
  | [], [], g => g
  | [], _ :: _, _ => false
  | _ :: _, [], _ => true
  | a :: x, b :: y, g => mayor x y (nuevo g a b)

theorem canon_tail {b : Bool} {l : List Bool} (h : canon (b :: l)) : canon l := by
  cases l with
  | nil => trivial
  | cons c l => exact h

theorem val_pos : ∀ {b : Bool} {l : List Bool}, canon (b :: l) → 0 < val (b :: l)
  | b, [], h => by
    have : b = true := h
    subst this
    simp [val]
  | b, c :: l, h => by
    have := val_pos (b := c) (l := l) h
    simp only [val] at this ⊢
    omega

/-- **El algoritmo es correcto**, para listas sin ceros de más. -/
theorem mayor_iff : ∀ (x y : List Bool) (g : Bool), canon x → canon y →
    (mayor x y g = true ↔ (val y < val x ∨ (val x = val y ∧ g = true)))
  | [], [], g, _, _ => by simp [mayor, val]
  | [], b :: y, g, _, hy => by
    have h := val_pos hy
    simp only [mayor, val] at h ⊢
    constructor
    · intro h'; exact absurd h' (by simp)
    · rintro (h' | ⟨h', -⟩) <;> omega
  | a :: x, [], g, hx, _ => by
    have h := val_pos hx
    simp only [mayor, val] at h ⊢
    constructor
    · intro _; exact Or.inl h
    · intro _; trivial
  | a :: x, b :: y, g, hx, hy => by
    have ih := mayor_iff x y (nuevo g a b) (canon_tail hx) (canon_tail hy)
    rw [mayor, ih]
    cases a <;> cases b <;> by_cases hg : g = true <;> simp [val, nuevo, hg] <;> omega

theorem val_encodePosNum : ∀ p : PosNum, val (encodePosNum p) = (p : ℕ)
  | PosNum.one => by simp [encodePosNum, val]
  | PosNum.bit0 n => by
    simp [encodePosNum, val, val_encodePosNum n, PosNum.cast_bit0]
    omega
  | PosNum.bit1 n => by
    simp [encodePosNum, val, val_encodePosNum n, PosNum.cast_bit1]
    omega

theorem canon_encodePosNum : ∀ p : PosNum, canon (encodePosNum p)
  | PosNum.one => rfl
  | PosNum.bit0 n => by
    have ih := canon_encodePosNum n
    have hne := encodePosNum_nonempty n
    cases h : encodePosNum n with
    | nil => exact absurd h hne
    | cons c l => rw [encodePosNum, h]; rw [h] at ih; exact ih
  | PosNum.bit1 n => by
    have ih := canon_encodePosNum n
    have hne := encodePosNum_nonempty n
    cases h : encodePosNum n with
    | nil => exact absurd h hne
    | cons c l => rw [encodePosNum, h]; rw [h] at ih; exact ih

theorem val_encodeNat (n : ℕ) : val (encodeNat n) = n := by
  have h := Num.to_of_nat n
  unfold encodeNat
  generalize (n : Num) = k at h
  cases k with
  | zero => simpa [encodeNum, val] using h
  | pos p => rw [encodeNum, val_encodePosNum]; simpa using h

theorem canon_encodeNat (n : ℕ) : canon (encodeNat n) := by
  unfold encodeNat
  cases (n : Num) with
  | zero => trivial
  | pos p => exact canon_encodePosNum p

/-- **El algoritmo decide `≤`** sobre las codificaciones de Mathlib. -/
theorem mayor_encodeNat (m n : ℕ) : (!mayor (encodeNat m) (encodeNat n) false) = decide (m ≤ n) := by
  have h := mayor_iff (encodeNat m) (encodeNat n) false (canon_encodeNat m) (canon_encodeNat n)
  rw [val_encodeNat, val_encodeNat] at h
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · intro hf
    by_contra hmn
    have : mayor (encodeNat m) (encodeNat n) false = true := h.mpr (Or.inl (by omega))
    rw [hf] at this
    exact absurd this (by simp)
  · intro hmn
    by_contra hf
    have ht : mayor (encodeNat m) (encodeNat n) false = true := by simpa using hf
    rcases h.mp ht with h' | ⟨-, h'⟩
    · omega
    · exact absurd h' (by simp)

/-! ## 2. La máquina

Cuatro pilas: entrada (0), auxiliar (1), el primer número (2) y salida (3). La entrada trae
`delimita x ++ y`.

* **A**: lee el bloque y pasa `x` a la auxiliar; queda invertido.
* **B**: pasa la auxiliar a la pila 2; `x` queda derecho, con el bit menos significativo arriba, como `y`.
* **C**: compara un bit de cada uno y actualiza el estado. Si uno se acaba, pasa a vaciar el otro.
* **D** y **E**: vacían lo que quede de `y` o de `x`, y escriben la respuesta.
-/

open Turing Turing.TM2 Turing.TM2.Stmt
open Componer (Llega)

/-- El estado: el bit «el primero es mayor» y los dos bits que se están comparando. -/
abbrev Est : Type := Bool × Option Bool × Option Bool

/-- El final común: escribe la respuesta, deja el estado como al inicio y se detiene. -/
def fin : TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 5) Est :=
  push 3 (fun v => !v.1) (load (fun _ => (false, none, none)) halt)

/-- La máquina que compara dos naturales. -/
@[reducible] def maquinaLe : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 5
  main := 0
  σ := Est
  initialState := (false, none, none)
  m := fun
    | 0 =>
      pop 0 (fun v o => (v.1, o, none))
        (branch (fun v => v.2.1 == some true)
          (pop 0 (fun v o => (v.1, o, none)) (push 1 (fun v => v.2.1.getD false) (goto fun _ => 0)))
          (goto fun _ => 1))
    | 1 =>
      pop 1 (fun v o => (v.1, o, none))
        (branch (fun v => v.2.1.isSome) (push 2 (fun v => v.2.1.getD false) (goto fun _ => 1))
          (goto fun _ => 2))
    | 2 =>
      pop 2 (fun v o => (v.1, o, none))
        (pop 0 (fun v o => (v.1, v.2.1, o))
          (branch (fun v => v.2.1.isSome)
            (branch (fun v => v.2.2.isSome)
              (load (fun v => (nuevo v.1 (v.2.1.getD false) (v.2.2.getD false), none, none))
                (goto fun _ => 2))
              (load (fun _ => (true, none, none)) (goto fun _ => 4)))
            (branch (fun v => v.2.2.isSome)
              (load (fun _ => (false, none, none)) (goto fun _ => 3))
              fin)))
    | 3 => pop 0 (fun v o => (v.1, o, none)) (branch (fun v => v.2.1.isSome) (goto fun _ => 3) fin)
    | 4 => pop 2 (fun v o => (v.1, o, none)) (branch (fun v => v.2.1.isSome) (goto fun _ => 4) fin)

/-- Las cuatro pilas. -/
def pilas (i t x o : List Bool) : ∀ _ : Fin 4, List Bool
  | 0 => i
  | 1 => t
  | 2 => x
  | 3 => o

theorem upd0 (i t x o z : List Bool) : Function.update (pilas i t x o) 0 z = pilas z t x o := by
  funext k; fin_cases k <;> rfl
theorem upd1 (i t x o z : List Bool) : Function.update (pilas i t x o) 1 z = pilas i z x o := by
  funext k; fin_cases k <;> rfl
theorem upd2 (i t x o z : List Bool) : Function.update (pilas i t x o) 2 z = pilas i t z o := by
  funext k; fin_cases k <;> rfl
theorem upd3 (i t x o z : List Bool) : Function.update (pilas i t x o) 3 z = pilas i t x z := by
  funext k; fin_cases k <;> rfl

/-- La configuración de la máquina, con sus tipos a la vista. -/
abbrev CL : Type := TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 5) Est

/-! ### Bucle A: leer el bloque -/

theorem pasoA_bit (v : Est) (b : Bool) (r t x o : List Bool) :
    TM2.step maquinaLe.m (⟨some 0, v, pilas (true :: b :: r) t x o⟩ : CL) =
      some ⟨some 0, (v.1, some b, none), pilas r (b :: t) x o⟩ := by
  show some (stepAux (maquinaLe.m 0) v (pilas (true :: b :: r) t x o)) = _
  simp [maquinaLe, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : Est) (r t x o : List Bool) :
    TM2.step maquinaLe.m (⟨some 0, v, pilas (false :: r) t x o⟩ : CL) =
      some ⟨some 1, (v.1, some false, none), pilas r t x o⟩ := by
  show some (stepAux (maquinaLe.m 0) v (pilas (false :: r) t x o)) = _
  simp [maquinaLe, stepAux, pilas, upd0]

theorem bucleA (r x o : List Bool) : ∀ (u t : List Bool) (v : Est),
    Llega (TM2.step maquinaLe.m) (u.length + 1)
      (⟨some 0, v, pilas (CodBits.delimita u ++ r) t x o⟩ : CL)
      ⟨some 1, (v.1, some false, none), pilas r (u.reverse ++ t) x o⟩
  | [], t, v => Llega.uno (pasoA_fin v r t x o)
  | b :: u, t, v => by
    have h1 := Llega.uno (pasoA_bit v b (CodBits.delimita u ++ r) t x o)
    have h2 := bucleA r x o u (b :: t) (v.1, some b, none)
    have := h1.trans h2
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

/-! ### Bucle B: enderezar el primer número -/

theorem pasoB_bit (v : Est) (c : Bool) (i t x o : List Bool) :
    TM2.step maquinaLe.m (⟨some 1, v, pilas i (c :: t) x o⟩ : CL) =
      some ⟨some 1, (v.1, some c, none), pilas i t (c :: x) o⟩ := by
  show some (stepAux (maquinaLe.m 1) v (pilas i (c :: t) x o)) = _
  simp [maquinaLe, stepAux, pilas, upd1, upd2]

theorem pasoB_fin (v : Est) (i x o : List Bool) :
    TM2.step maquinaLe.m (⟨some 1, v, pilas i [] x o⟩ : CL) =
      some ⟨some 2, (v.1, none, none), pilas i [] x o⟩ := by
  show some (stepAux (maquinaLe.m 1) v (pilas i [] x o)) = _
  simp [maquinaLe, stepAux, pilas, upd1]

theorem bucleB (i o : List Bool) : ∀ (t x : List Bool) (v : Est),
    Llega (TM2.step maquinaLe.m) (t.length + 1)
      (⟨some 1, v, pilas i t x o⟩ : CL) ⟨some 2, (v.1, none, none), pilas i [] (t.reverse ++ x) o⟩
  | [], x, v => Llega.uno (pasoB_fin v i x o)
  | c :: t, x, v => by
    have := (Llega.uno (pasoB_bit v c i t x o)).trans (bucleB i o t (c :: x) (v.1, some c, none))
    simpa [List.reverse_cons, List.append_assoc] using this

/-! ### Bucles D y E: vaciar lo que quede y responder -/

/-- La configuración final, con la respuesta `!g` en la salida. -/
abbrev final (g : Bool) : CL := ⟨none, (false, none, none), pilas [] [] [] [!g]⟩

theorem pasoD_bit (v : Est) (c : Bool) (r : List Bool) :
    TM2.step maquinaLe.m (⟨some 3, v, pilas (c :: r) [] [] []⟩ : CL) =
      some ⟨some 3, (v.1, some c, none), pilas r [] [] []⟩ := by
  show some (stepAux (maquinaLe.m 3) v (pilas (c :: r) [] [] [])) = _
  simp [maquinaLe, stepAux, pilas, upd0]

theorem pasoD_fin (v : Est) :
    TM2.step maquinaLe.m (⟨some 3, v, pilas [] [] [] []⟩ : CL) = some (final v.1) := by
  show some (stepAux (maquinaLe.m 3) v (pilas [] [] [] [])) = _
  simp [maquinaLe, fin, stepAux, pilas, upd0, upd3]

theorem bucleD : ∀ (r : List Bool) (v : Est),
    Llega (TM2.step maquinaLe.m) (r.length + 1) (⟨some 3, v, pilas r [] [] []⟩ : CL) (final v.1)
  | [], v => Llega.uno (pasoD_fin v)
  | c :: r, v => (Llega.uno (pasoD_bit v c r)).trans (bucleD r (v.1, some c, none))

theorem pasoE_bit (v : Est) (c : Bool) (r : List Bool) :
    TM2.step maquinaLe.m (⟨some 4, v, pilas [] [] (c :: r) []⟩ : CL) =
      some ⟨some 4, (v.1, some c, none), pilas [] [] r []⟩ := by
  show some (stepAux (maquinaLe.m 4) v (pilas [] [] (c :: r) [])) = _
  simp [maquinaLe, stepAux, pilas, upd2]

theorem pasoE_fin (v : Est) :
    TM2.step maquinaLe.m (⟨some 4, v, pilas [] [] [] []⟩ : CL) = some (final v.1) := by
  show some (stepAux (maquinaLe.m 4) v (pilas [] [] [] [])) = _
  simp [maquinaLe, fin, stepAux, pilas, upd2, upd3]

theorem bucleE : ∀ (r : List Bool) (v : Est),
    Llega (TM2.step maquinaLe.m) (r.length + 1) (⟨some 4, v, pilas [] [] r []⟩ : CL) (final v.1)
  | [], v => Llega.uno (pasoE_fin v)
  | c :: r, v => (Llega.uno (pasoE_bit v c r)).trans (bucleE r (v.1, some c, none))

/-! ### Bucle C: comparar -/

/-- Cuántos pasos tarda la comparación, con lo que haya que vaciar después. -/
def pasosC : List Bool → List Bool → ℕ
  | [], [] => 1
  | [], _ :: y => (y.length + 1) + 1
  | _ :: x, [] => (x.length + 1) + 1
  | _ :: x, _ :: y => pasosC x y + 1

theorem pasosC_le : ∀ x y : List Bool, pasosC x y ≤ x.length + y.length + 2
  | [], [] => by simp [pasosC]
  | [], _ :: y => by simp [pasosC]
  | _ :: x, [] => by simp [pasosC]
  | _ :: x, _ :: y => by have := pasosC_le x y; simp [pasosC]; omega

theorem pasoC_ambos (g : Bool) (p q : Option Bool) (a b : Bool) (x y : List Bool) :
    TM2.step maquinaLe.m (⟨some 2, (g, p, q), pilas (b :: y) [] (a :: x) []⟩ : CL) =
      some ⟨some 2, (nuevo g a b, none, none), pilas y [] x []⟩ := by
  show some (stepAux (maquinaLe.m 2) (g, p, q) (pilas (b :: y) [] (a :: x) [])) = _
  simp [maquinaLe, stepAux, pilas, upd0, upd2]

theorem pasoC_falta_x (g : Bool) (p q : Option Bool) (b : Bool) (y : List Bool) :
    TM2.step maquinaLe.m (⟨some 2, (g, p, q), pilas (b :: y) [] [] []⟩ : CL) =
      some ⟨some 3, (false, none, none), pilas y [] [] []⟩ := by
  show some (stepAux (maquinaLe.m 2) (g, p, q) (pilas (b :: y) [] [] [])) = _
  simp [maquinaLe, stepAux, pilas, upd0, upd2]

theorem pasoC_falta_y (g : Bool) (p q : Option Bool) (a : Bool) (x : List Bool) :
    TM2.step maquinaLe.m (⟨some 2, (g, p, q), pilas [] [] (a :: x) []⟩ : CL) =
      some ⟨some 4, (true, none, none), pilas [] [] x []⟩ := by
  show some (stepAux (maquinaLe.m 2) (g, p, q) (pilas [] [] (a :: x) [])) = _
  simp [maquinaLe, stepAux, pilas, upd0, upd2]

theorem pasoC_fin (g : Bool) (p q : Option Bool) :
    TM2.step maquinaLe.m (⟨some 2, (g, p, q), pilas [] [] [] []⟩ : CL) = some (final g) := by
  show some (stepAux (maquinaLe.m 2) (g, p, q) (pilas [] [] [] [])) = _
  simp [maquinaLe, fin, stepAux, pilas, upd0, upd2, upd3]

/-- **Bucle C.** La máquina termina con `!mayor x y g` en la salida. -/
theorem bucleC : ∀ (x y : List Bool) (g : Bool) (p q : Option Bool),
    Llega (TM2.step maquinaLe.m) (pasosC x y)
      (⟨some 2, (g, p, q), pilas y [] x []⟩ : CL) (final (mayor x y g))
  | [], [], g, p, q => Llega.uno (pasoC_fin g p q)
  | [], b :: y, g, p, q => (Llega.uno (pasoC_falta_x g p q b y)).trans (bucleD y (false, none, none))
  | a :: x, [], g, p, q => (Llega.uno (pasoC_falta_y g p q a x)).trans (bucleE x (true, none, none))
  | a :: x, b :: y, g, p, q =>
    (Llega.uno (pasoC_ambos g p q a b x y)).trans (bucleC x y (nuevo g a b) none none)

/-! ### El armado -/

theorem initLe (inp : List Bool) :
    (initList maquinaLe inp : CL) = ⟨some 0, (false, none, none), pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaLe inp).stk⟩ : CL) = _
  rw [Componer.initList_stk]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltLe (out : List Bool) :
    (haltList maquinaLe out : CL) = ⟨none, (false, none, none), pilas [] [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaLe out).stk⟩ : CL) = _
  rw [Componer.haltList_stk]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- **La corrida completa**: de `delimita x ++ y` a la respuesta. -/
theorem corridaLe (x y : List Bool) :
    Llega (TM2.step maquinaLe.m) (pasosC x y + ((x.length + 1) + (x.length + 1)))
      (initList maquinaLe (CodBits.delimita x ++ y) : CL) (haltList maquinaLe [!mayor x y false]) := by
  have a := bucleA y [] [] x [] (false, none, none)
  have b := bucleB y [] (x.reverse ++ []) [] (false, some false, none)
  have c := bucleC x y false none none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at a b
  have := (a.trans b).trans c
  rw [initLe, haltLe]
  exact this

open Polynomial in
/-- Comparar dos naturales se calcula en tiempo polinomial: a lo sumo `2n + 2` pasos. -/
noncomputable def leComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := ℕ × ℕ)).encode
      (CodBits.toEncoding (α := Bool)).encode (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) where
  tm := maquinaLe
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * X + 2
  outputsFun q := by
    have run := corridaLe (encodeNat q.1) (encodeNat q.2)
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := ℕ × ℕ)).encode q) =
        CodBits.delimita (encodeNat q.1) ++ encodeNat q.2 := by
      simp only [Equiv.refl]
      rw [List.map_id]
      rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := Bool)).encode (decide (q.1 ≤ q.2))) =
        [!mayor (encodeNat q.1) (encodeNat q.2) false] := by
      simp only [Equiv.refl]
      rw [List.map_id, mayor_encodeNat]
      rfl
    have hlen : ((CodBits.toEncoding (α := ℕ × ℕ)).encode q).length =
        2 * (encodeNat q.1).length + 1 + (encodeNat q.2).length := by
      show (CodBits.delimita (encodeNat q.1) ++ encodeNat q.2).length = _
      rw [List.length_append, Basicas.delimita_length]
    have hC := pasosC_le (encodeNat q.1) (encodeNat q.2)
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_mul, eval_X, eval_ofNat]; omega⟩

/-- **Quinta propiedad de `CierrePolinomial`, probada.** -/
theorem esPolinomial_le : EsPolinomial (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) := ⟨leComputable⟩

end Comparar
end Sagitta.Map
