import Sagitta.Map.Componer

/-!
# Máquinas básicas para `CierrePolinomial`

Las propiedades de `CierrePolinomial` que son una máquina concreta, sobre `Turing.FinTM2` de Mathlib.

## La conjunción de dos bits

Un par de bits `(b₁, b₂)` se codifica como `[true, b₁, false, b₂]`: el primero va en un bloque autodelimitado
(`Codificacion.lean`). La máquina tiene una sola pila y una sola instrucción: saca los cuatro símbolos, guarda
`b₁` y `b₂`, escribe `b₁ && b₂`, deja el estado como al inicio y se detiene. Tarda un paso.
-/

open Turing Turing.TM2 Turing.TM2.Stmt

namespace Sagitta.Map
namespace Basicas

/-- La máquina de la conjunción: una pila de bits, y dos bits de estado. -/
def maquinaY : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (false, false)
  m _ :=
    pop () (fun v _ => v)
      (pop () (fun v o => (o.getD false, v.2))
        (pop () (fun v _ => v)
          (pop () (fun v o => (v.1, o.getD false))
            (push () (fun v => v.1 && v.2)
              (load (fun _ => (false, false)) halt)))))

/-- La conjunción de dos bits se calcula en tiempo polinomial (en un paso). -/
noncomputable def yComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := Bool × Bool)).encode
      (CodBits.toEncoding (α := Bool)).encode (fun q : Bool × Bool => q.1 && q.2) where
  tm := maquinaY
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun q := by
    obtain ⟨b₁, b₂⟩ := q
    refine ⟨⟨1, ?_⟩, by simp⟩
    cases b₁ <;> cases b₂ <;> rfl

/-- **Tercera propiedad de `CierrePolinomial`, probada.** -/
theorem esPolinomial_y : EsPolinomial (fun q : Bool × Bool => q.1 && q.2) := ⟨yComputable⟩

/-! ## La negación de un bit

Un bit se codifica como una lista de un elemento. La máquina lo saca, escribe su negación y deja el estado como al
inicio. Tarda un paso. -/

/-- La máquina de la negación. -/
def maquinaNo : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := pop () (fun _ o => o.getD false) (push () (fun v => !v) (load (fun _ => false) halt))

/-- La negación de un bit se calcula en tiempo polinomial (en un paso). -/
noncomputable def noComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := Bool)).encode
      (CodBits.toEncoding (α := Bool)).encode (fun b : Bool => !b) where
  tm := maquinaNo
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun b := by
    refine ⟨⟨1, ?_⟩, by simp⟩
    cases b <;> rfl

theorem esPolinomial_no : EsPolinomial (fun b : Bool => !b) := ⟨noComputable⟩

/-! ## La primera proyección

Un par `(a, b)` se codifica como `delimita (cod a) ++ cod b`. La máquina devuelve `cod a`. Tiene tres pilas:
entrada (0), auxiliar (1) y salida (2), y tres bucles:

* **A**: lee el bloque. Por cada marca `true` saca el bit que sigue y lo pasa a la auxiliar; con la marca `false`
  termina.
* **B**: vacía lo que queda de la entrada.
* **C**: pasa la auxiliar a la salida. La auxiliar quedó invertida, y este traspaso la endereza.

Para una entrada de `n` bits tarda `n + 2` pasos.
-/

open Componer (Llega)

/-- La máquina de la primera proyección. -/
@[reducible] def maquinaFst : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  m := fun
    | 0 =>
      pop 0 (fun _ o => o)
        (branch (fun v => v == some true)
          (pop 0 (fun _ o => o) (push 1 (fun v => v.getD false) (goto fun _ => 0)))
          (goto fun _ => 1))
    | 1 =>
      pop 0 (fun _ o => o) (branch (fun v => v.isSome) (goto fun _ => 1) (goto fun _ => 2))
    | 2 =>
      pop 1 (fun _ o => o)
        (branch (fun v => v.isSome) (push 2 (fun v => v.getD false) (goto fun _ => 2)) halt)

/-- Las tres pilas: entrada, auxiliar y salida. -/
def pilas (i t o : List Bool) : ∀ _ : Fin 3, List Bool
  | 0 => i
  | 1 => t
  | 2 => o

theorem upd0 (i t o x : List Bool) : Function.update (pilas i t o) 0 x = pilas x t o := by
  funext k; fin_cases k <;> rfl

theorem upd1 (i t o x : List Bool) : Function.update (pilas i t o) 1 x = pilas i x o := by
  funext k; fin_cases k <;> rfl

theorem upd2 (i t o x : List Bool) : Function.update (pilas i t o) 2 x = pilas i t x := by
  funext k; fin_cases k <;> rfl

/-- La configuración de la máquina, con sus tipos a la vista. -/
abbrev CF : Type := TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)

theorem pasoA_bit (v : Option Bool) (b : Bool) (r t o : List Bool) :
    TM2.step maquinaFst.m (⟨some 0, v, pilas (true :: b :: r) t o⟩ : CF) =
      some ⟨some 0, some b, pilas r (b :: t) o⟩ := by
  show some (stepAux (maquinaFst.m 0) v (pilas (true :: b :: r) t o)) = _
  simp [maquinaFst, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : Option Bool) (r t o : List Bool) :
    TM2.step maquinaFst.m (⟨some 0, v, pilas (false :: r) t o⟩ : CF) =
      some ⟨some 1, some false, pilas r t o⟩ := by
  show some (stepAux (maquinaFst.m 0) v (pilas (false :: r) t o)) = _
  simp [maquinaFst, stepAux, pilas, upd0]

/-- **Bucle A.** Lee el bloque y deja su contenido, invertido, en la auxiliar. -/
theorem bucleA (r o : List Bool) : ∀ (u t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaFst.m) (u.length + 1)
      (⟨some 0, v, pilas (CodBits.delimita u ++ r) t o⟩ : CF)
      ⟨some 1, some false, pilas r (u.reverse ++ t) o⟩
  | [], t, v => Llega.uno (pasoA_fin v r t o)
  | b :: u, t, v => by
    have h1 := Llega.uno (pasoA_bit v b (CodBits.delimita u ++ r) t o)
    have h2 := bucleA r o u (b :: t) (some b)
    have := h1.trans h2
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

theorem pasoB_bit (v : Option Bool) (x : Bool) (r t o : List Bool) :
    TM2.step maquinaFst.m (⟨some 1, v, pilas (x :: r) t o⟩ : CF) = some ⟨some 1, some x, pilas r t o⟩ := by
  show some (stepAux (maquinaFst.m 1) v (pilas (x :: r) t o)) = _
  simp [maquinaFst, stepAux, pilas, upd0]

theorem pasoB_fin (v : Option Bool) (t o : List Bool) :
    TM2.step maquinaFst.m (⟨some 1, v, pilas [] t o⟩ : CF) = some ⟨some 2, none, pilas [] t o⟩ := by
  show some (stepAux (maquinaFst.m 1) v (pilas [] t o)) = _
  simp [maquinaFst, stepAux, pilas, upd0]

/-- **Bucle B.** Vacía lo que queda de la entrada. -/
theorem bucleB (t o : List Bool) : ∀ (r : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaFst.m) (r.length + 1)
      (⟨some 1, v, pilas r t o⟩ : CF) ⟨some 2, none, pilas [] t o⟩
  | [], v => Llega.uno (pasoB_fin v t o)
  | x :: r, v => (Llega.uno (pasoB_bit v x r t o)).trans (bucleB t o r (some x))

theorem pasoC_bit (v : Option Bool) (x : Bool) (t o : List Bool) :
    TM2.step maquinaFst.m (⟨some 2, v, pilas [] (x :: t) o⟩ : CF) =
      some ⟨some 2, some x, pilas [] t (x :: o)⟩ := by
  show some (stepAux (maquinaFst.m 2) v (pilas [] (x :: t) o)) = _
  simp [maquinaFst, stepAux, pilas, upd1, upd2]

theorem pasoC_fin (v : Option Bool) (o : List Bool) :
    TM2.step maquinaFst.m (⟨some 2, v, pilas [] [] o⟩ : CF) = some ⟨none, none, pilas [] [] o⟩ := by
  show some (stepAux (maquinaFst.m 2) v (pilas [] [] o)) = _
  simp [maquinaFst, stepAux, pilas, upd1]

/-- **Bucle C.** Pasa la auxiliar a la salida, invirtiéndola. -/
theorem bucleC : ∀ (t o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaFst.m) (t.length + 1)
      (⟨some 2, v, pilas [] t o⟩ : CF) ⟨none, none, pilas [] [] (t.reverse ++ o)⟩
  | [], o, v => Llega.uno (pasoC_fin v o)
  | x :: t, o, v => by
    have := (Llega.uno (pasoC_bit v x t o)).trans (bucleC t (x :: o) (some x))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem delimita_length : ∀ l : List Bool, (CodBits.delimita l).length = 2 * l.length + 1
  | [] => rfl
  | b :: l => by simp [CodBits.delimita, delimita_length l]; omega

theorem initFst (inp : List Bool) :
    (initList maquinaFst inp : CF) = ⟨some 0, none, pilas inp [] []⟩ := by
  show (⟨_, _, (initList maquinaFst inp).stk⟩ : CF) = _
  rw [Componer.initList_stk]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltFst (out : List Bool) :
    (haltList maquinaFst out : CF) = ⟨none, none, pilas [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaFst out).stk⟩ : CF) = _
  rw [Componer.haltList_stk]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- **La corrida completa**: de `delimita u ++ w` en la entrada a `u` en la salida. -/
theorem corridaFst (u w : List Bool) :
    Llega (TM2.step maquinaFst.m) ((u.length + 1) + ((w.length + 1) + (u.length + 1)))
      (initList maquinaFst (CodBits.delimita u ++ w) : CF) (haltList maquinaFst u) := by
  have a := bucleA w [] u [] none
  have b := bucleB (u.reverse ++ []) [] w (some false)
  have c := bucleC (u.reverse ++ []) [] none
  have := (a.trans b).trans c
  rw [initFst, haltFst]
  simpa using this

open Polynomial in
/-- La primera proyección de un par se calcula en tiempo polinomial: `n + 2` pasos. -/
noncomputable def fstComputable {α β : Type} [CodBits α] [CodBits β] :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := α × β)).encode
      (CodBits.toEncoding (α := α)).encode (Prod.fst : α × β → α) where
  tm := maquinaFst
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := X + 2
  outputsFun q := by
    have run := corridaFst (CodBits.cod q.1) (CodBits.cod q.2)
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := α × β)).encode q) =
        CodBits.delimita (CodBits.cod q.1) ++ CodBits.cod q.2 := by
      simp only [Equiv.refl]
      rw [List.map_id]
      rfl
    have hout : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := α)).encode q.1) =
        CodBits.cod q.1 := by
      simp only [Equiv.refl]
      rw [List.map_id]
      rfl
    have hlen : ((CodBits.toEncoding (α := α × β)).encode q).length =
        2 * (CodBits.cod q.1).length + 1 + (CodBits.cod q.2).length := by
      show (CodBits.delimita (CodBits.cod q.1) ++ CodBits.cod q.2).length = _
      rw [List.length_append, delimita_length]
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_X, eval_ofNat]; omega⟩

/-- **Segunda propiedad de `CierrePolinomial`, probada.** -/
theorem esPolinomial_fst {α β : Type} [CodBits α] [CodBits β] : EsPolinomial (Prod.fst : α × β → α) :=
  ⟨fstComputable⟩

end Basicas
end Sagitta.Map
