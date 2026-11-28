import Sagitta.Map.AlgoritmoEstandar

/-!
# El descenso exhaustivo, en tiempo polinomial

Para que la reducción de NP al problema del algoritmo estándar sea una reducción de tiempo polinomial, hay que
probar que la solución inicial, el vecino y el costo del descenso `exhaustivo` se calculan en tiempo polinomial.

**Lo probado** (`exhaustivo_polinomial`, `np_por_destino_polinomial`): las tres cosas, **dada una vara**: una
función polinomial `tope` cuyo resultado tiene el largo de la cota, `|tope x| = M x`. La vara reemplaza al número
`p(|x|)`: comparar largos de cadenas no necesita aritmética.

Las piezas:

1. el costo se codifica como su cadena (`encodeNat_costo`);
2. la solución inicial (`esPolinomial_vacia`);
3. la cadena siguiente (`esPolinomial_sig`);
4. la segunda proyección y la disyunción, por composición (`esPolinomial_snd`, `esPolinomial_o`);
5. comparar largos (`esPolinomial_menor`);
6. elegir entre dos cadenas (`esPolinomial_si`);
7. escribir el costo (`esPolinomial_costo`);
8. el vecino y el costo, armados por pares y composición.

**La vara** se construye en `Vara.lean`, para todo polinomio; con ella la reducción queda sin condiciones
(`Vara.np_al_algoritmo_estandar`).
-/

open Computability Turing Turing.TM2 Turing.TM2.Stmt

namespace Sagitta.Map
namespace ExhaustivoTiempo

open Componer (Llega)
open Comparar (val canon val_pos canon_tail canon_encodeNat val_encodeNat pilas upd0 upd1 upd2 upd3)
open Enumera

/-! ## 1. El costo se codifica como su cadena -/

/-- Entre listas sin ceros de más, el valor determina la lista. -/
theorem val_inj : ∀ a b : List Bool, canon a → canon b → val a = val b → a = b
  | [], [], _, _, _ => rfl
  | [], c :: b, _, hb, h => by
    have := val_pos hb
    simp only [val] at h this
    omega
  | c :: a, [], ha, _, h => by
    have := val_pos ha
    simp only [val] at h this
    omega
  | c :: a, d :: b, ha, hb, h => by
    simp only [val] at h
    have : c = d ∧ val a = val b := by cases c <;> cases d <;> simp at h ⊢ <;> omega
    rw [this.1, val_inj a b (canon_tail ha) (canon_tail hb) this.2]

/-- Una lista sin ceros de más es el código binario de su valor. -/
theorem encodeNat_val {l : List Bool} (h : canon l) : encodeNat (val l) = l :=
  val_inj _ _ (canon_encodeNat _) h (val_encodeNat _)

theorem canon_append_true : ∀ l : List Bool, canon (l ++ [true])
  | [] => rfl
  | [_] => rfl
  | _ :: d :: l => canon_append_true (d :: l)

theorem canon_costoBits (k : ℕ) (s : List Bool) : canon (costoBits k s) := by
  have : costoBits k s = (s.map not ++ false :: List.replicate (k - s.length) true) ++ [true] := by
    simp [costoBits]
  rw [this]
  exact canon_append_true _

/-- **El código binario del costo es la cadena `costoBits`.** -/
theorem encodeNat_costo (V : List Bool × List Bool → Bool) (M : List Bool → ℕ) (q : List Bool × List Bool) :
    encodeNat ((exhaustivo V M).costo q) = costoBits (M q.1) q.2 :=
  encodeNat_val (canon_costoBits _ _)

/-- La configuración de las máquinas de este archivo. -/
abbrev CE : Type := TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 4) (Option Bool)

/-! ## 2. La solución inicial: devolver la cadena vacía -/

/-- La máquina que vacía su entrada. -/
@[reducible] def maquinaVacia : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool
  initialState := none
  m := fun _ => pop 0 (fun _ o => o) (branch (fun v => v.isSome) (goto fun _ => 0) halt)

namespace Vacia

theorem paso_bit (v : Option Bool) (c : Bool) (i : List Bool) :
    TM2.step maquinaVacia.m (⟨some 0, v, pilas (c :: i) [] [] []⟩ : CE) =
      some ⟨some 0, some c, pilas i [] [] []⟩ := by
  show some (stepAux (maquinaVacia.m 0) v (pilas (c :: i) [] [] [])) = _
  simp [maquinaVacia, stepAux, pilas, upd0]

theorem paso_fin (v : Option Bool) :
    TM2.step maquinaVacia.m (⟨some 0, v, pilas [] [] [] []⟩ : CE) = some ⟨none, none, pilas [] [] [] []⟩ := by
  show some (stepAux (maquinaVacia.m 0) v (pilas [] [] [] [])) = _
  simp [maquinaVacia, stepAux, pilas, upd0]

theorem bucle : ∀ (i : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaVacia.m) (i.length + 1)
      (⟨some 0, v, pilas i [] [] []⟩ : CE) ⟨none, none, pilas [] [] [] []⟩
  | [], v => Llega.uno (paso_fin v)
  | c :: i, v => (Llega.uno (paso_bit v c i)).trans (bucle i (some c))

theorem init (inp : List Bool) : (initList maquinaVacia inp : CE) = ⟨some 0, none, pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaVacia inp).stk⟩ : CE) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt : (haltList maquinaVacia [] : CE) = ⟨none, none, pilas [] [] [] []⟩ := by
  show (⟨_, _, (haltList maquinaVacia []).stk⟩ : CE) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem corrida (i : List Bool) :
    Llega (TM2.step maquinaVacia.m) (i.length + 1) (initList maquinaVacia i : CE) (haltList maquinaVacia []) := by
  rw [init, halt]
  exact bucle i none

end Vacia

open Polynomial in
/-- Devolver la cadena vacía se calcula en tiempo polinomial. -/
noncomputable def vaciaComputable {α : Type} [CodBits α] :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := α)).encode
      (CodBits.toEncoding (α := List Bool)).encode (fun _ : α => ([] : List Bool)) where
  tm := maquinaVacia
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := X + 1
  outputsFun a := by
    have run := Vacia.corrida (CodBits.cod a)
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := α)).encode a) = CodBits.cod a := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool)).encode ([] : List Bool)) = [] := rfl
    have hlen : ((CodBits.toEncoding (α := α)).encode a).length = (CodBits.cod a).length := rfl
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_X, eval_one]; omega⟩

theorem esPolinomial_vacia {α : Type} [CodBits α] : EsPolinomial (fun _ : α => ([] : List Bool)) :=
  ⟨vaciaComputable⟩

/-! ## 3. La cadena siguiente

`sig` cambia los `true` del principio por `false` hasta dar con un `false`, que pasa a `true`; si no hay, agrega un
`false` al final. La máquina usa la entrada (0), una auxiliar (1) y la salida (3):

* **A**: mientras saca `true`, pone `false` en la auxiliar. Con un `false`, pone `true` y pasa a B. Si la entrada se
  acaba, pone `false` y pasa a C.
* **B**: pasa el resto de la entrada a la auxiliar.
* **C**: pasa la auxiliar a la salida. La auxiliar tiene el resultado al revés, y este traspaso lo endereza.
-/

/-- La máquina de la cadena siguiente. -/
@[reducible] def maquinaSig : FinTM2 where
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
          (push 1 (fun _ => false) (goto fun _ => 0))
          (branch (fun v => v.isSome)
            (push 1 (fun _ => true) (goto fun _ => 1))
            (push 1 (fun _ => false) (goto fun _ => 2))))
    | 1 => pop 0 (fun _ o => o)
        (branch (fun v => v.isSome) (push 1 (fun v => v.getD false) (goto fun _ => 1)) (goto fun _ => 2))
    | _ => pop 1 (fun _ o => o)
        (branch (fun v => v.isSome) (push 3 (fun v => v.getD false) (goto fun _ => 2)) halt)

namespace Sig

theorem pasoA_true (v : Option Bool) (i t x o : List Bool) :
    TM2.step maquinaSig.m (⟨some 0, v, pilas (true :: i) t x o⟩ : CE) =
      some ⟨some 0, some true, pilas i (false :: t) x o⟩ := by
  show some (stepAux (maquinaSig.m 0) v (pilas (true :: i) t x o)) = _
  simp [maquinaSig, stepAux, pilas, upd0, upd1]

theorem pasoA_false (v : Option Bool) (i t x o : List Bool) :
    TM2.step maquinaSig.m (⟨some 0, v, pilas (false :: i) t x o⟩ : CE) =
      some ⟨some 1, some false, pilas i (true :: t) x o⟩ := by
  show some (stepAux (maquinaSig.m 0) v (pilas (false :: i) t x o)) = _
  simp [maquinaSig, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : Option Bool) (t x o : List Bool) :
    TM2.step maquinaSig.m (⟨some 0, v, pilas [] t x o⟩ : CE) =
      some ⟨some 2, none, pilas [] (false :: t) x o⟩ := by
  show some (stepAux (maquinaSig.m 0) v (pilas [] t x o)) = _
  simp [maquinaSig, stepAux, pilas, upd0, upd1]

theorem pasoB_bit (v : Option Bool) (c : Bool) (i t x o : List Bool) :
    TM2.step maquinaSig.m (⟨some 1, v, pilas (c :: i) t x o⟩ : CE) =
      some ⟨some 1, some c, pilas i (c :: t) x o⟩ := by
  show some (stepAux (maquinaSig.m 1) v (pilas (c :: i) t x o)) = _
  simp [maquinaSig, stepAux, pilas, upd0, upd1]

theorem pasoB_fin (v : Option Bool) (t x o : List Bool) :
    TM2.step maquinaSig.m (⟨some 1, v, pilas [] t x o⟩ : CE) = some ⟨some 2, none, pilas [] t x o⟩ := by
  show some (stepAux (maquinaSig.m 1) v (pilas [] t x o)) = _
  simp [maquinaSig, stepAux, pilas, upd0]

theorem bucleB (x o : List Bool) : ∀ (i t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaSig.m) (i.length + 1)
      (⟨some 1, v, pilas i t x o⟩ : CE) ⟨some 2, none, pilas [] (i.reverse ++ t) x o⟩
  | [], t, v => Llega.uno (pasoB_fin v t x o)
  | c :: i, t, v => by
    have := (Llega.uno (pasoB_bit v c i t x o)).trans (bucleB x o i (c :: t) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

/-- Cuántos pasos tardan los bucles A y B. -/
def pasosA : List Bool → ℕ
  | [] => 1
  | false :: bs => (bs.length + 1) + 1
  | true :: bs => pasosA bs + 1

theorem pasosA_le : ∀ s : List Bool, pasosA s ≤ s.length + 1
  | [] => by simp [pasosA]
  | false :: bs => by simp [pasosA]
  | true :: bs => by have := pasosA_le bs; simp [pasosA]; omega

/-- **Bucles A y B.** Dejan `sig s`, al revés, en la auxiliar. -/
theorem bucleA (x o : List Bool) : ∀ (s t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaSig.m) (pasosA s)
      (⟨some 0, v, pilas s t x o⟩ : CE) ⟨some 2, none, pilas [] ((sig s).reverse ++ t) x o⟩
  | [], t, v => by
    have := Llega.uno (pasoA_fin v t x o)
    simpa [sig, pasosA] using this
  | false :: bs, t, v => by
    have := (Llega.uno (pasoA_false v bs t x o)).trans (bucleB x o bs (true :: t) (some false))
    simpa [sig, pasosA, List.reverse_cons, List.append_assoc] using this
  | true :: bs, t, v => by
    have := (Llega.uno (pasoA_true v bs t x o)).trans (bucleA x o bs (false :: t) (some true))
    simpa [sig, pasosA, List.reverse_cons, List.append_assoc] using this

theorem pasoC_bit (v : Option Bool) (c : Bool) (t x o : List Bool) :
    TM2.step maquinaSig.m (⟨some 2, v, pilas [] (c :: t) x o⟩ : CE) =
      some ⟨some 2, some c, pilas [] t x (c :: o)⟩ := by
  show some (stepAux (maquinaSig.m 2) v (pilas [] (c :: t) x o)) = _
  simp [maquinaSig, stepAux, pilas, upd1, upd3]

theorem pasoC_fin (v : Option Bool) (x o : List Bool) :
    TM2.step maquinaSig.m (⟨some 2, v, pilas [] [] x o⟩ : CE) = some ⟨none, none, pilas [] [] x o⟩ := by
  show some (stepAux (maquinaSig.m 2) v (pilas [] [] x o)) = _
  simp [maquinaSig, stepAux, pilas, upd1]

theorem bucleC (x : List Bool) : ∀ (t o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaSig.m) (t.length + 1)
      (⟨some 2, v, pilas [] t x o⟩ : CE) ⟨none, none, pilas [] [] x (t.reverse ++ o)⟩
  | [], o, v => Llega.uno (pasoC_fin v x o)
  | c :: t, o, v => by
    have := (Llega.uno (pasoC_bit v c t x o)).trans (bucleC x t (c :: o) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem init (inp : List Bool) : (initList maquinaSig inp : CE) = ⟨some 0, none, pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaSig inp).stk⟩ : CE) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) : (haltList maquinaSig out : CE) = ⟨none, none, pilas [] [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaSig out).stk⟩ : CE) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem sig_length_le : ∀ s : List Bool, (sig s).length ≤ s.length + 1
  | [] => by simp [sig]
  | false :: bs => by simp [sig]
  | true :: bs => by have := sig_length_le bs; simp [sig]; omega

/-- **La corrida**: de `s` a `sig s`. -/
theorem corrida (s : List Bool) :
    Llega (TM2.step maquinaSig.m) (((sig s).length + 1) + pasosA s)
      (initList maquinaSig s : CE) (haltList maquinaSig (sig s)) := by
  have a := bucleA [] [] s [] none
  have c := bucleC [] ((sig s).reverse ++ []) [] none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at a c
  rw [init, halt]
  exact a.trans c

end Sig

open Polynomial in
/-- La cadena siguiente se calcula en tiempo polinomial. -/
noncomputable def sigComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool)).encode
      (CodBits.toEncoding (α := List Bool)).encode sig where
  tm := maquinaSig
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * X + 3
  outputsFun s := by
    have run := Sig.corrida s
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := List Bool)).encode s) = s := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := List Bool)).encode (sig s)) =
        sig s := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := List Bool)).encode s).length = s.length := rfl
    have h1 := Sig.pasosA_le s
    have h2 := Sig.sig_length_le s
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_mul, eval_X, eval_ofNat]; omega⟩

theorem esPolinomial_sig : EsPolinomial sig := ⟨sigComputable⟩

/-! ## 4. Dos piezas que salen por composición -/

/-- La segunda proyección: intercambiar y tomar la primera. -/
theorem esPolinomial_snd {α β : Type} [CodBits α] [CodBits β] : EsPolinomial (Prod.snd : α × β → β) :=
  Componer.esPolinomial_comp (fun q : α × β => (q.2, q.1)) Prod.fst Pares.esPolinomial_swap
    Basicas.esPolinomial_fst

/-- La disyunción de dos bits, por De Morgan: `a || b = !(!a && !b)`. -/
theorem esPolinomial_o : EsPolinomial (fun q : Bool × Bool => q.1 || q.2) := by
  have hno := Basicas.esPolinomial_no
  have h1 : EsPolinomial (fun q : Bool × Bool => !q.1) :=
    Componer.esPolinomial_comp Prod.fst _ Basicas.esPolinomial_fst hno
  have h2 : EsPolinomial (fun q : Bool × Bool => !q.2) :=
    Componer.esPolinomial_comp Prod.snd _ esPolinomial_snd hno
  have h3 := Primero.esPolinomial_pares _ _ h1 h2
  have h4 := Componer.esPolinomial_comp _ _ h3 Basicas.esPolinomial_y
  have h5 := Componer.esPolinomial_comp _ _ h4 hno
  have : (fun q : Bool × Bool => q.1 || q.2) =
      ((fun b : Bool => !b) ∘ ((fun q : Bool × Bool => q.1 && q.2) ∘ fun q : Bool × Bool => (!q.1, !q.2))) := by
    funext q
    obtain ⟨a, b⟩ := q
    cases a <;> cases b <;> rfl
  rw [this]
  exact h5

/-! ## 5. Comparar largos

De `delimita t ++ r` a un bit: ¿`t` es más corta que `r`? La máquina pasa `t` a la auxiliar y después saca un
símbolo de cada una hasta que alguna se acabe. -/

/-- ¿La primera lista es más corta que la segunda? -/
def menor : List Bool → List Bool → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | _ :: t, _ :: r => menor t r

theorem menor_eq : ∀ t r : List Bool, menor t r = decide (t.length < r.length)
  | [], [] => by simp [menor]
  | [], _ :: _ => by simp [menor]
  | _ :: _, [] => by simp [menor]
  | _ :: t, _ :: r => by simp [menor, menor_eq t r]

/-- El estado: la respuesta y los dos símbolos que se están comparando. -/
abbrev EstM : Type := Bool × Option Bool × Option Bool

/-- La configuración de la máquina que compara largos. -/
abbrev CM : Type := TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 4) EstM

/-- El final común: escribe la respuesta, deja el estado como al inicio y se detiene. -/
def finM : TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 4) EstM :=
  push 3 (fun v => v.1) (load (fun _ => (false, none, none)) halt)

/-- La máquina que compara largos. -/
@[reducible] def maquinaMenor : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := EstM
  initialState := (false, none, none)
  m := fun
    | 0 => pop 0 (fun v o => (v.1, o, none))
        (branch (fun v => v.2.1 == some true)
          (pop 0 (fun v o => (v.1, o, none)) (push 1 (fun v => v.2.1.getD false) (goto fun _ => 0)))
          (goto fun _ => 1))
    | 1 => pop 1 (fun v o => (v.1, o, none))
        (pop 0 (fun v o => (v.1, v.2.1, o))
          (branch (fun v => v.2.1.isSome)
            (branch (fun v => v.2.2.isSome) (goto fun _ => 1)
              (load (fun _ => (false, none, none)) (goto fun _ => 3)))
            (branch (fun v => v.2.2.isSome)
              (load (fun _ => (true, none, none)) (goto fun _ => 2))
              (load (fun _ => (false, none, none)) finM))))
    | 2 => pop 0 (fun v o => (v.1, o, none)) (branch (fun v => v.2.1.isSome) (goto fun _ => 2) finM)
    | _ => pop 1 (fun v o => (v.1, o, none)) (branch (fun v => v.2.1.isSome) (goto fun _ => 3) finM)

namespace Menor

/-- La configuración final, con la respuesta en la salida. -/
abbrev final (b : Bool) : CM := ⟨none, (false, none, none), pilas [] [] [] [b]⟩

theorem pasoA_bit (v : EstM) (b : Bool) (r t : List Bool) :
    TM2.step maquinaMenor.m (⟨some 0, v, pilas (true :: b :: r) t [] []⟩ : CM) =
      some ⟨some 0, (v.1, some b, none), pilas r (b :: t) [] []⟩ := by
  show some (stepAux (maquinaMenor.m 0) v (pilas (true :: b :: r) t [] [])) = _
  simp [maquinaMenor, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : EstM) (r t : List Bool) :
    TM2.step maquinaMenor.m (⟨some 0, v, pilas (false :: r) t [] []⟩ : CM) =
      some ⟨some 1, (v.1, some false, none), pilas r t [] []⟩ := by
  show some (stepAux (maquinaMenor.m 0) v (pilas (false :: r) t [] [])) = _
  simp [maquinaMenor, stepAux, pilas, upd0]

theorem bucleA (r : List Bool) : ∀ (u t : List Bool) (v : EstM),
    Llega (TM2.step maquinaMenor.m) (u.length + 1)
      (⟨some 0, v, pilas (CodBits.delimita u ++ r) t [] []⟩ : CM)
      ⟨some 1, (v.1, some false, none), pilas r (u.reverse ++ t) [] []⟩
  | [], t, v => Llega.uno (pasoA_fin v r t)
  | b :: u, t, v => by
    have h1 := Llega.uno (pasoA_bit v b (CodBits.delimita u ++ r) t)
    have := h1.trans (bucleA r u (b :: t) (v.1, some b, none))
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

theorem pasoD_bit (v : EstM) (c : Bool) (r : List Bool) :
    TM2.step maquinaMenor.m (⟨some 2, v, pilas (c :: r) [] [] []⟩ : CM) =
      some ⟨some 2, (v.1, some c, none), pilas r [] [] []⟩ := by
  show some (stepAux (maquinaMenor.m 2) v (pilas (c :: r) [] [] [])) = _
  simp [maquinaMenor, stepAux, pilas, upd0]

theorem pasoD_fin (v : EstM) :
    TM2.step maquinaMenor.m (⟨some 2, v, pilas [] [] [] []⟩ : CM) = some (final v.1) := by
  show some (stepAux (maquinaMenor.m 2) v (pilas [] [] [] [])) = _
  simp [maquinaMenor, finM, stepAux, pilas, upd0, upd3]

theorem bucleD : ∀ (r : List Bool) (v : EstM),
    Llega (TM2.step maquinaMenor.m) (r.length + 1) (⟨some 2, v, pilas r [] [] []⟩ : CM) (final v.1)
  | [], v => Llega.uno (pasoD_fin v)
  | c :: r, v => (Llega.uno (pasoD_bit v c r)).trans (bucleD r (v.1, some c, none))

theorem pasoE_bit (v : EstM) (c : Bool) (t : List Bool) :
    TM2.step maquinaMenor.m (⟨some 3, v, pilas [] (c :: t) [] []⟩ : CM) =
      some ⟨some 3, (v.1, some c, none), pilas [] t [] []⟩ := by
  show some (stepAux (maquinaMenor.m 3) v (pilas [] (c :: t) [] [])) = _
  simp [maquinaMenor, stepAux, pilas, upd1]

theorem pasoE_fin (v : EstM) :
    TM2.step maquinaMenor.m (⟨some 3, v, pilas [] [] [] []⟩ : CM) = some (final v.1) := by
  show some (stepAux (maquinaMenor.m 3) v (pilas [] [] [] [])) = _
  simp [maquinaMenor, finM, stepAux, pilas, upd1, upd3]

theorem bucleE : ∀ (t : List Bool) (v : EstM),
    Llega (TM2.step maquinaMenor.m) (t.length + 1) (⟨some 3, v, pilas [] t [] []⟩ : CM) (final v.1)
  | [], v => Llega.uno (pasoE_fin v)
  | c :: t, v => (Llega.uno (pasoE_bit v c t)).trans (bucleE t (v.1, some c, none))

/-- Cuántos pasos tarda la comparación, con lo que haya que vaciar después. -/
def pasosB : List Bool → List Bool → ℕ
  | [], [] => 1
  | [], _ :: r => (r.length + 1) + 1
  | _ :: t, [] => (t.length + 1) + 1
  | _ :: t, _ :: r => pasosB t r + 1

theorem pasosB_le : ∀ t r : List Bool, pasosB t r ≤ t.length + r.length + 2
  | [], [] => by simp [pasosB]
  | [], _ :: r => by simp [pasosB]
  | _ :: t, [] => by simp [pasosB]
  | _ :: t, _ :: r => by have := pasosB_le t r; simp [pasosB]; omega

theorem pasoB_ambos (g : Bool) (p q : Option Bool) (a b : Bool) (t r : List Bool) :
    TM2.step maquinaMenor.m (⟨some 1, (g, p, q), pilas (b :: r) (a :: t) [] []⟩ : CM) =
      some ⟨some 1, (g, some a, some b), pilas r t [] []⟩ := by
  show some (stepAux (maquinaMenor.m 1) (g, p, q) (pilas (b :: r) (a :: t) [] [])) = _
  simp [maquinaMenor, stepAux, pilas, upd0, upd1]

theorem pasoB_falta_t (g : Bool) (p q : Option Bool) (b : Bool) (r : List Bool) :
    TM2.step maquinaMenor.m (⟨some 1, (g, p, q), pilas (b :: r) [] [] []⟩ : CM) =
      some ⟨some 2, (true, none, none), pilas r [] [] []⟩ := by
  show some (stepAux (maquinaMenor.m 1) (g, p, q) (pilas (b :: r) [] [] [])) = _
  simp [maquinaMenor, stepAux, pilas, upd0, upd1]

theorem pasoB_falta_r (g : Bool) (p q : Option Bool) (a : Bool) (t : List Bool) :
    TM2.step maquinaMenor.m (⟨some 1, (g, p, q), pilas [] (a :: t) [] []⟩ : CM) =
      some ⟨some 3, (false, none, none), pilas [] t [] []⟩ := by
  show some (stepAux (maquinaMenor.m 1) (g, p, q) (pilas [] (a :: t) [] [])) = _
  simp [maquinaMenor, stepAux, pilas, upd0, upd1]

theorem pasoB_fin (g : Bool) (p q : Option Bool) :
    TM2.step maquinaMenor.m (⟨some 1, (g, p, q), pilas [] [] [] []⟩ : CM) = some (final false) := by
  show some (stepAux (maquinaMenor.m 1) (g, p, q) (pilas [] [] [] [])) = _
  simp [maquinaMenor, finM, stepAux, pilas, upd0, upd1, upd3]

/-- **Bucle B.** La máquina termina con `menor t r` en la salida. -/
theorem bucleB : ∀ (t r : List Bool) (g : Bool) (p q : Option Bool),
    Llega (TM2.step maquinaMenor.m) (pasosB t r)
      (⟨some 1, (g, p, q), pilas r t [] []⟩ : CM) (final (menor t r))
  | [], [], g, p, q => Llega.uno (pasoB_fin g p q)
  | [], b :: r, g, p, q => (Llega.uno (pasoB_falta_t g p q b r)).trans (bucleD r (true, none, none))
  | a :: t, [], g, p, q => (Llega.uno (pasoB_falta_r g p q a t)).trans (bucleE t (false, none, none))
  | a :: t, b :: r, g, p, q => (Llega.uno (pasoB_ambos g p q a b t r)).trans (bucleB t r g (some a) (some b))

theorem init (inp : List Bool) :
    (initList maquinaMenor inp : CM) = ⟨some 0, (false, none, none), pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaMenor inp).stk⟩ : CM) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) :
    (haltList maquinaMenor out : CM) = ⟨none, (false, none, none), pilas [] [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaMenor out).stk⟩ : CM) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

/-- **La corrida**: de `delimita t ++ r` al bit «`t` es más corta que `r`». -/
theorem corrida (t r : List Bool) :
    Llega (TM2.step maquinaMenor.m) (pasosB t.reverse r + (t.length + 1))
      (initList maquinaMenor (CodBits.delimita t ++ r) : CM)
      (haltList maquinaMenor [decide (t.length < r.length)]) := by
  have a := bucleA r t [] (false, none, none)
  have b := bucleB (t.reverse ++ []) r false (some false) none
  simp only [List.append_nil] at a b
  rw [menor_eq, List.length_reverse] at b
  rw [init, halt]
  exact a.trans b

end Menor

open Polynomial in
/-- Comparar los largos de dos cadenas se calcula en tiempo polinomial. -/
noncomputable def menorComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool × List Bool)).encode
      (CodBits.toEncoding (α := Bool)).encode
      (fun q : List Bool × List Bool => decide (q.1.length < q.2.length)) where
  tm := maquinaMenor
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := X + 2
  outputsFun q := by
    have run := Menor.corrida q.1 q.2
    have hin : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool × List Bool)).encode q) = CodBits.delimita q.1 ++ q.2 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := Bool)).encode (decide (q.1.length < q.2.length))) =
        [decide (q.1.length < q.2.length)] := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := List Bool × List Bool)).encode q).length =
        2 * q.1.length + 1 + q.2.length := by
      show (CodBits.delimita q.1 ++ q.2).length = _
      rw [List.length_append, Basicas.delimita_length]
    have hB := Menor.pasosB_le q.1.reverse q.2
    rw [List.length_reverse] at hB
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_X, eval_ofNat]; omega⟩

theorem esPolinomial_menor :
    EsPolinomial (fun q : List Bool × List Bool => decide (q.1.length < q.2.length)) := ⟨menorComputable⟩

/-! ## 6. Elegir entre dos cadenas

De `(b, (u, w))` a `u` si `b`, y a `w` si no. La entrada trae `true, b, false` y después `delimita u ++ w`.

* **0**: lee `b`.
* **A**: pasa `u` a la auxiliar; queda al revés. En la entrada queda `w`.
* si `b`: vacía la entrada (**D1**) y pasa la auxiliar a la salida (**C**).
* si no: vacía la auxiliar (**D2**), pasa la entrada a la auxiliar (**B**) y de ahí a la salida (**C**).
-/

/-- La configuración de la máquina que elige. -/
abbrev CS : Type := TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 6) (Bool × Option Bool)

/-- La máquina que elige. -/
@[reducible] def maquinaSi : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 6
  main := 0
  σ := Bool × Option Bool
  initialState := (false, none)
  m := fun
    | 0 => pop 0 (fun v _ => v) (pop 0 (fun v o => (o.getD false, v.2)) (pop 0 (fun v _ => v) (goto fun _ => 1)))
    | 1 => pop 0 (fun v o => (v.1, o))
        (branch (fun v => v.2 == some true)
          (pop 0 (fun v o => (v.1, o)) (push 1 (fun v => v.2.getD false) (goto fun _ => 1)))
          (branch (fun v => v.1) (goto fun _ => 2) (goto fun _ => 3)))
    | 2 => pop 0 (fun v o => (v.1, o)) (branch (fun v => v.2.isSome) (goto fun _ => 2) (goto fun _ => 5))
    | 3 => pop 1 (fun v o => (v.1, o)) (branch (fun v => v.2.isSome) (goto fun _ => 3) (goto fun _ => 4))
    | 4 => pop 0 (fun v o => (v.1, o))
        (branch (fun v => v.2.isSome) (push 1 (fun v => v.2.getD false) (goto fun _ => 4)) (goto fun _ => 5))
    | _ => pop 1 (fun v o => (v.1, o))
        (branch (fun v => v.2.isSome) (push 3 (fun v => v.2.getD false) (goto fun _ => 5))
          (load (fun _ => (false, none)) halt))

namespace Si

theorem paso0 (v : Bool × Option Bool) (b : Bool) (r : List Bool) :
    TM2.step maquinaSi.m (⟨some 0, v, pilas (true :: b :: false :: r) [] [] []⟩ : CS) =
      some ⟨some 1, (b, v.2), pilas r [] [] []⟩ := by
  show some (stepAux (maquinaSi.m 0) v (pilas (true :: b :: false :: r) [] [] [])) = _
  simp [maquinaSi, stepAux, pilas, upd0]

theorem pasoA_bit (b : Bool) (p : Option Bool) (c : Bool) (r t : List Bool) :
    TM2.step maquinaSi.m (⟨some 1, (b, p), pilas (true :: c :: r) t [] []⟩ : CS) =
      some ⟨some 1, (b, some c), pilas r (c :: t) [] []⟩ := by
  show some (stepAux (maquinaSi.m 1) (b, p) (pilas (true :: c :: r) t [] [])) = _
  simp [maquinaSi, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (b : Bool) (p : Option Bool) (r t : List Bool) :
    TM2.step maquinaSi.m (⟨some 1, (b, p), pilas (false :: r) t [] []⟩ : CS) =
      some ⟨some (if b then 2 else 3), (b, some false), pilas r t [] []⟩ := by
  show some (stepAux (maquinaSi.m 1) (b, p) (pilas (false :: r) t [] [])) = _
  cases b <;> simp [maquinaSi, stepAux, pilas, upd0]

theorem bucleA (b : Bool) (w : List Bool) : ∀ (u t : List Bool) (p : Option Bool),
    Llega (TM2.step maquinaSi.m) (u.length + 1)
      (⟨some 1, (b, p), pilas (CodBits.delimita u ++ w) t [] []⟩ : CS)
      ⟨some (if b then 2 else 3), (b, some false), pilas w (u.reverse ++ t) [] []⟩
  | [], t, p => Llega.uno (pasoA_fin b p w t)
  | c :: u, t, p => by
    have h1 := Llega.uno (pasoA_bit b p c (CodBits.delimita u ++ w) t)
    have := h1.trans (bucleA b w u (c :: t) (some c))
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

theorem pasoD1_bit (b : Bool) (p : Option Bool) (c : Bool) (i t : List Bool) :
    TM2.step maquinaSi.m (⟨some 2, (b, p), pilas (c :: i) t [] []⟩ : CS) =
      some ⟨some 2, (b, some c), pilas i t [] []⟩ := by
  show some (stepAux (maquinaSi.m 2) (b, p) (pilas (c :: i) t [] [])) = _
  simp [maquinaSi, stepAux, pilas, upd0]

theorem pasoD1_fin (b : Bool) (p : Option Bool) (t : List Bool) :
    TM2.step maquinaSi.m (⟨some 2, (b, p), pilas [] t [] []⟩ : CS) = some ⟨some 5, (b, none), pilas [] t [] []⟩ := by
  show some (stepAux (maquinaSi.m 2) (b, p) (pilas [] t [] [])) = _
  simp [maquinaSi, stepAux, pilas, upd0]

theorem bucleD1 (b : Bool) (t : List Bool) : ∀ (i : List Bool) (p : Option Bool),
    Llega (TM2.step maquinaSi.m) (i.length + 1)
      (⟨some 2, (b, p), pilas i t [] []⟩ : CS) ⟨some 5, (b, none), pilas [] t [] []⟩
  | [], p => Llega.uno (pasoD1_fin b p t)
  | c :: i, p => (Llega.uno (pasoD1_bit b p c i t)).trans (bucleD1 b t i (some c))

theorem pasoD2_bit (b : Bool) (p : Option Bool) (c : Bool) (i t : List Bool) :
    TM2.step maquinaSi.m (⟨some 3, (b, p), pilas i (c :: t) [] []⟩ : CS) =
      some ⟨some 3, (b, some c), pilas i t [] []⟩ := by
  show some (stepAux (maquinaSi.m 3) (b, p) (pilas i (c :: t) [] [])) = _
  simp [maquinaSi, stepAux, pilas, upd1]

theorem pasoD2_fin (b : Bool) (p : Option Bool) (i : List Bool) :
    TM2.step maquinaSi.m (⟨some 3, (b, p), pilas i [] [] []⟩ : CS) = some ⟨some 4, (b, none), pilas i [] [] []⟩ := by
  show some (stepAux (maquinaSi.m 3) (b, p) (pilas i [] [] [])) = _
  simp [maquinaSi, stepAux, pilas, upd1]

theorem bucleD2 (b : Bool) (i : List Bool) : ∀ (t : List Bool) (p : Option Bool),
    Llega (TM2.step maquinaSi.m) (t.length + 1)
      (⟨some 3, (b, p), pilas i t [] []⟩ : CS) ⟨some 4, (b, none), pilas i [] [] []⟩
  | [], p => Llega.uno (pasoD2_fin b p i)
  | c :: t, p => (Llega.uno (pasoD2_bit b p c i t)).trans (bucleD2 b i t (some c))

theorem pasoB_bit (b : Bool) (p : Option Bool) (c : Bool) (i t : List Bool) :
    TM2.step maquinaSi.m (⟨some 4, (b, p), pilas (c :: i) t [] []⟩ : CS) =
      some ⟨some 4, (b, some c), pilas i (c :: t) [] []⟩ := by
  show some (stepAux (maquinaSi.m 4) (b, p) (pilas (c :: i) t [] [])) = _
  simp [maquinaSi, stepAux, pilas, upd0, upd1]

theorem pasoB_fin (b : Bool) (p : Option Bool) (t : List Bool) :
    TM2.step maquinaSi.m (⟨some 4, (b, p), pilas [] t [] []⟩ : CS) = some ⟨some 5, (b, none), pilas [] t [] []⟩ := by
  show some (stepAux (maquinaSi.m 4) (b, p) (pilas [] t [] [])) = _
  simp [maquinaSi, stepAux, pilas, upd0]

theorem bucleB (b : Bool) : ∀ (i t : List Bool) (p : Option Bool),
    Llega (TM2.step maquinaSi.m) (i.length + 1)
      (⟨some 4, (b, p), pilas i t [] []⟩ : CS) ⟨some 5, (b, none), pilas [] (i.reverse ++ t) [] []⟩
  | [], t, p => Llega.uno (pasoB_fin b p t)
  | c :: i, t, p => by
    have := (Llega.uno (pasoB_bit b p c i t)).trans (bucleB b i (c :: t) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem pasoC_bit (b : Bool) (p : Option Bool) (c : Bool) (t o : List Bool) :
    TM2.step maquinaSi.m (⟨some 5, (b, p), pilas [] (c :: t) [] o⟩ : CS) =
      some ⟨some 5, (b, some c), pilas [] t [] (c :: o)⟩ := by
  show some (stepAux (maquinaSi.m 5) (b, p) (pilas [] (c :: t) [] o)) = _
  simp [maquinaSi, stepAux, pilas, upd1, upd3]

theorem pasoC_fin (b : Bool) (p : Option Bool) (o : List Bool) :
    TM2.step maquinaSi.m (⟨some 5, (b, p), pilas [] [] [] o⟩ : CS) = some ⟨none, (false, none), pilas [] [] [] o⟩ := by
  show some (stepAux (maquinaSi.m 5) (b, p) (pilas [] [] [] o)) = _
  simp [maquinaSi, stepAux, pilas, upd1]

theorem bucleC (b : Bool) : ∀ (t o : List Bool) (p : Option Bool),
    Llega (TM2.step maquinaSi.m) (t.length + 1)
      (⟨some 5, (b, p), pilas [] t [] o⟩ : CS) ⟨none, (false, none), pilas [] [] [] (t.reverse ++ o)⟩
  | [], o, p => Llega.uno (pasoC_fin b p o)
  | c :: t, o, p => by
    have := (Llega.uno (pasoC_bit b p c t o)).trans (bucleC b t (c :: o) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem init (inp : List Bool) : (initList maquinaSi inp : CS) = ⟨some 0, (false, none), pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaSi inp).stk⟩ : CS) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) : (haltList maquinaSi out : CS) = ⟨none, (false, none), pilas [] [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaSi out).stk⟩ : CS) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

/-- Cuántos pasos tarda, según el bit. -/
def pasos (b : Bool) (u w : List Bool) : ℕ :=
  if b then (u.length + 1) + ((w.length + 1) + ((u.length + 1) + 1))
  else (w.length + 1) + ((w.length + 1) + ((u.length + 1) + ((u.length + 1) + 1)))

theorem pasos_le (b : Bool) (u w : List Bool) : pasos b u w ≤ 2 * u.length + 2 * w.length + 5 := by
  unfold pasos
  split_ifs <;> omega

/-- **La corrida**: de `true, b, false, delimita u ++ w` a `u` o a `w`, según `b`. -/
theorem corrida (b : Bool) (u w : List Bool) :
    Llega (TM2.step maquinaSi.m) (pasos b u w)
      (initList maquinaSi (true :: b :: false :: (CodBits.delimita u ++ w)) : CS)
      (haltList maquinaSi (if b then u else w)) := by
  have z := Llega.uno (paso0 (false, none) b (CodBits.delimita u ++ w))
  have a := bucleA b w u [] none
  rw [init, halt]
  cases b with
  | true =>
    have d := bucleD1 true (u.reverse ++ []) w (some false)
    have c := bucleC true (u.reverse ++ []) [] none
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at a d c
    exact ((z.trans a).trans d).trans c
  | false =>
    have d := bucleD2 false w (u.reverse ++ []) (some false)
    have b' := bucleB false w [] none
    have c := bucleC false (w.reverse ++ []) [] none
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at a d b' c
    exact (((z.trans a).trans d).trans b').trans c

end Si

open Polynomial in
/-- Elegir entre dos cadenas se calcula en tiempo polinomial. -/
noncomputable def siComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := Bool × (List Bool × List Bool))).encode
      (CodBits.toEncoding (α := List Bool)).encode
      (fun q : Bool × (List Bool × List Bool) => if q.1 then q.2.1 else q.2.2) where
  tm := maquinaSi
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * X
  outputsFun q := by
    have run := Si.corrida q.1 q.2.1 q.2.2
    have hn := Si.pasos_le q.1 q.2.1 q.2.2
    have hin : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := Bool × (List Bool × List Bool))).encode q) =
        true :: q.1 :: false :: (CodBits.delimita q.2.1 ++ q.2.2) := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool)).encode (if q.1 then q.2.1 else q.2.2)) =
        (if q.1 then q.2.1 else q.2.2) := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := Bool × (List Bool × List Bool))).encode q).length =
        2 * q.2.1.length + q.2.2.length + 4 := by
      show (true :: q.1 :: false :: (CodBits.delimita q.2.1 ++ q.2.2)).length = _
      simp only [List.length_cons, List.length_append, Basicas.delimita_length]
      omega
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_mul, eval_X, eval_ofNat]; omega⟩

theorem esPolinomial_si :
    EsPolinomial (fun q : Bool × (List Bool × List Bool) => if q.1 then q.2.1 else q.2.2) := ⟨siComputable⟩

/-! ## 7. Escribir el costo

De `(t, s)` a `costoBits |t| s`: el complemento de `s`, un cero, tantos unos como le falten a `s` para llegar al
largo de `t`, y un uno. La entrada trae `delimita t ++ s`.

* **A**: pasa `t` a la auxiliar (1). Solo importa su largo.
* **B**: por cada bit de `s`, gasta un símbolo de la auxiliar y pone el complemento en la pila 2. Al acabarse `s`,
  pone el cero.
* **C**: por cada símbolo que quede en la auxiliar pone un uno; al final, uno más.
* **D**: pasa la pila 2 a la salida. Estaba al revés, y este traspaso la endereza.
-/

/-- La máquina que escribe el costo. -/
@[reducible] def maquinaCosto : FinTM2 where
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
    | 1 => pop 0 (fun _ o => o)
        (branch (fun v => v.isSome)
          (pop 1 (fun v _ => v) (push 2 (fun v => !(v.getD false)) (goto fun _ => 1)))
          (push 2 (fun _ => false) (goto fun _ => 2)))
    | 2 => pop 1 (fun _ o => o)
        (branch (fun v => v.isSome) (push 2 (fun _ => true) (goto fun _ => 2))
          (push 2 (fun _ => true) (goto fun _ => 3)))
    | _ => pop 2 (fun _ o => o)
        (branch (fun v => v.isSome) (push 3 (fun v => v.getD false) (goto fun _ => 3)) halt)

namespace Costo

theorem pasoA_bit (v : Option Bool) (b : Bool) (r t : List Bool) :
    TM2.step maquinaCosto.m (⟨some 0, v, pilas (true :: b :: r) t [] []⟩ : CE) =
      some ⟨some 0, some b, pilas r (b :: t) [] []⟩ := by
  show some (stepAux (maquinaCosto.m 0) v (pilas (true :: b :: r) t [] [])) = _
  simp [maquinaCosto, stepAux, pilas, upd0, upd1]

theorem pasoA_fin (v : Option Bool) (r t : List Bool) :
    TM2.step maquinaCosto.m (⟨some 0, v, pilas (false :: r) t [] []⟩ : CE) =
      some ⟨some 1, some false, pilas r t [] []⟩ := by
  show some (stepAux (maquinaCosto.m 0) v (pilas (false :: r) t [] [])) = _
  simp [maquinaCosto, stepAux, pilas, upd0]

theorem bucleA (r : List Bool) : ∀ (u t : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaCosto.m) (u.length + 1)
      (⟨some 0, v, pilas (CodBits.delimita u ++ r) t [] []⟩ : CE)
      ⟨some 1, some false, pilas r (u.reverse ++ t) [] []⟩
  | [], t, v => Llega.uno (pasoA_fin v r t)
  | b :: u, t, v => by
    have h1 := Llega.uno (pasoA_bit v b (CodBits.delimita u ++ r) t)
    have := h1.trans (bucleA r u (b :: t) (some b))
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

theorem pasoB_bit (v : Option Bool) (c : Bool) (s t x : List Bool) :
    TM2.step maquinaCosto.m (⟨some 1, v, pilas (c :: s) t x []⟩ : CE) =
      some ⟨some 1, some c, pilas s t.tail ((!c) :: x) []⟩ := by
  show some (stepAux (maquinaCosto.m 1) v (pilas (c :: s) t x [])) = _
  simp [maquinaCosto, stepAux, pilas, upd0, upd1, upd2]

theorem pasoB_fin (v : Option Bool) (t x : List Bool) :
    TM2.step maquinaCosto.m (⟨some 1, v, pilas [] t x []⟩ : CE) =
      some ⟨some 2, none, pilas [] t (false :: x) []⟩ := by
  show some (stepAux (maquinaCosto.m 1) v (pilas [] t x [])) = _
  simp [maquinaCosto, stepAux, pilas, upd0, upd2]

theorem tail_drop (t : List Bool) (n : ℕ) : t.tail.drop n = t.drop (n + 1) := by
  cases t <;> simp

theorem bucleB : ∀ (s t x : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaCosto.m) (s.length + 1)
      (⟨some 1, v, pilas s t x []⟩ : CE)
      ⟨some 2, none, pilas [] (t.drop s.length) (false :: ((s.map not).reverse ++ x)) []⟩
  | [], t, x, v => by
    have := Llega.uno (pasoB_fin v t x)
    simpa using this
  | c :: s, t, x, v => by
    have := (Llega.uno (pasoB_bit v c s t x)).trans (bucleB s t.tail ((!c) :: x) (some c))
    simpa [tail_drop, List.reverse_cons, List.append_assoc] using this

theorem pasoC_bit (v : Option Bool) (c : Bool) (t x : List Bool) :
    TM2.step maquinaCosto.m (⟨some 2, v, pilas [] (c :: t) x []⟩ : CE) =
      some ⟨some 2, some c, pilas [] t (true :: x) []⟩ := by
  show some (stepAux (maquinaCosto.m 2) v (pilas [] (c :: t) x [])) = _
  simp [maquinaCosto, stepAux, pilas, upd1, upd2]

theorem pasoC_fin (v : Option Bool) (x : List Bool) :
    TM2.step maquinaCosto.m (⟨some 2, v, pilas [] [] x []⟩ : CE) =
      some ⟨some 3, none, pilas [] [] (true :: x) []⟩ := by
  show some (stepAux (maquinaCosto.m 2) v (pilas [] [] x [])) = _
  simp [maquinaCosto, stepAux, pilas, upd1, upd2]

theorem rep_cons (n : ℕ) (l : List Bool) :
    List.replicate n true ++ true :: l = List.replicate (n + 1) true ++ l := by
  rw [List.replicate_succ']
  simp

theorem bucleC : ∀ (t x : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaCosto.m) (t.length + 1)
      (⟨some 2, v, pilas [] t x []⟩ : CE)
      ⟨some 3, none, pilas [] [] (true :: (List.replicate t.length true ++ x)) []⟩
  | [], x, v => by
    have := Llega.uno (pasoC_fin v x)
    simpa using this
  | c :: t, x, v => by
    have := (Llega.uno (pasoC_bit v c t x)).trans (bucleC t (true :: x) (some c))
    rw [rep_cons] at this
    exact this

theorem pasoD_bit (v : Option Bool) (c : Bool) (x o : List Bool) :
    TM2.step maquinaCosto.m (⟨some 3, v, pilas [] [] (c :: x) o⟩ : CE) =
      some ⟨some 3, some c, pilas [] [] x (c :: o)⟩ := by
  show some (stepAux (maquinaCosto.m 3) v (pilas [] [] (c :: x) o)) = _
  simp [maquinaCosto, stepAux, pilas, upd2, upd3]

theorem pasoD_fin (v : Option Bool) (o : List Bool) :
    TM2.step maquinaCosto.m (⟨some 3, v, pilas [] [] [] o⟩ : CE) = some ⟨none, none, pilas [] [] [] o⟩ := by
  show some (stepAux (maquinaCosto.m 3) v (pilas [] [] [] o)) = _
  simp [maquinaCosto, stepAux, pilas, upd2]

theorem bucleD : ∀ (x o : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaCosto.m) (x.length + 1)
      (⟨some 3, v, pilas [] [] x o⟩ : CE) ⟨none, none, pilas [] [] [] (x.reverse ++ o)⟩
  | [], o, v => Llega.uno (pasoD_fin v o)
  | c :: x, o, v => by
    have := (Llega.uno (pasoD_bit v c x o)).trans (bucleD x (c :: o) (some c))
    simpa [List.reverse_cons, List.append_assoc] using this

theorem init (inp : List Bool) : (initList maquinaCosto inp : CE) = ⟨some 0, none, pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaCosto inp).stk⟩ : CE) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) : (haltList maquinaCosto out : CE) = ⟨none, none, pilas [] [] [] out⟩ := by
  show (⟨_, _, (haltList maquinaCosto out).stk⟩ : CE) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

/-- Lo que queda en la pila 2, enderezado, es `costoBits`. -/
theorem bits_final (j : ℕ) (s : List Bool) :
    (true :: (List.replicate j true ++ false :: (s.map not).reverse)).reverse =
      s.map not ++ false :: (List.replicate j true ++ [true]) := by
  simp [List.reverse_append]

/-- **La corrida**: de `delimita t ++ s` a `costoBits |t| s`. -/
theorem corrida (t s : List Bool) :
    Llega (TM2.step maquinaCosto.m)
      (((t.length - s.length) + (s.length + 1) + 1 + 1) +
        (((t.length - s.length) + 1) + ((s.length + 1) + (t.length + 1))))
      (initList maquinaCosto (CodBits.delimita t ++ s) : CE)
      (haltList maquinaCosto (costoBits t.length s)) := by
  have a := bucleA s t [] none
  have b := bucleB s (t.reverse ++ []) [] (some false)
  have c := bucleC ((t.reverse ++ []).drop s.length) (false :: ((s.map not).reverse ++ [])) none
  simp only [List.append_nil] at a b c
  have hj : (t.reverse.drop s.length).length = t.length - s.length := by simp
  rw [hj] at c
  have d := bucleD (true :: (List.replicate (t.length - s.length) true ++ false :: (s.map not).reverse)) [] none
  rw [List.append_nil, bits_final] at d
  have hlen : (true :: (List.replicate (t.length - s.length) true ++ false :: (s.map not).reverse)).length + 1 =
      (t.length - s.length) + (s.length + 1) + 1 + 1 := by
    simp
  rw [hlen] at d
  rw [init, halt]
  exact ((a.trans b).trans c).trans d

end Costo

open Polynomial in
/-- El costo, dada una vara `t` y la cadena `s`, se calcula en tiempo polinomial. -/
noncomputable def costoComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool × List Bool)).encode
      (CodBits.toEncoding (α := ℕ)).encode
      (fun q : List Bool × List Bool => val (costoBits q.1.length q.2)) where
  tm := maquinaCosto
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * X + 5
  outputsFun q := by
    have run := Costo.corrida q.1 q.2
    have hin : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool × List Bool)).encode q) = CodBits.delimita q.1 ++ q.2 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := ℕ)).encode (val (costoBits q.1.length q.2))) =
        costoBits q.1.length q.2 := by
      simp only [Equiv.refl]
      rw [List.map_id]
      exact encodeNat_val (canon_costoBits _ _)
    have hlen : ((CodBits.toEncoding (α := List Bool × List Bool)).encode q).length =
        2 * q.1.length + 1 + q.2.length := by
      show (CodBits.delimita q.1 ++ q.2).length = _
      rw [List.length_append, Basicas.delimita_length]
    rw [hin, hout]
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_mul, eval_X, eval_ofNat]; omega⟩

theorem esPolinomial_costo :
    EsPolinomial (fun q : List Bool × List Bool => val (costoBits q.1.length q.2)) := ⟨costoComputable⟩

/-! ## 8. El vecino y el costo, dada una vara

Una **vara** para la cota `M` es una función polinomial `tope` tal que el largo de `tope x` es `M x`. Con ella, el
vecino y el costo del descenso exhaustivo se arman por pares y composición de las piezas anteriores:

* vecino: `si (V q || menor (tope q.1, sig q.2), (q.2, sig q.2))`;
* costo: `costoBits` sobre `(tope q.1, q.2)`.
-/

section ConVara

variable (V : List Bool × List Bool → Bool) (tope : List Bool → List Bool)

/-- El descenso exhaustivo cuya cota es el largo de la vara. -/
abbrev exhaustivoVara : DescensoInstancia := exhaustivo V (fun x => (tope x).length)

theorem vecino_polinomial (hV : EsPolinomial V) (htope : EsPolinomial tope) :
    EsPolinomial (exhaustivoVara V tope).vecino := by
  have hcomp := @Componer.esPolinomial_comp
  have hpar := @Primero.esPolinomial_pares
  have hfst : EsPolinomial (Prod.fst : List Bool × List Bool → List Bool) := Basicas.esPolinomial_fst
  have hsnd : EsPolinomial (Prod.snd : List Bool × List Bool → List Bool) := esPolinomial_snd
  -- la vara de la instancia, y la cadena siguiente
  have h1 : EsPolinomial (fun q : List Bool × List Bool => tope q.1) := hcomp _ _ hfst htope
  have h2 : EsPolinomial (fun q : List Bool × List Bool => sig q.2) := hcomp _ _ hsnd esPolinomial_sig
  -- ¿la siguiente se pasa del largo?
  have h3 : EsPolinomial (fun q : List Bool × List Bool => decide ((tope q.1).length < (sig q.2).length)) :=
    hcomp _ _ (hpar _ _ h1 h2) esPolinomial_menor
  -- ¿hay que detenerse?
  have h4 : EsPolinomial (fun q : List Bool × List Bool =>
      V q || decide ((tope q.1).length < (sig q.2).length)) :=
    hcomp _ _ (hpar _ _ hV h3) esPolinomial_o
  -- las dos candidatas
  have h5 : EsPolinomial (fun q : List Bool × List Bool => (q.2, sig q.2)) := hpar _ _ hsnd h2
  have h6 := hcomp _ _ (hpar _ _ h4 h5) esPolinomial_si
  have : (exhaustivoVara V tope).vecino =
      ((fun q : Bool × (List Bool × List Bool) => if q.1 then q.2.1 else q.2.2) ∘
        fun q : List Bool × List Bool =>
          (V q || decide ((tope q.1).length < (sig q.2).length), (q.2, sig q.2))) := by
    funext q
    show (if V q = true ∨ (tope q.1).length < (sig q.2).length then q.2 else sig q.2) = _
    simp only [Function.comp_apply, Bool.or_eq_true, decide_eq_true_eq]
  rw [this]
  exact h6

theorem costo_polinomial (htope : EsPolinomial tope) : EsPolinomial (exhaustivoVara V tope).costo := by
  have hfst : EsPolinomial (Prod.fst : List Bool × List Bool → List Bool) := Basicas.esPolinomial_fst
  have hsnd : EsPolinomial (Prod.snd : List Bool × List Bool → List Bool) := esPolinomial_snd
  have h1 : EsPolinomial (fun q : List Bool × List Bool => tope q.1) :=
    Componer.esPolinomial_comp _ _ hfst htope
  have h2 := Primero.esPolinomial_pares _ _ h1 hsnd
  exact Componer.esPolinomial_comp (fun q : List Bool × List Bool => (tope q.1, q.2))
    (fun q : List Bool × List Bool => val (costoBits q.1.length q.2)) h2 esPolinomial_costo

/-- **El descenso exhaustivo es de tiempo polinomial**, dada una vara polinomial: su solución inicial, su vecino y
su costo. -/
theorem exhaustivo_polinomial (hV : EsPolinomial V) (htope : EsPolinomial tope) :
    EsPolinomial (exhaustivoVara V tope).inicial ∧ EsPolinomial (exhaustivoVara V tope).vecino ∧
      EsPolinomial (exhaustivoVara V tope).costo :=
  ⟨esPolinomial_vacia, vecino_polinomial V tope hV htope, costo_polinomial V tope htope⟩

end ConVara

/-- **NP por el algoritmo estándar de un descenso polinomial**, dada una vara. Si `L` tiene verificador polinomial
`V` con certificados de largo a lo sumo `p(|x|)`, y `tope` es una función polinomial con `|tope x| = p(|x|)`,
entonces el descenso `exhaustivoVara V tope` tiene solución inicial, vecino y costo polinomiales, y `x ∈ L` si y
solo si `V` acepta su destino. -/
theorem np_por_destino_polinomial {L : Problema} {p : Polynomial ℕ} {V : List Bool × List Bool → Bool}
    {tope : List Bool → List Bool} (hV : EsPolinomial V) (htope : EsPolinomial tope)
    (hlargo : ∀ x, (tope x).length = p.eval x.length)
    (hL : ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true) :
    (EsPolinomial (exhaustivoVara V tope).inicial ∧ EsPolinomial (exhaustivoVara V tope).vecino ∧
      EsPolinomial (exhaustivoVara V tope).costo) ∧
    ∀ x, L x = true ↔ V (x, (exhaustivoVara V tope).destino x) = true := by
  refine ⟨exhaustivo_polinomial V tope hV htope, fun x => ?_⟩
  rw [hL x, ← hlargo x]
  exact hay_certificado_iff V (fun x => (tope x).length) x

end ExhaustivoTiempo
end Sagitta.Map
