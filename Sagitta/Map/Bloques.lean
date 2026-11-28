import Sagitta.Map.Vara

/-!
# Bloques: piezas pequeñas de tiempo polinomial

Unas máquinas y lemas chicos sobre `Turing.FinTM2`, para armar funciones polinomiales sobre cadenas:

1. quitar el primer símbolo (`esPolinomial_cola`);
2. poner un `false` delante (`esPolinomial_ponerFalso`);
3. cambiar el tipo sin cambiar la codificación (`esPolinomial_retipo`, `esPolinomial_cod`);
4. leer un bloque autodelimitado de forma total (`leeTotal`, `esPolinomial_leeTotal`), con la máquina que decide
   si la entrada empieza con un bloque bien formado (`esPolinomial_bloqueValido`).
-/

open Computability Turing Turing.TM2 Turing.TM2.Stmt

namespace Sagitta.Map
namespace Bloques

open Componer (Llega)
open Comparar (pilas upd0)
open ExhaustivoTiempo (CE)

/-! ## 1. Quitar el primer símbolo -/

/-- La máquina que saca un símbolo, si lo hay, y se detiene. Tarda un paso. -/
@[reducible] def maquinaCola : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := pop () (fun _ _ => ()) halt

/-- Quitar el primer símbolo se calcula en tiempo polinomial (en un paso). -/
noncomputable def colaComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool)).encode
      (CodBits.toEncoding (α := List Bool)).encode (fun s : List Bool => s.tail) where
  tm := maquinaCola
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun s := by
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := List Bool)).encode s) = s := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool)).encode s.tail) = s.tail := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    rw [hin, hout]
    refine ⟨⟨1, ?_⟩, by simp⟩
    show some (stepAux (maquinaCola.m ()) () (initList maquinaCola s).stk) = some (haltList maquinaCola _)
    simp only [maquinaCola, stepAux, initList, haltList]
    congr 2

theorem esPolinomial_cola : EsPolinomial (fun s : List Bool => s.tail) := ⟨colaComputable⟩

/-! ## 2. Poner un `false` delante -/

/-- La máquina que pone un `false` delante de su entrada. Tarda un paso. -/
@[reducible] def maquinaPonerFalso : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := push () (fun _ => false) halt

/-- Poner un `false` delante se calcula en tiempo polinomial (en un paso). -/
noncomputable def ponerFalsoComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool)).encode
      (CodBits.toEncoding (α := List Bool)).encode (fun s : List Bool => false :: s) where
  tm := maquinaPonerFalso
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun s := by
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := List Bool)).encode s) = s := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := List Bool)).encode (false :: s)) = false :: s := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    rw [hin, hout]
    refine ⟨⟨1, ?_⟩, by simp⟩
    show some (stepAux (maquinaPonerFalso.m ()) () (initList maquinaPonerFalso s).stk) =
      some (haltList maquinaPonerFalso _)
    congr 1

theorem esPolinomial_ponerFalso : EsPolinomial (fun s : List Bool => false :: s) := ⟨ponerFalsoComputable⟩

/-! ## 3. Cambiar el tipo sin cambiar la codificación

`EsPolinomial` solo ve las codificaciones: si `f a` y `g a` se codifican igual, la misma máquina sirve para las
dos. -/

/-- Si `f` y `g` dan la misma cadena en cada entrada, `g` es polinomial cuando lo es `f`. -/
theorem esPolinomial_retipo {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] {f : α → β} {g : α → γ}
    (h : ∀ a, CodBits.cod (f a) = CodBits.cod (g a)) (hf : EsPolinomial f) : EsPolinomial g := by
  obtain ⟨hf⟩ := hf
  exact ⟨{
    tm := hf.tm
    inputAlphabet := hf.inputAlphabet
    outputAlphabet := hf.outputAlphabet
    time := hf.time
    outputsFun := fun a => by
      have e : (CodBits.toEncoding (α := γ)).encode (g a) = (CodBits.toEncoding (α := β)).encode (f a) :=
        (h a).symm
      rw [e]
      exact hf.outputsFun a }⟩

/-- Codificar es polinomial: como cadena de bits, el código de `a` se escribe como él mismo. -/
theorem esPolinomial_cod {α : Type} [CodBits α] : EsPolinomial (fun a : α => CodBits.cod a) :=
  esPolinomial_retipo (f := (id : α → α)) (fun _ => rfl) esPolinomial_id

/-! ## 4. Leer un bloque de forma total

`CodBits.lee` puede fallar; `leeTotal` devuelve `([], [])` en ese caso. El código de un par es
`delimita u ++ w`, así que `cod (leeTotal z)` es `z` mismo si la lectura sale bien, y `[false]` si no. Basta
entonces una máquina que decida si la lectura sale bien (`bloqueValido`) y elegir entre `z` y `[false]`.
-/

/-- Lee un bloque autodelimitado; si la entrada no empieza con uno, devuelve `([], [])`. -/
def leeTotal (z : List Bool) : List Bool × List Bool := (CodBits.lee z).getD ([], [])

/-- ¿La entrada empieza con un bloque autodelimitado bien formado? -/
def bloqueValido : List Bool → Bool := fun z => (CodBits.lee z).isSome

theorem cod_leeTotal_delimita (u w : List Bool) : leeTotal (CodBits.delimita u ++ w) = (u, w) := by
  simp [leeTotal]

/-- Lo que `lee` devuelve vuelve a armar la entrada. -/
theorem delimita_de_lee : ∀ (z : List Bool) {u w : List Bool}, CodBits.lee z = some (u, w) →
    CodBits.delimita u ++ w = z
  | [], _, _, h => by simp [CodBits.lee] at h
  | [true], _, _, h => by simp [CodBits.lee] at h
  | false :: r, u, w, h => by
    simp only [CodBits.lee, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | true :: b :: r, u, w, h => by
    simp only [CodBits.lee, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨p, q⟩, hp, rfl, rfl⟩ := h
    simp [CodBits.delimita, delimita_de_lee r hp]

theorem bloqueValido_nil : bloqueValido [] = false := by simp [bloqueValido, CodBits.lee]

theorem bloqueValido_true : bloqueValido [true] = false := by simp [bloqueValido, CodBits.lee]

theorem bloqueValido_false (r : List Bool) : bloqueValido (false :: r) = true := by
  simp [bloqueValido, CodBits.lee]

theorem bloqueValido_bit (b : Bool) (r : List Bool) : bloqueValido (true :: b :: r) = bloqueValido r := by
  simp [bloqueValido, CodBits.lee]

/-! ### La máquina que decide si hay un bloque

Una sola pila (0), que es entrada y salida.

* **0**: saca un símbolo. Con `true` (marca) pasa a 1; con `false` (cierre) el bloque está bien y pasa a 2; si la
  entrada se acabó, está mal y pasa a 3.
* **1**: saca el bit que sigue a la marca y vuelve a 0; si no hay, está mal y pasa a 3.
* **2**: vacía la entrada y escribe `true`.
* **3**: vacía la entrada y escribe `false`.

Para una entrada de `n` bits tarda a lo sumo `n + 2` pasos (`pasos_le`).
-/

/-- La máquina que decide si la entrada empieza con un bloque bien formado. -/
@[reducible] def maquinaBloque : FinTM2 where
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
        (branch (fun v => v == some true) (goto fun _ => 1)
          (branch (fun v => v.isSome) (goto fun _ => 2) (goto fun _ => 3)))
    | 1 => pop 0 (fun _ o => o) (branch (fun v => v.isSome) (goto fun _ => 0) (goto fun _ => 3))
    | 2 => pop 0 (fun _ o => o) (branch (fun v => v.isSome) (goto fun _ => 2) (push 0 (fun _ => true) halt))
    | _ => pop 0 (fun _ o => o) (branch (fun v => v.isSome) (goto fun _ => 3) (push 0 (fun _ => false) halt))

namespace Bloque

theorem paso0_marca (v : Option Bool) (r : List Bool) :
    TM2.step maquinaBloque.m (⟨some 0, v, pilas (true :: r) [] [] []⟩ : CE) =
      some ⟨some 1, some true, pilas r [] [] []⟩ := by
  show some (stepAux (maquinaBloque.m 0) v (pilas (true :: r) [] [] [])) = _
  simp [maquinaBloque, stepAux, pilas, upd0]

theorem paso0_cierre (v : Option Bool) (r : List Bool) :
    TM2.step maquinaBloque.m (⟨some 0, v, pilas (false :: r) [] [] []⟩ : CE) =
      some ⟨some 2, some false, pilas r [] [] []⟩ := by
  show some (stepAux (maquinaBloque.m 0) v (pilas (false :: r) [] [] [])) = _
  simp [maquinaBloque, stepAux, pilas, upd0]

theorem paso0_fin (v : Option Bool) :
    TM2.step maquinaBloque.m (⟨some 0, v, pilas [] [] [] []⟩ : CE) =
      some ⟨some 3, none, pilas [] [] [] []⟩ := by
  show some (stepAux (maquinaBloque.m 0) v (pilas [] [] [] [])) = _
  simp [maquinaBloque, stepAux, pilas, upd0]

theorem paso1_bit (v : Option Bool) (b : Bool) (r : List Bool) :
    TM2.step maquinaBloque.m (⟨some 1, v, pilas (b :: r) [] [] []⟩ : CE) =
      some ⟨some 0, some b, pilas r [] [] []⟩ := by
  show some (stepAux (maquinaBloque.m 1) v (pilas (b :: r) [] [] [])) = _
  simp [maquinaBloque, stepAux, pilas, upd0]

theorem paso1_fin (v : Option Bool) :
    TM2.step maquinaBloque.m (⟨some 1, v, pilas [] [] [] []⟩ : CE) =
      some ⟨some 3, none, pilas [] [] [] []⟩ := by
  show some (stepAux (maquinaBloque.m 1) v (pilas [] [] [] [])) = _
  simp [maquinaBloque, stepAux, pilas, upd0]

theorem paso2_bit (v : Option Bool) (c : Bool) (r : List Bool) :
    TM2.step maquinaBloque.m (⟨some 2, v, pilas (c :: r) [] [] []⟩ : CE) =
      some ⟨some 2, some c, pilas r [] [] []⟩ := by
  show some (stepAux (maquinaBloque.m 2) v (pilas (c :: r) [] [] [])) = _
  simp [maquinaBloque, stepAux, pilas, upd0]

theorem paso2_fin (v : Option Bool) :
    TM2.step maquinaBloque.m (⟨some 2, v, pilas [] [] [] []⟩ : CE) =
      some ⟨none, none, pilas [true] [] [] []⟩ := by
  show some (stepAux (maquinaBloque.m 2) v (pilas [] [] [] [])) = _
  simp [maquinaBloque, stepAux, pilas, upd0]

theorem paso3_fin (v : Option Bool) :
    TM2.step maquinaBloque.m (⟨some 3, v, pilas [] [] [] []⟩ : CE) =
      some ⟨none, none, pilas [false] [] [] []⟩ := by
  show some (stepAux (maquinaBloque.m 3) v (pilas [] [] [] [])) = _
  simp [maquinaBloque, stepAux, pilas, upd0]

theorem vaciar2 : ∀ (r : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaBloque.m) (r.length + 1)
      (⟨some 2, v, pilas r [] [] []⟩ : CE) ⟨none, none, pilas [true] [] [] []⟩
  | [], v => Llega.uno (paso2_fin v)
  | c :: r, v => by
    have := (Llega.uno (paso2_bit v c r)).trans (vaciar2 r (some c))
    simpa using this

/-- Los pasos de la corrida desde la etiqueta 0. -/
def pasos : List Bool → ℕ
  | [] => 2
  | [true] => 3
  | false :: r => r.length + 2
  | true :: _ :: r => pasos r + 2

theorem pasos_le : ∀ z : List Bool, pasos z ≤ z.length + 2
  | [] => le_refl _
  | [true] => le_refl _
  | false :: r => by simp [pasos]
  | true :: _ :: r => by
    have := pasos_le r
    simp only [pasos, List.length_cons]
    omega

/-- **La corrida** desde la etiqueta 0: termina con `bloqueValido z` en la pila, en `pasos z` pasos. -/
theorem corrida0 : ∀ (z : List Bool) (v : Option Bool),
    Llega (TM2.step maquinaBloque.m) (pasos z)
      (⟨some 0, v, pilas z [] [] []⟩ : CE) ⟨none, none, pilas [bloqueValido z] [] [] []⟩
  | [], v => by
    rw [bloqueValido_nil]
    exact (Llega.uno (paso0_fin v)).trans (Llega.uno (paso3_fin none))
  | [true], v => by
    rw [bloqueValido_true]
    exact ((Llega.uno (paso0_marca v [])).trans (Llega.uno (paso1_fin (some true)))).trans
      (Llega.uno (paso3_fin none))
  | false :: r, v => by
    rw [bloqueValido_false]
    exact (Llega.uno (paso0_cierre v r)).trans (vaciar2 r (some false))
  | true :: b :: r, v => by
    rw [bloqueValido_bit]
    exact ((Llega.uno (paso0_marca v (b :: r))).trans (Llega.uno (paso1_bit (some true) b r))).trans
      (corrida0 r (some b))

theorem init (inp : List Bool) : (initList maquinaBloque inp : CE) = ⟨some 0, none, pilas inp [] [] []⟩ := by
  show (⟨_, _, (initList maquinaBloque inp).stk⟩ : CE) = _
  rw [Componer.initList_stk]; congr 1; funext k; fin_cases k <;> rfl

theorem halt (out : List Bool) : (haltList maquinaBloque out : CE) = ⟨none, none, pilas out [] [] []⟩ := by
  show (⟨_, _, (haltList maquinaBloque out).stk⟩ : CE) = _
  rw [Componer.haltList_stk]; congr 1; funext k; fin_cases k <;> rfl

end Bloque

open Polynomial in
/-- Decidir si la entrada empieza con un bloque bien formado se calcula en tiempo polinomial. -/
noncomputable def bloqueValidoComputable :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := List Bool)).encode
      (CodBits.toEncoding (α := Bool)).encode bloqueValido where
  tm := maquinaBloque
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := X + 1 + 1
  outputsFun z := by
    have run := Bloque.corrida0 z none
    have hn := Bloque.pasos_le z
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := List Bool)).encode z) = z := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := Bool)).encode (bloqueValido z)) = [bloqueValido z] := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := List Bool)).encode z).length = z.length := rfl
    rw [hin, hout]
    rw [← Bloque.init, ← Bloque.halt] at run
    exact ⟨⟨_, run⟩, by simp only [eval_add, eval_X, eval_one]; omega⟩

theorem esPolinomial_bloqueValido : EsPolinomial bloqueValido := ⟨bloqueValidoComputable⟩

/-- Elegir entre la entrada y `[false]` según haya bloque. -/
theorem esPolinomial_eligeBloque :
    EsPolinomial (fun z : List Bool => if bloqueValido z then z else [false]) := by
  have hfalso : EsPolinomial (fun _ : List Bool => [false]) :=
    Componer.esPolinomial_comp _ _ ExhaustivoTiempo.esPolinomial_vacia esPolinomial_ponerFalso
  have hpar : EsPolinomial (fun z : List Bool => (z, [false])) :=
    Primero.esPolinomial_pares _ _ esPolinomial_id hfalso
  have htri : EsPolinomial (fun z : List Bool => (bloqueValido z, (z, [false]))) :=
    Primero.esPolinomial_pares _ _ esPolinomial_bloqueValido hpar
  exact Componer.esPolinomial_comp _ _ htri ExhaustivoTiempo.esPolinomial_si

/-- El código de `leeTotal z` es la elección anterior. -/
theorem cod_leeTotal (z : List Bool) :
    CodBits.cod (if bloqueValido z then z else [false]) = CodBits.cod (leeTotal z) := by
  unfold leeTotal bloqueValido
  cases h : CodBits.lee z with
  | none => rfl
  | some p =>
    obtain ⟨u, w⟩ := p
    show z = CodBits.delimita (CodBits.cod u) ++ CodBits.cod w
    exact (delimita_de_lee z h).symm

/-- **Leer un bloque de forma total se calcula en tiempo polinomial.** -/
theorem esPolinomial_leeTotal : EsPolinomial leeTotal :=
  esPolinomial_retipo cod_leeTotal esPolinomial_eligeBloque

end Bloques
end Sagitta.Map
