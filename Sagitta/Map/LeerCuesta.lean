import Sagitta.Map.Decidir

/-!
# Leer cuesta: de dónde sale el «1» de cada elección

En el modelo del costo de equivocarse, cada elección cuesta `1 + ε`. Aquí se justifica el `1`, y se dice qué se puede
decir del `ε`. Todo en el modelo de preguntas de `Decidir.lean` (un algoritmo pregunta posiciones de la entrada, una por
una, y cada pregunta cuesta 1).

## Lo que se prueba

* **Lo sensible se lee** (`lee_lo_sensible`). Una posición es *sensible* en la entrada `x` si cambiarla cambia la
  respuesta. Todo algoritmo que calcula la respuesta pregunta, con la entrada `x`, por cada posición sensible: si se
  saltara una, el adversario la cambia y el algoritmo responde igual, equivocándose.
* **Cuesta al menos lo que hay de sensible** (`costo_ge_sensibles`): con la entrada `x`, tantas preguntas como posiciones
  sensibles tenga `x`.
* **Verificar que todo se cumple** (`verificar_todo`): para decidir si las `n` condiciones se cumplen (si todas las
  cláusulas son verdaderas), en una entrada donde se cumplen hay que leer las `n`. Y alcanza: revisarlas una por una
  cuesta a lo sumo `n` (`revisar_alcanza`). El costo es exactamente `n`, o sea **1 por condición**.
* **Pero no siempre hay que leer todo** (`no_sensible_no_se_lee`): si la respuesta depende de una sola posición, una
  pregunta alcanza, sea cual sea el tamaño de la entrada. El «1 por elemento» vale para lo que la respuesta no puede
  ignorar, no para todo. En SAT vale para las cláusulas; para las variables del certificado no siempre: con dos literales
  verdaderos en una cláusula, ninguno de los dos es sensible.

## El `ε`

Elegir cuesta al menos un paso, así que `ε` es una constante, no necesariamente chica. Para la frontera da igual cuál: con
las elecciones **sumadas**, `c · (1 + ε)` es polinomial para todo `ε` constante (`elegir_sumado_pol`). Lo que separa lo
polinomial de lo exponencial es si el costo se suma o se multiplica, no su tamaño; eso lo deciden `ρ` y `d`
(`CostoError.lean`, `ArbolElecciones.lean`), que miden información, no pasos.
-/

namespace Sagitta.Map
namespace Tiempo

open Pregunta

variable {α : Type}

/-- `t` **calcula** `F`: con todo oráculo, responde lo que dice `F`. -/
def Calcula (t : Pregunta α) (F : (α → Bool) → Bool) : Prop := ∀ g, corre t g = F g

/-- La posición `i` es **sensible** en `x`: cambiarla cambia la respuesta. -/
def Sensible [DecidableEq α] (F : (α → Bool) → Bool) (x : α → Bool) (i : α) : Prop :=
  F (Function.update x i (!x i)) ≠ F x

/-- **Lo sensible se lee.** -/
theorem lee_lo_sensible [DecidableEq α] {t : Pregunta α} {F : (α → Bool) → Bool} (h : Calcula t F) {x : α → Bool}
    {i : α} (hs : Sensible F x i) : i ∈ vistos t x := by
  by_contra hi
  apply hs
  rw [← h, ← h]
  exact (corre_congr t x _ fun j hj => by
    have hji : j ≠ i := fun e => hi (e ▸ hj)
    simp [Function.update_of_ne hji]).symm

/-- **Cuesta al menos lo que hay de sensible.** -/
theorem costo_ge_sensibles [Fintype α] [DecidableEq α] {t : Pregunta α} {F : (α → Bool) → Bool} (h : Calcula t F)
    (x : α → Bool) [DecidablePred (Sensible F x)] :
    (Finset.univ.filter (Sensible F x)).card ≤ costo t x := by
  have hsub : Finset.univ.filter (Sensible F x) ⊆ (vistos t x).toFinset := fun i hi =>
    List.mem_toFinset.mpr (lee_lo_sensible h (Finset.mem_filter.mp hi).2)
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _)

/-! ## Verificar que todo se cumple -/

/-- **Todas las condiciones se cumplen.** -/
def todas [Fintype α] (g : α → Bool) : Bool := decide (∀ i, g i = true)

/-- Donde todas se cumplen, cada posición es sensible: si una falla, ya no se cumplen todas. -/
theorem todas_sensible [Fintype α] [DecidableEq α] (i : α) : Sensible todas (fun _ => true) i := by
  simp only [Sensible, todas, Bool.not_true, ne_eq, decide_eq_decide]
  intro h
  have := (h.mpr fun _ => trivial) i
  simp at this

/-- **Verificar que todo se cumple, donde se cumple, lee todo**: `n` preguntas. -/
theorem verificar_todo [Fintype α] {t : Pregunta α} (h : Calcula t todas) :
    Fintype.card α ≤ costo t (fun _ => true) := by
  classical
  have := costo_ge_sensibles h (fun _ => true)
  simpa [Finset.filter_true_of_mem fun i _ => todas_sensible i] using this

/-- **Revisar una por una**: si alguna falla, responde que no. -/
def revisar : List α → Pregunta α
  | [] => .resp true
  | i :: l => .preg i fun b => if b then revisar l else .resp false

theorem corre_revisar (g : α → Bool) : ∀ l : List α, corre (revisar l) g = true ↔ ∀ i ∈ l, g i = true
  | [] => by simp [revisar, corre]
  | i :: l => by
    simp only [revisar, corre, List.mem_cons, forall_eq_or_imp]
    cases hgi : g i
    · simp [corre]
    · simp only [ite_true, corre_revisar g l, true_and]

theorem costo_revisar (g : α → Bool) : ∀ l : List α, costo (revisar l) g ≤ l.length
  | [] => by simp [revisar, costo, vistos]
  | i :: l => by
    simp only [costo, revisar, vistos, List.length_cons]
    cases g i
    · simp [vistos]
    · simpa [costo] using costo_revisar g l

/-- **Y alcanza**: revisar todas calcula `todas` con a lo sumo `n` preguntas. Verificar cuesta exactamente `n`: 1 por
condición. -/
theorem revisar_alcanza [Fintype α] :
    Calcula (revisar (Finset.univ : Finset α).toList) todas ∧
      ∀ g, costo (revisar (Finset.univ : Finset α).toList) g ≤ Fintype.card α := by
  refine ⟨fun g => ?_, fun g => ?_⟩
  · have := corre_revisar g (Finset.univ : Finset α).toList
    simp only [Finset.mem_toList, Finset.mem_univ, true_implies] at this
    cases hc : corre (revisar (Finset.univ : Finset α).toList) g
    · simp only [todas]
      symm
      rw [decide_eq_false_iff_not]
      intro hall
      have := this.mpr hall
      rw [hc] at this
      exact Bool.false_ne_true this
    · simp only [todas]
      symm
      rw [decide_eq_true_iff]
      exact this.mp hc
  · simpa using costo_revisar g (Finset.univ : Finset α).toList

/-! ## No siempre hay que leer todo -/

/-- **Si la respuesta depende de una sola posición, una pregunta alcanza**, sea cual sea el tamaño de la entrada. -/
theorem no_sensible_no_se_lee (a : α) : Calcula (verificar a) (fun g => g a) ∧ ∀ g, costo (verificar a) g = 1 := by
  refine ⟨fun g => ?_, fun g => ?_⟩ <;> simp [verificar, corre, costo, vistos]

/-! ## El `ε`: una constante que se suma -/

/-- **Con las elecciones sumadas, el `ε` no importa**: `c · (1 + ε)` es polinomial para todo `ε` constante. -/
theorem elegir_sumado_pol (e : ℕ) : (fun c => c * (1 + e)) ∈ Pol :=
  ⟨1 + e, 1, fun c => by nlinarith⟩

end Tiempo
end Sagitta.Map
