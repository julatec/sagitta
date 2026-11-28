import Sagitta.Map.ArbolElecciones
import Sagitta.Map.CostoError

/-!
# El azar, encima del árbol (E3)

Tercera fase del plan. En `ArbolElecciones.lean` todo se cuenta,
sin probabilidad. Aquí la probabilidad se pone encima, y se ve que **es contar**.

## Lo que se prueba

* **La densidad** (`cuenta`, `densidad`): las soluciones debajo de un nodo, sobre `2^k`. Un nodo está vivo si y solo si
  su densidad es positiva (`cuenta_pos_iff`).
* **Elegir con una moneda promedia** (`densidad_succ`): la densidad de un nodo es el promedio de la de sus hijos. Es la
  probabilidad de que bajar al azar, eligiendo cada valor con una moneda justa, termine en una solución. Y es exactamente
  esa probabilidad bajo la medida uniforme sobre las hojas (`densidad_eq_card`).
* **Bajar al azar y reiniciar** (`costo_reiniciar`): si cada intento baja las `k` variables al azar y se reinicia cuando
  falla, el costo esperado es `k / densidad` (la geométrica de `CostoError.lean`). Es polinomial si y solo si la densidad
  es al menos `1/polinomio`.
* **Azar contra orden** (controles por `decide`): cuando la mitad de las asignaciones son solución pero el error del
  primer paso se ve tarde, la vuelta atrás determinista recorre medio árbol y el azar necesita dos intentos en promedio.
  Con una sola solución y un buen detector pasa lo contrario.

## Qué cambia respecto del plan

El plan esperaba recuperar el `ρ` de `CostoError` como fracción de hijos muertos. En un árbol binario esa fracción solo
vale `0` o `1/2` en un nodo vivo, así que no hay un `ρ` general. El parámetro que sí aparece es la densidad, y el modelo
de `CostoError` con `ρ = 1/2` y `d = k` es justamente el caso de densidad `2^(−k)`: una sola solución.
-/

open MeasureTheory ProbabilityTheory

namespace Sagitta.Map
namespace Tiempo

variable (sol : List Bool → Bool)

/-! ## Contar soluciones -/

/-- Las soluciones debajo de `p`, con `k` variables por fijar. -/
def cuenta : ℕ → List Bool → ℕ
  | 0, p => if sol p then 1 else 0
  | k + 1, p => cuenta k (p ++ [false]) + cuenta k (p ++ [true])

theorem cuenta_le : ∀ (k : ℕ) (p : List Bool), cuenta sol k p ≤ 2 ^ k
  | 0, p => by simp only [cuenta]; split <;> simp
  | k + 1, p => by
    have := cuenta_le k (p ++ [false]); have := cuenta_le k (p ++ [true])
    simp only [cuenta, pow_succ]; omega

/-- **Vivo si y solo si hay alguna solución que contar.** -/
theorem cuenta_pos_iff : ∀ (k : ℕ) (p : List Bool), 0 < cuenta sol k p ↔ Vivo sol k p
  | 0, p => by
    rw [vivo_cero]; simp only [cuenta]; split <;> simp_all
  | k + 1, p => by
    rw [vivo_succ, ← cuenta_pos_iff k, ← cuenta_pos_iff k]
    simp only [cuenta]; omega

/-- **La densidad**: la fracción de completaciones que son solución. -/
noncomputable def densidad (k : ℕ) (p : List Bool) : ℝ := cuenta sol k p / 2 ^ k

theorem densidad_nonneg (k : ℕ) (p : List Bool) : 0 ≤ densidad sol k p := by
  unfold densidad; positivity

theorem densidad_le_one (k : ℕ) (p : List Bool) : densidad sol k p ≤ 1 := by
  unfold densidad
  rw [div_le_one (by positivity)]
  exact_mod_cast cuenta_le sol k p

/-- **Elegir con una moneda promedia**: la densidad de un nodo es el promedio de la de sus hijos. -/
theorem densidad_succ (k : ℕ) (p : List Bool) :
    densidad sol (k + 1) p = (densidad sol k (p ++ [false]) + densidad sol k (p ++ [true])) / 2 := by
  unfold densidad
  simp only [cuenta, Nat.cast_add, pow_succ]
  field_simp

/-! ## La densidad es la probabilidad uniforme -/

/-- Las completaciones de largo `k`, como funciones `Fin k → Bool`. -/
def completar (p : List Bool) {k : ℕ} (v : Fin k → Bool) : List Bool := p ++ List.ofFn v

/-- **La densidad cuenta las hojas que son solución**: es la probabilidad de caer en una solución eligiendo una hoja al
azar, con todas igual de probables. -/
theorem densidad_eq_card : ∀ (k : ℕ) (p : List Bool),
    cuenta sol k p = (Finset.univ.filter fun v : Fin k → Bool => sol (completar p v) = true).card
  | 0, p => by
    simp only [cuenta, completar, List.ofFn_zero, List.append_nil]
    split <;> rename_i h <;> simp [h, Finset.filter_true_of_mem, Finset.filter_false_of_mem]
  | k + 1, p => by
    simp only [cuenta]
    rw [densidad_eq_card k (p ++ [false]), densidad_eq_card k (p ++ [true])]
    -- separar las funciones `Fin (k+1) → Bool` por su primer valor
    have e : ∀ b : Bool, (Finset.univ.filter fun v : Fin k → Bool => sol (completar (p ++ [b]) v) = true).card =
        (Finset.univ.filter fun v : Fin (k + 1) → Bool => v 0 = b ∧ sol (completar p v) = true).card := by
      intro b
      refine Finset.card_bij (fun v _ => Fin.cons b v) (fun v hv => ?_) (fun v _ w _ h => ?_) (fun w hw => ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        refine ⟨by simp, ?_⟩
        simpa [completar, List.ofFn_succ] using hv
      · exact Fin.cons_injective2 h |>.2
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        obtain ⟨h0, hs⟩ := hw
        refine ⟨Fin.tail w, ?_, ?_⟩
        · rw [← h0]
          simp only [completar, List.ofFn_succ, List.append_assoc, List.singleton_append] at hs ⊢
          exact hs
        · rw [← h0]; exact Fin.cons_self_tail w
    rw [e false, e true, ← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases v 0 <;> simp
    · rw [Finset.disjoint_filter]
      intro v _ h1 h2
      rw [h1.1] at h2
      exact Bool.false_ne_true h2.1

/-! ## Bajar al azar y reiniciar -/

/-- La densidad, como probabilidad de éxito de un intento. -/
noncomputable def exitoIntento (k : ℕ) : unitInterval :=
  ⟨densidad sol k [], densidad_nonneg sol k [], densidad_le_one sol k []⟩

/-- **Bajar al azar y reiniciar cuando falla**: cada intento baja las `k` variables (cuesta `k`) y sale bien con
probabilidad `densidad`; los intentos fallidos antes del primer éxito son geométricos. El costo esperado es
`k / densidad`. -/
theorem costo_reiniciar (k : ℕ) (hv : Vivo sol k []) :
    ∫ x, costo k x ∂tramos 1 (exitoIntento sol k) = k / densidad sol k [] := by
  have hpos : 0 < densidad sol k [] := by
    unfold densidad
    have := (cuenta_pos_iff sol k []).mpr hv
    positivity
  have hne : exitoIntento sol k ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    simp only [exitoIntento, Set.Icc.coe_zero] at this
    linarith
  rw [costo_esperado k 1 hne]
  simp [exitoIntento]

/-- **La frontera del azar**: el costo esperado de reiniciar, `k / densidad`, es a lo sumo `k · 2^k / cuenta`. Es
polinomial exactamente cuando las soluciones son al menos una fracción `1/polinomio` de las hojas. -/
theorem costo_reiniciar_eq (k : ℕ) (hv : Vivo sol k []) :
    k / densidad sol k [] = k * 2 ^ k / cuenta sol k [] := by
  unfold densidad
  have : (0 : ℝ) < cuenta sol k [] := by exact_mod_cast (cuenta_pos_iff sol k []).mpr hv
  field_simp

/-! ## Azar contra orden -/

/-- **La mitad son solución, pero el primer error se ve tarde**: las soluciones son las que tienen `x₀ = true`, y la
única cláusula que lo dice también pide `x₃`. -/
def mitadTarde : List Clausula := [[(0, true), (3, true)], [(0, true), (3, false)]]

/-- La vuelta atrás determinista prueba `x₀ = false` primero y no lo ve hasta fijar `x₃`: 20 nodos de 31. -/
example : nodos (solCNF mitadTarde) (detCNF mitadTarde) 4 [] = 20 := by decide

/-- El azar: la mitad de las hojas son solución, así que en promedio hacen falta 2 intentos de 4 pasos. -/
example : cuenta (solCNF mitadTarde) 4 [] = 2 ^ 4 / 2 := by decide

/-- **Una sola solución, y un buen detector**: la vuelta atrás cuesta `2·4 + 1`; el azar, una hoja de 16. -/
example : nodos (solCNF todoTrue4) (detCNF todoTrue4) 4 [] = 9 ∧ cuenta (solCNF todoTrue4) 4 [] = 1 := by decide

end Tiempo
end Sagitta.Map
