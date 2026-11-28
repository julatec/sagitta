import Mathlib.Computability.PartrecCode
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# La búsqueda universal de Levin

El algoritmo es de Levin (1973): para hallar una respuesta que se verifica rápido, correr *todos* los programas a
la vez, dándole al programa número `i` una fracción `1/2ⁱ` del esfuerzo, y verificar todo lo que entreguen. Si el
programa `i` resuelve la entrada con esfuerzo `k`, la búsqueda la resuelve con esfuerzo del orden de `2ⁱ · k`.

**De quién es cada cosa.** El evaluador universal es de Mathlib: `Nat.Partrec.Code` numera los programas
(`ofNatCode`), `evaln k c x` corre el programa `c` sobre `x` con presupuesto `k`, y `evaln_mono`, `evaln_complete` y
`exists_code` son sus teoremas. Lo propio de este archivo es la búsqueda por rondas y su contabilidad, y es un
ejercicio.

**Lo que esto NO es.**

* No es una máquina de Turing universal en el modelo `FinTM2` que usa el resto del proyecto.
* El presupuesto de `evaln` no es tiempo de máquina. Es un tope que acota a la vez la profundidad de la evaluación
  y el tamaño de la entrada (`evaln_bound`); crece con el trabajo, pero no hay un teorema que lo compare con pasos.
* Por eso de aquí **no sale ningún enunciado sobre `P` o `NP`**. Conectar las dos medidas exigiría un simulador
  con costo probado, que no existe ni en Mathlib ni aquí.

Lo que sí queda es la forma del argumento: corrección porque nada se acepta sin verificar, completitud con una
cota de rondas, y el costo `8 · 2ⁱ · k`.
-/

namespace Sagitta.Map
namespace Levin

open Nat.Partrec Nat.Partrec.Code

/-! ## El evaluador universal -/

/-- El programa número `i`, con presupuesto `k`, sobre la entrada `x`. `none` si el presupuesto no alcanza. -/
def correr (i k x : ℕ) : Option ℕ := evaln k (ofNatCode i) x

/-- **Más presupuesto no cambia la respuesta.** Lo que el programa entrega con `k₁` lo entrega con todo `k₂ ≥ k₁`. -/
theorem correr_mono {i k₁ k₂ x y : ℕ} (h : k₁ ≤ k₂) (hy : correr i k₁ x = some y) :
    correr i k₂ x = some y :=
  evaln_mono h hy

/-- **Es universal.** Toda función parcial recursiva es el programa número `i` para algún `i`: su valor en `x` es
`y` exactamente cuando algún presupuesto alcanza para obtenerlo. Es `exists_code` con `evaln_complete`, de Mathlib. -/
theorem correr_universal {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ i, ∀ x y, y ∈ f x ↔ ∃ k, correr i k x = some y := by
  obtain ⟨c, rfl⟩ := exists_code.1 hf
  refine ⟨encodeCode c, fun x y => ?_⟩
  have hc : ofNatCode (encodeCode c) = c := Denumerable.ofNat_encode c
  unfold correr
  rw [hc]
  exact evaln_complete

/-! ## La búsqueda por rondas -/

/-- En la ronda `t`, el programa `i` corre con presupuesto `2^(t-i)`; su respuesta se conserva solo si el
verificador la acepta. -/
def intento (V : ℕ → ℕ → Bool) (x t i : ℕ) : Option ℕ :=
  (correr i (2 ^ (t - i)) x).filter (V x)

/-- La ronda `t`: los programas `0, …, t`, en orden; se entrega la primera respuesta aceptada. -/
def ronda (V : ℕ → ℕ → Bool) (x t : ℕ) : Option ℕ :=
  (List.range (t + 1)).findSome? (intento V x t)

/-- La búsqueda hasta la ronda `T`: la primera ronda que entrega algo. -/
def buscar (V : ℕ → ℕ → Bool) (x T : ℕ) : Option ℕ :=
  (List.range (T + 1)).findSome? (ronda V x)

theorem intento_acepta {V : ℕ → ℕ → Bool} {x t i y : ℕ} (h : intento V x t i = some y) :
    V x y = true := by
  unfold intento at h
  exact (Option.filter_eq_some_iff.1 h).2

/-- **Corrección.** Todo lo que la búsqueda entrega lo acepta el verificador. No depende de que ningún programa
sea correcto. -/
theorem buscar_acepta {V : ℕ → ℕ → Bool} {x T y : ℕ} (h : buscar V x T = some y) : V x y = true := by
  obtain ⟨t, -, ht⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some ht
  exact intento_acepta hi

/-- **Completitud, con cota de rondas.** Si el programa `i` con presupuesto `k` da una respuesta aceptada, la
búsqueda entrega algo (aceptado, por `buscar_acepta`) en cuanto llega a la ronda `i + ⌈log₂ k⌉`. -/
theorem buscar_halla {V : ℕ → ℕ → Bool} {x i k y T : ℕ} (h : correr i k x = some y) (hV : V x y = true)
    (hT : i + Nat.clog 2 k ≤ T) : ∃ y', buscar V x T = some y' := by
  have hint : intento V x (i + Nat.clog 2 k) i = some y := by
    unfold intento
    rw [Nat.add_sub_cancel_left, correr_mono (Nat.le_pow_clog one_lt_two k) h]
    simp [hV]
  have hr : (ronda V x (i + Nat.clog 2 k)).isSome := by
    unfold ronda
    rw [List.findSome?_isSome_iff]
    exact ⟨i, List.mem_range.2 (by omega), by simp [hint]⟩
  have hb : (buscar V x T).isSome := by
    unfold buscar
    rw [List.findSome?_isSome_iff]
    exact ⟨i + Nat.clog 2 k, List.mem_range.2 (by omega), hr⟩
  exact Option.isSome_iff_exists.1 hb

/-- **Halla, no decide.** Si ningún programa, con ningún presupuesto, da una respuesta aceptada, la búsqueda no
entrega nada por más rondas que corra. -/
theorem buscar_nada {V : ℕ → ℕ → Bool} {x : ℕ}
    (h : ∀ i k y, correr i k x = some y → V x y = false) (T : ℕ) : buscar V x T = Option.none := by
  cases hb : buscar V x T with
  | none => rfl
  | some y =>
    obtain ⟨t, -, ht⟩ := List.exists_of_findSome?_eq_some hb
    obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some ht
    unfold intento at hi
    obtain ⟨hc, hv⟩ := Option.filter_eq_some_iff.1 hi
    rw [h i _ y hc] at hv
    exact absurd hv (by simp)

/-! ## El costo

Se mide en presupuesto de `evaln`, no en pasos de máquina de Turing: el costo de una ronda es la suma de los
presupuestos que reparte. -/

/-- El presupuesto que reparte la ronda `t`: `2^t + 2^(t-1) + … + 1`. -/
def costoRonda (t : ℕ) : ℕ := ∑ i ∈ Finset.range (t + 1), 2 ^ (t - i)

/-- El presupuesto repartido en las rondas `0, …, T`. -/
def costoHasta (T : ℕ) : ℕ := ∑ t ∈ Finset.range (T + 1), costoRonda t

/-- La ronda `t` reparte exactamente `2^(t+1) - 1`. -/
theorem costoRonda_eq (t : ℕ) : costoRonda t + 1 = 2 ^ (t + 1) := by
  induction t with
  | zero => simp [costoRonda]
  | succ t ih =>
    have h : costoRonda (t + 1) = 2 * costoRonda t + 1 := by
      unfold costoRonda
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have : t + 1 - i = (t - i) + 1 := by have := Finset.mem_range.1 hi; omega
      rw [this, pow_succ']
    rw [h, pow_succ']
    omega

/-- **Una ronda cuesta menos que el doble de su mayor presupuesto.** -/
theorem costoRonda_lt (t : ℕ) : costoRonda t < 2 ^ (t + 1) := by
  have := costoRonda_eq t
  omega

/-- **Todas las rondas hasta la `T` cuestan menos que `2^(T+2)`.** Cada ronda cuesta el doble que la anterior, así
que la última pesa tanto como todas las demás juntas. -/
theorem costoHasta_lt (T : ℕ) : costoHasta T < 2 ^ (T + 2) := by
  induction T with
  | zero => simp [costoHasta, costoRonda]
  | succ T ih =>
    have h : costoHasta (T + 1) = costoHasta T + costoRonda (T + 1) := by
      unfold costoHasta
      rw [Finset.sum_range_succ]
    have h2 := costoRonda_lt (T + 1)
    have h3 : 2 ^ (T + 1 + 2) = 2 ^ (T + 2) + 2 ^ (T + 2) := by rw [pow_succ]; ring
    have h4 : (2 : ℕ) ^ (T + 1 + 1) = 2 ^ (T + 2) := rfl
    omega

/-- Para `k ≥ 1`, la menor potencia de 2 que alcanza a `k` es menor que `2k`. -/
theorem pow_clog_lt {k : ℕ} (hk : 1 ≤ k) : 2 ^ Nat.clog 2 k < 2 * k := by
  rcases Nat.lt_or_ge 1 k with h | h
  · have hpos : 0 < Nat.clog 2 k := Nat.clog_pos one_lt_two h
    obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hlt := Nat.pow_pred_clog_lt_self one_lt_two h
    rw [hc] at hlt ⊢
    simp only [Nat.pred_succ] at hlt
    rw [pow_succ']
    omega
  · have : k = 1 := by omega
    subst this
    simp

/-- **El teorema de Levin, en esta medida.** Si el programa número `i` resuelve `x` con presupuesto `k ≥ 1`, la
búsqueda entrega una respuesta aceptada habiendo repartido menos de `8 · 2ⁱ · k`. El factor `2ⁱ` depende del
programa y no de la entrada: la búsqueda es tan buena como cualquier programa, salvo esa constante. -/
theorem levin {V : ℕ → ℕ → Bool} {x i k y : ℕ} (hk : 1 ≤ k) (h : correr i k x = some y)
    (hV : V x y = true) :
    ∃ T y', buscar V x T = some y' ∧ V x y' = true ∧ costoHasta T < 8 * 2 ^ i * k := by
  obtain ⟨y', hy'⟩ := buscar_halla (T := i + Nat.clog 2 k) h hV le_rfl
  refine ⟨i + Nat.clog 2 k, y', hy', buscar_acepta hy', ?_⟩
  have h1 := costoHasta_lt (i + Nat.clog 2 k)
  have h2 : 2 ^ (i + Nat.clog 2 k + 2) = 4 * 2 ^ i * 2 ^ Nat.clog 2 k := by
    rw [pow_add, pow_add]; ring
  have h3 : 4 * 2 ^ i * 2 ^ Nat.clog 2 k < 4 * 2 ^ i * (2 * k) :=
    Nat.mul_lt_mul_of_pos_left (pow_clog_lt hk) (by positivity)
  have h4 : 4 * 2 ^ i * (2 * k) = 8 * 2 ^ i * k := by ring
  omega

/-! ## Un ejemplo mínimo

El programa número 0 es `zero`, que responde 0. Con el verificador «la respuesta es 0», la búsqueda sobre la
entrada 0 termina en la primera ronda. -/

example : buscar (fun _ y => y == 0) 0 0 = some 0 := by
  have h : evaln (0 + 1) Code.zero 0 = some 0 := by simp [evaln]
  simpa [buscar, ronda, intento, correr, ofNatCode] using h

end Levin
end Sagitta.Map
