import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# El conteo de Shannon (primer intento)

Casi toda función booleana necesita circuitos grandes. Aquí, la forma de conteo: si los circuitos de `s` compuertas
son menos que las funciones de `n` bits, alguna función no tiene circuito de `s` compuertas. Es el principio del
palomar, como el argumento de que `0ⁿ1ⁿ` no es regular.

El modelo de `Circuitos.lean` no sirve para contar: una compuerta de entrada puede pedir cualquier índice, y hay
infinitos circuitos de cada tamaño. Este modelo acota los índices.

**El modelo.** Un circuito de `n` entradas y `s` compuertas tiene `n + s` cables: los `n` primeros son las entradas,
el `n + k` es la salida de la compuerta `k`. Cada compuerta elige una operación y dos cables cualesquiera; el
circuito elige además qué cable es la salida. Se evalúa compuerta por compuerta, en orden; un cable que todavía no
se calculó vale `false`. Así, toda descripción se evalúa, y todo circuito bien formado (que solo lee cables
anteriores) es una de ellas. Contar descripciones da entonces una cota superior del número de funciones que se
calculan con `s` compuertas, que es lo que el argumento necesita.
-/

namespace Sagitta.Map
namespace Shannon

/-- Las tres operaciones. La negación ignora su segundo cable. -/
inductive Op
  | y
  | o
  | no
  deriving DecidableEq

instance : Fintype Op where
  elems := {.y, .o, .no}
  complete := fun x => by cases x <;> simp

/-- Aplicar una operación. -/
def Op.aplica : Op → Bool → Bool → Bool
  | .y, a, b => a && b
  | .o, a, b => a || b
  | .no, a, _ => !a

theorem card_op : Fintype.card Op = 3 := rfl

/-- Un circuito de `n` entradas y `s` compuertas: para cada compuerta, su operación y sus dos cables; y el cable
de salida. -/
abbrev Circuito (n s : ℕ) := (Fin s → Op × Fin (n + s) × Fin (n + s)) × Fin (n + s)

/-- El cable donde escribe la compuerta `k`. -/
def cableDe {n s : ℕ} (k : Fin s) : Fin (n + s) := ⟨n + k, by have := k.isLt; omega⟩

/-- Los valores de los cables después de calcular las `m` primeras compuertas: al principio, las entradas y
`false` en el resto; cada paso escribe la compuerta siguiente. -/
def paso {n s : ℕ} (C : Circuito n s) (x : Fin n → Bool) : ℕ → Fin (n + s) → Bool
  | 0 => fun w => if h : w.val < n then x ⟨w.val, h⟩ else false
  | m + 1 =>
    if h : m < s then
      let v := paso C x m
      let g := C.1 ⟨m, h⟩
      Function.update v (cableDe ⟨m, h⟩) (g.1.aplica (v g.2.1) (v g.2.2))
    else paso C x m

/-- Los valores de todos los cables sobre la entrada `x`, calculando las compuertas en orden. -/
def cables {n s : ℕ} (C : Circuito n s) (x : Fin n → Bool) : Fin (n + s) → Bool := paso C x s

/-- La función que calcula el circuito: el valor de su cable de salida. -/
def calcula {n s : ℕ} (C : Circuito n s) : (Fin n → Bool) → Bool :=
  fun x => cables C x C.2

/-! El modelo calcula de verdad: el «o exclusivo» de dos bits con cuatro compuertas.
Cables 0 y 1: las entradas. 2 = x₀ o x₁; 3 = x₀ y x₁; 4 = no 3; 5 = 2 y 4, la salida. -/

/-- El «o exclusivo» como circuito de 2 entradas y 4 compuertas. -/
def circuitoXor : Circuito 2 4 :=
  (![(Op.o, 0, 1), (Op.y, 0, 1), (Op.no, 3, 3), (Op.y, 2, 4)], 5)

#guard [![false, false], ![false, true], ![true, false], ![true, true]].map (calcula circuitoXor)
    = [false, true, true, false]

/-- Un cable que lee uno todavía no calculado lo ve en `false`: el circuito que solo copia su última compuerta,
que lee el cable 3 antes de escribirlo, da siempre `false`. -/
def circuitoAdelantado : Circuito 2 2 := (![(Op.o, 3, 3), (Op.o, 0, 1)], 2)

#guard [![false, false], ![true, true]].map (calcula circuitoAdelantado) = [false, false]

/-- **Cuántos circuitos hay.** Cada compuerta: 3 operaciones y `(n + s)²` pares de cables; más el cable de
salida. -/
theorem card_circuito (n s : ℕ) :
    Fintype.card (Circuito n s) = (3 * (n + s) ^ 2) ^ s * (n + s) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, card_op]
  ring

/-- **Cuántas funciones hay.** Una por cada manera de asignar 0 o 1 a las `2ⁿ` entradas. -/
theorem card_funciones (n : ℕ) : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **El conteo de Shannon.** Si hay menos circuitos de `s` compuertas que funciones de `n` bits, alguna función
no la calcula ningún circuito de `s` compuertas. -/
theorem shannon (n s : ℕ) (h : (3 * (n + s) ^ 2) ^ s * (n + s) < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ C : Circuito n s, calcula C ≠ f := by
  by_contra hc
  push Not at hc
  have hsobre : Function.Surjective (fun C : Circuito n s => calcula C) := fun f => hc f
  have hcard := Fintype.card_le_of_surjective _ hsobre
  rw [card_circuito, card_funciones] at hcard
  exact absurd h (not_lt.mpr hcard)

set_option exponentiation.threshold 2048 in
/-- **Un caso concreto.** Hay una función de 10 bits que ningún circuito de 70 compuertas calcula. Hay
`2^1024` funciones de 10 bits y unos `2^1002` circuitos de 70 compuertas. -/
theorem diez_bits_setenta_compuertas :
    ∃ f : (Fin 10 → Bool) → Bool, ∀ C : Circuito 10 70, calcula C ≠ f :=
  shannon 10 70 (by norm_num)

/-! ## A lo sumo `s` compuertas

Se cuentan juntos los circuitos de todos los tamaños `t ≤ s`. Cada tamaño aporta a lo sumo lo que aporta el tamaño `s`,
así que el total es a lo sumo `(s + 1)` veces eso. El factor `s + 1` no cambia nada en la práctica. -/

/-- Los circuitos de a lo sumo `s` compuertas: un tamaño `t ≤ s` y un circuito de ese tamaño. -/
abbrev CircuitoHasta (n s : ℕ) := Σ t : Fin (s + 1), Circuito n t

/-- Más compuertas, más circuitos: el número de circuitos de `t` compuertas no pasa del de `s`, si `t ≤ s`. -/
theorem cuenta_mono {n s t : ℕ} (h : t ≤ s) :
    (3 * (n + t) ^ 2) ^ t * (n + t) ≤ (3 * (n + s) ^ 2) ^ s * (n + s) := by
  rcases Nat.eq_zero_or_pos (n + t) with h0 | hpos
  · rw [h0]; simp
  · have hb : 3 * (n + t) ^ 2 ≤ 3 * (n + s) ^ 2 :=
      Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) 2)
    have hns : 0 < n + s := by omega
    have hbpos : 0 < 3 * (n + s) ^ 2 := by positivity
    calc (3 * (n + t) ^ 2) ^ t * (n + t) ≤ (3 * (n + s) ^ 2) ^ t * (n + s) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hb t) (by omega)
      _ ≤ (3 * (n + s) ^ 2) ^ s * (n + s) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hbpos h)

/-- **Cuántos circuitos de a lo sumo `s` compuertas hay**, acotado. -/
theorem card_circuitoHasta_le (n s : ℕ) :
    Fintype.card (CircuitoHasta n s) ≤ (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s)) := by
  rw [Fintype.card_sigma]
  calc ∑ t : Fin (s + 1), Fintype.card (Circuito n t)
      ≤ ∑ _t : Fin (s + 1), (3 * (n + s) ^ 2) ^ s * (n + s) := by
        apply Finset.sum_le_sum
        intro t _
        rw [card_circuito]
        exact cuenta_mono (by have := t.isLt; omega)
    _ = (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **El conteo de Shannon, con «a lo sumo».** Si los circuitos de a lo sumo `s` compuertas son menos que las
funciones de `n` bits, alguna función no la calcula ningún circuito de `s` compuertas o menos. -/
theorem shannon_hasta (n s : ℕ)
    (h : (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s)) < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ t ≤ s, ∀ C : Circuito n t, calcula C ≠ f := by
  by_contra hc
  push Not at hc
  have hsobre : Function.Surjective (fun C : CircuitoHasta n s => calcula C.2) := by
    intro f
    obtain ⟨t, ht, C, hC⟩ := hc f
    exact ⟨⟨⟨t, by omega⟩, C⟩, hC⟩
  have hcard := Fintype.card_le_of_surjective _ hsobre
  rw [card_funciones] at hcard
  exact absurd (lt_of_le_of_lt (hcard.trans (card_circuitoHasta_le n s)) h) (lt_irrefl _)

set_option exponentiation.threshold 2048 in
/-- **El caso concreto, con «a lo sumo».** Hay una función de 10 bits que ningún circuito de 70 compuertas o menos
calcula. -/
theorem diez_bits_hasta_setenta_compuertas :
    ∃ f : (Fin 10 → Bool) → Bool, ∀ t ≤ 70, ∀ C : Circuito 10 t, calcula C ≠ f :=
  shannon_hasta 10 70 (by norm_num)

/-! ## La forma asintótica

Para todo `n ≥ 5`, alguna función de `n` bits necesita más de `2ⁿ / (8n)` compuertas. La constante `1/8` sale de
acotar cada pieza de la cuenta por una potencia de 2, con holgura; Shannon da `1`. Lo que importa es la forma:
exponencial dividido por `n`. -/

/-- `4n < 2ⁿ` desde `n = 5`. -/
theorem cuatro_n_lt (n : ℕ) (h : 5 ≤ n) : 4 * n < 2 ^ n := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

/-- **La cuenta, acotada por potencias de 2.** Si `8·n·s ≤ 2ⁿ` y `n ≥ 5`, los circuitos de a lo sumo `s`
compuertas son menos que las funciones de `n` bits. -/
theorem cota_asintotica (n s : ℕ) (hn : 5 ≤ n) (hs : 8 * n * s ≤ 2 ^ n) :
    (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s)) < 2 ^ 2 ^ n := by
  have h4 : 4 * n < 2 ^ n := cuatro_n_lt n hn
  have h8 : 8 * (n * s) ≤ 2 ^ n := by rw [← mul_assoc]; exact hs
  have hq : 5 * s ≤ n * s := Nat.mul_le_mul_right s hn
  have hns : n + s ≤ 2 ^ n := by omega
  have hs1 : s + 1 ≤ 2 ^ n := by omega
  -- Cada compuerta: a lo sumo `2^(2n+2)` elecciones.
  have hbase : 3 * (n + s) ^ 2 ≤ 2 ^ (2 * n + 2) := by
    have hcuad : (n + s) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hns 2
    calc 3 * (n + s) ^ 2 ≤ 4 * (2 ^ n) ^ 2 := by omega
      _ = 2 ^ (2 * n + 2) := by ring
  have hpot : (3 * (n + s) ^ 2) ^ s ≤ 2 ^ ((2 * n + 2) * s) := by
    rw [mul_comm (2 * n + 2) s, pow_mul']
    exact Nat.pow_le_pow_left hbase s
  have hresto : (s + 1) * (n + s) ≤ 2 ^ (2 * n) := by
    calc (s + 1) * (n + s) ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hs1 hns
      _ = 2 ^ (2 * n) := by ring
  -- El exponente total queda por debajo de `2ⁿ`.
  have hexp : (2 * n + 2) * s + 2 * n < 2 ^ n := by
    have hlin : (2 * n + 2) * s = 2 * (n * s) + 2 * s := by ring
    omega
  calc (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s))
      = (3 * (n + s) ^ 2) ^ s * ((s + 1) * (n + s)) := by ring
    _ ≤ 2 ^ ((2 * n + 2) * s) * 2 ^ (2 * n) := Nat.mul_le_mul hpot hresto
    _ = 2 ^ ((2 * n + 2) * s + 2 * n) := by rw [← pow_add]
    _ < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hexp

/-- **Shannon, forma asintótica.** Para todo `n ≥ 5` hay una función de `n` bits que ningún circuito de a lo sumo
`2ⁿ / (8n)` compuertas calcula. -/
theorem shannon_asintotico (n : ℕ) (hn : 5 ≤ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ t ≤ 2 ^ n / (8 * n), ∀ C : Circuito n t, calcula C ≠ f :=
  shannon_hasta n _ (cota_asintotica n _ hn (Nat.mul_div_le _ _))

end Shannon
end Sagitta.Map
