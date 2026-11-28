import Sagitta.Map.Circuitos
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log

/-!
# Dónde el crecimiento polinomial deja de ser cerrado

Todo aquí es sobre funciones `ℕ → ℕ` y sus cotas, sin máquinas. Son ejercicios: la matemática es de primer curso y
el marco es el de Cobham (1965), que caracterizó las funciones de tiempo polinomial como las que salen de la
composición y de la recursión *con una cota al tamaño del resultado*.

Tres partes:

* **lo que sí**: suma, producto, composición, componer `k` veces con `k` fijo, y un bucle de una cantidad polinomial
  de vueltas en que cada vuelta cuesta poco;
* **lo que no**: componer `n` veces (duplicar), multiplicar `n` factores, y elevar al cuadrado `n` veces, donde ni
  siquiera el *largo* del resultado queda acotado;
* **la salvación**: un bucle largo es polinomial si el tamaño del estado se mantiene acotado (la forma de Cobham).
-/

namespace Sagitta.Map
namespace Cerradura

open Polynomial

/-- `f` está acotada por algún polinomio. -/
def Acotada (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n

/-- Un polinomio de coeficientes naturales es creciente. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-! ## Lo que sí es cerrado -/

/-- **Suma.** Hacer una cosa y luego otra. -/
theorem suma {f g : ℕ → ℕ} (hf : Acotada f) (hg : Acotada g) : Acotada (fun n => f n + g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun n => by rw [eval_add]; exact Nat.add_le_add (hp n) (hq n)⟩

/-- **Producto.** Repetir una cosa tantas veces como diga la otra. -/
theorem producto {f g : ℕ → ℕ} (hf : Acotada f) (hg : Acotada g) : Acotada (fun n => f n * g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun n => by rw [eval_mul]; exact Nat.mul_le_mul (hp n) (hq n)⟩

/-- **Composición.** Aplicar una función a la salida de otra. -/
theorem composicion {f g : ℕ → ℕ} (hf : Acotada f) (hg : Acotada g) : Acotada (fun n => f (g n)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p.comp q, fun n => by rw [eval_comp]; exact (hp _).trans (eval_mono p (hq n))⟩

/-- **Componer `k` veces, con `k` fijo.** El polinomio depende de `k`, pero `k` no depende de `n`. -/
theorem iterada_fija {f : ℕ → ℕ} (hf : Acotada f) (k : ℕ) : Acotada (fun n => f^[k] n) := by
  induction k with
  | zero => exact ⟨X, fun n => by simp⟩
  | succ k ih =>
    have h := composicion ih hf
    simpa [Function.iterate_succ_apply] using h

/-- **Un bucle.** Una cantidad polinomial de vueltas, cada una de costo polinomial: el total es polinomial. La suma
aguanta ser repetida `v n` veces; el producto y la composición, no. -/
theorem bucle {c : ℕ → ℕ → ℕ} {v : ℕ → ℕ} (hv : Acotada v)
    (hc : ∃ p : Polynomial ℕ, ∀ n i, i < v n → c n i ≤ p.eval n) :
    Acotada (fun n => ∑ i ∈ Finset.range (v n), c n i) := by
  obtain ⟨q, hq⟩ := hv
  obtain ⟨p, hp⟩ := hc
  refine ⟨q * p, fun n => ?_⟩
  rw [eval_mul]
  calc ∑ i ∈ Finset.range (v n), c n i
      ≤ ∑ _i ∈ Finset.range (v n), p.eval n :=
        Finset.sum_le_sum fun i hi => hp n i (Finset.mem_range.mp hi)
    _ = v n * p.eval n := by simp
    _ ≤ q.eval n * p.eval n := Nat.mul_le_mul_right _ (hq n)

/-! ## Lo que no -/

/-- **La exponencial no está acotada por ningún polinomio.** -/
theorem dos_pow_no_acotada : ¬ Acotada (fun n => 2 ^ n) := by
  rintro ⟨p, hp⟩
  obtain ⟨N, hN⟩ := mul_pow_lt_dos_pow (p.eval 1) p.natDegree
  have h1 : 1 ≤ max N 1 := le_max_right _ _
  have h2 := hN (max N 1) (le_max_left _ _)
  exact absurd ((hp (max N 1)).trans (eval_le_mul_pow p h1)) (not_le.mpr h2)

/-- Duplicar: una función lineal. -/
def duplicar (x : ℕ) : ℕ := 2 * x

theorem duplicar_acotada : Acotada duplicar :=
  ⟨C 2 * X, fun n => by simp [duplicar]⟩

/-- Duplicar `n` veces multiplica por `2ⁿ`. -/
theorem duplicar_iter (n x : ℕ) : duplicar^[n] x = 2 ^ n * x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, ih, duplicar]; ring

/-- **Componer `n` veces rompe la cota.** Hay una función lineal cuyas iteradas fijas son todas polinomiales y
cuya iterada `n` veces no lo es. La diferencia entre las dos es solo si el número de vueltas depende de `n`. -/
theorem iterar_n_veces_rompe :
    ∃ f : ℕ → ℕ, Acotada f ∧ (∀ k, Acotada (fun n => f^[k] n)) ∧ ¬ Acotada (fun n => f^[n] 1) := by
  refine ⟨duplicar, duplicar_acotada, iterada_fija duplicar_acotada, ?_⟩
  simpa [duplicar_iter] using dos_pow_no_acotada

/-- **Multiplicar `n` factores rompe la cota.** Cada factor es `n`, que es lineal; el producto es `nⁿ`. -/
theorem producto_n_veces_rompe : ¬ Acotada (fun n => ∏ _i ∈ Finset.range n, n) := by
  rintro ⟨p, hp⟩
  obtain ⟨N, hN⟩ := mul_pow_lt_dos_pow (p.eval 1) p.natDegree
  have h2 : 2 ≤ max N 2 := le_max_right _ _
  have h3 := hN (max N 2) (le_max_left _ _)
  have h4 := hp (max N 2)
  simp only [Finset.prod_const, Finset.card_range] at h4
  have h5 : 2 ^ max N 2 ≤ max N 2 ^ max N 2 := Nat.pow_le_pow_left h2 _
  exact absurd (h5.trans (h4.trans (eval_le_mul_pow p (by omega)))) (not_le.mpr h3)

/-- Elevar al cuadrado: una función polinomial. -/
def cuadrado (x : ℕ) : ℕ := x * x

theorem cuadrado_acotada : Acotada cuadrado :=
  ⟨X * X, fun n => by simp [cuadrado]⟩

/-- Elevar al cuadrado `n` veces, desde 2, da `2^(2ⁿ)`. -/
theorem cuadrado_iter (n : ℕ) : cuadrado^[n] 2 = 2 ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, cuadrado, ← pow_add, ← two_mul, ← pow_succ']

/-- **Ni siquiera el largo queda acotado.** Tras elevar al cuadrado `n` veces, el resultado tiene `2ⁿ` bits: no
cabe escrito en espacio polinomial. Aquí lo que crece sin cota es el tamaño del dato, no solo su valor. -/
theorem largo_del_cuadrado_no_acotado : ¬ Acotada (fun n => Nat.log 2 (cuadrado^[n] 2)) := by
  have h : (fun n => Nat.log 2 (cuadrado^[n] 2)) = fun n => 2 ^ n := by
    funext n
    rw [cuadrado_iter, Nat.log_pow (by norm_num)]
  rw [h]
  exact dos_pow_no_acotada

/-! ## La salvación: acotar el tamaño

La forma de Cobham. Un bucle de `v n` vueltas va transformando un estado con `paso`. Si el tamaño del estado se
mantiene bajo un polinomio en `n` durante todo el bucle, y cada vuelta cuesta un polinomio en el tamaño del estado,
el costo total es polinomial. La hipótesis `htam` es justamente la que le falta a `cuadrado`. -/

theorem bucle_con_estado_acotado {paso costo v : ℕ → ℕ} (hv : Acotada v) (hcosto : Acotada costo)
    (htam : ∃ q : Polynomial ℕ, ∀ n i, i < v n → paso^[i] n ≤ q.eval n) :
    Acotada (fun n => ∑ i ∈ Finset.range (v n), costo (paso^[i] n)) := by
  obtain ⟨p, hp⟩ := hcosto
  obtain ⟨q, hq⟩ := htam
  refine bucle hv ⟨p.comp q, fun n i hi => ?_⟩
  rw [eval_comp]
  exact (hp _).trans (eval_mono p (hq n i hi))

/-! ## Apilar: un piso de cuantificadores por nivel

Supongamos `P = NP`, con SAT resuelto en tiempo `n^c`. Un problema con `k` cuantificadores alternados se colapsa de
adentro hacia afuera: cada piso se resuelve con el algoritmo de SAT, aplicado a un verificador que ya es el
resolvedor del piso anterior. El costo se compone: tras `k` pisos es `n^(c^k)`.

Con `k` fijo eso es un polinomio: es el colapso clásico de la jerarquía polinomial. Con `k = n` no lo es, y ahí está
la distancia entre la jerarquía y PSPACE. Esto dice que *este método* no alcanza; si `P = NP` implica `P = PSPACE`
es una pregunta abierta. Aquí solo va el cálculo del exponente, sin máquinas ni cuantificadores. -/

/-- El costo de resolver un piso: elevar a la `c`. -/
def piso (c : ℕ) (x : ℕ) : ℕ := x ^ c

theorem piso_acotada (c : ℕ) : Acotada (piso c) :=
  ⟨X ^ c, fun n => by simp [piso]⟩

/-- **El exponente se eleva en cada piso.** Tras `k` pisos el costo es `n^(c^k)`. -/
theorem piso_iter (c k n : ℕ) : (piso c)^[k] n = n ^ c ^ k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih, piso, ← pow_mul, pow_succ']

/-- **Con una cantidad fija de pisos, el costo sigue siendo polinomial.** -/
theorem pisos_fijos (c k : ℕ) : Acotada (fun n => (piso c)^[k] n) :=
  iterada_fija (piso_acotada c) k

/-- **Con `n` pisos, no.** Si `c ≥ 2`, apilar tantos pisos como mide la entrada da `2^(c^n)`, que no queda bajo
ningún polinomio. -/
theorem pisos_crecientes_rompen {c : ℕ} (hc : 2 ≤ c) : ¬ Acotada (fun n => (piso c)^[n] 2) := by
  rintro ⟨p, hp⟩
  apply dos_pow_no_acotada
  refine ⟨p, fun n => le_trans ?_ (hp n)⟩
  show 2 ^ n ≤ (piso c)^[n] 2
  rw [piso_iter]
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hc n))

end Cerradura
end Sagitta.Map
