import Sagitta.Map.Clases
import Sagitta.Map.Shannon
import Sagitta.Map.TodaFuncion
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Circuitos y la sucesión de tamaños mínimos

La analogía «iterar sobre n»: para un problema `L` y un tamaño `n`, `sucesion L n` es el número de compuertas del
menor circuito que decide `L` en las entradas de `n` bits. La versión no uniforme de P ≠ NP habla del crecimiento
de esa sucesión.

Desde el 22 nov 2026 hay un solo modelo de circuito, el de `Shannon.lean`, con los índices acotados. El modelo
anterior (una lista de compuertas que podían pedir cualquier índice) se retiró: con él había infinitos circuitos de
cada tamaño y el conteo de Shannon no se podía hacer.
-/

namespace Sagitta.Map

open Shannon

/-- `L` restringido a las entradas de `n` bits: una función booleana de `n` variables. -/
def rebanada (L : Problema) (n : ℕ) : (Fin n → Bool) → Bool := fun x => L (List.ofFn x)

/-- El número de compuertas del menor circuito que calcula `f`. Vale en `ℕ∞` por la forma de la definición, pero
nunca es `⊤`: toda función tiene algún circuito (`tamMin_lt_top`). -/
noncomputable def tamMin {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ∞ :=
  ⨅ (t : ℕ) (C : Circuito n t) (_ : calcula C = f), (t : ℕ∞)

/-- **La sucesión.** El tamaño del menor circuito que decide `L` en las entradas de `n` bits. -/
noncomputable def sucesion (L : Problema) (n : ℕ) : ℕ∞ := tamMin (rebanada L n)

/-- **Nunca infinito.** Toda función tiene algún circuito (`TodaFuncion.lean`), así que su tamaño mínimo es finito. -/
theorem tamMin_lt_top {n : ℕ} (f : (Fin n → Bool) → Bool) : tamMin f < ⊤ := by
  obtain ⟨t, C, hC⟩ := toda_funcion_calculable f
  exact lt_of_le_of_lt (iInf_le_of_le t (iInf_le_of_le C (iInf_le_of_le hC le_rfl))) (ENat.coe_lt_top t)

/-- Cada término de la sucesión es un número natural. -/
theorem sucesion_lt_top (L : Problema) (n : ℕ) : sucesion L n < ⊤ := tamMin_lt_top _

/-- Si ningún circuito de a lo sumo `s` compuertas calcula `f`, su tamaño mínimo pasa de `s`. -/
theorem lt_tamMin {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ∀ t ≤ s, ∀ C : Circuito n t, calcula C ≠ f) : (s : ℕ∞) < tamMin f := by
  have hle : ((s + 1 : ℕ) : ℕ∞) ≤ tamMin f := by
    refine le_iInf fun t => le_iInf fun C => le_iInf fun hC => ?_
    have : s < t := by
      by_contra hts
      exact h t (by omega) C hC
    exact_mod_cast this
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self s) hle

/-- **Shannon, en el lenguaje de la sucesión.** Para todo `n ≥ 5` hay una función de `n` bits cuyo menor circuito
tiene más de `2ⁿ / (8n)` compuertas. -/
theorem existe_funcion_exponencial (n : ℕ) (hn : 5 ≤ n) :
    ∃ f : (Fin n → Bool) → Bool, ((2 ^ n / (8 * n) : ℕ) : ℕ∞) < tamMin f := by
  obtain ⟨f, hf⟩ := shannon_asintotico n hn
  exact ⟨f, lt_tamMin hf⟩

/-- Para cada `n`, una función de `n` bits difícil (la que da Shannon desde `n = 5`; antes, cualquiera). Se elige
con `Classical.choose`: el teorema dice que existe, no cuál es. -/
noncomputable def dificil (n : ℕ) : (Fin n → Bool) → Bool :=
  if h : 5 ≤ n then Classical.choose (existe_funcion_exponencial n h) else fun _ => false

/-- La función difícil de tamaño `n`, leída sobre una lista (los bits que falten valen `false`). Separarla así deja
la longitud como un número, no como parte de un tipo, y permite reescribirla. -/
noncomputable def dificilEn (n : ℕ) (x : List Bool) : Bool := dificil n (fun i => x.getD i false)

/-- **Un problema cuya sucesión crece exponencialmente.** En las entradas de `n` bits, `L` calcula la función
difícil de ese tamaño. -/
noncomputable def problemaDificil : Problema :=
  fun x => dificilEn x.length x

theorem rebanada_problemaDificil (n : ℕ) : rebanada problemaDificil n = dificil n := by
  funext x
  change dificilEn (List.ofFn x).length (List.ofFn x) = dificil n x
  rw [List.length_ofFn]
  unfold dificilEn
  congr 1
  funext i
  simp [i.isLt]

/-- **Existe un problema cuya sucesión de tamaños mínimos es exponencial:** para todo `n ≥ 5`, decidirlo en las
entradas de `n` bits exige más de `2ⁿ / (8n)` compuertas. No dice nada de `NP`: el problema no es de esa clase. -/
theorem existe_problema_exponencial :
    ∃ L : Problema, ∀ n, 5 ≤ n → ((2 ^ n / (8 * n) : ℕ) : ℕ∞) < sucesion L n := by
  refine ⟨problemaDificil, fun n hn => ?_⟩
  rw [sucesion, rebanada_problemaDificil]
  simp only [dificil, hn, ↓reduceDIte]
  exact Classical.choose_spec (existe_funcion_exponencial n hn)

/-! ## P/poly y la versión no uniforme de P ≠ NP -/

/-- `L` tiene circuitos de tamaño polinomial. -/
def TieneCircuitosPolinomiales (L : Problema) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n : ℕ, sucesion L n ≤ ((p.eval n : ℕ) : ℕ∞)

/-- **P/poly**: los problemas con circuitos polinomiales. -/
def PsobrePoly : Clase := {L | TieneCircuitosPolinomiales L}

/-- P ⊆ P/poly. Teorema conocido (un cómputo polinomial se despliega en un circuito polinomial); aquí
queda como hipótesis explícita. -/
def PSubPsobrePoly : Prop := P ⊆ PsobrePoly

/-- **Abierto: P ≠ NP no uniforme.** Algún problema de NP no tiene circuitos polinomiales: su sucesión
de tamaños mínimos crece más que todo polinomio. -/
def NPSinCircuitosPolinomiales : Prop := ¬ (NP ⊆ PsobrePoly)

/-- La versión no uniforme implica P ≠ NP. -/
theorem pDistintoNP_of_sinCircuitos (h : PSubPsobrePoly) (hn : NPSinCircuitosPolinomiales) :
    PDistintoNP := by
  intro e
  apply hn
  rw [← show P = NP from e]
  exact h

/-! ## Un problema fuera de P/poly

Falta una sola pieza: que `2ⁿ / (8n)` termina pasando a todo polinomio. Con eso, el problema de
`existe_problema_exponencial` no tiene circuitos polinomiales. -/

/-- Con coeficientes naturales, un polinomio evaluado en `n ≥ 1` no pasa de (suma de coeficientes) · nᵈ. -/
theorem eval_le_mul_pow (p : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range (x := 1), Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn (by simp at hi; omega))

/-- **La exponencial le gana a la potencia.** Para cualesquiera `C` y `k`, desde algún `N` en adelante
`C · nᵏ < 2ⁿ`. Sale del límite `nᵏ / 2ⁿ → 0` de Mathlib. -/
theorem mul_pow_lt_dos_pow (C k : ℕ) : ∃ N, ∀ n ≥ N, C * n ^ k < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2 : ℝ)) (by norm_num)
  have hpos : (0 : ℝ) < 1 / ((C : ℝ) + 1) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds hpos))
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h1
  have h3 : ((C * n ^ k : ℕ) : ℝ) < 2 ^ n := by
    push_cast
    nlinarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) k]
  exact_mod_cast h3

/-- Todo polinomio queda, desde algún `N`, por debajo de `2ⁿ / (8n)`. -/
theorem eval_le_cota_eventualmente (p : Polynomial ℕ) :
    ∃ N, ∀ n ≥ N, p.eval n ≤ 2 ^ n / (8 * n) := by
  obtain ⟨N, hN⟩ := mul_pow_lt_dos_pow (8 * p.eval 1) (p.natDegree + 1)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  rw [Nat.le_div_iff_mul_le (by omega)]
  calc p.eval n * (8 * n) ≤ p.eval 1 * n ^ p.natDegree * (8 * n) :=
        Nat.mul_le_mul_right _ (eval_le_mul_pow p hn1)
    _ = 8 * p.eval 1 * n ^ (p.natDegree + 1) := by ring
    _ ≤ 2 ^ n := (hN n (le_of_max_le_left hn)).le

/-- **Existe un problema fuera de P/poly.** Su sucesión de tamaños mínimos pasa de todo polinomio. Como el de
`existe_problema_exponencial`, no es de `NP`: esto no acerca a P ≠ NP, solo muestra que la clase P/poly no lo
abarca todo. -/
theorem existe_problema_fuera_de_PsobrePoly : ∃ L : Problema, L ∉ PsobrePoly := by
  obtain ⟨L, hL⟩ := existe_problema_exponencial
  refine ⟨L, fun h => ?_⟩
  obtain ⟨p, hp⟩ : TieneCircuitosPolinomiales L := h
  obtain ⟨N, hN⟩ := eval_le_cota_eventualmente p
  have h1 := hL (max N 5) (le_max_right _ _)
  have h3 : ((p.eval (max N 5) : ℕ) : ℕ∞) ≤ ((2 ^ max N 5 / (8 * max N 5) : ℕ) : ℕ∞) := by
    exact_mod_cast hN _ (le_max_left _ _)
  exact lt_irrefl _ (h1.trans_le ((hp _).trans h3))

end Sagitta.Map
