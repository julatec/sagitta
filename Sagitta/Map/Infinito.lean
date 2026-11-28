import Sagitta.Map.Finitud
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Cofinite

/-!
# Irse al infinito sin tocarlo: las dos contradicciones

La propuesta (José, 24 nov 2026): intentar las dos contradicciones, «el circuito polinomial existe» y «no existe», y
ver adónde llevan. Y la intuición: irse al infinito sin tocarlo y encontrar ahí un circuito que cumpla.

**El infinito sin tocarlo** tiene una forma precisa: un **largo infinito**, dado por un ultrafiltro no principal `U`
sobre ℕ (`↑U ≤ cofinite`). «En el largo infinito `U` vale `P`» es `∀ᶠ n in U, P n`. Es el largo no estándar de un
ultrapoder (Łoś): desde afuera es infinito; desde adentro se porta como un largo más.

## Lo que se prueba

* **Un largo infinito es «infinitas veces»** (`io_iff_largo_infinito`): `P` vale en algún largo infinito si y solo si
  vale en infinitos largos finitos.
* **En todo largo infinito hay un circuito óptimo** (`circuito_en_el_infinito`): por `tamMin_alcanzado`, en cada largo
  el óptimo existe, así que en el infinito también. La intuición de José se cumple: el circuito **está**. Lo que no se
  sabe es su tamaño.
* **La contradicción «existe»** (`en_pol_iff`, `psobrePoly_iff_infinito`): un costo es polinomial si y solo si **un
  mismo** polinomio estándar `c·(n+1)^k` lo acota en **todos** los largos infinitos.
* **La contradicción «no existe»** (`fuera_de_pol_iff`, `fuera_iff_largo_infinito`): un costo no es polinomial si y
  solo si hay **un** largo infinito donde le gana a **todo** polinomio estándar a la vez. La construcción elige, para
  cada `m`, un largo `g m > m` donde el costo pasa de `m·(n+1)^m`, y empuja el hiperfiltro por `g`.
* **Un circuito que solo existe en el límite** (`existe_solo_en_el_limite`): un problema de verdad (`soloEnElLimite`:
  `false` en los largos pares, la función difícil de Shannon en los impares) con un largo infinito donde su circuito
  óptimo tiene **una** compuerta, y que aun así no tiene circuitos polinomiales.
* **El infinito solo no decide** (`ambos_a_la_vez`): un mismo costo puede ser chico (cero) en un largo infinito y
  superpolinomial en otro. Encontrar un circuito chico en **un** largo infinito da «infinitas veces», nunca «siempre».

## Adónde lleva

Las dos contradicciones se dejan escribir y ninguna se cierra sola.

* Suponer que el circuito polinomial existe obliga a un **único** exponente estándar en **todos** los largos infinitos.
* Suponer que no existe da **un** largo infinito donde SAT necesita más que cualquier polinomio estándar.

Para contradecir hay que **volver**: llevar lo que pasa en el largo infinito a todos los largos, o a una prueba. Ese
viaje de vuelta es el que hacen los modelos no estándar de la aritmética acotada: si S¹₂ no
demuestra que SAT necesita circuitos grandes, hay un modelo con un largo infinito donde SAT tiene circuitos chicos.
Por el `ambos_a_la_vez`, con el ultrapoder de ℕ solo no alcanza; hace falta lo que la teoría demuestra.

## Lo que no

Nada se dice de SAT en particular: los enunciados valen para todo costo `T : ℕ → ℕ` y toda sucesión de óptimos. La
construcción usa el axioma de elección (los ultrafiltros no principales).
-/

open Filter

namespace Sagitta.Map
namespace Tiempo
namespace Infinito

open Finitud Shannon

/-- **Un largo infinito**: un ultrafiltro sobre ℕ que no está concentrado en ningún largo finito. -/
def LargoInfinito (U : Ultrafilter ℕ) : Prop := (U : Filter ℕ) ≤ cofinite

/-! ## Un largo infinito es «infinitas veces» -/

/-- **Ir al infinito sin tocarlo**: `P` vale en algún largo infinito si y solo si vale en infinitos largos. -/
theorem io_iff_largo_infinito (P : ℕ → Prop) :
    {n | P n}.Infinite ↔ ∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∀ᶠ n in (U : Filter ℕ), P n := by
  constructor
  · intro h
    have hf : ∃ᶠ n in cofinite, P n := frequently_cofinite_iff_infinite.2 h
    have : (cofinite ⊓ 𝓟 {n | P n}).NeBot := frequently_iff_neBot.1 hf
    refine ⟨Ultrafilter.of (cofinite ⊓ 𝓟 {n | P n}), (Ultrafilter.of_le _).trans inf_le_left, ?_⟩
    exact (Ultrafilter.of_le _).trans inf_le_right (mem_principal_self _)
  · rintro ⟨U, hU, hP⟩
    exact frequently_cofinite_iff_infinite.1 (hP.frequently.filter_mono hU)

/-! ## En todo largo infinito hay un circuito óptimo -/

/-- **El circuito está en el infinito**: en todo largo (finito o infinito) hay un circuito que decide el problema con
exactamente el tamaño mínimo. -/
theorem circuito_en_el_infinito (L : Problema) (U : Ultrafilter ℕ) :
    ∀ᶠ n in (U : Filter ℕ), ∃ (t : ℕ) (C : Circuito n t), calcula C = rebanada L n ∧ t = sucNat L n :=
  Eventually.of_forall fun n => by
    obtain ⟨t, C, hC, ht⟩ := tamMin_alcanzado (rebanada L n)
    refine ⟨t, C, hC, ?_⟩
    have := sucesion_eq L n
    rw [sucesion, ht] at this
    exact_mod_cast this

/-! ## Las dos contradicciones, para cualquier costo -/

/-- Lo que vale desde algún largo, con un polinomio, es polinomial: los primeros largos caben en la constante. -/
theorem pol_de_casi {T : ℕ → ℕ} {c k N : ℕ} (h : ∀ n ≥ N, T n ≤ c * (n + 1) ^ k) : T ∈ Pol := by
  refine ⟨c + ∑ i ∈ Finset.range N, T i, k, fun n => ?_⟩
  have hp : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  by_cases hn : N ≤ n
  · exact (h n hn).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · have : T n ≤ ∑ i ∈ Finset.range N, T i :=
      Finset.single_le_sum (f := T) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    calc T n ≤ (c + ∑ i ∈ Finset.range N, T i) * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hp

/-- **La contradicción «existe»**: un costo es polinomial si y solo si un mismo polinomio estándar lo acota en todos
los largos infinitos. -/
theorem en_pol_iff (T : ℕ → ℕ) :
    T ∈ Pol ↔ ∃ c k, ∀ U : Ultrafilter ℕ, LargoInfinito U → ∀ᶠ n in (U : Filter ℕ), T n ≤ c * (n + 1) ^ k := by
  constructor
  · rintro ⟨c, k, h⟩
    exact ⟨c, k, fun U _ => Eventually.of_forall h⟩
  · rintro ⟨c, k, h⟩
    have hfin : {n | c * (n + 1) ^ k < T n}.Finite := by
      by_contra hinf
      obtain ⟨U, hU, hmalo⟩ := (io_iff_largo_infinito _).1 hinf
      obtain ⟨n, h1, h2⟩ := ((h U hU).and hmalo).exists
      omega
    obtain ⟨N, hN⟩ := hfin.bddAbove
    exact pol_de_casi (c := c) (k := k) (N := N + 1) fun n hn => by
      by_contra hc
      have := hN (show n ∈ {n | c * (n + 1) ^ k < T n} from by simp only [Set.mem_ofPred_eq]; omega)
      omega

/-- **La contradicción «no existe»**: un costo no es polinomial si y solo si hay un largo infinito donde le gana a todo
polinomio estándar a la vez. -/
theorem fuera_de_pol_iff (T : ℕ → ℕ) :
    T ∉ Pol ↔ ∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∀ c k, ∀ᶠ n in (U : Filter ℕ), c * (n + 1) ^ k < T n := by
  constructor
  · intro hT
    -- Para cada `m`, los largos donde `T` pasa de `m·(n+1)^m` son infinitos.
    have hinf : ∀ m, {n | m * (n + 1) ^ m < T n}.Infinite := fun m hfin => by
      obtain ⟨N, hN⟩ := hfin.bddAbove
      exact hT (pol_de_casi (c := m) (k := m) (N := N + 1) fun n hn => by
        by_contra hc
        have := hN (show n ∈ {n | m * (n + 1) ^ m < T n} from by simp only [Set.mem_ofPred_eq]; omega)
        omega)
    choose g hg using fun m => (hinf m).exists_gt m
    have hgtop : Tendsto g atTop atTop := tendsto_atTop_mono (fun m => (hg m).2.le) tendsto_id
    refine ⟨(Ultrafilter.map g (hyperfilter ℕ)), ?_, fun c k => ?_⟩
    · show map g (hyperfilter ℕ : Filter ℕ) ≤ cofinite
      rw [Nat.cofinite_eq_atTop]
      exact (map_mono (hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)).trans hgtop
    · rw [Ultrafilter.coe_map, eventually_map]
      have hge : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), max c k ≤ j :=
        (hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le) (eventually_ge_atTop (max c k))
      refine hge.mono fun j hj => ?_
      have h1 : j * (g j + 1) ^ j < T (g j) := (hg j).1
      have h2 : c * (g j + 1) ^ k ≤ j * (g j + 1) ^ j :=
        Nat.mul_le_mul (le_of_max_le_left hj) (Nat.pow_le_pow_right (by omega) (le_of_max_le_right hj))
      omega
  · rintro ⟨U, -, hU⟩ ⟨c, k, h⟩
    obtain ⟨n, hn⟩ := (hU c k).exists
    have := h n
    omega

/-! ## Para circuitos: P/poly en el infinito -/

/-- **«Existe»**, para circuitos: un problema está en P/poly si y solo si un mismo polinomio estándar acota su
circuito óptimo en todos los largos infinitos. -/
theorem psobrePoly_iff_infinito (L : Problema) :
    L ∈ PsobrePoly ↔ ∃ c k, ∀ U : Ultrafilter ℕ, LargoInfinito U →
      ∀ᶠ n in (U : Filter ℕ), sucNat L n ≤ c * (n + 1) ^ k := by
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff, en_pol_iff]

/-- **«No existe»**, para circuitos: un problema está fuera de P/poly si y solo si hay un largo infinito donde su
circuito óptimo le gana a todo polinomio estándar. -/
theorem fuera_iff_largo_infinito (L : Problema) :
    L ∉ PsobrePoly ↔ ∃ U : Ultrafilter ℕ, LargoInfinito U ∧
      ∀ c k, ∀ᶠ n in (U : Filter ℕ), c * (n + 1) ^ k < sucNat L n := by
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff, fuera_de_pol_iff]

/-- Shannon, en el infinito: hay un problema con un largo infinito donde ningún polinomio estándar alcanza. -/
theorem shannon_en_el_infinito : ∃ L : Problema, ∃ U : Ultrafilter ℕ, LargoInfinito U ∧
    ∀ c k, ∀ᶠ n in (U : Filter ℕ), c * (n + 1) ^ k < sucNat L n := by
  obtain ⟨L, hL⟩ := existe_problema_fuera_de_PsobrePoly
  exact ⟨L, (fuera_iff_largo_infinito L).1 hL⟩

/-! ## El infinito solo no decide -/

/-- Un costo que vale `0` en los largos pares y `2ⁿ` en los impares. -/
def pendulo (n : ℕ) : ℕ := if n % 2 = 0 then 0 else 2 ^ n

/-- **Las dos cosas a la vez**: hay un largo infinito donde el costo es `0` y otro donde le gana a todo polinomio. Un
circuito chico en un largo infinito no da «siempre», solo «infinitas veces». -/
theorem ambos_a_la_vez :
    (∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∀ᶠ n in (U : Filter ℕ), pendulo n = 0) ∧
      ∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∀ c k, ∀ᶠ n in (U : Filter ℕ), c * (n + 1) ^ k < pendulo n := by
  constructor
  · refine (io_iff_largo_infinito _).1 ?_
    refine Set.infinite_of_injective_forall_mem (f := fun j => 2 * j) (fun a b h => by simpa using h) fun j => ?_
    simp [pendulo, Nat.mul_mod_right]
  · refine (fuera_de_pol_iff pendulo).1 ?_
    rintro ⟨c, k, h⟩
    obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
    have h1 := hN (2 * N + 1) (by omega)
    have h2 := h (2 * N + 1)
    have : pendulo (2 * N + 1) = 2 ^ (2 * N + 1) := by
      simp [pendulo, Nat.add_mod]
    omega

/-! ## Un circuito que solo existe en el límite

La imagen de José: un circuito o algoritmo que solo existe en el límite infinito. Aquí, un problema de verdad: en los
largos pares es la constante `false` (un circuito de una compuerta), en los impares es la función difícil de Shannon.
En un largo infinito par, su circuito tiene **una** compuerta; y aun así el problema no tiene circuitos polinomiales.
El circuito chico existe en el infinito, no en todos los largos finitos. -/

/-- `false` en los largos pares; la función difícil en los impares. -/
noncomputable def soloEnElLimite : Problema := fun x => if x.length % 2 = 0 then false else problemaDificil x

theorem calcula_falso (n : ℕ) : calcula (falso n) = fun _ => false := by
  funext x
  unfold calcula
  have : (falso n).2 = cableDe (0 : Fin 1) := Fin.ext (by simp [falso, cableDe])
  rw [this, cables_compuerta]
  simp [falso, lee, Op.aplica]

theorem rebanada_par {n : ℕ} (h : n % 2 = 0) : rebanada soloEnElLimite n = fun _ => false := by
  funext x; simp [rebanada, soloEnElLimite, h]

theorem rebanada_impar {n : ℕ} (h : n % 2 = 1) : rebanada soloEnElLimite n = dificil n := by
  rw [← rebanada_problemaDificil]
  funext x; simp [rebanada, soloEnElLimite, h]

theorem sucNat_par {n : ℕ} (h : n % 2 = 0) : sucNat soloEnElLimite n ≤ 1 := by
  have : sucesion soloEnElLimite n ≤ 1 := by
    rw [sucesion, rebanada_par h, tamMin]
    exact iInf_le_of_le 1 (iInf_le_of_le (falso n) (iInf_le_of_le (calcula_falso n) (by norm_num)))
  rw [sucesion_eq] at this; exact_mod_cast this

theorem sucNat_impar {n : ℕ} (h : n % 2 = 1) (hn : 5 ≤ n) : 2 ^ n / (8 * n) < sucNat soloEnElLimite n := by
  have : ((2 ^ n / (8 * n) : ℕ) : ℕ∞) < sucesion soloEnElLimite n := by
    rw [sucesion, rebanada_impar h]
    simp only [dificil, hn, ↓reduceDIte]
    exact Classical.choose_spec (existe_funcion_exponencial n hn)
  rw [sucesion_eq] at this; exact_mod_cast this

/-- **Solo existe en el límite.** Hay un problema con un largo infinito donde su circuito óptimo tiene a lo sumo una
compuerta, y que sin embargo no tiene circuitos polinomiales. -/
theorem existe_solo_en_el_limite :
    (∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∀ᶠ n in (U : Filter ℕ), sucNat soloEnElLimite n ≤ 1) ∧
      soloEnElLimite ∉ PsobrePoly := by
  constructor
  · obtain ⟨U, hU, hpar⟩ := (io_iff_largo_infinito (fun n => n % 2 = 0)).1
      (Set.infinite_of_injective_forall_mem (f := fun j => 2 * j) (fun a b h => by simpa using h)
        fun j => by simp [Nat.mul_mod_right])
    exact ⟨U, hU, hpar.mono fun n hn => sucNat_par hn⟩
  · rw [psobrePoly_iff_grado, gradoPol_lt_top_iff]
    rintro ⟨c, k, h⟩
    obtain ⟨N, hN⟩ := pol_menor_dos_pow (8 * c) (k + 1)
    set n := 2 * (N + 5) + 1
    have hn5 : 5 ≤ n := by omega
    have h1 := hN n (by omega)
    have h2 := sucNat_impar (show n % 2 = 1 by omega) hn5
    have h3 := h n
    -- `c·(n+1)^k · 8n < 2ⁿ`, así que `c·(n+1)^k ≤ 2ⁿ/(8n)`.
    have h4 : c * (n + 1) ^ k * (8 * n) ≤ 8 * c * (n + 1) ^ (k + 1) := by
      rw [pow_succ]; nlinarith [Nat.zero_le (c * (n + 1) ^ k)]
    have h5 : c * (n + 1) ^ k ≤ 2 ^ n / (8 * n) :=
      (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    omega

end Infinito
end Tiempo
end Sagitta.Map
