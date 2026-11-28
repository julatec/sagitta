import Sagitta.Map.FormaDelTiempo
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card

/-!
# Componer y repetir: los árboles de tiempo en las familias de Landau

Con las familias `O(g)` de Landau sobre `ℕ → ℕ`, este archivo separa dos maneras de «hacer `n` veces» algo polinomial.

* **Repetir sobre un estado que no crece se queda en `Pol`.** `O(n · Pol(n)) ⊆ Pol` (`pol_mul_n`), `Pol · Pol ⊆ Pol`
  (`pol_mul`), y componer un número **fijo** de veces también (`pol_iterate`). Si cada paso agrega a lo sumo una
  constante al tamaño, `n` pasos de costo polinomial cuestan un polinomio (`costo_iterado_aditivo`). Es la forma del
  tiempo de PIND y de la recursión limitada de Cobham.
* **Componer `n` veces una función polinomial no.** Doblar, `x ↦ 2x`, es lineal; su iterada `n ↦ doblar^[n] n = n · 2ⁿ`
  no está en `O(K)` para **ningún** `K ∈ Pol` (`iterada_doblar_escapa`), en particular tampoco en `O(Pol · Pol)`. Está en
  `Exp = O(2^Pol)` (`iterada_doblar_en_exp`). Elevar al cuadrado es cuadrático; su iterada `n^(2ⁿ)` escapa también de
  `Exp` (`iterada_cuadrar_no_exp`). Cada paso **multiplica** el tamaño, y eso se compone.
* **El árbol de tiempo.** En el árbol binario completo, el frente a tiempo `t` tiene `2ᵗ` configuraciones
  (`ncard_frente_binario`): simular con la construcción de subconjuntos (`FormaDelTiempo.lean`) arrastra un estado que
  escapa de toda `O(K)` polinomial (`frente_binario_escapa`). El levantamiento a `2^C` es una composición de ese tipo.

Lo que esto **no** dice: que no haya otra simulación polinomial. Eso sería `P ≠ NP`.
-/

open Filter Topology

namespace Sagitta.Map
namespace Tiempo

/-! ## Las familias de Landau -/

/-- **`f = O(g)`**: desde algún `N`, `f n ≤ C · g n`. -/
def EsO (f g : ℕ → ℕ) : Prop := ∃ C N, ∀ n ≥ N, f n ≤ C * g n

/-- La familia `O(g)`. -/
def O (g : ℕ → ℕ) : Set (ℕ → ℕ) := {f | EsO f g}

/-- **`Pol`**: las funciones acotadas por un polinomio, `f n ≤ c · (n + 1)ᵏ` para todo `n`. -/
def Pol : Set (ℕ → ℕ) := {f | ∃ c k, ∀ n, f n ≤ c * (n + 1) ^ k}

/-- **`Exp = O(2^Pol)`**: acotadas por `2^K(n)` con `K ∈ Pol`. -/
def Exp : Set (ℕ → ℕ) := {f | ∃ K ∈ Pol, ∀ n, f n ≤ 2 ^ K n}

theorem one_le_succ_pow (n k : ℕ) : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)

/-- **`Pol` es la unión de las `O((n+1)ᵏ)`**: la cota para todo `n` y la cota desde algún `N` son lo mismo. -/
theorem pol_iff_O (f : ℕ → ℕ) : f ∈ Pol ↔ ∃ k, f ∈ O (fun n => (n + 1) ^ k) := by
  constructor
  · rintro ⟨c, k, h⟩; exact ⟨k, c, 0, fun n _ => h n⟩
  · rintro ⟨k, C, N, h⟩
    refine ⟨C + ∑ i ∈ Finset.range N, f i, k, fun n => ?_⟩
    have hp := one_le_succ_pow n k
    by_cases hn : N ≤ n
    · calc f n ≤ C * (n + 1) ^ k := h n hn
        _ ≤ (C + ∑ i ∈ Finset.range N, f i) * (n + 1) ^ k := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    · have : f n ≤ ∑ i ∈ Finset.range N, f i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
      calc f n ≤ C + ∑ i ∈ Finset.range N, f i := by omega
        _ = (C + ∑ i ∈ Finset.range N, f i) * 1 := (mul_one _).symm
        _ ≤ (C + ∑ i ∈ Finset.range N, f i) * (n + 1) ^ k := Nat.mul_le_mul_left _ hp

/-! ## Lo que se queda en `Pol` -/

theorem pol_id : (fun n => n) ∈ Pol := ⟨1, 1, fun n => by simp⟩

theorem pol_const (a : ℕ) : (fun _ => a) ∈ Pol := ⟨a, 0, fun n => by simp⟩

theorem pol_add {f g : ℕ → ℕ} (hf : f ∈ Pol) (hg : g ∈ Pol) : (fun n => f n + g n) ∈ Pol := by
  obtain ⟨c, k, hf⟩ := hf
  obtain ⟨d, j, hg⟩ := hg
  refine ⟨c + d, k + j, fun n => ?_⟩
  have h1 : (n + 1) ^ k ≤ (n + 1) ^ (k + j) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have h2 : (n + 1) ^ j ≤ (n + 1) ^ (k + j) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  calc f n + g n ≤ c * (n + 1) ^ k + d * (n + 1) ^ j := Nat.add_le_add (hf n) (hg n)
    _ ≤ c * (n + 1) ^ (k + j) + d * (n + 1) ^ (k + j) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (c + d) * (n + 1) ^ (k + j) := by ring

/-- **`Pol · Pol ⊆ Pol`.** -/
theorem pol_mul {f g : ℕ → ℕ} (hf : f ∈ Pol) (hg : g ∈ Pol) : (fun n => f n * g n) ∈ Pol := by
  obtain ⟨c, k, hf⟩ := hf
  obtain ⟨d, j, hg⟩ := hg
  refine ⟨c * d, k + j, fun n => ?_⟩
  calc f n * g n ≤ (c * (n + 1) ^ k) * (d * (n + 1) ^ j) := Nat.mul_le_mul (hf n) (hg n)
    _ = c * d * (n + 1) ^ (k + j) := by ring

/-- **`O(n · Pol(n)) ⊆ Pol`**: hacer `n` veces algo polinomial, sobre un estado fijo, es polinomial. -/
theorem pol_mul_n {f : ℕ → ℕ} (hf : f ∈ Pol) : (fun n => n * f n) ∈ Pol := pol_mul pol_id hf

/-- **`Pol` se cierra por composición.** -/
theorem pol_comp {f g : ℕ → ℕ} (hf : f ∈ Pol) (hg : g ∈ Pol) : (fun n => f (g n)) ∈ Pol := by
  obtain ⟨c, k, hf⟩ := hf
  obtain ⟨d, j, hg⟩ := hg
  refine ⟨c * (d + 1) ^ k, j * k, fun n => ?_⟩
  have hp := one_le_succ_pow n j
  have hgn : g n + 1 ≤ (d + 1) * (n + 1) ^ j := by
    have := hg n; nlinarith
  calc f (g n) ≤ c * (g n + 1) ^ k := hf (g n)
    _ ≤ c * ((d + 1) * (n + 1) ^ j) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgn k)
    _ = c * (d + 1) ^ k * (n + 1) ^ (j * k) := by rw [mul_pow, ← pow_mul]; ring

/-- **Componer un número fijo de veces se queda en `Pol`.** -/
theorem pol_iterate {f : ℕ → ℕ} (hf : f ∈ Pol) (k : ℕ) : f^[k] ∈ Pol := by
  induction k with
  | zero => exact pol_id
  | succ k ih =>
    rw [Function.iterate_succ']
    exact pol_comp (f := f) (g := f^[k]) hf ih

/-- Si cada paso agrega a lo sumo `c`, `k` pasos agregan a lo sumo `c · k`. -/
theorem iterate_aditivo {f : ℕ → ℕ} {c : ℕ} (h : ∀ m, f m ≤ m + c) (k m : ℕ) : f^[k] m ≤ m + c * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc f (f^[k] m) ≤ f^[k] m + c := h _
      _ ≤ m + c * k + c := by omega
      _ = m + c * (k + 1) := by ring

/-- **El costo de `n` pasos que crecen de forma aditiva**: la suma de `p` sobre los `n` estados que recorre la iterada
desde `n`. -/
def costoIterado (f p : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, p (f^[i] n)

/-- **Repetir `n` veces un paso de costo polinomial, si el estado crece de a una constante, es polinomial.** Es la
forma del tiempo de PIND y de la recursión limitada: el «`n` · Pol(n)» de verdad. -/
theorem costo_iterado_aditivo {f p : ℕ → ℕ} {c : ℕ} (h : ∀ m, f m ≤ m + c) (hp : p ∈ Pol) :
    costoIterado f p ∈ Pol := by
  obtain ⟨a, k, hp⟩ := hp
  refine ⟨a * (c + 1) ^ k, k + 1, fun n => ?_⟩
  have paso : ∀ i ∈ Finset.range n, p (f^[i] n) ≤ a * (c + 1) ^ k * (n + 1) ^ k := by
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    have hs : f^[i] n + 1 ≤ (c + 1) * (n + 1) := by
      have := iterate_aditivo h i n; nlinarith
    calc p (f^[i] n) ≤ a * (f^[i] n + 1) ^ k := hp _
      _ ≤ a * ((c + 1) * (n + 1)) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs k)
      _ = a * (c + 1) ^ k * (n + 1) ^ k := by rw [mul_pow]; ring
  calc costoIterado f p n ≤ ∑ _i ∈ Finset.range n, a * (c + 1) ^ k * (n + 1) ^ k := Finset.sum_le_sum paso
    _ = n * (a * (c + 1) ^ k * (n + 1) ^ k) := by simp
    _ ≤ (n + 1) * (a * (c + 1) ^ k * (n + 1) ^ k) := Nat.mul_le_mul_right _ (Nat.le_succ n)
    _ = a * (c + 1) ^ k * (n + 1) ^ (k + 1) := by ring

/-! ## El polinomio pierde contra la exponencial -/

/-- **Todo polinomio queda debajo de `2ⁿ`** desde algún punto. Por la cota de Mathlib sobre `nᵏ / rⁿ → 0`. -/
theorem pol_menor_dos_pow (c k : ℕ) : ∃ N, ∀ n ≥ N, c * (n + 1) ^ k < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2 : ℝ)) (by norm_num)
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k / 2 ^ (n + 1)) atTop (𝓝 0) :=
    h.comp (tendsto_add_atTop_nat 1)
  have hpos : (0 : ℝ) < 1 / (2 * ((c : ℝ) + 1)) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.eventually (gt_mem_nhds hpos))
  refine ⟨N, fun n hn => ?_⟩
  have hlt := hN n hn
  simp only [Nat.cast_add, Nat.cast_one] at hlt
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hc : (0 : ℝ) < 2 * ((c : ℝ) + 1) := by positivity
  rw [div_lt_div_iff₀ h2 hc, one_mul] at hlt
  have hx : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ k := by positivity
  have key : (c : ℝ) * ((n : ℝ) + 1) ^ k < 2 ^ n := by
    rw [pow_succ] at hlt
    nlinarith
  exact_mod_cast key

/-! ## Lo que escapa: componer `n` veces -/

/-- **La iterada diagonal**: `f` compuesta `n` veces, aplicada a `n`. -/
def iterada (f : ℕ → ℕ) (n : ℕ) : ℕ := f^[n] n

/-- Doblar: lineal. -/
def doblar (n : ℕ) : ℕ := 2 * n

/-- Elevar al cuadrado: cuadrático. -/
def cuadrar (n : ℕ) : ℕ := n ^ 2

theorem pol_doblar : doblar ∈ Pol := ⟨2, 1, fun n => by simp only [doblar, pow_one]; omega⟩

theorem pol_cuadrar : cuadrar ∈ Pol :=
  ⟨1, 2, fun n => by simp only [cuadrar, one_mul]; exact Nat.pow_le_pow_left (Nat.le_succ n) 2⟩

theorem iterate_doblar (k m : ℕ) : doblar^[k] m = 2 ^ k * m := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, doblar, pow_succ]; ring

theorem iterate_cuadrar (k m : ℕ) : cuadrar^[k] m = m ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, cuadrar, ← pow_mul, pow_succ]

/-- **Componer `n` veces una función lineal escapa de toda `O(K)` polinomial**: `doblar` está en `Pol`, pero
`n ↦ doblar^[n] n = n · 2ⁿ` no está en `O(K)` para ningún `K ∈ Pol`. -/
theorem iterada_doblar_escapa : ∀ K ∈ Pol, iterada doblar ∉ O K := by
  rintro K ⟨c, k, hK⟩ ⟨C, N, hO⟩
  obtain ⟨N', hN'⟩ := pol_menor_dos_pow (C * c) k
  set n := max N N' + 1
  have h1 : 2 ^ n ≤ iterada doblar n := by
    rw [iterada, iterate_doblar]; exact Nat.le_mul_of_pos_right _ (by omega)
  have h2 := hO n (by omega)
  have h3 : C * K n ≤ C * c * (n + 1) ^ k := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (hK n)
  have h4 := hN' n (by omega)
  omega

/-- En particular, **no está en `O(Pol · Pol)`**: ni en `O(p · q)` con `p, q ∈ Pol`. -/
theorem iterada_doblar_no_pol_por_pol {p q : ℕ → ℕ} (hp : p ∈ Pol) (hq : q ∈ Pol) :
    iterada doblar ∉ O (fun n => p n * q n) :=
  iterada_doblar_escapa _ (pol_mul hp hq)

theorem iterada_doblar_no_pol : iterada doblar ∉ Pol := fun h => by
  obtain ⟨k, hk⟩ := (pol_iff_O _).1 h
  exact iterada_doblar_escapa _ ⟨1, k, fun n => by simp⟩ hk

/-- **Pero está en `Exp`**: `n · 2ⁿ ≤ 2^(2n)`. La composición de `n` lineales es exponencial simple. -/
theorem iterada_doblar_en_exp : iterada doblar ∈ Exp := by
  refine ⟨fun n => 2 * n, ⟨2, 1, fun n => by simp only [pow_one]; omega⟩, fun n => ?_⟩
  show doblar^[n] n ≤ 2 ^ (2 * n)
  rw [iterate_doblar, two_mul, pow_add]
  exact Nat.mul_le_mul_left _ n.lt_two_pow_self.le

/-- **Componer `n` veces una cuadrática escapa también de `Exp`**: `n^(2ⁿ)` no se acota por `2^K(n)` con `K ∈ Pol`. -/
theorem iterada_cuadrar_no_exp : iterada cuadrar ∉ Exp := by
  rintro ⟨K, ⟨c, k, hK⟩, hE⟩
  obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
  set n := max N 2
  have h1 : 2 ^ (2 ^ n) ≤ iterada cuadrar n := by
    rw [iterada, iterate_cuadrar]; exact Nat.pow_le_pow_left (by omega) _
  have h2 : 2 ^ (2 ^ n) ≤ 2 ^ K n := h1.trans (hE n)
  have h3 : 2 ^ n ≤ K n := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have h4 := hN n (by omega)
  have h5 := hK n
  omega

/-! ## El árbol de tiempo -/

/-- **El árbol binario completo**: cada configuración (una lista de bits) tiene dos siguientes. -/
def ramaBinaria : Paso (List Bool) := fun l => {false :: l, true :: l}

theorem frente_binario (t : ℕ) : frente ramaBinaria t [] = {l | l.length = t} := by
  induction t with
  | zero =>
    ext l; simp only [frente, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟩; rfl
    · intro h; rw [List.length_eq_zero_iff] at h; subst h; exact .cero _
  | succ t ih =>
    ext l
    have : l ∈ frente ramaBinaria (t + 1) [] ↔ ∃ d, Alcanza ramaBinaria t [] d ∧ l ∈ ramaBinaria d := by
      simp only [frente, Set.mem_ofPred_eq]
      constructor
      · rintro (_ | ⟨h, he⟩); exact ⟨_, h, he⟩
      · rintro ⟨d, h, he⟩; exact .paso h he
    rw [this]
    simp only [Set.ext_iff, frente, Set.mem_ofPred_eq] at ih
    simp only [ih, ramaBinaria, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨d, hd, rfl | rfl⟩ <;> simp [hd]
    · intro h
      match l, h with
      | b :: d, h => exact ⟨d, by simpa using h, by cases b <;> simp⟩

/-- **El frente a tiempo `t` tiene `2ᵗ` configuraciones.** -/
theorem ncard_frente_binario (t : ℕ) : (frente ramaBinaria t []).ncard = 2 ^ t := by
  rw [frente_binario, ← Nat.card_coe_set_eq]
  have : Nat.card {l : List Bool | l.length = t} = Nat.card (List.Vector Bool t) := rfl
  rw [this, Nat.card_eq_fintype_card, card_vector, Fintype.card_bool]

/-- **El estado de la simulación por subconjuntos escapa de toda `O(K)` polinomial**: en el árbol binario completo, el
tamaño del frente a tiempo `t` no está en `O(K)` para ningún `K ∈ Pol`. -/
theorem frente_binario_escapa : ∀ K ∈ Pol, (fun t => (frente ramaBinaria t []).ncard) ∉ O K := by
  rintro K ⟨c, k, hK⟩ ⟨C, N, hO⟩
  obtain ⟨N', hN'⟩ := pol_menor_dos_pow (C * c) k
  set n := max N N'
  have h2 : 2 ^ n ≤ C * K n := by simpa [ncard_frente_binario] using hO n (by omega)
  have h3 : C * K n ≤ C * c * (n + 1) ^ k := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (hK n)
  have h4 := hN' n (by omega)
  omega

end Tiempo
end Sagitta.Map
