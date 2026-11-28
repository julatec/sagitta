import Sagitta.Map.Landau
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Order.Basic

/-!
# La cebolla: la jerarquía de crecimiento rápido, capa por capa

`Landau.lean` mostró que componer `n` veces una función polinomial se sale de `Pol`. Aquí eso se vuelve un principio:
**la composición diagonal siempre tira hacia arriba**. La jerarquía de crecimiento rápido (Wainer; Mathlib la tiene bajo
`ε₀` como `ONote.fastGrowing`) se define justo así:

* `F 0 = sucesor`;
* `F (k+1) n = (F k)^[n] n`: el nivel siguiente es la **iterada diagonal** del anterior (`F_succ`);
* `Fω n = F n n`: en el límite, la diagonal **entre** niveles.

Coincide con Mathlib en los primeros niveles (`F_eq_fastGrowing_*`): `F 1` es doblar y `F 2 n = n · 2ⁿ`, la iterada que
en `Landau.lean` escapaba de `Pol`.

**Las capas.** `Capa k` son las funciones acotadas por una iterada **fija** de `F k`. Es una cebolla:

1. cada capa es cerrada por composición (`capa_comp`) y por iterar un número fijo de veces (`capa_iterate`);
2. las capas crecen (`capa_mono`) y cada una contiene su función (`F_mem_capa`);
3. **la diagonal perfora la capa**: `F (k+1) ∉ Capa k` (`F_succ_no_capa`), así que las capas crecen estrictamente;
4. `Pol` cae entre la capa 1 y la 2: `Pol ⊆ Capa 2` (`pol_sub_capa_dos`) y `cuadrar ∉ Capa 1`;
5. **en el límite**, `Fω` escapa de todas las capas finitas (`Fω_no_capa`).

**La topología de la cebolla.** Las capas se indexan por `ω + 1 = ℕ∞` con la topología del orden. Cada capa finita es
un punto **aislado** (`isOpen_capa_finita`); la capa `ω` no lo es: es un punto de **acumulación** (`no_isOpen_top`,
`tiende_a_omega`). La capa límite es la unión de las anteriores (`capaE_top`), y aun así la diagonal `Fω` queda fuera
(`Fω_no_capaE_top`): el límite se alcanza por abajo, pero la composición diagonal sigue tirando hacia arriba.
-/

open Filter Topology Set

namespace Sagitta.Map
namespace Tiempo

/-! ## La jerarquía -/

/-- **La jerarquía de crecimiento rápido**, niveles finitos. -/
def F : ℕ → ℕ → ℕ
  | 0 => Nat.succ
  | k + 1 => iterada (F k)

/-- **El nivel siguiente es la iterada diagonal del anterior.** -/
theorem F_succ (k n : ℕ) : F (k + 1) n = (F k)^[n] n := rfl

/-- **El límite ω**: la diagonal entre niveles. -/
def Fω (n : ℕ) : ℕ := F n n

theorem F_eq_fastGrowing_zero : F 0 = ONote.fastGrowing 0 := by rw [ONote.fastGrowing_zero]; rfl

theorem F_uno : F 1 = doblar := by
  funext n; rw [F_succ]; simp only [F]; rw [Nat.succ_iterate]; simp [doblar, two_mul]

theorem F_eq_fastGrowing_one : F 1 = ONote.fastGrowing 1 := by
  rw [F_uno, ONote.fastGrowing_one]; rfl

theorem F_dos (n : ℕ) : F 2 n = 2 ^ n * n := by rw [F_succ, F_uno, iterate_doblar]

theorem F_eq_fastGrowing_two : F 2 = ONote.fastGrowing 2 := by
  funext n; rw [F_dos, ONote.fastGrowing_two]

/-- `F 2` es la iterada de doblar de `Landau.lean`. -/
theorem F_dos_eq_iterada : F 2 = iterada doblar := by rw [show (2 : ℕ) = 1 + 1 from rfl, F, F_uno]

/-! ## Crecimiento: inflación y monotonía -/

/-- **Cada nivel infla**: `x ≤ F k x`, y estrictamente si `x ≥ 1`. -/
theorem F_infla (k : ℕ) : ∀ x, x ≤ F k x ∧ (1 ≤ x → x < F k x) := by
  induction k with
  | zero => intro x; simp [F]
  | succ k ih =>
    -- iterar algo que infla, infla; y si infla estrictamente, `j` veces suma al menos `j`
    have it : ∀ j y, y ≤ (F k)^[j] y ∧ (1 ≤ y → y + j ≤ (F k)^[j] y) := by
      intro j
      induction j with
      | zero => intro y; simp
      | succ j ihj =>
        intro y
        rw [Function.iterate_succ_apply']
        obtain ⟨h1, h2⟩ := ihj y
        refine ⟨h1.trans (ih _).1, fun hy => ?_⟩
        have : 1 ≤ (F k)^[j] y := le_trans hy h1
        have := (ih _).2 this
        have := h2 hy
        omega
    intro x
    rw [F_succ]
    exact ⟨(it x x).1, fun hx => by have := (it x x).2 hx; omega⟩

theorem F_iter_infla (k j y : ℕ) (hy : 1 ≤ y) : y + j ≤ (F k)^[j] y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h1 : 1 ≤ (F k)^[j] y := by omega
    have := (F_infla k _).2 h1
    omega

theorem F_iter_ge (k j y : ℕ) : y ≤ (F k)^[j] y := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.trans (F_infla k _).1

/-- **Cada nivel es estrictamente creciente.** -/
theorem F_strictMono (k : ℕ) : StrictMono (F k) := by
  induction k with
  | zero => exact fun a b h => Nat.succ_lt_succ h
  | succ k ih =>
    refine strictMono_nat_of_lt_succ fun n => ?_
    rw [F_succ, F_succ, Function.iterate_succ_apply']
    calc (F k)^[n] n < (F k)^[n] (n + 1) := (ih.iterate n) (Nat.lt_succ_self n)
      _ ≤ F k ((F k)^[n] (n + 1)) := (F_infla k _).1

/-- **Subir de nivel no baja**, para argumentos `≥ 1`. -/
theorem F_le_F_succ (k y : ℕ) (hy : 1 ≤ y) : F k y ≤ F (k + 1) y := by
  rw [F_succ]
  obtain ⟨j, rfl⟩ : ∃ j, y = j + 1 := ⟨y - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  exact F_iter_ge k j _

theorem F_iter_le_succ (k m y : ℕ) (hy : 1 ≤ y) : (F k)^[m] y ≤ (F (k + 1))^[m] y := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 : 1 ≤ (F k)^[m] y := le_trans hy (F_iter_ge k m y)
    calc F k ((F k)^[m] y) ≤ F k ((F (k + 1))^[m] y) := (F_strictMono k).monotone ih
      _ ≤ F (k + 1) ((F (k + 1))^[m] y) := F_le_F_succ k _ (le_trans h1 ih)

theorem F_le_F_de_le {k l y : ℕ} (hkl : k ≤ l) (hy : 1 ≤ y) : F k y ≤ F l y := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact ih.trans (F_le_F_succ l y hy)

/-! ## Las capas -/

/-- **La capa `k`**: lo acotado por una iterada fija de `F k`, con el argumento corrido para no depender de lo que pasa
en 0. -/
def Capa (k : ℕ) : Set (ℕ → ℕ) := {f | ∃ m, ∀ n, f n ≤ (F k)^[m] (n + m)}

theorem F_mem_capa (k : ℕ) : F k ∈ Capa k :=
  ⟨1, fun n => by simpa using (F_strictMono k).monotone (Nat.le_succ n)⟩

/-- **Cada capa es cerrada por composición.** -/
theorem capa_comp {k : ℕ} {f g : ℕ → ℕ} (hf : f ∈ Capa k) (hg : g ∈ Capa k) : (fun n => f (g n)) ∈ Capa k := by
  obtain ⟨a, hf⟩ := hf
  obtain ⟨b, hg⟩ := hg
  refine ⟨a + b, fun n => ?_⟩
  have hmono := fun j => (F_strictMono k).iterate j
  -- `F^[b]` estrictamente creciente suma al menos lo que se le suma al argumento
  have hsuma : (F k)^[b] (n + b) + a ≤ (F k)^[b] (n + b + a) := by
    have := (hmono b).add_le_nat a (n + b)
    rw [show n + b + a = a + (n + b) by omega]
    omega
  calc f (g n) ≤ (F k)^[a] (g n + a) := hf _
    _ ≤ (F k)^[a] ((F k)^[b] (n + b) + a) := (hmono a).monotone (by have := hg n; omega)
    _ ≤ (F k)^[a] ((F k)^[b] (n + b + a)) := (hmono a).monotone hsuma
    _ = (F k)^[a + b] (n + (a + b)) := by rw [Function.iterate_add_apply]; congr 2; omega

theorem capa_id (k : ℕ) : (fun n => n) ∈ Capa k := ⟨0, fun n => by simp⟩

/-- **Iterar un número fijo de veces se queda en la capa.** -/
theorem capa_iterate {k : ℕ} {f : ℕ → ℕ} (hf : f ∈ Capa k) (j : ℕ) : f^[j] ∈ Capa k := by
  induction j with
  | zero => exact capa_id k
  | succ j ih => rw [Function.iterate_succ']; exact capa_comp (f := f) (g := f^[j]) hf ih

/-- **Las capas crecen.** -/
theorem capa_mono (k : ℕ) : Capa k ⊆ Capa (k + 1) := by
  rintro f ⟨m, hf⟩
  refine ⟨m, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hpos
  · have hm : m = 0 := by omega
    subst hm; simpa using hf n
  · exact (hf n).trans (F_iter_le_succ k m _ hpos)

theorem capa_mono' {k l : ℕ} (h : k ≤ l) : Capa k ⊆ Capa l := by
  induction l, h using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact ih.trans (capa_mono l)

/-- **La diagonal le gana a toda iterada fija**: para `n ≥ 2m + 1`, `(F k)^[m] (n + m) < F (k+1) n`. -/
theorem F_succ_gana (k m n : ℕ) (hn : 2 * m + 1 ≤ n) : (F k)^[m] (n + m) < F (k + 1) n := by
  rw [F_succ]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + m := ⟨n - m, by omega⟩
  rw [add_comm j m, Function.iterate_add_apply]
  apply (F_strictMono k).iterate m
  have := F_iter_infla k j (m + j) (by omega)
  omega

/-- **La diagonal perfora la capa**: `F (k+1) ∉ Capa k`. -/
theorem F_succ_no_capa (k : ℕ) : F (k + 1) ∉ Capa k := by
  rintro ⟨m, h⟩
  have := h (2 * m + 1)
  have := F_succ_gana k m (2 * m + 1) le_rfl
  omega

/-- **Las capas crecen estrictamente.** -/
theorem capa_estricta (k : ℕ) : Capa k ⊂ Capa (k + 1) :=
  ⟨capa_mono k, fun h => F_succ_no_capa k (h (F_mem_capa (k + 1)))⟩

/-! ## Dónde cae `Pol` -/

/-- **`Pol ⊆ Capa 2`**: todo polinomio queda debajo de una iterada fija de `n · 2ⁿ`. -/
theorem pol_sub_capa_dos : Pol ⊆ Capa 2 := by
  rintro f ⟨c, k, hf⟩
  obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
  set m := c * (N + 1) ^ k + 1
  refine ⟨m, fun n => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hbase : c * (n + 1) ^ k ≤ 2 ^ (n + m) := by
    by_cases hn : N ≤ n
    · exact (hN n hn).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · calc c * (n + 1) ^ k ≤ c * (N + 1) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
        _ ≤ m := Nat.le_succ _
        _ ≤ 2 ^ m := m.lt_two_pow_self.le
        _ ≤ 2 ^ (n + m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF2 : 2 ^ (n + m) ≤ F 2 (n + m) := by
    rw [F_dos]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hit : F 2 (n + m) ≤ (F 2)^[m] (n + m) := by
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [hj, Function.iterate_succ_apply']
    exact (F_strictMono 2).monotone (F_iter_ge 2 j _)
  exact (hf n).trans (hbase.trans (hF2.trans hit))

/-- **El cuadrado no está en la capa 1**: la capa 1 es lo lineal (`(F 1)^[m] (n + m) = 2ᵐ (n + m)`). -/
theorem cuadrar_no_capa_uno : cuadrar ∉ Capa 1 := by
  rintro ⟨m, h⟩
  set n := 2 ^ m * 2 + 2 * m + 1
  have h1 := h n
  rw [F_uno, iterate_doblar] at h1
  simp only [cuadrar] at h1
  have : 2 ^ m * (n + m) < n ^ 2 := by
    have hn : 2 ^ m * 2 + m + 1 ≤ n := by omega
    nlinarith [Nat.one_le_two_pow (n := m)]
  omega

/-! ## El límite ω -/

/-- **`Fω` escapa de todas las capas finitas.** -/
theorem Fω_no_capa (k : ℕ) : Fω ∉ Capa k := by
  rintro ⟨m, h⟩
  set n := max (k + 1) (2 * m + 1)
  have h1 := h n
  have h2 := F_succ_gana k m n (le_max_right _ _)
  have h3 : F (k + 1) n ≤ F n n := F_le_F_de_le (le_max_left _ _) (by omega)
  simp only [Fω] at h1
  omega

/-! ## La topología de la cebolla -/

/-- **Las capas indexadas por `ω + 1 = ℕ∞`**: la capa `ω` es la unión de las finitas. -/
def CapaE : ℕ∞ → Set (ℕ → ℕ)
  | (k : ℕ) => Capa k
  | ⊤ => ⋃ k, Capa k

theorem capaE_coe (k : ℕ) : CapaE k = Capa k := rfl

theorem capaE_top : CapaE ⊤ = ⋃ k : ℕ, CapaE k := rfl

/-- **La cebolla es monótona** en `ω + 1`. -/
theorem capaE_mono : Monotone CapaE := by
  intro a b hab
  induction a using ENat.recTopCoe with
  | top => rw [top_le_iff.1 hab]
  | coe k =>
    induction b using ENat.recTopCoe with
    | top => exact subset_iUnion (fun j => Capa j) k
    | coe l => exact capa_mono' (by exact_mod_cast hab)

/-- **La diagonal del límite queda fuera de la capa límite.** -/
theorem Fω_no_capaE_top : Fω ∉ CapaE ⊤ := by
  rw [capaE_top]; simp only [mem_iUnion, not_exists]; exact Fω_no_capa

/-- **Cada capa finita es un punto aislado** de `ω + 1`. -/
theorem isOpen_capa_finita (k : ℕ) : IsOpen ({(k : ℕ∞)} : Set ℕ∞) := by
  have := ENat.isOpenEmbedding_natCast.isOpenMap {k} (isOpen_discrete _)
  simpa using this

/-- **La capa `ω` no es aislada**: todo entorno de `ω` contiene capas finitas. -/
theorem no_isOpen_top : ¬ IsOpen ({⊤} : Set ℕ∞) := by
  intro h
  obtain ⟨a, ha, hsub⟩ := (nhds_top_basis (α := ℕ∞)).mem_iff.1 (h.mem_nhds rfl)
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 ha.ne
  have : ((n + 1 : ℕ) : ℕ∞) ∈ Ioi (n : ℕ∞) := Set.mem_Ioi.2 (Nat.cast_lt.2 (Nat.lt_succ_self n))
  have := hsub this
  simp at this

/-- **Las capas finitas tienden a la capa `ω`.** -/
theorem tiende_a_omega : Tendsto (fun k : ℕ => (k : ℕ∞)) atTop (𝓝 ⊤) := by
  rw [(nhds_top_basis (α := ℕ∞)).tendsto_right_iff]
  intro a ha
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 ha.ne
  exact eventually_atTop.2 ⟨n + 1, fun k hk => by simp; omega⟩

end Tiempo
end Sagitta.Map
