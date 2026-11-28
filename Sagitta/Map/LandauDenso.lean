import Sagitta.Map.Landau
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# El orden de Landau es denso, pero tiene huecos (C1)

Primera fase del refinamiento de la cebolla (`Jerarquia.lean`, `CebollaExp.lean`): en la capa 2 caen juntos los
polinomios y las exponenciales, así que hace falta una escala más fina. La fina la da Landau.

**El orden.** `f ∈ o g` (`f ≺ g`): para toda constante `c`, desde algún punto `c · f ≤ g`. Es «`f` es despreciable
frente a `g`».

## Lo que se prueba

1. **Es denso** (`denso`): si `f ≺ g`, la media geométrica `√(f · g)` cae estrictamente entre las dos
   (`media_entre`). No hacen falta logaritmos.
2. **Toda familia numerable tiene una cota** (`cota_numerable`, la diagonal de du Bois-Reymond): `g n = (n+1) ·
   ∑_{k ≤ n} f k n` está por encima de cada `f k`.
3. **Pero ninguna tiene una cota mínima** (`sin_supremo`): si `g` está por encima de todas las `f k`, hay `h` por
   encima de todas y estrictamente debajo de `g`. La prueba diagonaliza: va subiendo despacio por la familia, con un
   índice `κ(n)` que crece tan lento como haga falta para no alcanzar a `g`.

Juntas: el orden es denso y ninguna sucesión creciente converge. Una «sucesión de Cauchy» como
`n · log n, n · log² n, n · log³ n, …` (`nlog_crece`) no tiene límite: entre ella y cualquier cosa que la supere queda
espacio (`nlog_sin_limite`). Es un orden **denso y no completo**, con huecos.

## Fuentes, de memoria

P. du Bois-Reymond (años 1870), la diagonal; G. H. Hardy, *Orders of Infinity* (1910); F. Hausdorff (1909), los huecos
de tipo `(ω₁, ω₁*)`. No las leí en esta sesión; las pruebas de aquí son propias y no dependen de ellas.
-/

namespace Sagitta.Map
namespace Tiempo

/-- **`f ∈ o g`**: `f` es despreciable frente a `g`; para toda constante `c`, desde algún punto `c · f ≤ g`. -/
def o (g : ℕ → ℕ) : Set (ℕ → ℕ) := {f | ∀ c, ∃ N, ∀ n ≥ N, c * f n ≤ g n}

/-! ## Reglas básicas -/

/-- **Control**: la relación es estricta; una función positiva no es despreciable frente a sí misma. -/
theorem no_o_propia : (fun n => n + 1) ∉ o (fun n => n + 1) := by
  intro h
  obtain ⟨N, hN⟩ := h 2
  have := hN N le_rfl
  beta_reduce at this
  omega

theorem o_suma {f₁ f₂ g : ℕ → ℕ} (h₁ : f₁ ∈ o g) (h₂ : f₂ ∈ o g) : (fun n => f₁ n + f₂ n) ∈ o g := by
  intro c
  obtain ⟨N₁, h₁⟩ := h₁ (2 * c)
  obtain ⟨N₂, h₂⟩ := h₂ (2 * c)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have a := h₁ n (le_of_max_le_left hn)
  have b := h₂ n (le_of_max_le_right hn)
  rw [mul_add]
  nlinarith

theorem o_abajo {f f' g : ℕ → ℕ} (h : f ∈ o g) (hf : ∀ n, f' n ≤ f n) : f' ∈ o g := fun c => by
  obtain ⟨N, h⟩ := h c
  exact ⟨N, fun n hn => (Nat.mul_le_mul_left c (hf n)).trans (h n hn)⟩

/-! ## 1. Denso: la media geométrica -/

/-- La media geométrica de `f` y `g`. -/
def media (f g : ℕ → ℕ) (n : ℕ) : ℕ := Nat.sqrt (f n * g n)

/-- **La media geométrica cae estrictamente entre `f` y `g`.** -/
theorem media_entre {f g : ℕ → ℕ} (h : f ∈ o g) : f ∈ o (media f g) ∧ media f g ∈ o g := by
  constructor
  · intro c
    obtain ⟨N, hN⟩ := h (c * c)
    refine ⟨N, fun n hn => Nat.le_sqrt.mpr ?_⟩
    have := Nat.mul_le_mul_left (f n) (hN n hn)
    calc c * f n * (c * f n) = f n * (c * c * f n) := by ring
      _ ≤ f n * g n := this
  · intro c
    obtain ⟨N, hN⟩ := h (c * c)
    refine ⟨N, fun n hn => ?_⟩
    have hs := Nat.sqrt_le (f n * g n)
    have hg := Nat.mul_le_mul_right (g n) (hN n hn)
    refine Nat.mul_self_le_mul_self_iff.mp ?_
    calc c * media f g n * (c * media f g n) = c * c * (media f g n * media f g n) := by ring
      _ ≤ c * c * (f n * g n) := Nat.mul_le_mul_left _ hs
      _ = c * c * f n * g n := by ring
      _ ≤ g n * g n := hg

/-- **El orden de Landau es denso.** -/
theorem denso {f g : ℕ → ℕ} (h : f ∈ o g) : ∃ m, f ∈ o m ∧ m ∈ o g := ⟨media f g, media_entre h⟩

/-! ## 2. Toda familia numerable tiene cota: la diagonal -/

/-- Las sumas parciales de la familia. -/
def parcial (f : ℕ → ℕ → ℕ) (k n : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), f j n

theorem le_parcial (f : ℕ → ℕ → ℕ) {j k : ℕ} (h : j ≤ k) (n : ℕ) : f j n ≤ parcial f k n :=
  Finset.single_le_sum (f := fun i => f i n) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

theorem parcial_mono (f : ℕ → ℕ → ℕ) {j k : ℕ} (h : j ≤ k) (n : ℕ) : parcial f j n ≤ parcial f k n :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))

/-- **La diagonal de du Bois-Reymond**: toda familia numerable queda debajo de una sola función. -/
theorem cota_numerable (f : ℕ → ℕ → ℕ) : ∃ g, ∀ k, f k ∈ o g := by
  refine ⟨fun n => (n + 1) * parcial f n n, fun k c => ⟨max k c, fun n hn => ?_⟩⟩
  have h1 := le_parcial f (le_of_max_le_left hn) n
  calc c * f k n ≤ (n + 1) * f k n := Nat.mul_le_mul_right _ (by have := le_of_max_le_right hn; omega)
    _ ≤ (n + 1) * parcial f n n := Nat.mul_le_mul_left _ h1

/-! ## 3. Pero ninguna tiene cota mínima: los huecos -/

theorem parcial_o (f : ℕ → ℕ → ℕ) {g : ℕ → ℕ} (h : ∀ k, f k ∈ o g) (k : ℕ) : parcial f k ∈ o g := by
  induction k with
  | zero =>
    have e : parcial f 0 = f 0 := by funext n; simp [parcial]
    rw [e]; exact h 0
  | succ k ih =>
    have e : parcial f (k + 1) = fun n => parcial f k n + f (k + 1) n := by
      funext n; simp only [parcial, Finset.sum_range_succ]
    rw [e]; exact o_suma ih (h (k + 1))

/-- **Sin supremo**: si `g` está por encima de toda la familia, hay `h` por encima de toda la familia y estrictamente
debajo de `g`. -/
theorem sin_supremo (f : ℕ → ℕ → ℕ) {g : ℕ → ℕ} (hg : ∀ k, f k ∈ o g) :
    ∃ h, (∀ k, f k ∈ o h) ∧ h ∈ o g := by
  classical
  -- Desde `N k`, la suma parcial `k`, por `(k+1)²`, cabe debajo de `g`.
  have hN : ∀ k, ∃ N, ∀ n ≥ N, (k + 1) * (k + 1) * parcial f k n ≤ g n :=
    fun k => parcial_o f hg k ((k + 1) * (k + 1))
  choose N hN using hN
  -- `κ n`: el índice más alto `≤ n` cuyos umbrales (y los de todos los anteriores) ya pasaron.
  let P : ℕ → ℕ → Prop := fun n k => ∀ j ≤ k, N j ≤ n
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  have hκP : ∀ n, N 0 ≤ n → P n (κ n) := fun n hn =>
    Nat.findGreatest_spec (P := P n) (Nat.zero_le n) (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact hn)
  -- `κ` crece sin cota.
  have hκ : ∀ c, ∃ M, ∀ n ≥ M, c ≤ κ n := fun c => by
    refine ⟨c + ∑ j ∈ Finset.range (c + 1), N j, fun n hn => ?_⟩
    refine Nat.le_findGreatest (P := P n) (by omega) (fun j hj => ?_)
    have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (show j < c + 1 by omega))
    omega
  let G : ℕ → ℕ := fun n => (κ n + 1) * parcial f (κ n) n
  refine ⟨G, fun k c => ?_, fun c => ?_⟩
  · -- Cada `f k` es despreciable frente a `G`: cuando `κ n ≥ k, c`.
    obtain ⟨M, hM⟩ := hκ (k + c)
    refine ⟨M, fun n hn => ?_⟩
    have hk := hM n hn
    calc c * f k n ≤ (κ n + 1) * f k n := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (κ n + 1) * parcial f (κ n) n :=
        Nat.mul_le_mul_left _ ((le_parcial f le_rfl n).trans (parcial_mono f (by omega) n))
  · -- `G` es despreciable frente a `g`: `c · G ≤ (κ+1) · G ≤ g` cuando `κ n ≥ c`.
    obtain ⟨M, hM⟩ := hκ c
    refine ⟨max M (N 0), fun n hn => ?_⟩
    have hc := hM n (le_of_max_le_left hn)
    have hP := hκP n (le_of_max_le_right hn)
    have hb := hN (κ n) n (hP (κ n) le_rfl)
    calc c * G n ≤ (κ n + 1) * G n := Nat.mul_le_mul_right _ (by omega)
      _ = (κ n + 1) * (κ n + 1) * parcial f (κ n) n := by simp only [G]; ring
      _ ≤ g n := hb

/-- La densidad sale también de los huecos, con la familia constante. -/
example {f g : ℕ → ℕ} (h : f ∈ o g) : ∃ m, f ∈ o m ∧ m ∈ o g := by
  obtain ⟨m, hm, hmg⟩ := sin_supremo (fun _ => f) (fun _ => h)
  exact ⟨m, hm 0, hmg⟩

/-! ## El ejemplo: `n · logᵏ n` -/

/-- `n · (log₂ n)ᵏ`. -/
def nlog (k n : ℕ) : ℕ := n * Nat.log 2 n ^ k

/-- **La sucesión crece estrictamente**: cada término es despreciable frente al siguiente. -/
theorem nlog_crece (k : ℕ) : nlog k ∈ o (nlog (k + 1)) := fun c => by
  refine ⟨2 ^ c, fun n hn => ?_⟩
  have hl : c ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  simp only [nlog, pow_succ]
  calc c * (n * Nat.log 2 n ^ k) = n * Nat.log 2 n ^ k * c := by ring
    _ ≤ n * Nat.log 2 n ^ k * Nat.log 2 n := Nat.mul_le_mul_left _ hl
    _ = n * (Nat.log 2 n ^ k * Nat.log 2 n) := by ring

/-- **La sucesión no converge**: cualquier cosa que esté por encima de todas las `n · logᵏ n` tiene otra por debajo
que también está por encima de todas. -/
theorem nlog_sin_limite {g : ℕ → ℕ} (hg : ∀ k, nlog k ∈ o g) : ∃ h, (∀ k, nlog k ∈ o h) ∧ h ∈ o g :=
  sin_supremo nlog hg

end Tiempo
end Sagitta.Map
