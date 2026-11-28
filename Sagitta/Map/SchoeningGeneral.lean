import Sagitta.Map.Schoening

/-!
# El lema fino de Schöning para `k` general

`Schoening.lean` prueba el lema fino solo para `k = 3`. Aquí sale para todo `k ≥ 3`, con la misma forma de contar.

## Lo que se prueba

* **La cota del binomial** (`choose_moda_ge`): para `k ≥ 1` y todo `m`,
  `k^(km) ≤ (km + 1) · (k−1)^((k−1)m) · C(km, m)`. Es la moda de la binomial `B(km, 1/k)`. Los términos
  `C(N, i) · (k−1)^(N−i)` suman `k^N` (`add_pow`). El término `i = m` es el más grande (`termino_le_moda`): antes de
  `m` los términos suben (`termino_sube`), después bajan (`termino_baja`). Hay `N + 1` términos. Todo en naturales.
* **Los caminos** (`caminosA_moda_ge`): desde la distancia `(k−2)m`, en `km` pasos, la caminata pesimista tiene al menos
  `C(km, m) · (k−1)^m` caminos buenos: `(k−1)m` bajadas y `m` subidas, en cualquier orden.
* **El lema fino por bloques** (`lema_fino_bloques`): si `dist(α, β) ≤ (k−2)m` y `t ≥ km`, la proporción es
  `≥ (k−1)^(−(k−2)m) / (km + 1)`.
* **El lema fino por distancia** (`lema_fino_general`): con `m = ⌈r/(k−2)⌉` (`bloquesFinos`), a distancia `r` la
  proporción es `≥ (k−1)^(−r) / ((k−1)^(k−3) · (km + 1))`. Redondear `m` hacia arriba pierde a lo sumo `(k−1)^(k−3)`.
* **El éxito y el costo** (`exito_fino_general`, `tiempo_fino_general`): con `M = ⌈n/(k−2)⌉` y `t = kM` pasos, el
  éxito de un intento es `≥ (k/(2(k−1)))^n / C` y el costo esperado es `≤ kM · C · (2(k−1)/k)^n`, con
  `C = (k−1)^(k−3) · (kM + 1)`. Es el `(2(k−1)/k)^n · poli(n)` de Schöning, con la constante explícita.
  - Para `k = 3`: `M = n` y `C = 3n + 1`. Es la cota de `tiempo_fino_tres_probado` con `3n + 1` en vez de `2n + 1`.

## El factor polinomial

El factor `1/(km + 1)` no sobra. El lema sin factor polinomial es falso: ver el docstring de `Schoening.lean`, con un
contraejemplo de 3-SAT a distancia 1.

## Fuente

D. Scheder, «Algorithms and Extremal Properties of SAT and CSP», tesis doctoral, ETH Zürich 2011, §3.1, Lemas 3.2 y 3.3.
Scheder acota el binomial con la cota de MacWilliams–Sloane (entropía). Aquí se usa la moda de la binomial: es más
débil por un factor polinomial y se prueba sin análisis.
-/

namespace Sagitta.Map
namespace Tiempo

variable {n k : ℕ}

/-! ## La cota del binomial: la moda -/

/-- Antes de la moda los términos suben. Con `N = am + m` y `i < m`:
`C(N, i) · a^(N−i) ≤ C(N, i+1) · a^(N−i−1)`. -/
theorem termino_sube {a m i : ℕ} (hi : i < m) :
    (a * m + m).choose i * a ^ (a * m + m - i) ≤ (a * m + m).choose (i + 1) * a ^ (a * m + m - (i + 1)) := by
  set N := a * m + m with hN
  have ham : a * (i + 1) ≤ a * m := Nat.mul_le_mul_left a hi
  have e : N - i = (N - (i + 1)) + 1 := by omega
  have key := Nat.choose_succ_right_eq N i
  have ineq : a * (i + 1) ≤ N - i := by omega
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos i)
  rw [e, pow_succ]
  calc N.choose i * (a ^ (N - (i + 1)) * a) * (i + 1)
      = N.choose i * a ^ (N - (i + 1)) * (a * (i + 1)) := by ring
    _ ≤ N.choose i * a ^ (N - (i + 1)) * (N - i) := by gcongr
    _ = N.choose (i + 1) * (i + 1) * a ^ (N - (i + 1)) := by rw [key]; ring
    _ = N.choose (i + 1) * a ^ (N - (i + 1)) * (i + 1) := by ring

/-- Desde la moda los términos bajan. Con `N = am + m` y `m ≤ i`:
`C(N, i+1) · a^(N−i−1) ≤ C(N, i) · a^(N−i)`. -/
theorem termino_baja {a m i : ℕ} (hi : m ≤ i) :
    (a * m + m).choose (i + 1) * a ^ (a * m + m - (i + 1)) ≤ (a * m + m).choose i * a ^ (a * m + m - i) := by
  set N := a * m + m with hN
  by_cases hiN : N < i + 1
  · rw [Nat.choose_eq_zero_of_lt hiN]; simp
  have ham : a * m ≤ a * (i + 1) := Nat.mul_le_mul_left a (by omega)
  have e : N - i = (N - (i + 1)) + 1 := by omega
  have key := Nat.choose_succ_right_eq N i
  have ineq : N - i ≤ a * (i + 1) := by omega
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos i)
  rw [e, pow_succ]
  calc N.choose (i + 1) * a ^ (N - (i + 1)) * (i + 1)
      = N.choose i * (N - i) * a ^ (N - (i + 1)) := by rw [← key]; ring
    _ ≤ N.choose i * (a * (i + 1)) * a ^ (N - (i + 1)) := by gcongr
    _ = N.choose i * (a ^ (N - (i + 1)) * a) * (i + 1) := by ring

/-- **La moda**: el término `i = m` es el más grande de todos. -/
theorem termino_le_moda (a m i : ℕ) :
    (a * m + m).choose i * a ^ (a * m + m - i) ≤ (a * m + m).choose m * a ^ (a * m + m - m) := by
  rcases le_total i m with h | h
  · -- Subiendo: `m − d` para `d ≤ m`.
    have : ∀ d, d ≤ m → (a * m + m).choose (m - d) * a ^ (a * m + m - (m - d)) ≤
        (a * m + m).choose m * a ^ (a * m + m - m) := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        have h1 := termino_sube (a := a) (m := m) (i := m - (d + 1)) (by omega)
        rw [show m - (d + 1) + 1 = m - d by omega] at h1
        exact h1.trans (ih (by omega))
    simpa [Nat.sub_sub_self h] using this (m - i) (Nat.sub_le m i)
  · -- Bajando: `m + d`.
    have : ∀ d, (a * m + m).choose (m + d) * a ^ (a * m + m - (m + d)) ≤
        (a * m + m).choose m * a ^ (a * m + m - m) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        exact (termino_baja (a := a) (m := m) (i := m + d) (by omega)).trans ih
    simpa [Nat.add_sub_cancel' h] using this (i - m)

/-- **La cota del binomial por la moda**: `k^(km) ≤ (km + 1) · (k−1)^((k−1)m) · C(km, m)`. Los `km + 1` términos de
la binomial suman `k^(km)` y ninguno pasa del de la moda. -/
theorem choose_moda_ge (hk : 0 < k) (m : ℕ) :
    k ^ (k * m) ≤ (k * m + 1) * (k - 1) ^ ((k - 1) * m) * (k * m).choose m := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [add_one_mul a m]
  set N := a * m + m with hN
  have hs : (a + 1) ^ N = ∑ i ∈ Finset.range (N + 1), N.choose i * a ^ (N - i) := by
    rw [add_comm a 1, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hNm : N - m = a * m := by omega
  rw [hs]
  calc ∑ i ∈ Finset.range (N + 1), N.choose i * a ^ (N - i)
      ≤ ∑ _i ∈ Finset.range (N + 1), N.choose m * a ^ (N - m) :=
        Finset.sum_le_sum fun i _ => termino_le_moda a m i
    _ = (N + 1) * a ^ (a * m) * N.choose m := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, hNm]; ring

/-! ## Los caminos -/

/-- **La caminata pesimista para `k` general**: desde `(k−2)m`, en `km` pasos, al menos `C(km, m) · (k−1)^m`
sucesiones llegan a `0` (las de `(k−1)m` bajadas y `m` subidas, en cualquier orden). -/
theorem caminosA_moda_ge (hk : 2 ≤ k) (m : ℕ) :
    (k * m).choose m * (k - 1) ^ m ≤ caminosA k (k * m) ((k - 2) * m) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h := choose_le_caminosLibres (k := j + 2) ((j + 2) * m) ((j + 1) * m) m ((j * m : ℕ) : ℤ)
    (by ring) (le_of_eq (by push_cast; ring))
  have e : ((j + 2) * m).choose ((j + 1) * m) = ((j + 2) * m).choose m := by
    rw [show (j + 2) * m = (j + 1) * m + m by ring, Nat.choose_symm_add]
  rw [e] at h
  simp only [Nat.add_sub_cancel]
  exact le_trans h (caminosLibres_le_caminosA (by omega) _ _)

/-! ## El lema fino -/

/-- **El lema fino por bloques**: si `dist(α, β) ≤ (k−2)m` y `t ≥ km`, la caminata de `t` pasos acierta con
probabilidad `≥ (k−1)^(−(k−2)m) / (km + 1)`. Vale con cláusulas de a lo sumo `k` literales. -/
theorem lema_fino_bloques {F : List Clausula} (hk : 3 ≤ k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) {t m : ℕ} {α : Fin n → Bool} (hd : hammingDist α β ≤ (k - 2) * m)
    (ht : k * m ≤ t) :
    (1 / ((k : ℝ) - 1)) ^ ((k - 2) * m) / ((k : ℝ) * m + 1) ≤ proporcion F k t α := by
  have h1 : k ^ (t - k * m) * ((k * m).choose m * (k - 1) ^ m) ≤ aciertos F k t α := by
    calc k ^ (t - k * m) * ((k * m).choose m * (k - 1) ^ m)
        ≤ k ^ (t - k * m) * caminosA k (k * m) ((k - 2) * m) := by
          gcongr; exact caminosA_moda_ge (by omega) m
      _ ≤ caminosA k (k * m + (t - k * m)) ((k - 2) * m) := caminosA_add _ _ _
      _ = caminosA k t ((k - 2) * m) := by congr 1; omega
      _ ≤ caminosA k t (hammingDist α β) := caminosA_anti (by omega) t hd
      _ ≤ aciertos F k t α := caminosA_le_aciertos (by omega) hw hβ t α
  have h2 := choose_moda_ge (k := k) (by omega) m
  set c := k - 1 with hc
  set C := (k * m).choose m
  have hcR : ((k : ℝ) - 1) = (c : ℝ) := by
    rw [hc, Nat.cast_sub (by omega)]; simp
  have hc0 : (0 : ℝ) < c := by
    have : 2 ≤ c := by omega
    exact_mod_cast (by omega : 0 < c)
  have hexp : (k - 1) * m = (k - 2) * m + m := by
    rw [← add_one_mul]; congr 1; omega
  rw [hexp] at h2
  have h1' : (k : ℝ) ^ (t - k * m) * ((C : ℝ) * (c : ℝ) ^ m) ≤ aciertos F k t α := by exact_mod_cast h1
  have h2' : (k : ℝ) ^ (k * m) ≤ ((k : ℝ) * m + 1) * (c : ℝ) ^ ((k - 2) * m + m) * C := by exact_mod_cast h2
  have et : (k : ℝ) ^ t = k ^ (t - k * m) * k ^ (k * m) := by
    rw [← pow_add]; congr 1; omega
  unfold proporcion
  rw [hcR, le_div_iff₀ (by positivity), et]
  have hkm : (0 : ℝ) < (k : ℝ) * m + 1 := by positivity
  calc (1 / (c : ℝ)) ^ ((k - 2) * m) / ((k : ℝ) * m + 1) * (k ^ (t - k * m) * k ^ (k * m))
      ≤ (1 / (c : ℝ)) ^ ((k - 2) * m) / ((k : ℝ) * m + 1) *
          (k ^ (t - k * m) * (((k : ℝ) * m + 1) * (c : ℝ) ^ ((k - 2) * m + m) * C)) := by
        gcongr
    _ = (k : ℝ) ^ (t - k * m) * ((C : ℝ) * (c : ℝ) ^ m) := by
        rw [pow_add, div_pow, one_pow]
        field_simp
    _ ≤ aciertos F k t α := h1'

/-- **Los bloques**: `⌈r/(k−2)⌉`, escrito en naturales. -/
def bloquesFinos (k r : ℕ) : ℕ := (r + (k - 3)) / (k - 2)

/-- Los bloques cubren la distancia: `r ≤ (k−2) · ⌈r/(k−2)⌉`. -/
theorem le_bloquesFinos (hk : 3 ≤ k) (r : ℕ) : r ≤ (k - 2) * bloquesFinos k r := by
  unfold bloquesFinos
  have h := Nat.lt_mul_div_succ (r + (k - 3)) (show 0 < k - 2 by omega)
  have : k - 2 = (k - 3) + 1 := by omega
  rw [mul_add, mul_one] at h
  omega

/-- Y no se pasan por mucho: `(k−2) · ⌈r/(k−2)⌉ ≤ r + (k−3)`. -/
theorem bloquesFinos_le (k r : ℕ) : (k - 2) * bloquesFinos k r ≤ r + (k - 3) := by
  unfold bloquesFinos
  exact Nat.mul_div_le _ _

/-- Más distancia, más bloques. -/
theorem bloquesFinos_mono (k : ℕ) {r r' : ℕ} (h : r ≤ r') : bloquesFinos k r ≤ bloquesFinos k r' := by
  unfold bloquesFinos
  exact Nat.div_le_div_right (by omega)

/-- **El lema fino para `k`-SAT**: a distancia `r` de una solución, con `m = ⌈r/(k−2)⌉` y `t ≥ km` pasos, la caminata
acierta con probabilidad `≥ (k−1)^(−r) / ((k−1)^(k−3) · (km + 1))`. -/
theorem lema_fino_general {F : List Clausula} (hk : 3 ≤ k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) {t : ℕ} {α : Fin n → Bool}
    (ht : k * bloquesFinos k (hammingDist α β) ≤ t) :
    (1 / ((k : ℝ) - 1)) ^ hammingDist α β /
        (((k : ℝ) - 1) ^ (k - 3) * ((k : ℝ) * bloquesFinos k (hammingDist α β) + 1)) ≤ proporcion F k t α := by
  set r := hammingDist α β
  set m := bloquesFinos k r
  have h := lema_fino_bloques hk hw hβ (t := t) (m := m) (α := α) (le_bloquesFinos hk r) ht
  have hk1 : (2 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hq0 : (0 : ℝ) ≤ 1 / ((k : ℝ) - 1) := by positivity
  have hq1 : 1 / ((k : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hpow : (1 / ((k : ℝ) - 1)) ^ (r + (k - 3)) ≤ (1 / ((k : ℝ) - 1)) ^ ((k - 2) * m) :=
    pow_le_pow_of_le_one hq0 hq1 (bloquesFinos_le k r)
  have hkm : (0 : ℝ) < (k : ℝ) * m + 1 := by positivity
  refine le_trans ?_ h
  calc (1 / ((k : ℝ) - 1)) ^ r / (((k : ℝ) - 1) ^ (k - 3) * ((k : ℝ) * m + 1))
      = (1 / ((k : ℝ) - 1)) ^ (r + (k - 3)) / ((k : ℝ) * m + 1) := by
        rw [pow_add, div_pow, div_pow, one_pow, one_pow]
        have : ((k : ℝ) - 1) ^ (k - 3) ≠ 0 := by positivity
        field_simp
    _ ≤ (1 / ((k : ℝ) - 1)) ^ ((k - 2) * m) / ((k : ℝ) * m + 1) := by gcongr

/-! ## El éxito y el costo -/

/-- **El éxito de un intento para `k`-SAT**: con `M = ⌈n/(k−2)⌉` y `kM` pasos, el éxito es
`≥ ((1 + 1/(k−1))/2)^n / ((k−1)^(k−3) · (kM + 1))`, es decir `(k/(2(k−1)))^n` entre una constante por un polinomio. -/
theorem exito_fino_general {F : List Clausula} (hk : 3 ≤ k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) :
    ((1 + 1 / ((k : ℝ) - 1)) / 2) ^ n /
        (((k : ℝ) - 1) ^ (k - 3) * ((k : ℝ) * bloquesFinos k n + 1)) ≤
      exitoSchoening F n k (k * bloquesFinos k n) := by
  set M := bloquesFinos k n
  set C := ((k : ℝ) - 1) ^ (k - 3) * ((k : ℝ) * M + 1) with hC
  have hk1 : (2 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hCpos : 0 < C := by positivity
  have h := composicion (fun α => C * proporcion F k (k * M) α) β (1 / ((k : ℝ) - 1)) fun α => by
    have hd : hammingDist α β ≤ n := hammingDist_le_card_fintype.trans (by simp)
    have hb : bloquesFinos k (hammingDist α β) ≤ M := bloquesFinos_mono k hd
    have hbR : (bloquesFinos k (hammingDist α β) : ℝ) ≤ M := by exact_mod_cast hb
    have := lema_fino_general hk hw hβ (t := k * M) (α := α) (Nat.mul_le_mul_left k hb)
    calc (1 / ((k : ℝ) - 1)) ^ hammingDist α β = C * ((1 / ((k : ℝ) - 1)) ^ hammingDist α β / C) := by
          field_simp
      _ ≤ C * ((1 / ((k : ℝ) - 1)) ^ hammingDist α β /
            (((k : ℝ) - 1) ^ (k - 3) * ((k : ℝ) * bloquesFinos k (hammingDist α β) + 1))) := by
          gcongr
          rw [hC]
          have : (0 : ℝ) ≤ ((k : ℝ) - 1) ^ (k - 3) := pow_nonneg (by linarith) _
          gcongr
      _ ≤ _ := by gcongr
  rw [← Finset.mul_sum, mul_div_assoc] at h
  unfold exitoSchoening
  rw [div_le_iff₀ hCpos]
  linarith

/-- **Schöning para `k`-SAT, probado**: con `M = ⌈n/(k−2)⌉`, el costo esperado de reiniciar caminatas de `kM` pasos
es `≤ kM · (k−1)^(k−3) · (kM + 1) · (2(k−1)/k)^n`. Sin hipótesis más que una solución `β` y cláusulas de a lo sumo `k`
literales. -/
theorem tiempo_fino_general {F : List Clausula} (hk : 3 ≤ k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) :
    ∫ x, costo (k * bloquesFinos k n) x ∂tramos 1 (exitoU F n k (k * bloquesFinos k n)) ≤
      (k * bloquesFinos k n : ℕ) * (((k : ℝ) - 1) ^ (k - 3) * ((k : ℝ) * bloquesFinos k n + 1)) *
        (2 * ((k : ℝ) - 1) / k) ^ n := by
  set M := bloquesFinos k n
  set C := ((k : ℝ) - 1) ^ (k - 3) * ((k : ℝ) * M + 1) with hC
  have hk1 : (2 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hlow := exito_fino_general hk hw hβ
  have hCpos : 0 < C := by positivity
  have hpos : 0 < ((1 + 1 / ((k : ℝ) - 1)) / 2) ^ n / C := by positivity
  have hne : exitoU F n k (k * M) ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    simp only [exitoU, Set.Icc.coe_zero] at this
    linarith
  rw [costo_esperado (k * M) 1 hne]
  simp only [exitoU, Nat.cast_one, mul_one]
  have hb : (2 / (1 + 1 / ((k : ℝ) - 1))) = 2 * ((k : ℝ) - 1) / k := by
    have : (k : ℝ) - 1 ≠ 0 := by linarith
    have : (k : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  calc ((k * M : ℕ) : ℝ) / exitoSchoening F n k (k * M)
      ≤ (k * M : ℕ) / (((1 + 1 / ((k : ℝ) - 1)) / 2) ^ n / C) :=
        div_le_div_of_nonneg_left (by positivity) hpos hlow
    _ = (k * M : ℕ) * C * (2 / (1 + 1 / ((k : ℝ) - 1))) ^ n := by
        have : (1 + 1 / ((k : ℝ) - 1)) ≠ 0 := by positivity
        rw [div_pow, div_pow]
        field_simp
    _ = (k * M : ℕ) * C * (2 * ((k : ℝ) - 1) / k) ^ n := by rw [hb]

/-! ## Controles -/

/-- La cota del binomial con `k = 4`, `m = 3`: `4^12 = 16777216 ≤ 13 · 3^9 · C(12, 3) = 56293380`. -/
example : 4 ^ (4 * 3) ≤ (4 * 3 + 1) * 3 ^ (3 * 3) * (4 * 3).choose 3 := by decide

/-- La moda con `k = 4`, `m = 2`: el término `i = 2` (`28 · 3^6 = 20412`) le gana a los de `i = 1` y `i = 3`. -/
example : (8).choose 1 * 3 ^ 7 ≤ (8).choose 2 * 3 ^ 6 ∧ (8).choose 3 * 3 ^ 5 ≤ (8).choose 2 * 3 ^ 6 := by decide

/-- Sin el factor `km + 1` la cota es falsa: `4^4 = 256 > 3^3 · C(4, 1) = 108`. -/
example : ¬ (4 ^ (4 * 1) ≤ 3 ^ (3 * 1) * (4 * 1).choose 1) := by decide

/-- La pesimista con `k = 4`, desde `2`, en `4` pasos: al menos `C(4, 1) · 3 = 12` caminos. -/
example : (4 * 1).choose 1 * 3 ^ 1 ≤ caminosA 4 (4 * 1) ((4 - 2) * 1) := by decide

/-- Los bloques: `⌈7/3⌉ = 3` para `k = 5`, y `⌈6/3⌉ = 2`. -/
example : bloquesFinos 5 7 = 3 ∧ bloquesFinos 5 6 = 2 := by decide

end Tiempo
end Sagitta.Map
