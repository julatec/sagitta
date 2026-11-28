import Sagitta.Map.Alternancia
import Sagitta.Map.Decidir

/-!
# Entre P y EXP: `n^(log n)`, `n^(log log n)`, `n^(log log log n)`

La pregunta (José, 24 nov 2026): qué operación lleva de un polinomio a algo de la forma `n^(log n)`,
`n^(log log n)`, `n^(log log log n)`. La respuesta es una sola: **elevar un polinomio a una potencia que crece**,
`P(n)^d(n)`. Sumar, multiplicar o componer un número fijo de veces deja el exponente acotado; con `d(n)` creciente el
exponente es `d(n)`. La familia (`cuasi k n = n ^ log⁽ᵏ⁾ n`, con `log⁽ᵏ⁾` el logaritmo binario iterado `k` veces):

* **está fuera de `Pol`** (`cuasi_no_pol`) y **dentro de `Exp`** (`cuasi_en_exp`), para todo `k ≥ 1`;
* **está ordenada estrictamente**: `cuasi (k+1) ∈ O(cuasi k)` (`cuasi_succ_le`) pero `cuasi k ∉ O(cuasi (k+1))`
  (`cuasi_no_O_succ`). Es una escalera descendente infinita entre P y EXP.

## Medida en bits

Con `L = log n` (la observación de José: lo que cuenta es el largo en bits), `cuasi (k+1) (2^L) = 2^(L · log⁽ᵏ⁾ L)`
(`cuasi_en_bits`): `n^(log n) = 2^(L²)`, `n^(log log n) = 2^(L log L)`. Un polinomio es `2^O(L)`: lineal en el exponente.
La operación es **multiplicar el exponente lineal por un factor que crece**.

## Tres maneras de producir el `d(n)`

* **Elecciones escondidas** (`Decidir.lean`): `2^c(n)` es polinomial si y solo si `c = O(log n)` (`dos_pow_pol_iff`).
  Con `c(n) = log n · log⁽ᵏ⁾ n` elecciones ya no (`elecciones_no_pol`): un poco más que logarítmico basta para salir.
* **Recursión de profundidad `d` con ramaje polinomial**: el juego de Savitch de `Alternancia.lean` con `n`
  configuraciones y caminos de largo `≤ 2^i` tiene `(2n)^i` hojas. Si los caminos miden a lo sumo `log⁽ᵏ⁾ n`, basta
  `i = log⁽ᵏ⁺¹⁾ n` (`largo_savitch_le`), y el costo determinista es al menos `cuasi (k+1) n` (`savitch_cuasi`). Con
  `k = 0` (caminos de largo `n`) es `NL ⊆ DTIME(n^O(log n))`.
* **Componer `n²` consigo mismo `j` veces** da `n^(2^j)` (`iterate_cuadrar` de `Landau.lean`): `j = log log n` ya da
  `n^(log n)`. Aquí solo se anota.

## Lo que no

`log⁽ᵏ⁾` es el logaritmo entero (`Nat.log 2`, piso); las cotas son exactas en potencias de dos y valen con constantes
en general. No se prueba que ninguna clase de complejidad esté entre P y EXP; solo que estas funciones lo están.
-/

namespace Sagitta.Map
namespace Tiempo

/-- El logaritmo binario (piso), iterado `k` veces. -/
def itlog (k n : ℕ) : ℕ := (Nat.log 2)^[k] n

/-- `cuasi k n = n ^ log⁽ᵏ⁾ n`: `cuasi 1 = n^(log n)`, `cuasi 2 = n^(log log n)`, `cuasi 3 = n^(log log log n)`. -/
def cuasi (k n : ℕ) : ℕ := n ^ itlog k n

theorem itlog_succ (k n : ℕ) : itlog (k + 1) n = Nat.log 2 (itlog k n) := by
  simp [itlog, Function.iterate_succ_apply']

theorem itlog_succ' (k n : ℕ) : itlog (k + 1) n = itlog k (Nat.log 2 n) := by
  simp [itlog, Function.iterate_succ_apply]

theorem itlog_mono (k : ℕ) : Monotone (itlog k) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih => intro a b h; rw [itlog_succ, itlog_succ]; exact Nat.log_mono_right (ih h)

theorem itlog_pow (k L : ℕ) : itlog (k + 1) (2 ^ L) = itlog k L := by
  rw [itlog_succ', Nat.log_pow (by norm_num)]

/-- El logaritmo iterado no está acotado. -/
theorem itlog_no_acotado (k m : ℕ) : ∃ N, ∀ n ≥ N, m ≤ itlog k n := by
  induction k generalizing m with
  | zero => exact ⟨m, fun n hn => hn⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih m
    refine ⟨2 ^ N, fun n hn => ?_⟩
    rw [itlog_succ']
    exact hN _ (by
      calc N = Nat.log 2 (2 ^ N) := (Nat.log_pow (by norm_num) N).symm
        _ ≤ Nat.log 2 n := Nat.log_mono_right hn)

theorem itlog_le (k n : ℕ) : itlog k n ≤ n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [itlog_succ]; exact (Nat.log_le_self 2 _).trans ih

/-! ## Fuera de `Pol`, dentro de `Exp` -/

/-- **Fuera de `Pol`**: para todo `k`, `n^(log⁽ᵏ⁾ n)` no es polinomial. -/
theorem cuasi_no_pol (k : ℕ) : cuasi k ∉ Pol := by
  rintro ⟨c, d, h⟩
  obtain ⟨N, hN⟩ := itlog_no_acotado k (d + 1)
  set n := max N (c * 2 ^ d + 1) with hn
  have h1 : d + 1 ≤ itlog k n := hN n (le_max_left _ _)
  have hn1 : c * 2 ^ d < n := by have := le_max_right N (c * 2 ^ d + 1); omega
  have hpos : 1 ≤ n := by omega
  have h2 : (n + 1) ^ d ≤ 2 ^ d * n ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
  have h3 : n ^ (d + 1) ≤ cuasi k n := Nat.pow_le_pow_right hpos h1
  have h4 : c * (2 ^ d * n ^ d) < n ^ (d + 1) := by
    rw [pow_succ, ← mul_assoc]
    rw [mul_comm (n ^ d) n]
    exact Nat.mul_lt_mul_of_pos_right hn1 (Nat.pow_pos hpos)
  have := h n
  have h5 : c * (n + 1) ^ d ≤ c * (2 ^ d * n ^ d) := Nat.mul_le_mul_left _ h2
  omega

/-- **Dentro de `Exp`**: `n^(log⁽ᵏ⁾ n) ≤ 2^(n²)`. -/
theorem cuasi_en_exp (k : ℕ) : cuasi k ∈ Exp := by
  refine ⟨fun n => n * n, ⟨1, 2, fun n => by nlinarith⟩, fun n => ?_⟩
  calc cuasi k n = n ^ itlog k n := rfl
    _ ≤ (2 ^ n) ^ itlog k n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_right (Nat.one_le_two_pow) (itlog_le k n)
    _ = 2 ^ (n * n) := by rw [← pow_mul]

/-! ## La escalera: cada peldaño, estrictamente más abajo -/

/-- `n^(log⁽ᵏ⁺¹⁾ n) ≤ n^(log⁽ᵏ⁾ n)`, punto a punto. -/
theorem cuasi_succ_le (k : ℕ) : EsO (cuasi (k + 1)) (cuasi k) := by
  refine ⟨1, 1, fun n hn => ?_⟩
  rw [one_mul, cuasi, cuasi, itlog_succ]
  exact Nat.pow_le_pow_right hn (Nat.log_le_self 2 _)

theorem dos_mul_le_pow (m : ℕ) : 2 * m ≤ 2 ^ m + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega

/-- `2 · log a ≤ a + 1`: lo que el logaritmo le quita a un número es casi la mitad de él. -/
theorem dos_log_le (a : ℕ) : 2 * Nat.log 2 a ≤ a + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · exact (dos_mul_le_pow _).trans (by have := Nat.pow_log_le_self 2 ha.ne'; omega)

/-- **Estrictamente**: `n^(log⁽ᵏ⁾ n)` no está en `O(n^(log⁽ᵏ⁺¹⁾ n))`. -/
theorem cuasi_no_O_succ (k : ℕ) : ¬ EsO (cuasi k) (cuasi (k + 1)) := by
  rintro ⟨C, N, h⟩
  obtain ⟨M, hM⟩ := itlog_no_acotado k (2 * C + 3)
  set n := max (max N M) 2
  have hnN : N ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hnM : M ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn2 : 2 ≤ n := le_max_right _ _
  set a := itlog k n
  set b := Nat.log 2 a
  have ha : 2 * C + 3 ≤ a := hM n hnM
  have hab : 2 * b ≤ a + 1 := dos_log_le a
  have hba : b ≤ a := by omega
  have hd : C + 1 ≤ a - b := by omega
  have h1 : n ^ a ≤ C * n ^ b := by
    have := h n hnN
    rwa [cuasi, cuasi, itlog_succ] at this
  -- `n^a = n^b · n^(a−b) ≥ n^b · 2^(C+1) > C · n^b`.
  have hsplit : n ^ a = n ^ b * n ^ (a - b) := by rw [← pow_add, Nat.add_sub_cancel' hba]
  have h2 : 2 ^ (C + 1) ≤ n ^ (a - b) :=
    (Nat.pow_le_pow_left hn2 _).trans (Nat.pow_le_pow_right (by omega) hd)
  have h3 : C < 2 ^ (C + 1) := (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hb : 1 ≤ n ^ b := Nat.one_le_pow _ _ (by omega)
  have : C * n ^ b < n ^ b * n ^ (a - b) := by
    calc C * n ^ b < 2 ^ (C + 1) * n ^ b := Nat.mul_lt_mul_of_pos_right h3 hb
      _ ≤ n ^ (a - b) * n ^ b := Nat.mul_le_mul_right _ h2
      _ = n ^ b * n ^ (a - b) := mul_comm _ _
  rw [hsplit] at h1
  omega

/-! ## En bits -/

/-- **En bits**: con `L = log n`, `n^(log⁽ᵏ⁺¹⁾ n) = 2^(L · log⁽ᵏ⁾ L)`. Para `k = 0`, `2^(L²)`. -/
theorem cuasi_en_bits (k L : ℕ) : cuasi (k + 1) (2 ^ L) = 2 ^ (L * itlog k L) := by
  rw [cuasi, itlog_pow, ← pow_mul]

/-! ## Elecciones escondidas: un poco más que `log n` basta para salir de `Pol` -/

/-- Con `log n · log⁽ᵏ⁺¹⁾ n` elecciones escondidas, decidir cuesta más que un polinomio. Es `dos_pow_pol_iff`:
el número de elecciones ya no es `O(log n)`. -/
theorem elecciones_no_pol (k : ℕ) :
    (fun n => 2 ^ (Nat.log 2 n * itlog (k + 1) n)) ∉ Pol := by
  rw [dos_pow_pol_iff]
  rintro ⟨a, b, h⟩
  obtain ⟨M, hM⟩ := itlog_no_acotado k (a + 1)
  set L := max (max M (b + 1)) 1
  have hLM : M ≤ L := le_trans (le_max_left _ _) (le_max_left _ _)
  have hLb : b + 1 ≤ L := le_trans (le_max_right _ _) (le_max_left _ _)
  have hL1 : 1 ≤ L := le_max_right _ _
  have h1 := h (2 ^ L)
  rw [Nat.log_pow (by norm_num), itlog_pow] at h1
  -- `log₂(2^L + 1) = L` para `L ≥ 1`.
  have hlog : Nat.log 2 (2 ^ L + 1) = L := by
    apply Nat.log_eq_of_pow_le_of_lt_pow (by omega)
    rw [pow_succ]; have := Nat.one_le_two_pow (n := L); have : 2 ≤ 2 ^ L := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
    omega
  rw [hlog] at h1
  have h2 : (a + 1) * L ≤ L * itlog k L := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (hM L hLM)
  nlinarith

/-! ## Savitch con el largo del camino como parámetro -/

/-- Si los caminos miden a lo sumo `log⁽ᵏ⁾ n`, basta `i = log⁽ᵏ⁺¹⁾ n` niveles: `2^i ≤ log⁽ᵏ⁾ n`. -/
theorem largo_savitch_le (k n : ℕ) (h : 1 ≤ itlog k n) : 2 ^ itlog (k + 1) n ≤ itlog k n := by
  rw [itlog_succ]; exact Nat.pow_log_le_self 2 (by omega)

variable {C : Type*} (R : Paso C) [DecidableEq C] [∀ c d, Decidable (d ∈ R c)]

/-- **Savitch cuesta `cuasi`**: con `n` configuraciones y `log⁽ᵏ⁺¹⁾ n` niveles (caminos de largo hasta
`log⁽ᵏ⁾ n`), el juego tiene al menos `n^(log⁽ᵏ⁺¹⁾ n)` hojas, lo que paga el tiempo determinista. Con `k = 0`:
alcanzabilidad general en `n^(log n)`. -/
theorem savitch_cuasi {n : ℕ} (e : Fin n → C) (k : ℕ) (u v : C) :
    cuasi (k + 1) n ≤ Juego.hojas (juegoSav R e (itlog (k + 1) n) u v) := by
  rw [hojas_juegoSav, cuasi]
  exact Nat.pow_le_pow_left (by omega) _

/-- Y no mucho más: a lo sumo `(n²)^(log⁽ᵏ⁺¹⁾ n)`, el cuadrado de `cuasi (k+1)`, si `n ≥ 2`. -/
theorem savitch_cuasi_le {n : ℕ} (hn : 2 ≤ n) (e : Fin n → C) (k : ℕ) (u v : C) :
    Juego.hojas (juegoSav R e (itlog (k + 1) n) u v) ≤ cuasi (k + 1) n ^ 2 := by
  rw [hojas_juegoSav, cuasi, ← pow_mul, mul_comm (itlog _ _) 2, pow_mul]
  exact Nat.pow_le_pow_left (by nlinarith) _

/-! ## Controles -/

example : itlog 1 1024 = 10 := by decide
example : itlog 2 1024 = 3 := by decide
example : itlog 3 1024 = 1 := by decide
example : cuasi 1 16 = 65536 := by decide
example : cuasi 2 16 = 256 := by decide

end Tiempo
end Sagitta.Map
