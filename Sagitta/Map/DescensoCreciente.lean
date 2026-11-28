import Sagitta.Map.DescensoOrdinal
import Sagitta.Map.Circuitos

/-!
# Un descenso que alarga la cadena

Hay un colapso conocido: si el vecino conserva la longitud, un costo en `ω²` se cambia por un
natural menor que `2^p(n)` sin tocar ningún óptimo. Aquí se quita esa condición: el vecino puede agrandar el estado.

**El ejemplo.** El estado es un triple `(a, b, L)`; `L` hace el papel del largo de la cadena, y el tamaño del estado
es `a + L`. El costo es `(a, b)` en `ω²`. Un paso:

* si `b > 0`, baja `b` en uno;
* si `b = 0` y `a > 0`, baja `a` en uno, **recarga** `b` con `2^L` y **duplica** `L`;
* `(0, 0, L)` es el óptimo.

Escrito en bits, `b` cabe en `L + 1` bits, y cada paso se calcula en tiempo polinomial en el tamaño (esa parte, sobre
el tiempo, no se prueba aquí).

**Lo probado.**

1. Termina, por la buena fundación de `ω²` (`termina`).
2. Desde `(n + 1, 0, 1)`, de tamaño `n + 2`, no hay óptimo en los primeros `2^(2ⁿ)` pasos (`largo`), y el óptimo al
   que llega tiene `L = 2ⁿ⁺¹`: la respuesta misma es exponencialmente grande (`llega`).
3. **No colapsa** (`no_colapsa`): ningún costo natural menor que `2^p(tamaño)`, con `p` polinomio, hace del mismo
   vecino un descenso con los mismos óptimos. Con costo natural los pasos no pasan del costo inicial, y aquí hacen
   falta más de `2^p(n)`.
-/

namespace Sagitta.Map
namespace Creciente

/-! ## Descensos sobre un tipo cualquiera de estados -/

section General

variable {σ α : Type}

/-- **Termina**, con costo en un orden bien fundado, aunque los estados crezcan. -/
theorem termina_gen [LinearOrder α] [WellFoundedLT α] (c : σ → α) (v : σ → σ) (x : σ) :
    ∃ k, c (v^[k] x) ≤ c (v (v^[k] x)) := by
  suffices H : ∀ d : α, ∀ x, c x = d → ∃ k, c (v^[k] x) ≤ c (v (v^[k] x)) from H _ x rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro x hx
    by_cases h : c x ≤ c (v x)
    · exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := ih _ (hx ▸ not_le.mp h) (v x) rfl
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- **Con costo natural, el costo es el reloj**, aunque los estados crezcan: se llega a un óptimo en a lo sumo
`c x` pasos. -/
theorem desciende_gen (c : σ → ℕ) (v : σ → σ) :
    ∀ x, ∃ k ≤ c x, c (v^[k] x) ≤ c (v (v^[k] x)) := by
  suffices H : ∀ d x, c x ≤ d → ∃ k ≤ c x, c (v^[k] x) ≤ c (v (v^[k] x)) from fun x => H _ x le_rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hx
    by_cases h : c x ≤ c (v x)
    · exact ⟨0, Nat.zero_le _, h⟩
    · obtain ⟨k, hk, hopt⟩ := ih (c (v x)) (by omega) (v x) le_rfl
      exact ⟨k + 1, by omega, by rw [Function.iterate_succ_apply]; exact hopt⟩

end General

/-! ## El ejemplo -/

/-- Un estado: `(a, b, L)`. -/
abbrev Estado := ℕ × ℕ × ℕ

/-- El tamaño del estado: `a + L`. -/
def tam (s : Estado) : ℕ := s.1 + s.2.2

/-- El costo, en `ω²`. -/
def costo (s : Estado) : Omega2 := toLex (s.1, s.2.1)

/-- Un paso. -/
def vecino : Estado → Estado
  | (a, b + 1, L) => (a, b, L)
  | (a + 1, 0, L) => (a, 2 ^ L, 2 * L)
  | (0, 0, L) => (0, 0, L)

/-- Un óptimo: el vecino no cuesta menos. -/
def EsOptimo (s : Estado) : Prop := costo s ≤ costo (vecino s)

#guard (List.range 8).map (fun k => vecino^[k] (2, 0, 1)) =
  [(2, 0, 1), (1, 2, 2), (1, 1, 2), (1, 0, 2), (0, 4, 4), (0, 3, 4), (0, 2, 4), (0, 1, 4)]

theorem esOptimo_iff : ∀ s : Estado, EsOptimo s ↔ s.1 = 0 ∧ s.2.1 = 0
  | (a, b + 1, L) => by simp [EsOptimo, costo, vecino, Prod.Lex.toLex_le_toLex]
  | (a + 1, 0, L) => by simp [EsOptimo, costo, vecino, Prod.Lex.toLex_le_toLex]
  | (0, 0, L) => by simp [EsOptimo, costo, vecino]

/-- **Termina.** -/
theorem termina (s : Estado) : ∃ k, EsOptimo (vecino^[k] s) := termina_gen costo vecino s

/-- Mientras `b` alcance, cada paso baja `b` en uno. -/
theorem iter_baja (a L : ℕ) : ∀ j b, j ≤ b → vecino^[j] (a, b, L) = (a, b - j, L)
  | 0, b, _ => by simp
  | j + 1, b, h => by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [Function.iterate_succ_apply]
    show vecino^[j] (a, b', L) = _
    rw [iter_baja a L j b' (by omega)]
    congr 2
    omega

/-- Una recarga entera: `2^L + 1` pasos llevan de `(a + 1, 0, L)` a `(a, 0, 2L)`. -/
theorem recarga (a L r : ℕ) : vecino^[r + 2 ^ L + 1] (a + 1, 0, L) = vecino^[r] (a, 0, 2 * L) := by
  rw [Function.iterate_succ_apply, Function.iterate_add_apply]
  show vecino^[r] (vecino^[2 ^ L] (a, 2 ^ L, 2 * L)) = _
  rw [iter_baja a (2 * L) _ _ le_rfl, Nat.sub_self]

/-- **Largo.** Desde `(a + 1, 0, L)` no hay óptimo en los primeros `2^(L·2ᵃ)` pasos. -/
theorem largo : ∀ a L, ∀ k < 2 ^ (L * 2 ^ a), ¬ EsOptimo (vecino^[k] (a + 1, 0, L)) := by
  intro a
  induction a with
  | zero =>
    intro L k hk
    rw [esOptimo_iff]
    cases k with
    | zero => simp
    | succ j =>
      have hv : vecino (0 + 1, 0, L) = (0, 2 ^ L, 2 * L) := rfl
      simp only [pow_zero, mul_one] at hk
      rw [Function.iterate_succ_apply, hv, iter_baja 0 (2 * L) j _ (by omega)]
      simp only [true_and]
      omega
  | succ a ih =>
    intro L k hk
    by_cases hkL : k ≤ 2 ^ L
    · rw [esOptimo_iff]
      cases k with
      | zero => simp
      | succ j =>
        have hv : vecino (a + 1 + 1, 0, L) = (a + 1, 2 ^ L, 2 * L) := rfl
        rw [Function.iterate_succ_apply, hv, iter_baja (a + 1) (2 * L) j _ (by omega)]
        simp
    · obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 ^ L + 1 := ⟨k - 2 ^ L - 1, by omega⟩
      rw [recarga]
      apply ih (2 * L) r
      have : 2 * L * 2 ^ a = L * 2 ^ (a + 1) := by ring
      have h2 : r < 2 ^ (L * 2 ^ (a + 1)) := by
        rw [Nat.add_assoc] at hk
        exact lt_of_le_of_lt (Nat.le_add_right _ _) hk
      rw [this]
      exact h2

/-- Cuántos pasos tarda desde `(a, 0, L)`. -/
def T : ℕ → ℕ → ℕ
  | 0, _ => 0
  | a + 1, L => T a (2 * L) + 2 ^ L + 1

/-- **Llega**, a un óptimo exponencialmente grande: `L` termina multiplicado por `2ᵃ`. -/
theorem llega : ∀ a L, vecino^[T a L] (a, 0, L) = (0, 0, L * 2 ^ a)
  | 0, L => by simp [T]
  | a + 1, L => by
    rw [T, recarga, llega a (2 * L)]
    congr 2
    ring

/-- **No colapsa.** Ningún costo natural menor que `2^p(tamaño)` da el mismo descenso (el mismo vecino, los mismos
óptimos). -/
theorem no_colapsa :
    ¬ ∃ (c : Estado → ℕ) (p : Polynomial ℕ),
      (∀ s, c s < 2 ^ p.eval (tam s)) ∧ (∀ s, c s ≤ c (vecino s) ↔ EsOptimo s) := by
  rintro ⟨c, p, hc, hopt⟩
  -- Un `n` donde el polinomio ya quedó por debajo de `2ⁿ`.
  obtain ⟨N, hN⟩ := mul_pow_lt_dos_pow (4 * p.eval 1) p.natDegree
  have hm : p.eval (N + 2) < 2 ^ N := by
    have h1 := eval_le_mul_pow p (n := N + 2) (by omega)
    have h2 := hN (N + 2) (by omega)
    rw [pow_add] at h2
    have : 4 * p.eval 1 * (N + 2) ^ p.natDegree = 4 * (p.eval 1 * (N + 2) ^ p.natDegree) := by ring
    omega
  -- El costo natural llega a un óptimo en a lo sumo `c x < 2^p(N + 2) ≤ 2^(2^N)` pasos.
  let x : Estado := (N + 1, 0, 1)
  obtain ⟨k, hk, hk'⟩ := desciende_gen c vecino x
  have hcx : c x < 2 ^ p.eval (N + 2) := by
    have := hc x
    simp only [tam, x] at this
    rwa [show N + 1 + 1 = N + 2 by omega] at this
  have hlt : k < 2 ^ (1 * 2 ^ N) := by
    calc k ≤ c x := hk
      _ < 2 ^ p.eval (N + 2) := hcx
      _ ≤ 2 ^ (1 * 2 ^ N) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact largo N 1 k hlt ((hopt _).mp hk')

end Creciente
end Sagitta.Map
