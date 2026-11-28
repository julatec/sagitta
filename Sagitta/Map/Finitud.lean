import Sagitta.Map.Circuitos
import Sagitta.Map.Cuasipolinomial

/-!
# La finitud del límite: ¿llegamos, si todo lo que tenemos es finito?

La pregunta (José, 24 nov 2026). Pensemos SAT como un «irracional» aproximado por una sucesión de algoritmos cada vez
mejores, y fijémonos en si el límite es **finito**: si el exponente polinomial al que tienden los algoritmos es un
número o es `⊤`. Y como todo lo que tenemos es finito (cada algoritmo, cada entrada, cada circuito), ¿llegamos?

## Tres respuestas, cada una probada

1. **Por largo, sí** (`tamMin_alcanzado`). Para cada `n` hay finitos circuitos de cada tamaño, así que el **óptimo
   existe**: el menor circuito que decide un problema en las entradas de `n` bits se alcanza. Por largo no hay
   irracionales: la complejidad verdadera de cada rebanada es un número natural que algún circuito realiza.
2. **La finitud no se alcanza en el límite** (`limite_finito_iff`). Midiendo cada algoritmo por su grado polinomial
   (`gradoPol`, en `ℕ∞`: `⊤` si no es polinomial), el ínfimo de los grados de una sucesión es finito **si y solo si
   alguno de los algoritmos ya es polinomial**. Una sucesión de algoritmos superpolinomiales, por buena que se vuelva,
   tiene límite `⊤` (`no_llega`): o ya llegaste en un paso finito, o no llegás nunca. La escalera de
   `Cuasipolinomial.lean` es un ejemplo (`escalera_cuasi_no_llega`): cada peldaño más bajo, y el grado del límite
   sigue siendo `⊤`. El «irracional» de la imagen de José, si existe, no vive en la escala polinomial. Ahí solo hay
   finito o `⊤`. Vive en una escala más fina, la de la cebolla.
3. **Lo no uniforme es la finitud de la sucesión de óptimos** (`psobrePoly_iff_grado`). Un problema tiene circuitos
   polinomiales si y solo si el grado de la sucesión de tamaños mínimos (`sucNat`) es finito. Cada término es finito y
   se alcanza (1), pero la sucesión entera puede tener grado `⊤`: Shannon da problemas así
   (`existe_problema_fuera_de_PsobrePoly`, de `Circuitos.lean`).

## La lectura

Lo finito llega **largo por largo**. Lo que puede no llegar es lo **uniforme**: un solo programa finito que produzca
los óptimos de todos los largos, como una regla finita que produzca todos los decimales. La sucesión de óptimos es un
objeto infinito hecho de piezas finitas, como la expansión de un irracional. `P` pregunta si la genera un programa
polinomial; `P/poly` solo pregunta si sus tamaños crecen como un polinomio.

## Lo que no

Nada de esto dice de qué lado cae SAT. `NP ⊆ P/poly` y `P = NP` siguen abiertos; aquí solo se prueba que la pregunta
por la finitud del límite **es** la pregunta por un algoritmo (o una familia de circuitos) polinomial, y que ninguna
sucesión de algoritmos superpolinomiales la contesta por convergencia.
-/

namespace Sagitta.Map
namespace Tiempo
namespace Finitud

open Shannon

/-! ## 1. Por largo, el óptimo se alcanza -/

/-- **El menor circuito existe.** Para toda función de `n` bits hay un circuito de exactamente `tamMin f` compuertas
que la calcula. -/
theorem tamMin_alcanzado {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ (t : ℕ) (C : Circuito n t), calcula C = f ∧ tamMin f = t := by
  classical
  have hex : ∃ t, ∃ C : Circuito n t, calcula C = f := toda_funcion_calculable f
  obtain ⟨C, hC⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, C, hC, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le _ (iInf_le_of_le C (iInf_le_of_le hC le_rfl))
  · refine le_iInf fun t => le_iInf fun C' => le_iInf fun hC' => ?_
    exact_mod_cast Nat.find_min' hex ⟨C', hC'⟩

/-- La sucesión de tamaños mínimos, como números naturales (cada término es finito). -/
noncomputable def sucNat (L : Problema) (n : ℕ) : ℕ := (sucesion L n).toNat

theorem sucesion_eq (L : Problema) (n : ℕ) : sucesion L n = (sucNat L n : ℕ∞) :=
  (ENat.natCast_toNat (sucesion_lt_top L n).ne).symm

/-! ## 2. La finitud no se alcanza en el límite -/

/-- **El grado polinomial** de una función de costo: el menor `d` con `T(n) ≤ c · (n+1)^d`; `⊤` si no hay. -/
noncomputable def gradoPol (T : ℕ → ℕ) : ℕ∞ :=
  ⨅ (d : ℕ) (_ : ∃ c, ∀ n, T n ≤ c * (n + 1) ^ d), (d : ℕ∞)

/-- El grado es finito si y solo si el costo es polinomial. -/
theorem gradoPol_lt_top_iff (T : ℕ → ℕ) : gradoPol T < ⊤ ↔ T ∈ Pol := by
  constructor
  · intro h
    rw [gradoPol, iInf_lt_iff] at h
    obtain ⟨d, hd⟩ := h
    rw [iInf_lt_iff] at hd
    obtain ⟨⟨c, hc⟩, -⟩ := hd
    exact ⟨c, d, hc⟩
  · rintro ⟨c, d, hc⟩
    exact lt_of_le_of_lt (iInf_le_of_le d (iInf_le_of_le ⟨c, hc⟩ le_rfl)) (ENat.natCast_lt_top d)

/-- **La finitud del límite.** El ínfimo de los grados de una sucesión de algoritmos es finito si y solo si alguno de
ellos ya es polinomial. -/
theorem limite_finito_iff (T : ℕ → ℕ → ℕ) : (⨅ k, gradoPol (T k)) < ⊤ ↔ ∃ k, T k ∈ Pol := by
  rw [iInf_lt_iff]
  exact exists_congr fun k => gradoPol_lt_top_iff (T k)

/-- **O ya llegaste, o no llegás.** Si ningún algoritmo de la sucesión es polinomial, el límite de los grados es `⊤`,
por mucho que mejoren. -/
theorem no_llega (T : ℕ → ℕ → ℕ) (h : ∀ k, T k ∉ Pol) : (⨅ k, gradoPol (T k)) = ⊤ := by
  by_contra hne
  obtain ⟨k, hk⟩ := (limite_finito_iff T).1 (lt_top_iff_ne_top.2 hne)
  exact h k hk

/-- **La escalera de `Cuasipolinomial.lean` no llega**: cada peldaño `n^(log⁽ᵏ⁺¹⁾ n)` queda en `O` del anterior, y el
grado del límite sigue siendo `⊤`. -/
theorem escalera_cuasi_no_llega :
    (∀ k, EsO (cuasi (k + 2)) (cuasi (k + 1))) ∧ (⨅ k, gradoPol (cuasi (k + 1))) = ⊤ :=
  ⟨fun k => cuasi_succ_le (k + 1), no_llega (fun k => cuasi (k + 1)) fun k => cuasi_no_pol (k + 1)⟩

/-! ## 3. Lo no uniforme: la finitud de la sucesión de óptimos -/

/-- **P/poly es la finitud del grado de la sucesión de óptimos.** Cada término se alcanza (`tamMin_alcanzado`); lo
que se pregunta es si la sucesión entera crece como un polinomio. -/
theorem psobrePoly_iff_grado (L : Problema) : L ∈ PsobrePoly ↔ gradoPol (sucNat L) < ⊤ := by
  rw [gradoPol_lt_top_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.eval 1 + p.eval 0, p.natDegree, fun n => ?_⟩
    have h1 : sucNat L n ≤ p.eval n := by
      have := hp n; rw [sucesion_eq] at this; exact_mod_cast this
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [zero_add, one_pow, mul_one]; omega
    · have h2 := eval_le_mul_pow p hn
      have h3 : n ^ p.natDegree ≤ (n + 1) ^ p.natDegree := Nat.pow_le_pow_left (by omega) _
      calc sucNat L n ≤ p.eval 1 * n ^ p.natDegree := h1.trans h2
        _ ≤ (p.eval 1 + p.eval 0) * (n + 1) ^ p.natDegree :=
          Nat.mul_le_mul (Nat.le_add_right _ _) h3
  · rintro ⟨c, k, hc⟩
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ k, fun n => ?_⟩
    rw [sucesion_eq]
    have : (Polynomial.C c * (Polynomial.X + 1) ^ k).eval n = c * (n + 1) ^ k := by simp
    rw [this]; exact_mod_cast hc n

/-- **Hay sucesiones de óptimos sin límite finito**: Shannon da un problema cuya sucesión de tamaños mínimos tiene
grado `⊤`, aunque cada término sea un número que algún circuito alcanza. -/
theorem existe_grado_infinito : ∃ L : Problema, gradoPol (sucNat L) = ⊤ := by
  obtain ⟨L, hL⟩ := existe_problema_fuera_de_PsobrePoly
  exact ⟨L, by by_contra h; exact hL ((psobrePoly_iff_grado L).2 (lt_top_iff_ne_top.2 h))⟩

/-! ## Controles -/

/-- El costo lineal tiene grado a lo sumo 1. -/
example : gradoPol (fun n => n) ≤ 1 := iInf_le_of_le 1 (iInf_le_of_le ⟨1, fun n => by simp⟩ le_rfl)

/-- Una sucesión que llega en el paso 3 (ahí se vuelve lineal) tiene límite finito. -/
example : (⨅ k, gradoPol (fun n => if k < 3 then 2 ^ n else n)) < ⊤ :=
  (limite_finito_iff _).2 ⟨3, ⟨1, 1, fun n => by simp⟩⟩

end Finitud
end Tiempo
end Sagitta.Map
