import Sagitta.Map.BuenaFundacion

/-!
# El contador: un descenso largo que no es difícil

El ejemplo del contador binario, como teorema. El costo de una cadena es el número que representa en
binario; el vecino, ese número menos uno, con los mismos bits. Desde `11⋯1` el descenso tarda exactamente `2ⁿ − 1`
pasos. Pero el único óptimo de cada longitud es `00⋯0`, que se escribe sin buscar.

Convención: el primer bit de la lista es el menos significativo. Como `11⋯1` y `00⋯0` se leen igual en los dos
sentidos, no cambia nada del enunciado.

**Lo que no se prueba aquí:** que el costo y el vecino se calculan en tiempo polinomial, que es lo que haría del
contador una `BusquedaLocal`. Es cierto (sumar y restar en binario es lineal), pero construir las máquinas de Turing
en Mathlib es un trabajo aparte. Por eso el contador es un `Descenso`.
-/

namespace Sagitta.Map
namespace Contador

/-- El número que representa una cadena, con el primer bit como el menos significativo. -/
def valor : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * valor bs

/-- Restar uno en binario, con los mismos bits. Cero se queda en cero. -/
def dec : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => if valor bs = 0 then false :: bs else true :: dec bs

#guard (List.range 8).map (fun k => valor (dec^[k] [true, true, true])) = [7, 6, 5, 4, 3, 2, 1, 0]

theorem dec_length : ∀ x : List Bool, (dec x).length = x.length
  | [] => rfl
  | true :: _ => rfl
  | false :: bs => by
    unfold dec
    split_ifs
    · rfl
    · simp [dec_length bs]

/-- **El vecino vale uno menos** (o cero, si ya era cero). -/
theorem valor_dec : ∀ x : List Bool, valor (dec x) = valor x - 1
  | [] => rfl
  | true :: bs => by simp [dec, valor]
  | false :: bs => by
    unfold dec
    split_ifs with h
    · simp [valor, h]
    · have := valor_dec bs
      simp only [valor, Bool.false_eq_true, ↓reduceIte] at h ⊢
      omega

/-- Una cadena de `n` bits vale menos de `2ⁿ`. -/
theorem valor_lt : ∀ x : List Bool, valor x < 2 ^ x.length
  | [] => by simp [valor]
  | b :: bs => by
    have := valor_lt bs
    simp only [valor, List.length_cons, pow_succ]
    split_ifs <;> omega

/-- El contador como descenso. -/
def contador : Descenso where
  costo := valor
  vecino := dec
  conserva := dec_length

/-- Después de `k` pasos, el costo bajó `k` (hasta llegar a cero). -/
theorem valor_iterate (k : ℕ) (x : List Bool) : valor (dec^[k] x) = valor x - k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, valor_dec]
    omega

/-- **Óptimo es valer cero.** -/
theorem esOptimo_iff (x : List Bool) : contador.EsOptimo x ↔ valor x = 0 := by
  show valor x ≤ valor (dec x) ↔ _
  rw [valor_dec]
  omega

/-- **El descenso tarda exactamente `valor x` pasos**: llega al óptimo en ese paso y en ninguno antes. La cota de
`Descenso.desciende_desde` (a lo sumo `costo x` pasos) se alcanza. -/
theorem pasos_exactos (x : List Bool) :
    contador.EsOptimo (dec^[valor x] x) ∧ ∀ k < valor x, ¬ contador.EsOptimo (dec^[k] x) := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [esOptimo_iff, valor_iterate]
    omega
  · rw [esOptimo_iff, valor_iterate]
    omega

theorem valor_unos (n : ℕ) : valor (List.replicate n true) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, valor, ih, ↓reduceIte, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

/-- **Un descenso largo.** Desde `11⋯1` (`n` unos), seguir al vecino tarda exactamente `2ⁿ − 1` pasos. -/
theorem descenso_largo (n : ℕ) :
    contador.EsOptimo (dec^[2 ^ n - 1] (List.replicate n true)) ∧
      ∀ k < 2 ^ n - 1, ¬ contador.EsOptimo (dec^[k] (List.replicate n true)) := by
  have := pasos_exactos (List.replicate n true)
  rwa [valor_unos] at this

/-- Vale cero exactamente la cadena de ceros. -/
theorem valor_eq_cero_iff : ∀ x : List Bool, valor x = 0 ↔ x = List.replicate x.length false
  | [] => by simp [valor]
  | b :: bs => by
    have := valor_eq_cero_iff bs
    cases b <;> simp [valor, List.replicate_succ, this]

/-- **Un óptimo por longitud**: el único óptimo de longitud `n` es `00⋯0`. -/
theorem optimo_unico (x : List Bool) : contador.EsOptimo x ↔ x = List.replicate x.length false := by
  rw [esOptimo_iff, valor_eq_cero_iff]

/-- **El atajo.** Escribir `n` ceros: un óptimo de la misma longitud, sin recorrer el descenso. -/
def atajo (x : List Bool) : List Bool := List.replicate x.length false

theorem atajo_correcto (x : List Bool) :
    (atajo x).length = x.length ∧ contador.EsOptimo (atajo x) := by
  refine ⟨List.length_replicate, ?_⟩
  rw [optimo_unico]
  simp [atajo]

end Contador
end Sagitta.Map
