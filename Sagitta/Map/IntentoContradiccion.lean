import Sagitta.Map.RaizMuerta
import Sagitta.Map.DemoraEfectiva
import Sagitta.Map.Decidir

/-!
# Un intento: suponer el detector y buscar la contradicción

**El supuesto.** Hay un detector sano, de tiempo polinomial, con demora logarítmica sobre el árbol de elecciones de SAT.
Por `BusquedaPolinomial.lean`, eso pondría a SAT en P. Llegar a una contradicción en general sería probar P ≠ NP, así
que el intento no cierra. Lo que sí se puede es empujar cada ruta hasta su muro y dejar probadas las contradicciones que
salen.

## Lo que se prueba

* **Ruta de la caja negra** (`supuesto_caja_negra_falso`): si el detector solo puede preguntar por la fórmula como caja
  negra, el supuesto es falso. Ningún algoritmo decide «existe una opción buena» con menos preguntas que opciones; es el
  adversario de `Decidir.lean`. **El muro**: hay un oráculo con P = NP (Baker, Gill y Solovay, 1975), así que este
  argumento solo, que no mira dentro de la fórmula, no puede probar P ≠ NP.
* **Ruta del detector de cláusulas** (`detCNF_sin_demora_log`): el detector de los resolvedores, «hay una cláusula
  falsa», **no tiene demora logarítmica** en la familia del palomar. Si la tuviera, la cota superior de nodos de
  `DemoraEfectiva.lean` (`(N+1) · 2^(d+1)`, polinomial con `d` logarítmica) quedaría por encima de la inferior de
  `RaizMuerta.lean` (`(n/2+1)^(n/2) / 2`), que no es polinomial. **El muro**: vale para ese detector; uno más listo no
  queda cubierto.

## Lo que no

* **La ruta de los sistemas de pruebas** está en `RaizMuertaPruebas.lean` (`refutaciones_uniformes`): el supuesto da
  refutaciones cortas para toda fórmula sin solución. Una contradicción por aquí exigiría cotas inferiores para todo
  sistema de pruebas, que es NP ≠ coNP (Cook y Reckhow, 1979): abierto. Se conocen para resolución, no para Frege.
* **La diagonalización** no da contradicción: P = NP no contradice los teoremas de jerarquía, y la diagonalización
  relativiza, así que choca con el mismo muro que la caja negra.
-/

namespace Sagitta.Map
namespace Tiempo

open Cslib Cslib.Logic.PL

/-! ## La caja negra -/

/-- **En caja negra, el supuesto es falso**: ningún algoritmo de preguntas decide si hay una opción buena con menos
preguntas que opciones. -/
theorem supuesto_caja_negra_falso {α : Type} [Fintype α] :
    ¬ ∃ t : Pregunta α, DecideExiste t ∧ Pregunta.costo t (fun _ => false) < Fintype.card α := by
  classical
  rintro ⟨t, ht, hc⟩
  exact absurd (costo_adversario t ht) (by omega)

/-! ## El detector de cláusulas sobre el palomar -/

/-- El orden de las variables del palomar con `n + 1` palomas y `n` nidos: `(i, j) ↦ n·i + j`. -/
def ordenPal (n : ℕ) (v : Fin (n + 1) × Fin n) : ℕ := n * v.1.val + v.2.val

theorem ordenPal_lt (n : ℕ) (v : Fin (n + 1) × Fin n) : ordenPal n v < n * (n + 1) := by
  unfold ordenPal
  have h1 := v.1.isLt
  have h2 := v.2.isLt
  nlinarith

theorem ordenPal_inj (n : ℕ) : Function.Injective (ordenPal n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [ordenPal] at h
  have hj := j.isLt
  have hj' := j'.isLt
  have hpos : 0 < n := by omega
  have hdiv : i.val = i'.val := by
    have e1 : (n * i.val + j.val) / n = i.val := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj, zero_add]
    have e2 : (n * i'.val + j'.val) / n = i'.val := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj', zero_add]
    rw [← e1, ← e2, h]
  have hmod : j.val = j'.val := by rw [hdiv] at h; omega
  exact Prod.ext (Fin.ext hdiv) (Fin.ext hmod)

/-- **La familia del palomar**, con `n + 1` palomas, `n` nidos y el orden `ordenPal`. -/
def formulaPal (n : ℕ) : List Clausula := (CNF.pigeonhole (n + 1) n).relabel (ordenPal n)

/-- `2^(a · log₂ x) ≤ x^a`, para `x > 0`. -/
theorem dos_pow_mul_log_le (a x : ℕ) (hx : 0 < x) : 2 ^ (a * Nat.log 2 x) ≤ x ^ a := by
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hx.ne') a

/-- **La cuenta final**: `(t+1)^t` le gana a `C · (t+1)^e` cuando `t = C + e`. -/
theorem pow_gana (C e : ℕ) (hC : 1 ≤ C) : C * (C + e + 1) ^ e < (C + e + 1) ^ (C + e) := by
  set u := C + e + 1
  have hu : C < u := by omega
  have h1 : (u : ℕ) ^ (C + e) = u ^ e * u ^ C := by rw [← pow_add, add_comm]
  rw [h1]
  have hC1 : u ≤ u ^ C := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ C := Nat.pow_le_pow_right (by omega) hC
  have hpos : 0 < u ^ e := pow_pos (by omega) _
  calc C * u ^ e < u * u ^ e := Nat.mul_lt_mul_of_pos_right hu hpos
    _ ≤ u ^ C * u ^ e := Nat.mul_le_mul_right _ hC1
    _ = u ^ e * u ^ C := mul_comm _ _

/-- **El detector de cláusulas no tiene demora logarítmica en el palomar.** Para todos `a` y `b` hay un `n` tal que
`detCNF` no tiene demora `a · log₂(N + 1) + b` sobre la fórmula del palomar con `n + 1` palomas y `n` nidos, donde
`N = n(n+1)` es el número de variables. -/
theorem detCNF_sin_demora_log (a b : ℕ) :
    ∃ n, ¬ DemoraN (solCNF (formulaPal n)) (detCNF (formulaPal n)) (n * (n + 1))
      (a * Nat.log 2 (n * (n + 1) + 1) + b) := by
  set C := 2 ^ (b + 2) * 4 ^ (a + 1) with hCdef
  have hC : 1 ≤ C := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set e := 2 * a + 2
  set t := C + e
  refine ⟨2 * t, fun hd => ?_⟩
  set n := 2 * t with hn
  set N := n * (n + 1) with hN
  have hpos : 0 < n := by omega
  -- la cota inferior del palomar
  have hlow := palomar_nodos_mitad (m := n + 1) (n := n) (by omega) hpos (ordenPal_inj n) (ordenPal_lt n)
  -- la cota superior con demora logarítmica
  have hup := nodos_le (k := N) (p := []) (sano_sanoN N (detCNF_sano (formulaPal n))) hd (by simp)
  have hlog : 2 ^ (a * Nat.log 2 (N + 1) + b + 1) ≤ 2 ^ (b + 1) * (N + 1) ^ a := by
    rw [show a * Nat.log 2 (N + 1) + b + 1 = a * Nat.log 2 (N + 1) + (b + 1) by ring, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (dos_pow_mul_log_le a (N + 1) (by omega))
  have hN1 : N + 1 ≤ 4 * (t + 1) ^ 2 := by simp only [hN, hn]; nlinarith
  -- juntar: (t+1)^t < 2·(N+1)·2^(b+1)·(N+1)^a ≤ C·(t+1)^e
  have hn2 : n / 2 = t := by omega
  rw [hn2] at hlow
  have hbig : (t + 1) ^ t < C * (t + 1) ^ e := by
    calc (t + 1) ^ t < 2 * nodos (solCNF (formulaPal n)) (detCNF (formulaPal n)) N [] := by
          simpa [formulaPal] using hlow
      _ ≤ 2 * ((N + 1) * 2 ^ (a * Nat.log 2 (N + 1) + b + 1)) := Nat.mul_le_mul_left _ hup
      _ ≤ 2 * ((N + 1) * (2 ^ (b + 1) * (N + 1) ^ a)) := by gcongr
      _ = 2 ^ (b + 2) * (N + 1) ^ (a + 1) := by ring
      _ ≤ 2 ^ (b + 2) * (4 * (t + 1) ^ 2) ^ (a + 1) := by gcongr
      _ = C * (t + 1) ^ e := by rw [hCdef, mul_pow, ← pow_mul]; ring
  exact lt_irrefl _ (lt_trans hbig (pow_gana C e hC))

end Tiempo
end Sagitta.Map
