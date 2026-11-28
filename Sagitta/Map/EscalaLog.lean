import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Embedding.Basic

/-!
# La escala logarítmica: escribir un índice cuesta `⌈log_k m⌉` símbolos

Con un alfabeto de `k` símbolos, una palabra de largo `ℓ` es una función `Fin ℓ → Fin k`, y hay `k^ℓ`.

* `codificar_cota`: toda codificación inyectiva de `m` casos en palabras de largo `ℓ` cumple `m ≤ k^ℓ`.
* `codificar_log`: o sea, `⌈log_k m⌉ ≤ ℓ` (`Nat.clog`).
* `codificar_alcanza` (control): con `k ≥ 2`, largo `⌈log_k m⌉` alcanza: la cota es exacta.
* `cambiar_alfabeto` (lectura): pasar de `k` a `k^j` símbolos divide el largo necesario por `j`, a lo sumo con
  redondeo. El alfabeto solo cambia una constante.

Lo que esto NO dice: nada del costo de **calcular** qué índice escribir. Solo acota cuánto ocupa escribirlo.
-/

namespace Sagitta.Map.Tiempo.EscalaLog

/-- **Palomar de las palabras**: `m` casos distintos en palabras de largo `ℓ` sobre `k` símbolos exigen `m ≤ k^ℓ`. -/
theorem codificar_cota {m k ℓ : ℕ} (e : Fin m → (Fin ℓ → Fin k)) (he : Function.Injective e) : m ≤ k ^ ℓ := by
  have := Fintype.card_le_of_injective e he
  rwa [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at this

/-- **En logaritmo**: el largo es al menos `⌈log_k m⌉`. -/
theorem codificar_log {m k ℓ : ℕ} (e : Fin m → (Fin ℓ → Fin k)) (he : Function.Injective e) :
    Nat.clog k m ≤ ℓ :=
  Nat.clog_le_of_le_pow (codificar_cota e he)

/-- **Control: la cota se alcanza.** Con `k ≥ 2` hay una codificación inyectiva de largo `⌈log_k m⌉`. -/
theorem codificar_alcanza {m k : ℕ} (hk : 1 < k) :
    ∃ e : Fin m → (Fin (Nat.clog k m) → Fin k), Function.Injective e := by
  have h : Fintype.card (Fin m) ≤ Fintype.card (Fin (Nat.clog k m) → Fin k) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    exact Nat.le_pow_clog hk m
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le h
  exact ⟨f, f.injective⟩

/-- **El alfabeto solo cambia una constante**: si `m ≤ (k^j)^ℓ` entonces `m ≤ k^(j·ℓ)`; un símbolo de `k^j` vale `j`
símbolos de `k`. -/
theorem cambiar_alfabeto {m k j ℓ : ℕ} (h : m ≤ (k ^ j) ^ ℓ) : m ≤ k ^ (j * ℓ) := by
  rw [pow_mul]; exact h

/-- **Control concreto**: 1000 casos en bits piden 10; en decimal, 3. -/
example : Nat.clog 2 1000 = 10 ∧ Nat.clog 10 1000 = 3 := by decide

end Sagitta.Map.Tiempo.EscalaLog
