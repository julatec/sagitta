import Sagitta.Map.KtSAT

/-!
# Cuánto cuesta una ejecución, dada la descripción del resolvedor

La pregunta es de José (24 nov 2026): **suponiendo que existe un resolvedor polinomial de SAT, ¿cuánto costaría una
ejecución dada su complejidad descriptiva? Si cada paso cobra leer el programa, ¿eso no deja una cota inferior?**

## La respuesta, en tres piezas

1. **La descripción del programa no da cota inferior** (`descripcion_no_saca_de_pol`). Con un programa fijo de `L` bits
   que corre `t(n)` pasos y usa `S(n) ≤ t(n)` bits de estado, el costo real cobrando la lectura del programa y del estado
   en cada paso es `t · (L + S) ≤ t · (L + t)`. Si `t ∈ Pol`, eso también: el sobrecosto es polinomial y no saca a nadie
   de `P`. `L` es una constante porque el programa es uno solo para todos los tamaños.
2. **La cota inferior que sí funciona es la de la instancia** (`cota_por_instancia`). Si el proceso `(i, k)` resuelve la
   fórmula `F` en el universo cerrado, entonces `2^(kt F) < 2^(i+1) · k`, o sea `k > 2^(kt F − i − 1)`. El tiempo está
   acotado por debajo por la **profundidad de la instancia** (`kt`); el programa solo descuenta su largo `i`.
3. **La descripción del mejor resolvedor de búsqueda es constante** (`descripcion_constante`). Un único programa, el de
   Levin, sirve para todas las fórmulas satisfacibles, con `kt F ≤ código de L + ⌈log₂ costo⌉`. La complejidad
   descriptiva del resolvedor nunca puede ser la fuente de la dificultad: lo es la de las instancias.

## La lectura

Asumiendo el resolvedor polinomial, cada ejecución cuesta lo que pide su instancia; la descripción no agrega nada que
importe. Probar que alguna familia de fórmulas satisfacibles tiene `kt` superlogarítmica es, en el modelo, que SAT no es
fácil (`facil_iff_kt` de `KtSAT.lean`): ahí está todo el problema, en la profundidad de las instancias.

## Lo que NO se prueba

* El costo por paso `L + S` es un modelo declarado (como en `CuboTransiciones.lean`), no tiempo de máquina.
* Las piezas 2 y 3 están sobre la medida de `evaln` (rondas), no sobre pasos de máquina: ver `RondasAcotadas.lean`.
* Nada sobre `P` contra `NP`.
-/

namespace Sagitta.Map.Tiempo.CotaDescriptiva

open Sagitta.Map.Tiempo Sagitta.Map.Tiempo.KtSAT
open Sagitta.Map.Tiempo.UniversoCerrado

/-! ## 1. La descripción del programa no da cota inferior -/

/-- El costo real de una ejecución, cobrando en cada uno de los `t` pasos la lectura del programa (`L` bits) y del
estado (`S` bits). -/
def costoReal (L : ℕ) (t S : ℕ → ℕ) (n : ℕ) : ℕ := t n * (L + S n)

/-- **`Pol` es cerrado hacia abajo.** -/
theorem pol_abajo {f g : ℕ → ℕ} (hg : g ∈ Pol) (h : ∀ n, f n ≤ g n) : f ∈ Pol := by
  obtain ⟨c, k, hc⟩ := hg
  exact ⟨c, k, fun n => (h n).trans (hc n)⟩

/-- **El sobrecosto es a lo sumo cuadrático**: con `S ≤ t`, el costo real es `≤ t · (L + t)`. -/
theorem costoReal_le (L : ℕ) {t S : ℕ → ℕ} (hS : ∀ n, S n ≤ t n) (n : ℕ) :
    costoReal L t S n ≤ t n * (L + t n) :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_left (hS n) _)

/-- **La descripción no saca de `P`**: si el resolvedor corre en tiempo polinomial, el costo real cobrando la lectura
del programa y del estado en cada paso también es polinomial. -/
theorem descripcion_no_saca_de_pol (L : ℕ) {t S : ℕ → ℕ} (ht : t ∈ Pol) (hS : ∀ n, S n ≤ t n) :
    costoReal L t S ∈ Pol :=
  pol_abajo (pol_mul ht (pol_add (pol_const L) ht)) (costoReal_le L hS)

/-- **Control: el cobro no es gratis**: con `L ≥ 1`, el costo real nunca baja de `t`. -/
theorem cobro_cuenta (L : ℕ) (t S : ℕ → ℕ) (n : ℕ) (hL : 1 ≤ L) :
    t n < costoReal L t S n + 1 ∧ t n ≤ costoReal L t S n := by
  have : t n * 1 ≤ t n * (L + S n) := Nat.mul_le_mul_left _ (by omega)
  unfold costoReal
  constructor <;> omega

/-! ## 2. La cota inferior que sí funciona: la de la instancia -/

/-- **La cota por la instancia**: si el proceso `(i, k)` resuelve `F`, entonces `2^(kt F) < 2^(i+1) · k`. El tiempo
`k` está acotado por debajo por la profundidad de `F`, descontando solo el largo `i` del programa. -/
theorem cota_por_instancia {F : List Clausula} {p : Proceso} (h : Correcto (uSAT F) p) :
    2 ^ ktSAT F < 2 ^ (p.i + 1) * p.k := by
  have hk : 1 ≤ p.k := by have := Correcto.x_lt h; omega
  have h1 : 2 ^ ktSAT F ≤ 2 ^ p.i * 2 ^ Nat.clog 2 p.k := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (kt_de_proceso h)
  have h2 : 2 ^ Nat.clog 2 p.k < 2 * p.k := Levin.pow_clog_lt hk
  calc 2 ^ ktSAT F ≤ 2 ^ p.i * 2 ^ Nat.clog 2 p.k := h1
    _ < 2 ^ p.i * (2 * p.k) := Nat.mul_lt_mul_of_pos_left h2 (pow_pos (by norm_num) _)
    _ = 2 ^ (p.i + 1) * p.k := by ring

/-- **Con un programa fijo, el tiempo crece como `2^kt`**: si un mismo programa `i` resuelve una familia de
fórmulas, cada una con tiempo `k F`, entonces `2^(kt F) < 2^(i+1) · k F` para todas: si la `kt` de la familia no es
logarítmica, el tiempo no es polinomial. -/
theorem programa_fijo_paga_kt {ι : Type} {F : ι → List Clausula} {i : ℕ} {k : ι → ℕ}
    (h : ∀ j, Correcto (uSAT (F j)) ⟨i, k j⟩) (j : ι) : 2 ^ ktSAT (F j) < 2 ^ (i + 1) * k j :=
  cota_por_instancia (p := ⟨i, k j⟩) (h j)

/-! ## 3. La descripción del mejor resolvedor de búsqueda es constante -/

/-- **Un solo programa para todas las fórmulas**: el de Levin. Su descripción (`encodeCode L`) es una constante, y para
toda fórmula satisfacible `kt F ≤ encodeCode L + ⌈log₂ costo L⌉`. -/
theorem descripcion_constante : ∃ L : Nat.Partrec.Code, ∀ F, Satisfacible F →
    ktSAT F ≤ Nat.Partrec.Code.encodeCode L + Nat.clog 2 (AceleracionBlum.costo L (Encodable.encode F)) := by
  obtain ⟨L, -, hL⟩ := levin_es_programa_sat
  exact ⟨L, fun F hF => (hL F hF).2.2⟩

end Sagitta.Map.Tiempo.CotaDescriptiva
