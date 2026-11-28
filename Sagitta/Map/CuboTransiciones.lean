import Sagitta.Map.CuboCostos

/-!
# El cubo con las transiciones cobradas

La idea es de José (24 nov 2026). En el cubo de costos (`CuboCostos`) cada paso del autómata es **gratis** una vez que
el autómata existe: la descripción (programa más cita, `x` bits) se paga una sola vez, antes de correr. Pero moverse
entre estados cuesta: una máquina universal que simula al autómata tiene que **leer el estado actual y la descripción**
para saber cuál es el paso siguiente. Cobrar ese movimiento convierte la descripción en un costo de **ejecución**, que
se paga en cada paso, y no solo en un costo de una vez.

## El modelo de costo (declarado, no probado)

* **El costo por paso** es una función `c : ℕ → ℕ → ℕ` (`CostoPaso`) de los bits de descripción `a = L + s` y los bits
  de estado `S`. La forma base es `costoBase a S = a + S`: leer la descripción entera y el estado entero.
* **El costo de ejecución** de una corrida de `t` consultas es `T = t · c(a, S)` (`costoEjecucion`). En el cubo se mide
  en bits, `Y = ⌈log₂(T + 1)⌉`, como el tiempo `y = ⌈log₂(t + 1)⌉`.
* **Por qué se cobra también la cita.** En este modelo la cita no se copia al estado: el autómata `A p c` la usa en
  `consulta`, `δ` y `salida` sin guardarla en `σ` (el barrido `barridoA` consulta `(c, i)` con `c` fijo). Para dar un
  paso, el simulador la tiene que tener a mano igual que el programa. Si se la quisiera copiar al estado, se pagaría en
  `S` y el costo por paso sería el mismo.
* **Por qué es una cota razonable.** Una máquina universal que, en cada paso, relee la descripción entera y el estado
  entero hace a lo sumo `O(a + S)` trabajo por paso para buscar la transición: es el **peor caso** del sobrecosto de
  simulación y, por eso, honesto como **cota superior** de ese sobrecosto. Una máquina universal real puede pagar menos
  (indexando el programa, cacheando la transición) o más (moviendo un cabezal); el costo aquí es **declarado**.

## La ley con transiciones cobradas

* **En términos de `T`** (`ley_transiciones`): con `c ≥ 1`, `N ≤ 2^(L+s) · min (T / c + 1) 2^(S−1)`. En bits
  (`ley_transiciones_log`):

  `⌈log₂ N⌉ ≤ (L + s) + min (Y − ⌊log₂ c(L+s, S)⌋) (S − 1)`.

  El término `− ⌊log₂ c⌋` es lo nuevo: cada paso cuesta `c` y el tiempo útil es `T / c`. Con `c = 1` vuelve
  `ley_cubo_log` exacta (`ley_uno`, `trans_uno_es_cubo`).
* **La región, exacta, para cualquier `c` monótona en el estado** (`region_trans`): `(x, e, Y)` se alcanza si y solo si
  hay `k ≤ m` con `m − k ≤ x`, `S_k ≤ e` y `⌈log₂((2^k − 1) · c(m − k, S_k) + 1)⌉ ≤ Y`, donde `S_k = k + 1` (o `0` si
  `k = 0`). Es el barrido de `CuboCostos` con su costo cobrado (`punto_trans`), y nada lo mejora
  (`trans_sobre_frontera`): un programa a medias de `m − k` bits necesita `2^k − 1` pasos y `k + 1` bits de estado, y
  cada paso lo paga entero.
* **La forma base** (`region_base`, con `c = a + S`): se alcanza `(x, e, Y)` si y solo si

  `m ≤ x`, o bien `m − x + 1 ≤ e` y `⌈log₂((2^(m−x) − 1) · (m + 1) + 1)⌉ ≤ Y`.

  En la frontera el costo por paso es `(m − k) + (k + 1) = m + 1` **para todo `k`**: el bit de programa que se ahorra
  se paga en estado. En bits (`ley_base`): `m ≤ x`, o bien `m + ⌊log₂(m + 1)⌋ ≤ x + Y` (y `m ≤ x + (e − 1)`). Es
  `m ≤ x + min (Y − ⌊log₂ c⌋) (e − 1)` con `c = m + 1`.

## Lo que cambia respecto de `cubo_es_region`

* **La tabla sigue gratis** (`tabla_gratis`): con la solución escrita en la descripción (`x = m`, `t = 0`), el costo de
  ejecución es `0` con cualquier `c`.
* **Un programa a medias paga cada paso entero** (`a_medias_paga`): con `x = m − k` (`1 ≤ k ≤ m`) la corrida paga
  `(2^k − 1) · (m + 1)`, y con menos no se puede. El punto `(m − k, k + 1, k)` del cubo, que está en la frontera
  (`contador_en_la_recta`), ya **no** se alcanza (`cubo_no_basta`).
* **La diagonal se rompe** (`diagonal_rota`, `estrategia_cambia`): en el cubo toda la frontera con espacio de sobra
  cumple `x + y = m`, así que la tabla y el barrido empatan. Con las transiciones cobradas, para `m ≥ 1` todo punto
  con `x < m` paga `x + Y ≥ m + 1`: **la tabla es la única estrategia que minimiza `x + Y`**.
* **Un programa más largo encarece cada paso** (`programa_encarece`): con el mismo `t` y el mismo `S`, un bit más de
  descripción sube `T` (estrictamente si `t ≥ 1`). En el cubo `y` no dependía de `x`; aquí sí.

Lectura: con las transiciones cobradas, **la descripción deja de ser gratis durante la ejecución**, y la memoria del
programa y el tiempo dejan de ser ejes independientes. Lo que se ahorra de tiempo escribiendo en el programa se recobra
en parte en cada paso: el desplazamiento de la frontera es `⌊log₂(m + 1)⌋` bits de tiempo, el costo de leer una
descripción de `m + 1` bits.

## Controles

* `c ≡ 1` da el cubo exacto (`trans_uno_es_cubo`, `ley_uno`), conectado con `ley_cubo_log` y `cubo_es_region`.
* El barrido cobrado (`barridoA_cobrado`): `barridoA` con cita de `j` bits y `n` consultas paga `n · (j + S)` con
  `S = ⌈log₂(2n + 1)⌉`; en la frontera, `(2^k − 1)(m + 1)` (`costo_barrido_base`).
* La ley vieja aplicada a `T` es una cota válida (`ley_vieja_vale`) pero no la frontera (`mutante_ley_vieja`).

## Mutantes (refutados aquí; las copias que no compilan están fuera del repositorio)

* `mutante_solo_estado`: cobrar solo `S`. La región cambia y el programa vuelve a ser gratis durante la ejecución.
* `mutante_gratis`: no cobrar nada. El tiempo desaparece del cubo y la ley con `Y` es falsa.
* `mutante_decrece`: un costo por paso que decrece con la descripción. Un programa más largo abarata los pasos.
* `mutante_ley_vieja`: la ley del cubo aplicada a `T` sin el término de `c`, como frontera, es falsa.

## Lo que NO se prueba

* **Que una máquina universal real pague exactamente `L + S` por paso.** El costo por paso es **declarado**: es el
  peor caso de releer todo, una cota superior razonable del sobrecosto de simulación, no un teorema sobre máquinas.
* **No son máquinas de Turing.** El espacio es el número de estados de un autómata sin cinta; el tiempo, consultas al
  verificador; la «lectura» del programa no se modela con un cabezal.
* **Es caja negra y relativiza.** El verificador es un oráculo que se evalúa gratis; todo vale igual relativo a
  cualquier oráculo (Baker, Gill y Solovay, 1975, de memoria), así que no separa ni colapsa clases.
* **Nada sobre P contra NP.**
-/

namespace Sagitta.Map.Tiempo.CuboTransiciones

open Sagitta.Map.Tiempo.LeyTresMemorias
open Sagitta.Map.Tiempo.PlanoCostos
open Sagitta.Map.Tiempo.CuboCostos

/-! ## 1. El costo por transición -/

/-- **El costo de un paso**, como función de los bits de descripción `a = L + s` (programa más cita) y los bits de
estado `S`. Es lo que una máquina universal tiene que leer para dar el paso. Es un **modelo declarado**. -/
abbrev CostoPaso := ℕ → ℕ → ℕ

/-- **La forma base**: leer la descripción entera y el estado entero, `a + S` bits por paso. -/
def costoBase : CostoPaso := fun a S => a + S

/-- **El costo de ejecución** de una corrida de `t` consultas con descripción de `a` bits y estado de `S` bits:
`T = t · c(a, S)`. -/
def costoEjecucion (c : CostoPaso) (a S t : ℕ) : ℕ := t * c a S

/-- **Un programa más largo encarece cada paso** (forma base): con el mismo `t ≥ 1` y el mismo estado, un bit más de
descripción sube el costo de ejecución. -/
theorem programa_encarece {a S t : ℕ} (ht : 1 ≤ t) :
    costoEjecucion costoBase a S t < costoEjecucion costoBase (a + 1) S t := by
  simp only [costoEjecucion, costoBase]
  exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)

/-- **Con cualquier costo monótono en la descripción**, un programa más largo no abarata la corrida. -/
theorem programa_encarece_mono (c : CostoPaso) (hc : ∀ a a' S, a ≤ a' → c a S ≤ c a' S) {a a' S : ℕ} (t : ℕ)
    (h : a ≤ a') : costoEjecucion c a S t ≤ costoEjecucion c a' S t :=
  Nat.mul_le_mul_left _ (hc a a' S h)

/-! ## 2. La ley del cubo con las transiciones cobradas -/

/-- **La ley con `T`** (verificador de sí o no): con `c(L+s, S) ≥ 1` y `T = t · c`,
`N ≤ 2^(L+s) · min (T / c + 1) 2^(S−1)`. Es `ley_cubo` con `t = T / c`. -/
theorem ley_transiciones {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    (c : CostoPaso) {L s S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (A : P → C → Automata σ Y Bool Y) (h : ResuelveA igual A t)
    (hc : 1 ≤ c (L + s) S) :
    Fintype.card Y ≤
      2 ^ (L + s) * min (costoEjecucion c (L + s) S t / c (L + s) S + 1) (2 ^ (S - 1)) := by
  rw [costoEjecucion, Nat.mul_div_cancel _ (by omega : 0 < c (L + s) S), pow_add]
  exact ley_cubo hP hC hσ A h

/-- **El tiempo útil en bits**: si `⌈log₂(t·c + 1)⌉ ≤ Y` con `c ≥ 1`, entonces `⌈log₂(t + 1)⌉ ≤ Y − ⌊log₂ c⌋`. -/
theorem clog_le_sub_log {t c Y : ℕ} (hc : 1 ≤ c) (h : Nat.clog 2 (t * c + 1) ≤ Y) :
    Nat.clog 2 (t + 1) ≤ Y - Nat.log 2 c := by
  rw [Nat.clog_le_iff_le_pow one_lt_two] at h
  have hj : 2 ^ Nat.log 2 c ≤ c := Nat.pow_log_le_self 2 (by omega)
  have hlt : t * 2 ^ Nat.log 2 c < 2 ^ Y :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hj) (by omega)
  apply Nat.clog_le_of_le_pow
  by_cases hY : Nat.log 2 c ≤ Y
  · have h1 : t * 2 ^ Nat.log 2 c < 2 ^ (Y - Nat.log 2 c) * 2 ^ Nat.log 2 c := by
      rw [← pow_add, Nat.sub_add_cancel hY]; exact hlt
    have := Nat.lt_of_mul_lt_mul_right h1
    omega
  · have h1 : t * 2 ^ Nat.log 2 c < 1 * 2 ^ Nat.log 2 c := by
      rw [one_mul]; exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have := Nat.lt_of_mul_lt_mul_right h1
    rw [show Y - Nat.log 2 c = 0 by omega]
    omega

/-- **La ley con transiciones cobradas, en bits**: si la corrida paga `⌈log₂(T + 1)⌉ ≤ Y` con `T = t · c(L+s, S)` y
`c ≥ 1`, entonces `⌈log₂ N⌉ ≤ (L + s) + min (Y − ⌊log₂ c⌋) (S − 1)`. -/
theorem ley_transiciones_log {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    (c : CostoPaso) {L s S t Yb : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (A : P → C → Automata σ Y Bool Y) (h : ResuelveA igual A t)
    (hc : 1 ≤ c (L + s) S) (hT : Nat.clog 2 (costoEjecucion c (L + s) S t + 1) ≤ Yb) :
    Nat.clog 2 (Fintype.card Y) ≤ (L + s) + min (Yb - Nat.log 2 (c (L + s) S)) (S - 1) := by
  have h1 := ley_cubo_log hP hC hσ A h
  have h2 := clog_le_sub_log hc hT
  omega

/-- **Control: con `c = 1` vuelve `ley_cubo_log` exacta**: el término `⌊log₂ 1⌋` es `0` y `T = t`. -/
theorem ley_uno {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (A : P → C → Automata σ Y Bool Y) (h : ResuelveA igual A t) :
    costoEjecucion (fun _ _ => 1) (L + s) S t = t ∧
      Nat.clog 2 (Fintype.card Y) ≤
        (L + s) + min (Nat.clog 2 (costoEjecucion (fun _ _ => 1) (L + s) S t + 1) - Nat.log 2 1) (S - 1) := by
  refine ⟨Nat.mul_one t, ?_⟩
  have := ley_cubo_log hP hC hσ A h
  simp only [costoEjecucion, Nat.mul_one, Nat.log_one_right, Nat.sub_zero]
  omega

/-! ## 3. La región con las transiciones cobradas -/

/-- **Un punto del cubo con transiciones cobradas** `(x, e, Y)` se alcanza con el verificador de sí o no sobre
`N = 2^m` y el costo por paso `c`: como en `AlcanzableCubo`, pero el tercer eje es el costo de ejecución en bits,
`⌈log₂(t · c(L+s, S) + 1)⌉ ≤ Y`. El costo se evalúa en la descripción y el estado **usados**, no en los presupuestos. -/
def AlcanzableTrans (c : CostoPaso) (m x e Y : ℕ) : Prop :=
  ∃ (P C σ : Type) (_ : Fintype P) (_ : Fintype C) (_ : Fintype σ)
    (A : P → C → Automata σ (Fin (2 ^ m)) Bool (Fin (2 ^ m))) (L s S t : ℕ),
    Fintype.card P ≤ 2 ^ L ∧ Fintype.card C ≤ 2 ^ s ∧ Fintype.card σ ≤ 2 ^ S ∧ ResuelveA (siNo m) A t ∧
      L + s ≤ x ∧ S ≤ e ∧ Nat.clog 2 (costoEjecucion c (L + s) S t + 1) ≤ Y

/-- **La región es cerrada hacia arriba.** -/
theorem trans_cerrado_arriba {c : CostoPaso} {m x e Y x' e' Y' : ℕ} (h : AlcanzableTrans c m x e Y) (hx : x ≤ x')
    (he : e ≤ e') (hY : Y ≤ Y') : AlcanzableTrans c m x' e' Y' := by
  obtain ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, h1, h2, h3, h4, by omega, by omega, by omega⟩

/-- **Control: con `c ≡ 1` es el cubo**, punto por punto. -/
theorem trans_uno_es_cubo (m x e Y : ℕ) : AlcanzableTrans (fun _ _ => 1) m x e Y ↔ AlcanzableCubo m x e Y := by
  simp only [AlcanzableTrans, AlcanzableCubo, costoEjecucion, Nat.mul_one]

/-- **Y entonces la región es la de `cubo_es_region`**: `m ≤ x + min Y (e − 1)`. -/
theorem trans_uno_region (m x e Y : ℕ) : AlcanzableTrans (fun _ _ => 1) m x e Y ↔ m ≤ x + min Y (e - 1) := by
  rw [trans_uno_es_cubo, cubo_es_region]

/-- **Los bits de estado del barrido**: `k + 1`, o `0` si `k = 0` (un estado que devuelve la cita). -/
def estadoBarrido (k : ℕ) : ℕ := if k = 0 then 0 else k + 1

/-- **El costo del barrido en la frontera**: un programa a medias de `m − k` bits paga `2^k − 1` pasos, cada uno a
`c(m − k, S_k)`. -/
def costoFrontera (c : CostoPaso) (m k : ℕ) : ℕ := (2 ^ k - 1) * c (m - k) (estadoBarrido k)

/-- **El barrido con su costo cobrado alcanza su punto**: cita de `m − k` bits, `2^k − 1` consultas, `S_k` bits de
estado y costo de ejecución `costoFrontera c m k`. Es la construcción de `punto_cubo` con el costo a la vista. -/
theorem punto_trans (c : CostoPaso) {m k : ℕ} (hk : k ≤ m) :
    AlcanzableTrans c m (m - k) (estadoBarrido k) (Nat.clog 2 (costoFrontera c m k + 1)) := by
  have hcard : Fintype.card (Fin (2 ^ m)) = Fintype.card (Fin (2 ^ (m - k)) × Fin (2 ^ k - 1 + 1)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_add, Nat.sub_add_cancel hk]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨Unit, Fin (2 ^ (m - k)), Fin (2 ^ k - 1 + 1) ⊕ Fin (2 ^ k - 1), inferInstance, inferInstance,
    inferInstance, fun _ c => mapearA e (barridoA (m - k) (2 ^ k - 1) c), 0, m - k,
    estadoBarrido k, 2 ^ k - 1, by simp, by simp, ?_, ?_, by omega, le_rfl, ?_⟩
  · rw [card_barridoA, estadoBarrido]
    split_ifs with h0
    · subst h0; simp
    · rw [pow_succ]; have := Nat.one_le_two_pow (n := k); omega
  · intro y
    obtain ⟨p, c, h⟩ := barridoA_resuelve (m - k) (2 ^ k - 1) (e y)
    refine ⟨p, c, ?_⟩
    simp only [siNo]
    rw [show (mapearA e (barridoA (m - k) (2 ^ k - 1) c)).inicio = (barridoA (m - k) (2 ^ k - 1) c).inicio from rfl,
      mapearA_corre, h]
    simp
  · simp [costoEjecucion, costoFrontera]

/-- **Nada mejora al barrido cobrado.** Si `c` es monótona en el estado y `(x, e, Y)` se alcanza, hay `k ≤ m` con
`m − k ≤ x`, `S_k ≤ e` y `⌈log₂(costoFrontera c m k + 1)⌉ ≤ Y`. El `k` es lo que falta de descripción, `m − (L + s)`:
la ley del cubo obliga a `t ≥ 2^k − 1` y a `S ≥ k + 1`, y cada uno de esos pasos se paga a `c(L + s, S)`. -/
theorem trans_sobre_frontera (c : CostoPaso) (hmono : ∀ a S S', S ≤ S' → c a S ≤ c a S') {m x e Y : ℕ}
    (h : AlcanzableTrans c m x e Y) :
    ∃ k ≤ m, m - k ≤ x ∧ estadoBarrido k ≤ e ∧ Nat.clog 2 (costoFrontera c m k + 1) ≤ Y := by
  obtain ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, hP, hC, hσ, hA, hx, he, hY⟩ := h
  have hl := ley_cubo hP hC hσ A hA
  rw [Fintype.card_fin] at hl
  by_cases hm : m ≤ L + s
  · refine ⟨0, Nat.zero_le _, by omega, by simp [estadoBarrido], ?_⟩
    simp [costoFrontera]
  · set k := m - (L + s) with hk
    have hk1 : 1 ≤ k := by omega
    have hsplit : 2 ^ m = 2 ^ (L + s) * 2 ^ k := by rw [← pow_add]; congr 1; omega
    rw [← pow_add, hsplit] at hl
    have hl' : 2 ^ k ≤ min (t + 1) (2 ^ (S - 1)) := Nat.le_of_mul_le_mul_left hl (by positivity)
    have ht : 2 ^ k ≤ t + 1 := hl'.trans (min_le_left _ _)
    have hS : k ≤ S - 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hl'.trans (min_le_right _ _))
    have hest : estadoBarrido k = k + 1 := by simp [estadoBarrido]; omega
    refine ⟨k, by omega, by omega, by rw [hest]; omega, ?_⟩
    refine le_trans (Nat.clog_mono_right 2 (Nat.add_le_add_right ?_ 1)) hY
    simp only [costoFrontera, costoEjecucion, hest]
    rw [show m - k = L + s by omega]
    exact Nat.mul_le_mul (by omega) (hmono _ _ _ (by omega))

/-- **La región con transiciones cobradas, exacta**, para todo costo monótono en el estado: se alcanza `(x, e, Y)` si y
solo si algún barrido a medias (`k ≤ m`) cabe en la descripción, en el espacio y en el costo de ejecución. -/
theorem region_trans (c : CostoPaso) (hmono : ∀ a S S', S ≤ S' → c a S ≤ c a S') (m x e Y : ℕ) :
    AlcanzableTrans c m x e Y ↔
      ∃ k ≤ m, m - k ≤ x ∧ estadoBarrido k ≤ e ∧ Nat.clog 2 (costoFrontera c m k + 1) ≤ Y := by
  refine ⟨trans_sobre_frontera c hmono, fun ⟨k, hk, hx, he, hY⟩ => ?_⟩
  exact trans_cerrado_arriba (punto_trans c hk) hx he hY

/-! ## 4. La forma base, `c = a + S` -/

theorem costoBase_mono : ∀ a S S', S ≤ S' → costoBase a S ≤ costoBase a S' := fun _ _ _ h => by
  simp only [costoBase]; omega

/-- **En la frontera el costo por paso es `m + 1` para todo `k`**: `(m − k) + (k + 1)`. El bit de programa que se
ahorra se paga en estado. El barrido de `m − k` bits paga `(2^k − 1) · (m + 1)`. -/
theorem costo_barrido_base {m k : ℕ} (hk : k ≤ m) : costoFrontera costoBase m k = (2 ^ k - 1) * (m + 1) := by
  simp only [costoFrontera, costoBase, estadoBarrido]
  split_ifs with h0
  · subst h0; simp
  · congr 1; omega

/-- **La región base, exacta**: se alcanza `(x, e, Y)` si y solo si `m ≤ x` (la tabla), o bien `m − x + 1 ≤ e` y
`⌈log₂((2^(m−x) − 1)(m + 1) + 1)⌉ ≤ Y` (el barrido con la descripción que hay). -/
theorem region_base (m x e Y : ℕ) :
    AlcanzableTrans costoBase m x e Y ↔
      m ≤ x ∨ (m - x + 1 ≤ e ∧ Nat.clog 2 ((2 ^ (m - x) - 1) * (m + 1) + 1) ≤ Y) := by
  rw [region_trans costoBase costoBase_mono]
  constructor
  · rintro ⟨k, hk, hx, he, hY⟩
    by_cases hmx : m ≤ x
    · exact Or.inl hmx
    · right
      have hk0 : k ≠ 0 := by rintro rfl; omega
      have hest : estadoBarrido k = k + 1 := by simp [estadoBarrido, hk0]
      refine ⟨by omega, ?_⟩
      rw [costo_barrido_base hk] at hY
      refine le_trans (Nat.clog_mono_right 2 (Nat.add_le_add_right ?_ 1)) hY
      exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1)
  · rintro (h | ⟨he, hY⟩)
    · exact ⟨0, Nat.zero_le _, by omega, by simp [estadoBarrido], by simp [costoFrontera]⟩
    · by_cases hmx : m ≤ x
      · exact ⟨0, Nat.zero_le _, by omega, by simp [estadoBarrido], by simp [costoFrontera]⟩
      · have hk0 : m - x ≠ 0 := by omega
        refine ⟨m - x, by omega, by omega, by simp [estadoBarrido, hk0]; omega, ?_⟩
        rwa [costo_barrido_base (by omega)]

/-- **La ley base en bits**: si `(x, e, Y)` se alcanza con `c = a + S`, entonces `m ≤ x`, o bien
`m ≤ x + (e − 1)` y `m + ⌊log₂(m + 1)⌋ ≤ x + Y`. Es `m ≤ x + min (Y − ⌊log₂ c⌋) (e − 1)` con el costo de la frontera,
`c = m + 1`. -/
theorem ley_base {m x e Y : ℕ} (h : AlcanzableTrans costoBase m x e Y) :
    m ≤ x ∨ (m ≤ x + (e - 1) ∧ m + Nat.log 2 (m + 1) ≤ x + Y) := by
  rcases (region_base m x e Y).1 h with h | ⟨he, hY⟩
  · exact Or.inl h
  · by_cases hmx : m ≤ x
    · exact Or.inl hmx
    · right
      refine ⟨by omega, ?_⟩
      rw [Nat.clog_le_iff_le_pow one_lt_two] at hY
      set k := m - x
      have hk1 : 1 ≤ k := by omega
      have h1 : 2 ^ (k - 1) ≤ 2 ^ k - 1 := by
        have : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ]; congr 1; omega
        have := Nat.one_le_two_pow (n := k - 1)
        omega
      have h2 : 2 ^ Nat.log 2 (m + 1) ≤ m + 1 := Nat.pow_log_le_self 2 (by omega)
      have h3 : 2 ^ (k - 1 + Nat.log 2 (m + 1)) < 2 ^ Y := by
        rw [pow_add]
        exact lt_of_le_of_lt (Nat.mul_le_mul h1 h2) (by omega)
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
      omega

/-! ## 5. El efecto sobre la frontera -/

/-- **La tabla sigue gratis**: con la solución escrita en la descripción (`x = m`, `t = 0`, un estado), el costo de
ejecución es `0` con cualquier costo por paso. -/
theorem tabla_gratis (c : CostoPaso) (m : ℕ) : AlcanzableTrans c m m 0 0 := by
  have := punto_trans c (Nat.zero_le m)
  simpa [costoFrontera, estadoBarrido] using this

/-- **Un programa a medias paga cada paso entero**: con `m − k` bits de descripción (`1 ≤ k ≤ m`), el barrido paga
`(2^k − 1)` pasos a `m + 1` bits cada uno, y ninguna estrategia con esa descripción paga menos. -/
theorem a_medias_paga {m k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ m) :
    AlcanzableTrans costoBase m (m - k) (k + 1) (Nat.clog 2 ((2 ^ k - 1) * (m + 1) + 1)) ∧
      ∀ e Y, AlcanzableTrans costoBase m (m - k) e Y → Nat.clog 2 ((2 ^ k - 1) * (m + 1) + 1) ≤ Y := by
  refine ⟨?_, fun e Y h => ?_⟩
  · have := punto_trans costoBase hk
    rw [costo_barrido_base hk] at this
    simpa [estadoBarrido, show k ≠ 0 by omega] using this
  · rcases (region_base m (m - k) e Y).1 h with h | ⟨-, hY⟩
    · omega
    · rwa [show m - (m - k) = k by omega] at hY

/-- **El punto del cubo ya no basta**: `(m − k, k + 1, k)`, en la frontera del cubo (`contador_en_la_recta`), no se
alcanza con las transiciones cobradas, con ningún espacio, si `1 ≤ k ≤ m`. -/
theorem cubo_no_basta {m k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ m) :
    AlcanzableCubo m (m - k) (k + 1) k ∧ ∀ e, ¬ AlcanzableTrans costoBase m (m - k) e k := by
  refine ⟨contador_en_la_recta hk, fun e h => ?_⟩
  have hY := (a_medias_paga hk1 hk).2 e k h
  rw [Nat.clog_le_iff_le_pow one_lt_two] at hY
  have h1 : 2 ^ k ≤ (2 ^ k - 1) * 2 := by have := Nat.one_le_two_pow (n := k)
                                          have : 2 ≤ 2 ^ k := by
                                            calc 2 = 2 ^ 1 := by norm_num
                                              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
                                          omega
  have h2 : (2 ^ k - 1) * 2 ≤ (2 ^ k - 1) * (m + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **La diagonal se rompe**: con `m ≥ 1`, todo punto con descripción incompleta (`x < m`) paga `x + Y ≥ m + 1`. En el
cubo, en cambio, toda la frontera con espacio de sobra tiene `x + y = m` (`contador_en_la_recta`). -/
theorem diagonal_rota {m x e Y : ℕ} (hm : 1 ≤ m) (hx : x < m) (h : AlcanzableTrans costoBase m x e Y) :
    m + 1 ≤ x + Y := by
  rcases ley_base h with h | ⟨-, h⟩
  · omega
  · have : 1 ≤ Nat.log 2 (m + 1) := Nat.log_pos one_lt_two (by omega)
    omega

/-- **Cobrar el programa cambia cuál estrategia conviene** (`m = 2`). En el cubo, la tabla `(x, y) = (2, 0)` y el
barrido a medias `(1, 1)` empatan en `x + y = 2`. Con las transiciones cobradas, la tabla sigue en `x + Y = 2` y el
barrido a medias ya no baja de `x + Y = 3`: cuesta un paso a `1 + 2 = 3` bits, o sea `Y = ⌈log₂ 4⌉ = 2`. -/
theorem estrategia_cambia :
    AlcanzableCubo 2 2 0 0 ∧ AlcanzableCubo 2 1 2 1 ∧
      AlcanzableTrans costoBase 2 2 0 0 ∧ AlcanzableTrans costoBase 2 1 2 2 ∧
      ∀ e Y, AlcanzableTrans costoBase 2 1 e Y → 3 ≤ 1 + Y := by
  refine ⟨cara_tabla le_rfl, by rw [cubo_es_region]; norm_num, tabla_gratis _ _, ?_,
    fun e Y h => diagonal_rota (by norm_num) (by norm_num) h⟩
  rw [region_base]
  right
  refine ⟨by norm_num, ?_⟩
  rw [Nat.clog_le_iff_le_pow one_lt_two]
  norm_num

/-! ## 6. Controles -/

/-- **El barrido de `barridoA` con su costo cobrado**: con cita de `j` bits y `n` consultas resuelve los
`2^j · (n + 1)` candidatos con `2n + 1` estados, y paga `n · (j + ⌈log₂(2n + 1)⌉)` de ejecución. -/
theorem barridoA_cobrado (j n : ℕ) :
    ResuelveA (P := Unit) (C := Fin (2 ^ j)) igual (fun _ c => barridoA j n c) n ∧
      Fintype.card (Fin (n + 1) ⊕ Fin n) = 2 * n + 1 ∧
      costoEjecucion costoBase (0 + j) (Nat.clog 2 (2 * n + 1)) n = n * (j + Nat.clog 2 (2 * n + 1)) :=
  ⟨barridoA_resuelve j n, card_barridoA n, by simp [costoEjecucion, costoBase]⟩

/-- **La ley vieja aplicada a `T` es una cota válida**: si todo paso cuesta al menos `1`, `T ≥ t`, y lo que se alcanza
con transiciones cobradas cumple `m ≤ x + min Y (e − 1)`. Lo que no es, es la frontera (`mutante_ley_vieja`). -/
theorem ley_vieja_vale (c : CostoPaso) (hc : ∀ a S, 1 ≤ c a S) {m x e Y : ℕ} (h : AlcanzableTrans c m x e Y) :
    m ≤ x + min Y (e - 1) := by
  obtain ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, hP, hC, hσ, hA, hx, he, hY⟩ := h
  have hc' : AlcanzableCubo m x e Y := by
    refine ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, hP, hC, hσ, hA, hx, he, le_trans ?_ hY⟩
    exact Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.le_mul_of_pos_right t (hc _ _)) 1)
  exact (cubo_es_region m x e Y).1 hc'

/-! ## 7. Mutantes -/

/-- **Mutante 1, cobrar solo el estado** (`c = S`): el programa vuelve a ser gratis durante la ejecución (un bit más de
descripción no encarece nada) y la región cambia: `(3, 2, 2)` con `m = 4` se alcanza cobrando solo `S` (un paso a `2`
bits) y no con la forma base (un paso a `5` bits). -/
theorem mutante_solo_estado :
    ¬ (∀ a S t : ℕ, 1 ≤ t → costoEjecucion (fun _ S => S) a S t < costoEjecucion (fun _ S => S) (a + 1) S t) ∧
      AlcanzableTrans (fun _ S => S) 4 3 2 2 ∧ ¬ AlcanzableTrans costoBase 4 3 2 2 := by
  refine ⟨fun h => by have := h 0 0 1 le_rfl; simp [costoEjecucion] at this, ?_, ?_⟩
  · rw [region_trans _ (fun _ _ _ h => h)]
    refine ⟨1, by norm_num, by norm_num, by simp [estadoBarrido], ?_⟩
    rw [Nat.clog_le_iff_le_pow one_lt_two]
    simp [costoFrontera, estadoBarrido]
  · rw [region_base, Nat.clog_le_iff_le_pow one_lt_two]
    norm_num

/-- **Mutante 2, no cobrar nada** (`c = 0`): el tiempo desaparece del cubo. `(x, e, Y) = (0, 2, 0)` se alcanza con
`m = 1`, y la ley del cubo en `Y` (`m ≤ x + min Y (e − 1)`) pediría `1 ≤ 0`. -/
theorem mutante_gratis :
    AlcanzableTrans (fun _ _ => 0) 1 0 2 0 ∧ ¬ (1 ≤ 0 + min 0 (2 - 1)) := by
  refine ⟨?_, by norm_num⟩
  rw [region_trans _ (fun _ _ _ _ => le_rfl)]
  exact ⟨1, le_rfl, by norm_num, by simp [estadoBarrido], by simp [costoFrontera]⟩

/-- **Mutante 3, un costo que decrece con la descripción** (`c = S + 10 − a`): un programa más largo **abarata** los
pasos, y `programa_encarece` es falso. -/
theorem mutante_decrece :
    ¬ ∀ a S t : ℕ, 1 ≤ t →
      costoEjecucion (fun a S => S + 10 - a) a S t < costoEjecucion (fun a S => S + 10 - a) (a + 1) S t := by
  intro h
  have := h 0 0 1 le_rfl
  simp [costoEjecucion] at this

/-- **Mutante 4, la ley vieja aplicada a `T` sin el término de `c`, como frontera**: `m ≤ x + min Y (e − 1)` es cota
válida (`ley_vieja_vale`) pero no alcanza: `(0, 2, 1)` con `m = 1` la cumple y no se alcanza (el paso cuesta `2` bits,
`Y = ⌈log₂ 3⌉ = 2`). -/
theorem mutante_ley_vieja :
    ¬ ∀ m x e Y : ℕ, m ≤ x + min Y (e - 1) → AlcanzableTrans costoBase m x e Y := fun h => by
  have := h 1 0 2 1 (by norm_num)
  rw [region_base, Nat.clog_le_iff_le_pow one_lt_two] at this
  norm_num at this

end Sagitta.Map.Tiempo.CuboTransiciones
