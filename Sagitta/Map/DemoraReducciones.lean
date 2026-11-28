import Sagitta.Map.DemoraEfectiva
import Sagitta.Map.LandauDenso
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
# La demora y las reducciones: el umbral logarítmico es robusto, el lineal no

Sigue a `DemoraEfectiva.lean` (los detectores `SanoN`/`DemoraN` con horizonte `N`). La pregunta es qué umbral de
demora **sobrevive a una reducción polinomial**: si una instancia de tamaño `n` se lleva a una de tamaño
`N ≤ C·(n+1)^c`, ¿qué le pasa a una cota de demora expresada en función de `N` cuando se la mira en función de `n`?

## Lo que se prueba

1. **Aritmética del umbral.**
   * `log_poli`: `log₂ (C·(n+1)^c) ≤ c · log₂ n + (log₂ C + c)`. Es `log(poli n) = O(log n)`.
   * `umbral_log`: si `N n ≤ C·(n+1)^c` y `d M ≤ a · log₂ M + b` para todo `M`, entonces
     `d (N n) ≤ (a·c) · log₂ n + (a·(log₂ C + c) + b)`. El umbral `O(log)` **sobrevive** al cambio de escala.
   * `sqrt_o_id`: `Nat.sqrt ∈ o id` (con la `o` de `LandauDenso.lean`: para todo `c`, desde algún punto
     `c · √n ≤ n`), y `sqrt_cuadrado_no_o`: `(fun n => √(n²)) ∉ o id`. Juntos (`umbral_lineal_fragil`): con el
     cambio de escala `N n = n²`, una demora `d = √·` es `o(N)` pero `d (N n) = n` **no** es `o(n)`. Es aritmética
     de reescalar, sin reducción: el umbral `o(lineal)` no sobrevive a un cambio de tamaño **superlineal**.
2. **Reducción con testigos entre árboles, nivel a nivel** (`Reduccion`). Lleva el árbol de `sol₁` con `N₁` niveles
   al de `sol₂` con `N₂ = m · N₁` niveles mediante un mapa de prefijos `τ` que:
   * multiplica el largo por `m` (`largo`): cada elección del origen se traduce en exactamente `m` del destino;
   * es monótono (`prefijo`): `τ (p ++ q)` extiende a `τ p`;
   * preserva `Vivo` en las dos direcciones (`vivo`, `muerto`): prefijo vivo ↦ prefijo vivo, muerto ↦ muerto.
   El detector del origen es el del destino compuesto con `τ` (`tirar`).
   * `transporte_sano`: si `det₂` es `SanoN` para el destino, `tirar det₂ τ` es `SanoN` para el origen.
   * `transporte_demora`: si `det₂` tiene `DemoraN d₂` y `d₂ ≤ m · d₁`, `tirar det₂ τ` tiene `DemoraN d₁`.
     En particular demora `d₂ / m + 1` (`transporte_demora_div`) y, con `m ≥ 1`, demora `d₂` (`transporte_demora_igual`):
     **la demora del origen está acotada por la del destino**, medida en niveles del origen.
   * `transporte_efectiva`: la cuenta que se aplicaría si el costo por llamada del detector transportado fuera
     `t₂ + tτ` (el detector del destino más el mapa): `demoraEfectiva d₁ (t₂ + tτ) ≤ demoraEfectiva d₂ t₂ + log₂ tτ + 1`.
     Es aritmética sobre números; no menciona `tirar` ni `Reduccion`.
   * `transporte_familia`: juntando 1 y 2, una familia de reducciones con `N₂ n ≤ C·(n+1)^c` y un destino con demora
     `≤ a · log₂ N₂ + b` da detectores sanos para el origen con demora `≤ a' · log₂ n + b'`.
   * Una instancia no trivial (`reduccionDup`): duplicar cada variable (`dup`, `m = 2`), con
     `solDup sol y = esDoble y && sol (mitad y)`.

## Por qué el umbral logarítmico es robusto y el lineal frágil

Una reducción polinomial cambia la escala del tamaño: `N = poli(n)`. Un logaritmo se traga ese cambio,
`log(poli n) = c · log n + O(1)`, así que «demora `O(log N)`» en el destino es «demora `O(log n)`» en el origen
(`umbral_log`), y `2^(demora)` sigue siendo polinomial: es el régimen de `busqueda_polinomial` de `DemoraEfectiva`.
Una cota sublineal no se traga un cambio superlineal: `o(N)` con `N = n²` puede ser `n`, que no es `o(n)`
(`umbral_lineal_fragil`).

**Ojo con el alcance.** Las reducciones de este archivo (`Reduccion`) son lineales: `N₂ = m · N₁` con `m` fijo. Con
ellas, `o(N)` **sí** se transporta: `transporte_demora_div` da demora `d₂ / m + 1` en el origen, y si `d₂ ∈ o(N₂)`
eso es `o(N₁)`. La fragilidad aparece solo con reducciones que agrandan el tamaño de forma superlineal, que este
archivo no modela. Lo que sigue es motivación informal, no formalizada: por eso las hipótesis de tiempo `2^{o(n)}`
(la ETH de Impagliazzo–Paturi) piden reducciones que preserven el tamaño linealmente, y la ETH necesita el lema de
esparcimiento (Impagliazzo–Paturi–Zane). Para la frontera logarítmica basta `umbral_log`.

**Sobre la ETH** (informal). En octubre de 2026 Anthropic publicó un algoritmo determinista para 3-SAT en
`2^{O(n log log n/√log n)}` pasos, con prueba en Lean (`anthropics/formal-math`, carpeta `eth`; sin revisión de pares).
Si se confirma, cae la frontera lineal. La logarítmica no depende de ella: la de este archivo (`umbral_log`) sobrevive
a todo cambio de tamaño polinomial.

## Lo que NO se prueba, y lo que es trivial

* La aritmética (1) es elemental: `log_poli` es la cuenta `C·(n+1)^c < 2^(log C + 1) · 2^(c·(log n + 1))`.
* El transporte (2) es casi por construcción: si `τ` preserva `Vivo` en las dos direcciones, el detector compuesto
  hereda la sanidad, y la demora se transporta porque toda extensión de un muerto está muerta (`muerto_ext`). La
  hipótesis fuerte es la de la estructura (`vivo`/`muerto` para **todo** prefijo), no el teorema.
* **Qué queda afuera de la versión general.** Las reducciones de Levin (`LevinReduction` de cslib-frontier) llevan
  instancias y testigos completos, no prefijos: no dicen nada de prefijos parciales, y la mayoría de las reducciones
  reales (Cook–Levin, las de gadgets) **no** preservan `Vivo` prefijo a prefijo: un prefijo del origen no siempre
  determina un prefijo del destino, y las variables auxiliares del destino se fijan en otro orden. Aquí solo está el
  caso «nivel a nivel» con `m` fijo y `N₂ = m · N₁` exacto, sin variables auxiliares sueltas al final ni orden
  distinto. No hay puente con `LevinReduction` ni con `ComputableInPolyTime`.
* `tτ` es un número que se le asigna al mapa, no un tiempo medido; contar nodos o llamadas no es tiempo de máquina de
  Turing (como en `ArbolElecciones` y `DemoraEfectiva`).
* Nada de esto separa clases de complejidad: dice qué umbrales de demora son invariantes, no que alguno se cumpla.
-/

namespace Sagitta.Map
namespace Tiempo

/-! ## 1. Aritmética del umbral -/

/-- **`log(poli n) = O(log n)`**: `log₂ (C·(n+1)^c) ≤ c · log₂ n + (log₂ C + c)`. -/
theorem log_poli (C c n : ℕ) : Nat.log 2 (C * (n + 1) ^ c) ≤ c * Nat.log 2 n + (Nat.log 2 C + c) := by
  by_cases h0 : C * (n + 1) ^ c = 0
  · rw [h0]; simp
  have hn : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hC : C < 2 ^ (Nat.log 2 C + 1) := Nat.lt_pow_succ_log_self (by norm_num) C
  have hpos : 0 < (n + 1) ^ c := by positivity
  have h : C * (n + 1) ^ c < 2 ^ (c * Nat.log 2 n + (Nat.log 2 C + c) + 1) :=
    calc C * (n + 1) ^ c < 2 ^ (Nat.log 2 C + 1) * (n + 1) ^ c := Nat.mul_lt_mul_of_pos_right hC hpos
      _ ≤ 2 ^ (Nat.log 2 C + 1) * (2 ^ (Nat.log 2 n + 1)) ^ c :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn c)
      _ = 2 ^ (c * Nat.log 2 n + (Nat.log 2 C + c) + 1) := by
          rw [← pow_mul, ← pow_add]; congr 1; ring
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow h0 h)

/-- **El umbral logarítmico sobrevive a un cambio polinomial de escala.** -/
theorem umbral_log {N d : ℕ → ℕ} {C c a b : ℕ} (hN : ∀ n, N n ≤ C * (n + 1) ^ c)
    (hd : ∀ M, d M ≤ a * Nat.log 2 M + b) (n : ℕ) :
    d (N n) ≤ (a * c) * Nat.log 2 n + (a * (Nat.log 2 C + c) + b) := by
  have h1 : Nat.log 2 (N n) ≤ c * Nat.log 2 n + (Nat.log 2 C + c) :=
    (Nat.log_mono_right (hN n)).trans (log_poli C c n)
  calc d (N n) ≤ a * Nat.log 2 (N n) + b := hd _
    _ ≤ a * (c * Nat.log 2 n + (Nat.log 2 C + c)) + b := by
        have := Nat.mul_le_mul_left a h1; omega
    _ = (a * c) * Nat.log 2 n + (a * (Nat.log 2 C + c) + b) := by ring

/-- **`√n` es `o(n)`.** -/
theorem sqrt_o_id : Nat.sqrt ∈ o (fun n => n) := fun c => by
  refine ⟨c * c, fun n hn => ?_⟩
  have h1 : c ≤ Nat.sqrt n := Nat.le_sqrt.mpr hn
  calc c * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul_right _ h1
    _ ≤ n := Nat.sqrt_le n

/-- **Pero `√(n²) = n` no es `o(n)`.** -/
theorem sqrt_cuadrado_no_o : (fun n => Nat.sqrt (n ^ 2)) ∉ o (fun n => n) := by
  intro h
  obtain ⟨N, hN⟩ := h 2
  have := hN (N + 1) (by omega)
  simp only [Nat.sqrt_eq'] at this
  omega

/-- **El umbral sublineal es frágil ante un cambio superlineal**: con `N n = n²` (que cumple `N n ≤ 1·(n+1)^2`), la demora
`d = √·` es `o(N)` como función de `N`, pero `d (N n)` no es `o(n)`. Contrastar con `umbral_log`. Con las reducciones lineales de `Reduccion`, en cambio, `o(N)` se transporta. -/
theorem umbral_lineal_fragil :
    (∀ n, n ^ 2 ≤ 1 * (n + 1) ^ 2) ∧ Nat.sqrt ∈ o (fun n => n) ∧
      (fun n => Nat.sqrt ((fun m => m ^ 2) n)) ∉ o (fun n => n) :=
  ⟨fun n => by rw [one_mul]; exact Nat.pow_le_pow_left (by omega) 2, sqrt_o_id, sqrt_cuadrado_no_o⟩

/-! ## 2. Reducciones nivel a nivel -/

/-- **Reducción nivel a nivel** del árbol de `sol₁` (`N₁` niveles) al de `sol₂` (`N₂` niveles): cada elección del
origen se traduce en `m` elecciones del destino, y el mapa de prefijos preserva `Vivo` en las dos direcciones. -/
structure Reduccion (sol₁ sol₂ : List Bool → Bool) (N₁ N₂ m : ℕ) where
  τ : List Bool → List Bool
  largo : ∀ p, (τ p).length = m * p.length
  horizonte : N₂ = m * N₁
  prefijo : ∀ p q, ∃ r, τ (p ++ q) = τ p ++ r
  vivo : ∀ p, p.length ≤ N₁ → Vivo sol₁ (N₁ - p.length) p → Vivo sol₂ (N₂ - (τ p).length) (τ p)
  muerto : ∀ p, p.length ≤ N₁ → ¬ Vivo sol₁ (N₁ - p.length) p → ¬ Vivo sol₂ (N₂ - (τ p).length) (τ p)

/-- El detector del origen: el del destino, aplicado a la imagen del prefijo. -/
def tirar (det₂ : List Bool → Bool) (τ : List Bool → List Bool) : List Bool → Bool := fun p => det₂ (τ p)

variable {sol₁ sol₂ det₂ : List Bool → Bool} {N₁ N₂ m : ℕ}

/-- **La sanidad se transporta.** -/
theorem transporte_sano (R : Reduccion sol₁ sol₂ N₁ N₂ m) (hs : SanoN sol₂ det₂ N₂) :
    SanoN sol₁ (tirar det₂ R.τ) N₁ := by
  intro p hp hd hv
  have hl : (R.τ p).length ≤ N₂ := by
    rw [R.largo, R.horizonte]; exact Nat.mul_le_mul_left m hp
  exact hs (R.τ p) hl hd (R.vivo p hp hv)

/-- **La demora se transporta**: `d₂` niveles del destino caben en `d₁` del origen si `d₂ ≤ m · d₁`. -/
theorem transporte_demora (R : Reduccion sol₁ sol₂ N₁ N₂ m) {d₂ : ℕ} (hd : DemoraN sol₂ det₂ N₂ d₂) {d₁ : ℕ}
    (hdd : d₂ ≤ m * d₁) : DemoraN sol₁ (tirar det₂ R.τ) N₁ d₁ := by
  intro p hpl hm q hq
  obtain ⟨r, hr⟩ := R.prefijo p q
  have hlen : (R.τ p).length + r.length = m * p.length + m * d₁ := by
    have := congrArg List.length hr
    rw [List.length_append, R.largo, R.largo, List.length_append, hq, mul_add] at this
    rw [R.largo]; omega
  have hτp := R.largo p
  have hfit : m * p.length + m * d₁ ≤ N₂ := by
    rw [R.horizonte, ← mul_add]; exact Nat.mul_le_mul_left m hpl
  have hm₂ := R.muerto p (by omega) hm
  set e := m * d₁ - d₂ with he
  have h1 : (r.take e).length = e := by simp; omega
  have h2 : (r.drop e).length = d₂ := by simp; omega
  have hm' := muerto_ext (q := r.take e) hm₂ (by omega)
  have := hd (R.τ p ++ r.take e) (by simp; omega) hm' (r.drop e) h2
  show det₂ (R.τ (p ++ q)) = true
  rw [hr]; simpa using this

/-- Demora `d₂ / m + 1` en niveles del origen. -/
theorem transporte_demora_div (R : Reduccion sol₁ sol₂ N₁ N₂ m) (hm : 0 < m) {d₂ : ℕ}
    (hd : DemoraN sol₂ det₂ N₂ d₂) : DemoraN sol₁ (tirar det₂ R.τ) N₁ (d₂ / m + 1) :=
  transporte_demora R hd (Nat.lt_mul_div_succ d₂ hm).le

/-- **Con `m ≥ 1`, la demora del origen no pasa de la del destino.** -/
theorem transporte_demora_igual (R : Reduccion sol₁ sol₂ N₁ N₂ m) (hm : 1 ≤ m) {d₂ : ℕ}
    (hd : DemoraN sol₂ det₂ N₂ d₂) : DemoraN sol₁ (tirar det₂ R.τ) N₁ d₂ :=
  transporte_demora R hd (Nat.le_mul_of_pos_left d₂ hm)

/-- **La demora efectiva del detector transportado**: con demora `d₁ ≤ d₂` y costo por llamada `t₂ + tτ` (el
detector del destino más el mapa), `demoraEfectiva d₁ (t₂ + tτ) ≤ demoraEfectiva d₂ t₂ + log₂ tτ + 1`. -/
theorem transporte_efectiva {d₁ d₂ t₂ tτ : ℕ} (h : d₁ ≤ d₂) (hτ : tτ ≠ 0) :
    demoraEfectiva d₁ (t₂ + tτ) ≤ demoraEfectiva d₂ t₂ + Nat.log 2 tτ + 1 := by
  unfold demoraEfectiva
  have hmax : t₂ + tτ ≤ 2 * max t₂ tτ := by omega
  have hlog : Nat.log 2 (t₂ + tτ) ≤ Nat.log 2 (max t₂ tτ) + 1 := by
    calc Nat.log 2 (t₂ + tτ) ≤ Nat.log 2 (max t₂ tτ * 2) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 (max t₂ tτ) + 1 := Nat.log_mul_base (by norm_num) (by omega)
  have hm : Nat.log 2 (max t₂ tτ) ≤ Nat.log 2 t₂ + Nat.log 2 tτ := by
    rcases le_total t₂ tτ with h' | h'
    · rw [max_eq_right h']; omega
    · rw [max_eq_left h']; omega
  omega

/-- **El umbral logarítmico atraviesa una familia de reducciones.** Si para cada `n` hay una reducción nivel a nivel
con `m n ≥ 1` y `N₂ n ≤ C·(n+1)^c`, y el destino tiene detectores sanos con demora `d₂ (N₂ n)`, donde
`d₂ M ≤ a · log₂ M + b`, entonces el origen tiene detectores sanos con demora `≤ a' · log₂ n + b'`. -/
theorem transporte_familia (sol₁ sol₂ det₂ : ℕ → List Bool → Bool) (N₁ N₂ m d₂ : ℕ → ℕ)
    (R : ∀ n, Reduccion (sol₁ n) (sol₂ n) (N₁ n) (N₂ n) (m n)) (hm : ∀ n, 1 ≤ m n)
    (hs : ∀ n, SanoN (sol₂ n) (det₂ n) (N₂ n)) (hd : ∀ n, DemoraN (sol₂ n) (det₂ n) (N₂ n) (d₂ (N₂ n)))
    {C c a b : ℕ} (hN : ∀ n, N₂ n ≤ C * (n + 1) ^ c) (hlog : ∀ M, d₂ M ≤ a * Nat.log 2 M + b) :
    ∃ a' b' : ℕ, ∀ n, SanoN (sol₁ n) (tirar (det₂ n) (R n).τ) (N₁ n) ∧
      ∃ d₁, d₁ ≤ a' * Nat.log 2 n + b' ∧ DemoraN (sol₁ n) (tirar (det₂ n) (R n).τ) (N₁ n) d₁ :=
  ⟨a * c, a * (Nat.log 2 C + c) + b, fun n =>
    ⟨transporte_sano (R n) (hs n), d₂ (N₂ n), umbral_log hN hlog n,
      transporte_demora_igual (R n) (hm n) (hd n)⟩⟩

/-! ## Una instancia: duplicar cada variable -/

/-- Duplica cada elección: `[a, b] ↦ [a, a, b, b]`. -/
def dup : List Bool → List Bool
  | [] => []
  | b :: l => b :: b :: dup l

/-- Toma una de cada dos: `[a, a', b, b'] ↦ [a, b]`. -/
def mitad : List Bool → List Bool
  | a :: _ :: l => a :: mitad l
  | _ => []

/-- ¿Vienen las elecciones por pares iguales? -/
def esDoble : List Bool → Bool
  | [] => true
  | [_] => false
  | a :: b :: l => (a == b) && esDoble l

/-- El destino: pares iguales, y la mitad es solución del origen. -/
def solDup (sol : List Bool → Bool) (y : List Bool) : Bool := esDoble y && sol (mitad y)

theorem dup_append : ∀ p q : List Bool, dup (p ++ q) = dup p ++ dup q
  | [], _ => rfl
  | b :: l, q => by simp [dup, dup_append l q]

theorem length_dup : ∀ p : List Bool, (dup p).length = 2 * p.length
  | [] => rfl
  | b :: l => by simp [dup, length_dup l]; ring

theorem esDoble_dup_append : ∀ p r : List Bool, esDoble (dup p ++ r) = esDoble r
  | [], _ => rfl
  | b :: l, r => by simp [dup, esDoble, esDoble_dup_append l r]

theorem mitad_dup_append : ∀ p r : List Bool, mitad (dup p ++ r) = p ++ mitad r
  | [], _ => rfl
  | b :: l, r => by simp [dup, mitad, mitad_dup_append l r]

theorem dup_mitad : ∀ r : List Bool, esDoble r = true → dup (mitad r) = r
  | [], _ => rfl
  | [_], h => by simp [esDoble] at h
  | a :: b :: l, h => by
    simp only [esDoble, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp [mitad, dup, dup_mitad l h]

/-- **Duplicar es una reducción nivel a nivel con `m = 2`.** -/
def reduccionDup (sol : List Bool → Bool) (N : ℕ) : Reduccion sol (solDup sol) N (2 * N) 2 where
  τ := dup
  largo := length_dup
  horizonte := rfl
  prefijo p q := ⟨dup q, dup_append p q⟩
  vivo p hp := by
    rintro ⟨q, hq, hs⟩
    refine ⟨dup q, ?_, ?_⟩
    · rw [length_dup, length_dup]; omega
    · have h1 := esDoble_dup_append (p ++ q) []
      have h2 := mitad_dup_append (p ++ q) []
      simp only [List.append_nil, esDoble, mitad] at h1 h2
      rw [← dup_append, solDup, h1, h2, hs]; rfl
  muerto p hp := by
    rintro hm ⟨r, hr, hs⟩
    simp only [solDup, esDoble_dup_append, mitad_dup_append, Bool.and_eq_true] at hs
    obtain ⟨hd, hs⟩ := hs
    have hlr := congrArg List.length (dup_mitad r hd)
    simp only [length_dup] at hr hlr
    exact hm ⟨mitad r, by omega, hs⟩

/-- Corolario concreto: un detector sano con demora `d₂` para el árbol duplicado da uno sano con demora
`d₂ / 2 + 1` para el original. -/
theorem dup_transporte {sol det₂ : List Bool → Bool} {N d₂ : ℕ} (hs : SanoN (solDup sol) det₂ (2 * N))
    (hd : DemoraN (solDup sol) det₂ (2 * N) d₂) :
    SanoN sol (tirar det₂ dup) N ∧ DemoraN sol (tirar det₂ dup) N (d₂ / 2 + 1) :=
  ⟨transporte_sano (reduccionDup sol N) hs, transporte_demora_div (reduccionDup sol N) (by norm_num) hd⟩

/-! ## Controles -/

example : dup [true, false] = [true, true, false, false] ∧ mitad [true, true, false, false] = [true, false] ∧
    esDoble [true, true, false, false] = true ∧ esDoble [true, false] = false := by decide

/-- `solDup` no es trivial: acepta la duplicada de una solución y rechaza una lista no duplicada con la misma mitad. -/
example : solDup (solCNF todoTrue4) (dup [true, true, true, true]) = true ∧
    solDup (solCNF todoTrue4) [true, false, true, true, true, true, true, true] = false := by decide

/-- El detector del destino (`detCNF` sobre la mitad) tirado por `dup` da los mismos nodos que `detCNF` en el origen:
9 con `todoTrue4`, 31 sin solución en el último nivel. (Tirado por `dup`, este detector es `detCNF` por construcción;
el control compara los dos números, no dice nada más.) -/
example : nodos (solCNF todoTrue4) (tirar (fun y => detCNF todoTrue4 (mitad y)) dup) 4 [] = 9 ∧
    nodos (solCNF todoTrue4) (detCNF todoTrue4) 4 [] = 9 ∧
    nodos (solCNF tarde4) (tirar (fun y => detCNF tarde4 (mitad y)) dup) 4 [] = 31 ∧
    nodos (solCNF tarde4) (detCNF tarde4) 4 [] = 31 := by decide

/-- La aritmética: `log₂ (3·(n+1)^2)` en `n = 15` es `9`, y la cota de `log_poli` da `2·3 + (1 + 2) = 9`. -/
example : Nat.log 2 (3 * (15 + 1) ^ 2) = 9 ∧ 2 * Nat.log 2 15 + (Nat.log 2 3 + 2) = 9 := by decide

/-- `√(n²) = n` en concreto, mientras `√` de un cuadrado grande es pequeño frente a él. -/
example : Nat.sqrt (100 ^ 2) = 100 ∧ 10 * Nat.sqrt (10 ^ 2) ≤ 10 ^ 2 :=
  ⟨Nat.sqrt_eq' 100, by rw [Nat.sqrt_eq']; norm_num⟩

/-
Mutantes probados fuera del repositorio (cada uno es una copia de este archivo con un solo cambio; todos fallan):
* `r1_demora_al_reves`: `transporte_demora` con `m · d₁ ≤ d₂` en vez de `d₂ ≤ m · d₁`: falla (no caben los `d₂`
  niveles del destino).
* `r2_div_sin_mas1`: `transporte_demora_div` con demora `d₂ / m` (sin `+ 1`): falla; con `d₂ = 1`, `m = 2` pediría
  demora 0 en el origen.
* `r3_log_poli_sin_c`: `log_poli` sin el `+ c` (`c · log₂ n + log₂ C`): falla (es falso en `C = n = c = 1`).
* `r4_sqrt_no_o`: afirmar `(fun n => 2 · √n) ∉ o id`: la prueba de `sqrt_o_id` falla.
* `r5_control9`: el control de `dup` con `= 8` en vez de `= 9`: falla con `decide`.
* `r6_horizonte_mas1`: `reduccionDup` con horizonte `2·N + 1`: fallan `horizonte` y `vivo`.
* `r7_efectiva_sin1`: `transporte_efectiva` sin el `+ 1`: falla.
-/

end Tiempo
end Sagitta.Map
