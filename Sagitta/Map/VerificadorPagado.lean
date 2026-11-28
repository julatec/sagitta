import Sagitta.Map.UniversoCerrado

/-!
# El universo cerrado con el verificador pagado

`UniversoCerrado.lean` probó la frontera con Blum (`frontera`, `con_verificador_hay_minimo`): con el verificador de
una función `f` como caja, el costo cerrado tiene mínimo (Levin), mientras que `f` misma no tiene programa óptimo
(`sin_optimo`). El revisor y el autor notaron por qué: **el verificador calcula `f` gratis**. Evaluar `V` no se cobra.
Es la ley de José leída desde otro lado: si un lugar es gratis, el trabajo se esconde ahí. Este archivo cobra ese lugar.

## La definición

* `UniversoPagado`: el verificador ya no es una función `ℕ → ℕ → Bool` sino **un programa** `v` (un `Code` de Mathlib)
  y la entrada `x`. Verificar `y` es correr `v` sobre `⟨x, y⟩` (`Nat.pair`); **acepta si entrega `0`**.
* `ProcesoPagado`: el resolvedor `i`, su presupuesto `k` y el presupuesto `K` del verificador sobre lo que entrega.
  Es correcto si el resolvedor entrega un `y` y el verificador, con `K`, lo acepta.
* **La medida, una sola para todo**: el presupuesto de `evaln`. Es la de `correr` (el `k` del resolvedor), la de
  `pasos`/`costo` de `AceleracionBlum.lean` (el **menor** presupuesto que alcanza) y la de las rondas de `Levin.lean`
  (una suma de presupuestos). Se eligió esta porque así el resolvedor, el verificador y la búsqueda se miden con la
  misma vara, y desaparece el «rondas contra pasos» que dejaba la frontera de `UniversoCerrado.lean` como contraste y
  no como contradicción.
* `costoPagado = 2^i · (k + K)`: escribir el resolvedor, correrlo y **verificar lo que entrega**. El factor `2^i` también
  multiplica a `K` porque en la búsqueda universal el verificador de las respuestas del programa `i` corre dentro de la
  fracción `2^(-i)` del esfuerzo que le toca a ese programa; no hay otro lugar de donde sacar ese tiempo.
* `costoCerradoPagado`: el mínimo de `costoPagado` sobre los procesos correctos.

## Lo que se prueba

1. **La ley sigue valiendo** (`ley_pagada`, `levin_pagado`): la búsqueda de Levin que **paga** cada verificación
   (`buscarPagado`: en la ronda `t`, el programa `i` recibe `2^(t-i)` para correr y otro tanto para verificar) entrega
   una respuesta aceptada y cuesta menos que `16 · costo cerrado pagado`. Para un problema dado por una función
   (`VerificaA v f`) y cualquier programa `j` de `f`: costo cerrado pagado `≤ 2^j · (t_j + t_V)` y Levin pagado
   `< 16 · 2^j · (t_j + t_V)` (`pagado_en_O`). Es la forma `costo ≲ 2^i · (t_i + t_V)`.
2. **Verificar se paga** (`verificar_bajo_pagado`, `gratis_le_pagado`): el costo cerrado pagado es por lo menos el
   tiempo de una verificación aceptada, `t_V(x) = costo v ⟨x, f x⟩`, y nunca baja del costo cerrado gratis.
3. **Cuándo sobrevive el mínimo** (`sobrevive_iff`): para cualquier escala `g`, el costo cerrado pagado está en
   `O(t_j + g)` para **todo** programa `j` de `f` si y solo si el verificador lo está. El mínimo de Levin sobrevive
   exactamente cuando verificar es más barato que todo resolvedor.
4. **El arreglo de la frontera** (`sin_minimo_pagado`, `frontera_pagada`): para la `f` de Blum y para **cada** programa
   `j₀` de `f`, el verificador canónico `verificadorCodigo j₀` (calcula `j₀ x` y lo compara con `y`) verifica `f`, el
   costo cerrado pagado es `≥ costo j₀` en toda entrada, y **no** está en `O(costo j + lectura)` para todo programa `j`
   de `f`: el «mínimo» que daba Levin desaparece. En la misma `f`, con `verificadorDe f` gratis, sí estaba en
   `O(costo j)` para todo `j` (`con_verificador_hay_minimo`). La forma exacta: no hay contradicción entre medidas
   (ahora son la misma); lo que queda es que el mínimo de la frontera venía del verificador gratis, porque pagado, el
   verificador canónico es tan caro como el programa que lleva adentro, y ese programa no tiene óptimo (`sin_optimo`).
   El enunciado general (`sin_minimo_pagado`) vale para todo verificador `v` de `f` que **lleve adentro un programa de
   `f`** (`costo j₀ = O(t_V)`); el canónico lo lleva (`costo_le_verificadorCodigo`).

## Controles

* **El verificador barato** (`control_barato`): «la respuesta es `0`» con el verificador `Code.right` (lee `y` y nada
  más). Ahí `t_V` es exactamente lo que cuesta leer el par, `⟨x, 0⟩ + 1` (`tiempo_right`), y el mínimo **sobrevive**:
  el costo cerrado pagado está en `O(costo j + lectura)` para todo programa `j` de la constante. La cota casi se
  alcanza: `⟨x,0⟩ + 1 ≤ costo pagado ≤ ⟨x,0⟩ + x + 2` (`control_barato_ajustado`).
* **Leer el par cuesta** (`leer_el_par_cuesta`): aun en ese problema trivial, el costo pagado **no** está en
  `O(costo Code.zero)`: en esta medida el presupuesto acota el **valor** de la entrada (`evaln_bound`), y
  `⟨x, y⟩ ≥ x²`. Por eso la escala honesta es `t_j + lectura` y no `t_j` sola.
* **Lo gratis esconde** (`gratis_esconde`): en ese mismo problema, el costo cerrado **gratis** queda por debajo del
  costo de **una sola** verificación: el modelo gratis no la estaba contando.
* **El caso de Blum** (`frontera_pagada`): ahí el mínimo no sobrevive.

## La lectura en el proyecto

Las tres memorias de José: el **resolvedor** (lo que se escribe), la **cita** (el presupuesto que se le da) y el
**verificador** (la definición del problema), comunicadas por el tiempo. En `UniversoCerrado.lean` el verificador
era la única memoria que no pagaba: se consultaba gratis. Con el verificador gratis, el universo no estaba cerrado del
todo, y la complejidad de la `f` de Blum se escondía en él: el «mínimo» de Levin era el verificador haciendo el trabajo
sin cobrar. Con el verificador pagado el universo queda cerrado de verdad: la complejidad no se esfuma, aparece en
`t_V`, y el mínimo sobrevive solo si verificar es más barato que resolver. **El precio se paga sí o sí; lo abierto es
si una vez o en cada instancia**: escribir el resolvedor (`2^i`) se paga una vez para todas las entradas; verificar
(`t_V`) se paga en cada instancia.

## Lo que NO se prueba

* Que el presupuesto de `evaln` sea tiempo de máquina. Es una medida de Blum (acota a la vez profundidad y el valor
  de la entrada); en particular, leer `⟨x, y⟩` cuesta `x²` aquí, cosa que en una máquina de Turing costaría el largo.
* Una cota superior para `t_V` del verificador canónico (haría falta acotar el costo del código de la igualdad y de
  `pair`/`comp` constructor por constructor); solo se usa la inferior, `costo j₀ ≤ t_V`.
* Que **todo** verificador de la `f` de Blum lleve adentro un programa de `f` con su costo. Para una `f` con valores
  `0` y `1` el verificador decide `f` corriendo sobre `⟨x, 1⟩`, pero el costo pagado solo cobra la verificación
  aceptada `⟨x, f x⟩`, no la rechazada. Queda como hipótesis explícita de `sin_minimo_pagado`.
* Un problema donde verificar sea barato y **todo** resolvedor sea demostradamente caro: en esta medida la única cota
  inferior universal es leer la entrada (`costo_gt`), así que el control barato es uno donde resolver también es
  barato y el mínimo sobrevive en la escala `t_j + lectura`.
* Que el programa de la búsqueda pagada tenga costo de Blum acotado por `costoLevinPagado` (el mismo hueco que
  `levin_es_programa`).
* Nada sobre `P` contra `NP`.

## Fuente, de memoria

L. A. Levin, «Universal sequential search problems», *Problemy Peredachi Informatsii* 9(3), 1973; M. Blum, «A
machine-independent theory of the complexity of recursive functions», *J. ACM* 14(2), 1967. No se leyeron en esta
sesión; las pruebas son propias sobre `Levin.lean`, `AceleracionBlum.lean`, `BlumExiste.lean`, `CorteRacional.lean` y
`UniversoCerrado.lean`.
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map
namespace Tiempo
namespace VerificadorPagado

open Levin AceleracionBlum CorteRacional UniversoCerrado

/-! ## 1. La definición -/

/-- **Un universo con el verificador pagado.** La máquina universal es la misma (`correr`); el verificador ya no es una
caja: es un programa `v` que corre sobre `⟨x, y⟩` y **acepta si entrega `0`**. -/
structure UniversoPagado where
  /-- El verificador, como programa de la máquina universal. -/
  v : Code
  /-- La entrada. -/
  x : ℕ

/-- **Un proceso pagado**: el resolvedor `i` con presupuesto `k`, y el presupuesto `K` con que se corre el verificador
sobre lo que el resolvedor entrega. -/
structure ProcesoPagado where
  /-- El resolvedor, como índice de la máquina universal. -/
  i : ℕ
  /-- El presupuesto del resolvedor. -/
  k : ℕ
  /-- El presupuesto del verificador. -/
  K : ℕ

/-- **El proceso resuelve el universo pagado**: el resolvedor entrega `y` y el verificador, con presupuesto `K`, lo
acepta (entrega `0`). -/
def CorrectoPagado (U : UniversoPagado) (p : ProcesoPagado) : Prop :=
  ∃ y, correr p.i p.k U.x = some y ∧ evaln p.K U.v (Nat.pair U.x y) = some 0

/-- Algún proceso pagado lo resuelve. -/
def ResolublePagado (U : UniversoPagado) : Prop := ∃ p, CorrectoPagado U p

/-- **El costo de un proceso pagado**: `2^i · (k + K)`. Escribir el resolvedor, correrlo y verificar lo que entrega;
el verificador de las respuestas del programa `i` corre dentro de la misma fracción `2^(-i)` del esfuerzo. -/
def ProcesoPagado.costoPagado (p : ProcesoPagado) : ℕ := 2 ^ p.i * (p.k + p.K)

/-- **El costo cerrado pagado**: el mínimo de `2^i · (k + K)` sobre los procesos pagados correctos (`0` si no hay). -/
noncomputable def costoCerradoPagado (U : UniversoPagado) : ℕ :=
  sInf {c | ∃ p, CorrectoPagado U p ∧ c = p.costoPagado}

theorem costoCerradoPagado_le {U : UniversoPagado} {p : ProcesoPagado} (h : CorrectoPagado U p) :
    costoCerradoPagado U ≤ p.costoPagado :=
  Nat.sInf_le ⟨p, h, rfl⟩

theorem costoCerradoPagado_alcanzado {U : UniversoPagado} (h : ResolublePagado U) :
    ∃ p, CorrectoPagado U p ∧ costoCerradoPagado U = p.costoPagado := by
  obtain ⟨p, hp⟩ := h
  have hne : {c | ∃ p, CorrectoPagado U p ∧ c = p.costoPagado}.Nonempty := ⟨_, p, hp, rfl⟩
  obtain ⟨q, hq, he⟩ := Nat.sInf_mem hne
  exact ⟨q, hq, he⟩

/-- **Verificar lee el par**: el presupuesto del verificador supera a `⟨x, y⟩`. -/
theorem CorrectoPagado.par_lt {U : UniversoPagado} {p : ProcesoPagado} (h : CorrectoPagado U p) :
    ∃ y, correr p.i p.k U.x = some y ∧ Nat.pair U.x y < p.K := by
  obtain ⟨y, hy, hV⟩ := h
  exact ⟨y, hy, evaln_bound hV⟩

/-- **La cota inferior pagada.** En un universo pagado resoluble, el costo cerrado pagado es el de un proceso concreto,
no pasa de ningún otro, y supera a la entrada y al par que se verifica. -/
theorem cota_inferior_pagada {U : UniversoPagado} (h : ResolublePagado U) :
    (∃ p, CorrectoPagado U p ∧ costoCerradoPagado U = 2 ^ p.i * (p.k + p.K)) ∧
      (∀ p, CorrectoPagado U p → costoCerradoPagado U ≤ 2 ^ p.i * (p.k + p.K)) ∧
      ∃ y, U.x < costoCerradoPagado U ∧ Nat.pair U.x y < costoCerradoPagado U := by
  obtain ⟨p, hp, he⟩ := costoCerradoPagado_alcanzado h
  refine ⟨⟨p, hp, he⟩, fun q hq => costoCerradoPagado_le hq, ?_⟩
  obtain ⟨y, hy, hK⟩ := hp.par_lt
  have hk : U.x < p.k := evaln_bound hy
  have hle : p.k + p.K ≤ p.costoPagado := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  refine ⟨y, ?_, ?_⟩ <;> rw [he] <;> omega

/-! ## 2. La búsqueda de Levin que paga cada verificación -/

/-- En la ronda `t`, el programa `i` corre con presupuesto `2^(t-i)` y, si entrega `y`, el verificador corre sobre
`⟨x, y⟩` con el **mismo** presupuesto. Se conserva `y` solo si el verificador entrega `0`. -/
def intentoPagado (v : Code) (x t i : ℕ) : Option ℕ :=
  (correr i (2 ^ (t - i)) x).filter fun y => decide (evaln (2 ^ (t - i)) v (Nat.pair x y) = some 0)

/-- La ronda `t`, pagando: los programas `0, …, t`, en orden; la primera respuesta aceptada. -/
def rondaPagada (v : Code) (x t : ℕ) : Option ℕ :=
  (List.range (t + 1)).findSome? (intentoPagado v x t)

/-- La búsqueda pagada hasta la ronda `T`. -/
def buscarPagado (v : Code) (x T : ℕ) : Option ℕ :=
  (List.range (T + 1)).findSome? (rondaPagada v x)

/-- **Corrección**: lo que entrega la búsqueda pagada, el verificador lo acepta con algún presupuesto (y por lo tanto
`0 ∈ eval v ⟨x, y⟩`, `buscarPagado_acepta'`). -/
theorem buscarPagado_acepta {v : Code} {x T y : ℕ} (h : buscarPagado v x T = some y) :
    ∃ K, evaln K v (Nat.pair x y) = some 0 := by
  obtain ⟨t, -, ht⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some ht
  unfold intentoPagado at hi
  obtain ⟨-, hd⟩ := Option.filter_eq_some_iff.1 hi
  exact ⟨_, of_decide_eq_true hd⟩

theorem buscarPagado_acepta' {v : Code} {x T y : ℕ} (h : buscarPagado v x T = some y) :
    0 ∈ eval v (Nat.pair x y) := by
  obtain ⟨K, hK⟩ := buscarPagado_acepta h
  exact evaln_sound hK

/-- **Completitud**: si el proceso pagado `(i, k, K)` resuelve, la búsqueda pagada entrega algo en la ronda
`i + ⌈log₂ (k + K)⌉`. -/
theorem buscarPagado_halla {v : Code} {x i k K y T : ℕ} (h : correr i k x = some y)
    (hV : evaln K v (Nat.pair x y) = some 0) (hT : i + Nat.clog 2 (k + K) ≤ T) :
    ∃ y', buscarPagado v x T = some y' := by
  have hb : k + K ≤ 2 ^ Nat.clog 2 (k + K) := Nat.le_pow_clog one_lt_two _
  have hc : correr i (2 ^ Nat.clog 2 (k + K)) x = some y := correr_mono (by omega) h
  have hv : evaln (2 ^ Nat.clog 2 (k + K)) v (Nat.pair x y) = some 0 := evaln_mono (by omega) hV
  have hint : intentoPagado v x (i + Nat.clog 2 (k + K)) i = some y := by
    unfold intentoPagado
    rw [Nat.add_sub_cancel_left, hc]
    simp [hv]
  have hr : (rondaPagada v x (i + Nat.clog 2 (k + K))).isSome := by
    unfold rondaPagada
    rw [List.findSome?_isSome_iff]
    exact ⟨i, List.mem_range.2 (by omega), by simp [hint]⟩
  have hb' : (buscarPagado v x T).isSome := by
    unfold buscarPagado
    rw [List.findSome?_isSome_iff]
    exact ⟨i + Nat.clog 2 (k + K), List.mem_range.2 (by omega), hr⟩
  exact Option.isSome_iff_exists.1 hb'

/-- **El costo de la búsqueda pagada**: el doble de lo repartido hasta la primera ronda que entrega (cada programa
recibe su presupuesto para correr y otro igual para verificar). `0` si nunca entrega (no se usa). -/
noncomputable def costoLevinPagado (v : Code) (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ T, (buscarPagado v x T).isSome then 2 * costoHasta (Nat.find h) else 0

/-- **Levin, pagando el verificador**: si el proceso pagado `(i, k, K)` resuelve, la búsqueda pagada cuesta menos que
`16 · 2^i · (k + K)`. -/
theorem levin_pagado {U : UniversoPagado} {p : ProcesoPagado} (h : CorrectoPagado U p) :
    costoLevinPagado U.v U.x < 16 * p.costoPagado := by
  classical
  obtain ⟨y, hy, hV⟩ := h
  have hK : 1 ≤ p.K := by have := evaln_bound hV; omega
  obtain ⟨y', hy'⟩ := buscarPagado_halla (T := p.i + Nat.clog 2 (p.k + p.K)) hy hV le_rfl
  have hT : (buscarPagado U.v U.x (p.i + Nat.clog 2 (p.k + p.K))).isSome := by rw [hy']; rfl
  have hex : ∃ T, (buscarPagado U.v U.x T).isSome := ⟨_, hT⟩
  rw [costoLevinPagado, dite_eq_left_of_eq_true (eq_true hex)]
  have h1 := costoHasta_mono (Nat.find_min' hex hT)
  have h2 := costoHasta_lt (p.i + Nat.clog 2 (p.k + p.K))
  have h3 : 2 ^ (p.i + Nat.clog 2 (p.k + p.K) + 2) = 4 * 2 ^ p.i * 2 ^ Nat.clog 2 (p.k + p.K) := by
    rw [pow_add, pow_add]; ring
  have h4 : 4 * 2 ^ p.i * 2 ^ Nat.clog 2 (p.k + p.K) < 4 * 2 ^ p.i * (2 * (p.k + p.K)) :=
    Nat.mul_lt_mul_of_pos_left (pow_clog_lt (by omega)) (by positivity)
  have h5 : 4 * 2 ^ p.i * (2 * (p.k + p.K)) * 2 = 16 * p.costoPagado := by
    unfold ProcesoPagado.costoPagado; ring
  omega

/-- **La ley, con el verificador pagado.** En un universo pagado resoluble, la búsqueda pagada entrega una respuesta
que el verificador acepta y cuesta menos que `16` veces el costo cerrado pagado. -/
theorem ley_pagada {U : UniversoPagado} (h : ResolublePagado U) :
    (∃ T y, buscarPagado U.v U.x T = some y ∧ 0 ∈ eval U.v (Nat.pair U.x y)) ∧
      costoLevinPagado U.v U.x < 16 * costoCerradoPagado U := by
  obtain ⟨p, hp, he⟩ := costoCerradoPagado_alcanzado h
  refine ⟨?_, he ▸ levin_pagado hp⟩
  obtain ⟨y, hy, hV⟩ := hp
  obtain ⟨y', hy'⟩ := buscarPagado_halla (T := p.i + Nat.clog 2 (p.k + p.K)) hy hV le_rfl
  exact ⟨_, y', hy', buscarPagado_acepta' hy'⟩

/-! ## 3. Verificadores de una función y el tiempo de verificar -/

/-- **`v` verifica la función `f`**: es total y acepta `⟨x, y⟩` (entrega `0`) exactamente cuando `y = f x`. -/
def VerificaA (v : Code) (f : ℕ → ℕ) : Prop :=
  (∀ n, (eval v n).Dom) ∧ ∀ x y, 0 ∈ eval v (Nat.pair x y) ↔ y = f x

/-- **El tiempo de verificar** la respuesta correcta: `t_V(x) = costo v ⟨x, f x⟩`, en la medida de `pasos`. -/
noncomputable def tiempoVerificar (v : Code) (f : ℕ → ℕ) (x : ℕ) : ℕ := costo v (Nat.pair x (f x))

/-- **Lo que cuesta leer el par** que se verifica: `⟨x, f x⟩ + 1`. Ningún verificador baja de esto
(`lectura_le_tiempo`). -/
def lecturaPar (f : ℕ → ℕ) (x : ℕ) : ℕ := Nat.pair x (f x) + 1

theorem pasos_eq_costo_de_dom {v : Code} {n : ℕ} (hd : (eval v n).Dom) : pasos v n = costo v n :=
  (ENat.natCast_toNat (ne_of_lt ((pasos_lt_top_iff v n).2 hd))).symm

/-- Para un programa que termina en `n`, `costo v n ≤ K` si y solo si el presupuesto `K` alcanza. -/
theorem costo_le_iff_de_dom {v : Code} {n : ℕ} (hd : (eval v n).Dom) (K : ℕ) :
    costo v n ≤ K ↔ (evaln K v n).isSome := by
  rw [← pasos_le_iff, pasos_eq_costo_de_dom hd, ENat.natCast_le_natCast]

/-- Si el presupuesto `K` alcanza, el costo no pasa de `K`. -/
theorem costo_le_de_evaln {v : Code} {n K z : ℕ} (h : evaln K v n = some z) : costo v n ≤ K := by
  have hd : (eval v n).Dom := Part.dom_iff_mem.2 ⟨z, evaln_sound h⟩
  exact (costo_le_iff_de_dom hd K).2 (by simp [h])

/-- Un programa que termina en `n` lo lee: `n < costo v n`. -/
theorem lt_costo_de_dom {v : Code} {n : ℕ} (hd : (eval v n).Dom) : n < costo v n := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 ((costo_le_iff_de_dom hd _).1 le_rfl)
  exact evaln_bound hz

/-- **Con su propio costo, el verificador acepta la respuesta correcta.** -/
theorem acepta_en_tiempo {v : Code} {f : ℕ → ℕ} (hv : VerificaA v f) (x : ℕ) :
    evaln (tiempoVerificar v f x) v (Nat.pair x (f x)) = some 0 := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 ((costo_le_iff_de_dom (hv.1 _) _).1 le_rfl)
  have h0 : (0 : ℕ) ∈ eval v (Nat.pair x (f x)) := (hv.2 x (f x)).2 rfl
  have : z = 0 := Part.mem_unique (evaln_sound hz) h0
  unfold tiempoVerificar; rw [hz, this]

/-- **Lo que el verificador acepta es la respuesta correcta.** -/
theorem acepta_es_f {v : Code} {f : ℕ → ℕ} (hv : VerificaA v f) {x y K : ℕ}
    (h : evaln K v (Nat.pair x y) = some 0) : y = f x :=
  (hv.2 x y).1 (evaln_sound h)

theorem lectura_le_tiempo {v : Code} {f : ℕ → ℕ} (hv : VerificaA v f) (x : ℕ) :
    lecturaPar f x ≤ tiempoVerificar v f x :=
  lt_costo_de_dom (hv.1 _)

/-- **Un programa de `f` y su verificador dan un proceso pagado correcto**: el resolvedor es el programa con su costo
de Blum, y el verificador corre con su propio costo. -/
theorem correctoPagado_de_computa {v : Code} {f : ℕ → ℕ} {j : Code} (hv : VerificaA v f) (hj : Computa j f)
    (x : ℕ) : CorrectoPagado ⟨v, x⟩ ⟨encodeCode j, costo j x, tiempoVerificar v f x⟩ := by
  obtain ⟨y, hy, hVy⟩ := correcto_de_computa hj x
  have hyf : y = f x := by simpa [verificadorDe] using hVy
  subst hyf
  exact ⟨f x, hy, acepta_en_tiempo hv x⟩

/-- **El costo cerrado pagado no pasa de `2^j · (t_j + t_V)`** para ningún programa `j` de `f`. -/
theorem pagado_le {v : Code} {f : ℕ → ℕ} {j : Code} (hv : VerificaA v f) (hj : Computa j f) (x : ℕ) :
    costoCerradoPagado ⟨v, x⟩ ≤ 2 ^ encodeCode j * (costo j x + tiempoVerificar v f x) :=
  costoCerradoPagado_le (correctoPagado_de_computa hv hj x)

/-- **Verificar se paga**: el costo cerrado pagado es por lo menos el tiempo de verificar la respuesta correcta. -/
theorem verificar_bajo_pagado {v : Code} {f : ℕ → ℕ} {j : Code} (hv : VerificaA v f) (hj : Computa j f) (x : ℕ) :
    tiempoVerificar v f x ≤ costoCerradoPagado ⟨v, x⟩ := by
  obtain ⟨p, ⟨y, hy, hV⟩, he⟩ := costoCerradoPagado_alcanzado ⟨_, correctoPagado_de_computa hv hj x⟩
  have hyf := acepta_es_f hv hV
  subst hyf
  have h1 : tiempoVerificar v f x ≤ p.K := costo_le_de_evaln hV
  have h2 : p.k + p.K ≤ p.costoPagado := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  rw [he]; omega

/-- **Pagar nunca abarata**: el costo cerrado gratis (con `verificadorDe f` como caja) no pasa del pagado. -/
theorem gratis_le_pagado {v : Code} {f : ℕ → ℕ} {j : Code} (hv : VerificaA v f) (hj : Computa j f) (x : ℕ) :
    costoCerrado ⟨verificadorDe f, x⟩ ≤ costoCerradoPagado ⟨v, x⟩ := by
  obtain ⟨p, ⟨y, hy, hV⟩, he⟩ := costoCerradoPagado_alcanzado ⟨_, correctoPagado_de_computa hv hj x⟩
  have hyf := acepta_es_f hv hV
  have h1 : costoCerrado ⟨verificadorDe f, x⟩ ≤ 2 ^ p.i * p.k :=
    costoCerrado_le (p := ⟨p.i, p.k⟩) ⟨y, hy, by simp [verificadorDe, hyf]⟩
  have h2 : 2 ^ p.i * p.k ≤ p.costoPagado := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  rw [he]; omega

/-- **La ley pagada, para una función: `costo ≲ 2^j · (t_j + t_V)`.** Para todo programa `j` de `f`, el costo cerrado
pagado está debajo de `2^j · (t_j + t_V)` y la búsqueda pagada debajo de `16 · 2^j · (t_j + t_V)`, con la respuesta
correcta; y el costo pagado nunca baja de `t_V`. -/
theorem pagado_en_O {v : Code} {f : ℕ → ℕ} {j : Code} (hv : VerificaA v f) (hj : Computa j f) (x : ℕ) :
    tiempoVerificar v f x ≤ costoCerradoPagado ⟨v, x⟩ ∧
      costoCerradoPagado ⟨v, x⟩ ≤ 2 ^ encodeCode j * (costo j x + tiempoVerificar v f x) ∧
      costoLevinPagado v x < 16 * 2 ^ encodeCode j * (costo j x + tiempoVerificar v f x) ∧
      ∃ T, buscarPagado v x T = some (f x) := by
  have hc := correctoPagado_de_computa hv hj x
  refine ⟨verificar_bajo_pagado hv hj x, pagado_le hv hj x, ?_, ?_⟩
  · have := levin_pagado hc
    simp only [ProcesoPagado.costoPagado] at this
    rw [mul_assoc]; exact this
  · obtain ⟨T, y, hT, h0⟩ := (ley_pagada ⟨_, hc⟩).1
    exact ⟨T, by rw [hT, (hv.2 x y).1 h0]⟩

/-! ## 4. Cuándo sobrevive el mínimo -/

/-- **El mínimo sobrevive si y solo si verificar es barato.** Para cualquier escala `g` (por ejemplo `0`, o lo que
cuesta leer el par), el costo cerrado pagado está en `O(t_j + g)` para **todo** programa `j` de `f` si y solo si el
tiempo de verificar lo está. -/
theorem sobrevive_iff {v : Code} {f : ℕ → ℕ} (g : ℕ → ℕ) (hv : VerificaA v f) {j₀ : Code} (hj₀ : Computa j₀ f) :
    (∀ j, Computa j f → EsO (fun x => costoCerradoPagado ⟨v, x⟩) (fun x => costo j x + g x)) ↔
      (∀ j, Computa j f → EsO (tiempoVerificar v f) (fun x => costo j x + g x)) := by
  constructor
  · intro h j hj
    obtain ⟨C, N, hC⟩ := h j hj
    exact ⟨C, N, fun x hx => le_trans (verificar_bajo_pagado hv hj₀ x) (hC x hx)⟩
  · intro h j hj
    obtain ⟨C, N, hC⟩ := h j hj
    refine ⟨2 ^ encodeCode j * (1 + C), N, fun x hx => ?_⟩
    have h1 := pagado_le hv hj x
    have h2 : tiempoVerificar v f x ≤ C * (costo j x + g x) := hC x hx
    calc costoCerradoPagado ⟨v, x⟩ ≤ 2 ^ encodeCode j * (costo j x + tiempoVerificar v f x) := h1
      _ ≤ 2 ^ encodeCode j * ((costo j x + g x) + C * (costo j x + g x)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ encodeCode j * (1 + C) * (costo j x + g x) := by ring

/-- **El enunciado general del arreglo.** Si `f` tiene la aceleración de Blum con `r(n, x) = (n+1)·x`, toma valores
`0` y `1`, y el verificador `v` de `f` **lleva adentro** un programa `j₀` de `f` (`costo j₀ = O(t_V)`), entonces el
costo cerrado pagado **no** está en `O(costo j + lectura)` para todo programa `j` de `f`. -/
theorem sin_minimo_pagado {f : ℕ → ℕ} (hB : TieneAceleracion (fun n x => (n + 1) * x) f) (h01 : ∀ n, f n ≤ 1)
    {v : Code} (hv : VerificaA v f) {j₀ : Code} (hj₀ : Computa j₀ f)
    (hdentro : EsO (costo j₀) (tiempoVerificar v f)) :
    ¬ ∀ j, Computa j f → EsO (fun x => costoCerradoPagado ⟨v, x⟩) (fun x => costo j x + lecturaPar f x) := by
  intro H
  refine sin_optimo (r := fun n x => (n + 1) * x) (fun _ _ => le_rfl) hB ⟨j₀, hj₀, fun j hj => ?_⟩
  obtain ⟨C₀, N₀, h₀⟩ := hdentro
  obtain ⟨C, N, hC⟩ := H j hj
  -- Leer el par no pasa del costo de ningún programa de `f`, desde algún punto.
  obtain ⟨j', hj', N₁, h₁⟩ := hB.2 j hj
  refine ⟨C₀ * (C * 2), max (max N₀ N) (max N₁ 1), fun x hx => ?_⟩
  have hx0 : N₀ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hxN : N ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx1 : N₁ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hx2 : 1 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have a := h₀ x hx0
  have b := le_trans (verificar_bajo_pagado hv hj₀ x) (hC x hxN)
  have c : (x + 1) * costo j' x ≤ costo j x := h₁ x hx1
  have d : x < costo j' x := costo_gt hj' x
  have e : lecturaPar f x ≤ costo j x := by
    have hf := h01 x
    have hp : Nat.pair x (f x) = x * x + x + f x := by
      simp only [Nat.pair, show ¬ x < f x from by omega, ↓reduceIte]
    unfold lecturaPar; rw [hp]
    have : (x + 1) * (x + 1) ≤ (x + 1) * costo j' x := Nat.mul_le_mul_left _ d
    nlinarith
  calc costo j₀ x ≤ C₀ * tiempoVerificar v f x := a
    _ ≤ C₀ * (C * (costo j x + lecturaPar f x)) := Nat.mul_le_mul_left _ b
    _ ≤ C₀ * (C * (costo j x + costo j x)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    _ = C₀ * (C * 2) * costo j x := by ring

/-! ## 5. El verificador canónico: calcula `j₀ x` y lo compara -/

theorem existe_codigoIgual :
    ∃ c : Code, ∀ n, eval c n = Part.some (if n.unpair.1 = n.unpair.2 then 0 else 1) := by
  have hp : Primrec fun n : ℕ => if n.unpair.1 = n.unpair.2 then 0 else 1 :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 0) (Primrec.const 1)
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 hp.to_comp)
  exact ⟨c, fun n => by rw [hc]; rfl⟩

/-- Un código de la igualdad: sobre `⟨a, b⟩` entrega `0` si `a = b` y `1` si no. -/
noncomputable def codigoIgual : Code := Classical.choose existe_codigoIgual

theorem eval_codigoIgual (n : ℕ) :
    eval codigoIgual n = Part.some (if n.unpair.1 = n.unpair.2 then 0 else 1) :=
  Classical.choose_spec existe_codigoIgual n

/-- **El verificador canónico de un programa `j₀`**: sobre `⟨x, y⟩` calcula `⟨j₀ x, y⟩` y compara. Es el verificador
«`y = f x`» implementado de la única manera que no supone nada: corriendo un programa de `f`. -/
noncomputable def verificadorCodigo (j₀ : Code) : Code := comp codigoIgual (pair (comp j₀ left) right)

theorem eval_verificadorCodigo {j₀ : Code} {f : ℕ → ℕ} (hj : Computa j₀ f) (n : ℕ) :
    eval (verificadorCodigo j₀) n = Part.some (if f n.unpair.1 = n.unpair.2 then 0 else 1) := by
  have hl : eval left n = Part.some n.unpair.1 := rfl
  have hr : eval right n = Part.some n.unpair.2 := rfl
  have h1 : eval (comp j₀ left) n = Part.some (f n.unpair.1) := by
    change Part.bind (eval left n) (fun m => eval j₀ m) = _
    rw [hl, Part.bind_some, hj]
  have h2 : eval (pair (comp j₀ left) right) n = Part.some (Nat.pair (f n.unpair.1) n.unpair.2) := by
    change Nat.pair <$> eval (comp j₀ left) n <*> eval right n = _
    rw [h1, hr]; simp [Seq.seq]
  change Part.bind (eval (pair (comp j₀ left) right) n) (fun m => eval codigoIgual m) = _
  rw [h2, Part.bind_some, eval_codigoIgual, Nat.unpair_pair]

/-- **El canónico verifica `f`.** -/
theorem verificaA_verificadorCodigo {j₀ : Code} {f : ℕ → ℕ} (hj : Computa j₀ f) :
    VerificaA (verificadorCodigo j₀) f := by
  refine ⟨fun n => by rw [eval_verificadorCodigo hj]; trivial, fun x y => ?_⟩
  rw [eval_verificadorCodigo hj, Nat.unpair_pair, Part.mem_some_iff]
  constructor
  · intro h; by_contra hne; simp [Ne.symm hne] at h
  · intro h; simp [h]

theorem evaln_comp_isSome {K n : ℕ} {a b : Code} (h : (evaln K (comp a b) n).isSome) :
    ∃ m, evaln K b n = some m ∧ (evaln K a m).isSome := by
  cases K with
  | zero => simp [evaln] at h
  | succ k =>
    simp only [evaln] at h
    by_cases hn : n ≤ k
    · simp only [hn, guard, ite_true] at h
      cases hb : evaln (k + 1) b n with
      | none => simp [hb] at h
      | some m => exact ⟨m, rfl, by simpa [hb] using h⟩
    · simp [hn] at h

theorem evaln_pair_isSome {K n : ℕ} {a b : Code} (h : (evaln K (pair a b) n).isSome) :
    (evaln K a n).isSome ∧ (evaln K b n).isSome := by
  cases K with
  | zero => simp [evaln] at h
  | succ k =>
    simp only [evaln] at h
    by_cases hn : n ≤ k
    · simp only [hn, guard, ite_true] at h
      cases ha : evaln (k + 1) a n <;> cases hb : evaln (k + 1) b n <;> simp_all [Seq.seq]
    · simp [hn] at h

theorem evaln_left_eq {K n m : ℕ} (h : evaln K left n = some m) : m = n.unpair.1 := by
  cases K with
  | zero => simp [evaln] at h
  | succ k =>
    simp only [evaln] at h
    by_cases hn : n ≤ k
    · simp [hn, guard] at h; exact h.symm
    · simp [hn] at h

/-- **El canónico lleva adentro su programa**: con el presupuesto que alcanza para verificar `⟨x, y⟩`, alcanza para
correr `j₀` sobre `x`. Así `costo j₀ x ≤ costo (verificadorCodigo j₀) ⟨x, y⟩` para todo `y`. -/
theorem costo_le_verificadorCodigo {j₀ : Code} {f : ℕ → ℕ} (hj : Computa j₀ f) (x y : ℕ) :
    costo j₀ x ≤ costo (verificadorCodigo j₀) (Nat.pair x y) := by
  have hd : (eval (verificadorCodigo j₀) (Nat.pair x y)).Dom := (verificaA_verificadorCodigo hj).1 _
  have hs := (costo_le_iff_de_dom hd _).1 le_rfl
  obtain ⟨m, hm, -⟩ := evaln_comp_isSome hs
  have hp := (evaln_pair_isSome (by rw [hm]; rfl : (evaln _ (pair (comp j₀ left) right) (Nat.pair x y)).isSome)).1
  obtain ⟨l, hl, hjl⟩ := evaln_comp_isSome hp
  have hl' := evaln_left_eq hl
  rw [Nat.unpair_pair] at hl'
  subst hl'
  exact (costo_le_iff hj _ _).2 hjl

/-- **`t_V` del canónico es al menos el costo de su programa.** -/
theorem dentro_verificadorCodigo {j₀ : Code} {f : ℕ → ℕ} (hj : Computa j₀ f) :
    EsO (costo j₀) (tiempoVerificar (verificadorCodigo j₀) f) :=
  ⟨1, 0, fun x _ => by rw [one_mul]; exact costo_le_verificadorCodigo hj x (f x)⟩

/-! ## 6. El arreglo de la frontera -/

/-- **La frontera, con el verificador pagado.** Para la `f` de Blum (`BlumExiste.blum`):
* **con su verificador gratis** (`verificadorDe f`), el costo cerrado está en `O(costo j)` para todo programa `j` de `f`
  (el «mínimo» de `UniversoCerrado.frontera`);
* **con el verificador pagado**, para **cada** programa `j₀` de `f`, el verificador canónico `verificadorCodigo j₀`
  verifica `f`, el costo cerrado pagado es al menos `costo j₀` en toda entrada, y **no** está en
  `O(costo j + lectura)` para todo programa `j` de `f` (ni, menos aún, en `O(costo j)`).

El mínimo de la frontera venía del verificador gratis: pagado, verificar cuesta lo que cuesta calcular `f`, y calcular
`f` no tiene óptimo. -/
theorem frontera_pagada : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧
    (∀ j, Computa j f → EsO (fun x => costoCerrado ⟨verificadorDe f, x⟩) (costo j)) ∧
    ∀ j₀, Computa j₀ f → VerificaA (verificadorCodigo j₀) f ∧
      (∀ x, costo j₀ x ≤ costoCerradoPagado ⟨verificadorCodigo j₀, x⟩) ∧
      (¬ ∀ j, Computa j f →
        EsO (fun x => costoCerradoPagado ⟨verificadorCodigo j₀, x⟩) (fun x => costo j x + lecturaPar f x)) ∧
      ¬ ∀ j, Computa j f → EsO (fun x => costoCerradoPagado ⟨verificadorCodigo j₀, x⟩) (costo j) := by
  obtain ⟨f, h01, hf, hB⟩ := BlumExiste.blum BlumExiste.computable_lineal
  refine ⟨f, h01, hf, fun j hj => (con_verificador_hay_minimo hj).1, fun j₀ hj₀ => ?_⟩
  have hv := verificaA_verificadorCodigo hj₀
  have hno := sin_minimo_pagado hB h01 hv hj₀ (dentro_verificadorCodigo hj₀)
  refine ⟨hv, fun x => le_trans (costo_le_verificadorCodigo hj₀ x (f x)) (verificar_bajo_pagado hv hj₀ x), hno,
    fun H => hno fun j hj => ?_⟩
  obtain ⟨C, N, hC⟩ := H j hj
  exact ⟨C, N, fun x hx => le_trans (hC x hx) (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))⟩

/-! ## 7. Controles -/

/-- El problema del control barato: la respuesta es `0`. -/
def fCero : ℕ → ℕ := fun _ => 0

/-- **El verificador barato**: `Code.right` lee `y` de `⟨x, y⟩` y lo entrega; acepta exactamente `y = 0`. -/
theorem verificaA_right : VerificaA Code.right fCero := by
  refine ⟨fun n => trivial, fun x y => ?_⟩
  change (0 : ℕ) ∈ Part.some (Nat.pair x y).unpair.2 ↔ y = 0
  rw [Nat.unpair_pair, Part.mem_some_iff, eq_comm]

/-- `Code.right` cuesta exactamente leer su entrada. -/
theorem costo_right (n : ℕ) : costo Code.right n = n + 1 := by
  have hd : (eval Code.right n).Dom := trivial
  refine le_antisymm ((costo_le_iff_de_dom hd _).2 (by simp [evaln])) ?_
  exact lt_costo_de_dom hd

/-- **Verificar barato**: el tiempo de verificar es exactamente lo que cuesta leer el par. -/
theorem tiempo_right (x : ℕ) : tiempoVerificar Code.right fCero x = lecturaPar fCero x := by
  unfold tiempoVerificar lecturaPar; rw [costo_right]

theorem computa_fCero : Computa Code.zero fCero := computa_cero

theorem encode_zero : encodeCode Code.zero = 0 := by simp [encodeCode]

/-- **El control barato: el mínimo sobrevive.** Con el verificador barato, el costo cerrado pagado está en
`O(costo j + lectura)` para **todo** programa `j` de la constante `0`. Es la hipótesis de `sobrevive_iff`, no vacía. -/
theorem control_barato : ∀ j, Computa j fCero →
    EsO (fun x => costoCerradoPagado ⟨Code.right, x⟩) (fun x => costo j x + lecturaPar fCero x) :=
  (sobrevive_iff (lecturaPar fCero) verificaA_right computa_fCero).2 fun j _ =>
    ⟨1, 0, fun x _ => by
      change tiempoVerificar Code.right fCero x ≤ 1 * (costo j x + lecturaPar fCero x)
      rw [tiempo_right]; omega⟩

/-- **La cota casi se alcanza** en el control barato: `⟨x,0⟩ + 1 ≤ costo pagado ≤ ⟨x,0⟩ + x + 2`. -/
theorem control_barato_ajustado (x : ℕ) :
    Nat.pair x 0 + 1 ≤ costoCerradoPagado ⟨Code.right, x⟩ ∧
      costoCerradoPagado ⟨Code.right, x⟩ ≤ Nat.pair x 0 + x + 2 := by
  have h1 := verificar_bajo_pagado verificaA_right computa_fCero x
  have h2 := pagado_le verificaA_right computa_fCero x
  rw [tiempo_right, encode_zero, costo_cero] at *
  unfold lecturaPar fCero at *
  constructor <;> omega

/-- **Leer el par cuesta.** Aun en el problema trivial, el costo cerrado pagado **no** está en `O(costo Code.zero)`:
el presupuesto acota el valor de la entrada y `⟨x, 0⟩ ≥ x²`. Por eso la escala honesta es `t_j + lectura`. -/
theorem leer_el_par_cuesta :
    ¬ EsO (fun x => costoCerradoPagado ⟨Code.right, x⟩) (costo Code.zero) := by
  rintro ⟨C, N, h⟩
  set x := N + C + 1 with hxdef
  have a := (control_barato_ajustado x).1
  have b := h x (by omega)
  rw [costo_cero] at b
  have hp : Nat.pair x 0 = x * x + x := by
    simp only [Nat.pair, show ¬ x < 0 from by omega, ↓reduceIte, add_zero]
  rw [hp] at a
  have : C + 1 ≤ x := by omega
  nlinarith

/-- **Lo gratis esconde.** En el problema trivial, para `x ≥ 1`, el costo cerrado **gratis** queda por debajo del costo
de **una sola** verificación: el modelo de `UniversoCerrado.lean` no la estaba cobrando. -/
theorem gratis_esconde (x : ℕ) (hx : 1 ≤ x) :
    costoCerrado ⟨verificadorDe fCero, x⟩ < tiempoVerificar Code.right fCero x := by
  have h1 : costoCerrado ⟨verificadorDe fCero, x⟩ ≤ 2 ^ encodeCode Code.zero * costo Code.zero x :=
    costoCerrado_le (correcto_de_computa computa_fCero x)
  rw [encode_zero, costo_cero] at h1
  rw [tiempo_right]
  have hp : Nat.pair x (fCero x) = x * x + x := by
    simp only [Nat.pair, fCero, show ¬ x < 0 from by omega, ↓reduceIte, add_zero]
  unfold lecturaPar; rw [hp]
  nlinarith

end VerificadorPagado
end Tiempo
end Sagitta.Map
