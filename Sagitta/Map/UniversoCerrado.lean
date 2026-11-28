import Sagitta.Map.CorteRacional

/-!
# El universo cerrado: la complejidad se conserva si nada entra gratis

La idea es de José (24 nov 2026). En un **universo cerrado** solo hay tres cosas: una máquina universal fija, el
verificador `V` (la definición del problema) y la entrada `x`. El resolvedor no viene de afuera: hay que encontrarlo o
escribirlo pagando con tiempo adentro. No hay consejo no uniforme, ni oráculo, ni tabla regalada. Si se cuenta todo
(escribir el programa y correrlo), la complejidad se conserva.

## La definición y la ley

* `Universo`: el verificador `V : ℕ → ℕ → Bool` y la entrada `x`. La máquina es `correr` de `Levin.lean` (los códigos
  de Mathlib con `evaln`), fija para todos.
* `Proceso`: un programa `i` y un presupuesto `k`; arranca solo con `x`. Es **correcto** si entrega algo que `V` acepta.
* **La medida.** El costo de un proceso es `2^i · k`: **escribir por correr**. `k` es el presupuesto de `evaln` (la
  medida de rondas de `Levin.lean`) y `2^i` es lo que cuesta encontrar el programa `i` adentro, porque la búsqueda
  universal le da al programa `i` la fracción `2^(-i)` del esfuerzo. Se eligió el presupuesto, y no `pasos`, porque es
  la medida en que está probada la cota de Levin (`levin`, `costoLevin_le`); `pasos` aparece como puente en
  `levin_es_programa`. La «longitud» del programa es su índice `i` en la numeración de Mathlib, no su largo en bits.
* `costoCerrado U`: el mínimo de `2^i · k` sobre los procesos correctos. `kt U`: el mínimo de `i + ⌈log₂ k⌉`.

**La ley.** `costo cerrado ≈ min (escribir × correr)`, y en bits `log ≈ |p| + log t`, la `Kt` de Levin:

* **Cota inferior** (`cota_inferior`, `sin_atajo`): el costo cerrado es el costo de un proceso correcto concreto, está
  debajo del de todos los demás y supera a la entrada (ningún proceso resuelve sin leerla). Y ningún programa baja de él
  (`programa_no_baja`): si el código `c` resuelve `x`, `costo cerrado ≤ 2^(código de c) · pasos`.
* **Cota superior** (`ley`, `levin_contra_proceso`): la búsqueda de Levin entrega una respuesta aceptada y cuesta menos
  que `8 · costo cerrado`. Es un proceso cerrado: es **un programa** (`levin_es_programa`, con `Nat.rfind`, la técnica
  de `BlumExiste.lean`), uno solo para todas las entradas, si `V` es primitivo recursivo.
* **En bits** (`log_cerrado_le_kt`, `kt_le_log_cerrado`, `log_levin_lt_kt`):
  `kt − 1 ≤ log₂ (costo cerrado) ≤ kt` y `log₂ (costo de Levin) < kt + 3`.

## Dónde se escapa la complejidad

* **A la constante.** Para un problema fijo, el resolvedor `i` es uno solo para todas las entradas, así que `2^i` es una
  constante: `cerrado_en_O` da `costo cerrado ≤ 2^i · t(x)`, en `O(t)` con constante que depende de `i` y no de `x`. En
  una escalera estricta de resolvedores esas constantes no están acotadas (`constante_crece`); con la `f` de Blum, la
  escalera existe de verdad y sus constantes `2^(código)` crecen sin cota (`escalera_de_blum`). La complejidad no se
  esfuma: se esconde en la constante.
* **A la elección de la máquina universal.** Todo está medido con la numeración de Mathlib. Otra máquina universal
  cambia `i` por `i + c` (invariancia, de memoria; **no se prueba aquí**), es decir, la constante por `2^c`.
* **Afuera, si el universo no es cerrado.** Con una tabla regalada el costo es `1` en toda entrada y la cota inferior
  `x < costo` es falsa (`tabla_rompe`, gemelo de `tabla_gratis_rompe`). Con el resolvedor regalado (sin pagar `2^i`) el
  costo baja a la mitad o menos (`escribir_cuesta`, `sin_factor_falla`). La cerradura es la hipótesis que importa.

## La frontera con Blum

Con verificador, el corte de la búsqueda tiene mínimo: Levin queda debajo de todo programa (`levin_bajo_escalera`,
`con_verificador_hay_minimo`). Sin verificador, decidiendo, `blum` da funciones sin mínimo. `frontera` lo enuncia con
**la misma** `f`: con `verificadorDe f` como caja, la búsqueda está en `O(costo j)` para todo programa `j` de `f`; y
ningún programa de `f` lo está (`sin_optimo`). Lo que separa los dos lados es que el verificador se evalúa **gratis**:
el de `f` cuesta tanto como calcular `f`, y el modelo no lo cobra. La forma exacta que quedó: los dos lados están en
medidas distintas (rondas contra `pasos`), así que no es una contradicción, es un contraste.

## La lectura para P contra NP (lectura, no teorema)

En el universo cerrado con verificador, `P = NP` si y solo si el costo cerrado de buscar una asignación que satisfaga
una fórmula de SAT es polinomial en el tamaño de la fórmula. La dirección «si hay un resolvedor polinomial, el costo
cerrado es polinomial» es la forma de `cerrado_en_O`; la otra sería que la búsqueda de Levin misma sea polinomial. Nada
de esto se prueba aquí, porque las medidas no son tiempo de máquina.

## Lo que NO se prueba

* Que el presupuesto de `evaln` o la medida de rondas sean tiempo de máquina. `pasos` (de `AceleracionBlum.lean`) es una
  medida de Blum, tampoco es tiempo de una máquina de Turing. En particular, `levin_es_programa` **no** acota
  `costo L x` por un múltiplo de `costoLevin V x`: solo dice que el programa de Levin existe, es correcto, termina y
  paga el costo cerrado.
* **El costo de verificar no se cuenta.** `V` es una caja negra que se evalúa gratis, en la búsqueda y en la definición
  de proceso correcto. Por eso todo esto **relativiza**: vale igual con cualquier `V`, también con un oráculo.
* Nada sobre `P` contra `NP`.
* La invariancia respecto de la máquina universal.

## Fuente, de memoria

L. A. Levin, «Universal sequential search problems», *Problemy Peredachi Informatsii* 9(3), 1973. No la leí en esta
sesión; las pruebas son propias y usan `Levin.lean`, `CorteRacional.lean`, `AceleracionBlum.lean` y `BlumExiste.lean`.
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map
namespace Tiempo
namespace UniversoCerrado

open Levin AceleracionBlum CorteRacional

/-! ## 1. La definición -/

/-- **Un universo.** La máquina universal es fija y no es un campo: es `correr` de `Levin.lean` (los códigos de
Mathlib con `evaln`). Lo que cambia de un universo a otro es el verificador `V` (la definición del problema) y la
entrada `x`. Nada más entra. -/
structure Universo where
  /-- El verificador: `V x y = true` si `y` es una respuesta aceptable para `x`. -/
  V : ℕ → ℕ → Bool
  /-- La entrada. -/
  x : ℕ

/-- **Un proceso cerrado**: un programa (el número `i` de la máquina universal) y el presupuesto `k` con que se corre.
Arranca solo con la entrada: lo único que recibe es `x`. -/
structure Proceso where
  /-- El programa, como índice de la máquina universal. -/
  i : ℕ
  /-- El presupuesto de `evaln` con que se corre. -/
  k : ℕ

/-- **El proceso resuelve el universo**: corriendo el programa `i` con presupuesto `k` sobre la entrada, entrega algo
que el verificador acepta. -/
def Correcto (U : Universo) (p : Proceso) : Prop :=
  ∃ y, correr p.i p.k U.x = some y ∧ U.V U.x y = true

/-- El universo tiene solución: algún proceso cerrado lo resuelve. -/
def Resoluble (U : Universo) : Prop := ∃ p, Correcto U p

/-- **El costo cerrado de un proceso**: `2^i · k`, escribir por correr. El factor `2^i` es lo que cuesta encontrar
(o escribir) el programa `i` adentro: la búsqueda universal le da al programa `i` una fracción `2^(-i)` del esfuerzo.
Aquí la «longitud» del programa es su índice `i` en la numeración de Mathlib, no su largo en bits. -/
def Proceso.costoTotal (p : Proceso) : ℕ := 2 ^ p.i * p.k

/-- **El costo cerrado del universo**: el mínimo de `2^i · k` sobre los procesos cerrados que lo resuelven. Si no lo
resuelve ninguno, `0` por convención (`sInf ∅ = 0`); los teoremas piden `Resoluble`. -/
noncomputable def costoCerrado (U : Universo) : ℕ :=
  sInf {c | ∃ p, Correcto U p ∧ c = p.costoTotal}

/-- **La forma logarítmica**: el mínimo de `i + ⌈log₂ k⌉`, la `Kt` de Levin en este modelo. -/
noncomputable def kt (U : Universo) : ℕ :=
  sInf {c | ∃ p, Correcto U p ∧ c = p.i + Nat.clog 2 p.k}

/-! ## 2. La cota inferior: no hay atajo -/

/-- **Un proceso que resuelve lee la entrada**: su presupuesto supera a `x` (`evaln_bound` de Mathlib). -/
theorem Correcto.x_lt {U : Universo} {p : Proceso} (h : Correcto U p) : U.x < p.k := by
  obtain ⟨y, hy, -⟩ := h
  exact evaln_bound hy

theorem Correcto.k_pos {U : Universo} {p : Proceso} (h : Correcto U p) : 1 ≤ p.k := by
  have := h.x_lt; omega

theorem k_le_costoTotal (p : Proceso) : p.k ≤ p.costoTotal :=
  Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)

/-- **El mínimo está por debajo de cada proceso correcto.** -/
theorem costoCerrado_le {U : Universo} {p : Proceso} (h : Correcto U p) : costoCerrado U ≤ p.costoTotal :=
  Nat.sInf_le ⟨p, h, rfl⟩

/-- **El mínimo se alcanza**: es el costo de un proceso cerrado concreto. -/
theorem costoCerrado_alcanzado {U : Universo} (h : Resoluble U) :
    ∃ p, Correcto U p ∧ costoCerrado U = p.costoTotal := by
  obtain ⟨p, hp⟩ := h
  have hne : {c | ∃ p, Correcto U p ∧ c = p.costoTotal}.Nonempty := ⟨_, p, hp, rfl⟩
  obtain ⟨q, hq, he⟩ := Nat.sInf_mem hne
  exact ⟨q, hq, he⟩

/-- **La cota inferior.** En un universo resoluble, el costo cerrado (a) es el costo `2^i · k` de un proceso cerrado
correcto concreto, (b) no es mayor que el de ningún otro, y (c) supera a la entrada: ningún proceso cerrado resuelve
sin leerla. No baja de cero por magia: es el mínimo de algo que se paga. -/
theorem cota_inferior {U : Universo} (h : Resoluble U) :
    (∃ p, Correcto U p ∧ costoCerrado U = 2 ^ p.i * p.k) ∧
      (∀ p, Correcto U p → costoCerrado U ≤ 2 ^ p.i * p.k) ∧ U.x < costoCerrado U := by
  obtain ⟨p, hp, he⟩ := costoCerrado_alcanzado h
  refine ⟨⟨p, hp, he⟩, fun q hq => costoCerrado_le hq, ?_⟩
  rw [he]
  exact lt_of_lt_of_le hp.x_lt (k_le_costoTotal p)

/-- **Sin atajo**: por debajo del costo cerrado no hay ningún proceso cerrado que resuelva. -/
theorem sin_atajo {U : Universo} {c : ℕ} (hc : c < costoCerrado U) :
    ¬ ∃ p, Correcto U p ∧ p.costoTotal ≤ c := by
  rintro ⟨p, hp, hle⟩
  have := costoCerrado_le hp
  omega

/-! ## 3. La cota superior: la búsqueda de Levin es un proceso cerrado -/

/-- **Levin, contra un proceso.** La búsqueda universal (la de `Levin.lean`, que solo usa la máquina universal, el
verificador y la entrada) cuesta menos que `8 · 2^i · k` para todo proceso cerrado `(i, k)` que resuelve. -/
theorem levin_contra_proceso {U : Universo} {p : Proceso} (h : Correcto U p) :
    costoLevin U.V U.x < 8 * p.costoTotal := by
  obtain ⟨y, hy, hV⟩ := h
  have := costoLevin_le (Correcto.k_pos ⟨y, hy, hV⟩) hy hV
  unfold Proceso.costoTotal; rw [← mul_assoc]; exact this

/-- **La ley, cota superior.** En un universo resoluble, la búsqueda universal entrega una respuesta aceptada y cuesta
menos que `8` veces el costo cerrado: el costo cerrado se alcanza, salvo la constante `8`, con un solo proceso que no
depende del problema. -/
theorem ley {U : Universo} (h : Resoluble U) :
    (∃ T y, buscar U.V U.x T = some y ∧ U.V U.x y = true) ∧ costoLevin U.V U.x < 8 * costoCerrado U := by
  obtain ⟨p, hp, he⟩ := costoCerrado_alcanzado h
  refine ⟨?_, he ▸ levin_contra_proceso hp⟩
  obtain ⟨y, hy, hV⟩ := hp
  obtain ⟨T, y', hT, hV', -⟩ := levin (Correcto.k_pos ⟨y, hy, hV⟩) hy hV
  exact ⟨T, y', hT, hV'⟩

/-! ### En logaritmos: la `Kt` de Levin -/

theorem kt_le {U : Universo} {p : Proceso} (h : Correcto U p) : kt U ≤ p.i + Nat.clog 2 p.k :=
  Nat.sInf_le ⟨p, h, rfl⟩

theorem kt_alcanzado {U : Universo} (h : Resoluble U) :
    ∃ p, Correcto U p ∧ kt U = p.i + Nat.clog 2 p.k := by
  obtain ⟨p, hp⟩ := h
  have hne : {c | ∃ p, Correcto U p ∧ c = p.i + Nat.clog 2 p.k}.Nonempty := ⟨_, p, hp, rfl⟩
  obtain ⟨q, hq, he⟩ := Nat.sInf_mem hne
  exact ⟨q, hq, he⟩

/-- `2^i · k ≤ 2^(i + ⌈log₂ k⌉)`. -/
theorem costoTotal_le_pow (p : Proceso) : p.costoTotal ≤ 2 ^ (p.i + Nat.clog 2 p.k) := by
  unfold Proceso.costoTotal
  rw [pow_add]
  exact Nat.mul_le_mul_left _ (Nat.le_pow_clog one_lt_two _)

/-- **El costo cerrado, en bits, no pasa de la `Kt`**: `log₂ (costo cerrado) ≤ min (i + ⌈log₂ k⌉)`. -/
theorem log_cerrado_le_kt {U : Universo} (h : Resoluble U) : Nat.log 2 (costoCerrado U) ≤ kt U := by
  obtain ⟨p, hp, he⟩ := kt_alcanzado h
  rw [he]
  have h1 := costoCerrado_le hp
  have h2 := costoTotal_le_pow p
  by_cases h0 : costoCerrado U = 0
  · rw [h0]; simp
  · exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow h0 (by rw [pow_succ]; omega))

/-- **Y la `Kt` no pasa del costo cerrado en bits más uno**: `kt ≤ log₂ (costo cerrado) + 1`. -/
theorem kt_le_log_cerrado {U : Universo} (h : Resoluble U) : kt U ≤ Nat.log 2 (costoCerrado U) + 1 := by
  obtain ⟨p, hp, he⟩ := costoCerrado_alcanzado h
  have hk := hp.k_pos
  have h1 := kt_le hp
  have h2 : Nat.clog 2 p.k ≤ Nat.log 2 p.k + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two p.k).le
  have h3 : p.i + Nat.log 2 p.k ≤ Nat.log 2 (costoCerrado U) := by
    refine Nat.le_log_of_pow_le one_lt_two ?_
    rw [he, Proceso.costoTotal, pow_add]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
  omega

/-- **La forma `Kt` de la cota superior**: `log₂ (costo de Levin) < min (i + ⌈log₂ k⌉) + 3`. En bits, buscar cuesta
la longitud del programa más el logaritmo de su tiempo, más una constante. -/
theorem log_levin_lt_kt {U : Universo} (h : Resoluble U) : Nat.log 2 (costoLevin U.V U.x) < kt U + 3 := by
  obtain ⟨p, hp, he⟩ := kt_alcanzado h
  have h1 := levin_contra_proceso hp
  have h2 := costoTotal_le_pow p
  rw [he]
  by_cases h0 : costoLevin U.V U.x = 0
  · rw [h0]; simp
  · refine Nat.log_lt_of_lt_pow h0 ?_
    have : 2 ^ (p.i + Nat.clog 2 p.k + 3) = 8 * 2 ^ (p.i + Nat.clog 2 p.k) := by rw [pow_add]; ring
    rw [this]; omega

/-! ### La búsqueda misma es un programa

La búsqueda por rondas de `Levin.lean` es una función; aquí se prueba que también es un **código** de la máquina
universal, con la técnica de `BlumExiste.lean`: no se acota su costo desde la sintaxis, se arma con `Nat.rfind` y se
lee su costo con `pasos`. -/

/-- `findSome?` como `foldr`, para usar `Primrec.list_foldr`. -/
theorem findSome_foldr {α β : Type*} (f : α → Option β) (l : List α) :
    l.findSome? f = l.foldr (fun a acc => f a <|> acc) none := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [h, ih]

/-- La potencia es primitiva recursiva (`Nat.Primrec.pow` de Mathlib). -/
theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- **La máquina universal es primitiva recursiva** en `(i, k, x)`: es `primrec_evaln` de Mathlib. -/
theorem primrec_correr : Primrec fun p : ℕ × ℕ × ℕ => correr p.1 p.2.1 p.2.2 := by
  have h : Primrec fun p : ℕ × ℕ × ℕ => ((p.2.1, (Denumerable.ofNat Code p.1)), p.2.2) :=
    (Primrec.fst.comp Primrec.snd |>.pair ((Primrec.ofNat Code).comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.snd)
  exact (primrec_evaln.comp h).of_eq fun p => rfl

section Programa

variable {V : ℕ → ℕ → Bool}

theorem primrec_intento (hV : Primrec₂ V) :
    Primrec fun q : (ℕ × ℕ) × ℕ => intento V q.1.1 q.1.2 q.2 := by
  -- q = ((x, t), i)
  have hk : Primrec fun q : (ℕ × ℕ) × ℕ => 2 ^ (q.1.2 - q.2) :=
    primrec_pow.comp (Primrec.const 2) (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hc : Primrec fun q : (ℕ × ℕ) × ℕ => correr q.2 (2 ^ (q.1.2 - q.2)) q.1.1 :=
    primrec_correr.comp (Primrec.snd.pair (hk.pair (Primrec.fst.comp Primrec.fst)))
  have hg : Primrec₂ fun (q : (ℕ × ℕ) × ℕ) (y : ℕ) => bif V q.1.1 y then some y else none :=
    (Primrec.cond (hV.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  refine (Primrec.option_bind hc hg).of_eq fun q => ?_
  unfold intento
  cases correr q.2 (2 ^ (q.1.2 - q.2)) q.1.1 with
  | none => rfl
  | some y => cases h : V q.1.1 y <;> simp [Option.filter, h]

theorem primrec_ronda (hV : Primrec₂ V) : Primrec fun q : ℕ × ℕ => ronda V q.1 q.2 := by
  have h := Primrec.list_foldr (f := fun q : ℕ × ℕ => List.range (q.2 + 1)) (g := fun _ => (none : Option ℕ))
    (h := fun q (p : ℕ × Option ℕ) => intento V q.1 q.2 p.1 <|> p.2)
    (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))) (Primrec.const none)
    (Primrec.option_orElse.comp ((primrec_intento hV).comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun q => ?_
  unfold ronda
  rw [findSome_foldr]

/-- **La búsqueda hasta la ronda `T` es primitiva recursiva** si el verificador lo es. -/
theorem primrec_buscar (hV : Primrec₂ V) : Primrec fun q : ℕ × ℕ => buscar V q.1 q.2 := by
  have h := Primrec.list_foldr (f := fun q : ℕ × ℕ => List.range (q.2 + 1)) (g := fun _ => (none : Option ℕ))
    (h := fun q (p : ℕ × Option ℕ) => ronda V q.1 p.1 <|> p.2)
    (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))) (Primrec.const none)
    (Primrec.option_orElse.comp ((primrec_ronda hV).comp (Primrec.fst.comp Primrec.fst |>.pair
      (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun q => ?_
  unfold buscar
  rw [findSome_foldr]

/-- **La búsqueda de Levin sin tope**: busca la primera ronda `T` que entrega algo y devuelve eso. Es parcial: si nada
resuelve la entrada, no termina (`buscar_nada`). -/
def levinP (V : ℕ → ℕ → Bool) (x : ℕ) : Part ℕ :=
  (Nat.rfind fun T => Part.some (buscar V x T).isSome).map fun T => (buscar V x T).getD 0

/-- Es parcial recursiva, si el verificador es primitivo recursivo. -/
theorem partrec_levinP (hV : Primrec₂ V) : Nat.Partrec (levinP V) := by
  have hb := primrec_buscar hV
  have h1 : Partrec₂ fun (x T : ℕ) => (Part.some (buscar V x T).isSome : Part Bool) :=
    (Primrec.option_isSome.comp hb).to_comp.partrec
  have h2 : Computable₂ fun (x T : ℕ) => (buscar V x T).getD 0 :=
    (Primrec.option_getD.comp hb (Primrec.const 0)).to_comp
  exact Partrec.nat_iff.1 (Partrec.map (Partrec.rfind h1) h2)

/-- **Corrección**: lo que entrega, `V` lo acepta. -/
theorem levinP_acepta {x y : ℕ} (h : y ∈ levinP V x) : V x y = true := by
  obtain ⟨T, hT, rfl⟩ := (Part.mem_map_iff _).1 h
  have hs : (buscar V x T).isSome = true := by simpa using Nat.rfind_spec hT
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 hs
  rw [hy']
  exact buscar_acepta hy'

/-- **Termina** cuando algún proceso cerrado resuelve. -/
theorem levinP_dom {x i k y : ℕ} (h : correr i k x = some y) (hV : V x y = true) : (levinP V x).Dom := by
  obtain ⟨y', hy'⟩ := buscar_halla (T := i + Nat.clog 2 k) h hV le_rfl
  have : (Nat.rfind fun T => Part.some (buscar V x T).isSome).Dom :=
    Nat.rfind_dom'.2 ⟨i + Nat.clog 2 k, by simp [hy'], fun _ => trivial⟩
  exact this

/-- **Un programa que termina es un proceso cerrado con su costo de Blum de presupuesto.** Si `y ∈ eval c x`, correr
el índice de `c` con presupuesto `costo c x` (el menor que alcanza, `pasos` de `AceleracionBlum.lean`) entrega `y`. -/
theorem correr_de_eval {c : Code} {x y : ℕ} (h : y ∈ eval c x) : correr (encodeCode c) (costo c x) x = some y := by
  have hd : (eval c x).Dom := Part.dom_iff_mem.2 ⟨y, h⟩
  have hp : pasos c x = (costo c x : ℕ∞) :=
    (ENat.natCast_toNat (ne_of_lt ((pasos_lt_top_iff c x).2 hd))).symm
  have hs := (pasos_le_iff c x (costo c x)).1 (le_of_eq hp)
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 hs
  have hy'e : y' = y := Part.mem_unique (evaln_sound hy') h
  have hcod : ofNatCode (encodeCode c) = c := Denumerable.ofNat_encode c
  unfold correr
  rw [hcod, hy', hy'e]

/-- **Ningún programa baja del costo cerrado.** Si el programa `c` entrega en `x` algo que `V` acepta, su costo de Blum
`costo c x` (pasos de `evaln`) paga, junto con `2^(código de c)`, por lo menos el costo cerrado. -/
theorem programa_no_baja {c : Code} {x y : ℕ} (h : y ∈ eval c x) (hV : V x y = true) :
    costoCerrado ⟨V, x⟩ ≤ 2 ^ encodeCode c * costo c x :=
  costoCerrado_le (p := ⟨encodeCode c, costo c x⟩) ⟨y, correr_de_eval h, hV⟩

/-- **La búsqueda de Levin es un programa.** Si el verificador es primitivo recursivo, hay un código `L` (uno solo,
para todas las entradas) que entrega solo respuestas aceptadas y que, en toda entrada resoluble, termina. Su costo, en
la medida `pasos`, paga el costo cerrado (con su `2^L`), y el costo por rondas de la búsqueda queda debajo de `8` veces
el costo cerrado. Lo que **no** se prueba es la otra punta: que `costo L x` esté acotado por un múltiplo de
`costoLevin V x` (haría falta el costo de simular `evaln`, constructor por constructor). -/
theorem levin_es_programa (hV : Primrec₂ V) : ∃ L : Code,
    (∀ x y, y ∈ eval L x → V x y = true) ∧
    ∀ x, Resoluble ⟨V, x⟩ → (eval L x).Dom ∧
      costoLevin V x < 8 * costoCerrado ⟨V, x⟩ ∧ costoCerrado ⟨V, x⟩ ≤ 2 ^ encodeCode L * costo L x := by
  obtain ⟨L, hL⟩ := exists_code.1 (partrec_levinP hV)
  refine ⟨L, fun x y hy => levinP_acepta (V := V) (by rw [← hL]; exact hy), fun x hx => ?_⟩
  have hd : (eval L x).Dom := by
    obtain ⟨p, y, hy, hVy⟩ := hx
    rw [hL]; exact levinP_dom hy hVy
  refine ⟨hd, (ley hx).2, ?_⟩
  have hmem : (eval L x).get hd ∈ eval L x := Part.get_mem hd
  exact programa_no_baja hmem (levinP_acepta (V := V) (by rw [← hL]; exact hmem))

end Programa

/-! ## 4. El control de cerradura: con una caja regalada el costo baja -/

/-- **El universo abierto con una tabla**: además de la máquina, `V` y `x`, hay una tabla `t` llenada afuera, que se lee
con costo `1`. Si la tabla tiene una respuesta aceptada para `x`, el costo es `1`; si no, queda el costo cerrado. -/
noncomputable def costoAbierto (t : ℕ → ℕ) (U : Universo) : ℕ :=
  if U.V U.x (t U.x) = true then 1 else costoCerrado U

/-- Abrir el universo nunca encarece. -/
theorem abierto_le (t : ℕ → ℕ) {U : Universo} (h : Resoluble U) : costoAbierto t U ≤ costoCerrado U := by
  have := (cota_inferior h).2.2
  unfold costoAbierto; split_ifs <;> omega

/-- **El universo abierto con el resolvedor regalado**: el programa entra desde afuera y no se paga escribirlo; solo
se cuenta el presupuesto `k`, no `2^i · k`. -/
noncomputable def costoSinEscribir (U : Universo) : ℕ :=
  sInf {c | ∃ p, Correcto U p ∧ c = p.k}

/-- El verificador del ejemplo: la única respuesta aceptada es `1`. -/
def vUno : ℕ → ℕ → Bool := fun _ y => y == 1

/-- El universo del ejemplo, sobre la entrada `x`. -/
def uUno (x : ℕ) : Universo := ⟨vUno, x⟩

/-- Algún programa responde `1` en toda entrada (`correr_universal` con la constante `1`). -/
theorem hay_programa_uno : ∃ i, ∀ x, ∃ k, correr i k x = some 1 := by
  obtain ⟨i, hi⟩ := correr_universal (f := fun _ => Part.some 1)
    (Partrec.nat_iff.1 (Computable.const 1 : Computable fun _ : ℕ => (1 : ℕ)))
  exact ⟨i, fun x => (hi x 1).1 (Part.mem_some 1)⟩

theorem uUno_resoluble (x : ℕ) : Resoluble (uUno x) := by
  obtain ⟨i, hi⟩ := hay_programa_uno
  obtain ⟨k, hk⟩ := hi x
  exact ⟨⟨i, k⟩, 1, hk, rfl⟩

/-- El programa `0` es `Code.zero`: responde `0` o no responde. -/
theorem correr_cero {k x y : ℕ} (h : correr 0 k x = some y) : y = 0 := by
  have h0 : (ofNatCode 0 : Code) = Code.zero := by simp [ofNatCode]
  unfold correr at h
  rw [h0] at h
  cases k with
  | zero => simp [evaln] at h
  | succ k =>
    simp only [evaln] at h
    by_cases hx : x ≤ k
    · simp [hx] at h; exact h.symm
    · simp [hx] at h

/-- En `uUno` ningún proceso correcto usa el programa `0`. -/
theorem uUno_i_pos {x : ℕ} {p : Proceso} (h : Correcto (uUno x) p) : 1 ≤ p.i := by
  obtain ⟨y, hy, hV⟩ := h
  rcases Nat.eq_zero_or_pos p.i with h0 | h0
  · rw [h0] at hy
    have := correr_cero hy
    subst this
    simp [uUno, vUno] at hV
  · exact h0

/-- **El control de cerradura, con la tabla** (el gemelo de `tabla_gratis_rompe`). En `uUno`, todo proceso cerrado
cuesta más que la entrada, pero con la tabla `t = 1` regalada el costo es `1` en toda entrada. La cota inferior
`x < costo` es **falsa** en el universo abierto. -/
theorem tabla_rompe :
    (∀ x, x < costoCerrado (uUno x)) ∧ (∀ x, costoAbierto (fun _ => 1) (uUno x) = 1) ∧
      ¬ ∀ x, x < costoAbierto (fun _ => 1) (uUno x) := by
  have ha : ∀ x, costoAbierto (fun _ => 1) (uUno x) = 1 := fun x => by
    simp [costoAbierto, uUno, vUno]
  refine ⟨fun x => (cota_inferior (uUno_resoluble x)).2.2, ha, fun h => ?_⟩
  have := h 1
  rw [ha] at this
  exact lt_irrefl 1 this

/-- **El control de cerradura, con el resolvedor regalado.** En `uUno`, el costo cerrado es por lo menos el doble del
costo sin pagar la escritura, y por lo tanto mayor: escribir el programa no es gratis. -/
theorem escribir_cuesta (x : ℕ) :
    2 * costoSinEscribir (uUno x) ≤ costoCerrado (uUno x) ∧
      costoSinEscribir (uUno x) < costoCerrado (uUno x) := by
  obtain ⟨p, hp, he⟩ := costoCerrado_alcanzado (uUno_resoluble x)
  have hi := uUno_i_pos hp
  have hk := hp.k_pos
  have h1 : costoSinEscribir (uUno x) ≤ p.k := Nat.sInf_le ⟨p, hp, rfl⟩
  have h2 : 2 * p.k ≤ p.costoTotal := by
    unfold Proceso.costoTotal
    exact Nat.mul_le_mul_right _ (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ p.i := Nat.pow_le_pow_right (by norm_num) hi)
  omega

/-! ## 5. Dónde se esconde la complejidad: la constante -/

/-- **Un resolvedor fijo da una cota lineal.** Si el programa `i` resuelve **toda** entrada con presupuesto `t x`, el
costo cerrado es a lo sumo `2^i · t x` y Levin menos que `8 · 2^i · t x`: los dos están en `O(t)`, con una constante
que depende de `i` y no de `x`. -/
theorem cerrado_en_O {V : ℕ → ℕ → Bool} {i : ℕ} {t : ℕ → ℕ}
    (h : ∀ x, ∃ y, correr i (t x) x = some y ∧ V x y = true) :
    (∀ x, costoCerrado ⟨V, x⟩ ≤ 2 ^ i * t x) ∧ (∀ x, costoLevin V x < 8 * 2 ^ i * t x) ∧
      EsO (fun x => costoCerrado ⟨V, x⟩) t ∧ EsO (costoLevin V) t := by
  have hc : ∀ x, Correcto ⟨V, x⟩ ⟨i, t x⟩ := fun x => h x
  have h1 : ∀ x, costoCerrado ⟨V, x⟩ ≤ 2 ^ i * t x := fun x => costoCerrado_le (hc x)
  have h2 : ∀ x, costoLevin V x < 8 * 2 ^ i * t x := fun x => by
    have := levin_contra_proceso (hc x)
    simp only [Proceso.costoTotal] at this
    rw [mul_assoc]; exact this
  exact ⟨h1, h2, ⟨2 ^ i, 0, fun x _ => h1 x⟩, ⟨8 * 2 ^ i, 0, fun x _ => (h2 x).le⟩⟩

/-- **En una escalera, la constante crece.** Si los programas `i k` resuelven toda entrada con presupuestos `t k`, la
escalera es estricta (`t (k+1) ∈ o (t k)`) y el presupuesto de cada peldaño es función de su programa, la constante
`2^(i k)` con que el costo cerrado queda debajo de `t k` no está acotada. Es `constantes_no_acotadas` de
`CorteRacional.lean`. -/
theorem constante_crece {V : ℕ → ℕ → Bool} {i : ℕ → ℕ} {t : ℕ → ℕ → ℕ} (presupuesto : ℕ → ℕ → ℕ)
    (hpres : ∀ k, t k = presupuesto (i k)) (ho : ∀ k, t (k + 1) ∈ o (t k)) (ht1 : ∀ k x, 1 ≤ t k x)
    (h : ∀ k x, ∃ y, correr (i k) (t k x) x = some y ∧ V x y = true) :
    (∀ k x, costoCerrado ⟨V, x⟩ ≤ 2 ^ i k * t k x) ∧ ∀ M, ∃ k, M < 2 ^ i k := by
  refine ⟨fun k x => (cerrado_en_O (h k)).1 x, fun M => ?_⟩
  obtain ⟨k, hk⟩ := constantes_no_acotadas presupuesto hpres ho ht1 (8 * M)
  exact ⟨k, by omega⟩

/-! ## 6. La frontera con Blum: la diferencia es el verificador -/

/-- El verificador de una función: acepta `y` exactamente cuando `y = f x`. -/
def verificadorDe (f : ℕ → ℕ) : ℕ → ℕ → Bool := fun x y => decide (y = f x)

/-- **Un programa de `f` resuelve el universo de su verificador**, con su propio índice y su costo de Blum como
presupuesto. -/
theorem correcto_de_computa {c : Code} {f : ℕ → ℕ} (hc : Computa c f) (x : ℕ) :
    Correcto ⟨verificadorDe f, x⟩ ⟨encodeCode c, costo c x⟩ := by
  have hs := (costo_le_iff hc x (costo c x)).1 le_rfl
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  have hmem : y ∈ eval c x := evaln_sound hy
  rw [hc x] at hmem
  have hyf : y = f x := Part.mem_some_iff.1 hmem
  have hcod : ofNatCode (encodeCode c) = c := Denumerable.ofNat_encode c
  refine ⟨y, ?_, by simp [verificadorDe, hyf]⟩
  unfold correr
  rw [hcod]; exact hy

/-- **Con el verificador, el corte tiene mínimo**: para toda `f` computable, el costo cerrado y la búsqueda de Levin
sobre `verificadorDe f` están en `O(costo j)` para **todo** programa `j` de `f`, a la vez. -/
theorem con_verificador_hay_minimo {f : ℕ → ℕ} {j : Code} (hj : Computa j f) :
    EsO (fun x => costoCerrado ⟨verificadorDe f, x⟩) (costo j) ∧ EsO (costoLevin (verificadorDe f)) (costo j) := by
  have := cerrado_en_O (V := verificadorDe f) (i := encodeCode j) (t := costo j) (correcto_de_computa hj)
  exact ⟨this.2.2.1, this.2.2.2⟩

/-- **La frontera.** Hay una función computable `f` (la de Blum, `BlumExiste.blum`) tal que:
* **con su verificador** como caja, la búsqueda universal está en `O(costo j)` para todo programa `j` de `f`: el corte
  de la búsqueda tiene mínimo;
* **sin verificador**, decidiendo `f` con un programa, no hay mínimo: ningún programa de `f` está en `O(costo j)` para
  todo programa `j` de `f` (`sin_optimo`).

Las dos medidas son distintas (rondas contra `pasos`), y esa es la frontera: lo que separa los dos lados es que el
verificador de `f` se evalúa gratis, aunque cueste tanto como calcular `f`. -/
theorem frontera : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧
    (∀ j, Computa j f → EsO (costoLevin (verificadorDe f)) (costo j)) ∧
    (∀ j, Computa j f → EsO (fun x => costoCerrado ⟨verificadorDe f, x⟩) (costo j)) ∧
    ¬ ∃ i, Computa i f ∧ ∀ j, Computa j f → EsO (costo i) (costo j) := by
  obtain ⟨f, h1, h2, h3⟩ := BlumExiste.blum BlumExiste.computable_lineal
  exact ⟨f, h1, h2, fun j hj => (con_verificador_hay_minimo hj).2, fun j hj => (con_verificador_hay_minimo hj).1,
    sin_optimo (fun _ _ => le_rfl) h3⟩

/-- **La escalera de Blum, vista desde el universo cerrado.** Para la `f` de `existe_irracional`, cada peldaño `s k`
da la cota `costoCerrado ≤ 2^(código de s k) · costo (s k)`, y esas constantes no están acotadas: la complejidad que
la escalera no tiene en el exponente la tiene en la constante. -/
theorem escalera_de_blum : ∃ f : ℕ → ℕ, Computable f ∧ ∃ s : ℕ → Code, (∀ k, Computa (s k) f) ∧
    (∀ k, costo (s (k + 1)) ∈ o (costo (s k))) ∧
    (∀ k x, costoCerrado ⟨verificadorDe f, x⟩ ≤ 2 ^ encodeCode (s k) * costo (s k) x) ∧
    ∀ M, ∃ k, M < 2 ^ encodeCode (s k) := by
  obtain ⟨f, -, hf, s, hs, ho, hd⟩ := existe_irracional
  refine ⟨f, hf, s, hs, ho, fun k x => costoCerrado_le (correcto_de_computa (hs k) x), fun M => ?_⟩
  obtain ⟨k, hk⟩ := hd M
  exact ⟨k, lt_trans hk Nat.lt_two_pow_self⟩

/-! ## 7. Controles de que las hipótesis importan -/

/-- **Sin el factor `2^i` la cota es falsa.** En `uUno` hay un proceso correcto cuyo presupuesto `k` queda por debajo del
costo cerrado: el costo cerrado no es «el mínimo presupuesto»; escribir el programa se paga. -/
theorem sin_factor_falla (x : ℕ) : ¬ ∀ p, Correcto (uUno x) p → costoCerrado (uUno x) ≤ p.k := by
  intro h
  obtain ⟨p, hp⟩ := uUno_resoluble x
  have hne : {c | ∃ p, Correcto (uUno x) p ∧ c = p.k}.Nonempty := ⟨_, p, hp, rfl⟩
  obtain ⟨q, hq, he⟩ := Nat.sInf_mem hne
  have h1 := h q hq
  have h2 := (escribir_cuesta x).2
  unfold costoSinEscribir at h2
  omega

/-- **Sin verificador no hay mínimo.** Es falso que toda función computable tenga un programa óptimo salvo una
constante: la `f` de Blum no lo tiene. -/
theorem sin_verificador_no_hay_minimo :
    ¬ ∀ f : ℕ → ℕ, Computable f → ∃ i, Computa i f ∧ ∀ j, Computa j f → EsO (costo i) (costo j) := by
  intro h
  obtain ⟨f, -, hf, -, -, hno⟩ := frontera
  exact hno (h f hf)

/-- La búsqueda **sin verificar**: entrega lo primero que cualquier programa responda. -/
def buscarSinVerificar (x T : ℕ) : Option ℕ :=
  (List.range (T + 1)).findSome? fun t => (List.range (t + 1)).findSome? fun i => correr i (2 ^ (t - i)) x

/-- **Sin verificar, la búsqueda entrega basura.** Sobre la entrada `0`, el programa `0` responde `0` en la primera
ronda, y `vUno` no lo acepta. -/
theorem sin_verificar_falla : buscarSinVerificar 0 0 = some 0 ∧ vUno 0 0 = false := by
  have h : evaln (0 + 1) Code.zero 0 = some 0 := by simp [evaln]
  refine ⟨?_, rfl⟩
  simpa [buscarSinVerificar, correr, ofNatCode] using h

end UniversoCerrado
end Tiempo
end Sagitta.Map
