import Sagitta.Map.ConservacionTrabajo
import Sagitta.Map.LeerCuesta

/-!
# El plano de la caja: tamaño de la caja contra el costo de la primera corrida

Sobre `ConservacionTrabajo` (el llenado y la conservación del trabajo) y `LeerCuesta` (lo sensible se lee).

## El plano

Eje x: el tamaño `s` de la caja, en bits (pasarla cuesta copiarla). Eje y: el costo `t` de **la primera corrida
después de generar la caja**, sin amortizar entre corridas ni instancias. El modelo es de caja negra: el dato es un
oráculo `f : α → Bool` con `α` finito (las hojas). Una corrida es un árbol de preguntas `Pregunta (Fin s ⊕ α)` sobre el
oráculo combinado `Sum.elim caja f`: cada pregunta lee un bit de la caja (`inl`) o una hoja (`inr`) y cuesta 1. Con
`fijarCaja` la corrida se vuelve un `Pregunta α` que solo cuenta las lecturas de `f` (`corre_fijarCaja`,
`costo_fijarCaja_le`).

## Qué se prueba

1. **El colapso** (control obligatorio). Si la caja es una función cualquiera de `f`, gratis, y conoce la consulta, el
   plano es trivial.
   * «¿Hay una hoja buena?»: `s = 1` y una lectura (`colapso_hay`).
   * Encontrar una solución entre las `2^N` hojas `Fin N → Bool` (`card_hojas`): `s = N` bits y `N` lecturas
     (`colapso_hallar`). Para salidas que no son un bit va `Lectura`, un árbol de preguntas con salida en cualquier tipo.
   * Eso rompe la conservación (`colapso_rompe`): con `N ≥ 1`, una lectura y nada contado al generar no llegan a
     `|α| = 2^N`.
2. **Con la generación contada.** La generación es un `Llenado α (Fin s → Bool)` de costo `g`; la primera corrida
   cuesta `t`. Entonces `g + t ≥ |α|` para todo `s` (`plano_generacion`), y aun contando solo las lecturas de `f`
   de la corrida (`generacion_contada_f`). La caja no baja la recta: el enunciado no depende de `s`.
   Controles: los puntos `(g, t) = (|α|, 1)` (`punto_todo_generacion`) y `(0, |α|)` (`punto_todo_corrida`) se
   alcanzan, el segundo con igualdad.
3. **La caja estática: no conoce la consulta.** Las hojas son `ι × η`: `|ι| = M` subárboles (los prefijos del nivel
   `N − k`, `M = 2^(N−k)`) de `|η| = L` hojas cada uno (`L = 2^k`). La caja es **cualquier** función de `f` con `s`
   bits, sin costo y sin saber la consulta. Después llega una consulta `q : ι`, «¿hay una hoja buena debajo de `q`?»
   (`hayDebajo`), elegida por un adversario. La corrida `R q` responde bien para todo `f` y todo `q` (`Responde`) y
   hace a lo sumo `t` lecturas, de la caja o de `f`, sea cual sea el contenido de la caja (`Lee`: profundidad `≤ t`).
   * **La cota inferior** (`cota_caja_estatica`), la forma exacta que quedó:

         (M − s) · L ≤ 2^s · M · t        (resta truncada de ℕ)

     o sea `s ≥ M · (1 − 2^s · t / L)`. La prueba: `Z` son las hojas que lee alguna corrida (de las `M` consultas y los
     `2^s` contenidos de caja) con `f = 0`; son a lo sumo `2^s · M · t` (`card_leidasCero`). Un subárbol con todas
     sus hojas en `Z` es *saturado*; hay a lo sumo `|Z| / L`. En cada subárbol no saturado queda un hueco
     (`hueco`), y con los `1` puestos solo en huecos (`conUnos`) ninguna corrida ve un `1`: responde lo que respondería
     con `f = 0` y la caja que le tocó. Entonces la caja sola tiene que codificar qué subárboles no saturados están
     llenos: `2^(no saturados) ≤ 2^s` (`no_saturados_le`). Las funciones usadas tienen a lo sumo un `1` por subárbol,
     como sugería la pista.
   * **No es la forma producto `s ≥ M · (1 − t/L)`**: queda el factor `2^s`, porque el adversario elige los huecos
     antes de saber qué caja tocará y tiene que esquivar las lecturas de los `2^s` contenidos posibles. Con `s = 0` el
     factor es 1 y la cota es exacta: `t ≥ L` (`sin_caja`). Con `t = 1` y `L > M · 2^(M−1)` obliga a `s = M`, que es
     exacta también (control concreto `una_lectura_pide_todo`, `M = 2`, `L = 16`). En el medio es débil.
   * **La forma extrema** (`sin_leer_la_caja`): una corrida que no lee la caja y decide un subárbol lee, con `f = 0`,
     sus `L` hojas, sea cual sea `s`. Con `t < L` es imposible (`sin_leer_la_caja_imposible`).
   * **Los extremos se alcanzan** (controles de que la cota no es vacía): guardar el OR de cada subárbol da `s = M`,
     `t = 1` (`guardar_los_or`); no guardar nada da `s = 0`, `t = L` (`no_guardar_nada`), y ahí la cota vale con
     igualdad (`no_guardar_nada_justo`).

## La lectura

Medir la primera corrida tiene sentido solo de dos maneras: **o se cuenta la generación** (y entonces la conservación
del trabajo da `g + t ≥ |α|`, con cualquier `s`), **o se le esconde la consulta a la caja** (y entonces la caja paga en
bits lo que la corrida no lee). Si la caja es gratis y conoce la consulta, el plano colapsa a `(1, 1)` o `(N, N)`.

## Lo que NO se prueba

* **Es caja negra**: el argumento del adversario relativiza (Baker, Gill y Solovay, 1975; de memoria), así que no dice
  nada de una entrada dada por su texto, que se lee sin preguntar.
* **Con la generación gratis es no uniforme**: la caja de la parte 3 es cualquier función de `f`, un consejo; la cota
  dice cuántos bits necesita el consejo, no cuánto cuesta producirlo.
* **No toca P contra NP.**
* La forma producto `s ≥ M · (1 − t/L)` queda sin probar (ni refutar); la que quedó tiene el factor `2^s`.
* Contexto, **de memoria y sin verificar**: esta es la pregunta de las cotas de sondeo de celdas para estructuras
  estáticas (P. B. Miltersen; M. Pătrașcu y M. Thorup), y superar cotas logarítmicas en estructuras estáticas daría
  rigidez de matrices (Z. Dvir, A. Golovnev y O. Weinstein, 2019). Nada de eso se usa ni se cita como verificado.
-/

namespace Sagitta.Map.Tiempo.PlanoCaja

open Pregunta
open Sagitta.Map.Tiempo.ConservacionTrabajo
open Sagitta.Map.Tiempo.ConservacionTrabajo.Llenado

/-! ## La corrida con caja: leer bits de la caja o de `f` -/

section Fijar

variable {β α : Type}

/-- **Fijar la caja**: con el contenido `c` de la caja en la mano, la corrida se vuelve un `Pregunta α`. Las lecturas
de la caja se responden con `c` y no se cuentan; las de `f` quedan como preguntas. -/
def fijarCaja (c : β → Bool) : Pregunta (β ⊕ α) → Pregunta α
  | .resp b => .resp b
  | .preg (.inl j) sig => fijarCaja c (sig (c j))
  | .preg (.inr i) sig => .preg i fun b => fijarCaja c (sig b)

theorem corre_fijarCaja (c : β → Bool) (f : α → Bool) :
    ∀ r : Pregunta (β ⊕ α), corre (fijarCaja c r) f = corre r (Sum.elim c f)
  | .resp _ => rfl
  | .preg (.inl j) sig => by
    simp only [fijarCaja, corre, Sum.elim_inl]
    exact corre_fijarCaja c f (sig (c j))
  | .preg (.inr i) sig => by
    simp only [fijarCaja, corre, Sum.elim_inr]
    exact corre_fijarCaja c f (sig (f i))

/-- **Las lecturas de `f` no pasan de las lecturas totales.** -/
theorem costo_fijarCaja_le (c : β → Bool) (f : α → Bool) :
    ∀ r : Pregunta (β ⊕ α), costo (fijarCaja c r) f ≤ costo r (Sum.elim c f)
  | .resp _ => le_refl _
  | .preg (.inl j) sig => by
    have := costo_fijarCaja_le c f (sig (c j))
    simp only [costo, vistos, fijarCaja, Sum.elim_inl, List.length_cons] at this ⊢
    omega
  | .preg (.inr i) sig => by
    have := costo_fijarCaja_le c f (sig (f i))
    simp only [costo, vistos, fijarCaja, Sum.elim_inr, List.length_cons] at this ⊢
    omega

end Fijar

/-! ## Árboles de preguntas con salida en cualquier tipo -/

/-- **Una lectura**: un árbol de preguntas a `g : ι → Bool` cuya salida está en `γ` (no solo un bit). -/
inductive Lectura (ι γ : Type) : Type
  | fin (x : γ) : Lectura ι γ
  | preg (i : ι) (sig : Bool → Lectura ι γ) : Lectura ι γ

namespace Lectura

variable {ι γ : Type}

/-- La salida con el oráculo `g`. -/
def salida : Lectura ι γ → (ι → Bool) → γ
  | fin x, _ => x
  | preg i sig, g => salida (sig (g i)) g

/-- Las posiciones leídas con el oráculo `g`. -/
def leidas : Lectura ι γ → (ι → Bool) → List ι
  | fin _, _ => []
  | preg i sig, g => i :: leidas (sig (g i)) g

/-- **El costo**: cuántas lecturas. -/
def costoL (t : Lectura ι γ) (g : ι → Bool) : ℕ := (leidas t g).length

end Lectura

open Lectura

/-- **Leer una lista de posiciones** y entregar `k` de lo leído. -/
def leerLista {ι γ : Type} : List ι → (List Bool → γ) → Lectura ι γ
  | [], k => .fin (k [])
  | i :: l, k => .preg i fun b => leerLista l fun bs => k (b :: bs)

theorem salida_leerLista {ι γ : Type} (g : ι → Bool) :
    ∀ (l : List ι) (k : List Bool → γ), salida (leerLista l k) g = k (l.map g)
  | [], _ => rfl
  | i :: l, k => by
    simp only [leerLista, salida, List.map_cons]
    exact salida_leerLista g l _

theorem costoL_leerLista {ι γ : Type} (g : ι → Bool) :
    ∀ (l : List ι) (k : List Bool → γ), costoL (leerLista l k) g = l.length
  | [], _ => rfl
  | i :: l, k => by
    have := costoL_leerLista g l (fun bs => k (g i :: bs))
    simp only [costoL, leerLista, leidas, List.length_cons] at this ⊢
    omega

/-! ## Meta 1: el colapso -/

section Colapso

variable {α : Type}

/-- **La caja que ya sabe la respuesta**: un bit, «hay una hoja buena», armado mirando `f` entero sin contar. -/
def cajaHay [Fintype α] (f : α → Bool) : Fin 1 → Bool := fun _ => decide (∃ i, f i = true)

/-- **La corrida que lee el bit 0 de la caja** y lo devuelve. -/
def leerUno : Pregunta (Fin 1 ⊕ α) := .preg (.inl 0) fun b => .resp b

theorem costo_leerUno (g : Fin 1 ⊕ α → Bool) : costo (leerUno (α := α)) g = 1 := rfl

/-- **El colapso, «¿hay una hoja buena?»**: con la caja gratis y sabiendo la consulta, `s = 1` y una lectura. -/
theorem colapso_hay [Fintype α] (f : α → Bool) :
    (corre leerUno (Sum.elim (cajaHay f) f) = true ↔ ∃ i, f i = true) ∧
      costo leerUno (Sum.elim (cajaHay f) f) = 1 := by
  refine ⟨?_, costo_leerUno _⟩
  simp [leerUno, cajaHay, corre]

/-- Las hojas del árbol de `N` elecciones son `2^N`. -/
theorem card_hojas (N : ℕ) : Fintype.card (Fin N → Bool) = 2 ^ N := by simp

/-- **La caja que ya tiene una solución**: `N` bits, una hoja buena si la hay. -/
noncomputable def cajaSol {N : ℕ} (f : (Fin N → Bool) → Bool) : Fin N → Bool :=
  if h : ∃ v, f v = true then Classical.choose h else fun _ => false

/-- **La corrida que copia la caja**: lee los `N` bits y los entrega como hoja. -/
def leerSol (N : ℕ) : Lectura (Fin N ⊕ (Fin N → Bool)) (Fin N → Bool) :=
  leerLista ((List.finRange N).map Sum.inl) fun bs j => bs.getD j false

theorem salida_leerSol {N : ℕ} (c : Fin N → Bool) (f : (Fin N → Bool) → Bool) :
    salida (leerSol N) (Sum.elim c f) = c := by
  rw [leerSol, salida_leerLista]
  funext j
  simp [List.getD_eq_getElem?_getD, List.map_map]

theorem costoL_leerSol {N : ℕ} (g : Fin N ⊕ (Fin N → Bool) → Bool) : costoL (leerSol N) g = N := by
  rw [leerSol, costoL_leerLista]
  simp

/-- **El colapso, «encontrá una solución»**: con la caja gratis de `N` bits, `N` lecturas encuentran una hoja buena
entre las `2^N`, si la hay. -/
theorem colapso_hallar {N : ℕ} (f : (Fin N → Bool) → Bool) (h : ∃ v, f v = true) :
    f (salida (leerSol N) (Sum.elim (cajaSol f) f)) = true ∧ costoL (leerSol N) (Sum.elim (cajaSol f) f) = N := by
  refine ⟨?_, costoL_leerSol _⟩
  rw [salida_leerSol, cajaSol]
  split
  · exact Classical.choose_spec ‹_›
  · contradiction

/-- **El colapso rompe la conservación**: con `N ≥ 1`, nada contado al generar más una lectura no llega a
`|α| = 2^N`. Con la caja gratis, la primera corrida no mide nada. -/
theorem colapso_rompe (N : ℕ) (hN : 1 ≤ N) :
    0 + costo (leerUno (α := Fin N → Bool)) (Sum.elim (cajaHay (fun _ : Fin N → Bool => false)) (fun _ => false)) <
      Fintype.card (Fin N → Bool) := by
  rw [costo_leerUno, card_hojas]
  have : 2 ^ 1 ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  omega

end Colapso

/-! ## Meta 2: con la generación contada -/

section Generacion

variable {β α : Type}

/-- **Generar y correr, contando solo las lecturas de `f` de la corrida.** Si la generación es un `Llenado` que produce
la caja y la primera corrida, con esa caja, decide «¿hay una hoja buena?», las preguntas de la generación más las
lecturas de `f` de la corrida son al menos `|α|`, con el oráculo todo `false`. -/
theorem generacion_contada_f [Fintype α] (L : Llenado α (β → Bool)) (R : Pregunta (β ⊕ α))
    (h : ∀ f, corre R (Sum.elim (tablaDe L f) f) = true ↔ ∃ i, f i = true) :
    Fintype.card α ≤ costoLl L (fun _ => false) +
      costo (fijarCaja (tablaDe L (fun _ => false)) R) (fun _ => false) := by
  have hdec : DecideExiste (encadenar L fun T => fijarCaja T R) := by
    intro f
    rw [corre_encadenar, corre_fijarCaja]
    exact h f
  exact trabajo_se_conserva L _ hdec

/-- **El plano con la generación contada**: para todo `s`, generación `g` más primera corrida `t` (lecturas de la caja
y de `f`) es al menos `|α|`. La recta `g + t = |α|` no depende de `s`. -/
theorem plano_generacion [Fintype α] (s : ℕ) (L : Llenado α (Fin s → Bool)) (R : Pregunta (Fin s ⊕ α))
    (h : ∀ f, corre R (Sum.elim (tablaDe L f) f) = true ↔ ∃ i, f i = true) :
    Fintype.card α ≤ costoLl L (fun _ => false) +
      costo R (Sum.elim (tablaDe L (fun _ => false)) (fun _ => false)) :=
  (generacion_contada_f L R h).trans (Nat.add_le_add_left (costo_fijarCaja_le _ _ R) _)

/-- **Generar todo**: barrer las hojas y guardar la respuesta en un bit. -/
noncomputable def generarTodo [Fintype α] : Llenado α (Fin 1 → Bool) :=
  deP (fun b _ => b) (barrer (Finset.univ : Finset α).toList)

/-- **Control, el punto `(g, t) = (|α|, 1)`**: generar todo y leer un bit. -/
theorem punto_todo_generacion [Fintype α] :
    (∀ f, corre leerUno (Sum.elim (tablaDe (generarTodo (α := α)) f) f) = true ↔ ∃ i, f i = true) ∧
      costoLl (generarTodo (α := α)) (fun _ => false) = Fintype.card α ∧
      costo (leerUno (α := α)) (Sum.elim (tablaDe (generarTodo (α := α)) (fun _ => false)) (fun _ => false)) = 1 := by
  classical
  refine ⟨fun f => ?_, ?_, costo_leerUno _⟩
  · simp only [leerUno, corre, Sum.elim_inl, generarTodo, tablaDe_deP]
    exact barrer_alcanza.1 f
  · rw [generarTodo, costoLl_deP]
    have hle := (barrer_alcanza (α := α)).2 (fun _ => false)
    have hge := costo_adversario _ (barrer_alcanza (α := α)).1
    omega

/-- **La corrida que barre** las hojas, sin mirar la caja (vacía). -/
noncomputable def corridaBarrer [Fintype α] : Pregunta (Fin 0 ⊕ α) :=
  barrer ((Finset.univ : Finset α).toList.map Sum.inr)

theorem corre_barrer_inr {β : Type} (c : β → Bool) (f : α → Bool) (l : List α) :
    corre (barrer (l.map Sum.inr)) (Sum.elim c f) = true ↔ ∃ i ∈ l, f i = true := by
  rw [corre_barrer]
  simp

/-- La generación que no pregunta nada y deja la caja vacía. -/
def generarNada : Llenado α (Fin 0 → Bool) := .fin fun _ => false

/-- **Control, el punto `(g, t) = (0, |α|)`**: no generar nada y barrer. Se alcanza con igualdad. -/
theorem punto_todo_corrida [Fintype α] :
    (∀ f, corre corridaBarrer (Sum.elim (tablaDe (generarNada (α := α)) f) f) = true ↔ ∃ i, f i = true) ∧
      costoLl (generarNada (α := α)) (fun _ => false) = 0 ∧
      costo (corridaBarrer (α := α)) (Sum.elim (tablaDe (generarNada (α := α)) (fun _ => false)) (fun _ => false)) =
        Fintype.card α := by
  have hdec : ∀ f, corre corridaBarrer (Sum.elim (tablaDe (generarNada (α := α)) f) f) = true ↔
      ∃ i, f i = true := fun f => by
    rw [corridaBarrer, corre_barrer_inr]
    simp
  refine ⟨hdec, rfl, ?_⟩
  have hge := plano_generacion 0 generarNada corridaBarrer hdec
  have hle := costo_barrer (Sum.elim (tablaDe (generarNada (α := α)) (fun _ => false)) (fun _ => false))
    ((Finset.univ : Finset α).toList.map Sum.inr)
  simp only [List.length_map, Finset.length_toList, Finset.card_univ] at hle
  rw [corridaBarrer]
  have : costoLl (generarNada (α := α)) (fun _ => false) = 0 := rfl
  rw [this, zero_add] at hge
  exact le_antisymm hle hge

end Generacion

/-! ## Meta 3: la caja estática, que no conoce la consulta -/

section Estatica

variable {ι η β : Type}

/-- **¿Hay una hoja buena debajo de `q`?** Las hojas son `ι × η`: el subárbol `q` son las `(q, y)`. -/
def hayDebajo [Fintype η] (f : ι × η → Bool) (q : ι) : Bool := decide (∃ y, f (q, y) = true)

/-- **La corrida responde**: para todo `f` y toda consulta `q`, con la caja `caja f`, la corrida `R q` dice si hay una
hoja buena debajo de `q`. La caja es cualquier función de `f` y **no conoce `q`**. -/
def Responde [Fintype η] (caja : (ι × η → Bool) → (β → Bool)) (R : ι → Pregunta (β ⊕ (ι × η))) : Prop :=
  ∀ f q, corre (R q) (Sum.elim (caja f) f) = hayDebajo f q

/-- **La corrida lee a lo sumo `t`**, sea lo que sea que diga la caja y el oráculo (profundidad `≤ t`). -/
def Lee {α : Type} (R : ι → Pregunta (β ⊕ α)) (t : ℕ) : Prop := ∀ q g, costo (R q) g ≤ t

variable [Fintype ι] [Fintype η]

open Classical in
/-- **Las hojas que lee alguna corrida con `f = 0`**: de las `M` consultas y los `2^s` contenidos de caja. -/
noncomputable def leidasCero {s : ℕ} (R : ι → Pregunta (Fin s ⊕ (ι × η))) : Finset (ι × η) :=
  Finset.univ.biUnion fun c : Fin s → Bool =>
    Finset.univ.biUnion fun q : ι => (vistos (fijarCaja c (R q)) (fun _ => false)).toFinset

omit [Fintype η] in
theorem card_leidasCero {s t : ℕ} (R : ι → Pregunta (Fin s ⊕ (ι × η))) (ht : Lee R t) :
    (leidasCero R).card ≤ 2 ^ s * Fintype.card ι * t := by
  classical
  unfold leidasCero
  calc _ ≤ ∑ c : Fin s → Bool, (Finset.univ.biUnion fun q : ι =>
          (vistos (fijarCaja c (R q)) (fun _ => false)).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ c : Fin s → Bool, ∑ q : ι, (vistos (fijarCaja c (R q)) (fun _ => false)).toFinset.card :=
        Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
    _ ≤ ∑ _c : Fin s → Bool, ∑ _q : ι, t :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun q _ =>
          (List.toFinset_card_le _).trans ((costo_fijarCaja_le c _ (R q)).trans (ht q _))
    _ = 2 ^ s * Fintype.card ι * t := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          smul_eq_mul]
        ring

open Classical in
/-- **Los subárboles saturados**: todas sus hojas están en `Z`. -/
noncomputable def saturados (Z : Finset (ι × η)) : Finset ι := Finset.univ.filter fun q => ∀ y, (q, y) ∈ Z

open Classical in
/-- **Los no saturados**: les queda un hueco. -/
noncomputable def noSaturados (Z : Finset (ι × η)) : Finset ι := Finset.univ.filter fun q => ¬ ∀ y, (q, y) ∈ Z

theorem saturados_mul_le (Z : Finset (ι × η)) : (saturados Z).card * Fintype.card η ≤ Z.card := by
  classical
  have hsub : saturados Z ×ˢ (Finset.univ : Finset η) ⊆ Z := by
    intro p hp
    rw [Finset.mem_product] at hp
    have := (Finset.mem_filter.1 hp.1).2 p.2
    simpa using this
  have := Finset.card_le_card hsub
  rwa [Finset.card_product, Finset.card_univ] at this

theorem saturados_add (Z : Finset (ι × η)) : (saturados Z).card + (noSaturados Z).card = Fintype.card ι := by
  classical
  exact Finset.card_filter_add_card_filter_not _

open Classical in
/-- **El hueco** de un subárbol: una hoja fuera de `Z`, si la hay. -/
noncomputable def hueco (Z : Finset (ι × η)) (q : ι) : Option η :=
  if h : ∃ y, (q, y) ∉ Z then some (Classical.choose h) else none

omit [Fintype ι] in
theorem hueco_fuera {Z : Finset (ι × η)} {q : ι} {y : η} (h : hueco Z q = some y) : (q, y) ∉ Z := by
  unfold hueco at h
  split at h
  · rename_i hh
    cases h
    exact Classical.choose_spec hh
  · cases h

theorem hueco_some {Z : Finset (ι × η)} {q : ι} (h : q ∈ noSaturados Z) : ∃ y, hueco Z q = some y := by
  classical
  have hq : ∃ y, (q, y) ∉ Z := by
    simpa [noSaturados] using h
  unfold hueco
  split
  · exact ⟨_, rfl⟩
  · contradiction

open Classical in
/-- **Los unos en los huecos**: un `1` en el hueco de cada subárbol de `S`, y nada más. A lo sumo un `1` por
subárbol. -/
noncomputable def conUnos (Z : Finset (ι × η)) (S : Finset ι) (i : ι × η) : Bool :=
  decide (i.1 ∈ S ∧ hueco Z i.1 = some i.2)

omit [Fintype ι] in
theorem conUnos_en_Z {Z : Finset (ι × η)} (S : Finset ι) {i : ι × η} (hi : i ∈ Z) : conUnos Z S i = false := by
  unfold conUnos
  rw [decide_eq_false_iff_not]
  rintro ⟨-, h⟩
  exact hueco_fuera h hi

theorem hayDebajo_conUnos {Z : Finset (ι × η)} (S : Finset ι) {q : ι} (hq : q ∈ noSaturados Z) :
    hayDebajo (conUnos Z S) q = true ↔ q ∈ S := by
  obtain ⟨y, hy⟩ := hueco_some hq
  unfold hayDebajo conUnos
  simp only [decide_eq_true_eq, hy, Option.some.injEq]
  constructor
  · rintro ⟨_, h, _⟩; exact h
  · intro h; exact ⟨y, h, rfl⟩

/-- **Ninguna corrida ve un `1` puesto en un hueco**: con la caja que sea, responde lo mismo que con `f = 0`. -/
theorem corre_conUnos {s : ℕ} (R : ι → Pregunta (Fin s ⊕ (ι × η))) (S : Finset ι) (c : Fin s → Bool) (q : ι) :
    corre (fijarCaja c (R q)) (conUnos (leidasCero R) S) = corre (fijarCaja c (R q)) (fun _ => false) := by
  refine (corre_congr _ _ _ fun i hi => ?_).symm
  have hZ : i ∈ leidasCero R := by
    unfold leidasCero
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset]
    exact ⟨c, q, hi⟩
  rw [conUnos_en_Z S hZ]

/-- **La caja codifica los subárboles no saturados**: `2^(no saturados) ≤ 2^s`, o sea, a lo sumo `s` no saturados. -/
theorem no_saturados_le {s : ℕ} (caja : (ι × η → Bool) → (Fin s → Bool)) (R : ι → Pregunta (Fin s ⊕ (ι × η)))
    (hR : Responde caja R) : (noSaturados (leidasCero R)).card ≤ s := by
  classical
  let U := noSaturados (leidasCero R)
  have hinj : Set.InjOn (fun S => caja (conUnos (leidasCero R) S)) (U.powerset : Set (Finset ι)) := by
    intro S hS T hT hST
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hS hT
    have key : ∀ q ∈ U, (q ∈ S ↔ q ∈ T) := by
      intro q hq
      have e : hayDebajo (conUnos (leidasCero R) S) q = hayDebajo (conUnos (leidasCero R) T) q := by
        rw [← hR, ← hR, ← corre_fijarCaja, ← corre_fijarCaja, corre_conUnos, corre_conUnos]
        simp only at hST
        rw [hST]
      rw [← hayDebajo_conUnos S hq, ← hayDebajo_conUnos T hq, e]
    ext q
    by_cases hq : q ∈ U
    · exact key q hq
    · exact ⟨fun h => absurd (hS h) hq, fun h => absurd (hT h) hq⟩
  have hcard := Finset.card_le_card_of_injOn (fun S => caja (conUnos (leidasCero R) S))
    (t := (Finset.univ : Finset (Fin s → Bool))) (fun _ _ => by simp) hinj
  rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard

/-- **La cota de la caja estática.** Si la caja (cualquier función de `f`, de `s` bits, sin conocer la consulta) y la
corrida (a lo sumo `t` lecturas) responden «¿hay una hoja buena debajo de `q`?» para todo `f` y todo `q`, entonces

`(M − s) · L ≤ 2^s · M · t`,

con `M = |ι|` subárboles de `L = |η|` hojas. -/
theorem cota_caja_estatica {s t : ℕ} (caja : (ι × η → Bool) → (Fin s → Bool))
    (R : ι → Pregunta (Fin s ⊕ (ι × η))) (hR : Responde caja R) (ht : Lee R t) :
    (Fintype.card ι - s) * Fintype.card η ≤ 2 ^ s * Fintype.card ι * t := by
  have h1 := card_leidasCero R ht
  have h2 := saturados_mul_le (leidasCero R)
  have h3 := saturados_add (leidasCero R)
  have h4 := no_saturados_le caja R hR
  have h5 : Fintype.card ι - s ≤ (saturados (leidasCero R)).card := by omega
  calc (Fintype.card ι - s) * Fintype.card η ≤ (saturados (leidasCero R)).card * Fintype.card η :=
        Nat.mul_le_mul_right _ h5
    _ ≤ _ := h2.trans h1

/-- **Sin caja, la cota es exacta**: con `s = 0` y al menos un subárbol, `t ≥ L`. -/
theorem sin_caja {t : ℕ} (caja : (ι × η → Bool) → (Fin 0 → Bool)) (R : ι → Pregunta (Fin 0 ⊕ (ι × η)))
    (hR : Responde caja R) (ht : Lee R t) (hM : 0 < Fintype.card ι) : Fintype.card η ≤ t := by
  have := cota_caja_estatica caja R hR ht
  simp only [Nat.sub_zero, pow_zero, one_mul] at this
  exact Nat.le_of_mul_le_mul_left this hM

omit [Fintype ι] in
/-- **La forma extrema**: una corrida que no lee la caja (un `Pregunta` sobre las hojas solas) y decide el subárbol `q`
lee, con `f = 0`, las `L` hojas de `q`. -/
theorem sin_leer_la_caja (q : ι) (P : Pregunta (ι × η)) (hP : ∀ f, corre P f = hayDebajo f q) :
    Fintype.card η ≤ costo P (fun _ => false) := by
  classical
  have hc : Calcula P (fun f => hayDebajo f q) := hP
  have hsub : (Finset.univ : Finset η).image (fun y => (q, y)) ⊆ (vistos P (fun _ => false)).toFinset := by
    intro i hi
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hi
    refine List.mem_toFinset.2 (lee_lo_sensible hc ?_)
    unfold Sensible hayDebajo
    simp only [Bool.not_false, ne_eq, decide_eq_decide]
    intro h
    obtain ⟨z, hz⟩ := h.1 ⟨y, by simp⟩
    simp at hz
  have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  rwa [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2), Finset.card_univ] at this

omit [Fintype ι] in
/-- **Sin leer la caja, con `t < L`, imposible**, sea cual sea `s`. -/
theorem sin_leer_la_caja_imposible (q : ι) (t : ℕ) (ht : t < Fintype.card η) :
    ¬ ∃ P : Pregunta (ι × η), (∀ f, corre P f = hayDebajo f q) ∧ ∀ f, costo P f ≤ t := by
  rintro ⟨P, hP, hc⟩
  have := sin_leer_la_caja q P hP
  have := hc (fun _ => false)
  omega

/-! ### Los extremos se alcanzan -/

/-- **Guardar el OR de cada subárbol**: `s = M` bits, el bit `j` dice si hay hoja buena en el subárbol `j`. -/
noncomputable def cajaOr (f : ι × η → Bool) : Fin (Fintype.card ι) → Bool :=
  fun j => hayDebajo f ((Fintype.equivFin ι).symm j)

/-- **La corrida lee el bit de su subárbol.** -/
noncomputable def leerOr (q : ι) : Pregunta (Fin (Fintype.card ι) ⊕ (ι × η)) :=
  .preg (.inl (Fintype.equivFin ι q)) fun b => .resp b

/-- **Control: `s = M`, `t = 1` se alcanza.** -/
theorem guardar_los_or : Responde (cajaOr (ι := ι) (η := η)) leerOr ∧ Lee (leerOr (ι := ι) (η := η)) 1 := by
  refine ⟨fun f q => ?_, fun q g => le_of_eq rfl⟩
  simp [leerOr, corre, cajaOr]

/-- **No guardar nada**: la corrida barre las `L` hojas de su subárbol. -/
noncomputable def barrerDebajo (q : ι) : Pregunta (Fin 0 ⊕ (ι × η)) :=
  barrer ((Finset.univ : Finset η).toList.map fun y => Sum.inr (q, y))

omit [Fintype ι] in
/-- **Control: `s = 0`, `t = L` se alcanza.** -/
theorem no_guardar_nada :
    Responde (fun _ _ => false) (barrerDebajo (ι := ι) (η := η)) ∧
      Lee (barrerDebajo (ι := ι) (η := η)) (Fintype.card η) := by
  refine ⟨fun f q => ?_, fun q g => ?_⟩
  · rw [barrerDebajo]
    have := corre_barrer (Sum.elim (fun _ : Fin 0 => false) f)
      ((Finset.univ : Finset η).toList.map fun y => Sum.inr (q, y))
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at this
    unfold hayDebajo
    cases h : corre (barrer ((Finset.univ : Finset η).toList.map fun y => Sum.inr (q, y)))
        (Sum.elim (fun _ : Fin 0 => false) f)
    · symm
      rw [decide_eq_false_iff_not]
      rintro ⟨y, hy⟩
      have := this.2 ⟨_, ⟨y, rfl⟩, by simpa using hy⟩
      rw [h] at this
      exact Bool.false_ne_true this
    · symm
      rw [decide_eq_true_iff]
      obtain ⟨_, ⟨y, rfl⟩, hy⟩ := this.1 h
      exact ⟨y, by simpa using hy⟩
  · have := costo_barrer g ((Finset.univ : Finset η).toList.map fun y => Sum.inr (q, y))
    simpa [barrerDebajo] using this

/-- **Y ahí la cota vale con igualdad**: `(M − 0) · L = 2^0 · M · L`. -/
theorem no_guardar_nada_justo :
    (Fintype.card ι - 0) * Fintype.card η = 2 ^ 0 * Fintype.card ι * Fintype.card η := by
  simp

end Estatica

/-- **Control concreto: con una lectura, la caja tiene que guardarlo todo.** Con `M = 2` subárboles de `L = 16`
hojas (`N = 5`, `k = 4`) y `t = 1`, la cota obliga a `s ≥ 2 = M`, y `guardar_los_or` lo alcanza. -/
theorem una_lectura_pide_todo {s : ℕ} (caja : (Fin 2 × Fin 16 → Bool) → (Fin s → Bool))
    (R : Fin 2 → Pregunta (Fin s ⊕ (Fin 2 × Fin 16))) (hR : Responde caja R) (ht : Lee R 1) : 2 ≤ s := by
  have h := cota_caja_estatica caja R hR ht
  simp only [Fintype.card_fin, mul_one] at h
  rcases Nat.lt_or_ge s 2 with hs | hs
  · rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> norm_num at h
  · exact hs

end Sagitta.Map.Tiempo.PlanoCaja
