import Sagitta.Map.CuboCostos

/-!
# El no determinismo en el cubo

La pregunta es de José (25 nov 2026): el tiempo imaginario, el no determinismo, ¿le agrega un cuarto eje al cubo de
costos (`CuboCostos`), un teseracto, o se conserva la dimensión? La respuesta: **se conserva**. Adivinar `w` bits es
escribirlos antes de correr, o sea más descripción.

## 1. Adivinar al principio es citar

Un resolvedor no determinista elige uno de `|G| ≤ 2^w` comienzos (autómata y estado inicial) y resuelve si **alguna**
elección devuelve la solución, verificada (`ResuelveND`). Es exactamente un resolvedor determinista con la adivinanza
pegada a la cita, `C × G` (`nd_es_cita`), y al revés una cita de `s + w` bits se parte en `s` de cita y `w` de
adivinanza (`cita_es_nd`). La ley (`ley_cubo_nd`, `ley_cubo_nd_log`):
`N ≤ 2^L · 2^s · 2^w · min (t + 1) 2^(S−1)`, o sea `m ≤ x + w + min (y, e − 1)`. Es exacta
(`cubo_nd_es_region`): con el barrido de `CuboCostos` el borde se alcanza. `w` no es un eje nuevo: entra sumado a `x`.

## 2. Adivinar a mitad de corrida no da más; da menos

Un autómata cuya transición, en los estados que eligen (`elige`), escoge entre dos sucesores según un bit, con a lo
sumo `w` elecciones (`AutomataND`; la sucesión de elecciones es `f : Fin w → Bool`, y pasada la `w`-ésima la elección
es `false`). Se corre fijando la sucesión (`fijar`): es un autómata determinista con estados `σ × List Bool`, el estado
más lo que falta de la sucesión. Ahí está la respuesta a la pregunta de cómo se simula:

* **(a) La simulación camino por camino paga espacio.** Fijar las elecciones al principio da un autómata determinista
  por sucesión, pero sus estados son `σ × (lo que falta)`: el autómata tiene que saber cuántas elecciones lleva. Ese
  contador es un **reloj** de las elecciones, como en `mutante_reloj`, y sin él no se puede: `contador_es_reloj` da un
  autómata de **2 estados** y una elección cuya trayectoria pasa dos veces por el mismo estado y sale distinto, así que
  no es la trayectoria de ningún autómata determinista sobre esos 2 estados. Con el contador sí cierra
  (`fijarFin`, `fijarFin_corre`, `corrida_a_principio`): toda corrida con `w` elecciones es una adivinanza al principio
  de `w` bits sobre estados `σ × Fin (w + 1)` (`card_contador`), o sea `⌈log₂(w+1)⌉` bits más de espacio.
* **(b) La ley vale igual, contando directo.** Lo que acota a un autómata no es su trayectoria sino cuántos estados
  devuelven y cuántos consultan, y esos son estados de `σ`, sin el contador. Por cada programa y cita, las soluciones
  halladas (`halladosND`) son a lo sumo
  - `2^w · (t + 1)` (`halladosND_le_tiempo`: una trayectoria del «no» por sucesión);
  - `|σ|` (`halladosND_le_salidas`: cada una la devuelve un estado distinto, **sin** el factor `2^w`);
  - `⌊(|σ| + 2^w)/2⌋` (`halladosND_le_espacio`: cada sucesión compra a lo sumo un «alto» que no consulta).
  De ahí `ley_corrida`: `N ≤ 2^L · 2^s · 2^w · min (t + 1) 2^(S−1)`, la misma ley de 1. **La sospecha se confirma.**
* **Y es más débil que adivinar al principio**: con espacio, `N ≤ 2^L · 2^s · 2^S` sin `w` (`ley_corrida_salidas`).
  Lo adivinado a mitad de corrida hay que guardarlo en estados para usarlo; lo adivinado al principio elige el autómata
  entero y no ocupa estados. El contraejemplo chico (`corrida_menos_que_principio`): con **un** estado, una adivinanza
  al principio de `1` bit y ninguna consulta resuelve `2` candidatos; a mitad de corrida, con un estado, no se resuelven
  `2` con ninguna cantidad de elecciones ni de tiempo.

## 3. La lectura

La rotación de Wick cambia la signatura, no la dimensión; el no determinismo cambia quién paga un eje, no cuántos ejes
hay: adivinado al principio lo paga la descripción, adivinado durante la corrida lo paga el espacio.

## Lo que NO se prueba

* Es caja negra y relativiza, como todo el cubo: nada sobre `P` contra `NP`.
* La ley de 2 es cota, no frontera: la región exacta de la corrida no determinista (con `|σ|` y `2^w` peleándose en
  `⌊(|σ| + 2^w)/2⌋`) no se calcula aquí.
* Que el contador de `⌈log₂(w+1)⌉` bits sea **necesario** para simular camino por camino se prueba solo en el
  ejemplo chico (`contador_es_reloj`, `w = 1`), no en general.
-/

namespace Sagitta.Map.Tiempo.CuboNoDeterminista

open Sagitta.Map.Tiempo.LeyTresMemorias
open Sagitta.Map.Tiempo.PlanoCostos
open Sagitta.Map.Tiempo.CuboCostos

/-! ## 1. Adivinar al principio es citar -/

/-- **Un resolvedor no determinista al principio**: para toda solución oculta `y` hay programa `p`, cita `c` y alguna
adivinanza `g` cuyo autómata (con su estado inicial) devuelve `y` con el verificador de `y` en a lo sumo `t`
consultas. La adivinanza elige el comienzo: autómata y estado inicial. -/
def ResuelveND {P C G σ Q R Y : Type} (O : Y → Q → R) (A : P → C → G → Automata σ Q R Y) (t : ℕ) : Prop :=
  ∀ y, ∃ p c g, (A p c g).corre (O y) t (A p c g).inicio = some y

/-- **Adivinar es citar**: un resolvedor no determinista con adivinanzas `G` es, tal cual, uno determinista con citas
`C × G`. Las dos direcciones. -/
theorem nd_es_cita {P C G σ Q R Y : Type} (O : Y → Q → R) (A : P → C → G → Automata σ Q R Y) (t : ℕ) :
    ResuelveND O A t ↔ ResuelveA O (fun p (cg : C × G) => A p cg.1 cg.2) t := by
  constructor
  · intro h y
    obtain ⟨p, c, g, hy⟩ := h y
    exact ⟨p, (c, g), hy⟩
  · intro h y
    obtain ⟨p, ⟨c, g⟩, hy⟩ := h y
    exact ⟨p, c, g, hy⟩

/-- Un tipo de a lo sumo `2^a · 2^b` elementos (no vacío) es imagen de `Fin (2^a) × Fin (2^b)`. -/
theorem existe_sobre {D : Type} [Fintype D] [Nonempty D] {a b : ℕ} (h : Fintype.card D ≤ 2 ^ a * 2 ^ b) :
    ∃ f : Fin (2 ^ a) × Fin (2 ^ b) → D, Function.Surjective f := by
  classical
  obtain ⟨d₀⟩ := ‹Nonempty D›
  let e := Fintype.equivFin D
  refine ⟨fun cg => if hk : (finProdFinEquiv cg : ℕ) < Fintype.card D then e.symm ⟨_, hk⟩ else d₀, ?_⟩
  intro d
  refine ⟨finProdFinEquiv.symm ⟨e d, lt_of_lt_of_le (e d).isLt h⟩, ?_⟩
  simp only [Equiv.apply_symm_apply, Fin.is_lt, dite_true, Fin.eta, Equiv.symm_apply_apply]

/-- **Y al revés: una cita de `s + w` bits es una cita de `s` y una adivinanza de `w`.** Todo resolvedor determinista
con citas `|D| ≤ 2^s · 2^w` es uno no determinista con citas `Fin (2^s)` y adivinanzas `Fin (2^w)`. -/
theorem cita_es_nd {P D σ Q R Y : Type} [Fintype D] [Nonempty Y] {s w t : ℕ} (hD : Fintype.card D ≤ 2 ^ s * 2 ^ w)
    (O : Y → Q → R) (B : P → D → Automata σ Q R Y) (h : ResuelveA O B t) :
    ∃ A : P → Fin (2 ^ s) → Fin (2 ^ w) → Automata σ Q R Y, ResuelveND O A t := by
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have : Nonempty D := ⟨(h y₀).choose_spec.choose⟩
  obtain ⟨f, hf⟩ := existe_sobre hD
  refine ⟨fun p c g => B p (f (c, g)), fun y => ?_⟩
  obtain ⟨p, d, hy⟩ := h y
  obtain ⟨⟨c, g⟩, hcg⟩ := hf d
  exact ⟨p, c, g, by simp only [hcg]; exact hy⟩

/-- **La ley del cubo no determinista**: `N ≤ 2^L · 2^s · 2^w · min (t + 1) 2^(S−1)`. -/
theorem ley_cubo_nd {P C G σ Y : Type} [Fintype P] [Fintype C] [Fintype G] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s w S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hG : Fintype.card G ≤ 2 ^ w)
    (hσ : Fintype.card σ ≤ 2 ^ S) (A : P → C → G → Automata σ Y Bool Y) (h : ResuelveND igual A t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * 2 ^ w * min (t + 1) (2 ^ (S - 1)) := by
  have hCG : Fintype.card (C × G) ≤ 2 ^ (s + w) := by
    rw [Fintype.card_prod, pow_add]; exact Nat.mul_le_mul hC hG
  have := ley_cubo hP hCG hσ _ ((nd_es_cita igual A t).1 h)
  rwa [pow_add, ← mul_assoc] at this

/-- **La ley en bits**: `⌈log₂ N⌉ ≤ L + s + w + min ⌈log₂(t+1)⌉ (S − 1)`. La adivinanza se suma a la descripción. -/
theorem ley_cubo_nd_log {P C G σ Y : Type} [Fintype P] [Fintype C] [Fintype G] [Fintype σ] [Fintype Y]
    [DecidableEq Y] {L s w S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hG : Fintype.card G ≤ 2 ^ w) (hσ : Fintype.card σ ≤ 2 ^ S) (A : P → C → G → Automata σ Y Bool Y)
    (h : ResuelveND igual A t) :
    Nat.clog 2 (Fintype.card Y) ≤ L + s + w + min (Nat.clog 2 (t + 1)) (S - 1) := by
  have hCG : Fintype.card (C × G) ≤ 2 ^ (s + w) := by
    rw [Fintype.card_prod, pow_add]; exact Nat.mul_le_mul hC hG
  have := ley_cubo_log hP hCG hσ _ ((nd_es_cita igual A t).1 h)
  omega

/-- **Un punto del cubo no determinista** `(x, w, e, y)`: programas y citas de `x` bits, adivinanzas de `w`, espacio
`e`, tiempo `y` en bits, sobre `N = 2^m` con el verificador de sí o no. -/
def AlcanzableCuboND (m x w e y : ℕ) : Prop :=
  ∃ (P C G σ : Type) (_ : Fintype P) (_ : Fintype C) (_ : Fintype G) (_ : Fintype σ)
    (A : P → C → G → Automata σ (Fin (2 ^ m)) Bool (Fin (2 ^ m))) (L s g S t : ℕ),
    Fintype.card P ≤ 2 ^ L ∧ Fintype.card C ≤ 2 ^ s ∧ Fintype.card G ≤ 2 ^ g ∧ Fintype.card σ ≤ 2 ^ S ∧
      ResuelveND (siNo m) A t ∧ L + s ≤ x ∧ g ≤ w ∧ S ≤ e ∧ Nat.clog 2 (t + 1) ≤ y

/-- **La región, exacta**: `(x, w, e, y)` se alcanza si y solo si `m ≤ x + w + min y (e − 1)`. No hay cuarto eje:
es la región del cubo (`cubo_es_region`) en `(x + w, e, y)`. -/
theorem cubo_nd_es_region (m x w e y : ℕ) : AlcanzableCuboND m x w e y ↔ m ≤ x + w + min y (e - 1) := by
  constructor
  · rintro ⟨P, C, G, σ, iP, iC, iG, iσ, A, L, s, g, S, t, hP, hC, hG, hσ, hA, hx, hw, he, hy⟩
    have := ley_cubo_nd_log hP hC hG hσ A hA
    rw [Fintype.card_fin, Nat.clog_pow 2 m one_lt_two] at this
    omega
  · intro h
    have hc : AlcanzableCubo m (x + w) e y := (cubo_es_region m (x + w) e y).2 h
    obtain ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, hP, hC, hσ, hA, hx, he, hy⟩ := hc
    -- la descripción `L + s` se parte en `a ≤ x` bits de cita y `b ≤ w` de adivinanza
    set a := min (L + s) x
    set b := L + s - a
    have hD : Fintype.card (P × C) ≤ 2 ^ a * 2 ^ b := by
      rw [Fintype.card_prod, ← pow_add, show a + b = L + s by omega, pow_add]
      exact Nat.mul_le_mul hP hC
    have hB : ResuelveA (siNo m) (fun (_ : Unit) (pc : P × C) => A pc.1 pc.2) t := fun y => by
      obtain ⟨p, c, hy⟩ := hA y
      exact ⟨(), (p, c), hy⟩
    obtain ⟨A', hA'⟩ := cita_es_nd hD (siNo m) _ hB
    exact ⟨Unit, Fin (2 ^ a), Fin (2 ^ b), σ, inferInstance, inferInstance, inferInstance, iσ, A', 0, a, b, S, t,
      by simp, by simp, by simp, hσ, hA', by omega, by omega, he, hy⟩

/-- **El borde, como corte**: con `w` bits de adivinanza alcanza una cita de `w` bits menos, y uno menos no alcanza. -/
theorem adivinar_reemplaza_citar {m w e y : ℕ} :
    AlcanzableCuboND m (m - w - min y (e - 1)) w e y ∧
      (min y (e - 1) + w < m → ¬ AlcanzableCuboND m (m - w - min y (e - 1) - 1) w e y) := by
  refine ⟨by rw [cubo_nd_es_region]; omega, fun h => by rw [cubo_nd_es_region]; omega⟩

/-! ## 2. Adivinar a mitad de corrida -/

/-- **Un autómata que adivina durante la corrida.** Como `Automata`, pero en los estados que eligen (`elige x = true`)
la transición escoge entre dos sucesores según un bit: `δ x r b`. En los que no eligen, el bit no se usa (`δ x r false`).
No hay contador de pasos ni de elecciones: lo que sepa de eso lo guarda en `σ`. -/
structure AutomataND (σ Q R Y : Type) where
  inicio : σ
  consulta : σ → Q
  /-- `true`: en este estado la transición elige. -/
  elige : σ → Bool
  δ : σ → R → Bool → σ
  salida : σ → Option Y

namespace AutomataND

variable {σ Q R Y : Type}

/-- **Un paso con la sucesión de elecciones a la vista**: si el estado elige, usa el primer bit que queda (`false` si ya
no quedan) y lo gasta. -/
def sigue (a : AutomataND σ Q R Y) (z : σ × List Bool) (r : R) : σ × List Bool :=
  if a.elige z.1 then (a.δ z.1 r (z.2.headD false), z.2.tail) else (a.δ z.1 r false, z.2)

/-- **Fijar las elecciones al principio.** Con la sucesión `bs` escrita antes de correr, la corrida es la de un autómata
determinista, pero con estados `σ × List Bool`: el estado y lo que falta de la sucesión. Ese segundo componente es el
contador de elecciones, y no es gratis (`contador_es_reloj`). -/
def fijar (a : AutomataND σ Q R Y) (bs : List Bool) : Automata (σ × List Bool) Q R Y where
  inicio := (a.inicio, bs)
  consulta := fun z => a.consulta z.1
  δ := a.sigue
  salida := fun z => a.salida z.1

/-- **Las soluciones que halla con `w` elecciones** (con el verificador de sí o no y a lo sumo `t` consultas): las que
devuelve con alguna sucesión `f : Fin w → Bool`. Pasada la `w`-ésima elección, la elección es `false`. -/
def halladosND [DecidableEq Y] [Fintype Y] (a : AutomataND σ Y Bool Y) (w t : ℕ) : Finset Y :=
  Finset.univ.biUnion fun f : Fin w → Bool => (a.fijar (List.ofFn f)).hallados t

theorem mem_halladosND [DecidableEq Y] [Fintype Y] {a : AutomataND σ Y Bool Y} {w t : ℕ} {y : Y} :
    y ∈ a.halladosND w t ↔ ∃ f : Fin w → Bool,
      (a.fijar (List.ofFn f)).corre (igual y) t (a.fijar (List.ofFn f)).inicio = some y := by
  simp [halladosND, Automata.hallados]

variable [DecidableEq Y] [Fintype Y] {a : AutomataND σ Y Bool Y}

/-- **El tope del tiempo**: a lo sumo `2^w · (t + 1)`, una trayectoria del «no» por sucesión de elecciones. -/
theorem halladosND_le_tiempo (w t : ℕ) : (a.halladosND w t).card ≤ 2 ^ w * (t + 1) := by
  calc _ ≤ ∑ f : Fin w → Bool, ((a.fijar (List.ofFn f)).hallados t).card := Finset.card_biUnion_le
    _ ≤ ∑ _f : Fin w → Bool, (t + 1) := Finset.sum_le_sum fun f _ => Automata.hallados_le_tiempo t
    _ = 2 ^ w * (t + 1) := by simp

/-- **El tope de las salidas**: a lo sumo tantas como estados de `σ` que paran, **sin** el factor `2^w`. Cada solución
hallada la devuelve un estado de `σ` (el contador de elecciones no cuenta: la salida solo mira `σ`). -/
theorem halladosND_le_salidas [Fintype σ] (w t : ℕ) :
    (a.halladosND w t).card ≤ (Finset.univ.filter fun x : σ => ¬ a.salida x = none).card := by
  classical
  have hex : ∀ y ∈ a.halladosND w t, ∃ x, a.salida x = some y := fun y hy => by
    obtain ⟨f, hf⟩ := mem_halladosND.1 hy
    obtain ⟨z, hz⟩ := Automata.corre_salida hf
    exact ⟨z.1, hz⟩
  let g : Y → σ := fun y => if h : ∃ x, a.salida x = some y then h.choose else a.inicio
  have hg : ∀ y ∈ a.halladosND w t, a.salida (g y) = some y := fun y hy => by
    simp only [g, dite_eq_left_of_eq_true (eq_true (hex y hy))]; exact (hex y hy).choose_spec
  refine Finset.card_le_card_of_injOn g (fun y hy => ?_) (fun y hy y' hy' he => ?_)
  · simp [hg y hy]
  · have := hg y hy; rw [he, hg y' hy'] at this; exact (Option.some.inj this).symm

/-- **El tope del espacio**: `2 · |hallados| ≤ |σ| + 2^w`. Como en `hallados_le_espacio`, cada solución hallada necesita
un estado de `σ` que la devuelva, y todas menos las de los «altos» (la primera parada de la trayectoria del «no» de
cada sucesión, una por sucesión) necesitan además un estado de `σ` que no para y la consulta. Cada bit de adivinanza
duplica los altos, no los estados. -/
theorem halladosND_le_espacio [Fintype σ] (w t : ℕ) : 2 * (a.halladosND w t).card ≤ Fintype.card σ + 2 ^ w := by
  classical
  set F := a.halladosND w t
  let alto : (Fin w → Bool) → Y → Prop := fun f y =>
    ∃ j, (∀ i < j, (a.fijar (List.ofFn f)).salida ((a.fijar (List.ofFn f)).trayNo (a.fijar (List.ofFn f)).inicio i) =
      none) ∧ (a.fijar (List.ofFn f)).salida ((a.fijar (List.ofFn f)).trayNo (a.fijar (List.ofFn f)).inicio j) = some y
  let altos : Finset Y := Finset.univ.biUnion fun f : Fin w → Bool => Finset.univ.filter (alto f)
  have hA : altos.card ≤ 2 ^ w := by
    calc altos.card ≤ ∑ f : Fin w → Bool, (Finset.univ.filter (alto f)).card := Finset.card_biUnion_le
      _ ≤ ∑ _f : Fin w → Bool, 1 := Finset.sum_le_sum fun f _ => Finset.card_le_one.2 fun y hy y' hy' => by
          obtain ⟨j, h1, h2⟩ := (Finset.mem_filter.1 hy).2
          obtain ⟨j', h1', h2'⟩ := (Finset.mem_filter.1 hy').2
          exact Automata.alto_unico h1 h2 h1' h2'
      _ = 2 ^ w := by simp
  have hB : (F.filter fun y => y ∉ altos).card ≤ (Finset.univ.filter fun x : σ => a.salida x = none).card := by
    calc _ ≤ ((Finset.univ.filter fun x : σ => a.salida x = none).image a.consulta).card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨hyF, hna⟩ := Finset.mem_filter.1 hy
          obtain ⟨f, hf⟩ := mem_halladosND.1 hyF
          obtain ⟨j, -, hpre, hfin⟩ := Automata.halla_en_trayNo y t _ hf
          rcases hfin with h | ⟨h, hq⟩
          · exact absurd (Finset.mem_biUnion.2 ⟨f, Finset.mem_univ _,
              Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hpre, h⟩⟩) hna
          · exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, hq⟩
      _ ≤ _ := Finset.card_image_le
  have hC : F.card ≤ (Finset.univ.filter fun x : σ => ¬ a.salida x = none).card := halladosND_le_salidas w t
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun y => y ∈ altos)
  have hin : (F.filter fun y => y ∈ altos).card ≤ altos.card :=
    Finset.card_le_card fun y hy => (Finset.mem_filter.1 hy).2
  have hsig := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset σ))
    (fun x => a.salida x = none)
  rw [Finset.card_univ] at hsig
  omega

/-- **En bits**: con `|σ| ≤ 2^S`, a lo sumo `2^w · min (t + 1) 2^(S−1)`, lo mismo que adivinando al principio. -/
theorem halladosND_le_bits [Fintype σ] {S : ℕ} (hσ : Fintype.card σ ≤ 2 ^ S) (w t : ℕ) :
    (a.halladosND w t).card ≤ 2 ^ w * min (t + 1) (2 ^ (S - 1)) := by
  rcases le_total (t + 1) (2 ^ (S - 1)) with h | h
  · rw [min_eq_left h]; exact halladosND_le_tiempo w t
  · rw [min_eq_right h]
    have hsal := (halladosND_le_salidas (a := a) w t).trans (Finset.card_le_univ _)
    have hesp := halladosND_le_espacio (a := a) w t
    have hw1 := Nat.one_le_two_pow (n := w)
    cases S with
    | zero => simp at hσ ⊢; omega
    | succ S =>
        cases w with
        | zero => simp at hesp ⊢; rw [pow_succ] at hσ; omega
        | succ w =>
            simp only [Nat.add_sub_cancel]
            rw [pow_succ] at hσ
            rw [pow_succ]
            have h2w := Nat.one_le_two_pow (n := w)
            have : 2 ^ S * 2 ≤ 2 ^ w * 2 * 2 ^ S := by
              calc 2 ^ S * 2 = 1 * 2 * 2 ^ S := by ring
                _ ≤ 2 ^ w * 2 * 2 ^ S := by gcongr
            omega

end AutomataND

open AutomataND

/-- **Un resolvedor que adivina durante la corrida**: para toda `y` hay programa, cita y alguna sucesión de `w`
elecciones con la que el autómata devuelve `y` en a lo sumo `t` consultas. -/
def ResuelveCorrida {P C σ Q R Y : Type} (O : Y → Q → R) (A : P → C → AutomataND σ Q R Y) (w t : ℕ) : Prop :=
  ∀ y, ∃ p c, ∃ f : Fin w → Bool,
    ((A p c).fijar (List.ofFn f)).corre (O y) t ((A p c).fijar (List.ofFn f)).inicio = some y

/-- **La sospecha, confirmada: adivinar a mitad de corrida no da más.** La ley es la misma que adivinando al principio:
`N ≤ 2^L · 2^s · 2^w · min (t + 1) 2^(S−1)`. -/
theorem ley_corrida {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s w S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S)
    (A : P → C → AutomataND σ Y Bool Y) (h : ResuelveCorrida igual A w t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * 2 ^ w * min (t + 1) (2 ^ (S - 1)) := by
  classical
  have hc := cubrir (ι := P × C) (fun pc y => y ∈ (A pc.1 pc.2).halladosND w t) (2 ^ w * min (t + 1) (2 ^ (S - 1)))
    (fun pc => by rw [Finset.filter_mem_eq_inter, Finset.univ_inter]; exact halladosND_le_bits hσ w t)
    (fun y => by obtain ⟨p, c, f, hy⟩ := h y; exact ⟨(p, c), mem_halladosND.2 ⟨f, hy⟩⟩)
  rw [Fintype.card_prod] at hc
  calc Fintype.card Y ≤ Fintype.card P * Fintype.card C * (2 ^ w * min (t + 1) (2 ^ (S - 1))) := hc
    _ ≤ 2 ^ L * 2 ^ s * (2 ^ w * min (t + 1) (2 ^ (S - 1))) := by gcongr
    _ = _ := by ring

/-- **En bits**: `⌈log₂ N⌉ ≤ L + s + w + min ⌈log₂(t+1)⌉ (S − 1)`, la de `ley_cubo_nd_log`. -/
theorem ley_corrida_log {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s w S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S)
    (A : P → C → AutomataND σ Y Bool Y) (h : ResuelveCorrida igual A w t) :
    Nat.clog 2 (Fintype.card Y) ≤ L + s + w + min (Nat.clog 2 (t + 1)) (S - 1) := by
  apply Nat.clog_le_of_le_pow
  calc Fintype.card Y ≤ 2 ^ L * 2 ^ s * 2 ^ w * min (t + 1) (2 ^ (S - 1)) := ley_corrida hP hC hσ A h
    _ ≤ 2 ^ L * 2 ^ s * 2 ^ w * 2 ^ min (Nat.clog 2 (t + 1)) (S - 1) := by gcongr; exact min_le_pow_min t S
    _ = _ := by rw [pow_add, pow_add, pow_add]

/-- **Y da menos: el espacio topa sin `w`.** `N ≤ 2^L · 2^s · 2^S`: lo adivinado a mitad de corrida hay que usarlo en
estados de `σ`, y cada solución la devuelve uno distinto. -/
theorem ley_corrida_salidas {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s w S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S)
    (A : P → C → AutomataND σ Y Bool Y) (h : ResuelveCorrida igual A w t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * 2 ^ S := by
  classical
  have hc := cubrir (ι := P × C) (fun pc y => y ∈ (A pc.1 pc.2).halladosND w t) (2 ^ S)
    (fun pc => by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact ((halladosND_le_salidas w t).trans (Finset.card_le_univ _)).trans hσ)
    (fun y => by obtain ⟨p, c, f, hy⟩ := h y; exact ⟨(p, c), mem_halladosND.2 ⟨f, hy⟩⟩)
  rw [Fintype.card_prod] at hc
  calc Fintype.card Y ≤ Fintype.card P * Fintype.card C * 2 ^ S := hc
    _ ≤ _ := by gcongr

/-! ### El contraejemplo chico: a mitad de corrida da menos que al principio -/

/-- Un autómata de un estado que devuelve `g` sin preguntar. -/
def constante (g : Fin 2) : Automata Unit (Fin 2) Bool (Fin 2) where
  inicio := ()
  consulta := fun _ => 0
  δ := fun _ _ => ()
  salida := fun _ => some g

/-- **Al principio, `1` bit y **un** estado bastan para `2` candidatos**, sin consultas: la adivinanza elige qué
autómata constante correr. A mitad de corrida, con un estado, **no** se resuelven `2` candidatos con ningún número de
elecciones `w` ni de consultas `t`. -/
theorem corrida_menos_que_principio :
    ResuelveND (P := Unit) (C := Unit) (G := Fin 2) igual (fun _ _ g => constante g) 0 ∧
      ∀ (A : Unit → Unit → AutomataND Unit (Fin 2) Bool (Fin 2)) (w t : ℕ), ¬ ResuelveCorrida igual A w t := by
  refine ⟨fun y => ⟨(), (), y, rfl⟩, fun A w t h => ?_⟩
  have := ley_corrida_salidas (L := 0) (s := 0) (S := 0) (by simp) (by simp) (by simp) A h
  simp at this

/-- **El contador, finito: lo que cuesta.** La simulación camino por camino con un contador de elecciones de
`w + 1` valores (`0, …, w`, saturado en `w`): estados `σ × Fin (w + 1)`, o sea `⌈log₂(w+1)⌉` bits más de espacio. -/
def fijarFin {σ Q R Y : Type} (a : AutomataND σ Q R Y) (bs : List Bool) (w : ℕ) : Automata (σ × Fin (w + 1)) Q R Y where
  inicio := (a.inicio, 0)
  consulta := fun z => a.consulta z.1
  δ := fun z r => if a.elige z.1 then (a.δ z.1 r ((bs.drop z.2).headD false), ⟨min (z.2 + 1) w, by omega⟩)
    else (a.δ z.1 r false, z.2)
  salida := fun z => a.salida z.1

/-- **El contador finito simula la corrida**: con `|bs| ≤ w`, desde `(x, k)` corre igual que `fijar` desde
`(x, lo que falta después de k elecciones)`. -/
theorem fijarFin_corre {σ Q R Y : Type} (a : AutomataND σ Q R Y) (bs : List Bool) (w : ℕ) (hb : bs.length ≤ w)
    (O : Q → R) : ∀ (t : ℕ) (x : σ) (k : Fin (w + 1)),
      (fijarFin a bs w).corre O t (x, k) = (a.fijar bs).corre O t (x, bs.drop k)
  | 0, x, k => rfl
  | t + 1, x, k => by
      cases hs : a.salida x with
      | some y =>
          rw [Automata.corre_some (a := fijarFin a bs w) (show (fijarFin a bs w).salida (x, k) = some y from hs),
            Automata.corre_some (a := a.fijar bs) (show (a.fijar bs).salida (x, bs.drop k) = some y from hs)]
      | none =>
          rw [Automata.corre_none (a := fijarFin a bs w) (show (fijarFin a bs w).salida (x, k) = none from hs),
            Automata.corre_none (a := a.fijar bs) (show (a.fijar bs).salida (x, bs.drop k) = none from hs)]
          cases he : a.elige x
          · have st : (fijarFin a bs w).δ (x, k) (O ((fijarFin a bs w).consulta (x, k))) =
                (a.δ x (O (a.consulta x)) false, k) := by simp [fijarFin, he]
            have st' : (a.fijar bs).δ (x, bs.drop k) (O ((a.fijar bs).consulta (x, bs.drop k))) =
                (a.δ x (O (a.consulta x)) false, bs.drop k) := by simp [fijar, sigue, he]
            rw [st, st']
            exact fijarFin_corre a bs w hb O t _ k
          · have hd : bs.drop (min (k.val + 1) w) = (bs.drop k).tail := by
              rw [List.tail_drop]
              rcases Nat.lt_or_ge k.val w with hk | hk
              · rw [min_eq_left (by omega)]
              · rw [min_eq_right (by omega), List.drop_eq_nil_of_le (by omega),
                  List.drop_eq_nil_of_le (by omega)]
            have st : (fijarFin a bs w).δ (x, k) (O ((fijarFin a bs w).consulta (x, k))) =
                (a.δ x (O (a.consulta x)) ((bs.drop k).headD false), ⟨min (k.val + 1) w, by omega⟩) := by
              simp [fijarFin, he]
            have st' : (a.fijar bs).δ (x, bs.drop k) (O ((a.fijar bs).consulta (x, bs.drop k))) =
                (a.δ x (O (a.consulta x)) ((bs.drop k).headD false), (bs.drop k).tail) := by
              simp [fijar, sigue, he]
            rw [st, st', ← hd]
            exact fijarFin_corre a bs w hb O t _ _

/-- **(a), con su precio: la corrida no determinista es una adivinanza al principio, pagando el contador.** Todo
resolvedor que hace a lo sumo `w` elecciones durante la corrida, con estados `σ`, es uno que adivina al principio la
sucesión (`2^w` comienzos) con estados `σ × Fin (w + 1)`. Por la ley de 1 eso da `S + ⌈log₂(w+1)⌉` bits de espacio;
`ley_corrida` muestra que ese precio no se refleja en la ley. -/
theorem corrida_a_principio {P C σ Q R Y : Type} (O : Y → Q → R) (A : P → C → AutomataND σ Q R Y) (w t : ℕ)
    (h : ResuelveCorrida O A w t) :
    ResuelveND O (fun p c (f : Fin w → Bool) => fijarFin (A p c) (List.ofFn f) w) t := by
  intro y
  obtain ⟨p, c, f, hy⟩ := h y
  refine ⟨p, c, f, ?_⟩
  have := fijarFin_corre (A p c) (List.ofFn f) w (by simp) (O y) t (A p c).inicio 0
  simp only [Fin.val_zero, List.drop_zero] at this
  exact this.trans hy

/-- El precio en estados: `|σ| · (w + 1)`. -/
theorem card_contador (σ : Type) [Fintype σ] (w : ℕ) : Fintype.card (σ × Fin (w + 1)) = Fintype.card σ * (w + 1) := by
  simp

/-! ### Dónde se paga la simulación camino por camino: el contador de elecciones es un reloj -/

/-- **Dos estados y una elección.** `false` elige: con el bit `true` se queda en `false`, con `false` pasa a `true`.
`true` no elige y se queda. -/
def dosEstados : AutomataND Bool (Fin 2) Bool (Fin 2) where
  inicio := false
  consulta := fun _ => 0
  elige := fun x => !x
  δ := fun x _ b => if x then true else !b
  salida := fun x => if x then some 1 else none

/-- **El contador de elecciones es un reloj.** Con la sucesión `[true]`, la trayectoria del «no» pasa por `false`,
`false`, `true`: sale de `false` una vez a `false` (gasta la elección) y otra vez a `true` (ya no le queda). Ningún
autómata determinista sobre los mismos **2** estados (`g : Bool → Bool` como transición con «no») tiene esa
trayectoria: la simulación camino por camino tiene que guardar cuántas elecciones lleva, y eso es espacio, como el
reloj de `mutante_reloj`. -/
theorem contador_es_reloj :
    ¬ ∃ g : Bool → Bool, ∀ j, ((dosEstados.fijar [true]).trayNo (dosEstados.fijar [true]).inicio (j + 1)).1 =
      g ((dosEstados.fijar [true]).trayNo (dosEstados.fijar [true]).inicio j).1 := by
  rintro ⟨g, hg⟩
  have h0 : false = g false := hg 0
  have h1 : true = g false := hg 1
  rw [← h0] at h1
  exact Bool.false_ne_true h1.symm

/-- **Y aun así esa corrida halla su solución**: con la sucesión `[true]` devuelve `1` en dos consultas. La ley no se
rompe porque lo que cuenta son los estados que devuelven y consultan, no la trayectoria. -/
theorem dosEstados_halla : (dosEstados.fijar [true]).corre (igual 1) 2 (dosEstados.fijar [true]).inicio = some 1 := by
  decide

/-! ## 3. La lectura

La rotación de Wick cambia la signatura, no la dimensión; el no determinismo cambia quién paga un eje, no cuántos ejes
hay: adivinado al principio lo paga la descripción (`cubo_nd_es_region`), adivinado durante la corrida lo paga el
espacio (`ley_corrida_salidas`). -/

end Sagitta.Map.Tiempo.CuboNoDeterminista
