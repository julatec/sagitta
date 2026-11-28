import Sagitta.Map.PlanoCostos
import Mathlib.Data.Fintype.Pigeonhole

/-!
# El cubo de costos

La idea es de José (24 nov 2026). El plano de costos (`PlanoCostos`) es en realidad un **cubo**: la cara que se probó
allá, descripción × tiempo, tenía el espacio gratis.

## Los tres ejes

* **La descripción** `x`: lo que está escrito **antes** de correr, el programa más la cita, `L + s` bits (como en
  `LeyTresMemorias`: a lo sumo `2^L` programas y `2^s` citas; cada par fija un autómata y su estado inicial).
* **El espacio** `e`: la memoria de trabajo **durante** la corrida, `S` bits, o sea a lo sumo `2^S` estados.
* **El tiempo** `y`: el número de consultas al verificador, en bits, `⌈log₂(t+1)⌉`.

## El modelo, y la decisión sobre el contador de pasos

Un resolvedor con espacio `S` es un **autómata** (`Automata σ Q R Y`): estados `σ` con `|σ| ≤ 2^S`, un estado inicial,
`consulta : σ → Q`, `δ : σ → R → σ` y `salida : σ → Option Y` (`some y`: devuelve `y` y para). Corre con a lo sumo `t`
consultas (`Automata.corre`). Resolver (`ResuelveA`) es lo mismo que en `LeyTresMemorias`: para toda `y` hay programa y
cita cuyo autómata devuelve `y` con el verificador de `y` en a lo sumo `t` consultas.

**No hay contador de pasos.** Ni la consulta, ni la transición, ni la salida reciben el número de paso: lo que el
autómata sabe de cuánto lleva corriendo es lo que guardó en `σ`, y lo paga en estados. Con el reloj regalado (como en
los programas por niveles, donde el nivel es el paso) la ley es falsa: `mutante_reloj` da un autómata de **2 estados**
con reloj que resuelve `4` candidatos en `3` consultas, contra el tope `1` de la ley.

## La ley del cubo, exacta

* **El tope del tiempo útil** (meta 1). Contra el verificador de sí o no, mientras no acierta el autómata oye siempre
  «no», así que recorre la **trayectoria del «no»** (`trayNo`), que no depende de la solución. Por palomar se repite antes
  de `|σ|` pasos (`trayNo_periodica`): si `y` no es lo que aporta (`aporte`: lo que consulta o lo que devuelve) ninguno
  de sus primeros `|σ|` estados, el autómata no devuelve `y` **nunca** (`no_la_halla_nunca`). Mientras oye «no» hace a lo
  sumo `min t |σ|` consultas distintas (`consultas_distintas_le`).
* **Cuántas halla un autómata** (`hallados`): a lo sumo `t + 1` (`hallados_le_tiempo`, como `halla_le_si_no`) y a lo sumo
  `⌊(|σ| + 1)/2⌋` (`hallados_le_espacio`: `2 · |hallados| ≤ |σ| + 1`). Cada solución hallada necesita un estado que la
  **devuelva**, y todas menos una (la del primer alto de la trayectoria del «no») necesitan además un estado que **no
  para y la consulta**; unos paran y otros no, así que son distintos. Con `|σ| ≤ 2^S`: `min (t + 1) 2^(S−1)`
  (`hallados_le_bits`; `S − 1` truncado).
* **La ley** (meta 2, `ley_cubo`): `N ≤ 2^L · 2^s · min (t + 1) 2^(S−1)`. En bits (`ley_cubo_log`):
  `⌈log₂ N⌉ ≤ L + s + min ⌈log₂(t+1)⌉ (S − 1)`.
* **Es exacta** (`cubo_es_region`): con `N = 2^m`, el punto `(x, e, y)` se alcanza (`AlcanzableCubo`) **si y solo si**
  `m ≤ x + min y (e − 1)`. Lo construye el barrido como autómata (`barridoA`, `punto_cubo`): cita de `m − k` bits,
  `2^k − 1` consultas y `2^(k+1) − 1` estados.
* **El redondeo, exacto.** La conjetura era `L + s + min(log₂(t+1), S) ≳ m`. Lo que queda es **`S − 1`** en lugar de
  `S`, y ningún otro redondeo: el tiempo entra como `⌈log₂(t+1)⌉` sin pérdida (como en el plano), y el espacio pierde
  exactamente un bit, el que separa los estados que preguntan de los que responden. El `−1` no es holgura de la prueba:
  la conjetura sin él es cota válida pero no frontera (`mutante_sin_menos_uno`), y el contador de `⌈log₂(t+1)⌉` bits
  sin el bit de más no alcanza la recta (`contador_sin_bit_extra`).

## La lectura: el tiempo sin memoria para contarlo no rinde

Pasado `e − 1` bits de tiempo, más tiempo no cambia nada (`tiempo_no_rinde`). Es el bombeo de `BombeoDetector`
dentro del cubo: allá un detector de pocos estados confunde prefijos y paga en demora; aquí un autómata de
pocos estados entra en ciclo oyendo «no» y deja de consultar candidatos nuevos. Las tres caras, como cortes:

* **la recta del plano** (`cara_plano`): con `y < e` el corte es el semiplano `x + y ≥ m` de `PlanoCostos`
  (`region_es_semiplano`); toda la región proyecta al plano (`cubo_a_plano`, `ley_cubo_plano`);
* **el bombeo** (`cara_bombeo`): con `e − 1 ≤ y` el espacio pone el tope, `x + (e − 1) ≥ m`; `mucho_tiempo_no_sirve`
  lo dice para `2^S ≤ t` sin descripción;
* **la tabla** (`cara_tabla`): con `x ≥ m` bits escritos antes basta un estado y ninguna consulta.

## Controles

* El contador alcanza la recta del plano con `k + 1` bits de espacio (`contador_en_la_recta`) y no con `k`
  (`contador_sin_bit_extra`).
* Un autómata de `2^S` estados no halla más de `2^(S−1)` candidatos con ningún tiempo (`espacio_topa`).
* La cita compensa el espacio (`cita_compensa`): con `S` bits de espacio, cita de `m − (S − 1)` bits resuelve; con
  `m − S`, no.

## Mutantes (refutados aquí; las copias que no compilan están fuera del repositorio)

* `mutante_reloj`: regalar el contador de pasos rompe la ley con `min`.
* `mutante_sin_min`: la ley sin `min` (solo el tiempo) es cota válida pero no frontera del cubo.
* `mutante_sin_espacio`: sin acotar los estados, la ley con `S = 0` es falsa.
* `mutante_sin_menos_uno`: la conjetura con `S` en lugar de `S − 1`, como frontera, es falsa.
* `mutante_bits`: con un verificador informativo de `1` bit la ley del sí o no es falsa.

## El verificador informativo

Con respuestas de `b` bits la cuenta cambia (`ley_cubo_general`, `ley_cubo_general_log`):
`N ≤ 2^L · 2^s · min (2^(b·t)) 2^S`, o sea `⌈log₂ N⌉ ≤ L + s + min (b·t) S`. El tiempo rinde `b·t` bits y no
`log₂(t+1)`, porque la trayectoria ya no es una sola (`halla_gen`), y el espacio topa en `S` y no en `S − 1`, porque
basta contar los estados que devuelven (`hallados_gen_le_estados`). Que `min (b·t) S` sea la frontera exacta **no** se
prueba; el lector de dos bits (`mutante_bits`) alcanza el primer término con igualdad.

## Lo que NO se prueba

* **Es caja negra y relativiza.** El verificador es un oráculo que se evalúa gratis; todo vale igual relativo a cualquier
  oráculo (Baker, Gill y Solovay, 1975, de memoria), así que no separa ni colapsa clases.
* **Con un verificador informativo el análisis cambia**: arriba está la cota que se prueba (`min (b·t) S`), sin la
  exactitud que sí tiene el caso de sí o no.
* **No son máquinas de Turing.** El espacio es el número de estados de un autómata que no lee la entrada ni tiene cinta;
  el tiempo, número de consultas. El autómata ve la instancia solo a través del verificador.
* **Nada sobre P contra NP.**
-/

namespace Sagitta.Map.Tiempo.CuboCostos

open Sagitta.Map.Tiempo.LeyTresMemorias
open Sagitta.Map.Tiempo.PlanoCostos

/-! ## 1. El modelo: un autómata con espacio acotado -/

/-- **Un autómata que consulta al verificador.** Estados `σ` (la memoria de trabajo: `S` bits si `|σ| ≤ 2^S`), un
estado inicial, la consulta que hace cada estado, la transición según la respuesta y la salida. Si `salida x = some y`,
el autómata devuelve `y` y para; si es `none`, consulta `consulta x` y pasa a `δ x r`.

**No hay contador de pasos.** Ni `consulta`, ni `δ`, ni `salida` reciben el número de paso: lo único que el autómata
sabe de cuánto lleva corriendo es lo que haya guardado en `σ`, y eso lo paga en estados. -/
structure Automata (σ Q R Y : Type) where
  /-- El estado al empezar. Lo fijan el programa y la cita. -/
  inicio : σ
  /-- Qué le pregunta al verificador en cada estado. -/
  consulta : σ → Q
  /-- La transición según la respuesta. -/
  δ : σ → R → σ
  /-- `some y`: devuelve `y` y para. `none`: sigue consultando. -/
  salida : σ → Option Y

namespace Automata

variable {σ Q R Y : Type} (a : Automata σ Q R Y)

/-- **La corrida con a lo sumo `t` consultas**, desde el estado `x`, con el verificador `O`. Con `0` consultas de
presupuesto solo puede devolver lo que diga la salida del estado; con `t + 1`, si el estado no para, consulta una vez
y sigue con `t`. -/
def corre (O : Q → R) : ℕ → σ → Option Y
  | 0, x => a.salida x
  | t + 1, x =>
    match a.salida x with
    | some y => some y
    | none => corre O t (a.δ x (O (a.consulta x)))

variable {a}

theorem corre_cero (O : Q → R) (x : σ) : a.corre O 0 x = a.salida x := rfl

theorem corre_some {O : Q → R} {x : σ} {y : Y} (h : a.salida x = some y) : ∀ t, a.corre O t x = some y
  | 0 => h
  | t + 1 => by simp [corre, h]

theorem corre_none {O : Q → R} {x : σ} (h : a.salida x = none) (t : ℕ) :
    a.corre O (t + 1) x = a.corre O t (a.δ x (O (a.consulta x))) := by
  simp [corre, h]

/-- **Más presupuesto no cambia lo que ya se devolvió.** -/
theorem corre_mono {O : Q → R} {y : Y} : ∀ {t : ℕ} {x : σ} (u : ℕ), a.corre O t x = some y → a.corre O (t + u) x = some y
  | 0, x, u, h => corre_some h _
  | t + 1, x, u, h => by
      cases hs : a.salida x with
      | some z =>
          rw [corre_some hs (O := O)] at h
          rw [← h]; exact corre_some hs _
      | none =>
          rw [corre_none hs] at h
          rw [show t + 1 + u = (t + u) + 1 by omega, corre_none hs]
          exact corre_mono u h

/-- **Lo que se devuelve sale de algún estado que para con eso.** -/
theorem corre_salida {O : Q → R} {y : Y} : ∀ {t : ℕ} {x : σ}, a.corre O t x = some y → ∃ x', a.salida x' = some y
  | 0, x, h => ⟨x, h⟩
  | t + 1, x, h => by
      cases hs : a.salida x with
      | some z => exact ⟨x, by rw [hs, ← corre_some hs (O := O) (t + 1), h]⟩
      | none => rw [corre_none hs] at h; exact corre_salida h

end Automata

open Automata

/-- **Un resolvedor del cubo resuelve en tiempo `t`**: para toda solución oculta `y` hay un programa `p` y una cita `c`
cuyo autómata, arrancando en su estado inicial y con el verificador de `y`, devuelve `y` con a lo sumo `t` consultas.
Es `Resuelve` de `LeyTresMemorias` con autómatas en lugar de árboles. -/
def ResuelveA {P C σ Q R Y : Type} (O : Y → Q → R) (A : P → C → Automata σ Q R Y) (t : ℕ) : Prop :=
  ∀ y, ∃ p c, (A p c).corre (O y) t (A p c).inicio = some y

/-! ## 2. El tope del tiempo útil: el bombeo dentro del cubo

Contra el verificador de sí o no, mientras no acierta el autómata oye siempre «no». Su sucesión de estados es entonces
la **trayectoria del no** (`trayNo`): `x, δ x false, δ (δ x false) false, …`, que no depende de la solución oculta. -/

namespace Automata

section TopeTiempo

variable {σ Y : Type} [DecidableEq Y] (a : Automata σ Y Bool Y)

/-- **La trayectoria del «no»**: el estado después de `j` respuestas «no», arrancando en `x`. -/
def trayNo (x : σ) (j : ℕ) : σ := (fun z => a.δ z false)^[j] x

/-- **Lo que un estado aporta**: si para, lo que devuelve; si no, lo que consulta. -/
def aporte (x : σ) : Y := (a.salida x).getD (a.consulta x)

variable {a}

omit [DecidableEq Y] in
theorem trayNo_succ (x : σ) (j : ℕ) : a.trayNo x (j + 1) = a.trayNo (a.δ x false) j :=
  Function.iterate_succ_apply _ _ _

/-- **Dónde se halla una solución.** Si el autómata devuelve `y` desde `x` con a lo sumo `t` consultas, hay un `j ≤ t`
tal que los primeros `j` estados de la trayectoria del «no» siguen sin parar, y el estado `j`, o devuelve `y`, o no para
y consulta `y`. -/
theorem halla_en_trayNo (y : Y) : ∀ (t : ℕ) (x : σ), a.corre (igual y) t x = some y →
    ∃ j ≤ t, (∀ i < j, a.salida (a.trayNo x i) = none) ∧
      (a.salida (a.trayNo x j) = some y ∨ (a.salida (a.trayNo x j) = none ∧ a.consulta (a.trayNo x j) = y))
  | 0, x, h => ⟨0, le_rfl, fun _ hi => absurd hi (Nat.not_lt_zero _), Or.inl h⟩
  | t + 1, x, h => by
      cases hs : a.salida x with
      | some z =>
          rw [corre_some hs] at h
          exact ⟨0, Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _), Or.inl (by rw [← h]; exact hs)⟩
      | none =>
          by_cases hq : a.consulta x = y
          · exact ⟨0, Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _), Or.inr ⟨hs, hq⟩⟩
          · have hf : igual y (a.consulta x) = false := by simp [igual, hq]
            rw [corre_none hs, hf] at h
            obtain ⟨j, hj, hpre, hfin⟩ := halla_en_trayNo y t _ h
            refine ⟨j + 1, by omega, fun i hi => ?_, by rwa [trayNo_succ]⟩
            cases i with
            | zero => exact hs
            | succ i => rw [trayNo_succ]; exact hpre i (by omega)

omit [DecidableEq Y] in
/-- **La trayectoria del «no» se repite antes de `|σ|` pasos** (el palomar sobre los estados): todo estado de la
trayectoria ya apareció entre los primeros `|σ|`. -/
theorem trayNo_periodica [Fintype σ] (x : σ) : ∀ j, ∃ i < Fintype.card σ, a.trayNo x j = a.trayNo x i := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < Fintype.card σ
    · exact ⟨j, hj, rfl⟩
    · obtain ⟨u, v, huv, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun k : Fin (Fintype.card σ + 1) => a.trayNo x k) (by simp)
      have key : ∀ {p q : Fin (Fintype.card σ + 1)}, p < q → a.trayNo x p = a.trayNo x q →
          ∃ i < Fintype.card σ, a.trayNo x j = a.trayNo x i := by
        intro p q hpq hpq'
        have hq : (q : ℕ) ≤ j := by omega
        have : a.trayNo x j = a.trayNo x (j - q + p) := by
          simp only [trayNo] at hpq' ⊢
          rw [show j = (j - q) + q by omega, Function.iterate_add_apply, ← hpq',
            ← Function.iterate_add_apply, Nat.add_sub_cancel]
        obtain ⟨i, hi, hi'⟩ := ih (j - q + p) (by omega)
        exact ⟨i, hi, this.trans hi'⟩
      rcases lt_or_gt_of_ne huv with h | h
      · exact key h he
      · exact key h he.symm

/-- **Meta 1, el tope del tiempo útil.** Si `y` no es lo que aporta ninguno de los primeros `|σ|` estados de la
trayectoria del «no» (ni la consulta de uno que no para, ni la salida de uno que para), el autómata no devuelve `y`
**nunca**, con ningún presupuesto `t`. Correr más no sirve. -/
theorem no_la_halla_nunca [Fintype σ] {y : Y} (hy : ∀ i < Fintype.card σ, a.aporte (a.trayNo a.inicio i) ≠ y)
    (t : ℕ) : a.corre (igual y) t a.inicio ≠ some y := by
  intro h
  obtain ⟨j, -, -, hj⟩ := halla_en_trayNo y t a.inicio h
  obtain ⟨i, hi, he⟩ := trayNo_periodica (a := a) a.inicio j
  apply hy i hi
  rw [← he, aporte]
  rcases hj with hj | ⟨hj, hq⟩
  · simp [hj]
  · simp [hj, hq]

/-- **A lo sumo `|σ|` consultas distintas mientras oye «no»**, por más tiempo que corra: las consultas de la
trayectoria del «no» en `t` pasos son las de los primeros `min t |σ|` estados. -/
theorem consultas_distintas_le [Fintype σ] (t : ℕ) :
    ((Finset.range t).image fun j => a.consulta (a.trayNo a.inicio j)).card ≤ min t (Fintype.card σ) := by
  classical
  refine le_min ((Finset.card_image_le).trans (by simp)) ?_
  calc _ ≤ ((Finset.range t).image fun j => a.trayNo a.inicio j).card := by
        rw [show (fun j => a.consulta (a.trayNo a.inicio j)) = a.consulta ∘ fun j => a.trayNo a.inicio j from rfl,
          ← Finset.image_image]
        exact Finset.card_image_le
    _ ≤ Fintype.card σ := Finset.card_le_univ _

end TopeTiempo

end Automata

/-! ## 3. Cuántas soluciones halla un autómata, y la ley del cubo -/

namespace Automata

section Hallados

variable {σ Y : Type} [DecidableEq Y] [Fintype Y] (a : Automata σ Y Bool Y)

/-- **Las soluciones que el autómata halla** con a lo sumo `t` consultas: las `y` para las que, con el verificador de
`y`, devuelve `y`. -/
def hallados (t : ℕ) : Finset Y := Finset.univ.filter fun y => a.corre (igual y) t a.inicio = some y

variable {a}

/-- **El tope del tiempo**: a lo sumo `t + 1` soluciones (es `halla_le_si_no` para autómatas). Cada una es lo que aporta
alguno de los primeros `t + 1` estados de la trayectoria del «no». -/
theorem hallados_le_tiempo (t : ℕ) : (a.hallados t).card ≤ t + 1 := by
  calc (a.hallados t).card ≤ ((Finset.range (t + 1)).image fun j => a.aporte (a.trayNo a.inicio j)).card := by
        apply Finset.card_le_card
        intro y hy
        obtain ⟨j, hj, -, hfin⟩ := halla_en_trayNo y t a.inicio (Finset.mem_filter.1 hy).2
        refine Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), ?_⟩
        rcases hfin with h | ⟨h, hq⟩
        · simp [aporte, h]
        · simp [aporte, h, hq]
    _ ≤ (Finset.range (t + 1)).card := Finset.card_image_le
    _ = t + 1 := Finset.card_range _

omit [DecidableEq Y] [Fintype Y] in
/-- **El primer alto de la trayectoria del «no» es uno solo.** Dos soluciones que se devuelven en el primer estado de
la trayectoria que para son la misma. -/
theorem alto_unico {x : σ} {y y' : Y} {j j' : ℕ} (h1 : ∀ i < j, a.salida (a.trayNo x i) = none)
    (h2 : a.salida (a.trayNo x j) = some y) (h1' : ∀ i < j', a.salida (a.trayNo x i) = none)
    (h2' : a.salida (a.trayNo x j') = some y') : y = y' := by
  rcases lt_trichotomy j j' with h | rfl | h
  · rw [h1' j h] at h2; cases h2
  · rw [h2] at h2'; exact Option.some.inj h2'
  · rw [h1 j' h] at h2'; cases h2'

/-- **El tope del espacio**: `2 · |hallados| ≤ |σ| + 1`. Toda solución hallada necesita un estado que la devuelva (los
estados que paran), y todas menos a lo sumo una (la del primer alto de la trayectoria del «no») necesitan además un
estado que no para y la consulta. Son estados distintos: unos paran y otros no. -/
theorem hallados_le_espacio [Fintype σ] (t : ℕ) : 2 * (a.hallados t).card ≤ Fintype.card σ + 1 := by
  classical
  set F := a.hallados t
  -- las que se devuelven en el primer alto
  let alto : Y → Prop := fun y => ∃ j, (∀ i < j, a.salida (a.trayNo a.inicio i) = none) ∧
    a.salida (a.trayNo a.inicio j) = some y
  have hA : (F.filter alto).card ≤ 1 := by
    refine Finset.card_le_one.2 fun y hy y' hy' => ?_
    obtain ⟨j, h1, h2⟩ := (Finset.mem_filter.1 hy).2
    obtain ⟨j', h1', h2'⟩ := (Finset.mem_filter.1 hy').2
    exact alto_unico h1 h2 h1' h2'
  -- las demás las consulta un estado que no para
  have hB : (F.filter fun y => ¬ alto y).card ≤ (Finset.univ.filter fun x : σ => a.salida x = none).card := by
    calc _ ≤ ((Finset.univ.filter fun x : σ => a.salida x = none).image a.consulta).card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨hyF, hna⟩ := Finset.mem_filter.1 hy
          obtain ⟨j, -, hpre, hfin⟩ := halla_en_trayNo y t a.inicio (Finset.mem_filter.1 hyF).2
          rcases hfin with h | ⟨h, hq⟩
          · exact absurd ⟨j, hpre, h⟩ hna
          · exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, hq⟩
      _ ≤ _ := Finset.card_image_le
  -- y todas necesitan un estado que la devuelva
  have hC : F.card ≤ (Finset.univ.filter fun x : σ => ¬ a.salida x = none).card := by
    have hex : ∀ y ∈ F, ∃ x, a.salida x = some y := fun y hy =>
      corre_salida (Finset.mem_filter.1 hy).2
    let f : Y → σ := fun y => if h : ∃ x, a.salida x = some y then h.choose else a.inicio
    have hf : ∀ y ∈ F, a.salida (f y) = some y := fun y hy => by
      simp only [f, dite_eq_left_of_eq_true (eq_true (hex y hy))]; exact (hex y hy).choose_spec
    refine Finset.card_le_card_of_injOn f (fun y hy => ?_) (fun y hy y' hy' he => ?_)
    · simp [hf y hy]
    · have := hf y hy; rw [he, hf y' hy'] at this; exact (Option.some.inj this).symm
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) alto
  have hsig := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset σ))
    (fun x => a.salida x = none)
  rw [Finset.card_univ] at hsig
  omega

/-- **Las dos cotas juntas**: `|hallados| ≤ min (t + 1) ⌊(|σ| + 1)/2⌋`. -/
theorem hallados_le [Fintype σ] (t : ℕ) :
    (a.hallados t).card ≤ min (t + 1) ((Fintype.card σ + 1) / 2) :=
  le_min (hallados_le_tiempo t) (by have := hallados_le_espacio (a := a) t; omega)

/-- **Con `|σ| ≤ 2^S`**, a lo sumo `2^(S−1)` soluciones (con `S − 1` truncado: `S = 0` da `1`). -/
theorem hallados_le_bits [Fintype σ] {S : ℕ} (hσ : Fintype.card σ ≤ 2 ^ S) (t : ℕ) :
    (a.hallados t).card ≤ min (t + 1) (2 ^ (S - 1)) := by
  refine le_min (hallados_le_tiempo t) ?_
  have h := hallados_le_espacio (a := a) t
  cases S with
  | zero => simp at hσ ⊢; omega
  | succ S => rw [pow_succ] at hσ; simp; omega

end Hallados

end Automata

/-- **Meta 2, la ley del cubo** (verificador de sí o no): con `|P| ≤ 2^L` programas, `|C| ≤ 2^s` citas y autómatas
de `|σ| ≤ 2^S` estados que resuelven en `t` consultas, `N ≤ 2^L · 2^s · min (t + 1) 2^(S−1)`. -/
theorem ley_cubo {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y] {L s S t : ℕ}
    (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S)
    (A : P → C → Automata σ Y Bool Y) (h : ResuelveA igual A t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S - 1)) := by
  have hc := cubrir (ι := P × C)
    (fun pc y => (A pc.1 pc.2).corre (igual y) t (A pc.1 pc.2).inicio = some y) (min (t + 1) (2 ^ (S - 1)))
    (fun pc => Automata.hallados_le_bits hσ t) (fun y => by obtain ⟨p, c, hy⟩ := h y; exact ⟨(p, c), hy⟩)
  rw [Fintype.card_prod] at hc
  calc Fintype.card Y ≤ Fintype.card P * Fintype.card C * min (t + 1) (2 ^ (S - 1)) := hc
    _ ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S - 1)) := by gcongr

/-- `min (t + 1) 2^(S−1) ≤ 2^(min ⌈log₂(t+1)⌉ (S−1))`. -/
theorem min_le_pow_min (t S : ℕ) :
    min (t + 1) (2 ^ (S - 1)) ≤ 2 ^ min (Nat.clog 2 (t + 1)) (S - 1) := by
  rcases le_total (Nat.clog 2 (t + 1)) (S - 1) with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans (Nat.le_pow_clog one_lt_two _)
  · rw [min_eq_right h]; exact min_le_right _ _

/-- **La ley del cubo en bits**: `⌈log₂ N⌉ ≤ L + s + min ⌈log₂(t+1)⌉ (S − 1)`. -/
theorem ley_cubo_log {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S)
    (A : P → C → Automata σ Y Bool Y) (h : ResuelveA igual A t) :
    Nat.clog 2 (Fintype.card Y) ≤ L + s + min (Nat.clog 2 (t + 1)) (S - 1) := by
  apply Nat.clog_le_of_le_pow
  calc Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S - 1)) := ley_cubo hP hC hσ A h
    _ ≤ 2 ^ L * 2 ^ s * 2 ^ min (Nat.clog 2 (t + 1)) (S - 1) := by gcongr; exact min_le_pow_min t S
    _ = 2 ^ (L + s + min (Nat.clog 2 (t + 1)) (S - 1)) := by rw [pow_add, pow_add]

/-! ## 4. Con un verificador informativo -/

namespace Automata

section General

variable {σ Q R Y : Type} [DecidableEq Y] [Fintype Y] {a : Automata σ Q R Y}

/-- **Con cualquier verificador, a lo sumo `|σ|` soluciones**: cada una la devuelve un estado distinto. -/
theorem hallados_gen_le_estados [Fintype σ] (O : Y → Q → R) (t : ℕ) :
    (Finset.univ.filter fun y => a.corre (O y) t a.inicio = some y).card ≤ Fintype.card σ := by
  classical
  have hex : ∀ y ∈ Finset.univ.filter (fun y => a.corre (O y) t a.inicio = some y), ∃ x, a.salida x = some y :=
    fun y hy => corre_salida (Finset.mem_filter.1 hy).2
  let f : Y → σ := fun y => if h : ∃ x, a.salida x = some y then h.choose else a.inicio
  have hf : ∀ y ∈ Finset.univ.filter (fun y => a.corre (O y) t a.inicio = some y), a.salida (f y) = some y :=
    fun y hy => by
      simp only [f, dite_eq_left_of_eq_true (eq_true (hex y hy))]; exact (hex y hy).choose_spec
  calc _ ≤ (Finset.univ : Finset σ).card := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _)
          (fun y hy y' hy' he => by
            have := hf y hy; rw [he, hf y' hy'] at this; exact (Option.some.inj this).symm)
    _ = Fintype.card σ := Finset.card_univ

omit [Fintype Y] in
/-- **Con respuestas de `b` bits, a lo sumo `(2^b)^t` soluciones** (es `halla_le` para autómatas): cada solución hallada
queda determinada por la sucesión de respuestas que oye. -/
theorem halla_gen [Fintype R] {b : ℕ} (hR : Fintype.card R ≤ 2 ^ b) (O : Y → Q → R) :
    ∀ (t : ℕ) (x : σ) (T : Finset Y), (T.filter fun y => a.corre (O y) t x = some y).card ≤ (2 ^ b) ^ t
  | 0, x, T => by
      calc _ ≤ ((a.salida x).toFinset).card := Finset.card_le_card fun y hy => by
              rw [Finset.mem_filter] at hy; simp [← hy.2, corre_cero]
        _ ≤ 1 := by rw [Option.card_toFinset]; cases a.salida x <;> simp
        _ ≤ _ := Nat.one_le_pow _ _ (by positivity)
  | t + 1, x, T => by
      classical
      cases hs : a.salida x with
      | some z =>
          calc _ ≤ ({z} : Finset Y).card := Finset.card_le_card fun y hy => by
                  rw [Finset.mem_filter, corre_some hs] at hy; simp [Option.some.inj hy.2]
            _ = 1 := Finset.card_singleton z
            _ ≤ _ := Nat.one_le_pow _ _ (by positivity)
      | none =>
          calc _ ≤ (Finset.univ.biUnion fun r : R => (T.filter fun y => O y (a.consulta x) = r).filter
                  fun y => a.corre (O y) t (a.δ x r) = some y).card := by
                apply Finset.card_le_card
                intro y hy
                rw [Finset.mem_filter, corre_none hs] at hy
                simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
                exact ⟨_, ⟨hy.1, rfl⟩, hy.2⟩
            _ ≤ ∑ r : R, ((T.filter fun y => O y (a.consulta x) = r).filter
                  fun y => a.corre (O y) t (a.δ x r) = some y).card := Finset.card_biUnion_le
            _ ≤ ∑ _r : R, (2 ^ b) ^ t := Finset.sum_le_sum fun r _ => halla_gen hR O t _ _
            _ = Fintype.card R * (2 ^ b) ^ t := by simp
            _ ≤ 2 ^ b * (2 ^ b) ^ t := Nat.mul_le_mul_right _ hR
            _ = (2 ^ b) ^ (t + 1) := (pow_succ' _ _).symm

end General

end Automata

/-- **La ley del cubo con un verificador de `b` bits**: `N ≤ 2^L · 2^s · min (2^(b·t)) 2^S`. En bits,
`⌈log₂ N⌉ ≤ L + s + min (b·t) S`. El tiempo ya no rinde `log₂(t+1)` sino `b·t`, y el tope del espacio queda en `S`
(no en `S − 1`): con respuestas informativas un solo estado que consulta puede repartir en muchos que devuelven. -/
theorem ley_cubo_general {P C σ Q R Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype R] [Fintype Y]
    {L s S b t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (hR : Fintype.card R ≤ 2 ^ b) (O : Y → Q → R)
    (A : P → C → Automata σ Q R Y) (h : ResuelveA O A t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (2 ^ (b * t)) (2 ^ S) := by
  classical
  have hc := cubrir (ι := P × C)
    (fun pc y => (A pc.1 pc.2).corre (O y) t (A pc.1 pc.2).inicio = some y) (min (2 ^ (b * t)) (2 ^ S))
    (fun pc => le_min (by rw [pow_mul]; exact Automata.halla_gen hR O t _ _)
      ((Automata.hallados_gen_le_estados O t).trans hσ))
    (fun y => by obtain ⟨p, c, hy⟩ := h y; exact ⟨(p, c), hy⟩)
  rw [Fintype.card_prod] at hc
  calc Fintype.card Y ≤ Fintype.card P * Fintype.card C * min (2 ^ (b * t)) (2 ^ S) := hc
    _ ≤ _ := by gcongr

theorem ley_cubo_general_log {P C σ Q R Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype R] [Fintype Y]
    {L s S b t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (hR : Fintype.card R ≤ 2 ^ b) (O : Y → Q → R)
    (A : P → C → Automata σ Q R Y) (h : ResuelveA O A t) :
    Nat.clog 2 (Fintype.card Y) ≤ L + s + min (b * t) S := by
  apply Nat.clog_le_of_le_pow
  calc Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (2 ^ (b * t)) (2 ^ S) := ley_cubo_general hP hC hσ hR O A h
    _ = 2 ^ L * 2 ^ s * 2 ^ min (b * t) S := by
        congr 1; rcases le_total (b * t) S with h | h
        · rw [min_eq_left h, min_eq_left (Nat.pow_le_pow_right (by norm_num) h)]
        · rw [min_eq_right h, min_eq_right (Nat.pow_le_pow_right (by norm_num) h)]
    _ = _ := by rw [pow_add, pow_add]

/-! ## 5. Controles: la ley se alcanza -/

/-- **Renombrar un autómata** por una biyección de las instancias (como `mapear` del plano). -/
def mapearA {σ Y Y' : Type} (e : Y ≃ Y') (a : Automata σ Y' Bool Y') : Automata σ Y Bool Y where
  inicio := a.inicio
  consulta := fun x => e.symm (a.consulta x)
  δ := a.δ
  salida := fun x => (a.salida x).map e.symm

theorem mapearA_corre {σ Y Y' : Type} [DecidableEq Y] [DecidableEq Y'] (e : Y ≃ Y') (a : Automata σ Y' Bool Y')
    (y : Y) : ∀ (t : ℕ) (x : σ), (mapearA e a).corre (igual y) t x = (a.corre (igual (e y)) t x).map e.symm
  | 0, x => rfl
  | t + 1, x => by
      have hq : igual y (e.symm (a.consulta x)) = igual (e y) (a.consulta x) := by
        simp only [igual]; congr 1; exact propext (Equiv.symm_apply_eq e)
      cases hs : a.salida x with
      | some z =>
          rw [corre_some hs]
          exact corre_some (a := mapearA e a) (by simp [mapearA, hs]) _
      | none =>
          rw [corre_none hs, corre_none (a := mapearA e a) (by simp [mapearA, hs])]
          simp only [mapearA] at hq ⊢
          rw [hq]
          exact mapearA_corre e a y t _

/-- **El barrido como autómata.** Las soluciones son pares `(c, i)`: la cita da la parte alta `c` y el autómata barre
la parte baja `i ∈ {0, …, n}`. Estados: `inr i` (`i < n`) consulta `(c, i)`; `inl i` (`i ≤ n`) devuelve `(c, i)`. Si
`inr i` oye «sí», pasa a `inl i`; si oye «no», a `inr (i+1)`, o a `inl n` (el último se devuelve sin preguntar, como
en `fuerza_bruta`). Son `2n + 1` estados: la mitad pregunta y la otra mitad responde. -/
def barridoA (j n : ℕ) (c : Fin (2 ^ j)) :
    Automata (Fin (n + 1) ⊕ Fin n) (Fin (2 ^ j) × Fin (n + 1)) Bool (Fin (2 ^ j) × Fin (n + 1)) where
  inicio := if h : 0 < n then .inr ⟨0, h⟩ else .inl (Fin.last n)
  consulta := fun
    | .inl i => (c, i)
    | .inr i => (c, i.castSucc)
  δ := fun
    | .inl i, _ => .inl i
    | .inr i, r => if r then .inl i.castSucc else if h : i.val + 1 < n then .inr ⟨i.val + 1, h⟩ else .inl (Fin.last n)
  salida := fun
    | .inl i => some (c, i)
    | .inr _ => none

theorem card_barridoA (n : ℕ) : Fintype.card (Fin (n + 1) ⊕ Fin n) = 2 * n + 1 := by simp; omega

theorem barridoA_paso (j n : ℕ) (c : Fin (2 ^ j)) (y : Fin (2 ^ j) × Fin (n + 1)) (t i : ℕ) (hi : i < n) :
    (barridoA j n c).corre (igual y) (t + 1) (.inr ⟨i, hi⟩) =
      (barridoA j n c).corre (igual y) t ((barridoA j n c).δ (.inr ⟨i, hi⟩)
        (igual y (c, (⟨i, hi⟩ : Fin n).castSucc))) :=
  corre_none rfl t

theorem barridoA_no (j n : ℕ) (c : Fin (2 ^ j)) (i : ℕ) (hi : i < n) :
    (barridoA j n c).δ (.inr ⟨i, hi⟩) false =
      if h : i + 1 < n then .inr ⟨i + 1, h⟩ else .inl (Fin.last n) := rfl

theorem igual_no {j n : ℕ} {c : Fin (2 ^ j)} {i₀ : Fin (n + 1)} {i : ℕ} (hi : i < n) (h : i ≠ i₀.val) :
    igual (c, i₀) (c, (⟨i, hi⟩ : Fin n).castSucc) = false := by
  simp only [igual, decide_eq_false_iff_not, Prod.mk.injEq, true_and]
  intro he; exact h (congrArg Fin.val he)

/-- Una solución que no es la última se halla consultándola: desde `inr i`, con `i + d = i₀ < n`, en `d + 1` pasos. -/
theorem barridoA_medio (j n : ℕ) (c : Fin (2 ^ j)) (i₀ : Fin (n + 1)) (h₀ : i₀.val < n) :
    ∀ (d i : ℕ) (hi : i < n), i + d = i₀.val →
      (barridoA j n c).corre (igual (c, i₀)) (d + 1) (.inr ⟨i, hi⟩) = some (c, i₀)
  | 0, i, hi, hd => by
      have he : (⟨i, hi⟩ : Fin n).castSucc = i₀ := Fin.ext (by simp; omega)
      have ht : igual (c, i₀) (c, (⟨i, hi⟩ : Fin n).castSucc) = true := by simp [igual, he]
      rw [barridoA_paso, ht]
      change some (c, (⟨i, hi⟩ : Fin n).castSucc) = some (c, i₀)
      rw [he]
  | d + 1, i, hi, hd => by
      have hi1 : i + 1 < n := by omega
      rw [barridoA_paso, igual_no hi (by omega), barridoA_no]
      simp only [hi1, ↓reduceDIte]
      exact barridoA_medio j n c i₀ h₀ d (i + 1) hi1 (by omega)

/-- La última solución se devuelve sin preguntar: desde `inr i`, con `i + d + 1 = n`, en `d + 1` pasos. -/
theorem barridoA_ultimo (j n : ℕ) (c : Fin (2 ^ j)) :
    ∀ (d i : ℕ) (hi : i < n), i + d + 1 = n →
      (barridoA j n c).corre (igual (c, Fin.last n)) (d + 1) (.inr ⟨i, hi⟩) = some (c, Fin.last n)
  | 0, i, hi, hd => by
      have hi1 : ¬ i + 1 < n := by omega
      rw [barridoA_paso, igual_no hi (by simp; omega), barridoA_no]
      simp only [hi1, ↓reduceDIte]
      rfl
  | d + 1, i, hi, hd => by
      have hi1 : i + 1 < n := by omega
      rw [barridoA_paso, igual_no hi (by simp; omega), barridoA_no]
      simp only [hi1, ↓reduceDIte]
      exact barridoA_ultimo j n c d (i + 1) hi1 (by omega)

/-- **El barrido resuelve en `n` consultas**, con la cita como parte alta. -/
theorem barridoA_resuelve (j n : ℕ) :
    ResuelveA (P := Unit) (C := Fin (2 ^ j)) igual (fun _ c => barridoA j n c) n := by
  rintro ⟨c, i₀⟩
  refine ⟨(), c, ?_⟩
  by_cases hn : 0 < n
  · have hini : (barridoA j n c).inicio = .inr ⟨0, hn⟩ := by simp [barridoA, hn]
    rw [hini]
    by_cases h₀ : i₀.val < n
    · have := barridoA_medio j n c i₀ h₀ i₀.val 0 hn (by omega)
      have := corre_mono (n - (i₀.val + 1)) this
      rwa [show i₀.val + 1 + (n - (i₀.val + 1)) = n by omega] at this
    · have hl : i₀ = Fin.last n := Fin.ext (by simp; omega)
      subst hl
      have := barridoA_ultimo j n c (n - 1) 0 hn (by omega)
      rwa [show n - 1 + 1 = n by omega] at this
  · have hn0 : n = 0 := by omega
    subst hn0
    have hl : i₀ = Fin.last 0 := Fin.ext (by have := i₀.isLt; simp)
    subst hl
    rfl

/-! ## 6. El cubo, la región y sus caras -/

/-- **Un punto del cubo** `(x, e, y)` se alcanza con el verificador de sí o no sobre `N = 2^m`: hay programas
`|P| ≤ 2^L`, citas `|C| ≤ 2^s` y autómatas de `|σ| ≤ 2^S` estados que resuelven en `t` consultas, con `L + s ≤ x`
(descripción), `S ≤ e` (espacio) y `⌈log₂(t+1)⌉ ≤ y` (tiempo en bits). -/
def AlcanzableCubo (m x e y : ℕ) : Prop :=
  ∃ (P C σ : Type) (_ : Fintype P) (_ : Fintype C) (_ : Fintype σ)
    (A : P → C → Automata σ (Fin (2 ^ m)) Bool (Fin (2 ^ m))) (L s S t : ℕ),
    Fintype.card P ≤ 2 ^ L ∧ Fintype.card C ≤ 2 ^ s ∧ Fintype.card σ ≤ 2 ^ S ∧ ResuelveA (siNo m) A t ∧
      L + s ≤ x ∧ S ≤ e ∧ Nat.clog 2 (t + 1) ≤ y

/-- **La región del cubo es cerrada hacia arriba.** -/
theorem cubo_cerrado_arriba {m x e y x' e' y' : ℕ} (h : AlcanzableCubo m x e y) (hx : x ≤ x') (he : e ≤ e')
    (hy : y ≤ y') : AlcanzableCubo m x' e' y' := by
  obtain ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, h1, h2, h3, h4, by omega, by omega, by omega⟩

/-- **Toda la región cumple la ley**: `m ≤ x + min y (e − 1)`. -/
theorem cubo_sobre_ley {m x e y : ℕ} (h : AlcanzableCubo m x e y) : m ≤ x + min y (e - 1) := by
  obtain ⟨P, C, σ, iP, iC, iσ, A, L, s, S, t, hP, hC, hσ, hA, hx, he, hy⟩ := h
  have := ley_cubo_log hP hC hσ A hA
  rw [Fintype.card_fin, Nat.clog_pow 2 m one_lt_two] at this
  omega

/-- **Los puntos de la frontera se alcanzan**: para `k ≤ m`, cita de `m − k` bits, `2^k − 1` consultas y el barrido
de `2^(k+1) − 1` estados, o sea `S = k + 1` bits (`S = 0` si `k = 0`: un estado que devuelve la cita). -/
theorem punto_cubo {m k : ℕ} (hk : k ≤ m) : AlcanzableCubo m (m - k) (if k = 0 then 0 else k + 1) k := by
  have hcard : Fintype.card (Fin (2 ^ m)) = Fintype.card (Fin (2 ^ (m - k)) × Fin (2 ^ k - 1 + 1)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_add, Nat.sub_add_cancel hk]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨Unit, Fin (2 ^ (m - k)), Fin (2 ^ k - 1 + 1) ⊕ Fin (2 ^ k - 1), inferInstance, inferInstance,
    inferInstance, fun _ c => mapearA e (barridoA (m - k) (2 ^ k - 1) c), 0, m - k,
    if k = 0 then 0 else k + 1, 2 ^ k - 1, by simp, by simp, ?_, ?_, by omega, le_rfl, ?_⟩
  · rw [card_barridoA]
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
  · rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.clog_pow 2 k one_lt_two]

/-- **La región del cubo, exacta**: `(x, e, y)` se alcanza si y solo si `m ≤ x + min y (e − 1)`. -/
theorem cubo_es_region (m x e y : ℕ) : AlcanzableCubo m x e y ↔ m ≤ x + min y (e - 1) := by
  refine ⟨cubo_sobre_ley, fun h => ?_⟩
  have hk : min (min y (e - 1)) m ≤ m := min_le_right _ _
  refine cubo_cerrado_arriba (punto_cubo hk) ?_ ?_ ?_
  · omega
  · split_ifs <;> omega
  · omega

/-! ### Las caras como cortes -/

/-- **Cara del plano** (Meta 3): con espacio de sobra, `y < e` (o sea `2^(S−1) ≥ t + 1` en el mejor caso), el corte del
cubo es el plano de costos: se alcanza `(x, e, y)` si y solo si se alcanza `(x, y)` en `PlanoCostos`, y los dos son
`x + y ≥ m` (`region_es_semiplano`). -/
theorem cara_plano {m x e y : ℕ} (h : y < e) : AlcanzableCubo m x e y ↔ Alcanzable (siNo m) x y := by
  rw [cubo_es_region, region_es_semiplano, min_eq_left (by omega)]

/-- **Todo punto del cubo proyecta al plano**: olvidar el espacio no saca de la región del plano. -/
theorem cubo_a_plano {m x e y : ℕ} (h : AlcanzableCubo m x e y) : Alcanzable (siNo m) x y := by
  rw [region_es_semiplano]; have := cubo_sobre_ley h; omega

/-- **La ley del cubo contiene la del plano**: con autómatas, `N ≤ 2^L · 2^s · (t + 1)`, como `ley_si_no`. -/
theorem ley_cubo_plano {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S)
    (A : P → C → Automata σ Y Bool Y) (h : ResuelveA igual A t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * (t + 1) :=
  (ley_cubo hP hC hσ A h).trans (Nat.mul_le_mul_left _ (min_le_left _ _))

/-- **Cara del bombeo** (Meta 3): con tiempo de sobra, `e − 1 ≤ y`, el espacio pone el tope: `x + (e − 1) ≥ m`. -/
theorem cara_bombeo {m x e y : ℕ} (h : e - 1 ≤ y) : AlcanzableCubo m x e y ↔ m ≤ x + (e - 1) := by
  rw [cubo_es_region, min_eq_right h]

/-- **El tiempo sin memoria para contarlo no rinde**: pasado `e − 1` bits de tiempo, más tiempo no cambia nada. -/
theorem tiempo_no_rinde {m x e y y' : ℕ} (hy : e - 1 ≤ y) (hy' : e - 1 ≤ y') :
    AlcanzableCubo m x e y ↔ AlcanzableCubo m x e y' := by
  rw [cara_bombeo hy, cara_bombeo hy']

/-- **Cara de la tabla**: con `x ≥ m` bits escritos antes, basta un estado y ninguna consulta. -/
theorem cara_tabla {m x : ℕ} (h : m ≤ x) : AlcanzableCubo m x 0 0 := by
  rw [cubo_es_region]; omega

/-! ### Controles (Meta 4) -/

/-- **El contador alcanza la recta del plano**: cita de `m − k` bits, `2^k − 1` consultas y `k + 1` bits de espacio.
`(m − k) + k = m`: está en la recta. -/
theorem contador_en_la_recta {m k : ℕ} (hk : k ≤ m) : AlcanzableCubo m (m - k) (k + 1) k :=
  cubo_cerrado_arriba (punto_cubo hk) le_rfl (by split_ifs <;> omega) le_rfl

/-- **Y el bit de más hace falta**: con `S = k = ⌈log₂(t+1)⌉` bits (sin el `+1`) el contador no alcanza, para `k ≥ 1`.
Ese bit separa los estados que preguntan de los que responden. -/
theorem contador_sin_bit_extra {m k : ℕ} (h1 : 1 ≤ k) (hk : k ≤ m) : ¬ AlcanzableCubo m (m - k) k k := by
  rw [cubo_es_region]; omega

/-- **Con `2^S ≤ t`, el tiempo no compra nada más**: sin descripción ni cita, `2^S` estados con `t ≥ 2^S` consultas
resuelven `2^m` candidatos si y solo si `m ≤ S − 1`. -/
theorem mucho_tiempo_no_sirve {m S t : ℕ} (ht : 2 ^ S ≤ t) :
    AlcanzableCubo m 0 S (Nat.clog 2 (t + 1)) ↔ m ≤ S - 1 := by
  have : S - 1 ≤ Nat.clog 2 (t + 1) := by
    have h1 : S - 1 < Nat.clog 2 (t + 1) := by
      rw [Nat.lt_clog_iff_pow_lt one_lt_two]
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.sub_le S 1)
      omega
    omega
  rw [cara_bombeo this]; omega

/-- **Un autómata de `2^S` estados no halla más de `2^(S−1)` candidatos**, con cualquier tiempo. -/
theorem espacio_topa {σ Y : Type} [Fintype σ] [Fintype Y] [DecidableEq Y] {S : ℕ}
    (a : Automata σ Y Bool Y) (hσ : Fintype.card σ ≤ 2 ^ S) (t : ℕ) : (a.hallados t).card ≤ 2 ^ (S - 1) :=
  (Automata.hallados_le_bits hσ t).trans (min_le_right _ _)

/-- **La cita compensa la falta de espacio**: con `S ≥ 1` bits de espacio y cita de `m − (S − 1)` bits se resuelve
(en `2^(S−1) − 1` consultas); con un bit menos de cita, `m − S`, ya no, con ningún tiempo. -/
theorem cita_compensa {m S : ℕ} (h1 : 1 ≤ S) (hS : S ≤ m) :
    AlcanzableCubo m (m - (S - 1)) S (S - 1) ∧ ∀ y, ¬ AlcanzableCubo m (m - S) S y := by
  refine ⟨by rw [cubo_es_region]; omega, fun y => by rw [cubo_es_region]; omega⟩

/-! ## 7. Mutantes -/

/-! ### Mutante 1: regalar el contador de pasos -/

/-- **Un autómata con reloj** (el modelo PROHIBIDO): la consulta, la transición y la salida reciben el número de paso.
Es lo que pasa en los programas por niveles: el reloj es gratis y no se cuenta en `σ`. -/
structure AutomataReloj (σ Q R Y : Type) where
  inicio : σ
  consulta : ℕ → σ → Q
  δ : ℕ → σ → R → σ
  salida : ℕ → σ → Option Y

/-- La corrida del autómata con reloj: presupuesto, paso actual, estado. -/
def AutomataReloj.corre {σ Q R Y : Type} (a : AutomataReloj σ Q R Y) (O : Q → R) : ℕ → ℕ → σ → Option Y
  | 0, i, x => a.salida i x
  | t + 1, i, x =>
    match a.salida i x with
    | some y => some y
    | none => AutomataReloj.corre a O t (i + 1) (a.δ i x (O (a.consulta i x)))

/-- **El barrido con reloj y dos estados**: el estado solo dice si ya oyó «sí»; el reloj dice qué consultar y qué
devolver. -/
def relojBarrido : AutomataReloj Bool (Fin 4) Bool (Fin 4) where
  inicio := false
  consulta := fun i _ => ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩
  δ := fun _ b r => b || r
  salida := fun i b => if b then some ⟨(i - 1) % 4, Nat.mod_lt _ (by norm_num)⟩ else if i = 3 then some 3 else none

theorem relojBarrido_resuelve : ∀ y : Fin 4, relojBarrido.corre (igual y) 3 0 relojBarrido.inicio = some y := by
  decide

/-- **Mutante 1, refutado**: con el reloj regalado, un autómata de **2 estados** (`S = 1`) resuelve los `4` candidatos
en `3` consultas, y la ley del cubo con `min` pediría `4 ≤ min (3 + 1) 2^0 = 1`. La ley con `min` cae. (La del plano,
`4 ≤ 3 + 1`, se cumple con igualdad: el reloj convierte tiempo en espacio gratis.) -/
theorem mutante_reloj :
    (∀ y : Fin 4, relojBarrido.corre (igual y) 3 0 relojBarrido.inicio = some y) ∧ Fintype.card Bool ≤ 2 ^ 1 ∧
      ¬ (Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (3 + 1) (2 ^ (1 - 1))) :=
  ⟨relojBarrido_resuelve, by simp, by simp⟩

/-! ### Mutante 2: sacar el `min` (solo el tiempo) -/

/-- **Mutante 2, refutado**: `x + y ≥ m` (la ley del plano, sin `min`) no basta en el cubo: con `e = 0` (un estado) y
`y = 1`, `m = 1` no se alcanza. La desigualdad `m ≤ x + y` sigue valiendo (`cubo_a_plano`); lo falso es que sea la
frontera del cubo. -/
theorem mutante_sin_min : ¬ ∀ m x e y : ℕ, m ≤ x + y → AlcanzableCubo m x e y := fun h => by
  have := h 1 0 0 1 (by norm_num)
  rw [cubo_es_region] at this; omega

/-! ### Mutante 3: sacar `S` (no acotar los estados) -/

/-- **Mutante 3, refutado**: sin la hipótesis `|σ| ≤ 2^S`, la ley con `S = 0` (un estado, «el espacio no cuenta») es
falsa: el barrido de `3` estados resuelve `2` candidatos sin cita. -/
theorem mutante_sin_espacio : ¬ ∀ (σ Y : Type) [Fintype σ] [Fintype Y] [DecidableEq Y]
    (A : Unit → Unit → Automata σ Y Bool Y) (t : ℕ), ResuelveA igual A t → Fintype.card Y ≤ min (t + 1) (2 ^ (0 - 1)) :=
  fun h => by
    have hA : ResuelveA (P := Unit) (C := Unit) igual (fun _ _ => barridoA 0 1 0) 1 := by
      intro y
      obtain ⟨p, c, hc⟩ := barridoA_resuelve 0 1 y
      refine ⟨p, (), ?_⟩
      have : c = 0 := Fin.ext (by have := c.isLt; simp at this ⊢)
      rwa [this] at hc
    have := h _ _ _ 1 hA
    simp at this

/-! ### Mutante 4: sacar el `−1` (la conjetura tal cual, como frontera) -/

/-- **Mutante 4, refutado**: `L + s + min(⌈log₂(t+1)⌉, S) ≥ m`, la conjetura sin el `−1`, es cota válida pero **no** es
la frontera: `(x, e, y) = (0, 1, 1)` la cumple con `m = 1` y no se alcanza. Dos estados no alcanzan para preguntar y
además devolver dos respuestas distintas. -/
theorem mutante_sin_menos_uno : ¬ ∀ m x e y : ℕ, m ≤ x + min y e → AlcanzableCubo m x e y := fun h => by
  have := h 1 0 1 1 (by norm_num)
  rw [cubo_es_region] at this; omega

/-! ### Mutante 5: un verificador de `b` bits -/

/-- **Leer los bits de la solución**: la consulta `q` pregunta el bit `q` de `y`. -/
def bitDe (y : Fin 4) (q : Fin 2) : Bool := Nat.testBit y.val q.val

/-- **El lector de dos bits**: `inl none` lee el bit 0, `inl (some b₀)` lee el bit 1, `inr y` devuelve `y`. Siete
estados (`S = 3`), dos consultas. -/
def lectorBits : Automata (Option Bool ⊕ Fin 4) (Fin 2) Bool (Fin 4) where
  inicio := .inl none
  consulta := fun
    | .inl none => 0
    | _ => 1
  δ := fun
    | .inl none, r => .inl (some r)
    | .inl (some b₀), r => .inr ⟨b₀.toNat + 2 * r.toNat, by cases b₀ <;> cases r <;> decide⟩
    | .inr y, _ => .inr y
  salida := fun
    | .inr y => some y
    | .inl _ => none

theorem lectorBits_resuelve : ∀ y : Fin 4, lectorBits.corre (bitDe y) 2 lectorBits.inicio = some y := by
  decide

/-- **Mutante 5, refutado**: con un verificador de `1` bit **informativo** la ley del sí o no es falsa: `7 ≤ 2^3`
estados y `2` consultas hallan `4` candidatos, y la ley pediría `4 ≤ min (2 + 1) 2^(3−1) = 3`. Lo que vale es
`ley_cubo_general`: `4 ≤ min (2^(1·2)) 2^3`, con igualdad en el primer término. -/
theorem mutante_bits :
    ResuelveA (P := Unit) (C := Unit) bitDe (fun _ _ => lectorBits) 2 ∧
      Fintype.card (Option Bool ⊕ Fin 4) ≤ 2 ^ 3 ∧
      ¬ (Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (2 + 1) (2 ^ (3 - 1))) ∧
      Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (2 ^ (1 * 2)) (2 ^ 3) :=
  ⟨fun y => ⟨(), (), lectorBits_resuelve y⟩, by simp, by simp, by simp⟩

end Sagitta.Map.Tiempo.CuboCostos
