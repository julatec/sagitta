import Sagitta.Map.CuboNoDeterminista

/-!
# La CHT: el reloj se paga en memoria

Las notas del proyecto llaman **CHT** (conservación de la
homogeneidad del tiempo) a la simetría que todos los modelos usan sin decirlo: la regla no sabe en qué instante está.
Deja en cola: «un autómata que depende del tiempo, con un reloj de `c` bits, equivale a uno homogéneo con `c` bits más de
memoria, en las dos direcciones. El reloj se paga en memoria.» Este archivo lo prueba, con el cubo y el cubo no
determinista como casos.

## 1. El modelo con reloj

`AutomataConReloj κ σ Q R Y`: como `Automata` de `CuboCostos`, pero la consulta, la transición y la salida reciben además
el valor de un registro de tiempo `κ`, que empieza en `reloj0` y avanza con `tic`. Los dos relojes del enunciado:

* **de `c` bits** (`ticMod`): `κ = Fin (2^c)`, el paso módulo `2^c`;
* **hasta un tope `T`** (`ticTope`): `κ = Fin (T + 1)`, el paso saturado en `T`.

`tic` puede mirar el estado (`κ → σ → κ`): así entra también el contador de elecciones de `CuboNoDeterminista`, que solo
avanza cuando el estado elige (§ 4). Un **reloj de paso** es el caso en que `tic` no mira el estado.

El reloj libre de `CuboCostos` (`AutomataReloj`, con el paso en `ℕ`) se trunca sin perder nada: corrido `t` pasos desde
el paso `0`, solo ve pasos `≤ t`, y coincide con el de tope `T = t` (`truncar_corre`). Si sus funciones solo dependen del
paso módulo `2^c`, coincide con el de `c` bits para cualquier presupuesto (`truncarMod_corre`).

## 2. Noether para la homogeneidad, en las dos direcciones

* **(a) Homogéneo = con reloj que lo ignora** (`conReloj_corre`, `olvidar_corre`): todo `Automata` es un autómata con
  cualquier reloj que no lo mira, y todo autómata con reloj cuyas funciones no miran el reloj es el homogéneo que se
  obtiene olvidándolo. Mismas salidas y mismas consultas (`conReloj_traza`).
* **(b) El reloj se paga en memoria** (`homogeneizar`, `homogeneizar_corre`, `homogeneizar_traza`): todo autómata con
  reloj `κ` es un `Automata` homogéneo sobre `σ × κ`, con las mismas salidas, las mismas consultas en el mismo orden y,
  por lo tanto, el mismo número de pasos. Con `c` bits, `σ × Fin (2^c)`; con tope, `σ × Fin (T + 1)`.
* **(c) La ley del cubo con reloj** (`ley_cubo_reloj`, `ley_cubo_reloj_log`): con `|σ| ≤ 2^S` y `|κ| ≤ 2^c`,
  `N ≤ 2^L · 2^s · min (t + 1) 2^(S + c − 1)`, o sea `⌈log₂ N⌉ ≤ L + s + min ⌈log₂(t+1)⌉ (S + c − 1)`.
  **El reloj entra en el eje del espacio**: `e` pasa a `e + c`, y el término del tiempo no cambia. Para el reloj libre
  de `CuboCostos` (`ley_cubo_reloj_libre`), `c = ⌈log₂(t+1)⌉`:
  `⌈log₂ N⌉ ≤ L + s + min ⌈log₂(t+1)⌉ (S + ⌈log₂(t+1)⌉ − 1)`.
  El control es `mutante_reloj` (`control_reloj`): sus 2 estados y su reloj resuelven 4 candidatos en 3 consultas; la ley
  sin el reloj pide `4 ≤ 1` y falla; con los `2` bits del reloj contados pide `4 ≤ min 4 2^(1+2−1) = 4`, y se cumple con
  igualdad; con un bit de reloj menos pediría `4 ≤ 2`, y falla. El precio del reloj, en ese ejemplo, es exacto.

## 3. La carga de Noether

En un autómata homogéneo, si dos corridas (con el mismo verificador) llegan al **mismo estado** en tiempos `i` y `j`,
sin haber parado, toda la continuación es igual: `corre O (i + t) x = corre O (j + t) x'`, y los estados siguientes
coinciden (`carga_noether`). En particular una misma corrida que vuelve a un estado no sabe si está en `i` o en `j`
(`no_sabe_la_hora`). **El tiempo no deja huella fuera del estado.** Con reloj, falla: la versión con reloj del barrido
de `mutante_reloj` pasa por el estado `false` en el paso `0` y en el paso `3`, y desde ahí la continuación es distinta
(`reloj_deja_huella`).

## 4. El contador de `fijarFin` como caso de 2(b)

`fijarFin a bs w` es exactamente `homogeneizar` del autómata con reloj `Fin (w + 1)` cuyo `tic` avanza solo en los
estados que eligen (`fijarFin_es_homogeneizar`): el contador de elecciones es un reloj, y `card_contador` es su precio.

## 5. El ejemplo chico

`barridoTope = truncar relojBarrido 3` es el barrido de `mutante_reloj` con reloj de tope `3` (`2` bits); su versión
homogénea `homogeneizar barridoTope` tiene `2 · 4 = 8` estados y resuelve los 4 candidatos en 3 consultas
(`barridoHomogeneo_resuelve`), con las mismas corridas que el original (`barridoTope_igual`).

## Lo que NO se prueba

* (b) es una construcción de producto y casi definicional; el contenido está en (c), en la carga de Noether y en el
  control. Que `c` bits de reloj sean **necesarios** en general (que no haya simulación homogénea con menos memoria) no
  se prueba: solo que la ley con un bit menos falla en el ejemplo.
* Como todo el cubo, es caja negra y relativiza: nada sobre `P` contra `NP`.
-/

namespace Sagitta.Map.Informacion.Homogeneidad

open Sagitta.Map.Tiempo.LeyTresMemorias
open Sagitta.Map.Tiempo.PlanoCostos
open Sagitta.Map.Tiempo.CuboCostos
open Sagitta.Map.Tiempo.CuboNoDeterminista

/-! ## 1. El modelo con reloj -/

/-- **Un autómata con reloj**: la consulta, la transición y la salida reciben el valor del registro de tiempo `κ`, que
empieza en `reloj0` y avanza con `tic` en cada consulta. -/
structure AutomataConReloj (κ σ Q R Y : Type) where
  inicio : σ
  reloj0 : κ
  tic : κ → σ → κ
  consulta : κ → σ → Q
  δ : κ → σ → R → σ
  salida : κ → σ → Option Y

namespace AutomataConReloj

variable {κ σ Q R Y : Type}

/-- La corrida con a lo sumo `t` consultas, desde el reloj `k` y el estado `x`. -/
def corre (a : AutomataConReloj κ σ Q R Y) (O : Q → R) : ℕ → κ → σ → Option Y
  | 0, k, x => a.salida k x
  | t + 1, k, x =>
    match a.salida k x with
    | some y => some y
    | none => corre a O t (a.tic k x) (a.δ k x (O (a.consulta k x)))

/-- Las consultas que hace, en orden, con a lo sumo `t`. Su largo es el número de pasos. -/
def traza (a : AutomataConReloj κ σ Q R Y) (O : Q → R) : ℕ → κ → σ → List Q
  | 0, _, _ => []
  | t + 1, k, x =>
    match a.salida k x with
    | some _ => []
    | none => a.consulta k x :: traza a O t (a.tic k x) (a.δ k x (O (a.consulta k x)))

end AutomataConReloj

/-- El reloj de `c` bits: el paso módulo `2^c`. -/
def ticMod (c : ℕ) (k : Fin (2 ^ c)) : Fin (2 ^ c) := ⟨(k.val + 1) % 2 ^ c, Nat.mod_lt _ (by positivity)⟩

/-- El reloj con tope `T`: el paso saturado en `T`. -/
def ticTope (T : ℕ) (k : Fin (T + 1)) : Fin (T + 1) := ⟨min (k.val + 1) T, by omega⟩

/-- Las consultas de un autómata homogéneo, en orden. -/
def trazaH {σ Q R Y : Type} (a : Automata σ Q R Y) (O : Q → R) : ℕ → σ → List Q
  | 0, _ => []
  | t + 1, x =>
    match a.salida x with
    | some _ => []
    | none => a.consulta x :: trazaH a O t (a.δ x (O (a.consulta x)))

/-! ### El reloj libre de `CuboCostos`, truncado -/

section Truncar

variable {σ Q R Y : Type}

/-- **Truncar el reloj libre en el tope `T`.** -/
def truncar (a : AutomataReloj σ Q R Y) (T : ℕ) : AutomataConReloj (Fin (T + 1)) σ Q R Y where
  inicio := a.inicio
  reloj0 := 0
  tic := fun k _ => ticTope T k
  consulta := fun k => a.consulta k.val
  δ := fun k => a.δ k.val
  salida := fun k => a.salida k.val

/-- **Hasta el tope, truncar no cambia nada**: con `i + t ≤ T`, la corrida del reloj libre desde el paso `i` es la del
reloj de tope `T`. -/
theorem truncar_corre (a : AutomataReloj σ Q R Y) (T : ℕ) (O : Q → R) :
    ∀ (t i : ℕ) (x : σ) (h : i + t ≤ T), a.corre O t i x = (truncar a T).corre O t ⟨i, by omega⟩ x
  | 0, i, x, _ => rfl
  | t + 1, i, x, h => by
      simp only [AutomataReloj.corre, AutomataConReloj.corre]
      cases hs : a.salida i x with
      | some y => simp [truncar, hs]
      | none =>
          have e : ticTope T ⟨i, by omega⟩ = ⟨i + 1, by omega⟩ := by
            simp only [ticTope, Fin.mk.injEq]; omega
          simp only [truncar, hs, e]
          exact truncar_corre a T O t (i + 1) _ (by omega)

/-- **Un reloj libre periódico es un reloj de `c` bits.** -/
def truncarMod (a : AutomataReloj σ Q R Y) (c : ℕ) : AutomataConReloj (Fin (2 ^ c)) σ Q R Y where
  inicio := a.inicio
  reloj0 := ⟨0, by positivity⟩
  tic := fun k _ => ticMod c k
  consulta := fun k => a.consulta k.val
  δ := fun k => a.δ k.val
  salida := fun k => a.salida k.val

/-- Si las funciones del reloj libre solo dependen del paso módulo `2^c`, la corrida es la del reloj de `c` bits, con
cualquier presupuesto. -/
theorem truncarMod_corre (a : AutomataReloj σ Q R Y) (c : ℕ) (hq : ∀ i, a.consulta i = a.consulta (i % 2 ^ c))
    (hd : ∀ i, a.δ i = a.δ (i % 2 ^ c)) (hs : ∀ i, a.salida i = a.salida (i % 2 ^ c)) (O : Q → R) :
    ∀ (t i : ℕ) (x : σ), a.corre O t i x = (truncarMod a c).corre O t ⟨i % 2 ^ c, Nat.mod_lt _ (by positivity)⟩ x
  | 0, i, x => by simp only [AutomataReloj.corre, AutomataConReloj.corre, truncarMod]; rw [hs]
  | t + 1, i, x => by
      simp only [AutomataReloj.corre, AutomataConReloj.corre]
      have e : ticMod c ⟨i % 2 ^ c, Nat.mod_lt _ (by positivity)⟩ =
          ⟨(i + 1) % 2 ^ c, Nat.mod_lt _ (by positivity)⟩ := by
        simp only [ticMod, Fin.mk.injEq]; exact Nat.mod_add_mod i (2 ^ c) 1
      simp only [truncarMod, e]
      rw [hs i, hq i, hd i]
      cases a.salida (i % 2 ^ c) x with
      | some y => rfl
      | none =>
          simp only
          rw [← hq i, ← hd i]
          have := truncarMod_corre a c hq hd hs O t (i + 1) (a.δ i x (O (a.consulta i x)))
          rw [this]
          rfl

end Truncar

/-! ## 2. Noether para la homogeneidad -/

section Noether

variable {κ σ Q R Y : Type}

/-! ### (a) Homogéneo = con reloj que lo ignora -/

/-- Un autómata homogéneo, visto como uno con cualquier reloj que no mira. -/
def conReloj (a : Automata σ Q R Y) (k₀ : κ) (tic : κ → σ → κ) : AutomataConReloj κ σ Q R Y where
  inicio := a.inicio
  reloj0 := k₀
  tic := tic
  consulta := fun _ => a.consulta
  δ := fun _ => a.δ
  salida := fun _ => a.salida

theorem conReloj_corre (a : Automata σ Q R Y) (k₀ : κ) (tic : κ → σ → κ) (O : Q → R) :
    ∀ (t : ℕ) (k : κ) (x : σ), (conReloj a k₀ tic).corre O t k x = a.corre O t x
  | 0, k, x => rfl
  | t + 1, k, x => by
      simp only [AutomataConReloj.corre, Automata.corre, conReloj]
      cases a.salida x with
      | some y => rfl
      | none => exact conReloj_corre a k₀ tic O t _ _

theorem conReloj_traza (a : Automata σ Q R Y) (k₀ : κ) (tic : κ → σ → κ) (O : Q → R) :
    ∀ (t : ℕ) (k : κ) (x : σ), (conReloj a k₀ tic).traza O t k x = trazaH a O t x
  | 0, k, x => rfl
  | t + 1, k, x => by
      simp only [AutomataConReloj.traza, trazaH, conReloj]
      cases a.salida x with
      | some y => rfl
      | none => simp only; rw [← conReloj_traza a k₀ tic O t]; rfl

/-- **Olvidar el reloj**: el homogéneo que se lee en un valor fijo `k₀` del reloj. -/
def olvidar (a : AutomataConReloj κ σ Q R Y) (k₀ : κ) : Automata σ Q R Y where
  inicio := a.inicio
  consulta := a.consulta k₀
  δ := a.δ k₀
  salida := a.salida k₀

/-- **Si el reloj no se mira, se puede olvidar**: con consulta, transición y salida que no dependen del reloj, la corrida
es la del homogéneo `olvidar a k₀`, desde cualquier valor del reloj. -/
theorem olvidar_corre (a : AutomataConReloj κ σ Q R Y) (k₀ : κ) (hq : ∀ k, a.consulta k = a.consulta k₀)
    (hd : ∀ k, a.δ k = a.δ k₀) (hs : ∀ k, a.salida k = a.salida k₀) (O : Q → R) :
    ∀ (t : ℕ) (k : κ) (x : σ), a.corre O t k x = (olvidar a k₀).corre O t x
  | 0, k, x => by simp only [AutomataConReloj.corre, Automata.corre, olvidar]; rw [hs]
  | t + 1, k, x => by
      simp only [AutomataConReloj.corre, Automata.corre, olvidar]
      rw [hs k, hq k, hd k]
      cases a.salida k₀ x with
      | some y => rfl
      | none => exact olvidar_corre a k₀ hq hd hs O t _ _

/-! ### (b) El reloj se paga en memoria -/

/-- **Homogeneizar**: el reloj pasa a ser parte del estado. Estados `σ × κ`. -/
def homogeneizar (a : AutomataConReloj κ σ Q R Y) : Automata (σ × κ) Q R Y where
  inicio := (a.inicio, a.reloj0)
  consulta := fun z => a.consulta z.2 z.1
  δ := fun z r => (a.δ z.2 z.1 r, a.tic z.2 z.1)
  salida := fun z => a.salida z.2 z.1

/-- **Mismas salidas**: la corrida homogénea desde `(x, k)` es la corrida con reloj desde el reloj `k` y el estado `x`. -/
theorem homogeneizar_corre (a : AutomataConReloj κ σ Q R Y) (O : Q → R) :
    ∀ (t : ℕ) (k : κ) (x : σ), (homogeneizar a).corre O t (x, k) = a.corre O t k x
  | 0, k, x => rfl
  | t + 1, k, x => by
      simp only [AutomataConReloj.corre, Automata.corre, homogeneizar]
      cases a.salida k x with
      | some y => rfl
      | none => exact homogeneizar_corre a O t _ _

/-- **Mismas consultas en el mismo orden, y por lo tanto los mismos pasos.** -/
theorem homogeneizar_traza (a : AutomataConReloj κ σ Q R Y) (O : Q → R) :
    ∀ (t : ℕ) (k : κ) (x : σ), trazaH (homogeneizar a) O t (x, k) = a.traza O t k x
  | 0, k, x => rfl
  | t + 1, k, x => by
      simp only [AutomataConReloj.traza, trazaH, homogeneizar]
      cases a.salida k x with
      | some y => rfl
      | none => simp only; rw [← homogeneizar_traza a O t]; rfl

theorem homogeneizar_pasos (a : AutomataConReloj κ σ Q R Y) (O : Q → R) (t : ℕ) :
    (trazaH (homogeneizar a) O t (homogeneizar a).inicio).length = (a.traza O t a.reloj0 a.inicio).length := by
  rw [show (homogeneizar a).inicio = (a.inicio, a.reloj0) from rfl, homogeneizar_traza]

/-- El precio, con `c` bits: `|σ × Fin (2^c)| = |σ| · 2^c`. -/
theorem card_reloj_bits (σ : Type) [Fintype σ] (c : ℕ) : Fintype.card (σ × Fin (2 ^ c)) = Fintype.card σ * 2 ^ c := by
  simp

/-- El precio, con tope: `|σ × Fin (T + 1)| = |σ| · (T + 1)`. -/
theorem card_reloj_tope (σ : Type) [Fintype σ] (T : ℕ) : Fintype.card (σ × Fin (T + 1)) = Fintype.card σ * (T + 1) := by
  simp

end Noether

/-! ### (c) La ley del cubo con reloj -/

/-- Resolver con reloj: como `ResuelveA`, arrancando en el reloj inicial. -/
def ResuelveR {P C κ σ Q R Y : Type} (O : Y → Q → R) (A : P → C → AutomataConReloj κ σ Q R Y) (t : ℕ) : Prop :=
  ∀ y, ∃ p c, (A p c).corre (O y) t (A p c).reloj0 (A p c).inicio = some y

theorem resuelveR_homogeneo {P C κ σ Q R Y : Type} {O : Y → Q → R} {A : P → C → AutomataConReloj κ σ Q R Y} {t : ℕ}
    (h : ResuelveR O A t) : ResuelveA O (fun p c => homogeneizar (A p c)) t := by
  intro y
  obtain ⟨p, c, hy⟩ := h y
  exact ⟨p, c, (homogeneizar_corre (A p c) (O y) t _ _).trans hy⟩

/-- **La ley del cubo con reloj**: con `|σ| ≤ 2^S` y un reloj de `|κ| ≤ 2^c` valores,
`N ≤ 2^L · 2^s · min (t + 1) 2^(S + c − 1)`. El reloj suma `c` al eje del espacio. -/
theorem ley_cubo_reloj {P C κ σ Y : Type} [Fintype P] [Fintype C] [Fintype κ] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s S c t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S)
    (hκ : Fintype.card κ ≤ 2 ^ c) (A : P → C → AutomataConReloj κ σ Y Bool Y) (h : ResuelveR igual A t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S + c - 1)) := by
  have hσκ : Fintype.card (σ × κ) ≤ 2 ^ (S + c) := by
    rw [Fintype.card_prod, pow_add]; exact Nat.mul_le_mul hσ hκ
  exact ley_cubo hP hC hσκ _ (resuelveR_homogeneo h)

/-- **En bits**: `⌈log₂ N⌉ ≤ L + s + min ⌈log₂(t+1)⌉ (S + c − 1)`. -/
theorem ley_cubo_reloj_log {P C κ σ Y : Type} [Fintype P] [Fintype C] [Fintype κ] [Fintype σ] [Fintype Y]
    [DecidableEq Y] {L s S c t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (hσ : Fintype.card σ ≤ 2 ^ S) (hκ : Fintype.card κ ≤ 2 ^ c) (A : P → C → AutomataConReloj κ σ Y Bool Y)
    (h : ResuelveR igual A t) :
    Nat.clog 2 (Fintype.card Y) ≤ L + s + min (Nat.clog 2 (t + 1)) (S + c - 1) := by
  have hσκ : Fintype.card (σ × κ) ≤ 2 ^ (S + c) := by
    rw [Fintype.card_prod, pow_add]; exact Nat.mul_le_mul hσ hκ
  exact ley_cubo_log hP hC hσκ _ (resuelveR_homogeneo h)

/-- **El reloj libre de `CuboCostos`, cobrado**: un autómata con el paso en `ℕ` regalado que resuelve en `t` consultas
paga `⌈log₂(t+1)⌉` bits de espacio: `N ≤ 2^L · 2^s · min (t + 1) 2^(S + ⌈log₂(t+1)⌉ − 1)`. -/
theorem ley_cubo_reloj_libre {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]
    {L s S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hσ : Fintype.card σ ≤ 2 ^ S)
    (A : P → C → AutomataReloj σ Y Bool Y) (h : ∀ y, ∃ p c, (A p c).corre (igual y) t 0 (A p c).inicio = some y) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (S + Nat.clog 2 (t + 1) - 1)) := by
  refine ley_cubo_reloj (κ := Fin (t + 1)) hP hC hσ ?_ (fun p c => truncar (A p c) t) ?_
  · simpa using Nat.le_pow_clog one_lt_two (t + 1)
  · intro y
    obtain ⟨p, c, hy⟩ := h y
    exact ⟨p, c, (truncar_corre (A p c) t (igual y) t 0 _ (by omega)).symm.trans hy⟩

/-! ## 3. La carga de Noether -/

section Carga

variable {σ Q R Y : Type}

/-- Un paso de la corrida homogénea, sin mirar si para. -/
def paso (a : Automata σ Q R Y) (O : Q → R) (x : σ) : σ := a.δ x (O (a.consulta x))

/-- **Partir la corrida**: si no paró en los primeros `i` estados, correr `i + t` es correr `t` desde el estado `i`. -/
theorem corre_partir (a : Automata σ Q R Y) (O : Q → R) :
    ∀ (i t : ℕ) (x : σ), (∀ k < i, a.salida ((paso a O)^[k] x) = none) →
      a.corre O (i + t) x = a.corre O t ((paso a O)^[i] x)
  | 0, t, x, _ => by simp
  | i + 1, t, x, h => by
      have h0 : a.salida x = none := h 0 (by omega)
      rw [show i + 1 + t = (i + t) + 1 by omega, Automata.corre_none h0, Function.iterate_succ_apply]
      exact corre_partir a O i t _ fun k hk => by
        have := h (k + 1) (by omega); rwa [Function.iterate_succ_apply] at this

/-- **La carga de Noether de la homogeneidad.** Dos corridas homogéneas con el mismo verificador que llegan al mismo
estado, una en el tiempo `i` y otra en el `j`, sin haber parado: desde ahí todo es igual, la salida con cualquier
presupuesto restante y todos los estados siguientes. El tiempo no deja huella fuera del estado. -/
theorem carga_noether (a : Automata σ Q R Y) (O : Q → R) {x x' : σ} {i j : ℕ}
    (hi : ∀ k < i, a.salida ((paso a O)^[k] x) = none) (hj : ∀ k < j, a.salida ((paso a O)^[k] x') = none)
    (h : (paso a O)^[i] x = (paso a O)^[j] x') (t : ℕ) :
    a.corre O (i + t) x = a.corre O (j + t) x' ∧ (paso a O)^[i + t] x = (paso a O)^[j + t] x' := by
  refine ⟨by rw [corre_partir a O i t x hi, corre_partir a O j t x' hj, h], ?_⟩
  rw [add_comm i, add_comm j, Function.iterate_add_apply, Function.iterate_add_apply, h]

/-- **Una corrida no sabe la hora**: si vuelve en `j` al estado que tenía en `i`, sin haber parado, desde `i` y desde `j`
continúa igual. -/
theorem no_sabe_la_hora (a : Automata σ Q R Y) (O : Q → R) {x : σ} {i j : ℕ}
    (hj : ∀ k < j, a.salida ((paso a O)^[k] x) = none) (hij : i ≤ j)
    (h : (paso a O)^[i] x = (paso a O)^[j] x) (t : ℕ) : a.corre O (i + t) x = a.corre O (j + t) x :=
  (carga_noether a O (fun k hk => hj k (by omega)) hj h t).1

end Carga

/-! ## 5. El ejemplo chico (antes de 4, porque 3 lo usa) -/

/-- **El barrido de `mutante_reloj` con reloj de tope `3`** (`2` bits). -/
def barridoTope : AutomataConReloj (Fin 4) Bool (Fin 4) Bool (Fin 4) := truncar relojBarrido 3

/-- **Las mismas corridas que el original**, con el presupuesto `3`. -/
theorem barridoTope_igual (O : Fin 4 → Bool) :
    relojBarrido.corre O 3 0 relojBarrido.inicio = barridoTope.corre O 3 barridoTope.reloj0 barridoTope.inicio :=
  truncar_corre relojBarrido 3 O 3 0 _ (by omega)

/-- **Su versión homogénea**: `2 · 4 = 8` estados, sin reloj. -/
def barridoHomogeneo : Automata (Bool × Fin 4) (Fin 4) Bool (Fin 4) := homogeneizar barridoTope

theorem barridoHomogeneo_resuelve :
    ∀ y : Fin 4, barridoHomogeneo.corre (igual y) 3 barridoHomogeneo.inicio = some y := by
  intro y
  rw [show barridoHomogeneo.inicio = (barridoTope.inicio, barridoTope.reloj0) from rfl, barridoHomogeneo,
    homogeneizar_corre, ← barridoTope_igual]
  exact relojBarrido_resuelve y

theorem card_barridoHomogeneo : Fintype.card (Bool × Fin 4) = 2 ^ (1 + 2) := by simp

/-- **El control `mutante_reloj`, cobrado.** El barrido con reloj (2 estados, `S = 1`) resuelve 4 candidatos en 3
consultas. La ley sin reloj pide `4 ≤ 1` y falla; con los `2` bits del reloj contados (`c = ⌈log₂ 4⌉ = 2`) pide
`4 ≤ min 4 2^(1+2−1) = 4` y se cumple, y es consecuencia de `ley_cubo_reloj_libre`; con un bit menos de reloj pediría
`4 ≤ 2`. -/
theorem control_reloj :
    ¬ (Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (3 + 1) (2 ^ (1 - 1))) ∧
      Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (3 + 1) (2 ^ (1 + Nat.clog 2 (3 + 1) - 1)) ∧
      Nat.clog 2 (3 + 1) = 2 ∧
      ¬ (Fintype.card (Fin 4) ≤ 2 ^ 0 * 2 ^ 0 * min (3 + 1) (2 ^ (1 + (2 - 1) - 1))) := by
  refine ⟨mutante_reloj.2.2, ?_, by decide, by simp⟩
  exact ley_cubo_reloj_libre (P := Unit) (C := Unit) (L := 0) (s := 0) (S := 1) (by simp) (by simp) (by simp)
    (fun _ _ => relojBarrido) (fun y => ⟨(), (), relojBarrido_resuelve y⟩)

/-- **Con reloj, el tiempo deja huella.** En la corrida de `barridoTope` con el verificador de `3`, el estado (sin el
reloj) es `false` en el paso `0` y otra vez en el paso `3`, pero en el paso `0` no devuelve nada y en el `3` devuelve
`3`: la continuación depende del instante. Lo que en el homogéneo (`carga_noether`) no puede pasar, aquí pasa porque
la homogeneización guarda el reloj en el estado: `(false, 0) ≠ (false, 3)`. -/
theorem reloj_deja_huella :
    ((paso barridoHomogeneo (igual 3))^[0] barridoHomogeneo.inicio).1 = false ∧
      ((paso barridoHomogeneo (igual 3))^[3] barridoHomogeneo.inicio).1 = false ∧
      barridoHomogeneo.corre (igual 3) 0 ((paso barridoHomogeneo (igual 3))^[0] barridoHomogeneo.inicio) = none ∧
      barridoHomogeneo.corre (igual 3) 0 ((paso barridoHomogeneo (igual 3))^[3] barridoHomogeneo.inicio) = some 3 := by
  decide

/-! ## 4. El contador de `fijarFin` como caso de 2(b) -/

/-- **El contador de elecciones como reloj**: `Fin (w + 1)`, avanza (saturado en `w`) solo en los estados que eligen, y
la elección lee el bit de la sucesión que indica el reloj. -/
def relojEleccion {σ Q R Y : Type} (a : AutomataND σ Q R Y) (bs : List Bool) (w : ℕ) :
    AutomataConReloj (Fin (w + 1)) σ Q R Y where
  inicio := a.inicio
  reloj0 := 0
  tic := fun k x => if a.elige x then ⟨min (k.val + 1) w, by omega⟩ else k
  consulta := fun _ => a.consulta
  δ := fun k x r => if a.elige x then a.δ x r ((bs.drop k).headD false) else a.δ x r false
  salida := fun _ => a.salida

/-- **`fijarFin` es la homogeneización del reloj de elecciones**: el contador de `CuboNoDeterminista` es un caso de
2(b), y `card_contador` es el precio del reloj. -/
theorem fijarFin_es_homogeneizar {σ Q R Y : Type} (a : AutomataND σ Q R Y) (bs : List Bool) (w : ℕ) :
    fijarFin a bs w = homogeneizar (relojEleccion a bs w) := by
  simp only [fijarFin, homogeneizar, relojEleccion, Automata.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  funext z r
  split_ifs <;> rfl

/-- Y por lo tanto la corrida de `fijarFin` es la del autómata con reloj de elecciones. -/
theorem fijarFin_corre_reloj {σ Q R Y : Type} (a : AutomataND σ Q R Y) (bs : List Bool) (w : ℕ) (O : Q → R) (t : ℕ)
    (x : σ) (k : Fin (w + 1)) : (fijarFin a bs w).corre O t (x, k) = (relojEleccion a bs w).corre O t k x := by
  rw [fijarFin_es_homogeneizar, homogeneizar_corre]

end Sagitta.Map.Informacion.Homogeneidad
