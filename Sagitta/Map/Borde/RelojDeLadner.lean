import Sagitta.Map.Borde.SatPorBloques
import Sagitta.Map.Informacion.Rupturas
import CslibFrontier.Computability.Complexity.Classes.Ladner
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Tactic.PolyTime

/-!
# El reloj de Ladner: fabricar la oscilación cuesta un reloj (fase B4, acotada)

`SatPorBloques.lean` (B2b) fuerza la oscilación con un conjunto de largos `B`, pero su `B` (el de
`ladner_no_constructivo`) se elige con un ultrafiltro y no se calcula. Ladner (1975) pone lo que falta: un reloj barato.
Este archivo mide ese reloj en las dos monedas de la CHT (conservación de la homogeneidad del tiempo, ver `Informacion/Homogeneidad.lean`): memoria y tiempo.

## 1. La oscilación es la ruptura de la homogeneidad en el largo

`HomogeneoEnLargo B`: la decisión «¿el largo `n` está en `B`?» es finalmente la misma (siempre sí o siempre no).
`no_homogeneo_iff`: no serlo es que `B` y `Bᶜ` sean infinitos.

* `regiones_de_mezcla` (`bajo_mezcla_iff`, `sobre_mezcla_iff`, `oscila_mezcla_iff`): si un costo `h` copia a un costo
  `g` arriba (`Sobre g`) en los largos de `B` y vale a lo sumo `1` fuera, entonces `h` está abajo si y solo si
  finalmente `n ∉ B`, arriba si y solo si finalmente `n ∈ B`, y **oscila si y solo si `B` no es homogéneo en el largo**.
  La tricotomía de `Tricotomia.lean` es, para estos costos, la tricotomía de la decisión de largo.
* `oscila_porBloques_iff`: con SAT arriba (`Sobre (sucNat satMarco)`), `porBloques B` oscila si y solo si `B` no es
  homogéneo en el largo. Sin hipótesis, `bajo_porBloques_de_homogeneo`: la homogeneidad «abajo» da P/poly.

## 2. El reloj cuesta memoria

Un autómata finito sin reloj que lee `1ⁿ` (homogéneo, en el sentido de `Homogeneidad.lean`) es finalmente periódico
(`unario_periodico` de `Rupturas.lean`). Por eso:

* `estados_de_racha`: si un DFA en una letra acierta «`n ∈ B`» para todo `n < N`, y `B` tiene una racha
  `[s, s + L) ⊆ B` seguida de un `m ∉ B` con `m < N`, el DFA tiene **más de `min s L` estados**.
* `no_regular_de_rachas`: si `B` tiene rachas arbitrariamente largas tan lejos como se quiera y `Bᶜ` es infinito,
  ningún DFA decide `{1ⁿ | n ∈ B}`: hace falta un reloj. Los bloques de Ladner crecen, así que rompen la CHT.
* El control: oscilar no basta para pedir reloj. Con `B` = los pares (`pares_no_homogeneo`, `pares_periodico`), la
  decisión es periódica y la decide un DFA de dos estados; lo que cuesta es que los bloques **crezcan**.

## 3. El reloj cuesta poco tiempo

Los bloques se dan por sus extremos `e : ℕ → ℕ`; `bloque e n` cuenta los extremos `e (m + 1) ≤ n`, y es el índice del
bloque de `n` si `e` es estrictamente creciente (`bloque_eq`).

* `RelojBarato e`: decidir `e m ≤ n` es polinomial en `m` y `n` en unario. **Es la cota precisa**: con eso, `bloque e`
  es polinomial en unario (`bloque_polinomial`).
* `largos_en_P_iff`: el filtro de largos `{y | c |y|}` está en P exactamente cuando `c` es polinomial en unario.
* `porBloquesReloj_mem_NP`: con un reloj barato y un selector polinomial, `{y ∈ A | sel (bloque e |y|)}` está en NP
  para todo `A ∈ NP`. `porBloques_mem_NP`: SAT por bloques de `SatPorBloques` está en NP **si** `satMarco` lo está
  (eso no está probado en Sagitta: es la hipótesis), con `B` dado por un reloj barato.
* **Los bloques dobles** (`dobles m = 2^m − 1`, bloques de largo `2^m`, `B` = los bloques pares): reloj barato
  (`relojBarato_dobles`, con la potencia acotada `capPow` de cslib-frontier), NP (`dobles_mem_NP`), oscila si SAT está
  arriba (`dobles_oscila`), ningún DFA lo decide (`dobles_no_regular`) y uno correcto hasta `2^(m+1)` necesita
  `≥ 2^m` estados (`dobles_estados`): **`m ≈ log₂ n` bits de reloj**, el precio de `Homogeneidad.lean`
  (`c = ⌈log₂(t+1)⌉`).

## 4. El reloj de cslib-frontier

cslib-frontier trae Ladner completo (`Cslib.Complexity.Ladner.exists_NP_not_P_not_npComplete`), con relleno y no por
bloques: `SATH` rellena una fórmula de largo `m` con `m^(H m)` unos. Su reloj es `H`: polinomial en unario
(`reloj_de_ladner` = `computableInPolyTime_H`) y lento, `H n ≤ log₂ log₂ n` (`H_le`). `bloquesDeH_mem_NP`: los
bloques que dibuja `H` (sus valores) también dan problemas en NP.

## Lo que NO se prueba, y qué quedó de B4

* Que un `e` barato concreto haga a `porBloques` (con SAT) **ni P ni NP-completo** si P ≠ NP: es el corazón de Ladner
  por bloques (la diagonalización perezosa elige los extremos mirando máquinas). Aquí `e` es un dato. cslib-frontier
  tiene la versión por bloques en `Ladner/Density.lean` (`exists_mem_P_ite_empty_lt`, Schöning 1982: un `G ∈ P` de
  **palabras**, no de largos), pero sus dependencias (diagonalización uniforme, `Halting.Partrec`) no están compiladas
  y no se importaron.
* `satMarco ∈ NP` (de cslib) no está probado en Sagitta (`CookS12.lean` lo dice); `porBloques_mem_NP` lo toma como
  hipótesis.
* `estados_de_racha` es una cota inferior de memoria para DFA en una letra (la CHT con memoria finita), no para
  máquinas de Turing: una máquina con cinta calcula el reloj en tiempo polinomial (§ 3), y esa es justamente la
  memoria que paga.
-/

open Filter Set

namespace Sagitta.Map.Borde.RelojDeLadner

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Finitud
open Sagitta.Map.Tiempo.Infinito Sagitta.Map.Tiempo.Relleno Sagitta.Map.Borde.Tricotomia
open Sagitta.Map.Borde.SatEnElBorde Sagitta.Map.Borde.SatPorBloques

/-! ## 1. La oscilación es la ruptura de la homogeneidad en el largo -/

/-- **Homogéneo en el largo**: la decisión «¿`n ∈ B`?» es finalmente constante. -/
def HomogeneoEnLargo (B : Set ℕ) : Prop := (∀ᶠ n in atTop, n ∈ B) ∨ (∀ᶠ n in atTop, n ∉ B)

theorem eventually_notMem_iff (B : Set ℕ) : (∀ᶠ n in atTop, n ∉ B) ↔ B.Finite := by
  rw [← Nat.cofinite_eq_atTop, eventually_cofinite]
  simp

theorem eventually_mem_iff (B : Set ℕ) : (∀ᶠ n in atTop, n ∈ B) ↔ Bᶜ.Finite := by
  rw [← Nat.cofinite_eq_atTop, eventually_cofinite]
  rfl

/-- **No ser homogéneo es que `B` y `Bᶜ` sean infinitos.** -/
theorem no_homogeneo_iff (B : Set ℕ) : ¬ HomogeneoEnLargo B ↔ B.Infinite ∧ Bᶜ.Infinite := by
  rw [HomogeneoEnLargo, eventually_mem_iff, eventually_notMem_iff, not_or]
  exact and_comm

section Mezcla

variable {g h : ℕ → ℕ} {B : Set ℕ}

/-- Abajo si y solo si finalmente fuera de `B`. -/
theorem bajo_mezcla_iff (hg : Sobre g) (hd : ∀ n ∈ B, h n = g n) (hf : ∀ n ∉ B, h n ≤ 1) :
    Bajo h ↔ ∀ᶠ n in atTop, n ∉ B := by
  constructor
  · rintro ⟨c, k, hck⟩
    by_contra hno
    rw [eventually_notMem_iff] at hno
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hg c k)
    obtain ⟨n, hnB, hnN⟩ := (Set.Infinite.exists_gt hno N)
    have := hck n
    rw [hd n hnB] at this
    have := hN n hnN.le
    omega
  · intro hev
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact pol_de_casi (c := 1) (k := 0) (N := N) fun n hn => by
      have := hf n (hN n hn)
      simpa using this

/-- Arriba si y solo si finalmente dentro de `B`. -/
theorem sobre_mezcla_iff (hg : Sobre g) (hd : ∀ n ∈ B, h n = g n) (hf : ∀ n ∉ B, h n ≤ 1) :
    Sobre h ↔ ∀ᶠ n in atTop, n ∈ B := by
  constructor
  · intro hs
    filter_upwards [hs 1 0] with n hn
    by_contra hnB
    have := hf n hnB
    simp at hn
    omega
  · intro hev c k
    filter_upwards [hev, hg c k] with n hnB hn
    rw [hd n hnB]
    exact hn

/-- **Oscilar es no ser homogéneo en el largo**, para un costo que copia a uno arriba en `B` y es trivial fuera. -/
theorem oscila_mezcla_iff (hg : Sobre g) (hd : ∀ n ∈ B, h n = g n) (hf : ∀ n ∉ B, h n ≤ 1) :
    Oscila h ↔ ¬ HomogeneoEnLargo B := by
  rw [Oscila, bajo_mezcla_iff hg hd hf, sobre_mezcla_iff hg hd hf, HomogeneoEnLargo, not_or]
  exact and_comm

/-- Las tres regiones, leídas en la decisión de largo. -/
theorem regiones_de_mezcla (hg : Sobre g) (hd : ∀ n ∈ B, h n = g n) (hf : ∀ n ∉ B, h n ≤ 1) :
    (Bajo h ↔ ∀ᶠ n in atTop, n ∉ B) ∧ (Sobre h ↔ ∀ᶠ n in atTop, n ∈ B) ∧
      (Oscila h ↔ ¬ HomogeneoEnLargo B) :=
  ⟨bajo_mezcla_iff hg hd hf, sobre_mezcla_iff hg hd hf, oscila_mezcla_iff hg hd hf⟩

end Mezcla

/-- **SAT por bloques oscila si y solo si sus largos no son homogéneos**, con SAT arriba. -/
theorem oscila_porBloques_iff (hS : Sobre (sucNat satMarco)) (B : Set ℕ) :
    Oscila (sucNat (porBloques B)) ↔ ¬ HomogeneoEnLargo B :=
  oscila_mezcla_iff hS (fun _ hn => sucNat_dentro hn) (fun _ hn => sucNat_fuera hn)

/-- Sin hipótesis: la homogeneidad «abajo» deja a SAT por bloques en P/poly. -/
theorem bajo_porBloques_de_homogeneo {B : Set ℕ} (h : ∀ᶠ n in atTop, n ∉ B) : Bajo (sucNat (porBloques B)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact pol_de_casi (c := 1) (k := 0) (N := N) fun n hn => by simpa using sucNat_fuera (hN n hn)

/-! ## 2. El reloj cuesta memoria -/

section Memoria

open Sagitta.Map.Informacion.Rupturas

/-- La periodicidad de `unario_periodico`, iterada. -/
theorem periodico_iter {σ : Type} (M : DFA Unit σ) {μ p : ℕ}
    (h : ∀ n, μ ≤ n → (List.replicate (n + p) () ∈ M.accepts ↔ List.replicate n () ∈ M.accepts)) :
    ∀ q n, μ ≤ n → (List.replicate (n + p * q) () ∈ M.accepts ↔ List.replicate n () ∈ M.accepts) := by
  intro q
  induction q with
  | zero => intro n _; simp
  | succ q ih =>
    intro n hn
    rw [show n + p * (q + 1) = (n + p * q) + p by ring, h _ (by omega)]
    exact ih n hn

/-- **Una racha cuesta estados.** Si un DFA en una letra acierta `n ∈ B` para `n < N`, y hay una racha
`[s, s + L) ⊆ B` y un `m ∉ B` con `s ≤ m < N`, el DFA tiene más de `min s L` estados. -/
theorem estados_de_racha {σ : Type} [Fintype σ] (M : DFA Unit σ) (B : Set ℕ) {N : ℕ}
    (hM : ∀ n < N, (List.replicate n () ∈ M.accepts ↔ n ∈ B))
    {s L m : ℕ} (hrun : ∀ i < L, s + i ∈ B) (hsm : s ≤ m) (hmN : m < N) (hmB : m ∉ B) :
    min s L < Fintype.card σ := by
  by_contra hc
  push Not at hc
  have hs : Fintype.card σ ≤ s := le_trans hc (min_le_left _ _)
  have hL : Fintype.card σ ≤ L := le_trans hc (min_le_right _ _)
  obtain ⟨μ, p, hp, hle, hper⟩ := unario_periodico M ()
  have e := Nat.mod_add_div (m - s) p
  generalize hr' : (m - s) % p = r at e
  generalize (m - s) / p = q at e
  have hr : r < p := hr' ▸ Nat.mod_lt _ hp
  have hm' : m = (s + r) + p * q := by omega
  have hin : s + r ∈ B := hrun r (by omega)
  have h1 := periodico_iter M hper q (s + r) (by omega)
  rw [← hm'] at h1
  have h2 := hM m hmN
  have h3 := hM (s + r) (by omega)
  exact hmB (h2.1 (h1.2 (h3.2 hin)))

/-- **Rachas sin fin piden reloj.** Si `B` tiene rachas de todo largo más allá de todo punto y `Bᶜ` es infinito,
ningún DFA en una letra decide `B`. -/
theorem no_regular_de_rachas {σ : Type} [Finite σ] (B : Set ℕ) (hrun : ∀ L N, ∃ s ≥ N, ∀ i < L, s + i ∈ B)
    (hc : Bᶜ.Infinite) (M : DFA Unit σ) : ¬ ∀ n, (List.replicate n () ∈ M.accepts ↔ n ∈ B) := by
  have := Fintype.ofFinite σ
  intro hM
  obtain ⟨s, hs, hsr⟩ := hrun (Fintype.card σ) (Fintype.card σ)
  obtain ⟨m, hmB, hm⟩ := hc.exists_gt s
  have := estados_de_racha M B (N := m + 1) (fun n _ => hM n) hsr hm.le (by omega) hmB
  have : min s (Fintype.card σ) = Fintype.card σ := min_eq_right hs
  omega

end Memoria

/-- El control: los pares oscilan en el largo (no son homogéneos)… -/
theorem pares_no_homogeneo : ¬ HomogeneoEnLargo {n | Even n} := by
  rw [no_homogeneo_iff]
  refine ⟨?_, ?_⟩
  · exact Set.infinite_of_injective_forall_mem (f := fun k => 2 * k) (fun a b h => by simp only at h; omega)
      fun k => (⟨k, by ring⟩ : Even (2 * k))
  · exact Set.infinite_of_injective_forall_mem (f := fun k => 2 * k + 1)
      (fun a b h => by simp only at h; omega) fun k => by simp

/-- … pero su decisión es periódica: no hay rachas que crezcan y no hace falta reloj. -/
theorem pares_periodico (n : ℕ) : (n + 2 ∈ {n | Even n}) ↔ n ∈ {n | Even n} := by
  simp [Nat.even_add]

/-! ## 3. El reloj cuesta poco tiempo -/

/-- **El bloque de `n`**: cuántos extremos `e (m + 1)` ya pasó `n`. -/
def bloque (e : ℕ → ℕ) (n : ℕ) : ℕ := (List.range (n + 1)).countP (fun m => decide (e (m + 1) ≤ n))

theorem countP_range_lt (k : ℕ) : ∀ N, (List.range N).countP (fun m => decide (m < k)) = min N k
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_lt k N]
    by_cases h : N < k <;> simp [h] <;> omega

/-- Con `e` estrictamente creciente, `bloque e n` es el índice del bloque `[e k, e (k+1))` que contiene a `n`. -/
theorem bloque_eq {e : ℕ → ℕ} (he : StrictMono e) {k n : ℕ} (h1 : e k ≤ n) (h2 : n < e (k + 1)) :
    bloque e n = k := by
  unfold bloque
  rw [List.countP_congr (q := fun m => decide (m < k)) (fun m _ => by
    simp only [decide_eq_true_eq]
    constructor
    · intro hm
      have := he.lt_iff_lt.1 (lt_of_le_of_lt hm h2)
      omega
    · intro hm
      exact (he.monotone (show m + 1 ≤ k by omega)).trans h1), countP_range_lt]
  have : k ≤ e k := he.id_le k
  omega

open Turing.MultiTapeTM Cslib.Complexity

/-- **Un reloj barato**: decidir `e m ≤ n` es polinomial en `m` y `n` en unario. -/
def RelojBarato (e : ℕ → ℕ) : Prop :=
  ComputableInPolyTime (fun p : ℕ × ℕ => decide (e p.1 ≤ p.2)) (encPair encUnary encUnary) encBool

/-- **Con un reloj barato, el bloque se calcula en tiempo polinomial** (en el largo, en unario). -/
theorem bloque_polinomial {e : ℕ → ℕ} (he : RelojBarato e) : ComputableInPolyTime (bloque e) encUnary encUnary := by
  unfold bloque
  have h2 : ComputableInPolyTime (fun p : ℕ × ℕ => decide (e (p.2 + 1) ≤ p.1)) (encPair encUnary encUnary)
      encBool :=
    he.comp (show ComputableInPolyTime (fun p : ℕ × ℕ => (p.2 + 1, p.1))
      (encPair encUnary encUnary) (encPair encUnary encUnary) by fun_prop)
  fun_prop

/-- **El filtro de largos está en P exactamente cuando su decisión es polinomial en unario.** -/
theorem largos_en_P_iff (c : ℕ → Bool) :
    {y : List Bool | c y.length = true} ∈ Cslib.Complexity.P encBits ↔ ComputableInPolyTime c encUnary encBool := by
  constructor
  · rintro ⟨f, hf, hA⟩
    have hr : ComputableInPolyTime (fun n => List.replicate n false) encUnary encBits := by fun_prop
    convert hf.comp hr using 1
    funext n
    have := hA (List.replicate n false)
    simp only [Set.mem_ofPred_eq, List.length_replicate] at this
    cases h1 : c n <;> cases h2 : f (List.replicate n false) <;> simp_all
  · intro hc
    exact ⟨fun y => c y.length, by fun_prop, fun _ => Iff.rfl⟩

/-- Los largos que el reloj `e` manda a bloques con `sel` verdadero. -/
def largosReloj (e : ℕ → ℕ) (sel : ℕ → Bool) : Set ℕ := {n | sel (bloque e n) = true}

/-- `A` restringido a los largos de esos bloques. -/
def porBloquesReloj (A : Set (List Bool)) (e : ℕ → ℕ) (sel : ℕ → Bool) : Set (List Bool) :=
  {y | sel (bloque e y.length) = true ∧ y ∈ A}

/-- **Con reloj barato, por bloques queda en NP.** -/
theorem porBloquesReloj_mem_NP {A : Set (List Bool)} (hA : A ∈ Cslib.Complexity.NP encBits) {e : ℕ → ℕ}
    (he : RelojBarato e) {sel : ℕ → Bool} (hsel : ComputableInPolyTime sel encUnary encBool) :
    porBloquesReloj A e sel ∈ Cslib.Complexity.NP encBits := by
  have hb := bloque_polinomial he
  have hc : ComputableInPolyTime (fun y : List Bool => sel (bloque e y.length)) encBits encBool := by fun_prop
  exact mem_NP_of_guard hc hA fun _ => Iff.rfl

/-- **SAT por bloques, con reloj barato, está en NP si `satMarco` lo está.** -/
theorem porBloques_mem_NP (hSat : {y | satMarco y = true} ∈ Cslib.Complexity.NP encBits) {e : ℕ → ℕ}
    (he : RelojBarato e) {sel : ℕ → Bool} (hsel : ComputableInPolyTime sel encUnary encBool) :
    {y | porBloques (largosReloj e sel) y = true} ∈ Cslib.Complexity.NP encBits := by
  convert porBloquesReloj_mem_NP hSat he hsel using 1
  ext y
  classical
  simp only [Set.mem_ofPred_eq, porBloques, porBloquesReloj, largosReloj]
  by_cases h : sel (bloque e y.length) = true <;> simp [h]

/-! ### Los bloques dobles -/

/-- Extremos `2^m − 1`: el bloque `m` es `[2^m − 1, 2^(m+1) − 1)`, de largo `2^m`. -/
def dobles (m : ℕ) : ℕ := 2 ^ m - 1

/-- Paridad en unario, con lo que hay en cslib-frontier (no hay `%`): `k` es par si `j + j = k` para algún `j ≤ k`. -/
def par (k : ℕ) : Bool := (List.range (k + 1)).any (fun j => j + j == k)

theorem par_iff (k : ℕ) : par k = true ↔ Even k := by
  simp only [par, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨j, -, hj⟩; exact ⟨j, hj.symm⟩
  · rintro ⟨j, hj⟩; exact ⟨j, by omega, hj.symm⟩

theorem par_polinomial : ComputableInPolyTime par encUnary encBool := by
  unfold par
  fun_prop

theorem dobles_strictMono : StrictMono dobles := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  simp only [dobles, pow_succ]
  have := Nat.one_le_two_pow (n := m)
  omega

theorem relojBarato_dobles : RelojBarato dobles := by
  have h : ComputableInPolyTime (fun p : ℕ × ℕ =>
      min (Ladner.capPow 2 p.1 (p.2 + 2)) (p.2 + 1) == Ladner.capPow 2 p.1 (p.2 + 2))
      (encPair encUnary encUnary) encBool := by fun_prop
  unfold RelojBarato
  convert h using 1
  funext p
  show decide (dobles p.1 ≤ p.2) = _
  have := Nat.one_le_two_pow (n := p.1)
  rw [Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]
  simp only [dobles, Ladner.capPow]
  omega

/-- Los largos de los bloques dobles pares. -/
def largosDobles : Set ℕ := largosReloj dobles par

theorem bloque_dobles {m i : ℕ} (hi : i < 2 ^ m) : bloque dobles (2 ^ m - 1 + i) = m := by
  apply bloque_eq dobles_strictMono
  · simp [dobles]
  · simp only [dobles, pow_succ]
    have := Nat.one_le_two_pow (n := m)
    omega

theorem mem_largosDobles {m i : ℕ} (hi : i < 2 ^ m) : 2 ^ m - 1 + i ∈ largosDobles ↔ Even m := by
  simp only [largosDobles, largosReloj, Set.mem_ofPred_eq, bloque_dobles hi, par_iff]

theorem largosDobles_no_homogeneo : ¬ HomogeneoEnLargo largosDobles := by
  rw [no_homogeneo_iff]
  have h0 : ∀ m, 0 < 2 ^ m := fun m => by positivity
  constructor
  · refine Set.infinite_of_injective_forall_mem (f := fun k => 2 ^ (2 * k) - 1) ?_ fun k => ?_
    · intro a b hab
      have := Nat.pow_right_injective (le_refl 2) (show 2 ^ (2 * a) = 2 ^ (2 * b) by
        have := h0 (2 * a); have := h0 (2 * b); simp only at hab; omega)
      omega
    · simpa using (mem_largosDobles (m := 2 * k) (i := 0) (h0 _)).2 ⟨k, by ring⟩
  · refine Set.infinite_of_injective_forall_mem (f := fun k => 2 ^ (2 * k + 1) - 1) ?_ fun k => ?_
    · intro a b hab
      have := Nat.pow_right_injective (le_refl 2) (show 2 ^ (2 * a + 1) = 2 ^ (2 * b + 1) by
        have := h0 (2 * a + 1); have := h0 (2 * b + 1); simp only at hab; omega)
      omega
    · have := (mem_largosDobles (m := 2 * k + 1) (i := 0) (h0 _))
      simp only [add_zero] at this
      simp only [Set.mem_compl_iff, this, Nat.not_even_iff_odd]
      exact ⟨k, rfl⟩

theorem dobles_rachas : ∀ L N, ∃ s ≥ N, ∀ i < L, s + i ∈ largosDobles := by
  intro L N
  set m := 2 * (L + N)
  have hm : L + N < 2 ^ m := by
    have := Nat.lt_two_pow_self (n := m)
    omega
  refine ⟨2 ^ m - 1, by omega, fun i hi => (mem_largosDobles (by omega)).2 ⟨L + N, by ring⟩⟩

/-- **Bloques dobles: oscila si SAT está arriba.** -/
theorem dobles_oscila (hS : Sobre (sucNat satMarco)) : Oscila (sucNat (porBloques largosDobles)) :=
  (oscila_porBloques_iff hS _).2 largosDobles_no_homogeneo

/-- **Bloques dobles: NP si `satMarco` lo está**, con el reloj barato. -/
theorem dobles_mem_NP (hSat : {y | satMarco y = true} ∈ Cslib.Complexity.NP encBits) :
    {y | porBloques largosDobles y = true} ∈ Cslib.Complexity.NP encBits :=
  porBloques_mem_NP hSat relojBarato_dobles par_polinomial

/-- **Bloques dobles: ningún DFA sin reloj los decide.** -/
theorem dobles_no_regular {σ : Type} [Finite σ] (M : DFA Unit σ) :
    ¬ ∀ n, (List.replicate n () ∈ M.accepts ↔ n ∈ largosDobles) :=
  no_regular_de_rachas _ dobles_rachas ((no_homogeneo_iff _).1 largosDobles_no_homogeneo).2 M

/-- **El precio en memoria**: un DFA que acierta los bloques dobles hasta `2^(m+1)` (con `m` par) tiene al menos
`2^m` estados, o sea `m` bits de reloj. -/
theorem dobles_estados {σ : Type} [Fintype σ] (M : DFA Unit σ) {m : ℕ} (hm : Even m)
    (hM : ∀ n < 2 ^ (m + 1), (List.replicate n () ∈ M.accepts ↔ n ∈ largosDobles)) :
    2 ^ m ≤ Fintype.card σ := by
  have h0 := Nat.one_le_two_pow (n := m)
  have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have hfuera : 2 ^ (m + 1) - 1 ∉ largosDobles := by
    have := (mem_largosDobles (m := m + 1) (i := 0) (by positivity))
    simp only [add_zero] at this
    rw [this, Nat.even_add_one]
    exact not_not.2 hm
  have := estados_de_racha M largosDobles hM (s := 2 ^ m - 1) (L := 2 ^ m)
    (fun i hi => (mem_largosDobles hi).2 hm) (by omega) (by omega) hfuera
  have : min (2 ^ m - 1) (2 ^ m) = 2 ^ m - 1 := min_eq_left (by omega)
  omega

/-! ## 4. El reloj de cslib-frontier -/

/-- **El reloj de Ladner es barato**: `H` es polinomial en unario (cslib-frontier). -/
theorem reloj_de_ladner : ComputableInPolyTime Ladner.H encUnary encUnary := Ladner.computableInPolyTime_H

/-- … y lento: `H n ≤ log₂ log₂ n`. -/
theorem reloj_de_ladner_lento (n : ℕ) : Ladner.H n ≤ Nat.log 2 (Nat.log 2 n) := Ladner.H_le n

/-- Los bloques que dibuja `H` (largos donde `sel (H n)`) dan problemas en NP. -/
theorem bloquesDeH_mem_NP {A : Set (List Bool)} (hA : A ∈ Cslib.Complexity.NP encBits) {sel : ℕ → Bool}
    (hsel : ComputableInPolyTime sel encUnary encBool) :
    {y | sel (Ladner.H y.length) = true ∧ y ∈ A} ∈ Cslib.Complexity.NP encBits := by
  have hH := reloj_de_ladner
  have hc : ComputableInPolyTime (fun y : List Bool => sel (Ladner.H y.length)) encBits encBool := by fun_prop
  exact mem_NP_of_guard hc hA fun _ => Iff.rfl

/-- Ladner, tal cual está en cslib-frontier (con relleno, no por bloques). -/
theorem ladner_cslib {α : Type} {enc : α ↪ List Bool} (h : Cslib.Complexity.P enc ≠ Cslib.Complexity.NP enc) :
    ∃ L : Set (List Bool), L ∈ Cslib.Complexity.NP encBits ∧ L ∉ Cslib.Complexity.P encBits ∧
      ¬ NPComplete encBits L := by
  exact Ladner.exists_NP_not_P_not_npComplete h

/- Mutantes probados (25 nov 2026, fuera del repositorio):
1. `oscila_mezcla_iff` sin `Sobre g`: es falso, y la negación se prueba (`g = h = 0`, `B` = los pares: `h` está abajo y
   `B` no es homogéneo).
2. `bloque_eq` sin `StrictMono e`: falso; con `e m = if m = 1 then 5 else 0`, `bloque e 2 = 2 ≠ 0` (por `decide`).
3. `estados_de_racha` con `m < s` en vez de `s ≤ m`: la descomposición `m = (s + r) + p·q` ya no sale (`omega` falla:
   la resta truncada `m − s` es `0`).
4. `dobles_estados` pidiendo `2^(m+1)` estados: `omega` falla; la racha da `2^m − 1 < |σ|` y nada más.
5. `bloque_polinomial` sin `RelojBarato e`: `fun_prop` no cierra (no sabe calcular `e (m+1) ≤ n`). -/

end Sagitta.Map.Borde.RelojDeLadner
