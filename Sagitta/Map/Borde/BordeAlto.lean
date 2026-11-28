import Sagitta.Map.Borde.RelojDeLadner
import Sagitta.Map.Borde.OscilacionParikh
import Sagitta.Map.Borde.FormulaBuenosEnsamble
import CslibFrontier.Computability.Complexity.Classes.Ladner.Density

/-!
# El borde sube en Lean: Ladner conectado, «infinitas veces» contra «casi siempre» y una magnificación de juguete

José (25 nov 2026) ve Sagitta como un edificio de columnas. En Lean, la del borde era la más baja: la tricotomía
(`Tricotomia.lean`) y el reloj de Ladner (`RelojDeLadner.lean`), contra lo entendido, que llega a
Bydžovský–Krajíček–Oliveira (2020) y a la magnificación (2018–2020). Este archivo sube la columna en tres pisos.

## 1. Ladner de cslib-frontier, conectado con el borde de Sagitta

cslib-frontier prueba Ladner (`Cslib.Complexity.Ladner.exists_NP_not_P_not_npComplete`) con el lenguaje `SATH`: una
fórmula de largo `m` rellenada con `m ^ H m` unos. Y prueba la versión de Schöning (1982) en
`Classes/Ladner/Density.lean` (compilado aquí por primera vez, con sus dependencias).

* **El reloj de Ladner no oscila** (`reloj_dicotomia`, sin hipótesis): `H` está acotado o tiende a infinito; nunca
  las dos cosas a medias. `sath_en_P_iff_acotado`: acotado si y solo si `SATH ∈ P`.
* **El relleno de Ladner, en la tricotomía de Sagitta** (`relleno_bajo_iff`, `relleno_sobre_iff`,
  `relleno_no_oscila`): el largo del relleno `m ↦ m ^ H m` está `Bajo` si `SATH ∈ P` y `Sobre` si no; **no oscila
  nunca**. Bajo P ≠ NP está arriba, pero apenas: `relleno_cuasipolinomial` lo acota por `m ^ log₂ log₂ m`. El
  problema intermedio de Ladner vive justo encima del borde de `no_hay_borde`, sin oscilar.
* **Por qué no es la oscilación de Sagitta, dicho exactamente.** La tricotomía de Sagitta es sobre costos de circuitos
  por largo (`sucNat`); Ladner habla de `P` uniforme y de reducciones de Karp. Sagitta no tiene `P ⊆ P/poly` (es la
  fase B3, no hecha), así que ningún teorema de cslib sobre `SATH ∈ P` dice algo de `sucNat`. Lo que sí calza es el
  relleno (arriba) y la forma de los bloques (abajo). En Ladner, la oscilación no está en el costo sino en el
  **acuerdo con las máquinas**: `H` sube porque cada máquina falla en algún lado.
* **Ladner por palabras** (`ladner_por_palabras`, de `exists_mem_P_ite_empty_lt` de Schöning): para todo `B ∈ NP` fuera
  de `P` hay `G ∈ P` tal que `B \ G` está en NP, no en P y no es NP-completo. Es B4 completo, **por palabras**: el `G`
  barato que faltaba en `RelojDeLadner.lean` lo da la diagonalización uniforme de Schöning.
* **El puente con los bloques** (`ite_de_largos`, `porBloquesReloj_es_ite`): si `G` es cerrado por largo
  (`G = {y | |y| ∈ C}`), `B \ G` es exactamente el problema por bloques de Sagitta con los largos de `Cᶜ`; y `G ∈ P` es
  que `C` sea polinomial en unario (`largos_en_P_iff`). Schöning no garantiza que su `G` sea cerrado por largo: por
  eso «Ladner por bloques de largo» sigue siendo B4 sin cerrar en la forma de Sagitta, y lo que sube es la forma por
  palabras.

## 2. «Infinitas veces» contra «casi siempre»

Para un costo `f` y una cota `s`: `DificilCS f s` (para todo largo grande, `s n < f n`), `DificilIO f s` (para
infinitos largos), `FacilCS` y `FacilIO` (lo mismo con `f n ≤ s n`).

* `dificilCS_io`, `facilCS_io`: casi siempre ⇒ infinitas veces. `no_dificilCS_iff`, `no_facilCS_iff`: la negación
  de una cota casi siempre es la cota contraria infinitas veces.
* `bajo_iff_facilCS`, `sobre_iff_dificilCS`: abajo es fácil casi siempre para algún polinomio; arriba es difícil casi
  siempre para todo polinomio.
* **`oscila_iff_ni_ni`**: oscilar es ni fácil casi siempre ni difícil casi siempre. **`oscila_iff_io`**: es ser
  difícil infinitas veces para todo polinomio y fácil infinitas veces para alguno.
* **Con BKO 2020** (`verdadero_buenos_iff_facilIO`, `s12_no_demuestra_facil_io`, `s12_io_da_cs`): `Buenos` de
  `OscilacionParikh.lean` es exactamente la cota superior **infinitas veces** (`UB^{i.o.}`). Si SAT oscila, esa cota
  es verdadera para algún polinomio y S¹₂ no la deriva (con la fórmula de `FormulaBuenosEnsamble.lean`); si S¹₂ la
  deriva, la cota vale **casi siempre**: en S¹₂, una cota superior i.o. demostrada se vuelve a.e.

## 3. Una magnificación de juguete, por relleno

`leerLog L` es `L` rellenado exponencialmente: en el largo `N` lee solo los primeros `⌊log₂ N⌋` bits. En `N = 2^n`
es `L` en el largo `n`, más relleno.

* `sucNat_leerLog_le`, `sucNat_le_leerLog`: los dos costos difieren en a lo sumo dos compuertas,
  `sucNat L n` contra `sucNat (leerLog L) (2^n)`.
* **`magnifica`**: una cota inferior `s(N) + 2` para el rellenado en `N = 2^n` da la cota `s(2^n)` para `L` en `n`.
  Medida en el largo propio, la cota se agranda: una cota **polilogarítmica** en `N`, `(log₂ N + 1)^k`, es una cota
  **polinomial** en `n`.
* **`magnifica_polylog`**: si para todo `k` el rellenado pide más de `(log₂ N + 1)^k + 2` compuertas en infinitos
  `N = 2^n`, `L` no está en P/poly. `magnifica_polylog_cs`: con «casi siempre» y todo polinomio, `L` queda arriba.
  Para SAT: `sat_magnifica`.

Es la forma más simple de la idea, y es un cambio de variable: las dos desigualdades de arriba muestran que el
rellenado y el original tienen el mismo costo, así que nada se gana en verdad. **No es la magnificación de
Oliveira–Santhanam** (2018), que parte de una cota casi lineal para una versión de MCSP con brecha, usa la
estructura de MCSP (no un relleno) y choca con la **barrera de localidad** (Chen, Hirahara, Oliveira, Pich,
Rajgopal y Santhanam): las técnicas conocidas valen también con compuertas oráculo locales, y los problemas
magnificables tienen circuitos así. Nada de eso se formaliza aquí. En el juguete, además, la cota polilogarítmica
para el rellenado es tan difícil como la polinomial para SAT: el relleno no baja la dificultad, solo la cambia de
escala.

## Cuánto subió el borde

En Lean, la columna del borde estaba en Ladner sin reloj (1975, la versión no constructiva de `SatPorBloques`) y la
tricotomía. Con este archivo llega a Schöning 1982 (Ladner por palabras con `G ∈ P`, vía cslib-frontier), a la
lectura i.o./a.e. de Bydžovský–Krajíček–Oliveira 2020 (la cota i.o. demostrada en S¹₂ se vuelve a.e.) y a la forma
de juguete de la magnificación (la idea de 2018, sin MCSP). Falta para la cornisa: el método algorítmico de Williams
(2011–2014) y su paso a casi todo largo (Chen–Lyu–Williams 2020), evitar el rango (2021–2026), la magnificación con
MCSP y la barrera de localidad (2018–2022), `P ⊆ P/poly` en Sagitta (B3) y Ladner por bloques de largo.
-/

open Filter Set

namespace Sagitta.Map.Borde.BordeAlto

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Finitud
open Sagitta.Map.Tiempo.Infinito Sagitta.Map.Tiempo.Relleno Sagitta.Map.Borde.Tricotomia
open Sagitta.Map.Borde.SatEnElBorde Sagitta.Map.Borde.SatPorBloques
open Sagitta.Map.Borde.RelojDeLadner

/-! ## 1. Ladner de cslib-frontier -/

section Ladner

open Cslib.Complexity Turing.MultiTapeTM

/-- Una función acotada toma algún valor infinitas veces (el palomar en el infinito). -/
theorem frecuente_de_acotada {f : ℕ → ℕ} {C : ℕ} (hC : ∀ n, f n ≤ C) : ∃ i, ∃ᶠ n in atTop, f n = i := by
  by_contra hno
  have hno' : ∀ i, ∀ᶠ n in atTop, f n ≠ i := fun i => not_frequently.1 fun h => hno ⟨i, h⟩
  have : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (C + 1), f n ≠ i :=
    (Finset.range (C + 1)).eventually_all.2 fun i _ => hno' i
  obtain ⟨n, hn⟩ := this.exists
  exact hn (f n) (Finset.mem_range.2 (Nat.lt_succ_of_le (hC n))) rfl

/-- **`SATH ∈ P` si y solo si el reloj de Ladner está acotado.** -/
theorem sath_en_P_iff_acotado : Ladner.SATH ∈ Cslib.Complexity.P encBits ↔ ∃ C, ∀ n, Ladner.H n ≤ C := by
  refine ⟨Ladner.exists_H_le_of_mem_P, fun ⟨C, hC⟩ => ?_⟩
  obtain ⟨i, hi⟩ := frecuente_de_acotada hC
  exact Ladner.SATH_mem_P_of_frequently_H_eq hi

/-- **El reloj de Ladner no oscila**, sin hipótesis: está acotado o tiende a infinito. -/
theorem reloj_dicotomia : (∃ C, ∀ n, Ladner.H n ≤ C) ∨ Tendsto Ladner.H atTop atTop := by
  by_cases h : Ladner.SATH ∈ Cslib.Complexity.P encBits
  · exact Or.inl (Ladner.exists_H_le_of_mem_P h)
  · exact Or.inr (Ladner.tendsto_H_of_notMem_P h)

/-- … y las dos salidas se excluyen. -/
theorem reloj_no_ambas : ¬ ((∃ C, ∀ n, Ladner.H n ≤ C) ∧ Tendsto Ladner.H atTop atTop) := by
  rintro ⟨⟨C, hC⟩, ht⟩
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop C).exists
  exact absurd (hC n) (by omega)

/-- **El largo del relleno de Ladner**: una fórmula de largo `m` se rellena con `m ^ H m` unos. -/
noncomputable def rellenoLadner (m : ℕ) : ℕ := m ^ Ladner.H m

/-- Con el reloj acotado, el relleno es polinomial. -/
theorem bajo_relleno_de_acotado {C : ℕ} (hC : ∀ n, Ladner.H n ≤ C) : Bajo rellenoLadner :=
  ⟨1, C, fun m => by
    rw [one_mul, rellenoLadner]
    calc m ^ Ladner.H m ≤ (m + 1) ^ Ladner.H m := Nat.pow_le_pow_left (by omega) _
      _ ≤ (m + 1) ^ C := Nat.pow_le_pow_right (by omega) (hC m)⟩

/-- Con el reloj que tiende a infinito, el relleno le gana a todo polinomio. -/
theorem sobre_relleno_de_tendsto (h : Tendsto Ladner.H atTop atTop) : Sobre rellenoLadner := by
  intro c k
  filter_upwards [h.eventually_ge_atTop (k + 1), eventually_gt_atTop (c * 2 ^ k)] with n hH hn
  have hn1 : 1 ≤ n := by omega
  have h1 : (n + 1) ^ k ≤ 2 ^ k * n ^ k := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) k
  have h2 : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn1
  calc c * (n + 1) ^ k ≤ c * (2 ^ k * n ^ k) := Nat.mul_le_mul_left c h1
    _ = (c * 2 ^ k) * n ^ k := by ring
    _ < n * n ^ k := Nat.mul_lt_mul_of_pos_right hn (by omega)
    _ = n ^ (k + 1) := by ring
    _ ≤ n ^ Ladner.H n := Nat.pow_le_pow_right hn1 hH

/-- **El relleno está abajo si y solo si `SATH ∈ P`.** -/
theorem relleno_bajo_iff : Bajo rellenoLadner ↔ Ladner.SATH ∈ Cslib.Complexity.P encBits := by
  constructor
  · intro hb
    by_contra hP
    exact bajo_no_sobre hb (sobre_relleno_de_tendsto (Ladner.tendsto_H_of_notMem_P hP))
  · intro hP
    obtain ⟨C, hC⟩ := Ladner.exists_H_le_of_mem_P hP
    exact bajo_relleno_de_acotado hC

/-- **El relleno está arriba si y solo si `SATH ∉ P`.** -/
theorem relleno_sobre_iff : Sobre rellenoLadner ↔ Ladner.SATH ∉ Cslib.Complexity.P encBits := by
  constructor
  · intro hs hP
    exact sobre_no_bajo hs (relleno_bajo_iff.2 hP)
  · intro hP
    exact sobre_relleno_de_tendsto (Ladner.tendsto_H_of_notMem_P hP)

/-- **El relleno de Ladner no oscila nunca.** -/
theorem relleno_no_oscila : ¬ Oscila rellenoLadner := by
  rintro ⟨hb, hs⟩
  by_cases hP : Ladner.SATH ∈ Cslib.Complexity.P encBits
  · exact hb (relleno_bajo_iff.2 hP)
  · exact hs (relleno_sobre_iff.2 hP)

/-- **Bajo P ≠ NP el relleno está arriba**: es la mitad «no está en P» de Ladner, leída en la tricotomía. -/
theorem relleno_sobre_de_P_ne_NP {α : Type} {enc : α ↪ List Bool} (h : Cslib.Complexity.P enc ≠ Cslib.Complexity.NP enc) : Sobre rellenoLadner :=
  relleno_sobre_iff.2 (Ladner.SATH_notMem_P h)

/-- … pero apenas: el relleno es a lo sumo cuasipolinomial, `m ^ log₂ log₂ m`. -/
theorem relleno_cuasipolinomial (m : ℕ) : rellenoLadner m ≤ m ^ Nat.log 2 (Nat.log 2 m) := by
  rw [rellenoLadner]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := Ladner.H_le 0
    simp at this
    simp [this]
  · exact Nat.pow_le_pow_right hm (Ladner.H_le m)

/-- **Ladner por palabras** (Schöning 1982, en cslib-frontier): para todo `B ∈ NP` fuera de `P` hay un `G ∈ P` tal que
`B` fuera de `G` está en NP, no en P y no es NP-completo. -/
theorem ladner_por_palabras {B : Set (List Bool)} (hNP : B ∈ Cslib.Complexity.NP encBits) (hP : B ∉ Cslib.Complexity.P encBits) :
    ∃ G ∈ Cslib.Complexity.P encBits, G.ite ∅ B ∈ Cslib.Complexity.NP encBits ∧ G.ite ∅ B ∉ Cslib.Complexity.P encBits ∧ ¬ NPComplete encBits (G.ite ∅ B) := by
  have hdec : IsDecidable B encBits := isDecidable_of_mem_EXP (NP_subset_EXP hNP)
  obtain ⟨G, hG, hnotP, -, hBA⟩ := exists_mem_P_ite_empty_lt hdec hP
  exact ⟨G, hG, ite_mem_NP hG empty_mem_NP hNP, hnotP, fun hc => hBA (hc.2 encBits B hNP)⟩

/-- `G.ite ∅ B` es `B` fuera de `G`. -/
theorem ite_vacio (G B : Set (List Bool)) : G.ite ∅ B = {y | y ∉ G ∧ y ∈ B} := by
  ext y; simp [Set.ite, and_comm]

/-- **El puente con los bloques**: si `G` es cerrado por largo, `B` fuera de `G` es `B` en los largos de `Cᶜ`. -/
theorem ite_de_largos (C : Set ℕ) (B : Set (List Bool)) :
    ({y | y.length ∈ C} : Set (List Bool)).ite ∅ B = {y | y.length ∉ C ∧ y ∈ B} := by
  rw [ite_vacio]; rfl

/-- **El problema por bloques de `RelojDeLadner` es un `G.ite ∅ A`**, con `G` cerrado por largo (los largos cuyo
bloque no se elige). -/
theorem porBloquesReloj_es_ite (A : Set (List Bool)) (e : ℕ → ℕ) (sel : ℕ → Bool) :
    porBloquesReloj A e sel = ({y | y.length ∈ {n | sel (bloque e n) = false}} : Set (List Bool)).ite ∅ A := by
  rw [ite_de_largos]
  ext y
  simp [porBloquesReloj]

/-- **Ladner por palabras para SAT de cslib**: si P ≠ NP, SAT (en bits) fuera de un `G ∈ P` es NP-intermedio. -/
theorem ladner_por_palabras_SATH {α : Type} {enc : α ↪ List Bool} (h : Cslib.Complexity.P enc ≠ Cslib.Complexity.NP enc) :
    ∃ G ∈ Cslib.Complexity.P encBits, G.ite ∅ Ladner.SATH ∈ Cslib.Complexity.NP encBits ∧ G.ite ∅ Ladner.SATH ∉ Cslib.Complexity.P encBits ∧
      ¬ NPComplete encBits (G.ite ∅ Ladner.SATH) :=
  ladner_por_palabras Ladner.SATH_mem_NP (Ladner.SATH_notMem_P h)

end Ladner

/-! ## 2. «Infinitas veces» contra «casi siempre» -/

section IOCS

/-- La cota polinomial `c·(n+1)^k`. -/
def pol (c k : ℕ) (n : ℕ) : ℕ := c * (n + 1) ^ k

/-- **Difícil casi siempre**: para todo largo grande, el costo pasa de `s`. -/
def DificilCS (f s : ℕ → ℕ) : Prop := ∀ᶠ n in atTop, s n < f n
/-- **Difícil infinitas veces**. -/
def DificilIO (f s : ℕ → ℕ) : Prop := ∃ᶠ n in atTop, s n < f n
/-- **Fácil casi siempre**: para todo largo grande, el costo no pasa de `s`. -/
def FacilCS (f s : ℕ → ℕ) : Prop := ∀ᶠ n in atTop, f n ≤ s n
/-- **Fácil infinitas veces**. -/
def FacilIO (f s : ℕ → ℕ) : Prop := ∃ᶠ n in atTop, f n ≤ s n

variable {f s : ℕ → ℕ}

theorem dificilCS_io (h : DificilCS f s) : DificilIO f s := h.frequently
theorem facilCS_io (h : FacilCS f s) : FacilIO f s := h.frequently

/-- No ser difícil casi siempre es ser fácil infinitas veces. -/
theorem no_dificilCS_iff : ¬ DificilCS f s ↔ FacilIO f s := by
  rw [DificilCS, FacilIO, not_eventually]; simp only [not_lt]

/-- No ser fácil casi siempre es ser difícil infinitas veces. -/
theorem no_facilCS_iff : ¬ FacilCS f s ↔ DificilIO f s := by
  rw [FacilCS, DificilIO, not_eventually]; simp only [not_le]

/-- Las dos «casi siempre» se excluyen. -/
theorem no_facil_y_dificil_cs : ¬ (FacilCS f s ∧ DificilCS f s) := by
  rintro ⟨h1, h2⟩
  obtain ⟨n, h1, h2⟩ := (h1.and h2).exists
  omega

/-- **Abajo es fácil casi siempre para algún polinomio.** -/
theorem bajo_iff_facilCS : Bajo f ↔ ∃ c k, FacilCS f (pol c k) := by
  constructor
  · rintro ⟨c, k, h⟩; exact ⟨c, k, Eventually.of_forall h⟩
  · rintro ⟨c, k, h⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 h
    exact pol_de_casi (c := c) (k := k) (N := N) hN

/-- **Arriba es difícil casi siempre para todo polinomio.** -/
theorem sobre_iff_dificilCS : Sobre f ↔ ∀ c k, DificilCS f (pol c k) := Iff.rfl

/-- **Oscilar es ni fácil casi siempre ni difícil casi siempre.** -/
theorem oscila_iff_ni_ni : Oscila f ↔ ¬ (∃ c k, FacilCS f (pol c k)) ∧ ¬ (∀ c k, DificilCS f (pol c k)) := by
  rw [Oscila, bajo_iff_facilCS, sobre_iff_dificilCS]

/-- **Oscilar, en «infinitas veces»**: difícil infinitas veces para todo polinomio, fácil infinitas veces para alguno. -/
theorem oscila_iff_io : Oscila f ↔ (∀ c k, DificilIO f (pol c k)) ∧ (∃ c k, FacilIO f (pol c k)) := by
  rw [oscila_iff_ni_ni]
  push Not
  simp only [no_facilCS_iff, no_dificilCS_iff]

/-- Arriba da difícil infinitas veces, y abajo fácil infinitas veces: las regiones extremas, leídas en i.o. -/
theorem sobre_io (h : Sobre f) (c k : ℕ) : DificilIO f (pol c k) := dificilCS_io (h c k)
theorem bajo_io (h : Bajo f) : ∃ c k, FacilIO f (pol c k) := by
  obtain ⟨c, k, h⟩ := bajo_iff_facilCS.1 h; exact ⟨c, k, facilCS_io h⟩

/-! ### Con Bydžovský–Krajíček–Oliveira -/

open Sagitta.Map.Borde.OscilacionParikh

/-- **`Buenos` es la cota superior infinitas veces.** -/
theorem verdadero_buenos_iff_facilIO {P : Problema} {c k : ℕ} :
    Verdadero (Buenos P c k) ↔ FacilIO (sucNat P) (pol c k) := by
  rw [verdadero_buenos_iff, FacilIO, Nat.frequently_atTop_iff_infinite]
  rfl

open Sagitta.Map.Acotada in
/-- **S¹₂ no demuestra la cota superior infinitas veces de un SAT que oscila**: hay un polinomio con la cota i.o.
verdadera, una fórmula acotada que la define, y S¹₂ no deriva `∀ x ∃ y φ`. -/
theorem s12_no_demuestra_facil_io (hO : Oscila (sucNat satMarco)) :
    ∃ c k, FacilIO (sucNat satMarco) (pol c k) ∧ ∃ φ : FirstOrder.Language.Formula L (Fin 2),
      EsAcotada φ ∧ Define φ (Buenos satMarco c k) ∧ ¬ DerivaS12 (cierre (existeY φ)) := by
  obtain ⟨c, k, hv⟩ := (no_sobre_iff_verdadero satMarco).1 hO.2
  obtain ⟨φ, hφ, hdef⟩ := FormulaBuenos.formulaBuenos c k
  exact ⟨c, k, verdadero_buenos_iff_facilIO.1 hv, φ, hφ, hdef, s12_no_deriva_oscila hO c k hφ hdef⟩

open Sagitta.Map.Acotada in
/-- **En S¹₂, una cota superior i.o. demostrada es una cota a.e.** Si S¹₂ deriva «los largos buenos de `satMarco` para
`c·(m+1)^k` no se acaban» (con cualquier fórmula acotada que lo defina), entonces `satMarco` es fácil casi siempre
para algún polinomio. -/
theorem s12_io_da_cs {c k : ℕ} {φ : FirstOrder.Language.Formula L (Fin 2)} (hφ : EsAcotada φ)
    (hdef : Define φ (Buenos satMarco c k)) (hder : DerivaS12 (cierre (existeY φ))) :
    ∃ c' k', FacilCS (sucNat satMarco) (pol c' k') := by
  have hdem : DemuestraExiste φ := (demuestraExiste_iff φ).2 hder
  have := (no_oscila_de_demuestra parikhSana_S12 (Set.mem_univ _) ⟨φ, hφ, hdef, hdem⟩).2.2
  exact bajo_iff_facilCS.1 ((bajo_sucNat_iff satMarco).2 this)

end IOCS

/-! ## 3. Una magnificación de juguete, por relleno -/

section Magnificacion

/-- **`L` rellenado exponencialmente**: en el largo `N` lee los primeros `⌊log₂ N⌋` bits. -/
def leerLog (L : Problema) : Problema := fun w => L (w.take (Nat.log 2 w.length))

theorem lt_dos_pow' (n : ℕ) : n < 2 ^ n := Nat.lt_two_pow_self

/-- El rellenado en `2^n` se obtiene de `L` en `n` (las entradas de `L` son las primeras `n` del rellenado). -/
theorem leerLog_fija (L : Problema) (n : ℕ) :
    SeObtieneFijando (rebanada (leerLog L) (2 ^ n)) (rebanada L n) := by
  refine ⟨fun i => .inl ⟨i.val, lt_of_lt_of_le i.isLt (lt_dos_pow' n).le⟩, fun x => ?_⟩
  simp only [rebanada, leerLog, List.length_ofFn, Nat.log_pow (by norm_num : 1 < 2)]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]; have := lt_dos_pow' n; omega
  · intro i h1 h2
    simp [sustituir]

/-- `L` en `n` se obtiene del rellenado en `2^n` (las entradas sobrantes se fijan en `false`). -/
theorem fija_leerLog (L : Problema) (n : ℕ) :
    SeObtieneFijando (rebanada L n) (rebanada (leerLog L) (2 ^ n)) := by
  refine ⟨fun i => if h : i.val < n then .inl ⟨i.val, h⟩ else .inr false, fun x => ?_⟩
  simp only [rebanada, leerLog, List.length_ofFn, Nat.log_pow (by norm_num : 1 < 2)]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]; have := lt_dos_pow' n; omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp [sustituir, h1]

/-- El rellenado no cuesta más que el original, más dos. -/
theorem sucNat_leerLog_le (L : Problema) (n : ℕ) : sucNat (leerLog L) (2 ^ n) ≤ sucNat L n + 2 :=
  sucNat_fijar (leerLog_fija L n)

/-- Y el original no cuesta más que el rellenado, más dos: es un cambio de variable. -/
theorem sucNat_le_leerLog (L : Problema) (n : ℕ) : sucNat L n ≤ sucNat (leerLog L) (2 ^ n) + 2 :=
  sucNat_fijar (fija_leerLog L n)

/-- **La magnificación de juguete**: una cota inferior `s(N) + 2` para el rellenado en `N = 2^n` da `s(N)` para `L` en
el largo `n = log₂ N`. -/
theorem magnifica (L : Problema) (s : ℕ → ℕ) (n : ℕ) (h : s (2 ^ n) + 2 < sucNat (leerLog L) (2 ^ n)) :
    s (2 ^ n) < sucNat L n := by
  have := sucNat_leerLog_le L n; omega

/-- Una cota polilogarítmica en `N` es polinomial en `n`: `(log₂ 2^n + 1)^k = (n+1)^k`. -/
theorem polylog_dos_pow (k n : ℕ) : (Nat.log 2 (2 ^ n) + 1) ^ k = (n + 1) ^ k := by
  rw [Nat.log_pow (by norm_num : 1 < 2)]

/-- **Cota polilogarítmica i.o. para el rellenado ⇒ fuera de P/poly.** Si para todo `k` el rellenado pide más de
`(log₂ N + 1)^k + 2` compuertas en infinitos `N = 2^n`, `L` no está abajo. -/
theorem magnifica_polylog (L : Problema)
    (h : ∀ k, ∃ᶠ n in atTop, (Nat.log 2 (2 ^ n) + 1) ^ k + 2 < sucNat (leerLog L) (2 ^ n)) :
    ¬ Bajo (sucNat L) := by
  rintro ⟨c, k, hc⟩
  obtain ⟨n, hn, hcn⟩ := ((h (k + 1)).and_eventually (eventually_ge_atTop c)).exists
  rw [polylog_dos_pow] at hn
  have h1 := magnifica L (fun _ => (n + 1) ^ (k + 1)) n hn
  have h2 := hc n
  have h3 : c * (n + 1) ^ k ≤ (n + 1) ^ (k + 1) := by
    rw [pow_succ, mul_comm ((n + 1) ^ k)]; exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Casi siempre y todo polinomio**: si el rellenado pide más de `c·(log₂ N + 1)^k + 2` para todo `N = 2^n` grande,
`L` está arriba. -/
theorem magnifica_polylog_cs (L : Problema)
    (h : ∀ c k, ∀ᶠ n in atTop, c * (Nat.log 2 (2 ^ n) + 1) ^ k + 2 < sucNat (leerLog L) (2 ^ n)) :
    Sobre (sucNat L) := by
  intro c k
  filter_upwards [h c k] with n hn
  rw [polylog_dos_pow] at hn
  exact magnifica L (fun _ => c * (n + 1) ^ k) n hn

/-- **Y al revés**: el juguete no gana nada; si `L` está fuera de P/poly, el rellenado pide más que cualquier cota
polilogarítmica en infinitos `N = 2^n`. -/
theorem polylog_de_no_bajo (L : Problema) (h : ¬ Bajo (sucNat L)) (c k : ℕ) :
    ∃ᶠ n in atTop, c * (Nat.log 2 (2 ^ n) + 1) ^ k < sucNat (leerLog L) (2 ^ n) := by
  have hio : DificilIO (sucNat L) (pol (c + 2) k) :=
    no_facilCS_iff.1 fun hh => h (bajo_iff_facilCS.2 ⟨_, _, hh⟩)
  refine hio.mono fun n hn => ?_
  rw [polylog_dos_pow]
  have h0 := sucNat_le_leerLog L n
  have h1 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : (c + 2) * (n + 1) ^ k = c * (n + 1) ^ k + 2 * (n + 1) ^ k := by ring
  simp only [pol] at hn
  omega

/-- **Para SAT**: una cota polilogarítmica i.o. para SAT rellenado exponencialmente saca a `satMarco` de P/poly, y
con eso a `satBits` (`MarcoDeBits.lean` lo da en la otra dirección; aquí basta `satMarco`). -/
theorem sat_magnifica
    (h : ∀ k, ∃ᶠ n in atTop, (Nat.log 2 (2 ^ n) + 1) ^ k + 2 < sucNat (leerLog satMarco) (2 ^ n)) :
    satMarco ∉ PsobrePoly := fun hP => magnifica_polylog satMarco h ((bajo_sucNat_iff satMarco).2 hP)

end Magnificacion

/- Mutantes probados (25 nov 2026, fuera del repositorio, `borde-alto/Mut.lean` y
`MutFallan.lean`):
1. `frecuente_de_acotada` sin la cota (base de `sath_en_P_iff_acotado`): falso, y la negación se prueba con `f = id`.
2. `reloj_dicotomia` para una `f` cualquiera, sin Ladner: falso; `f n = 0` en pares y `n` en impares no está acotada
   ni tiende a infinito (negación probada). La dicotomía es de Ladner, no de la aritmética.
3. `relleno_cuasipolinomial` con exponente `1` en vez de `log₂ log₂ m`: la prueba no cierra, y en `m = 0` es falso
   (`0^0 = 1 > 0^1`).
4. `ladner_por_palabras` sin `B ∉ P`: falso con `B = ∅` (`G.ite ∅ ∅ = ∅ ∈ P`; negación probada).
5. `bajo_iff_facilCS` con «infinitas veces» en vez de «casi siempre»: falso con `t alterna` de `Tricotomia.lean`
   (`2^n` en pares, `n` en impares: oscila y es fácil i.o.; negación probada).
6. `magnifica` sin el `+ 2`: `omega` falla (fijar entradas cuesta dos compuertas).
7. `leerLog_fija` en el largo `n + 1` en vez de `2^n`: `Nat.log_pow` no reescribe y los largos no calzan.
8. `oscila_iff_io` con los cuantificadores cambiados (`∃` difícil i.o., `∀` fácil i.o.): falso con `t alterna`
   (con `c = 0` solo el largo `0` es fácil; negación probada). -/

end Sagitta.Map.Borde.BordeAlto
