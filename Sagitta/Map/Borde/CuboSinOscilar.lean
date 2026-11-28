import Sagitta.Map.Borde.Tricotomia
import Sagitta.Map.DosCuentas
import Sagitta.Map.CuboCostos

/-!
# En el cubo, la oscilación colapsa (3c)

La pregunta de José (24 nov 2026): «en el cubo del universo cerrado, ¿cómo se vería la oscilación de la complejidad?».
El vocabulario de `Tricotomia.lean` (`Bajo`, `Sobre`, `Oscila`) se aplica aquí al tiempo `t m` (consultas al verificador)
como función del tamaño `m`. Las cuentas son de `DosCuentas.lean` y `CuboCostos.lean` (de otra sesión; solo se
importan).

## Lo que se prueba

* `sobre_de_exponencial`: si `2^(m − L) ≤ t m + 1` para todo `m`, el tiempo está arriba (`Sobre`).
* (i) **Caja negra, programa fijo, sin cita ⇒ siempre arriba** (`tiempo_sobre_sin_cita`, `tiempo_no_oscila_sin_cita`):
  corolario de `tiempo_uniforme_sin_cita`. La tricotomía colapsa a una sola región: el tiempo nunca oscila ni está
  abajo.
* (ii) **Oscilar en tiempo obliga a pagar en otro eje** (`cita_casi_lineal`, `cita_sube_sin_cota`,
  `cita_sube_si_no_sobre`): con cita `s m` variable, en todo tamaño donde el tiempo es polinomial la cita es casi lineal,
  `m − L − ⌈log₂(c·(m+1)^k + 1)⌉ ≤ s m` (de `cuenta_por_instancia_uniforme`), y por lo tanto sube sin cota a lo largo de
  esos tamaños. Si el tiempo no está arriba (abajo u oscila), hay un largo infinito donde la cita sube sin cota. En el
  cubo, el zigzag va de la cara del tiempo a la de la memoria escrita; nunca baja al origen.
* (iii) **El espacio no rescata** (`espacio_acotado_pide_descripcion`, `espacio_y_descripcion_acotados`): con `cubo_es_region`,
  si el espacio es a lo sumo `E` en todo tamaño, la descripción crece como `m − (E − 1)` sin importar el tiempo; con la
  descripción también acotada, el cubo no se alcanza en tamaños grandes. La oscilación no puede venir del espacio.

## Dónde queda la oscilación de SAT, si existe

Solo en dos lugares: con **cita** en los largos buenos (lo no uniforme: `huecos_de_sat` de `Relleno.lean`, donde los
circuitos por largo son la cita), o en **caja blanca**, si leer la fórmula baja el `m` efectivo (ver las notas del
proyecto). En caja negra, con un programa fijo y sin cita, el tiempo está arriba siempre.

## Lo que no

* Todo es caja negra y relativiza (lo dice `CuboCostos.lean`). Nada sobre P contra NP.
-/

open Filter

namespace Sagitta.Map.Borde.CuboSinOscilar

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Infinito
open Sagitta.Map.Borde.Tricotomia
open Sagitta.Map.Tiempo.LeyTresMemorias Sagitta.Map.Tiempo.LeyTresMemorias.ArbolV
open Sagitta.Map.Tiempo.DosCuentas

/-- **Una cota exponencial pone el tiempo arriba.** -/
theorem sobre_de_exponencial {t : ℕ → ℕ} {L : ℕ} (h : ∀ m, 2 ^ (m - L) ≤ t m + 1) : Sobre t := by
  intro c k
  obtain ⟨N, hN⟩ := pol_menor_dos_pow (2 ^ L * (c + 1)) k
  refine eventually_atTop.2 ⟨max N L, fun m hm => ?_⟩
  have h1 := hN m (le_of_max_le_left hm)
  have hmL : L ≤ m := le_of_max_le_right hm
  have h2 : 2 ^ m = 2 ^ L * 2 ^ (m - L) := by rw [← pow_add, Nat.add_sub_cancel' hmL]
  rw [h2, mul_assoc] at h1
  have h3 : (c + 1) * (m + 1) ^ k < 2 ^ (m - L) := Nat.lt_of_mul_lt_mul_left h1
  have h4 := h m
  have h5 : 1 ≤ (m + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- `⌈log₂(c·(m+1)^k + 1)⌉ ≤ m − (K + L)` desde algún tamaño: el logaritmo de un polinomio es chico. -/
theorem clog_pol_chico (c k K L : ℕ) : ∀ᶠ m in atTop, Nat.clog 2 (c * (m + 1) ^ k + 1) ≤ m - (K + L) := by
  obtain ⟨N, hN⟩ := pol_menor_dos_pow (2 ^ (K + L) * (c + 1)) k
  refine eventually_atTop.2 ⟨max N (K + L), fun m hm => Nat.clog_le_of_le_pow ?_⟩
  have h1 := hN m (le_of_max_le_left hm)
  have h2 : 2 ^ m = 2 ^ (K + L) * 2 ^ (m - (K + L)) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_max_le_right hm)]
  rw [h2, mul_assoc] at h1
  have h3 : (c + 1) * (m + 1) ^ k < 2 ^ (m - (K + L)) := Nat.lt_of_mul_lt_mul_left h1
  have h5 : 1 ≤ (m + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  nlinarith

section Cubo

variable {Y C : ℕ → Type} [∀ m, Fintype (Y m)] [∀ m, DecidableEq (Y m)] [∀ m, Fintype (C m)] {s t : ℕ → ℕ}
  {P : Type} [Fintype P] {L : ℕ}

/-! ## (i) Sin cita, siempre arriba -/

/-- **Caja negra, un mismo juego de programas para todo tamaño, sin cita: el tiempo está arriba.** -/
theorem tiempo_sobre_sin_cita (hY : ∀ m, Fintype.card (Y m) = 2 ^ m) (hP : Fintype.card P ≤ 2 ^ L)
    (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ 0) (A : ∀ m, P → C m → ArbolV (Y m) Bool (Y m))
    (h : ∀ m, Resuelve igual (A m) (t m)) : Sobre t :=
  sobre_de_exponencial (tiempo_uniforme_sin_cita hY hP hC A h)

/-- La tricotomía colapsa: sin cita, el tiempo ni oscila ni está abajo. -/
theorem tiempo_no_oscila_sin_cita (hY : ∀ m, Fintype.card (Y m) = 2 ^ m) (hP : Fintype.card P ≤ 2 ^ L)
    (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ 0) (A : ∀ m, P → C m → ArbolV (Y m) Bool (Y m))
    (h : ∀ m, Resuelve igual (A m) (t m)) : ¬ Oscila t ∧ ¬ Bajo t := by
  have hs := tiempo_sobre_sin_cita hY hP hC A h
  exact ⟨fun ho => ho.2 hs, sobre_no_bajo hs⟩

/-! ## (ii) Con cita: oscilar en tiempo se paga en la cita -/

/-- **Donde el tiempo es polinomial, la cita es casi lineal.** -/
theorem cita_casi_lineal (hY : ∀ m, Fintype.card (Y m) = 2 ^ m) (hP : Fintype.card P ≤ 2 ^ L)
    (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m) (A : ∀ m, P → C m → ArbolV (Y m) Bool (Y m))
    (h : ∀ m, Resuelve igual (A m) (t m)) {c k m : ℕ} (ht : t m ≤ c * (m + 1) ^ k) :
    m - L - Nat.clog 2 (c * (m + 1) ^ k + 1) ≤ s m := by
  have h1 := cuenta_por_instancia_uniforme hY hP hC A h m
  have h2 : Nat.clog 2 (t m + 1) ≤ Nat.clog 2 (c * (m + 1) ^ k + 1) := Nat.clog_mono_right _ (by omega)
  omega

/-- **Y sube sin cota a lo largo de esos tamaños**: en todo largo infinito donde el tiempo es polinomial, la cita pasa
de cualquier constante. -/
theorem cita_sube_sin_cota (hY : ∀ m, Fintype.card (Y m) = 2 ^ m) (hP : Fintype.card P ≤ 2 ^ L)
    (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m) (A : ∀ m, P → C m → ArbolV (Y m) Bool (Y m))
    (h : ∀ m, Resuelve igual (A m) (t m)) {U : Ultrafilter ℕ} (hU : LargoInfinito U) {c k : ℕ}
    (ht : ∀ᶠ m in (U : Filter ℕ), t m ≤ c * (m + 1) ^ k) (K : ℕ) : ∀ᶠ m in (U : Filter ℕ), K ≤ s m := by
  refine ((ht.and (largo_de_atTop hU (clog_pol_chico c k K L))).and
    (largo_de_atTop hU (eventually_ge_atTop (K + L)))).mono fun m hm => ?_
  have h1 := cita_casi_lineal hY hP hC A h hm.1.1
  have h2 := hm.1.2
  have h3 := hm.2
  have : K ≤ m - L - Nat.clog 2 (c * (m + 1) ^ k + 1) := by omega
  omega

/-- **Si el tiempo no está arriba, hay un largo infinito donde la cita sube sin cota.** El zigzag de un tiempo que
oscila va a la cara de la memoria escrita. -/
theorem cita_sube_si_no_sobre (hY : ∀ m, Fintype.card (Y m) = 2 ^ m) (hP : Fintype.card P ≤ 2 ^ L)
    (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m) (A : ∀ m, P → C m → ArbolV (Y m) Bool (Y m))
    (h : ∀ m, Resuelve igual (A m) (t m)) (hno : ¬ Sobre t) :
    ∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∀ K, ∀ᶠ m in (U : Filter ℕ), K ≤ s m := by
  obtain ⟨U, hU, c, k, ht⟩ := (no_sobre_iff t).1 hno
  exact ⟨U, hU, cita_sube_sin_cota hY hP hC A h hU ht⟩

end Cubo

/-! ## (iii) El espacio no rescata -/

open Sagitta.Map.Tiempo.CuboCostos in
/-- **Con espacio acotado, la descripción crece linealmente, con cualquier tiempo.** -/
theorem espacio_acotado_pide_descripcion {x y : ℕ → ℕ} {E : ℕ} (h : ∀ m, AlcanzableCubo m (x m) E (y m)) (m : ℕ) :
    m - (E - 1) ≤ x m := by
  have := (cubo_es_region m (x m) E (y m)).1 (h m)
  have := min_le_right (y m) (E - 1)
  omega

open Sagitta.Map.Tiempo.CuboCostos in
/-- Con espacio y descripción acotados, ningún tiempo alcanza los tamaños grandes. -/
theorem espacio_y_descripcion_acotados {y : ℕ → ℕ} {E X : ℕ} :
    ¬ ∀ m, AlcanzableCubo m X E (y m) := by
  intro h
  have := espacio_acotado_pide_descripcion (x := fun _ => X) h (X + E + 1)
  omega

/-! ## Controles -/

/-- `sobre_de_exponencial` necesita la cota en todo tamaño grande: el tiempo `2^m` está arriba (con `L = 0`). -/
example : Sobre (fun m => 2 ^ m) := sobre_de_exponencial (L := 0) fun m => by simp

/-- Y un tiempo polinomial no cumple la hipótesis: la cota exponencial excluye lo de abajo. -/
example : ¬ ∀ m, 2 ^ (m - 0) ≤ (fun m => m ^ 2) m + 1 := by
  intro h
  have := h 5
  norm_num at this

open Sagitta.Map.Tiempo.CuboCostos in
/-- (iii) no es vacía: el cubo sí se alcanza con descripción `m` y espacio `1` (la tabla), así que la cota
`m − (E − 1) ≤ x` es la que se toca. -/
example (m : ℕ) : AlcanzableCubo m m 1 0 := (cubo_es_region m m 1 0).2 (by simp)

/- Mutante probado (25 nov 2026, en /tmp/claude-noche/MutCubo.lean): en `cita_casi_lineal`, quitar el `− L`
(`m − ⌈log₂(...)⌉ ≤ s m`) no compila: el programa fijo aporta `L` bits que la cita no tiene que pagar. -/

end Sagitta.Map.Borde.CuboSinOscilar
