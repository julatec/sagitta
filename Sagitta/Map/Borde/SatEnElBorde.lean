import Sagitta.Map.Borde.Tricotomia
import Sagitta.Map.Borde.PBombeo

/-!
# Dónde puede estar SAT: abajo, arriba u oscilando con huecos (fase B2)

El vocabulario es el de `Tricotomia.lean` (`Bajo`, `Sobre`, `Oscila`), aplicado al costo de circuitos
`sucNat L : ℕ → ℕ` (el tamaño del menor circuito por largo, de `Finitud.lean`). El problema es el SAT enmarcado
`satMarco` de `Relleno.lean`, que es rellenable (`rellenable_satMarco`). Es el mismo que usa la jugada de relleno de
`PBombeo.lean` (`JugadaRelleno`, `jugada_relleno_iff`): aquí se dice **en cuál de las tres regiones** queda SAT según
la jugada valga o no, y qué forma tienen sus largos buenos en cada una.

## Lo que se prueba

* `bajo_sucNat_iff`: `Bajo (sucNat L) ↔ L ∈ PsobrePoly`.
* **La lectura de arriba** (`sobre_iff_buenos_finitos`): un costo está arriba si y solo si, para cada polinomio, sus
  largos buenos (`f n ≤ c·(n+1)^k`) son finitos.
* **La lectura de oscilar** (`oscila_iff_buenos_ralos`): para un problema rellenable, el costo oscila si y solo si hay
  un polinomio con infinitos largos buenos **y** para todo polinomio y toda ventana polinomial hay infinitos huecos
  (`Hueco` de `Relleno.lean`): los largos buenos existen pero están más ralos que cualquier polinomio. Las dos
  direcciones están probadas.
* **La tricotomía de un problema rellenable** (`tricotomia_rellenable`): está en P/poly, o su costo está arriba, o
  oscila con huecos más que polinomiales; y las tres salidas se excluyen.
* **La tricotomía de SAT** (`tricotomia_sat`): `satBits ∈ PsobrePoly`, o el costo de `satMarco` está arriba, o oscila y
  tiene infinitos huecos para todo polinomio y toda ventana. Con `jugada_iff_arriba_u_oscila`: la jugada de relleno
  de `PBombeo.lean` contra `satMarco` es exactamente «arriba u oscila».

## Lo que no

* Nada sobre en cuál de las tres está SAT; sigue abierto (estar fuera de P/poly es más fuerte que P ≠ NP).
* La primera rama habla de `satBits` y las otras dos de `satMarco`; aquí la tricotomía de SAT es un «o». El puente
  `SatMarcoDeSatBits` de `Relleno.lean` se probó después en `MarcoDeBits.lean` (25 nov 2026, continuación), donde
  `tricotomia_sat_exacta` la vuelve una partición sobre `satMarco`. Para un problema rellenable cualquiera ya lo era.
* Que los ceros de la sucesión de largos difíciles de SAT sean raros en sentido de medida está en `HuecosFlacos.lean`.
-/

open Filter Set

namespace Sagitta.Map.Borde.SatEnElBorde

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Finitud
open Sagitta.Map.Tiempo.Relleno Sagitta.Map.Borde.Tricotomia Sagitta.Map.Borde.PBombeo

/-- Abajo del borde, para circuitos, es P/poly. -/
theorem bajo_sucNat_iff (L : Problema) : Bajo (sucNat L) ↔ L ∈ PsobrePoly := by
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff]; rfl

/-- **Arriba es tener, para cada polinomio, solo finitos largos buenos.** -/
theorem sobre_iff_buenos_finitos (f : ℕ → ℕ) :
    Sobre f ↔ ∀ c k, {n | f n ≤ c * (n + 1) ^ k}.Finite := by
  unfold Sobre
  refine forall₂_congr fun c k => ?_
  rw [← Nat.cofinite_eq_atTop, eventually_cofinite]
  simp only [not_lt]

/-- No estar arriba es tener un polinomio con infinitos largos buenos. -/
theorem no_sobre_iff_buenos (f : ℕ → ℕ) :
    ¬ Sobre f ↔ ∃ c k, {n | f n ≤ c * (n + 1) ^ k}.Infinite := by
  rw [sobre_iff_buenos_finitos]
  push Not
  rfl

/-- **Oscilar, para un problema rellenable**: hay un polinomio con infinitos largos buenos, y para todo polinomio y
toda ventana polinomial hay infinitos huecos. Los largos buenos existen y están más ralos que cualquier polinomio. -/
theorem oscila_iff_buenos_ralos {L : Problema} (hL : Rellenable L) :
    Oscila (sucNat L) ↔
      (∃ c k, {n | sucNat L n ≤ c * (n + 1) ^ k}.Infinite) ∧
      (∀ c k a b, {n | Hueco L c k a b n}.Infinite) := by
  unfold Oscila
  rw [bajo_sucNat_iff, fuera_iff_huecos hL, no_sobre_iff_buenos]
  exact and_comm

/-- **La tricotomía de un problema rellenable**: P/poly, arriba, u oscilando con huecos más que polinomiales. -/
theorem tricotomia_rellenable {L : Problema} (hL : Rellenable L) :
    L ∈ PsobrePoly ∨ Sobre (sucNat L) ∨
      (Oscila (sucNat L) ∧ ∀ c k a b, {n | Hueco L c k a b n}.Infinite) := by
  rcases tricotomia (sucNat L) with h | h | h
  · exact Or.inl ((bajo_sucNat_iff L).1 h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h, ((oscila_iff_buenos_ralos hL).1 h).2⟩)

/-- Y las tres salidas se excluyen. -/
theorem tricotomia_rellenable_exclusiva (L : Problema) :
    ¬ (L ∈ PsobrePoly ∧ Sobre (sucNat L)) ∧ ¬ (L ∈ PsobrePoly ∧ Oscila (sucNat L)) ∧
      ¬ (Sobre (sucNat L) ∧ Oscila (sucNat L)) := by
  have := disjuntas (sucNat L)
  rw [bajo_sucNat_iff] at this
  exact this

/-- **Dónde puede estar SAT.** O `satBits` tiene circuitos polinomiales, o el costo de su versión enmarcada está arriba
del borde (para cada polinomio, finitos largos buenos), o oscila: infinitos largos buenos para algún polinomio, pero
separados por huecos más grandes que cualquier ventana polinomial. -/
theorem tricotomia_sat :
    CookS12.satBits ∈ PsobrePoly ∨ Sobre (sucNat satMarco) ∨
      (Oscila (sucNat satMarco) ∧ ∀ c k a b, {n | Hueco satMarco c k a b n}.Infinite) := by
  by_cases h : CookS12.satBits ∈ PsobrePoly
  · exact Or.inl h
  · right
    have hm : satMarco ∉ PsobrePoly := fun hm => h (satBits_de_satMarco hm)
    rcases tricotomia_rellenable rellenable_satMarco with h' | h' | h'
    · exact absurd h' hm
    · exact Or.inl h'
    · exact Or.inr h'

/-- SAT arriba, leído: para cada polinomio, solo finitos largos tienen un circuito de ese tamaño. -/
theorem sat_sobre_iff :
    Sobre (sucNat satMarco) ↔ ∀ c k, {n | sucNat satMarco n ≤ c * (n + 1) ^ k}.Finite :=
  sobre_iff_buenos_finitos _

/-- SAT oscilando, leído: hay largos buenos infinitos, pero más ralos que cualquier polinomio. -/
theorem sat_oscila_iff :
    Oscila (sucNat satMarco) ↔
      (∃ c k, {n | sucNat satMarco n ≤ c * (n + 1) ^ k}.Infinite) ∧
      (∀ c k a b, {n | Hueco satMarco c k a b n}.Infinite) :=
  oscila_iff_buenos_ralos rellenable_satMarco

/-- **La jugada de relleno contra SAT es «arriba u oscila».** Conecta con `PBombeo.lean`: la jugada que rompe el
bombeo de relleno es exactamente salir de la región de abajo. -/
theorem jugada_iff_arriba_u_oscila :
    JugadaRelleno satMarco ↔ Sobre (sucNat satMarco) ∨ Oscila (sucNat satMarco) := by
  rw [jugada_relleno_iff rellenable_satMarco, ← bajo_sucNat_iff]
  constructor
  · intro h
    by_cases hs : Sobre (sucNat satMarco)
    · exact Or.inl hs
    · exact Or.inr ⟨h, hs⟩
  · rintro (h | h)
    · exact sobre_no_bajo h
    · exact h.1

/-! ## Controles -/

/-- La rama «oscila con huecos» no es vacía de contenido: el problema `espaciado` de `Relleno.lean` es rellenable,
está fuera de P/poly y tiene infinitos largos buenos para el polinomio `n`; así que oscila (no está arriba), y por
`oscila_iff_buenos_ralos` tiene huecos para toda ventana. Es un problema real en la tercera rama. -/
example : Oscila (sucNat espaciado) ∧ ∀ c k a b, {n | Hueco espaciado c k a b n}.Infinite := by
  obtain ⟨-, hbuenos, hfuera⟩ := control_densidad
  have hosc : Oscila (sucNat espaciado) :=
    ⟨fun hb => hfuera ((bajo_sucNat_iff _).1 hb), (no_sobre_iff_buenos _).2 ⟨1, 1, hbuenos⟩⟩
  exact ⟨hosc, ((oscila_iff_buenos_ralos rellenable_espaciado).1 hosc).2⟩

/-- La rama «abajo» también está habitada por un problema rellenable: la constante `false`. -/
example : (fun _ : List Bool => false) ∈ PsobrePoly ∨ Sobre (sucNat fun _ => false) ∨
    (Oscila (sucNat fun _ => false) ∧ ∀ c k a b, {n | Hueco (fun _ => false) c k a b n}.Infinite) :=
  tricotomia_rellenable (L := fun _ => false) (fun _ _ _ => ⟨fun _ => .inr false, fun _ => rfl⟩)

/- Mutante probado (25 nov 2026, en /tmp/claude-noche/MutSat.lean): en `oscila_iff_buenos_ralos`, quitar la
primera conjunción (dejar solo los huecos) no compila: los huecos solos son `¬ Bajo`, y no excluyen estar arriba.
Arriba también tiene infinitos huecos; lo que distingue oscilar es que los largos buenos existan. -/

end Sagitta.Map.Borde.SatEnElBorde
