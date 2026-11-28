import Sagitta.Map.LevinMaquinas
import Sagitta.Map.Relleno

/-!
# El P-bombeo: la primera mitad

La pregunta de José (24 nov 2026): ¿qué forma tendría un «lema de bombeo para P»? Un lema de bombeo tiene dos mitades:
**el lema** (lo que toda máquina del modelo cumple) y **la jugada** (la palabra explícita que lo rompe, como `aᵖbᵖ`
para los autómatas). Este archivo arma la primera mitad para P, en dos formas que ya estaban probadas en Sagitta, y
deja enunciada, como definición, la jugada que haría falta contra SAT. Es un empaque: no prueba nada nuevo sobre
P contra NP, y lo dice.

## Lo que se prueba

**El bombeo de profundidad** (sobre `Sagitta/Map/LevinMaquinas.lean`, en las máquinas de cslib-frontier):
* `bombeo_profundidad`: si la búsqueda de `A` está en P, toda instancia de `A` tiene un testigo de `kt`
  logarítmica (`KtMTLog`): un programa corto lo encuentra rápido. Es `enP_implica_kt`.
* `JugadaProfundidad enc V A`: para toda constante `c` hay una instancia de `A` cuya `kt` supera `c·log`. Es la
  jugada: una instancia profunda para cada nivel.
* `jugada_iff_no_bombea`: la jugada es exactamente la negación del bombeo.
* `jugada_rompe`: si la jugada existe, la búsqueda no está en P. `sat_jugada_rompe` lo dice para SAT.

**El bombeo de relleno** (sobre `Sagitta/Map/Relleno.lean`, en circuitos; de otra sesión, solo se importa):
* `bombeo_relleno`: si un problema rellenable está en P/poly, sus largos buenos son densos (`Denso`). Rellenar es
  bombear: se agrega material a la entrada sin cambiar la respuesta.
* `JugadaRelleno L`: para todo polinomio y toda ventana, los largos buenos de `L` no son densos.
* `jugada_relleno_iff`: en un problema rellenable, la jugada es exactamente estar fuera de P/poly.
* `sat_jugada_relleno_de_fuera`: si SAT (`satBits`) está fuera de P/poly, la jugada vale para la versión enmarcada
  `satMarco`. `sat_jugada_relleno_rompe`: con la jugada, `satMarco` está fuera de P/poly.

## Lo que NO se prueba, y por qué es el punto

* En las dos formas, **la jugada contra SAT es equivalente al problema mismo** (`jugada_iff_no_bombea`,
  `jugada_relleno_iff`): el lema es fácil y la jugada es todo. Por eso no se intenta construirla.
* Las barreras ponen tres condiciones a una jugada que sirva: hablar de SAT en particular y no de las funciones difíciles en general (pruebas naturales),
  mirar dentro de la computación (relativización) y mirar los polinomios por dentro (algebrización). Nada de eso
  está aquí.
* La forma «de restricción» (estilo Håstad) no tiene versión para P: P calcula paridad, que no se simplifica al fijar
  variables.
-/

namespace Sagitta.Map.Borde.PBombeo

open Sagitta.Map Sagitta.Map.Tiempo.LevinMaquinas Sagitta.Map.Tiempo.Relleno
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.Complexity

/-! ## 1. El bombeo de profundidad -/

section Profundidad

variable {α : Type} (enc : α ↪ List Bool) (V : α × List Bool → Bool)

/-- **La jugada de profundidad**: para toda constante `c` hay una instancia de `A` que, si tiene testigo, no tiene
ninguno de `kt` a lo sumo `c·log`. Es el `aᵖbᵖ` que le falta a SAT: una instancia profunda para cada nivel. -/
def JugadaProfundidad (A : Set α) : Prop :=
  ∀ c, ∃ a ∈ A, ResolubleMT enc V a → c * Nat.log 2 ((enc a).length + 2) < ktMT enc V a

variable {enc V}

/-- **El lema** (primera mitad del P-bombeo): si la búsqueda está en P, toda instancia tiene un testigo superficial. -/
theorem bombeo_profundidad {A : Set α} (h : BusquedaEnP enc V A) : KtMTLog enc V A :=
  enP_implica_kt h

/-- La jugada es exactamente la negación del bombeo: no hay nada más débil que alcance. -/
theorem jugada_iff_no_bombea {A : Set α} : JugadaProfundidad enc V A ↔ ¬ KtMTLog enc V A := by
  unfold JugadaProfundidad KtMTLog
  push Not
  rfl

/-- **La jugada rompe**: con una instancia profunda para cada nivel, la búsqueda no está en P. -/
theorem jugada_rompe {A : Set α} (j : JugadaProfundidad enc V A) : ¬ BusquedaEnP enc V A :=
  fun h => (jugada_iff_no_bombea.1 j) (bombeo_profundidad h)

end Profundidad

/-- **Para SAT**: si alguien exhibe, para cada `c`, una fórmula satisfacible sin testigos de `kt ≤ c·log`, la
búsqueda de SAT no está en P. -/
theorem sat_jugada_rompe (j : JugadaProfundidad encCNF SAT.verifier SAT) :
    ¬ BusquedaEnP encCNF SAT.verifier SAT :=
  jugada_rompe j

/-! ## 2. El bombeo de relleno -/

/-- **La jugada de relleno**: para todo polinomio de calidad y toda ventana, los largos buenos de `L` no son densos. -/
def JugadaRelleno (L : Problema) : Prop := ∀ c k a b, ¬ Denso L c k a b

/-- **El lema**: un problema rellenable en P/poly tiene largos buenos densos. -/
theorem bombeo_relleno {L : Problema} (hL : Rellenable L) (h : L ∈ PsobrePoly) :
    ∃ c k a b, Denso L c k a b :=
  (psobrePoly_iff_denso hL).1 h

/-- En un problema rellenable, la jugada es exactamente estar fuera de P/poly. -/
theorem jugada_relleno_iff {L : Problema} (hL : Rellenable L) : JugadaRelleno L ↔ L ∉ PsobrePoly := by
  rw [psobrePoly_iff_denso hL]
  unfold JugadaRelleno
  push Not
  rfl

/-- Si SAT está fuera de P/poly, la jugada de relleno vale para su versión enmarcada. -/
theorem sat_jugada_relleno_de_fuera (h : CookS12.satBits ∉ PsobrePoly) : JugadaRelleno satMarco :=
  (jugada_relleno_iff rellenable_satMarco).2 (fun hm => h (satBits_de_satMarco hm))

/-- Con la jugada de relleno, la versión enmarcada de SAT está fuera de P/poly. -/
theorem sat_jugada_relleno_rompe (j : JugadaRelleno satMarco) : satMarco ∉ PsobrePoly :=
  (jugada_relleno_iff rellenable_satMarco).1 j

/-! ## Controles -/

/-- La jugada de relleno no es trivialmente verdadera: un problema constante (rellenable, con circuitos de tamaño
fijo) no la cumple, porque está en P/poly. -/
example {L : Problema} (hL : Rellenable L) (h : L ∈ PsobrePoly) : ¬ JugadaRelleno L :=
  fun j => (jugada_relleno_iff hL).1 j h

/-- La jugada de profundidad tampoco es vacía: para el conjunto vacío de instancias no vale (no hay instancia que
exhibir), así que el enunciado sí exige algo. -/
example {α : Type} (enc : α ↪ List Bool) (V : α × List Bool → Bool) :
    ¬ JugadaProfundidad enc V (∅ : Set α) := by
  intro j
  obtain ⟨a, ha, -⟩ := j 0
  exact ha

/- Mutante probado (24 nov 2026, fuera del repositorio): en `JugadaProfundidad`, cambiar `<` por `≤`
(`c * Nat.log 2 (...) ≤ ktMT enc V a`) hace fallar `jugada_iff_no_bombea`: la negación de `kt ≤ c·log` es
`c·log < kt`, no `c·log ≤ kt`. -/

end Sagitta.Map.Borde.PBombeo
