import Sagitta.Map.Clases
import Mathlib.Order.WellFounded

/-!
# Buena fundación y descenso finito

El nombre que acordamos para «no hay cadenas descendentes infinitas», y su versión finita: la búsqueda
local (la clase PLS). Lo que es teorema está probado; lo abierto va como proposición.
-/

namespace Sagitta.Map

/-- No hay descenso infinito: ninguna sucesión `a₀, a₁, a₂, …` baja para siempre. -/
def SinDescensoInfinito {α : Type} (r : α → α → Prop) : Prop :=
  ¬ ∃ a : ℕ → α, ∀ n, r (a (n + 1)) (a n)

/-- **Buena fundación = sin descenso infinito.** La vuelta usa elección (dependiente): compárese con
`#print axioms` al final del archivo. -/
theorem bienFundado_iff_sinDescensoInfinito {α : Type} (r : α → α → Prop) :
    WellFounded r ↔ SinDescensoInfinito r := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  · rintro ⟨h⟩ ⟨a, ha⟩
    exact h ⟨a, ha⟩
  · intro h
    exact ⟨fun ⟨a, ha⟩ => h ⟨a, ha⟩⟩

/-- La buena fundación de ℕ: la que tiene la aritmética de Peano. -/
theorem sinDescensoInfinito_nat : SinDescensoInfinito (· < · : ℕ → ℕ → Prop) :=
  (bienFundado_iff_sinDescensoInfinito _).mp wellFounded_lt

/-! ## Descenso finito pero largo: búsqueda local -/

/-- Un descenso sobre cadenas de bits: un costo y un vecino que conserva la longitud. Es la parte combinatoria de
una búsqueda local, sin exigir nada del tiempo de cálculo; lo que se prueba aquí vale para todo descenso. -/
structure Descenso where
  /-- El costo de una cadena. -/
  costo : List Bool → ℕ
  /-- El vecino propuesto para una cadena. -/
  vecino : List Bool → List Bool
  conserva : ∀ x, (vecino x).length = x.length

/-- Un problema de búsqueda local (PLS): un descenso cuyo costo y vecino se calculan en tiempo polinomial. -/
structure BusquedaLocal extends Descenso where
  costo_pol : EsPolinomial costo
  vecino_pol : EsPolinomial vecino

/-- `x` es un óptimo local: su vecino no cuesta menos. -/
def Descenso.EsOptimo (B : Descenso) (x : List Bool) : Prop :=
  B.costo x ≤ B.costo (B.vecino x)

/-- **Siempre hay un óptimo local de cada longitud**, por la buena fundación de ℕ. La prueba no da un
algoritmo rápido: toma el mínimo del costo entre las `2ⁿ` cadenas de longitud `n`. -/
theorem Descenso.existe_optimo (B : Descenso) (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ B.EsOptimo x := by
  have hne : (B.costo '' {x | x.length = n}).Nonempty :=
    ⟨_, List.replicate n false, by simp, rfl⟩
  obtain ⟨m, ⟨x, hx, rfl⟩, hmin⟩ := wellFounded_lt.has_min _ hne
  refine ⟨x, hx, not_lt.mp (hmin _ ⟨B.vecino x, ?_, rfl⟩)⟩
  change (B.vecino x).length = n
  rw [B.conserva]
  exact hx

/-- **El descenso termina, y se sabe cuándo.** Seguir al vecino desde `x` llega a un óptimo local en a lo sumo
`costo x` pasos: cada paso que no se detiene baja el costo, y en `ℕ` eso se acaba. El costo de una cadena de
longitud `n` puede valer hasta `2^(nᵏ)`, así que la cota es finita pero puede ser exponencial. -/
theorem Descenso.desciende (B : Descenso) :
    ∀ (c : ℕ) (x : List Bool), B.costo x ≤ c →
      ∃ k ≤ B.costo x, B.EsOptimo (B.vecino^[k] x) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro x hx
    by_cases h : B.EsOptimo x
    · exact ⟨0, Nat.zero_le _, h⟩
    · have hlt : B.costo (B.vecino x) < B.costo x := by
        simp only [Descenso.EsOptimo, not_le] at h
        exact h
      obtain ⟨k, hk, hopt⟩ := ih (B.costo (B.vecino x)) (by omega) (B.vecino x) le_rfl
      refine ⟨k + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      exact hopt

/-- La forma que se cita: desde cualquier `x`, a lo sumo `costo x` pasos. -/
theorem Descenso.desciende_desde (B : Descenso) (x : List Bool) :
    ∃ k ≤ B.costo x, B.EsOptimo (B.vecino^[k] x) :=
  B.desciende _ x le_rfl

/-- **Abierto (PLS ⊆ FP).** ¿Se llega siempre al fondo sin recorrer todo el descenso? Hay una función
polinomial que, dada una cadena, devuelve un óptimo local de su misma longitud. -/
def BusquedaLocalEsPolinomial : Prop :=
  ∀ B : BusquedaLocal, ∃ f : List Bool → List Bool,
    EsPolinomial f ∧ ∀ x, (f x).length = x.length ∧ B.EsOptimo (f x)

end Sagitta.Map
