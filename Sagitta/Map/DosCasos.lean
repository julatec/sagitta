import Sagitta.Map.KtSAT
import Sagitta.Map.LevinMaquinas
import Sagitta.Map.DosCuentas

/-!
# Los dos casos: solución fija o profundidad que crece

José (24 nov 2026): **«creo que SAT cae en el segundo caso»**. Los dos casos vienen de `KtPruebaFija`: en el primero,
una misma solución sirve para toda una familia de instancias, y la `kt` es una constante más lo que cuesta leer la
entrada; en el segundo, lo que hay que encontrar crece con la instancia, y el precio por instancia crece.

## Tres medidas, tres respuestas para SAT

| Medida | SAT |
|---|---|
| ¿La solución cambia con la instancia? | sí: SAT no tiene una solución fija para todas las fórmulas |
| ¿La información está en la entrada? | sí: la fórmula determina su solución (por fuerza bruta) |
| ¿Cuesta extraerla, crece la `kt`? | **abierto**: es `P` contra `NP` |

## Lo que se prueba

1. **SAT contiene familias del primer caso** (`negativas_caso_fijo`, `negativas_kt_piso`): las fórmulas donde toda
   cláusula tiene un literal negativo comparten la solución todo falso, y su `kt` está en el piso.
2. **En caja negra, la familia de solución escondida es del segundo caso** (`caja_negra_caso_dos`): con un programa
   fijo, todo el precio se paga en cada instancia (alias de `DosCuentas.por_instancia_paga_todo`).
3. **«SAT tiene una familia del segundo caso en profundidad» equivale a que la `kt` de máquinas de SAT no sea
   logarítmica** (`caso_dos_iff_no_kt_log`), y por `sat_busqueda_iff_kt` (sobre las máquinas de cslib-frontier), a que la
   búsqueda universal de SAT no sea polinomial (`caso_dos_iff_universal_no_pol`).
4. **Si hay una familia del segundo caso, la búsqueda de SAT no está en `P`** (`caso_dos_implica_no_enP`), sin
   condiciones. La vuelta pide construir la búsqueda como máquina de cslib, como en `kt_implica_enP_condicional`
   (`no_enP_implica_caso_dos`, con esa hipótesis explícita).

## La apuesta de José, escrita

`∃ A ⊆ SAT, ¬ KtMTLog A`: hay una familia de fórmulas satisfacibles cuya solución, aunque esté escrita en la fórmula,
cuesta cada vez más extraer. Es la apuesta de casi todos. Este archivo la deja como un enunciado exacto, equivalente a la
negación de «la búsqueda universal de SAT es polinomial»; no la prueba.

## Lo que NO se prueba

* Que exista una familia del segundo caso en profundidad: eso es `P ≠ NP` (para la búsqueda).
* Que las fórmulas plantadas con una función de un solo sentido caigan en el segundo caso (sería condicional a la
  función).
* Nada sobre `P` contra `NP`.
-/

namespace Sagitta.Map.Tiempo.DosCasos

open Sagitta.Map.Tiempo Sagitta.Map.Tiempo.KtSAT Sagitta.Map.Tiempo.LevinMaquinas
open Cslib Cslib.Logic.PL Cslib.Complexity

/-! ## 1. El primer caso dentro de SAT -/

/-- **Una familia con solución fija**: una misma asignación satisface a todas. -/
def SolucionFija {ι : Type} (F : ι → List Clausula) : Prop :=
  ∃ σ : ℕ → Bool, ∀ j, CNF.eval σ (F j : CNF ℕ) = true

/-- **Las fórmulas con un literal negativo en cada cláusula comparten la solución todo falso.** -/
theorem negativas_caso_fijo {ι : Type} {F : ι → List Clausula} (h : ∀ j, TodaNegativa (F j)) :
    SolucionFija F :=
  ⟨TerceraCuenta.asigDeLista [], fun j => eval_todo_falso (h j)⟩

/-- **Y su `kt` está en el piso**: a lo sumo lo que cuesta leer la fórmula. -/
theorem negativas_kt_piso {F : List Clausula} (h : TodaNegativa F) :
    ktSAT F ≤ Nat.clog 2 (Encodable.encode F + 1) :=
  (negativa_facil h).2.2.1

/-! ## 2. El segundo caso, en caja negra -/

/-- **En caja negra, la solución escondida es del segundo caso**: con un programa fijo, todo el precio se paga por
instancia, `m ≤ s + ⌈log₂(t+1)⌉`. -/
alias caja_negra_caso_dos := DosCuentas.por_instancia_paga_todo

/-! ## 3. El segundo caso en profundidad, para SAT -/

/-- **La `kt` logarítmica se hereda a las subfamilias.** -/
theorem ktLog_mono {α : Type} {enc : α ↪ List Bool} {V : α × List Bool → Bool} {A B : Set α} (hBA : B ⊆ A)
    (h : KtMTLog enc V A) : KtMTLog enc V B := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun a ha => hc a (hBA ha)⟩

/-- **Una familia de fórmulas satisfacibles del segundo caso en profundidad**: su `kt` de máquinas no es
logarítmica. -/
def CasoDos (A : Set (CNF ℕ)) : Prop := A ⊆ SAT ∧ ¬ KtMTLog encCNF SAT.verifier A

/-- **Hay una familia del segundo caso si y solo si la `kt` de SAT no es logarítmica.** -/
theorem caso_dos_iff_no_kt_log : (∃ A, CasoDos A) ↔ ¬ KtMTLog encCNF SAT.verifier SAT := by
  constructor
  · rintro ⟨A, hA, hn⟩ h
    exact hn (ktLog_mono hA h)
  · intro h
    exact ⟨SAT, le_rfl, h⟩

/-- **Y si y solo si la búsqueda universal de SAT no es polinomial** (sobre las máquinas de cslib-frontier, con un
verificador cobrado polinomialmente). -/
theorem caso_dos_iff_universal_no_pol {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV) :
    (∃ A, CasoDos A) ↔ ¬ BusquedaUniversalPol encCNF SAT.verifier tV SAT := by
  rw [caso_dos_iff_no_kt_log, sat_busqueda_iff_kt htV htVm]

/-- **Si hay una familia del segundo caso, la búsqueda de SAT no está en `P`** (cslib). Sin condiciones. -/
theorem caso_dos_implica_no_enP (h : ∃ A, CasoDos A) : ¬ BusquedaEnP encCNF SAT.verifier SAT :=
  fun hP => (caso_dos_iff_no_kt_log.1 h) (sat_enP_implica_kt hP)

/-- **La vuelta, condicional**: si la búsqueda de SAT no está en `P`, hay una familia del segundo caso, suponiendo
que la búsqueda universal polinomial dé una máquina de `P` (construir la búsqueda como máquina de cslib). -/
theorem no_enP_implica_caso_dos {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV)
    (hImpl : BusquedaUniversalPol encCNF SAT.verifier tV SAT → BusquedaEnP encCNF SAT.verifier SAT)
    (h : ¬ BusquedaEnP encCNF SAT.verifier SAT) : ∃ A, CasoDos A :=
  caso_dos_iff_no_kt_log.2 fun hk => h (kt_implica_enP_condicional htV htVm hImpl hk)

/-! ## Controles -/

/-- **Control: el vacío no es del segundo caso**: una familia vacía tiene `kt` logarítmica trivialmente. -/
theorem vacia_no_caso_dos : ¬ CasoDos ∅ := fun ⟨_, h⟩ => h ⟨0, fun _ ha => ha.elim⟩

end Sagitta.Map.Tiempo.DosCasos
