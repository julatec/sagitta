import CslibFrontier.Computability.Complexity.ProofSystem.Exhaustive

/-!
# El límite blanco: la conservación en toda caja gris es `NP ≠ coNP`

`EscaleraGris.lean` subió peldaños grises (árbol, resolución, planos de corte, Gauss, Nullstellensatz, cálculo
polinomial) y en cada uno miró si la conservación (el costo de refutar no baja de un piso) se sabe o no. Aquí se pasa al
**límite** de la escalera: un sistema de pruebas cualquiera en el sentido de Cook y Reckhow (1979), una función calculable
en tiempo polinomial de las palabras **sobre** las fórmulas sin modelo. Ese sistema ve la fórmula, pero sus reglas son
un programa arbitrario: es la caja blanca de las respuestas «no».

Todo lo que hace falta ya está en cslib-frontier (`CslibFrontier/Computability/Complexity/ProofSystem.lean` y
`ProofSystem/Exhaustive.lean`, de S. Schlesinger; sus `.olean` se compilaron en esta copia el 25 nov 2026, sin compilar
cslib-frontier entero). Este archivo **solo traduce** al lenguaje de Sagitta:

* `NPigualCoNP`: la proposición de cslib, `∀ enc, NP enc = coNP enc`.
* `ConservaCR P`: el peldaño `P` conserva, o sea, **no** está polinomialmente acotado (`ProofSystem.PolynomiallyBounded`).
* `LeyEnTodaCajaGris`: todo peldaño conserva.
* `ley_iff_np_ne_conp`: `LeyEnTodaCajaGris ↔ ¬ NPigualCoNP`. Es `NP_eq_coNP_iff_exists_polynomiallyBounded` (Cook y
  Reckhow) con la negación por fuera.
* `conserva_baja`: si `Q` simula a `P` y `Q` conserva, `P` conserva (`PolynomiallyBounded.of_simulates`). La conservación
  baja por la escalera; nunca sube sola.
* `limite_explicito`: hay **un** sistema `M` cuya conservación es exactamente `NP ≠ coNP`
  (`exists_polynomiallyBounded_iff_NP_eq_coNP`, Goldreich, Teorema B.13). El `M` se elige por casos y no es explícito: si
  `NP = coNP` es uno acotado, y si no, el exhaustivo. No es un peldaño que se pueda nombrar.
* `ley_implica_P_ne_NP`: la ley en toda caja gris implicaría `P ≠ NP` (si `P = NP`, `NP` es cerrado bajo complemento).
  Es una implicación, no una prueba de nada: la ley es una proposición abierta.

## Lo que NO se prueba

* Ni `NP ≠ coNP` ni la ley: las dos quedan abiertas, como `SigmaIgualNP` en otros archivos.
* No hay cotas para Frege ni para Frege extendido. La escalera de `EscaleraGris.lean` se detiene en planos de corte y en
  cálculo polinomial; arriba, no se sabe nada.
* No se prueba que la caja blanca no se alcance desde ningún peldaño: eso sería que ningún sistema sea óptimo, y la
  existencia de un sistema óptimo (Krajíček y Pudlák, 1989) está abierta.
-/

namespace Sagitta.Map.Borde.LimiteBlanco

open Cslib.Complexity Cslib.Complexity.ProofSystem

/-- `NP = coNP` en la forma de cslib-frontier: para toda codificación. -/
def NPigualCoNP : Prop := ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC

/-- **El peldaño `P` conserva**: no hay polinomio que acote el tamaño de la refutación más corta de cada fórmula. -/
def ConservaCR (P : ProofSystem encCNF UNSAT) : Prop := ¬ P.PolynomiallyBounded

/-- **La ley de conservación en toda caja gris de reglas polinomiales.** -/
def LeyEnTodaCajaGris : Prop := ∀ P : ProofSystem encCNF UNSAT, ConservaCR P

/-- **Cook–Reckhow, en el lenguaje de la escalera**: la conservación vale en toda caja gris exactamente cuando
`NP ≠ coNP`. -/
theorem ley_iff_np_ne_conp : LeyEnTodaCajaGris ↔ ¬ NPigualCoNP := by
  unfold LeyEnTodaCajaGris ConservaCR NPigualCoNP
  rw [NP_eq_coNP_iff_exists_polynomiallyBounded, not_exists]

/-- **La conservación baja por la simulación**: si `Q` simula a `P` y `Q` conserva, `P` también. -/
theorem conserva_baja {P Q : ProofSystem encCNF UNSAT} (hQP : Q.Simulates P) (hQ : ConservaCR Q) : ConservaCR P :=
  fun hP => hQ (hP.of_simulates hQP)

/-- **La p-simulación también baja la conservación.** -/
theorem conserva_baja_p {P Q : ProofSystem encCNF UNSAT} (hQP : Q.PSimulates P) (hQ : ConservaCR Q) : ConservaCR P :=
  conserva_baja hQP.simulates hQ

/-- **El límite, como un solo sistema**: hay un `M` (no explícito) que conserva exactamente cuando `NP ≠ coNP`. -/
theorem limite_explicito : ∃ M : ProofSystem encCNF UNSAT, (ConservaCR M ↔ ¬ NPigualCoNP) := by
  obtain ⟨M, hM⟩ := exists_polynomiallyBounded_iff_NP_eq_coNP
  exact ⟨M, not_congr hM⟩

/-- Si la ley falla, falla en un peldaño concreto: hay un sistema acotado, y entonces `NP = coNP`. -/
theorem falla_en_un_peldano (h : ¬ LeyEnTodaCajaGris) : ∃ P : ProofSystem encCNF UNSAT, P.PolynomiallyBounded := by
  unfold LeyEnTodaCajaGris ConservaCR at h
  push Not at h
  exact h

/-- `P = NP` implica `NP = coNP`: un problema de `coNP` tiene complemento en `NP = P`, que es cerrado bajo complemento. -/
theorem np_eq_conp_de_p_eq_np (h : ∀ {γ : Type} (encC : γ ↪ List Bool), P encC = NP encC) : NPigualCoNP := by
  intro γ encC
  ext A
  rw [mem_coNP, ← h encC]
  refine ⟨compl_mem_P, fun hA => ?_⟩
  simpa using compl_mem_P hA

/-- **La ley en toda caja gris implicaría `P ≠ NP`.** Implicación, no prueba: la ley está abierta. -/
theorem ley_implica_P_ne_NP (h : LeyEnTodaCajaGris) : ¬ ∀ {γ : Type} (encC : γ ↪ List Bool), P encC = NP encC :=
  fun hP => ley_iff_np_ne_conp.1 h (np_eq_conp_de_p_eq_np hP)

/-! ## Controles -/

/-- Control: con el `M` de `limite_explicito`, la ley en toda caja gris equivale a que **ese** peldaño conserve. -/
example : ∃ M : ProofSystem encCNF UNSAT, (LeyEnTodaCajaGris ↔ ConservaCR M) := by
  obtain ⟨M, hM⟩ := limite_explicito
  exact ⟨M, ley_iff_np_ne_conp.trans hM.symm⟩

/-- Control: hay sistemas de pruebas para `UNSAT` (el conjunto no es vacío), así que la ley no es vacía por falta de
peldaños. -/
example : Nonempty (ProofSystem encCNF UNSAT) :=
  nonempty_of_mem_coNP cnfDecoder CookLevin.UNSAT_coNPComplete.1 ⟨[[]], fun ⟨_, h⟩ => by simp at h⟩

/- Mutantes (probados en /tmp/claude-noche/MutLim*.lean, 25 nov 2026; fallan, como debe ser):
   * MutLim1: `conserva_baja` al revés (de `ConservaCR P` y `Q.Simulates P` concluir `ConservaCR Q`): no cierra.
   * MutLim2: `ley_iff_np_ne_conp` sin la negación (`LeyEnTodaCajaGris ↔ NPigualCoNP`): el `rw` deja una meta falsa. -/

end Sagitta.Map.Borde.LimiteBlanco
