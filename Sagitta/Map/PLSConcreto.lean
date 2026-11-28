import Sagitta.Map.Vara

/-!
# Un problema de PLS concreto

Hasta aquí `ProblemaPLS` era una definición sin ningún ejemplo: construir uno pide probar que cuatro funciones son de
tiempo polinomial. Con el cierre y con las máquinas de `ExhaustivoTiempo.lean` y `Vara.lean` ya se puede.

**El problema.** Para un verificador polinomial `V` y una vara `tope`, el descenso exhaustivo con la cuarta función
que faltaba: una cadena es **factible** si no es más larga que la vara. Sale por composición, con la máquina que
compara largos.

**Lo probado.**

* `problemaExhaustivo` es un `ProblemaPLS`, y por lo tanto está en `TFNP` (`enTFNP`).
* `existe_problemaPLS`: la clase ya no está vacía en Lean.
* `np_por_pls`: para todo `L` de NP hay un problema de PLS cuyo **algoritmo estándar** decide `L`.
* `solucion_trivial`: ese mismo problema tiene una solución que se escribe sin buscar, la cadena de unos del largo
  de la vara. Es el mismo contraste, ahora sobre un problema de PLS de verdad: como problema de PLS es
  trivial; como problema del algoritmo estándar, decide NP.

**Atribución.** `np_por_pls` es el lema 1 de Johnson, Papadimitriou y Yannakakis (1988, pp. 83–84), y
`solucion_trivial` es la nota que le sigue en el artículo («en el problema anterior, 0 es siempre un óptimo local»).
Lo de aquí es su formalización, con las cuatro funciones probadas de tiempo polinomial.
-/

open Computability

namespace Sagitta.Map
namespace PLSConcreto

open Enumera
open ExhaustivoTiempo (exhaustivoVara esPolinomial_snd esPolinomial_menor esPolinomial_vacia
  exhaustivo_polinomial)

/-! ## 1. Factible -/

/-- Una cadena es factible si no es más larga que la vara de la instancia. -/
def factible (tope : List Bool → List Bool) (q : List Bool × List Bool) : Bool :=
  !decide ((tope q.1).length < q.2.length)

theorem factible_iff (tope : List Bool → List Bool) (x s : List Bool) :
    factible tope (x, s) = true ↔ s.length ≤ (tope x).length := by
  simp [factible]

/-- «Factible» es de tiempo polinomial: comparar largos y negar. -/
theorem factible_polinomial {tope : List Bool → List Bool} (htope : EsPolinomial tope) :
    EsPolinomial (factible tope) := by
  have hfst : EsPolinomial (Prod.fst : List Bool × List Bool → List Bool) := Basicas.esPolinomial_fst
  have hsnd : EsPolinomial (Prod.snd : List Bool × List Bool → List Bool) := esPolinomial_snd
  have h1 : EsPolinomial (fun q : List Bool × List Bool => tope q.1) :=
    Componer.esPolinomial_comp _ _ hfst htope
  have h2 := Primero.esPolinomial_pares _ _ h1 hsnd
  have h3 := Componer.esPolinomial_comp (fun q : List Bool × List Bool => (tope q.1, q.2))
    (fun q : List Bool × List Bool => decide (q.1.length < q.2.length)) h2 esPolinomial_menor
  exact Componer.esPolinomial_comp _ (fun b : Bool => !b) h3 Basicas.esPolinomial_no

/-! ## 2. El problema -/

/-- **El descenso exhaustivo, como problema de PLS.** -/
noncomputable def problemaExhaustivo (p : Polynomial ℕ) (V : List Bool × List Bool → Bool)
    (tope : List Bool → List Bool) (hV : EsPolinomial V) (htope : EsPolinomial tope)
    (hlargo : ∀ x, (tope x).length = p.eval x.length) : ProblemaPLS where
  cota := p
  factible := factible tope
  inicial := (exhaustivoVara V tope).inicial
  vecino := (exhaustivoVara V tope).vecino
  costo := (exhaustivoVara V tope).costo
  inicial_factible := fun x => by
    rw [factible_iff]
    exact Nat.zero_le _
  vecino_factible := fun x s h => by
    rw [factible_iff] at h ⊢
    show (if V (x, s) = true ∨ (tope x).length < (sig s).length then s else sig s).length ≤ _
    split_ifs with hc
    · exact h
    · push Not at hc
      exact hc.2
  corta := fun x s h => by
    rw [factible_iff] at h
    rw [← hlargo x]
    exact h
  factible_pol := factible_polinomial htope
  inicial_pol := (exhaustivo_polinomial V tope hV htope).1
  vecino_pol := (exhaustivo_polinomial V tope hV htope).2.1
  costo_pol := (exhaustivo_polinomial V tope hV htope).2.2

section Propiedades

variable {p : Polynomial ℕ} {V : List Bool × List Bool → Bool} {tope : List Bool → List Bool}
  (hV : EsPolinomial V) (htope : EsPolinomial tope) (hlargo : ∀ x, (tope x).length = p.eval x.length)

/-- Su descenso es el exhaustivo. -/
theorem aDescenso_eq :
    (problemaExhaustivo p V tope hV htope hlargo).aDescenso = exhaustivoVara V tope := rfl

/-- Está en TFNP, como todo problema de PLS. -/
theorem enTFNP : EnTFNP (problemaExhaustivo p V tope hV htope hlargo).EsSolucion :=
  (problemaExhaustivo p V tope hV htope hlargo).enTFNP

theorem sig_unos : ∀ n : ℕ, (sig (List.replicate n true)).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, sig, sig_unos n]

/-- **Como problema de PLS es trivial**: la cadena de unos del largo de la vara es siempre una solución. Se
escribe sin buscar, y no dice si hay certificado. -/
theorem solucion_trivial (x : List Bool) :
    (problemaExhaustivo p V tope hV htope hlargo).EsSolucion x (List.replicate (tope x).length true) := by
  refine ⟨?_, ?_⟩
  · show factible tope (x, _) = true
    rw [factible_iff, List.length_replicate]
  · show (exhaustivoVara V tope).EsOptimo x _
    rw [exhaustivo_esOptimo_iff]
    right
    rw [sig_unos]
    exact Nat.lt_succ_self _

end Propiedades

/-! ## 3. La clase no está vacía, y NP -/

/-- Un verificador que nunca acepta, polinomial: comparar los largos de dos cadenas vacías. -/
theorem esPolinomial_nunca : EsPolinomial (fun _ : List Bool × List Bool => false) := by
  have hv : EsPolinomial (fun _ : List Bool × List Bool => ([] : List Bool)) := esPolinomial_vacia
  have h := Componer.esPolinomial_comp (fun _ : List Bool × List Bool => (([] : List Bool), ([] : List Bool)))
    (fun q : List Bool × List Bool => decide (q.1.length < q.2.length))
    (Primero.esPolinomial_pares _ _ hv hv) esPolinomial_menor
  exact h

/-- **Existe un problema de PLS.** Hasta ahora la definición no tenía ningún ejemplo en Lean. -/
theorem existe_problemaPLS : Nonempty ProblemaPLS := by
  obtain ⟨tope, htope, hlargo⟩ := Vara.tieneVara (Polynomial.X)
  exact ⟨problemaExhaustivo Polynomial.X (fun _ => false) tope esPolinomial_nunca htope hlargo⟩

/-- **NP por el algoritmo estándar de un problema de PLS.** Para todo `L` de NP hay un problema de PLS y un
verificador polinomial tales que `x ∈ L` si y solo si el verificador acepta el destino de la ruta. Ese mismo
problema, visto como problema de PLS, tiene una solución trivial (`solucion_trivial`). -/
theorem np_por_pls {L : Problema} (hL : L ∈ NP) :
    ∃ (P : ProblemaPLS) (V : List Bool × List Bool → Bool),
      EsPolinomial V ∧ ∀ x, L x = true ↔ V (x, P.aDescenso.destino x) = true := by
  obtain ⟨p, V, hV, hiff⟩ := hL
  obtain ⟨tope, htope, hlargo⟩ := Vara.tieneVara p
  refine ⟨problemaExhaustivo p V tope hV htope hlargo, V, hV, ?_⟩
  exact (ExhaustivoTiempo.np_por_destino_polinomial hV htope hlargo hiff).2

end PLSConcreto
end Sagitta.Map
