/-
Las definiciones de `P`, `NP` y `coNP` están adaptadas de
`FormalConjecturesForMathlib/Computability/Complexity.lean` y `FormalConjectures/Millennium/PvsNP.lean`
(google-deepmind/formal-conjectures, commit 2207c54). Copyright 2025-2026 The Formal Conjectures Authors.
Licencia Apache 2.0 (ver `NOTICE.md`). Cambios: nombres en español, y los enunciados abiertos van como
proposiciones (`def … : Prop`), no como teoremas con `sorry`.
-/
import Sagitta.Map.Codificacion
import Mathlib.Computability.TuringMachine.Computable

/-!
# P, NP y el enunciado de P = NP

Sobre las máquinas de Turing de Mathlib (`Turing.TM2ComputableInPolyTime`). NP va por verificadores
(Arora–Barak, def. 2.1).
-/

open Computability Turing

namespace Sagitta.Map

/-- Un problema de decisión: una función de cadenas de bits en sí o no. -/
abbrev Problema := List Bool → Bool

/-- Una clase de complejidad: un conjunto de problemas. -/
abbrev Clase := Set Problema

/-- `f` se calcula en tiempo polinomial con las codificaciones dadas. -/
def EsPolinomialCon {α β Γα Γβ : Type} (ea : Encoding α Γα) (eb : Encoding β Γβ) (f : α → β) : Prop :=
  Nonempty (TM2ComputableInPolyTime ea.encode eb.encode f)

/-- `f` se calcula en tiempo polinomial con las codificaciones canónicas en bits. -/
def EsPolinomial {α β : Type} [CodBits α] [CodBits β] (f : α → β) : Prop :=
  EsPolinomialCon (CodBits.toEncoding (α := α)) (CodBits.toEncoding (α := β)) f

/-- La identidad se calcula en tiempo polinomial. -/
theorem esPolinomial_id {α : Type} [CodBits α] : EsPolinomial (id : α → α) :=
  ⟨Turing.idComputableInPolyTime CodBits.cod⟩

/-- **P**: los problemas que una máquina determinista decide en tiempo polinomial. -/
def P : Clase := {L | EsPolinomial L}

/-- **NP**: los problemas con verificador polinomial y certificados de longitud polinomial. -/
def NP : Clase :=
  {L | ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
      EsPolinomial V ∧
      ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true}

/-- **coNP**: los problemas cuyo complemento está en NP. -/
def coNP : Clase := {L | (fun x => !L x) ∈ NP}

/-! ## Los enunciados abiertos, como proposiciones -/

/-- **P = NP.** -/
def PIgualNP : Prop := P = NP

/-- **P ≠ NP.** -/
def PDistintoNP : Prop := P ≠ NP

/-- **NP ≠ coNP.** -/
def NPDistintoCoNP : Prop := NP ≠ coNP

/-- P ⊆ NP. Es un teorema conocido (el verificador ignora el certificado); aquí queda como hipótesis
explícita porque su prueba exige construir la máquina. Hay una prueba formal externa citada en
formal-conjectures. -/
def PSubNP : Prop := P ⊆ NP

/-- La forma en que lo dijo José: todo lo que tiene verificador polinomial tiene resolvedor polinomial. -/
def VerificarImplicaResolver : Prop := ∀ L : Problema, L ∈ NP → L ∈ P

/-- Las dos formas dicen lo mismo, dado P ⊆ NP. -/
theorem pIgualNP_iff_verificarImplicaResolver (h : PSubNP) : PIgualNP ↔ VerificarImplicaResolver := by
  constructor
  · intro e L hL
    rw [show P = NP from e]
    exact hL
  · intro v
    exact Set.Subset.antisymm h v

end Sagitta.Map
