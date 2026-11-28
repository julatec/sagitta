import Sagitta.Map.Acotada
import Mathlib.ModelTheory.Satisfiability

/-!
# S¹₂ como teoría de Mathlib: la reserva de `Demuestra`

`Acotada.lean` define «S¹₂ demuestra σ» por modelos: σ vale en todo modelo de S¹₂ (`Demuestra`). Buss lo dice por
pruebas. Las dos cosas coinciden por el teorema de completitud de Gödel, que Mathlib no trae (tampoco un cálculo de
pruebas). Este archivo acerca las dos lecturas todo lo que Mathlib permite hoy:

1. Los 32 axiomas BASIC y el esquema PIND se escriben como **sentencias** de Mathlib (`teoriaBASIC`, `pindAx`), y S¹₂
   es una **teoría** de Mathlib, un conjunto de sentencias (`S12`).
2. Ser modelo de S¹₂ en el sentido de `Acotada.lean` es lo mismo que ser modelo de esa teoría (`modelo_S12_iff`).
3. `Demuestra σ` es la consecuencia semántica de Mathlib, `S12 ⊨ᵇ σ` (`demuestra_iff_models`). Mathlib la define
   sobre modelos no vacíos; un modelo de S¹₂ nunca es vacío porque tiene el `0`.
4. **Compacidad** (`demuestra_iff_finito`): lo que S¹₂ demuestra se sigue de un número finito de sus axiomas, como pasa
   con una prueba, que solo usa los que cita.

Lo que sigue faltando es exactamente la completitud: que de «vale en todo modelo» se pueda sacar una derivación.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-! ## Términos y fórmulas del lenguaje de S¹₂ -/

section Sintaxis

variable {β : Type} {α : Type} {n : ℕ}

/-- `0`. -/
def tC : L.Term β := Term.func (Fun.cero : L.Functions 0) ![]
/-- `S t`. -/
def tSc (t : L.Term β) : L.Term β := Functions.apply₁ (Fun.suc : L.Functions 1) t
/-- `|t|`. -/
def tLg (t : L.Term β) : L.Term β := Functions.apply₁ (Fun.long : L.Functions 1) t
/-- `⌊t/2⌋`. -/
def tMt (t : L.Term β) : L.Term β := Functions.apply₁ (Fun.mitad : L.Functions 1) t
/-- `t + u`. -/
def tMs (t u : L.Term β) : L.Term β := Functions.apply₂ (Fun.suma : L.Functions 2) t u
/-- `t · u`. -/
def tPr (t u : L.Term β) : L.Term β := Functions.apply₂ (Fun.prod : L.Functions 2) t u
/-- `t # u`. -/
def tSm (t u : L.Term β) : L.Term β := Functions.apply₂ (Fun.smash : L.Functions 2) t u
/-- `1 = S 0`. -/
def tU : L.Term β := tSc tC
/-- `2 · t`. -/
def tD (t : L.Term β) : L.Term β := tPr (tSc (tSc tC)) t
/-- `t ≤ u`. -/
def fLe (t u : L.Term (α ⊕ Fin n)) : L.BoundedFormula α n :=
  Relations.boundedFormula₂ (Rel.le : L.Relations 2) t u

end Sintaxis

section Realizacion

variable {M : Type} [L.Structure M]

@[simp] theorem realize_tC {γ : Type} (v : γ → M) : (tC : L.Term γ).realize v = cero := by
  simp only [tC, Term.realize, cero]
  congr 1; funext i; exact i.elim0

end Realizacion

/-! ## Los 32 axiomas BASIC, como sentencias -/

/-- BASIC 1. -/
def axB1 : L.Sentence := ∀' ∀' (fLe (&1) (&0) ⟹ fLe (&1) (tSc (&0)))

/-- BASIC 2. -/
def axB2 : L.Sentence := ∀' ∼((&0) =' tSc (&0))

/-- BASIC 3. -/
def axB3 : L.Sentence := ∀' fLe tC (&0)

/-- BASIC 4. -/
def axB4 : L.Sentence := ∀' ∀' ((fLe (&0) (&1) ⊓ ∼((&0) =' (&1))) ⇔ fLe (tSc (&0)) (&1))

/-- BASIC 5. -/
def axB5 : L.Sentence := ∀' (∼((&0) =' tC) ⟹ ∼(tD (&0) =' tC))

/-- BASIC 6. -/
def axB6 : L.Sentence := ∀' ∀' (fLe (&1) (&0) ⊔ fLe (&0) (&1))

/-- BASIC 7. -/
def axB7 : L.Sentence := ∀' ∀' (fLe (&0) (&1) ⟹ fLe (&1) (&0) ⟹ (&0) =' (&1))

/-- BASIC 8. -/
def axB8 : L.Sentence := ∀' ∀' ∀' (fLe (&0) (&1) ⟹ fLe (&1) (&2) ⟹ fLe (&0) (&2))

/-- BASIC 9. -/
def axB9 : L.Sentence := tLg tC =' tC

/-- BASIC 10. -/
def axB10 : L.Sentence := ∀' (∼((&0) =' tC) ⟹ (tLg (tD (&0)) =' tSc (tLg (&0)) ⊓ tLg (tSc (tD (&0))) =' tSc (tLg (&0))))

/-- BASIC 11. -/
def axB11 : L.Sentence := tLg tU =' tU

/-- BASIC 12. -/
def axB12 : L.Sentence := ∀' ∀' (fLe (&0) (&1) ⟹ fLe (tLg (&0)) (tLg (&1)))

/-- BASIC 13. -/
def axB13 : L.Sentence := ∀' ∀' (tLg (tSm (&0) (&1)) =' tSc (tPr (tLg (&0)) (tLg (&1))))

/-- BASIC 14. -/
def axB14 : L.Sentence := ∀' (tSm tC (&0) =' tU)

/-- BASIC 15. -/
def axB15 : L.Sentence := ∀' (∼((&0) =' tC) ⟹ (tSm tU (tD (&0)) =' tD (tSm tU (&0)) ⊓ tSm tU (tSc (tD (&0))) =' tD (tSm tU (&0))))

/-- BASIC 16. -/
def axB16 : L.Sentence := ∀' ∀' (tSm (&0) (&1) =' tSm (&1) (&0))

/-- BASIC 17. -/
def axB17 : L.Sentence := ∀' ∀' ∀' (tLg (&0) =' tLg (&1) ⟹ tSm (&0) (&2) =' tSm (&1) (&2))

/-- BASIC 18. -/
def axB18 : L.Sentence := ∀' ∀' ∀' ∀' (tLg (&0) =' tMs (tLg (&2)) (tLg (&3)) ⟹ tSm (&0) (&1) =' tPr (tSm (&2) (&1)) (tSm (&3) (&1)))

/-- BASIC 19. -/
def axB19 : L.Sentence := ∀' ∀' fLe (&0) (tMs (&0) (&1))

/-- BASIC 20. -/
def axB20 : L.Sentence := ∀' ∀' (fLe (&0) (&1) ⟹ ∼((&0) =' (&1)) ⟹ (fLe (tSc (tD (&0))) (tD (&1)) ⊓ ∼(tSc (tD (&0)) =' tD (&1))))

/-- BASIC 21. -/
def axB21 : L.Sentence := ∀' ∀' (tMs (&0) (&1) =' tMs (&1) (&0))

/-- BASIC 22. -/
def axB22 : L.Sentence := ∀' (tMs (&0) tC =' (&0))

/-- BASIC 23. -/
def axB23 : L.Sentence := ∀' ∀' (tMs (&0) (tSc (&1)) =' tSc (tMs (&0) (&1)))

/-- BASIC 24. -/
def axB24 : L.Sentence := ∀' ∀' ∀' (tMs (tMs (&0) (&1)) (&2) =' tMs (&0) (tMs (&1) (&2)))

/-- BASIC 25. -/
def axB25 : L.Sentence := ∀' ∀' ∀' (fLe (tMs (&0) (&1)) (tMs (&0) (&2)) ⇔ fLe (&1) (&2))

/-- BASIC 26. -/
def axB26 : L.Sentence := ∀' (tPr (&0) tC =' tC)

/-- BASIC 27. -/
def axB27 : L.Sentence := ∀' ∀' (tPr (&0) (tSc (&1)) =' tMs (tPr (&0) (&1)) (&0))

/-- BASIC 28. -/
def axB28 : L.Sentence := ∀' ∀' (tPr (&0) (&1) =' tPr (&1) (&0))

/-- BASIC 29. -/
def axB29 : L.Sentence := ∀' ∀' ∀' (tPr (&0) (tMs (&1) (&2)) =' tMs (tPr (&0) (&1)) (tPr (&0) (&2)))

/-- BASIC 30. -/
def axB30 : L.Sentence := ∀' ∀' ∀' (fLe tU (&0) ⟹ (fLe (tPr (&0) (&1)) (tPr (&0) (&2)) ⇔ fLe (&1) (&2)))

/-- BASIC 31. -/
def axB31 : L.Sentence := ∀' (∼((&0) =' tC) ⟹ tLg (&0) =' tSc (tLg (tMt (&0))))

/-- BASIC 32. -/
def axB32 : L.Sentence := ∀' ∀' ((&0) =' tMt (&1) ⇔ (tD (&0) =' (&1) ⊔ tSc (tD (&0)) =' (&1)))

/-- **Los 32 axiomas BASIC, como teoría.** -/
def teoriaBASIC : L.Theory :=
  {axB1, axB2, axB3, axB4, axB5, axB6, axB7, axB8, axB9, axB10, axB11, axB12, axB13, axB14, axB15, axB16, axB17, axB18, axB19, axB20, axB21, axB22, axB23, axB24, axB25, axB26, axB27, axB28, axB29, axB30, axB31, axB32}

section Equivalencias

-- Las 32 equivalencias usan la misma lista de `simp` (todos los términos del lenguaje): cada axioma usa solo
-- algunos, y el aviso de argumentos sin usar no dice nada útil aquí.
set_option linter.unusedSimpArgs false

variable (M : Type) [L.Structure M]

theorem realize_axB1 : M ⊨ axB1 ↔ ∀ x y : M, le y x → le y (suc x) := by
  simp [axB1, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB2 : M ⊨ axB2 ↔ ∀ x : M, x ≠ suc x := by
  simp [axB2, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB3 : M ⊨ axB3 ↔ ∀ x : M, le cero x := by
  simp [axB3, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB4 : M ⊨ axB4 ↔ ∀ x y : M, (le x y ∧ x ≠ y) ↔ le (suc x) y := by
  simp [axB4, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB5 : M ⊨ axB5 ↔ ∀ x : M, x ≠ cero → doble x ≠ cero := by
  simp [axB5, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB6 : M ⊨ axB6 ↔ ∀ x y : M, le y x ∨ le x y := by
  simp [axB6, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB7 : M ⊨ axB7 ↔ ∀ x y : M, le x y → le y x → x = y := by
  simp [axB7, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB8 : M ⊨ axB8 ↔ ∀ x y z : M, le x y → le y z → le x z := by
  simp [axB8, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB9 : M ⊨ axB9 ↔ long (cero : M) = cero := by
  simp [axB9, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB10 : M ⊨ axB10 ↔ ∀ x : M, x ≠ cero → long (doble x) = suc (long x) ∧ long (suc (doble x)) = suc (long x) := by
  simp [axB10, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB11 : M ⊨ axB11 ↔ long (uno : M) = uno := by
  simp [axB11, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB12 : M ⊨ axB12 ↔ ∀ x y : M, le x y → le (long x) (long y) := by
  simp [axB12, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB13 : M ⊨ axB13 ↔ ∀ x y : M, long (smash x y) = suc (prod (long x) (long y)) := by
  simp [axB13, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB14 : M ⊨ axB14 ↔ ∀ y : M, smash cero y = uno := by
  simp [axB14, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB15 : M ⊨ axB15 ↔ ∀ x : M, x ≠ cero → smash uno (doble x) = doble (smash uno x) ∧ smash uno (suc (doble x)) = doble (smash uno x) := by
  simp [axB15, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB16 : M ⊨ axB16 ↔ ∀ x y : M, smash x y = smash y x := by
  simp [axB16, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB17 : M ⊨ axB17 ↔ ∀ x y z : M, long x = long y → smash x z = smash y z := by
  simp [axB17, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB18 : M ⊨ axB18 ↔ ∀ x y u v : M, long x = suma (long u) (long v) → smash x y = prod (smash u y) (smash v y) := by
  simp [axB18, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB19 : M ⊨ axB19 ↔ ∀ x y : M, le x (suma x y) := by
  simp [axB19, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB20 : M ⊨ axB20 ↔ ∀ x y : M, le x y → x ≠ y → le (suc (doble x)) (doble y) ∧ suc (doble x) ≠ doble y := by
  simp [axB20, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB21 : M ⊨ axB21 ↔ ∀ x y : M, suma x y = suma y x := by
  simp [axB21, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB22 : M ⊨ axB22 ↔ ∀ x : M, suma x cero = x := by
  simp [axB22, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB23 : M ⊨ axB23 ↔ ∀ x y : M, suma x (suc y) = suc (suma x y) := by
  simp [axB23, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB24 : M ⊨ axB24 ↔ ∀ x y z : M, suma (suma x y) z = suma x (suma y z) := by
  simp [axB24, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB25 : M ⊨ axB25 ↔ ∀ x y z : M, le (suma x y) (suma x z) ↔ le y z := by
  simp [axB25, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB26 : M ⊨ axB26 ↔ ∀ x : M, prod x cero = cero := by
  simp [axB26, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB27 : M ⊨ axB27 ↔ ∀ x y : M, prod x (suc y) = suma (prod x y) x := by
  simp [axB27, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB28 : M ⊨ axB28 ↔ ∀ x y : M, prod x y = prod y x := by
  simp [axB28, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB29 : M ⊨ axB29 ↔ ∀ x y z : M, prod x (suma y z) = suma (prod x y) (prod x z) := by
  simp [axB29, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB30 : M ⊨ axB30 ↔ ∀ x y z : M, le uno x → (le (prod x y) (prod x z) ↔ le y z) := by
  simp [axB30, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB31 : M ⊨ axB31 ↔ ∀ x : M, x ≠ cero → long x = suc (long (mitad x)) := by
  simp [axB31, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

theorem realize_axB32 : M ⊨ axB32 ↔ ∀ x y : M, x = mitad y ↔ (doble x = y ∨ suc (doble x) = y) := by
  simp [axB32, fLe, tSc, tLg, tMt, tMs, tPr, tSm, tU, tD, Sentence.Realize, Formula.Realize, Fin.snoc]; rfl

/-- **Cumplir los 32 axiomas en el sentido de `EsModeloBASIC` es ser modelo de la teoría.** -/
theorem modelo_basic_iff : M ⊨ teoriaBASIC ↔ EsModeloBASIC M := by
  simp only [teoriaBASIC, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, realize_axB1, realize_axB2, realize_axB3, realize_axB4, realize_axB5, realize_axB6, realize_axB7, realize_axB8, realize_axB9, realize_axB10, realize_axB11, realize_axB12, realize_axB13, realize_axB14, realize_axB15, realize_axB16, realize_axB17, realize_axB18, realize_axB19, realize_axB20, realize_axB21, realize_axB22, realize_axB23, realize_axB24, realize_axB25, realize_axB26, realize_axB27, realize_axB28, realize_axB29, realize_axB30, realize_axB31, realize_axB32]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
  · intro h
    exact ⟨h.b1, h.b2, h.b3, h.b4, h.b5, h.b6, h.b7, h.b8, h.b9, h.b10, h.b11, h.b12, h.b13, h.b14, h.b15, h.b16, h.b17, h.b18, h.b19, h.b20, h.b21, h.b22, h.b23, h.b24, h.b25, h.b26, h.b27, h.b28, h.b29, h.b30, h.b31, h.b32⟩

end Equivalencias

/-! ## PIND, como esquema de sentencias -/

section PIND

variable {k : ℕ}

/-- **El axioma PIND de `φ`**, como sentencia: para todos los parámetros `v⃗`, si `φ(0, v⃗)` y, para todo `x`,
`φ(⌊x/2⌋, v⃗) → φ(x, v⃗)`, entonces `φ(x, v⃗)` para todo `x`. La variable 0 de `φ` es la de inducción y las
demás son los parámetros, como en `EsModeloS12`. -/
noncomputable def pindAx (φ : L.Formula (Fin (k + 1))) : L.Sentence :=
  let x : L.Term (Fin k ⊕ Fin 1) := Term.var (Sum.inr 0)
  let par : Fin k → L.Term (Fin k ⊕ Fin 1) := fun i => Term.var (Sum.inl i)
  let base : L.Formula (Fin k) := φ.subst (Fin.cons tC (fun i => Term.var i))
  let paso : L.Formula (Fin k) :=
    Formula.iAlls (β := Fin 1) ((φ.subst (Fin.cons (tMt x) par)).imp (φ.subst (Fin.cons x par)))
  let concl : L.Formula (Fin k) := Formula.iAlls (β := Fin 1) (φ.subst (Fin.cons x par))
  let cuerpo : L.Formula (Fin k) := (base ⊓ paso).imp concl
  Formula.iAlls (β := Fin k) (cuerpo.subst (fun i => Term.var (Sum.inr i)) : L.Formula (Empty ⊕ Fin k))

variable {M : Type} [L.Structure M]

/-- Sustituir variables por términos y después realizar es realizar con los valores de esos términos. -/
theorem formula_realize_subst {γ δ : Type} (ψ : L.Formula γ) (tf : γ → L.Term δ) (w : δ → M) :
    Formula.Realize (ψ.subst tf) w ↔ Formula.Realize ψ (fun a => (tf a).realize w) := by
  simp only [Formula.Realize, BoundedFormula.realize_subst]

/-- Los valores de `Fin.cons t par`: el de `t` y los de `par`. -/
theorem realize_fin_cons {γ : Type} (t : L.Term γ) (par : Fin k → L.Term γ) (w : γ → M) :
    (fun a => (Fin.cons (α := fun _ => L.Term γ) t par a).realize w) =
      Fin.cons (α := fun _ => M) (t.realize w) (fun i => (par i).realize w) := by
  funext a
  refine Fin.cases ?_ ?_ a <;> simp

/-- Realizar `φ` con la variable 0 cambiada por `t` y la `i + 1` por `par i`. -/
theorem realize_subst_cons {γ : Type} (φ : L.Formula (Fin (k + 1))) (t : L.Term γ) (par : Fin k → L.Term γ)
    (w : γ → M) :
    Formula.Realize (φ.subst (Fin.cons t par)) w ↔
      Formula.Realize φ (Fin.cons (t.realize w) (fun i => (par i).realize w)) := by
  rw [formula_realize_subst]
  apply iff_of_eq; congr 1; funext a
  refine Fin.cases ?_ ?_ a <;> simp

/-- **Cumplir PIND para `φ` es ser modelo de su sentencia.** -/
theorem realize_pindAx (φ : L.Formula (Fin (k + 1))) :
    M ⊨ pindAx φ ↔ ∀ v : Fin k → M, Formula.Realize φ (Fin.cons cero v) →
      (∀ x : M, Formula.Realize φ (Fin.cons (mitad x) v) → Formula.Realize φ (Fin.cons x v)) →
      ∀ x : M, Formula.Realize φ (Fin.cons x v) := by
  simp only [pindAx, Sentence.Realize, Formula.realize_iAlls, formula_realize_subst, Formula.realize_imp,
    Formula.realize_inf, realize_fin_cons, Term.realize_var, Sum.elim_inr, realize_tC, tMt,
    Term.realize_functions_apply₁]
  constructor
  · intro h v h0 hpaso x
    exact h v ⟨h0, fun i => hpaso (i 0)⟩ (fun _ => x)
  · intro h v ⟨h0, hpaso⟩ i
    exact h v h0 (fun x => hpaso (fun _ => x)) (i 0)

end PIND

/-! ## La teoría S¹₂ -/

/-- **S¹₂ como teoría de Mathlib**: los 32 axiomas BASIC y el axioma PIND de cada fórmula `Σᵇ₁`. -/
noncomputable def S12 : L.Theory :=
  teoriaBASIC ∪ {σ | ∃ (k : ℕ) (φ : L.Formula (Fin (k + 1))), EsSigma1 φ ∧ σ = pindAx φ}

/-- **Ser modelo de S¹₂ (`EsModeloS12`) es ser modelo de la teoría `S12`.** -/
theorem modelo_S12_iff (M : Type) [L.Structure M] : M ⊨ S12 ↔ EsModeloS12 M := by
  rw [S12, Theory.model_union_iff, modelo_basic_iff, Theory.model_iff]
  constructor
  · rintro ⟨hb, hp⟩
    refine ⟨hb, fun k φ hφ v h0 hpaso x => ?_⟩
    exact (realize_pindAx φ).1 (hp _ ⟨k, φ, hφ, rfl⟩) v h0 hpaso x
  · rintro ⟨hb, hp⟩
    refine ⟨hb, ?_⟩
    rintro σ ⟨k, φ, hφ, rfl⟩
    exact (realize_pindAx φ).2 (hp k φ hφ)

/-! ## `Demuestra` es la consecuencia semántica de Mathlib, y es finita -/

/-- **`Demuestra σ` es `S12 ⊨ᵇ σ`.** Mathlib cuenta solo modelos no vacíos; un modelo de S¹₂ siempre tiene el `0`. -/
theorem demuestra_iff_models (σ : L.Sentence) :
    Demuestra σ ↔ Theory.ModelsBoundedFormula.{0, 0, 0} S12 σ := by
  constructor
  · intro h M v xs
    have hM : EsModeloS12 M := (modelo_S12_iff M).1 inferInstance
    have := h M hM
    rw [Sentence.Realize, Formula.Realize] at this
    simpa [Unique.eq_default v, Unique.eq_default xs] using this
  · intro h M _ hM
    have : M ⊨ S12 := (modelo_S12_iff M).2 hM
    have : Nonempty M := ⟨cero⟩
    exact (Theory.models_sentence_iff.1 h) (Theory.ModelType.of S12 M)

/-- **Compacidad**: lo que S¹₂ demuestra se sigue de un número finito de sus axiomas, como pasa con una prueba. -/
theorem demuestra_iff_finito (σ : L.Sentence) :
    Demuestra σ ↔ ∃ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ S12 ∧
      Theory.ModelsBoundedFormula.{0, 0, 0} (T0 : L.Theory) σ := by
  rw [demuestra_iff_models, Theory.models_iff_finset_models]

end Acotada
end Sagitta.Map
