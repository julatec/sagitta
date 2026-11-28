import Sagitta.Map.TeoriaCobham
import Sagitta.Map.CobNumerable

/-!
# Saturación de Herbrand para la teoría de Cobham (R3)

Tercer paso de la ruta por modelos. Sigue a J. Avigad, «Saturated models
of universal theories» (2001), teoremas 3.2 y 3.3, especializados a la teoría `TC` de `TeoriaCobham.lean`.

## Parte A: herramientas dentro de un modelo cualquiera

* Las proyecciones y la composición de programas se portan en todo modelo como en ℕ (`ap_proy`, `ap_comp`).
* **`Enunciado`**: combinaciones con «no», «y», «o» y «si… entonces» de ecuaciones entre programas, y su
  transferencia a todo modelo (`Enunciado.transferir`).
* **`generado_es_programa`**: en lo que generan unas constantes, todo elemento es un programa aplicado a ellas.

## Parte B: condiciones y compacidad

* **`Cond`**: «para todo `ȳ`, `χ(c₀, …, c_{K-1}, ȳ) = 0`», sobre las primeras `K` constantes.
* **`compacidad`**: si todo subconjunto finito de condiciones tiene modelo, el conjunto entero lo tiene. Viene de
  la compacidad de Mathlib, pasando por el lenguaje con constantes.

## Parte C: el cierre y Herbrand

* **`Realizacion.cierre`**: lo que generan las constantes; ahí todo elemento es un programa de ellas.
* **`herbrand`**: si unas condiciones más «para todo `y`, `χ = 0`» no tienen modelo, ya no lo tienen con un número
  finito de casos `y = P(constantes)`. Es la prueba por modelos: se cierra y se mira qué queda.

## Partes D y E: la construcción y el teorema

* **`Pedido`** y **`estado`**: se recorren todos los pedidos «existen `x̄` con: para todo `y`, `θ = 0`» (los
  programas son numerables, `CobNumerable.lean`); a cada uno se le dan testigos nuevos, y se acepta si no
  contradice lo ya elegido. Es la construcción del teorema 3.2 de Avigad.
* **`existe_saturada`**: toda lista consistente de condiciones se cumple en una realización **generada** por sus
  constantes y **saturada**: todo «para todo `x̄` existe `y`» sin cuantificadores que valga tiene un solo programa
  que da el `y`. Es el teorema 3.3 de Avigad en la forma que usa R4. La parte del rechazo va por Herbrand y junta
  los finitos programas con definición por casos (`elegir`).

## Qué no hay

* **Que el modelo cumple S¹₂.** Es R4: la inducción por bits sale de la saturación y de `pind_abierta`.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language

/-! ## Enunciados sin cuantificadores -/

/-- Enunciados sin cuantificadores sobre `n` variables: ecuaciones entre programas y sus combinaciones. -/
inductive Enunciado (n : ℕ) : Type
  | ec (p q : Cob n)
  | no (e : Enunciado n)
  | yy (e f : Enunciado n)
  | oo (e f : Enunciado n)
  | entonces (e f : Enunciado n)

namespace Enunciado

/-- Su valor en una estructura. -/
def Vale {M : Type} [LC.Structure M] {n : ℕ} : Enunciado n → (Fin n → M) → Prop
  | ec p q, v => ap p v = ap q v
  | no e, v => ¬ e.Vale v
  | yy e f, v => e.Vale v ∧ f.Vale v
  | oo e f, v => e.Vale v ∨ f.Vale v
  | entonces e f, v => e.Vale v → f.Vale v

/-- Su fórmula en la lógica de Mathlib. -/
def formula {n : ℕ} : Enunciado n → LC.BoundedFormula Empty n
  | ec p q => ecuacion p q
  | no e => e.formula.not
  | yy e f => e.formula ⊓ f.formula
  | oo e f => e.formula ⊔ f.formula
  | entonces e f => e.formula.imp f.formula

theorem formula_isQF {n : ℕ} : ∀ e : Enunciado n, e.formula.IsQF
  | ec _ _ => (BoundedFormula.IsAtomic.equal _ _).isQF
  | no e => (formula_isQF e).not
  | yy e f => ((formula_isQF e).imp (formula_isQF f).not).not
  | oo e f => (formula_isQF e).not.imp (formula_isQF f)
  | entonces e f => (formula_isQF e).imp (formula_isQF f)

theorem realize_formula {M : Type} [LC.Structure M] {n : ℕ} :
    ∀ (e : Enunciado n) (v : Fin n → M), e.formula.Realize Empty.elim v ↔ e.Vale v
  | ec p q, v => realize_ecuacion p q v
  | no e, v => by simp only [formula, BoundedFormula.realize_not, realize_formula e, Vale]
  | yy e f, v => by simp only [formula, BoundedFormula.realize_inf, realize_formula e, realize_formula f, Vale]
  | oo e f, v => by simp only [formula, BoundedFormula.realize_sup, realize_formula e, realize_formula f, Vale]
  | entonces e f, v => by
      simp only [formula, BoundedFormula.realize_imp, realize_formula e, realize_formula f, Vale]

/-- **Lo que vale en ℕ vale en todo modelo de la teoría.** -/
theorem transferir {M : Type} [LC.Structure M] [M ⊨ TC] {n : ℕ} (e : Enunciado n)
    (h : ∀ v : Fin n → ℕ, e.Vale v) (v : Fin n → M) : e.Vale v :=
  (realize_formula e v).mp
    (Cobham.transferir e.formula (formula_isQF e) (fun w => (realize_formula e w).mpr (h w)) v)

end Enunciado

/-! ## Proyecciones y composición en un modelo -/

section Modelo

variable {M : Type} [LC.Structure M] [M ⊨ TC]

/-- Una ecuación entre un programa aplicado a las variables y un término cualquiera. -/
private theorem ecuacion_termino {n : ℕ} (p : Cob n) (t : LC.Term (Empty ⊕ Fin n))
    (h : ∀ v : Fin n → ℕ, ap p v = t.realize (Sum.elim Empty.elim v)) (v : Fin n → M) :
    ap p v = t.realize (Sum.elim Empty.elim v) := by
  have := Cobham.transferir (M := M) (Term.bdEqual (aplicado p) t) (BoundedFormula.IsAtomic.equal _ _).isQF
    (fun w => by
      simp only [BoundedFormula.realize_bdEqual, aplicado, Term.realize_func, Term.realize_var, Sum.elim_inr]
      exact h w) v
  unfold ap
  simpa only [BoundedFormula.realize_bdEqual, aplicado, Term.realize_func, Term.realize_var,
    Sum.elim_inr] using this

/-- **Las proyecciones se portan bien** en todo modelo. -/
theorem ap_proy {n : ℕ} (i : Fin n) (v : Fin n → M) : ap (Cob.proy i) v = v i :=
  ecuacion_termino (Cob.proy i) (Term.var (Sum.inr i)) (fun _ => rfl) v

/-- **La composición se porta bien** en todo modelo: aplicar `comp f gs` es aplicar `f` a lo que dan los `gs`. -/
theorem ap_comp {n m : ℕ} (f : Cob m) (gs : Fin m → Cob n) (v : Fin n → M) :
    ap (Cob.comp f gs) v = ap f (fun i => ap (gs i) v) :=
  ecuacion_termino (Cob.comp f gs) (Term.func (L := LC) f fun i => aplicado (gs i)) (fun _ => rfl) v

/-- Un programa con sus variables renombradas. -/
def Cob.renombrar {n n' : ℕ} (p : Cob n) (σ : Fin n → Fin n') : Cob n' :=
  .comp p fun i => .proy (σ i)

theorem ap_renombrar {n n' : ℕ} (p : Cob n) (σ : Fin n → Fin n') (v : Fin n' → M) :
    ap (p.renombrar σ) v = ap p (v ∘ σ) := by
  simp only [Cob.renombrar, ap_comp, ap_proy]; rfl

end Modelo

/-! ## Lo generado por constantes -/

section Generado

variable {M : Type} [LC.Structure M] [M ⊨ TC]

/-- **Todo lo generado por unas constantes es un programa aplicado a ellas.** Si `ι` nombra elementos con
números, todo elemento del cierre de su imagen es `P (ι 0, …, ι (N - 1))` para algún programa `P`. -/
theorem generado_es_programa (ι : ℕ → M) {x : M} (hx : x ∈ Substructure.closure LC (Set.range ι)) :
    ∃ (N : ℕ) (P : Cob N), x = ap P fun j : Fin N => ι j := by
  obtain ⟨t, rfl⟩ := (Substructure.mem_closure_iff_exists_term).mp hx
  clear hx
  induction t with
  | var a =>
    obtain ⟨c, hc⟩ := a.2
    refine ⟨c + 1, .proy ⟨c, Nat.lt_succ_self c⟩, ?_⟩
    rw [ap_proy]; exact hc.symm
  | func f ts ih =>
    choose N P hP using ih
    let K : ℕ := Finset.univ.sup N
    have hN : ∀ i, N i ≤ K := fun i => Finset.le_sup (f := N) (Finset.mem_univ i)
    refine ⟨K, .comp f fun i => (P i).renombrar (Fin.castLE (hN i)), ?_⟩
    rw [ap_comp]
    simp only [Term.realize_func]
    unfold ap
    congr 1
    funext i
    change _ = ap ((P i).renombrar (Fin.castLE (hN i))) _
    rw [ap_renombrar, hP i]
    rfl

end Generado

/-! ## Parte B: condiciones y compacidad -/

/-- Las primeras `K` constantes. -/
def pre {M : Type} (ι : ℕ → M) (K : ℕ) : Fin K → M := fun j => ι j

/-- **Una condición**: «para todo `ȳ`, `χ(c₀, …, c_{K-1}, ȳ) = 0`», sobre las primeras `K` constantes. -/
structure Cond where
  K : ℕ
  m : ℕ
  χ : Cob (K + m)

/-- La condición vale cuando las constantes se leen con `ι`. -/
def Cond.Vale {M : Type} [LC.Structure M] (ι : ℕ → M) (C : Cond) : Prop :=
  ∀ ys : Fin C.m → M, ap C.χ (Fin.append (pre ι C.K) ys) = ap Cob.cero (Fin.append (pre ι C.K) ys)

/-- Un modelo de la teoría con una lectura de las constantes. -/
structure Realizacion where
  M : Type
  [str : LC.Structure M]
  [modelo : M ⊨ TC]
  ι : ℕ → M

attribute [instance] Realizacion.str Realizacion.modelo

/-- Un conjunto de condiciones es **consistente** si algún modelo de la teoría las cumple todas. -/
def Consistente (S : Set Cond) : Prop := ∃ R : Realizacion, ∀ C ∈ S, C.Vale R.ι

/-- Las variables de una condición, como términos: primero las constantes, después las cuantificadas. -/
def Cond.vars (C : Cond) : Fin (C.K + C.m) → LC.Term (ℕ ⊕ Fin C.m) :=
  Fin.addCases (fun i => Term.var (Sum.inl i.val)) (fun i => Term.var (Sum.inr i))

/-- La condición como fórmula de Mathlib, con las constantes como variables libres. -/
def Cond.formula (C : Cond) : LC.Formula ℕ :=
  (Term.bdEqual (Term.func (L := LC) C.χ C.vars)
    (Term.func (L := LC) (Cob.cero : Cob (C.K + C.m)) C.vars)).alls

theorem Cond.realize_vars {M : Type} [LC.Structure M] (ι : ℕ → M) (C : Cond) (ys : Fin C.m → M) :
    (fun j => (C.vars j).realize (Sum.elim ι ys)) = Fin.append (pre ι C.K) ys := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [Cond.vars, Fin.append_left, Fin.append_right, pre]

theorem Cond.realize_formula {M : Type} [LC.Structure M] (ι : ℕ → M) (C : Cond) :
    C.formula.Realize ι ↔ C.Vale ι := by
  simp only [Cond.formula, BoundedFormula.realize_alls, BoundedFormula.realize_bdEqual,
    Term.realize_func, Cond.Vale]
  refine forall_congr' fun ys => ?_
  rw [Cond.realize_vars]
  exact Iff.rfl

/-- La condición como enunciado del lenguaje con constantes. -/
noncomputable def Cond.sent (C : Cond) : LC[[ℕ]].Sentence := Formula.equivSentence C.formula

/-- **Compacidad para condiciones.** Si todo subconjunto finito es consistente, el conjunto lo es. -/
theorem compacidad (S : Set Cond) (h : ∀ F : Finset Cond, (↑F : Set Cond) ⊆ S → Consistente ↑F) :
    Consistente S := by
  classical
  let T' : LC[[ℕ]].Theory := (LC.lhomWithConstants ℕ).onTheory TC ∪ Cond.sent '' S
  have hfin : T'.IsFinitelySatisfiable := by
    intro T0 hT0
    let F : Finset Cond := T0.biUnion fun σ => if hσ : σ ∈ Cond.sent '' S then {hσ.choose} else ∅
    have hF : (↑F : Set Cond) ⊆ S := by
      intro C hC
      simp only [F, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hC
      obtain ⟨σ, -, hC⟩ := hC
      split at hC
      · rename_i hσ
        rw [Finset.mem_singleton] at hC
        rw [hC]; exact hσ.choose_spec.1
      · simp at hC
    obtain ⟨R, hR⟩ := h F hF
    let _ : (constantsOn ℕ).Structure R.M := constantsOn.structure R.ι
    have : Nonempty R.M := ⟨R.ι 0⟩
    have hTC : R.M ⊨ (LC.lhomWithConstants ℕ).onTheory TC :=
      (LHom.onTheory_model (LC.lhomWithConstants ℕ) TC).mpr R.modelo
    have hM : R.M ⊨ (↑T0 : LC[[ℕ]].Theory) := by
      refine (Theory.model_iff _).mpr fun σ hσ => ?_
      rcases hT0 hσ with hσ' | hσ'
      · exact Theory.realize_sentence_of_mem _ hσ'
      · have hC : hσ'.choose ∈ F := by
          simp only [F, Finset.mem_biUnion]
          exact ⟨σ, hσ, by simp only [hσ', ↓reduceDIte]; exact Finset.mem_singleton_self _⟩
        rw [← hσ'.choose_spec.2, Cond.sent, Formula.realize_equivSentence]
        exact (Cond.realize_formula _ _).mpr (hR _ hC)
    exact ⟨Theory.ModelType.of _ R.M⟩
  obtain ⟨N⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfin
  let _ : LC.Structure N := (LC.lhomWithConstants ℕ).reduct N
  have : N ⊨ TC :=
    (LHom.onTheory_model (LC.lhomWithConstants ℕ) TC).mp (Theory.Model.mono N.is_model Set.subset_union_left)
  refine ⟨⟨N, fun a => (LC.con a : N)⟩, fun C hC => ?_⟩
  have hs : N ⊨ C.sent := Theory.realize_sentence_of_mem T' (Or.inr ⟨C, hC, rfl⟩)
  rw [Cond.sent, Formula.realize_equivSentence] at hs
  exact (Cond.realize_formula _ _).mp hs

/-- Un subconjunto de un conjunto consistente es consistente. -/
theorem Consistente.mono {S S' : Set Cond} (h : Consistente S') (hs : S ⊆ S') : Consistente S :=
  let ⟨R, hR⟩ := h; ⟨R, fun C hC => hR C (hs hC)⟩

/-! ## Parte C: el cierre y Herbrand -/

/-- El cero de una estructura. -/
def cero0 (M : Type) [LC.Structure M] : M := ap (Cob.cero : Cob 0) Fin.elim0

theorem ap_cero {M : Type} [LC.Structure M] [M ⊨ TC] {n : ℕ} (v : Fin n → M) :
    ap (Cob.cero : Cob n) v = cero0 M := by
  have : ap (Cob.cero : Cob n) v = ap (Cob.comp (Cob.cero : Cob 0) Fin.elim0) v :=
    identidad Cob.cero (Cob.comp (Cob.cero : Cob 0) Fin.elim0) (fun _ => rfl) v
  rw [this, ap_comp]; unfold cero0; congr 1; funext i; exact i.elim0

/-- **El cierre**: lo que generan las constantes, con la misma lectura. -/
abbrev Realizacion.cierre (R : Realizacion) : Realizacion where
  M := Substructure.closure LC (Set.range R.ι)
  modelo := cerrar (Set.range R.ι)
  ι a := ⟨R.ι a, Substructure.subset_closure ⟨a, rfl⟩⟩

theorem Realizacion.cierre_ap (R : Realizacion) {n : ℕ} (p : Cob n)
    (v : Fin n → Substructure.closure LC (Set.range R.ι)) :
    ((ap p v : Substructure.closure LC (Set.range R.ι)) : R.M) = ap p (fun i => (v i : R.M)) := rfl

/-- Lo que vale arriba vale en el cierre: las condiciones son universales. -/
theorem Realizacion.vale_cierre (R : Realizacion) {C : Cond} (h : C.Vale R.ι) : C.Vale R.cierre.ι := by
  intro ys
  apply Subtype.ext
  refine (R.cierre_ap C.χ _).trans (Eq.trans ?_ (R.cierre_ap Cob.cero _).symm)
  have e : (fun i => ((Fin.append (pre R.cierre.ι C.K) ys i : R.cierre.M) : R.M)) =
      Fin.append (pre R.ι C.K) (fun i => (ys i : R.M)) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [Fin.append_left, Fin.append_right, pre, Realizacion.cierre]
  rw [e]; exact h _

/-- En el cierre, todo elemento es un programa aplicado a las primeras constantes. -/
theorem Realizacion.cierre_programa (R : Realizacion) (x : R.cierre.M) :
    ∃ (N : ℕ) (P : Cob N), x = ap P (pre R.cierre.ι N) := by
  obtain ⟨N, P, hP⟩ := generado_es_programa R.ι x.2
  exact ⟨N, P, Subtype.ext (hP.trans (R.cierre_ap P (pre R.cierre.ι N)).symm)⟩

/-- Una condición con una sola variable cuantificada: «para todo `y`, `χ(c₀, …, c_{K-1}, y) = 0`». -/
structure Cond1 where
  K : ℕ
  χ : Cob (K + 1)

def Cond1.cond (C : Cond1) : Cond := ⟨C.K, 1, C.χ⟩

/-- **Un caso concreto**: la condición con `y` igual a un programa `P` de las primeras `N` constantes. -/
def Cond1.caso (C : Cond1) (N : ℕ) (P : Cob N) : Cond :=
  ⟨max C.K N, 0, .comp C.χ (Fin.lastCases
    (P.renombrar fun l => Fin.castAdd 0 (Fin.castLE (le_max_right _ _) l))
    (fun i => .proy (Fin.castAdd 0 (Fin.castLE (le_max_left _ _) i))))⟩

section Valores

variable {M : Type} [LC.Structure M] [M ⊨ TC]

theorem Cond.vale_iff (ι : ℕ → M) (C : Cond) :
    C.Vale ι ↔ ∀ ys : Fin C.m → M, ap C.χ (Fin.append (pre ι C.K) ys) = cero0 M := by
  simp only [Cond.Vale, ap_cero]

theorem Cond1.vale_iff (ι : ℕ → M) (C : Cond1) :
    C.cond.Vale ι ↔ ∀ y : M, ap C.χ (Fin.append (pre ι C.K) ![y]) = cero0 M := by
  rw [Cond.vale_iff]
  change (∀ ys : Fin 1 → M, ap C.χ (Fin.append (pre ι C.K) ys) = cero0 M) ↔ _
  constructor
  · intro h y; exact h ![y]
  · intro h ys
    have : ys = ![ys 0] := by funext i; fin_cases i; rfl
    rw [this]; exact h _

theorem Cond1.caso_vale (ι : ℕ → M) (C : Cond1) (N : ℕ) (P : Cob N) :
    (C.caso N P).Vale ι ↔ ap C.χ (Fin.append (pre ι C.K) ![ap P (pre ι N)]) = cero0 M := by
  rw [Cond.vale_iff]
  dsimp only [Cond1.caso]
  have key : ∀ ys : Fin 0 → M,
      (fun i => ap (Fin.lastCases (P.renombrar fun l => Fin.castAdd 0 (Fin.castLE (le_max_right C.K N) l))
        (fun i => Cob.proy (Fin.castAdd 0 (Fin.castLE (le_max_left C.K N) i))) i)
        (Fin.append (pre ι (max C.K N)) ys)) = Fin.append (pre ι C.K) ![ap P (pre ι N)] := by
    intro ys
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.lastCases_last, ap_renombrar]
      rw [show Fin.last C.K = Fin.natAdd C.K (0 : Fin 1) from rfl, Fin.append_right, Matrix.cons_val_zero]
      congr 1; funext l
      simp only [Function.comp_apply, Fin.append_left, pre, Fin.val_castLE]
    · simp only [Fin.lastCases_castSucc, ap_proy]
      rw [show Fin.castSucc i = Fin.castAdd 1 i from rfl, Fin.append_left, Fin.append_left]
      simp only [pre, Fin.val_castLE]
  simp only [ap_comp, key]
  exact ⟨fun h => h Fin.elim0, fun h _ => h⟩

end Valores

/-- **Herbrand.** Si unas condiciones más «para todo `y`, `χ = 0`» son inconsistentes, ya lo son con un número
finito de casos concretos, cada uno con `y` igual a un programa de las constantes. -/
theorem herbrand (S : Set Cond) (C : Cond1) (h : ¬ Consistente (S ∪ {C.cond})) :
    ∃ F : Finset (Σ N, Cob N),
      ¬ Consistente (S ∪ (fun q : (Σ N, Cob N) => C.caso q.1 q.2) '' (↑F : Set (Σ N, Cob N))) := by
  classical
  by_contra hno
  push Not at hno
  have hall : Consistente (S ∪ Set.range fun q : Σ N, Cob N => C.caso q.1 q.2) := by
    refine compacidad _ fun F0 hF0 => ?_
    let F : Finset (Σ N, Cob N) := F0.biUnion fun D =>
      if hD : ∃ q : Σ N, Cob N, C.caso q.1 q.2 = D then {hD.choose} else ∅
    refine (hno F).mono fun D hD => ?_
    rcases hF0 hD with hS | ⟨q, rfl⟩
    · exact Or.inl hS
    · refine Or.inr ⟨(⟨q, rfl⟩ : ∃ q' : Σ N, Cob N, C.caso q'.1 q'.2 = C.caso q.1 q.2).choose, ?_, ?_⟩
      · simp only [F, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
        exact ⟨_, hD, by
          simp only [show (∃ q' : Σ N, Cob N, C.caso q'.1 q'.2 = C.caso q.1 q.2) from ⟨q, rfl⟩,
            ↓reduceDIte]
          exact Finset.mem_singleton_self _⟩
      · exact (⟨q, rfl⟩ : ∃ q' : Σ N, Cob N, C.caso q'.1 q'.2 = C.caso q.1 q.2).choose_spec
  obtain ⟨R, hR⟩ := hall
  refine h ⟨R.cierre, fun D hD => ?_⟩
  rcases hD with hS | rfl
  · exact R.vale_cierre (hR D (Or.inl hS))
  · rw [Cond1.vale_iff]
    intro y
    obtain ⟨N, P, rfl⟩ := R.cierre_programa y
    exact (Cond1.caso_vale _ C N P).mp (R.vale_cierre (hR _ (Or.inr ⟨⟨N, P⟩, rfl⟩)))

/-! ## Parte D: la construcción -/

/-- **Un pedido**: «existen `x̄` (`a` valores) con: para todo `y`, `θ(c₀, …, c_{K-1}, x̄, y) = 0`». -/
structure Pedido where
  K : ℕ
  a : ℕ
  θ : Cob (K + a + 1)

instance : Countable Pedido :=
  Function.Injective.countable (f := fun P : Pedido => (P.K, P.a, (⟨_, P.θ⟩ : Σ n, Cob n))) fun P Q h => by
    obtain ⟨K, a, θ⟩ := P; obtain ⟨K', a', θ'⟩ := Q
    simp only [Prod.mk.injEq, Sigma.mk.injEq] at h
    obtain ⟨rfl, rfl, -, h⟩ := h
    rw [eq_of_heq h]

instance : Nonempty Pedido := ⟨⟨0, 0, .cero⟩⟩

/-- Dónde van las variables `(c₀, …, c_{K-1}, x̄, y)` de un pedido cuando los `x̄` son las constantes
`B, …, B + a - 1`. -/
def lugar (K a B : ℕ) (hB : K ≤ B) : Fin (K + a + 1) → Fin (B + a + 1) :=
  Fin.lastCases (Fin.last _) fun j => Fin.castSucc (Fin.addCases
    (fun i : Fin K => Fin.castAdd a (Fin.castLE hB i)) (fun i : Fin a => Fin.natAdd B i) j)

theorem vec_lugar {M : Type} (ι : ℕ → M) (K a B : ℕ) (hB : K ≤ B) (y : M) :
    Fin.append (pre ι (B + a)) ![y] ∘ lugar K a B hB =
      Fin.append (Fin.append (pre ι K) fun i => ι (B + i)) ![y] := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Function.comp_apply, lugar, Fin.lastCases_last]
    rw [show Fin.last (B + a) = Fin.natAdd (B + a) (0 : Fin 1) from rfl,
      show Fin.last (K + a) = Fin.natAdd (K + a) (0 : Fin 1) from rfl, Fin.append_right, Fin.append_right]
  · simp only [Function.comp_apply, lugar, Fin.lastCases_castSucc]
    rw [show Fin.castSucc j = Fin.castAdd 1 j from rfl, Fin.append_left]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.addCases_left]
      rw [show Fin.castSucc (Fin.castAdd a (Fin.castLE hB i)) = Fin.castAdd 1 (Fin.castAdd a (Fin.castLE hB i))
        from rfl, Fin.append_left, Fin.append_left]
      simp only [pre, Fin.val_castAdd, Fin.val_castLE]
    · simp only [Fin.addCases_right]
      rw [show Fin.castSucc (Fin.natAdd B i) = Fin.castAdd 1 (Fin.natAdd B i) from rfl, Fin.append_left,
        Fin.append_right]
      simp only [pre, Fin.val_natAdd]

/-- La condición que agrega un pedido, con los testigos `B, …, B + a - 1`. -/
def Pedido.cond (P : Pedido) (B : ℕ) (hB : P.K ≤ B) : Cond1 :=
  ⟨B + P.a, P.θ.renombrar (lugar P.K P.a B hB)⟩

theorem Pedido.cond_vale {M : Type} [LC.Structure M] [M ⊨ TC] (ι : ℕ → M) (P : Pedido) (B : ℕ)
    (hB : P.K ≤ B) :
    (P.cond B hB).cond.Vale ι ↔
      ∀ y, ap P.θ (Fin.append (Fin.append (pre ι P.K) fun i => ι (B + i)) ![y]) = cero0 M := by
  rw [Cond1.vale_iff]
  refine forall_congr' fun y => ?_
  simp only [Pedido.cond, ap_renombrar, vec_lugar]

/-- Un estado de la construcción: las condiciones elegidas y una cota de las constantes usadas. -/
structure Estado where
  S : List Cond
  B : ℕ

/-- **Un paso**: atender un pedido con testigos nuevos; se agrega si no contradice lo elegido. -/
noncomputable def Estado.siguiente (E : Estado) (P : Pedido) : Estado := by
  classical exact if Consistente ({D | D ∈ E.S} ∪ {(P.cond (max E.B P.K) (le_max_right _ _)).cond}) then
    ⟨(P.cond (max E.B P.K) (le_max_right _ _)).cond :: E.S, max E.B P.K + P.a⟩
  else ⟨E.S, max E.B P.K + P.a⟩

/-- Los estados, atendiendo los pedidos en el orden de `e`. -/
noncomputable def estado (E0 : Estado) (e : ℕ → Pedido) : ℕ → Estado
  | 0 => E0
  | i + 1 => (estado E0 e i).siguiente (e i)

theorem Estado.siguiente_sub (E : Estado) (P : Pedido) : ∀ D ∈ E.S, D ∈ (E.siguiente P).S := by
  intro D hD; unfold Estado.siguiente; split
  · exact List.mem_cons_of_mem _ hD
  · exact hD

theorem Estado.siguiente_B (E : Estado) (P : Pedido) : (E.siguiente P).B = max E.B P.K + P.a := by
  unfold Estado.siguiente; split <;> rfl

theorem Estado.siguiente_cota (E : Estado) (P : Pedido) (h : ∀ D ∈ E.S, D.K ≤ E.B) :
    ∀ D ∈ (E.siguiente P).S, D.K ≤ (E.siguiente P).B := by
  rw [Estado.siguiente_B]
  intro D hD; unfold Estado.siguiente at hD; split at hD
  · rcases List.mem_cons.mp hD with rfl | hD
    · exact le_refl _
    · exact (h D hD).trans ((le_max_left _ _).trans (Nat.le_add_right _ _))
  · exact (h D hD).trans ((le_max_left _ _).trans (Nat.le_add_right _ _))

theorem Estado.siguiente_consistente (E : Estado) (P : Pedido) (h : Consistente {D | D ∈ E.S}) :
    Consistente {D | D ∈ (E.siguiente P).S} := by
  unfold Estado.siguiente; split
  · rename_i hc
    refine hc.mono fun D hD => ?_
    rcases List.mem_cons.mp hD with rfl | hD
    · exact Or.inr rfl
    · exact Or.inl hD
  · exact h

theorem estado_mono (E0 : Estado) (e : ℕ → Pedido) {i j : ℕ} (hij : i ≤ j) :
    ∀ D ∈ (estado E0 e i).S, D ∈ (estado E0 e j).S := by
  induction j, hij using Nat.le_induction with
  | base => exact fun D hD => hD
  | succ j _ ih => exact fun D hD => Estado.siguiente_sub _ _ D (ih D hD)

theorem estado_cota (E0 : Estado) (e : ℕ → Pedido) (h0 : ∀ D ∈ E0.S, D.K ≤ E0.B) :
    ∀ i, ∀ D ∈ (estado E0 e i).S, D.K ≤ (estado E0 e i).B
  | 0 => h0
  | i + 1 => Estado.siguiente_cota _ _ (estado_cota E0 e h0 i)

theorem estado_consistente (E0 : Estado) (e : ℕ → Pedido) (h0 : Consistente {D | D ∈ E0.S}) :
    ∀ i, Consistente {D | D ∈ (estado E0 e i).S}
  | 0 => h0
  | i + 1 => Estado.siguiente_consistente _ _ (estado_consistente E0 e h0 i)

/-- **Todo lo elegido junto es consistente**, por compacidad. -/
theorem limite_consistente (E0 : Estado) (e : ℕ → Pedido) (h0 : Consistente {D | D ∈ E0.S}) :
    Consistente {D | ∃ i, D ∈ (estado E0 e i).S} := by
  classical
  refine compacidad _ fun F hF => ?_
  choose idx hidx using fun D : {D // D ∈ F} => hF D.2
  let j := Finset.univ.sup idx
  refine (estado_consistente E0 e h0 j).mono fun D hD => ?_
  exact estado_mono E0 e (Finset.le_sup (f := idx) (Finset.mem_univ ⟨D, hD⟩)) D (hidx ⟨D, hD⟩)

/-! ## Parte E: el modelo saturado -/

section Casos

variable {M : Type} [LC.Structure M] [M ⊨ TC]

/-- «no» en un modelo. -/
theorem ap_no {n : ℕ} (θ : Cob n) (v : Fin n → M) : ap (no θ) v = cero0 M ↔ ap θ v ≠ cero0 M := by
  have h := Enunciado.transferir (M := M)
    (.yy (.entonces (.ec (no θ) .cero) (.no (.ec θ .cero))) (.entonces (.no (.ec θ .cero)) (.ec (no θ) .cero)))
    (fun w => by
      simp only [Enunciado.Vale, ap_nat, eval_cero]
      exact ⟨(no_vale θ w).mp, (no_vale θ w).mpr⟩) v
  simp only [Enunciado.Vale, ap_cero] at h
  exact ⟨h.1, h.2⟩

/-- El condicional en un modelo. -/
theorem ap_cond3 {n : ℕ} (p q r : Cob n) (v : Fin n → M) :
    (ap p v = cero0 M → ap (c3 .cond p q r) v = ap q v) ∧
      (ap p v ≠ cero0 M → ap (c3 .cond p q r) v = ap r v) := by
  have h := Enunciado.transferir (M := M)
    (.yy (.entonces (.ec p .cero) (.ec (c3 .cond p q r) q))
      (.entonces (.no (.ec p .cero)) (.ec (c3 .cond p q r) r)))
    (fun w => by
      simp only [Enunciado.Vale, ap_nat, eval_cero, eval_c3, eval_cond]
      exact ⟨fun h => by simp [h], fun h => by simp [h]⟩) v
  simp only [Enunciado.Vale, ap_cero] at h
  exact h

end Casos

/-- Las variables `(c₀, …, c_{K-1}, x̄, y)` de un pedido, con `y` dado por `G`, como programas sobre
`(c₀, …, c_{L-1}, x̄)`. -/
def selector (K a L : ℕ) (hK : K ≤ L) (G : Cob (L + a)) : Fin (K + a + 1) → Cob (L + a) :=
  Fin.lastCases G fun j => Fin.addCases (fun i : Fin K => .proy (Fin.castAdd a (Fin.castLE hK i)))
    (fun i : Fin a => .proy (Fin.natAdd L i)) j

/-- `θ` con el `y` dado por el programa `G`. -/
def conTestigo {K a L : ℕ} (θ : Cob (K + a + 1)) (hK : K ≤ L) (G : Cob (L + a)) : Cob (L + a) :=
  .comp θ (selector K a L hK G)

theorem ap_conTestigo {M : Type} [LC.Structure M] [M ⊨ TC] {K a L : ℕ} (θ : Cob (K + a + 1)) (hK : K ≤ L)
    (G : Cob (L + a)) (ι : ℕ → M) (x : Fin a → M) :
    ap (conTestigo θ hK G) (Fin.append (pre ι L) x) =
      ap θ (Fin.append (Fin.append (pre ι K) x) ![ap G (Fin.append (pre ι L) x)]) := by
  rw [conTestigo, ap_comp]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [selector, Fin.lastCases_last]
    rw [show Fin.last (K + a) = Fin.natAdd (K + a) (0 : Fin 1) from rfl, Fin.append_right]
    rfl
  · simp only [selector, Fin.lastCases_castSucc]
    rw [show Fin.castSucc j = Fin.castAdd 1 j from rfl, Fin.append_left]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.addCases_left, ap_proy, Fin.append_left, pre, Fin.val_castLE]
    · simp only [Fin.addCases_right, ap_proy, Fin.append_right]

/-- **Elegir por casos**: el primero de una lista de programas que sirva. -/
def elegir {n : ℕ} (T : Cob n → Cob n) : List (Cob n) → Cob n
  | [] => .cero
  | G :: Gs => c3 .cond (T G) G (elegir T Gs)

theorem elegir_sirve {M : Type} [LC.Structure M] [M ⊨ TC] {n : ℕ} (T : Cob n → Cob n) (w : Fin n → M)
    (hT : ∀ G G' : Cob n, ap G w = ap G' w → ap (T G) w = ap (T G') w) :
    ∀ Gs : List (Cob n), (∃ G ∈ Gs, ap (T G) w = cero0 M) → ap (T (elegir T Gs)) w = cero0 M
  | [], ⟨_, hG, _⟩ => absurd hG List.not_mem_nil
  | G :: Gs, ⟨G', hG', h'⟩ => by
      by_cases h : ap (T G) w = cero0 M
      · rw [hT (elegir T (G :: Gs)) G (by rw [elegir]; exact (ap_cond3 _ _ _ _).1 h)]; exact h
      · rcases List.mem_cons.mp hG' with rfl | hG'
        · exact absurd h' h
        · rw [hT (elegir T (G :: Gs)) (elegir T Gs) (by rw [elegir]; exact (ap_cond3 _ _ _ _).2 h)]
          exact elegir_sirve T w hT Gs ⟨G', hG', h'⟩

/-- Todo elemento es un programa aplicado a las primeras constantes. -/
def Generada (R : Realizacion) : Prop := ∀ x : R.M, ∃ (N : ℕ) (P : Cob N), x = ap P (pre R.ι N)

/-- **Saturada**: si para todo `x̄` hay un `y` con `θ(c̄, x̄, y) = 0`, un solo programa de las constantes y de `x̄` da
ese `y`. Es la forma del teorema 3.3 de Avigad que usa el paso siguiente. -/
def Saturada (R : Realizacion) : Prop :=
  ∀ (K a : ℕ) (θ : Cob (K + a + 1)),
    (∀ x : Fin a → R.M, ∃ y : R.M, ap θ (Fin.append (Fin.append (pre R.ι K) x) ![y]) = cero0 R.M) →
    ∃ (L : ℕ) (G : Cob (L + a)), ∀ x : Fin a → R.M,
      ap θ (Fin.append (Fin.append (pre R.ι K) x) ![ap G (Fin.append (pre R.ι L) x)]) = cero0 R.M

/-- Cambiar la lectura de constantes que una condición no usa no la cambia. -/
theorem Cond.vale_congr {M : Type} [LC.Structure M] {ι ι' : ℕ → M} (D : Cond) (h : ∀ c < D.K, ι c = ι' c)
    (hD : D.Vale ι) : D.Vale ι' := by
  have : pre ι D.K = pre ι' D.K := funext fun j => h j j.2
  intro ys; rw [← this]; exact hD ys

/-- **El teorema de R3.** Toda lista consistente de condiciones se cumple en una realización generada por sus
constantes y saturada. -/
theorem existe_saturada (E0 : Estado) (h0 : ∀ D ∈ E0.S, D.K ≤ E0.B) (hc : Consistente {D | D ∈ E0.S}) :
    ∃ R : Realizacion, (∀ D ∈ E0.S, D.Vale R.ι) ∧ Generada R ∧ Saturada R := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat Pedido
  obtain ⟨R0, hR0⟩ := limite_consistente E0 e hc
  refine ⟨R0.cierre, fun D hD => R0.vale_cierre (hR0 D ⟨0, hD⟩), R0.cierre_programa, ?_⟩
  intro K a θ hθ
  obtain ⟨i, hi⟩ := he ⟨K, a, no θ⟩
  have hKB : K ≤ max (estado E0 e i).B K := le_max_right _ _
  have hvale : ∀ D ∈ (estado E0 e i).S, D.Vale R0.cierre.ι := fun D hD => R0.vale_cierre (hR0 D ⟨i, hD⟩)
  by_cases hcons : Consistente ({D | D ∈ (estado E0 e i).S} ∪
      {(Pedido.cond ⟨K, a, no θ⟩ (max (estado E0 e i).B K) hKB).cond})
  · exfalso
    have hmem : (Pedido.cond ⟨K, a, no θ⟩ (max (estado E0 e i).B K) hKB).cond ∈ (estado E0 e (i + 1)).S := by
      change _ ∈ ((estado E0 e i).siguiente (e i)).S
      rw [hi]; unfold Estado.siguiente
      rw [ite_eq_left hcons]; exact List.mem_cons_self
    have hv := R0.vale_cierre (hR0 _ ⟨i + 1, hmem⟩)
    rw [Pedido.cond_vale] at hv
    obtain ⟨y, hy⟩ := hθ fun j => R0.cierre.ι (max (estado E0 e i).B K + j)
    exact (ap_no θ _).mp (hv y) hy
  · obtain ⟨F, hF⟩ := herbrand _ _ hcons
    set B' := max (estado E0 e i).B K with hB'
    set R := R0.cierre
    let L := max (B' + a) (F.sup fun q => q.1)
    have hNL : ∀ q ∈ F, q.1 ≤ L := fun q hq => (Finset.le_sup (f := fun q => q.1) hq).trans (le_max_right _ _)
    have hKL : K ≤ L := hKB.trans ((Nat.le_add_right _ _).trans (le_max_left _ _))
    let ι2 : (Fin a → R.M) → ℕ → R.M := fun x c =>
      if h : B' ≤ c ∧ c < B' + a then x ⟨c - B', by omega⟩ else R.ι c
    let τ : (q : Σ N, Cob N) → q.1 ≤ L → Fin q.1 → Fin (L + a) := fun q hq c =>
      if h : B' ≤ c.val ∧ c.val < B' + a then Fin.natAdd L ⟨c.val - B', by omega⟩
      else Fin.castAdd a ⟨c.val, lt_of_lt_of_le c.2 hq⟩
    let Gs : List (Cob (L + a)) := F.attach.toList.map fun q => q.1.2.renombrar (τ q.1 (hNL q.1 q.2))
    have hι2 : ∀ x c, c < B' → ι2 x c = R.ι c := fun x c hc => by
      simp only [ι2]; rw [dite_eq_right (by omega)]
    have hpreK : ∀ x, pre (ι2 x) K = pre R.ι K := fun x => funext fun j => hι2 x j (by omega)
    have hx : ∀ x, (fun j : Fin a => ι2 x (B' + j)) = x := fun x => funext fun j => by
      simp only [ι2]; rw [dite_eq_left (by omega)]; congr 1; ext; simp
    have hτ : ∀ x q (hq : q.1 ≤ L), Fin.append (pre R.ι L) x ∘ τ q hq = pre (ι2 x) q.1 := fun x q hq => by
      funext c
      simp only [Function.comp_apply, τ, ι2, pre]
      by_cases h : B' ≤ c.val ∧ c.val < B' + a
      · rw [dite_eq_left h, dite_eq_left h, Fin.append_right]
      · rw [dite_eq_right h, dite_eq_right h, Fin.append_left]; rfl
    have hcada : ∀ x : Fin a → R.M, ∃ G ∈ Gs,
        ap (conTestigo θ hKL G) (Fin.append (pre R.ι L) x) = cero0 R.M := by
      intro x
      let R2 : Realizacion := { M := R.M, ι := ι2 x }
      have hS : ∀ D ∈ (estado E0 e i).S, D.Vale R2.ι := fun D hD =>
        Cond.vale_congr D (fun c hc => (hι2 x c (lt_of_lt_of_le hc
          ((estado_cota E0 e h0 i D hD).trans (le_max_left _ _)))).symm) (hvale D hD)
      by_contra hno
      push Not at hno
      refine hF ⟨R2, fun D hD => ?_⟩
      rcases hD with hD | ⟨q, hq, rfl⟩
      · exact hS D hD
      · by_contra hc
        rw [Cond1.caso_vale] at hc
        simp only [Pedido.cond, ap_renombrar] at hc
        rw [vec_lugar] at hc
        change ¬ ap (no θ) _ = cero0 R.M at hc
        rw [ap_no, not_not, hpreK, hx] at hc
        refine hno _ (List.mem_map.mpr ⟨⟨q, hq⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩) ?_
        rw [ap_conTestigo, ap_renombrar, hτ x q (hNL q hq)]
        exact hc
    refine ⟨L, elegir (conTestigo θ hKL) Gs, fun x => ?_⟩
    have := elegir_sirve (conTestigo θ hKL) (Fin.append (pre R.ι L) x)
      (fun G G' hG => by rw [ap_conTestigo, ap_conTestigo, hG]) Gs (hcada x)
    rwa [ap_conTestigo] at this

end Cobham
end Sagitta.Map
