import Sagitta.Map.InduccionModelo
import Sagitta.Map.Teoria

/-!
# El enlace con la aritmética de Buss (R5a)

Quinto paso de la ruta por modelos, primera parte. Conecta lo de
`Cobham.lean` … `InduccionModelo.lean` con el lenguaje de Buss de `Acotada.lean` y `Teoria.lean`, sin modificar esos archivos.

## Qué hay

* **`estructuraBuss`**: todo modelo de `LC` es una estructura del lenguaje de Buss. Cada símbolo es un programa
  (`progFun`), y `x ≤ y` es `x ∸ y = 0`.
* **`trT`, `trF`**: los términos y las fórmulas sin cuantificadores de Buss, traducidos a programas y a
  `Enunciado`. `realize_trF` dice que la traducción vale donde vale el original, en toda estructura
  **compatible** con los programas (`Compatible`): la inducida y la estándar de ℕ.
* **`universal_vale`**: todo enunciado universal de Buss verdadero en ℕ vale en todo modelo de `TC`.
* **`esModeloBASIC`**: todo modelo de `TC` cumple los 32 axiomas BASIC.

## Qué no hay

* **Las fórmulas Σᵇ₁** de Buss y la inducción para ellas: es R5b, la pieza cara.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language
open Acotada (Fun Rel)

/-- El lenguaje de Buss. -/
abbrev LB : Language := Acotada.L

/-- **Cada símbolo de Buss, como programa.** -/
def progFun : {n : ℕ} → Fun n → Cob n
  | _, .cero => .cero
  | _, .suc => .suc
  | _, .long => .largo
  | _, .mitad => .mitad
  | _, .suma => .suma
  | _, .prod => .prod
  | _, .smash => .smash

/-- `x ≤ y`, como relación en una estructura de `LC`: `x ∸ y = 0`. -/
def relLe {M : Type} [LC.Structure M] : {n : ℕ} → Rel n → (Fin n → M) → Prop
  | _, .le, v => ap Cob.resta v = ap (Cob.cero : Cob 2) v

/-- **La estructura de Buss de un modelo de `LC`.** No es una instancia: ℕ ya tiene la suya, la estándar. -/
@[instance_reducible]
def estructuraBuss (M : Type) [LC.Structure M] : LB.Structure M where
  funMap f v := ap (progFun f) v
  RelMap r v := relLe r v

/-- Una estructura de Buss es **compatible** si sus símbolos son los programas. -/
structure Compatible (M : Type) [LC.Structure M] (S : LB.Structure M) : Prop where
  fun_eq : ∀ {n : ℕ} (f : Fun n) (v : Fin n → M), S.funMap f v = ap (progFun f) v
  rel_iff : ∀ v : Fin 2 → M, S.RelMap Rel.le v ↔ ap Cob.resta v = ap (Cob.cero : Cob 2) v

theorem compatible_buss (M : Type) [LC.Structure M] : Compatible M (estructuraBuss M) :=
  ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩

/-- La estructura estándar de ℕ es compatible. -/
theorem compatible_nat : Compatible ℕ (inferInstance : LB.Structure ℕ) :=
  ⟨fun f v => by cases f <;> rfl, fun v => by
    change v 0 ≤ v 1 ↔ v 0 - v 1 = 0
    omega⟩

/-! ## La traducción -/

/-- Los términos de Buss como programas. Las variables libres se leen por `ρ`; las ligadas van después. -/
def trT {α : Type} {a n : ℕ} (ρ : α → Fin a) : LB.Term (α ⊕ Fin n) → Cob (a + n)
  | .var (.inl x) => .proy (Fin.castAdd n (ρ x))
  | .var (.inr j) => .proy (Fin.natAdd a j)
  | .func f ts => .comp (progFun f) fun i => trT ρ (ts i)

/-- Las fórmulas sin cuantificadores de Buss como enunciados. Lo cuantificado se traduce a cualquier cosa: solo se
usa para fórmulas sin cuantificadores. -/
def trF {α : Type} {a : ℕ} (ρ : α → Fin a) : {n : ℕ} → LB.BoundedFormula α n → Enunciado (a + n)
  | _, .falsum => .no (.ec .cero .cero)
  | _, .equal t u => .ec (trT ρ t) (trT ρ u)
  | _, .rel R ts => match R with
    | .le => .ec (.comp Cob.resta fun i => trT ρ (ts i)) (.comp (Cob.cero : Cob 2) fun i => trT ρ (ts i))
  | _, .imp φ ψ => .entonces (trF ρ φ) (trF ρ ψ)
  | _, .all _ => .no (.ec .cero .cero)

section Traduccion

variable {M : Type} [LC.Structure M] [M ⊨ TC]

theorem realize_trT (S : LB.Structure M) (hS : Compatible M S) {α : Type} {a n : ℕ} (ρ : α → Fin a)
    (u : Fin a → M) (xs : Fin n → M) (t : LB.Term (α ⊕ Fin n)) :
    @Term.realize LB M S _ (Sum.elim (u ∘ ρ) xs) t = ap (trT ρ t) (Fin.append u xs) := by
  induction t with
  | var x =>
    rcases x with x | j
    · change u (ρ x) = ap (Cob.proy (Fin.castAdd n (ρ x))) (Fin.append u xs)
      rw [ap_proy, Fin.append_left]
    · change xs j = ap (Cob.proy (Fin.natAdd a j)) (Fin.append u xs)
      rw [ap_proy, Fin.append_right]
  | func f ts ih =>
    simp only [Term.realize, trT, ap_comp, ih]
    exact hS.fun_eq f _

/-- **La traducción vale donde vale el original**, para fórmulas sin cuantificadores. -/
theorem realize_trF (S : LB.Structure M) (hS : Compatible M S) {α : Type} {a n : ℕ} (ρ : α → Fin a)
    (u : Fin a → M) (xs : Fin n → M) {φ : LB.BoundedFormula α n} (hφ : φ.IsQF) :
    @BoundedFormula.Realize LB M S _ _ φ (u ∘ ρ) xs ↔ (trF ρ φ).Vale (Fin.append u xs) := by
  induction hφ with
  | falsum => simp [trF, Enunciado.Vale, BoundedFormula.Realize]
  | of_isAtomic h =>
    rcases h with ⟨t, u'⟩ | ⟨R, ts⟩
    · change @Term.realize LB M S _ (Sum.elim (u ∘ ρ) xs) t = @Term.realize LB M S _ (Sum.elim (u ∘ ρ) xs) u' ↔
        ap (trT ρ t) (Fin.append u xs) = ap (trT ρ u') (Fin.append u xs)
      rw [realize_trT S hS, realize_trT S hS]
    · cases R
      change S.RelMap Rel.le (fun i => @Term.realize LB M S _ (Sum.elim (u ∘ ρ) xs) (ts i)) ↔
        ap (Cob.comp Cob.resta fun i => trT ρ (ts i)) (Fin.append u xs) =
          ap (Cob.comp (Cob.cero : Cob 2) fun i => trT ρ (ts i)) (Fin.append u xs)
      simp only [realize_trT S hS, ap_comp]
      exact hS.rel_iff _
  | imp _ _ ih₁ ih₂ => simp only [BoundedFormula.Realize, trF, Enunciado.Vale, ih₁, ih₂]

end Traduccion

/-- Todo vector de `0 + n` lugares es el `append` del vacío y su parte derecha. -/
theorem append_vacio {M : Type} {n : ℕ} (w : Fin (0 + n) → M) :
    w = Fin.append (Fin.elim0 : Fin 0 → M) (fun j => w (Fin.natAdd 0 j)) := by
  funext k
  refine Fin.addCases (fun i => i.elim0) (fun j => ?_) k
  rw [Fin.append_right]

/-- **Lo universal verdadero en ℕ vale en todo modelo de `TC`**, leído con la estructura de Buss inducida. -/
theorem universal_vale {M : Type} [LC.Structure M] [M ⊨ TC] :
    ∀ {n : ℕ} {φ : LB.BoundedFormula Empty n}, φ.IsUniversal →
      (∀ xs : Fin n → ℕ, φ.Realize Empty.elim xs) →
      ∀ xs : Fin n → M, @BoundedFormula.Realize LB M (estructuraBuss M) _ _ φ Empty.elim xs := by
  let _ : LB.Structure M := estructuraBuss M
  intro n φ hU
  induction hU with
  | of_isQF hqf =>
    intro hN xs
    have hv : ∀ w : Fin (0 + _) → ℕ, (trF (a := 0) Empty.elim _).Vale w := fun w => by
      rw [append_vacio w]
      have := (realize_trF (M := ℕ) inferInstance compatible_nat Empty.elim Fin.elim0
        (fun j => w (Fin.natAdd 0 j)) hqf).mp
      exact this (by convert hN _)
    have := (realize_trF (estructuraBuss M) (compatible_buss M) Empty.elim Fin.elim0 xs hqf).mpr
      (Enunciado.transferir _ hv _)
    convert this
  | all _ ih =>
    intro hN xs
    rw [BoundedFormula.realize_all]
    intro x
    refine ih (fun ys => ?_) _
    have := hN (Fin.init ys)
    rw [BoundedFormula.realize_all] at this
    have h := this (ys (Fin.last _))
    rwa [Fin.snoc_init_self] at h

/-- Un enunciado vale si y solo si vale con cualquier lectura de sus (inexistentes) variables. -/
theorem realize_sentence_iff {N : Type} [LB.Structure N] (σ : LB.Sentence) (v : Empty → N) (xs : Fin 0 → N) :
    BoundedFormula.Realize σ v xs ↔ N ⊨ σ := by
  rw [Subsingleton.elim v default, Subsingleton.elim xs default]; rfl

/-! ## Los BASIC -/

theorem isQF_inf {α : Type} {n : ℕ} {φ ψ : LB.BoundedFormula α n} (h₁ : φ.IsQF) (h₂ : ψ.IsQF) :
    (φ ⊓ ψ).IsQF := (h₁.imp h₂.not).not

theorem isQF_sup {α : Type} {n : ℕ} {φ ψ : LB.BoundedFormula α n} (h₁ : φ.IsQF) (h₂ : ψ.IsQF) :
    (φ ⊔ ψ).IsQF := h₁.not.imp h₂

theorem isQF_iff {α : Type} {n : ℕ} {φ ψ : LB.BoundedFormula α n} (h₁ : φ.IsQF) (h₂ : ψ.IsQF) :
    (φ.iff ψ).IsQF := isQF_inf (h₁.imp h₂) (h₂.imp h₁)

/-- Para probar que una fórmula de Buss escrita con `∀`, `⇔`, `⊓`, `⊔`, `∼`, `⟹` es universal. -/
macro "universal" : tactic =>
  `(tactic| (repeat' apply BoundedFormula.IsUniversal.all
             apply BoundedFormula.IsUniversal.of_isQF
             repeat' first
               | apply isQF_iff | apply isQF_inf | apply isQF_sup | apply BoundedFormula.IsQF.not
               | apply BoundedFormula.IsQF.imp | exact BoundedFormula.IsQF.falsum
               | exact (BoundedFormula.IsAtomic.equal _ _).isQF | exact (BoundedFormula.IsAtomic.rel _ _).isQF))

open Acotada in
theorem basic_universal : ∀ σ ∈ teoriaBASIC, σ.IsUniversal := by
  simp only [teoriaBASIC, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> universal

/-- **Todo modelo de `TC` cumple los 32 axiomas BASIC**, con la estructura de Buss inducida. -/
theorem esModeloBASIC (M : Type) [LC.Structure M] [M ⊨ TC] :
    @Acotada.EsModeloBASIC M (estructuraBuss M) := by
  let _ : LB.Structure M := estructuraBuss M
  rw [← Acotada.modelo_basic_iff]
  have hN : ℕ ⊨ Acotada.teoriaBASIC := (Acotada.modelo_basic_iff (M := ℕ)).mpr Acotada.nat_esModeloBASIC
  refine (Theory.model_iff _).mpr fun σ hσ => ?_
  have h := universal_vale (M := M) (basic_universal σ hσ)
    (fun xs => (realize_sentence_iff σ _ xs).mpr (Theory.realize_sentence_of_mem (M := ℕ) _ hσ)) Fin.elim0
  exact (realize_sentence_iff σ _ _).mp h

end Cobham
end Sagitta.Map
