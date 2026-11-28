import Sagitta.Map.SigmaFagin.Traduccion

/-!
# Fase B de Σᵇ₁ = NP: el ensamble existencial de segundo orden

Tercera pieza de la fase B del plan, sobre `Traduccion.lean` (la parte de primer orden) y
`Bits.lean` (las relaciones como números). Una sentencia existencial de segundo orden `∃ R₁ … Rₖ φ`, sobre el
vocabulario numérico (`LNum`: `≤`, `BIT`, `0`, `1`, `máx`) más las variables de relación, vale en el universo
`[0, |x|)` si y solo si hay **números** `y₁, …, yₖ`, cada `yᵢ < 2^(N^{kᵢ})`, que hacen verdadera la traducción `Σᵇ₁` de
`φ`. Las variables de relación pasan a ser variables libres de S¹₂ (los códigos), y la pertenencia es `pertF`.

## Lo que se prueba

* `LVar arity`: las variables de relación, una copia del `ESO.varLanguage` de cslib-frontier (mismas funciones vacías,
  mismas relaciones `{i // arity i = n}`, misma semántica `x ∘ Fin.cast _ ∈ R i`). Se copia para no importar módulos de
  cslib-frontier que no están compilados en esta máquina.
* `atomosE`: los átomos del lenguaje `LNum.sum (LVar arity)`, con la entrada `x` como variable libre `none` y el código de
  `Rᵢ` como variable libre `some i`. `atomosE_correctos`: son correctos si los códigos codifican las relaciones.
* **`eso_iff`**: `(∃ R, φ vale en Fin N con R) ↔ ∃ y, (∀ i, y i < 2^(N^{kᵢ})) ∧ (tr φ true) vale con `x` y los `y`.
  Con `lt_cotaRel` (fase A), cada `yᵢ` queda debajo del término `cotaRel kᵢ x` (`eso_iff_cota`).

## Lo que no se prueba aquí

* Cerrar los `∃ yᵢ ≤ cotaRel kᵢ x` dentro de una sola fórmula de S¹₂ (hay que ordenar las variables de relación; es
  sintaxis, no matemática).
* El lenguaje de entrada (las letras de la palabra) y el puente con el `language L` y el `ESO.Sentence` de cslib-frontier
  (fase C), y la vuelta `Σᵇ₁ ⊆ NP` (fase D).
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace SigmaFagin

open Acotada Acotada.Parikh

variable {ι : Type} (arity : ι → ℕ)

/-- Las variables de relación (copia del `ESO.varLanguage` de cslib-frontier). -/
def LVar : Language.{0, 0} where
  Functions _ := Empty
  Relations n := {i : ι // arity i = n}

/-- La estructura que interpreta la variable `i` como `R i`. -/
@[instance_reducible]
def varEstr {M : Type} (R : ∀ i, Set (Fin (arity i) → M)) : (LVar arity).Structure M where
  funMap f _ := Empty.elim f
  RelMap r x := x ∘ Fin.cast r.2 ∈ R r.1

/-- El lenguaje de la matriz: el numérico más las variables de relación. -/
abbrev LEso : Language.{0, 0} := LNum.sum (LVar arity)

/-- La estructura de la matriz en `Fin N`. -/
@[instance_reducible]
def estrE (N : ℕ) (hN : 2 ≤ N) (R : ∀ i, Set (Fin (arity i) → Fin N)) : (LEso arity).Structure (Fin N) :=
  @Language.sumStructure _ _ _ (numEstructura N hN) (varEstr arity R)

variable {arity}

/-- La entrada: la variable libre `none`. -/
abbrev entrada : L.Term (Option ι) := Term.var none

/-- Los términos de la matriz (solo variables y las tres constantes numéricas). -/
def termE : ∀ {n : ℕ}, (LEso arity).Term (Empty ⊕ Fin n) → L.Term (Option ι ⊕ Fin n)
  | _, .var (Sum.inl e) => e.elim
  | _, .var (Sum.inr i) => Term.var (Sum.inr i)
  | _, .func (Sum.inl NumFun.cero) _ => tC
  | _, .func (Sum.inl NumFun.uno) _ => tU
  | _, .func (Sum.inl NumFun.max) _ => tLg (tMt (baja entrada))
  | _, .func (Sum.inr f) _ => Empty.elim f

/-- Las relaciones numéricas sobre términos de S¹₂. -/
def posNumT {β : Type} {m : ℕ} : ∀ {l : ℕ}, NumRel l → (Fin l → L.Term (β ⊕ Fin m)) → L.BoundedFormula β m
  | _, .le, as => leF (as 0) (as 1)
  | _, .bit, as => bitF (as 1) (as 0)

/-- Sus negaciones. -/
def negNumT {β : Type} {m : ℕ} : ∀ {l : ℕ}, NumRel l → (Fin l → L.Term (β ⊕ Fin m)) → L.BoundedFormula β m
  | _, .le, as => leF (tSc (as 1)) (as 0)
  | _, .bit, as => noBitF (as 1) (as 0)

theorem posNumT_sigma {β : Type} {m : ℕ} : ∀ {l : ℕ} (R : NumRel l) (as : Fin l → L.Term (β ⊕ Fin m)),
    EsSigma1 (posNumT R as)
  | _, .le, _ => EsSigma1.aguda (aguda_leF _ _)
  | _, .bit, _ => bitF_sigma _ _

theorem negNumT_sigma {β : Type} {m : ℕ} : ∀ {l : ℕ} (R : NumRel l) (as : Fin l → L.Term (β ⊕ Fin m)),
    EsSigma1 (negNumT R as)
  | _, .le, _ => EsSigma1.aguda (aguda_leF _ _)
  | _, .bit, _ => noBitF_sigma _ _

/-- La pertenencia a la variable de relación `i`: el bit `idx N a` de su código. -/
def posE {n : ℕ} : ∀ {l : ℕ}, (LEso arity).Relations l → (Fin l → (LEso arity).Term (Empty ⊕ Fin n)) →
    L.BoundedFormula (Option ι) n
  | _, Sum.inl R, ts => posNumT R (fun j => termE (ts j))
  | _, Sum.inr r, ts => pertF (Term.var (Sum.inl (some r.1))) (tLong (baja entrada)) (fun j => termE (ts j))

/-- La no pertenencia. -/
def negE {n : ℕ} : ∀ {l : ℕ}, (LEso arity).Relations l → (Fin l → (LEso arity).Term (Empty ⊕ Fin n)) →
    L.BoundedFormula (Option ι) n
  | _, Sum.inl R, ts => negNumT R (fun j => termE (ts j))
  | _, Sum.inr r, ts => noPertF (Term.var (Sum.inl (some r.1))) (tLong (baja entrada)) (fun j => termE (ts j))

variable (arity) in
/-- **Los átomos de la matriz.** -/
def atomosE : Atomos (LEso arity) (Option ι) where
  term := termE
  pos := posE
  neg := negE
  pos_sigma := fun R _ => match R with
    | Sum.inl R => posNumT_sigma R _
    | Sum.inr _ => (pertF_sigma _ _ _).1
  neg_sigma := fun R _ => match R with
    | Sum.inl R => negNumT_sigma R _
    | Sum.inr _ => (pertF_sigma _ _ _).2

/-! ## La corrección -/

section Correccion

variable (v : Option ι → ℕ) (hN : 2 ≤ tam entrada v) (R : ∀ i, Set (Fin (arity i) → Fin (tam entrada v)))

/-- Los códigos codifican las relaciones. -/
def Codifican : Prop :=
  ∀ i (a : Fin (arity i) → Fin (tam entrada v)),
    (v (some i)).testBit (idx (tam entrada v) (Fin.val ∘ a)) = true ↔ a ∈ R i

theorem termE_realize (e : Empty → Fin (tam entrada v)) :
    ∀ {n : ℕ} (t : (LEso arity).Term (Empty ⊕ Fin n)) (xs : Fin n → Fin (tam entrada v)),
      (termE t).realize (Sum.elim v (Fin.val ∘ xs)) =
        (@Term.realize (LEso arity) (Fin (tam entrada v)) (estrE arity _ hN R) _ (Sum.elim e xs) t).val
  | _, .var (Sum.inl x), _ => x.elim
  | _, .var (Sum.inr i), xs => rfl
  | _, .func (Sum.inl NumFun.cero) _, xs => rfl
  | _, .func (Sum.inl NumFun.uno) _, xs => rfl
  | _, .func (Sum.inl NumFun.max) _, xs => by
    have h := size_mitad (x := v none) (by intro h0; simp [tam, h0] at hN)
    rw [show termE (Term.func (Sum.inl NumFun.max : (LEso arity).Functions 0) _ : (LEso arity).Term (Empty ⊕ Fin _)) =
      tLg (tMt (baja entrada)) from rfl, rn_tLg, rn_tMt, realize_baja]
    show _ = tam entrada v - 1
    simp only [tam] at hN ⊢
    exact (by simp at h ⊢; omega)
  | _, .func (Sum.inr f) _, _ => Empty.elim f

variable {v hN R}

/-- **Los átomos de la matriz son correctos** si los códigos codifican las relaciones. -/
theorem atomosE_correctos (hc : Codifican v R) (e : Empty → Fin (tam entrada v)) :
    @Atomos.Correctos (LEso arity) (Option ι) (atomosE arity) entrada v (estrE arity _ hN R) e := by
  let _ := estrE arity _ hN R
  have hT : ∀ {n : ℕ} (t : (LEso arity).Term (Empty ⊕ Fin n)) (xs : Fin n → Fin (tam entrada v)),
      (termE t).realize (Sum.elim v (Fin.val ∘ xs)) = (t.realize (Sum.elim e xs)).val :=
    fun t xs => termE_realize v hN R e t xs
  refine ⟨fun t xs => hT t xs, fun {n l} Q ts xs => ?_, fun {n l} Q ts xs => ?_⟩
  · rcases Q with Q | ⟨i, rfl⟩
    · cases Q with
      | le =>
        show (leF _ _).Realize v _ ↔ _
        rw [realize_leF_nat, hT, hT]
        exact Fin.le_iff_val_le_val.symm
      | bit =>
        show (bitF _ _).Realize v _ ↔ _
        rw [realize_bitF, hT, hT]
        rfl
    · show (pertF _ _ _).Realize v _ ↔ _
      rw [realize_pertF]
      change (v (some i)).testBit (idx (tam entrada v)
        (fun j => (termE (ts j)).realize (Sum.elim v (Fin.val ∘ xs)))) = true ↔ _
      simp only [hT]
      exact hc i (fun j => (ts j).realize (Sum.elim e xs))
  · rcases Q with Q | ⟨i, rfl⟩
    · cases Q with
      | le =>
        show (leF _ _).Realize v _ ↔ _
        rw [realize_leF_nat, rn_tSc, hT, hT]
        show _ ↔ ¬ ((_ : Fin (tam entrada v)) ≤ _)
        rw [Fin.not_le, Fin.lt_def]
        dsimp only
        omega
      | bit =>
        show (noBitF _ _).Realize v _ ↔ _
        rw [realize_noBitF, hT, hT]
        show _ ↔ ¬ (_ = true)
        simp
    · show (noPertF _ _ _).Realize v _ ↔ _
      rw [realize_noPertF]
      change (v (some i)).testBit (idx (tam entrada v)
        (fun j => (termE (ts j)).realize (Sum.elim v (Fin.val ∘ xs)))) = false ↔ _
      simp only [hT]
      rw [← Bool.not_eq_true]
      exact not_congr (hc i (fun j => (ts j).realize (Sum.elim e xs)))

end Correccion

/-! ## El ensamble -/

theorem vacio_val' (N : ℕ) : (Fin.val ∘ (default : Fin 0 → Fin N)) = default := funext fun i => i.elim0

/-- **Fagin, la mitad sintáctica, en ℕ.** Una sentencia existencial de segundo orden sobre `LNum` vale en `Fin N`
(`N = |x|`) si y solo si hay códigos `yᵢ < 2^(N^{kᵢ})` que hacen verdadera su traducción `Σᵇ₁`. -/
theorem eso_iff (φ : (LEso arity).BoundedFormula Empty 0) (X : ℕ) (hN : 2 ≤ Nat.size X) :
    (∃ R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)),
        @BoundedFormula.Realize (LEso arity) (Fin (Nat.size X)) (estrE arity _ hN R) _ _ φ default default) ↔
      ∃ y : ι → ℕ, (∀ i, y i < 2 ^ (Nat.size X ^ arity i)) ∧
        (tr (atomosE arity) entrada φ true).Realize (fun o => o.elim X y) default := by
  have htam : ∀ y : ι → ℕ, tam (entrada : L.Term (Option ι)) (fun o => o.elim X y) = Nat.size X := fun _ => rfl
  constructor
  · rintro ⟨R, hR⟩
    have hcod := fun i => relacion_codificada (Nat.size X) (arity i)
      (fun a => ∃ h : ∀ j, a j < Nat.size X, (fun j => (⟨a j, h j⟩ : Fin (Nat.size X))) ∈ R i)
    choose y hy hyR using hcod
    refine ⟨y, hy, ?_⟩
    have hc : Codifican (fun o => o.elim X y) R := by
      intro i a
      exact (hyR i (Fin.val ∘ a) (fun j => (a j).isLt)).trans
        ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun j => (a j).isLt, h⟩⟩
    let _ : (LEso arity).Structure (Fin (tam entrada (fun o => o.elim X y))) := estrE arity _ hN R
    have := (realize_tr (atomosE_correctos (v := fun o => o.elim X y) (hN := hN) hc default) φ default).1
    rw [vacio_val'] at this
    exact this.2 hR
  · rintro ⟨y, -, hT⟩
    let R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)) :=
      fun i => {a | (y i).testBit (idx (Nat.size X) (Fin.val ∘ a)) = true}
    refine ⟨R, ?_⟩
    have hc : Codifican (fun o => o.elim X y) R := fun i a => Iff.rfl
    let _ : (LEso arity).Structure (Fin (tam entrada (fun o => o.elim X y))) := estrE arity _ hN R
    have := (realize_tr (atomosE_correctos (v := fun o => o.elim X y) (hN := hN) hc default) φ default).1
    rw [vacio_val'] at this
    exact this.1 hT

/-- Lo mismo con la cota como término de S¹₂: cada código cabe debajo de `cotaRel kᵢ x`. -/
theorem eso_iff_cota (φ : (LEso arity).BoundedFormula Empty 0) (X : ℕ) (hN : 2 ≤ Nat.size X) :
    (∃ R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)),
        @BoundedFormula.Realize (LEso arity) (Fin (Nat.size X)) (estrE arity _ hN R) _ _ φ default default) →
      ∃ y : ι → ℕ, (∀ i, y i ≤ (cotaRel (arity i) (Term.var 0 : L.Term (Fin 1))).realize ![X]) ∧
        (tr (atomosE arity) entrada φ true).Realize (fun o => o.elim X y) default := by
  intro h
  obtain ⟨y, hy, hT⟩ := (eso_iff φ X hN).1 h
  exact ⟨y, fun i => lt_cotaRel ![X] _ _ _ (hy i), hT⟩

/-! ## Controles -/

/-- «Existe una relación unaria `R` que contiene al 0 y no al máximo»: verdadera en todo universo con dos elementos. -/
def ejemploR : (LEso (fun _ : Unit => 1)).BoundedFormula Empty 0 :=
  (BoundedFormula.rel (Sum.inr ⟨(), rfl⟩ : (LEso (fun _ : Unit => 1)).Relations 1)
      ![Term.func (Sum.inl NumFun.cero) Fin.elim0]) ⊓
    (BoundedFormula.rel (Sum.inr ⟨(), rfl⟩ : (LEso (fun _ : Unit => 1)).Relations 1)
      ![Term.func (Sum.inl NumFun.max) Fin.elim0]).not

example : EsSigma1 (tr (atomosE (fun _ : Unit => 1)) entrada ejemploR true) := tr_sigma _ _ _ _

theorem cuatro : 2 ≤ Nat.size 4 := by decide

/-- Con la entrada `X = 4` (`N = 3`), la traducción es satisfacible: `R = {0}` da los códigos. -/
example : ∃ y : Unit → ℕ, (∀ i, y i < 2 ^ (Nat.size 4 ^ 1)) ∧
    (tr (atomosE (fun _ : Unit => 1)) entrada ejemploR true).Realize (fun o => o.elim 4 y) default := by
  refine (eso_iff ejemploR 4 cuatro).1 ⟨fun _ => {a | (a 0).val = 0}, ?_⟩
  let _ := estrE (fun _ : Unit => 1) _ cuatro (fun _ => {a | (a 0).val = 0})
  simp only [ejemploR, BoundedFormula.realize_inf, BoundedFormula.realize_not]
  refine ⟨rfl, fun h => ?_⟩
  change (Nat.size 4 - 1) = 0 at h
  exact absurd h (by decide)

/-- `R(0) ∧ ¬R(0)`: ningún código hace verdadera su traducción. -/
def ejemploMal : (LEso (fun _ : Unit => 1)).BoundedFormula Empty 0 :=
  (BoundedFormula.rel (Sum.inr ⟨(), rfl⟩ : (LEso (fun _ : Unit => 1)).Relations 1)
      ![Term.func (Sum.inl NumFun.cero) Fin.elim0]) ⊓
    (BoundedFormula.rel (Sum.inr ⟨(), rfl⟩ : (LEso (fun _ : Unit => 1)).Relations 1)
      ![Term.func (Sum.inl NumFun.cero) Fin.elim0]).not

example : ¬ ∃ y : Unit → ℕ, (∀ i, y i < 2 ^ (Nat.size 4 ^ 1)) ∧
    (tr (atomosE (fun _ : Unit => 1)) entrada ejemploMal true).Realize (fun o => o.elim 4 y) default := by
  intro h
  obtain ⟨R, hR⟩ := (eso_iff ejemploMal 4 cuatro).2 h
  let _ := estrE (fun _ : Unit => 1) _ cuatro R
  simp only [ejemploMal, BoundedFormula.realize_inf, BoundedFormula.realize_not] at hR
  exact hR.2 hR.1

/-! Mutante (probado en /tmp/claude-noche/MutanteEnsamble.lean, 25 nov 2026): con los argumentos de `BIT` al revés
(`bitF (as 0) (as 1)`, «el bit `x` de `i`» en lugar de «el bit `i` de `x`»), Lean rechaza el caso `bit` de
`atomosE_correctos` (el `rfl` no cierra): el orden de cslib-frontier, `bit x i` = bit `i` de `x`, es el que se tradujo. -/

end SigmaFagin
end Sagitta.Map
