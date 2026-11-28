import Sagitta.Map.SigmaFagin.Bits

/-!
# Fase B de Σᵇ₁ = NP (núcleo): traducir primer orden sobre `[0, |x|)` a `Σᵇ₁` sobre ℕ

Segunda fase del plan. Una sentencia existencial de segundo orden es `∃ R₁ … Rₖ φ`, con `φ` de
primer orden en el lenguaje de entrada más las variables de relación. Fase A dio los ladrillos: las relaciones como
números (`relacion_acotada`) y la pertenencia como fórmula `Σᵇ₁` con negación `Σᵇ₁` (`pertF`, `noPertF`). Aquí se
traduce la parte de primer orden.

## La traducción

El universo es `[0, N)` con `N = |u|`, donde `u` es un término en las variables libres (en Fagin sobre palabras, `u`
es la entrada). Los elementos se leen como números menores que `N`. Como `N` es un largo, los cuantificadores son
**agudos**: `∀ z ≤ |u| (z < N → …)` y `∃ z ≤ |u| (z < N ∧ …)`, que `Σᵇ₁` admite (Buss, cláusula b).

La negación no es gratis en `Σᵇ₁`: la negación de una `Σᵇ₁` es `Πᵇ₁`. Por eso se traduce con **polaridad**: `tr φ true`
dice `φ` y `tr φ false` dice `¬φ`, las dos `Σᵇ₁`. La implicación cambia la polaridad del antecedente:
`tr (φ → ψ) true = tr φ false ∨ tr ψ true`, `tr (φ → ψ) false = tr φ true ∧ tr ψ false`. Lo atómico lo da el que usa la
traducción (`Atomos`): un término de S¹₂ por cada término, y por cada relación una fórmula positiva y una negativa, las
dos `Σᵇ₁`. Es exactamente lo que fase A provee para las variables de relación (`pertF`, `noPertF`) y para el `BIT` del
vocabulario numérico de cslib-frontier (`bitF`, `noBitF`).

## Lo que se prueba

* `tr_sigma`: `tr φ b` es `Σᵇ₁` para toda fórmula `φ` y toda polaridad `b`.
* **`realize_tr`**: si los átomos dicen lo que deben (`Atomos.Correctos`), en el universo `Fin N`, `tr φ true` vale
  exactamente cuando `φ` vale y `tr φ false` exactamente cuando no vale.
* `atomosNumericos` y `numericos_correctos`: los átomos del vocabulario numérico de cslib-frontier (`≤` y `BIT`, con las
  constantes `0`, `1` y `máx = |⌊x/2⌋|`), en un lenguaje propio que lo copia (`LNum`), con su corrección.

## Lo que no se prueba aquí

* Las variables de relación como átomos ya están en fase A, pero no se armó todavía el ensamble
  «`ESO.Sentence.Realize` ⇔ hay códigos `yᵢ ≤ cotaRel kᵢ x` con `tr` verdadera»: hace falta enumerar las variables de
  relación (un tipo finito cualquiera en cslib) y cerrar los `∃ yᵢ` acotados. Es lo siguiente de la fase B.
* El lenguaje de entrada de las palabras y el puente con el `numeroDe` de `SigmaNP.lean` (fase C), y la vuelta (fase D).
* `LNum` copia a mano el vocabulario numérico de cslib-frontier en vez de importarlo: el ensamble con su `language L`
  queda para la fase C.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace SigmaFagin

open Acotada Acotada.Parikh

variable {L' : Language.{0, 0}} {α : Type}

/-- Lo atómico de un lenguaje `L'`, traducido a S¹₂: un término por cada término, y para cada relación una fórmula
que la afirma y otra que la niega, las dos `Σᵇ₁`. -/
structure Atomos (L' : Language.{0, 0}) (α : Type) where
  term : ∀ {n : ℕ}, L'.Term (Empty ⊕ Fin n) → L.Term (α ⊕ Fin n)
  pos : ∀ {n l : ℕ}, L'.Relations l → (Fin l → L'.Term (Empty ⊕ Fin n)) → L.BoundedFormula α n
  neg : ∀ {n l : ℕ}, L'.Relations l → (Fin l → L'.Term (Empty ⊕ Fin n)) → L.BoundedFormula α n
  pos_sigma : ∀ {n l : ℕ} (R : L'.Relations l) (ts : Fin l → L'.Term (Empty ⊕ Fin n)), EsSigma1 (pos R ts)
  neg_sigma : ∀ {n l : ℕ} (R : L'.Relations l) (ts : Fin l → L'.Term (Empty ⊕ Fin n)), EsSigma1 (neg R ts)

/-- El término `u`, con las variables ligadas que haya. -/
def baja {n : ℕ} (u : L.Term α) : L.Term (α ⊕ Fin n) := u.relabel Sum.inl

/-- La guarda «`z < N`», con `N = |u|`, para la variable recién ligada `z`. -/
def guarda {n : ℕ} (u : L.Term α) : L.BoundedFormula α (n + 1) := leF (tSc nueva) (tLong (baja u))

/-- **La traducción con polaridad.** `tr φ true` dice `φ`; `tr φ false` dice `¬φ`. -/
def tr (A : Atomos L' α) (u : L.Term α) : ∀ {n : ℕ}, L'.BoundedFormula Empty n → Bool → L.BoundedFormula α n
  | _, .falsum, true => BoundedFormula.falsum
  | _, .falsum, false => BoundedFormula.falsum.imp BoundedFormula.falsum
  | _, .equal t s, true => BoundedFormula.equal (A.term t) (A.term s)
  | _, .equal t s, false => (BoundedFormula.equal (A.term t) (A.term s)).not
  | _, .rel R ts, true => A.pos R ts
  | _, .rel R ts, false => A.neg R ts
  | _, .imp φ ψ, true => tr A u φ false ⊔ tr A u ψ true
  | _, .imp φ ψ, false => tr A u φ true ⊓ tr A u ψ false
  | _, .all φ, true => paraTodoAcotado (tLong (baja u)) ((guarda u).imp (tr A u φ true))
  | _, .all φ, false => existeAcotado (tLong (baja u)) (guarda u ⊓ tr A u φ false)

theorem guarda_aguda {n : ℕ} (u : L.Term α) : EsAguda (guarda (n := n) u) := aguda_leF _ _

/-- **La traducción es `Σᵇ₁`**, en las dos polaridades. -/
theorem tr_sigma (A : Atomos L' α) (u : L.Term α) :
    ∀ {n : ℕ} (φ : L'.BoundedFormula Empty n) (b : Bool), EsSigma1 (tr A u φ b)
  | _, .falsum, true => EsSigma1.aguda EsAguda.falso
  | _, .falsum, false => EsSigma1.aguda (aguda_not EsAguda.falso)
  | _, .equal _ _, true => EsSigma1.aguda (EsAguda.igual _ _)
  | _, .equal _ _, false => EsSigma1.aguda (aguda_not (EsAguda.igual _ _))
  | _, .rel R ts, true => A.pos_sigma R ts
  | _, .rel R ts, false => A.neg_sigma R ts
  | _, .imp φ ψ, true => EsSigma1.o (tr_sigma A u φ false) (tr_sigma A u ψ true)
  | _, .imp φ ψ, false => EsSigma1.y (tr_sigma A u φ true) (tr_sigma A u ψ false)
  | _, .all φ, true =>
      EsSigma1.todoAgudo _ (EsSigma1.imp (EsPi1.aguda (guarda_aguda u)) (tr_sigma A u φ true))
  | _, .all φ, false =>
      EsSigma1.existe _ (EsSigma1.y (EsSigma1.aguda (guarda_aguda u)) (tr_sigma A u φ false))

/-! ## El significado -/

section Significado

variable (A : Atomos L' α) (u : L.Term α) (v : α → ℕ)

/-- El tamaño del universo: `N = |u|`. -/
def tam : ℕ := Nat.size (u.realize v)

omit A in
theorem rn_tLong {β : Type} (t : L.Term β) (w : β → ℕ) : (tLong t).realize w = Nat.size (t.realize w) := rfl

omit A in
theorem realize_baja {n : ℕ} (xs : Fin n → ℕ) : (baja u).realize (Sum.elim v xs) = u.realize v := by
  rw [baja, Term.realize_relabel, Sum.elim_comp_inl]

theorem realize_guarda {n : ℕ} (xs : Fin n → ℕ) (z : ℕ) :
    (guarda (n := n) u).Realize v (Fin.snoc xs z) ↔ z < tam u v := by
  simp only [guarda, realize_leF_nat, rn_tSc, realize_nueva, rn_tLong, realize_baja, tam]
  omega

/-- **Los átomos son correctos** en la estructura `Fin (tam u v)` (con `e` la asignación vacía de libres). -/
structure Atomos.Correctos [L'.Structure (Fin (tam u v))] (e : Empty → Fin (tam u v)) : Prop where
  term : ∀ {n : ℕ} (t : L'.Term (Empty ⊕ Fin n)) (xs : Fin n → Fin (tam u v)),
    (A.term t).realize (Sum.elim v (Fin.val ∘ xs)) = (t.realize (Sum.elim e xs)).val
  pos : ∀ {n l : ℕ} (R : L'.Relations l) (ts : Fin l → L'.Term (Empty ⊕ Fin n)) (xs : Fin n → Fin (tam u v)),
    (A.pos R ts).Realize v (Fin.val ∘ xs) ↔ Structure.RelMap R (fun i => (ts i).realize (Sum.elim e xs))
  neg : ∀ {n l : ℕ} (R : L'.Relations l) (ts : Fin l → L'.Term (Empty ⊕ Fin n)) (xs : Fin n → Fin (tam u v)),
    (A.neg R ts).Realize v (Fin.val ∘ xs) ↔ ¬ Structure.RelMap R (fun i => (ts i).realize (Sum.elim e xs))

variable {A u v}

/-- **La traducción dice lo mismo**, en las dos polaridades. -/
theorem realize_tr [L'.Structure (Fin (tam u v))] {e : Empty → Fin (tam u v)} (hA : A.Correctos u v e) :
    ∀ {n : ℕ} (φ : L'.BoundedFormula Empty n) (xs : Fin n → Fin (tam u v)),
      ((tr A u φ true).Realize v (Fin.val ∘ xs) ↔ φ.Realize e xs) ∧
      ((tr A u φ false).Realize v (Fin.val ∘ xs) ↔ ¬ φ.Realize e xs)
  | _, .falsum, xs => by
    simp [tr, BoundedFormula.Realize]
  | _, .equal t s, xs => by
    have h1 := hA.term t xs
    have h2 := hA.term s xs
    refine ⟨?_, ?_⟩
    · show (A.term t).realize _ = (A.term s).realize _ ↔ t.realize _ = s.realize _
      rw [h1, h2, Fin.val_inj]
    · show ¬ ((A.term t).realize _ = (A.term s).realize _) ↔ ¬ (t.realize _ = s.realize _)
      rw [h1, h2, Fin.val_inj]
  | _, .rel R ts, xs => ⟨hA.pos R ts xs, hA.neg R ts xs⟩
  | _, .imp φ ψ, xs => by
    obtain ⟨h1, h2⟩ := realize_tr hA φ xs
    obtain ⟨h3, h4⟩ := realize_tr hA ψ xs
    simp only [tr, BoundedFormula.realize_sup, BoundedFormula.realize_inf, BoundedFormula.realize_imp, h1, h2, h3,
      h4]
    constructor
    · constructor
      · rintro (h | h) hφ
        · exact absurd hφ h
        · exact h
      · intro h
        by_cases hφ : φ.Realize e xs
        · exact Or.inr (h hφ)
        · exact Or.inl hφ
    · constructor
      · rintro ⟨hφ, hψ⟩ h
        exact hψ (h hφ)
      · intro h
        by_cases hφ : φ.Realize e xs
        · exact ⟨hφ, fun hψ => h fun _ => hψ⟩
        · exact absurd (fun h' => absurd h' hφ) h
  | _, .all φ, xs => by
    have key : ∀ a : Fin (tam u v), Fin.val ∘ Fin.snoc xs a = Fin.snoc (Fin.val ∘ xs) a.val := fun a =>
      Fin.comp_snoc _ _ _
    simp only [tr, realize_paraTodo, realize_existe, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
      BoundedFormula.realize_all, le_nat, rn_tLong, realize_baja, realize_guarda]
    constructor
    · constructor
      · intro h a
        have := h a.val (by have := a.isLt; simp only [tam] at this; omega) a.isLt
        rw [← key, (realize_tr hA φ (Fin.snoc xs a)).1] at this
        exact this
      · intro h z _ hz
        have := (realize_tr hA φ (Fin.snoc xs ⟨z, hz⟩)).1
        rw [key] at this
        exact this.2 (h _)
    · constructor
      · rintro ⟨z, _, hz, h⟩ hall
        have := (realize_tr hA φ (Fin.snoc xs ⟨z, hz⟩)).2
        rw [key] at this
        exact this.1 h (hall _)
      · intro h
        push Not at h
        obtain ⟨a, ha⟩ := h
        refine ⟨a.val, by have := a.isLt; simp only [tam] at this; omega, a.isLt, ?_⟩
        have := (realize_tr hA φ (Fin.snoc xs a)).2
        rw [key] at this
        exact this.2 ha

end Significado

/-! ## Los átomos del vocabulario numérico -/

/-- Las constantes del vocabulario numérico de cslib-frontier (`Ordered.NumericFunction`): `0`, `1` y el máximo. -/
inductive NumFun : ℕ → Type
  | cero : NumFun 0
  | uno : NumFun 0
  | max : NumFun 0

/-- Las relaciones numéricas (`Ordered.NumericRelation`): el orden y `BIT`. -/
inductive NumRel : ℕ → Type
  | le : NumRel 2
  | bit : NumRel 2

/-- Una copia del vocabulario numérico de cslib-frontier. -/
abbrev LNum : Language.{0, 0} := ⟨NumFun, NumRel⟩

/-- La semántica de cslib-frontier (`numericStructure`): el máximo es `N − 1` y `bit x i` es el bit `i` de `x`. -/
@[instance_reducible]
def numEstructura (N : ℕ) (hN : 2 ≤ N) : LNum.Structure (Fin N) where
  funMap f _ := match f with
    | .cero => ⟨0, by omega⟩
    | .uno => ⟨1, by omega⟩
    | .max => ⟨N - 1, by omega⟩
  RelMap r x := match r with
    | .le => x 0 ≤ x 1
    | .bit => (x 0).val.testBit (x 1).val = true

/-- Los términos numéricos en S¹₂, con `u` la entrada: `máx = |⌊u/2⌋|`, que es `|u| − 1`. -/
def numTerm (u : L.Term α) : ∀ {n : ℕ}, LNum.Term (Empty ⊕ Fin n) → L.Term (α ⊕ Fin n)
  | _, .var (Sum.inl e) => e.elim
  | _, .var (Sum.inr i) => Term.var (Sum.inr i)
  | _, .func NumFun.cero _ => tC
  | _, .func NumFun.uno _ => tU
  | _, .func NumFun.max _ => tLg (tMt (baja u))

/-- Las fórmulas que afirman las relaciones numéricas. -/
def posNum (u : L.Term α) {n : ℕ} : ∀ {l : ℕ}, NumRel l → (Fin l → LNum.Term (Empty ⊕ Fin n)) → L.BoundedFormula α n
  | _, .le, ts => leF (numTerm u (ts 0)) (numTerm u (ts 1))
  | _, .bit, ts => bitF (numTerm u (ts 1)) (numTerm u (ts 0))

/-- Las fórmulas que las niegan. -/
def negNum (u : L.Term α) {n : ℕ} : ∀ {l : ℕ}, NumRel l → (Fin l → LNum.Term (Empty ⊕ Fin n)) → L.BoundedFormula α n
  | _, .le, ts => leF (tSc (numTerm u (ts 1))) (numTerm u (ts 0))
  | _, .bit, ts => noBitF (numTerm u (ts 1)) (numTerm u (ts 0))

theorem posNum_sigma (u : L.Term α) {n : ℕ} : ∀ {l : ℕ} (R : NumRel l) (ts : Fin l → LNum.Term (Empty ⊕ Fin n)),
    EsSigma1 (posNum u R ts)
  | _, .le, _ => EsSigma1.aguda (aguda_leF _ _)
  | _, .bit, _ => bitF_sigma _ _

theorem negNum_sigma (u : L.Term α) {n : ℕ} : ∀ {l : ℕ} (R : NumRel l) (ts : Fin l → LNum.Term (Empty ⊕ Fin n)),
    EsSigma1 (negNum u R ts)
  | _, .le, _ => EsSigma1.aguda (aguda_leF _ _)
  | _, .bit, _ => noBitF_sigma _ _

/-- Los átomos numéricos. -/
def atomosNumericos (u : L.Term α) : Atomos LNum α where
  term := numTerm u
  pos := fun R ts => posNum u R ts
  neg := fun R ts => negNum u R ts
  pos_sigma := fun R ts => posNum_sigma u R ts
  neg_sigma := fun R ts => negNum_sigma u R ts

theorem numTerm_realize (u : L.Term α) (v : α → ℕ) (hN : 2 ≤ tam u v) (e : Empty → Fin (tam u v)) :
    ∀ {n : ℕ} (t : LNum.Term (Empty ⊕ Fin n)) (xs : Fin n → Fin (tam u v)),
      (numTerm u t).realize (Sum.elim v (Fin.val ∘ xs)) =
        (@Term.realize LNum (Fin (tam u v)) (numEstructura _ hN) _ (Sum.elim e xs) t).val
  | _, .var (Sum.inl x), _ => x.elim
  | _, .var (Sum.inr i), xs => rfl
  | _, .func NumFun.cero _, xs => rfl
  | _, .func NumFun.uno _, xs => rfl
  | _, .func NumFun.max _, xs => by
    have h := size_mitad (x := u.realize v) (by intro h0; simp [tam, h0] at hN)
    rw [show numTerm u (Term.func (NumFun.max : LNum.Functions 0) _ : LNum.Term (Empty ⊕ Fin _)) =
      tLg (tMt (baja u)) from rfl, rn_tLg, rn_tMt, realize_baja]
    show _ = tam u v - 1
    simp only [tam] at hN ⊢
    omega

/-- **Los átomos numéricos son correctos.** -/
theorem numericos_correctos (u : L.Term α) (v : α → ℕ) (hN : 2 ≤ tam u v) (e : Empty → Fin (tam u v)) :
    @Atomos.Correctos LNum α (atomosNumericos u) u v (numEstructura _ hN) e := by
  let _ := numEstructura _ hN
  refine ⟨fun t xs => numTerm_realize u v hN e t xs, fun {n l} R ts xs => ?_, fun {n l} R ts xs => ?_⟩
  · cases R with
    | le =>
      show (leF _ _).Realize v _ ↔ _
      rw [realize_leF_nat, numTerm_realize u v hN e, numTerm_realize u v hN e]
      exact Fin.le_iff_val_le_val.symm
    | bit =>
      show (bitF _ _).Realize v _ ↔ _
      rw [realize_bitF, numTerm_realize u v hN e, numTerm_realize u v hN e]
      rfl
  · cases R with
    | le =>
      show (leF _ _).Realize v _ ↔ _
      rw [realize_leF_nat, rn_tSc, numTerm_realize u v hN e, numTerm_realize u v hN e]
      show _ ↔ ¬ (_ ≤ _)
      rw [Fin.not_le, Fin.lt_def]
      dsimp only
      omega
    | bit =>
      show (noBitF _ _).Realize v _ ↔ _
      rw [realize_noBitF, numTerm_realize u v hN e, numTerm_realize u v hN e]
      show _ ↔ ¬ (_ = true)
      simp

/-! ## Controles -/

/-- `∀ x, x ≤ máx`, en el vocabulario numérico. -/
def todoBajoMax : LNum.BoundedFormula Empty 0 :=
  BoundedFormula.all (BoundedFormula.rel NumRel.le
    ![Term.var (Sum.inr 0), Term.func NumFun.max Fin.elim0])

example : EsSigma1 (tr (atomosNumericos (Term.var 0 : L.Term (Fin 1))) (Term.var 0) todoBajoMax true) :=
  tr_sigma _ _ _ _

/-- `∀ x, máx ≤ x`: falsa en todo universo con al menos dos elementos. -/
def maxBajoTodo : LNum.BoundedFormula Empty 0 :=
  BoundedFormula.all (BoundedFormula.rel NumRel.le
    ![Term.func NumFun.max Fin.elim0, Term.var (Sum.inr 0)])

/-- La entrada como único término. -/
abbrev u0 : L.Term (Fin 1) := Term.var 0

theorem vacio_val (N : ℕ) : (Fin.val ∘ (Fin.elim0 : Fin 0 → Fin N)) = Fin.elim0 := funext fun i => i.elim0

/-- Control positivo: la traducción de `∀ x, x ≤ máx` vale con toda entrada de al menos dos bits. -/
theorem control_si (X : ℕ) (hN : 2 ≤ tam u0 ![X]) :
    (tr (atomosNumericos u0) u0 todoBajoMax true).Realize ![X] Fin.elim0 := by
  let _ := numEstructura _ hN
  have h := (realize_tr (numericos_correctos u0 ![X] hN Empty.elim) todoBajoMax Fin.elim0).1
  rw [vacio_val] at h
  refine h.2 fun a => ?_
  show a.val ≤ tam u0 ![X] - 1
  have := a.isLt
  omega

/-- Control negativo: la de `∀ x, máx ≤ x` no vale (falla en `x = 0`), y su negación traducida sí. -/
theorem control_no (X : ℕ) (hN : 2 ≤ tam u0 ![X]) :
    ¬ (tr (atomosNumericos u0) u0 maxBajoTodo true).Realize ![X] Fin.elim0 ∧
      (tr (atomosNumericos u0) u0 maxBajoTodo false).Realize ![X] Fin.elim0 := by
  let _ := numEstructura _ hN
  have h := realize_tr (numericos_correctos u0 ![X] hN Empty.elim) maxBajoTodo Fin.elim0
  rw [vacio_val] at h
  have hf : ¬ maxBajoTodo.Realize (Empty.elim : Empty → Fin (tam u0 ![X])) Fin.elim0 := fun hr => by
    have := hr ⟨0, by omega⟩
    change tam u0 ![X] - 1 ≤ 0 at this
    omega
  exact ⟨fun ht => hf (h.1.1 ht), h.2.2 hf⟩

/-! Mutante (probado en /tmp/claude-noche/MutanteTraduccion.lean, 25 nov 2026): con la guarda `z ≤ N` en lugar de
`z < N` (`leF nueva (tLong (baja u))`), Lean rechaza `realize_guarda` (el `omega` no cierra) y con él el caso `∀`
de `realize_tr`: el cuantificador traducido también miraría `z = N`, que no es un elemento del universo. -/

end SigmaFagin
end Sagitta.Map
