import Sagitta.Map.SigmaFagin.Cierre
import Sagitta.Map.SigmaFagin.SigmaaNP
import Sagitta.Map.CookS12
import CslibFrontier.Computability.Complexity.Fagin.Ordered
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Logics.FirstOrder.Encoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# Fase C de Σᵇ₁ = NP: las palabras como estructuras ordenadas, y `NP ⊆ Σᵇ₁`

Fase C del plan, la que faltaba. Las fases A y B dejaron la mitad sintáctica de Fagin en
ℕ (`Cierre.eso_iff_cerrada`: una sentencia existencial de segundo orden sobre el vocabulario numérico es una fórmula
`Σᵇ₁` con una variable libre); la fase D, la vuelta `Σᵇ₁ ⊆ NP` y `sigmaIgualNP_iff`. Aquí se junta todo con el teorema
de Fagin **ordenado** de cslib-frontier (`FO.Ordered.ESODefinable.of_encodedLanguage_mem_NP`).

## La ruta

1. **Una palabra es una estructura ordenada.** El lenguaje `LPal` tiene una sola relación unaria («la letra es 1»).
   La palabra `w` es la estructura en `Fin |X|`, `X = numeroDe w`, donde la letra vale en `i` si el bit `i` de `X` es
   1 (`palEstr`). Como `numeroDe` pone un 1 arriba, el universo tiene `|w| + 1` elementos y su tabla es `w ++ [1]`.
2. **La consulta está en la NP de cslib.** La codificación de cslib es `(n, [tabla])`; `palabraDe` le quita el último
   bit a la tabla, y la consulta de `P` es «`P (palabraDe (código de M))`». Su lenguaje se reduce en tiempo polinomial
   a `{w | P w}` (que está en la NP de cslib por `CookS12.np_a_cslib`) con un guardia polinomial (forma bien formada y
   `n ≥ 2`).
3. **Fagin ordenado** da una sentencia `Φ` de segundo orden existencial sobre `Ordered.language LPal`.
4. **El puente de lenguajes** (`puente`): el numérico de cslib va al `LNum` de Sagitta, las variables de `Φ` a las
   `some i` de `LVar`, y la letra a una variable más, `none`, de aridad 1.
5. **La letra no se adivina: es la entrada.** `cerradaP` cierra con cuantificadores las variables `some i`, como
   `Cierre.cerrada`, pero el código de `none` es la variable libre misma (`etiquetaP`): el código de una relación unaria
   en `[0, |X|)` es el número cuyos bits la listan, y para la letra ese número es `X` (`codificanP`).
6. **La palabra vacía**: `|numeroDe []| = 1 < 2` no da estructura; la fórmula final es
   `(ψ ∧ x ≥ 2) ∨ (x ≤ 1 si P [] vale)`.

## Lo que se prueba

* `esoP_iff_cerrada`, `esoP_definible`: la sentencia con la letra fija vale en `[0, |X|)` sii la fórmula `Σᵇ₁`
  `cerradaP` vale en `X`.
* `realize_puente`: `Φ` vale en la palabra sii su traducción vale con la letra fija.
* `palabraDe_poly`, `guarda_poly`, **`consulta_NP`**: el lenguaje de la consulta está en la NP de cslib.
* `palabraDe_encode`, `mem_consulta`: la palabra `w` está en la consulta de `P` sii `P w`.
* **`np_sub_sigma`** (`NP ⊆ Σᵇ₁`) y, con `sigmaIgualNP_iff`, **`sigmaIgualNP`**: `Acotada.SigmaIgualNP`, el teorema de
  Wrathall–Stockmeyer en la forma de `SigmaNP.lean`. Y `piIgualCoNP` y `npDistintoCoNP_iff_formulas` (la pregunta
  NP ≠ coNP como pregunta sobre fórmulas, ya sin la hipótesis).

## Quién usaba `SigmaIgualNP` como hipótesis

* `SigmaNP.piIgualCoNP_de_sigma` y `SigmaNP.npDistintoCoNP_iff`: ahora valen sin ella (arriba).
* `Borde/FactorizacionS12.lean`: su hipótesis 1 («hay una `Σᵇ₁` con gráfico `Nat.minFac`») se sigue de
  `sigmaIgualNP` en cuanto se pruebe que ese gráfico está en la NP de Sagitta (certificados de Pratt); eso falta.
* `Borde/LimiteBlanco.lean` y el encabezado de `SigmaNP.lean` la mencionan como abierta en su prosa.
-/

open FirstOrder FirstOrder.Language
open Computability Turing Turing.MultiTapeTM

namespace Sagitta.Map
namespace SigmaFagin

open Acotada Acotada.Parikh
open Acotada (numeroDe numeroDe_cons DefinidoPor)
open Cobham (LB)

/-! ## La letra fija: una variable de relación cuyo código es la entrada -/

section Letra

variable {ι : Type} {k : ℕ}

/-- Las aridades con la letra: `none` es la letra (aridad 1), `some i` la variable `i`. -/
def arityP (arity : ι → ℕ) : Option ι → ℕ := fun o => o.elim 1 arity

/-- El reetiquetado: la entrada y el código de la letra van a la libre `0`; el código de `Rᵢ`, a la ligada `e i`. -/
def etiquetaP (e : ι ≃ Fin k) : Option (Option ι) → Fin 1 ⊕ Fin k
  | none => Sum.inl 0
  | some none => Sum.inl 0
  | some (some i) => Sum.inr (e i)

/-- La letra de la palabra de código `X`, en `Fin N`: vale en `i` si el bit `i` de `X` es 1. -/
def letra (X N : ℕ) : Set (Fin 1 → Fin N) := {a | X.testBit (a 0).val = true}

/-- Las relaciones con la letra: `none ↦ P`, `some i ↦ R i`. -/
def extR {arity : ι → ℕ} {N : ℕ} (P : Set (Fin 1 → Fin N)) (R : ∀ i, Set (Fin (arity i) → Fin N)) :
    ∀ o, Set (Fin (arityP arity o) → Fin N)
  | none => P
  | some i => R i

variable {arity : ι → ℕ}

/-- La matriz con los códigos de las variables ligados y el de la letra igual a la entrada. -/
def matrizP (e : ι ≃ Fin k) (φ : (LEso (arityP arity)).BoundedFormula Empty 0) : L.BoundedFormula (Fin 1) k :=
  (tr (atomosE (arityP arity)) entrada φ true).relabel (etiquetaP e)

/-- **La fórmula cerrada con la letra fija.** -/
def cerradaP (e : ι ≃ Fin k) (φ : (LEso (arityP arity)).BoundedFormula Empty 0) : L.Formula (Fin 1) :=
  cierra (cotasE arity e) k le_rfl (matrizP e φ)

theorem cerradaP_sigma (e : ι ≃ Fin k) (φ : (LEso (arityP arity)).BoundedFormula Empty 0) :
    EsSigma1 (cerradaP e φ) :=
  cierra_sigma _ k le_rfl (Arranque.EsSigma1.relabel _ (tr_sigma _ _ φ true))

/-- La valuación: la entrada y el código de la letra son `X`; el de `Rᵢ`, `y i`. -/
def valP (X : ℕ) (y : ι → ℕ) : Option (Option ι) → ℕ := fun o => o.elim X (fun o' => o'.elim X y)

theorem realize_matrizP (e : ι ≃ Fin k) (φ : (LEso (arityP arity)).BoundedFormula Empty 0) (X : ℕ)
    (ys : Fin k → ℕ) :
    (matrizP e φ).Realize ![X] ys ↔ (tr (atomosE (arityP arity)) entrada φ true).Realize (valP X (ys ∘ e)) default := by
  rw [matrizP, BoundedFormula.realize_relabel]
  have h1 : (Sum.elim ![X] (ys ∘ Fin.castAdd 0) ∘ etiquetaP e) = valP X (ys ∘ e) := by
    funext o
    rcases o with _ | _ | i
    · rfl
    · rfl
    · simp [etiquetaP, valP, Fin.castAdd]
  have h2 : (ys ∘ Fin.natAdd k : Fin 0 → ℕ) = default := funext fun i => i.elim0
  rw [h1, h2]

theorem idx_uno (N : ℕ) (a : Fin 1 → ℕ) : idx N a = a 0 := by simp [idx]

/-- **El código de la letra es la entrada.** Si los `y i` codifican las `R i`, la valuación `valP X y` codifica las
relaciones con la letra. -/
theorem codificanP (X : ℕ) (y : ι → ℕ) (R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)))
    (hR : ∀ i (a : Fin (arity i) → Fin (Nat.size X)),
      (y i).testBit (idx (Nat.size X) (Fin.val ∘ a)) = true ↔ a ∈ R i) :
    Codifican (arity := arityP arity) (valP X y) (extR (letra X (Nat.size X)) R) := by
  intro o a
  rcases o with _ | i
  · revert a
    change ∀ a : Fin 1 → Fin (Nat.size X), X.testBit (idx (Nat.size X) (Fin.val ∘ a)) = true ↔
      X.testBit (a 0).val = true
    intro a
    rw [idx_uno]
    rfl
  · exact hR i a

/-- **Fagin en ℕ con la letra fija.** La sentencia, con la letra de `X` y unas `R` cualesquiera, vale en `[0, |X|)`
sii la fórmula `Σᵇ₁` cerrada `cerradaP e φ` vale en `X`. -/
theorem esoP_iff_cerrada (e : ι ≃ Fin k) (φ : (LEso (arityP arity)).BoundedFormula Empty 0) (X : ℕ)
    (hN : 2 ≤ Nat.size X) :
    (∃ R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)),
        @BoundedFormula.Realize (LEso (arityP arity)) (Fin (Nat.size X))
          (estrE (arityP arity) _ hN (extR (letra X (Nat.size X)) R)) _ _ φ default default) ↔
      (cerradaP e φ).Realize ![X] := by
  rw [Formula.Realize, cerradaP, realize_cierra]
  constructor
  · rintro ⟨R, hR⟩
    have hcod := fun i => relacion_codificada (Nat.size X) (arity i)
      (fun a => ∃ h : ∀ j, a j < Nat.size X, (fun j => (⟨a j, h j⟩ : Fin (Nat.size X))) ∈ R i)
    choose y hy hyR using hcod
    have hc : Codifican (arity := arityP arity) (valP X y) (extR (letra X (Nat.size X)) R) :=
      codificanP X y R fun i a => (hyR i (Fin.val ∘ a) (fun j => (a j).isLt)).trans
        ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun j => (a j).isLt, h⟩⟩
    let _ : (LEso (arityP arity)).Structure (Fin (tam entrada (valP X y))) :=
      estrE (arityP arity) _ hN (extR (letra X (Nat.size X)) R)
    have := (realize_tr (atomosE_correctos (v := valP X y) (hN := hN) hc default) φ default).1
    rw [vacio_val'] at this
    refine ⟨y ∘ e.symm, fun j => lt_cotaRel ![X] (Term.var 0) _ _ (hy (e.symm j)), ?_⟩
    rw [realize_matrizP]
    have hy' : (y ∘ e.symm) ∘ e = y := by funext i; simp
    rw [hy']
    exact this.2 hR
  · rintro ⟨ys, -, hM⟩
    rw [realize_matrizP] at hM
    let R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)) :=
      fun i => {a | ((ys ∘ e) i).testBit (idx (Nat.size X) (Fin.val ∘ a)) = true}
    refine ⟨R, ?_⟩
    have hc : Codifican (arity := arityP arity) (valP X (ys ∘ e)) (extR (letra X (Nat.size X)) R) :=
      codificanP X (ys ∘ e) R fun _ _ => Iff.rfl
    let _ : (LEso (arityP arity)).Structure (Fin (tam entrada (valP X (ys ∘ e)))) :=
      estrE (arityP arity) _ hN (extR (letra X (Nat.size X)) R)
    have := (realize_tr (atomosE_correctos (v := valP X (ys ∘ e)) (hN := hN) hc default) φ default).1
    rw [vacio_val'] at this
    exact this.1 hM

/-- La forma con `ι` finito. -/
theorem esoP_definible [Finite ι] (φ : (LEso (arityP arity)).BoundedFormula Empty 0) :
    ∃ ψ : L.Formula (Fin 1), EsSigma1 ψ ∧ ∀ (X : ℕ) (hN : 2 ≤ Nat.size X),
      ((∃ R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)),
        @BoundedFormula.Realize (LEso (arityP arity)) (Fin (Nat.size X))
          (estrE (arityP arity) _ hN (extR (letra X (Nat.size X)) R)) _ _ φ default default) ↔
        ψ.Realize ![X]) := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact ⟨cerradaP e φ, cerradaP_sigma e φ, fun X hN => esoP_iff_cerrada e φ X hN⟩

end Letra

/-! ## El puente con el vocabulario de cslib-frontier -/

section Puente

/-- **El lenguaje de las palabras**: una sola relación unaria, «la letra es 1». -/
abbrev LPal : Language.{0, 0} := Cslib.Logic.ESO.varLanguage (fun _ : Unit => 1)

/-- Las constantes numéricas de cslib, en `LNum`. -/
def numF : ∀ {n : ℕ}, Cslib.Logic.FO.Ordered.NumericFunction n → NumFun n
  | _, .zero => .cero
  | _, .one => .uno
  | _, .max => .max

/-- Las relaciones numéricas de cslib, en `LNum`. -/
def numR : ∀ {n : ℕ}, Cslib.Logic.FO.Ordered.NumericRelation n → NumRel n
  | _, .le => .le
  | _, .bit => .bit

variable {ι : Type} (arity : ι → ℕ)

/-- **El puente**: el lenguaje de la matriz de cslib (palabras + numérico + variables) en `LEso` con la letra. -/
def puente : (Cslib.Logic.FO.Ordered.language LPal).sum (Cslib.Logic.ESO.varLanguage arity) →ᴸ
    LEso (arityP arity) where
  onFunction _ f := match f with
    | Sum.inl (Sum.inl f) => Empty.elim f
    | Sum.inl (Sum.inr f) => Sum.inl (numF f)
    | Sum.inr f => Empty.elim f
  onRelation _ r := match r with
    | Sum.inl (Sum.inl r) => Sum.inr ⟨none, r.2⟩
    | Sum.inl (Sum.inr r) => Sum.inl (numR r)
    | Sum.inr r => Sum.inr ⟨some r.1, r.2⟩

/-- La palabra de código `X` como estructura ordenada de cslib. -/
def palEstr (X : ℕ) (hX : 2 ≤ Nat.size X) : Cslib.Logic.FO.Ordered.Structure LPal :=
  ⟨Nat.size X, hX, Cslib.Logic.ESO.varLanguage.structure (fun _ => letra X (Nat.size X))⟩

variable {arity}

/-- **`Φ` vale en la palabra sii su traducción vale con la letra fija.** -/
theorem realize_puente (X : ℕ) (hX : 2 ≤ Nat.size X)
    (Φ : Cslib.Logic.ESO.Sentence (Cslib.Logic.FO.Ordered.language LPal)) :
    Φ.Realize (palEstr X hX) ↔ ∃ R : ∀ i, Set (Fin (Φ.arity i) → Fin (Nat.size X)),
      @BoundedFormula.Realize (LEso (arityP Φ.arity)) (Fin (Nat.size X))
        (estrE (arityP Φ.arity) _ hX (extR (letra X (Nat.size X)) R)) _ _
        ((puente Φ.arity).onSentence Φ.matrix) default default := by
  unfold Cslib.Logic.ESO.Sentence.Realize
  refine exists_congr fun R => ?_
  let iV : (Cslib.Logic.ESO.varLanguage Φ.arity).Structure (Fin (Nat.size X)) :=
    Cslib.Logic.ESO.varLanguage.structure R
  let iE : (LEso (arityP Φ.arity)).Structure (Fin (Nat.size X)) :=
    estrE (arityP Φ.arity) _ hX (extR (letra X (Nat.size X)) R)
  let iO : (Cslib.Logic.FO.Ordered.language LPal).Structure (Fin (Nat.size X)) :=
    @Language.sumStructure _ _ _ (Cslib.Logic.ESO.varLanguage.structure (fun _ => letra X (Nat.size X)))
      (Cslib.Logic.FO.Ordered.numericStructure hX)
  have : (puente Φ.arity).IsExpansionOn (Fin (Nat.size X)) := by
    refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
    · rcases f with (f | f) | f
      · exact Empty.elim f
      · cases f <;> rfl
      · exact Empty.elim f
    · rcases r with (r | r) | r
      · rfl
      · cases r <;> rfl
      · rfl
  exact (LHom.realize_onSentence (Fin (Nat.size X)) (puente Φ.arity) Φ.matrix).symm

end Puente

/-! ## La consulta: las palabras de un problema de NP -/

section Consulta

/-- El vocabulario de las palabras: una tabla, la de la letra. -/
def vocPal : Cslib.Logic.Vocabulary LPal where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨1, ⟨(), rfl⟩⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun ⟨n, ⟨(), h⟩⟩ => by cases h; rfl }

/-- **La palabra de una entrada**: la primera tabla sin su último bit (el 1 de arriba de `numeroDe`). -/
def palabraDe (a : Cslib.Logic.EncodedStructure) : List Bool :=
  (a.2.headD []).take ((a.2.headD []).length - 1)

/-- La consulta de `P`: las estructuras cuyo código da una palabra de `P`. -/
def consulta (P : Problema) : Cslib.Logic.FO.Ordered.Query LPal :=
  {M | P (palabraDe (Cslib.Logic.FO.Ordered.encode vocPal M)) = true}

theorem palabraDe_poly : ComputableInPolyTime palabraDe Cslib.Logic.encStructure encBits := by
  have h1 : ComputableInPolyTime (fun a : Cslib.Logic.EncodedStructure => a.2.headD [])
      Cslib.Logic.encStructure encBits :=
    (ComputableInPolyTime.headD (encA := encBits) (encL := encList encBits) []).comp
      (ComputableInPolyTime.snd encUnary (encList encBits))
  have h2 : ComputableInPolyTime (fun a : Cslib.Logic.EncodedStructure => (a.2.headD []).length - 1)
      Cslib.Logic.encStructure encUnary :=
    ComputableInPolyTime.unary_sub.comp
      ((ComputableInPolyTime.length_bits.comp h1).prod (ComputableInPolyTime.const 1))
  exact ComputableInPolyTime.bitsTakeWithInput h1 h2

theorem guarda_poly : ComputableInPolyTime
    (fun a : Cslib.Logic.EncodedStructure => vocPal.checkShape a && decide (2 ≤ a.1))
    Cslib.Logic.encStructure encBool :=
  ComputableInPolyTime.bool_and' vocPal.computableInPolyTime_checkShape
    (ComputableInPolyTime.unary_le' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.fst encUnary (encList encBits)))

theorem encode_decoded {a : Cslib.Logic.EncodedStructure} (hw : vocPal.WellFormed a) (hn : 2 ≤ a.1) :
    Cslib.Logic.FO.Ordered.encode vocPal (Cslib.Logic.FO.Ordered.decoded vocPal a hn) = a :=
  (vocPal.wellFormed_iff a).1 hw

theorem mem_encLang (P : Problema) (a : Cslib.Logic.EncodedStructure) :
    a ∈ (consulta P).encodedLanguage vocPal ↔
      (vocPal.checkShape a && decide (2 ≤ a.1)) = true ∧ a ∈ {a | palabraDe a ∈ {w | P w = true}} := by
  simp only [Cslib.Logic.FO.Ordered.Query.encodedLanguage, Set.mem_ofPred_eq, Bool.and_eq_true,
    decide_eq_true_eq, vocPal.checkShape_eq_true_iff]
  constructor
  · rintro ⟨hw, hn, hK⟩
    refine ⟨⟨hw, hn⟩, ?_⟩
    have hK' : P (palabraDe (Cslib.Logic.FO.Ordered.encode vocPal
        (Cslib.Logic.FO.Ordered.decoded vocPal a hn))) = true := hK
    rwa [encode_decoded hw hn] at hK'
  · rintro ⟨⟨hw, hn⟩, hP⟩
    refine ⟨hw, hn, ?_⟩
    show P (palabraDe (Cslib.Logic.FO.Ordered.encode vocPal (Cslib.Logic.FO.Ordered.decoded vocPal a hn))) = true
    rwa [encode_decoded hw hn]

/-- **La consulta de un problema de NP está en la NP de cslib** (con la codificación de estructuras). -/
theorem consulta_NP {P : Problema} (h : P ∈ NP) :
    (consulta P).encodedLanguage vocPal ∈ Cslib.Complexity.NP Cslib.Logic.encStructure := by
  have hB := CookS12.np_a_cslib h
  have hA : {a : Cslib.Logic.EncodedStructure | palabraDe a ∈ {w | P w = true}} ∈
      Cslib.Complexity.NP Cslib.Logic.encStructure :=
    Cslib.Complexity.PolyTimeReducible.mem_NP ⟨palabraDe, palabraDe_poly, fun _ => Iff.rfl⟩ hB
  exact Cslib.Complexity.mem_NP_of_guard guarda_poly hA (fun a => mem_encLang P a)

end Consulta

/-! ## Las palabras: la tabla de `numeroDe w` es `w ++ [1]` -/

section Palabras

theorem numeroDe_div_dos (b : Bool) (w : List Bool) : numeroDe (b :: w) / 2 = numeroDe w := by
  rw [numeroDe_cons]; cases b <;> simp; omega

/-- **Los bits de `numeroDe w`**: el bit `i` es la letra `i`, y el bit `|w|` es el 1 de arriba. -/
theorem testBit_numeroDe : ∀ (w : List Bool) (i : ℕ), i ≤ w.length → (numeroDe w).testBit i = w.getD i true
  | [], 0, _ => rfl
  | [], _ + 1, h => absurd h (by simp)
  | b :: w, 0, _ => by
    rw [Nat.testBit_zero, numeroDe_cons]
    cases b <;> simp
  | b :: w, i + 1, h => by
    rw [Nat.testBit_succ, numeroDe_div_dos, testBit_numeroDe w i (by simpa using h)]
    simp

theorem dos_le_size {w : List Bool} (hw : w ≠ []) : 2 ≤ Nat.size (numeroDe w) := by
  rw [size_numeroDe]
  cases w with
  | nil => exact absurd rfl hw
  | cons b w => simp

/-- La tabla de la letra en el código de `palEstr X`: los bits de `X` debajo de `|X|`. -/
theorem headD_encode (X : ℕ) (hX : 2 ≤ Nat.size X) :
    (Cslib.Logic.FO.Ordered.encode vocPal (palEstr X hX)).2.headD [] =
      List.ofFn (fun i : Fin (Nat.size X) => X.testBit i) := by
  apply List.ext_getElem
  · simp [Cslib.Logic.FO.Ordered.encode, Cslib.Logic.Vocabulary.encode, Cslib.Logic.Vocabulary.relTable, palEstr,
      vocPal]
    show X.size ^ 1 = X.size
    exact Nat.pow_one _
  · intro j h1 h2
    simp [Cslib.Logic.FO.Ordered.encode, Cslib.Logic.Vocabulary.encode, Cslib.Logic.Vocabulary.relTable, palEstr,
      letra, vocPal]
    have hj : j < Nat.size X := by simpa using h2
    rw [Bool.eq_iff_iff]
    refine (@decide_eq_true_iff _ (Classical.propDecidable _)).trans ?_
    change X.testBit ((finFunctionFinEquiv.symm (⟨j, by simpa using hj⟩ : Fin (Nat.size X ^ 1)) :
      Fin 1 → Fin (Nat.size X)) 0).val = true ↔ _
    rw [finFunctionFinEquiv_symm_apply_val]
    simp [Nat.mod_eq_of_lt hj]

/-- **La palabra de la estructura de `w` es `w`.** -/
theorem palabraDe_encode (w : List Bool) (hw : 2 ≤ Nat.size (numeroDe w)) :
    palabraDe (Cslib.Logic.FO.Ordered.encode vocPal (palEstr (numeroDe w) hw)) = w := by
  have hs := size_numeroDe w
  rw [palabraDe, headD_encode]
  apply List.ext_getElem
  · simp [hs]
  · intro j h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    rw [testBit_numeroDe w j h2.le, List.getD_eq_getElem]

/-- **La palabra `w` está en la consulta de `P` sii `P w`.** -/
theorem mem_consulta (P : Problema) (w : List Bool) (hw : 2 ≤ Nat.size (numeroDe w)) :
    palEstr (numeroDe w) hw ∈ consulta P ↔ P w = true := by
  show P (palabraDe _) = true ↔ _
  rw [palabraDe_encode]

end Palabras

/-! ## NP ⊆ Σᵇ₁ -/

/-- `x ≥ 2`. -/
def dosLe : LB.Formula (Fin 1) := leF (tSc tU) (Term.var (Sum.inl 0))

/-- `x ≤ 1`. -/
def leUno : LB.Formula (Fin 1) := leF (Term.var (Sum.inl 0)) tU

theorem realize_dosLe (X : ℕ) : dosLe.Realize ![X] ↔ 2 ≤ X := by
  rw [Formula.Realize, dosLe, realize_leF_nat]
  simp

theorem realize_leUno (X : ℕ) : leUno.Realize ![X] ↔ X ≤ 1 := by
  rw [Formula.Realize, leUno, realize_leF_nat]
  simp

/-- **NP ⊆ Σᵇ₁** (Wrathall 1976, por Fagin ordenado): todo problema de NP lo define una fórmula `Σᵇ₁`. -/
theorem np_sub_sigma (P : Problema) (h : P ∈ NP) :
    ∃ φ : LB.Formula (Fin 1), EsSigma1 φ ∧ DefinidoPor φ P := by
  obtain ⟨Φ, hΦ⟩ := Cslib.Logic.FO.Ordered.ESODefinable.of_encodedLanguage_mem_NP vocPal (consulta_NP h)
  obtain ⟨ψ, hψ, hψX⟩ := esoP_definible ((puente Φ.arity).onSentence Φ.matrix)
  let vacio : LB.Formula (Fin 1) := if P [] = true then leUno else BoundedFormula.falsum
  refine ⟨(ψ ⊓ dosLe) ⊔ vacio, EsSigma1.o (EsSigma1.y hψ (EsSigma1.aguda (aguda_leF _ _))) ?_, fun w => ?_⟩
  · simp only [vacio]
    split
    · exact EsSigma1.aguda (aguda_leF _ _)
    · exact EsSigma1.aguda EsAguda.falso
  have hv : vacio.Realize ![numeroDe w] ↔ P [] = true ∧ numeroDe w ≤ 1 := by
    simp only [vacio]
    split
    · rw [realize_leUno]; simp_all
    · rename_i hP
      simp only [hP, Bool.false_eq_true, false_and, iff_false]
      exact fun h => h
  rw [Formula.realize_sup, Formula.realize_inf, hv, realize_dosLe]
  rcases w with _ | ⟨b, w⟩
  · simp
  · have hw := dos_le_size (w := b :: w) (by simp)
    have h2 : 2 ≤ numeroDe (b :: w) := by
      by_contra hc
      have : Nat.size (numeroDe (b :: w)) ≤ 1 := Nat.size_le.2 (by omega)
      omega
    rw [← mem_consulta P (b :: w) hw, hΦ, realize_puente, hψX _ hw]
    constructor
    · intro h; exact Or.inl ⟨h, h2⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact h
      · omega

/-- **`NP ⊆ Σᵇ₁`**, en la forma de `sigmaIgualNP_iff`. -/
theorem npSubSigma : ∀ P ∈ NP, ∃ φ : LB.Formula (Fin 1), EsSigma1 φ ∧ DefinidoPor φ P := np_sub_sigma

/-- **Wrathall–Stockmeyer: Σᵇ₁ = NP.** -/
theorem sigmaIgualNP : Acotada.SigmaIgualNP := sigmaIgualNP_iff.2 npSubSigma

/-- Y por dualidad, `Πᵇ₁ = coNP`. -/
theorem piIgualCoNP : Acotada.PiIgualCoNP := Acotada.piIgualCoNP_de_sigma sigmaIgualNP

/-- **NP ≠ coNP como pregunta sobre fórmulas, sin hipótesis**: `SigmaNP.npDistintoCoNP_iff` con `sigmaIgualNP`. -/
theorem npDistintoCoNP_iff_formulas : NPDistintoCoNP ↔
    ∃ P : Problema, (∃ φ : LB.Formula (Fin 1), EsPi1 φ ∧ DefinidoPor φ P) ∧
      ¬ ∃ ψ : LB.Formula (Fin 1), EsSigma1 ψ ∧ DefinidoPor ψ P :=
  Acotada.npDistintoCoNP_iff sigmaIgualNP

/-! Mutantes (probados fuera del repositorio, 25 nov 2026, tarde):

* Con la letra corrida un bit (`letra X N = {a | X.testBit ((a 0) + 1)}`), Lean rechaza `codificanP` (el código de la
  letra ya no es la entrada: hace falta `testBit (idx N a) = testBit (a 0)`) y `headD_encode` (la tabla ya no son los
  bits de `X`). La letra no se adivina porque su código es exactamente `X`.
* Sin la disyunción de la palabra vacía (`(ψ ∧ x ≥ 2) ∨ ⊥`), Lean deja abierto el caso `w = []`: hay que probar
  `P [] = true ↔ False`, que no vale para los `P` que aceptan la vacía. -/

end SigmaFagin
end Sagitta.Map
