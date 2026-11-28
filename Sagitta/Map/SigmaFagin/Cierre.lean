import Sagitta.Map.SigmaFagin.Ensamble
import Sagitta.Map.Arranque

/-!
# Fase B de Σᵇ₁ = NP, cerrada: los códigos dentro de una sola fórmula

Cuarta pieza de la fase B del plan. `Ensamble.lean` dejó la traducción de una sentencia
existencial de segundo orden como una fórmula `Σᵇ₁` con **variables libres** para los códigos de las relaciones
(`some i`) además de la entrada (`none`), y el teorema `eso_iff`: la sentencia vale en `[0, |x|)` si y solo si **hay**
códigos que hacen verdadera la traducción. Aquí esos «hay códigos» pasan a ser cuantificadores de la fórmula: queda una
**fórmula de S¹₂ con una sola variable libre**, la entrada, que es `Σᵇ₁` y dice lo mismo que la sentencia.

## La construcción

1. **Ordenar** las variables de relación: un `e : ι ≃ Fin k` cualquiera (todo `ι` finito tiene uno).
2. **Reetiquetar**: la variable libre `none` (la entrada) pasa a ser la libre `0 : Fin 1`, y la libre `some i` (el código
   de `Rᵢ`) pasa a ser la **ligada** número `e i`. Es `BoundedFormula.relabel` de Mathlib, y `EsSigma1.relabel`
   (`Arranque.lean`) dice que no saca de `Σᵇ₁`.
3. **Cuantificar**: `cierra` pone `∃ y_{k−1} ≤ c_{k−1}`, …, `∃ y₀ ≤ c₀` por fuera, de adentro hacia afuera, con
   `cᵢ = cotaRel (arity (e⁻¹ i)) x` (fase A). Son cuantificadores acotados **no agudos** (la cota es `2^{poly(|x|)}`), que
   `Σᵇ₁` admite (Buss, cláusula 2b): es justo el «adivinar el testigo» de NP.

## Lo que se prueba

* `cierra_sigma`, `realize_cierra`: cerrar con cotas cualesquiera conserva `Σᵇ₁` y se lee como «hay `ys` debajo de las
  cotas que hacen verdadera la matriz».
* `cerrada_sigma`: la fórmula cerrada es `Σᵇ₁`, en `L.Formula (Fin 1)`, el tipo de `DefinidoPor` de `SigmaNP.lean`.
* **`eso_iff_cerrada`**: `(∃ R, φ vale en Fin |x| con R) ↔ (cerrada e φ).Realize ![x]`, para todo `x` con `|x| ≥ 2`.
* `eso_definible`: la forma con `ι` finito cualquiera: existe una fórmula `Σᵇ₁` con una variable libre que dice lo mismo
  que la sentencia en toda entrada con `|x| ≥ 2`.

## Lo que no se prueba aquí

* El caso `|x| < 2` (universos de 0 o 1 elementos): `numEstructura` pide dos elementos para que `0 ≠ 1`, como en
  cslib-frontier. Las palabras de largo 0 son un número finito de casos y se agregan con una disyunción en la fase C.
* El lenguaje de las letras de la palabra, el `numeroDe` de `SigmaNP.lean` y el puente con `Ordered.language` y
  `ESO.Sentence` de cslib-frontier (fase C), y la vuelta `Σᵇ₁ ⊆ NP` (fase D).
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace SigmaFagin

open Acotada Acotada.Parikh

/-! ## Cerrar variables ligadas con cuantificadores acotados -/

section Cierra

variable {α : Type} {k : ℕ} (cota : Fin k → L.Term α)

/-- `cierra cota j h φ = ∃ y₀ ≤ c₀ … ∃ y_{j−1} ≤ c_{j−1}, φ`: cierra las `j` variables ligadas de `φ`, la última
(la `j − 1`) por dentro. Las cotas solo dependen de las variables libres. -/
def cierra : ∀ (j : ℕ), j ≤ k → L.BoundedFormula α j → L.BoundedFormula α 0
  | 0, _, φ => φ
  | j + 1, h, φ => cierra j (Nat.le_of_succ_le h) (existeAcotado ((cota ⟨j, h⟩).relabel Sum.inl) φ)

theorem cierra_sigma : ∀ (j : ℕ) (h : j ≤ k) {φ : L.BoundedFormula α j}, EsSigma1 φ → EsSigma1 (cierra cota j h φ)
  | 0, _, _, hφ => hφ
  | j + 1, h, _, hφ => cierra_sigma j (Nat.le_of_succ_le h) (EsSigma1.existe _ hφ)

/-- **Cerrar se lee como «existen debajo de las cotas».** -/
theorem realize_cierra (v : α → ℕ) (xs0 : Fin 0 → ℕ) : ∀ (j : ℕ) (h : j ≤ k) (φ : L.BoundedFormula α j),
    (cierra cota j h φ).Realize v xs0 ↔
      ∃ ys : Fin j → ℕ, (∀ i : Fin j, ys i ≤ (cota ⟨i, lt_of_lt_of_le i.2 h⟩).realize v) ∧ φ.Realize v ys
  | 0, _, φ => by
    simp only [cierra]
    refine ⟨fun hφ => ⟨xs0, fun i => i.elim0, hφ⟩, fun ⟨ys, _, hφ⟩ => ?_⟩
    rwa [show ys = xs0 from funext fun i => i.elim0] at hφ
  | j + 1, h, φ => by
    rw [cierra, realize_cierra v xs0 j]
    have hc : ∀ ys : Fin j → ℕ, ((cota ⟨j, h⟩).relabel Sum.inl : L.Term (α ⊕ Fin j)).realize (Sum.elim v ys) =
        (cota ⟨j, h⟩).realize v := fun ys => by
      rw [Term.realize_relabel, Sum.elim_comp_inl]
    simp only [realize_existe, le_nat, hc]
    constructor
    · rintro ⟨ys, hys, z, hz, hφ⟩
      refine ⟨Fin.snoc ys z, fun i => ?_, hφ⟩
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact hz
      · rw [Fin.snoc_castSucc]; exact hys i
    · rintro ⟨ys, hys, hφ⟩
      refine ⟨Fin.init ys, fun i => hys (Fin.castSucc i), ys (Fin.last j), hys (Fin.last j), ?_⟩
      rwa [Fin.snoc_init_self]

end Cierra

/-! ## La sentencia existencial de segundo orden como una fórmula cerrada -/

section Cerrada

variable {ι : Type} {arity : ι → ℕ} {k : ℕ}

/-- El reetiquetado: la entrada a la libre `0`, el código de `Rᵢ` a la ligada `e i`. -/
def etiqueta (e : ι ≃ Fin k) : Option ι → Fin 1 ⊕ Fin k
  | none => Sum.inl 0
  | some i => Sum.inr (e i)

/-- Las cotas, en el orden de `e`: la del código de `R_{e⁻¹ j}` es `cotaRel (arity (e⁻¹ j)) x`. -/
def cotasE (arity : ι → ℕ) (e : ι ≃ Fin k) (j : Fin k) : L.Term (Fin 1) :=
  cotaRel (arity (e.symm j)) (Term.var 0)

/-- La matriz con los códigos como variables ligadas. -/
def matrizCerrada (e : ι ≃ Fin k) (φ : (LEso arity).BoundedFormula Empty 0) : L.BoundedFormula (Fin 1) k :=
  (tr (atomosE arity) entrada φ true).relabel (etiqueta e)

/-- **La fórmula cerrada**: `∃ y₀ ≤ c₀ … ∃ y_{k−1} ≤ c_{k−1}, tr φ`, con una sola variable libre (la entrada). -/
def cerrada (e : ι ≃ Fin k) (φ : (LEso arity).BoundedFormula Empty 0) : L.Formula (Fin 1) :=
  cierra (cotasE arity e) k le_rfl (matrizCerrada e φ)

/-- **La fórmula cerrada es `Σᵇ₁`.** -/
theorem cerrada_sigma (e : ι ≃ Fin k) (φ : (LEso arity).BoundedFormula Empty 0) : EsSigma1 (cerrada e φ) :=
  cierra_sigma _ k le_rfl (Arranque.EsSigma1.relabel _ (tr_sigma _ _ φ true))

theorem realize_matrizCerrada (e : ι ≃ Fin k) (φ : (LEso arity).BoundedFormula Empty 0) (X : ℕ) (ys : Fin k → ℕ) :
    (matrizCerrada e φ).Realize ![X] ys ↔
      (tr (atomosE arity) entrada φ true).Realize (fun o => o.elim X (ys ∘ e)) default := by
  rw [matrizCerrada, BoundedFormula.realize_relabel]
  have h1 : (Sum.elim ![X] (ys ∘ Fin.castAdd 0) ∘ etiqueta e) = fun o => o.elim X (ys ∘ e) := by
    funext o
    rcases o with _ | i
    · rfl
    · simp [etiqueta, Fin.castAdd]
  have h2 : (ys ∘ Fin.natAdd k : Fin 0 → ℕ) = default := funext fun i => i.elim0
  rw [h1, h2]

/-- La mitad de `eso_iff` que no usa la cota: si unos códigos cualesquiera hacen verdadera la traducción, la sentencia
vale (las relaciones son los conjuntos de bits de los códigos). -/
theorem eso_de_codigos (φ : (LEso arity).BoundedFormula Empty 0) (X : ℕ) (hN : 2 ≤ Nat.size X) (y : ι → ℕ)
    (hT : (tr (atomosE arity) entrada φ true).Realize (fun o => o.elim X y) default) :
    ∃ R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)),
      @BoundedFormula.Realize (LEso arity) (Fin (Nat.size X)) (estrE arity _ hN R) _ _ φ default default := by
  let R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)) :=
    fun i => {a | (y i).testBit (idx (Nat.size X) (Fin.val ∘ a)) = true}
  refine ⟨R, ?_⟩
  have hc : Codifican (fun o => o.elim X y) R := fun i a => Iff.rfl
  let _ : (LEso arity).Structure (Fin (tam entrada (fun o => o.elim X y))) := estrE arity _ hN R
  have := (realize_tr (atomosE_correctos (v := fun o => o.elim X y) (hN := hN) hc default) φ default).1
  rw [vacio_val'] at this
  exact this.1 hT

/-- **Fagin, la mitad sintáctica, cerrada.** Una sentencia existencial de segundo orden sobre el vocabulario numérico
vale en `[0, |x|)` si y solo si la fórmula `Σᵇ₁` cerrada `cerrada e φ`, con la sola variable libre `x`, es verdadera. -/
theorem eso_iff_cerrada (e : ι ≃ Fin k) (φ : (LEso arity).BoundedFormula Empty 0) (X : ℕ) (hN : 2 ≤ Nat.size X) :
    (∃ R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)),
        @BoundedFormula.Realize (LEso arity) (Fin (Nat.size X)) (estrE arity _ hN R) _ _ φ default default) ↔
      (cerrada e φ).Realize ![X] := by
  rw [Formula.Realize, cerrada, realize_cierra]
  constructor
  · intro h
    obtain ⟨y, hy, hT⟩ := eso_iff_cota φ X hN h
    refine ⟨y ∘ e.symm, fun j => hy (e.symm j), ?_⟩
    rw [realize_matrizCerrada]
    simpa [Function.comp_def] using hT
  · rintro ⟨ys, -, hM⟩
    rw [realize_matrizCerrada] at hM
    exact eso_de_codigos φ X hN _ hM

/-- **La forma con `ι` finito.** Para toda sentencia existencial de segundo orden con finitas variables de relación hay
una fórmula `Σᵇ₁` de S¹₂, con una sola variable libre, que vale en `x` exactamente cuando la sentencia vale en
`[0, |x|)` (para `|x| ≥ 2`). -/
theorem eso_definible [Finite ι] (φ : (LEso arity).BoundedFormula Empty 0) :
    ∃ ψ : L.Formula (Fin 1), EsSigma1 ψ ∧ ∀ (X : ℕ) (hN : 2 ≤ Nat.size X),
      ((∃ R : ∀ i, Set (Fin (arity i) → Fin (Nat.size X)),
        @BoundedFormula.Realize (LEso arity) (Fin (Nat.size X)) (estrE arity _ hN R) _ _ φ default default) ↔
        ψ.Realize ![X]) := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact ⟨cerrada e φ, cerrada_sigma e φ, fun X hN => eso_iff_cerrada e φ X hN⟩

end Cerrada

/-! ## Controles -/

/-- El orden de una sola variable de relación. -/
def unoE : Unit ≃ Fin 1 := ⟨fun _ => 0, fun _ => (), fun _ => rfl, fun _ => Subsingleton.elim _ _⟩

/-- `ejemploR` de `Ensamble.lean` («existe `R` unaria con `R(0)` y no `R(máx)`»), cerrada: verdadera en `x = 4`. -/
example : (cerrada (unoE) ejemploR).Realize ![4] := by
  refine (eso_iff_cerrada _ ejemploR 4 cuatro).1 ⟨fun _ => {a | (a 0).val = 0}, ?_⟩
  let _ := estrE (fun _ : Unit => 1) _ cuatro (fun _ => {a | (a 0).val = 0})
  simp only [ejemploR, BoundedFormula.realize_inf, BoundedFormula.realize_not]
  refine ⟨rfl, fun h => ?_⟩
  change (Nat.size 4 - 1) = 0 at h
  exact absurd h (by decide)

/-- `ejemploMal` («existe `R` con `R(0) ∧ ¬R(0)`»), cerrada: falsa en `x = 4`. -/
example : ¬ (cerrada (unoE) ejemploMal).Realize ![4] := by
  intro h
  obtain ⟨R, hR⟩ := (eso_iff_cerrada _ ejemploMal 4 cuatro).2 h
  let _ := estrE (fun _ : Unit => 1) _ cuatro R
  simp only [ejemploMal, BoundedFormula.realize_inf, BoundedFormula.realize_not] at hR
  exact hR.2 hR.1

/-- La cerrada es `Σᵇ₁` con una sola variable libre: el tipo de `SigmaNP.DefinidoPor`. -/
example : EsSigma1 (cerrada (unoE) ejemploR) := cerrada_sigma _ _

/-! Mutantes (probados fuera del repositorio, 25 nov 2026, continuación):

* Con las cotas de los códigos cambiadas por `1` (`cotasE … = tU`), Lean rechaza la ida de `eso_iff_cerrada` (en
  `fun j => hy (e.symm j)`: el código solo se sabe `≤ cotaRel`, no `≤ 1`). La cota de fase A es la que deja adivinar
  la relación entera.
* Con `paraTodoAcotado` en lugar de `existeAcotado` en `cierra`, Lean rechaza `cierra_sigma` (un `∀` no agudo no es
  `Σᵇ₁`: no hay regla que lo admita) y `realize_cierra`. Los códigos se adivinan, no se recorren. -/

end SigmaFagin
end Sagitta.Map
