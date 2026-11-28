import Sagitta.Map.DeltaUno
import Sagitta.Map.AlfabetoFinito
import CslibFrontier.Computability.Complexity.CookLevin.Completeness

/-!
# Si S¹₂ decide SAT, NP ⊆ P: el corolario de Δᵇ₁ ⊆ P con un solo problema

`DeltaUno.np_sub_p_si_s12_decide` pide que S¹₂ decida, con dos fórmulas `Σᵇ₁`, **todos** los problemas de NP. Aquí
basta uno: SAT. La ruta no entra a la teoría:

1. `DeltaUno.deltaUno_en_P` da que el SAT en bits está en **P** (la de `Clases.lean`).
2. **Cook–Levin**, ya formalizado en cslib-frontier (`Cslib.Complexity.CookLevin.SAT_npHard`): todo problema de NP,
   con cualquier codificación, se reduce en tiempo polinomial a `SAT` con `encCNF`.
3. P se cierra bajo esas reducciones (`Cslib.Complexity.PolyTimeReducible.mem_P`).

Lo que faltaba era el puente entre las dos NP. La de `Clases.lean` acepta certificados de largo **a lo sumo**
`p(|x|)`; la de cslib-frontier pide largo **exacto**. El verificador nuevo lee el certificado enmarcado (`frame`:
cada bit `b` como `true, b`, y un `false` al final) y relleno con `false`; desenmarcar (`unframe`) es polinomial en
cslib-frontier. Las P coinciden por `AlfabetoFinito.esPolinomial_iff`.

## Qué se prueba (sin hipótesis abiertas)

* `np_a_cslib`: la NP de `Clases.lean` está dentro de la de cslib-frontier (con `encBits`).
* `bits`, `mem_P_de_bits`: un problema `B` con su codificación `enc`, leído como problema de cadenas; si está en P
  como cadenas, `B` está en la P de cslib-frontier.
* `np_sub_p_de_dificil`: si un problema NP-difícil (en el sentido de cslib-frontier) está en P como cadenas, NP ⊆ P.
* `np_sub_p_de_sat`, `pIgualNP_de_sat`: lo mismo para `satBits`, el SAT de `encCNF` en cadenas.
* **`np_sub_p_si_s12_decide_sat`** y **`pIgualNP_si_s12_decide_sat`**: si S¹₂ decide SAT con dos `Σᵇ₁`, NP ⊆ P y
  P = NP.

## Qué queda abierto

* La versión «dentro de S¹₂»: que S¹₂ demuestre la corrección de la reducción de Cook–Levin. No se intenta aquí.
* El recíproco (P = NP ⇒ `satBits ∈ P`) pide que `satBits` esté en la NP de `Clases.lean`, es decir, reconocer en
  tiempo polinomial las cadenas que son `encCNF` de algo. Es cierto y conocido; no se formaliza aquí.
* Los axiomas de la prueba de Cook–Levin son las de cslib-frontier; `Axiomas.lean` las imprime.
-/

open FirstOrder FirstOrder.Language
open Computability Turing Turing.MultiTapeTM

namespace Sagitta.Map
namespace CookS12

open AlfabetoFinito Acotada

/-! ## De la NP de `Clases.lean` a la de cslib-frontier -/

/-- Desenmarcar deja a lo sumo la mitad del largo. -/
theorem length_unframe_mul_dos_le : ∀ w : List Bool, 2 * (unframe w).length ≤ w.length
  | true :: b :: v => by
    have := length_unframe_mul_dos_le v
    simp only [unframe, List.length_cons]
    omega
  | [] => by simp [unframe]
  | [true] => by simp [unframe]
  | false :: v => by simp [unframe]

/-- El verificador con el certificado enmarcado: `V'(x, w) = V(x, unframe w)`. -/
def desenmarcado (V : List Bool × List Bool → Bool) : List Bool × List Bool → Bool :=
  fun q => V (q.1, unframe q.2)

/-- **La NP de `Clases.lean` está en la NP de cslib-frontier**, con certificados de largo exacto `2p + 1`. -/
theorem np_a_cslib {Pr : Problema} (h : Pr ∈ NP) : {w | Pr w = true} ∈ Cslib.Complexity.NP encBits := by
  obtain ⟨p, V, hV, hPr⟩ := h
  have hVc : ComputableInPolyTime V (encPair encBits encBits) encBool := by
    have := esPolinomial_iff.mp hV
    rwa [incrustar_par, incrustar_bool] at this
  have hpre : ComputableInPolyTime (fun q : List Bool × List Bool => (q.1, unframe q.2))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.fst encBits encBits).prod
      (ComputableInPolyTime.unframe.comp (ComputableInPolyTime.snd encBits encBits))
  refine ⟨2 * p + 1, desenmarcado V, hVc.comp hpre, ?_⟩
  refine Cslib.Complexity.IsVerifier.of_padding (fun x w hw hacc => ?_) (fun x hx => ?_)
  · -- Sano: el certificado desenmarcado es corto.
    have hlen := length_unframe_mul_dos_le w
    rw [hw] at hlen
    simp only [encBits_apply, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_ofNat] at hlen
    change Pr x = true
    exact (hPr x).2 ⟨unframe w, by omega, hacc⟩
  · -- Completo: el certificado `y`, enmarcado.
    obtain ⟨y, hy, hVy⟩ := (hPr x).1 hx
    refine ⟨frame y, ?_, fun k => ?_⟩
    · simp only [length_frame, encBits_apply, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
        Polynomial.eval_ofNat]
      omega
    · simp only [desenmarcado, unframe_frame_append]
      exact hVy

/-! ## Un problema con codificación, leído como cadenas -/

/-- `B`, con la codificación `enc`, como problema de cadenas: `w` está si es el código de algo de `B`. -/
noncomputable def bits {β : Type} (enc : β ↪ List Bool) (B : Set β) : Problema :=
  fun w => @decide (∃ b ∈ B, enc b = w) (Classical.dec _)

theorem bits_enc {β : Type} (enc : β ↪ List Bool) (B : Set β) (b : β) : bits enc B (enc b) = true ↔ b ∈ B := by
  unfold bits
  rw [@decide_eq_true_iff _ (Classical.dec _)]
  exact ⟨fun ⟨b', hb', e⟩ => enc.injective e ▸ hb', fun hb => ⟨b, hb, rfl⟩⟩

/-- **Si `B` está en P como cadenas, está en la P de cslib-frontier con `enc`**: leer `enc b` como cadena no cuesta. -/
theorem mem_P_de_bits {β : Type} {enc : β ↪ List Bool} {B : Set β} (h : bits enc B ∈ P) :
    B ∈ Cslib.Complexity.P enc := by
  have henc : ComputableInPolyTime (fun b => enc b) enc encBits := .of_eq fun _ => rfl
  exact ⟨fun b => bits enc B (enc b), (computable_of_mem_P h).comp henc, fun b => (bits_enc enc B b).symm⟩

/-- **Si un problema NP-difícil está en P como cadenas, NP ⊆ P.** La dificultad es la de cslib-frontier (toda NP,
con toda codificación, se le reduce). -/
theorem np_sub_p_de_dificil {β : Type} {enc : β ↪ List Bool} {B : Set β} (hB : Cslib.Complexity.NPHard enc B)
    (h : bits enc B ∈ P) : NP ⊆ P := by
  intro Pr hPr
  obtain ⟨f, hf, hA⟩ := (hB encBits _ (np_a_cslib hPr)).mem_P (mem_P_de_bits h)
  have e : Pr = f := funext fun w => by
    have := hA w
    simp only [Set.mem_ofPred_eq] at this
    cases hw : Pr w <;> cases hfw : f w <;> simp_all
  rw [e]
  exact mem_P_of_computable hf

/-! ## SAT -/

/-- **SAT en cadenas**: las cadenas que son `encCNF φ` de una CNF `φ` satisfacible. -/
noncomputable def satBits : Problema := bits Cslib.Complexity.encCNF Cslib.Complexity.SAT

/-- **Si SAT está en P, NP ⊆ P**, por Cook–Levin de cslib-frontier. -/
theorem np_sub_p_de_sat (h : satBits ∈ P) : NP ⊆ P :=
  np_sub_p_de_dificil Cslib.Complexity.CookLevin.SAT_npHard h

/-- **Si SAT está en P, P = NP.** -/
theorem pIgualNP_de_sat (h : satBits ∈ P) : PIgualNP :=
  Set.Subset.antisymm pSubNP (np_sub_p_de_sat h)

/-! ## El corolario de Δᵇ₁ ⊆ P, con un solo problema -/

/-- **S¹₂ decide SAT**: dos fórmulas `Σᵇ₁` definen SAT y su complemento, y S¹₂ demuestra que toda entrada cumple
una de las dos. -/
def S12DecideSat : Prop :=
  ∃ φ ψ : L.Formula (Fin 1), EsSigma1 φ ∧ EsSigma1 ψ ∧ DefinidoPor φ satBits ∧
    DefinidoPor ψ (fun w => !satBits w) ∧ DeltaUno.DemuestraDisyuncion φ ψ

/-- **Si S¹₂ decide SAT con dos `Σᵇ₁`, NP ⊆ P.** Baja `DeltaUno.np_sub_p_si_s12_decide` de «todo problema de NP» a
SAT. Leído al revés: si P ≠ NP, S¹₂ no demuestra con dos `Σᵇ₁` que cada entrada está o no está en SAT. -/
theorem np_sub_p_si_s12_decide_sat (h : S12DecideSat) : NP ⊆ P := by
  obtain ⟨φ, ψ, hφ, hψ, hP, hQ, hd⟩ := h
  exact np_sub_p_de_sat (DeltaUno.deltaUno_en_P hφ hψ hd hP hQ)

/-- **Si S¹₂ decide SAT con dos `Σᵇ₁`, P = NP.** -/
theorem pIgualNP_si_s12_decide_sat (h : S12DecideSat) : PIgualNP :=
  Set.Subset.antisymm pSubNP (np_sub_p_si_s12_decide_sat h)

/-- La forma contrapuesta: **si P ≠ NP, S¹₂ no decide SAT así.** -/
theorem no_decide_sat_si_pDistintoNP (h : PDistintoNP) : ¬ S12DecideSat :=
  fun hs => h (pIgualNP_si_s12_decide_sat hs)

/-! ## Controles -/

/-- `bits` distingue: la CNF vacía es satisfacible, la que tiene la cláusula vacía no. -/
example : satBits (Cslib.Complexity.encCNF []) = true :=
  (bits_enc _ _ _).2 (by
    change Cslib.Logic.PL.CNF.Satisfiable ([] : Cslib.Logic.PL.CNF ℕ)
    exact ⟨fun _ => true, by simp [Cslib.Logic.PL.CNF.eval]⟩)

example : satBits (Cslib.Complexity.encCNF [([] : Cslib.Logic.PL.Clause ℕ)]) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨v, hv⟩ := (bits_enc _ _ _).1 h
  simp [Cslib.Logic.PL.CNF.eval] at hv

end CookS12
end Sagitta.Map
