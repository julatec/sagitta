import Sagitta.Map.TiempoCobham
import Sagitta.Map.ExhaustivoTiempo
import Sagitta.Map.Vara
import Sagitta.Map.Comparar
import Sagitta.Map.Primero
import Sagitta.Map.SigmaNP
import Sagitta.Map.Secuentes
import Sagitta.Map.Parikh

/-!
# Lo que S¹₂ decide, es polinomial; y el corolario hacia P contra NP

Buss (1986): un predicado **Δᵇ₁ en S¹₂** (definido por una fórmula `Σᵇ₁` cuya negación S¹₂ también define con una
`Σᵇ₁`) es de tiempo polinomial. Aquí sale de la versión del teorema del testigo para **búsquedas**,
`Cobham.busqueda_es_cobham` (`Conservacion.lean`), que no pide unicidad.

1. **`decide_cobham`**: si `φ` y `ψ` son `Σᵇ₁` y S¹₂ demuestra `∀ x (φ(x) ∨ ψ(x))`, un programa de Cobham `c` dice en
   ℕ cuál de las dos vale: `c(n) = 0` y `φ(n)`, o `c(n) = 1` y `ψ(n)`. La búsqueda es la de `y ≤ 1` con
   `(y = 0 ∧ φ) ∨ (y = 1 ∧ ψ)`: la cota es explícita, así que no hace falta Parikh.
2. **`deltaUno_en_P`**: si `φ` define el problema `P` y `ψ` su complemento, y S¹₂ demuestra `∀ x (φ ∨ ψ)`, entonces
   `P` está en **P** (la clase de `Clases.lean`, sobre las máquinas de Mathlib).
3. **`np_sub_p_si_s12_decide`**: si para **todo** problema de NP S¹₂ demuestra así que está o no está, entonces
   `NP ⊆ P`. Leído al revés: si P ≠ NP, hay un problema de NP cuya decisión S¹₂ no puede demostrar con dos `Σᵇ₁`.

El paso de ℕ a cadenas va por `numeroDe` de `SigmaNP.lean` (la cadena `w` es el número `1w` en binario): su código
binario es `w ++ [true]` (`cod_numeroDe`), así que pasar de cadena a número es agregar un bit.
-/

open FirstOrder FirstOrder.Language
open Computability Turing

namespace Sagitta.Map
namespace DeltaUno

open Acotada

/-! ## Mismo código, misma máquina -/

/-- Si `f` y `g` dejan siempre la misma cadena en la cinta, una máquina para `g` sirve para `f`. -/
theorem esPolinomial_de_mismo_cod {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] {f : α → β} {g : α → γ}
    (h : ∀ a, CodBits.cod (f a) = CodBits.cod (g a)) (hg : EsPolinomial g) : EsPolinomial f := by
  obtain ⟨m⟩ := hg
  exact ⟨{ tm := m.tm
           inputAlphabet := m.inputAlphabet
           outputAlphabet := m.outputAlphabet
           time := m.time
           outputsFun := fun a => by
             have := m.outputsFun a
             have e : (CodBits.toEncoding (α := β)).encode (f a) = (CodBits.toEncoding (α := γ)).encode (g a) := h a
             rw [e]; exact this }⟩

theorem cod_nat (n : ℕ) : CodBits.cod n = n.bits := Cobham.encodeNat_eq_bits n

/-- **El código de `numeroDe w` es `w ++ [true]`.** -/
theorem cod_numeroDe : ∀ w : List Bool, (numeroDe w).bits = w ++ [true]
  | [] => by simp [numeroDe]
  | b :: w => by
    have hpos : numeroDe w ≠ 0 := Nat.one_le_iff_ne_zero.mp (uno_le_numeroDe w)
    have e : numeroDe (b :: w) = Nat.bit b (numeroDe w) := by
      rw [numeroDe_cons, Nat.bit_val]; cases b <;> simp
    rw [e, Nat.bits_append_bit _ _ (fun h => absurd h hpos), cod_numeroDe w]
    rfl

/-- **Pasar de cadena a número es polinomial**: agregar un bit al final. -/
theorem esPolinomial_numeroDe : EsPolinomial numeroDe := by
  have hk : EsPolinomial (fun _ : List Bool => [true]) :=
    Componer.esPolinomial_comp (fun _ : List Bool => ([] : List Bool)) (fun s => true :: s)
      ExhaustivoTiempo.esPolinomial_vacia Vara.esPolinomial_poner
  have hp : EsPolinomial (fun w : List Bool => (w, [true])) :=
    Primero.esPolinomial_pares (fun w => w) (fun _ => [true]) (esPolinomial_id) hk
  have hg : EsPolinomial (fun w : List Bool => w ++ [true]) :=
    Componer.esPolinomial_comp (fun w : List Bool => (w, [true])) (fun q => q.1 ++ q.2) hp Vara.esPolinomial_concat
  exact esPolinomial_de_mismo_cod (g := fun w : List Bool => w ++ [true])
    (fun w => by rw [cod_nat, cod_numeroDe]; rfl) hg

/-- **Preguntar si un número es 0 es polinomial.** -/
theorem esPolinomial_esCero : EsPolinomial (fun n : ℕ => decide (n ≤ 0)) := by
  have h0 : EsPolinomial (fun _ : ℕ => (0 : ℕ)) :=
    esPolinomial_de_mismo_cod (g := fun _ : ℕ => ([] : List Bool)) (fun _ => by rw [cod_nat]; rfl)
      ExhaustivoTiempo.esPolinomial_vacia
  have hp : EsPolinomial (fun n : ℕ => (n, (0 : ℕ))) :=
    Primero.esPolinomial_pares (fun n => n) (fun _ => 0) esPolinomial_id h0
  exact Componer.esPolinomial_comp (fun n : ℕ => (n, (0 : ℕ))) (fun q => decide (q.1 ≤ q.2)) hp
    Comparar.esPolinomial_le

/-- **Un programa de Cobham de un argumento es polinomial** (como en `definibleEsPolinomial`). -/
theorem esPolinomial_cob (c : Cobham.Cob 1) : EsPolinomial (fun n : ℕ => c.eval ![n]) :=
  Cobham.esPolinomial_of_computable ((Cobham.cob_polinomial c).comp Cobham.uno_polinomial)

/-! ## La búsqueda de `y ≤ 1` -/

/-- **`θ(x, y) = (y = 0 ∧ φ(x)) ∨ (y = 1 ∧ ψ(x))`.** -/
noncomputable def θ (φ ψ : L.Formula (Fin 1)) : L.Formula (Fin 2) :=
  (Term.equal (Term.var 1) tC ⊓ φ.subst (fun _ => Term.var 0)) ⊔
    (Term.equal (Term.var 1) tU ⊓ ψ.subst (fun _ => Term.var 0))

theorem esSigma1_θ {φ ψ : L.Formula (Fin 1)} (hφ : EsSigma1 φ) (hψ : EsSigma1 ψ) : EsSigma1 (θ φ ψ) :=
  .o (.y (.aguda (.igual _ _)) (hφ.subst _)) (.y (.aguda (.igual _ _)) (hψ.subst _))

theorem realize_θ {M : Type} [L.Structure M] (φ ψ : L.Formula (Fin 1)) (x y : M) :
    (θ φ ψ).Realize ![x, y] ↔ (y = cero ∧ φ.Realize ![x]) ∨ (y = suc cero ∧ ψ.Realize ![x]) := by
  have hU : (tU : L.Term (Fin 2)).realize ![x, y] = suc cero := by
    simp only [tU, tSc, Term.realize_functions_apply₁, realize_tC]; rfl
  have hx : (fun _ : Fin 1 => ![x, y] 0) = ![x] := by funext i; fin_cases i; rfl
  simp only [θ, Formula.realize_sup, Formula.realize_inf, Formula.realize_equal, Term.realize_var,
    formula_realize_subst, realize_tC, hU]
  rw [hx]
  exact Iff.rfl

/-- **S¹₂ decide entre `φ` y `ψ`.** -/
def DemuestraDisyuncion (φ ψ : L.Formula (Fin 1)) : Prop :=
  ∀ (M : Type) [L.Structure M], EsModeloS12 M → ∀ x : M, φ.Realize ![x] ∨ ψ.Realize ![x]

/-- **Lo que S¹₂ decide, un programa de Cobham lo decide**: `c(n) = 0` con `φ(n)`, o `c(n) = 1` con `ψ(n)`. -/
theorem decide_cobham {φ ψ : L.Formula (Fin 1)} (hφ : EsSigma1 φ) (hψ : EsSigma1 ψ)
    (hd : DemuestraDisyuncion φ ψ) :
    ∃ c : Cobham.Cob 1, ∀ n : ℕ, (c.eval ![n] = 0 ∧ φ.Realize ![n]) ∨ (c.eval ![n] = 1 ∧ ψ.Realize ![n]) := by
  obtain ⟨c, hc⟩ := Cobham.busqueda_es_cobham (θ φ ψ) (esSigma1_θ hφ hψ) tU fun M _ hM x => by
    have hU : (tU : L.Term (Fin 1)).realize ![x] = suc cero := by
      simp only [tU, tSc, Term.realize_functions_apply₁, realize_tC]; rfl
    rcases hd M hM x with h | h
    · exact ⟨cero, by rw [hU]; exact hM.basic.b3 _, (realize_θ φ ψ x _).2 (.inl ⟨rfl, h⟩)⟩
    · refine ⟨suc cero, ?_, (realize_θ φ ψ x _).2 (.inr ⟨rfl, h⟩)⟩
      rw [hU]; rcases hM.basic.b6 (suc cero) (suc cero) with h' | h' <;> exact h'
  exact ⟨c, fun n => by
    have := (realize_θ φ ψ n _).1 (hc n)
    have e0 : (cero : ℕ) = 0 := rfl
    have e1 : (suc cero : ℕ) = 1 := rfl
    rwa [e1, e0] at this⟩

/-! ## Δᵇ₁ en S¹₂ es P -/

/-- **Buss: lo que S¹₂ decide con dos `Σᵇ₁` es de tiempo polinomial.** Si `φ` define `P`, `ψ` define su
complemento, y S¹₂ demuestra `∀ x (φ(x) ∨ ψ(x))`, entonces `P ∈ P`. -/
theorem deltaUno_en_P {φ ψ : L.Formula (Fin 1)} (hφ : EsSigma1 φ) (hψ : EsSigma1 ψ) (hd : DemuestraDisyuncion φ ψ)
    {Pr : Problema} (hP : DefinidoPor φ Pr) (hQ : DefinidoPor ψ (fun w => !Pr w)) : Pr ∈ P := by
  obtain ⟨c, hc⟩ := decide_cobham hφ hψ hd
  have heq : Pr = fun w => decide (c.eval ![numeroDe w] ≤ 0) := by
    funext w
    rcases hc (numeroDe w) with ⟨h0, hφw⟩ | ⟨h1, hψw⟩
    · rw [h0]; simpa using (hP w).2 hφw
    · rw [h1]
      have := (hQ w).2 hψw
      simpa using this
  rw [heq]
  show EsPolinomial _
  exact Componer.esPolinomial_comp (fun w => c.eval ![numeroDe w]) (fun n => decide (n ≤ 0))
    (Componer.esPolinomial_comp numeroDe (fun n => c.eval ![n]) esPolinomial_numeroDe (esPolinomial_cob c))
    esPolinomial_esCero

/-- **El corolario hacia P contra NP.** Si para todo problema de NP S¹₂ demuestra, con dos fórmulas `Σᵇ₁`, que
cada entrada está o no está, entonces `NP ⊆ P`. Leído al revés: si `NP ⊄ P`, hay un problema de NP cuya decisión
S¹₂ no demuestra así. -/
theorem np_sub_p_si_s12_decide
    (h : ∀ Pr ∈ NP, ∃ φ ψ : L.Formula (Fin 1), EsSigma1 φ ∧ EsSigma1 ψ ∧ DefinidoPor φ Pr ∧
      DefinidoPor ψ (fun w => !Pr w) ∧ DemuestraDisyuncion φ ψ) : NP ⊆ P := by
  intro Pr hPr
  obtain ⟨φ, ψ, hφ, hψ, hP, hQ, hd⟩ := h Pr hPr
  exact deltaUno_en_P hφ hψ hd hP hQ

/-! ## Con Parikh: la definibilidad informal también basta -/

/-- **Buss con la definición informal** (p. 3 de Buss 1986): si S¹₂ demuestra `∀ x ∃! y φ(x, y)` con `φ` en `Σᵇ₁`,
**sin** cota, y `φ` es en ℕ el gráfico de `f`, entonces `f` es de tiempo polinomial. Es Parikh más la dirección
difícil. -/
theorem definible_sin_cota_es_polinomial (f : ℕ → ℕ) (φ : L.Formula (Fin 2)) (hφ : EsSigma1 φ)
    (htot : DemuestraTotalSinCota φ) (hgraf : ∀ n : ℕ, φ.Realize ![n, f n]) : EsPolinomial f :=
  Cobham.definibleEsPolinomial f ⟨φ, hφ, Parikh.parikh φ hφ htot, hgraf⟩

end DeltaUno
end Sagitta.Map
