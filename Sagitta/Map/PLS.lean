import Sagitta.Map.BuenaFundacion
import Sagitta.Map.Primero

/-!
# PLS completo, dentro de TFNP

La definición de Johnson, Papadimitriou y Yannakakis (1988): cada instancia `x` tiene soluciones factibles (cortas y
fáciles de reconocer), una solución inicial, un vecino y un costo, todo en tiempo polinomial. Se pide un óptimo local.

`TFNP` (Megiddo y Papadimitriou, 1991): problemas de búsqueda cuya solución siempre existe, es corta, y se verifica
en tiempo polinomial.

**Lo probado:** `PLS ⊆ TFNP`, sin hipótesis. El verificador junta funciones de tiempo polinomial con cinco
propiedades de cierre (composición, pares, primera proyección, conjunción y comparación de naturales). Mathlib solo
trae la identidad; las cinco están probadas en este proyecto sobre sus máquinas de Turing (`cierrePolinomial`).

Lo que no usa el cierre: que la solución siempre existe, y que seguir al vecino desde la solución inicial la
alcanza en a lo sumo tantos pasos como su costo. Esa es la buena fundación de `ℕ`, otra vez.
-/

namespace Sagitta.Map

/-! ## TFNP -/

/-- Un problema de búsqueda: qué respuestas `y` sirven para la instancia `x`. -/
abbrev Busqueda := List Bool → List Bool → Prop

/-- `R` está en **TFNP**: verificable en tiempo polinomial, con respuestas de largo polinomial, y **total**: toda
instancia tiene respuesta. -/
def EnTFNP (R : Busqueda) : Prop :=
  ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    EsPolinomial V ∧ (∀ x y, R x y ↔ V (x, y) = true) ∧
    (∀ x y, R x y → y.length ≤ p.eval x.length) ∧ (∀ x, ∃ y, R x y)

/-- **TFNP**, como conjunto de problemas de búsqueda. -/
def TFNP : Set Busqueda := {R | EnTFNP R}

/-- **El cierre del tiempo polinomial.** Composición, pares, primera proyección, conjunción de dos bits y
comparación de dos naturales. Fue hipótesis explícita hasta el 22 nov 2026; ahora es el teorema `cierrePolinomial`. -/
def CierrePolinomial : Prop :=
  (∀ {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] (f : α → β) (g : β → γ),
      EsPolinomial f → EsPolinomial g → EsPolinomial (g ∘ f)) ∧
  (∀ {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] (f : α → β) (g : α → γ),
      EsPolinomial f → EsPolinomial g → EsPolinomial (fun a => (f a, g a))) ∧
  (∀ {α β : Type} [CodBits α] [CodBits β], EsPolinomial (Prod.fst : α × β → α)) ∧
  EsPolinomial (fun q : Bool × Bool => q.1 && q.2) ∧
  EsPolinomial (fun q : ℕ × ℕ => decide (q.1 ≤ q.2))

/-- **El cierre del tiempo polinomial, probado.** Las cinco propiedades, sobre las máquinas de Turing de Mathlib:
composición (`Componer.esPolinomial_comp`), pares (`Primero.esPolinomial_pares`), primera proyección
(`Basicas.esPolinomial_fst`), conjunción (`Basicas.esPolinomial_y`) y comparación (`Comparar.esPolinomial_le`). -/
theorem cierrePolinomial : CierrePolinomial :=
  ⟨fun f g hf hg => Componer.esPolinomial_comp f g hf hg,
    fun f g hf hg => Primero.esPolinomial_pares f g hf hg,
    Basicas.esPolinomial_fst, Basicas.esPolinomial_y, Comparar.esPolinomial_le⟩

/-! ## PLS -/

/-- **Un problema de PLS.** Para cada instancia `x`: qué cadenas son soluciones factibles, una inicial, el vecino de
cada una y su costo. -/
structure ProblemaPLS where
  /-- Las soluciones factibles no pasan de este largo. -/
  cota : Polynomial ℕ
  factible : List Bool × List Bool → Bool
  inicial : List Bool → List Bool
  vecino : List Bool × List Bool → List Bool
  costo : List Bool × List Bool → ℕ
  inicial_factible : ∀ x, factible (x, inicial x) = true
  vecino_factible : ∀ x s, factible (x, s) = true → factible (x, vecino (x, s)) = true
  corta : ∀ x s, factible (x, s) = true → s.length ≤ cota.eval x.length
  factible_pol : EsPolinomial factible
  inicial_pol : EsPolinomial inicial
  vecino_pol : EsPolinomial vecino
  costo_pol : EsPolinomial costo

namespace ProblemaPLS

variable (P : ProblemaPLS)

/-- Lo que se busca: una solución factible cuyo vecino no cuesta menos (un óptimo local). -/
def EsSolucion (x s : List Bool) : Prop :=
  P.factible (x, s) = true ∧ P.costo (x, s) ≤ P.costo (x, P.vecino (x, s))

/-- Un paso del descenso, para la instancia `x`. -/
def paso (x : List Bool) (s : List Bool) : List Bool := P.vecino (x, s)

/-- **El descenso desde la solución inicial termina**, en a lo sumo tantos pasos como su costo. No usa
`CierrePolinomial`: es la buena fundación de `ℕ`. -/
theorem desciende (x : List Bool) :
    ∃ k ≤ P.costo (x, P.inicial x), P.EsSolucion x ((P.paso x)^[k] (P.inicial x)) := by
  suffices H : ∀ c s, P.factible (x, s) = true → P.costo (x, s) ≤ c →
      ∃ k ≤ P.costo (x, s), P.EsSolucion x ((P.paso x)^[k] s) from
    H _ _ (P.inicial_factible x) le_rfl
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro s hs hc
    by_cases h : P.costo (x, s) ≤ P.costo (x, P.vecino (x, s))
    · exact ⟨0, Nat.zero_le _, hs, h⟩
    · obtain ⟨k, hk, hsol⟩ := ih _ (by omega) (P.vecino (x, s)) (P.vecino_factible x s hs) le_rfl
      refine ⟨k + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      exact hsol

/-- **Toda instancia tiene solución.** -/
theorem existe_solucion (x : List Bool) : ∃ s, P.EsSolucion x s := by
  obtain ⟨k, -, h⟩ := P.desciende x
  exact ⟨_, h⟩

/-- El verificador: ¿es factible, y su vecino no cuesta menos? -/
def verificador (q : List Bool × List Bool) : Bool :=
  P.factible q && decide (P.costo q ≤ P.costo (q.1, P.vecino q))

theorem verificador_iff (x s : List Bool) : P.verificador (x, s) = true ↔ P.EsSolucion x s := by
  simp [verificador, EsSolucion]

/-- El verificador es polinomial. -/
theorem verificador_pol : EsPolinomial P.verificador := by
  obtain ⟨hcomp, hpar, hfst, hand, hle⟩ := cierrePolinomial
  have h1 : EsPolinomial (fun q : List Bool × List Bool => (q.1, P.vecino q)) :=
    hpar _ _ (hfst (α := List Bool) (β := List Bool)) P.vecino_pol
  have h2 : EsPolinomial (fun q : List Bool × List Bool => P.costo (q.1, P.vecino q)) :=
    hcomp _ _ h1 P.costo_pol
  have h3 : EsPolinomial (fun q : List Bool × List Bool => (P.costo q, P.costo (q.1, P.vecino q))) :=
    hpar _ _ P.costo_pol h2
  have h4 : EsPolinomial (fun q : List Bool × List Bool => decide (P.costo q ≤ P.costo (q.1, P.vecino q))) :=
    hcomp _ _ h3 hle
  have h5 := hpar _ _ P.factible_pol h4
  exact hcomp _ _ h5 hand

/-- **Cada problema de PLS está en TFNP.** -/
theorem enTFNP : EnTFNP P.EsSolucion :=
  ⟨P.cota, P.verificador, P.verificador_pol, fun x s => (P.verificador_iff x s).symm,
    fun x s hs => P.corta x s hs.1, P.existe_solucion⟩

end ProblemaPLS

/-- **PLS**: los problemas de búsqueda que son la relación de solución de algún `ProblemaPLS`. -/
def PLS : Set Busqueda := {R | ∃ P : ProblemaPLS, R = P.EsSolucion}

/-- **PLS ⊆ TFNP.** Sin hipótesis: el cierre del tiempo polinomial está probado (`cierrePolinomial`). -/
theorem pls_sub_tfnp : PLS ⊆ TFNP := by
  rintro R ⟨P, rfl⟩
  exact P.enTFNP

/-- **Abierto: PLS ⊆ FP.** Para todo problema de PLS hay una función polinomial que da una solución. Seguir al vecino
no sirve en general: puede tardar un número exponencial de pasos. -/
def PLSEnFP : Prop :=
  ∀ P : ProblemaPLS, ∃ f : List Bool → List Bool, EsPolinomial f ∧ ∀ x, P.EsSolucion x (f x)

end Sagitta.Map
