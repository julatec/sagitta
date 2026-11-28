import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# El NP infinito

José (25 nov 2026): la teoría descriptiva de conjuntos es la complejidad del infinito. Ahí la pregunta que en lo
finito no se sabe contestar tiene respuesta, y en ZF, sin cardinales grandes: **«NP ≠ P»** es «analítico ≠ Borel»
(Suslin 1917, al corregir a Lebesgue; Lusin), y **«P = NP ∩ coNP»** es el teorema de Suslin, Σ¹₁ ∩ Π¹₁ = Borel. Los
cardinales grandes solo empiezan a decidir la estructura fina desde Σ¹₂ (ver las notas del
proyecto).

## El diccionario

| finito (palabras `{0,1}*`)                      | infinito (espacio polaco, p. ej. `ℕ → ℕ`, `ℕ → Bool`) |
|-------------------------------------------------|-------------------------------------------------------|
| P: se decide en tiempo polinomial               | Borel (`claseP`, `MeasurableSet`), Δ¹₁                 |
| NP: `∃ y` corto, con un verificador en P        | analítico (`claseNP`, `AnalyticSet`), Σ¹₁: `∃ z ∈ ℕ^ℕ` con un cerrado |
| coNP: `∀ y` corto                               | coanalítico (`claseCoNP`), Π¹₁                         |
| P ⊆ NP ∩ coNP (trivial)                          | Borel ⊆ Σ¹₁ ∩ Π¹₁ (`claseP_sub_NP_inter_coNP`)        |
| ¿P = NP ∩ coNP? (abierto)                        | Suslin: Σ¹₁ ∩ Π¹₁ = Borel (`np_inter_coNP_iff_P`)     |
| pares NP disjuntos e interpolación factible      | Lusin: dos Σ¹₁ disjuntos se separan con un Borel (`separacion_lusin`) |
| ¿P ≠ NP? ¿NP ≠ coNP? (abiertos)                  | sí, por una diagonal (`np_ne_coNP_infinito`, `p_ne_np_infinito`) |

El testigo `∃ z` del lado infinito es una sucesión entera, no una palabra corta: lo que en lo finito cuesta (la cota
polinomial del certificado) en lo infinito no se mide, y por eso la diagonal pasa. En lo finito la misma diagonal choca
con las barreras (relativización, pruebas naturales, algebrización).

## La separación de Lusin y Razborov

Un **par NP disjunto** `(A, B)` es **separable en P** si hay un `C ∈ P` con `A ⊆ C` y `B ∩ C = ∅`. La interpolación
factible de un sistema de pruebas (Krajíček 1997, Pudlák) dice que de una refutación corta de «`x ∈ A ∧ x ∈ B`» sale
un circuito separador pequeño; Razborov (1995, *Unprovability of lower bounds on circuit size in certain fragments of
bounded arithmetic*) usa exactamente eso: si `S¹₂(α)` (o `S²₂(α)`) probara cotas inferiores superpolinomiales para
circuitos, interpolando se rompería un generador pseudoaleatorio. En lo infinito el teorema de separación es **verdad
siempre** (Lusin 1927): dos analíticos disjuntos se separan con un Borel (`separacion_lusin`), y Suslin es el caso
`B = Aᶜ`. En lo finito la separación de todos los pares NP disjuntos es falsa si existen funciones de un solo sentido
seguras (Grollmann–Selman 1988; el par canónico de un sistema de pruebas se separa si y solo si el sistema tiene
interpolación factible).

## La diagonal

Para `X = ℕ → K` (`K = ℕ`: espacio de Baire; `K = Bool`: espacio de Cantor) se arma un **conjunto analítico
universal** `U ⊆ X × X`:

1. `W ⊆ X × Y` (con `Y = X × X`) es un **abierto universal** (`W`, `isOpen_W`, `W_universal`): con una base numerable
   `B n` de `Y`, `(p, y) ∈ W ↔ ∃ n, p n ≠ k₀ ∧ y ∈ B n`. Todo abierto de `Y` es una sección `W_p` (`p n = k₁` si y
   solo si `B n ⊆ O`).
2. `U_p = {x | ∃ z ∈ ℕ^ℕ, (p, (x, z)) ∉ W}` es la proyección de la sección cerrada `Wᶜ_p`. Todo analítico de `X`
   es una `U_p` (`U_universal`): si `A = range f` con `f : ℕ^ℕ → X` continua, `A` es la proyección del cerrado
   `{(x, z) | f z = x}` de `X × ℕ^ℕ`; si `A = ∅`, del cerrado vacío. El testigo `z` vive siempre en `ℕ^ℕ`, también
   en el espacio de Cantor.
3. La diagonal `D = {x | (x, x) ∈ U}` es analítica (proyección de un cerrado, `diagonal_analitica`), y `Dᶜ` no es
   analítico: si `Dᶜ = U_p`, entonces `p ∈ D ↔ p ∉ D` (`compl_diagonal_no_analitica`).

Entonces **NP ≠ coNP en el infinito** (`np_ne_coNP_infinito`) y, como P ⊆ coNP, **P ≠ NP** (`p_ne_np_infinito`).
Es la prueba de Suslin–Lusin, la misma diagonal de la jerarquía de tiempo: sin cota de recursos que la frene.

## El contraste finito

En **árboles de decisión** (consultas) la pregunta finita sí tiene respuesta, y es la de Suslin: P = NP ∩ coNP.
Si `C₀(f)` y `C₁(f)` son las complejidades de certificado (cuántos bits hay que mostrar para convencer de `f = 0` y
de `f = 1`), entonces `D(f) ≤ C₀(f) · C₁(f)` (Blum–Impagliazzo 1987, Hartmanis–Hemachandra, Tardos; en
Buhrman–de Wolf 2002): cada certificado de 1 corta a todo certificado de 0, así que consultar
un certificado de 1 entero baja en uno el `C₀` de lo que queda. Está probado abajo, sobre un árbol de decisión propio
(`Arbol`, `arbol_de_certificados`, `prof_le_C1_mul_C0`): Sagitta tenía árboles de decisión solo como corridas de la
vuelta atrás contra `PHP` (`Sagitta.Map.RaizMuerta`). Para máquinas de Turing no se sabe.

La prueba clásica vale en ZF más elección numerable; en Mathlib usa `Classical.choice`, como todo lo demás
(`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Sagitta.Map.Informacion.NPInfinito

open MeasureTheory Set TopologicalSpace

/-! ## El diccionario -/

section Diccionario

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

/-- **«P» del infinito**: los conjuntos Borel (`MeasurableSet` en un espacio con `BorelSpace`), Δ¹₁. -/
def claseP (s : Set α) : Prop := MeasurableSet s

/-- **«NP» del infinito**: los conjuntos analíticos, Σ¹₁ (imágenes continuas de `ℕ → ℕ`, o vacíos); en un polaco,
proyecciones de cerrados de `α × ℕ^ℕ`: `x ∈ A ↔ ∃ z, (x, z) ∈ F`. -/
def claseNP (s : Set α) : Prop := AnalyticSet s

/-- **«coNP» del infinito**: los coanalíticos, Π¹₁ (complementos de analíticos). -/
def claseCoNP (s : Set α) : Prop := AnalyticSet sᶜ

/-- **P ⊆ NP ∩ coNP en el infinito**: todo Borel de un polaco es analítico, y su complemento también. -/
theorem claseP_sub_NP_inter_coNP [PolishSpace α] [BorelSpace α] {s : Set α} (h : claseP s) :
    claseNP s ∧ claseCoNP s :=
  ⟨MeasurableSet.analyticSet h, MeasurableSet.analyticSet (MeasurableSet.compl h)⟩

/-- **P = NP ∩ coNP en el infinito** (Suslin): un analítico de complemento analítico es Borel. -/
theorem np_inter_coNP_iff_P [PolishSpace α] [BorelSpace α] {s : Set α} :
    claseNP s ∧ claseCoNP s ↔ claseP s :=
  ⟨fun h => AnalyticSet.measurableSet_of_compl h.1 h.2, claseP_sub_NP_inter_coNP⟩

/-- **La separación de Lusin con el nombre del diccionario**: dos «NP» disjuntos se separan con un «P». Es el
análogo infinito de la separación de pares NP disjuntos y de la interpolación factible (Razborov 1995). -/
theorem separacion_lusin [T2Space α] [OpensMeasurableSpace α] {s t : Set α} (hs : claseNP s)
    (ht : claseNP t) (h : Disjoint s t) : ∃ u, claseP u ∧ s ⊆ u ∧ t ⊆ uᶜ := by
  obtain ⟨u, hsu, htu, hu⟩ := AnalyticSet.measurablySeparable hs ht h
  exact ⟨u, hu, hsu, fun x hx hxu => Set.disjoint_left.1 htu hx hxu⟩

end Diccionario

/-! ## La diagonal: un analítico universal -/

section Diagonal

variable {K : Type} [Inhabited K]

/-- El espacio `ℕ → K`: Baire si `K = ℕ`, Cantor si `K = Bool`. -/
abbrev Espacio (K : Type) := ℕ → K

/-- Una enumeración de una base numerable de un espacio segundo numerable no vacío. -/
theorem existe_base (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [Nonempty Y] :
    ∃ B : ℕ → Set Y, (∀ n, IsOpen (B n)) ∧
      ∀ O : Set Y, IsOpen O → ∀ y ∈ O, ∃ n, y ∈ B n ∧ B n ⊆ O := by
  have hb := isBasis_countableBasis Y
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hne : (countableBasis Y).Nonempty := by
    obtain ⟨v, hv, -, -⟩ := hb.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨v, hv⟩
  obtain ⟨B, hB⟩ := (countable_countableBasis Y).exists_eq_range hne
  refine ⟨B, fun n => hb.isOpen (hB ▸ Set.mem_range_self n), fun O hO z hz => ?_⟩
  obtain ⟨v, hv, hzv, hvO⟩ := hb.exists_subset_of_mem_open hz hO
  rw [hB] at hv
  obtain ⟨n, rfl⟩ := hv
  exact ⟨n, hzv, hvO⟩

variable {Y : Type} [TopologicalSpace Y]

/-- El abierto universal con parámetro en `ℕ → K`, dada la base `B`. -/
def W [TopologicalSpace K] (B : ℕ → Set Y) : Set (Espacio K × Y) :=
  {q | ∃ n, q.1 n ≠ default ∧ q.2 ∈ B n}

theorem isOpen_W [TopologicalSpace K] [DiscreteTopology K] (B : ℕ → Set Y) (hB : ∀ n, IsOpen (B n)) : IsOpen (W (K := K) B) := by
  have : W (K := K) B =
      ⋃ n, ((fun q : Espacio K × Y => q.1 n) ⁻¹' {default}ᶜ ∩ Prod.snd ⁻¹' B n) := by
    ext q; simp [W]
  rw [this]
  exact isOpen_iUnion fun n =>
    ((isOpen_discrete _).preimage ((continuous_apply n).comp continuous_fst)).inter
      ((hB n).preimage continuous_snd)

/-- Todo abierto es una sección del abierto universal. -/
theorem W_universal [TopologicalSpace K] [Nontrivial K] (B : ℕ → Set Y)
    (hbase : ∀ O : Set Y, IsOpen O → ∀ y ∈ O, ∃ n, y ∈ B n ∧ B n ⊆ O)
    (O : Set Y) (hO : IsOpen O) : ∃ p : Espacio K, ∀ y, (p, y) ∈ W B ↔ y ∈ O := by
  classical
  obtain ⟨k₁, hk₁⟩ := exists_ne (default : K)
  refine ⟨fun n => if B n ⊆ O then k₁ else default, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn, hy⟩
    by_cases h : B n ⊆ O
    · exact h hy
    · simp [h] at hn
  · intro hy
    obtain ⟨n, hyn, hn⟩ := hbase O hO y hy
    exact ⟨n, by simp [hn, hk₁], hyn⟩

/-- **El analítico universal** `U ⊆ X × X`, con `X = ℕ → K`: `x ∈ U_p ↔ ∃ z, (p, (x, z)) ∉ W`. -/
def U [TopologicalSpace K] (B : ℕ → Set (Espacio K × (ℕ → ℕ))) : Set (Espacio K × Espacio K) :=
  {q | ∃ z, (q.1, (q.2, z)) ∉ W B}

/-- La diagonal `D = {x | (x, x) ∈ U}`. -/
def D [TopologicalSpace K] (B : ℕ → Set (Espacio K × (ℕ → ℕ))) : Set (Espacio K) := {x | (x, x) ∈ U B}

/-- La diagonal es analítica: proyección del cerrado `{(x, z) | (x, (x, z)) ∉ W}`. -/
theorem diagonal_analitica [TopologicalSpace K] [DiscreteTopology K] [PolishSpace K] (B : ℕ → Set (Espacio K × (ℕ → ℕ))) (hB : ∀ n, IsOpen (B n)) :
    claseNP (D B) := by
  have hcerr : IsClosed {r : Espacio K × (ℕ → ℕ) | (r.1, (r.1, r.2)) ∉ W B} :=
    (isOpen_W B hB).isClosed_compl.preimage
      (continuous_fst.prodMk (continuous_fst.prodMk continuous_snd))
  have : D B = Prod.fst '' {r : Espacio K × (ℕ → ℕ) | (r.1, (r.1, r.2)) ∉ W B} := by
    ext x; simp [D, U]
  rw [this]
  exact AnalyticSet.image_of_continuous hcerr.analyticSet continuous_fst

/-- **Todo analítico es una sección de `U`.** Si `A = range f` con `f : ℕ^ℕ → X` continua, `A` es la proyección
del cerrado `{(x, z) | f z = x}`; si `A = ∅`, del cerrado vacío. -/
theorem U_universal [TopologicalSpace K] [DiscreteTopology K] [Nontrivial K] (B : ℕ → Set (Espacio K × (ℕ → ℕ)))
    (hbase : ∀ O : Set (Espacio K × (ℕ → ℕ)), IsOpen O → ∀ y ∈ O, ∃ n, y ∈ B n ∧ B n ⊆ O)
    {A : Set (Espacio K)} (hA : claseNP A) : ∃ p, ∀ x, (p, x) ∈ U B ↔ x ∈ A := by
  have hcl : ∃ C : Set (Espacio K × (ℕ → ℕ)), IsClosed C ∧ ∀ x, (∃ z, (x, z) ∈ C) ↔ x ∈ A := by
    unfold claseNP AnalyticSet at hA
    rcases hA with rfl | ⟨f, hf, rfl⟩
    · exact ⟨∅, isClosed_empty, by simp⟩
    · refine ⟨{r | f r.2 = r.1}, isClosed_eq (hf.comp continuous_snd) continuous_fst, ?_⟩
      intro x; simp
  obtain ⟨C, hC, hCA⟩ := hcl
  obtain ⟨p, hp⟩ := W_universal (K := K) B hbase Cᶜ hC.isOpen_compl
  refine ⟨p, fun x => ?_⟩
  rw [← hCA]
  simp only [U, Set.mem_ofPred_eq]
  exact exists_congr fun z => by rw [hp]; simp

/-- **El complemento de la diagonal no es analítico**: si `Dᶜ = U_p`, `p ∈ D ↔ p ∉ D`. -/
theorem compl_diagonal_no_analitica [TopologicalSpace K] [DiscreteTopology K] [Nontrivial K] (B : ℕ → Set (Espacio K × (ℕ → ℕ)))
    (hbase : ∀ O : Set (Espacio K × (ℕ → ℕ)), IsOpen O → ∀ y ∈ O, ∃ n, y ∈ B n ∧ B n ⊆ O) :
    ¬ claseCoNP (D B) := by
  intro h
  obtain ⟨p, hp⟩ := U_universal B hbase h
  have := hp p
  simp only [Set.mem_compl_iff] at this
  exact iff_not_self (a := p ∈ D B) this

/-- **NP ≠ coNP en el infinito** (Suslin–Lusin): en `ℕ → K` hay un analítico cuyo complemento no lo es. -/
theorem np_ne_coNP_infinito [TopologicalSpace K] [DiscreteTopology K] [PolishSpace K]
    [Nontrivial K] : ∃ s : Set (Espacio K), claseNP s ∧ ¬ claseCoNP s := by
  obtain ⟨B, hB, hbase⟩ := existe_base (Espacio K × (ℕ → ℕ))
  exact ⟨D B, diagonal_analitica B hB, compl_diagonal_no_analitica B hbase⟩

/-- **P ≠ NP en el infinito**: en `ℕ → K` hay un analítico que no es Borel. -/
theorem p_ne_np_infinito [TopologicalSpace K] [DiscreteTopology K] [PolishSpace K]
    [Nontrivial K] [MeasurableSpace K] [BorelSpace K] : ∃ s : Set (Espacio K), claseNP s ∧ ¬ claseP s := by
  obtain ⟨s, hs, hns⟩ := np_ne_coNP_infinito (K := K)
  exact ⟨s, hs, fun hp => hns (claseP_sub_NP_inter_coNP hp).2⟩

/-- La forma de la pregunta: no todo «NP» del infinito es «P». -/
theorem no_np_sub_p [TopologicalSpace K] [DiscreteTopology K] [PolishSpace K]
    [Nontrivial K] [MeasurableSpace K] [BorelSpace K] : ¬ ∀ s : Set (Espacio K), claseNP s → claseP s := by
  intro h
  obtain ⟨s, hs, hns⟩ := p_ne_np_infinito (K := K)
  exact hns (h s hs)

/-- **En el espacio de Baire** `ℕ → ℕ`: un analítico que no es Borel. -/
theorem p_ne_np_baire : ∃ s : Set (ℕ → ℕ), claseNP s ∧ ¬ claseP s := p_ne_np_infinito (K := ℕ)

/-- **En el espacio de Cantor** `ℕ → Bool`, el análogo de `{0,1}*`: un analítico que no es Borel. -/
theorem p_ne_np_cantor : ∃ s : Set (ℕ → Bool), claseNP s ∧ ¬ claseP s :=
  p_ne_np_infinito (K := Bool)

/-- **NP ≠ coNP en el espacio de Cantor.** -/
theorem np_ne_coNP_cantor : ∃ s : Set (ℕ → Bool), claseNP s ∧ ¬ claseCoNP s :=
  np_ne_coNP_infinito (K := Bool)

end Diagonal

/-! ## El contraste finito: P = NP ∩ coNP en árboles de decisión

Si toda entrada de valor 1 tiene un certificado de a lo sumo `a` bits (`C₁(f) ≤ a`) y toda entrada de valor 0 uno de
a lo sumo `b` (`C₀(f) ≤ b`), hay un árbol de decisión de profundidad `≤ a · b` (`prof_le_C1_mul_C0`). La prueba:
consultar los bits de un certificado de 1; en cada hoja, todo certificado de 0 cortaba a ese certificado (si no,
mezclando se tendría una entrada con valor 0 y 1), así que el `C₀` de lo que queda baja en uno. -/

section ContrasteFinito

variable {n : ℕ}

/-- Árbol de decisión sobre `n` bits: una hoja con la respuesta, o una consulta a un bit con un subárbol por cada
respuesta (`false` a la izquierda). -/
inductive Arbol (n : ℕ) where
  | hoja : Bool → Arbol n
  | consulta : Fin n → Arbol n → Arbol n → Arbol n

namespace Arbol

def eval : Arbol n → (Fin n → Bool) → Bool
  | hoja b, _ => b
  | consulta i t₀ t₁, x => if x i then t₁.eval x else t₀.eval x

def prof : Arbol n → ℕ
  | hoja _ => 0
  | consulta _ t₀ t₁ => max t₀.prof t₁.prof + 1

end Arbol

open Arbol

/-- El subcubo de una restricción parcial. -/
def cubo (ρ : Fin n → Option Bool) : Set (Fin n → Bool) :=
  {x | ∀ i v, ρ i = some v → x i = v}

/-- `S` certifica el valor de `f` en `x` dentro del conjunto `Q`. -/
def Cert (f : (Fin n → Bool) → Bool) (Q : Set (Fin n → Bool)) (x : Fin n → Bool)
    (S : Finset (Fin n)) : Prop :=
  ∀ y ∈ Q, (∀ i ∈ S, y i = x i) → f y = f x

/-- Toda entrada de `Q` con valor `v` tiene un certificado de tamaño `≤ c`. -/
def Acotado (f : (Fin n → Bool) → Bool) (Q : Set (Fin n → Bool)) (v : Bool) (c : ℕ) : Prop :=
  ∀ x ∈ Q, f x = v → ∃ S : Finset (Fin n), S.card ≤ c ∧ Cert f Q x S

/-- Consultar todas las variables de la lista y seguir con `k` en la restricción que resulta. -/
def consultarTodas (k : (Fin n → Option Bool) → Arbol n) :
    List (Fin n) → (Fin n → Option Bool) → Arbol n
  | [], ρ => k ρ
  | i :: L, ρ => consulta i (consultarTodas k L (Function.update ρ i (some false)))
      (consultarTodas k L (Function.update ρ i (some true)))

theorem prof_consultarTodas (k : (Fin n → Option Bool) → Arbol n) (M : ℕ)
    (hk : ∀ ρ, (k ρ).prof ≤ M) : ∀ L ρ, (consultarTodas k L ρ).prof ≤ L.length + M
  | [], ρ => by simpa [consultarTodas] using hk ρ
  | i :: L, ρ => by
    have h0 := prof_consultarTodas k M hk L (Function.update ρ i (some false))
    have h1 := prof_consultarTodas k M hk L (Function.update ρ i (some true))
    simp only [consultarTodas, prof, List.length_cons]
    omega

theorem mem_cubo_update {ρ : Fin n → Option Bool} {i : Fin n} {v : Bool} {y : Fin n → Bool}
    (h : y ∈ cubo ρ) (hv : y i = v) : y ∈ cubo (Function.update ρ i (some v)) := by
  intro j w hj
  by_cases hji : j = i
  · subst hji; simp only [Function.update_self, Option.some.injEq] at hj; rw [← hj]; exact hv
  · exact h j w (by simpa [Function.update_of_ne hji] using hj)

theorem cubo_update_sub {ρ : Fin n → Option Bool} {i : Fin n} {x y : Fin n → Bool}
    (hx : x ∈ cubo ρ) (hy : y ∈ cubo (Function.update ρ i (some (x i)))) :
    y ∈ cubo ρ ∧ y i = x i := by
  have hyi : y i = x i := hy i (x i) (by simp)
  refine ⟨fun j w hj => ?_, hyi⟩
  by_cases hji : j = i
  · subst hji; rw [hyi]; exact hx j w hj
  · exact hy j w (by simpa [Function.update_of_ne hji] using hj)

/-- Lo que deja la consulta de todas las variables de `L` en la entrada `x`. -/
theorem eval_consultarTodas (k : (Fin n → Option Bool) → Arbol n) (x : Fin n → Bool) :
    ∀ L ρ, x ∈ cubo ρ → ∃ ρ', (consultarTodas k L ρ).eval x = (k ρ').eval x ∧ x ∈ cubo ρ' ∧
      cubo ρ' ⊆ cubo ρ ∧ ∀ i ∈ L, ∀ y ∈ cubo ρ', y i = x i
  | [], ρ, hx => ⟨ρ, rfl, hx, subset_rfl, by simp⟩
  | i :: L, ρ, hx => by
    have hx1 : x ∈ cubo (Function.update ρ i (some (x i))) := mem_cubo_update hx rfl
    obtain ⟨ρ', he, hx', hsub, hL⟩ := eval_consultarTodas k x L _ hx1
    refine ⟨ρ', ?_, hx', fun y hy => (cubo_update_sub hx (hsub hy)).1, ?_⟩
    · cases hxi : x i
      · simp only [consultarTodas, eval, hxi] at he ⊢; simpa [hxi] using he
      · simp only [consultarTodas, eval, hxi] at he ⊢; simpa [hxi] using he
    · intro j hj y hy
      rcases List.mem_cons.1 hj with rfl | hj
      · exact (cubo_update_sub hx (hsub hy)).2
      · exact hL j hj y hy

/-- **D ≤ C₁ · C₀ sobre un subcubo**: si toda entrada de valor 1 tiene un certificado de tamaño `≤ a` y toda
entrada de valor 0 uno de tamaño `≤ b`, hay un árbol de profundidad `≤ a · b` que calcula `f`. -/
theorem arbol_de_certificados (f : (Fin n → Bool) → Bool) (a : ℕ) :
    ∀ b ρ, Acotado f (cubo ρ) true a → Acotado f (cubo ρ) false b →
      ∃ T : Arbol n, T.prof ≤ a * b ∧ ∀ x ∈ cubo ρ, T.eval x = f x := by
  classical
  intro b
  induction b with
  | zero =>
    intro ρ _ h0
    by_cases hz : ∃ x ∈ cubo ρ, f x = false
    · obtain ⟨x₀, hx₀, hf₀⟩ := hz
      obtain ⟨S, hS, hc⟩ := h0 x₀ hx₀ hf₀
      have hS0 : S = ∅ := Finset.card_eq_zero.1 (by omega)
      refine ⟨hoja false, by simp [prof], fun x hx => ?_⟩
      have := hc x hx (by simp [hS0])
      simp [eval, this, hf₀]
    · refine ⟨hoja true, by simp [prof], fun x hx => ?_⟩
      simp only [not_exists, not_and] at hz
      cases h : f x
      · exact absurd h (hz x hx)
      · rfl
  | succ b ih =>
    intro ρ h1 h0
    by_cases hu : ∃ x ∈ cubo ρ, f x = true
    · obtain ⟨x₁, hx₁, hf₁⟩ := hu
      obtain ⟨S, hS, hc₁⟩ := h1 x₁ hx₁ hf₁
      -- la condición para seguir en una hoja de la consulta
      let H : (Fin n → Option Bool) → Prop := fun ρ' =>
        Acotado f (cubo ρ') true a ∧ Acotado f (cubo ρ') false b
      let k : (Fin n → Option Bool) → Arbol n := fun ρ' =>
        if h : H ρ' then Classical.choose (ih ρ' h.1 h.2) else hoja true
      have hk : ∀ ρ', (k ρ').prof ≤ a * b := by
        intro ρ'
        by_cases h : H ρ'
        · simp only [k, h, ↓reduceDIte]; exact (Classical.choose_spec (ih ρ' h.1 h.2)).1
        · simp [k, h, prof]
      refine ⟨consultarTodas k S.toList ρ, ?_, fun x hx => ?_⟩
      · have := prof_consultarTodas k (a * b) hk S.toList ρ
        rw [Finset.length_toList] at this
        calc _ ≤ S.card + a * b := this
          _ ≤ a + a * b := by omega
          _ = a * (b + 1) := by rw [Nat.mul_succ]; omega
      · obtain ⟨ρ', he, hx', hsub, hL⟩ := eval_consultarTodas k x S.toList ρ hx
        rw [he]
        -- las hipótesis valen en la hoja
        have hH : H ρ' := by
          refine ⟨fun z hz hfz => ?_, fun z hz hfz => ?_⟩
          · obtain ⟨T, hT, hcT⟩ := h1 z (hsub hz) hfz
            exact ⟨T, hT, fun y hy hyz => hcT y (hsub hy) hyz⟩
          · obtain ⟨S₀, hS₀, hc₀⟩ := h0 z (hsub hz) hfz
            -- un certificado de 0 corta a S
            have hcorta : (S₀ ∩ S).Nonempty := by
              by_contra hvac
              rw [Finset.not_nonempty_iff_eq_empty] at hvac
              let y : Fin n → Bool := fun i => if i ∈ S then x₁ i else z i
              have hy : y ∈ cubo ρ := by
                intro j w hj
                by_cases hjS : j ∈ S
                · simp only [y, hjS, ↓reduceIte]; exact hx₁ j w hj
                · simp only [y, hjS, ↓reduceIte]; exact hsub hz j w hj
              have e1 : f y = true := by
                rw [← hf₁]; exact hc₁ y hy (fun i hi => by simp [y, hi])
              have e0 : f y = false := by
                rw [← hfz]
                refine hc₀ y hy (fun i hi => ?_)
                have : i ∉ S := fun hiS => by
                  have : i ∈ S₀ ∩ S := Finset.mem_inter.2 ⟨hi, hiS⟩
                  rw [hvac] at this; simp at this
                simp [y, this]
              rw [e1] at e0; exact Bool.noConfusion e0
            refine ⟨S₀ \ S, ?_, fun y hy hyz => ?_⟩
            · have h1' := Finset.card_sdiff_add_card_inter S₀ S
              have h2' := hcorta.card_pos
              omega
            · refine hc₀ y (hsub hy) (fun i hi => ?_)
              by_cases hiS : i ∈ S
              · have hm : i ∈ S.toList := Finset.mem_toList.2 hiS
                rw [hL i hm y hy, hL i hm z hz]
              · exact hyz i (Finset.mem_sdiff.2 ⟨hi, hiS⟩)
        simp only [k, hH, ↓reduceDIte]
        exact (Classical.choose_spec (ih ρ' hH.1 hH.2)).2 x hx'
    · refine ⟨hoja false, by simp [prof], fun x hx => ?_⟩
      simp only [not_exists, not_and] at hu
      cases h : f x
      · rfl
      · exact absurd h (hu x hx)

/-- **D(f) ≤ C₁(f) · C₀(f)** en todo el cubo (`ρ = ninguna variable fija`). -/
theorem prof_le_C1_mul_C0 (f : (Fin n → Bool) → Bool) (a b : ℕ)
    (h1 : ∀ x, f x = true → ∃ S : Finset (Fin n), S.card ≤ a ∧
      ∀ y, (∀ i ∈ S, y i = x i) → f y = f x)
    (h0 : ∀ x, f x = false → ∃ S : Finset (Fin n), S.card ≤ b ∧
      ∀ y, (∀ i ∈ S, y i = x i) → f y = f x) :
    ∃ T : Arbol n, T.prof ≤ a * b ∧ ∀ x, T.eval x = f x := by
  have hc : ∀ x, x ∈ cubo (fun _ : Fin n => (none : Option Bool)) := fun x i v h => by simp at h
  obtain ⟨T, hT, he⟩ := arbol_de_certificados f a b (fun _ => none)
    (fun x _ hx => by obtain ⟨S, hS, h⟩ := h1 x hx; exact ⟨S, hS, fun y _ hy => h y hy⟩)
    (fun x _ hx => by obtain ⟨S, hS, h⟩ := h0 x hx; exact ⟨S, hS, fun y _ hy => h y hy⟩)
  exact ⟨T, hT, fun x => he x (hc x)⟩

end ContrasteFinito

end Sagitta.Map.Informacion.NPInfinito
