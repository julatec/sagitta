import Sagitta.Map.Informacion.Repeticiones
import CslibFrontier.Computability.Complexity.Classes.Ladner.Density
import CslibFrontier.Computability.Complexity.Classes.Hierarchy

/-!
# Universal ⟹ diagonal ⟹ medio

El paso «universal ⟹ diagonal ⟹ medio» de las notas del proyecto («El fractal de SAT»), sección «Sin universalidad no hay
diagonal; sin diagonal no hay medio». José (25 nov 2026) resumió así lo que sobrevivió de la tricotomía:

> el medio aparece cuando el problema puede simular una máquina.

El mecanismo común es el punto fijo de Lawvere. Una familia `e : A → (A → B)` es **universal** (punto-sobreyectiva)
cuando toda función `A → B` es una de sus filas; si además `B` tiene una `f` sin punto fijo (la negación en `Bool`),
la fila `x ↦ f (e x x)` no puede estar: es la diagonal. En complejidad, las filas son los lenguajes de una clase
presentable (`M₀, M₁, …`) y la diagonal `D(i) = ¬ Mᵢ(i)` cae fuera de la clase. Ladner es la misma diagonal hecha
**perezosa**: en vez de negar a `Mᵢ` en el punto `i`, espera un testigo de la diferencia, y entre tanto copia a otro
conjunto. Lo único que la construcción pide de las clases es poder recorrerlas: una enumeración.

## Lo que se prueba

1. **Lawvere en la forma que hace falta** (§ 1). Se reusa `Informacion/Repeticiones.lean` (`lawvere`,
   `lawvere_debil`, `lawvere_contra`, `cantor_bool`, `cantor_prop`), sin duplicarlo. Aquí solo se nombra la
   contrapositiva con la palabra del informe: `sin_enumeracion_universal` (si `B` tiene una `f` sin punto fijo, no hay
   `e : A → (A → B)` punto-sobreyectiva) y `sin_enumeracion_universal_bool` (la negación).
2. **La diagonal de complejidad como instancia** (§ 2). Modelo abstracto: lenguajes sobre `α`, una enumeración
   `M : ℕ → Set α` de la clase y un índice sobreyectivo `idx : α → ℕ` (en cslib, `Ladner.index`, biyectivo sobre las
   palabras de bits). `diagonal M idx = {a | a ∉ M (idx a)}`.
   * `diagonal_mem_range_iff`: la diagonal está en la clase **si y solo si** `e a b := b ∈ M (idx a)` representa la
     diagonal modificada `x ↦ ¬ e x x`, la hipótesis de `lawvere_debil` con `f = Not`.
   * `diagonal_fuera`: la diagonal no está en la clase; sale de `lawvere_contra` con `Not_sin_punto_fijo`.
   * En cslib (`diagonal_fuera_de_presentable`): toda clase `RecursivelyPresentable encBits C` deja fuera su diagonal
     `{w | F (index w, w) = false}`, y con `recursivelyPresentable_P` hay un conjunto fuera de P
     (`diagonal_fuera_de_P`). La versión con máquinas y reloj, la de la jerarquía de tiempo, ya está en cslib-frontier:
     `Cslib.Complexity.diagonal_notMem_P` (`jerarquia_de_cslib`).
3. **Ladner como diagonal perezosa** (§ 3).
   * Modelo abstracto de Schöning (`schoning_abstracto`): `C₁ = range M₁` y `C₂ = range M₂` cerradas bajo variación
     finita, `A₁ ∉ C₁`, `A₂ ∉ C₂`. Entonces hay un `G` con `G.ite A₁ A₂ ∉ C₁` y `∉ C₂`. La prueba es la diagonal
     perezosa desnuda: se eligen testigos `w₀ < w₁ < …` de la diferencia, `w₂ᵢ ∈ A₁ ∆ M₁ i` y `w₂ᵢ₊₁ ∈ A₂ ∆ M₂ i`
     (existen porque la clausura bajo variación finita hace infinita cada diferencia), y `G = {w₂ᵢ}`. **El único
     ingrediente es la enumeración**: las hipótesis son `C = range M`, nada más. `fuera_de_la_entrelazada`: el
     conjunto mezclado no es ninguna fila de la enumeración entrelazada `M₁ 0, M₂ 0, M₁ 1, …`; es la conclusión de la
     diagonal (§ 2) contra una familia, con la negación reemplazada por «esperar un testigo».
   * La versión efectiva es la de cslib-frontier (`Cslib.Complexity.exists_mem_P_ite_notMem`, Schöning 1982): con las
     enumeraciones **computables** (`RecursivelyPresentable`) el `G` sale en P. `schoning_de_enumeraciones` la
     reenuncia con las dos presentabilidades como hipótesis con nombre (`Enumeracion`).
   * `ladner_de_enumeraciones`: Ladner hacia abajo (para `B` decidible fuera de P hay `G ∈ P` con `G.ite ∅ B` fuera
     de P y estrictamente debajo de `B`) **a partir de las dos enumeraciones** (de P y del grado de `B`) como
     hipótesis; `ladner_cslib_universal` las descarga con `recursivelyPresentable_P` y
     `recursivelyPresentable_polyTimeDegree` y recupera `Cslib.Complexity.exists_mem_P_ite_empty_lt`.
4. **El contraste «sin universalidad no hay diagonal»** (§ 4). Es **un ejemplo, no un teorema de dicotomía**.
   * La plantilla fija de las constantes (`constantes : Bool → (Bool → Bool)`): `f = not` no tiene punto fijo, y no
     pasa nada, porque la familia no es punto-sobreyectiva sobre sí misma (`constantes_no_universal`): la diagonal
     modificada es `not`, que no es una fila (`constantes_no_representan_diagonal`), y queda fuera sin paradoja ni
     jerarquía: es una función más que la plantilla no habla.
   * El otro ingrediente: sin negación no hay diagonal. Con `B = Unit` toda familia es universal
     (`unit_universal`) y Lawvere no concluye nada.
   * Un conjunto finito de lenguajes sobre un alfabeto infinito no es cerrado bajo variación finita si no es vacío
     (`finita_no_cerrada`): la construcción de Schöning ni se puede plantear.

## Gödel, en paralelo

Es la misma forma que la del primer teorema de incompletitud (Testigo 7, `DiagonalGodel.lean`): la aritmética de
Robinson Q es **universal** (representa las funciones computables, en particular su propia sustitución), y por la
diagonal tiene enunciados independientes; la de Presburger (la suma sin el producto) no representa la
multiplicación, no puede montar su propia diagonal y es **decidible y completa**. Q contra Presburger es el par
«universal contra plantilla» de la lógica.

## Honestidad: qué dirección es la profunda

* La dirección «universal ⟹ medio» se **hereda de Ladner** (Schöning, en cslib-frontier) y, una vez que la clase se
  puede enumerar, es casi trivial: § 3 la reduce a elegir testigos.
* La dirección profunda es la otra, «sin universalidad no hay medio»: para los CSP de plantilla finita, que no
  simulan máquinas, la dicotomía de **Bulatov y Zhuk** (2017). **No se prueba aquí**; en Sagitta está como hipótesis
  con nombre en `TresInterruptores.lean` y en `DicotomiaBooleana.lean` (el caso booleano, Schaefer).
* Los intermedios **naturales** que se conjeturan (factorización, isomorfismo de grafos) no vienen de una diagonal:
  usan otro mecanismo, el exceso de estructura (simetrías, aritmética) que los deja lejos de ser NP-completos. Este
  archivo no dice nada de ellos.

## Lo que NO se prueba

* Que la diagonal de § 2 sea **decidible** (en cslib haría falta componer `F` con `w ↦ (index w, w)` en tiempo
  computable); la versión con reloj, decidible en tiempo exponencial, es la de cslib (`computableInO_diagonal`).
* Que la presentabilidad sea **necesaria** para el medio en general: el contraste de § 4 es un ejemplo.
* Bulatov–Zhuk.
-/

namespace Sagitta.Map.Borde.UniversalDiagonal

open Function Set
open Sagitta.Map.Informacion.Repeticiones

/-! ## 1. Lawvere en la forma que hace falta -/

section Lawvere

variable {A B : Type*}

/-- **Universal** (punto-sobreyectiva): toda función `A → B` es una fila de `e`. -/
def Universal (e : A → A → B) : Prop := Surjective e

/-- **Lawvere**: una familia universal obliga a que toda `f : B → B` tenga un punto fijo (`Repeticiones.lawvere`,
que es `Function.exists_fixed_point_of_surjective` de Mathlib). -/
theorem universal_punto_fijo {e : A → A → B} (he : Universal e) (f : B → B) : ∃ b, f b = b :=
  lawvere e he f

/-- **Contrapositiva**: si `B` tiene una `f` sin punto fijo, no hay enumeración universal de `A → B` por `A`. -/
theorem sin_enumeracion_universal (f : B → B) (hf : ∀ b, f b ≠ b) (e : A → A → B) : ¬ Universal e := fun he =>
  let ⟨b, hb⟩ := universal_punto_fijo he f
  hf b hb

/-- Con la negación de `Bool`: es `Repeticiones.cantor_bool`. -/
theorem sin_enumeracion_universal_bool (e : A → A → Bool) : ¬ Universal e :=
  sin_enumeracion_universal (fun b => !b) not_sin_punto_fijo e

end Lawvere

/-! ## 2. La diagonal de complejidad como instancia -/

section Diagonal

variable {α : Type*}

/-- **El lenguaje diagonal** de una enumeración `M` de lenguajes sobre `α`, con el índice `idx`: `a ∈ D` si y solo si
`a ∉ M (idx a)`. -/
def diagonal (M : ℕ → Set α) (idx : α → ℕ) : Set α := {a | a ∉ M (idx a)}

/-- La familia de Lawvere de una enumeración: `e a b` es «`b ∈ M (idx a)`». -/
def familia (M : ℕ → Set α) (idx : α → ℕ) : α → α → Prop := fun a b => b ∈ M (idx a)

/-- **La diagonal está en la clase si y solo si la familia representa la diagonal modificada con `f = Not`.** Es la
hipótesis de `lawvere_debil`, dicha con lenguajes. -/
theorem diagonal_mem_range_iff (M : ℕ → Set α) {idx : α → ℕ} (hidx : Surjective idx) :
    diagonal M idx ∈ range M ↔ Representa (familia M idx) (fun x => ¬ familia M idx x x) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨a, rfl⟩ := hidx k
    exact ⟨a, fun x => by simp only [familia, hk, diagonal, mem_ofPred_eq]⟩
  · rintro ⟨a, ha⟩
    refine ⟨idx a, Set.ext fun x => ?_⟩
    have := ha x
    simp only [familia] at this
    simp only [diagonal, mem_ofPred_eq, this]

/-- **La diagonal no está en la clase**: Lawvere con `f = Not`, que no tiene punto fijo. -/
theorem diagonal_fuera (M : ℕ → Set α) {idx : α → ℕ} (hidx : Surjective idx) :
    diagonal M idx ∉ range M := fun h =>
  lawvere_contra (familia M idx) Not Not_sin_punto_fijo ((diagonal_mem_range_iff M hidx).1 h)

/-- Sin pasar por Lawvere, para comparar: es la prueba de siempre, y es la misma. -/
theorem diagonal_fuera_directa (M : ℕ → Set α) {idx : α → ℕ} (hidx : Surjective idx) :
    diagonal M idx ∉ range M := by
  rintro ⟨k, hk⟩
  obtain ⟨a, rfl⟩ := hidx k
  have h : a ∈ M (idx a) ↔ a ∈ diagonal M idx := by rw [hk]
  simp only [diagonal, mem_ofPred_eq] at h
  tauto

/-- **Universal es exactamente lo que falla**: si una clase `C = range M` contiene la diagonal de su propia
enumeración, la familia es universal para la diagonal modificada, y Lawvere lo prohíbe. Dicho como cerradura: una
clase enumerada por sus propios índices no es cerrada bajo «negar la diagonal». -/
theorem no_cerrada_bajo_diagonal (M : ℕ → Set α) {idx : α → ℕ} (hidx : Surjective idx) :
    ¬ (∀ N : ℕ → Set α, range N ⊆ range M → diagonal N idx ∈ range M) := fun h =>
  diagonal_fuera M hidx (h M subset_rfl)

end Diagonal

/-! ### La instancia de cslib: clases recursivamente presentables -/

section Cslib

open Cslib.Complexity Turing.MultiTapeTM

/-- La enumeración `i ↦ {w | F (i, w) = true}` de una presentación. -/
def filas (F : ℕ × List Bool → Bool) : ℕ → Set (List Bool) := fun i => {w | F (i, w) = true}

theorem index_surjective : Surjective Ladner.index := fun k => ⟨Ladner.word k, Ladner.index_word k⟩

/-- **Toda clase recursivamente presentable deja fuera su diagonal** `{w | F (index w, w) = false}`. -/
theorem diagonal_fuera_de_presentable {C : Set (Set (List Bool))} {F : ℕ × List Bool → Bool}
    (hC : C = range (filas F)) : {w | F (Ladner.index w, w) = false} ∉ C := by
  rw [hC]
  have : {w | F (Ladner.index w, w) = false} = diagonal (filas F) Ladner.index := by
    ext w
    simp [diagonal, filas]
  rw [this]
  exact diagonal_fuera _ index_surjective

/-- La forma con la definición de cslib: una clase presentable tiene un conjunto fuera, y es su diagonal. -/
theorem existe_fuera_de_presentable {C : Set (Set (List Bool))} (hC : RecursivelyPresentable encBits C) :
    ∃ F : ℕ × List Bool → Bool, {w | F (Ladner.index w, w) = false} ∉ C := by
  obtain ⟨F, -, hF⟩ := hC
  exact ⟨F, diagonal_fuera_de_presentable hF⟩

/-- **La diagonal contra P**: con la enumeración de P de cslib (`recursivelyPresentable_P`, las máquinas con reloj
polinomial), su diagonal no está en P. -/
theorem diagonal_fuera_de_P : ∃ F : ℕ × List Bool → Bool, {w | F (Ladner.index w, w) = false} ∉ Cslib.Complexity.P encBits :=
  existe_fuera_de_presentable recursivelyPresentable_P

/-- **La versión con máquinas y reloj es la de cslib**: la diagonal con reloj `2^n` (que lee la descripción de una
máquina al principio de la entrada, la corre y niega) no está en P. Es la jerarquía de tiempo. -/
theorem jerarquia_de_cslib : {x | Cslib.Complexity.diagonal x = true} ∉ Cslib.Complexity.P encBits :=
  Cslib.Complexity.diagonal_notMem_P

end Cslib

/-! ## 3. Ladner como diagonal perezosa -/

section Perezosa

/-- La sucesión de testigos: `w 0 ∈ S 0` y `w (k + 1) ∈ S (k + 1)` mayor que `w k`. -/
noncomputable def testigo (S : ℕ → Set ℕ) (hS : ∀ k, (S k).Infinite) : ℕ → ℕ
  | 0 => (hS 0).nonempty.some
  | k + 1 => Classical.choose ((hS (k + 1)).exists_gt (testigo S hS k))

theorem testigo_mem (S : ℕ → Set ℕ) (hS : ∀ k, (S k).Infinite) : ∀ k, testigo S hS k ∈ S k
  | 0 => (hS 0).nonempty.some_mem
  | k + 1 => (Classical.choose_spec ((hS (k + 1)).exists_gt (testigo S hS k))).1

theorem testigo_lt (S : ℕ → Set ℕ) (hS : ∀ k, (S k).Infinite) (k : ℕ) :
    testigo S hS k < testigo S hS (k + 1) :=
  (Classical.choose_spec ((hS (k + 1)).exists_gt (testigo S hS k))).2

theorem testigo_strictMono (S : ℕ → Set ℕ) (hS : ∀ k, (S k).Infinite) : StrictMono (testigo S hS) :=
  strictMono_nat_of_lt_succ (testigo_lt S hS)

/-- La diferencia que hay que atestiguar en la etapa `k`: con `A₁` contra `M₁ (k/2)` en las pares, con `A₂` contra
`M₂ (k/2)` en las impares. -/
def etapa (A₁ A₂ : Set ℕ) (M₁ M₂ : ℕ → Set ℕ) (k : ℕ) : Set ℕ :=
  if k % 2 = 0 then symmDiff A₁ (M₁ (k / 2)) else symmDiff A₂ (M₂ (k / 2))

/-- **La diagonal perezosa, desnuda.** Si cada `A₁ ∆ M₁ i` y cada `A₂ ∆ M₂ i` es infinita, hay un `G` tal que el
conjunto mezclado `G.ite A₁ A₂` (igual a `A₁` en `G`, a `A₂` fuera) no es ninguna fila de `M₁` ni de `M₂`. -/
theorem perezosa (A₁ A₂ : Set ℕ) (M₁ M₂ : ℕ → Set ℕ) (h₁ : ∀ i, (symmDiff A₁ (M₁ i)).Infinite)
    (h₂ : ∀ i, (symmDiff A₂ (M₂ i)).Infinite) :
    ∃ G : Set ℕ, ∀ i, G.ite A₁ A₂ ≠ M₁ i ∧ G.ite A₁ A₂ ≠ M₂ i := by
  have hS : ∀ k, (etapa A₁ A₂ M₁ M₂ k).Infinite := fun k => by
    unfold etapa; split_ifs
    · exact h₁ _
    · exact h₂ _
  set w := testigo _ hS
  have hw := testigo_strictMono _ hS
  refine ⟨range (fun i => w (2 * i)), fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hm := testigo_mem _ hS (2 * i)
    simp only [etapa, Nat.mul_mod_right, ite_true, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at hm
    have hG : w (2 * i) ∈ range (fun i => w (2 * i)) := ⟨i, rfl⟩
    have hx : w (2 * i) ∈ (range fun i => w (2 * i)).ite A₁ A₂ ↔ w (2 * i) ∈ A₁ := by
      simp [Set.ite, hG]
    rw [h] at hx
    rcases hm with ⟨ha, hn⟩ | ⟨hn, ha⟩
    · exact hn (hx.2 ha)
    · exact ha (hx.1 hn)
  · have hm := testigo_mem _ hS (2 * i + 1)
    have hmod : (2 * i + 1) % 2 = 1 := by omega
    have hdiv : (2 * i + 1) / 2 = i := by omega
    simp only [etapa, hmod, hdiv] at hm
    have hG : w (2 * i + 1) ∉ range (fun i => w (2 * i)) := by
      rintro ⟨j, hj⟩
      have := hw.injective hj
      omega
    have hx : w (2 * i + 1) ∈ (range fun i => w (2 * i)).ite A₁ A₂ ↔ w (2 * i + 1) ∈ A₂ := by
      simp [Set.ite, hG]
    rw [h] at hx
    rcases hm with ⟨ha, hn⟩ | ⟨hn, ha⟩
    · exact hn (hx.2 ha)
    · exact ha (hx.1 hn)

/-- La enumeración entrelazada `M₁ 0, M₂ 0, M₁ 1, M₂ 1, …`. -/
def entrelazada (M₁ M₂ : ℕ → Set ℕ) (k : ℕ) : Set ℕ := if k % 2 = 0 then M₁ (k / 2) else M₂ (k / 2)

/-- **El conjunto mezclado está fuera de la enumeración entrelazada**: es la conclusión de la diagonal de § 2
(`diagonal_fuera`) contra una sola familia, con «negar en el punto `i`» reemplazado por «esperar un testigo». -/
theorem fuera_de_la_entrelazada (A₁ A₂ : Set ℕ) (M₁ M₂ : ℕ → Set ℕ) (h₁ : ∀ i, (symmDiff A₁ (M₁ i)).Infinite)
    (h₂ : ∀ i, (symmDiff A₂ (M₂ i)).Infinite) :
    ∃ G : Set ℕ, G.ite A₁ A₂ ∉ range (entrelazada M₁ M₂) := by
  obtain ⟨G, hG⟩ := perezosa A₁ A₂ M₁ M₂ h₁ h₂
  refine ⟨G, ?_⟩
  rintro ⟨k, hk⟩
  unfold entrelazada at hk
  split_ifs at hk
  · exact (hG _).1 hk.symm
  · exact (hG _).2 hk.symm

/-- **Schöning en el modelo abstracto.** Dos clases **enumeradas** (`C = range M`), cerradas bajo variación finita,
y `A₁ ∉ C₁`, `A₂ ∉ C₂`: hay un `G` con `G.ite A₁ A₂` fuera de las dos. El único ingrediente es la enumeración; la
clausura bajo variación finita convierte «fuera» en «infinitamente distinto de cada fila»
(`ClosedUnderFiniteVariation.infinite_symmDiff` de cslib). -/
theorem schoning_abstracto {C₁ C₂ : Set (Set ℕ)} {M₁ M₂ : ℕ → Set ℕ} (e₁ : C₁ = range M₁) (e₂ : C₂ = range M₂)
    (hv₁ : Cslib.Complexity.ClosedUnderFiniteVariation C₁)
    (hv₂ : Cslib.Complexity.ClosedUnderFiniteVariation C₂)
    {A₁ A₂ : Set ℕ} (hA₁ : A₁ ∉ C₁) (hA₂ : A₂ ∉ C₂) :
    ∃ G : Set ℕ, G.ite A₁ A₂ ∉ C₁ ∧ G.ite A₁ A₂ ∉ C₂ := by
  obtain ⟨G, hG⟩ := perezosa A₁ A₂ M₁ M₂
    (fun i => hv₁.infinite_symmDiff hA₁ (e₁ ▸ ⟨i, rfl⟩))
    (fun i => hv₂.infinite_symmDiff hA₂ (e₂ ▸ ⟨i, rfl⟩))
  refine ⟨G, ?_, ?_⟩
  · rw [e₁]; rintro ⟨i, hi⟩; exact (hG i).1 hi.symm
  · rw [e₂]; rintro ⟨i, hi⟩; exact (hG i).2 hi.symm

end Perezosa

/-! ### La versión efectiva: la de cslib, con la enumeración a la vista -/

section Efectiva

open Cslib.Complexity Turing.MultiTapeTM

/-- **Enumeración** (universalidad efectiva): la clase es el rango de una familia computable. Es
`RecursivelyPresentable` de cslib con el nombre del informe. -/
def Enumeracion (C : Set (Set (List Bool))) : Prop := RecursivelyPresentable encBits C

/-- **Schöning (cslib), con las enumeraciones como hipótesis con nombre**: con enumeraciones computables el `G` sale
en P. -/
theorem schoning_de_enumeraciones {C₁ C₂ : Set (Set (List Bool))} (enum₁ : Enumeracion C₁)
    (enum₂ : Enumeracion C₂) (hv₁ : ClosedUnderFiniteVariation C₁) (hv₂ : ClosedUnderFiniteVariation C₂)
    {A₁ A₂ : Set (List Bool)} (hA₁ : IsDecidable A₁ encBits) (hA₂ : IsDecidable A₂ encBits) (h₁ : A₁ ∉ C₁)
    (h₂ : A₂ ∉ C₂) : ∃ G ∈ Cslib.Complexity.P encBits, G.ite A₁ A₂ ∉ C₁ ∧ G.ite A₁ A₂ ∉ C₂ :=
  exists_mem_P_ite_notMem enum₁ enum₂ hv₁ hv₂ hA₁ hA₂ h₁ h₂

/-- **Ladner hacia abajo desde dos enumeraciones**: la del grado de `B` y la de P. Lo demás (clausura bajo variación
finita, la reducción del mezclado a `B`) no depende de ellas. -/
theorem ladner_de_enumeraciones {B : Set (List Bool)} (hdec : IsDecidable B encBits) (hB : B ∉ Cslib.Complexity.P encBits)
    (enumGrado : Enumeracion (polyTimeDegree B)) (enumP : Enumeracion (Cslib.Complexity.P encBits)) :
    ∃ G ∈ Cslib.Complexity.P encBits, G.ite ∅ B ∉ Cslib.Complexity.P encBits ∧
      PolyTimeReducible encBits encBits (G.ite ∅ B) B ∧
      ¬ PolyTimeReducible encBits encBits B (G.ite ∅ B) := by
  obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩ := exists_notMem_and_mem_of_notMem_P hB
  have hempty : (∅ : Set (List Bool)) ∉ polyTimeDegree B := fun h => hB (h.2.mem_P empty_mem_P)
  obtain ⟨G, hG, hnotDeg, hnotP⟩ := schoning_de_enumeraciones enumGrado enumP
    (closedUnderFiniteVariation_polyTimeDegree hB) (closedUnderFiniteVariation_P encBits)
    (isDecidable_of_mem_P empty_mem_P) hdec hempty hB
  have hred : PolyTimeReducible encBits encBits (G.ite ∅ B) B :=
    polyTimeReducible_ite_of_mem_P hG empty_mem_P hb₀ hb₁
  exact ⟨G, hG, hnotP, hred, fun hback => hnotDeg ⟨hred, hback⟩⟩

/-- **Las dos enumeraciones existen** (cslib: `recursivelyPresentable_polyTimeDegree`, `recursivelyPresentable_P`), y
con ellas sale Ladner hacia abajo, que es `Cslib.Complexity.exists_mem_P_ite_empty_lt`. -/
theorem ladner_cslib_universal {B : Set (List Bool)} (hdec : IsDecidable B encBits) (hB : B ∉ Cslib.Complexity.P encBits) :
    ∃ G ∈ Cslib.Complexity.P encBits, G.ite ∅ B ∉ Cslib.Complexity.P encBits ∧
      PolyTimeReducible encBits encBits (G.ite ∅ B) B ∧
      ¬ PolyTimeReducible encBits encBits B (G.ite ∅ B) :=
  ladner_de_enumeraciones hdec hB (recursivelyPresentable_polyTimeDegree hdec hB) recursivelyPresentable_P

end Efectiva

/-! ## 4. El contraste: sin universalidad no hay diagonal (un ejemplo, no un teorema) -/

section Contraste

/-- **La plantilla fija de las constantes**: la fila `a` es la función constante `a`. -/
def constantes : Bool → Bool → Bool := fun a _ => a

/-- La plantilla no es universal: la identidad no es una fila. -/
theorem constantes_no_universal : ¬ Universal constantes := fun h => by
  obtain ⟨a, ha⟩ := h id
  have h0 : a = false := congrFun ha false
  have h1 : a = true := congrFun ha true
  exact Bool.false_ne_true (h0.symm.trans h1)

/-- La diagonal modificada con `not` es `not` mismo, y no es una fila: queda fuera **sin paradoja**. La negación no
tiene punto fijo, y no hay contradicción, porque la plantilla no habla de sí misma. -/
theorem constantes_no_representan_diagonal :
    ¬ Representa constantes (fun x => !(constantes x x)) ∧ (fun x => !(constantes x x)) = not := by
  refine ⟨fun ⟨a, ha⟩ => ?_, rfl⟩
  have := ha a
  simp [constantes] at this

/-- **Sin negación no hay diagonal**: con `B = Unit` toda familia (sobre un `A` no vacío o vacío) es universal, y
Lawvere no concluye nada (`Unit` no tiene función sin punto fijo). -/
theorem unit_universal {A : Type*} [Nonempty A] (e : A → A → Unit) : Universal e := fun _ =>
  ⟨Classical.arbitrary A, funext fun _ => rfl⟩

theorem unit_todo_punto_fijo (f : Unit → Unit) : ∃ b, f b = b := ⟨(), rfl⟩

/-- **Un conjunto finito de lenguajes no es cerrado bajo variación finita** (si no es vacío y el alfabeto es
infinito): las variaciones de un punto de un miembro ya son infinitas. Ahí la construcción de Schöning ni se plantea. -/
theorem finita_no_cerrada {α : Type} [Infinite α] {C : Set (Set α)} (hC : C.Finite) (hne : C.Nonempty) :
    ¬ Cslib.Complexity.ClosedUnderFiniteVariation C := by
  intro hv
  obtain ⟨L, hL⟩ := hne
  have hmem : ∀ a : α, symmDiff L {a} ∈ C := fun a =>
    hv hL (by rw [symmDiff_symmDiff_cancel_left]; exact Set.finite_singleton a)
  have hinj : Injective (fun a : α => symmDiff L {a}) := fun a b h => by
    have : symmDiff L (symmDiff L {a}) = symmDiff L (symmDiff L {b}) := by simp only at h; rw [h]
    simpa [symmDiff_symmDiff_cancel_left] using this
  exact Set.infinite_of_injective_forall_mem hinj hmem hC

end Contraste

end Sagitta.Map.Borde.UniversalDiagonal
