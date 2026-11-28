import Sagitta.Map.Informacion.Simetria
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Robar teoremas conservando la estructura

La idea es de José (25 nov 2026): si un morfismo conserva la estructura, los teoremas de la física que solo usan
esa estructura pasan a la computación. La estructura es la del «homomorfismo de los fenómenos»: un
grupo `G` que actúa sobre un espacio de estados `X` y una energía `E : X → ℝ`. Un **isomorfismo de estructuras**
(`IsoEstructura`) es una biyección `φ : X ≃ X'` con un isomorfismo de grupos `h : G ≃* G'` tal que
`φ (g • x) = h g • φ x` y `E' (φ x) = a · E x + b` con `a > 0` (los cambios afines de energía incluidos).

## Lo que se prueba

1. **La transferencia, en abstracto** (§ 1). «Todo lo que se define con el vocabulario de la estructura se transfiere»
   no se formaliza como teoría de modelos, sino como estos teoremas concretos:
   * el número de órbitas (`IsoEstructura.orbitas_eq`, por una biyección entre los cocientes);
   * los estados fundamentales: `x` es mínimo de `E` sii `φ x` lo es de `E'` (`esMinimo_iff`), la imagen del conjunto
     de mínimos es el conjunto de mínimos (`image_minimos`), cuántos hay (`card_minimos`) y la energía mínima, que
     va a su imagen afín (`energiaMin_eq`);
   * el estabilizador de cada estado, vía `h` (`map_stabilizer`, `card_stabilizer`), y con él la ruptura espontánea:
     un estado rompe la simetría sii su imagen la rompe (`rompe_iff`);
   * los niveles de energía (`card_nivel`) y, si `b = 0`, el número de estados de energía `0`, las soluciones
     (`card_soluciones`);
   * la invariancia misma de la energía (`invariante`).
2. **Ising ↔ MAX-CUT, exacto (Barahona)** (§ 2). Espines `σ : Fin n → ℤˣ`, `H(σ) = −Σ_{i<j} J_ij σ_i σ_j`, y el corte
   de `S = {i : σ_i = +1}`. Se prueba `H(σ) = −Σ_{i<j} J_ij + 2·cut_J(S)` (`ising_eq_corte`), para cualquier `J`: la
   suma es sobre los pares `i < j`, así que no hace falta pedir simetría ni diagonal nula. La simetría ℤ₂ de Ising
   (`σ ↦ −σ`, la acción de `ℤˣ`) va al complemento de `S`, y todo junto es un isomorfismo de estructuras con
   `a = 1/2`, `b = Σ J/2` (`isingCorte`). Por § 1: los estados fundamentales de `H` son exactamente los cortes de
   peso **mínimo** de `J` (`fundamental_iff_corte_min`); para un antiferroimán `J = −w` son los cortes de peso
   **máximo** de `w` (`antiferro_fundamental_iff_corte_max`), que es MAX-CUT. Con `J ≥ 0` (ferroimán) el mínimo es el
   corte vacío y no hay problema. Que el corte no cambia al complementar sale de la invariancia de Ising por
   transferencia (`corte_compl`), sin cuenta propia.
3. **SAT → vidrio de espín** (§ 3). Para una fórmula CNF (listas de literales `(i, b)`, verdadero si `x i = b`), la
   energía `E(x)` = número de cláusulas falsas es la evaluación en los espines `s_i = ±1` del polinomio
   `Σ_c Π_{(i,b) ∈ c} (1 − s(b)·X_i)/2` (`hamiltoniano`, un `MvPolynomial (Fin n) ℝ`; `eval_hamiltoniano`). Sus
   estados de energía `0` son las soluciones (`falsas_eq_cero_iff`), y si la fórmula es satisfacible, los estados
   fundamentales son exactamente las soluciones (`fundamental_iff_solucion`). Pasar de asignaciones a espines es un
   isomorfismo de estructuras con `a = 1`, `b = 0` (`satEspin`), con la negación global de un lado y `σ ↦ −σ` del
   otro. Corolario (por § 1): el mínimo del hamiltoniano es el mínimo de cláusulas falsas, MAX-SAT
   (`energiaMin_hamiltoniano`); tiene tantos estados de energía `0` como soluciones tiene la fórmula
   (`card_ceros_hamiltoniano`); y las órbitas coinciden (`orbitas_sat_espin`).

## Lo trivial y lo difícil (con honestidad)

Lo de § 1 es trivial una vez que hay isomorfismo: son cuentas de una línea, y por eso mismo valen para todo lo que se
diga con ese vocabulario. Lo difícil está en otra parte, y aquí no se hace:

* **Construir el morfismo.** Barahona (1982) y la traducción de SAT a un hamiltoniano son exactos porque cambian la
  descripción, no el problema. Las reducciones de Karp, en cambio, no preservan la geometría de los racimos de
  soluciones (cuántos hay, a qué distancia, cuánto se solapan): un isomorfismo en el sentido de § 1 es mucho más que
  una reducción polinomial, y casi ninguna reducción lo es.
* **Que el teorema físico sea riguroso.** Lo que se quiere robar suele venir de las réplicas o de la cavidad, que no
  son pruebas. Los casos en que ya se hizo, citados de memoria: Talagrand probó la fórmula de Parisi para el modelo
  de Sherrington–Kirkpatrick (`talagrand2006parisi`); Ding, Sly y Sun, el umbral de k-SAT para `k` grande
  (`ding2022satisfiability`); Gamarnik, la brecha de solapamiento como obstrucción a ciertos algoritmos
  (`gamarnik2021overlap`). Ninguno se formaliza aquí.

## Lo que NO se prueba

* Nada sobre la complejidad de encontrar el estado fundamental: la transferencia conserva *qué* es el mínimo, no
  cuánto cuesta hallarlo (eso lo da que `φ` sea computable en tiempo polinomial, y aquí no se mide).
* Ningún teorema de vidrios de espín (Parisi, el umbral, la brecha): solo el puente por el que pasarían.
* Nada sobre P contra NP.
-/

namespace Sagitta.Map.Informacion.Transferencia

open Finset MulAction
open Sagitta.Map.Informacion.Simetria (orbitas)

/-! ## 1. El principio de transferencia -/

/-- Un **isomorfismo de estructuras** entre `(G ↷ X, E)` y `(G' ↷ X', E')`: una biyección equivariante respecto de un
isomorfismo de grupos, que lleva la energía a una imagen afín creciente. -/
structure IsoEstructura (G X G' X' : Type*) [Group G] [MulAction G X] [Group G'] [MulAction G' X']
    (E : X → ℝ) (E' : X' → ℝ) where
  /-- La biyección de estados. -/
  φ : X ≃ X'
  /-- El isomorfismo de grupos. -/
  h : G ≃* G'
  /-- Equivariancia: `φ (g • x) = h g • φ x`. -/
  equivariante : ∀ (g : G) (x : X), φ (g • x) = h g • φ x
  /-- La pendiente del cambio de energía. -/
  a : ℝ
  /-- La ordenada del cambio de energía. -/
  b : ℝ
  a_pos : 0 < a
  /-- La energía: `E' ∘ φ = a · E + b`. -/
  energia : ∀ x, E' (φ x) = a * E x + b

/-- `x` es un estado fundamental de `E`. -/
def EsMinimo {X : Type*} (E : X → ℝ) (x : X) : Prop := ∀ y, E x ≤ E y

/-- La energía mínima, en un espacio finito y no vacío. -/
noncomputable def energiaMin {X : Type*} [Fintype X] [Nonempty X] (E : X → ℝ) : ℝ := univ.inf' univ_nonempty E

namespace IsoEstructura

variable {G X G' X' : Type*} [Group G] [MulAction G X] [Group G'] [MulAction G' X']
  {E : X → ℝ} {E' : X' → ℝ} (I : IsoEstructura G X G' X' E E')

include I

/-- La equivariancia lleva órbitas a órbitas, en los dos sentidos. -/
theorem mem_orbit_iff (x y : X) : x ∈ orbit G y ↔ I.φ x ∈ orbit G' (I.φ y) := by
  simp only [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨I.h g, (I.equivariante g y).symm⟩
  · rintro ⟨g', hg'⟩
    refine ⟨I.h.symm g', I.φ.injective ?_⟩
    rw [I.equivariante, MulEquiv.apply_symm_apply, hg']

/-- La biyección entre los espacios de órbitas. -/
def orbitasEquiv : orbitRel.Quotient G X ≃ orbitRel.Quotient G' X' :=
  Quotient.congr I.φ (fun x y => by rw [orbitRel_apply, orbitRel_apply]; exact I.mem_orbit_iff x y)

/-- **Se transfiere el número de órbitas.** -/
theorem orbitas_eq : orbitas G X = orbitas G' X' := Nat.card_congr I.orbitasEquiv

/-- **Se transfieren los estados fundamentales**: `x` es mínimo de `E` sii `φ x` lo es de `E'`. -/
theorem esMinimo_iff (x : X) : EsMinimo E x ↔ EsMinimo E' (I.φ x) := by
  constructor
  · intro hx y'
    obtain ⟨y, rfl⟩ := I.φ.surjective y'
    rw [I.energia, I.energia]
    have := mul_le_mul_of_nonneg_left (hx y) I.a_pos.le
    linarith
  · intro hx y
    have := hx (I.φ y)
    rw [I.energia, I.energia] at this
    exact le_of_mul_le_mul_left (by linarith) I.a_pos

/-- La imagen del conjunto de mínimos es el conjunto de mínimos. -/
theorem image_minimos : I.φ '' {x | EsMinimo E x} = {x' | EsMinimo E' x'} := by
  ext x'
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (I.esMinimo_iff x).1 hx
  · intro hx'
    refine ⟨I.φ.symm x', (I.esMinimo_iff _).2 (by simpa using hx'), by simp⟩

/-- Hay tantos estados fundamentales de un lado como del otro. -/
theorem card_minimos : Nat.card {x // EsMinimo E x} = Nat.card {x' // EsMinimo E' x'} :=
  Nat.card_congr (I.φ.subtypeEquiv I.esMinimo_iff)

/-- **La energía mínima va a su imagen afín.** -/
theorem energiaMin_eq [Fintype X] [Nonempty X] [Fintype X'] [Nonempty X'] :
    energiaMin E' = I.a * energiaMin E + I.b := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := X)) E
  have hmin : EsMinimo E x := fun y => hx ▸ Finset.inf'_le _ (mem_univ y)
  have hmin' := (I.esMinimo_iff x).1 hmin
  have h1 : energiaMin E' = E' (I.φ x) :=
    le_antisymm (Finset.inf'_le _ (mem_univ _)) (Finset.le_inf' _ _ fun y _ => hmin' y)
  rw [h1, I.energia, energiaMin, hx]

/-- El estabilizador se transfiere elemento a elemento, vía `h`. -/
theorem mem_stabilizer_iff (g : G) (x : X) : g ∈ stabilizer G x ↔ I.h g ∈ stabilizer G' (I.φ x) := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← I.equivariante, I.φ.injective.eq_iff]

/-- **Se transfiere el estabilizador**: es la imagen por `h`. -/
theorem map_stabilizer (x : X) :
    (stabilizer G x).map (I.h : G →* G') = stabilizer G' (I.φ x) := by
  ext g'
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (I.mem_stabilizer_iff g x).1 hg
  · intro hg'
    exact ⟨I.h.symm g', (I.mem_stabilizer_iff _ x).2 (by simpa using hg'), by simp⟩

/-- Los estabilizadores tienen el mismo tamaño. -/
theorem card_stabilizer (x : X) : Nat.card (stabilizer G' (I.φ x)) = Nat.card (stabilizer G x) := by
  rw [← I.map_stabilizer]
  exact Subgroup.card_map_of_injective I.h.injective

/-- **La ruptura espontánea se transfiere**: el estabilizador de `x` es todo `G` sii el de `φ x` es todo `G'`. -/
theorem rompe_iff (x : X) : stabilizer G x = ⊤ ↔ stabilizer G' (I.φ x) = ⊤ := by
  rw [← I.map_stabilizer]
  constructor
  · intro h
    rw [h, Subgroup.map_top_of_surjective _ I.h.surjective]
  · intro h
    rw [eq_top_iff]
    intro g _
    have : (I.h : G →* G') g ∈ (stabilizer G x).map (I.h : G →* G') := h ▸ Subgroup.mem_top _
    obtain ⟨g₀, hg₀, he⟩ := Subgroup.mem_map.1 this
    rwa [I.h.injective he] at hg₀

/-- **Se transfieren los niveles de energía**: hay tantos estados de energía `c` como de energía `a·c + b`. -/
theorem card_nivel (c : ℝ) : Nat.card {x // E x = c} = Nat.card {x' // E' x' = I.a * c + I.b} := by
  refine Nat.card_congr (I.φ.subtypeEquiv fun x => ?_)
  rw [I.energia]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact mul_left_cancel₀ I.a_pos.ne' (by linarith)

/-- **Se transfiere el número de soluciones** (estados de energía `0`) cuando el cambio de energía es lineal. -/
theorem card_soluciones (hb : I.b = 0) : Nat.card {x // E x = 0} = Nat.card {x' // E' x' = 0} := by
  rw [I.card_nivel 0, hb, mul_zero, add_zero]

/-- **Se transfiere la invariancia** de la energía. -/
theorem invariante (hE : ∀ (g : G) x, E (g • x) = E x) : ∀ (g' : G') x', E' (g' • x') = E' x' := by
  intro g' x'
  obtain ⟨x, rfl⟩ := I.φ.surjective x'
  obtain ⟨g, rfl⟩ := I.h.surjective g'
  rw [← I.equivariante, I.energia, I.energia, hE]

end IsoEstructura

/-! ## 2. Ising ↔ MAX-CUT (Barahona) -/

section Ising

variable {n : ℕ}

/-- Un espín `±1` como real. -/
def esp (u : ℤˣ) : ℝ := ((u : ℤ) : ℝ)

theorem esp_mul (u v : ℤˣ) : esp (u * v) = esp u * esp v := by simp [esp]

/-- Los pares `i < j`. -/
def pares (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

/-- **Ising sin campo**: `H(σ) = −Σ_{i<j} J_ij σ_i σ_j`. -/
noncomputable def ising (J : Fin n → Fin n → ℝ) (σ : Fin n → ℤˣ) : ℝ :=
  -∑ p ∈ pares n, J p.1 p.2 * esp (σ p.1) * esp (σ p.2)

/-- El peso total `Σ_{i<j} J_ij`. -/
noncomputable def pesoTotal (J : Fin n → Fin n → ℝ) : ℝ := ∑ p ∈ pares n, J p.1 p.2

/-- Un corte: un lado `S ⊆ Fin n`. Sinónimo de `Finset (Fin n)` para darle la acción de `ℤˣ` por complemento. -/
def Corte (n : ℕ) := Finset (Fin n)

/-- El lado de un corte. -/
def Corte.lado (S : Corte n) : Finset (Fin n) := S

/-- El corte de lado `s`. -/
def Corte.mk (s : Finset (Fin n)) : Corte n := s

instance : Fintype (Corte n) := inferInstanceAs (Fintype (Finset (Fin n)))
instance : DecidableEq (Corte n) := inferInstanceAs (DecidableEq (Finset (Fin n)))
instance : Nonempty (Corte n) := ⟨Corte.mk ∅⟩

@[simp] theorem Corte.lado_mk (s : Finset (Fin n)) : (Corte.mk s).lado = s := rfl
@[simp] theorem Corte.mk_lado (S : Corte n) : Corte.mk S.lado = S := rfl

theorem Corte.ext {S T : Corte n} (h : ∀ i, i ∈ S.lado ↔ i ∈ T.lado) : S = T := Finset.ext h

/-- `−1` complementa, `1` deja igual. -/
def Corte.accion (u : ℤˣ) (S : Corte n) : Corte n := if u = 1 then S else Corte.mk S.ladoᶜ

/-- `ℤˣ` actúa sobre los cortes: `−1` complementa. -/
instance : MulAction ℤˣ (Corte n) where
  smul := Corte.accion
  one_smul S := by change Corte.accion 1 S = S; simp [Corte.accion]
  mul_smul u v S := by
    change Corte.accion (u * v) S = Corte.accion u (Corte.accion v S)
    have h : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [Corte.accion, h]

theorem Corte.smul_def (u : ℤˣ) (S : Corte n) : u • S = if u = 1 then S else Corte.mk S.ladoᶜ := rfl

/-- **El peso del corte** `cut_J(S) = Σ_{i<j, i y j de lados distintos} J_ij`. -/
noncomputable def corte (J : Fin n → Fin n → ℝ) (S : Corte n) : ℝ :=
  ∑ p ∈ pares n, if (p.1 ∈ S.lado ↔ p.2 ∈ S.lado) then 0 else J p.1 p.2

/-- El lado `+1` de una configuración de espines, como biyección. -/
def ladoMas : (Fin n → ℤˣ) ≃ Corte n where
  toFun σ := Corte.mk (univ.filter fun i => σ i = 1)
  invFun S i := if i ∈ S.lado then 1 else -1
  left_inv σ := by
    funext i
    have h : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or (σ i) with hi | hi <;> simp [hi, h]
  right_inv S := by
    apply Corte.ext
    intro i
    by_cases h : i ∈ S.lado <;> simp [h]

@[simp] theorem mem_ladoMas (σ : Fin n → ℤˣ) (i : Fin n) : i ∈ (ladoMas σ).lado ↔ σ i = 1 := by
  simp [ladoMas]

/-- La cuenta de un par: `J σ_i σ_j = J − 2·[σ_i ≠ σ_j]·J`. -/
theorem termino (J : ℝ) (a b : ℤˣ) :
    J * esp a * esp b = J - 2 * (if (a = 1 ↔ b = 1) then 0 else J) := by
  have h : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
    simp [esp, h] <;> ring

/-- **Barahona**: `H(σ) = −Σ_{i<j} J_ij + 2·cut_J(S)` con `S` el lado `+1`. -/
theorem ising_eq_corte (J : Fin n → Fin n → ℝ) (σ : Fin n → ℤˣ) :
    ising J σ = -pesoTotal J + 2 * corte J (ladoMas σ) := by
  unfold ising pesoTotal corte
  simp only [mem_ladoMas]
  rw [Finset.sum_congr rfl fun p _ => termino (J p.1 p.2) (σ p.1) (σ p.2), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

/-- La equivariancia: `σ ↦ −σ` lleva el lado `+1` a su complemento. -/
theorem ladoMas_smul (u : ℤˣ) (σ : Fin n → ℤˣ) : ladoMas (u • σ) = u • ladoMas σ := by
  have h : (-1 : ℤˣ) ≠ 1 := by decide
  rw [Corte.smul_def]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp only [h, ↓reduceIte]
    apply Corte.ext
    intro i
    rw [Corte.lado_mk, Finset.mem_compl, mem_ladoMas, mem_ladoMas, Pi.smul_apply, smul_eq_mul]
    rcases Int.units_eq_one_or (σ i) with hi | hi <;> simp [hi, h]

/-- **Ising y MAX-CUT son la misma estructura**, con `G = ℤˣ` (la simetría ℤ₂) de los dos lados:
`cut_J(S) = ½·H(σ) + ½·Σ J`. -/
noncomputable def isingCorte (J : Fin n → Fin n → ℝ) :
    IsoEstructura ℤˣ (Fin n → ℤˣ) ℤˣ (Corte n) (ising J) (corte J) where
  φ := ladoMas
  h := MulEquiv.refl _
  equivariante u σ := ladoMas_smul u σ
  a := 1 / 2
  b := pesoTotal J / 2
  a_pos := by norm_num
  energia σ := by rw [ising_eq_corte]; ring

/-- La energía de Ising es invariante por `σ ↦ −σ`. -/
theorem ising_invariante (J : Fin n → Fin n → ℝ) (u : ℤˣ) (σ : Fin n → ℤˣ) : ising J (u • σ) = ising J σ := by
  unfold ising
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, esp_mul]
  have : esp u * esp u = 1 := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp [esp]
  linear_combination (J p.1 p.2 * esp (σ p.1) * esp (σ p.2)) * this

/-- **Robado**: el peso del corte no cambia al complementar, por transferencia de la invariancia de Ising. -/
theorem corte_compl (J : Fin n → Fin n → ℝ) (S : Corte n) : corte J (Corte.mk S.ladoᶜ) = corte J S := by
  have h : (-1 : ℤˣ) ≠ 1 := by decide
  have := IsoEstructura.invariante (isingCorte J) (ising_invariante J) (-1) S
  simpa only [Corte.smul_def, h, ↓reduceIte] using this

/-- **Los estados fundamentales de Ising son los cortes de peso mínimo de `J`.** -/
theorem fundamental_iff_corte_min (J : Fin n → Fin n → ℝ) (σ : Fin n → ℤˣ) :
    EsMinimo (ising J) σ ↔ ∀ T : Corte n, corte J (ladoMas σ) ≤ corte J T :=
  (isingCorte J).esMinimo_iff σ

/-- `cut_{−w} = −cut_w`. -/
theorem corte_neg (w : Fin n → Fin n → ℝ) (S : Corte n) : corte (fun i j => -w i j) S = -corte w S := by
  unfold corte
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

/-- **MAX-CUT**: en un antiferroimán `J = −w`, los estados fundamentales son los cortes de peso máximo de `w`. -/
theorem antiferro_fundamental_iff_corte_max (w : Fin n → Fin n → ℝ) (σ : Fin n → ℤˣ) :
    EsMinimo (ising fun i j => -w i j) σ ↔ ∀ T : Corte n, corte w T ≤ corte w (ladoMas σ) := by
  rw [fundamental_iff_corte_min]
  simp only [corte_neg, neg_le_neg_iff]

/-- La energía mínima de Ising y el corte mínimo, uno en función del otro. -/
theorem energiaMin_corte (J : Fin n → Fin n → ℝ) :
    energiaMin (corte J) = 1 / 2 * energiaMin (ising J) + pesoTotal J / 2 :=
  (isingCorte J).energiaMin_eq

/-- Las órbitas de las configuraciones bajo `σ ↦ −σ` y las de los cortes bajo el complemento: las mismas. -/
theorem orbitas_ising_corte : orbitas ℤˣ (Fin n → ℤˣ) = orbitas ℤˣ (Corte n) :=
  IsoEstructura.orbitas_eq (isingCorte (n := n) fun _ _ => 0)

end Ising

/-! ## 3. SAT → vidrio de espín -/

section SAT

variable {n : ℕ}

/-- Un literal `(i, b)`: verdadero en `x` si `x i = b`. -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- Una cláusula: la disyunción de sus literales. -/
abbrev Clausula (n : ℕ) := List (Literal n)

/-- Una fórmula CNF: la conjunción de sus cláusulas. -/
abbrev Formula (n : ℕ) := List (Clausula n)

/-- La cláusula se cumple. -/
def cumple (x : Fin n → Bool) (c : Clausula n) : Bool := c.any fun l => x l.1 == l.2

/-- `x` es solución de `F`. -/
def Satisface (F : Formula n) (x : Fin n → Bool) : Prop := ∀ c ∈ F, cumple x c = true

/-- **La energía de SAT**: el número de cláusulas falsas. -/
def falsas (F : Formula n) (x : Fin n → Bool) : ℕ := (F.map fun c => if cumple x c then 0 else 1).sum

/-- El signo de un valor de verdad: `true ↦ 1`, `false ↦ −1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

open MvPolynomial in
/-- El factor de un literal: `(1 − s(b)·X_i)/2`, que vale `1` si el literal es falso y `0` si es verdadero. -/
noncomputable def factor (l : Literal n) : MvPolynomial (Fin n) ℝ := C (1 / 2) * (1 - C (sgn l.2) * X l.1)

/-- El término de una cláusula: el producto de sus factores, `1` sii todos los literales son falsos. -/
noncomputable def terminoClausula (c : Clausula n) : MvPolynomial (Fin n) ℝ := (c.map factor).prod

/-- **El hamiltoniano de la fórmula**, un polinomio en los espines: `Σ_c Π_{(i,b) ∈ c} (1 − s(b)·X_i)/2`. -/
noncomputable def hamiltoniano (F : Formula n) : MvPolynomial (Fin n) ℝ := (F.map terminoClausula).sum

theorem eval_factor (x : Fin n → Bool) (l : Literal n) :
    MvPolynomial.eval (fun i => sgn (x i)) (factor l) = if x l.1 == l.2 then 0 else 1 := by
  unfold factor
  cases hx : x l.1 <;> cases hb : l.2 <;> simp [sgn, hx] <;> norm_num

theorem eval_terminoClausula (x : Fin n → Bool) (c : Clausula n) :
    MvPolynomial.eval (fun i => sgn (x i)) (terminoClausula c) = if cumple x c then 0 else 1 := by
  unfold terminoClausula cumple
  induction c with
  | nil => simp
  | cons l c ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, eval_factor, List.any_cons]
    cases x l.1 == l.2 <;> simp

/-- **El polinomio es exactamente la energía**: evaluado en los espines `s_i = sgn(x_i)`, cuenta las cláusulas
falsas. -/
theorem eval_hamiltoniano (F : Formula n) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => sgn (x i)) (hamiltoniano F) = (falsas F x : ℝ) := by
  unfold hamiltoniano falsas
  induction F with
  | nil => simp
  | cons c F ih =>
    rw [List.map_cons, List.sum_cons, map_add, ih, eval_terminoClausula, List.map_cons, List.sum_cons]
    split_ifs <;> simp

/-- **Energía `0` es ser solución.** -/
theorem falsas_eq_cero_iff (F : Formula n) (x : Fin n → Bool) : falsas F x = 0 ↔ Satisface F x := by
  unfold falsas Satisface
  induction F with
  | nil => simp
  | cons c F ih =>
    rw [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    cases cumple x c <;> simp

/-- **Si la fórmula es satisfacible, los estados fundamentales son exactamente las soluciones.** -/
theorem fundamental_iff_solucion (F : Formula n) (hF : ∃ x₀, Satisface F x₀) (x : Fin n → Bool) :
    EsMinimo (fun y => (falsas F y : ℝ)) x ↔ Satisface F x := by
  obtain ⟨x₀, h₀⟩ := hF
  constructor
  · intro hx
    have := hx x₀
    dsimp only at this
    rw [(falsas_eq_cero_iff F x₀).2 h₀] at this
    exact (falsas_eq_cero_iff F x).1 (by exact_mod_cast le_antisymm this (Nat.cast_nonneg _))
  · intro hx y
    dsimp only
    rw [(falsas_eq_cero_iff F x).2 hx]
    exact_mod_cast Nat.zero_le _

/-- Negar si `u = −1`. -/
def negarSi (u : ℤˣ) (b : Bool) : Bool := if u = 1 then b else !b

/-- `ℤˣ` actúa sobre los valores de verdad: `−1` niega. -/
scoped instance accionBool : MulAction ℤˣ Bool where
  smul := negarSi
  one_smul b := by change negarSi 1 b = b; simp [negarSi]
  mul_smul u v b := by
    change negarSi (u * v) b = negarSi u (negarSi v b)
    have h : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      cases b <;> simp [negarSi, h]

/-- El espín de un valor de verdad. -/
def aEspin (b : Bool) : ℤˣ := if b then 1 else -1

/-- Valores de verdad y espines, como biyección. -/
def boolEspin : Bool ≃ ℤˣ where
  toFun := aEspin
  invFun u := decide (u = 1)
  left_inv b := by cases b <;> decide
  right_inv u := by rcases Int.units_eq_one_or u with rfl | rfl <;> decide

theorem esp_aEspin (b : Bool) : esp (aEspin b) = sgn b := by cases b <;> simp [esp, aEspin, sgn]

/-- La energía del lado de los espines: el hamiltoniano evaluado en `σ`. -/
noncomputable def energiaEspin (F : Formula n) (σ : Fin n → ℤˣ) : ℝ :=
  MvPolynomial.eval (fun i => esp (σ i)) (hamiltoniano F)

/-- **SAT y su vidrio de espín son la misma estructura**, con `G = ℤˣ` (negar todo, o `σ ↦ −σ`), `a = 1`, `b = 0`. -/
noncomputable def satEspin (F : Formula n) :
    IsoEstructura ℤˣ (Fin n → Bool) ℤˣ (Fin n → ℤˣ) (fun x => (falsas F x : ℝ)) (energiaEspin F) where
  φ := Equiv.piCongrRight fun _ => boolEspin
  h := MulEquiv.refl _
  equivariante u x := by
    funext i
    have h : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [Equiv.piCongrRight_apply, Pi.smul_apply, MulEquiv.refl_apply, smul_eq_mul]
    change aEspin (negarSi u (x i)) = u * aEspin (x i)
    rcases Int.units_eq_one_or u with rfl | rfl <;> cases x i <;>
      simp [negarSi, aEspin, h]
  a := 1
  b := 0
  a_pos := one_pos
  energia x := by
    unfold energiaEspin
    simp only [Equiv.piCongrRight_apply, one_mul, add_zero]
    change MvPolynomial.eval (fun i => esp (aEspin (x i))) (hamiltoniano F) = _
    simp only [esp_aEspin]
    exact eval_hamiltoniano F x

/-- **MAX-SAT es el estado fundamental**: el mínimo del hamiltoniano es el mínimo de cláusulas falsas. -/
theorem energiaMin_hamiltoniano (F : Formula n) :
    energiaMin (energiaEspin F) = energiaMin fun x => (falsas F x : ℝ) := by
  rw [(satEspin F).energiaMin_eq]
  simp [satEspin]

/-- **El hamiltoniano tiene tantos estados de energía `0` como soluciones tiene la fórmula.** -/
theorem card_ceros_hamiltoniano (F : Formula n) :
    Nat.card {σ : Fin n → ℤˣ // energiaEspin F σ = 0} = Nat.card {x : Fin n → Bool // Satisface F x} := by
  rw [← (satEspin F).card_soluciones rfl]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    rw [← falsas_eq_cero_iff]; exact_mod_cast Iff.rfl)

/-- Las órbitas de las asignaciones bajo la negación global y las de los espines bajo `σ ↦ −σ`: las mismas. -/
theorem orbitas_sat_espin : orbitas ℤˣ (Fin n → Bool) = orbitas ℤˣ (Fin n → ℤˣ) :=
  IsoEstructura.orbitas_eq (satEspin (n := n) [])

end SAT

end Sagitta.Map.Informacion.Transferencia
