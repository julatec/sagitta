import Sagitta.Map.ConsumoNP
import Mathlib.Probability.ProductMeasure

/-!
# Ω entero: el espacio compacto de las corridas infinitas, con sus dos medidas

`Consumo.lean` y `ConsumoNP.lean` cortaron Ω en `n` elecciones. Aquí Ω es el espacio de **todas** las corridas
infinitas de elecciones binarias, `ℕ → Bool`, con la topología producto (el conjunto de Cantor: compacto). Es el espacio
de corridas de `FormaDelTiempo.lean` para el paso que agrega un bit (`crece`): una corrida es la historia de sus
prefijos (`historia_corrida`, `corrida_historia`).

## La medida aditiva, generada por los cilindros

El cilindro de un prefijo `q` (`cil q`) son las corridas que empiezan por `q`. Es abierto y cerrado a la vez
(`isClopen_cil`). La medida `μΩ` es el producto infinito de monedas justas (`Measure.infinitePi` de Mathlib), la única
que le da a cada cilindro `2^(−|q|)` (`medida_cil`); los cilindros generan la σ-álgebra. Es la medida de conteo de
`Consumo.lean`, normalizada: el árbol completo de `n` elecciones reparte la masa 1 en `2ⁿ` pedazos de `2^(−n)`.

Los cortes de un detector (`ConsumoNP.lean`) cubren Ω (`cortes_cubren_omega`) y sus masas suman 1
(`suma_cortes_omega`): la igualdad de Kraft, ahora como medida de probabilidad.

## La compacidad: lo demoníaco tiene profundidad común

Si el detector mata **toda** corrida infinita en algún momento (la raíz muerta, `x ∉ L`), la mata antes de una
profundidad **común** `T` (`corte_uniforme`). No es un argumento nuevo: es `demoniaca_acotada` de
`FormaDelTiempo.lean` aplicado al paso `crece`, y esa es compacidad (König). Sin compacidad no vale: con infinitas
opciones por paso, cada corrida podría morir a su propio tiempo, sin cota.

## La medida maxitiva, como supremo

La profundidad a la que muere cada corrida (`profCorte`) es lo que la búsqueda tiene en la pila al llegar ahí. La medida
maxitiva de un conjunto de corridas (`nu`) es el supremo de esa profundidad; es maxitiva (`nu_union`, Shilkret) y, por
compacidad, **finita** en Ω entero (`nu_omega_le`). La aditiva (`μΩ`) es una probabilidad. Una cuenta cuántos
cilindros hay que pagar, la otra cuánto hay que recordar.

## Lo que no

La integral de Shilkret en general (aquí solo la medida de conjuntos) y la medida de lo que **no** muere cuando la raíz
está viva.
-/

namespace Sagitta.Map
namespace Consumo

open MeasureTheory Set Topology Tiempo
open scoped ENNReal

/-- Ω: las corridas infinitas de elecciones binarias. -/
abbrev Omega := ℕ → Bool

/-- Los primeros `n` bits de una corrida. -/
def pre (ω : Omega) (n : ℕ) : List Bool := List.ofFn fun i : Fin n => ω i

@[simp] theorem length_pre (ω : Omega) (n : ℕ) : (pre ω n).length = n := by simp [pre]

theorem pre_succ (ω : Omega) (n : ℕ) : pre ω (n + 1) = pre ω n ++ [ω n] := by
  simp only [pre]; rw [List.ofFn_succ_last]; simp

theorem getElem_pre (ω : Omega) (n i : ℕ) (h : i < (pre ω n).length) : (pre ω n)[i] = ω i := by
  simp [pre]

theorem pre_prefijo (ω : Omega) {m n : ℕ} (h : m ≤ n) : pre ω m <+: pre ω n := by
  induction n with
  | zero => obtain rfl : m = 0 := by omega
            exact List.prefix_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact List.prefix_refl _
    · rw [pre_succ]; exact (ih (by omega)).trans (List.prefix_append _ _)

/-- Un prefijo de la historia es la historia de ese largo. -/
theorem pre_de_prefijo {ω : Omega} {q : List Bool} {n : ℕ} (h : q <+: pre ω n) : pre ω q.length = q := by
  have hl : q.length ≤ n := by simpa using h.length_le
  exact (List.prefix_of_prefix_length_le (pre_prefijo ω hl) h (by simp)).eq_of_length (by simp)

/-! ## Los cilindros -/

/-- El cilindro de `q`: las corridas que empiezan por `q`. -/
def cil (q : List Bool) : Set Omega := {ω | pre ω q.length = q}

theorem cil_eq_pi (q : List Bool) :
    cil q = Set.pi (↑(Finset.range q.length)) (fun i => {q.getD i false}) := by
  ext ω
  simp only [cil, mem_ofPred_eq, Set.mem_pi, Finset.coe_range, mem_Iio, mem_singleton_iff]
  constructor
  · intro h i hi
    have := getElem_pre ω q.length i (by simpa using hi)
    rw [List.getD_eq_getElem _ _ hi, ← this]
    simp [h]
  · intro h
    apply List.ext_getElem (by simp)
    intro i h1 h2
    rw [getElem_pre, h i h2, List.getD_eq_getElem _ _ h2]

/-- **Los cilindros son abiertos y cerrados.** -/
theorem isClopen_cil (q : List Bool) : IsClopen (cil q) := by
  rw [cil_eq_pi]
  exact ⟨isClosed_set_pi fun _ _ => isClosed_discrete _,
    isOpen_set_pi (Finset.finite_toSet _) fun _ _ => isOpen_discrete _⟩

theorem measurableSet_cil (q : List Bool) : MeasurableSet (cil q) := by
  rw [cil_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _) fun _ _ => measurableSet_singleton _

/-- Ω es compacto. -/
theorem isCompact_omega : IsCompact (univ : Set Omega) := isCompact_univ

/-! ## La medida aditiva -/

/-- La moneda justa. -/
noncomputable def moneda : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

theorem moneda_singleton (b : Bool) : moneda {b} = 2⁻¹ := by
  simp [moneda]

instance : IsProbabilityMeasure moneda := by
  constructor
  rw [moneda, smul_apply, Measure.count_univ]
  simp [ENat.card_eq_coe_fintype_card, ENNReal.inv_mul_cancel]

/-- La medida de Ω: monedas justas independientes, el producto infinito. -/
noncomputable def muOmega : Measure Omega := Measure.infinitePi fun _ => moneda

instance : IsProbabilityMeasure muOmega := by unfold muOmega; infer_instance

/-- **Cada cilindro pesa `2^(−|q|)`.** -/
theorem medida_cil (q : List Bool) : muOmega (cil q) = 2⁻¹ ^ q.length := by
  rw [cil_eq_pi, muOmega, Measure.infinitePi_pi _ fun _ _ => measurableSet_singleton _]
  simp [moneda_singleton]

/-! ## Los cortes de un detector, sobre Ω entero -/

/-- Los cortes cubren Ω: toda corrida infinita cae en algún cilindro de corte. -/
theorem cortes_cubren_omega (det : List Bool → Bool) (N : ℕ) (ω : Omega) :
    ∃ q ∈ cortes det N [], ω ∈ cil q := by
  obtain ⟨q, hq, hpre⟩ := cortes_cubren det N [] (pre ω N) (by simp)
  exact ⟨q, hq, pre_de_prefijo (by simpa using hpre)⟩

theorem union_cortes (det : List Bool → Bool) (N : ℕ) : (⋃ q ∈ cortes det N [], cil q) = univ :=
  eq_univ_of_forall fun ω => by
    obtain ⟨q, hq, h⟩ := cortes_cubren_omega det N ω
    exact Set.mem_iUnion₂.2 ⟨q, hq, h⟩

/-- **Kraft como probabilidad**: las masas de los cilindros de corte suman 1. -/
theorem suma_cortes_omega (det : List Bool → Bool) (N : ℕ) :
    ((cortes det N []).map fun q => muOmega (cil q)).sum = 1 := by
  have hk := kraft det N []
  simp only [List.length_nil, Nat.zero_add] at hk
  have hle : ∀ q ∈ cortes det N [], q.length ≤ N := fun q hq => by
    simpa using (cortes_prefijo det N [] q hq).2
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  -- `2^(−a) = 2^(N−a) · 2^(−N)` cuando `a ≤ N`.
  have hpaso : ∀ q ∈ cortes det N [],
      muOmega (cil q) = ((2 ^ (N - q.length) : ℕ) : ℝ≥0∞) * 2⁻¹ ^ N := by
    intro q hq
    rw [medida_cil]
    have ha := hle q hq
    obtain ⟨c, hc⟩ : ∃ c, N = q.length + c := ⟨N - q.length, by omega⟩
    have hc1 : (2 : ℝ≥0∞) ^ c * 2⁻¹ ^ c = 1 := by
      rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (pow_ne_zero _ h2) (ENNReal.pow_ne_top h2')]
    rw [hc, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    calc (2⁻¹ : ℝ≥0∞) ^ q.length = 2⁻¹ ^ q.length * (2 ^ c * 2⁻¹ ^ c) := by rw [hc1, mul_one]
      _ = 2 ^ c * (2⁻¹ ^ q.length * 2⁻¹ ^ c) := by ring
  rw [List.map_congr_left hpaso, List.sum_map_mul_right]
  have hcast : ((cortes det N []).map fun q => ((2 ^ (N - q.length) : ℕ) : ℝ≥0∞)).sum =
      (((cortes det N []).map fun q => 2 ^ (N - q.length)).sum : ℕ) := by
    rw [Nat.cast_list_sum, List.map_map]; rfl
  rw [hcast, hk, Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.inv_pow,
    ENNReal.mul_inv_cancel (pow_ne_zero _ h2) (ENNReal.pow_ne_top h2')]

/-! ## La compacidad: lo demoníaco tiene profundidad común -/

/-- La topología de las historias: discreta. Solo para hablar de corridas de `crece`. -/
@[reducible] def topoHistorias : TopologicalSpace (List Bool) := ⊥

attribute [local instance] topoHistorias

theorem discretaHistorias : DiscreteTopology (List Bool) := ⟨rfl⟩

attribute [local instance] discretaHistorias

/-- El paso que agrega un bit: el árbol binario como `Paso` de `FormaDelTiempo.lean`. -/
def crece : Paso (List Bool) := fun l => {l ++ [false], l ++ [true]}

theorem crece_finito (l : List Bool) : (crece l).Finite := (Set.finite_singleton _).insert _

/-- La historia de una corrida infinita es una corrida de `crece`. -/
theorem historia_corrida (ω : Omega) : pre ω ∈ Corrida crece [] := by
  refine ⟨by simp [pre], fun n => ?_⟩
  rw [pre_succ]
  cases ω n <;> simp [crece]

/-- Y toda corrida de `crece` es la historia de una corrida infinita. -/
theorem corrida_historia {s : ℕ → List Bool} (hs : s ∈ Corrida crece []) : ∃ ω : Omega, s = pre ω := by
  obtain ⟨h0, hpaso⟩ := hs
  have hb : ∀ n, ∃ b, s (n + 1) = s n ++ [b] := fun n => by
    rcases hpaso n with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  choose b hb using hb
  refine ⟨b, funext fun n => ?_⟩
  induction n with
  | zero => simp [h0, pre]
  | succ n ih => rw [hb n, ih, pre_succ]

/-- **Profundidad común.** Si el detector mata toda corrida infinita en algún momento, hay una profundidad `T` antes
de la cual las mata todas. Es `demoniaca_acotada`: compacidad. -/
theorem corte_uniforme (det : List Bool → Bool) (h : ∀ ω : Omega, ∃ n, det (pre ω n) = true) :
    ∃ T, ∀ ω : Omega, ∃ n ≤ T, det (pre ω n) = true := by
  obtain ⟨T, hT⟩ := demoniaca_acotada crece_finito [] {q | det q = true} fun s hs => by
    obtain ⟨ω, rfl⟩ := corrida_historia hs
    exact h ω
  exact ⟨T, fun ω => hT _ (historia_corrida ω)⟩

/-! ## La medida maxitiva -/

/-- La profundidad a la que muere cada corrida: lo que la búsqueda tiene en la pila al llegar ahí. -/
noncomputable def profCorte (det : List Bool → Bool) (h : ∀ ω : Omega, ∃ n, det (pre ω n) = true)
    (ω : Omega) : ℕ := by
  classical exact Nat.find (h ω)

/-- La medida maxitiva de un conjunto de corridas: la mayor profundidad de corte. -/
noncomputable def nu (det : List Bool → Bool) (h : ∀ ω : Omega, ∃ n, det (pre ω n) = true) (A : Set Omega) :
    ℕ∞ := ⨆ ω ∈ A, (profCorte det h ω : ℕ∞)

/-- **Maxitiva** (Shilkret): la unión pesa el máximo, no la suma. -/
theorem nu_union (det : List Bool → Bool) (h : ∀ ω : Omega, ∃ n, det (pre ω n) = true) (A B : Set Omega) :
    nu det h (A ∪ B) = max (nu det h A) (nu det h B) := iSup_union

/-- **Finita en Ω entero**, por compacidad: la memoria de la búsqueda está acotada. -/
theorem nu_omega_le (det : List Bool → Bool) (h : ∀ ω : Omega, ∃ n, det (pre ω n) = true) :
    ∃ T : ℕ, nu det h univ ≤ T := by
  classical
  obtain ⟨T, hT⟩ := corte_uniforme det h
  refine ⟨T, iSup₂_le fun ω _ => ?_⟩
  obtain ⟨n, hn, hd⟩ := hT ω
  have : profCorte det h ω ≤ n := by unfold profCorte; convert Nat.find_min' (h ω) hd
  exact_mod_cast this.trans hn

/-! ## Controles -/

example : pre (fun i => decide (i = 1)) 3 = [false, true, false] := by decide

end Consumo
end Sagitta.Map
