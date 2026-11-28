import Sagitta.Map.Landau
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Del mundo discreto al continuo: la clase no es continua

Lo pidió José (24 nov 2026), después de las notas del proyecto («El borde es un hueco»). Es la forma formal de «la complejidad de
una máquina depende de toda la cola de su descripción». La discontinuidad no viene del tiempo, que es continuo, sino de
pasar a la clase asintótica.

## El modelo

Una descripción infinita es un punto del espacio de Cantor, `d : ℕ → Bool`, con la topología producto de Mathlib
(`Bool` discreto). La máquina de descripción `d` gasta `t d n = if d n then 2^n else n` en la entrada `n`.

## Lo que se prueba

* (a) **`t_continuo`**: el mapa `d ↦ t d`, de `ℕ → Bool` a `ℕ → ℕ` (topología producto), es continuo. Cada valor
  `t d n` depende de un solo bit.
* `t_pol_iff_finito`: `t d ∈ Pol ↔ {n | d n = true}.Finite`, con `pol_menor_dos_pow` de `Landau.lean`; y su corolario
  `t_pol_iff_finalmente`: `t d ∈ Pol ↔` `d` es finalmente `false` («la clase de `d` es la de una descripción finita»).
* (d) **`continuoEn_iff_prefijo`** (en un punto) y **`continuo_iff_prefijo`** (global): un mapa
  `F : (ℕ → Bool) → Bool` es continuo si y solo si en cada punto `d` su valor depende de un prefijo finito de `d`. Es la
  lectura de José: una decisión uniforme, que usa una parte finita de la descripción, es una función continua. Mathlib
  no trae este enunciado tal cual; trae los cilindros (`PiNat.cylinder`, con su base `PiNat.isTopologicalBasis_cylinders`)
  y la descripción de los vecindarios de un producto (`nhds_pi`, `Filter.mem_pi`), de donde sale aquí en pocas líneas.
* (b) **`clase_no_continua`**: `fun d => decide (t d ∈ Pol)` no es continua en **ningún** punto. En todo cilindro
  alrededor de `d` hay una descripción con cola toda `true` (no polinomial) y otra con cola toda `false` (polinomial).
* (c) **`parar_no_continuo`**: `fun d => decide (∃ n, d n = true)` no es continua en la sucesión toda `false`;
  `parar_continuo_en` lo es en todos los demás puntos.
* (f) **`oscila_fuera_de_pol`** y **`oscila_vuelve_abajo`**: si `d` tiene infinitos `true` e infinitos `false`, `t d ∉ Pol`
  y además `∃ᶠ n in atTop, t d n = n`, de modo que `¬ ∀ᶠ n in atTop, n ^ 2 < t d n` (`oscila_no_superpolinomial`).
  `t d` no es comparable con el borde de P: lo cruza para siempre. Control: `alterna`, que vale `true` en los pares.
* (e) **El análogo infinito de NP ∩ coNP = P es verdadero (Suslin).** Con la dicción de Sipser (P ↔ Borel,
  NP ↔ analítico = proyección de un cerrado, coNP ↔ complemento de analítico): `suslin_cantor` (un analítico de
  `ℕ → Bool` con complemento analítico es de Borel), `lusin_cantor` (dos analíticos disjuntos se separan con un Borel), y
  `proyeccion_analitica` (la proyección de un cerrado de `(ℕ → Bool) × (ℕ → ℕ)` es analítica). Son corolarios directos
  de `MeasureTheory.AnalyticSet.measurableSet_of_compl` y `AnalyticSet.measurablySeparable` de Mathlib; lo propio es solo
  ponerlos en el espacio de Cantor y la lectura. La σ-álgebra de `ℕ → Bool` es la producto, que es la de Borel
  (`borel_igual`).

## Lo que no se prueba

* El análogo infinito de P ≠ NP (que existe un analítico que no es de Borel) no está en Mathlib y no se intenta.
* En lo finito, el análogo de Lusin es `SeparacionDeLusinNP` (`FormaDelTiempo.lean`), que se espera **falso**
  (Grollmann–Selman), y NP ∩ coNP = P se cree falso (factorización). Aquí no se dice nada de eso: solo que la versión
  infinita es verdadera, de modo que la analogía de Sipser no se puede llevar a ciegas de un lado al otro.
* Relación (solo mencionada): con `tabla_rompe` de `UniversoCerrado.lean` (una descripción infinita sin la condición del
  prefijo es una tabla regalada), con la analogía de Sipser y con «El borde es un hueco».
-/

open Filter Topology Set MeasureTheory TopologicalSpace

namespace Sagitta.Map
namespace Continuo

open Tiempo

/-- El tiempo de la máquina de descripción `d` en la entrada `n`. -/
def t (d : ℕ → Bool) (n : ℕ) : ℕ := if d n then 2 ^ n else n

/-! ## (a) El tiempo es continuo -/

theorem t_continuo : Continuous (fun d : ℕ → Bool => t d) := by
  apply continuous_pi
  intro n
  have : (fun d : ℕ → Bool => t d n) = (fun b : Bool => if b then 2 ^ n else n) ∘ (fun d => d n) := rfl
  rw [this]
  exact continuous_of_discreteTopology.comp (continuous_apply n)

/-! ## La clase de `t d` -/

theorem t_pol_iff_finito (d : ℕ → Bool) : t d ∈ Pol ↔ {n | d n = true}.Finite := by
  constructor
  · rintro ⟨c, k, h⟩
    obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
    apply (Set.finite_lt_nat N).subset
    intro n hn
    simp only [mem_ofPred_eq] at hn ⊢
    by_contra hlt
    have h1 := h n
    have h2 := hN n (Nat.le_of_not_lt hlt)
    simp [t, hn] at h1
    omega
  · intro hf
    obtain ⟨M, hM⟩ := hf.bddAbove
    refine ⟨2 ^ (M + 1), 1, fun n => ?_⟩
    simp only [pow_one]
    by_cases hd : d n = true
    · have hn : n ≤ M := hM hd
      have : 2 ^ n ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [t, hd, ite_true]
      exact this.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos n))
    · have hd' : d n = false := by simpa using hd
      simp only [t, hd', Bool.false_eq_true, ite_false]
      have : 1 ≤ 2 ^ (M + 1) := Nat.one_le_two_pow
      nlinarith

theorem finito_iff_finalmente (d : ℕ → Bool) :
    {n | d n = true}.Finite ↔ ∀ᶠ n in atTop, d n = false := by
  rw [← Set.not_infinite, ← Nat.frequently_atTop_iff_infinite, not_frequently]
  simp

/-- La clase de `d` es la de una descripción finita: `t d` es polinomial si y solo si `d` termina en `false`. -/
theorem t_pol_iff_finalmente (d : ℕ → Bool) : t d ∈ Pol ↔ ∀ᶠ n in atTop, d n = false :=
  (t_pol_iff_finito d).trans (finito_iff_finalmente d)

/-! ## (d) Continuo = depende de un prefijo finito -/

/-- Los vecindarios de `d`: un conjunto es vecindario si contiene un cilindro (las `d'` que coinciden con `d` en
`[0, N)`). -/
theorem mem_nhds_iff_cilindro (d : ℕ → Bool) (S : Set (ℕ → Bool)) :
    S ∈ 𝓝 d ↔ ∃ N, ∀ d', (∀ i < N, d' i = d i) → d' ∈ S := by
  rw [nhds_pi, Filter.mem_pi]
  constructor
  · rintro ⟨I, hI, u, hu, hsub⟩
    obtain ⟨N, hN⟩ := hI.bddAbove
    refine ⟨N + 1, fun d' hd' => hsub fun i hi => ?_⟩
    have hdi : d i ∈ u i := mem_of_mem_nhds (hu i)
    rw [hd' i (Nat.lt_succ_of_le (hN hi))]
    exact hdi
  · rintro ⟨N, hN⟩
    refine ⟨Iio N, finite_Iio N, fun i => {d i}, fun i => ?_, fun d' hd' => hN d' fun i hi => hd' i hi⟩
    rw [nhds_discrete]
    exact mem_pure.2 rfl

theorem continuoEn_iff_prefijo (F : (ℕ → Bool) → Bool) (d : ℕ → Bool) :
    ContinuousAt F d ↔ ∃ N, ∀ d', (∀ i < N, d' i = d i) → F d' = F d := by
  rw [ContinuousAt, nhds_discrete Bool, tendsto_pure]
  exact mem_nhds_iff_cilindro d {d' | F d' = F d}

/-- **Continuo = uniforme**: `F` es continua si y solo si en cada punto decide mirando un prefijo finito. -/
theorem continuo_iff_prefijo (F : (ℕ → Bool) → Bool) :
    Continuous F ↔ ∀ d, ∃ N, ∀ d', (∀ i < N, d' i = d i) → F d' = F d := by
  rw [continuous_iff_continuousAt]
  exact forall_congr' fun d => continuoEn_iff_prefijo F d

/-! ## (b) La clase no es continua en ningún punto -/

/-- `d` hasta `N`, y después siempre `b`. -/
def pegar (d : ℕ → Bool) (N : ℕ) (b : Bool) : ℕ → Bool := fun i => if i < N then d i else b

theorem pegar_prefijo (d : ℕ → Bool) (N : ℕ) (b : Bool) : ∀ i < N, pegar d N b i = d i :=
  fun i hi => by simp [pegar, hi]

theorem pegar_false_pol (d : ℕ → Bool) (N : ℕ) : t (pegar d N false) ∈ Pol := by
  rw [t_pol_iff_finalmente, eventually_atTop]
  exact ⟨N, fun n hn => by simp [pegar, Nat.not_lt.2 hn]⟩

theorem pegar_true_no_pol (d : ℕ → Bool) (N : ℕ) : t (pegar d N true) ∉ Pol := by
  rw [t_pol_iff_finalmente, eventually_atTop]
  rintro ⟨M, hM⟩
  have := hM (max M N) (le_max_left _ _)
  simp [pegar, Nat.not_lt.2 (le_max_right M N)] at this

open Classical in
/-- La clase: `true` si `t d` es polinomial. -/
noncomputable def clase (d : ℕ → Bool) : Bool := decide (t d ∈ Pol)

/-- **La clase no es continua en ningún punto.** -/
theorem clase_no_continua : ∀ d, ¬ ContinuousAt clase d := by
  intro d h
  obtain ⟨N, hN⟩ := (continuoEn_iff_prefijo clase d).1 h
  have h1 := hN _ (pegar_prefijo d N false)
  have h2 := hN _ (pegar_prefijo d N true)
  have e1 : clase (pegar d N false) = true := by simp [clase, pegar_false_pol]
  have e2 : clase (pegar d N true) = false := by simp [clase, pegar_true_no_pol]
  rw [e1] at h1
  rw [e2] at h2
  rw [← h1] at h2
  exact Bool.false_ne_true h2

/-! ## (c) Parar no es continuo -/

open Classical in
/-- «Para»: en algún momento aparece un `true`. -/
noncomputable def parar (d : ℕ → Bool) : Bool := decide (∃ n, d n = true)

theorem parar_no_continuo : ¬ ContinuousAt parar (fun _ => false) := by
  intro h
  obtain ⟨N, hN⟩ := (continuoEn_iff_prefijo parar _).1 h
  have := hN (fun i => decide (i = N)) (fun i hi => by simp [Nat.ne_of_lt hi])
  simp [parar] at this

theorem parar_continuo_en (d : ℕ → Bool) (hd : d ≠ fun _ => false) : ContinuousAt parar d := by
  rw [continuoEn_iff_prefijo]
  obtain ⟨n, hn⟩ : ∃ n, d n = true := by
    by_contra hc
    exact hd (funext fun i => by simpa using fun h => hc ⟨i, h⟩)
  refine ⟨n + 1, fun d' hd' => ?_⟩
  have : d' n = true := by rw [hd' n (Nat.lt_succ_self n)]; exact hn
  simp only [parar, decide_eq_decide]
  exact ⟨fun _ => ⟨n, hn⟩, fun _ => ⟨n, this⟩⟩

/-! ## (f) Los «irracionales» oscilan a través del corte -/

theorem oscila_fuera_de_pol (d : ℕ → Bool) (hT : {n | d n = true}.Infinite) : t d ∉ Pol := by
  rw [t_pol_iff_finito]
  exact hT

theorem oscila_vuelve_abajo (d : ℕ → Bool) (hF : {n | d n = false}.Infinite) :
    ∃ᶠ n in atTop, t d n = n := by
  rw [← Nat.frequently_atTop_iff_infinite] at hF
  exact hF.mono fun n hn => by simp [t, hn]

theorem oscila_no_superpolinomial (d : ℕ → Bool) (hF : {n | d n = false}.Infinite) :
    ¬ ∀ᶠ n in atTop, n ^ 2 < t d n := by
  intro h
  obtain ⟨n, h1, h2⟩ := ((oscila_vuelve_abajo d hF).and_eventually h).exists
  rw [h1] at h2
  nlinarith

/-- La descripción que alterna: `true` en los pares. -/
def alterna (n : ℕ) : Bool := decide (n % 2 = 0)

theorem alterna_true_infinito : {n | alterna n = true}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  have := hM (show 2 * M + 2 ∈ {n | alterna n = true} by simp [alterna, Nat.mul_mod_right])
  omega

theorem alterna_false_infinito : {n | alterna n = false}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  have := hM (show 2 * M + 1 ∈ {n | alterna n = false} by simp [alterna, Nat.add_mod, Nat.mul_mod_right])
  omega

theorem alterna_oscila :
    t alterna ∉ Pol ∧ ¬ ∀ᶠ n in atTop, n ^ 2 < t alterna n :=
  ⟨oscila_fuera_de_pol _ alterna_true_infinito, oscila_no_superpolinomial _ alterna_false_infinito⟩

/-! ## (e) Suslin y Lusin en el espacio de Cantor -/

/-- El espacio de Cantor es polaco (la búsqueda de instancias de Mathlib no lo arma sola; las piezas sí están). -/
instance cantorPolaco : PolishSpace (ℕ → Bool) := {}

/-- La σ-álgebra de `ℕ → Bool` (la producto) es la de Borel. -/
theorem borel_igual : (inferInstance : MeasurableSpace (ℕ → Bool)) = borel (ℕ → Bool) :=
  BorelSpace.measurable_eq

/-- «NP» infinito: la proyección de un cerrado de `(ℕ → Bool) × (ℕ → ℕ)` (el certificado es la segunda coordenada)
es analítica. -/
theorem proyeccion_analitica {C : Set ((ℕ → Bool) × (ℕ → ℕ))} (hC : IsClosed C) :
    AnalyticSet (Prod.fst '' C) :=
  hC.analyticSet.image_of_continuous continuous_fst

/-- **Suslin en el espacio de Cantor**: «NP ∩ coNP = P» infinito. Un analítico con complemento analítico es de Borel. -/
theorem suslin_cantor {s : Set (ℕ → Bool)} (hs : AnalyticSet s) (hsc : AnalyticSet sᶜ) : MeasurableSet s :=
  hs.measurableSet_of_compl hsc

/-- **Lusin en el espacio de Cantor**: dos analíticos disjuntos se separan con un Borel. El análogo finito es
`SeparacionDeLusinNP`, que se espera falso. -/
theorem lusin_cantor {s u : Set (ℕ → Bool)} (hs : AnalyticSet s) (hu : AnalyticSet u) (h : Disjoint s u) :
    ∃ b, s ⊆ b ∧ Disjoint u b ∧ MeasurableSet b :=
  hs.measurablySeparable hu h

/-! ## Controles -/

/-- La descripción toda `false` da tiempo polinomial (es la identidad). -/
example : t (fun _ => false) ∈ Pol := by
  rw [t_pol_iff_finalmente]; exact Eventually.of_forall fun _ => rfl

/-- La descripción toda `true` da `2^n`: no polinomial. -/
example : t (fun _ => true) ∉ Pol := by
  rw [t_pol_iff_finalmente]; simp only [Bool.true_eq_false, eventually_false_iff_eq_bot, atTop_neBot.ne,
    not_false_eq_true]

/-- Un mapa que mira un solo bit sí es continuo: la condición de (d) no es vacía. -/
example : Continuous (fun d : ℕ → Bool => d 3) := by
  rw [continuo_iff_prefijo]
  exact fun d => ⟨4, fun d' hd' => hd' 3 (by norm_num)⟩

/-- `parar` es continua lejos de la sucesión toda `false`, por ejemplo en la toda `true`. -/
example : ContinuousAt parar (fun _ => true) :=
  parar_continuo_en _ fun h => by simpa using congrFun h 0

/-- Valores concretos de `t`. -/
example : t alterna 4 = 16 ∧ t alterna 5 = 5 := by decide

/-! Mutante (probado en /tmp/claude-noche/MutanteContinuo.lean, 25 nov 2026): con `t d n = if d n then n ^ 2 else n`
(el lado alto también polinomial) el enunciado `t (fun _ => true) ∉ Pol` deja de ser demostrable; Lean rechaza la prueba
de `t_pol_iff_finito` (el `omega` de la ida no cierra, porque `n^2` ya no choca con `pol_menor_dos_pow`), y con ella
caen `pegar_true_no_pol` y `clase_no_continua`. -/

end Continuo
end Sagitta.Map
