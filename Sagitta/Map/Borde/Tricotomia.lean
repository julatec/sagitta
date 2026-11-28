import Sagitta.Map.Infinito
import Sagitta.Map.LandauDenso
import Sagitta.Map.Continuo.ClaseNoContinua
import Sagitta.Map.Continuo.MonedaOscila
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# El vocabulario del borde: abajo, arriba y oscila (fase B1)

Es la primera fase del plan «El borde es un hueco» (24 nov 2026; ver las notas del proyecto). Un costo `f : ℕ → ℕ` puede estar en tres
lugares respecto del borde de P:

* `Bajo f` : `f ∈ Pol`, acotado por un polinomio en todo largo;
* `Sobre f` : finalmente por encima de **todo** polinomio, `∀ c k, ∀ᶠ n in atTop, c·(n+1)^k < f n`;
* `Oscila f` : ni lo uno ni lo otro.

## Lo que se prueba

* (i) **La tricotomía** (`tricotomia`) y que las tres regiones son disjuntas (`bajo_no_sobre`, y las otras dos por
  definición).
* (ii) **Con los largos infinitos de `Infinito.lean`**: `sobre_iff_largos` (arriba es ganarle a todo polinomio en
  **todo** largo infinito), `no_sobre_iff` (no estar arriba es que un polinomio acote en **algún** largo infinito) y
  `oscila_iff_largos` (oscilar es tener un largo infinito donde un polinomio acota y otro donde ninguno alcanza).
  Además `sobre_iff_o`: arriba es que todo `(n+1)^k` sea despreciable (`o` de `LandauDenso.lean`) frente a `f`.
* (iii) **No hay función en el borde** (`no_hay_borde`): si `Sobre f`, hay `g` con `Sobre g` y `g ∈ o f`. Es
  `sin_supremo` de `LandauDenso.lean` aplicado a la familia `(n+1)^k`, con el `o` de ese archivo tal cual.
* (iv) **El sándwich no encierra el borde** (`sandwich`): para toda sucesión `F : ℕ → ℕ → ℕ` de costos arriba hay un
  `g` arriba que finalmente queda debajo de cada `F i`; `sandwich_estricto` da además `g ∈ o (F i)` para todo `i`.
  `sin_supremo` hace lo simétrico (desde abajo: una escalera que sube no tiene supremo). Lo que agrega este: **desde
  arriba tampoco**; ninguna sucesión numerable de costos arriba baja hasta el borde. Los dos juntos dicen que el borde
  de P no es un punto del orden de Landau ni un límite de sucesiones numerables por ninguno de los dos lados.
* (v) **Las tres regiones están habitadas** (`bajo_cuadrado`, `sobre_dos_pow`, `oscila_alterna`).
* (vi) **Lo genérico oscila** en el modelo `t d` de `ClaseNoContinua.lean` (`t d n = 2^n` si `d n`, si no `n`):
  `bajo_t_iff` (`d` termina en `false`), `sobre_t_iff` (termina en `true`), `oscila_t_iff` (infinitos de cada uno).
  - **Por medida** (`casi_seguro_oscila_t`): para la moneda justa `lanzar` de `MonedaOscila.lean`, casi toda `d`
    oscila.
  - **Por categoría** (`residual_oscila_t`, `oscila_t_isGδ`, `oscila_t_denso`): las `d` que oscilan forman un
    conjunto residual, un Gδ denso. «Vale `b` desde `N`» es cerrado (`cola_cerrada`) y de interior vacío
    (`cola_interior_vacio`), así que «finalmente `b`» es magro (`finalmente_magro`).
  - **Numerables** (`finalmente_numerable`): abajo y arriba son conjuntos numerables de descripciones.
* (vii) **Parar contra estar en P** (`parar_abierto`, `en_P_no_abierto`, `en_P_no_cerrado`, `en_P_sigma`): «se
  detiene en algún momento» es abierto; «termina en `false`» (estar en P en el modelo) no es abierto ni cerrado y es
  una unión numerable de cerrados (un Fσ, nivel Σ⁰₂ de Borel). Se probó sobre la sucesión cruda; la versión con
  `halt` absorbente (trazas monótonas) da el mismo conjunto abierto `{d | ∃ n, d n = true}` y no se separó.

## Lo que no

* Nada sobre SAT: eso es `SatEnElBorde.lean`. Nada con tiempo de máquinas (B3) ni Ladner (B4).
* El modelo `t d` es de juguete: un bit decide si el largo `n` cuesta `2^n` o `n`. Las afirmaciones de «genérico»
  son sobre ese espacio de descripciones, no sobre los programas reales.

Lo conocido: la tricotomía es definicional; (iii) y (iv) son la diagonal de du Bois-Reymond y Hausdorff en otra forma
(los huecos del orden de crecimiento); (vi) es la categoría de Baire y el 0-1 de la moneda; (vii) es la jerarquía de
Borel en el espacio de Cantor. La formalización es propia.
-/

open Filter Topology Set MeasureTheory

namespace Sagitta.Map.Borde.Tricotomia

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Infinito
open Sagitta.Map.Continuo

/-! ## Las tres regiones -/

/-- **Abajo** del borde: polinomial. -/
def Bajo (f : ℕ → ℕ) : Prop := f ∈ Pol

/-- **Arriba** del borde: finalmente por encima de todo polinomio. -/
def Sobre (f : ℕ → ℕ) : Prop := ∀ c k, ∀ᶠ n in atTop, c * (n + 1) ^ k < f n

/-- **Oscila**: ni abajo ni arriba. -/
def Oscila (f : ℕ → ℕ) : Prop := ¬ Bajo f ∧ ¬ Sobre f

/-! ## (i) La tricotomía -/

theorem bajo_no_sobre {f : ℕ → ℕ} (h : Bajo f) : ¬ Sobre f := by
  rintro hs
  obtain ⟨c, k, hc⟩ := h
  obtain ⟨n, hn⟩ := (hs c k).exists
  have := hc n
  omega

theorem sobre_no_bajo {f : ℕ → ℕ} (h : Sobre f) : ¬ Bajo f := fun hb => bajo_no_sobre hb h

/-- **La tricotomía**: todo costo está abajo, arriba u oscila. -/
theorem tricotomia (f : ℕ → ℕ) : Bajo f ∨ Sobre f ∨ Oscila f := by
  by_cases hb : Bajo f
  · exact Or.inl hb
  · by_cases hs : Sobre f
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr ⟨hb, hs⟩)

/-- **Exactamente una**: las tres regiones son disjuntas dos a dos. -/
theorem disjuntas (f : ℕ → ℕ) :
    ¬ (Bajo f ∧ Sobre f) ∧ ¬ (Bajo f ∧ Oscila f) ∧ ¬ (Sobre f ∧ Oscila f) :=
  ⟨fun h => bajo_no_sobre h.1 h.2, fun h => h.2.1 h.1, fun h => h.2.2 h.1⟩

/-! ## (ii) Con los largos infinitos -/

theorem largo_de_atTop {U : Ultrafilter ℕ} (hU : LargoInfinito U) {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) :
    ∀ᶠ n in (U : Filter ℕ), P n :=
  hU (Nat.cofinite_eq_atTop ▸ h)

/-- **Arriba es arriba en todo largo infinito.** -/
theorem sobre_iff_largos (f : ℕ → ℕ) :
    Sobre f ↔ ∀ U : Ultrafilter ℕ, LargoInfinito U → ∀ c k, ∀ᶠ n in (U : Filter ℕ), c * (n + 1) ^ k < f n := by
  constructor
  · intro h U hU c k
    exact largo_de_atTop hU (h c k)
  · intro h c k
    by_contra hno
    rw [not_eventually] at hno
    have hinf : {n | ¬ c * (n + 1) ^ k < f n}.Infinite := Nat.frequently_atTop_iff_infinite.1 hno
    obtain ⟨U, hU, hmalo⟩ := (io_iff_largo_infinito _).1 hinf
    obtain ⟨n, h1, h2⟩ := ((h U hU c k).and hmalo).exists
    exact h2 h1

/-- **No estar arriba** es que un polinomio acote el costo en algún largo infinito. -/
theorem no_sobre_iff (f : ℕ → ℕ) :
    ¬ Sobre f ↔ ∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∃ c k, ∀ᶠ n in (U : Filter ℕ), f n ≤ c * (n + 1) ^ k := by
  constructor
  · intro h
    unfold Sobre at h
    push Not at h
    obtain ⟨c, k, hck⟩ := h
    have hinf : {n | f n ≤ c * (n + 1) ^ k}.Infinite :=
      Nat.frequently_atTop_iff_infinite.1 hck
    obtain ⟨U, hU, hb⟩ := (io_iff_largo_infinito _).1 hinf
    exact ⟨U, hU, c, k, hb⟩
  · rintro ⟨U, hU, c, k, hb⟩ hs
    obtain ⟨n, h1, h2⟩ := ((largo_de_atTop hU (hs c k)).and hb).exists
    omega

/-- **Oscilar**, con largos infinitos: hay uno donde un polinomio acota y otro donde ningún polinomio alcanza. -/
theorem oscila_iff_largos (f : ℕ → ℕ) :
    Oscila f ↔
      (∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∃ c k, ∀ᶠ n in (U : Filter ℕ), f n ≤ c * (n + 1) ^ k) ∧
      (∃ V : Ultrafilter ℕ, LargoInfinito V ∧ ∀ c k, ∀ᶠ n in (V : Filter ℕ), c * (n + 1) ^ k < f n) := by
  unfold Oscila Bajo
  rw [fuera_de_pol_iff, no_sobre_iff]
  exact and_comm

/-- **Arriba, en el lenguaje de Landau**: todo `(n+1)^k` es despreciable frente a `f`. -/
theorem sobre_iff_o (f : ℕ → ℕ) : Sobre f ↔ ∀ k, (fun n => (n + 1) ^ k) ∈ o f := by
  constructor
  · intro h k c
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h c k)
    exact ⟨N, fun n hn => (hN n hn).le⟩
  · intro h c k
    obtain ⟨N, hN⟩ := h k (c + 1)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    simp only at h1
    nlinarith

/-! ## (iii) No hay función en el borde -/

/-- **No hay función en el borde.** Debajo de todo costo arriba hay otro arriba, despreciable frente a él. -/
theorem no_hay_borde {f : ℕ → ℕ} (hf : Sobre f) : ∃ g, Sobre g ∧ g ∈ o f := by
  obtain ⟨g, hg, hgf⟩ := sin_supremo (fun k n => (n + 1) ^ k) ((sobre_iff_o f).1 hf)
  exact ⟨g, (sobre_iff_o g).2 hg, hgf⟩

/-! ## (iv) El sándwich no encierra el borde -/

/-- El mínimo de `F 0 n, …, F m n`. -/
def minHasta (F : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => F 0 n
  | m + 1, n => min (minHasta F m n) (F (m + 1) n)

theorem minHasta_le (F : ℕ → ℕ → ℕ) : ∀ {m i : ℕ}, i ≤ m → ∀ n, minHasta F m n ≤ F i n
  | 0, i, h, n => by obtain rfl : i = 0 := by omega
                     exact le_rfl
  | m + 1, i, h, n => by
    simp only [minHasta]
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · exact (min_le_left _ _).trans (minHasta_le F (by omega) n)
    · obtain rfl : i = m + 1 := by omega
      exact min_le_right _ _

theorem lt_minHasta (F : ℕ → ℕ → ℕ) {x n : ℕ} : ∀ {m : ℕ}, (∀ i ≤ m, x < F i n) → x < minHasta F m n
  | 0, h => h 0 le_rfl
  | m + 1, h => by
    simp only [minHasta]
    exact lt_min (lt_minHasta F fun i hi => h i (by omega)) (h (m + 1) le_rfl)

/-- **El sándwich no encierra el borde.** Para toda sucesión de costos arriba hay uno arriba que finalmente queda
debajo de cada uno. La construcción es el mínimo de los primeros `κ n`, con `κ` creciendo despacio: `κ n` es el
mayor `m ≤ n` tal que desde `N j` (para cada `j ≤ m`) los primeros `j` costos ya pasan a `j·(n+1)^j`. -/
theorem sandwich (F : ℕ → ℕ → ℕ) (hF : ∀ i, Sobre (F i)) :
    ∃ g, Sobre g ∧ ∀ i, ∀ᶠ n in atTop, g n ≤ F i n := by
  classical
  -- Desde `N m`, los costos `F 0, …, F m` pasan a `m·(n+1)^m`.
  have hN : ∀ m, ∃ N, ∀ n ≥ N, ∀ i ≤ m, m * (n + 1) ^ m < F i n := by
    intro m
    have : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (m + 1), m * (n + 1) ^ m < F i n :=
      (Finset.eventually_all (Finset.range (m + 1))).2 fun i _ => hF i m m
    obtain ⟨N, hN⟩ := eventually_atTop.1 this
    exact ⟨N, fun n hn i hi => hN n hn i (Finset.mem_range.2 (by omega))⟩
  choose N hN using hN
  let P : ℕ → ℕ → Prop := fun n m => ∀ j ≤ m, N j ≤ n
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  have hκP : ∀ n, N 0 ≤ n → P n (κ n) := fun n hn =>
    Nat.findGreatest_spec (P := P n) (Nat.zero_le n) (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact hn)
  have hκ : ∀ c, ∃ M, ∀ n ≥ M, c ≤ κ n := fun c => by
    refine ⟨c + ∑ j ∈ Finset.range (c + 1), N j, fun n hn => ?_⟩
    refine Nat.le_findGreatest (P := P n) (by omega) (fun j hj => ?_)
    have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (show j < c + 1 by omega))
    omega
  refine ⟨fun n => minHasta F (κ n) n, fun c k => ?_, fun i => ?_⟩
  · obtain ⟨M, hM⟩ := hκ (max c k)
    refine eventually_atTop.2 ⟨max M (N 0), fun n hn => ?_⟩
    have hc := hM n (le_of_max_le_left hn)
    have hP := hκP n (le_of_max_le_right hn)
    have hb : ∀ i ≤ κ n, κ n * (n + 1) ^ κ n < F i n := hN (κ n) n (hP (κ n) le_rfl)
    have hpol : c * (n + 1) ^ k ≤ κ n * (n + 1) ^ κ n :=
      Nat.mul_le_mul (le_of_max_le_left hc) (Nat.pow_le_pow_right (by omega) (le_of_max_le_right hc))
    exact lt_of_le_of_lt hpol (lt_minHasta F hb)
  · obtain ⟨M, hM⟩ := hκ i
    exact eventually_atTop.2 ⟨M, fun n hn => minHasta_le F (hM n hn) n⟩

/-- **El sándwich, estricto**: además el `g` es despreciable frente a cada `F i`. -/
theorem sandwich_estricto (F : ℕ → ℕ → ℕ) (hF : ∀ i, Sobre (F i)) :
    ∃ g, Sobre g ∧ ∀ i, g ∈ o (F i) := by
  obtain ⟨g, hg, hle⟩ := sandwich F hF
  obtain ⟨h, hh, hhg⟩ := no_hay_borde hg
  refine ⟨h, hh, fun i c => ?_⟩
  obtain ⟨N₁, h₁⟩ := hhg c
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 (hle i)
  exact ⟨max N₁ N₂, fun n hn => (h₁ n (le_of_max_le_left hn)).trans (h₂ n (le_of_max_le_right hn))⟩

/-! ## (v) Las tres regiones están habitadas -/

theorem bajo_cuadrado : Bajo (fun n => n ^ 2) :=
  ⟨1, 2, fun n => by rw [one_mul]; exact Nat.pow_le_pow_left (Nat.le_succ n) 2⟩

theorem sobre_dos_pow : Sobre (fun n => 2 ^ n) := fun c k => by
  obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
  exact eventually_atTop.2 ⟨N, hN⟩

theorem oscila_alterna : Oscila (t alterna) := by
  refine ⟨alterna_oscila.1, fun hs => ?_⟩
  obtain ⟨n, h1, h2⟩ := ((oscila_vuelve_abajo alterna alterna_false_infinito).and_eventually (hs 1 1)).exists
  rw [h1, pow_one, one_mul] at h2
  omega

/-! ## (vi) Lo genérico oscila -/

theorem bajo_t_iff (d : ℕ → Bool) : Bajo (t d) ↔ ∀ᶠ n in atTop, d n = false := t_pol_iff_finalmente d

theorem sobre_t_iff (d : ℕ → Bool) : Sobre (t d) ↔ ∀ᶠ n in atTop, d n = true := by
  constructor
  · intro h
    refine (h 1 1).mono fun n hn => ?_
    by_contra hd
    simp only [t, Bool.not_eq_true] at hn hd
    simp [hd] at hn
  · intro h c k
    obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
    refine (h.and (eventually_ge_atTop N)).mono fun n hn => ?_
    simp only [t, hn.1, ite_true]
    exact hN n hn.2

theorem oscila_t_iff (d : ℕ → Bool) :
    Oscila (t d) ↔ (∃ᶠ n in atTop, d n = true) ∧ (∃ᶠ n in atTop, d n = false) := by
  unfold Oscila
  rw [bajo_t_iff, sobre_t_iff, not_eventually, not_eventually]
  simp only [Bool.not_eq_false, Bool.not_eq_true]

/-- **Por medida**: casi toda descripción, con bits de moneda justa, da un costo que oscila. -/
theorem casi_seguro_oscila_t : ∀ᵐ d ∂Sagitta.Map.Continuo.Moneda.lanzar, Oscila (t d) :=
  Sagitta.Map.Continuo.Moneda.casi_seguro_oscila.mono fun d h => (oscila_t_iff d).2 h

/-- Las descripciones que valen `b` desde `N`. -/
def cola (N : ℕ) (b : Bool) : Set (ℕ → Bool) := {d | ∀ n, N ≤ n → d n = b}

theorem cola_cerrada (N : ℕ) (b : Bool) : IsClosed (cola N b) := by
  have : cola N b = ⋂ n, ⋂ (_ : N ≤ n), {d : ℕ → Bool | d n = b} := by
    ext d; simp [cola]
  rw [this]
  exact isClosed_iInter fun n => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply n) continuous_const

/-- Todo vecindario de `d` contiene una descripción que no vale `b` desde `N`. -/
theorem cola_interior_vacio (N : ℕ) (b : Bool) : interior (cola N b) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro d hd
  obtain ⟨M, hM⟩ := (mem_nhds_iff_cilindro d _).1 (mem_interior_iff_mem_nhds.1 hd)
  have h := hM (Function.update d (max M N) (!b)) (fun i hi => by
    rw [Function.update_of_ne (by omega)])
  have := h (max M N) (le_max_right M N)
  simp at this

theorem cola_rara (N : ℕ) (b : Bool) : IsNowhereDense (cola N b) :=
  (cola_cerrada N b).isNowhereDense_iff.2 (cola_interior_vacio N b)

theorem finalmente_eq_cola (b : Bool) : {d : ℕ → Bool | ∀ᶠ n in atTop, d n = b} = ⋃ N, cola N b := by
  ext d; simp [cola, eventually_atTop]

/-- **«Finalmente `b`» es magro**: una unión numerable de cerrados sin interior. -/
theorem finalmente_magro (b : Bool) : IsMeagre {d : ℕ → Bool | ∀ᶠ n in atTop, d n = b} := by
  rw [finalmente_eq_cola]
  exact isMeagre_iUnion fun N => (cola_rara N b).isMeagre

theorem oscila_t_eq : {d : ℕ → Bool | Oscila (t d)} =
    ({d : ℕ → Bool | ∀ᶠ n in atTop, d n = false} ∪ {d | ∀ᶠ n in atTop, d n = true})ᶜ := by
  ext d
  simp only [mem_ofPred_eq, mem_compl_iff, mem_union, not_or]
  unfold Oscila
  rw [bajo_t_iff, sobre_t_iff]

/-- **Por categoría**: oscilar es residual. -/
theorem residual_oscila_t : ∀ᶠ d in residual (ℕ → Bool), Oscila (t d) := by
  show {d | Oscila (t d)} ∈ residual (ℕ → Bool)
  rw [oscila_t_eq]
  exact (finalmente_magro false).union (finalmente_magro true)

/-- Las que oscilan forman un Gδ. -/
theorem oscila_t_isGδ : IsGδ {d : ℕ → Bool | Oscila (t d)} := by
  have : {d : ℕ → Bool | Oscila (t d)} = ⋂ p : ℕ × Bool, (cola p.1 p.2)ᶜ := by
    rw [oscila_t_eq, finalmente_eq_cola, finalmente_eq_cola]
    ext d
    simp only [mem_compl_iff, mem_union, mem_iUnion, not_or, not_exists, mem_iInter, Prod.forall, Bool.forall_bool]
    exact forall_and.symm
  rw [this]
  exact IsGδ.iInter_of_isOpen fun p => (cola_cerrada p.1 p.2).isOpen_compl

/-- Y es denso (Baire: el espacio de Cantor es compacto y Hausdorff). -/
theorem oscila_t_denso : Dense {d : ℕ → Bool | Oscila (t d)} :=
  dense_of_mem_residual residual_oscila_t

/-- **Numerables**: las descripciones que terminan en `b` son numerables. -/
theorem finalmente_numerable (b : Bool) : Set.Countable {d : ℕ → Bool | ∀ᶠ n in atTop, d n = b} := by
  rw [finalmente_eq_cola]
  refine countable_iUnion fun N => ?_
  refine (countable_range (fun p : Fin N → Bool => fun n => if h : n < N then p ⟨n, h⟩ else b)).mono ?_
  intro d hd
  refine ⟨fun i => d i, funext fun n => ?_⟩
  by_cases h : n < N
  · simp [h]
  · simp only [h, dite_false]
    exact (hd n (by omega)).symm

/-- Abajo y arriba, en el modelo, son numerables. -/
theorem bajo_sobre_numerables :
    Set.Countable {d : ℕ → Bool | Bajo (t d)} ∧ Set.Countable {d : ℕ → Bool | Sobre (t d)} := by
  constructor
  · simpa only [bajo_t_iff] using finalmente_numerable false
  · simpa only [sobre_t_iff] using finalmente_numerable true

/-! ## (vii) Parar contra estar en P -/

/-- **Parar es abierto**: basta ver un `true`. -/
theorem parar_abierto : IsOpen {d : ℕ → Bool | ∃ n, d n = true} := by
  have : {d : ℕ → Bool | ∃ n, d n = true} = ⋃ n, {d : ℕ → Bool | d n = true} := by ext d; simp
  rw [this]
  exact isOpen_iUnion fun n => by
    have : {d : ℕ → Bool | d n = true} = (fun d : ℕ → Bool => d n) ⁻¹' {true} := by ext d; simp
    rw [this]
    exact (isOpen_discrete {true}).preimage (continuous_apply n)

/-- **Estar en P (en el modelo) no es abierto**: todo vecindario de una `d` que termina en `false` contiene una que
termina en `true`. -/
theorem en_P_no_abierto : ¬ IsOpen {d : ℕ → Bool | ∀ᶠ n in atTop, d n = false} := by
  intro h
  have hm : (fun _ => false : ℕ → Bool) ∈ {d : ℕ → Bool | ∀ᶠ n in atTop, d n = false} := by simp
  obtain ⟨N, hN⟩ := (mem_nhds_iff_cilindro _ _).1 (h.mem_nhds hm)
  have := hN (pegar (fun _ => false) N true) (pegar_prefijo _ N true)
  simp only [mem_ofPred_eq, eventually_atTop] at this
  obtain ⟨M, hM⟩ := this
  have := hM (max M N) (le_max_left _ _)
  simp [pegar, Nat.not_lt.2 (le_max_right M N)] at this

/-- **Ni cerrado**: todo vecindario de la constante `true` contiene una que termina en `false`. -/
theorem en_P_no_cerrado : ¬ IsClosed {d : ℕ → Bool | ∀ᶠ n in atTop, d n = false} := by
  intro h
  have hm : (fun _ => true : ℕ → Bool) ∈ {d : ℕ → Bool | ∀ᶠ n in atTop, d n = false}ᶜ := by
    simp; exact fun x => ⟨x, le_rfl⟩
  obtain ⟨N, hN⟩ := (mem_nhds_iff_cilindro _ _).1 (h.isOpen_compl.mem_nhds hm)
  have := hN (pegar (fun _ => true) N false) (pegar_prefijo _ N false)
  apply this
  simp only [mem_ofPred_eq, eventually_atTop]
  exact ⟨N, fun n hn => by simp [pegar, Nat.not_lt.2 hn]⟩

/-- **Estar en P es un Fσ**: unión numerable de cerrados. -/
theorem en_P_sigma : ∃ C : ℕ → Set (ℕ → Bool), (∀ N, IsClosed (C N)) ∧
    {d : ℕ → Bool | Bajo (t d)} = ⋃ N, C N := by
  refine ⟨fun N => cola N false, fun N => cola_cerrada N false, ?_⟩
  ext d
  rw [mem_ofPred_eq, bajo_t_iff]
  exact Set.ext_iff.1 (finalmente_eq_cola false) d

/-! ## Controles -/

/-- La tricotomía no colapsa: hay un costo en cada región, y son distintos. -/
example : Bajo (fun n => n ^ 2) ∧ Sobre (fun n => 2 ^ n) ∧ Oscila (t alterna) :=
  ⟨bajo_cuadrado, sobre_dos_pow, oscila_alterna⟩

/-- `Sobre` exige más que `∉ Pol`: el péndulo de `Infinito.lean` no es polinomial y tampoco está arriba (vale `0` en
los pares). -/
example : ¬ Sobre pendulo := by
  intro h
  have : ∃ᶠ n in atTop, pendulo n = 0 := by
    rw [frequently_atTop]; intro a; exact ⟨2 * a, by omega, by simp [pendulo]⟩
  obtain ⟨m, hm1, hm2⟩ := (this.and_eventually (h 1 0)).exists
  rw [hm1] at hm2
  simp at hm2

/-- El sándwich no es vacío: con la familia constante `2^n`, el `g` que da está arriba y debajo de `2^n`. -/
example : ∃ g, Sobre g ∧ ∀ᶠ n in atTop, g n ≤ 2 ^ n := by
  obtain ⟨g, hg, hle⟩ := sandwich (fun _ n => 2 ^ n) (fun _ => sobre_dos_pow)
  exact ⟨g, hg, hle 0⟩

/-- Una cola no es vacía (la constante está), así que «interior vacío» dice algo. -/
example (N : ℕ) (b : Bool) : (fun _ => b) ∈ cola N b := fun _ _ => rfl

/- Mutante probado (25 nov 2026, en /tmp/claude-noche/MutTri.lean): cambiar en `Sobre` el «finalmente» `∀ᶠ` por
«infinitas veces» `∃ᶠ` rompe el archivo (entre otros, `no_sobre_iff`, `sobre_iff_o`, `sandwich` y `oscila_alterna`
dejan de compilar). Es el error que importa: con `∃ᶠ`, `t alterna` estaría «arriba», porque le gana a todo polinomio
en los largos pares, y la tricotomía dejaría de separar arriba de oscila. -/

end Sagitta.Map.Borde.Tricotomia
