import Sagitta.Map.Borde.SatEnElBorde

/-!
# El puente: si SAT tiene circuitos polinomiales, SAT enmarcado también (`SatMarcoDeSatBits`)

En `Relleno.lean` quedó como `Prop` documentado, sin construir, la dirección `satBits ∈ P/poly ⇒ satMarco ∈ P/poly`
(`SatMarcoDeSatBits`). Por eso la tricotomía de SAT (`SatEnElBorde.tricotomia_sat`) hablaba de `satBits` en la primera
rama y de `satMarco` en las otras dos, y era un «o», no una partición. Aquí se construye el circuito y se cierra.
`Relleno.lean` no se toca (es de otra sesión): el puente vive en este archivo.

## La construcción

Una entrada `x` de `m` bits se desenmarca en `unframe x`, que tiene algún largo `j ≤ m/2`. El largo es `j` cuando los
marcadores `x₀, x₂, …, x₂ⱼ₋₂` valen `true` y el siguiente par, si cabe completo, empieza con `false` (`Marca`). Entonces
`unframe x` es `x₁, x₃, …, x₂ⱼ₋₁` (`unframe_de_marca`), y siempre hay tal `j`: el largo de `unframe x`
(`marca_largo`). Así

  `satMarco(x) = ⋁_{j ≤ m/2} (Marca_j(x) ∧ satBits_j(x₁, x₃, …, x₂ⱼ₋₁))` (`rebanada_satMarco`).

No hace falta que el `j` sea único: si alguna disyunción vale, ese `j` da el mismo `unframe`.

Los circuitos se cuentan con `Cabe f B` («`f` tiene un circuito de a lo sumo `B` compuertas», en el modelo de
`Shannon.lean`), con las piezas que ya había: proyecciones (0 compuertas), la constante `false` (1), una operación
sobre dos circuitos (`combinar`, `t₁ + t₂ + 1`), fijar entradas (`reetiquetar` de `Relleno.lean`, `+2`). Con eso,
`Marca_j` cabe en `2j + 7` compuertas, el término `j` en `sucNat satBits j + 2j + 11`, y la disyunción de los `m/2 + 1`
términos en la suma más uno por término (`cabe_satMarco`).

## Lo que se prueba

* **`satMarcoDeSatBits : SatMarcoDeSatBits`**: si `satBits ∈ P/poly`, `satMarco ∈ P/poly`, con la cota explícita
  `sucNat satMarco m ≤ (c + 13)·(m+1)^(k+2)` cuando `sucNat satBits j ≤ c·(j+1)^k` (`sucNat_satMarco_le`).
* `satMarco_iff_satBits`: las dos versiones de SAT están juntas en P/poly o juntas fuera.
* **`tricotomia_sat_exacta`** (el corolario nuevo; `tricotomia_sat` no se reescribe): las tres ramas hablan de
  `satMarco` (abajo ↔ `satBits ∈ P/poly`, arriba, oscila con huecos), y se excluyen dos a dos: **es una partición**.
* `fuera_iff_huecos_sat`: `satBits ∉ P/poly` **si y solo si** `satMarco` tiene, para todo polinomio y toda ventana,
  infinitos huecos (antes, en `Relleno.huecos_de_sat`, solo la ida).

## Lo que no

* Nada sobre en cuál de las tres ramas cae SAT.
* La cota es grosera (`(m+1)^(k+2)` contra el `(m+1)^k` de `satBits`: se pagan un factor por la disyunción sobre los
  largos y otro por la cuenta); para P/poly da lo mismo.
-/

open Filter Set

namespace Sagitta.Map.Borde.MarcoDeBits

open Sagitta.Map Sagitta.Map.Shannon Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Finitud
open Sagitta.Map.Tiempo.Relleno Sagitta.Map.Borde.Tricotomia
open Turing.MultiTapeTM CookS12

/-! ## 1. Contar compuertas -/

/-- `f` tiene un circuito de a lo sumo `B` compuertas. -/
def Cabe {n : ℕ} (f : (Fin n → Bool) → Bool) (B : ℕ) : Prop := ∃ t ≤ B, ∃ C : Circuito n t, calcula C = f

variable {n : ℕ}

theorem cabe_mono {f : (Fin n → Bool) → Bool} {B B' : ℕ} (h : Cabe f B) (hB : B ≤ B') : Cabe f B' := by
  obtain ⟨t, ht, C, hC⟩ := h
  exact ⟨t, ht.trans hB, C, hC⟩

theorem cabe_congr {f g : (Fin n → Bool) → Bool} {B : ℕ} (h : Cabe f B) (hfg : ∀ x, f x = g x) : Cabe g B := by
  rwa [show g = f from funext fun x => (hfg x).symm]

theorem cabe_proy (i : Fin n) : Cabe (fun x : Fin n → Bool => x i) 0 := by
  refine ⟨0, le_rfl, proy i, ?_⟩
  funext x
  unfold calcula
  rw [cables_entrada _ _ _ (by simp only [proy]; exact i.isLt)]
  rfl

theorem cabe_falso : Cabe (fun _ : Fin n → Bool => false) 1 := by
  obtain ⟨t, C, hC⟩ := (calculable_falso : Calculable (fun _ : Fin n → Bool => false))
  refine ⟨1, le_rfl, falso n, ?_⟩
  funext x
  unfold calcula
  have : (falso n).2 = cableDe (0 : Fin 1) := Fin.ext (by simp [falso, cableDe])
  rw [this, cables_compuerta]
  simp [falso, lee, Op.aplica]

theorem cabe_op (op : Op) {f g : (Fin n → Bool) → Bool} {B₁ B₂ : ℕ} (hf : Cabe f B₁) (hg : Cabe g B₂) :
    Cabe (fun x => op.aplica (f x) (g x)) (B₁ + B₂ + 1) := by
  obtain ⟨t₁, h₁, C₁, rfl⟩ := hf
  obtain ⟨t₂, h₂, C₂, rfl⟩ := hg
  exact ⟨_, by omega, combinar op C₁ C₂, calcula_combinar op C₁ C₂⟩

theorem cabe_y {f g : (Fin n → Bool) → Bool} {B₁ B₂ : ℕ} (hf : Cabe f B₁) (hg : Cabe g B₂) :
    Cabe (fun x => f x && g x) (B₁ + B₂ + 1) := cabe_op Op.y hf hg

theorem cabe_o {f g : (Fin n → Bool) → Bool} {B₁ B₂ : ℕ} (hf : Cabe f B₁) (hg : Cabe g B₂) :
    Cabe (fun x => f x || g x) (B₁ + B₂ + 1) := cabe_op Op.o hf hg

theorem cabe_no {f : (Fin n → Bool) → Bool} {B : ℕ} (hf : Cabe f B) : Cabe (fun x => !f x) (B + B + 1) :=
  cabe_op Op.no hf hf

theorem cabe_verdadero : Cabe (fun _ : Fin n → Bool => true) 3 := cabe_no cabe_falso

/-- Fijar entradas cuesta dos compuertas (`reetiquetar` de `Relleno.lean`). -/
theorem cabe_fijar {m : ℕ} {g : (Fin n → Bool) → Bool} {f : (Fin m → Bool) → Bool} {B : ℕ}
    (h : SeObtieneFijando g f) (hf : Cabe f B) : Cabe g (B + 2) := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨t, ht, C, rfl⟩ := hf
  refine ⟨t + 2, by omega, reetiquetar σ C, ?_⟩
  rw [calcula_reetiquetar]
  funext x
  exact (hσ x).symm

theorem tamMin_le_de_cabe {f : (Fin n → Bool) → Bool} {B : ℕ} (h : Cabe f B) : tamMin f ≤ B := by
  obtain ⟨t, ht, C, hC⟩ := h
  exact iInf_le_of_le t (iInf_le_of_le C (iInf_le_of_le hC (by exact_mod_cast ht)))

/-- La rebanada de un problema cabe en su óptimo. -/
theorem cabe_rebanada (L : Problema) (m : ℕ) : Cabe (rebanada L m) (sucNat L m) := by
  obtain ⟨t, C, hC, ht⟩ := tamMin_alcanzado (rebanada L m)
  refine ⟨t, ?_, C, hC⟩
  have : sucesion L m = t := ht
  rw [sucesion_eq] at this
  exact_mod_cast this.ge

theorem sucNat_le_de_cabe {L : Problema} {m B : ℕ} (h : Cabe (rebanada L m) B) : sucNat L m ≤ B := by
  have := tamMin_le_de_cabe h
  rw [← sucesion, sucesion_eq] at this
  exact_mod_cast this

/-- El bit `i` de la entrada, `false` si no existe. -/
def bit (x : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then x ⟨i, h⟩ else false

theorem cabe_bit (i : ℕ) : Cabe (fun x : Fin n → Bool => bit x i) 1 := by
  by_cases h : i < n
  · exact cabe_congr (cabe_mono (cabe_proy ⟨i, h⟩) (by omega)) fun x => by simp [bit, h]
  · exact cabe_congr cabe_falso fun x => by simp [bit, h]

/-- **Una disyunción de `J + 1` funciones** cabe en la suma de sus tamaños más uno por término. -/
theorem cabe_disy (h : ℕ → (Fin n → Bool) → Bool) (B : ℕ → ℕ) (hB : ∀ j, Cabe (h j) (B j)) :
    ∀ J, Cabe (fun x => decide (∃ j ≤ J, h j x = true)) (∑ j ∈ Finset.range (J + 1), (B j + 1))
  | 0 => by
    refine cabe_congr (cabe_mono (hB 0) (by simp)) fun x => ?_
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    exact ⟨fun hx => ⟨0, le_rfl, hx⟩, fun ⟨j, hj, hx⟩ => by rwa [show j = 0 by omega] at hx⟩
  | J + 1 => by
    refine cabe_congr (cabe_mono (cabe_o (cabe_disy h B hB J) (hB (J + 1)))
      (by rw [Finset.sum_range_succ (n := J + 1)]; omega)) fun x => ?_
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨j, hj, hx⟩ | hx)
      · exact ⟨j, by omega, hx⟩
      · exact ⟨J + 1, le_rfl, hx⟩
    · rintro ⟨j, hj, hx⟩
      rcases Nat.lt_or_ge j (J + 1) with hj' | hj'
      · exact Or.inl ⟨j, by omega, hx⟩
      · exact Or.inr (by rwa [show j = J + 1 by omega] at hx)

/-- **Una conjunción de `j` funciones de tamaño `B`** cabe en `j·(B+1) + 3`. -/
theorem cabe_conj (h : ℕ → (Fin n → Bool) → Bool) (B : ℕ) (hB : ∀ i, Cabe (h i) B) :
    ∀ j, Cabe (fun x => decide (∀ i < j, h i x = true)) (j * (B + 1) + 3)
  | 0 => cabe_congr (cabe_mono cabe_verdadero (by omega)) fun _ =>
    (decide_eq_true fun i hi => absurd hi (Nat.not_lt_zero i)).symm
  | j + 1 => by
    refine cabe_congr (cabe_mono (cabe_y (cabe_conj h B hB j) (hB j)) (by rw [Nat.succ_mul]; omega)) fun x => ?_
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i j with hi' | hi'
      · exact h1 i hi'
      · rwa [show i = j by omega]
    · intro h1
      exact ⟨fun i hi => h1 i (by omega), h1 j (by omega)⟩

/-! ## 2. El marco -/

/-- La lista se desenmarca en largo `j`: `j` marcadores `true` seguidos de su bit, y después o no cabe un par completo
o el marcador siguiente es `false`. -/
def Marca (l : List Bool) (j : ℕ) : Prop :=
  (∀ i < j, 2 * i + 2 ≤ l.length ∧ l.getD (2 * i) false = true) ∧
    (l.length < 2 * j + 2 ∨ l.getD (2 * j) false = false)

/-- **Con la marca de largo `j`, `unframe` lee los bits impares hasta `2j`.** -/
theorem unframe_de_marca : ∀ (j : ℕ) (l : List Bool), Marca l j →
    unframe l = List.ofFn (fun i : Fin j => l.getD (2 * i + 1) false)
  | 0, [], _ => rfl
  | 0, [a], _ => by cases a <;> rfl
  | 0, a :: b :: u, ⟨_, h⟩ => by
    simp only [List.length_cons] at h
    rcases h with h | rfl
    · omega
    · rfl
  | j + 1, l, ⟨h1, h2⟩ => by
    obtain ⟨hl, hv⟩ := h1 0 (by omega)
    match l, hl, hv with
    | true :: b :: u, _, _ =>
      have hu : Marca u j := by
        refine ⟨fun i hi => ?_, ?_⟩
        · obtain ⟨a1, a2⟩ := h1 (i + 1) (by omega)
          simp only [List.length_cons] at a1
          refine ⟨by omega, ?_⟩
          rwa [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ] at a2
        · simp only [List.length_cons] at h2
          rcases h2 with h2 | h2
          · exact Or.inl (by omega)
          · right
            rwa [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ] at h2
      simp only [unframe]
      rw [unframe_de_marca j u hu, List.ofFn_succ]
      simp only [Fin.val_zero, mul_zero, zero_add, List.getD_cons_succ, List.getD_cons_zero, Fin.val_succ]
      congr 2

/-- **Toda lista tiene su marca**: la del largo de `unframe`. -/
theorem marca_largo : ∀ (l : List Bool), Marca l (unframe l).length
  | [] => ⟨fun i hi => by simp [unframe] at hi, Or.inl (by simp [unframe])⟩
  | [a] => ⟨fun i hi => by cases a <;> simp [unframe] at hi, Or.inl (by cases a <;> simp [unframe])⟩
  | false :: b :: u => ⟨fun i hi => by simp [unframe] at hi, Or.inr (by simp [unframe])⟩
  | true :: b :: u => by
    obtain ⟨h1, h2⟩ := marca_largo u
    simp only [unframe, List.length_cons]
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · simp
      · obtain ⟨a1, a2⟩ := h1 i (by omega)
        refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        rwa [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]
    · rcases h2 with h2 | h2
      · exact Or.inl (by simp only [List.length_cons]; omega)
      · right
        rwa [show 2 * ((unframe u).length + 1) = 2 * (unframe u).length + 1 + 1 by omega, List.getD_cons_succ,
          List.getD_cons_succ]

theorem largo_unframe_le : ∀ (l : List Bool), 2 * (unframe l).length ≤ l.length
  | [] => by simp [unframe]
  | [a] => by cases a <;> simp [unframe]
  | false :: b :: u => by simp [unframe]
  | true :: b :: u => by
    have := largo_unframe_le u
    simp only [unframe, List.length_cons]
    omega

/-! ## 3. SAT enmarcado como disyunción sobre los largos -/

theorem getD_ofFn (x : Fin n → Bool) (i : ℕ) : (List.ofFn x).getD i false = bit x i := by
  unfold bit
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

/-- La marca de largo `j` como función booleana de la entrada (para `j ≤ m/2`). -/
def marcaB (m j : ℕ) (x : Fin m → Bool) : Bool :=
  decide (∀ i < j, bit x (2 * i) = true) && (if m < 2 * j + 2 then true else !bit x (2 * j))

/-- El término `j`: `satBits` sobre los bits impares. -/
noncomputable def satImpar (m j : ℕ) (x : Fin m → Bool) : Bool :=
  satBits (List.ofFn (fun i : Fin j => bit x (2 * i + 1)))

theorem marcaB_iff {m j : ℕ} (hj : 2 * j ≤ m) (x : Fin m → Bool) :
    marcaB m j x = true ↔ Marca (List.ofFn x) j := by
  simp only [marcaB, Marca, List.length_ofFn, getD_ofFn, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr ⟨fun h i hi => ⟨by omega, h i hi⟩, fun h i hi => (h i hi).2⟩ ?_
  split_ifs with h
  · simp [h]
  · simp only [Bool.not_eq_true', h, false_or]

/-- **SAT enmarcado, por largos.** -/
theorem rebanada_satMarco (m : ℕ) (x : Fin m → Bool) :
    rebanada satMarco m x = decide (∃ j ≤ m / 2, (marcaB m j x && satImpar m j x) = true) := by
  have hx : rebanada satMarco m x = satBits (unframe (List.ofFn x)) := rfl
  rw [hx]
  have hof : ∀ j, Marca (List.ofFn x) j → unframe (List.ofFn x) = List.ofFn (fun i : Fin j => bit x (2 * i + 1)) :=
    fun j hm => by rw [unframe_de_marca j _ hm]; simp only [getD_ofFn]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro hs
    set j := (unframe (List.ofFn x)).length
    have hj : 2 * j ≤ m := by simpa using largo_unframe_le (List.ofFn x)
    refine ⟨j, by omega, (marcaB_iff hj x).2 (marca_largo _), ?_⟩
    rw [satImpar, ← hof j (marca_largo _)]
    exact hs
  · rintro ⟨j, hj, hm, hs⟩
    rw [hof j ((marcaB_iff (by omega) x).1 hm)]
    exact hs

theorem cabe_marcaB (m j : ℕ) : Cabe (marcaB m j) (2 * j + 7) := by
  have h1 := cabe_conj (fun i (x : Fin m → Bool) => bit x (2 * i)) 1 (fun i => cabe_bit (2 * i)) j
  have h2 : Cabe (fun x : Fin m → Bool => if m < 2 * j + 2 then true else !bit x (2 * j)) 3 := by
    split_ifs
    · exact cabe_verdadero
    · exact cabe_no (cabe_bit (2 * j))
  exact cabe_mono (cabe_y h1 h2) (by omega)

theorem cabe_satImpar (m j : ℕ) : Cabe (satImpar m j) (sucNat satBits j + 2) := by
  refine cabe_fijar ⟨fun i => if h : 2 * (i : ℕ) + 1 < m then .inl ⟨2 * i + 1, h⟩ else .inr false, fun x => ?_⟩
    (cabe_rebanada satBits j)
  simp only [satImpar, rebanada]
  congr 1
  apply List.ofFn_inj.2
  funext i
  simp only [sustituir, bit]
  split_ifs <;> rfl

/-- **El circuito de SAT enmarcado.** -/
theorem cabe_satMarco (m : ℕ) :
    Cabe (rebanada satMarco m) (∑ j ∈ Finset.range (m / 2 + 1), ((2 * j + 7) + (sucNat satBits j + 2) + 1 + 1)) :=
  cabe_congr (cabe_disy _ _ (fun j => cabe_y (cabe_marcaB m j) (cabe_satImpar m j)) (m / 2))
    fun x => (rebanada_satMarco m x).symm

/-- La cota polinomial. -/
theorem sucNat_satMarco_le {c k : ℕ} (h : ∀ j, sucNat satBits j ≤ c * (j + 1) ^ k) (m : ℕ) :
    sucNat satMarco m ≤ (c + 13) * (m + 1) ^ (k + 2) := by
  refine (sucNat_le_de_cabe (cabe_satMarco m)).trans ?_
  have hp : 1 ≤ (m + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have hterm : ∀ j ∈ Finset.range (m / 2 + 1),
      (2 * j + 7) + (sucNat satBits j + 2) + 1 + 1 ≤ (c + 13) * (m + 1) ^ (k + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : j + 1 ≤ m + 1 := by omega
    have h1 : sucNat satBits j ≤ c * (m + 1) ^ k :=
      (h j).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hjm k))
    have h2 : (m + 1) ^ (k + 1) = (m + 1) ^ k * (m + 1) := pow_succ _ _
    have h3 : c * (m + 1) ^ k ≤ c * (m + 1) ^ (k + 1) := by
      rw [h2]; exact Nat.mul_le_mul_left c (Nat.le_mul_of_pos_right _ (by omega))
    have h4 : 2 * j + 11 ≤ 13 * (m + 1) ^ (k + 1) := by
      rw [h2]
      have : m + 1 ≤ (m + 1) ^ k * (m + 1) := Nat.le_mul_of_pos_left _ hp
      omega
    nlinarith
  calc ∑ j ∈ Finset.range (m / 2 + 1), ((2 * j + 7) + (sucNat satBits j + 2) + 1 + 1)
      ≤ ∑ _j ∈ Finset.range (m / 2 + 1), (c + 13) * (m + 1) ^ (k + 1) := Finset.sum_le_sum hterm
    _ = (m / 2 + 1) * ((c + 13) * (m + 1) ^ (k + 1)) := by simp
    _ ≤ (m + 1) * ((c + 13) * (m + 1) ^ (k + 1)) := Nat.mul_le_mul_right _ (by omega)
    _ = (c + 13) * (m + 1) ^ (k + 2) := by ring

/-- **El puente: `SatMarcoDeSatBits` de `Relleno.lean`, probado.** -/
theorem satMarcoDeSatBits : SatMarcoDeSatBits := by
  intro h
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff] at h ⊢
  obtain ⟨c, k, hc⟩ := h
  exact ⟨c + 13, k + 2, sucNat_satMarco_le hc⟩

/-- Las dos versiones de SAT están juntas en P/poly o juntas fuera. -/
theorem satMarco_iff_satBits : satMarco ∈ PsobrePoly ↔ satBits ∈ PsobrePoly :=
  ⟨satBits_de_satMarco, satMarcoDeSatBits⟩

/-! ## 4. La tricotomía de SAT, unificada -/

open SatEnElBorde

/-- Abajo del borde, para SAT enmarcado, es exactamente que `satBits` tenga circuitos polinomiales. -/
theorem bajo_satMarco_iff : Bajo (sucNat satMarco) ↔ satBits ∈ PsobrePoly :=
  (bajo_sucNat_iff satMarco).trans satMarco_iff_satBits

/-- **La tricotomía de SAT, exacta** (corolario nuevo; `SatEnElBorde.tricotomia_sat` queda como estaba). Las tres ramas
hablan del costo del mismo problema, `satMarco`; la primera equivale a `satBits ∈ P/poly`; y se excluyen dos a dos: es
una partición. -/
theorem tricotomia_sat_exacta :
    ((satBits ∈ PsobrePoly ↔ Bajo (sucNat satMarco)) ∧
      (Bajo (sucNat satMarco) ∨ Sobre (sucNat satMarco) ∨
        (Oscila (sucNat satMarco) ∧ ∀ c k a b, {n | Hueco satMarco c k a b n}.Infinite))) ∧
    ¬ (Bajo (sucNat satMarco) ∧ Sobre (sucNat satMarco)) ∧ ¬ (Bajo (sucNat satMarco) ∧ Oscila (sucNat satMarco)) ∧
      ¬ (Sobre (sucNat satMarco) ∧ Oscila (sucNat satMarco)) := by
  refine ⟨⟨bajo_satMarco_iff.symm, ?_⟩, disjuntas _⟩
  rcases tricotomia_sat with h | h | h
  · exact Or.inl (bajo_satMarco_iff.2 h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **Fuera de P/poly si y solo si hay huecos**: la vuelta de `Relleno.huecos_de_sat`. -/
theorem fuera_iff_huecos_sat :
    satBits ∉ PsobrePoly ↔ ∀ c k a b, {n | Hueco satMarco c k a b n}.Infinite := by
  rw [← satMarco_iff_satBits]
  exact fuera_iff_huecos rellenable_satMarco

/-! ## Controles -/

/-- La marca no es trivial: `[true, true, false, false]` se desenmarca en largo 1 y no en 0 ni en 2. -/
example : Marca [true, true, false, false] 1 ∧ ¬ Marca [true, true, false, false] 0 ∧
    ¬ Marca [true, true, false, false] 2 := by
  refine ⟨⟨fun i hi => ?_, Or.inr rfl⟩, fun ⟨_, h⟩ => ?_, fun ⟨h, _⟩ => ?_⟩
  · obtain rfl : i = 0 := by omega
    exact ⟨by simp, rfl⟩
  · simp at h
  · have := (h 1 (by omega)).2; simp at this

/-- `unframe_de_marca` en un caso concreto: lee el bit 1. -/
example : unframe [true, true, false, false] = [true] :=
  unframe_de_marca 1 _ ⟨fun i hi => (by obtain rfl : i = 0 := by omega
                                        exact ⟨by simp, rfl⟩), Or.inr rfl⟩

/-- La disyunción no se puede achicar a un solo largo fijo: con la entrada vacía la marca es la de largo 0 y con
`[true, b]` la de largo 1. -/
example : Marca [] 0 ∧ Marca [true, false] 1 :=
  ⟨⟨fun i hi => absurd hi (by omega), Or.inl (by simp)⟩,
   ⟨fun i hi => (by obtain rfl : i = 0 := by omega
                    exact ⟨by simp, rfl⟩), Or.inl (by simp)⟩⟩

/- Mutantes probados (25 nov 2026, fuera del repositorio):
* `MutMarca.lean`: quitar de `Marca` la condición de cierre (dejar `… ∧ True`). No compila: el caso `j = 0` de
  `unframe_de_marca` ya no tiene con qué descartar un par `true :: b :: u`, y el enunciado mutado es falso
  (`[true, true]` tendría marca de largo `0` pero `unframe [true, true] = [true]`).
* `MutImpar.lean`: en `satImpar`, leer los bits pares (`bit x (2 * i)`, los marcadores) en vez de los impares. No
  compila: `rebanada_satMarco` falla en `rw [satImpar, ← hof …]` (lo que se le pasa a `satBits` ya no es `unframe`) y
  `cabe_satImpar` en el `rfl` del reetiquetado. -/

end Sagitta.Map.Borde.MarcoDeBits
