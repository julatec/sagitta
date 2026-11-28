import Sagitta.Map.PLS

/-!
# Buscar un certificado de NP como un descenso

El «paso meta»: ¿se puede ver el costo de encontrar la respuesta corta de un problema de NP como el costo de un
descenso? Dos resultados, uno a favor y uno en contra.

1. **La ruta sí es un descenso** (`Exhaustiva`). Probar los candidatos en orden es un descenso con costo natural:
   «candidatos que faltan», o cero si el actual es un certificado. Seguir al vecino desde el primer candidato tarda
   exactamente tantos pasos como la posición del primer certificado (`ruta`). El costo es el reloj, como en todo el
   proyecto.

2. **Pero como problema de PLS es trivial** (`ultimo_esOptimo`). PLS acepta *cualquier* óptimo local, y el último
   candidato siempre lo es, haya certificado o no. La búsqueda de NP pide el óptimo *al que llega la ruta*, no uno
   cualquiera.

3. **Y no es un defecto de esta codificación** (`np_y_conp_de_tfnp`). Si las soluciones de un problema de `TFNP`
   deciden un lenguaje `L` (de cada solución se lee, en tiempo polinomial, si `x ∈ L`), entonces `L ∈ NP ∩ coNP`: la
   solución, que siempre existe y es corta, sirve de certificado tanto del «sí» como del «no». Por eso, si toda
   búsqueda de NP se pudiera codificar así, sería `NP ⊆ coNP` (`np_sub_conp_de_tfnp`). Es el argumento de Megiddo y
   Papadimitriou (1991). Sin hipótesis: el cierre del tiempo polinomial y la negación de un bit están probados.
   Para PLS en particular es el lema 4 de Johnson, Papadimitriou y Yannakakis (1988, p. 85).
-/

namespace Sagitta.Map

/-! ## 1 y 2. La búsqueda exhaustiva como descenso -/

namespace Exhaustiva

/-- `N` candidatos, numerados desde cero; `cert i` dice si el candidato `i` es un certificado. -/
structure Busca where
  N : ℕ
  cert : ℕ → Bool

variable (B : Busca)

/-- El costo: cero en un certificado; si no, los candidatos que faltan. -/
def costo (i : ℕ) : ℕ := if B.cert i then 0 else B.N - i

/-- El vecino: el candidato siguiente, salvo en un certificado o en el último. -/
def vecino (i : ℕ) : ℕ := if B.cert i ∨ B.N ≤ i + 1 then i else i + 1

/-- Un óptimo local. -/
def EsOptimo (i : ℕ) : Prop := costo B i ≤ costo B (vecino B i)

theorem esOptimo_iff (i : ℕ) : EsOptimo B i ↔ B.cert i = true ∨ B.N ≤ i + 1 := by
  unfold EsOptimo vecino
  by_cases h : B.cert i = true ∨ B.N ≤ i + 1
  · simp [h]
  · simp only [h, ↓reduceIte, iff_false, not_le]
    push Not at h
    obtain ⟨h1, h2⟩ := h
    unfold costo
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> omega

/-- **PLS acepta cualquier óptimo, y el último candidato siempre lo es.** Como problema de PLS, la búsqueda
exhaustiva es trivial: su respuesta no dice si hay certificado. -/
theorem ultimo_esOptimo (hN : 0 < B.N) : EsOptimo B (B.N - 1) :=
  (esOptimo_iff B _).mpr (Or.inr (by omega))

/-- Antes del primer certificado, la ruta avanza de a un candidato. -/
theorem iterate_eq (k : ℕ) (hk : k < B.N) (hno : ∀ j < k, B.cert j = false) :
    ∀ j ≤ k, (vecino B)^[j] 0 = j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [Function.iterate_succ_apply', ih (by omega)]
    unfold vecino
    rw [ite_eq_right]
    rw [hno j (by omega)]
    simp
    omega

/-- **La ruta.** Si el primer certificado es el candidato `k`, seguir al vecino desde el candidato cero llega a él
en exactamente `k` pasos, y no hay óptimo antes. El costo de encontrar la respuesta es la posición del primer
certificado. -/
theorem ruta (k : ℕ) (hk : k < B.N) (hcert : B.cert k = true) (hno : ∀ j < k, B.cert j = false) :
    (vecino B)^[k] 0 = k ∧ EsOptimo B ((vecino B)^[k] 0) ∧
      ∀ j < k, ¬ EsOptimo B ((vecino B)^[j] 0) := by
  have hit := iterate_eq B k hk hno
  refine ⟨hit k le_rfl, ?_, fun j hj => ?_⟩
  · rw [hit k le_rfl]
    exact (esOptimo_iff B k).mpr (Or.inl hcert)
  · rw [hit j hj.le, esOptimo_iff B j, hno j hj]
    simp
    omega

end Exhaustiva

/-! ## 3. Por qué ninguna codificación en TFNP alcanza -/

/-- Las soluciones de `R` **deciden** `L`: de cualquier solución `y` de `x` se lee, en tiempo polinomial, si `x`
está en `L`. -/
def DecididoPor (L : Problema) (R : Busqueda) : Prop :=
  ∃ d : List Bool × List Bool → Bool, EsPolinomial d ∧ ∀ x y, R x y → d (x, y) = L x

/-- **Megiddo–Papadimitriou.** Si las soluciones de un problema de `TFNP` deciden `L`, entonces `L ∈ NP ∩ coNP`: la
solución, que siempre existe y es corta, certifica el «sí» y también el «no». -/
theorem np_y_conp_de_tfnp
    {L : Problema} {R : Busqueda} (hR : EnTFNP R) (hd : DecididoPor L R) : L ∈ NP ∧ L ∈ coNP := by
  obtain ⟨hcomp, hpar, -, hand, -⟩ := cierrePolinomial
  have hneg := Basicas.esPolinomial_no
  obtain ⟨p, V, hV, hiff, hlen, htot⟩ := hR
  obtain ⟨d, hdpol, hdec⟩ := hd
  have hnd : EsPolinomial (fun q : List Bool × List Bool => !d q) := hcomp _ _ hdpol hneg
  constructor
  · refine ⟨p, fun q => V q && d q, hcomp _ _ (hpar _ _ hV hdpol) hand, fun x => ?_⟩
    constructor
    · intro hL
      obtain ⟨y, hy⟩ := htot x
      exact ⟨y, hlen x y hy, by simp [(hiff x y).mp hy, hdec x y hy, hL]⟩
    · rintro ⟨y, -, hy⟩
      simp only [Bool.and_eq_true] at hy
      rw [← hdec x y ((hiff x y).mpr hy.1)]
      exact hy.2
  · refine ⟨p, fun q => V q && !d q, hcomp _ _ (hpar _ _ hV hnd) hand, fun x => ?_⟩
    constructor
    · intro hL
      obtain ⟨y, hy⟩ := htot x
      refine ⟨y, hlen x y hy, ?_⟩
      simp only [Bool.not_eq_true'] at hL
      simp [(hiff x y).mp hy, hdec x y hy, hL]
    · rintro ⟨y, -, hy⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy
      simp only [Bool.not_eq_true']
      rw [← hdec x y ((hiff x y).mpr hy.1)]
      exact hy.2

/-- **Si toda búsqueda de NP se codificara en TFNP, sería NP ⊆ coNP.** -/
theorem np_sub_conp_de_tfnp
    (hcod : ∀ L ∈ NP, ∃ R, EnTFNP R ∧ DecididoPor L R) : NP ⊆ coNP := by
  intro L hL
  obtain ⟨R, hR, hd⟩ := hcod L hL
  exact (np_y_conp_de_tfnp hR hd).2

end Sagitta.Map
