import Sagitta.Map.DetectorResolucion
import CslibFrontier.Logics.Propositional.Frege.Resolution

/-!
# Detectores certificados por Frege (peldaño condicional)

Peldaño «Frege» de la escalera de detectores (ver las notas del proyecto). `DetectorResolucion.lean` probó la cota para
detectores cuyos veredictos «muerto» vienen con una derivación por resolución. Aquí vienen con una prueba de Frege: el
sistema de Hilbert de cslib-frontier (axiomas K, S, eliminación de doble negación, `∧`, `∨`; modus ponens).

## Lo que se prueba

* `CertificaFrege F N det c`: cada vez que `det` dice «muerto» en `p` (de largo `≤ N`), hay una prueba de Frege de a
  lo sumo `c p` líneas, desde las cláusulas de `F` como fórmulas (`hipFrege F`), de `ℓ₀ → ℓ₁ → ⋯ → ⊥`. Los `ℓᵢ` son
  los literales de `p` (`litsFrege p`). Esa fórmula niega la conjunción de los literales, escrita en forma curry.
* **La forma elegida.** Probar `ℓ₀ → ⋯ → ⊥` desde `Γ` equivale a probar `⊥` desde `Γ` más los literales, con costo
  lineal en las dos direcciones: `imps_de_bot` (deducción, `10 (|p|+1)` por línea) y `bot_de_imps` (`2 |p|` líneas
  más). Se eligió la forma con implicaciones porque las hipótesis no cambian de nodo a nodo: así las pruebas de los
  dos hijos se juntan sin volver a aplicar la deducción a toda la prueba, que multiplicaría por `20` en cada nivel.
* **El paso de la rama** (`paso_frege`): de `P → ¬x → ⊥` y `P → x → ⊥` sale `P → ⊥`, con `22 |P| + 164` líneas más.
  Es el tercero excluido: `tercero` prueba `¬¬x → ¬x → ⊥` en `150` líneas (deducción sobre 5 líneas que usan la
  eliminación de doble negación), y se distribuye bajo `P` con `imps_dist` de cslib (`5 + 10 |P|` cada vez).
* **El puente** (`refuta_debajo_frege`, `refutacion_traza_frege`): si `F` no tiene solución, la traza de `buscar` da
  una refutación de Frege de `F` (una prueba de `⊥` desde `hipFrege F`) de a lo sumo `peso … (costoFrege N det c) N []`
  líneas: `c p` donde `det` dijo «muerto», `cotaFrege N = 10 (N+1)(2N+1) + 22 N + 165` en los demás nodos. Con
  `c ≤ K`: a lo sumo `nodos · max K (cotaFrege N)` (`refutacion_traza_frege_nodos`), es decir `O(nodos · N² + Σ c)`.
  Las hojas completas cuestan `O(N²)`: la cláusula falsa se debilita a `ℓ₀ → ⋯ → ⊥` con la deducción
  (`imps_de_clausula`). Las ramas cuestan `O(N)`.
* **El corolario condicional** (`frege_sin_demora_log`): si `ConFregeDificil φ N` (fórmulas `φ n` insatisfacibles, sin
  refutaciones de Frege de tamaño polinomial en el número de variables), ningún detector certificado por Frege con
  pruebas de tamaño polinomial tiene demora logarítmica sobre la familia. No pide que el detector sea sano: lo es por
  estar certificado (`certificaFrege_sanoN`).
* **Casos particulares** (`certificaFrege_de_res`, `certificaFrege_de_res_N`, `res_sin_demora_log_de_frege`): todo
  detector de `CertificaRes` está en `CertificaFrege`, con costo `stepBound (2N) · c p + 10 (N+1)(2N+1)` (la
  simulación de cslib-frontier, `CNF.IsProof.frege`). `detCNF` está en `CertificaFrege` con costo
  `1 + 10 (N+1)(2N+1)` (`certificaFrege_detCNF`).
* **Controles**: la hipótesis del puente se cumple (`detCNF`, y `contra3` con la refutación que sale); `CertificaFrege`
  no es trivial (no certifica un detector que no es sano, ni la raíz con tamaño `0`); `ConFregeDificil` no es trivial
  (falla en una familia constante) y no es «no hay refutación» disfrazado: por la completitud para CNF de
  cslib-frontier, toda `φ n` tiene alguna refutación (`refutacion_existe`); las demás premisas del corolario se cumplen
  con `detCNF`.

## Por qué es condicional

* **La contradicción incondicional en este peldaño es un problema abierto.** No se conoce ninguna cota inferior
  superpolinomial para Frege. No conocemos ninguna familia que cumpla `ConFregeDificil`. El teorema reduce la
  contradicción para detectores certificados por Frege exactamente a una cota inferior para Frege.
* *De memoria, sin verificar contra la fuente:* el palomar no sirve aquí. Frege lo refuta en tamaño polinomial
  (Buss 1987), así que el peldaño de resolución (`palomar_res`) no sube.
* *De memoria, sin verificar contra la fuente:* la herramienta de los peldaños anteriores, la interpolación factible,
  no se espera para Frege. Bonet, Pitassi y Raz mostraron que, bajo supuestos criptográficos, sistemas como Frege no
  la tienen.

## Lo que no se prueba

* Ninguna cota inferior para Frege. Ninguna familia concreta que cumpla `ConFregeDificil`.
* La completitud general de Frege (issue #3069 de cslib-frontier). Para CNF sí está, vía la simulación de resolución,
  y es lo que usa `refutacion_existe`.
* Se cuentan líneas, no símbolos. Las fórmulas de la traza tienen `O(N)` conectivos cada una, pero eso no se mide.
* Las pruebas de los veredictos son independientes: si se reusan entre nodos, `c` cuenta la prueba entera en cada uso.
* La búsqueda sigue un orden fijo de variables. Contar líneas y nodos no es tiempo de máquina de Turing.
-/

open Cslib Cslib.Logic.PL Cslib.Logic.PL.Frege Cslib.Logic.PL.Frege.Formula

namespace Sagitta.Map.Tiempo.DetectorFrege

/-! ## Las definiciones -/

/-- Las hipótesis: las cláusulas de `F` como fórmulas de Frege (`Clause.toFormula`). -/
def hipFrege (F : List Clausula) : List (Formula ℕ) := (F : CNF ℕ).map Clause.toFormula

/-- El literal de la variable `i` con valor `b`: `xᵢ` si `b`, `¬xᵢ` si no. -/
def litFrege (i : ℕ) (b : Bool) : Formula ℕ := if b then var i else Proposition.neg (var i)

/-- Los literales del prefijo `p`, en orden: `p[i]` fija la variable `i`. -/
def litsFrege (p : List Bool) : List (Formula ℕ) := p.mapIdx fun i b => litFrege i b

/-- **Detector certificado por Frege con tamaño `c`.** Cada vez que `det` dice «muerto» en un prefijo `p` de largo
`≤ N`, hay una prueba de Frege desde `hipFrege F` de `ℓ₀ → ⋯ → ℓ_{|p|-1} → ⊥`, con a lo sumo `c p` líneas. -/
def CertificaFrege (F : List Clausula) (N : ℕ) (det : List Bool → Bool) (c : List Bool → ℕ) : Prop :=
  ∀ p : List Bool, p.length ≤ N → det p = true → DerivableInSize (hipFrege F) (imps (litsFrege p) ⊥) (c p)

/-- El costo fijo de un nodo donde el detector no dispara: cubre la hoja completa y la rama. -/
def cotaFrege (N : ℕ) : ℕ := 10 * (N + 1) * (2 * N + 1) + 22 * N + 165

/-- El costo de cada nodo de la búsqueda: `c p` donde el detector dice «muerto», `cotaFrege N` en los demás. -/
def costoFrege (N : ℕ) (det : List Bool → Bool) (c : List Bool → ℕ) (p : List Bool) : ℕ :=
  if det p then c p else cotaFrege N

/-! ## Los literales de un prefijo -/

theorem length_litsFrege (p : List Bool) : (litsFrege p).length = p.length := by simp [litsFrege]

theorem litsFrege_snoc (p : List Bool) (b : Bool) :
    litsFrege (p ++ [b]) = litsFrege p ++ [litFrege p.length b] := by
  simp [litsFrege, List.mapIdx_append]

theorem mem_litsFrege {p : List Bool} {φ : Formula ℕ} :
    φ ∈ litsFrege p ↔ ∃ (i : ℕ) (h : i < p.length), litFrege i p[i] = φ := by
  simp [litsFrege, List.mem_mapIdx]

theorem eval_litFrege (σ : ℕ → Bool) (i : ℕ) (b : Bool) : (litFrege i b).eval σ = (σ i == b) := by
  cases b <;> cases h : σ i <;> simp [litFrege, h]

/-- Si `σ` sigue a `p`, los literales de `p` son verdaderos en `σ`. -/
theorem eval_litsFrege {σ : ℕ → Bool} {p : List Bool} (hs : Sigue σ p) :
    ∀ φ ∈ litsFrege p, φ.eval σ = true := by
  intro φ hφ
  obtain ⟨i, hi, rfl⟩ := mem_litsFrege.1 hφ
  simp [eval_litFrege, hs i hi]

theorem imps_append (Δ Δ' : List (Formula ℕ)) (φ : Formula ℕ) : imps (Δ ++ Δ') φ = imps Δ (imps Δ' φ) := by
  simp [imps, List.foldr_append]

/-- La negación de un literal de cláusula es el literal de `p` con el valor contrario. -/
theorem negFormula_eq (l : ℕ × Bool) : Literal.negFormula l = litFrege l.1 (!l.2) := by
  obtain ⟨v, b⟩ := l
  cases b <;> rfl

theorem negFormula_inj : Function.Injective (Literal.negFormula : Literal ℕ → Formula ℕ) := by
  rintro ⟨u, a⟩ ⟨v, b⟩ h
  cases a <;> cases b <;> simp_all [Literal.negFormula]

/-- **Una cláusula falsa debajo de `p` tiene sus antecedentes entre los literales de `p`.** Si `C` es falsa en toda
asignación que sigue a `p`, cada literal de `C` tiene su variable fijada por `p` con el valor contrario. -/
theorem negFormula_mem {C : Clausula} {p : List Bool} (hC : ∀ σ, Sigue σ p → Clause.eval σ C = false) :
    ∀ l ∈ C, Literal.negFormula l ∈ litsFrege p := by
  intro l hl
  by_cases h : ∃ (hi : l.1 < p.length), p[l.1] = !l.2
  · obtain ⟨hi, he⟩ := h
    rw [negFormula_eq, ← he]
    exact mem_litsFrege.2 ⟨l.1, hi, rfl⟩
  · exfalso
    set σ : ℕ → Bool := fun i => if i = l.1 then l.2 else p.getD i false with hσ
    have hs : Sigue σ p := by
      intro i hi
      by_cases hil : i = l.1
      · subst hil
        have : p[l.1] ≠ !l.2 := fun he => h ⟨hi, he⟩
        simp only [hσ, ite_true]
        cases hb : l.2 <;> cases hp : p[l.1] <;> simp_all
      · simp [hσ, hil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hev := hC σ hs
    simp only [Clause.eval, List.any_eq_false] at hev
    exact hev l hl (by simp [Literal.eval, hσ])

/-! ## Herramientas de Frege con conteo de líneas -/

/-- Una extensión agrega a lo sumo `n` líneas. -/
theorem Grows.length_le' {Γ L L' : List (Formula ℕ)} {n : ℕ} (g : Grows Γ L L' n) : L'.length ≤ L.length + n := by
  obtain ⟨m₁, rfl, -, hm₁⟩ := g
  simp only [List.length_append]; omega

/-- Debilitar bajo los antecedentes `Δ`, dos líneas por antecedente. -/
theorem lifts {Γ : List (Formula ℕ)} {n : ℕ} {φ : Formula ℕ} (Δ : List (Formula ℕ))
    (h : DerivableInSize Γ φ n) : DerivableInSize Γ (imps Δ φ) (n + 2 * Δ.length) := by
  induction Δ with
  | nil => simpa using h
  | cons a Δ ih => exact (ih.lift a).mono (by simp; omega)

/-- **El tercero excluido, en forma de reglas**: `¬¬a → ¬a → ⊥` en `150` líneas. Desde `¬¬a` y `¬a`: la eliminación
de doble negación da `a`, y modus ponens da `⊥` (5 líneas); la deducción con dos hipótesis cuesta `10 · 3` por
línea. -/
theorem tercero (Γ : List (Formula ℕ)) (a : Formula ℕ) :
    DerivableInSize Γ (imp (imp (Proposition.neg a) ⊥) (imp (imp a ⊥) ⊥)) 150 := by
  set Γ' := Γ ++ [imp (Proposition.neg a) ⊥, imp a ⊥]
  have h₁ : IsProof Γ' [imp (Proposition.neg a) ⊥] := IsProof.nil.hyp (by simp [Γ'])
  have h₂ : IsProof Γ' [imp (Proposition.neg (Proposition.neg a)) a, imp (Proposition.neg a) ⊥] :=
    h₁.ax (IsAxiom.dne a)
  have h₃ : IsProof Γ' [a, imp (Proposition.neg (Proposition.neg a)) a, imp (Proposition.neg a) ⊥] :=
    h₂.mp (φ := imp (Proposition.neg a) ⊥) (by simp) List.mem_cons_self
  have h₄ := h₃.hyp (φ := imp a ⊥) (by simp [Γ'])
  have h : IsProof Γ' [⊥, imp a ⊥, a, imp (Proposition.neg (Proposition.neg a)) a, imp (Proposition.neg a) ⊥] :=
    h₄.mp (φ := a) (by simp) List.mem_cons_self
  obtain ⟨L, g, hL⟩ := IsProof.deduction (Γ := Γ) (Δ := [imp (Proposition.neg a) ⊥, imp a ⊥]) h (L := []) .nil
  exact ⟨L, g.proof, by simpa using hL ⊥ (by simp), by simpa using g.length_of_nil⟩

/-- **El paso de la rama.** De `P → ¬x → ⊥` y `P → x → ⊥` sale `P → ⊥`, con `22 |P| + 164` líneas más que las dos
pruebas juntas: `tercero` debilitado bajo `P` (`150 + 2 |P|`), dos distribuciones (`5 + 10 |P|` cada una) y cuatro
modus ponens. -/
theorem paso_frege {Γ : List (Formula ℕ)} (P : List (Formula ℕ)) (x : Formula ℕ) {m₀ m₁ : ℕ}
    (h₀ : DerivableInSize Γ (imps (P ++ [Proposition.neg x]) ⊥) m₀)
    (h₁ : DerivableInSize Γ (imps (P ++ [x]) ⊥) m₁) :
    DerivableInSize Γ (imps P ⊥) (m₀ + m₁ + 22 * P.length + 164) := by
  rw [imps_append] at h₀ h₁
  simp only [imps_cons, imps_nil] at h₀ h₁
  have T := lifts P (tercero Γ x)
  have s₁ := ((DerivableInSize.imps_dist P _ _).mp T).mp h₀
  have s₂ := ((DerivableInSize.imps_dist P _ _).mp s₁).mp h₁
  exact s₂.mono (by omega)

/-- **Debilitar `Q → ⊥` a `P → ⊥`** cuando todo antecedente de `Q` está en `P`. Se prueba `⊥` desde `Q → ⊥` y `P` en
`2 |Q| + 1` líneas, se descarga `P` con la deducción y se encola sobre la prueba de `Q → ⊥` con `cut`. -/
theorem debilitar_imps {Γ Q P : List (Formula ℕ)} (hQ : ∀ q ∈ Q, q ∈ P) {m : ℕ}
    (h : DerivableInSize Γ (imps Q ⊥) m) :
    DerivableInSize Γ (imps P ⊥) (m + 10 * (P.length + 1) * (2 * Q.length + 1)) := by
  have hp₀ : IsProof ((Γ ++ [imps Q ⊥]) ++ P) [] := .nil
  obtain ⟨M₁, g₁, h₁⟩ := Grows.collect hp₀ (Δ := imps Q ⊥ :: Q) (fun δ hδ => Or.inl (by
    rcases List.mem_cons.1 hδ with rfl | hδ
    · simp
    · exact List.mem_append_right _ (hQ δ hδ)))
  obtain ⟨M₂, g₂, h₂⟩ := Grows.imps_elim g₁.proof (h₁ _ List.mem_cons_self)
    fun δ hδ => h₁ δ (List.mem_cons_of_mem _ hδ)
  have hlen : M₂.length ≤ 2 * Q.length + 1 := by
    have := (g₁.trans g₂).length_of_nil
    simp only [List.length_cons] at this
    omega
  obtain ⟨L', g', h'⟩ := IsProof.deduction (Γ := Γ ++ [imps Q ⊥]) (Δ := P) (Grows.proof (g₁.trans g₂)) (L := []) .nil
  obtain ⟨Lq, hLq, hmem, hlenq⟩ := h
  obtain ⟨M', hM', hlenM', hmemM'⟩ := IsProof.cut g'.proof hLq (by simpa using hmem)
  refine ⟨M' ++ Lq, hM', hmemM' _ (h' _ h₂), ?_⟩
  have hL' := g'.length_of_nil
  have : 10 * (P.length + 1) * M₂.length ≤ 10 * (P.length + 1) * (2 * Q.length + 1) :=
    Nat.mul_le_mul_left _ hlen
  simp only [List.length_append]
  omega

/-- **De una cláusula falsa debajo de `p` a `ℓ₀ → ⋯ → ⊥`.** Los antecedentes de la cláusula son literales de `p`
(`negFormula_mem`), y son a lo sumo `|p|` (sin repetir). -/
theorem imps_de_clausula {Γ : List (Formula ℕ)} {C : Clausula} {p : List Bool}
    (hC : ∀ σ, Sigue σ p → Clause.eval σ C = false) {m : ℕ} (h : DerivableInSize Γ (Clause.toFormula C) m) :
    DerivableInSize Γ (imps (litsFrege p) ⊥) (m + 10 * (p.length + 1) * (2 * p.length + 1)) := by
  have hQ : ∀ q ∈ (C.dedup).map Literal.negFormula, q ∈ litsFrege p := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hq
    exact negFormula_mem hC l (List.mem_dedup.1 hl)
  have hlen : ((C.dedup).map Literal.negFormula).length ≤ p.length := by
    have := (List.subperm_of_subset ((List.nodup_dedup C).map negFormula_inj) hQ).length_le
    rwa [length_litsFrege] at this
  have := debilitar_imps (Q := (C.dedup).map Literal.negFormula) hQ h
  refine this.mono ?_
  rw [length_litsFrege]
  have : 10 * (p.length + 1) * (2 * ((C.dedup).map Literal.negFormula).length + 1) ≤
      10 * (p.length + 1) * (2 * p.length + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## La forma del certificado: con implicaciones o con hipótesis -/

/-- De `⊥` desde `Γ` y los literales a `ℓ₀ → ⋯ → ⊥` desde `Γ`: la deducción, `10 (|P|+1)` por línea. -/
theorem imps_de_bot {Γ P : List (Formula ℕ)} {m : ℕ} (h : DerivableInSize (Γ ++ P) ⊥ m) :
    DerivableInSize Γ (imps P ⊥) (10 * (P.length + 1) * m) := by
  obtain ⟨M, hM, hbot, hlen⟩ := h
  obtain ⟨L, g, hL⟩ := IsProof.deduction (Γ := Γ) (Δ := P) hM (L := []) .nil
  exact ⟨L, g.proof, hL _ hbot, g.length_of_nil.trans (Nat.mul_le_mul_left _ hlen)⟩

/-- De `ℓ₀ → ⋯ → ⊥` desde `Γ` a `⊥` desde `Γ` y los literales: `2 |P|` líneas más. -/
theorem bot_de_imps {Γ P : List (Formula ℕ)} {m : ℕ} (h : DerivableInSize Γ (imps P ⊥) m) :
    DerivableInSize (Γ ++ P) ⊥ (m + 2 * P.length) := by
  obtain ⟨L, hL, hmem, hlen⟩ := h
  have hL' : IsProof (Γ ++ P) L := hL.mono (List.subset_append_left _ _)
  obtain ⟨L₁, g₁, h₁⟩ := Grows.collect hL' (Δ := P) fun δ hδ => Or.inl (List.mem_append_right _ hδ)
  obtain ⟨L₂, g₂, h₂⟩ := Grows.imps_elim g₁.proof (g₁.subset hmem) h₁
  refine ⟨L₂, g₂.proof, h₂, ?_⟩
  have := Grows.length_le' (g₁.trans g₂)
  omega

/-! ## El puente: la traza de la búsqueda es una refutación de Frege -/

theorem cotaFrege_hoja (N : ℕ) : 1 + 10 * (N + 1) * (2 * N + 1) ≤ cotaFrege N := by
  unfold cotaFrege; omega

theorem cotaFrege_rama (N : ℕ) : 22 * N + 164 ≤ cotaFrege N := by
  unfold cotaFrege; omega

/-- **El puente.** Debajo de todo nodo muerto hay una prueba de Frege, desde las cláusulas, de `ℓ₀ → ⋯ → ⊥` con los
literales del nodo. Su tamaño es a lo sumo la suma de `costoFrege N det c` sobre los nodos que visita la búsqueda. -/
theorem refuta_debajo_frege {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N)
    {det : List Bool → Bool} {c : List Bool → ℕ} (hcert : CertificaFrege F N det c) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = N → ¬ Vivo (solCNF F) k p →
      DerivableInSize (hipFrege F) (imps (litsFrege p) ⊥) (peso (solCNF F) det (costoFrege N det c) k p)
  | 0, p, hl, hm => by
    by_cases hd : det p = true
    · simpa [peso, costoFrege, hd] using hcert p (by omega) hd
    · have hsol : solCNF F p = false := by
        cases h : solCNF F p
        · rfl
        · exact absurd ((vivo_cero _ p).mpr h) hm
      obtain ⟨h1, h2⟩ := clFalsa_spec (det_de_completa hvar (by omega) hsol)
      have hh : DerivableInSize (hipFrege F) (Clause.toFormula (clFalsa F p)) 1 :=
        DerivableInSize.hyp (List.mem_map_of_mem h1)
      refine (imps_de_clausula (fun σ hs => eval_falsificada hs h2) hh).mono ?_
      have hp : p.length = N := by omega
      simp only [peso, costoFrege, hd, Bool.false_eq_true, ite_false, hp]
      exact cotaFrege_hoja N
  | k + 1, p, hl, hm => by
    by_cases hd : det p = true
    · simpa [peso, costoFrege, hd] using hcert p (by omega) hd
    · have hb : ∀ b, ¬ Vivo (solCNF F) k (p ++ [b]) := fun b h =>
        hm ((vivo_succ _ k p).mpr (by cases b <;> simp [h]))
      have ha : (buscar (solCNF F) det k (p ++ [false])).1 = false := by
        cases h : (buscar (solCNF F) det k (p ++ [false])).1
        · rfl
        · exact absurd (buscar_vivo _ _ k _ h) (hb false)
      have h₀ := refuta_debajo_frege hvar hcert k (p ++ [false]) (by simp; omega) (hb false)
      have h₁ := refuta_debajo_frege hvar hcert k (p ++ [true]) (by simp; omega) (hb true)
      rw [litsFrege_snoc] at h₀ h₁
      simp only [litFrege, Bool.false_eq_true, ite_false, ite_true] at h₀ h₁
      refine (paso_frege (litsFrege p) (var p.length) h₀ h₁).mono ?_
      have := cotaFrege_rama N
      simp only [peso, costoFrege, hd, ha, Bool.false_eq_true, ite_false, length_litsFrege]
      omega

/-- **La traza de la búsqueda es una refutación de Frege.** Si `F` no tiene solución y `det` está certificado por
Frege con tamaño `c`, hay una prueba de `⊥` desde las cláusulas de `F` de a lo sumo `peso … (costoFrege N det c) N []`
líneas. -/
theorem refutacion_traza_frege {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N)
    (hF : ¬ CNF.Satisfiable (F : CNF ℕ)) {det : List Bool → Bool} {c : List Bool → ℕ}
    (hcert : CertificaFrege F N det c) :
    DerivableInSize (hipFrege F) ⊥ (peso (solCNF F) det (costoFrege N det c) N []) := by
  simpa [litsFrege] using refuta_debajo_frege hvar hcert N [] (by simp) (raiz_muerta hF N)

/-- **Con pruebas de a lo sumo `K` líneas**: la refutación tiene a lo sumo `nodos · max K (cotaFrege N)` líneas. -/
theorem refutacion_traza_frege_nodos {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N)
    (hF : ¬ CNF.Satisfiable (F : CNF ℕ)) {det : List Bool → Bool} {c : List Bool → ℕ} {K : ℕ}
    (hK : ∀ p, c p ≤ K) (hcert : CertificaFrege F N det c) :
    DerivableInSize (hipFrege F) ⊥ (nodos (solCNF F) det N [] * max K (cotaFrege N)) := by
  refine (refutacion_traza_frege hvar hF hcert).mono (peso_le _ _ _ (fun p => ?_) N [])
  unfold costoFrege
  split
  · exact (hK p).trans (le_max_left _ _)
  · exact le_max_right _ _

/-! ## Un detector certificado es sano -/

/-- **Un detector certificado por Frege es sano**: por la corrección de Frege, `ℓ₀ → ⋯ → ⊥` es verdadera en toda
asignación que satisface `F`, y es falsa en toda asignación que sigue a `p`. -/
theorem certificaFrege_sanoN {F : List Clausula} {N : ℕ} {det : List Bool → Bool} {c : List Bool → ℕ}
    (h : CertificaFrege F N det c) : SanoN (solCNF F) det N := by
  rintro p hp hd ⟨q, -, hs⟩
  obtain ⟨L, hL, hmem, -⟩ := h p hp hd
  have hσ := eval_de_solCNF hs
  have hΓ : ∀ γ ∈ hipFrege F, γ.eval (fun i => (p ++ q).getD i false) = true := by
    intro γ hγ
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hγ
    rw [Clause.eval_toFormula]
    exact List.all_eq_true.1 hσ c hc
  have hseg : Sigue (fun i => (p ++ q).getD i false) p := fun i hi => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  have := hL.eval hΓ _ hmem
  rw [eval_imps_bot, List.any_eq_true] at this
  obtain ⟨φ, hφ, hne⟩ := this
  rw [eval_litsFrege hseg φ hφ] at hne
  exact absurd hne (by decide)

/-- Un tamaño mayor también certifica. -/
theorem certificaFrege_mono {F : List Clausula} {N : ℕ} {det : List Bool → Bool} {c c' : List Bool → ℕ}
    (h : CertificaFrege F N det c) (hc : ∀ p, c p ≤ c' p) : CertificaFrege F N det c' :=
  fun p hp hd => (h p hp hd).mono (hc p)

/-! ## Casos particulares: los peldaños anteriores -/

/-- **`detCNF` está certificado por Frege** con pruebas de `1 + 10 (N+1)(2N+1)` líneas: la cláusula falsa, como
hipótesis, debilitada a `ℓ₀ → ⋯ → ⊥`. -/
theorem certificaFrege_detCNF (F : List Clausula) (N : ℕ) :
    CertificaFrege F N (detCNF F) (fun _ => 1 + 10 * (N + 1) * (2 * N + 1)) := by
  intro p hp hd
  obtain ⟨h1, h2⟩ := clFalsa_spec hd
  refine (imps_de_clausula (fun σ hs => eval_falsificada hs h2)
    (DerivableInSize.hyp (Γ := hipFrege F) (List.mem_map_of_mem h1))).mono ?_
  have : 10 * (p.length + 1) * (2 * p.length + 1) ≤ 10 * (N + 1) * (2 * N + 1) := by gcongr
  change _ ≤ 1 + 10 * (N + 1) * (2 * N + 1)
  omega

/-- **Todo detector certificado por resolución está certificado por Frege**, con la simulación de cslib-frontier
(`CNF.IsProof.frege`, `stepBound` líneas por línea de resolución, con el ancho acotado por `2 ·` las variables de
`F`) más el debilitamiento de la cláusula a `ℓ₀ → ⋯ → ⊥`. -/
theorem certificaFrege_de_res {F : List Clausula} {N : ℕ} {det : List Bool → Bool} {c : List Bool → ℕ}
    (h : CertificaRes F N det c) :
    CertificaFrege F N det
      (fun p => stepBound (2 * (CNF.vars (F : CNF ℕ)).toFinset.card) * c p + 10 * (N + 1) * (2 * N + 1)) := by
  intro p hp hd
  obtain ⟨C, ls, hpr, hC, hl, hf⟩ := h p hp hd
  obtain ⟨L, hL, hmem, hlen⟩ := hpr.frege (fun d hd => hpr.width_le hd)
  have h1 : DerivableInSize (hipFrege F) (Clause.toFormula C)
      (stepBound (2 * (CNF.vars (F : CNF ℕ)).toFinset.card) * c p) :=
    ⟨L, hL, hmem C hC, hlen.trans (Nat.mul_le_mul_left _ hl)⟩
  refine (imps_de_clausula hf h1).mono ?_
  have : 10 * (p.length + 1) * (2 * p.length + 1) ≤ 10 * (N + 1) * (2 * N + 1) := by gcongr
  change _ ≤ stepBound (2 * (CNF.vars (F : CNF ℕ)).toFinset.card) * c p + 10 * (N + 1) * (2 * N + 1)
  omega

/-- Con las variables de `F` debajo de `N`, `F` tiene a lo sumo `N` variables. -/
theorem card_vars_le {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N) :
    (CNF.vars (F : CNF ℕ)).toFinset.card ≤ N := by
  have hsub : (CNF.vars (F : CNF ℕ)).toFinset ⊆ Finset.range N := by
    intro v hv
    simp only [CNF.vars, List.mem_toFinset, List.mem_map, List.mem_flatten] at hv
    obtain ⟨l, ⟨c, hc, hl⟩, rfl⟩ := hv
    exact Finset.mem_range.2 (hvar c hc l hl)
  simpa using Finset.card_le_card hsub

/-- **Resolución, con costo polinomial en `N`**: `stepBound (2N) · c p + 10 (N+1)(2N+1)`. `stepBound (2N)` es
cuadrático en `N`. -/
theorem certificaFrege_de_res_N {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N)
    {det : List Bool → Bool} {c : List Bool → ℕ} (h : CertificaRes F N det c) :
    CertificaFrege F N det (fun p => stepBound (2 * N) * c p + 10 * (N + 1) * (2 * N + 1)) :=
  certificaFrege_mono (certificaFrege_de_res h) fun p =>
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (stepBound_mono (by have := card_vars_le hvar; omega))) _

/-! ## El corolario condicional -/

/-- **Una familia difícil para Frege.** Las fórmulas `φ n` tienen sus variables debajo de `N n`, no tienen solución, y
ninguna cota polinomial `K · (N n + 1)^e` alcanza para refutarlas todas en Frege.

**Es un problema abierto si existe una familia así.** No se conoce ninguna cota inferior superpolinomial para Frege,
y no conocemos ninguna familia que cumpla esta definición. El palomar no la cumple (Buss 1987, de memoria). -/
def ConFregeDificil (φ : ℕ → List Clausula) (N : ℕ → ℕ) : Prop :=
  (∀ n, ∀ c ∈ φ n, ∀ l ∈ c, l.1 < N n) ∧ (∀ n, ¬ CNF.Satisfiable (φ n : CNF ℕ)) ∧
    ∀ K e : ℕ, ∃ n, ¬ DerivableInSize (hipFrege (φ n)) ⊥ (K * (N n + 1) ^ e)

theorem cotaFrege_le (N : ℕ) : cotaFrege N ≤ 210 * (N + 1) ^ 2 := by
  unfold cotaFrege; nlinarith

/-- **Condicional: ningún detector certificado por Frege con pruebas de tamaño polinomial tiene demora logarítmica
sobre una familia difícil para Frege.** Si `ConFregeDificil φ N`, para todos `a`, `b`, `e` y `K` hay un `n` tal que
ningún detector certificado por Frege con pruebas de a lo sumo `K · (N n + 1)^e` líneas tiene demora
`a · log₂(N n + 1) + b` sobre `φ n`.

La hipótesis es un problema abierto: no conocemos ninguna familia que la cumpla. El teorema dice que la contradicción
para este peldaño se reduce exactamente a una cota inferior para Frege. -/
theorem frege_sin_demora_log {φ : ℕ → List Clausula} {N : ℕ → ℕ} (hφ : ConFregeDificil φ N) (a b e K : ℕ) :
    ∃ n, ∀ (det : List Bool → Bool) (c : List Bool → ℕ),
      CertificaFrege (φ n) (N n) det c → (∀ p, c p ≤ K * (N n + 1) ^ e) →
      ¬ DemoraN (solCNF (φ n)) det (N n) (a * Nat.log 2 (N n + 1) + b) := by
  obtain ⟨hvar, hunsat, hdif⟩ := hφ
  obtain ⟨n, hn⟩ := hdif (2 ^ (b + 1) * (K + 210)) (a + e + 3)
  refine ⟨n, fun det c hcert hc hd => hn ?_⟩
  set M := N n with hMdef
  have hup := nodos_le (k := M) (p := []) (certificaFrege_sanoN hcert) hd (by simp)
  have href := refutacion_traza_frege_nodos (hvar n) (hunsat n) hc hcert
  refine href.mono ?_
  have hlog : 2 ^ (a * Nat.log 2 (M + 1) + b + 1) ≤ 2 ^ (b + 1) * (M + 1) ^ a := by
    rw [show a * Nat.log 2 (M + 1) + b + 1 = a * Nat.log 2 (M + 1) + (b + 1) by ring, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (dos_pow_mul_log_le a (M + 1) (by omega))
  have hX : 1 ≤ (M + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have hY : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hmax : max (K * (M + 1) ^ e) (cotaFrege M) ≤ (K + 210) * (M + 1) ^ (e + 2) := by
    rw [pow_add]
    have h1 : (M + 1) ^ 2 ≤ (M + 1) ^ e * (M + 1) ^ 2 := Nat.le_mul_of_pos_left _ hX
    have h2 : (M + 1) ^ e ≤ (M + 1) ^ e * (M + 1) ^ 2 := Nat.le_mul_of_pos_right _ hY
    refine max_le ?_ ((cotaFrege_le M).trans ?_)
    · calc K * (M + 1) ^ e ≤ K * ((M + 1) ^ e * (M + 1) ^ 2) := Nat.mul_le_mul_left _ h2
        _ ≤ (K + 210) * ((M + 1) ^ e * (M + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
    · calc 210 * (M + 1) ^ 2 ≤ 210 * ((M + 1) ^ e * (M + 1) ^ 2) := Nat.mul_le_mul_left _ h1
        _ ≤ (K + 210) * ((M + 1) ^ e * (M + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
  calc nodos (solCNF (φ n)) det M [] * max (K * (M + 1) ^ e) (cotaFrege M)
      ≤ ((M + 1) * (2 ^ (b + 1) * (M + 1) ^ a)) * ((K + 210) * (M + 1) ^ (e + 2)) := by
        refine Nat.mul_le_mul ?_ hmax
        exact hup.trans (Nat.mul_le_mul_left _ hlog)
    _ = 2 ^ (b + 1) * (K + 210) * (M + 1) ^ (a + e + 3) := by ring

/-- **Caso particular: resolución.** Con la misma hipótesis, tampoco los detectores de `CertificaRes` con derivaciones
de tamaño polinomial. (Para resolución la cota ya es incondicional sobre el palomar: `res_sin_demora_log`.) -/
theorem res_sin_demora_log_de_frege {φ : ℕ → List Clausula} {N : ℕ → ℕ} (hφ : ConFregeDificil φ N)
    (a b e K : ℕ) :
    ∃ n, ∀ (det : List Bool → Bool) (c : List Bool → ℕ),
      CertificaRes (φ n) (N n) det c → (∀ p, c p ≤ K * (N n + 1) ^ e) →
      ¬ DemoraN (solCNF (φ n)) det (N n) (a * Nat.log 2 (N n + 1) + b) := by
  obtain ⟨n, hn⟩ := frege_sin_demora_log hφ a b (e + 2) (3400 * (K + 1))
  refine ⟨n, fun det c hcert hc => hn det _ (certificaFrege_de_res_N (hφ.1 n) hcert) fun p => ?_⟩
  set M := N n
  have hs : stepBound (2 * M) ≤ 3400 * (M + 1) ^ 2 := by unfold stepBound; nlinarith
  have hX : 1 ≤ (M + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have hY : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h10 : 10 * (M + 1) * (2 * M + 1) ≤ 3400 * (M + 1) ^ 2 := by nlinarith
  have hcp := hc p
  calc stepBound (2 * M) * c p + 10 * (M + 1) * (2 * M + 1)
      ≤ 3400 * (M + 1) ^ 2 * (K * (M + 1) ^ e) + 3400 * (M + 1) ^ 2 * (M + 1) ^ e := by
        exact Nat.add_le_add (Nat.mul_le_mul hs hcp) (h10.trans (Nat.le_mul_of_pos_right _ hX))
    _ = 3400 * (K + 1) * (M + 1) ^ (e + 2) := by ring

/-! ## Controles -/

/-- `contra3` (`x3 ∧ ¬x3`) no tiene solución. -/
theorem contra3_insat : ¬ CNF.Satisfiable (contra3 : CNF ℕ) := by
  rintro ⟨σ, h⟩
  cases hσ : σ 3 <;> simp [contra3, CNF.eval, Clause.eval, Literal.eval, hσ] at h

/-- **Control: la hipótesis del puente se cumple.** `detCNF` está certificado por Frege, y sobre `contra3`
`refutacion_traza_frege` da una refutación de Frege de tamaño a lo sumo el peso de la búsqueda. -/
example : DerivableInSize (hipFrege contra3) ⊥
    (peso (solCNF contra3) (detCNF contra3) (costoFrege 4 (detCNF contra3) (fun _ => 1 + 10 * (4 + 1) * (2 * 4 + 1)))
      4 []) :=
  refutacion_traza_frege (by simp [contra3]) contra3_insat (certificaFrege_detCNF _ _)

/-- La hipótesis también se cumple por la vía de resolución: `certificaRes_detCNF` y la simulación. -/
example (F : List Clausula) (N : ℕ) (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N) :
    CertificaFrege F N (detCNF F) (fun _ => stepBound (2 * N) * 1 + 10 * (N + 1) * (2 * N + 1)) :=
  certificaFrege_de_res_N hvar (certificaRes_detCNF F N)

/-- **`CertificaFrege` no es trivial (1)**: no certifica un detector que no es sano. En `x0`, el detector que siempre
dispara no está certificado con ningún tamaño, porque `[true]` es solución. -/
example (c : List Bool → ℕ) : ¬ CertificaFrege [[(0, true)]] 1 (fun _ => true) c := by
  intro h
  exact certificaFrege_sanoN h [] (by simp) rfl ⟨[true], rfl, by decide⟩

/-- **`CertificaFrege` no es trivial (2)**: en la raíz de `contra3`, ninguna prueba de `0` líneas sirve. -/
example {det : List Bool → Bool} (hd : det [] = true) : ¬ CertificaFrege contra3 4 det (fun _ => 0) := by
  intro h
  obtain ⟨L, -, hmem, hlen⟩ := h [] (by simp) hd
  have : L = [] := List.eq_nil_of_length_eq_zero (by simp only at hlen; omega)
  simp [this] at hmem

/-- **La completitud para CNF** (cslib-frontier, vía la simulación de resolución): toda fórmula sin solución tiene
alguna refutación de Frege. La versión de `ConFregeDificil` sin «polinomial» («no hay refutación») es falsa. -/
theorem refutacion_existe {F : List Clausula} (hF : ¬ CNF.Satisfiable (F : CNF ℕ)) :
    ∃ s, DerivableInSize (hipFrege F) ⊥ s := by
  obtain ⟨L, hL, hbot⟩ := CNF.exists_frege_refutation_iff_not_satisfiable.2 hF
  exact ⟨L.length, L, hL, hbot, le_rfl⟩

/-- **`ConFregeDificil` no es trivialmente cierta**: falla en la familia constante `contra3`, que tiene una refutación
de tamaño fijo. -/
example : ¬ ConFregeDificil (fun _ => contra3) (fun _ => 4) := by
  rintro ⟨-, -, h⟩
  obtain ⟨s, hs⟩ := refutacion_existe contra3_insat
  obtain ⟨n, hn⟩ := h s 0
  exact hn (by simpa using hs)

/-- **Las demás premisas del corolario se cumplen**: `detCNF` está certificado con tamaño `21 (N+1)²`, de la forma
`K (N+1)^e`. Con una familia difícil, el corolario se aplica a `detCNF`. (La premisa `ConFregeDificil` es el problema
abierto.) -/
theorem certificaFrege_detCNF_pol (F : List Clausula) (N : ℕ) :
    CertificaFrege F N (detCNF F) (fun _ => 21 * (N + 1) ^ 2) :=
  certificaFrege_mono (certificaFrege_detCNF F N) fun _ => by nlinarith

example {φ : ℕ → List Clausula} {N : ℕ → ℕ} (hφ : ConFregeDificil φ N) (a b : ℕ) :
    ∃ n, ¬ DemoraN (solCNF (φ n)) (detCNF (φ n)) (N n) (a * Nat.log 2 (N n + 1) + b) := by
  obtain ⟨n, hn⟩ := frege_sin_demora_log hφ a b 2 21
  exact ⟨n, hn _ _ (certificaFrege_detCNF_pol _ _) fun _ => le_rfl⟩

/-- `DemoraN` sola se cumple: el detector que siempre dispara tiene demora `0`. La que pesa en el corolario es la
conjunción con el certificado de tamaño polinomial. -/
example (sol : List Bool → Bool) (N : ℕ) : DemoraN sol (fun _ => true) N 0 := fun _ _ _ _ _ => rfl

/- Mutantes probados fuera del repositorio (todos rompen la compilación, como debe ser):
1. `litFrege` con los signos invertidos: rompen `eval_litFrege`, `negFormula_eq` y lo que depende de ellos.
2. `cotaFrege` sin el término `22 N`: rompe `cotaFrege_rama` (el paso de la rama no cabe).
3. `tercero` con `149` líneas en vez de `150`: la deducción no cabe.
4. `paso_frege` con `21 |P|` en vez de `22 |P|`: la cuenta no cierra.
5. Costo `0` en los nodos donde `det` no dispara (`costoFrege`): rompe `refuta_debajo_frege` (hoja y rama).
6. `ConFregeDificil` sin pedir que las fórmulas no tengan solución: rompe `frege_sin_demora_log` (la raíz no está
   muerta).
-/

end Sagitta.Map.Tiempo.DetectorFrege
