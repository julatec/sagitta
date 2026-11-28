import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic
import Sagitta.Map.Borde.Tricotomia

/-!
# El regreso a lo finito: quitar el `halt` y cortar con un reloj

La pregunta de José (24 nov 2026): si una máquina que se detiene es una traza infinita que termina
llena de `halt`, ¿cómo se vuelve a las máquinas finitas? ¿«Quitando el `halt` al final»? Este archivo formaliza los
dos primeros mecanismos de regreso, cada uno con su precio.

## El modelo

Una traza es una sucesión `x : ℕ → α` sobre un alfabeto discreto `α`, con un símbolo distinguido `h : α` que hace de
`halt`. Para las máquinas de verdad, `α = Option σ` y `h = none` (ver `Sagitta/Map/Continuo/MemoriaPeriodica.lean`); para
el modelo de juguete de `Tricotomia.lean`, `α = Bool` y `h = true`. Nada aquí pide que el `halt` sea absorbente: los
resultados valen para toda traza, y los testigos que se construyen sí lo son (`Absorbente`).

## Lo que se prueba

**1. Quitar el `halt`** (exacto, pero solo donde se para):
* (i) `para_abierto`: el conjunto `Para h` de las trazas que en algún momento muestran `h` es abierto. Con `α = Bool`
  es `parar_abierto` de `Tricotomia.lean` (`para_bool`).
* (ii) `largo h x` es el primer instante con `h` (con `Nat.find`), y `regreso h x` es la corrida finita antes de él.
  `largo_localmente_constante` y `regreso_localmente_constante`: en cada traza que para, los dos son constantes en un
  vecindario (el cilindro de los primeros `largo + 1` símbolos). `largo_continuoEn`: el largo es continuo en el
  abierto `Para h`, con valores en `ℕ` discreto.
* (iii) **No se extiende.** `paran_lejos`: en todo vecindario de una traza que no para hay trazas que paran (y son
  absorbentes) con largo tan grande como se quiera. `no_se_extiende`: ninguna función a `ℕ` continua en una traza
  que no para coincide con `largo` en las trazas que paran de un vecindario; `no_se_extiende_regreso`: lo mismo para
  la corrida, con cualquier función localmente constante a `List α`.

**2. El reloj** (siempre vuelve, pero puede equivocarse):
* `largoHasta t x`: el primer `halt` antes de `t`, o `t`; `reloj t x`: la corrida cortada ahí.
* `reloj_local` y `reloj_localmente_constante`: el corte depende de los primeros `t` símbolos y es localmente
  constante en **todas** partes (`reloj_continuo` para el largo).
* `reloj_eq_regreso`: si la traza para a más tardar en `t`, el corte es el regreso exacto.
  `reloj_puede_fallar`: para todo `t` hay una traza que para (en `t + 1`) y donde el corte no es el regreso.
* **El corte seguro.** `seguro t x`: si paró antes de `t`, la salida de la corrida; si no, una respuesta de respaldo.
  `seguro_acierta`: si la máquina acierta cuando para y el respaldo acierta, el corte seguro acierta para **todo**
  `t`. `seguro_localmente_constante`: y es una función continua de la traza.

## La lectura

Volver es fácil: en el abierto de las que paran, quitar el `halt` es continuo y localmente constante. Lo difícil es
saber **si** se puede volver: en el borde de ese abierto (las que no paran), el regreso explota, y eso es la parada.
El reloj cambia el problema: siempre vuelve y es continuo, pero acierta solo en lo que paró a tiempo; la complejidad
es dónde cortar. Con un respaldo correcto (para SAT, la fuerza bruta en `2ⁿ`), cortar nunca es un error: resolver
SAT nunca es indecidible. Lo indecidible es saber cosas de la máquina (Rice), no de la entrada.

## Lo que no se prueba

* Que el respaldo exista es una hipótesis (`hb`): no se modela la fuerza bruta ni su costo.
* Los mecanismos 3 (compacidad: `Sagitta/Map/Continuo/CompacidadCircuitos.lean`) y 4 (comprimir la familia: P/poly contra
  P) no están aquí; el 3 ya está probado en su archivo y el 4 es la pregunta abierta.
* La topología de la parada es conocida (el conjunto de parada es Σ⁰₁, abierto en el espacio de Baire); lo propio es
  la formalización y la lectura.
-/

open Filter Topology Set

set_option linter.unusedSectionVars false

namespace Sagitta.Map.Continuo.Regreso

variable {α : Type*} [TopologicalSpace α] [DiscreteTopology α] (h : α)

/-! ## 1. Quitar el `halt` -/

/-- Las trazas que paran: en algún momento muestran `h`. -/
def Para : Set (ℕ → α) := {x | ∃ n, x n = h}

/-- El `halt` es absorbente: una vez que aparece, se queda. -/
def Absorbente (x : ℕ → α) : Prop := ∀ n, x n = h → x (n + 1) = h

open Classical in
/-- El largo de la corrida: el primer instante con `h` (y `0` si nunca aparece; ese valor no se usa). -/
noncomputable def largo (x : ℕ → α) : ℕ := if hx : ∃ n, x n = h then Nat.find hx else 0

/-- La corrida finita: lo que la traza mostró antes del primer `halt`. -/
noncomputable def regreso (x : ℕ → α) : List α := (List.range (largo h x)).map x

variable {h}

theorem largo_spec {x : ℕ → α} (hx : x ∈ Para h) :
    x (largo h x) = h ∧ ∀ k < largo h x, x k ≠ h := by
  classical
  have hx' : ∃ n, x n = h := hx
  have e : largo h x = Nat.find hx' := by simp [largo, hx']
  rw [e]
  exact ⟨Nat.find_spec hx', fun k hk => Nat.find_min hx' hk⟩

theorem largo_eq_of_spec {x : ℕ → α} {L : ℕ} (hL : x L = h) (hmin : ∀ k < L, x k ≠ h) : largo h x = L := by
  classical
  have hx : ∃ n, x n = h := ⟨L, hL⟩
  have e : largo h x = Nat.find hx := by simp [largo, hx]
  rw [e, Nat.find_eq_iff]
  exact ⟨hL, fun k hk => hmin k hk⟩

theorem largo_le {x : ℕ → α} {n : ℕ} (hn : x n = h) : largo h x ≤ n := by
  classical
  have hx : ∃ n, x n = h := ⟨n, hn⟩
  have e : largo h x = Nat.find hx := by simp [largo, hx]
  rw [e]
  exact Nat.find_min' hx hn

theorem length_regreso (x : ℕ → α) : (regreso h x).length = largo h x := by
  simp [regreso]

/-- (i) **Parar es abierto.** -/
theorem para_abierto : IsOpen (Para h) := by
  have : Para h = ⋃ n, (fun x : ℕ → α => x n) ⁻¹' {h} := by ext x; simp [Para]
  rw [this]
  exact isOpen_iUnion fun n => (isOpen_discrete {h}).preimage (continuous_apply n)

omit [DiscreteTopology α] in
/-- Con `α = Bool` y `h = true`, `Para` es el conjunto de `parar_abierto` de `Tricotomia.lean`. -/
theorem para_bool : Para true = {d : ℕ → Bool | ∃ n, d n = true} := rfl

theorem para_bool_abierto : IsOpen (Para true : Set (ℕ → Bool)) :=
  Sagitta.Map.Borde.Tricotomia.parar_abierto

/-- Coincidir en los primeros `N` símbolos es un vecindario. -/
theorem cilindro_mem_nhds (x : ℕ → α) (N : ℕ) : ∀ᶠ y in 𝓝 x, ∀ i < N, y i = x i := by
  have : ∀ i ∈ Finset.range N, ∀ᶠ y in 𝓝 x, y i = x i := fun i _ => by
    have ho : IsOpen {y : ℕ → α | y i = x i} :=
      (isOpen_discrete {x i}).preimage (continuous_apply (A := fun _ : ℕ => α) i)
    exact ho.mem_nhds rfl
  filter_upwards [(Finset.range N).eventually_all.2 this] with y hy i hi
  exact hy i (Finset.mem_range.2 hi)

/-- Si `y` coincide con una traza que para en los primeros `largo + 1` símbolos, para en el mismo instante. -/
theorem largo_de_prefijo {x y : ℕ → α} (hx : x ∈ Para h) (hy : ∀ i < largo h x + 1, y i = x i) :
    largo h y = largo h x := by
  obtain ⟨hL, hmin⟩ := largo_spec hx
  apply largo_eq_of_spec
  · rw [hy _ (Nat.lt_succ_self _)]; exact hL
  · intro k hk
    rw [hy k (Nat.lt_succ_of_lt hk)]
    exact hmin k hk

theorem regreso_de_prefijo {x y : ℕ → α} (hx : x ∈ Para h) (hy : ∀ i < largo h x + 1, y i = x i) :
    regreso h y = regreso h x := by
  unfold regreso
  rw [largo_de_prefijo hx hy]
  apply List.map_congr_left
  intro i hi
  exact hy i (Nat.lt_succ_of_lt (List.mem_range.1 hi))

/-- (ii) **El largo es localmente constante** en las trazas que paran. -/
theorem largo_localmente_constante {x : ℕ → α} (hx : x ∈ Para h) :
    ∀ᶠ y in 𝓝 x, largo h y = largo h x := by
  filter_upwards [cilindro_mem_nhds x (largo h x + 1)] with y hy using largo_de_prefijo hx hy

/-- (ii) **La corrida es localmente constante** en las trazas que paran. -/
theorem regreso_localmente_constante {x : ℕ → α} (hx : x ∈ Para h) :
    ∀ᶠ y in 𝓝 x, regreso h y = regreso h x := by
  filter_upwards [cilindro_mem_nhds x (largo h x + 1)] with y hy using regreso_de_prefijo hx hy

theorem largo_continuoEn : ContinuousOn (largo h) (Para h) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  rw [ContinuousAt, nhds_discrete ℕ, tendsto_pure]
  exact largo_localmente_constante hx

/-- `x` hasta `N`, y después `h` para siempre. -/
def cortarEn (h : α) (x : ℕ → α) (N : ℕ) : ℕ → α := fun i => if i < N then x i else h

theorem cortarEn_absorbente {x : ℕ → α} (hx : ∀ i, x i ≠ h) (N : ℕ) : Absorbente h (cortarEn h x N) := by
  intro n hn
  by_cases hnN : n < N
  · exact absurd (by simpa [cortarEn, hnN] using hn) (hx n)
  · simp [cortarEn, show ¬ n + 1 < N by omega]

/-- (iii) **En el borde, el largo explota**: en todo vecindario de una traza que no para hay trazas que paran, con
el `halt` absorbente, y con largo al menos `M`. -/
theorem paran_lejos {x : ℕ → α} (hx : x ∉ Para h) {U : Set (ℕ → α)} (hU : U ∈ 𝓝 x) (M : ℕ) :
    ∃ y ∈ U, y ∈ Para h ∧ Absorbente h y ∧ M ≤ largo h y := by
  have hnunca : ∀ i, x i ≠ h := fun i hi => hx ⟨i, hi⟩
  -- El cilindro de largo `K` dentro de `U`.
  obtain ⟨K, hK⟩ : ∃ K, ∀ y, (∀ i < K, y i = x i) → y ∈ U := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, u, hu, hsub⟩ := hU
    obtain ⟨K, hKb⟩ := hI.bddAbove
    refine ⟨K + 1, fun y hy => hsub fun i hi => ?_⟩
    have hxi : x i ∈ u i := mem_of_mem_nhds (hu i)
    rw [hy i (Nat.lt_succ_of_le (hKb hi))]
    exact hxi
  set N := max K M
  refine ⟨cortarEn h x N, hK _ fun i hi => ?_, ⟨N, by simp [cortarEn]⟩, cortarEn_absorbente hnunca N, ?_⟩
  · have : i < N := lt_of_lt_of_le hi (le_max_left _ _)
    simp [cortarEn, this]
  have : largo h (cortarEn h x N) = N :=
    largo_eq_of_spec (by simp [cortarEn]) fun k hk => by simp [cortarEn, hk, hnunca k]
  rw [this]
  exact le_max_right _ _

/-- (iii) **El regreso no se extiende**: ninguna `F` continua en una traza que no para coincide con el largo en las
trazas que paran de un vecindario. -/
theorem no_se_extiende {x : ℕ → α} (hx : x ∉ Para h) (F : (ℕ → α) → ℕ) (hF : ContinuousAt F x) :
    ¬ ∀ᶠ y in 𝓝 x, y ∈ Para h → F y = largo h y := by
  intro hco
  rw [ContinuousAt, nhds_discrete ℕ, tendsto_pure] at hF
  obtain ⟨y, ⟨hFy, hcy⟩, hy, _, hM⟩ := paran_lejos hx (hF.and hco) (F x + 1)
  have := hcy hy
  omega

/-- (iii) Lo mismo para la corrida: ninguna función localmente constante en `x` la extiende. -/
theorem no_se_extiende_regreso {x : ℕ → α} (hx : x ∉ Para h) (F : (ℕ → α) → List α)
    (hF : ∀ᶠ y in 𝓝 x, F y = F x) : ¬ ∀ᶠ y in 𝓝 x, y ∈ Para h → F y = regreso h y := by
  intro hco
  obtain ⟨y, ⟨hFy, hcy⟩, hy, _, hM⟩ := paran_lejos hx (hF.and hco) ((F x).length + 1)
  have := congrArg List.length (hcy hy)
  rw [hFy, length_regreso] at this
  omega

/-! ## 2. El reloj -/

variable (h) [DecidableEq α]

/-- El primer `halt` antes de `t`, o `t` si no hubo. -/
noncomputable def largoHasta (t : ℕ) (x : ℕ → α) : ℕ :=
  Nat.find (p := fun n => n = t ∨ x n = h) ⟨t, Or.inl rfl⟩

/-- **El reloj**: la corrida cortada en el primer `halt` o en `t`, lo que llegue antes. -/
noncomputable def reloj (t : ℕ) (x : ℕ → α) : List α := (List.range (largoHasta h t x)).map x

variable {h}

theorem largoHasta_spec (t : ℕ) (x : ℕ → α) :
    (largoHasta h t x = t ∨ x (largoHasta h t x) = h) ∧ ∀ k < largoHasta h t x, k ≠ t ∧ x k ≠ h := by
  refine ⟨Nat.find_spec (p := fun n => n = t ∨ x n = h) ⟨t, Or.inl rfl⟩, fun k hk => ?_⟩
  have := Nat.find_min (p := fun n => n = t ∨ x n = h) ⟨t, Or.inl rfl⟩ hk
  simpa only [not_or] using this

theorem largoHasta_le (t : ℕ) (x : ℕ → α) : largoHasta h t x ≤ t :=
  Nat.find_min' (p := fun n => n = t ∨ x n = h) ⟨t, Or.inl rfl⟩ (Or.inl rfl)

theorem largoHasta_eq_of_spec {t : ℕ} {x : ℕ → α} {m : ℕ} (hm : m = t ∨ x m = h)
    (hmin : ∀ k < m, k ≠ t ∧ x k ≠ h) : largoHasta h t x = m := by
  unfold largoHasta
  rw [Nat.find_eq_iff]
  refine ⟨hm, fun k hk => ?_⟩
  rintro (e | e)
  · exact (hmin k hk).1 e
  · exact (hmin k hk).2 e

/-- El reloj solo mira los primeros `t` símbolos. -/
theorem largoHasta_local {t : ℕ} {x y : ℕ → α} (hy : ∀ i < t, y i = x i) :
    largoHasta h t y = largoHasta h t x := by
  obtain ⟨hm, hmin⟩ := largoHasta_spec (h := h) t x
  have hle := largoHasta_le (h := h) t x
  apply largoHasta_eq_of_spec
  · rcases hm with e | e
    · exact Or.inl e
    · rcases Nat.lt_or_ge (largoHasta h t x) t with hl | hl
      · right; rw [hy _ hl]; exact e
      · left; omega
  · intro k hk
    refine ⟨(hmin k hk).1, ?_⟩
    rw [hy k (by omega)]
    exact (hmin k hk).2

theorem reloj_local {t : ℕ} {x y : ℕ → α} (hy : ∀ i < t, y i = x i) : reloj h t y = reloj h t x := by
  unfold reloj
  rw [largoHasta_local hy]
  apply List.map_congr_left
  intro i hi
  exact hy i (lt_of_lt_of_le (List.mem_range.1 hi) (largoHasta_le t x))

/-- **El reloj es localmente constante en todas partes.** -/
theorem reloj_localmente_constante (t : ℕ) (x : ℕ → α) : ∀ᶠ y in 𝓝 x, reloj h t y = reloj h t x := by
  filter_upwards [cilindro_mem_nhds x t] with y hy using reloj_local hy

theorem reloj_continuo (t : ℕ) : Continuous (largoHasta h t) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, nhds_discrete ℕ, tendsto_pure]
  filter_upwards [cilindro_mem_nhds x t] with y hy using largoHasta_local hy

/-- Si la traza para a más tardar en `t`, el reloj marca el mismo largo. -/
theorem largoHasta_eq_largo {t : ℕ} {x : ℕ → α} (hx : x ∈ Para h) (ht : largo h x ≤ t) :
    largoHasta h t x = largo h x := by
  obtain ⟨hL, hmin⟩ := largo_spec hx
  exact largoHasta_eq_of_spec (Or.inr hL) fun k hk => ⟨by omega, hmin k hk⟩

/-- **El reloj acierta en lo que paró a tiempo.** -/
theorem reloj_eq_regreso {t : ℕ} {x : ℕ → α} (hx : x ∈ Para h) (ht : largo h x ≤ t) :
    reloj h t x = regreso h x := by
  simp [reloj, regreso, largoHasta_eq_largo hx ht]

/-- Si el reloj marcó menos que `t`, la traza paró ahí. -/
theorem para_de_largoHasta_lt {t : ℕ} {x : ℕ → α} (hlt : largoHasta h t x < t) :
    x ∈ Para h ∧ largo h x = largoHasta h t x := by
  obtain ⟨hm, hmin⟩ := largoHasta_spec (h := h) t x
  have e : x (largoHasta h t x) = h := hm.resolve_left (Nat.ne_of_lt hlt)
  exact ⟨⟨_, e⟩, largo_eq_of_spec e fun k hk => (hmin k hk).2⟩

/-- **El reloj puede equivocarse**: si hay un símbolo `a ≠ h`, para todo `t` hay una traza que para (en `t + 1`, con
`halt` absorbente) y donde el corte no es la corrida. -/
theorem reloj_puede_fallar {a : α} (ha : a ≠ h) (t : ℕ) :
    ∃ x, x ∈ Para h ∧ Absorbente h x ∧ largo h x = t + 1 ∧ reloj h t x ≠ regreso h x := by
  let x := cortarEn h (fun _ => a) (t + 1)
  have hL : largo h x = t + 1 :=
    largo_eq_of_spec (by simp [x, cortarEn]) fun k hk => by simp [x, cortarEn, hk, ha]
  refine ⟨x, ⟨t + 1, by simp [x, cortarEn]⟩, cortarEn_absorbente (fun _ => ha) _, hL, fun e => ?_⟩
  have := congrArg List.length e
  rw [length_regreso, hL] at this
  have hle := largoHasta_le (h := h) t x
  simp only [reloj, List.length_map, List.length_range] at this
  omega

/-! ### El corte seguro -/

variable {β : Type*}

/-- **El corte seguro**: correr con reloj `t`; si paró, leer la salida; si no, usar el respaldo `b`. -/
noncomputable def seguro (salida : List α → β) (b : β) (t : ℕ) (x : ℕ → α) : β :=
  if largoHasta h t x < t then salida (reloj h t x) else b

/-- **El corte seguro acierta para todo `t`**: si la máquina acierta cuando para y el respaldo acierta, cortar en
cualquier tiempo da la respuesta correcta. -/
theorem seguro_acierta (salida : List α → β) {r b : β} {x : ℕ → α}
    (hm : x ∈ Para h → salida (regreso h x) = r) (hb : b = r) (t : ℕ) : seguro (h := h) salida b t x = r := by
  unfold seguro
  split_ifs with hlt
  · obtain ⟨hx, hl⟩ := para_de_largoHasta_lt hlt
    rw [reloj_eq_regreso hx (by omega)]
    exact hm hx
  · exact hb

theorem seguro_localmente_constante (salida : List α → β) (b : β) (t : ℕ) (x : ℕ → α) :
    ∀ᶠ y in 𝓝 x, seguro (h := h) salida b t y = seguro (h := h) salida b t x := by
  filter_upwards [cilindro_mem_nhds x t] with y hy
  simp [seguro, largoHasta_local hy, reloj_local hy]

/-! ## Controles -/

section Controles

/-- Una traza en `Bool` que para en el paso 3: `false, false, false, true, true, …`. -/
def tres : ℕ → Bool := fun i => decide (3 ≤ i)

example : tres ∈ Para true := ⟨3, rfl⟩

theorem tres_largo : largo true tres = 3 :=
  largo_eq_of_spec rfl fun k hk => by simp [tres]; omega

example : regreso true tres = [false, false, false] := by
  simp [regreso, tres_largo, List.range_succ, tres]

example : Absorbente true tres := fun n _ => by simp [tres] at *; omega

/-- Con reloj 5 acierta; con reloj 2 corta antes. -/
example : reloj true 5 tres = regreso true tres :=
  reloj_eq_regreso ⟨3, rfl⟩ (by rw [tres_largo]; omega)

example : reloj true 2 tres = [false, false] := by
  have : largoHasta true 2 tres = 2 :=
    largoHasta_eq_of_spec (Or.inl rfl) fun k hk => ⟨by omega, by simp [tres]; omega⟩
  simp [reloj, this, List.range_succ, tres]

/-- La traza que nunca para no está en `Para`, y cerca de ella hay de todo. -/
example : (fun _ => false : ℕ → Bool) ∉ Para true := by simp [Para]

/- Mutante (probado en /tmp/claude-noche/MutReg1.lean, 25 nov 2026): con `reloj_eq_regreso` pidiendo solo
`largo h x ≤ t + 1` en vez de `≤ t`, la prueba falla (`omega` no cierra el caso `largo = t + 1`), como debe:
`reloj_puede_fallar` es justamente ese caso. -/

end Controles

end Sagitta.Map.Continuo.Regreso
