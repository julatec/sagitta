import Sagitta.Map.Informacion.Polimorfismos
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Set.Finite.Range
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# El álgebra decide y no deja medio: la dicotomía booleana

El paso «el álgebra decide y no deja medio» de las notas del proyecto («El fractal de SAT»), sección «Qué principio permite la
dimensión fraccionaria». José (25 nov 2026) conjeturó una **tricotomía**: el álgebra presente da colapso (dimensión 0,
lo fácil) o completitud (dimensión 1), y su ausencia deja el fractal (los intermedios). En el caso booleano el
teorema de Schaefer (1978) es la instancia limpia, y este archivo la arma sobre `Polimorfismos.lean` (importado, no
editado).

**La honestidad primero.** «Dimensión 0 o 1» es una *lectura*; lo formal es una **dicotomía contra intermedios**:
cada `CSP(Γ)` booleano finito está en P o es NP-completo, y ninguno queda en medio, aunque Ladner diga que en NP en
general sí los hay si P ≠ NP (`FractalSAT.lean`). Lo que decide de qué lado cae es **una sola identidad**: que
`Pol(Γ)` tenga una de seis operaciones. El álgebra presente colapsa; la ausencia de álgebra no deja fractal, deja
completitud. Así que, en los CSP, la tercera rama de la tricotomía está **vacía**, y ese es el contenido.

## Lo que se prueba

1. **`Pol(3-SAT)` en toda aridad** (§ 1, `tresSAT_pol_iff_todas`). Cierra lo que `Polimorfismos.lean` dejó en
   `1 ≤ k ≤ 3`. El argumento del ultrafiltro: `{A : f(1_A) = 1}` contiene a `univ` (`pol_uno`), no a `∅`
   (`pol_cero`), y es cerrado por intersección en la forma `paso_ultrafiltro` (si `A` está y `j ∈ A`, está `{j}` o
   está `A ∖ j`); bajando por el cardinal se llega a un unitario (`existe_unitario`), es decir, un ultrafiltro
   principal, y `de_unitario` da `f = proy j`.
2. **El lado fácil, en una muestra** (§ 3). Instancias de `CSP(Γ)` como listas de restricciones (§ 2).
   * Constantes (`const_decide`): si la constante `b` es polimorfismo, basta evaluar la asignación constante.
   * **Horn, completo** (`decideHorn_correcto`): propagación unitaria desde `∅`, `n + 1` rondas (`prop_fijo`: cada
     ronda que no es fija agrega una variable), y revisar. Correcto en las dos direcciones; su costo declarado es
     `(n + 2)·m` evaluaciones de cláusula (`costoHorn_poly`). El álgebra queda a la vista en `modelo_inter`: los
     modelos son cerrados por intersección (el AND es polimorfismo), por eso hay modelo mínimo y por eso propagar desde
     abajo basta.
   * Dual-Horn (`decideDual_correcto`): el mismo algoritmo sobre los complementos.
   * 2-SAT (mayoría) y afín (minoría `x ⊕ y ⊕ z`, eliminación gaussiana): solo enunciados, dentro de la hipótesis
     `Supuestos.facil`.
3. **El lado completo** (§ 4). Definiciones primitivas positivas (`DefPP`: conjunción de restricciones de `Γ` con
   variables existenciales; las libres pueden repetirse, que hace de igualdad).
   * **La conexión de Galois, probada** en el caso booleano con `Γ` finito: `definible_preserva` (lo definible es
     preservado por `Pol Γ`) y `galois` (lo preservado por `Pol Γ` lo define la definición canónica sobre `Bool^|S|`,
     cuyas soluciones son exactamente los polimorfismos `|S|`-arios). Es `Inv(Pol Γ) = ⟨Γ⟩` (Geiger; Bodnarchuk,
     Kaluzhnin, Kotov y Romov, 1968–1969).
   * **La reducción por gadgets** (`traducir`): reemplazar cada restricción por su definición preserva la
     satisfacibilidad (`traducir_correcto`, con variables libres distintas) y es lineal (`traducir_largo`).
   * Consecuencias: si `Pol Γ` son solo proyecciones, 3-SAT se reduce a `CSP(Γ)` (`tresSAT_se_reduce`); si son
     proyecciones y negaciones, NAE-3-SAT (`naeSAT_se_reduce`).
   * **Corrección del enunciado del paso**: «no tiene ninguno de los seis» **no** basta para definir 3-SAT. Si la
     negación es polimorfismo, ninguna cláusula es definible (`negacion_impide`). Ese caso (el clon `N₂` de Post)
     pasa por NAE-3-SAT, que también es NP-completo.
4. **«No deja medio»** (§ 5). Con lo no probado reunido en `Supuestos` (el lado fácil de 2-SAT y afín; el retículo de
   Post; Cook–Levin para 3-SAT y NAE-3-SAT; que la traducción es polinomial; y P ≠ NP en la forma «lo NP-completo no
   está en P»), con `EnP` y `NPc` como predicados opacos: `dificil` (sin los seis, NP-completo), `dicotomia` (en P y
   no NP-completo, o NP-completo y no en P), `interruptor` (`EnP Γ ↔ TieneUnaDeLasSeis Γ`: la identidad es el
   interruptor) y `sin_intermedios`.

## Contexto: Feder–Vardi

Feder y Vardi (1993–1998) buscaron la clase lógica más grande de NP que todavía pudiera tener dicotomía. MMSNP
(SNP monádico, monótono, sin desigualdades) es CSP hasta equivalencia polinomial (aleatoria en su prueba;
Kun la desaleatorizó en 2013), y cada una de las tres
restricciones funciona como un **axioma que prohíbe lo intermedio**: quitando cualquiera, la clase ya captura todo NP
hasta equivalencia, y con ella los intermedios de Ladner. Conjeturaron la dicotomía para los CSP finitos; la probaron
Bulatov y Zhuk (2017). En la lectura de José: la sintaxis restringida obliga a que el álgebra exista o no, sin grados.

## Antecedentes (de memoria)

Schaefer (1978); Post (1941), el retículo de los clones booleanos; Geiger (1968) y Bodnarchuk–Kaluzhnin–Kotov–Romov
(1969), la conexión de Galois; Jeavons (1998), la lectura por polimorfismos; Feder–Vardi (1998); Bulatov (2017) y
Zhuk (2020).
-/

namespace Sagitta.Map.Borde.DicotomiaBooleana

open Sagitta.Map.Informacion.Polimorfismos

/-! ## 1. `Pol(3-SAT)` en toda aridad: el ultrafiltro principal -/

/-- La indicadora de `A ⊆ Fin k` como tupla booleana. -/
def ind {k : ℕ} (A : Finset (Fin k)) : Fin k → Bool := fun i => decide (i ∈ A)

theorem ind_singleton {k : ℕ} (j : Fin k) : ind {j} = e j := by
  funext i; simp [ind, e]

/-- El paso del ultrafiltro. Si `f (1_A) = 1` y `j ∈ A`, con las filas `1_A, e j, 1_{A ∖ j}` la proyección `j'` que
coincide tiene `j' ∈ A`; o es `j` (y `f (e j) = 1`) o está en `A ∖ j` (y `f (1_{A ∖ j}) = 1`). Es el cierre por
intersección de `{A : f(1_A) = 1}`, en la forma que basta para bajar. -/
theorem paso_ultrafiltro {k : ℕ} (f : (Fin k → Bool) → Bool)
    (hf : ∀ σ : Fin 3 → Bool, Preserva f (clausula σ)) (A : Finset (Fin k)) (hA : f (ind A) = true)
    (j : Fin k) : f (e j) = true ∨ f (ind (A.erase j)) = true := by
  obtain ⟨j', hj'⟩ := filas f hf ![ind A, e j, ind (A.erase j)]
  have h0 : f (ind A) = ind A j' := hj' 0
  have h1 : f (e j) = e j j' := hj' 1
  have h2 : f (ind (A.erase j)) = ind (A.erase j) j' := hj' 2
  rw [hA] at h0
  have hA' : j' ∈ A := by simpa [ind] using h0.symm
  by_cases hjj : j' = j
  · left; rw [h1]; simp [e, hjj]
  · right; rw [h2]; simp [ind, hjj, hA']

/-- Las constantes: un polimorfismo de 3-SAT vale `1` en el `1` y `0` en el `0` (idempotente). -/
theorem pol_uno {k : ℕ} (f : (Fin k → Bool) → Bool) (hf : ∀ σ : Fin 3 → Bool, Preserva f (clausula σ)) :
    f (ind Finset.univ) = true := by
  obtain ⟨j, hj⟩ := filas f hf (fun _ => ind Finset.univ)
  rw [hj 0]; simp [ind]

theorem pol_cero {k : ℕ} (f : (Fin k → Bool) → Bool) (hf : ∀ σ : Fin 3 → Bool, Preserva f (clausula σ)) :
    f (ind ∅) = false := by
  obtain ⟨j, hj⟩ := filas f hf (fun _ => ind ∅)
  rw [hj 0]; simp [ind]

/-- El ultrafiltro es principal: hay una coordenada `j` con `f (e j) = 1`. Se baja desde `univ` (que está) quitando
coordenadas; `∅` no está, así que en algún momento se cae en un unitario. -/
theorem existe_unitario {k : ℕ} (f : (Fin k → Bool) → Bool)
    (hf : ∀ σ : Fin 3 → Bool, Preserva f (clausula σ)) : ∃ j, f (e j) = true := by
  suffices h : ∀ n, ∀ A : Finset (Fin k), A.card = n → f (ind A) = true → ∃ j, f (e j) = true from
    h _ _ rfl (pol_uno f hf)
  intro n
  induction n with
  | zero =>
    intro A hA h
    rw [Finset.card_eq_zero] at hA
    subst hA
    rw [pol_cero f hf] at h
    exact absurd h (by decide)
  | succ n ih =>
    intro A hA h
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    rcases paso_ultrafiltro f hf A h j with h1 | h1
    · exact ⟨j, h1⟩
    · exact ih _ (by rw [Finset.card_erase_of_mem hj]; omega) h1

/-- **`Pol(3-SAT)` son las proyecciones, en toda aridad.** Cierra lo que `Polimorfismos.lean` dejó para
`1 ≤ k ≤ 3`. En aridad `0` no hay ninguno (no hay `j : Fin 0`). -/
theorem tresSAT_pol_iff_todas {k : ℕ} (f : (Fin k → Bool) → Bool) :
    Polimorfismo tresSAT f ↔ ∃ j, f = proy j := by
  constructor
  · intro hf
    have hf' : ∀ σ : Fin 3 → Bool, Preserva f (clausula σ) := fun σ => hf _ ⟨σ, rfl⟩
    obtain ⟨j, hj⟩ := existe_unitario f hf'
    exact ⟨j, de_unitario f hf' j hj⟩
  · rintro ⟨j, rfl⟩; exact proy_polimorfismo _ j

/-! ## 2. Instancias de un CSP booleano -/

/-- Una restricción sobre las variables `V`: una relación del molde `Γ` y su alcance. -/
structure Restriccion (Γ : Relaciones) (V : Type) where
  R : Σ r : ℕ, Relacion r
  mem : R ∈ Γ
  alcance : Fin R.1 → V

/-- `x` cumple la restricción. -/
def Restriccion.Cumple {Γ : Relaciones} {V : Type} (x : V → Bool) (c : Restriccion Γ V) : Prop :=
  c.R.2 (x ∘ c.alcance)

/-- Una instancia de `CSP(Γ)`: una lista de restricciones. -/
abbrev Instancia (Γ : Relaciones) (V : Type) := List (Restriccion Γ V)

/-- La instancia se satisface. -/
def Satisfacible {Γ : Relaciones} {V : Type} (I : Instancia Γ V) : Prop :=
  ∃ x : V → Bool, ∀ c ∈ I, c.Cumple x

/-! ## 3. El lado fácil, en una muestra -/

/-! ### 3a. Las constantes: decidir es mirar una sola asignación -/

/-- La constante `b`, como operación unaria. -/
def const (b : Bool) : (Fin 1 → Bool) → Bool := fun _ => b

/-- Si la constante `b` es polimorfismo de `Γ`, una instancia se satisface si y solo si la satisface la asignación
constante `b`. El algoritmo es evaluar una asignación. -/
theorem const_decide {Γ : Relaciones} {V : Type} (b : Bool) (hb : Polimorfismo Γ (const b))
    (I : Instancia Γ V) : Satisfacible I ↔ ∀ c ∈ I, c.Cumple (fun _ => b) := by
  constructor
  · rintro ⟨x, hx⟩ c hc
    exact hb c.R c.mem (fun _ => x ∘ c.alcance) (fun _ => hx c hc)
  · intro h; exact ⟨_, h⟩

/-! ### 3b. Horn: propagación unitaria con su corrección -/

/-- Una cláusula de Horn sobre `n` variables: `⋀ cuerpo → cabeza`, con cabeza `none` para `⋀ cuerpo → ⊥`. Como
disyunción tiene a lo sumo un literal positivo (la cabeza), así que es una `clausula σ` con `EsHorn σ`. -/
structure ClausulaHorn (n : ℕ) where
  cuerpo : Finset (Fin n)
  cabeza : Option (Fin n)

/-- `S` (las variables en `1`) cumple la cláusula. -/
def ClausulaHorn.cumple {n : ℕ} (c : ClausulaHorn n) (S : Finset (Fin n)) : Bool :=
  !decide (c.cuerpo ⊆ S) ||
    match c.cabeza with
    | none => false
    | some h => decide (h ∈ S)

/-- `S` es modelo de la lista. -/
def ModeloHorn {n : ℕ} (cs : List (ClausulaHorn n)) (S : Finset (Fin n)) : Prop :=
  ∀ c ∈ cs, c.cumple S = true

/-- Un paso de propagación: agregar las cabezas de las cláusulas cuyo cuerpo ya está. -/
def paso {n : ℕ} (cs : List (ClausulaHorn n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ (cs.filterMap fun c => if c.cuerpo ⊆ S then c.cabeza else none).toFinset

theorem sub_paso {n : ℕ} (cs : List (ClausulaHorn n)) (S : Finset (Fin n)) : S ⊆ paso cs S :=
  Finset.subset_union_left

theorem paso_mono {n : ℕ} (cs : List (ClausulaHorn n)) {S T : Finset (Fin n)} (h : S ⊆ T) :
    paso cs S ⊆ paso cs T := by
  intro x hx
  simp only [paso, Finset.mem_union, List.mem_toFinset, List.mem_filterMap] at hx ⊢
  rcases hx with hx | ⟨c, hc, hx⟩
  · exact Or.inl (h hx)
  · right
    refine ⟨c, hc, ?_⟩
    by_cases hb : c.cuerpo ⊆ S
    · simp only [hb, hb.trans h, ↓reduceIte] at hx ⊢; exact hx
    · simp only [hb, ↓reduceIte] at hx; cases hx

/-- La sucesión de propagación desde `∅`. -/
def prop {n : ℕ} (cs : List (ClausulaHorn n)) (i : ℕ) : Finset (Fin n) := (paso cs)^[i] ∅

theorem prop_succ {n : ℕ} (cs : List (ClausulaHorn n)) (i : ℕ) : prop cs (i + 1) = paso cs (prop cs i) :=
  Function.iterate_succ_apply' _ _ _

/-- O la propagación ya se detuvo, o lleva al menos `i` variables puestas. -/
theorem prop_crece {n : ℕ} (cs : List (ClausulaHorn n)) :
    ∀ i, (∃ m ≤ i, paso cs (prop cs m) = prop cs m) ∨ i ≤ (prop cs i).card := by
  intro i
  induction i with
  | zero => right; exact Nat.zero_le _
  | succ i ih =>
    rcases ih with ⟨m, hm, h⟩ | h
    · exact Or.inl ⟨m, by omega, h⟩
    · by_cases hf : paso cs (prop cs i) = prop cs i
      · exact Or.inl ⟨i, by omega, hf⟩
      · right
        rw [prop_succ]
        have hs : prop cs i ⊂ paso cs (prop cs i) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨sub_paso _ _, fun h' => hf h'.symm⟩
        have := Finset.card_lt_card hs
        omega

/-- En `n + 1` pasos la propagación llega a su punto fijo: cada paso que no es fijo agrega una variable, y hay `n`. -/
theorem prop_fijo {n : ℕ} (cs : List (ClausulaHorn n)) : paso cs (prop cs (n + 1)) = prop cs (n + 1) := by
  rcases prop_crece cs (n + 1) with ⟨m, hm, h⟩ | h
  · have : prop cs (n + 1) = prop cs m := by
      unfold prop
      rw [show n + 1 = (n + 1 - m) + m by omega, Function.iterate_add_apply]
      exact Function.iterate_fixed h _
    rw [this]; exact h
  · have := Finset.card_le_univ (prop cs (n + 1))
    simp only [Fintype.card_fin] at this
    omega

/-- El modelo mínimo. -/
def minimo {n : ℕ} (cs : List (ClausulaHorn n)) : Finset (Fin n) := prop cs (n + 1)

/-- **El algoritmo de Horn**: propagar `n + 1` veces desde `∅` y revisar las cláusulas en lo que quedó. -/
def decideHorn {n : ℕ} (cs : List (ClausulaHorn n)) : Bool := cs.all fun c => c.cumple (minimo cs)

/-- Su costo, en evaluaciones de cláusula (cada una es un `⊆` de `Finset`, a lo sumo `n` pertenencias): `n + 1` rondas
de propagación sobre la lista y una de revisión. Es un conteo declarado, no un modelo de máquina. -/
def costoHorn (n m : ℕ) : ℕ := (n + 2) * m

theorem costoHorn_poly (n m : ℕ) : costoHorn n m ≤ (n + m + 2) ^ 2 := by
  unfold costoHorn
  calc (n + 2) * m ≤ (n + m + 2) * (n + m + 2) := Nat.mul_le_mul (by omega) (by omega)
    _ = (n + m + 2) ^ 2 := (sq _).symm

/-- Un modelo es cerrado bajo el paso: si el cuerpo está en `T`, la cabeza también. -/
theorem paso_sub_modelo {n : ℕ} {cs : List (ClausulaHorn n)} {T : Finset (Fin n)} (hT : ModeloHorn cs T) :
    paso cs T ⊆ T := by
  intro x hx
  simp only [paso, Finset.mem_union, List.mem_toFinset, List.mem_filterMap] at hx
  rcases hx with hx | ⟨c, hc, hx⟩
  · exact hx
  · by_cases hb : c.cuerpo ⊆ T
    · simp only [hb, ↓reduceIte] at hx
      have := hT c hc
      simp only [ClausulaHorn.cumple, hb, decide_true, Bool.not_true, Bool.false_or, hx] at this
      simpa using this
    · simp only [hb, ↓reduceIte] at hx; cases hx

/-- Todo modelo contiene al mínimo. -/
theorem minimo_sub {n : ℕ} {cs : List (ClausulaHorn n)} {T : Finset (Fin n)} (hT : ModeloHorn cs T) :
    ∀ i, prop cs i ⊆ T := by
  intro i
  induction i with
  | zero => exact Finset.empty_subset _
  | succ i ih => rw [prop_succ]; exact (paso_mono cs ih).trans (paso_sub_modelo hT)

/-- **Corrección de Horn**: el algoritmo dice que sí si y solo si hay modelo. -/
theorem decideHorn_correcto {n : ℕ} (cs : List (ClausulaHorn n)) :
    decideHorn cs = true ↔ ∃ T, ModeloHorn cs T := by
  constructor
  · intro h
    refine ⟨minimo cs, fun c hc => ?_⟩
    exact List.all_eq_true.mp h c hc
  · rintro ⟨T, hT⟩
    apply List.all_eq_true.mpr
    intro c hc
    have hsub := minimo_sub hT (n + 1)
    have hcT := hT c hc
    unfold ClausulaHorn.cumple at hcT ⊢
    by_cases hb : c.cuerpo ⊆ minimo cs
    · have hbT : c.cuerpo ⊆ T := hb.trans hsub
      simp only [hbT, decide_true, Bool.not_true, Bool.false_or] at hcT
      simp only [hb, decide_true, Bool.not_true, Bool.false_or]
      cases hcab : c.cabeza with
      | none => rw [hcab] at hcT; cases hcT
      | some h =>
        -- la cabeza entra en el paso siguiente, y el mínimo es punto fijo
        have hmem : h ∈ paso cs (minimo cs) := by
          simp only [paso, Finset.mem_union, List.mem_toFinset, List.mem_filterMap]
          exact Or.inr ⟨c, hc, by simp only [hb, ↓reduceIte, hcab]⟩
        have hfix : paso cs (minimo cs) = minimo cs := prop_fijo cs
        rw [hfix] at hmem
        simpa using hmem
    · simp [hb]

/-- **El álgebra, a la vista**: los modelos de Horn son cerrados por intersección (el AND es polimorfismo). Por eso
existe un modelo mínimo, y por eso propagar desde abajo basta. -/
theorem modelo_inter {n : ℕ} {cs : List (ClausulaHorn n)} {S T : Finset (Fin n)}
    (hS : ModeloHorn cs S) (hT : ModeloHorn cs T) : ModeloHorn cs (S ∩ T) := by
  intro c hc
  have h1 := hS c hc
  have h2 := hT c hc
  unfold ClausulaHorn.cumple at h1 h2 ⊢
  by_cases hb : c.cuerpo ⊆ S ∩ T
  · have hbS : c.cuerpo ⊆ S := hb.trans Finset.inter_subset_left
    have hbT : c.cuerpo ⊆ T := hb.trans Finset.inter_subset_right
    simp only [hbS, hbT, hb, decide_true, Bool.not_true, Bool.false_or] at h1 h2 ⊢
    cases hcab : c.cabeza with
    | none => rw [hcab] at h1; cases h1
    | some h => rw [hcab] at h1 h2; simp_all
  · simp [hb]

/-! ### 3c. Dual-Horn: el mismo algoritmo sobre los complementos -/

/-- Un modelo dual-Horn de `cs`: la misma cláusula leída con los valores negados (`¬cuerpo → ¬cabeza`, a lo sumo un
literal negativo). `S` son las variables en `0`. -/
def ModeloDual {n : ℕ} (cs : List (ClausulaHorn n)) (S : Finset (Fin n)) : Prop := ModeloHorn cs Sᶜ

/-- Dual-Horn se decide con `decideHorn`: complementar es una biyección de asignaciones. -/
theorem decideDual_correcto {n : ℕ} (cs : List (ClausulaHorn n)) :
    decideHorn cs = true ↔ ∃ S, ModeloDual cs S := by
  rw [decideHorn_correcto]
  constructor
  · rintro ⟨T, hT⟩; exact ⟨Tᶜ, by simpa [ModeloDual] using hT⟩
  · rintro ⟨S, hS⟩; exact ⟨Sᶜ, hS⟩

/-! ## 4. El lado completo: definiciones primitivas positivas y la conexión de Galois -/

/-- Una **definición primitiva positiva** de una relación de aridad `s` sobre el molde `Γ`: variables `W`, una
conjunción de restricciones de `Γ` indexada por `ι` (finita), y las `s` variables libres `libre` (que pueden
repetirse: eso hace las veces de la igualdad). Lo demás está cuantificado existencialmente. -/
structure DefPP (Γ : Relaciones) (s : ℕ) where
  W : Type
  ι : Type
  [finW : Finite W]
  [finι : Finite ι]
  rel : ι → Σ r : ℕ, Relacion r
  mem : ∀ i, rel i ∈ Γ
  alcance : (i : ι) → Fin (rel i).1 → W
  libre : Fin s → W

attribute [instance] DefPP.finW DefPP.finι

/-- La relación que define: `∃ x, x ∘ libre = y ∧ ⋀ᵢ relᵢ (x ∘ alcanceᵢ)`. -/
def DefPP.Define {Γ : Relaciones} {s : ℕ} (D : DefPP Γ s) (y : Fin s → Bool) : Prop :=
  ∃ x : D.W → Bool, (∀ c, x (D.libre c) = y c) ∧ ∀ i, (D.rel i).2 (x ∘ D.alcance i)

/-- **La dirección fácil de Galois**: un polimorfismo de `Γ` preserva todo lo que `Γ` define primitivo-positivamente.
Se aplica `f` a los testigos, variable por variable. -/
theorem definible_preserva {Γ : Relaciones} {s : ℕ} (D : DefPP Γ s) {k : ℕ} (f : (Fin k → Bool) → Bool)
    (hf : Polimorfismo Γ f) : Preserva f D.Define := by
  intro t ht
  choose x hx1 hx2 using ht
  refine ⟨fun w => f (fun i => x i w), fun c => ?_, fun j => ?_⟩
  · simp only [hx1]
  · exact hf _ (D.mem j) (fun i => x i ∘ D.alcance j) (fun i => hx2 i j)

/-- Las tuplas de `S`, enumeradas: `tuplas S : Fin m → Bool^s` con `m = |S|`. -/
noncomputable def tuplas {s : ℕ} (S : Relacion s) : Fin (Nat.card {y // S y}) → Fin s → Bool :=
  fun i => ((Finite.equivFin {y // S y}).symm i).1

theorem tuplas_mem {s : ℕ} (S : Relacion s) (i : Fin (Nat.card {y // S y})) : S (tuplas S i) :=
  ((Finite.equivFin {y // S y}).symm i).2

theorem tuplas_sobre {s : ℕ} (S : Relacion s) {y : Fin s → Bool} (hy : S y) : ∃ i, tuplas S i = y :=
  ⟨Finite.equivFin {y // S y} ⟨y, hy⟩, by simp [tuplas]⟩

/-- Las restricciones de la definición canónica: una relación de `Γ` y un alcance sobre `Bool^m` tales que la
restricción se cumple en las `m` asignaciones canónicas `w ↦ w i`. -/
def Canonicas (Γ : Relaciones) (m : ℕ) : Type :=
  {p : Σ R : Γ, Fin R.1.1 → (Fin m → Bool) // ∀ i : Fin m, p.1.1.2 (fun c => p.2 c i)}

instance {Γ : Relaciones} (m : ℕ) [Finite Γ] : Finite (Canonicas Γ m) := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  unfold Canonicas; infer_instance

/-- La definición canónica de `S` sobre `Γ` (Geiger; Bodnarchuk, Kaluzhnin, Kotov y Romov, 1968–1969): las variables
son `Bool^m` con `m = |S|`, las restricciones son todas las de `Γ` que valen en las `m` asignaciones canónicas, y la
variable libre `c` es la columna `c` de las tuplas de `S`. Sus soluciones son exactamente los polimorfismos `m`-arios
de `Γ`. -/
noncomputable def canonica (Γ : Relaciones) [Finite Γ] {s : ℕ} (S : Relacion s) : DefPP Γ s where
  W := Fin (Nat.card {y // S y}) → Bool
  ι := Canonicas Γ (Nat.card {y // S y})
  rel p := p.1.1.1
  mem p := p.1.1.2
  alcance p := p.1.2
  libre c := fun i => tuplas S i c

/-- **La conexión de Galois, en el caso booleano finito** (`Inv(Pol Γ) ⊆ ⟨Γ⟩`): si todo polimorfismo de `Γ`
preserva `S`, la definición canónica define `S`. Con `definible_preserva` es la igualdad `Inv(Pol Γ) = ⟨Γ⟩`. -/
theorem galois {Γ : Relaciones} [Finite Γ] {s : ℕ} (S : Relacion s)
    (hS : ∀ (k : ℕ) (f : (Fin k → Bool) → Bool), Polimorfismo Γ f → Preserva f S) :
    ∀ y, S y ↔ (canonica Γ S).Define y := by
  intro y
  constructor
  · intro hy
    obtain ⟨i, rfl⟩ := tuplas_sobre S hy
    exact ⟨fun w => w i, fun c => rfl, fun p => p.2 i⟩
  · rintro ⟨x, hx1, hx2⟩
    have hpol : Polimorfismo Γ x := by
      intro R hR t ht
      exact hx2 ⟨⟨⟨R, hR⟩, fun c i => t i c⟩, ht⟩
    have := hS _ x hpol (tuplas S) (tuplas_mem S)
    have heq : (fun c => x (fun i => tuplas S i c)) = y := funext hx1
    rwa [heq] at this

/-- Si `S` separa sus coordenadas, las variables libres de la definición canónica son distintas. -/
theorem canonica_libre_iny {Γ : Relaciones} [Finite Γ] {s : ℕ} (S : Relacion s)
    (hsep : ∀ c c', c ≠ c' → ∃ y, S y ∧ y c ≠ y c') : Function.Injective (canonica Γ S).libre := by
  intro c c' h
  by_contra hne
  obtain ⟨y, hy, hyc⟩ := hsep c c' hne
  obtain ⟨i, rfl⟩ := tuplas_sobre S hy
  exact hyc (congrFun h i)

/-! ### La reducción por gadgets -/

section Reduccion

variable {Γ Δ : Relaciones} {V : Type}

/-- Las variables de la instancia traducida: las originales y, por cada restricción `i`, las existenciales de su
gadget. -/
abbrev VarT (defs : ∀ R ∈ Δ, DefPP Γ R.1) (I : Instancia Δ V) : Type :=
  V ⊕ Σ i : Fin I.length, (defs _ (I.get i).mem).W

open Classical in
/-- Dónde va a parar la variable `w` del gadget `i`: si es libre, a la variable original de su alcance; si no, a una
variable nueva. -/
noncomputable def φ (defs : ∀ R ∈ Δ, DefPP Γ R.1) (I : Instancia Δ V) (i : Fin I.length)
    (w : (defs _ (I.get i).mem).W) : VarT defs I :=
  if h : ∃ c, (defs _ (I.get i).mem).libre c = w then Sum.inl ((I.get i).alcance h.choose)
  else Sum.inr ⟨i, w⟩

/-- La restricción `j` del gadget `i`, ya con las variables puestas. -/
noncomputable def gadget (defs : ∀ R ∈ Δ, DefPP Γ R.1) (I : Instancia Δ V) (i : Fin I.length)
    (j : (defs _ (I.get i).mem).ι) : Restriccion Γ (VarT defs I) where
  R := (defs _ (I.get i).mem).rel j
  mem := (defs _ (I.get i).mem).mem j
  alcance := φ defs I i ∘ (defs _ (I.get i).mem).alcance j

/-- **La traducción**: cada restricción de `Δ` se reemplaza por su gadget. -/
noncomputable def traducir (defs : ∀ R ∈ Δ, DefPP Γ R.1) (I : Instancia Δ V) : Instancia Γ (VarT defs I) :=
  (List.finRange I.length).flatMap fun i =>
    (List.finRange (Nat.card (defs _ (I.get i).mem).ι)).map fun a =>
      gadget defs I i ((Finite.equivFin _).symm a)

theorem mem_traducir (defs : ∀ R ∈ Δ, DefPP Γ R.1) (I : Instancia Δ V) (c : Restriccion Γ (VarT defs I)) :
    c ∈ traducir defs I ↔ ∃ i j, gadget defs I i j = c := by
  simp only [traducir, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  constructor
  · rintro ⟨i, a, rfl⟩; exact ⟨i, _, rfl⟩
  · rintro ⟨i, j, rfl⟩; exact ⟨i, Finite.equivFin _ j, by simp⟩

/-- Una variable libre del gadget va a parar a la variable original de su alcance. -/
theorem φ_libre (defs : ∀ R ∈ Δ, DefPP Γ R.1)
    (hiny : ∀ R (h : R ∈ Δ), Function.Injective (defs R h).libre) (I : Instancia Δ V) (i : Fin I.length)
    (c0 : Fin (I.get i).R.1) :
    φ defs I i ((defs _ (I.get i).mem).libre c0) = Sum.inl ((I.get i).alcance c0) := by
  unfold φ
  split_ifs with h
  · rw [hiny _ _ h.choose_spec]
  · exact absurd ⟨c0, rfl⟩ h

/-- **La reducción preserva la satisfacibilidad**, si cada relación de `Δ` tiene una definición con variables libres
distintas. -/
theorem traducir_correcto (defs : ∀ R ∈ Δ, DefPP Γ R.1)
    (hdefs : ∀ R (h : R ∈ Δ), ∀ y, R.2 y ↔ (defs R h).Define y)
    (hiny : ∀ R (h : R ∈ Δ), Function.Injective (defs R h).libre) (I : Instancia Δ V) :
    Satisfacible I ↔ Satisfacible (traducir defs I) := by
  constructor
  · rintro ⟨x, hx⟩
    have hi : ∀ i : Fin I.length, (defs _ (I.get i).mem).Define (x ∘ (I.get i).alcance) := fun i =>
      (hdefs _ _ _).mp (hx _ (List.get_mem I i))
    choose z hz1 hz2 using hi
    let x' : VarT defs I → Bool := Sum.elim x (fun p => z p.1 p.2)
    have hφ : ∀ i, x' ∘ φ defs I i = z i := by
      intro i; funext w
      show x' (φ defs I i w) = z i w
      unfold φ
      split_ifs with h
      · have hs := h.choose_spec
        generalize h.choose = c at hs ⊢
        subst hs
        simp only [x', Sum.elim_inl]
        rw [hz1]; rfl
      · rfl
    refine ⟨x', fun c hc => ?_⟩
    obtain ⟨i, j, rfl⟩ := (mem_traducir defs I c).mp hc
    show ((defs _ (I.get i).mem).rel j).2 (x' ∘ (φ defs I i ∘ (defs _ (I.get i).mem).alcance j))
    rw [← Function.comp_assoc, hφ]
    exact hz2 i j
  · rintro ⟨x', hx'⟩
    refine ⟨x' ∘ Sum.inl, fun c hc => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
    apply (hdefs _ _ _).mpr
    refine ⟨x' ∘ φ defs I i, fun c0 => ?_, fun j => ?_⟩
    · show x' (φ defs I i _) = _
      rw [φ_libre defs hiny]; rfl
    · have := hx' (gadget defs I i j) ((mem_traducir defs I _).mpr ⟨i, j, rfl⟩)
      exact this

/-- Y es lineal: a lo sumo `K` restricciones por cada una, si cada gadget tiene a lo sumo `K`. -/
theorem traducir_largo (defs : ∀ R ∈ Δ, DefPP Γ R.1) (K : ℕ)
    (hK : ∀ R (h : R ∈ Δ), Nat.card (defs R h).ι ≤ K) (I : Instancia Δ V) :
    (traducir defs I).length ≤ I.length * K := by
  unfold traducir
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_finRange]
  calc _ ≤ ((List.finRange I.length).map fun _ => K).sum := List.sum_le_sum (fun i _ => hK _ _)
    _ = I.length * K := by simp

end Reduccion

/-! ### 3-SAT y NAE-3-SAT se definen cuando el álgebra es pobre -/

/-- Las tres coordenadas no son iguales. -/
def nae : Relacion 3 := fun x => ¬ (x 0 = x 1 ∧ x 1 = x 2)

/-- NAE-3-SAT como molde. -/
def naeSAT : Relaciones := {⟨3, nae⟩}

/-- Una operación **esencialmente unaria y autodual**: una proyección o una proyección negada (el clon `N₂` de Post,
generado por la negación). -/
def EsencialUnaria {k : ℕ} (f : (Fin k → Bool) → Bool) : Prop :=
  ∃ j, f = proy j ∨ f = fun x => !x j

theorem clausula_separa (σ : Fin 3 → Bool) : ∀ c c' : Fin 3, c ≠ c' → ∃ y, clausula σ y ∧ y c ≠ y c' := by
  revert σ; decide

theorem nae_separa : ∀ c c' : Fin 3, c ≠ c' → ∃ y, nae y ∧ y c ≠ y c' := by
  unfold nae; decide

theorem nae_preserva_unaria {k : ℕ} (f : (Fin k → Bool) → Bool) (hf : EsencialUnaria f) : Preserva f nae := by
  obtain ⟨j, rfl | rfl⟩ := hf
  · exact proy_preserva j nae
  · intro t ht
    have := ht j
    unfold nae at this ⊢
    intro h; apply this
    simp only [Bool.not_inj_iff] at h ⊢
    exact h

/-- **Lado completo, la forma que se usa**: si `Γ` es finito y todos sus polimorfismos son proyecciones, cada
cláusula de 3 literales tiene una definición primitiva positiva sobre `Γ`, con variables libres distintas. -/
theorem define_tresSAT {Γ : Relaciones} [Finite Γ]
    (hΓ : ∀ (k : ℕ) (f : (Fin k → Bool) → Bool), Polimorfismo Γ f → ∃ j, f = proy j) :
    ∀ R ∈ tresSAT, ∀ y, R.2 y ↔ (canonica Γ R.2).Define y := by
  rintro R ⟨σ, rfl⟩
  apply galois
  intro k f hf
  obtain ⟨j, rfl⟩ := hΓ k f hf
  exact proy_preserva j _

/-- **3-SAT se reduce a `CSP(Γ)`** si los polimorfismos de `Γ` son solo proyecciones: la traducción por gadgets
preserva la satisfacibilidad y tiene largo lineal. -/
theorem tresSAT_se_reduce {Γ : Relaciones} [Finite Γ]
    (hΓ : ∀ (k : ℕ) (f : (Fin k → Bool) → Bool), Polimorfismo Γ f → ∃ j, f = proy j) {V : Type}
    (I : Instancia tresSAT V) :
    Satisfacible I ↔ Satisfacible (traducir (fun R _ => canonica Γ R.2) I) := by
  apply traducir_correcto
  · intro R h; exact define_tresSAT hΓ R h
  · rintro R ⟨σ, rfl⟩
    exact canonica_libre_iny _ (clausula_separa σ)

/-- Lo mismo para NAE-3-SAT cuando los polimorfismos de `Γ` son esencialmente unarios (proyecciones o negaciones). -/
theorem naeSAT_se_reduce {Γ : Relaciones} [Finite Γ]
    (hΓ : ∀ (k : ℕ) (f : (Fin k → Bool) → Bool), Polimorfismo Γ f → EsencialUnaria f) {V : Type}
    (I : Instancia naeSAT V) :
    Satisfacible I ↔ Satisfacible (traducir (fun R _ => canonica Γ R.2) I) := by
  apply traducir_correcto
  · rintro R rfl
    apply galois
    intro k f hf
    exact nae_preserva_unaria f (hΓ k f hf)
  · rintro R rfl
    exact canonica_libre_iny _ nae_separa

/-- **La honestidad sobre la negación**: si la negación es polimorfismo de `Γ`, **ninguna** cláusula se define sobre
`Γ` (la negación la rompería). Por eso «no tiene ninguno de los seis» no basta para definir 3-SAT: el caso `N₂` pasa
por NAE-3-SAT. -/
theorem negacion_impide {Γ : Relaciones} (hneg : Polimorfismo Γ negacion) {r : ℕ} [NeZero r]
    (σ : Fin r → Bool) (D : DefPP Γ r) : ¬ ∀ y, clausula σ y ↔ D.Define y := by
  intro h
  apply negacion_no_preserva σ
  have hp := definible_preserva D negacion hneg
  intro t ht
  exact (h _).mpr (hp t fun i => (h _).mp (ht i))

/-! ## 5. «No deja medio»: la dicotomía, módulo lo que se nombra -/

/-- El OR de dos. -/
def o : (Fin 2 → Bool) → Bool := fun x => x 0 || x 1

/-- **Los seis interruptores de Schaefer**: alguna de las seis identidades se cumple en `Pol(Γ)`. Constantes `0` y
`1` (0-válido, 1-válido), AND (Horn), OR (dual-Horn), mayoría (2-SAT, bijuntivo) y minoría `x ⊕ y ⊕ z` (afín). -/
def TieneUnaDeLasSeis (Γ : Relaciones) : Prop :=
  Polimorfismo Γ (const false) ∨ Polimorfismo Γ (const true) ∨ Polimorfismo Γ y ∨ Polimorfismo Γ o ∨
    Polimorfismo Γ maj ∨ Polimorfismo Γ maltsev

/-- Lo que esta formalización **no** prueba, con nombre. `EnP Γ` y `NPc Γ` son predicados opacos («`CSP(Γ)` está en
P», «es NP-completo»): aquí no hay modelo de máquina para los CSP.

* `facil`: el lado fácil de Schaefer. Aquí se prueban, como algoritmos con su corrección, las constantes
  (`const_decide`), Horn (`decideHorn_correcto`) y dual-Horn (`decideDual_correcto`); 2-SAT y el afín (eliminación
  gaussiana) quedan en la hipótesis.
* `post`: el retículo de Post. Sin ninguno de los seis, `Pol(Γ)` está en `N₂` (proyecciones y proyecciones negadas).
* `tres`, `naeC`: 3-SAT y NAE-3-SAT son NP-completos (Cook–Levin; Schaefer).
* `reduce`: la traducción por gadgets es una reducción polinomial; aquí se prueba que preserva la satisfacibilidad y
  que es lineal (`traducir_correcto`, `traducir_largo`), no el tiempo de calcularla.
* `separa`: P ≠ NP, en la forma «lo NP-completo no está en P». -/
structure Supuestos (EnP NPc : Relaciones → Prop) : Prop where
  facil : ∀ Γ : Relaciones, Γ.Finite → TieneUnaDeLasSeis Γ → EnP Γ
  post : ∀ Γ : Relaciones, ¬ TieneUnaDeLasSeis Γ →
    ∀ (k : ℕ) (f : (Fin k → Bool) → Bool), Polimorfismo Γ f → EsencialUnaria f
  tres : NPc tresSAT
  naeC : NPc naeSAT
  reduce : ∀ Γ Δ : Relaciones, Γ.Finite → Δ.Finite → NPc Δ →
    (∀ R ∈ Δ, ∃ D : DefPP Γ R.1, Function.Injective D.libre ∧ ∀ y, R.2 y ↔ D.Define y) → NPc Γ
  separa : ∀ Γ, NPc Γ → ¬ EnP Γ

/-- Las ocho cláusulas son finitas. -/
theorem tresSAT_finito : tresSAT.Finite := by
  have : tresSAT = Set.range (fun σ : Fin 3 → Bool => (⟨3, clausula σ⟩ : Σ r : ℕ, Relacion r)) := by
    ext R; simp [tresSAT, eq_comm]
  rw [this]; exact Set.finite_range _

/-- Sin ninguno de los seis, `CSP(Γ)` es NP-completo: o los polimorfismos son solo proyecciones (y 3-SAT se define),
o hay negación (y NAE-3-SAT se define). -/
theorem dificil {EnP NPc : Relaciones → Prop} (H : Supuestos EnP NPc) (Γ : Relaciones) (hΓ : Γ.Finite)
    (h6 : ¬ TieneUnaDeLasSeis Γ) : NPc Γ := by
  have := hΓ.to_subtype
  have hpost := H.post Γ h6
  by_cases hneg : Polimorfismo Γ negacion
  · apply H.reduce Γ naeSAT hΓ (Set.finite_singleton _) H.naeC
    rintro R rfl
    refine ⟨canonica Γ nae, canonica_libre_iny _ nae_separa, galois nae fun k f hf => ?_⟩
    exact nae_preserva_unaria f (hpost k f hf)
  · apply H.reduce Γ tresSAT hΓ tresSAT_finito H.tres
    rintro R ⟨σ, rfl⟩
    refine ⟨canonica Γ (clausula σ), canonica_libre_iny _ (clausula_separa σ), galois _ fun k f hf => ?_⟩
    obtain ⟨j, hj | hj⟩ := hpost k f hf
    · subst hj; exact proy_preserva j _
    · -- una proyección negada en `Pol(Γ)` da la negación en `Pol(Γ)`: identificar todas las variables
      exfalso; apply hneg
      intro R' hR' t ht
      have := hf R' hR' (fun _ => t 0) (fun _ => ht 0)
      simpa [hj, negacion, unaria] using this

/-- **La dicotomía booleana, módulo los supuestos**: cada `CSP(Γ)` finito está en P o es NP-completo, nunca las dos
cosas, y lo decide **una sola identidad**: tener uno de los seis polimorfismos. No queda medio. -/
theorem dicotomia {EnP NPc : Relaciones → Prop} (H : Supuestos EnP NPc) (Γ : Relaciones) (hΓ : Γ.Finite) :
    (EnP Γ ∧ ¬ NPc Γ) ∨ (NPc Γ ∧ ¬ EnP Γ) := by
  by_cases h6 : TieneUnaDeLasSeis Γ
  · have hp := H.facil Γ hΓ h6
    exact Or.inl ⟨hp, fun hn => H.separa Γ hn hp⟩
  · have hn := dificil H Γ hΓ h6
    exact Or.inr ⟨hn, H.separa Γ hn⟩

/-- **El interruptor**: estar en P es exactamente tener una de las seis identidades. -/
theorem interruptor {EnP NPc : Relaciones → Prop} (H : Supuestos EnP NPc) (Γ : Relaciones) (hΓ : Γ.Finite) :
    EnP Γ ↔ TieneUnaDeLasSeis Γ := by
  constructor
  · intro hp; by_contra h6; exact H.separa Γ (dificil H Γ hΓ h6) hp
  · exact H.facil Γ hΓ

/-- **No hay intermedios**: ningún `CSP(Γ)` finito queda fuera de P sin ser NP-completo. (Contra Ladner, que en NP en
general sí los da bajo P ≠ NP: ver `FractalSAT.lean`.) -/
theorem sin_intermedios {EnP NPc : Relaciones → Prop} (H : Supuestos EnP NPc) (Γ : Relaciones) (hΓ : Γ.Finite) :
    ¬ (¬ EnP Γ ∧ ¬ NPc Γ) := by
  rintro ⟨h1, h2⟩
  rcases dicotomia H Γ hΓ with h | h
  · exact h1 h.1
  · exact h2 h.1

end Sagitta.Map.Borde.DicotomiaBooleana
