import Sagitta.Map.EspejoEF

/-!
# La inducción se rompe en una familia

La inducción es una **regla homogénea**: el mismo paso `φ(x) → φ(x+1)` sirve para todo `x`, y una prueba en `S¹₂`
que la usa es **una sola** para todos los `n`. Al bajar a la lógica proposicional (la traducción de `EspejoEF.lean`,
la mitad semántica del espejo de Cook y de Paris–Wilkie) esa uniformidad se rompe: para cada `N` fijo, la instancia

  `φ(0) ∧ ∀x<N (φ(x) → φ(x+1)) → φ(N)`

se vuelve una fórmula proposicional distinta, y su prueba es la **cadena de `N` modus ponens**. Este archivo la
construye en el sistema de Frege de cslib-frontier (`Cslib.Logic.PL.Frege`: K, S, doble negación, los esquemas de
`∧` y `∨`, y modus ponens), línea por línea, y la mide.

## Qué está probado

* **La regla, en abstracto** (`deriva_induccion`): para cualquier familia `P : ℕ → Proposition V`, la fórmula
  `induccion P N = (P 0 ∧ cadena P 0 N) → P N`, con `cadena P 0 N` la conjunción de los pasos `P k → P (k+1)` para
  `k < N`, tiene una prueba de Frege **sin hipótesis** de exactamente `15 N + 17` líneas, y cada línea mide a lo sumo
  `9 h + 9` símbolos, con `h` el tamaño de la hipótesis. No se usa el teorema de la deducción de cslib (que no acota
  símbolos): la prueba se arma a mano bajo el antecedente `H` con dos bloques, un axioma bajo `H` (`bajo_ax`, 3 líneas) y
  un modus ponens bajo `H` (`bajo_mp`, 3 líneas, el esquema S). Cada paso de la cadena son 15 líneas: sacar el paso
  `P k → P (k+1)` de la conjunción (6), sacar el resto (6) y el modus ponens (3).
* **El tamaño** (`tamProof_induccion`): la suma de los tamaños de las líneas es a lo sumo
  `(15 N + 17) · (9 h + 9)`, y `h ≤ C + N (2C + 2) + 4` si cada `P k` mide a lo sumo `C` (`tamG_hipInd`).
* **Con la traducción `trad`** (`indTrad`): `P k = ⟦φ⟧` con `x := k` (la constante `k` en bits, `extE k`) y
  los parámetros de `φ` como `N` bits de entrada. Para toda `φ` (en la clase o no) la familia tiene pruebas de Frege
  de `15 N + 17` líneas (`indTrad_deriva`) y tamaño total acotado por un polinomio en `N` (`indTrad_cota`,
  `cotaInd_acotada`). Para `φ` en la clase `Σᵇ₀` restringida, la fórmula dice lo que debe
  (`indTrad_eval`: vale con `σ` si y solo si la instancia de inducción vale en el número que forman los bits).
* **Dos rutas a la verdad**: la tautología sale de la corrección de Frege (`indTrad_tautologia`) y, por separado, la
  instancia de inducción en `ℕ` sale de `indTrad_eval` (`instancia_de_prueba`): la prueba proposicional, leída de vuelta,
  da la inducción aritmética acotada.

## Controles

* `sin_ultimo_paso`: si a la cadena le falta el último paso, la fórmula ya no es tautología (con `P k` el átomo `k` y
  `N = 1`): la cadena entera hace falta. Por la corrección de Frege, tampoco tiene prueba.
* `indTrad_sucMayor_eval`: para `φ = (x + 1 ≰ x)` y `N = 2` la fórmula concreta se arma y se evalúa con `decide` (en la
  asignación toda falsa; que sea tautología lo da `indTrad_tautologia`).
* Mutantes (fuera del repositorio): un paso equivocado en la cadena (`P i → P i`), 14 líneas por paso en vez de
  15, y `2C + 1` por paso en la cota de la hipótesis; los tres los rechaza Lean.

## Lo que NO se prueba

* **Una cota inferior.** Que la familia no tenga pruebas más cortas que lineales en `N` no está probado. De hecho la
  cadena es lineal en `N`, que es el valor de `x`, no su largo: para `N` exponencial en el largo (la inducción
  completa `IND` sobre `x < 2ⁿ`) esta cadena es exponencial, y por eso `S¹₂` usa la inducción de largo (`LIND`/`PIND`),
  donde `N = |a|` y la cadena es polinomial. Eso es lo que este archivo modela: `N` es un número chico, del orden del
  largo.
* **La traducción de las pruebas** de `S¹₂` regla por regla (corte con fórmulas acotadas, reglas aritméticas, los
  cuantificadores, la `Σᵇ₁`-`PIND` con su testigo): eso es Paris–Wilkie y Cook completo, y no está. Aquí solo la
  inducción, que es la regla homogénea, y con las instancias `φ(k)` ya traducidas (no se prueba que `⟦φ(k)⟧` venga de
  sustituir en `⟦φ(x)⟧`; aquí se define así).
* Ni Frege extendido, ni la reflexión, ni la simulación (ver `EspejoEF.lean`).
-/

open Cslib.Logic.PL

namespace Sagitta.Map
namespace Extraccion
namespace EspejoInduccion

open Cerradura (Acotada)
open EspejoEF

variable {V : Type}

/-! ## Tamaño genérico -/

/-- El tamaño de una fórmula con átomos cualesquiera: número de símbolos. -/
def tamG : Proposition V → ℕ
  | .atom _ => 1
  | .falsum => 1
  | .and a b => tamG a + tamG b + 1
  | .or a b => tamG a + tamG b + 1
  | .imp a b => tamG a + tamG b + 1

/-- Coincide con el `tam` de `EspejoEF` en las fórmulas con átomos en `ℕ`. -/
theorem tamG_eq_tam (p : FP) : tamG p = tam p := by
  induction p with
  | atom => rfl
  | falsum => rfl
  | and a b iha ihb => simp only [tamG, tam, iha, ihb]
  | or a b iha ihb => simp only [tamG, tam, iha, ihb]
  | imp a b iha ihb => simp only [tamG, tam, iha, ihb]

/-- El tamaño total de una prueba: la suma de los tamaños de sus líneas. -/
def tamProof (L : List (Proposition V)) : ℕ := (L.map tamG).sum

theorem tamProof_le {L : List (Proposition V)} {B : ℕ} (h : ∀ l ∈ L, tamG l ≤ B) : tamProof L ≤ L.length * B := by
  induction L with
  | nil => simp [tamProof]
  | cons a L ih =>
    have h₁ := h a List.mem_cons_self
    have h₂ := ih fun l hl => h l (List.mem_cons_of_mem _ hl)
    simp only [tamProof, List.map_cons, List.sum_cons, List.length_cons] at h₂ ⊢
    rw [Nat.succ_mul]; omega

/-! ## La instancia de inducción, proposicional -/

/-- Los pasos `P i → P (i+1)`, …, `P (i+m-1) → P (i+m)`, en conjunción (termina en `⊥ → ⊥`). -/
def cadena (P : ℕ → Proposition V) (i : ℕ) : ℕ → Proposition V
  | 0 => .imp .falsum .falsum
  | m + 1 => .and (.imp (P i) (P (i + 1))) (cadena P (i + 1) m)

/-- La hipótesis de la inducción: la base y los `N` pasos. -/
def hipInd (P : ℕ → Proposition V) (N : ℕ) : Proposition V := .and (P 0) (cadena P 0 N)

/-- **La instancia de inducción para `N` fijo**: `P 0 ∧ (P 0 → P 1) ∧ ⋯ ∧ (P (N-1) → P N) → P N`. -/
def induccion (P : ℕ → Proposition V) (N : ℕ) : Proposition V := .imp (hipInd P N) (P N)

theorem eval_cadena (P : ℕ → Proposition V) (σ : V → Bool) :
    ∀ (i m : ℕ), (cadena P i m).eval σ = true ↔ ∀ j < m, (P (i + j)).eval σ = true → (P (i + j + 1)).eval σ = true
  | i, 0 => by simp [cadena, Proposition.eval_imp_bool]
  | i, m + 1 => by
    rw [cadena, Proposition.eval_and_bool, Bool.and_eq_true, eval_cadena P σ (i + 1) m,
      Proposition.eval_imp_bool]
    constructor
    · rintro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · intro hp; simp only [Nat.add_zero] at hp ⊢; rw [hp] at h₀; simpa using h₀
      · have := h j (by omega); rw [show i + (j + 1) = i + 1 + j by omega]; exact this
    · intro h
      refine ⟨?_, fun j hj => ?_⟩
      · cases hp : (P i).eval σ
        · rfl
        · have := h 0 (by omega) (by simpa using hp); simpa using this
      · have := h (j + 1) (by omega); rwa [show i + (j + 1) = i + 1 + j by omega] at this

theorem eval_induccion (P : ℕ → Proposition V) (N : ℕ) (σ : V → Bool) :
    (induccion P N).eval σ = true ↔
      ((P 0).eval σ = true ∧ (cadena P 0 N).eval σ = true) → (P N).eval σ = true := by
  simp only [induccion, hipInd, Proposition.eval_imp_bool, Proposition.eval_and_bool]
  cases (P 0).eval σ <;> cases (cadena P 0 N).eval σ <;> cases (P N).eval σ <;> simp

/-! ## Dos bloques bajo un antecedente `H` -/

/-- Un axioma bajo `H`, en tres líneas: `X`, `X → (H → X)` (K) y `H → X`. -/
theorem bajo_ax {H X : Proposition V} {L : List (Proposition V)} (hL : Frege.IsProof [] L) (hX : Frege.IsAxiom X) :
    Frege.IsProof [] (.imp H X :: .imp X (.imp H X) :: X :: L) :=
  ((hL.ax hX).ax (.k X H)).mp (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self

/-- Modus ponens bajo `H`, en tres líneas: el esquema S y dos modus ponens. -/
theorem bajo_mp {H X Y : Proposition V} {L : List (Proposition V)} (hL : Frege.IsProof [] L)
    (h₁ : .imp H X ∈ L) (h₂ : .imp H (.imp X Y) ∈ L) :
    Frege.IsProof [] (.imp H Y :: .imp (.imp H X) (.imp H Y) ::
      .imp (.imp H (.imp X Y)) (.imp (.imp H X) (.imp H Y)) :: L) := by
  have a := hL.ax (Frege.IsAxiom.s H X Y)
  have b := a.mp (List.mem_cons_of_mem _ h₂) List.mem_cons_self
  exact b.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h₁)) List.mem_cons_self

/-- El invariante de una prueba en construcción: largo exacto y cada línea de a lo sumo `9 h + 9` símbolos. -/
def Buena (H : Proposition V) (L : List (Proposition V)) (n : ℕ) : Prop :=
  Frege.IsProof [] L ∧ L.length = n ∧ ∀ l ∈ L, tamG l ≤ 9 * tamG H + 9

/-- **Sacar la izquierda bajo `H`**: de `H → (A ∧ B)`, `H → A` en seis líneas. -/
theorem bajo_izq {H A B : Proposition V} {L : List (Proposition V)} {n : ℕ} (hL : Buena H L n)
    (hmem : .imp H (.and A B) ∈ L) (hAB : tamG (.and A B : Proposition V) ≤ tamG H) :
    ∃ L', Buena H L' (n + 6) ∧ .imp H A ∈ L' ∧ ∀ l ∈ L, l ∈ L' := by
  obtain ⟨hp, hlen, ht⟩ := hL
  have p₁ := bajo_ax (H := H) hp (Frege.IsAxiom.andElimL A B)
  have p₂ := bajo_mp (H := H) (X := .and A B) (Y := A) p₁ (by simp [hmem]) List.mem_cons_self
  refine ⟨_, ⟨p₂, by simp [hlen], ?_⟩, List.mem_cons_self, fun l hl => by simp [hl]⟩
  simp only [tamG] at hAB
  intro l hl
  simp only [List.mem_cons] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | hl
  all_goals first | exact ht _ hl | (simp only [tamG]; omega)

/-- **Sacar la derecha bajo `H`**: de `H → (A ∧ B)`, `H → B` en seis líneas. -/
theorem bajo_der {H A B : Proposition V} {L : List (Proposition V)} {n : ℕ} (hL : Buena H L n)
    (hmem : .imp H (.and A B) ∈ L) (hAB : tamG (.and A B : Proposition V) ≤ tamG H) :
    ∃ L', Buena H L' (n + 6) ∧ .imp H B ∈ L' ∧ ∀ l ∈ L, l ∈ L' := by
  obtain ⟨hp, hlen, ht⟩ := hL
  have p₁ := bajo_ax (H := H) hp (Frege.IsAxiom.andElimR A B)
  have p₂ := bajo_mp (H := H) (X := .and A B) (Y := B) p₁ (by simp [hmem]) List.mem_cons_self
  refine ⟨_, ⟨p₂, by simp [hlen], ?_⟩, List.mem_cons_self, fun l hl => by simp [hl]⟩
  simp only [tamG] at hAB
  intro l hl
  simp only [List.mem_cons] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | hl
  all_goals first | exact ht _ hl | (simp only [tamG]; omega)

/-- **Modus ponens bajo `H`, con el invariante**: de `H → X` y `H → (X → Y)`, `H → Y` en tres líneas. -/
theorem bajo_mp' {H X Y : Proposition V} {L : List (Proposition V)} {n : ℕ} (hL : Buena H L n)
    (h₁ : .imp H X ∈ L) (h₂ : .imp H (.imp X Y) ∈ L) (hXY : tamG (.imp X Y : Proposition V) ≤ tamG H) :
    ∃ L', Buena H L' (n + 3) ∧ .imp H Y ∈ L' ∧ ∀ l ∈ L, l ∈ L' := by
  obtain ⟨hp, hlen, ht⟩ := hL
  have p := bajo_mp hp h₁ h₂
  refine ⟨_, ⟨p, by simp [hlen], ?_⟩, List.mem_cons_self, fun l hl => by simp [hl]⟩
  simp only [tamG] at hXY
  intro l hl
  simp only [List.mem_cons] at hl
  rcases hl with rfl | rfl | rfl | hl
  all_goals first | exact ht _ hl | (simp only [tamG]; omega)

/-- `H → H` en cinco líneas (S, K, modus ponens, K, modus ponens). -/
theorem identidad (H : Proposition V) :
    Buena H [.imp H H, .imp H (.imp H H), .imp (.imp H (.imp H H)) (.imp H H), .imp H (.imp (.imp H H) H),
      .imp (.imp H (.imp (.imp H H) H)) (.imp (.imp H (.imp H H)) (.imp H H))] 5 := by
  refine ⟨?_, rfl, ?_⟩
  · have a := (Frege.IsProof.nil (Γ := ([] : List (Proposition V)))).ax (Frege.IsAxiom.s H (.imp H H) H)
    have b := a.ax (Frege.IsAxiom.k H (.imp H H))
    have c := b.mp List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
    have d := c.ax (Frege.IsAxiom.k H H)
    exact d.mp List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> simp only [tamG] <;> omega

/-! ## Tamaños dentro de la hipótesis -/

theorem tamG_cadena_paso (P : ℕ → Proposition V) (i m : ℕ) :
    tamG (cadena P (i + 1) m) < tamG (cadena P i (m + 1)) ∧
      tamG (.imp (P i) (P (i + 1))) < tamG (cadena P i (m + 1)) := by
  simp only [cadena, tamG]; omega

/-- Lo que queda de la cadena después de `k` pasos cabe en la hipótesis. -/
theorem tamG_resto (P : ℕ → Proposition V) (N : ℕ) :
    ∀ k ≤ N, tamG (cadena P k (N - k)) ≤ tamG (cadena P 0 N)
  | 0, _ => le_rfl
  | k + 1, hk => by
    have ih := tamG_resto P N k (by omega)
    have e : N - k = (N - (k + 1)) + 1 := by omega
    rw [e] at ih
    have := (tamG_cadena_paso P k (N - (k + 1))).1
    omega

/-- Cada `P k` con `k ≤ N` cabe en la hipótesis. -/
theorem tamG_P (P : ℕ → Proposition V) (N : ℕ) : ∀ k ≤ N, tamG (P k) ≤ tamG (hipInd P N)
  | 0, _ => by simp only [hipInd, tamG]; omega
  | k + 1, hk => by
    have h₁ := tamG_resto P N k (by omega)
    have e : N - k = (N - (k + 1)) + 1 := by omega
    rw [e] at h₁
    have h₂ := (tamG_cadena_paso P k (N - (k + 1))).2
    simp only [hipInd, tamG] at h₂ ⊢
    omega

/-! ## La cadena de modus ponens -/

/-- **El invariante de la cadena**: después de `k` pasos, una prueba de `17 + 15 k` líneas con `H → P k` y `H → (lo que
queda de la cadena)`. -/
theorem cadena_mp (P : ℕ → Proposition V) (N : ℕ) :
    ∀ k ≤ N, ∃ L, Buena (hipInd P N) L (17 + 15 * k) ∧ .imp (hipInd P N) (P k) ∈ L ∧
      .imp (hipInd P N) (cadena P k (N - k)) ∈ L
  | 0, _ => by
    set H := hipInd P N
    obtain ⟨L₁, b₁, m₁, s₁⟩ := bajo_izq (A := P 0) (B := cadena P 0 N) (identidad H) List.mem_cons_self le_rfl
    obtain ⟨L₂, b₂, m₂, s₂⟩ := bajo_der (A := P 0) (B := cadena P 0 N) b₁ (s₁ _ List.mem_cons_self) le_rfl
    exact ⟨L₂, b₂, s₂ _ m₁, by simpa using m₂⟩
  | k + 1, hk => by
    set H := hipInd P N
    obtain ⟨L, b, mP, mC⟩ := cadena_mp P N k (by omega)
    have e : N - k = (N - (k + 1)) + 1 := by omega
    rw [e] at mC
    have hc := tamG_resto P N k (by omega)
    rw [e] at hc
    have hH : tamG (cadena P 0 N) < tamG H := by simp only [H, hipInd, tamG]; omega
    have hc' : tamG (cadena P k (N - (k + 1) + 1)) ≤ tamG H := by omega
    obtain ⟨L₁, b₁, m₁, s₁⟩ := bajo_izq b mC (by simpa [cadena] using hc')
    obtain ⟨L₂, b₂, m₂, s₂⟩ := bajo_der b₁ (s₁ _ mC) (by simpa [cadena] using hc')
    have hpaso : tamG (.imp (P k) (P (k + 1)) : Proposition V) ≤ tamG H :=
      le_trans (le_of_lt (tamG_cadena_paso P k (N - (k + 1))).2) hc'
    obtain ⟨L₃, b₃, m₃, s₃⟩ := bajo_mp' b₂ (s₂ _ (s₁ _ mP)) (s₂ _ m₁) hpaso
    refine ⟨L₃, ?_, m₃, s₃ _ m₂⟩
    have e₂ : 17 + 15 * k + 6 + 6 + 3 = 17 + 15 * (k + 1) := by ring
    rw [← e₂]; exact b₃

/-- **La inducción como regla homogénea, rota en una familia**: para cada `N`, la instancia
`P 0 ∧ (pasos) → P N` tiene una prueba de Frege sin hipótesis de exactamente `15 N + 17` líneas, cada una de a lo
sumo `9 h + 9` símbolos, `h` el tamaño de la hipótesis. -/
theorem deriva_induccion (P : ℕ → Proposition V) (N : ℕ) :
    ∃ L, Frege.IsProof [] L ∧ induccion P N ∈ L ∧ L.length = 15 * N + 17 ∧
      ∀ l ∈ L, tamG l ≤ 9 * tamG (hipInd P N) + 9 := by
  obtain ⟨L, ⟨hp, hlen, ht⟩, hm, -⟩ := cadena_mp P N N le_rfl
  exact ⟨L, hp, hm, by omega, ht⟩

/-- En `15 N + 17` líneas, en el lenguaje de cslib. -/
theorem induccion_derivable (P : ℕ → Proposition V) (N : ℕ) :
    Frege.DerivableInSize [] (induccion P N) (15 * N + 17) := by
  obtain ⟨L, hp, hm, hlen, -⟩ := deriva_induccion P N
  exact ⟨L, hp, hm, hlen.le⟩

/-- El tamaño de la hipótesis, si cada `P k` (con `k ≤ N`) mide a lo sumo `C`. -/
theorem tamG_hipInd {P : ℕ → Proposition V} {N C : ℕ} (hP : ∀ k ≤ N, tamG (P k) ≤ C) :
    tamG (hipInd P N) ≤ C + N * (2 * C + 2) + 4 := by
  have hc : ∀ i m, i + m ≤ N → tamG (cadena P i m) ≤ m * (2 * C + 2) + 3 := by
    intro i m
    induction m generalizing i with
    | zero => intro _; simp [cadena, tamG]
    | succ m ih =>
      intro him
      have h₁ := hP i (by omega)
      have h₂ := hP (i + 1) (by omega)
      have h₃ := ih (i + 1) (by omega)
      simp only [cadena, tamG]
      rw [Nat.succ_mul]; omega
  have h₀ := hP 0 (Nat.zero_le _)
  have := hc 0 N (by omega)
  simp only [hipInd, tamG]; omega

/-- **El tamaño total de la prueba**: a lo sumo `(15 N + 17) · (9 (C + N (2C + 2) + 4) + 9)` símbolos. -/
theorem tamProof_induccion {P : ℕ → Proposition V} {N C : ℕ} (hP : ∀ k ≤ N, tamG (P k) ≤ C) :
    ∃ L, Frege.IsProof [] L ∧ induccion P N ∈ L ∧ L.length = 15 * N + 17 ∧
      tamProof L ≤ (15 * N + 17) * (9 * (C + N * (2 * C + 2) + 4) + 9) := by
  obtain ⟨L, hp, hm, hlen, ht⟩ := deriva_induccion P N
  refine ⟨L, hp, hm, hlen, ?_⟩
  have hh := tamG_hipInd hP
  have := tamProof_le (L := L) (B := 9 * (C + N * (2 * C + 2) + 4) + 9) fun l hl => by
    have := ht l hl; omega
  rwa [hlen] at this

/-! ## Con la traducción `trad` -/

/-- La instancia `φ(k)` traducida: `x := k` (la constante en bits) y los parámetros de `φ` como `N` bits de entrada. -/
def instancia (φ : Formula) (N k : ℕ) : FP := trad φ (N + N) (extE k (entradaE N))

/-- **La instancia de inducción de `φ`, traducida para `N` fijo.** -/
def indTrad (φ : Formula) (N : ℕ) : FP := induccion (instancia φ N) N

/-- Cada instancia mide a lo sumo `cotaF φ (2N)`. -/
theorem tam_instancia (φ : Formula) (N k : ℕ) : tamG (instancia φ N k) ≤ cotaF φ (N + N) := by
  rw [tamG_eq_tam]
  exact tam_trad φ (N + N) _ (tam_extE (tam_entradaE N) k)

/-- La cota del tamaño total de la prueba de la familia. -/
def cotaInd (φ : Formula) (N : ℕ) : ℕ :=
  (15 * N + 17) * (9 * (cotaF φ (N + N) + N * (2 * cotaF φ (N + N) + 2) + 4) + 9)

/-- **La familia tiene pruebas de Frege de `15 N + 17` líneas.** -/
theorem indTrad_deriva (φ : Formula) (N : ℕ) : Frege.DerivableInSize [] (indTrad φ N) (15 * N + 17) :=
  induccion_derivable _ N

/-- **Y de tamaño total `cotaInd φ N`**, contando símbolos. -/
theorem indTrad_cota (φ : Formula) (N : ℕ) :
    ∃ L, Frege.IsProof [] L ∧ indTrad φ N ∈ L ∧ L.length = 15 * N + 17 ∧ tamProof L ≤ cotaInd φ N :=
  tamProof_induccion fun k _ => tam_instancia φ N k

/-- **`cotaInd φ` es un polinomio en `N`.** -/
theorem cotaInd_acotada (φ : Formula) : Acotada (cotaInd φ) := by
  have hd : Acotada fun N => N + N := Cerradura.suma acotada_id acotada_id
  have hC : Acotada fun N => cotaF φ (N + N) := Cerradura.composicion (cotaF_acotada φ) hd
  have h15 : Acotada fun N => 15 * N + 17 :=
    Cerradura.suma (Cerradura.producto (acotada_const 15) acotada_id) (acotada_const 17)
  have hin : Acotada fun N => cotaF φ (N + N) + N * (2 * cotaF φ (N + N) + 2) + 4 :=
    Cerradura.suma (Cerradura.suma hC (Cerradura.producto acotada_id
      (Cerradura.suma (Cerradura.producto (acotada_const 2) hC) (acotada_const 2)))) (acotada_const 4)
  exact Cerradura.producto h15 (Cerradura.suma (Cerradura.producto (acotada_const 9) hin) (acotada_const 9))

/-- El tamaño de la fórmula misma también es polinomial (cabe en su prueba). -/
theorem tam_indTrad_le (φ : Formula) (N : ℕ) : tam (indTrad φ N) ≤ cotaInd φ N := by
  obtain ⟨L, -, hm, -, ht⟩ := indTrad_cota φ N
  have : tamG (indTrad φ N) ≤ tamProof L := by
    unfold tamProof
    exact List.le_sum_of_mem (List.mem_map_of_mem hm)
  rw [← tamG_eq_tam]; omega

/-- El entorno de la instancia `k`: `x = k` y los parámetros con los bits de la entrada. -/
def entornoInd (σ : ℕ → Bool) (N k : ℕ) : Entorno := ext k (entorno (numDe σ N))

/-- **La traducción dice lo que debe**: para `φ` en la clase, la instancia `k ≤ N` vale con `σ` si y solo si `φ(k)` vale
con los parámetros que forman los bits de `σ`. -/
theorem instancia_eval {φ : Formula} (hφ : EsSb0 φ) (σ : ℕ → Bool) {N k : ℕ} (hk : k ≤ N) :
    (instancia φ N k).eval σ = true ↔ Formula.Vale φ (entornoInd σ N k) := by
  rw [← evalB_eq]
  exact trad_eval σ φ hφ (N + N) _ _ (extE_eval σ (entradaE_eval σ N) k)
    (ext_lt (entorno_lt (numDe_lt N σ)) hk)

/-- **`indTrad φ N` vale con `σ` si y solo si la instancia de inducción vale** en el número que forman los bits:
`φ(0) ∧ ∀ k < N (φ(k) → φ(k+1)) → φ(N)`. -/
theorem indTrad_eval {φ : Formula} (hφ : EsSb0 φ) (N : ℕ) (σ : ℕ → Bool) :
    (indTrad φ N).eval σ = true ↔
      (Formula.Vale φ (entornoInd σ N 0) ∧
        (∀ k < N, Formula.Vale φ (entornoInd σ N k) → Formula.Vale φ (entornoInd σ N (k + 1))) →
          Formula.Vale φ (entornoInd σ N N)) := by
  rw [indTrad, eval_induccion, eval_cadena, instancia_eval hφ σ le_rfl, instancia_eval hφ σ (Nat.zero_le N)]
  simp only [Nat.zero_add]
  have hc : (∀ j < N, (instancia φ N j).eval σ = true → (instancia φ N (j + 1)).eval σ = true) ↔
      (∀ k < N, Formula.Vale φ (entornoInd σ N k) → Formula.Vale φ (entornoInd σ N (k + 1))) := by
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    rw [instancia_eval hφ σ (by omega), instancia_eval hφ σ (by omega)]
  rw [hc]

/-- **Primera ruta**: la familia es tautología porque tiene prueba de Frege (corrección de cslib). -/
theorem indTrad_tautologia (φ : Formula) (N : ℕ) : Tautologia (indTrad φ N) := by
  intro σ
  obtain ⟨L, hL, hm, -⟩ := indTrad_deriva φ N
  exact hL.eval (by simp) _ hm

/-- **Segunda ruta, de vuelta a la aritmética**: leída con la traducción, la prueba proposicional da la instancia de
inducción para todos los parámetros de `N` bits. -/
theorem instancia_de_prueba {φ : Formula} (hφ : EsSb0 φ) (N : ℕ) (σ : ℕ → Bool)
    (h₀ : Formula.Vale φ (entornoInd σ N 0))
    (hs : ∀ k < N, Formula.Vale φ (entornoInd σ N k) → Formula.Vale φ (entornoInd σ N (k + 1))) :
    Formula.Vale φ (entornoInd σ N N) :=
  (indTrad_eval hφ N σ).mp (indTrad_tautologia φ N σ) ⟨h₀, hs⟩

/-! ## Controles -/

/-- **Sin el último paso, no es tautología**: con `P k` el átomo `k` y `N = 1`, `P 0 ∧ ⊤ → P 1` falla cuando `P 0` es
verdadero y `P 1` falso. Por la corrección de Frege, esa fórmula tampoco tiene prueba: la cadena entera hace falta. -/
theorem sin_ultimo_paso :
    ¬ ∀ σ : ℕ → Bool,
      (Proposition.imp (.and (.atom 0) (cadena (fun k => (.atom k : Proposition ℕ)) 0 0)) (.atom 1)).eval σ = true := by
  intro h
  have := h fun j => decide (j = 0)
  simp [cadena, Proposition.eval_imp_bool, Proposition.eval_and_bool] at this

theorem sin_ultimo_paso_sin_prueba (m : ℕ) :
    ¬ Frege.DerivableInSize []
      (Proposition.imp (.and (.atom 0) (cadena (fun k => (.atom k : Proposition ℕ)) 0 0)) (.atom 1)) m := by
  rintro ⟨L, hL, hm, -⟩
  exact sin_ultimo_paso fun σ => hL.eval (by simp) _ hm

/-- La fórmula `x + 1 ≰ x` está en la clase. -/
theorem sucMayor_Sb0 : EsSb0 sucMayor := by
  simp [sucMayor, EsSb0, EsSimple]

/-- Control concreto: la instancia de inducción de `x + 1 ≰ x` para `N = 2` se arma y se evalúa con `decide` en la
asignación toda falsa. -/
theorem indTrad_sucMayor_eval : evalB (fun _ => false) (indTrad sucMayor 2) = true := by decide

end EspejoInduccion
end Extraccion
end Sagitta.Map
