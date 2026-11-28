import Sagitta.Map.Decidir
import Sagitta.Map.LandauDenso

/-!
# De algoritmos a cotas: la forma del argumento de Williams, en caja negra

Sobre `Decidir` (el modelo de caja negra: `Pregunta α`, `corre`, `costo`, `vistos`, el adversario) y `LandauDenso`
(la `o` de Landau).

## Esto es un juguete, y no esquiva ninguna barrera

R. Williams probó que NEXP no está en ACC⁰ por el camino «algoritmos ⇒ cotas»: un algoritmo para la satisfactibilidad
de circuitos de una clase `C` apenas mejor que la fuerza bruta implica que una función explícita no está en `C`. Es la
única técnica conocida que esquiva las tres barreras (relativización, pruebas naturales, algebrización).

**Lo de aquí no las esquiva.** El modelo es de caja negra: el algoritmo solo pregunta valores de `f` y la prueba es un
adversario. Eso **relativiza** (Baker, Gill y Solovay, 1975; de memoria). El argumento de Williams no relativiza porque
usa tres cosas que aquí no están:

* que el algoritmo de SAT **lee el circuito** (su texto), no solo sus valores, y por eso puede ser más rápido que
  `2^n` en serio (para ACC⁰, con la representación de Yao y Beigel–Tarui y la multiplicación rápida de matrices);
* **SAT sucinto**: una fórmula de tamaño exponencial descrita por un circuito chico, que se resuelve adivinando un
  circuito testigo chico y verificándolo con el algoritmo de SAT;
* la **jerarquía de tiempo no determinista**, fina: NEXP no cabe en `NTIME(2^n / n^{ω(1)})`, y es lo que choca con la
  simulación rápida. Más el lema del testigo fácil (Impagliazzo, Kabanets y Wigderson) para pasar de «NEXP ⊆ C» a
  «los testigos tienen circuitos en C».

## Lo que sí comparte: la forma

Un algoritmo de C-SAT que hace **menos preguntas que la fuerza bruta** da una cota inferior **explícita**: un punto
que el algoritmo no mira cuando corre con la función nula define un indicador que no está en `C`. Y alcanza **cualquier**
ahorro: una pregunta menos que `|α|` basta.

## Qué se prueba

1. **El juguete** (`algoritmo_implica_cota`). Si `A` decide C-SAT (`DecideSATEn C A`), la nula está en `C` y
   `costo A nula < |α|`, hay un `x` con `indicador x ∉ C`. El núcleo es `ciego_excluido`: **todo** punto que `A` no
   mira con la nula da un indicador fuera de `C`, sin hipótesis de costo.
2. **La cota explícita** (`cota_explicita`). El punto lo calcula `ciego l A`, una función de la `Pregunta` (y de una
   lista `l` que enumera `α`): el primer punto de `l` que `A` no pregunta con la nula. Si devuelve `some x`, entonces
   `indicador x ∉ C`; si `A` es más rápido que la fuerza bruta, devuelve `some`.
3. **La contrapositiva** (`contrapositiva`). Si `C` contiene a la nula y a todos los indicadores, todo algoritmo de C-SAT
   hace al menos `|α|` preguntas con la nula. Con `C = univ` es `costo_adversario` de `Decidir`
   (`recupera_costo_adversario`), y el `g` del adversario de allá es el indicador de aquí (`indicador_eq_update`): la
   prueba de `adversario` solo evalúa en la nula y en los indicadores. Es exacta: `barrer` alcanza (`contrapositiva_justa`).
4. **Con Landau** (`ahorro_infinitas_veces`, `ahorro_o`). Con una familia `C n` sobre `Fin n → Bool` y algoritmos
   `A n` con costo a lo sumo `t n`: si `t n < 2^n` para infinitos `n`, `C` excluye un indicador explícito
   (`puntoCiego n (A n)`) para infinitos `n`; si `t ∈ o(2^n)`, para todo `n` grande. El ahorro mínimo, `t = 2^n − 1`,
   no está en `o(2^n)` (`menos_uno_no_es_o`) y alcanza igual (`familia_menos_uno`): **una** pregunta menos basta.
5. **Casos concretos** sobre `Fin 3 → Bool` (8 entradas):
   * `C` = las constantes: una pregunta decide (`constantes_rapido`), y la cota sale con el punto que calcula
     `puntoCiego` (`constantes_cota`, comprobado con `decide`);
   * `C` = a lo sumo un uno, con un punto prohibido: barrer todo salvo el prohibido decide con 7 preguntas, y el punto
     que calcula el teorema es **exactamente** el prohibido (`prohibido_cota`).
6. **Controles** (de que las hipótesis no son vacías ni sobran):
   * sin `nula ∈ C` la conclusión falla (`sin_nula_falla`): `C` = los indicadores, `A` = responder `true`;
   * con todos los indicadores no hay algoritmo rápido (`indicadores_sin_rapido`);
   * cambiar `<` por `≤` es falso (`refuta_le`), cambiar el indicador por la constante uno es falso
     (`refuta_uno`), y cambiar `o` por `O` en la versión de Landau es falso (`refuta_O`).

## Qué haría falta para la versión real, y qué hay en cslib-frontier

Buscado con `grep` en `.lake/packages/cslib-frontier` y `.lake/packages/cslib` (24 nov 2026); no lo compilé ni lo
importo.

* **Circuitos como objetos**: están. `cslib` trae `Cslib/Computability/Circuit/` (circuitos De Morgan, conteo,
  Shannon) y cslib-frontier define `ACC0` (`Computability/Circuit/Boolean/ACC0.lean`, con `AC0 ⊂ ACC0`, Razborov–Smolensky
  y la simulación de compuertas `MOD_q`).
* **C-SAT como lenguaje**: está `CircuitSAT` (`Computability/Complexity/Problems/CircuitSAT.lean`), con codificación
  de circuitos.
* **SAT sucinto y el paso de verificación de Williams**: está, y es lo más cercano a esto.
  `Computability/Complexity/Classes/AlgorithmsToLowerBounds.lean` simula en `NTIME`, con costo cargado, «adivinar un
  circuito testigo y correr un algoritmo de SAT sobre el circuito de la cláusula violada»
  (`smallWitnessLanguage_mem_NTIME`), y de ahí saca que un miembro satisfactible no tiene testigos de circuito chico
  (`exists_hard_satisfyingAssignment_of_notMem_NTIME`, `…_of_expLazyDiagonal`). Más `SuccinctVerifier.lean`.
* **La jerarquía no determinista**: solo la **gruesa**. `Hierarchy/NondeterministicExponentialTime.lean` separa
  `NTIME(2^{kn}) ⊊ NTIME(2^{en})` con `8k + 16 ≤ e`, por diagonalización perezosa (Žák). No hay jerarquía fina, la que
  distingue un ahorro de `n^{ω(1)}`.
* **Lo que falta**, según el mismo archivo lo dice: la jerarquía fina; el **lema del testigo fácil**
  (no está; `grep` solo lo encuentra mencionado como ausente); una reducción sucinta uniforme con `n + O(log n)` bits
  de índice de cláusula; y el algoritmo de ACC-SAT de Williams (hay piezas: la transformada zeta rápida de Yates en
  `Algorithms/Lean/Yates.lean`, citando a Williams 2014, Lema 4.2, y polinomios de grado bajo con Beigel–Tarui en
  `Foundations/BooleanAnalysis/LowDegree/`, pero no el algoritmo armado ni su tiempo en máquina de Turing).

## Fuentes, de memoria

R. Williams, «Nonuniform ACC circuit lower bounds», CCC 2011 y J. ACM 2014. Para el resto (Yao, Beigel–Tarui,
Impagliazzo–Kabanets–Wigderson, Žák, Baker–Gill–Solovay): de memoria y sin verificar. Las pruebas de aquí son propias y
no dependen de ninguna.
-/

namespace Sagitta.Map.Tiempo.AlgoritmosACotas

open Pregunta

variable {α : Type}

/-! ## 1. El juguete en caja negra -/

/-- **La función nula**: ninguna entrada la satisface. -/
def nula : α → Bool := fun _ => false

/-- **El indicador de `x`**: vale `true` solo en `x`. La función «simple» que la cota excluye. -/
def indicador [DecidableEq α] (x : α) : α → Bool := fun y => decide (y = x)

/-- **El adversario de `Decidir` usa este indicador**: el `g` de `adversario` es `indicador x`. -/
theorem indicador_eq_update [DecidableEq α] (x : α) :
    indicador x = Function.update (fun _ => false) x true := by
  funext y
  by_cases h : y = x
  · subst h; simp [indicador]
  · simp [indicador, h]

/-- **`A` decide C-SAT**: para toda `f` de la clase, responde `true` si y solo si `f` es satisfactible. Fuera de la
clase puede responder cualquier cosa. -/
def DecideSATEn (C : Set (α → Bool)) (A : Pregunta α) : Prop :=
  ∀ f ∈ C, corre A f = true ↔ ∃ x, f x = true

/-- Decidir para todo oráculo (`DecideExiste` de `Decidir`) es decidir C-SAT para cualquier `C`. -/
theorem decideSATEn_de_decideExiste {A : Pregunta α} (h : DecideExiste A) (C : Set (α → Bool)) :
    DecideSATEn C A := fun f _ => h f

/-- Una clase más chica es más fácil: lo que decide en `D` decide en `C ⊆ D`. -/
theorem decideSATEn_mono {C D : Set (α → Bool)} (hCD : C ⊆ D) {A : Pregunta α} (h : DecideSATEn D A) :
    DecideSATEn C A := fun f hf => h f (hCD hf)

/-- **El núcleo: un punto que no se mira da un indicador fuera de la clase.** Si `A` decide C-SAT, la nula está en `C`
y `A` no pregunta por `x` cuando corre con la nula, entonces `indicador x ∉ C`. No hace falta ninguna hipótesis de
costo. -/
theorem ciego_excluido [DecidableEq α] {C : Set (α → Bool)} {A : Pregunta α} (hA : DecideSATEn C A)
    (h0 : nula ∈ C) {x : α} (hx : x ∉ vistos A nula) : indicador x ∉ C := by
  intro hxC
  have hc : corre A nula = corre A (indicador x) :=
    corre_congr A _ _ fun j hj => by
      have hjx : j ≠ x := fun e => hx (e ▸ hj)
      simp [nula, indicador, hjx]
  have h0' : corre A nula = false := by
    cases hc0 : corre A nula
    · rfl
    · obtain ⟨j, hj⟩ := (hA _ h0).1 hc0
      simp [nula] at hj
  have h1 : corre A (indicador x) = true := (hA _ hxC).2 ⟨x, by simp [indicador]⟩
  rw [← hc, h0'] at h1
  exact Bool.false_ne_true h1

/-- **Más rápido que la fuerza bruta deja un punto sin mirar.** -/
theorem existe_no_visto [Fintype α] (A : Pregunta α) (h : costo A nula < Fintype.card α) :
    ∃ x, x ∉ vistos A nula := by
  classical
  by_contra hne
  simp only [not_exists, not_not] at hne
  have hsub : (Finset.univ : Finset α) ⊆ (vistos A nula).toFinset := fun i _ => List.mem_toFinset.2 (hne i)
  have hle : Fintype.card α ≤ costo A nula :=
    calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
      _ ≤ (vistos A nula).toFinset.card := Finset.card_le_card hsub
      _ ≤ costo A nula := List.toFinset_card_le _
  omega

/-- **Meta 1: un algoritmo más rápido que la fuerza bruta implica una cota.** Si `A` decide C-SAT con menos de `|α|`
preguntas sobre la nula, y la nula está en `C`, entonces `C` no contiene algún indicador. -/
theorem algoritmo_implica_cota [Fintype α] [DecidableEq α] {C : Set (α → Bool)} {A : Pregunta α}
    (hA : DecideSATEn C A) (h0 : nula ∈ C) (hrap : costo A nula < Fintype.card α) :
    ∃ x, indicador x ∉ C := by
  obtain ⟨x, hx⟩ := existe_no_visto A hrap
  exact ⟨x, ciego_excluido hA h0 hx⟩

/-! ### La cota es explícita: el punto lo calcula el algoritmo -/

/-- **El punto ciego**: el primer punto de la lista `l` que `A` no pregunta cuando corre con la nula. Es una función
computable de la `Pregunta`; `l` es una enumeración de `α`. -/
def ciego [DecidableEq α] (l : List α) (A : Pregunta α) : Option α :=
  l.find? fun x => decide (x ∉ vistos A nula)

theorem ciego_no_visto [DecidableEq α] {l : List α} {A : Pregunta α} {x : α} (h : ciego l A = some x) :
    x ∉ vistos A nula := by
  have := List.find?_some h
  simpa using this

theorem ciego_isSome [DecidableEq α] {l : List α} (hl : ∀ y, y ∈ l) {A : Pregunta α} {x : α}
    (hx : x ∉ vistos A nula) : ∃ y, ciego l A = some y := by
  cases h : ciego l A with
  | some y => exact ⟨y, rfl⟩
  | none =>
    rw [ciego, List.find?_eq_none] at h
    exact absurd (by simpa using h x (hl x)) hx

/-- **Meta 1, explícita.** El punto que calcula `ciego` desde el algoritmo da siempre un indicador fuera de `C`, y si
el algoritmo es más rápido que la fuerza bruta, `ciego` encuentra uno. -/
theorem cota_explicita [Fintype α] [DecidableEq α] {C : Set (α → Bool)} {A : Pregunta α}
    (hA : DecideSATEn C A) (h0 : nula ∈ C) (l : List α) :
    (∀ x, ciego l A = some x → indicador x ∉ C) ∧
      ((∀ y, y ∈ l) → costo A nula < Fintype.card α → ∃ x, ciego l A = some x ∧ indicador x ∉ C) := by
  refine ⟨fun x hx => ciego_excluido hA h0 (ciego_no_visto hx), fun hl hrap => ?_⟩
  obtain ⟨z, hz⟩ := existe_no_visto A hrap
  obtain ⟨x, hx⟩ := ciego_isSome hl hz
  exact ⟨x, hx, ciego_excluido hA h0 (ciego_no_visto hx)⟩

/-! ### La contrapositiva y el adversario de siempre -/

/-- **La contrapositiva.** Si `C` contiene a la nula y a todos los indicadores, todo algoritmo de C-SAT hace al menos
`|α|` preguntas con la nula. -/
theorem contrapositiva [Fintype α] [DecidableEq α] {C : Set (α → Bool)} (h0 : nula ∈ C)
    (hδ : ∀ x, indicador x ∈ C) {A : Pregunta α} (hA : DecideSATEn C A) :
    Fintype.card α ≤ costo A nula := by
  by_contra hlt
  obtain ⟨x, hx⟩ := algoritmo_implica_cota hA h0 (Nat.lt_of_not_le hlt)
  exact hx (hδ x)

/-- **Recupera `costo_adversario` de `Decidir`**: es la contrapositiva con `C = univ`. -/
theorem recupera_costo_adversario [Fintype α] (A : Pregunta α) (h : DecideExiste A) :
    Fintype.card α ≤ costo A (fun _ => false) := by
  classical
  exact contrapositiva (C := Set.univ) trivial (fun _ => trivial) (decideSATEn_de_decideExiste h _)

/-- **La contrapositiva no exige más de lo que el adversario usa.** La clase mínima, la nula y los indicadores, ya
obliga a `|α|` preguntas, y es mucho más chica que `univ`: el adversario de `Decidir` no necesitaba que `A` decidiera
sobre todo oráculo. -/
def nulaEIndicadores [DecidableEq α] : Set (α → Bool) := insert nula (Set.range indicador)

theorem contrapositiva_minima [Fintype α] [DecidableEq α] {A : Pregunta α} (hA : DecideSATEn nulaEIndicadores A) :
    Fintype.card α ≤ costo A nula :=
  contrapositiva (C := nulaEIndicadores) (Set.mem_insert _ _)
    (fun x => show indicador x ∈ insert nula (Set.range indicador) from Set.mem_insert_of_mem _ ⟨x, rfl⟩) hA

/-- **Y es justa**: barrer todo decide C-SAT para cualquier `C` con exactamente `|α|` preguntas sobre la nula. -/
theorem contrapositiva_justa [Fintype α] (C : Set (α → Bool)) :
    DecideSATEn C (barrer (Finset.univ : Finset α).toList) ∧
      costo (barrer (Finset.univ : Finset α).toList) nula = Fintype.card α := by
  classical
  have h := (barrer_alcanza (α := α))
  refine ⟨decideSATEn_de_decideExiste h.1 C, le_antisymm (h.2 _) ?_⟩
  exact contrapositiva (C := Set.univ) trivial (fun _ => trivial) (decideSATEn_de_decideExiste h.1 _)

/-! ## 2. La versión con Landau: alcanza cualquier ahorro -/

/-- **Las `2^n` entradas de `n` bits**, en una lista. -/
def entradas : (n : ℕ) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n + 1 => (entradas n).flatMap fun v => [Fin.cons false v, Fin.cons true v]

theorem mem_entradas : ∀ (n : ℕ) (v : Fin n → Bool), v ∈ entradas n
  | 0, v => by
    have : v = Fin.elim0 := funext fun i => i.elim0
    simp [entradas, this]
  | n + 1, v => by
    rw [entradas, List.mem_flatMap]
    refine ⟨Fin.tail v, mem_entradas n _, ?_⟩
    have hv : v = Fin.cons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
    cases h0 : v 0 <;> rw [h0] at hv <;> simp [← hv]

theorem card_entradas (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by simp

/-- **El punto ciego de un algoritmo sobre `n` bits.** -/
def puntoCiego (n : ℕ) (A : Pregunta (Fin n → Bool)) : Option (Fin n → Bool) := ciego (entradas n) A

/-- **Un `n` con ahorro da una cota explícita en ese `n`.** -/
theorem cota_en (C : Set ((Fin n → Bool) → Bool)) (A : Pregunta (Fin n → Bool)) (hA : DecideSATEn C A)
    (h0 : nula ∈ C) (hrap : costo A nula < 2 ^ n) :
    ∃ x, puntoCiego n A = some x ∧ indicador x ∉ C :=
  (cota_explicita hA h0 (entradas n)).2 (mem_entradas n) (by rwa [card_entradas])

/-- **Meta 2: un ahorro infinitas veces da una cota infinitas veces.** `C n` es la clase en `n` bits, `A n` el
algoritmo y `t n` su costo en el peor caso. Si `t n < 2^n` para infinitos `n`, para infinitos `n` el punto que calcula
`puntoCiego n (A n)` da un indicador fuera de `C n`. -/
theorem ahorro_infinitas_veces (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) (A : (n : ℕ) → Pregunta (Fin n → Bool))
    (t : ℕ → ℕ) (hA : ∀ n, DecideSATEn (C n) (A n)) (h0 : ∀ n, nula ∈ C n)
    (ht : ∀ n f, costo (A n) f ≤ t n) (hinf : ∀ N, ∃ n ≥ N, t n < 2 ^ n) :
    ∀ N, ∃ n ≥ N, ∃ x, puntoCiego n (A n) = some x ∧ indicador x ∉ C n := by
  intro N
  obtain ⟨n, hn, htn⟩ := hinf N
  exact ⟨n, hn, cota_en (C n) (A n) (hA n) (h0 n) ((ht n nula).trans_lt htn)⟩

/-- Lo de `o(2^n)` queda debajo de `2^n` desde algún punto. -/
theorem lt_de_o {t : ℕ → ℕ} (h : t ∈ o (fun n => 2 ^ n)) : ∃ N, ∀ n ≥ N, t n < 2 ^ n := by
  obtain ⟨N, hN⟩ := h 2
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
  beta_reduce at h1
  omega

/-- **Meta 2, con Landau: un ahorro de `o(2^n)` da la cota en todo `n` grande.** -/
theorem ahorro_o (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) (A : (n : ℕ) → Pregunta (Fin n → Bool))
    (t : ℕ → ℕ) (hA : ∀ n, DecideSATEn (C n) (A n)) (h0 : ∀ n, nula ∈ C n)
    (ht : ∀ n f, costo (A n) f ≤ t n) (ho : t ∈ o (fun n => 2 ^ n)) :
    ∃ N, ∀ n ≥ N, ∃ x, puntoCiego n (A n) = some x ∧ indicador x ∉ C n := by
  obtain ⟨N, hN⟩ := lt_de_o ho
  exact ⟨N, fun n hn => cota_en (C n) (A n) (hA n) (h0 n) ((ht n nula).trans_lt (hN n hn))⟩

/-- **El ahorro mínimo no está en `o(2^n)`**: `2^n − 1` es una pregunta menos y no es despreciable frente a `2^n`. La
versión «infinitas veces» lo cubre; la de `o`, no. -/
theorem menos_uno_no_es_o : (fun n => 2 ^ n - 1) ∉ o (fun n => 2 ^ n) := by
  intro h
  obtain ⟨N, hN⟩ := h 2
  have h1 := hN (N + 2) (by omega)
  have h4 : 4 ≤ 2 ^ (N + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (N + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  beta_reduce at h1
  omega

/-- **Una superpolinomial por debajo, como en Williams**: `2^n / (n + 1)` está en `o(2^n)`. En el juguete alcanza
mucho menos, pero este es el orden de ahorro de la forma `2^n / n^{ω(1)}`, aquí con `n` en vez de `n^{ω(1)}`. -/
theorem dividido_es_o : (fun n => 2 ^ n / (n + 1)) ∈ o (fun n => 2 ^ n) := by
  intro c
  refine ⟨c, fun n hn => ?_⟩
  beta_reduce
  calc c * (2 ^ n / (n + 1)) ≤ (n + 1) * (2 ^ n / (n + 1)) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2 ^ n := Nat.mul_div_le _ _

/-! ### El ahorro mínimo, realizado: barrer todo salvo un punto prohibido -/

/-- **La clase con un punto prohibido** `p`: las funciones que valen `false` en `p`. -/
def sinPunto {β : Type} (p : β) : Set (β → Bool) := {f | f p = false}

/-- **Barrer todo salvo `p`.** -/
def barrerSalvo [DecidableEq α] (l : List α) (p : α) : Pregunta α := barrer (l.filter fun x => decide (x ≠ p))

theorem barrerSalvo_decide [DecidableEq α] {l : List α} (hl : ∀ y, y ∈ l) (p : α) :
    DecideSATEn (sinPunto p) (barrerSalvo l p) := by
  intro f hf
  rw [barrerSalvo, corre_barrer]
  constructor
  · rintro ⟨x, -, hx⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    have hxp : x ≠ p := fun e => by simp [sinPunto, ← e, hx] at hf
    exact ⟨x, List.mem_filter.2 ⟨hl x, by simpa using hxp⟩, hx⟩

theorem costo_barrerSalvo_lt [DecidableEq α] {l : List α} (hl : ∀ y, y ∈ l) (p : α) (f : α → Bool) :
    costo (barrerSalvo l p) f < l.length := by
  have h1 := costo_barrer f (l.filter fun x => decide (x ≠ p))
  have h2 : (l.filter fun x => decide (x ≠ p)).length < l.length :=
    List.length_filter_lt_length_iff_exists.2 ⟨p, hl p, by simp⟩
  exact h1.trans_lt h2

theorem length_entradas : ∀ n : ℕ, (entradas n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    rw [entradas, List.length_flatMap, pow_succ]
    have : ∀ l : List (Fin n → Bool),
        (l.map fun v => ([Fin.cons false v, Fin.cons true v] : List (Fin (n + 1) → Bool)).length).sum =
          l.length * 2 := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp at ih ⊢; omega
    rw [this, length_entradas n]

/-- La entrada toda en `false`, el punto prohibido de la familia. -/
def ceros (n : ℕ) : Fin n → Bool := fun _ => false

/-- **Control: el ahorro mínimo `t = 2^n − 1` se realiza y la cota sale en todo `n`.** La clase prohíbe `ceros n`;
barrer lo demás cuesta `2^n − 1`, que no está en `o(2^n)`; y el punto que calcula el teorema da un indicador fuera
de la clase. -/
theorem familia_menos_uno :
    (∀ n, DecideSATEn (sinPunto (ceros n)) (barrerSalvo (entradas n) (ceros n))) ∧
      (∀ n f, costo (barrerSalvo (entradas n) (ceros n)) f ≤ 2 ^ n - 1) ∧
      (fun n => 2 ^ n - 1) ∉ o (fun n => 2 ^ n) ∧
      ∀ N, ∃ n ≥ N, ∃ x, puntoCiego n (barrerSalvo (entradas n) (ceros n)) = some x ∧
        indicador x ∉ sinPunto (ceros n) := by
  have hdec := fun n => barrerSalvo_decide (mem_entradas n) (ceros n)
  have hcost : ∀ n f, costo (barrerSalvo (entradas n) (ceros n)) f ≤ 2 ^ n - 1 := fun n f => by
    have := costo_barrerSalvo_lt (mem_entradas n) (ceros n) f
    rw [length_entradas] at this
    omega
  refine ⟨hdec, hcost, menos_uno_no_es_o, ?_⟩
  apply ahorro_infinitas_veces _ _ (fun n => 2 ^ n - 1) hdec (fun n => rfl) hcost
  intro N
  exact ⟨N, le_rfl, by have : 0 < 2 ^ N := Nat.two_pow_pos N; omega⟩

/-! ## 3. Casos concretos sobre `Fin 3 → Bool` -/

/-- La entrada `000`. -/
def x000 : Fin 3 → Bool := ceros 3

/-- **Las constantes.** -/
def constantes {β : Type} : Set (β → Bool) := {f | ∀ x y, f x = f y}

/-- **El algoritmo de una pregunta**: mira `000` y responde lo que vio. Es `verificar` de `Decidir`. -/
def unaPregunta : Pregunta (Fin 3 → Bool) := verificar x000

/-- **Control: con las constantes hay un algoritmo de una pregunta.** -/
theorem constantes_rapido :
    DecideSATEn constantes unaPregunta ∧ ∀ f, costo unaPregunta f = 1 := by
  refine ⟨fun f hf => ?_, fun f => rfl⟩
  simp only [unaPregunta, verificar, corre]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨x, hx⟩ => by rw [hf x000 x]; exact hx⟩

theorem nula_constante {β : Type} : (nula : β → Bool) ∈ constantes := fun _ _ => rfl

/-- **La cota con las constantes**, por el teorema: el punto que calcula `puntoCiego` da un indicador no constante. -/
theorem constantes_cota : ∃ x, puntoCiego 3 unaPregunta = some x ∧ indicador x ∉ constantes :=
  cota_en constantes unaPregunta constantes_rapido.1 nula_constante (by rw [constantes_rapido.2]; norm_num)

/-- El punto que sale: el primero de la enumeración que no es `000`. -/
def x100 : Fin 3 → Bool := Fin.cons true (ceros 2)

/-- **Lo mismo, calculado**: `puntoCiego` devuelve `100`, y su indicador no es constante (comprobado con `decide`). -/
theorem constantes_cota_decide :
    puntoCiego 3 unaPregunta = some x100 ∧ ¬ ∀ x y, indicador x100 x = indicador x100 y := by
  decide

/-- **A lo sumo un uno, con `000` prohibido.** -/
def unoSalvo : Set ((Fin 3 → Bool) → Bool) :=
  {f | f x000 = false ∧ ∀ x y, f x = true → f y = true → x = y}

theorem unoSalvo_sub : unoSalvo ⊆ sinPunto x000 := fun _ hf => hf.1

/-- **Control: barrer todo salvo `000` decide con 7 preguntas, y el punto que calcula el teorema es el prohibido.** -/
theorem prohibido_cota :
    DecideSATEn unoSalvo (barrerSalvo (entradas 3) x000) ∧
      (∀ f, costo (barrerSalvo (entradas 3) x000) f ≤ 7) ∧
      puntoCiego 3 (barrerSalvo (entradas 3) x000) = some x000 ∧ indicador x000 ∉ unoSalvo := by
  have hdec := decideSATEn_mono unoSalvo_sub (barrerSalvo_decide (mem_entradas 3) x000)
  have hcost : ∀ f, costo (barrerSalvo (entradas 3) x000) f ≤ 7 := fun f => by
    have := costo_barrerSalvo_lt (mem_entradas 3) x000 f
    rw [length_entradas] at this
    omega
  have hp : puntoCiego 3 (barrerSalvo (entradas 3) x000) = some x000 := by decide
  have h0 : (nula : (Fin 3 → Bool) → Bool) ∈ unoSalvo := ⟨rfl, fun _ _ h => by simp [nula] at h⟩
  exact ⟨hdec, hcost, hp, (cota_explicita hdec h0 (entradas 3)).1 _ hp⟩

/-! ## 4. Controles -/

/-- **Sin `nula ∈ C` la conclusión falla.** Con `C` = los indicadores, responder `true` sin preguntar decide C-SAT con
0 preguntas, y todos los indicadores están en `C`. -/
theorem sin_nula_falla [Fintype α] [DecidableEq α] [Nonempty α] :
    DecideSATEn (Set.range (indicador (α := α))) (.resp true) ∧
      costo (.resp true : Pregunta α) nula < Fintype.card α ∧ ∀ x, indicador x ∈ Set.range (indicador (α := α)) := by
  refine ⟨?_, by simp [costo, vistos, Fintype.card_pos], fun x => ⟨x, rfl⟩⟩
  rintro f ⟨x, rfl⟩
  simp only [corre, true_iff]
  exact ⟨x, by simp [indicador]⟩

/-- **El enunciado sin `nula ∈ C` es falso** (refuta el mutante 1). -/
theorem refuta_sin_nula :
    ¬ ∀ (C : Set ((Fin 3 → Bool) → Bool)) (A : Pregunta (Fin 3 → Bool)),
      DecideSATEn C A → costo A nula < 8 → ∃ x, indicador x ∉ C := by
  intro h
  obtain ⟨hA, -, hδ⟩ := sin_nula_falla (α := Fin 3 → Bool)
  obtain ⟨x, hx⟩ := h _ _ hA (by simp [costo, vistos])
  exact hx (hδ x)

/-- **Con todos los indicadores no hay algoritmo rápido.** -/
theorem indicadores_sin_rapido [Fintype α] [DecidableEq α] :
    ¬ ∃ A : Pregunta α, DecideSATEn nulaEIndicadores A ∧ costo A nula < Fintype.card α := by
  rintro ⟨A, hA, hlt⟩
  exact absurd (contrapositiva_minima hA) (Nat.not_le_of_lt hlt)

/-- **Cambiar `<` por `≤` es falso** (refuta el mutante 2): barrer cuesta `|α|` y `univ` tiene todos los indicadores. -/
theorem refuta_le :
    ¬ ∀ (C : Set ((Fin 3 → Bool) → Bool)) (A : Pregunta (Fin 3 → Bool)),
      DecideSATEn C A → nula ∈ C → costo A nula ≤ Fintype.card (Fin 3 → Bool) → ∃ x, indicador x ∉ C := by
  intro h
  obtain ⟨hA, hc⟩ := contrapositiva_justa (α := Fin 3 → Bool) Set.univ
  obtain ⟨x, hx⟩ := h _ _ hA trivial hc.le
  exact hx trivial

/-- **Cambiar el indicador por la constante uno es falso** (refuta el mutante 3): las constantes tienen un algoritmo
de una pregunta y contienen a la constante uno. -/
theorem refuta_uno :
    ¬ ∀ (C : Set ((Fin 3 → Bool) → Bool)) (A : Pregunta (Fin 3 → Bool)),
      DecideSATEn C A → nula ∈ C → costo A nula < 8 → (fun _ => true) ∉ C := by
  intro h
  exact h constantes unaPregunta constantes_rapido.1 nula_constante (by rw [constantes_rapido.2]; norm_num)
    (fun _ _ => rfl)

/-- **Cambiar `o` por `O` es falso** (refuta el mutante 4): barrer cuesta `2^n`, que está en `O(2^n)`, y con
`C n = univ` ningún indicador queda afuera. -/
theorem refuta_O :
    ¬ ∀ (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) (A : (n : ℕ) → Pregunta (Fin n → Bool)) (t : ℕ → ℕ),
      (∀ n, DecideSATEn (C n) (A n)) → (∀ n, nula ∈ C n) → (∀ n f, costo (A n) f ≤ t n) →
        t ∈ O (fun n => 2 ^ n) → ∃ N, ∀ n ≥ N, ∃ x, indicador x ∉ C n := by
  intro h
  obtain ⟨N, hN⟩ := h (fun _ => Set.univ) (fun n => barrer (Finset.univ : Finset (Fin n → Bool)).toList)
    (fun n => 2 ^ n) (fun n => (contrapositiva_justa _).1) (fun _ => trivial)
    (fun n f => by have := (barrer_alcanza (α := Fin n → Bool)).2 f; simpa using this)
    ⟨1, 0, fun n _ => by simp⟩
  obtain ⟨x, hx⟩ := hN N le_rfl
  exact hx trivial

end Sagitta.Map.Tiempo.AlgoritmosACotas
