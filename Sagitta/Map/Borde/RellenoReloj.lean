import Sagitta.Map.Borde.TresInterruptores
import Sagitta.Map.Borde.UniversalDiagonal
import Sagitta.Map.Borde.RelojDeLadner
import Sagitta.Map.Informacion.Homogeneidad

/-!
# El relleno traslada el trabajo, y su control cuesta un reloj

El paso «el relleno traslada el trabajo y su control cuesta un reloj» de las notas del proyecto («El fractal de SAT»), sección «La
conservación del trabajo con los interruptores: cuantizado contra denso». José (25 nov 2026) juntó las leyes de
conservación de Sagitta con los interruptores de Feder–Vardi y la ley que salió fue esta:

> con plantilla finita y sin reloj, el trabajo viene en cuantos, 0 o 1 (dicotomía); al ganar un reloj, el trabajo se
> puede trasladar y diluir en el eje del tamaño, el espectro se vuelve denso y aparece el medio (Ladner).

Es la ley de las notas del proyecto (`ConservacionTrabajo.lean`: lo que la consulta no paga lo pagó el llenado; la memoria
traslada el trabajo) puesta en el eje del tamaño de la entrada: el relleno no destruye trabajo, cambia la unidad con que
se mide. Y la de la CHT (`Homogeneidad.lean`: el reloj se paga en memoria, `ley_cubo_reloj`): diluir el trabajo en
algunos largos y no en otros obliga a consultar un reloj.

## La tabla

| pieza                                         | papel                                                                  |
|-----------------------------------------------|------------------------------------------------------------------------|
| `relleno g L` (§ 1)                           | trasladar: el mismo trabajo, medido contra una entrada más larga       |
| `relleno_equivalente`                         | con `g` polinomial, `L ≡ₚ relleno g L`: el trabajo se conserva          |
| `traslacion`, `traslacion_exponencial`        | Hartmanis–Stearns: `T(n)` se vuelve `T(g⁻¹(m)) + p(m)`; `2^n` → lineal |
| `trabajo_no_se_destruye`                      | en cada entrada rellenada se paga lo mismo que antes, más la guardia   |
| `diluido A S` (§ 2)                           | diluir: `A` encendido solo en los largos de `S` (el `L_S` de Ladner)   |
| `reloj_de_diluido`                            | decidir `L_S` en P exige decidir `|x| ∈ S` en P: consultar un reloj     |
| `reloj_de_dobles`, `dobles_estados_reloj`     | B4: el reloj de los bloques dobles no es memoria finita; `c` bits pagan `2^c` |
| `Cuantizado`, `Denso` (§ 3)                   | 0 o 1 contra espectro denso                                            |
| `medio_de_denso`, `denso_no_cuantizado`       | con P ≠ NP, denso y con los dos tipos ⟹ hay medio ⟹ no cuantizado      |
| `denso_NP`, `denso_de_captura`                | Ladner–Schöning de cslib-frontier: NP es denso, y toda clase que lo captura |
| `AdmiteReloj` (§ 4)                           | la clase se cierra bajo «encender solo en las palabras de un `G ∈ P`» |
| `medio_de_reloj`                              | reloj ⟹ se puede diluir ⟹ aparece el medio (Ladner hacia abajo)       |
| `InterruptorEsReloj`                          | la lectura «apagar un interruptor da un reloj», con nombre             |
| `interruptorEsReloj_de_FV`, `apagado_denso`   | con Feder–Vardi la lectura ya sale: lo apagado tiene reloj y es denso  |
| `encendido_sin_reloj`, `encendido_no_denso`   | con BZ y P ≠ NP, MMSNP no tiene reloj ni es denso                      |

## Lo que se prueba

**Probado** (sin `sorry`, axiomas `propext`, `Classical.choice`, `Quot.sound`):

* (1) **El relleno conserva el trabajo**. `relleno g L = {frame x ++ 1^(g |x|) | x ∈ L}` (el marco de cslib-frontier
  separa la palabra del relleno; el largo total es `ℓ_g(n) = 2n + 1 + g(n)`, `length_rellenar`). Si `g` es polinomial en
  unario, las **dos reducciones** son de Karp polinomiales (`reduce_a_relleno`, `reduce_de_relleno`), con la única
  condición de que `L` no sea `Σ*` (`relleno_univ_no_reduce` muestra que hace falta), y por lo tanto se conservan «en
  P», «en NP», «NP-completo» e «intermedio» (`relleno_intermedio`). La **traslación cuantitativa** (`traslacion`) va en
  un modelo de costo aditivo (no en las máquinas de cslib): si `L` se decide en tiempo `T(n)` con `T` monótona y la
  guardia cuesta `p(m)`, el rellenado se decide en `p(m) + T(g⁻¹(m))`, con `g⁻¹(m)` el mayor `n` con `ℓ_g(n) ≤ m`. Con
  `g(n) = 2^n` y `T(n) = 2^n`, eso es `p(m) + m + 1` (`traslacion_exponencial`): el tiempo exponencial, medido contra la
  entrada rellenada, se vuelve polinomial. Y en cada entrada rellenada el costo es exactamente el de antes más la guardia
  (`trabajo_no_se_destruye`): el trabajo no se destruye, cambia la unidad.
* (2) **Diluir cuesta un reloj**. `diluido A S = {x ∈ A | |x| ∈ S}`. Si `A` tiene **testigos uniformes** (una familia
  polinomial `w n ∈ A` de largo `n`, desde algún `N`), decidir `diluido A S` en P da una función `c`, polinomial en
  unario, que acierta `n ∈ S` desde `N` (`reloj_de_diluido`): un reloj, porque solo mira el largo (`largos_de_diluido`,
  con `largos_en_P_iff` de B4). SAT enmarcado tiene testigos uniformes (`testigos_sat`), y SAT por bloques de B4 es un
  `diluido` (`porBloques_eq_diluido`, `porBloquesReloj_eq_diluido`). Con los bloques dobles, `reloj_de_dobles`: si SAT
  diluido en ellos estuviera en P, habría un reloj polinomial para sus largos, y ningún autómata finito lo es
  (`dobles_no_regular` de B4); un autómata con `c` bits de reloj y memoria `σ₀` (estados `σ₀ × Fin 2^c`, el
  `card_reloj_bits` de la CHT) que acierta hasta `2^(m+1)` necesita `2^m ≤ |σ₀| · 2^c` (`dobles_estados_reloj`). Las
  vueltas: con `A ∈ P` (o NP) y un reloj polinomial exacto, `diluido A S ∈ P` (o NP) (`diluido_en_P`, `diluido_en_NP`).
* (3) **Cuantizado contra denso**, en abstracto. `Cuantizado F` es la dicotomía de `TresInterruptores.lean`. `Denso F`:
  para `A <ₚ B` en `F` con `B ∉ P` hay `C ∈ F` con `A <ₚ C <ₚ B`. La condición `B ∉ P` es necesaria
  (`denso_sin_condicion_falso`: entre `∅` y `{[true]}`, los dos en NP, no hay nada). Con P ≠ NP, una clase densa con un
  problema no trivial en P y uno NP-completo tiene un intermedio (`medio_de_denso`) y no es cuantizada
  (`denso_no_cuantizado`). La densidad de NP **no es hipótesis**: es `exists_mem_NP_between_of_notMem_P` de
  cslib-frontier (Ladner 1975, Schöning 1982) (`denso_NP`), y pasa a toda clase dentro de NP que lo capture
  (`denso_de_captura`).
* (4) **El interruptor como reloj**. `AdmiteReloj F`: para `B ∈ F` y `G ∈ P`, «`B` encendido solo fuera de `G`»
  (`G.ite ∅ B`, la forma de Ladner por huecos de cslib-frontier, con un `G` de palabras en vez de largos) es equivalente
  a algo de `F`. `medio_de_reloj`: una clase con reloj que tenga un NP-completo tiene intermedios si P ≠ NP
  (`exists_mem_P_ite_empty_lt` de cslib-frontier); es «reloj ⟹ se puede diluir ⟹ aparece el medio», y
  `denso_abajo_de_reloj` da la densidad hacia abajo.

**Hipótesis con nombre**:

* `InterruptorEsReloj frag`: apagar cualquier interruptor da una clase con reloj. **Es una lectura de los Teos. 1 a 3
  de Feder–Vardi, no un teorema de ellos**: Feder y Vardi prueban que las tres esquinas capturan NP salvo equivalencia;
  no hablan de relojes. Lo que sí se prueba es que, con las capturas de Feder–Vardi como hipótesis (`FederVardi` de
  `TresInterruptores.lean`), la lectura **sale**: `interruptorEsReloj_de_FV`. O sea que la hipótesis nueva no agrega
  supuestos; agrega una manera de leer los que ya estaban. Su consecuencia: `interruptor_reloj_medio` (apagado y con un
  NP-completo ⟹ intermedios si P ≠ NP), `apagado_denso`.
* Bulatov–Zhuk (`BZ`) y `FederVardi`, de `TresInterruptores.lean`, para el lado encendido: con ellos y P ≠ NP, la
  clase encendida **no tiene reloj** (`encendido_sin_reloj`) y **no es densa** (`encendido_no_denso`).
* Ladner **no** es hipótesis: viene de cslib-frontier (`Ladner/Density.lean`).

**Lo que NO se prueba**:

* Que **sin reloj no haya medio**. La dirección «una clase sin reloj es cuantizada» es Bulatov–Zhuk (2017) para los
  CSP de plantilla finita, y aquí entra como la hipótesis `BZ`, no como consecuencia de no tener reloj. `AdmiteReloj` es
  una propiedad de cerradura, no una sintaxis: no se prueba que una clase sin esa cerradura tenga dicotomía.
* La traslación de Hartmanis–Stearns en las máquinas de cslib. La forma cuantitativa de aquí es un modelo de costo
  aditivo donde el costo de la guardia `p` es un dato. La versión con máquinas está en cslib-frontier
  (`Padding/Translation.lean`, `DTIME_comp_subset_of_subset`, Fortnow–Santhanam), sin compilar en este proyecto y no
  importada.
* Que `satMarco ∈ NP` (como en B4, no está probado en Sagitta): por eso `diluido_en_NP` pide `A ∈ NP`.
* **Todo es condicional a P ≠ NP: organiza, no decide.** Si P = NP, todas las clases dentro de NP son cuantizadas de
  balde (`dicotomia_de_P_eq_NP`) y la densidad de Ladner es vacía (no hay `B ∈ NP \ P`).

## Antecedentes

Hartmanis y Stearns, Trans. AMS 117, 1965 (traslación por relleno); Ladner, J. ACM 22(1), 1975; Schöning, TCS 18, 1982;
Feder y Vardi, SIAM J. Comput. 28(1), 1998; Bulatov, FOCS 2017; Zhuk, J. ACM 67(5), 2020. Las referencias de Ladner,
Feder–Vardi y Bulatov–Zhuk son las de `TresInterruptores.lean` y `Ladner/Density.lean`. La de Hartmanis–Stearns está
verificada en Crossref (en la bibliografía de los informes de Sagitta), pero no se leyó: el nombre «traslación de
Hartmanis–Stearns» es el del pedido, y no se verificó en qué artículo aparece por primera vez el lema de traslación.
-/

namespace Sagitta.Map.Borde.RellenoReloj

open Turing.MultiTapeTM Cslib.Complexity
open Sagitta.Map.Borde.TresInterruptores
open Sagitta.Map.Borde.FractalSAT (Intermedio)

/-! ## 1. El relleno conserva el trabajo -/

/-- **Rellenar** `x`: enmarcarlo y agregar `g |x|` unos. El marco separa la palabra del relleno. -/
def rellenar (g : ℕ → ℕ) (x : List Bool) : List Bool := frame x ++ List.replicate (g x.length) true

/-- **El lenguaje rellenado** `pad_g(L) = {x # 1^(g |x|) | x ∈ L}`. -/
def relleno (g : ℕ → ℕ) (L : Lenguaje) : Lenguaje := {y | y = rellenar g (unframe y) ∧ unframe y ∈ L}

variable {g : ℕ → ℕ} {L : Lenguaje}

@[simp] theorem unframe_rellenar (g : ℕ → ℕ) (x : List Bool) : unframe (rellenar g x) = x :=
  unframe_frame_append _ _

/-- El largo rellenado: `ℓ_g(n) = 2n + 1 + g(n)`. -/
def largoRelleno (g : ℕ → ℕ) (n : ℕ) : ℕ := 2 * n + 1 + g n

theorem length_rellenar (g : ℕ → ℕ) (x : List Bool) : (rellenar g x).length = largoRelleno g x.length := by
  simp [rellenar, largoRelleno, length_frame]

theorem rellenar_mem_iff {x : List Bool} : rellenar g x ∈ relleno g L ↔ x ∈ L := by
  simp [relleno]

theorem mem_relleno_iff {y : List Bool} : y ∈ relleno g L ↔ ∃ x ∈ L, y = rellenar g x := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, h1⟩
  · rintro ⟨x, hx, rfl⟩
    exact rellenar_mem_iff.2 hx

/-- **La ida**: `L ≤ₚ relleno g L`, rellenando. -/
theorem reduce_a_relleno (hg : ComputableInPolyTime g encUnary encUnary) : Reduce L (relleno g L) :=
  ⟨rellenar g, by unfold rellenar; fun_prop, fun _ => rellenar_mem_iff.symm⟩

/-- Desrellenar: si la entrada tiene la forma correcta, la palabra enmarcada; si no, un `x₀ ∉ L` fijo. -/
def desrellenar (g : ℕ → ℕ) (x₀ y : List Bool) : List Bool :=
  if decide (y = rellenar g (unframe y)) then unframe y else x₀

/-- **La vuelta**: `relleno g L ≤ₚ L`, si `L` tiene un no-miembro `x₀`. -/
theorem reduce_de_relleno (hg : ComputableInPolyTime g encUnary encUnary) {x₀ : List Bool} (hx₀ : x₀ ∉ L) :
    Reduce (relleno g L) L := by
  refine ⟨desrellenar g x₀, by unfold desrellenar rellenar; fun_prop, fun y => ?_⟩
  unfold desrellenar
  split_ifs with h
  · have h : y = rellenar g (unframe y) := by simpa using h
    exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
  · have h : ¬ y = rellenar g (unframe y) := by simpa using h
    exact ⟨fun h' => absurd h'.1 h, fun h' => absurd h' hx₀⟩

/-- **El relleno polinomial es una equivalencia polinomial**, salvo para `Σ*`. -/
theorem relleno_equivalente (hg : ComputableInPolyTime g encUnary encUnary) (hL : ∃ x₀, x₀ ∉ L) :
    Equivalentes L (relleno g L) :=
  ⟨reduce_a_relleno hg, reduce_de_relleno hg hL.choose_spec⟩

/-- El control: para `Σ*` la vuelta no existe (`[]` no es un rellenado). -/
theorem relleno_univ_no_reduce : ¬ Reduce (relleno g Set.univ) Set.univ := by
  rintro ⟨f, -, hf⟩
  obtain ⟨h1, -⟩ := (hf []).2 trivial
  have h2 : (rellenar g (unframe [])).length = 0 := by rw [← h1]; rfl
  rw [length_rellenar] at h2
  unfold largoRelleno at h2
  omega

theorem relleno_P_iff (hg : ComputableInPolyTime g encUnary encUnary) (hL : ∃ x₀, x₀ ∉ L) :
    L ∈ Cslib.Complexity.P encBits ↔ relleno g L ∈ Cslib.Complexity.P encBits :=
  (relleno_equivalente hg hL).enP_iff

theorem relleno_NP_iff (hg : ComputableInPolyTime g encUnary encUnary) (hL : ∃ x₀, x₀ ∉ L) :
    L ∈ Cslib.Complexity.NP encBits ↔ relleno g L ∈ Cslib.Complexity.NP encBits :=
  (relleno_equivalente hg hL).enNP_iff

theorem relleno_completo_iff (hg : ComputableInPolyTime g encUnary encUnary) (hL : ∃ x₀, x₀ ∉ L) :
    NPComplete encBits L ↔ NPComplete encBits (relleno g L) :=
  (relleno_equivalente hg hL).completo_iff

/-- **El relleno polinomial conserva el medio.** Un intermedio no es `Σ*` (que está en P), así que la condición de
`relleno_equivalente` sale sola. -/
theorem relleno_intermedio (hg : ComputableInPolyTime g encUnary encUnary) (h : Intermedio L) :
    Intermedio (relleno g L) := by
  have hL : ∃ x₀, x₀ ∉ L := by
    by_contra hc
    push Not at hc
    exact h.2.1 (Set.eq_univ_of_forall hc ▸ univ_mem_P)
  exact (relleno_equivalente hg hL).intermedio_iff.1 h

/-! ### La traslación, en forma cuantitativa (modelo de costo aditivo) -/

/-- **Un decisor con costo**: la respuesta y lo que cuesta en cada entrada. El modelo es aditivo (la composición suma
costos) y **no** es el de las máquinas de cslib. -/
structure Decisor where
  responde : List Bool → Bool
  costo : List Bool → ℕ

/-- `D` decide `L` en tiempo `T`: acierta siempre, y en `x` cuesta a lo sumo `T |x|`. -/
def Decisor.DecideEn (D : Decisor) (L : Lenguaje) (T : ℕ → ℕ) : Prop :=
  ∀ x, (x ∈ L ↔ D.responde x = true) ∧ D.costo x ≤ T x.length

theorem Decisor.DecideEn.mono {D : Decisor} {T T' : ℕ → ℕ} (h : D.DecideEn L T) (hT : ∀ n, T n ≤ T' n) :
    D.DecideEn L T' := fun x => ⟨(h x).1, (h x).2.trans (hT _)⟩

/-- **La inversa por abajo** de `ℓ_g`: el mayor `n ≤ m` con `ℓ_g(n) ≤ m` (`0` si no hay). -/
def inversa (g : ℕ → ℕ) (m : ℕ) : ℕ := Nat.findGreatest (fun n => largoRelleno g n ≤ m) m

theorem le_inversa {n m : ℕ} (h : largoRelleno g n ≤ m) : n ≤ inversa g m :=
  Nat.le_findGreatest (by unfold largoRelleno at h; omega) h

/-- **El decisor del rellenado**: la guardia, que cuesta `p |y|`, y, si pasa, el decisor de `L` sobre lo desenmarcado. -/
def Decisor.rellenado (D : Decisor) (g p : ℕ → ℕ) : Decisor where
  responde y := decide (y = rellenar g (unframe y)) && D.responde (unframe y)
  costo y := p y.length + if y = rellenar g (unframe y) then D.costo (unframe y) else 0

/-- **El trabajo no se destruye**: en la entrada rellenada se paga exactamente lo de antes, más la guardia. -/
theorem trabajo_no_se_destruye (D : Decisor) (p : ℕ → ℕ) (x : List Bool) :
    (D.rellenado g p).costo (rellenar g x) = p (largoRelleno g x.length) + D.costo x := by
  simp [Decisor.rellenado, length_rellenar]

/-- **La traslación (Hartmanis–Stearns), cuantitativa**: si `L` se decide en tiempo `T(n)` (monótona) y la guardia
cuesta `p(m)`, el rellenado se decide en tiempo `p(m) + T(g⁻¹(m))`. -/
theorem traslacion {D : Decisor} {T p : ℕ → ℕ} (hD : D.DecideEn L T) (hT : Monotone T) :
    (D.rellenado g p).DecideEn (relleno g L) (fun m => p m + T (inversa g m)) := by
  intro y
  refine ⟨?_, ?_⟩
  · simp only [relleno, Set.mem_ofPred_eq, Decisor.rellenado, Bool.and_eq_true, decide_eq_true_eq]
    rw [(hD (unframe y)).1]
  · simp only [Decisor.rellenado]
    split_ifs with h
    · have hlen : largoRelleno g (unframe y).length ≤ y.length := by
        rw [← length_rellenar]; exact (congrArg List.length h).ge
      have := hT (le_inversa hlen)
      have := (hD (unframe y)).2
      omega
    · omega

/-- Con relleno exponencial, `2^(g⁻¹(m)) ≤ m + 1`. -/
theorem pow_inversa_le (m : ℕ) : 2 ^ inversa (fun n => 2 ^ n) m ≤ m + 1 := by
  by_cases h0 : largoRelleno (fun n => 2 ^ n) 0 ≤ m
  · have := Nat.findGreatest_spec (P := fun n => largoRelleno (fun n => 2 ^ n) n ≤ m)
      (Nat.zero_le m) h0
    unfold inversa
    simp only [largoRelleno] at this ⊢
    omega
  · have : inversa (fun n => 2 ^ n) m = 0 := by
      unfold inversa
      rw [Nat.findGreatest_eq_zero_iff]
      intro n _ _ hn
      simp only [largoRelleno] at h0 hn
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [this]
    omega

/-- **El trabajo exponencial, medido contra la entrada rellenada exponencialmente, es lineal más la guardia.** -/
theorem traslacion_exponencial {D : Decisor} {p : ℕ → ℕ} (hD : D.DecideEn L (fun n => 2 ^ n)) :
    (D.rellenado (fun n => 2 ^ n) p).DecideEn (relleno (fun n => 2 ^ n) L) (fun m => p m + (m + 1)) :=
  (traslacion hD (fun _ _ h => Nat.pow_le_pow_right (by norm_num) h)).mono fun m => by
    have := pow_inversa_le m
    omega

/-! ## 2. Diluir cuesta un reloj -/

/-- **`A` diluido en `S`**: encendido solo en los largos de `S` (el `L_S` de Ladner). -/
def diluido (A : Lenguaje) (S : Set ℕ) : Lenguaje := {y | y.length ∈ S ∧ y ∈ A}

/-- **Testigos uniformes**: una familia polinomial (en unario) de miembros de `A`, uno de cada largo desde `N`. -/
def TestigosUniformes (A : Lenguaje) (N : ℕ) : Prop :=
  ∃ w : ℕ → List Bool, ComputableInPolyTime w encUnary encBits ∧ ∀ n, N ≤ n → (w n).length = n ∧ w n ∈ A

/-- **Decidir `L_S` en P exige un reloj para `S`**: con testigos uniformes, `c n = [w n ∈ L_S]` es polinomial en
unario y acierta `n ∈ S` desde `N`. Solo mira el largo: es la consulta de un reloj. -/
theorem reloj_de_diluido {A : Lenguaje} {S : Set ℕ} {N : ℕ} (hw : TestigosUniformes A N)
    (hP : diluido A S ∈ Cslib.Complexity.P encBits) :
    ∃ c : ℕ → Bool, ComputableInPolyTime c encUnary encBool ∧ ∀ n, N ≤ n → (c n = true ↔ n ∈ S) := by
  obtain ⟨w, hwc, hw⟩ := hw
  obtain ⟨f, hf, hfL⟩ := hP
  refine ⟨fun n => f (w n), by fun_prop, fun n hn => ?_⟩
  obtain ⟨hlen, hmem⟩ := hw n hn
  rw [← hfL]
  simp [diluido, hlen, hmem]

/-- **En la moneda de B4**: el filtro de largos del reloj está en P (`largos_en_P_iff`) y coincide con `S` desde `N`. -/
theorem largos_de_diluido {A : Lenguaje} {S : Set ℕ} {N : ℕ} (hw : TestigosUniformes A N)
    (hP : diluido A S ∈ Cslib.Complexity.P encBits) :
    ∃ S' : Set ℕ, {y : List Bool | y.length ∈ S'} ∈ Cslib.Complexity.P encBits ∧ ∀ n, N ≤ n → (n ∈ S' ↔ n ∈ S) := by
  obtain ⟨c, hc, hcS⟩ := reloj_de_diluido hw hP
  exact ⟨{n | c n = true}, (RelojDeLadner.largos_en_P_iff c).2 hc, hcS⟩

/-- La vuelta en P: con `A ∈ P` y un reloj polinomial exacto, `L_S ∈ P`. -/
theorem diluido_en_P {A : Lenguaje} {S : Set ℕ} (hA : A ∈ Cslib.Complexity.P encBits) {c : ℕ → Bool}
    (hc : ComputableInPolyTime c encUnary encBool) (hcS : ∀ n, c n = true ↔ n ∈ S) :
    diluido A S ∈ Cslib.Complexity.P encBits := by
  obtain ⟨f, hf, hfA⟩ := hA
  refine ⟨fun y => c y.length && f y, by fun_prop, fun y => ?_⟩
  simp [diluido, hcS, hfA]

/-- La vuelta en NP: con `A ∈ NP` y un reloj polinomial exacto, `L_S ∈ NP`. -/
theorem diluido_en_NP {A : Lenguaje} {S : Set ℕ} (hA : A ∈ Cslib.Complexity.NP encBits) {c : ℕ → Bool}
    (hc : ComputableInPolyTime c encUnary encBool) (hcS : ∀ n, c n = true ↔ n ∈ S) :
    diluido A S ∈ Cslib.Complexity.NP encBits := by
  have hc' : ComputableInPolyTime (fun y : List Bool => c y.length) encBits encBool := by fun_prop
  exact mem_NP_of_guard hc' hA fun y => by simp [diluido, hcS]

/-! ### SAT y los bloques de B4 -/

section Sat

open Sagitta.Map.Tiempo.Relleno Sagitta.Map.Borde.SatPorBloques

/-- SAT enmarcado como lenguaje. -/
def satL : Lenguaje := {y | satMarco y = true}

/-- La fórmula vacía (satisfacible), enmarcada. -/
def satCero : List Bool := frame (encCNF ([] : Cslib.Logic.PL.CNF ℕ))

/-- El testigo de largo `n`: la fórmula vacía enmarcada, rellena con ceros. -/
def testigoSat (n : ℕ) : List Bool := satCero ++ List.replicate (n - satCero.length) false

/-- **SAT enmarcado tiene testigos uniformes** desde el largo de la fórmula vacía enmarcada. -/
theorem testigos_sat : TestigosUniformes satL satCero.length := by
  refine ⟨testigoSat, by unfold testigoSat; fun_prop, fun n hn => ⟨?_, ?_⟩⟩
  · simp [testigoSat]
    omega
  · change satMarco (frame _ ++ _) = true
    rw [satMarco_frame, CookS12.satBits, CookS12.bits_enc]
    exact ⟨fun _ => false, by simp [Cslib.Logic.PL.CNF.eval]⟩

/-- **SAT por bloques de B4 es SAT diluido.** -/
theorem porBloques_eq_diluido (B : Set ℕ) : {y | porBloques B y = true} = diluido satL B := by
  ext y
  classical
  simp only [Set.mem_ofPred_eq, porBloques, diluido, satL]
  by_cases h : y.length ∈ B <;> simp [h]

/-- El `porBloquesReloj` de B4 es el `diluido` en los largos del reloj. -/
theorem porBloquesReloj_eq_diluido (A : Lenguaje) (e : ℕ → ℕ) (sel : ℕ → Bool) :
    RelojDeLadner.porBloquesReloj A e sel = diluido A (RelojDeLadner.largosReloj e sel) := rfl

/-- **Decidir SAT diluido en P exige un reloj polinomial para los largos.** -/
theorem reloj_de_sat_diluido {S : Set ℕ} (hP : diluido satL S ∈ Cslib.Complexity.P encBits) :
    ∃ c : ℕ → Bool, ComputableInPolyTime c encUnary encBool ∧ ∀ n, satCero.length ≤ n → (c n = true ↔ n ∈ S) :=
  reloj_de_diluido testigos_sat hP

/-- **B4: el reloj de los bloques dobles.** Si SAT por bloques dobles estuviera en P, habría un reloj polinomial (en
unario) para sus largos; y ningún autómata finito en una letra lo es (`dobles_no_regular`). -/
theorem reloj_de_dobles (hP : {y | porBloques RelojDeLadner.largosDobles y = true} ∈ Cslib.Complexity.P encBits) :
    (∃ c : ℕ → Bool, ComputableInPolyTime c encUnary encBool ∧
      ∀ n, satCero.length ≤ n → (c n = true ↔ n ∈ RelojDeLadner.largosDobles)) ∧
    ∀ {σ : Type} [Finite σ] (M : DFA Unit σ),
      ¬ ∀ n, (List.replicate n () ∈ M.accepts ↔ n ∈ RelojDeLadner.largosDobles) :=
  ⟨reloj_de_sat_diluido (porBloques_eq_diluido _ ▸ hP), fun M => RelojDeLadner.dobles_no_regular M⟩

/-- **El precio en la moneda de la CHT**: memoria `σ₀` y `c` bits de reloj (estados `σ₀ × Fin 2^c`, como en
`card_reloj_bits` y `ley_cubo_reloj`). Para acertar los bloques dobles hasta `2^(m+1)` hace falta `2^m ≤ |σ₀| · 2^c`:
cada bit de reloj ahorra un bit de memoria, y no más. -/
theorem dobles_estados_reloj {σ₀ : Type} [Fintype σ₀] {c m : ℕ} (hm : Even m) (M : DFA Unit (σ₀ × Fin (2 ^ c)))
    (hM : ∀ n < 2 ^ (m + 1), (List.replicate n () ∈ M.accepts ↔ n ∈ RelojDeLadner.largosDobles)) :
    2 ^ m ≤ Fintype.card σ₀ * 2 ^ c := by
  have := RelojDeLadner.dobles_estados M hm hM
  rwa [Informacion.Homogeneidad.card_reloj_bits] at this

end Sat

/-! ## 3. Cuantizado contra denso, en abstracto -/

/-- **Espectro cuantizado**: todo problema de la clase está en P o es NP-completo (la dicotomía). -/
def Cuantizado (F : TresInterruptores.Clase) : Prop := TieneDicotomia F

/-- `A <ₚ B`: reducción estricta. -/
def Estricta (A B : Lenguaje) : Prop := Reduce A B ∧ ¬ Reduce B A

/-- **Espectro denso**: entre `A <ₚ B` de la clase, con `B ∉ P`, hay un `C` de la clase estrictamente en medio. -/
def Denso (F : TresInterruptores.Clase) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, B ∉ Cslib.Complexity.P encBits → Estricta A B → ∃ C ∈ F, Estricta A C ∧ Estricta C B

theorem reduce_trans {A B C : Lenguaje} (h₁ : Reduce A B) (h₂ : Reduce B C) : Reduce A C :=
  PolyTimeReducible.trans h₁ h₂

/-- **NP es denso** (Ladner 1975, Schöning 1982), de cslib-frontier. -/
theorem denso_NP : Denso (Cslib.Complexity.NP encBits) := by
  intro A hA B hB hBP hAB
  obtain ⟨C, hC, h1, h2, h3, h4⟩ := exists_mem_NP_between_of_notMem_P hA hB hBP hAB.1 hAB.2
  exact ⟨C, hC, ⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- La equivalencia transporta las reducciones estrictas. -/
theorem Estricta.de_equiv {A B C C' : Lenguaje} (e : Equivalentes C C') (h1 : Estricta A C) (h2 : Estricta C B) :
    Estricta A C' ∧ Estricta C' B :=
  ⟨⟨reduce_trans h1.1 e.1, fun h => h1.2 (reduce_trans e.1 h)⟩,
    ⟨reduce_trans e.2 h2.1, fun h => h2.2 (reduce_trans h e.2)⟩⟩

/-- **Una clase dentro de NP que captura NP es densa**: el medio de Ladner está en NP y la captura lo trae. -/
theorem denso_de_captura {F : TresInterruptores.Clase} (hF : F ⊆ Cslib.Complexity.NP encBits) (hcap : CapturaNP F) : Denso F := by
  intro A hA B hB hBP hAB
  obtain ⟨C, hC, h1, h2⟩ := denso_NP A (hF hA) B (hF hB) hBP hAB
  obtain ⟨C', hC', e⟩ := hcap C hC
  exact ⟨C', hC', Estricta.de_equiv e h1 h2⟩

/-- **La condición `B ∉ P` hace falta**: entre `∅` y `{[true]}` (los dos en NP) no hay nada. -/
theorem denso_sin_condicion_falso :
    ¬ ∀ A ∈ Cslib.Complexity.NP encBits, ∀ B ∈ Cslib.Complexity.NP encBits, Estricta A B →
      ∃ C ∈ Cslib.Complexity.NP encBits, Estricta A C ∧ Estricta C B := by
  intro h
  have hT : ({[true]} : Lenguaje) ∈ Cslib.Complexity.P encBits :=
    ⟨fun y => decide (y = [true]), by fun_prop, fun y => by simp⟩
  have h0 : Estricta (∅ : Lenguaje) {[true]} :=
    ⟨⟨fun _ => [false], .const _, fun _ => by simp⟩, fun ⟨f, _, hf⟩ => by simpa using (hf [true])⟩
  obtain ⟨C, -, ⟨⟨f, -, hf⟩, hC0⟩, ⟨hCT, hTC⟩⟩ := h ∅ empty_mem_NP {[true]} (P_subset_NP hT) h0
  by_cases hne : ∃ c, c ∈ C
  · by_cases hno : ∃ c, c ∉ C
    · obtain ⟨c₁, hc₁⟩ := hne
      obtain ⟨c₀, hc₀⟩ := hno
      -- `C` es no trivial y está en P: `{[true]} ≤ₚ C`.
      exact hTC (polyTimeReducible_of_mem_P hT hc₁ hc₀)
    · -- `C = Σ*`: `∅ ≤ₚ C` es imposible.
      push Not at hno
      exact absurd ((hf []).2 (hno _)) (Set.notMem_empty _)
  · -- `C = ∅`: `C ≤ₚ ∅` con la identidad.
    push Not at hne
    exact hC0 ⟨id, by fun_prop, fun y => by simp [hne y]⟩

/-- **Denso, con un no trivial en P y un NP-completo, da un intermedio** (si P ≠ NP). -/
theorem medio_de_denso (hne : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits) {F : TresInterruptores.Clase} (hD : Denso F)
    {A B : Lenguaje} (hA : A ∈ F) (hAP : A ∈ Cslib.Complexity.P encBits) {a₁ a₀ : List Bool} (ha₁ : a₁ ∈ A)
    (ha₀ : a₀ ∉ A) (hB : B ∈ F) (hBc : NPComplete encBits B) :
    ∃ C ∈ F, C ∉ Cslib.Complexity.P encBits ∧ ¬ NPComplete encBits C := by
  have hBP : B ∉ Cslib.Complexity.P encBits := fun h => hne (hBc.P_eq_NP_of_mem_P h encBits)
  have hAB : Estricta A B := ⟨hBc.2 encBits A (P_subset_NP hAP), fun h => hBP (h.mem_P hAP)⟩
  obtain ⟨C, hC, ⟨-, hCA⟩, ⟨-, hBC⟩⟩ := hD A hA B hB hBP hAB
  exact ⟨C, hC, fun h => hCA (polyTimeReducible_of_mem_P h ha₁ ha₀),
    fun h => hBC (h.2 encBits B hBc.1)⟩

/-- **Denso y cuantizado se excluyen** cuando la clase tiene un no trivial en P y un NP-completo, si P ≠ NP. -/
theorem denso_no_cuantizado (hne : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits) {F : TresInterruptores.Clase}
    (hD : Denso F) {A B : Lenguaje} (hA : A ∈ F) (hAP : A ∈ Cslib.Complexity.P encBits) {a₁ a₀ : List Bool}
    (ha₁ : a₁ ∈ A) (ha₀ : a₀ ∉ A) (hB : B ∈ F) (hBc : NPComplete encBits B) : ¬ Cuantizado F := by
  intro hQ
  obtain ⟨C, hC, hCP, hCc⟩ := medio_de_denso hne hD hA hAP ha₁ ha₀ hB hBc
  rcases hQ C hC with h | h
  · exact hCP h
  · exact hCc h

/-! ## 4. El interruptor como reloj -/

/-- **Una clase con reloj**: encender un problema de la clase solo fuera de las palabras de un `G ∈ P` (`G.ite ∅ B`, la
forma por huecos de Ladner en cslib-frontier) da, salvo equivalencia, otro problema de la clase. Con
`G = {y | |y| ∉ S}` es el `diluido` de § 2. -/
def AdmiteReloj (F : TresInterruptores.Clase) : Prop :=
  ∀ B ∈ F, ∀ G ∈ Cslib.Complexity.P encBits, ∃ C ∈ F, Equivalentes C (G.ite ∅ B)

theorem diluido_eq_ite (A : Lenguaje) (S : Set ℕ) :
    diluido A S = Set.ite {y : List Bool | y.length ∉ S} ∅ A := by
  ext y
  simp [diluido, Set.ite, and_comm]

/-- **Reloj ⟹ se puede diluir ⟹ densidad hacia abajo** (Ladner hacia abajo, de cslib-frontier): bajo todo
`B ∈ F ∩ NP` fuera de P hay un `C ∈ F` fuera de P, en NP, estrictamente debajo. -/
theorem denso_abajo_de_reloj {F : TresInterruptores.Clase} (hR : AdmiteReloj F) {B : Lenguaje} (hB : B ∈ F)
    (hBNP : B ∈ Cslib.Complexity.NP encBits) (hBP : B ∉ Cslib.Complexity.P encBits) :
    ∃ C ∈ F, C ∈ Cslib.Complexity.NP encBits ∧ C ∉ Cslib.Complexity.P encBits ∧ Estricta C B := by
  have hdec : IsDecidable B encBits := isDecidable_of_mem_EXP (NP_subset_EXP hBNP)
  obtain ⟨G, hG, hnotP, hAB, hBA⟩ := exists_mem_P_ite_empty_lt hdec hBP
  obtain ⟨C, hC, e⟩ := hR B hB G hG
  refine ⟨C, hC, e.enNP_iff.2 (ite_mem_NP hG empty_mem_NP hBNP), fun h => hnotP (e.enP_iff.1 h),
    reduce_trans e.1 hAB, fun h => hBA (reduce_trans h e.1)⟩

/-- **Reloj ⟹ medio**: una clase con reloj que tenga un NP-completo tiene intermedios si P ≠ NP. -/
theorem medio_de_reloj (hne : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits) {F : TresInterruptores.Clase}
    (hR : AdmiteReloj F) {B : Lenguaje} (hB : B ∈ F) (hBc : NPComplete encBits B) : TieneIntermedios F := by
  have hBP : B ∉ Cslib.Complexity.P encBits := fun h => hne (hBc.P_eq_NP_of_mem_P h encBits)
  obtain ⟨C, hC, hCNP, hCP, -, hBC⟩ := denso_abajo_de_reloj hR hB hBc.1 hBP
  exact ⟨C, hC, hCNP, hCP, fun h => hBC (h.2 encBits B hBc.1)⟩

/-- **Reloj ⟹ no cuantizado**, en las mismas condiciones. -/
theorem reloj_no_cuantizado (hne : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits) {F : TresInterruptores.Clase}
    (hR : AdmiteReloj F) {B : Lenguaje} (hB : B ∈ F) (hBc : NPComplete encBits B) : ¬ Cuantizado F :=
  fun hQ => no_ambas hQ (medio_de_reloj hne hR hB hBc)

/-- **Una clase dentro de NP que captura NP tiene reloj**: el `G.ite ∅ B` está en NP y la captura lo trae. -/
theorem reloj_de_captura {F : TresInterruptores.Clase} (hF : F ⊆ Cslib.Complexity.NP encBits) (hcap : CapturaNP F) : AdmiteReloj F :=
  fun B hB G hG => by
    obtain ⟨C, hC, e⟩ := hcap _ (ite_mem_NP hG empty_mem_NP (hF hB))
    exact ⟨C, hC, e.symm⟩

variable {frag : Interruptores → TresInterruptores.Clase} {csp : TresInterruptores.Clase}

/-- **«Interruptor = reloj», con nombre.** Apagar cualquiera de los tres interruptores da una clase con reloj. Es una
**lectura** de los Teos. 1 a 3 de Feder–Vardi (que dicen «captura NP salvo equivalencia», no «tiene reloj»), no un
teorema de ellos. `interruptorEsReloj_de_FV` muestra que, con las capturas de Feder–Vardi, la lectura sale. -/
def InterruptorEsReloj (frag : Interruptores → TresInterruptores.Clase) : Prop := ∀ s, s ≠ encendido → AdmiteReloj (frag s)

/-- **Con Feder–Vardi, la lectura sale**: lo apagado captura NP, y capturar NP dentro de NP es tener reloj. -/
theorem interruptorEsReloj_de_FV (H : FederVardi frag csp) : InterruptorEsReloj frag :=
  fun _ hs => reloj_de_captura (H.enNP _) (captura_de_apagado H hs)

/-- **La consecuencia**: apagado (reloj) y con un NP-completo ⟹ intermedios, si P ≠ NP. -/
theorem interruptor_reloj_medio (hR : InterruptorEsReloj frag) (hne : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits)
    {s : Interruptores} (hs : s ≠ encendido) {B : Lenguaje} (hB : B ∈ frag s) (hBc : NPComplete encBits B) :
    TieneIntermedios (frag s) :=
  medio_de_reloj hne (hR s hs) hB hBc

/-- **Lo apagado es denso**, con las capturas de Feder–Vardi y Ladner–Schöning de cslib-frontier. -/
theorem apagado_denso (H : FederVardi frag csp) {s : Interruptores} (hs : s ≠ encendido) : Denso (frag s) :=
  denso_de_captura (H.enNP _) (captura_de_apagado H hs)

/-- **Lo encendido no tiene reloj**, con Feder–Vardi, Bulatov–Zhuk y P ≠ NP, si tiene un NP-completo. -/
theorem encendido_sin_reloj (H : FederVardi frag csp) (BZ : TieneDicotomia csp)
    (hne : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits) {B : Lenguaje} (hB : B ∈ frag encendido)
    (hBc : NPComplete encBits B) : ¬ AdmiteReloj (frag encendido) :=
  fun hR => reloj_no_cuantizado hne hR hB hBc (encendido_dicotomia H BZ)

/-- **Lo encendido no es denso**, en las mismas condiciones y con un no trivial en P. -/
theorem encendido_no_denso (H : FederVardi frag csp) (BZ : TieneDicotomia csp)
    (hne : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits) {A B : Lenguaje} (hA : A ∈ frag encendido)
    (hAP : A ∈ Cslib.Complexity.P encBits) {a₁ a₀ : List Bool} (ha₁ : a₁ ∈ A) (ha₀ : a₀ ∉ A)
    (hB : B ∈ frag encendido) (hBc : NPComplete encBits B) : ¬ Denso (frag encendido) :=
  fun hD => denso_no_cuantizado hne hD hA hAP ha₁ ha₀ hB hBc (encendido_dicotomia H BZ)

/- Mutantes probados (25 nov 2026, fuera del repositorio):
1. `relleno_equivalente` sin `∃ x₀ ∉ L`: falso, y la negación se prueba para `Σ*` (`relleno_univ_no_reduce`).
2. `traslacion` sin `Monotone T`: `omega` no cierra (no sabe pasar de `T |unframe y|` a `T (inversa g |y|)`).
3. `traslacion_exponencial` con la cota `p m + 1` en vez de `p m + (m + 1)`: `omega` no cierra.
4. `reloj_de_diluido` con testigos sin el largo exacto (`w n ∈ A` sin `|w n| = n`): `simp` deja `|w n| ∈ S ↔ n ∈ S`.
5. `medio_de_denso` sin el no-miembro `a₀ ∉ A`: no hay con qué armar `C ≤ₚ A` (`polyTimeReducible_of_mem_P`).
6. `medio_de_reloj` sin P ≠ NP: no sale `B ∉ P`, y Ladner hacia abajo no arranca. -/

end Sagitta.Map.Borde.RellenoReloj
