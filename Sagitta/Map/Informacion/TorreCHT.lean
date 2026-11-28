import Sagitta.Map.Informacion.EspacioCubo
import Sagitta.Map.Informacion.BuscarPolinomial
import CslibFrontier.Computability.Complexity.Classes.P

/-!
# La torre CHT: SAT ∈ P y todo lo del costo

José (25 nov 2026) pidió formalizar «SAT ∈ P ⟺ CHT y todo lo del costo». La lectura acordada: una máquina de Turing ya
es homogénea en el tiempo (la regla no sabe en qué paso está: `Homogeneidad.no_sabe_la_hora`,
`EspacioCubo.no_sabe_la_hora_mt`), así que «SAT ∈ P ⟺ sistema homogéneo polinomial» sería vacío. **El contenido está en
los costos.** Es la **sexta traducción** de la serie (después de `npDistintoCoNP_iff_formulas` en
`SigmaFagin/Palabras.lean`, `sat_enP_iff_kt` en `Informacion/BuscarPolinomial.lean`, el Ising de `Hamiltoniano.lean`
y las otras): traduce, no resuelve.

## 1. La CHT con sus costos da PSPACE, y nada más

* `cht_tiempo`, `cht_presupuesto`: un autómata homogéneo (`Automata` de `CuboCostos`) con `|σ| ≤ 2^S` que devuelve,
  devuelve en menos de `2^S` consultas. Sale de parar o ciclar (`MemoriaProfundidad.para_antes_de_dos_pow`, el palomar
  de `MemoriaPeriodica`) por `sistema` (el autómata con el verificador fijo como `σ → Option σ`) y `traza_sistema`.
  Con el reloj (`reloj_en_memoria`): `c` bits de reloj suben la cota a `2^(S + c)`; con `c = O(log n)` es un factor
  `poly(n)`, así que el reloj logarítmico no cambia nada.
* `contador`, `contador_sat`: SAT_n cabe en ese marco. Un contador de `n` bits (`n + 1` bits de memoria,
  `card_contador`) recorre las `2^n` asignaciones con el verificador como oráculo y decide en `2^n` consultas;
  `contador_no_antes` dice que con `2^n − 1` no alcanza: el contador gasta todo el tiempo que la CHT le da a su memoria.

**El salto entre P y PSPACE vive entre `2^S` y `poly(n)`**: la CHT, con memoria polinomial, solo garantiza tiempo
`2^S = 2^poly(n)`; P pide que el presupuesto de tiempo sea `poly(n)` con la misma memoria. Nada en la homogeneidad
cierra esa distancia.

## 2. Correr hacia atrás bit por bit: la autorreducibilidad

* `buscar`: con un decisor `D` de SAT, recorre las variables y fija cada una preguntando «¿se puede poner en `1` sin
  perder lo fijado?» (`pregunta`: la fórmula con las unitarias fijadas, `fijados`). `buscar_correcto`: si `φ` es
  satisfacible, lo hallado la satisface (invariante `paso_satisfacible`: lo fijado sigue siendo satisfacible).
* El conteo exacto: `testigo` hace una llamada para saber si hay y una por variable distinta, **`numVars φ + 1`**
  (`llamadas_largo`), y el decisor solo entra por esas llamadas (`testigo_oraculo`). **El costo por bit escondido es una
  decisión.**
* En cslib (`buscar_poly`): con el decisor en tiempo polinomial, la búsqueda es un `foldl` de cslib-frontier sobre las
  apariciones de variables cuyo estado (los bits fijados) crece un bit por paso; `busqueda_de_decision`:
  **SAT ∈ P ⟹ la búsqueda de SAT está en FP** (`LevinMaquinas.BusquedaEnP`, con el verificador de cslib). La recíproca
  es trivial (`decision_de_busqueda`, y en abstracto `decide_de_buscar`): verificar lo hallado. `sat_enP_iff_busqueda`, y
  con la quinta traducción, `sat_enP_iff_kt`: SAT ∈ P ⟺ la `ktMT` de las satisfacibles es logarítmica.

## 3. La equivalencia de la torre

`TorreSAT`: una sola máquina de cslib (la uniformidad), polinomios `t`, `s` y, para cada fórmula de largo codificado
`n`, (i) su corrida vista por el cubo es un sistema **homogéneo** (`EspacioCubo.automata`, reloj de `0` bits) con
`|σ| ≤ 2^bitsEspacio`, `bitsEspacio = ⌈log₂(n+2)⌉ + ⌈log₂ base⌉ + exp·k·s(n)` (`memoria_torre`), que es polinomial
(`bitsEspacio_poly`); (ii) ese sistema devuelve en `t(n)` consultas a la entrada; (iii) la cinta de salida de la máquina
lleva la respuesta. **`sat_enP_iff_torre`: SAT ∈ P ⟺ `TorreSAT`**, en las dos direcciones y sin hipótesis.

**El puente que falta.** El estado `σ` del cubo es el núcleo de la configuración (cabezal de entrada, estado y cintas
de trabajo en la ventana): no incluye la cinta de salida, que la máquina solo escribe (cslib la deja fuera de
`Cfg.core`). Por eso la respuesta, en (iii), se lee en la máquina y no en `σ`: el sistema homogéneo devuelve `()`
(«ya paró») y no el bit de SAT. Cerrarlo pide modificar la máquina para que copie su salida a una cinta de trabajo antes
de parar (una construcción estándar de cslib que no se formaliza aquí; es el mismo hueco que declara `EspacioCubo` en
«La salida de la cinta de salida»). Con ese puente, la torre se diría solo con `Automata` y su `salida`.

**Sin uniformidad la torre es vacía** (`familia_no_uniforme`): con una familia de sistemas, uno por largo, hay sistemas
homogéneos de `n + ⌈log₂(n+1)⌉` bits, reloj de `0` bits y `n` consultas que deciden SAT (el `lector` copia la entrada y
contesta con una tabla de tamaño `2^n`). La homogeneidad, la memoria polinomial y el tiempo polinomial juntos no
separan nada; lo que pesa es que una sola máquina los genere, y el costo de describir su regla.

## La honestidad

* **Traduce, no resuelve.** Las equivalencias son entre formulaciones de la misma pregunta. La dificultad no se mueve:
  queda entre `2^S` y `poly(n)` (§ 1) y en el costo por bit (§ 2: si una decisión es barata, todo el testigo lo es; nada
  aquí dice si lo es).
* **`Mᵗ` como recordatorio** (general 25, «Los colapsos vistos desde la CHT»): el producto iterado de matrices es
  homogéneo (la misma `M` en cada paso) y difícil; la homogeneidad sola no separa. Lo que decide es el presupuesto.
* Como todo el cubo, el modelo abstracto relativiza (el verificador es un oráculo); las piezas de cslib (§ 2, § 3) no,
  pero tampoco dicen nada sobre P contra NP.

## Controles y mutantes

* Controles en el archivo: `contador_no_antes` (la cota `2^n` del contador no baja) y `control_variables` (sin que la
  lista recorrida cubra las variables, lo hallado no satisface: `[[(0, true)]]` con la lista vacía).
* Mutantes (en el área de trabajo de la sesión, 25 nov 2026; los ocho fallan): `cht_tiempo` con `2^S − 1` (falla en
  `omega`); `contador_decide` con `2^n − 1` consultas (falla en `omega`; `contador_no_antes` lo refuta); `buscar_correcto`
  sin `hvs` (falla en `assumption`); `llamadas_largo` con `numVars` en vez de `numVars + 1` (metas sin cerrar);
  `busqueda_de_decision` con las variables distintas como certificado del verificador de cslib (falla el tipo: el
  certificado de cslib se indexa por apariciones); la vuelta de `sat_enP_iff_torre` sin «el sistema devuelve en `t n`»
  (falla: no hay de dónde sacar `RunsInTime`); `familia_no_uniforme` con `n − 1` consultas (falla en `omega`);
  `reloj_en_memoria` con `2^S` en vez de `2^(S + c)` (falla el tipo: el reloj se cobra).
-/

namespace Sagitta.Map.Informacion.TorreCHT

open Cslib.Logic.PL Cslib.Complexity Turing Turing.MultiTapeTM
open Sagitta.Map.Tiempo.CuboCostos
open Sagitta.Map.Continuo.Memoria
open Sagitta.Map.Continuo.Regreso (Para)

/-! ## 1. La CHT con sus costos: parar antes de `2^S` -/

section Tiempo

variable {σ Q R Y : Type}

/-- **El autómata homogéneo con su verificador fijo, como sistema determinista** (el de `MemoriaPeriodica`): `none`
cuando el estado ya devuelve. -/
def sistema (a : Automata σ Q R Y) (O : Q → R) : σ → Option σ := fun x =>
  match a.salida x with
  | some _ => none
  | none => some (a.δ x (O (a.consulta x)))

theorem iterate_paso_none (δ : σ → Option σ) : ∀ m, (paso δ)^[m] none = none
  | 0 => rfl
  | m + 1 => by rw [Function.iterate_succ_apply]; exact iterate_paso_none δ m

/-- **La traza del sistema se apaga en `n + 1` si y solo si el autómata devuelve con presupuesto `n`.** -/
theorem traza_sistema (a : Automata σ Q R Y) (O : Q → R) :
    ∀ (n : ℕ) (x : σ), traza (sistema a O) x (n + 1) = none ↔ (a.corre O n x).isSome
  | 0, x => by
    change sistema a O x = none ↔ (a.salida x).isSome
    unfold sistema
    cases a.salida x <;> simp
  | n + 1, x => by
    have e : traza (sistema a O) x (n + 1 + 1) = (paso (sistema a O))^[n + 1] (sistema a O x) := by
      simp only [traza, Function.iterate_succ_apply]; rfl
    rw [e]
    cases hs : a.salida x with
    | some y =>
      simp only [sistema, hs, iterate_paso_none, Automata.corre_some hs, Option.isSome_some]
    | none =>
      simp only [sistema, hs, Automata.corre_none hs]
      exact traza_sistema a O n _

/-- **La CHT con sus costos**: un autómata homogéneo de `S` bits (`|σ| ≤ 2^S`) que devuelve algo, lo devuelve en
menos de `2^S` consultas. Sale de parar o ciclar (`MemoriaProfundidad.para_antes_de_dos_pow`, el palomar de
`MemoriaPeriodica`): si no devuelve en `2^S`, repite un estado, y por la carga de Noether no devuelve nunca. -/
theorem cht_tiempo [Fintype σ] (a : Automata σ Q R Y) (O : Q → R) {S : ℕ} (hσ : Fintype.card σ ≤ 2 ^ S) {t : ℕ}
    {x : σ} {y : Y} (h : a.corre O t x = some y) : ∃ m < 2 ^ S, a.corre O m x = some y := by
  have hp : traza (sistema a O) x ∈ Para none := ⟨t + 1, (traza_sistema a O t x).2 (by simp [h])⟩
  obtain ⟨n, hn, e⟩ := Sagitta.Map.Informacion.MemoriaProfundidad.para_antes_de_dos_pow
    (sistema a O) x hσ hp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => simp [traza] at e
    | succ m => exact ⟨m, rfl⟩
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 ((traza_sistema a O m x).1 e)
  have h1 := Automata.corre_mono (a := a) t hy'
  have h2 := Automata.corre_mono (a := a) m h
  rw [Nat.add_comm, h2] at h1
  cases h1
  exact ⟨m, by omega, hy'⟩

/-- **El tiempo que da la CHT**: con `S` bits basta un presupuesto de `2^S` consultas. -/
theorem cht_presupuesto [Fintype σ] (a : Automata σ Q R Y) (O : Q → R) {S : ℕ} (hσ : Fintype.card σ ≤ 2 ^ S)
    {t : ℕ} {x : σ} {y : Y} (h : a.corre O t x = some y) : a.corre O (2 ^ S) x = some y := by
  obtain ⟨m, hm, e⟩ := cht_tiempo a O hσ h
  have := Automata.corre_mono (a := a) (2 ^ S - m) e
  rwa [show m + (2 ^ S - m) = 2 ^ S by omega] at this

end Tiempo

/-! ### SAT_n con un contador de `n` bits -/

section Contador

/-- **El contador**: estados `0, …, 2^n − 1` (la asignación que prueba), `2^n` (no hay) y `2^n + 1` (hay). Consulta
al verificador la asignación número `x`; si dice que sí, devuelve `true`; si no, pasa a la siguiente. -/
def contador (n : ℕ) : Automata (Fin (2 ^ n + 2)) (Fin (2 ^ n)) Bool Bool where
  inicio := ⟨0, by positivity⟩
  consulta x := ⟨x.val % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
  δ x r := if r then ⟨2 ^ n + 1, by omega⟩ else ⟨min (x.val + 1) (2 ^ n), Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩
  salida x := if x.val = 2 ^ n then some false else if x.val = 2 ^ n + 1 then some true else none

theorem contador_salida {n i : ℕ} (hi : i < 2 ^ n) : (contador n).salida ⟨i, by omega⟩ = none := by
  have h1 : i ≠ 2 ^ n := by omega
  have h2 : i ≠ 2 ^ n + 1 := by omega
  simp [contador, h1, h2]

theorem contador_corre {n : ℕ} (O : Fin (2 ^ n) → Bool) :
    ∀ (m i : ℕ) (hi : i + m = 2 ^ n), (contador n).corre O m ⟨i, by omega⟩ =
      some (decide (∃ k : Fin (2 ^ n), i ≤ k.val ∧ O k = true))
  | 0, i, hi => by
    simp only [Automata.corre_cero, contador, show i = 2 ^ n by omega, ite_true, Option.some.injEq]
    symm; simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro k hk; exact absurd k.isLt (by omega)
  | m + 1, i, hi => by
    have hs : (contador n).salida ⟨i, by omega⟩ = none := contador_salida (by omega)
    rw [Automata.corre_none hs]
    have hq : (contador n).consulta ⟨i, by omega⟩ = ⟨i, by omega⟩ := by
      simp only [contador, Fin.mk.injEq]; exact Nat.mod_eq_of_lt (by omega)
    rw [hq]
    cases hO : O ⟨i, by omega⟩
    · have hd : (contador n).δ ⟨i, by omega⟩ false = ⟨i + 1, by omega⟩ := by
        simp only [contador, Bool.false_eq_true, ite_false, Fin.mk.injEq]; omega
      rw [hd, contador_corre O m (i + 1) (by omega)]
      congr 1
      apply decide_eq_decide.2
      constructor
      · rintro ⟨k, hk, hk'⟩; exact ⟨k, by omega, hk'⟩
      · rintro ⟨k, hk, hk'⟩
        refine ⟨k, ?_, hk'⟩
        rcases Nat.eq_or_lt_of_le hk with e | e
        · exfalso; have : k = ⟨i, by omega⟩ := Fin.ext e.symm
          rw [this, hO] at hk'; exact Bool.false_ne_true hk'
        · omega
    · have hd : (contador n).δ ⟨i, by omega⟩ true = ⟨2 ^ n + 1, by omega⟩ := by simp [contador]
      rw [hd, Automata.corre_some (y := true) (by simp [contador]) m]
      simp only [Option.some.injEq]
      symm; simp only [decide_eq_true_eq]
      exact ⟨⟨i, by omega⟩, le_rfl, hO⟩

/-- **El contador decide en `2^n` consultas** si alguna de las `2^n` asignaciones satisface. -/
theorem contador_decide {n : ℕ} (O : Fin (2 ^ n) → Bool) :
    (contador n).corre O (2 ^ n) (contador n).inicio = some (decide (∃ k, O k = true)) := by
  rw [show (contador n).inicio = ⟨0, by positivity⟩ from rfl, contador_corre O (2 ^ n) 0 (by omega)]
  simp

/-- **Y no antes**: con el verificador que siempre dice que no, `2^n − 1` consultas no alcanzan. El contador gasta
todo el tiempo que la CHT le permite a su memoria (salvo el factor de los dos estados de salida). -/
theorem contador_lento (n : ℕ) : ∀ (m i : ℕ) (hi : i + m < 2 ^ n),
    (contador n).corre (fun _ => false) m ⟨i, by omega⟩ = none
  | 0, i, hi => by
    rw [Automata.corre_cero]; exact contador_salida (by omega)
  | m + 1, i, hi => by
    have hs : (contador n).salida ⟨i, by omega⟩ = none := contador_salida (by omega)
    rw [Automata.corre_none hs]
    have hd : (contador n).δ ⟨i, by omega⟩ false = ⟨i + 1, by omega⟩ := by
      simp only [contador, Bool.false_eq_true, ite_false, Fin.mk.injEq]; omega
    rw [hd]
    exact contador_lento n m (i + 1) (by omega)

theorem contador_no_antes (n : ℕ) :
    (contador n).corre (fun _ => false) (2 ^ n - 1) (contador n).inicio = none :=
  contador_lento n _ 0 (by have := Nat.one_le_two_pow (n := n); omega)

/-- **La memoria del contador**: `n + 1` bits (con `n ≥ 1`). -/
theorem card_contador {n : ℕ} (hn : 1 ≤ n) : Fintype.card (Fin (2 ^ n + 2)) ≤ 2 ^ (n + 1) := by
  simp only [Fintype.card_fin, pow_succ]
  have : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- Una asignación de las `n` primeras variables, extendida con `false`. -/
def extender (n : ℕ) (a : Fin n → Bool) (v : ℕ) : Bool := if h : v < n then a ⟨v, h⟩ else false

/-- La numeración de las asignaciones de `n` variables. -/
noncomputable def numerar (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (by simp)

/-- **El verificador de SAT_n**: la asignación número `k` satisface `φ`. -/
noncomputable def verificadorN (n : ℕ) (φ : CNF ℕ) (k : Fin (2 ^ n)) : Bool :=
  φ.eval (extender n ((numerar n).symm k))

/-- Con las variables entre `0` y `n − 1`, ser satisfacible es que alguna de las `2^n` asignaciones lo sea. -/
theorem satisfacible_iff_N {n : ℕ} {φ : CNF ℕ} (hφ : ∀ v ∈ φ.vars, v < n) :
    φ.Satisfiable ↔ ∃ k, verificadorN n φ k = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨numerar n (fun i => σ i), ?_⟩
    simp only [verificadorN, Equiv.symm_apply_apply]
    rw [← hσ]
    exact CNF.eval_congr fun v hv => by simp [extender, hφ v hv]
  · rintro ⟨k, hk⟩; exact ⟨_, hk⟩

/-- **SAT_n en el marco de la CHT**: el contador, con `n + 1` bits de memoria y el verificador como oráculo, decide en
`2^n` consultas si una fórmula con variables `< n` es satisfacible. Es la esquina PSPACE de la torre: memoria
polinomial, tiempo `2^S`. -/
theorem contador_sat {n : ℕ} {φ : CNF ℕ} (hφ : ∀ v ∈ φ.vars, v < n) :
    ∃ b, (contador n).corre (verificadorN n φ) (2 ^ n) (contador n).inicio = some b ∧ (b = true ↔ φ.Satisfiable) :=
  ⟨_, contador_decide _, by rw [decide_eq_true_iff, satisfacible_iff_N hφ]⟩

end Contador

/-! ## 2. Correr hacia atrás bit por bit -/

section Autorreducir

/-- Las cláusulas unitarias que fijan las variables `vs` a los bits `bs` (las primeras `|bs|`). -/
def fijados (vs : List ℕ) (bs : List Bool) : CNF ℕ := (vs.zip bs).map fun p => [p]

/-- La pregunta al decisor en el paso de la variable `v`: ¿se puede poner `v` en `1` sin perder lo fijado? -/
def pregunta (vs : List ℕ) (φ : CNF ℕ) (bs : List Bool) (v : ℕ) : CNF ℕ :=
  [(v, true)] :: (fijados vs bs ++ φ)

/-- Un paso: pregunta una vez y fija el bit. -/
def pasoBit (D : CNF ℕ → Bool) (vs : List ℕ) (φ : CNF ℕ) (bs : List Bool) (v : ℕ) : List Bool :=
  bs ++ [D (pregunta vs φ bs v)]

/-- **La búsqueda autorreducida**: recorre `vs` y fija cada variable con una llamada al decisor. -/
def buscar (D : CNF ℕ → Bool) (vs : List ℕ) (φ : CNF ℕ) : List Bool := vs.foldl (pasoBit D vs φ) []

/-- La misma corrida, con la lista de las preguntas que hace. -/
def correr (D : CNF ℕ → Bool) (vs : List ℕ) (φ : CNF ℕ) : List Bool → List ℕ → List Bool × List (CNF ℕ)
  | bs, [] => (bs, [])
  | bs, v :: rest =>
    let r := correr D vs φ (pasoBit D vs φ bs v) rest
    (r.1, pregunta vs φ bs v :: r.2)

theorem correr_fst (D : CNF ℕ → Bool) (vs : List ℕ) (φ : CNF ℕ) :
    ∀ (rest : List ℕ) (bs : List Bool), (correr D vs φ bs rest).1 = rest.foldl (pasoBit D vs φ) bs
  | [], _ => rfl
  | _ :: rest, _ => correr_fst D vs φ rest _

/-- **Una pregunta por variable.** -/
theorem correr_largo (D : CNF ℕ → Bool) (vs : List ℕ) (φ : CNF ℕ) :
    ∀ (rest : List ℕ) (bs : List Bool), (correr D vs φ bs rest).2.length = rest.length
  | [], _ => rfl
  | v :: rest, bs => by simp [correr, correr_largo D vs φ rest]

/-- **El decisor solo entra por las preguntas**: dos decisores que contestan igual las preguntas que hace la corrida
con el primero dan la misma corrida. -/
theorem correr_oraculo (D D' : CNF ℕ → Bool) (vs : List ℕ) (φ : CNF ℕ) :
    ∀ (rest : List ℕ) (bs : List Bool), (∀ q ∈ (correr D vs φ bs rest).2, D q = D' q) →
      correr D vs φ bs rest = correr D' vs φ bs rest
  | [], _, _ => rfl
  | v :: rest, bs, h => by
    have h0 : D (pregunta vs φ bs v) = D' (pregunta vs φ bs v) := h _ (by simp [correr])
    have hp : pasoBit D vs φ bs v = pasoBit D' vs φ bs v := by simp [pasoBit, h0]
    have ih := correr_oraculo D D' vs φ rest (pasoBit D vs φ bs v) (fun q hq => h q (by simp [correr, hq]))
    simp only [correr]
    rw [← hp, ih]

/-- El decisor es correcto. -/
def Decide (D : CNF ℕ → Bool) : Prop := ∀ ψ : CNF ℕ, D ψ = true ↔ ψ.Satisfiable

theorem fijados_snoc {pre post : List ℕ} {v : ℕ} {bs : List Bool} (h : bs.length = pre.length) (b : Bool) :
    fijados (pre ++ v :: post) (bs ++ [b]) = fijados (pre ++ v :: post) bs ++ [[(v, b)]] := by
  unfold fijados
  rw [List.zip_append h.symm, show pre ++ v :: post = pre ++ v :: post from rfl]
  have : (pre ++ v :: post).zip bs = pre.zip bs := by
    rw [← List.append_nil bs, List.zip_append h.symm]; simp
  rw [this]; simp

theorem satisfiable_append_comm {F G : CNF ℕ} : (F ++ G).Satisfiable ↔ (G ++ F).Satisfiable := by
  simp only [CNF.Satisfiable, CNF.eval_append, Bool.and_comm]

/-- **El invariante**: si lo fijado hasta ahora es satisfacible, un paso lo mantiene satisfacible. -/
theorem paso_satisfacible {D : CNF ℕ → Bool} (hD : Decide D) {pre post : List ℕ} {v : ℕ} {φ : CNF ℕ}
    {bs : List Bool} (h : bs.length = pre.length)
    (hs : (fijados (pre ++ v :: post) bs ++ φ).Satisfiable) :
    (fijados (pre ++ v :: post) (pasoBit D (pre ++ v :: post) φ bs v) ++ φ).Satisfiable := by
  unfold pasoBit
  rw [fijados_snoc h, List.append_assoc]
  set F := fijados (pre ++ v :: post) bs
  cases hq : D (pregunta (pre ++ v :: post) φ bs v)
  · obtain ⟨σ, hσ⟩ := hs
    have hv : σ v = false := by
      by_contra hv
      have : (pregunta (pre ++ v :: post) φ bs v).Satisfiable :=
        ⟨σ, by simp only [CNF.eval_append, Bool.and_eq_true] at hσ
               simp [pregunta, Clause.eval, Literal.eval, Bool.eq_true_of_ne_false hv, hσ]
               exact hσ.1⟩
      rw [← hD, hq] at this; exact Bool.false_ne_true this
    refine ⟨σ, ?_⟩
    simp only [CNF.eval_append, CNF.eval_cons, CNF.eval_nil] at hσ ⊢
    simp [Clause.eval, Literal.eval, hv, hσ]
  · obtain ⟨σ, hσ⟩ := (hD _).1 hq
    refine ⟨σ, ?_⟩
    simp only [pregunta, CNF.eval_append, CNF.eval_cons, CNF.eval_nil] at hσ ⊢
    simp only [Bool.and_eq_true] at hσ ⊢
    tauto

/-- El invariante a lo largo del recorrido. -/
theorem foldl_satisfacible {D : CNF ℕ → Bool} (hD : Decide D) (vs : List ℕ) (φ : CNF ℕ) :
    ∀ (rest pre : List ℕ) (bs : List Bool), vs = pre ++ rest → bs.length = pre.length →
      (fijados vs bs ++ φ).Satisfiable →
      (rest.foldl (pasoBit D vs φ) bs).length = vs.length ∧
        (fijados vs (rest.foldl (pasoBit D vs φ) bs) ++ φ).Satisfiable
  | [], pre, bs, hv, hl, hs => by simp only [List.foldl_nil]; subst hv; simpa [hl] using hs
  | v :: rest, pre, bs, hv, hl, hs => by
    subst hv
    refine foldl_satisfacible hD _ φ rest (pre ++ [v]) _ (by simp) ?_ (paso_satisfacible hD hl hs)
    simp [pasoBit, hl]

/-- La asignación que dicen los bits: la variable `v` toma el bit de su primera aparición en `vs`. -/
def asignacion (vs : List ℕ) (bs : List Bool) (v : ℕ) : Bool := bs.getD (vs.idxOf v) false

/-- Lo fijado obliga: quien satisface las unitarias toma en cada `v ∈ vs` el bit de su primera aparición. -/
theorem fijados_obliga {vs : List ℕ} {bs : List Bool} {σ : ℕ → Bool} (hl : bs.length = vs.length)
    (hσ : (fijados vs bs).eval σ = true) {v : ℕ} (hv : v ∈ vs) : σ v = asignacion vs bs v := by
  have hi : vs.idxOf v < vs.length := List.idxOf_lt_length_iff.2 hv
  have hi' : vs.idxOf v < bs.length := hl ▸ hi
  have hmem : (v, bs[vs.idxOf v]) ∈ vs.zip bs := by
    rw [List.mem_iff_getElem]
    exact ⟨vs.idxOf v, by simp [hi, hi'], by simp [List.getElem_idxOf]⟩
  have hc := (CNF.eval_eq_true_iff σ _).1 hσ [(v, bs[vs.idxOf v])] (List.mem_map.2 ⟨_, hmem, rfl⟩)
  rw [Clause.eval_eq_true_iff] at hc
  obtain ⟨l, hl', e⟩ := hc
  simp only [List.mem_singleton] at hl'
  subst hl'
  simpa [asignacion, List.getD_eq_getElem?_getD, hi'] using e

/-- **La búsqueda autorreducida es correcta**: si `φ` es satisfacible y `vs` contiene sus variables, los bits hallados
la satisfacen. -/
theorem buscar_correcto {D : CNF ℕ → Bool} (hD : Decide D) {vs : List ℕ} {φ : CNF ℕ}
    (hvs : ∀ v ∈ φ.vars, v ∈ vs) (hφ : φ.Satisfiable) : φ.eval (asignacion vs (buscar D vs φ)) = true := by
  obtain ⟨hl, σ, hσ⟩ := foldl_satisfacible hD vs φ vs [] [] rfl rfl (by simpa [fijados] using hφ)
  simp only [CNF.eval_append, Bool.and_eq_true] at hσ
  rw [← hσ.2]
  exact CNF.eval_congr fun v hv => (fijados_obliga hl hσ.1 (hvs v hv)).symm

/-- **El testigo, con `n + 1` llamadas**: una para saber si hay, y una por variable (las `n` distintas). -/
def testigo (D : CNF ℕ → Bool) (φ : CNF ℕ) : Option (List Bool) :=
  if D φ then some (buscar D φ.distinctVars φ) else none

/-- Las llamadas al decisor que hace `testigo`, en orden. -/
def llamadas (D : CNF ℕ → Bool) (φ : CNF ℕ) : List (CNF ℕ) :=
  φ :: if D φ then (correr D φ.distinctVars φ [] φ.distinctVars).2 else []

theorem testigo_eq (D : CNF ℕ → Bool) (φ : CNF ℕ) :
    testigo D φ = if D φ then some (correr D φ.distinctVars φ [] φ.distinctVars).1 else none := by
  simp [testigo, buscar, correr_fst]

/-- **El conteo exacto**: si hay testigo, `numVars φ + 1` llamadas; si no, una. El costo por bit escondido es una
decisión. -/
theorem llamadas_largo (D : CNF ℕ → Bool) (φ : CNF ℕ) :
    (llamadas D φ).length = if D φ then φ.numVars + 1 else 1 := by
  unfold llamadas
  split <;> simp [correr_largo, CNF.length_distinctVars]

/-- **El decisor solo entra por esas llamadas.** -/
theorem testigo_oraculo (D D' : CNF ℕ → Bool) (φ : CNF ℕ) (h : ∀ q ∈ llamadas D φ, D q = D' q) :
    testigo D φ = testigo D' φ := by
  have h0 : D φ = D' φ := h φ (by simp [llamadas])
  rw [testigo_eq, testigo_eq, ← h0]
  split
  · next hD =>
    rw [correr_oraculo D D' _ φ _ [] (fun q hq => h q (by simp [llamadas, hD, hq]))]
  · rfl

/-- **Correcto**: `testigo` devuelve un testigo si y solo si `φ` es satisfacible, y el testigo la satisface. -/
theorem testigo_correcto {D : CNF ℕ → Bool} (hD : Decide D) (φ : CNF ℕ) :
    (testigo D φ = none ↔ ¬ φ.Satisfiable) ∧
      ∀ w, testigo D φ = some w → φ.eval (asignacion φ.distinctVars w) = true := by
  refine ⟨?_, fun w hw => ?_⟩
  · unfold testigo; split <;> simp_all [← hD φ]
  · unfold testigo at hw
    split at hw
    · next h =>
      cases hw
      exact buscar_correcto hD (fun v hv => CNF.mem_distinctVars.2 hv) ((hD φ).1 h)
    · cases hw

/-- **Control**: sin que la lista recorrida cubra las variables, lo hallado no satisface. -/
theorem control_variables (D : CNF ℕ → Bool) :
    CNF.Satisfiable ([[(0, true)]] : CNF ℕ) ∧
      CNF.eval (asignacion [] (buscar D [] [[(0, true)]])) ([[(0, true)]] : CNF ℕ) = false :=
  ⟨⟨fun _ => true, rfl⟩, rfl⟩

/-- **La recíproca, trivial**: de un buscador sale un decisor con una evaluación. -/
theorem decide_de_buscar {B : CNF ℕ → ℕ → Bool} (hB : ∀ φ : CNF ℕ, φ.Satisfiable → φ.eval (B φ) = true) :
    Decide fun φ => φ.eval (B φ) :=
  fun φ => ⟨fun h => ⟨_, h⟩, hB φ⟩

end Autorreducir

/-! ### En cslib: SAT ∈ P si y solo si la búsqueda de SAT está en FP -/

section FP

theorem fijados_poly : ComputableInPolyTime (fun p : List ℕ × List Bool => fijados p.1 p.2)
    (encPair (encList encNat) encBits) encCNF := by
  unfold fijados encCNF
  have hb := (bits_encList_polyTime encBool).1
  have hz := (ComputableInPolyTime.zip encNat encBool).comp
    (ComputableInPolyTime.prod (ComputableInPolyTime.fst (encList encNat) encBits)
      (hb.comp (ComputableInPolyTime.snd _ _)))
  have hs : ComputableInPolyTime (fun p : ℕ × Bool => [p]) (encPair encNat encBool)
      (encList (encPair encNat encBool)) := by
    fun_prop
  exact (ComputableInPolyTime.map hs).comp hz

theorem pregunta_poly :
    ComputableInPolyTime (fun p : (CNF ℕ × List Bool) × ℕ => pregunta p.1.1.vars p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encBits) encNat) encCNF := by
  have hf : ComputableInPolyTime (fun p : (CNF ℕ × List Bool) × ℕ => fijados p.1.1.vars p.1.2)
      (encPair (encPair encCNF encBits) encNat) encCNF :=
    fijados_poly.comp ((SAT.computableInPolyTime_vars.comp
      ((ComputableInPolyTime.fst encCNF encBits).comp (ComputableInPolyTime.fst _ encNat))).prod
      ((ComputableInPolyTime.snd encCNF encBits).comp (ComputableInPolyTime.fst _ encNat)))
  unfold pregunta
  unfold encCNF at hf ⊢
  fun_prop

theorem pasoBit_poly {D : CNF ℕ → Bool} (hD : ComputableInPolyTime D encCNF encBool) :
    ComputableInPolyTime (fun p : (CNF ℕ × List Bool) × ℕ => pasoBit D p.1.1.vars p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encBits) encNat) encBits := by
  have hq := hD.comp pregunta_poly
  unfold pasoBit
  have h1 : ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × ℕ => [D (pregunta p.1.1.vars p.1.1 p.1.2 p.2)])
      (encPair (encPair encCNF encBits) encNat) encBits :=
    (ComputableInPolyTime.of_finite (fun b : Bool => [b]) (encIn := encBool) (encOut := encBits)).comp hq
  exact ComputableInPolyTime.bitsAppend (by fun_prop) h1

/-- **La búsqueda autorreducida es polinomial** si el decisor lo es: el recorrido es un `foldl` de cslib sobre las
apariciones de variables, y el estado (los bits fijados) crece un bit por paso. -/
theorem buscar_poly {D : CNF ℕ → Bool} (hD : ComputableInPolyTime D encCNF encBool) :
    ComputableInPolyTime (fun φ => buscar D φ.vars φ) encCNF encBits := by
  unfold buscar
  exact ComputableInPolyTime.foldlWith_of_bounded_growth (par := id) (list := CNF.vars)
    (init := fun _ => []) (step := fun φ bs v => pasoBit D φ.vars φ bs v) ComputableInPolyTime.id'
    SAT.computableInPolyTime_vars (ComputableInPolyTime.const []) (pasoBit_poly hD) (growth := fun _ => 1)
    (PolyBounded.const 1) (fun φ bs v _ => by simp [pasoBit, encBits])

open Sagitta.Map.Tiempo.LevinMaquinas in
/-- **SAT ∈ P ⟹ la búsqueda de SAT está en FP** (en el sentido de `LevinMaquinas.BusquedaEnP`, con el verificador de
cslib): el decisor, llamado una vez por aparición de variable, fija el testigo bit por bit. -/
theorem busqueda_de_decision (h : SAT ∈ Cslib.Complexity.P encCNF) : BusquedaEnP encCNF SAT.verifier SAT := by
  obtain ⟨f, hf, hA⟩ := h
  have hD : Decide f := fun ψ => (hA ψ).symm
  exact ⟨fun φ => buscar f φ.vars φ, buscar_poly hf, fun φ hφ => buscar_correcto hD (fun v hv => hv) hφ⟩

open Sagitta.Map.Tiempo.LevinMaquinas in
/-- **La recíproca, trivial**: de la búsqueda en FP sale la decisión en P, verificando lo hallado. -/
theorem decision_de_busqueda (h : BusquedaEnP encCNF SAT.verifier SAT) : SAT ∈ Cslib.Complexity.P encCNF := by
  obtain ⟨f, hf, hA⟩ := h
  refine ⟨fun φ => SAT.verifier (φ, f φ), SAT.computableInPolyTime_verifier.comp
    (ComputableInPolyTime.id'.prod hf), fun φ => ⟨hA φ, fun hv => ⟨_, hv⟩⟩⟩

open Sagitta.Map.Tiempo.LevinMaquinas in
/-- **Decidir SAT y buscar sus testigos cuestan lo mismo, salvo un polinomio.** -/
theorem sat_enP_iff_busqueda : SAT ∈ Cslib.Complexity.P encCNF ↔ BusquedaEnP encCNF SAT.verifier SAT :=
  ⟨busqueda_de_decision, decision_de_busqueda⟩

open Sagitta.Map.Tiempo.LevinMaquinas in
/-- **Y con la quinta traducción**: SAT ∈ P si y solo si la `ktMT` de las satisfacibles es logarítmica
(`BuscarPolinomial.sat_enP_iff_kt`). -/
theorem sat_enP_iff_kt : SAT ∈ Cslib.Complexity.P encCNF ↔ KtMTLog encCNF SAT.verifier SAT :=
  sat_enP_iff_busqueda.trans BuscarPolinomial.sat_enP_iff_kt

end FP

/-! ## 3. La torre -/

section Torre

open Sagitta.Map.Informacion.EspacioCubo

/-- **La torre CHT para SAT**, en el vocabulario de `Homogeneidad` y `EspacioCubo`: una sola máquina de cslib (la
uniformidad), polinomios `t` y `s`, y para cada fórmula `φ` (de largo codificado `n`):

* su corrida, vista por el cubo, es un sistema **homogéneo** (`EspacioCubo.automata`, sin reloj: `c = 0`) cuya memoria
  es la ventana de espacio `s n`, o sea `|σ| ≤ 2^bitsEspacio` con
  `bitsEspacio = ⌈log₂(n + 2)⌉ + ⌈log₂ base⌉ + exp · k · s n` (`memoria_torre`, `bitsEspacio_poly`);
* ese sistema, con la entrada como verificador, **devuelve en `t n` consultas** (para en tiempo polinomial);
* y lo que la máquina deja en su cinta de salida (que solo escribe: no es memoria) es la respuesta de SAT.

El reloj de `O(log n)` bits no agrega nada: se paga en memoria (`reloj_en_memoria`), `c` bits más sobre
`bitsEspacio`. -/
def TorreSAT : Prop :=
  ∃ (t s : ℕ → ℕ), Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (g : CNF ℕ → Bool),
      (∀ φ, φ ∈ SAT ↔ g φ = true) ∧
      ∀ φ : CNF ℕ, tm.RunsInSpace (encCNF φ) (s (encCNF φ).length) ∧
        (automata tm (encCNF φ).length (s (encCNF φ).length) (fun _ => ())).corre (simboloEn (encCNF φ))
          (t (encCNF φ).length) (automata tm (encCNF φ).length (s (encCNF φ).length) (fun _ => ())).inicio =
            some () ∧
        tm.Computes (encCNF φ) (encBool (g φ))

/-- **La sexta traducción: SAT ∈ P si y solo si la torre CHT tiene presupuesto polinomial.** -/
theorem sat_enP_iff_torre : SAT ∈ Cslib.Complexity.P encCNF ↔ TorreSAT := by
  rw [mem_P_iff_exists_decidableInTimeAndSpace]
  constructor
  · rintro ⟨t, s, ht, hs, h⟩
    obtain ⟨g, ⟨k, State, hfin, tm, htm⟩, hA⟩ := decidableInTimeAndSpace_iff.1 h
    refine ⟨t, s, ht, hs, k, State, hfin, tm, g, hA, fun φ => ?_⟩
    obtain ⟨hc, hrt, hrs⟩ := htm φ
    refine ⟨hrs, ?_, hc⟩
    obtain ⟨u, hu, hhalt⟩ := exists_haltsAt (runsInTime_iff_halted.1 hrt)
    exact corre_automata rfl (fun _ => ()) hrs hhalt hu
  · rintro ⟨t, s, ht, hs, k, State, hfin, tm, g, hA, H⟩
    refine ⟨t, s, ht, hs, decidableInTimeAndSpace_iff.2 ⟨g, ⟨k, State, hfin, tm, fun φ => ?_⟩, hA⟩⟩
    obtain ⟨hrs, hcorre, hc⟩ := H φ
    refine ⟨hc, runsInTime_iff_halted.2 ?_, hrs⟩
    by_contra hno
    have hnone := corre_automata_none (tm := tm) (input := encCNF φ) rfl (fun _ => ()) hrs
      (t := t (encCNF φ).length) (fun j hj hj' => hno (by
        rw [runFrom_eq_of_halt tm _ hj hj']; exact hj'))
    rw [hcorre] at hnone
    exact Option.some_ne_none _ hnone

/-- **La memoria de la torre**: `|σ| ≤ 2^bitsEspacio` (de `EspacioCubo`). -/
theorem memoria_torre {k : ℕ} {State : Type} [Fintype State] (n S : ℕ) :
    Fintype.card (Estados Bool State k n S) ≤ 2 ^ bitsEspacio Bool State k n S :=
  card_estados_bits n S

/-- **Con espacio polinomial, los bits de memoria son polinomiales**: `bitsEspacio n (s n)` es `O(log n) + O(s n)`. -/
theorem bitsEspacio_poly {k : ℕ} {State : Type} [Fintype State] {s : ℕ → ℕ} (hs : Cslib.PolynomiallyBounded s) :
    Cslib.PolynomiallyBounded fun n => bitsEspacio Bool State k n (s n) := by
  refine Cslib.PolynomiallyBounded.mono_of_le
    (((Cslib.PolynomiallyBounded.id.add (.const 2)).add (.const (Nat.clog 2 (storageBoundBase Bool State k)))).add
      ((Cslib.PolynomiallyBounded.const (storageBoundExp Bool k * k)).mul hs)) fun n => ?_
  have h1 : Nat.clog 2 (n + 2) ≤ n + 2 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  simp only [bitsEspacio, mul_assoc]
  omega

end Torre

/-! ### El reloj de `c` bits, cobrado -/

section Reloj

open Sagitta.Map.Informacion.Homogeneidad

/-- **El reloj se paga en memoria, y la CHT cobra el total**: un autómata con reloj de `|κ| ≤ 2^c` valores y
`|σ| ≤ 2^S` estados, si devuelve, devuelve en menos de `2^(S + c)` consultas. Con `c = O(log n)` el factor es `poly(n)`:
el reloj logarítmico no cambia la clase. -/
theorem reloj_en_memoria {κ σ Q R Y : Type} [Fintype κ] [Fintype σ] (a : AutomataConReloj κ σ Q R Y) (O : Q → R)
    {S c : ℕ} (hσ : Fintype.card σ ≤ 2 ^ S) (hκ : Fintype.card κ ≤ 2 ^ c) {t : ℕ} {y : Y}
    (h : a.corre O t a.reloj0 a.inicio = some y) :
    ∃ m < 2 ^ (S + c), a.corre O m a.reloj0 a.inicio = some y := by
  have hσκ : Fintype.card (σ × κ) ≤ 2 ^ (S + c) := by
    rw [Fintype.card_prod, pow_add]; exact Nat.mul_le_mul hσ hκ
  rw [← homogeneizar_corre] at h
  obtain ⟨m, hm, e⟩ := cht_tiempo (homogeneizar a) O hσκ h
  exact ⟨m, hm, (homogeneizar_corre a O m _ _).symm.trans e⟩

end Reloj

/-! ### Sin uniformidad la torre es vacía -/

section NoUniforme

open Sagitta.Map.Informacion.Homogeneidad
open Sagitta.Map.Informacion.EspacioCubo (simboloEn)

/-- **Una familia de sistemas CHT para SAT**, una por largo `n`, sin uniformidad: memoria `S n` bits, reloj `c n`
bits, `T n` consultas a la entrada (el verificador del cubo es la entrada: `simboloEn`). -/
def FamiliaCHT (S c T : ℕ → ℕ) : Prop :=
  ∀ n, ∃ (κ σ : Type) (_ : Fintype κ) (_ : Fintype σ) (a : AutomataConReloj κ σ ℕ (Option Bool) Bool),
    Fintype.card σ ≤ 2 ^ S n ∧ Fintype.card κ ≤ 2 ^ c n ∧
    ∀ φ : CNF ℕ, (encCNF φ).length = n →
      ∃ b, a.corre (simboloEn (encCNF φ)) (T n) a.reloj0 a.inicio = some b ∧ (b = true ↔ φ ∈ SAT)

open Classical in
/-- **El lector**: copia los `n` bits de la entrada a su memoria y contesta con una tabla. Homogéneo, sin reloj. -/
noncomputable def lector (n : ℕ) : Automata (Fin (n + 1) × (Fin n → Bool)) ℕ (Option Bool) Bool where
  inicio := (0, fun _ => false)
  consulta x := x.1.val + 1
  δ x r := if h : x.1.val < n then (⟨x.1.val + 1, by omega⟩, Function.update x.2 ⟨x.1.val, h⟩ (r.getD false))
    else x
  salida x := if x.1.val = n then some (decide (∃ φ : CNF ℕ, encCNF φ = List.ofFn x.2 ∧ φ ∈ SAT)) else none

open Classical in
theorem lector_corre {w : List Bool} {n : ℕ} (hw : w.length = n) :
    ∀ (r i : ℕ) (hi : i + r = n) (b : Fin n → Bool), (∀ j : Fin n, j.val < i → b j = w[j.val]'(by omega)) →
      (lector n).corre (simboloEn w) r (⟨i, by omega⟩, b) =
        some (decide (∃ φ : CNF ℕ, encCNF φ = w ∧ φ ∈ SAT))
  | 0, i, hi, b, hb => by
    have hof : List.ofFn b = w := by
      apply List.ext_getElem (by simp [hw])
      intro j h1 h2
      simp only [List.getElem_ofFn]
      exact hb ⟨j, by simpa using h1⟩ (by simp at h1; omega)
    simp [Automata.corre_cero, lector, show i = n by omega, hof]
  | r + 1, i, hi, b, hb => by
    have hs : (lector n).salida (⟨i, by omega⟩, b) = none := by
      have : i ≠ n := by omega
      simp [lector, this]
    rw [Automata.corre_none hs]
    have hsym : simboloEn w ((lector n).consulta (⟨i, by omega⟩, b)) = some (w[i]'(by omega)) := by
      simp [lector, simboloEn]
    rw [hsym]
    have hd : (lector n).δ (⟨i, by omega⟩, b) (some (w[i]'(by omega))) =
        (⟨i + 1, by omega⟩, Function.update b ⟨i, by omega⟩ (w[i]'(by omega))) := by
      simp [lector, show i < n by omega]
    rw [hd]
    refine lector_corre hw r (i + 1) (by omega) _ fun j hj => ?_
    by_cases e : j = ⟨i, by omega⟩
    · rw [e, Function.update_self]
    · rw [Function.update_of_ne e]
      exact hb j (by have : j.val ≠ i := fun h => e (Fin.ext h); omega)

/-- **Sin uniformidad la torre es vacía**: hay una familia de sistemas homogéneos (reloj de `0` bits) con memoria
`n + ⌈log₂(n + 1)⌉` bits y `n` consultas que decide SAT en cada largo. Copia la entrada y contesta con una tabla: el
costo se esconde en la descripción de la salida, que es de tamaño `2^n`. Lo que decide en la torre no es la
homogeneidad, ni la memoria, ni el tiempo por separado: es que **una sola** máquina las genere (`TorreSAT`). -/
theorem familia_no_uniforme : FamiliaCHT (fun n => n + Nat.clog 2 (n + 1)) (fun _ => 0) (fun n => n) := by
  intro n
  refine ⟨Unit, _, inferInstance, inferInstance, conReloj (lector n) () (fun _ _ => ()), ?_, by simp, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, pow_add]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.le_pow_clog one_lt_two _)
  · intro φ hφ
    classical
    refine ⟨_, (conReloj_corre (lector n) () (fun _ _ => ()) _ n () _).trans
      (lector_corre hφ n 0 (by omega) _ (fun j hj => absurd hj (by omega))), ?_⟩
    rw [decide_eq_true_iff]
    constructor
    · rintro ⟨ψ, hψ, hs⟩; rwa [encCNF.injective hψ] at hs
    · intro h; exact ⟨φ, rfl, h⟩

end NoUniforme

end Sagitta.Map.Informacion.TorreCHT
