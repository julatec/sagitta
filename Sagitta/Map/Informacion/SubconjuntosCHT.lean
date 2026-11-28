import Sagitta.Map.Informacion.Homogeneidad
import Mathlib.Computability.NFA
import Mathlib.Data.List.GetD

/-!
# Los subconjuntos como CHT: el primer colapso demostrado como consecuencia de la CHT

**La heurística** (José, 25 nov 2026; notas del proyecto, «Los colapsos vistos desde la CHT»): un problema colapsa cuando la
dinámica no determinista admite una **cantidad conservada que cabe en el presupuesto**, de modo que un proceso homogéneo
y determinista, el mismo paso repetido, la lleva de un paso al siguiente. El caso más limpio es NFA → DFA: la
construcción de subconjuntos conserva la homogeneidad del tiempo y paga en memoria. Este archivo lo prueba con la CHT
de `Homogeneidad.lean`; es el **primer colapso demostrado como consecuencia de la CHT**.

## 1. La construcción de subconjuntos es homogénea

`subconjuntos M q sal` es un `Automata (Set σ) Q R Y` del cubo: su estado es el conjunto de estados vivos del NFA `M`,
lee como palabra las respuestas del verificador y su transición es la de `M.toDFA` (`subconjuntos_paso`). Es un
`Automata`, no un `AutomataConReloj`: la regla no recibe el paso, y con cualquier reloj que no mire corre igual
(`subconjuntos_sin_reloj`, el caso (a) de la CHT). **La cantidad conservada** es el conjunto vivo: tras `k` pasos, el
estado es exactamente `M.evalFrom` de las `k` respuestas oídas (`iterate_paso`). Hay una sola palabra y todas las ramas
la leen a la vez; por eso un conjunto basta para llevar el pasado. La carga de Noether de la CHT vale tal cual
(`subconjuntos_carga`), y en el lenguaje se lee así: dos prefijos que dejan vivo el mismo conjunto no se distinguen
con ninguna continuación (`noether_lenguaje`).

Contraste con `CuboNoDeterminista`: simular el NFA **camino por camino** (`fijarFin`) es homogeneizar un reloj de
elecciones (`fijarFin_es_homogeneizar`) y paga `⌈log₂(w+1)⌉` bits de contador más `2^w` adivinanzas. La construcción
de subconjuntos no adivina ni cuenta: guarda todas las ramas.

## 2. El colapso, como lenguaje

`colapsa_como_lenguaje`: `M.toDFA.accepts = M.accepts` (`NFA.toDFA_correct` de Mathlib). `colapsa_sin_tiempo`: el
estado del determinista tras leer `x` es el conjunto que el NFA tiene vivo tras leer `x`, un paso por símbolo. El
tiempo no se paga.

## 3. La ley del cubo, para los subconjuntos

`ley_subconjuntos` sale de `ley_cubo_reloj` con el reloj trivial (`κ = Unit`, `c = 0`) y memoria `S = |σ|` bits, sin
holgura porque `|Set σ| = 2^|σ|` (`card_subconjuntos`): `N ≤ 2^L · 2^s · min (t + 1) 2^(|σ| − 1)`, o en bits
`⌈log₂ N⌉ ≤ L + s + min ⌈log₂(t+1)⌉ (|σ| − 1)` (`ley_subconjuntos_log`). Qué dice: **se conserva** el conjunto vivo
(y con él la homogeneidad: el término del tiempo, `⌈log₂(t+1)⌉`, es el mismo que el de cada rama, y `c = 0`); **se
paga** en el eje del espacio, que pasa de `⌈log₂ |σ|⌉` bits (un estado del NFA) a `|σ|` bits; **dónde**: en el
término `S − 1` de la ley, nunca en `t`.

## 4. El costo en memoria es necesario

El lenguaje «el `k`-ésimo símbolo desde el final es `1`» (`kesimo k`) lo reconoce un NFA de `k + 1` estados
(`nfaKesimo`, `nfaKesimo_accepts`, para `k ≥ 1`), y **todo** DFA que lo reconozca tiene al menos `2^k` estados
(`dfa_kesimo_cota`: las `2^k` palabras de largo `k` llevan a estados distintos, porque si dos difieren en el lugar `i`,
`i` ceros más las separan). `colapsa_y_separa` junta todo: **colapsa como lenguaje, se separa en tamaño**. La cota es
exacta en `k = 1` (`cota_exacta_uno`: dos estados bastan, `2^(k+1)` no es cota).

## Lo que NO se prueba

* **Es un caso, no prueba la heurística.** Que todo colapso venga de una cantidad conservada chica no se prueba; aquí
  solo se muestra que este colapso es una instancia de la ley de la CHT.
* **CSP no se reduce a esto.** Los polimorfismos dan un algoritmo, pero el de Zhuk no es un conjunto vivo llevado paso
  a paso por una regla fija; la heurística describe un patrón, no el mecanismo.
* La construcción funciona porque todas las ramas leen el **mismo** símbolo al mismo tiempo. Con un verificador al que
  cada rama le pregunta otra cosa, el conjunto vivo no tiene una consulta común; `subconjuntos` toma la consulta como
  dato (`q : Set σ → Q`) y no resuelve eso.
* La ley es la del verificador de sí o no (`R = Bool`); la cota inferior de `kesimo` es de lenguajes, no del cubo.
  No se prueba que la memoria `|σ|` sea necesaria **en el cubo**.
* Como todo el cubo, es caja negra y relativiza: nada sobre `P` contra `NP`.
-/

namespace Sagitta.Map.Informacion.SubconjuntosCHT

open Sagitta.Map.Tiempo.LeyTresMemorias
open Sagitta.Map.Tiempo.CuboCostos
open Sagitta.Map.Tiempo.CuboNoDeterminista
open Sagitta.Map.Informacion.Homogeneidad

/-! ## 1. La construcción de subconjuntos como sistema homogéneo -/

section Homogeneo

variable {σ Q R Y : Type}

/-- **La construcción de subconjuntos como autómata del cubo.** El estado es el conjunto de estados vivos del NFA `M`;
la palabra que lee son las respuestas del verificador, y la transición es la de `M.toDFA` (`NFA.stepSet`). La consulta
y la salida las pone el que la usa. Es un `Automata`: la regla no recibe el paso. -/
def subconjuntos (M : NFA R σ) (q : Set σ → Q) (sal : Set σ → Option Y) : Automata (Set σ) Q R Y where
  inicio := M.start
  consulta := q
  δ := M.toDFA.step
  salida := sal

/-- **La misma regla en cada paso**: un paso es `stepSet` del conjunto vivo con la respuesta oída, y nada más. -/
theorem subconjuntos_paso (M : NFA R σ) (q : Set σ → Q) (sal : Set σ → Option Y) (O : Q → R) (S : Set σ) :
    paso (subconjuntos M q sal) O S = M.stepSet S (O (q S)) := rfl

/-- **Sin reloj**: con cualquier reloj que no mira, la corrida es la misma (el caso (a) de la CHT). -/
theorem subconjuntos_sin_reloj {κ : Type} (M : NFA R σ) (q : Set σ → Q) (sal : Set σ → Option Y) (k₀ : κ)
    (tic : κ → Set σ → κ) (O : Q → R) (t : ℕ) (k : κ) (S : Set σ) :
    (conReloj (subconjuntos M q sal) k₀ tic).corre O t k S = (subconjuntos M q sal).corre O t S :=
  conReloj_corre _ _ _ _ _ _ _

/-- Las respuestas que oye la corrida, en orden: la palabra que lee. -/
def oidas (M : NFA R σ) (q : Set σ → Q) (O : Q → R) : ℕ → Set σ → List R
  | 0, _ => []
  | k + 1, S => O (q S) :: oidas M q O k (M.stepSet S (O (q S)))

theorem oidas_length (M : NFA R σ) (q : Set σ → Q) (O : Q → R) : ∀ k S, (oidas M q O k S).length = k
  | 0, _ => rfl
  | k + 1, _ => by simp [oidas, oidas_length M q O k]

/-- **La cantidad conservada**: después de `k` pasos, el estado es exactamente el conjunto de estados del NFA
alcanzables leyendo las `k` respuestas oídas (`NFA.evalFrom`). Cada rama del NFA lee la misma palabra al mismo
tiempo, así que el conjunto vivo es todo lo que hace falta del pasado. -/
theorem iterate_paso (M : NFA R σ) (q : Set σ → Q) (sal : Set σ → Option Y) (O : Q → R) :
    ∀ k S, (paso (subconjuntos M q sal) O)^[k] S = M.evalFrom S (oidas M q O k S)
  | 0, S => rfl
  | k + 1, S => by
      rw [Function.iterate_succ_apply, subconjuntos_paso, iterate_paso M q sal O k, oidas, NFA.evalFrom_cons]

/-- **La carga de Noether, para los subconjuntos**: dos corridas que llegan al mismo conjunto vivo, en tiempos `i` y
`j` y sin haber parado, siguen igual. Es `carga_noether` de la CHT, instanciada. -/
theorem subconjuntos_carga (M : NFA R σ) (q : Set σ → Q) (sal : Set σ → Option Y) (O : Q → R) {S S' : Set σ}
    {i j : ℕ} (hi : ∀ k < i, sal ((paso (subconjuntos M q sal) O)^[k] S) = none)
    (hj : ∀ k < j, sal ((paso (subconjuntos M q sal) O)^[k] S') = none)
    (h : M.evalFrom S (oidas M q O i S) = M.evalFrom S' (oidas M q O j S')) (t : ℕ) :
    (subconjuntos M q sal).corre O (i + t) S = (subconjuntos M q sal).corre O (j + t) S' :=
  (carga_noether (subconjuntos M q sal) O hi hj (by rw [iterate_paso, iterate_paso, h]) t).1

/-- **La carga de Noether, para el lenguaje**: si dos prefijos dejan vivo el mismo conjunto, ninguna continuación los
distingue. Cuánto se tardó en llegar (el largo del prefijo) no deja huella fuera del conjunto. -/
theorem noether_lenguaje {α : Type} (M : NFA α σ) {u v : List α} (h : M.eval u = M.eval v) (w : List α) :
    u ++ w ∈ M.accepts ↔ v ++ w ∈ M.accepts := by
  rw [← M.toDFA_correct, DFA.mem_accepts, DFA.mem_accepts]
  simp only [DFA.eval, DFA.evalFrom_of_append]
  exact Iff.of_eq (congrArg (fun S => M.toDFA.evalFrom S w ∈ M.toDFA.accept) h)

/-- **El precio**: `|Set σ| = 2^|σ|`. La memoria pasa de `⌈log₂ |σ|⌉` bits (un estado del NFA) a `|σ|` bits. -/
theorem card_subconjuntos [Fintype σ] : Fintype.card (Set σ) = 2 ^ Fintype.card σ := Fintype.card_set

end Homogeneo

/-! ## 2. El colapso como lenguaje -/

/-- **El colapso, como lenguaje**: el autómata de subconjuntos, determinista y homogéneo, acepta lo mismo que el NFA
(`NFA.toDFA_correct` de Mathlib). -/
theorem colapsa_como_lenguaje {α σ : Type} (M : NFA α σ) : M.toDFA.accepts = M.accepts := M.toDFA_correct

/-- **Sin pagar tiempo**: el determinista da un paso por símbolo, el mismo que cada rama del NFA; su estado tras leer
`x` es el conjunto que el NFA tiene vivo tras leer `x`. -/
theorem colapsa_sin_tiempo {α σ : Type} (M : NFA α σ) (x : List α) : M.toDFA.eval x = M.eval x := rfl

/-! ## 3. La ley del cubo para el autómata de subconjuntos -/

section Ley

variable {P C σ Y : Type} [Fintype P] [Fintype C] [Fintype σ] [Fintype Y] [DecidableEq Y]

/-- **La ley de la CHT para los subconjuntos.** Un resolvedor del cubo cuyos autómatas son construcciones de
subconjuntos de NFA sobre `σ` (que leen las respuestas sí/no del verificador) cumple
`N ≤ 2^L · 2^s · min (t + 1) 2^(|σ| − 1)`. Se obtiene de `ley_cubo_reloj` con un reloj trivial (`κ = Unit`, `c = 0`)
y memoria `S = |σ|` bits, exacta: `|Set σ| = 2^|σ|`. -/
theorem ley_subconjuntos {L s t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (M : P → C → NFA Bool σ) (q : P → C → Set σ → Y) (sal : P → C → Set σ → Option Y)
    (h : ResuelveA igual (fun p c => subconjuntos (M p c) (q p c) (sal p c)) t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (t + 1) (2 ^ (Fintype.card σ - 1)) := by
  have := ley_cubo_reloj (κ := Unit) (S := Fintype.card σ) (c := 0) hP hC (by rw [Fintype.card_set])
    (by simp) (fun p c => conReloj (subconjuntos (M p c) (q p c) (sal p c)) () (fun _ _ => ()))
    (fun y => by
      obtain ⟨p, c, hy⟩ := h y
      exact ⟨p, c, (conReloj_corre _ _ _ _ _ _ _).trans hy⟩)
  simpa using this

/-- **En bits**: `⌈log₂ N⌉ ≤ L + s + min ⌈log₂(t+1)⌉ (|σ| − 1)`. -/
theorem ley_subconjuntos_log {L s t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s)
    (M : P → C → NFA Bool σ) (q : P → C → Set σ → Y) (sal : P → C → Set σ → Option Y)
    (h : ResuelveA igual (fun p c => subconjuntos (M p c) (q p c) (sal p c)) t) :
    Nat.clog 2 (Fintype.card Y) ≤ L + s + min (Nat.clog 2 (t + 1)) (Fintype.card σ - 1) :=
  ley_cubo_log hP hC (by rw [Fintype.card_set]) _ h

end Ley

/-! ## 4. El costo en memoria es necesario: el `k`-ésimo símbolo desde el final -/

/-- **El lenguaje «el `k`-ésimo símbolo desde el final es `1`»** (`true`). -/
def kesimo (k : ℕ) : Language Bool := {x | k ≤ x.length ∧ x.getD (x.length - k) false = true}

theorem mem_kesimo {k : ℕ} {x : List Bool} : x ∈ kesimo k ↔ k ≤ x.length ∧ x.getD (x.length - k) false = true :=
  Iff.rfl

/-- Pegarle `i < k` ceros a una palabra de largo `k` pone su símbolo `i` en el lugar `k`-ésimo desde el final. -/
theorem mem_kesimo_ofFn {k : ℕ} (w : Fin k → Bool) (i : Fin k) :
    List.ofFn w ++ List.replicate i.val false ∈ kesimo k ↔ w i = true := by
  rw [mem_kesimo]
  simp only [List.length_append, List.length_ofFn, List.length_replicate]
  rw [show k + i.val - k = i.val by omega, List.getD_append _ _ _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp

/-- **La cota inferior**: todo DFA que reconoce `kesimo k` tiene al menos `2^k` estados. Las `2^k` palabras de largo
`k` llevan a estados distintos: si dos difieren en el lugar `i`, `i` ceros más las separan. -/
theorem dfa_kesimo_cota {τ : Type} [Fintype τ] (k : ℕ) (D : DFA Bool τ) (hD : D.accepts = kesimo k) :
    2 ^ k ≤ Fintype.card τ := by
  have hinj : Function.Injective fun u : Fin k → Bool => D.eval (List.ofFn u) := by
    intro u v huv
    funext i
    have e : D.eval (List.ofFn u ++ List.replicate i.val false) =
        D.eval (List.ofFn v ++ List.replicate i.val false) := by
      simp only [DFA.eval, DFA.evalFrom_of_append] at huv ⊢
      rw [huv]
    have hu := mem_kesimo_ofFn u i
    have hv := mem_kesimo_ofFn v i
    rw [← hD, DFA.mem_accepts, e, ← DFA.mem_accepts, hD, hv] at hu
    cases hui : u i <;> cases hvi : v i <;> simp_all
  simpa using Fintype.card_le_of_injective _ hinj

/-- **El NFA de `k + 1` estados**: el `0` se queda y, si lee `1`, adivina que es el `k`-ésimo desde el final y salta
al `1`; de ahí cuenta `k − 1` símbolos más hasta `k`, que acepta. -/
def nfaKesimo (k : ℕ) : NFA Bool (Fin (k + 1)) where
  step i a := {j | (i.val = 0 ∧ j.val = 0) ∨ (i.val = 0 ∧ a = true ∧ j.val = 1) ∨ (0 < i.val ∧ j.val = i.val + 1)}
  start := {j | j.val = 0}
  accept := {j | j.val = k}

theorem mem_eval_nfaKesimo (k : ℕ) (x : List Bool) (j : Fin (k + 1)) :
    j ∈ (nfaKesimo k).eval x ↔
      j.val = 0 ∨ (0 < j.val ∧ j.val ≤ x.length ∧ x.getD (x.length - j.val) false = true) := by
  induction x using List.reverseRecOn generalizing j with
  | nil => simp [nfaKesimo, NFA.eval]
  | append_singleton x a ih =>
      rw [NFA.eval_append_singleton, NFA.mem_stepSet]
      simp only [List.length_append, List.length_singleton]
      constructor
      · rintro ⟨i, hi, hj⟩
        simp only [nfaKesimo, Set.mem_ofPred_eq] at hj
        rw [ih] at hi
        rcases hj with ⟨-, h0⟩ | ⟨h0, ha, h1⟩ | ⟨hpos, hs⟩
        · exact Or.inl h0
        · subst ha
          refine Or.inr ⟨by omega, by omega, ?_⟩
          rw [show x.length + 1 - j.val = x.length by omega, List.getD_append_right _ _ _ _ le_rfl]
          simp
        · rcases hi with hi | ⟨-, hle, hg⟩
          · omega
          · refine Or.inr ⟨by omega, by omega, ?_⟩
            rw [show x.length + 1 - j.val = x.length - i.val by omega,
              List.getD_append _ _ _ _ (by omega)]
            exact hg
      · rintro (h0 | ⟨hpos, hle, hg⟩)
        · exact ⟨⟨0, by omega⟩, (ih _).2 (Or.inl rfl), Or.inl ⟨rfl, h0⟩⟩
        · by_cases h1 : j.val = 1
          · refine ⟨⟨0, by omega⟩, (ih _).2 (Or.inl rfl), Or.inr (Or.inl ⟨rfl, ?_, h1⟩)⟩
            rw [show x.length + 1 - j.val = x.length by omega, List.getD_append_right _ _ _ _ le_rfl] at hg
            simpa using hg
          · refine ⟨⟨j.val - 1, by omega⟩, (ih _).2 (Or.inr ⟨by simp; omega, by simp; omega, ?_⟩),
              Or.inr (Or.inr ⟨by simp; omega, by simp; omega⟩)⟩
            rw [show x.length + 1 - j.val = x.length - (j.val - 1) by omega,
              List.getD_append _ _ _ _ (by omega)] at hg
            simpa using hg

/-- **El NFA reconoce el lenguaje**, para `k ≥ 1`. -/
theorem nfaKesimo_accepts {k : ℕ} (hk : 0 < k) : (nfaKesimo k).accepts = kesimo k := by
  ext x
  rw [NFA.mem_accepts]
  constructor
  · rintro ⟨j, hj, hm⟩
    simp only [nfaKesimo, Set.mem_ofPred_eq] at hj
    rw [← NFA.eval, mem_eval_nfaKesimo] at hm
    rcases hm with h0 | ⟨-, hle, hg⟩
    · omega
    · rw [hj] at hle hg; exact mem_kesimo.2 ⟨hle, hg⟩
  · rintro ⟨hle, hg⟩
    refine ⟨⟨k, by omega⟩, rfl, ?_⟩
    rw [← NFA.eval, mem_eval_nfaKesimo]
    exact Or.inr ⟨hk, hle, hg⟩

/-- **Colapsa como lenguaje, se separa en tamaño.** Para `k ≥ 1`, el lenguaje «el `k`-ésimo desde el final es `1`» lo
reconoce un NFA de `k + 1` estados; su construcción de subconjuntos lo reconoce de forma determinista y homogénea,
con `2^(k+1)` estados; y **todo** DFA que lo reconozca tiene al menos `2^k`. El colapso paga memoria, y la paga
necesariamente: de `⌈log₂(k+1)⌉` bits a `k` bits por lo menos. -/
theorem colapsa_y_separa {k : ℕ} (hk : 0 < k) :
    (nfaKesimo k).accepts = kesimo k ∧ Fintype.card (Fin (k + 1)) = k + 1 ∧
      (nfaKesimo k).toDFA.accepts = kesimo k ∧ Fintype.card (Set (Fin (k + 1))) = 2 ^ (k + 1) ∧
      ∀ (τ : Type) [Fintype τ] (D : DFA Bool τ), D.accepts = kesimo k → 2 ^ k ≤ Fintype.card τ := by
  refine ⟨nfaKesimo_accepts hk, by simp, by rw [colapsa_como_lenguaje, nfaKesimo_accepts hk], by simp, ?_⟩
  intro τ _ D hD
  exact dfa_kesimo_cota k D hD

/-- **El último símbolo, con dos estados**: el DFA que recuerda lo último que leyó. -/
def dfaUltimo : DFA Bool Bool where
  step _ a := a
  start := false
  accept := {true}

theorem dfaUltimo_accepts : dfaUltimo.accepts = kesimo 1 := by
  ext x
  rw [DFA.mem_accepts, mem_kesimo]
  induction x using List.reverseRecOn with
  | nil => simp [dfaUltimo]
  | append_singleton x a _ =>
      rw [DFA.eval_append_singleton]
      simp only [List.length_append, List.length_singleton]
      rw [show x.length + 1 - 1 = x.length by omega, List.getD_append_right _ _ _ _ le_rfl]
      simp [dfaUltimo]

/-- **La cota es exacta en `k = 1`**: hay un DFA de `2^1` estados para `kesimo 1`, así que `2^(k+1)` no vale como cota
inferior. Es el control de `dfa_kesimo_cota`. -/
theorem cota_exacta_uno :
    dfaUltimo.accepts = kesimo 1 ∧ Fintype.card Bool = 2 ^ 1 ∧ ¬ (2 ^ (1 + 1) ≤ Fintype.card Bool) :=
  ⟨dfaUltimo_accepts, rfl, by decide⟩

end Sagitta.Map.Informacion.SubconjuntosCHT

section Axiomas
open Sagitta.Map.Informacion.SubconjuntosCHT
#print axioms iterate_paso
#print axioms subconjuntos_carga
#print axioms noether_lenguaje
#print axioms ley_subconjuntos
#print axioms ley_subconjuntos_log
#print axioms dfa_kesimo_cota
#print axioms nfaKesimo_accepts
#print axioms colapsa_y_separa
#print axioms cota_exacta_uno
end Axiomas
