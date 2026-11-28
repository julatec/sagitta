import Sagitta.Map.RaizMuertaFuerte
import Sagitta.Map.IntentoContradiccion

/-!
# Propagación unitaria: también paga `2^Ω(n log n)` en el palomar

Es el peldaño «propagación unitaria» de la escalera de detectores (ver las notas del proyecto). `RaizMuertaFuerte.lean` dejó la interfaz
(`Certifica`) y dijo que la propagación unitaria debería caer bajo ella. Aquí se escribe la propagación y se prueba que
cae.

## El detector

* Una **asignación parcial** es una función `ℕ → Option Bool` (`Parcial`). La de un prefijo `p` fija la variable `i`
  en `p[i]` y deja libres las demás (`iniParcial`).
* Un literal es **falso** si su variable está fijada con el signo contrario (`litFalso`). Una cláusula es **falsa** si
  todos sus literales lo son (`falsaParcial`).
* Una cláusula es **unitaria** en el literal `l` si `l` está libre y cada literal de la cláusula es falso o es `l`
  (`unitario`). La primera de `F` se busca con `buscaUnit`.
* **La propagación** (`propaga F k a`): si hay una cláusula falsa, dice «muerto». Si no, y hay una unitaria, fija su
  literal y repite, a lo sumo `k` veces. Si no hay ninguna, se detiene sin decir nada.
* `detUP F N p` es la propagación desde el prefijo `p`, con `N` rondas. `costoUP F N p` cuenta las rondas que hizo,
  más uno: a lo sumo `N + 1` (`costoUP_le`).

## Lo que se prueba

* `cert_propaga`: si la propagación llega a una cláusula falsa, hay un árbol de decisión de a lo sumo
  `pasosUP` hojas que, para toda asignación que concuerda con la parcial, llega a una cláusula falsa. El árbol pregunta
  cada variable propagada, en orden. La rama contraria al valor propagado termina en la cláusula unitaria que lo forzó,
  y esa cláusula queda falsa. Al final del camino está la cláusula falsa que encontró la propagación.
* `certifica_detUP`: `Certifica F N (detUP F N) (costoUP F N)`, con `costoUP ≤ N + 1`.
* `detUP_sano`: `detUP` es sano (`Sano`). Sale del mismo árbol (`sano_de_encuentra`).
* **El resultado** (`palomar_detUP_rondas`): sobre el palomar, la búsqueda con `detUP` hace, sumando las rondas de
  propagación de todos los nodos que visita, más de `(n + 1 − j)^j / 2`. En nodos (`palomar_detUP_nodos`):
  `(n + 1 − j)^j < 2 · nodos · (N + 1)`. Con `j = n/2` es `2^Ω(n log n)` (`palomar_detUP_mitad`).
* **Sin demora logarítmica** (`detUP_sin_demora_log`): como `detCNF_sin_demora_log` de `IntentoContradiccion.lean`.
  Para todos `a` y `b` hay un `n` tal que `detUP` no tiene demora `a · log₂(N + 1) + b` sobre la familia del palomar.

## Lo que NO se prueba

* El orden de las variables de la búsqueda es fijo, y no hay aprendizaje de cláusulas: esto es DPLL con propagación
  unitaria, no CDCL. Con aprendizaje la búsqueda deja de ser resolución tree-like y la cota de aquí no se aplica.
* El orden en que se propagan las cláusulas unitarias es uno fijo (la primera de `F`, el primer literal). El
  certificado no depende de ese orden, pero el teorema está escrito para este detector.
* Contar rondas no es tiempo de máquina: cada ronda recorre `F`, y eso no se cuenta. La cota inferior en rondas es la
  que importa; en tiempo real es mayor.
* Una cláusula con un literal repetido de signos opuestos (`x ∨ ¬x`) nunca es unitaria. Es conservador y no afecta la
  cota.
* Como en `RaizMuertaFuerte`, el contenido es la cota de resolución tree-like de cslib-frontier. Lo nuevo es ver que
  la propagación unitaria cabe en un árbol de decisión pequeño.
-/

open Cslib Cslib.Logic.PL

namespace Sagitta.Map
namespace Tiempo

/-! ## Asignaciones parciales -/

/-- Una asignación parcial: cada variable está fijada o libre. -/
abbrev Parcial : Type := ℕ → Option Bool

/-- La asignación parcial de un prefijo: fija la variable `i` en `p[i]`. -/
def iniParcial (p : List Bool) : Parcial := fun i => p[i]?

/-- El literal es falso: su variable está fijada con el signo contrario. -/
def litFalso (a : Parcial) (l : ℕ × Bool) : Bool := a l.1 == some (!l.2)

/-- La cláusula es falsa en la asignación parcial: todos sus literales son falsos. -/
def falsaParcial (a : Parcial) (c : Clausula) : Bool := c.all (litFalso a)

/-- El literal unitario de la cláusula, si lo hay: está libre, y los demás literales son falsos o son él mismo. -/
def unitario (a : Parcial) (c : Clausula) : Option (ℕ × Bool) :=
  c.find? fun l => (a l.1).isNone && c.all fun l' => litFalso a l' || l' == l

/-- El primer literal unitario de la fórmula. -/
def buscaUnit (F : List Clausula) (a : Parcial) : Option (ℕ × Bool) := F.findSome? (unitario a)

/-- Fijar el literal `l`: su variable toma su signo. -/
def asignaLit (a : Parcial) (l : ℕ × Bool) : Parcial := fun i => if i = l.1 then some l.2 else a i

/-- **La propagación unitaria, con `k` rondas**: si hay una cláusula falsa, dice «muerto». Si no, fija el primer
literal unitario y sigue. -/
def propaga (F : List Clausula) : ℕ → Parcial → Bool
  | 0, a => F.any (falsaParcial a)
  | k + 1, a =>
    if F.any (falsaParcial a) then true else
      match buscaUnit F a with
      | some l => propaga F k (asignaLit a l)
      | none => false

/-- **Las rondas de la propagación, más uno.** Es el tamaño del certificado. -/
def pasosUP (F : List Clausula) : ℕ → Parcial → ℕ
  | 0, _ => 1
  | k + 1, a =>
    if F.any (falsaParcial a) then 1 else
      match buscaUnit F a with
      | some l => 1 + pasosUP F k (asignaLit a l)
      | none => 1

/-- **El detector de propagación unitaria**: desde el prefijo `p`, con `N` rondas. -/
def detUP (F : List Clausula) (N : ℕ) (p : List Bool) : Bool := propaga F N (iniParcial p)

/-- El costo de una evaluación de `detUP`: las rondas más uno. -/
def costoUP (F : List Clausula) (N : ℕ) (p : List Bool) : ℕ := pasosUP F N (iniParcial p)

theorem pasosUP_le (F : List Clausula) : ∀ (k : ℕ) (a : Parcial), pasosUP F k a ≤ k + 1
  | 0, _ => le_refl _
  | k + 1, a => by
    unfold pasosUP
    split
    · omega
    · split
      · rename_i l _
        have := pasosUP_le F k (asignaLit a l); omega
      · omega

theorem pasosUP_pos (F : List Clausula) : ∀ (k : ℕ) (a : Parcial), 1 ≤ pasosUP F k a
  | 0, _ => le_refl _
  | k + 1, a => by
    unfold pasosUP
    split
    · omega
    · split <;> omega

/-- **Cada evaluación hace a lo sumo `N` rondas.** -/
theorem costoUP_le (F : List Clausula) (N : ℕ) (p : List Bool) : costoUP F N p ≤ N + 1 := pasosUP_le F N _

/-! ## Concordar con una asignación parcial -/

/-- `σ` concuerda con la asignación parcial `a` en las variables fijadas. -/
def Concuerda (σ : ℕ → Bool) (a : Parcial) : Prop := ∀ i b, a i = some b → σ i = b

theorem concuerda_ini {σ : ℕ → Bool} {p : List Bool} (h : Sigue σ p) : Concuerda σ (iniParcial p) := by
  intro i b hb
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hb
  rw [h i hlt, hget]

theorem concuerda_asigna {σ : ℕ → Bool} {a : Parcial} (h : Concuerda σ a) {l : ℕ × Bool} (hl : σ l.1 = l.2) :
    Concuerda σ (asignaLit a l) := by
  intro i b hb
  unfold asignaLit at hb
  split at hb
  · rename_i hi
    subst hi
    simp only [Option.some.injEq] at hb
    rw [hl, hb]
  · exact h i b hb

theorem litFalso_eval {σ : ℕ → Bool} {a : Parcial} (h : Concuerda σ a) {l : ℕ × Bool} (hl : litFalso a l = true) :
    Literal.eval σ l = false := by
  simp only [litFalso, beq_iff_eq] at hl
  have := h _ _ hl
  simp only [Literal.eval, this]
  cases l.2 <;> rfl

/-- Una cláusula falsa en la parcial es falsa en toda asignación que concuerda. -/
theorem falsaParcial_eval {σ : ℕ → Bool} {a : Parcial} (h : Concuerda σ a) {c : Clausula}
    (hc : falsaParcial a c = true) : Clause.eval σ c = false := by
  simp only [Clause.eval, List.any_eq_false]
  intro l hl
  have := List.all_eq_true.mp hc l hl
  simp [litFalso_eval h this]

theorem unitario_spec {a : Parcial} {c : Clausula} {l : ℕ × Bool} (h : unitario a c = some l) :
    l ∈ c ∧ ∀ l' ∈ c, litFalso a l' = true ∨ l' = l := by
  refine ⟨List.mem_of_find?_eq_some h, fun l' hl' => ?_⟩
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
  exact hp.2 l' hl'

/-- **La otra rama de un literal propagado falsifica su cláusula unitaria.** -/
theorem unitario_eval {σ : ℕ → Bool} {a : Parcial} (h : Concuerda σ a) {c : Clausula} {l : ℕ × Bool}
    (hu : unitario a c = some l) (hσ : σ l.1 ≠ l.2) : Clause.eval σ c = false := by
  obtain ⟨-, hall⟩ := unitario_spec hu
  simp only [Clause.eval, List.any_eq_false]
  intro l' hl'
  rcases hall l' hl' with hf | rfl
  · simp [litFalso_eval h hf]
  · simpa [Literal.eval] using hσ

/-! ## El certificado -/

/-- **La propagación cabe en un árbol de decisión.** Si llega a una cláusula falsa, hay un árbol de a lo sumo
`pasosUP` hojas que, para toda asignación que concuerda con `a`, llega a una cláusula de `F` falsa en ella. -/
theorem cert_propaga (F : List Clausula) :
    ∀ (k : ℕ) (a : Parcial), propaga F k a = true →
      ∃ t : DecisionTree ℕ Clausula, t.leafCount ≤ pasosUP F k a ∧
        ∀ σ, Concuerda σ a → t.eval σ ∈ F ∧ Clause.eval σ (t.eval σ) = false
  | 0, a, hp => by
    simp only [propaga, List.any_eq_true] at hp
    obtain ⟨c, hc, hf⟩ := hp
    exact ⟨.leaf c, by simp [pasosUP, DecisionTree.leafCount], fun σ hσ => ⟨hc, falsaParcial_eval hσ hf⟩⟩
  | k + 1, a, hp => by
    by_cases hd : F.any (falsaParcial a) = true
    · obtain ⟨c, hc, hf⟩ := List.any_eq_true.mp hd
      exact ⟨.leaf c, by simp [pasosUP, hd, DecisionTree.leafCount],
        fun σ hσ => ⟨hc, falsaParcial_eval hσ hf⟩⟩
    · cases hb : buscaUnit F a with
      | none => simp [propaga, hd, hb] at hp
      | some l =>
        have hp' : propaga F k (asignaLit a l) = true := by simpa [propaga, hd, hb] using hp
        obtain ⟨c, hc, hu⟩ := List.exists_of_findSome?_eq_some hb
        obtain ⟨t, ht, he⟩ := cert_propaga F k (asignaLit a l) hp'
        have hcnt : pasosUP F (k + 1) a = 1 + pasosUP F k (asignaLit a l) := by simp [pasosUP, hd, hb]
        refine ⟨if l.2 then .node l.1 (.leaf c) t else .node l.1 t (.leaf c), ?_, ?_⟩
        · rw [hcnt]; cases l.2 <;> simp [DecisionTree.leafCount] <;> omega
        · intro σ hσ
          by_cases hv : σ l.1 = l.2
          · have := he σ (concuerda_asigna hσ hv)
            cases h2 : l.2 <;> simp_all
          · have hev := unitario_eval hσ hu hv
            cases h2 : l.2 <;> cases h3 : σ l.1 <;> simp_all

/-- **`detUP` está certificado con costo `costoUP`** (a lo sumo `N + 1`). -/
theorem certifica_detUP (F : List Clausula) (N : ℕ) : Certifica F N (detUP F N) (costoUP F N) := by
  intro p _ hd
  obtain ⟨t, ht, he⟩ := cert_propaga F N (iniParcial p) hd
  exact ⟨t, ht, fun σ hs => he σ (concuerda_ini hs)⟩

/-! ## Sano -/

/-- Si un árbol encuentra cláusulas falsas debajo de `p`, ninguna extensión de `p` es solución. -/
theorem sano_de_encuentra {F : List Clausula} {p : List Bool} {t : DecisionTree ℕ Clausula}
    (he : EncuentraDebajo F p t) (q : List Bool) : solCNF F (p ++ q) = false := by
  set σ : ℕ → Bool := fun i => (p ++ q).getD i false
  have hs : Sigue σ p := by
    intro i hi
    simp [σ, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  obtain ⟨hmem, hev⟩ := he σ hs
  cases hsol : solCNF F (p ++ q)
  · rfl
  · simp only [solCNF, List.all_eq_true] at hsol
    have := hsol _ hmem
    simp only [satisface, List.any_eq_true, beq_iff_eq] at this
    obtain ⟨l, hl, hget⟩ := this
    have : Clause.eval σ (t.eval σ) = true := by
      simp only [Clause.eval, List.any_eq_true]
      exact ⟨l, hl, by simp [Literal.eval, σ, List.getD_eq_getElem?_getD, hget]⟩
    rw [hev] at this
    exact absurd this (by simp)

/-- **La propagación unitaria es un detector sano.** -/
theorem detUP_sano (F : List Clausula) (N : ℕ) : Sano (solCNF F) (detUP F N) := by
  intro p q hd
  obtain ⟨t, -, he⟩ := cert_propaga F N (iniParcial p) hd
  exact sano_de_encuentra (fun σ hs => he σ (concuerda_ini hs)) q

/-! ## El palomar -/

/-- **El resultado, en rondas**: la búsqueda con `detUP` sobre el palomar hace, sumando las rondas de propagación (más
uno) de todos los nodos que visita, más de `(n + 1 − j)^j / 2`. -/
theorem palomar_detUP_rondas {m n : ℕ} (j : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    let F : List Clausula := (CNF.pigeonhole m n).relabel f
    (n + 1 - j) ^ j < 2 * peso (solCNF F) (detUP F N) (costoUP F N) N [] :=
  palomar_certificado j hnm hn hf hN (fun _ => pasosUP_pos _ _ _) (certifica_detUP _ N)

/-- **En nodos**: `(n + 1 − j)^j < 2 · nodos · (N + 1)`. La propagación baja los nodos a lo sumo en el factor `N + 1`
de las rondas que hace cada evaluación. -/
theorem palomar_detUP_nodos {m n : ℕ} (j : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    let F : List Clausula := (CNF.pigeonhole m n).relabel f
    (n + 1 - j) ^ j < 2 * (nodos (solCNF F) (detUP F N) N [] * (N + 1)) := by
  intro F
  exact lt_of_lt_of_le (palomar_detUP_rondas j hnm hn hf hN)
    (Nat.mul_le_mul_left 2 (peso_le _ _ _ (costoUP_le F N) N []))

/-- **Con `j = n/2`**: `(n/2 + 1)^(n/2) < 2 · nodos · (N + 1)`. -/
theorem palomar_detUP_mitad {m n : ℕ} (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    let F : List Clausula := (CNF.pigeonhole m n).relabel f
    (n / 2 + 1) ^ (n / 2) < 2 * (nodos (solCNF F) (detUP F N) N [] * (N + 1)) :=
  lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) _) (palomar_detUP_nodos (n / 2) hnm hn hf hN)

/-- **La propagación unitaria no tiene demora logarítmica en el palomar.** Para todos `a` y `b` hay un `n` tal que
`detUP` (con `N = n(n+1)` rondas) no tiene demora `a · log₂(N + 1) + b` sobre la fórmula del palomar con `n + 1`
palomas y `n` nidos. -/
theorem detUP_sin_demora_log (a b : ℕ) :
    ∃ n, ¬ DemoraN (solCNF (formulaPal n)) (detUP (formulaPal n) (n * (n + 1))) (n * (n + 1))
      (a * Nat.log 2 (n * (n + 1) + 1) + b) := by
  set C := 2 ^ (b + 2) * 4 ^ (a + 2) with hCdef
  have hC : 1 ≤ C := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set e := 2 * a + 4
  set t := C + e
  refine ⟨2 * t, fun hd => ?_⟩
  set n := 2 * t with hn
  set N := n * (n + 1) with hN
  have hpos : 0 < n := by omega
  -- la cota inferior del palomar
  have hlow := palomar_detUP_mitad (m := n + 1) (n := n) (N := N) (by omega) hpos (ordenPal_inj n) (ordenPal_lt n)
  -- la cota superior con demora logarítmica
  have hup := nodos_le (k := N) (p := []) (sano_sanoN N (detUP_sano (formulaPal n) N)) hd (by simp)
  have hlog : 2 ^ (a * Nat.log 2 (N + 1) + b + 1) ≤ 2 ^ (b + 1) * (N + 1) ^ a := by
    rw [show a * Nat.log 2 (N + 1) + b + 1 = a * Nat.log 2 (N + 1) + (b + 1) by ring, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (dos_pow_mul_log_le a (N + 1) (by omega))
  have hN1 : N + 1 ≤ 4 * (t + 1) ^ 2 := by simp only [hN, hn]; nlinarith
  have hn2 : n / 2 = t := by omega
  rw [hn2] at hlow
  -- juntar: (t+1)^t < 2·nodos·(N+1) ≤ 2^(b+2)·(N+1)^(a+2) ≤ C·(t+1)^e
  have hbig : (t + 1) ^ t < C * (t + 1) ^ e := by
    calc (t + 1) ^ t < 2 * (nodos (solCNF (formulaPal n)) (detUP (formulaPal n) N) N [] * (N + 1)) := by
          simpa [formulaPal] using hlow
      _ ≤ 2 * (((N + 1) * 2 ^ (a * Nat.log 2 (N + 1) + b + 1)) * (N + 1)) := by gcongr
      _ ≤ 2 * (((N + 1) * (2 ^ (b + 1) * (N + 1) ^ a)) * (N + 1)) := by gcongr
      _ = 2 ^ (b + 2) * (N + 1) ^ (a + 2) := by ring
      _ ≤ 2 ^ (b + 2) * (4 * (t + 1) ^ 2) ^ (a + 2) := by gcongr
      _ = C * (t + 1) ^ e := by rw [hCdef, mul_pow, ← pow_mul]; ring
  exact lt_irrefl _ (lt_trans hbig (pow_gana C e hC))

/-! ## Controles -/

/-- Una cadena de implicaciones: `x0`, `x0 → x1`, `¬x1`. Ninguna cláusula es falsa en la raíz, pero propagar dos
veces llega a una. -/
def cadena3 : List Clausula := [[(0, true)], [(0, false), (1, true)], [(1, false)]]

-- `detCNF` no ve nada en la raíz; `detUP` con 2 rondas sí, y con 1 ronda todavía no: propaga de verdad.
example : detCNF cadena3 [] = false ∧ detUP cadena3 2 [] = true ∧ detUP cadena3 1 [] = false := by decide
-- El costo: 2 rondas, más uno.
example : costoUP cadena3 2 [] = 3 := by decide
-- La búsqueda con `detCNF` visita 5 nodos; con `detUP`, 1.
example : nodos (solCNF cadena3) (detCNF cadena3) 2 [] = 5 ∧
    nodos (solCNF cadena3) (detUP cadena3 2) 2 [] = 1 := by decide

/-- **`detUP` no es `detCNF` con otro nombre.** -/
theorem detUP_no_es_detCNF : detUP cadena3 2 ≠ detCNF cadena3 := fun h => by
  have := congrFun h []
  revert this
  decide

/-- **El certificado no puede tener una hoja menos**: en `cadena3`, ningún árbol de 2 hojas encuentra cláusulas
falsas debajo de la raíz. El `+ 1` de `costoUP` hace falta. -/
theorem cadena3_sin_arbol_de_dos :
    ¬ ∃ t : DecisionTree ℕ Clausula, t.leafCount ≤ 2 ∧ EncuentraDebajo cadena3 [] t := by
  rintro ⟨t, ht, he⟩
  have he' : ∀ σ, t.eval σ ∈ cadena3 ∧ Clause.eval σ (t.eval σ) = false :=
    fun σ => he σ (fun i hi => absurd hi (by simp))
  let s (a b : Bool) : ℕ → Bool := fun j => if j = 0 then a else if j = 1 then b else false
  have h00 := he' (s false false)
  have h01 := he' (s false true)
  have h10 := he' (s true false)
  have h11 := he' (s true true)
  cases t with
  | leaf c =>
    simp only [DecisionTree.eval_leaf, cadena3, List.mem_cons, List.not_mem_nil, or_false] at h00 h10
    rcases h10.1 with rfl | rfl | rfl <;> simp_all [s, Clause.eval, Literal.eval]
  | node i t0 t1 =>
    cases t0 with
    | node _ _ _ =>
      have := DecisionTree.leafCount_pos t1
      rename_i u v
      have := DecisionTree.leafCount_pos u
      have := DecisionTree.leafCount_pos v
      simp [DecisionTree.leafCount] at ht; omega
    | leaf c0 =>
    cases t1 with
    | node _ u v =>
      have := DecisionTree.leafCount_pos u
      have := DecisionTree.leafCount_pos v
      simp [DecisionTree.leafCount] at ht; omega
    | leaf c1 =>
      simp only [DecisionTree.eval_node, DecisionTree.eval_leaf, cadena3, List.mem_cons, List.not_mem_nil,
        or_false] at h00 h01 h10 h11
      by_cases hi0 : i = 0
      · subst hi0
        rcases h10.1 with rfl | rfl | rfl <;> simp_all [s, Clause.eval, Literal.eval]
      · by_cases hi1 : i = 1
        · subst hi1
          rcases h00.1 with rfl | rfl | rfl <;> simp_all [s, Clause.eval, Literal.eval]
        · have hs : ∀ a b, s a b i = false := fun a b => by simp [s, hi0, hi1]
          simp only [hs, Bool.cond_false] at h00 h01 h10 h11
          rcases h00.1 with rfl | rfl | rfl <;> simp_all [s, Clause.eval, Literal.eval]

-- Por eso `costoUP` no se puede bajar en uno: con `costoUP − 1` no está certificado.
example : ¬ Certifica cadena3 2 (detUP cadena3 2) (fun p => costoUP cadena3 2 p - 1) := fun h => by
  obtain ⟨t, ht, he⟩ := h [] (by simp) (by decide)
  exact cadena3_sin_arbol_de_dos ⟨t, by simpa [show costoUP cadena3 2 [] = 3 by decide] using ht, he⟩

-- La hipótesis del teorema principal se cumple en la familia del palomar: el orden `ordenPal 2` es inyectivo y cabe
-- en `N = 6` variables.
example : Function.Injective (ordenPal 2) := by decide
example : ∀ v : Fin 3 × Fin 2, ordenPal 2 v < 2 * (2 + 1) := by decide
-- Sobre `PHP^3_2`: `detCNF` visita 29 nodos y `detUP` 3, con 12 rondas en total. La propagación ayuda mucho en lo
-- pequeño; la cota dice que no alcanza en lo grande. La conclusión de `palomar_detUP_rondas` con `j = 1`: `2 < 24`.
example : nodos (solCNF (formulaPal 2)) (detCNF (formulaPal 2)) 6 [] = 29 ∧
    nodos (solCNF (formulaPal 2)) (detUP (formulaPal 2) 6) 6 [] = 3 ∧
    peso (solCNF (formulaPal 2)) (detUP (formulaPal 2) 6) (costoUP (formulaPal 2) 6) 6 [] = 12 := by decide
example : (2 + 1 - 1) ^ 1 < 2 * peso (solCNF (formulaPal 2)) (detUP (formulaPal 2) 6) (costoUP (formulaPal 2) 6) 6 [] :=
  palomar_detUP_rondas (m := 3) (n := 2) 1 (by omega) (by omega) (ordenPal_inj 2) (ordenPal_lt 2)

/- Mutantes probados fuera del repositorio (cada uno es una copia de este archivo con un solo cambio; todos fallan):
* `m1_no_fija`: la propagación no fija el literal (`propaga F k a` en vez de `propaga F k (asignaLit a l)`, lo mismo
  en `pasosUP`). Así es `detCNF` con más costo. Fallan los controles de `cadena3` y de `PHP^3_2` con `decide`.
* `m2_hoja_menos`: `pasosUP` sin el `1 +` de cada ronda (el certificado con una hoja menos). Falla `cert_propaga` en
  la cuenta de hojas. `cadena3_sin_arbol_de_dos` muestra que no es un problema de la prueba: esa cota es falsa.
* `m3_unit_sin_resto`: `unitario` sin pedir que los demás literales sean falsos. Falla `unitario_spec`, y con él el
  certificado y la sanidad.
* `m4_constante`: `detUP_sin_demora_log` con `4^(a+1)` (la constante de `detCNF_sin_demora_log`) en vez de `4^(a+2)`.
  Falla: el factor `N + 1` de las rondas cuesta un grado más.
-/

end Tiempo
end Sagitta.Map
