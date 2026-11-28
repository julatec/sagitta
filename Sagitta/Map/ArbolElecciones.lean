import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# El árbol de elecciones: equivocarse sin probabilidad (E0)

Primera fase del plan rearmado. El costo de equivocarse, sin
probabilidad y sin suponer un «mundo bueno».

## El modelo

* **Un nodo** es una asignación parcial `p : List Bool`; faltan `k` variables.
* **Vivo** (`Vivo sol k p`): alguna forma de completar `p` con `k` valores es solución. **Muerto**: ninguna.
* **Error** (`Error`): pasar de un nodo vivo a un hijo muerto. No depende de cuál solución se tome como referencia.
* **Detector** `det`: mira un nodo y puede decir «muerto». Es **sano** (`Sano`) si nunca se equivoca al decirlo. Ejemplo:
  «hay una cláusula falsa» (`detCNF`, `detCNF_sano`).
* **Demora** `d` (`Demora`): el detector reconoce todo nodo muerto, a más tardar, `d` niveles más abajo.
* **La vuelta atrás** (`buscar`): si el detector dice muerto, vuelve; si no, prueba `false` y, si esa rama falla, `true`.
  Devuelve si encontró y cuántos nodos visitó (`nodos`). Es un número exacto, no un promedio.

## Lo que se prueba

* **Es correcta** (`buscar_correcto`): encuentra si y solo si el nodo está vivo.
* **Un error cuesta a lo sumo el subárbol que tarda en detectarse** (`costo_detectado`): `2^(d+1) − 1` nodos.
* **La frontera, sin azar** (`costo_vivo`): con demora `d`, la vuelta atrás visita a lo sumo `k · 2^(d+1) + 1` nodos.
  Es polinomial si `d = O(log n)`. Cada nivel comete a lo sumo un error, y cada error cuesta a lo sumo `2^(d+1)`.
* **Con un detector perfecto** (`con_detector_perfecto`): `d = 0`, y buscar cuesta `2k + 1`. Pero un detector perfecto
  decide si una fórmula tiene solución: es SAT mismo.

**Fe de erratas (23 nov, hallazgo de una revisión posterior).** `Demora` cuantifica sobre todo `k`, incluido `k = 0`. En una CNF,
`solCNF` de un prefijo parcial es `false`, así que la raíz está «muerta con 0 variables por fijar», y `Demora d` le pide al
detector que dispare sobre **toda** lista de largo `d`. Un detector sano no puede si la fórmula tiene solución. Por eso
`costo_vivo` y `con_detector_perfecto` son verdaderos pero **vacíos para toda CNF con solución**
(`demora_global_degenera` en `DemoraEfectiva.lean`). La versión correcta usa un horizonte fijo `N` (`SanoN`, `DemoraN`) y
está probada en `DemoraEfectiva.lean`: `buscar_correctoN`, `costo_vivoN`, `costo_muertoN`. Aquí `Demora` se deja como
estaba porque otros archivos la usan. Lo demás de este archivo no depende de `Demora`: `buscar_correcto`,
`costo_detectado`, `sin_detector_muerto`, `a_ciegas_unica`, `error_unica_iff` y `detCNF_sano`, y tampoco
`RaizMuerta.lean`. Los controles del final no lo detectaron porque calculan `nodos` por cómputo sin pasar por la
hipótesis `Demora`.
* **Sin detector** (`sin_detector_muerto`, `a_ciegas_unica`): certificar que no hay solución cuesta **todo** el árbol,
  `2^(k+1) − 1` nodos, y encontrar la única solución en el peor lugar cuesta lo mismo.
* **El mundo bueno, como caso particular** (`error_unica_iff`): con una sola solución, equivocarse es exactamente
  apartarse de ella. Con varias, contar contra una sola cuenta errores de más (`varias_sobrecuenta`).
-/

namespace Sagitta.Map
namespace Tiempo

variable (sol det : List Bool → Bool)

/-! ## Vivo y muerto -/

/-- **`p` está vivo con `k` variables por fijar**: alguna forma de completarlo es solución. -/
def Vivo (k : ℕ) (p : List Bool) : Prop := ∃ q : List Bool, q.length = k ∧ sol (p ++ q) = true

theorem vivo_cero (p : List Bool) : Vivo sol 0 p ↔ sol p = true := by
  constructor
  · rintro ⟨q, hq, h⟩
    rw [List.length_eq_zero_iff.mp hq, List.append_nil] at h
    exact h
  · intro h; exact ⟨[], rfl, by simpa using h⟩

theorem vivo_succ (k : ℕ) (p : List Bool) :
    Vivo sol (k + 1) p ↔ Vivo sol k (p ++ [false]) ∨ Vivo sol k (p ++ [true]) := by
  constructor
  · rintro ⟨q, hq, h⟩
    match q, hq with
    | b :: q', hq =>
      have hq' : q'.length = k := by simpa using hq
      have e : p ++ b :: q' = p ++ [b] ++ q' := by simp
      rw [e] at h
      cases b
      · exact .inl ⟨q', hq', h⟩
      · exact .inr ⟨q', hq', h⟩
  · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · exact ⟨false :: q, by simp [hq], by simpa using h⟩
    · exact ⟨true :: q, by simp [hq], by simpa using h⟩

/-- **El detector es sano**: si dice «muerto», ninguna extensión es solución. -/
def Sano : Prop := ∀ p q : List Bool, det p = true → sol (p ++ q) = false

theorem sano_muerto {sol det} (hs : Sano sol det) {k : ℕ} {p : List Bool} (h : det p = true) : ¬ Vivo sol k p := by
  rintro ⟨q, -, hq⟩
  rw [hs p q h] at hq
  exact Bool.false_ne_true hq

/-! ## La vuelta atrás -/

/-- **La vuelta atrás**: si el detector dice muerto, vuelve; si no, prueba `false` y, si esa rama falla, `true`.
Devuelve si encontró solución y cuántos nodos visitó. -/
def buscar : ℕ → List Bool → Bool × ℕ
  | 0, p => if det p then (false, 1) else (sol p, 1)
  | k + 1, p =>
    if det p then (false, 1) else
      if (buscar k (p ++ [false])).1 then (true, (buscar k (p ++ [false])).2 + 1)
      else ((buscar k (p ++ [true])).1, (buscar k (p ++ [false])).2 + (buscar k (p ++ [true])).2 + 1)

/-- Los nodos que visita la vuelta atrás. -/
def nodos (k : ℕ) (p : List Bool) : ℕ := (buscar sol det k p).2

/-- **La vuelta atrás es correcta**: encuentra si y solo si el nodo está vivo. -/
theorem buscar_correcto {sol det} (hs : Sano sol det) :
    ∀ (k : ℕ) (p : List Bool), (buscar sol det k p).1 = true ↔ Vivo sol k p
  | 0, p => by
    rw [vivo_cero]
    by_cases hd : det p = true
    · simp only [buscar, hd, ite_true, Bool.false_eq_true, false_iff]
      have := hs p [] hd
      simp only [List.append_nil] at this
      simp [this]
    · simp [buscar, hd]
  | k + 1, p => by
    rw [vivo_succ]
    by_cases hd : det p = true
    · simp only [buscar, hd, ite_true, Bool.false_eq_true, false_iff]
      have := sano_muerto hs (k := k + 1) hd
      rw [vivo_succ] at this
      exact this
    · have hf := buscar_correcto hs k (p ++ [false])
      have ht := buscar_correcto hs k (p ++ [true])
      by_cases ha : (buscar sol det k (p ++ [false])).1 = true
      · simp only [buscar, hd, ha, ite_true, Bool.false_eq_true, ite_false, true_iff]
        exact .inl (hf.mp ha)
      · simp only [buscar, hd, ha, Bool.false_eq_true, ite_false]
        rw [ht]
        constructor
        · exact .inr
        · rintro (h | h)
          · exact absurd (hf.mpr h) ha
          · exact h

/-! ## Lo que cuesta un error -/

/-- **Un subárbol que el detector reconoce a profundidad `e` cuesta a lo sumo `2^(e+1) − 1` nodos.** -/
theorem costo_detectado : ∀ (e k : ℕ) (p : List Bool),
    (∀ q : List Bool, q.length = e → det (p ++ q) = true) → nodos sol det k p + 1 ≤ 2 ^ (e + 1)
  | 0, k, p, h => by
    have hd : det p = true := by simpa using h [] rfl
    cases k <;> simp [nodos, buscar, hd]
  | e + 1, 0, p, _ => by
    have : 2 ≤ 2 ^ (e + 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold nodos buscar
    split <;> omega
  | e + 1, k + 1, p, h => by
    have hb : ∀ b : Bool, ∀ q : List Bool, q.length = e → det (p ++ [b] ++ q) = true := fun b q hq => by
      have := h (b :: q) (by simp [hq])
      simpa using this
    have cf := costo_detectado e k (p ++ [false]) (hb false)
    have ct := costo_detectado e k (p ++ [true]) (hb true)
    unfold nodos at cf ct ⊢
    have e2 : 2 ^ (e + 1 + 1) = 2 * 2 ^ (e + 1) := by ring
    rw [e2]
    unfold buscar
    split
    · have : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
      simp only; omega
    · split <;> simp only <;> omega

/-! ## Demora y la frontera sin azar -/

/-- **Demora `d`**: el detector reconoce todo nodo muerto, a más tardar, `d` niveles más abajo.

**Cuidado**: cuantifica sobre todo `k`, y en una CNF con solución es insatisfacible por un detector sano (ver la fe de
erratas del módulo). Usar `DemoraN`, con horizonte, de `DemoraEfectiva.lean`. -/
def Demora (d : ℕ) : Prop :=
  ∀ (k : ℕ) (p : List Bool), ¬ Vivo sol k p → ∀ q : List Bool, q.length = d → det (p ++ q) = true

/-- **La frontera, sin azar**: con demora `d`, la vuelta atrás desde un nodo vivo visita a lo sumo `k · 2^(d+1) + 1`
nodos. Cada nivel comete a lo sumo un error, y cada error cuesta a lo sumo `2^(d+1) − 1`. -/
theorem costo_vivo {sol det} (hs : Sano sol det) {d : ℕ} (hd : Demora sol det d) :
    ∀ (k : ℕ) (p : List Bool), Vivo sol k p → nodos sol det k p ≤ k * 2 ^ (d + 1) + 1
  | 0, p, _ => by unfold nodos buscar; split <;> simp
  | k + 1, p, hv => by
    have hdp : det p = false := by
      by_contra h
      exact sano_muerto hs (Bool.eq_true_of_not_eq_false h) hv
    have hf := buscar_correcto hs k (p ++ [false])
    have hpow : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
    unfold nodos
    by_cases hvf : Vivo sol k (p ++ [false])
    · have ha : (buscar sol det k (p ++ [false])).1 = true := hf.mpr hvf
      have ih := costo_vivo hs hd k (p ++ [false]) hvf
      unfold nodos at ih
      simp only [buscar, hdp, ha, Bool.false_eq_true, ite_false, ite_true]
      nlinarith
    · have ha : (buscar sol det k (p ++ [false])).1 = false := by
        cases h : (buscar sol det k (p ++ [false])).1
        · rfl
        · exact absurd (hf.mp h) hvf
      have hvt : Vivo sol k (p ++ [true]) := ((vivo_succ sol k p).mp hv).resolve_left hvf
      have ih := costo_vivo hs hd k (p ++ [true]) hvt
      have hm := costo_detectado sol det d k (p ++ [false]) (hd k _ hvf)
      unfold nodos at ih hm
      simp only [buscar, hdp, ha, Bool.false_eq_true, ite_false]
      nlinarith

/-- **Un nodo muerto cuesta a lo sumo `2^(d+1) − 1`.** -/
theorem costo_muerto {d : ℕ} (hd : Demora sol det d) {k : ℕ} {p : List Bool} (hm : ¬ Vivo sol k p) :
    nodos sol det k p + 1 ≤ 2 ^ (d + 1) :=
  costo_detectado sol det d k p (hd k p hm)

/-- **Con un detector perfecto** (demora 0), buscar cuesta `2k + 1`. Un detector así decide si hay solución: es el
problema mismo. -/
theorem con_detector_perfecto {sol det} (hs : Sano sol det) (hd : Demora sol det 0) {k : ℕ} {p : List Bool}
    (hv : Vivo sol k p) : nodos sol det k p ≤ 2 * k + 1 := by
  have := costo_vivo hs hd k p hv
  simpa [mul_comm] using this

/-! ## Sin detector: a ciegas -/

/-- El detector que nunca dice nada. -/
def nunca : List Bool → Bool := fun _ => false

theorem nunca_sano : Sano sol nunca := fun _ _ h => absurd h (by simp [nunca])

/-- **Sin detector, certificar que no hay solución cuesta todo el árbol**: `2^(k+1) − 1` nodos. -/
theorem sin_detector_muerto : ∀ (k : ℕ) (p : List Bool), ¬ Vivo sol k p → nodos sol nunca k p + 1 = 2 ^ (k + 1)
  | 0, p, hm => by
    have : sol p = false := by
      cases h : sol p
      · rfl
      · exact absurd ((vivo_cero sol p).mpr h) hm
    simp [nodos, buscar, nunca]
  | k + 1, p, hm => by
    have hb : ∀ b, ¬ Vivo sol k (p ++ [b]) := fun b h => hm ((vivo_succ sol k p).mpr (by cases b <;> simp [h]))
    have ha : (buscar sol nunca k (p ++ [false])).1 = false := by
      cases h : (buscar sol nunca k (p ++ [false])).1
      · rfl
      · exact absurd ((buscar_correcto (nunca_sano sol) k _).mp h) (hb false)
    have cf := sin_detector_muerto k (p ++ [false]) (hb false)
    have ct := sin_detector_muerto k (p ++ [true]) (hb true)
    unfold nodos at cf ct ⊢
    simp only [buscar, nunca, ha, Bool.false_eq_true, ite_false]
    rw [pow_succ]
    omega

/-- **A ciegas, con la única solución en el peor lugar** (todo `true`, que la vuelta atrás prueba último), encontrarla
también cuesta todo el árbol. -/
theorem a_ciegas_unica : ∀ (k : ℕ) (p : List Bool),
    (∀ q : List Bool, q.length = k → (sol (p ++ q) = true ↔ q = List.replicate k true)) →
      nodos sol nunca k p + 1 = 2 ^ (k + 1)
  | 0, p, h => by
    have : sol p = true := by simpa using (h [] rfl).mpr rfl
    simp [nodos, buscar, nunca, this]
  | k + 1, p, h => by
    have hmf : ¬ Vivo sol k (p ++ [false]) := by
      rintro ⟨q, hq, hs⟩
      have := (h (false :: q) (by simp [hq])).mp (by simpa using hs)
      simp [List.replicate_succ] at this
    have ht : ∀ q : List Bool, q.length = k → (sol (p ++ [true] ++ q) = true ↔ q = List.replicate k true) :=
      fun q hq => by
        have := h (true :: q) (by simp [hq])
        simpa [List.replicate_succ] using this
    have ha : (buscar sol nunca k (p ++ [false])).1 = false := by
      cases hh : (buscar sol nunca k (p ++ [false])).1
      · rfl
      · exact absurd ((buscar_correcto (nunca_sano sol) k _).mp hh) hmf
    have cf := sin_detector_muerto sol k (p ++ [false]) hmf
    have ct := a_ciegas_unica k (p ++ [true]) ht
    unfold nodos at cf ct ⊢
    simp only [buscar, nunca, ha, Bool.false_eq_true, ite_false]
    rw [pow_succ]
    omega

/-! ## El mundo bueno, como caso particular -/

/-- **Error**: desde un nodo vivo, elegir `b` lleva a un hijo muerto. -/
def Error (k : ℕ) (p : List Bool) (b : Bool) : Prop := Vivo sol (k + 1) p ∧ ¬ Vivo sol k (p ++ [b])

/-- **Con una sola solución, equivocarse es apartarse de ella.** Si las soluciones debajo de `p` son exactamente
`c :: w`, el hijo `b` está muerto si y solo si `b ≠ c`. -/
theorem error_unica_iff {k : ℕ} {p : List Bool} {c : Bool} {w : List Bool} (hw : w.length = k)
    (h : ∀ q : List Bool, q.length = k + 1 → (sol (p ++ q) = true ↔ q = c :: w)) (b : Bool) :
    ¬ Vivo sol k (p ++ [b]) ↔ b ≠ c := by
  constructor
  · intro hm hbc
    subst hbc
    exact hm ⟨w, hw, by simpa using (h (b :: w) (by simp [hw])).mpr rfl⟩
  · rintro hbc ⟨q, hq, hs⟩
    have := (h (b :: q) (by simp [hq])).mp (by simpa using hs)
    simp only [List.cons.injEq] at this
    exact hbc this.1

/-- **Con varias soluciones, contar contra una sola da de más.** Si toda asignación es solución, elegir `false` se
aparta del mundo `[true]`, pero no es un error. -/
theorem varias_sobrecuenta : ¬ Error (fun _ => true) 0 [] false ∧ (false ≠ true) := by
  refine ⟨fun ⟨_, hm⟩ => hm ⟨[], rfl, rfl⟩, by decide⟩

/-! ## Un detector concreto: «hay una cláusula falsa» -/

/-- Una cláusula: literales `(variable, signo)`. -/
abbrev Clausula := List (ℕ × Bool)

/-- El literal vale en `p` si la variable ya está fijada con su signo. -/
def satisface (p : List Bool) (c : Clausula) : Bool := c.any fun l => p[l.1]? == some l.2

/-- La cláusula es falsa en `p`: todas sus variables ya están fijadas, y ninguna con su signo. -/
def falsificada (p : List Bool) (c : Clausula) : Bool :=
  c.all fun l => match p[l.1]? with
    | some v => v != l.2
    | none => false

/-- Una asignación es solución si satisface todas las cláusulas. -/
def solCNF (F : List Clausula) (p : List Bool) : Bool := F.all (satisface p)

/-- **El detector de la búsqueda con propagación**: alguna cláusula ya es falsa. -/
def detCNF (F : List Clausula) (p : List Bool) : Bool := F.any (falsificada p)

/-- **«Hay una cláusula falsa» es un detector sano**: completar la asignación no arregla una cláusula ya falsa. -/
theorem detCNF_sano (F : List Clausula) : Sano (solCNF F) (detCNF F) := by
  intro p q h
  simp only [detCNF, List.any_eq_true] at h
  obtain ⟨c, hc, hf⟩ := h
  simp only [solCNF, List.all_eq_false]
  refine ⟨c, hc, ?_⟩
  simp only [satisface, List.any_eq_true, beq_iff_eq, not_exists, not_and]
  simp only [falsificada, List.all_eq_true] at hf
  intro l hl heq
  have hfl := hf l hl
  split at hfl
  · rename_i v hv
    have hlt : l.1 < p.length := (List.getElem?_eq_some_iff.mp hv).1
    rw [List.getElem?_append_left hlt, hv] at heq
    simp only [Option.some.injEq] at heq
    simp [heq] at hfl
  · exact absurd hfl (by simp)

/-! ## Controles: las cotas se alcanzan -/

/-- La única solución es todo `true`, con 4 variables. -/
def todoTrue4 : List Clausula := [[(0, true)], [(1, true)], [(2, true)], [(3, true)]]

/-- **La cota del detector perfecto es exacta**: `2·4 + 1 = 9`. Cada `false` se detecta en el acto y cuesta un nodo. -/
example : nodos (solCNF todoTrue4) (detCNF todoTrue4) 4 [] = 2 * 4 + 1 := by decide

/-- **A ciegas, la misma fórmula cuesta el árbol entero**: `2^5 − 1 = 31`. -/
example : nodos (solCNF todoTrue4) nunca 4 [] = 2 ^ 5 - 1 := by decide

/-- **Contradicción tarde**: si la contradicción está en la última variable, el detector no ayuda. -/
example : nodos (solCNF [[(3, true)], [(3, false)]]) (detCNF [[(3, true)], [(3, false)]]) 4 [] = 2 ^ 5 - 1 := by
  decide

end Tiempo
end Sagitta.Map
