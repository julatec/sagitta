import Sagitta.Map.Consumo
import Sagitta.Map.FormaDelTiempo
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card

/-!
# Savitch: recorrer el árbol de configuraciones sin escribirlo

`Consumo.lean` midió un árbol **dado**. Una máquina no determinista no da su árbol: da un paso (`Paso C` de
`FormaDelTiempo.lean`) sobre sus configuraciones. Si su espacio está acotado, las configuraciones son finitas
(`[Fintype C]`; con espacio `s` son `2^O(s)`). Decidir si acepta es decidir si se **llega** de la configuración inicial
a una que acepta.

## Dos maneras de decidirlo

* **Escribir el árbol** (la construcción de subconjuntos): llevar el frente, un subconjunto de `C`. Cuesta
  `|C|` bits de memoria: con espacio `s`, `2^O(s)`.
* **No escribirlo** (Savitch, 1970): `alc i u v` pregunta si se llega de `u` a `v` en a lo sumo `2^i` pasos, probando
  cada configuración `w` como punto medio y preguntando por las dos mitades con `i − 1`. No guarda ningún conjunto: solo
  la pila de llamadas, y cada marco tiene tres configuraciones (`u`, `v`, `w`).

## Lo que se prueba

* **Es correcto** (`alc_iff`): `alc i u v` si y solo si se llega en a lo sumo `2^i` pasos.
* **Basta `log₂ |C|`** (`savitch`): si se llega, se llega en menos de `|C|` pasos (`alcanza_corto`, palomar: un camino
  más largo repite configuración, y el ciclo se corta), así que `alc ⌈log₂ |C|⌉` decide la alcanzabilidad.
* **El costo, con el `⊕` de `Consumo.lean`** (`costoSav`): cada llamada hace `2|C|` subllamadas. Si `⊕` es idempotente
  (la memoria: las subllamadas reusan el mismo marco), la pila tiene `i + 1` marcos (`costoSav_idempotente`). Si suma (el
  tiempo), son al menos `(2|C|)^i` llamadas (`costoSav_aditivo`).
* **Con espacio `s`** (`savitch_bits`): con `|C| = 2^s` configuraciones, la pila ocupa `(s + 1)` marcos de `3s` bits,
  `3s(s + 1)` bits. **Cuadrático**, contra los `2^s` bits de escribir el frente. Es `NSPACE(s) ⊆ SPACE(s²)`.

## Lo que no

* No hay máquina de Turing: `C` es cualquier tipo finito con un paso decidible. Llevarlo a las máquinas de Mathlib pide
  que sus configuraciones con cinta acotada sean finitas, y que la recursión corra en una cinta de `O(s²)`. Aquí el
  espacio es el modelo de costo de `Consumo.lean` (marcos de pila), no casillas de una cinta.
* El tiempo de Savitch es `2^O(s²)`: recicla el espacio y paga en tiempo. Es la cara opuesta de la construcción de
  subconjuntos, que paga en espacio.
-/

namespace Sagitta.Map
namespace Tiempo

variable {C : Type*} {R : Paso C}

/-! ## Caminos: pegar, partir y acortar -/

theorem Alcanza.cero_inv {c d : C} (h : Alcanza R 0 c d) : c = d := by
  cases h; rfl

theorem Alcanza.succ_inv {t : ℕ} {c e : C} (h : Alcanza R (t + 1) c e) : ∃ d, Alcanza R t c d ∧ e ∈ R d := by
  cases h with
  | paso h he => exact ⟨_, h, he⟩

theorem Alcanza.trans {a b : ℕ} {c d e : C} (h1 : Alcanza R a c d) (h2 : Alcanza R b d e) :
    Alcanza R (a + b) c e := by
  induction h2 with
  | cero => exact h1
  | paso _ he ih => exact .paso (ih h1) he

theorem Alcanza.partir {a : ℕ} : ∀ {b : ℕ} {c e : C}, Alcanza R (a + b) c e →
    ∃ d, Alcanza R a c d ∧ Alcanza R b d e
  | 0, _, e, h => ⟨e, h, .cero e⟩
  | b + 1, _, _, h => by
    obtain ⟨d', h', he⟩ := Alcanza.succ_inv (t := a + b) h
    obtain ⟨d, h1, h2⟩ := Alcanza.partir h'
    exact ⟨d, h1, .paso h2 he⟩

/-- **Palomar**: si se llega, se llega en menos de `|C|` pasos. Un camino más largo repite configuración, y el ciclo
se corta. -/
theorem alcanza_corto [Fintype C] : ∀ (t : ℕ) {c d : C}, Alcanza R t c d →
    ∃ t' < Fintype.card C, Alcanza R t' c d := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro c d h
    by_cases ht : t < Fintype.card C
    · exact ⟨t, ht, h⟩
    obtain ⟨s, h0, hs, hfin⟩ := h.camino
    obtain ⟨i, j, hij, hsij⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (t + 1) => s k)
      (by simp; omega)
    -- Sin pérdida, `i < j`.
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm hsij.symm (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij))
    have hi : Alcanza R i c (s i) := corrida_en_frente h0 t hs i (by omega)
    have hj : Alcanza R (t - j) (s j) d := by
      have := corrida_en_frente (s := fun n => s (j + n)) rfl (t - j)
        (fun n hn => by simpa [Nat.add_assoc] using hs (j + n) (by omega)) (t - j) le_rfl
      simpa [frente, show j + (t - j) = t by omega, hfin t le_rfl] using this
    have hij' : Alcanza R (i + (t - j)) c d := hi.trans (by simpa [hsij] using hj)
    exact ih _ (by omega) hij'

/-! ## El algoritmo -/

variable [DecidableEq C] [Fintype C] (R) [∀ c d, Decidable (d ∈ R c)]

/-- `alc i u v`: ¿se llega de `u` a `v` en a lo sumo `2^i` pasos? Prueba cada punto medio `w`. -/
def alc : ℕ → C → C → Bool
  | 0, u, v => decide (u = v ∨ v ∈ R u)
  | i + 1, u, v => decide (∃ w, alc i u w = true ∧ alc i w v = true)

/-- **Correcto**: `alc i u v` si y solo si se llega en a lo sumo `2^i` pasos. -/
theorem alc_iff : ∀ (i : ℕ) (u v : C), alc R i u v = true ↔ ∃ t ≤ 2 ^ i, Alcanza R t u v
  | 0, u, v => by
    simp only [alc, decide_eq_true_eq, pow_zero]
    constructor
    · rintro (rfl | h)
      · exact ⟨0, by omega, .cero u⟩
      · exact ⟨1, le_rfl, .paso (.cero u) h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
      · exact Or.inl h.cero_inv
      · obtain ⟨d, hd, hv⟩ := Alcanza.succ_inv (t := 0) h
        exact Or.inr (hd.cero_inv ▸ hv)
  | i + 1, u, v => by
    simp only [alc, decide_eq_true_eq, alc_iff i]
    constructor
    · rintro ⟨w, ⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
      exact ⟨a + b, by rw [pow_succ]; omega, h1.trans h2⟩
    · rintro ⟨t, ht, h⟩
      have : t = min t (2 ^ i) + (t - min t (2 ^ i)) := by omega
      rw [this] at h
      obtain ⟨w, h1, h2⟩ := Alcanza.partir h
      exact ⟨w, ⟨_, min_le_right _ _, h1⟩, ⟨_, by rw [pow_succ] at ht; omega, h2⟩⟩

/-- **Savitch**: `⌈log₂ |C|⌉` niveles bastan para decidir si se llega. -/
theorem savitch (u v : C) :
    (∃ t, Alcanza R t u v) ↔ alc R (Nat.clog 2 (Fintype.card C)) u v = true := by
  rw [alc_iff]
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨t', ht', h'⟩ := alcanza_corto t h
    exact ⟨t', (ht'.le).trans (Nat.le_pow_clog (by norm_num) _), h'⟩
  · rintro ⟨t, -, h⟩
    exact ⟨t, h⟩

/-- La aceptación de una máquina no determinista, decidida sin escribir su árbol: alguna corrida llega a una
configuración que acepta. -/
theorem acepta_iff (u : C) (A : C → Prop) :
    (∃ t, ∃ v ∈ frente R t u, A v) ↔ ∃ v, A v ∧ alc R (Nat.clog 2 (Fintype.card C)) u v = true := by
  constructor
  · rintro ⟨t, v, hv, hA⟩
    exact ⟨v, hA, (savitch R u v).1 ⟨t, hv⟩⟩
  · rintro ⟨v, hA, h⟩
    obtain ⟨t, ht⟩ := (savitch R u v).2 h
    exact ⟨t, v, ht, hA⟩

/-! ## El costo, con el `⊕` de `Consumo.lean` -/

/-- El costo de la recursión de `alc i` sobre `n` configuraciones: cada llamada paga 1 y hace `2n` subllamadas (dos
mitades por cada punto medio), combinadas con `op`. -/
def costoSav (op : ℕ → ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => 1 + (List.replicate (2 * n) (costoSav op n i)).foldr op 0

omit [DecidableEq C] [Fintype C] [∀ c d, Decidable (d ∈ R c)] in
theorem foldr_replicate_idem {op : ℕ → ℕ → ℕ} (h : ∀ a, op a a = a) (h0 : ∀ a, op a 0 = a) (x : ℕ) :
    ∀ m, (List.replicate (m + 1) x).foldr op 0 = x
  | 0 => by simp [h0]
  | m + 1 => by rw [List.replicate_succ, List.foldr_cons, foldr_replicate_idem h h0 x m, h]

omit [DecidableEq C] [Fintype C] [∀ c d, Decidable (d ∈ R c)] in
theorem foldr_replicate_suma {op : ℕ → ℕ → ℕ} (h : ∀ a b, a + b ≤ op a b) (x : ℕ) :
    ∀ m, m * x ≤ (List.replicate m x).foldr op 0
  | 0 => by simp
  | m + 1 => by
    rw [List.replicate_succ, List.foldr_cons]
    have := foldr_replicate_suma h x m
    have := h x ((List.replicate m x).foldr op 0)
    rw [Nat.succ_mul]; omega

omit [DecidableEq C] [Fintype C] [∀ c d, Decidable (d ∈ R c)] in
/-- **La memoria se recicla**: con `⊕` idempotente, la pila tiene `i + 1` marcos. -/
theorem costoSav_idempotente {op : ℕ → ℕ → ℕ} (h : ∀ a, op a a = a) (h0 : ∀ a, op a 0 = a) {n : ℕ} (hn : 1 ≤ n) :
    ∀ i, costoSav op n i = i + 1
  | 0 => rfl
  | i + 1 => by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    rw [costoSav, hm, foldr_replicate_idem h h0, costoSav_idempotente h h0 hn i]; omega

omit [DecidableEq C] [Fintype C] [∀ c d, Decidable (d ∈ R c)] in
/-- **El tiempo se consume**: con `⊕` que suma, son al menos `(2n)^i` llamadas. -/
theorem costoSav_aditivo {op : ℕ → ℕ → ℕ} (h : ∀ a b, a + b ≤ op a b) (n : ℕ) :
    ∀ i, (2 * n) ^ i ≤ costoSav op n i
  | 0 => by simp [costoSav]
  | i + 1 => by
    rw [costoSav, pow_succ]
    have := foldr_replicate_suma h (costoSav op n i) (2 * n)
    have := Nat.mul_le_mul_left (2 * n) (costoSav_aditivo h n i)
    nlinarith

omit [DecidableEq C] [Fintype C] [∀ c d, Decidable (d ∈ R c)] in
/-- Las dos instancias: la pila (`max`) y las llamadas (`+`). -/
theorem marcos_savitch {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : costoSav max n i = i + 1 :=
  costoSav_idempotente max_self (fun a => by simp) hn i

omit [DecidableEq C] [Fintype C] [∀ c d, Decidable (d ∈ R c)] in
theorem llamadas_savitch (n i : ℕ) : (2 * n) ^ i ≤ costoSav (· + ·) n i :=
  costoSav_aditivo (fun _ _ => le_rfl) n i

/-- **Los bits de la pila**: marcos por tres configuraciones de `⌈log₂ n⌉` bits. -/
def bitsSavitch (n : ℕ) : ℕ := costoSav max n (Nat.clog 2 n) * (3 * Nat.clog 2 n)

omit [DecidableEq C] [Fintype C] [∀ c d, Decidable (d ∈ R c)] in
/-- **Con espacio `s`, la pila cabe en `3s(s+1)` bits**: con `2^s` configuraciones. Escribir el frente pide `2^s`. -/
theorem savitch_bits (s : ℕ) : bitsSavitch (2 ^ s) = 3 * s * (s + 1) := by
  rw [bitsSavitch, marcos_savitch (Nat.one_le_two_pow) _, Nat.clog_pow 2 s (by norm_num)]
  ring

omit [DecidableEq C] [Fintype C] [∀ c d, Decidable (d ∈ R c)] in
/-- Cuadrático contra exponencial: desde `s = 8`, la pila de Savitch ocupa menos que escribir el frente. -/
theorem savitch_menor_que_frente (s : ℕ) (hs : 8 ≤ s) : bitsSavitch (2 ^ s) < 2 ^ s := by
  rw [savitch_bits]
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    nlinarith

/-! ## Controles -/

/-- Un ciclo de tres configuraciones: de 0 se llega a 2, y `alc 1` (hasta 2 pasos) lo ve; `alc 0` (1 paso) no. -/
def ciclo3 : Paso (Fin 3) := fun c => {c + 1}

instance (c d : Fin 3) : Decidable (d ∈ ciclo3 c) := by unfold ciclo3; infer_instance

example : alc ciclo3 1 0 2 = true := by decide
example : alc ciclo3 0 0 2 = false := by decide

end Tiempo
end Sagitta.Map
