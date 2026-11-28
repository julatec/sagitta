import Sagitta.Map.Landau
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card

/-!
# Decidir nunca es gratis, a menos que te digan la elección

Tres lecturas de la frase, y lo que se prueba de cada una.

1. **Te dicen la elección.** Verificarla cuesta **una** pregunta (`te_dicen`). El costo no es cero, pero se **suma**: con
   `c` elecciones son `c` lecturas, no `2^c`.
2. **La elección está escondida** (caja negra). Un algoritmo adaptativo de preguntas (`Pregunta α`) que decide si hay
   alguna opción buena tiene que mirar **todas** las opciones cuando ninguna lo es (`adversario`, `costo_adversario`):
   `|α|` preguntas, y alcanza (`barrer`). Con `c` elecciones binarias, las ramas son `2^c` (`decidir_ramas`) y ese costo
   escapa de toda `O(K)` polinomial (`decidir_ramas_escapa`). El `ε` de elegir **se compone**.
3. **La elección la define un programa corto.** Que entonces también cueste es `P ≠ NP`, abierto. El argumento del
   adversario relativiza (Baker, Gill y Solovay, 1975), así que solo no puede resolverlo.

**El ε acumulado.** Si se elige una vez cada `k` pasos (`ε = 1/k`), lo que cuesta buscar crece como `2^(n/k)`, que escapa
de toda `O(K)` polinomial para todo `k` (`rala_escapa`), mientras que el certificado mide `n/k`, que es lineal. La
frontera exacta: `2^c(n)` está en `Pol` **si y solo si** `c(n) = O(log n)` (`dos_pow_pol_iff`). Un número logarítmico de
elecciones es gratis; uno mayor, no.
-/

open Filter

namespace Sagitta.Map
namespace Tiempo

/-! ## Algoritmos que preguntan -/

/-- **Un algoritmo que pregunta** a un oráculo `f : α → Bool`: o responde, o pregunta por una opción `i` y sigue según
la respuesta. Es adaptativo: cada pregunta puede depender de las anteriores. -/
inductive Pregunta (α : Type) : Type
  | resp (b : Bool) : Pregunta α
  | preg (i : α) (sig : Bool → Pregunta α) : Pregunta α

namespace Pregunta

variable {α : Type}

/-- La respuesta del algoritmo con el oráculo `f`. -/
def corre : Pregunta α → (α → Bool) → Bool
  | resp b, _ => b
  | preg i sig, f => corre (sig (f i)) f

/-- Las opciones que el algoritmo mira con el oráculo `f`, en orden. -/
def vistos : Pregunta α → (α → Bool) → List α
  | resp _, _ => []
  | preg i sig, f => i :: vistos (sig (f i)) f

/-- **El costo**: cuántas preguntas hace con `f`. -/
def costo (t : Pregunta α) (f : α → Bool) : ℕ := (vistos t f).length

/-- **Lo que no se mira no cuenta**: dos oráculos que coinciden en lo mirado dan la misma respuesta. -/
theorem corre_congr : ∀ (t : Pregunta α) (f g : α → Bool), (∀ i ∈ vistos t f, f i = g i) → corre t f = corre t g
  | resp _, _, _, _ => rfl
  | preg i sig, f, g, h => by
    have hi : f i = g i := h i List.mem_cons_self
    simp only [corre]
    rw [← hi]
    exact corre_congr (sig (f i)) f g (fun j hj => h j (List.mem_cons_of_mem _ hj))

end Pregunta

open Pregunta

/-- **`t` decide si hay una opción buena**: responde `true` exactamente cuando el oráculo tiene algún `true`. -/
def DecideExiste {α : Type} (t : Pregunta α) : Prop := ∀ f : α → Bool, corre t f = true ↔ ∃ i, f i = true

/-- **El adversario.** Si `t` decide si hay una opción buena, con el oráculo que dice «no» a todo `t` mira **todas** las
opciones. Si dejara una sin mirar, el adversario la vuelve buena y `t` no lo nota. -/
theorem adversario {α : Type} [DecidableEq α] (t : Pregunta α) (h : DecideExiste t) (i : α) :
    i ∈ vistos t (fun _ => false) := by
  by_contra hi
  let g : α → Bool := Function.update (fun _ => false) i true
  have hcon : corre t (fun _ => false) = corre t g :=
    corre_congr t _ g fun j hj => by
      have hji : j ≠ i := fun e => hi (e ▸ hj)
      simp [g, Function.update_of_ne hji]
  have h0 : corre t (fun _ => false) = false := by
    cases hc : corre t (fun _ => false)
    · rfl
    · obtain ⟨j, hj⟩ := (h _).1 hc; simp at hj
  have h1 : corre t g = true := (h g).2 ⟨i, by simp [g]⟩
  rw [← hcon, h0] at h1
  exact Bool.false_ne_true h1

/-- **Decidir con la elección escondida cuesta tantas preguntas como opciones hay.** -/
theorem costo_adversario {α : Type} [Fintype α] [DecidableEq α] (t : Pregunta α) (h : DecideExiste t) :
    Fintype.card α ≤ costo t (fun _ => false) := by
  have hsub : (Finset.univ : Finset α) ⊆ (vistos t (fun _ => false)).toFinset :=
    fun i _ => List.mem_toFinset.2 (adversario t h i)
  calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
    _ ≤ (vistos t (fun _ => false)).toFinset.card := Finset.card_le_card hsub
    _ ≤ costo t (fun _ => false) := List.toFinset_card_le _

/-- **Barrer**: preguntar una por una hasta encontrar una buena. -/
def barrer {α : Type} : List α → Pregunta α
  | [] => .resp false
  | i :: l => .preg i fun b => if b then .resp true else barrer l

theorem corre_barrer {α : Type} (f : α → Bool) : ∀ l : List α, corre (barrer l) f = true ↔ ∃ i ∈ l, f i = true
  | [] => by simp [barrer, corre]
  | i :: l => by
    simp only [barrer, corre]
    cases hfi : f i
    · simp only [Bool.false_eq_true, ite_false, corre_barrer f l, List.mem_cons, exists_eq_or_imp, hfi, false_or]
    · simp [corre, hfi]

theorem costo_barrer {α : Type} (f : α → Bool) : ∀ l : List α, costo (barrer l) f ≤ l.length
  | [] => by simp [barrer, costo, vistos]
  | i :: l => by
    simp only [costo, barrer, vistos, List.length_cons]
    cases f i
    · simpa [costo] using costo_barrer f l
    · simp [vistos]

/-- **Y alcanza**: barrer todas las opciones decide con a lo sumo `|α|` preguntas. El adversario es exacto. -/
theorem barrer_alcanza {α : Type} [Fintype α] :
    DecideExiste (barrer (Finset.univ : Finset α).toList) ∧
      ∀ f, costo (barrer (Finset.univ : Finset α).toList) f ≤ Fintype.card α := by
  refine ⟨fun f => ?_, fun f => ?_⟩
  · rw [corre_barrer]; simp
  · simpa using costo_barrer f (Finset.univ : Finset α).toList

/-- **Verificar la elección dicha**: preguntar por ella. -/
def verificar {α : Type} (i : α) : Pregunta α := .preg i fun b => .resp b

/-- **Si te dicen la elección, cuesta una pregunta**: hay una opción buena si y solo si hay una elección que, verificada
con una sola pregunta, da `true`. -/
theorem te_dicen {α : Type} (f : α → Bool) :
    (∃ i, f i = true) ↔ ∃ i, corre (verificar i) f = true ∧ costo (verificar i) f = 1 := by
  simp [verificar, corre, costo, vistos]

/-! ## El árbol de tiempo: `c` elecciones binarias -/

/-- Una función que domina a `2ⁿ` escapa de toda `O(K)` polinomial. -/
theorem escapa_de_dos_pow {g : ℕ → ℕ} (hg : ∀ n, 2 ^ n ≤ g n) : ∀ K ∈ Pol, g ∉ O K := by
  rintro K ⟨c, k, hK⟩ ⟨C, N, hO⟩
  obtain ⟨N', hN'⟩ := pol_menor_dos_pow (C * c) k
  set n := max N N'
  have h1 := hg n
  have h2 := hO n (le_max_left _ _)
  have h3 : C * K n ≤ C * c * (n + 1) ^ k := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (hK n)
  have h4 := hN' n (le_max_right _ _)
  omega

/-- **Decidir si alguna de las `2^c` ramas acepta**, con la aceptación escondida, cuesta `2^c` preguntas. -/
theorem decidir_ramas (c : ℕ) (t : Pregunta (List.Vector Bool c)) (h : DecideExiste t) :
    2 ^ c ≤ costo t (fun _ => false) := by
  have := costo_adversario t h
  rwa [card_vector, Fintype.card_bool] at this

/-- **Y como función de `c`, escapa de toda `O(K)` polinomial**: el `ε` de elegir se compone. -/
theorem decidir_ramas_escapa (t : ∀ c, Pregunta (List.Vector Bool c)) (h : ∀ c, DecideExiste (t c)) :
    ∀ K ∈ Pol, (fun c => costo (t c) (fun _ => false)) ∉ O K :=
  escapa_de_dos_pow fun c => decidir_ramas c (t c) (h c)

/-! ## El ε acumulado -/

/-- **Elegir una vez cada `k` pasos ya escapa**: `2^(n/k)` no está en `O(K)` para ningún `K ∈ Pol`, para todo `k ≥ 1`.
Por chico que sea `ε = 1/k`, compuesto `n` veces es exponencial. -/
theorem rala_escapa (k : ℕ) (hk : 1 ≤ k) : ∀ K ∈ Pol, (fun n => 2 ^ (n / k)) ∉ O K := by
  rintro K ⟨c, j, hK⟩ ⟨C, N, hO⟩
  obtain ⟨M, hM⟩ := pol_menor_dos_pow (C * c * (k + 1) ^ j) j
  set m := max N M
  have hn : N ≤ k * m := le_trans (le_max_left _ _) (Nat.le_mul_of_pos_left m (by omega))
  have h1 := hO (k * m) hn
  simp only [Nat.mul_div_cancel_left m (by omega : 0 < k)] at h1
  have h2 : C * K (k * m) ≤ C * c * (k * m + 1) ^ j := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (hK _)
  have h3 : (k * m + 1) ^ j ≤ (k + 1) ^ j * (m + 1) ^ j := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) j
  have h4 := hM m (le_max_right _ _)
  have h5 : C * c * (k * m + 1) ^ j ≤ C * c * (k + 1) ^ j * (m + 1) ^ j := by
    rw [mul_assoc (C * c)]; exact Nat.mul_le_mul_left _ h3
  omega

/-- **Mientras que el certificado de esas elecciones es lineal**: `n/k` bits. -/
theorem rala_certificado (k : ℕ) : (fun n => n / k) ∈ Pol := ⟨1, 1, fun n => by simp; exact (Nat.div_le_self n k).trans (Nat.le_succ n)⟩

/-- **La frontera**: `2^c(n)` está en `Pol` si y solo si `c(n) = O(log n)`. Un número logarítmico de elecciones se puede
buscar en tiempo polinomial; uno mayor, no. -/
theorem dos_pow_pol_iff (c : ℕ → ℕ) :
    (fun n => 2 ^ c n) ∈ Pol ↔ ∃ a b, ∀ n, c n ≤ a * Nat.log 2 (n + 1) + b := by
  constructor
  · rintro ⟨C, k, h⟩
    refine ⟨k, C + k, fun n => ?_⟩
    set L := Nat.log 2 (n + 1)
    have hL : n + 1 < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
    have hC : C ≤ 2 ^ C := C.lt_two_pow_self.le
    have hpow : (n + 1) ^ k ≤ 2 ^ ((L + 1) * k) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hL.le k
    have : 2 ^ c n ≤ 2 ^ (C + (L + 1) * k) := by
      calc 2 ^ c n ≤ C * (n + 1) ^ k := h n
        _ ≤ 2 ^ C * 2 ^ ((L + 1) * k) := Nat.mul_le_mul hC hpow
        _ = 2 ^ (C + (L + 1) * k) := (pow_add _ _ _).symm
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    nlinarith
  · rintro ⟨a, b, h⟩
    refine ⟨2 ^ b, a, fun n => ?_⟩
    set L := Nat.log 2 (n + 1)
    have hL : 2 ^ L ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    calc 2 ^ c n ≤ 2 ^ (a * L + b) := Nat.pow_le_pow_right (by norm_num) (h n)
      _ = 2 ^ b * (2 ^ L) ^ a := by rw [pow_add, mul_comm a L, pow_mul]; ring
      _ ≤ 2 ^ b * (n + 1) ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL a)

end Tiempo
end Sagitta.Map
