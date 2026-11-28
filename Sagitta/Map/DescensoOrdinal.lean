import Sagitta.Map.Contador
import Mathlib.Order.Prod.Lex.Basic

/-!
# Descenso con costo en ω²

El costo de un descenso no tiene por qué ser un número natural: basta que viva en un orden bien fundado. Aquí el
costo es un par `(a, b)` ordenado lexicográficamente, `ℕ ×ₗ ℕ`, cuyo tipo de orden es el ordinal `ω²`: `(a, b)` hace
el papel de `ω·a + b`. Bajar `a` en uno permite subir `b` todo lo que se quiera.

Dos resultados:

1. **Termina igual** (`DescensoEn.termina`): para todo orden bien fundado, seguir al vecino llega a un óptimo. Es la
   buena fundación, sin cuentas.
2. **Pero el costo ya no acota los pasos** (`Recarga.sin_cota`). En `ℕ`, `Descenso.desciende_desde` dice que los
   pasos no pasan del costo. Con costo en `ω²` eso se pierde: hay un descenso donde todas las cadenas que empiezan
   en `1` cuestan lo mismo, `(1, 0)` (el ordinal `ω`), y sin embargo los pasos crecen sin límite con la longitud. Ninguna
   función del costo los acota.

Es la forma pequeña de lo que pasa con Goodstein: el ordinal baja en cada paso, así que la sucesión termina; pero el
número de pasos no lo controla ninguna función que la aritmética de Peano demuestre total.

Como en `Contador.lean`, no se prueba que costo y vecino sean polinomiales.
-/

namespace Sagitta.Map

/-- Un descenso con costo en un orden total `α`. -/
structure DescensoEn (α : Type) [LinearOrder α] where
  /-- El costo de una cadena. -/
  costo : List Bool → α
  /-- El vecino propuesto para una cadena. -/
  vecino : List Bool → List Bool
  conserva : ∀ x, (vecino x).length = x.length

namespace DescensoEn

variable {α : Type} [LinearOrder α]

/-- `x` es un óptimo local: su vecino no cuesta menos. -/
def EsOptimo (D : DescensoEn α) (x : List Bool) : Prop := D.costo x ≤ D.costo (D.vecino x)

/-- **Termina igual.** Si el orden del costo es bien fundado, seguir al vecino llega a un óptimo local. La prueba es
inducción bien fundada sobre el costo; no da cota de pasos. -/
theorem termina [WellFoundedLT α] (D : DescensoEn α) (x : List Bool) :
    ∃ k, D.EsOptimo (D.vecino^[k] x) := by
  suffices H : ∀ c : α, ∀ x, D.costo x = c → ∃ k, D.EsOptimo (D.vecino^[k] x) from H _ x rfl
  intro c
  induction c using WellFoundedLT.induction with
  | _ c ih =>
    intro x hx
    by_cases h : D.EsOptimo x
    · exact ⟨0, h⟩
    · have hlt : D.costo (D.vecino x) < c := hx ▸ not_le.mp h
      obtain ⟨k, hk⟩ := ih _ hlt (D.vecino x) rfl
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

end DescensoEn

/-- `ω²`, como pares ordenados lexicográficamente: `(a, b)` es `ω·a + b`. -/
abbrev Omega2 := ℕ ×ₗ ℕ

/-! ## Un descenso en ω² que el costo no acota: el contador con recarga -/

namespace Recarga

open Contador

/-- El costo: una cadena que empieza en `1` vale `(1, 0)`, o sea `ω`; una que empieza en `0` vale `(0, número del
resto)`. -/
def costo : List Bool → Omega2
  | [] => toLex (0, 0)
  | true :: _ => toLex (1, 0)
  | false :: bs => toLex (0, valor bs)

/-- El vecino: el `1` inicial se gasta y **recarga** el resto con unos; después, el contador de `Contador.lean`. -/
def vecino : List Bool → List Bool
  | [] => []
  | true :: bs => false :: List.replicate bs.length true
  | false :: bs => false :: dec bs

/-- El contador con recarga, como descenso en `ω²`. -/
def recarga : DescensoEn Omega2 where
  costo := costo
  vecino := vecino
  conserva := by
    intro x
    match x with
    | [] => rfl
    | true :: bs => simp [vecino]
    | false :: bs => simp [vecino, dec_length]

#guard (List.range 6).map (fun k => vecino^[k] [true, true, true]) =
  [[true, true, true], [false, true, true], [false, false, true], [false, true, false], [false, false, false],
   [false, false, false]]

/-- Cada paso baja el costo en `ω²`, aunque el primero suba la segunda coordenada de `0` a `2ⁿ − 1`. -/
example (bs : List Bool) : costo (vecino (true :: bs)) < costo (true :: bs) := by
  simp [costo, vecino, Prod.Lex.toLex_lt_toLex]

theorem iterate_cero (k : ℕ) (y : List Bool) : vecino^[k] (false :: y) = false :: dec^[k] y := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (dec y)

theorem esOptimo_cero (y : List Bool) : recarga.EsOptimo (false :: y) ↔ valor y = 0 := by
  show costo (false :: y) ≤ costo (vecino (false :: y)) ↔ _
  simp only [costo, vecino, Prod.Lex.toLex_le_toLex, lt_self_iff_false, true_and, false_or, valor_dec]
  omega

theorem no_esOptimo_uno (bs : List Bool) : ¬ recarga.EsOptimo (true :: bs) := by
  show ¬ costo (true :: bs) ≤ costo (vecino (true :: bs))
  simp [costo, vecino, Prod.Lex.toLex_le_toLex]

/-- **Los pasos exactos.** Desde `1` seguido de `n` bits cualesquiera, el descenso tarda exactamente `2ⁿ` pasos: uno
para recargar y `2ⁿ − 1` de contador. -/
theorem pasos_exactos (bs : List Bool) :
    recarga.EsOptimo (vecino^[2 ^ bs.length] (true :: bs)) ∧
      ∀ k < 2 ^ bs.length, ¬ recarga.EsOptimo (vecino^[k] (true :: bs)) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ bs.length = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)).symm⟩
  have hval : valor (List.replicate bs.length true) = m := by rw [valor_unos]; omega
  have paso (j : ℕ) : vecino^[j + 1] (true :: bs) = false :: dec^[j] (List.replicate bs.length true) := by
    rw [Function.iterate_succ_apply]
    exact iterate_cero j _
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hm, paso, esOptimo_cero, valor_iterate, hval]
    omega
  · cases k with
    | zero => exact no_esOptimo_uno bs
    | succ j =>
      rw [paso, esOptimo_cero, valor_iterate, hval]
      omega

/-- **Termina**, por el teorema general en `ω²`. -/
theorem termina (x : List Bool) : ∃ k, recarga.EsOptimo (vecino^[k] x) := recarga.termina x

/-- **Ninguna función del costo acota los pasos.** En `ℕ`, la cota es el costo mismo (`Descenso.desciende_desde`).
Aquí no hay ninguna: todas las cadenas que empiezan en `1` cuestan `ω`, y tardan `2ⁿ` pasos con `n` tan grande como
se quiera. -/
theorem sin_cota :
    ¬ ∃ g : Omega2 → ℕ, ∀ x, ∃ k ≤ g (recarga.costo x), recarga.EsOptimo (vecino^[k] x) := by
  rintro ⟨g, hg⟩
  let N := g (toLex (1, 0))
  obtain ⟨k, hk, hopt⟩ := hg (true :: List.replicate N true)
  have hlen : (List.replicate N true).length = N := List.length_replicate
  have hlt : k < 2 ^ (List.replicate N true).length := by
    rw [hlen]
    exact lt_of_le_of_lt hk (Nat.lt_two_pow_self)
  exact (pasos_exactos (List.replicate N true)).2 k hlt hopt

end Recarga

/-! ## El colapso: con longitud fija y segunda coordenada acotada, ω² no agrega nada

Si el vecino conserva la longitud y la segunda coordenada del costo queda por debajo de una cota `B` que depende solo
de la longitud, el par `(a, b)` se puede cambiar por el natural `a·B + b` sin cambiar ningún óptimo. Cuando el costo
se calcula en tiempo polinomial, esa cota existe: `b` tiene a lo sumo `p(n)` bits, y `B = 2^p(n)` sirve (esta parte,
sobre el tiempo, no se prueba aquí). Así, un descenso en `ω²` sobre cadenas de longitud fija es un descenso en `ℕ`.

**Atribución.** Esto es un ejercicio, no un resultado. El teorema de verdad es de Beckmann, Buss y Pollett,
«Ordinal notations and well-orderings in bounded arithmetic», Ann. Pure Appl. Logic 120 (2003) 197–223: el costo de
PLS puede tomar valores ordinales por debajo de `Γ₀` sin agrandar la clase. Llega muchísimo más lejos que `ω²` y se
prueba dentro de la aritmética acotada (`T¹₂`, `S²₂`). Lo de aquí es el caso más pequeño, por una cuenta directa. -/

/-- Con `b, b' < B`, comparar `a·B + b` con `a'·B + b'` es comparar `(a, b)` con `(a', b')` como en un diccionario. -/
theorem mul_add_le_iff {a b a' b' B : ℕ} (hb : b < B) (hb' : b' < B) :
    a * B + b ≤ a' * B + b' ↔ a < a' ∨ a = a' ∧ b ≤ b' := by
  rcases lt_trichotomy a a' with h | rfl | h
  · have : (a + 1) * B ≤ a' * B := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    constructor
    · intro; exact Or.inl h
    · intro; omega
  · omega
  · have : (a' + 1) * B ≤ a * B := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    constructor
    · intro; omega
    · rintro (h' | ⟨h', _⟩) <;> omega

/-- **El colapso.** Un descenso en `ω²` cuya segunda coordenada está acotada por una función de la longitud es, con
el mismo vecino y los mismos óptimos, un descenso con costo natural. -/
theorem DescensoEn.a_naturales (D : DescensoEn Omega2) (B : ℕ → ℕ)
    (hB : ∀ x, (ofLex (D.costo x)).2 < B x.length) :
    ∃ D' : Descenso, D'.vecino = D.vecino ∧ ∀ x, D'.EsOptimo x ↔ D.EsOptimo x := by
  refine ⟨{ costo := fun x => (ofLex (D.costo x)).1 * B x.length + (ofLex (D.costo x)).2
            vecino := D.vecino
            conserva := D.conserva }, rfl, fun x => ?_⟩
  have h1 := hB x
  have h2 := hB (D.vecino x)
  rw [D.conserva] at h2
  show _ * B x.length + _ ≤ _ * B (D.vecino x).length + _ ↔ D.costo x ≤ D.costo (D.vecino x)
  rw [D.conserva, mul_add_le_iff h1 h2, Prod.Lex.le_iff]

/-- El contador con recarga colapsa: la segunda coordenada de una cadena de longitud `n` vale menos de `2ⁿ`. -/
theorem Recarga.colapsa :
    ∃ D' : Descenso, D'.vecino = Recarga.recarga.vecino ∧ ∀ x, D'.EsOptimo x ↔ Recarga.recarga.EsOptimo x := by
  refine Recarga.recarga.a_naturales (fun n => 2 ^ n) fun x => ?_
  match x with
  | [] => simp [Recarga.recarga, Recarga.costo]
  | true :: _ => simp [Recarga.recarga, Recarga.costo]
  | false :: bs =>
    show Contador.valor bs < 2 ^ (bs.length + 1)
    have := Contador.valor_lt bs
    rw [pow_succ]
    omega

end Sagitta.Map
