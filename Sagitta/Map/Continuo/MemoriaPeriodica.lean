import Sagitta.Map.Continuo.RegresoFinito
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Function.Iterate

/-!
# Memoria acotada: toda traza es periódica y la parada se decide

El detalle de la conversación del 24 nov 2026: los racionales diádicos (terminan en ceros) son las máquinas que paran;
los racionales **periódicos** (como `1/3`) son las corridas que entran en un ciclo, que es lo que pasa con memoria
acotada; los irracionales necesitan memoria que crece. Aquí se prueba la parte del medio: con un paso determinista
sobre un conjunto finito de estados, la órbita es finalmente periódica (palomar) y la parada se decide mirando un
prefijo de largo fijo.

## Lo que se prueba

* `orbita_repite`: para `f : β → β` con `[Fintype β]`, hay `i < j ≤ card β` con `f^[i] x = f^[j] x` (palomar,
  `Fintype.exists_ne_map_eq_of_card_lt`).
* **`finalmente_periodica`**: hay preperíodo `i` y período `p > 0` con `i + p ≤ card β` y `f^[n + p] x = f^[n] x`
  para todo `n ≥ i`.
* **`orbita_en_prefijo`**: todo valor de la órbita ya apareció entre los primeros `card β` pasos.
* La máquina: `paso δ` es el paso sobre `Option σ` (con `none` = `halt`, absorbente) y `traza δ s` la traza desde `s`,
  en el modelo de `RegresoFinito.lean` (`α = Option σ`, `h = none`). `traza_absorbente`.
* **`para_iff_acotado`**: la traza para si y solo si para en uno de los primeros `card σ + 1` pasos.
  **`decidirPara`**: por eso la parada es `Decidable`, mirando un prefijo de largo fijo.
* `largo_le_card`: cuando para, el largo es a lo sumo `card σ`; y `reloj_exacto`: con memoria finita el reloj
  `card σ + 1` nunca se equivoca (`reloj = regreso` en toda traza que para). Es el mecanismo 2 de `RegresoFinito.lean`
  con un corte universal.

## La lectura

Diádico = para; periódico = entra en un ciclo, y con memoria finita es lo único que puede pasar si no para; por eso se
decide. Irracional = la memoria tiene que crecer (una traza que no se repite nunca, como `n ↦ n`, no cabe en un
`Fintype`). El palomar es el mismo argumento que el lema de bombeo de los autómatas (y el bombeo de `BombeoDetector`, que
compara memoria contra demora); la conexión formal con `Sagitta/Map/Borde/PBombeo.lean` está en
`Sagitta/Map/Borde/BombeoFinito.lean`.

## Lo que no se prueba

* No se modela una cinta: la «memoria acotada» es `Fintype σ` sobre la configuración entera. Una máquina de espacio
  `s(n)` tiene `2^O(s(n))` configuraciones, y la cota de este archivo da el corte `2^O(s(n))`, el de PSPACE ⊆ EXP; eso
  se dice en las notas del proyecto y no se formaliza.
* El palomar es conocido; lo propio es la formalización en el modelo de trazas y la lectura.
-/

open Function

namespace Sagitta.Map.Continuo.Memoria

open Sagitta.Map.Continuo.Regreso

section Orbita

variable {β : Type*} [Fintype β] (f : β → β) (x : β)

/-- **Palomar**: en los primeros `card β + 1` pasos la órbita repite un valor. -/
theorem orbita_repite : ∃ i j, i < j ∧ j ≤ Fintype.card β ∧ f^[i] x = f^[j] x := by
  have hc : Fintype.card β < Fintype.card (Fin (Fintype.card β + 1)) := by simp
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card β + 1) => f^[k] x) hc
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact ⟨a, b, h, Nat.lt_succ_iff.1 b.2, he⟩
  · exact ⟨b, a, h, Nat.lt_succ_iff.1 a.2, he.symm⟩

/-- **La órbita es finalmente periódica**, con preperíodo más período a lo sumo `card β`. -/
theorem finalmente_periodica :
    ∃ i p, 0 < p ∧ i + p ≤ Fintype.card β ∧ ∀ n, i ≤ n → f^[n + p] x = f^[n] x := by
  obtain ⟨i, j, hij, hj, he⟩ := orbita_repite f x
  refine ⟨i, j - i, by omega, by omega, fun n hn => ?_⟩
  have e1 : n + (j - i) = (n - i) + j := by omega
  have e2 : n = (n - i) + i := by omega
  rw [e1, iterate_add_apply, ← he, ← iterate_add_apply, ← e2]

/-- Todo valor de la órbita ya apareció en los primeros `card β` pasos. -/
theorem orbita_en_prefijo (k : ℕ) : ∃ k' < Fintype.card β, f^[k] x = f^[k'] x := by
  obtain ⟨i, p, hp, hip, hper⟩ := finalmente_periodica f x
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < i + p
    · exact ⟨k, by omega, rfl⟩
    · obtain ⟨k', hk', e⟩ := ih (k - p) (by omega)
      refine ⟨k', hk', ?_⟩
      rw [← e, ← hper (k - p) (by omega), show k - p + p = k by omega]

end Orbita

/-! ## La máquina con `halt` -/

variable {σ : Type*}

/-- Un paso de la máquina: `δ s = none` es el `halt`; `none` se queda en `none`. -/
def paso (δ : σ → Option σ) : Option σ → Option σ := fun c => c.bind δ

/-- La traza desde el estado `s`. -/
def traza (δ : σ → Option σ) (s : σ) : ℕ → Option σ := fun n => (paso δ)^[n] (some s)

scoped instance : TopologicalSpace (Option σ) := ⊥
scoped instance : DiscreteTopology (Option σ) := ⟨rfl⟩

theorem traza_absorbente (δ : σ → Option σ) (s : σ) : Absorbente none (traza δ s) := by
  intro n hn
  simp only [traza, iterate_succ_apply'] at *
  rw [hn]
  rfl

variable [Fintype σ]

/-- **Con memoria finita, parar es parar pronto**: si la traza para, para en uno de los primeros `card σ + 1` pasos. -/
theorem para_iff_acotado (δ : σ → Option σ) (s : σ) :
    traza δ s ∈ Para none ↔ ∃ n < Fintype.card σ + 1, traza δ s n = none := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨k', hk', e⟩ := orbita_en_prefijo (paso δ) (some s) k
    refine ⟨k', by simpa using hk', ?_⟩
    simp only [traza] at hk ⊢
    rw [← e, hk]
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

/-- **La parada se decide** mirando los primeros `card σ + 1` pasos. -/
def decidirPara [DecidableEq σ] (δ : σ → Option σ) (s : σ) : Decidable (traza δ s ∈ Para none) :=
  decidable_of_iff _ (para_iff_acotado δ s).symm

theorem largo_le_card (δ : σ → Option σ) (s : σ) (hp : traza δ s ∈ Para none) :
    largo none (traza δ s) ≤ Fintype.card σ := by
  obtain ⟨n, hn, e⟩ := (para_iff_acotado δ s).1 hp
  have := largo_le (h := none) e
  omega

/-- **El reloj universal**: con memoria finita, cortar en `card σ + 1` nunca se equivoca. -/
theorem reloj_exacto [DecidableEq σ] (δ : σ → Option σ) (s : σ) (hp : traza δ s ∈ Para none) :
    reloj none (Fintype.card σ + 1) (traza δ s) = regreso none (traza δ s) :=
  reloj_eq_regreso hp (by have := largo_le_card δ s hp; omega)

/-! ## Controles -/

section Controles

/-- Una órbita en `Fin 4`: `0 → 1 → 2 → 3 → 2 → 3 → …` (preperíodo 2, período 2). -/
def g : Fin 4 → Fin 4 := ![1, 2, 3, 2]

example : g^[2 + 2] 0 = g^[2] 0 := by decide
example : g^[3 + 2] 0 = g^[3] 0 := by decide
example : g^[1 + 2] 0 ≠ g^[1] 0 := by decide

/-- Una máquina en `Fin 3` que cuenta hasta 2 y para: la traza es `0, 1, 2, halt, halt, …`. -/
def cuenta : Fin 3 → Option (Fin 3) := ![some 1, some 2, none]

example : traza cuenta 0 3 = none := by decide
example : traza cuenta 0 2 = some 2 := by decide

/-- Una máquina en `Fin 2` que oscila y no para: `0, 1, 0, 1, …`. -/
def vaiven : Fin 2 → Option (Fin 2) := ![some 1, some 0]

example : traza vaiven 0 ∉ Para none := by
  rw [para_iff_acotado]
  decide

/-- La parada de `cuenta` se decide con `decidirPara`. -/
example : traza cuenta 0 ∈ Para none := @of_decide_eq_true _ (decidirPara cuenta 0) (by decide)

/- Mutante (probado en /tmp/claude-noche/MutMem1.lean, 25 nov 2026): con `n < Fintype.card σ` en lugar de
`n < Fintype.card σ + 1` en `para_iff_acotado`, la prueba falla (`simpa using hk'` no cierra: el `halt` es un estado
más de `Option σ`). Y es falso: `cuenta` para en el paso 3 = `card (Fin 3)`. -/

end Controles

end Sagitta.Map.Continuo.Memoria
