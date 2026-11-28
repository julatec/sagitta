import Sagitta.Map.Continuo.MemoriaPeriodica
import Sagitta.Map.Borde.PBombeo
import Mathlib.Computability.DFA
import Mathlib.Computability.MyhillNerode

/-!
# El bombeo con memoria finita: las dos mitades, y la jugada sí se puede exhibir

`Sagitta/Map/Borde/PBombeo.lean` arma «el lema» y «la jugada» para P y muestra que allí la jugada contra SAT es
equivalente al problema mismo (`jugada_iff_no_bombea`, `jugada_relleno_iff`). `Sagitta/Map/Continuo/MemoriaPeriodica.lean`
prueba el palomar de la órbita finita. Este archivo los conecta: con memoria finita el palomar **es** el lema de
bombeo, y la jugada (la palabra que lo rompe) es igualmente equivalente a salir de la clase, pero aquí se puede
exhibir: `aⁿbⁿ`.

## Lo que se prueba

**Sin entrada** (el modelo de trazas de `RegresoFinito.lean` y `MemoriaPeriodica.lean`, `α = Option σ`):
* `corrida_repite`: en los primeros `card σ + 1` pasos la traza repite una configuración (es `orbita_repite` sobre
  `Option σ`, que tiene `card σ + 1` elementos).
* **`traza_bombea`**: si la traza repite en `i < j`, el lazo `i → j` se puede dar cualquier número de veces:
  `traza (i + m·(j − i) + n) = traza (i + n)` para todo `m` y todo `n`.
* **`corrida_larga_bombea`**: una máquina de memoria finita que pasa por `card σ + 1` configuraciones sin parar
  repite una, el lazo bombea (todas sus vueltas son configuraciones sin `halt`) y la traza no para nunca.
* `memoria_crece`: si una familia de máquinas para con largos no acotados, sus memorias no están acotadas (la forma
  «jugada rompe» de `largo_le_card`).

**Con entrada** (los autómatas finitos de Mathlib, `DFA`):
* `evalFrom_replicate`: leer `a` `k` veces es la órbita del paso con `a`; ahí entra `orbita_repite` tal cual.
* `bombeo_lectura`: si leer `v` deja la configuración como estaba, `v` se puede repetir `m` veces.
* **`bombeo_finito`** (el lema): toda palabra de largo `≥ card σ` tiene un tramo `y ≠ []` dentro de los primeros
  `card σ` símbolos que se puede repetir `m` veces sin cambiar la configuración final. Es el lema de bombeo; Mathlib
  ya lo tiene en la forma de lenguajes (`DFA.pumping_lemma`); aquí sale del mismo palomar que `MemoriaPeriodica`.
* `JugadaFinita L`: para todo `k` hay `k + 1` prefijos que `L` distingue dos a dos (cocientes izquierdos distintos).
  **`jugada_finita_iff`**: la jugada es exactamente no ser regular (Myhill–Nerode, el de Mathlib). Es el análogo de
  `jugada_relleno_iff` de `PBombeo.lean`.
* **`anbn_no_regular`**: `{aⁿbⁿ}` no es regular, probado directo con `orbita_repite`: leyendo `a` la máquina pasa
  por `card σ + 1` configuraciones, repite en `aⁱ` y `aʲ`, y desde ahí no distingue `aⁱbⁱ` de `aʲbⁱ`.
  `anbn_jugada`: la jugada misma, exhibida (y por `jugada_finita_iff`, otra prueba de lo mismo).

## La lectura

En P, la jugada contra SAT equivale a la pregunta abierta y no se sabe exhibir. Con memoria finita la jugada también
equivale a salir de la clase (`jugada_finita_iff`), pero se exhibe en tres renglones porque el lema es un palomar
sobre un conjunto **fijo** de configuraciones: lo que la máquina no puede recordar, una palabra lo pide. En P el
conjunto de configuraciones crece con la entrada y el palomar no muerde.

## Lo que no se prueba

* Nada sobre P: el archivo es la versión finita, donde todo se sabe. El bombeo de autómatas y Myhill–Nerode son
  clásicos (Rabin–Scott 1959, Bar-Hillel–Perles–Shamir 1961, Nerode 1958); lo propio es la conexión con el modelo de
  trazas de Sagitta y con `PBombeo.lean`.
-/

open Function

namespace Sagitta.Map.Borde.BombeoFinito

open Sagitta.Map.Continuo.Memoria Sagitta.Map.Continuo.Regreso

/-! ## 1. Sin entrada: la traza repite y bombea -/

section SinEntrada

/-- Si `f^[i] x = f^[i + p] x`, el lazo de largo `p` se puede dar `m` veces. -/
theorem iterate_lazo {β : Type*} (f : β → β) (x : β) {i p : ℕ} (he : f^[i] x = f^[i + p] x) (m : ℕ) :
    f^[i + m * p] x = f^[i] x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show i + (m + 1) * p = m * p + (i + p) by ring, iterate_add_apply, ← he, ← iterate_add_apply,
      show m * p + i = i + m * p by ring, ih]

variable {σ : Type*} (δ : σ → Option σ) (s : σ)

/-- **El lazo bombea**: si la traza repite en `i < j`, dar el lazo `m` veces más no cambia nada. -/
theorem traza_bombea {i j : ℕ} (hij : i < j) (he : traza δ s i = traza δ s j) (m n : ℕ) :
    traza δ s (i + m * (j - i) + n) = traza δ s (i + n) := by
  simp only [traza] at he ⊢
  have he' : (paso δ)^[i] (some s) = (paso δ)^[i + (j - i)] (some s) := by
    rw [show i + (j - i) = j by omega]; exact he
  rw [show i + m * (j - i) + n = n + (i + m * (j - i)) by ring, iterate_add_apply, iterate_lazo _ _ he' m,
    ← iterate_add_apply, show n + i = i + n by ring]

variable [Fintype σ]

/-- **Palomar sobre la traza**: en los primeros `card σ + 1` pasos se repite una configuración. -/
theorem corrida_repite : ∃ i j, i < j ∧ j ≤ Fintype.card σ + 1 ∧ traza δ s i = traza δ s j := by
  obtain ⟨i, j, hij, hj, he⟩ := orbita_repite (paso δ) (some s)
  exact ⟨i, j, hij, by simpa using hj, he⟩

/-- **Corrida larga, bombeo y no parada**: si la máquina pasa por `card σ + 1` configuraciones sin `halt`, repite
una en `i < j ≤ card σ`, todas las vueltas del lazo son configuraciones sin `halt`, y la traza no para nunca. -/
theorem corrida_larga_bombea (h : ∀ n ≤ Fintype.card σ, traza δ s n ≠ none) :
    ∃ i j, i < j ∧ j ≤ Fintype.card σ ∧
      (∀ m n, traza δ s (i + m * (j - i) + n) = traza δ s (i + n)) ∧
      (∀ m, traza δ s (i + m * (j - i)) ≠ none) ∧ traza δ s ∉ Para none := by
  have hno : traza δ s ∉ Para none := by
    rw [para_iff_acotado]
    rintro ⟨n, hn, e⟩
    exact h n (by omega) e
  -- El palomar entre las configuraciones `some _` de los primeros `card σ + 1` pasos.
  have hsome : ∀ n ≤ Fintype.card σ, ∃ c, traza δ s n = some c := fun n hn =>
    Option.ne_none_iff_exists'.1 (h n hn)
  have : Nonempty σ := ⟨s⟩
  choose! c hc using hsome
  have hcard : Fintype.card σ < Fintype.card (Fin (Fintype.card σ + 1)) := by simp
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card σ + 1) => c k) hcard
  have ha := hc a (Nat.lt_succ_iff.1 a.2)
  have hb := hc b (Nat.lt_succ_iff.1 b.2)
  have key : ∀ {i j : ℕ}, i < j → j ≤ Fintype.card σ → traza δ s i = traza δ s j →
      ∃ i j, i < j ∧ j ≤ Fintype.card σ ∧
        (∀ m n, traza δ s (i + m * (j - i) + n) = traza δ s (i + n)) ∧
        (∀ m, traza δ s (i + m * (j - i)) ≠ none) ∧ traza δ s ∉ Para none := by
    intro i j hij hj e
    refine ⟨i, j, hij, hj, traza_bombea δ s hij e, fun m => ?_, hno⟩
    have := traza_bombea δ s hij e m 0
    simp only [add_zero] at this
    rw [this]
    exact h i (by omega)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
  · exact key hlt (Nat.lt_succ_iff.1 b.2) (by rw [ha, hb]; simp [he])
  · exact key hlt (Nat.lt_succ_iff.1 a.2) (by rw [ha, hb]; simp [he])

end SinEntrada

/-- **La jugada sin entrada rompe la memoria acotada**: una familia de máquinas que paran con largos no acotados
necesita memorias no acotadas. -/
theorem memoria_crece {σ : ℕ → Type*} [∀ n, Fintype (σ n)] (δ : ∀ n, σ n → Option (σ n)) (s : ∀ n, σ n)
    (hp : ∀ n, traza (δ n) (s n) ∈ Para none) (hL : ∀ k, ∃ n, k < largo none (traza (δ n) (s n))) :
    ∀ k, ∃ n, k < Fintype.card (σ n) := by
  intro k
  obtain ⟨n, hn⟩ := hL k
  exact ⟨n, lt_of_lt_of_le hn (largo_le_card (δ n) (s n) (hp n))⟩

/-! ## 2. Con entrada: autómatas finitos -/

section Automatas

variable {Γ : Type*} {σ : Type*} (M : DFA Γ σ)

/-- Leer `a` `k` veces es la órbita del paso con `a`. -/
theorem evalFrom_replicate (q : σ) (a : Γ) (k : ℕ) :
    M.evalFrom q (List.replicate k a) = (fun t => M.step t a)^[k] q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, DFA.evalFrom_cons, ih, iterate_succ_apply]

/-- Si leer `v` deja la configuración como estaba, `v` se puede repetir `m` veces. -/
theorem bombeo_lectura {q : σ} {u v : List Γ} (he : M.evalFrom q (u ++ v) = M.evalFrom q u) (m : ℕ) :
    M.evalFrom q (u ++ (List.replicate m v).flatten) = M.evalFrom q u := by
  rw [DFA.evalFrom_of_append] at he ⊢
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.flatten_cons, DFA.evalFrom_of_append, he, ih]

/-- **El lema de bombeo, desde el palomar**: toda palabra de largo al menos `card σ` tiene un tramo no vacío, dentro
de los primeros `card σ` símbolos, que se puede repetir `m` veces sin cambiar la configuración final. -/
theorem bombeo_finito [Fintype σ] (q : σ) (w : List Γ) (hw : Fintype.card σ ≤ w.length) :
    ∃ x y z, w = x ++ y ++ z ∧ y ≠ [] ∧ x.length + y.length ≤ Fintype.card σ ∧
      ∀ m, M.evalFrom q (x ++ (List.replicate m y).flatten ++ z) = M.evalFrom q w := by
  have hcard : Fintype.card σ < Fintype.card (Fin (Fintype.card σ + 1)) := by simp
  obtain ⟨a, b, hab, he⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card σ + 1) => M.evalFrom q (w.take k)) hcard
  -- Ordenar el par.
  obtain ⟨i, j, hij, hj, he⟩ : ∃ i j, i < j ∧ j ≤ Fintype.card σ ∧
      M.evalFrom q (w.take i) = M.evalFrom q (w.take j) := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
    · exact ⟨a, b, h, Nat.lt_succ_iff.1 b.2, he⟩
    · exact ⟨b, a, h, Nat.lt_succ_iff.1 a.2, he.symm⟩
  have htj : w.take j = w.take i ++ (w.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (w.take j)]
    rw [List.take_take, min_eq_left hij.le]
  refine ⟨w.take i, (w.take j).drop i, w.drop j, ?_, ?_, ?_, fun m => ?_⟩
  · rw [← htj, List.take_append_drop]
  · intro hnil
    have := congrArg List.length hnil
    simp [List.length_drop, List.length_take] at this
    omega
  · simp [List.length_drop, List.length_take]
    omega
  · have hl : M.evalFrom q (w.take i ++ (w.take j).drop i) = M.evalFrom q (w.take i) := by
      rw [← htj, he]
    rw [DFA.evalFrom_of_append, bombeo_lectura M hl m, he, ← DFA.evalFrom_of_append, List.take_append_drop]

/-- Dos prefijos que `L` distingue: sus cocientes izquierdos son distintos (hay un sufijo que acepta uno y no el
otro). -/
def Distinguibles (L : Language Γ) (u v : List Γ) : Prop := L.leftQuotient u ≠ L.leftQuotient v

/-- **La jugada con memoria finita**: para todo `k` hay `k + 1` prefijos que `L` distingue dos a dos. -/
def JugadaFinita (L : Language Γ) : Prop :=
  ∀ k : ℕ, ∃ u : Fin (k + 1) → List Γ, Pairwise fun i j => Distinguibles L (u i) (u j)

/-- **La jugada es exactamente no ser regular** (con Myhill–Nerode de Mathlib). Es el análogo de
`PBombeo.jugada_relleno_iff`; la diferencia es que aquí la jugada se puede exhibir. -/
theorem jugada_finita_iff (L : Language Γ) : JugadaFinita L ↔ ¬ L.IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  constructor
  · intro j hfin
    have := hfin.fintype
    obtain ⟨u, hu⟩ := j (Fintype.card (Set.range L.leftQuotient))
    have hinj : Injective fun i : Fin (Fintype.card (Set.range L.leftQuotient) + 1) =>
        (⟨L.leftQuotient (u i), u i, rfl⟩ : Set.range L.leftQuotient) := by
      intro a b hab
      by_contra hne
      exact hu hne (congrArg Subtype.val hab)
    have := Fintype.card_le_of_injective _ hinj
    simp at this
  · intro hinf k
    let e := Set.Infinite.natEmbedding _ hinf
    have hpre : ∀ n, ∃ x, L.leftQuotient x = (e n).val := fun n => (e n).prop
    choose u hu using hpre
    refine ⟨fun i => u i, fun a b hab heq => hab ?_⟩
    simp only [hu] at heq
    exact Fin.ext (e.injective (Subtype.ext heq))

theorem jugada_finita_rompe {L : Language Γ} (j : JugadaFinita L) : ¬ L.IsRegular :=
  (jugada_finita_iff L).1 j

/-- `{aⁿbⁿ}`. -/
def anbn (a b : Γ) : Language Γ := {w | ∃ n, w = List.replicate n a ++ List.replicate n b}


theorem count_anbn [DecidableEq Γ] {a b : Γ} (hab : a ≠ b) (i j : ℕ) :
    (List.replicate i a ++ List.replicate j b).count a = i ∧
      (List.replicate i a ++ List.replicate j b).count b = j := by
  constructor <;> simp [List.count_replicate, hab, Ne.symm hab]

/-- `aʲbⁱ ∈ {aⁿbⁿ}` solo si `i = j`. -/
theorem mem_anbn_iff {a b : Γ} (hab : a ≠ b) (i j : ℕ) :
    List.replicate j a ++ List.replicate i b ∈ anbn a b ↔ i = j := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    have h1 := (count_anbn hab j i).1
    have h2 := (count_anbn hab j i).2
    rw [hn, (count_anbn hab n n).1] at h1
    rw [hn, (count_anbn hab n n).2] at h2
    omega
  · rintro rfl
    exact ⟨i, rfl⟩

/-- **`aⁿbⁿ` no es regular, por el palomar de la órbita**: leyendo `a` la máquina pasa por `card σ + 1`
configuraciones (la órbita de `MemoriaPeriodica.orbita_repite`), repite en `aⁱ` y `aʲ` con `i < j`, y desde ahí
acepta `aʲbⁱ` igual que `aⁱbⁱ`. -/
theorem anbn_no_regular {a b : Γ} (hab : a ≠ b) : ¬ (anbn a b).IsRegular := by
  rintro ⟨τ, _, M, hM⟩
  obtain ⟨i, j, hij, -, he⟩ := orbita_repite (fun t => M.step t a) M.start
  have hmem : List.replicate i a ++ List.replicate i b ∈ M.accepts := by
    rw [hM, mem_anbn_iff hab]
  have hmem' : List.replicate j a ++ List.replicate i b ∈ M.accepts := by
    rw [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append, evalFrom_replicate M M.start a j, ← he,
      ← evalFrom_replicate,
      ← DFA.evalFrom_of_append]
    exact hmem
  rw [hM, mem_anbn_iff hab] at hmem'
  omega

/-- **La jugada, exhibida**: los prefijos `a⁰, a¹, …, aᵏ` son distinguibles dos a dos (el sufijo `bⁱ` acepta `aⁱ` y
ningún otro). -/
theorem anbn_jugada {a b : Γ} (hab : a ≠ b) : JugadaFinita (anbn a b) := by
  intro k
  refine ⟨fun i => List.replicate i a, fun x y hxy heq => hxy ?_⟩
  have h : List.replicate (x : ℕ) b ∈ (anbn a b).leftQuotient (List.replicate x a) := by
    rw [Language.mem_leftQuotient, mem_anbn_iff hab]
  rw [heq, Language.mem_leftQuotient, mem_anbn_iff hab] at h
  exact Fin.ext h

/-- La otra prueba: con la jugada exhibida y `jugada_finita_iff`. -/
example {a b : Γ} (hab : a ≠ b) : ¬ (anbn a b).IsRegular := jugada_finita_rompe (anbn_jugada hab)

end Automatas

/-! ## Controles -/

section Controles

/-- Un autómata de un solo estado que no acepta nada. -/
def mudo : DFA Bool Unit := ⟨fun _ _ => (), (), ∅⟩

/-- La jugada no es trivial: un lenguaje regular no la cumple. -/
example : ¬ JugadaFinita mudo.accepts := by
  rw [jugada_finita_iff, not_not]
  exact ⟨Unit, inferInstance, mudo, rfl⟩

/-- La máquina `vaiven` de `MemoriaPeriodica` (en `Fin 2`, `0, 1, 0, 1, …`) pasa por 3 configuraciones sin parar,
repite y no para. -/
example : traza vaiven 0 ∉ Para none :=
  (corrida_larga_bombea vaiven 0 (by decide)).choose_spec.choose_spec.2.2.2.2

/- Mutantes (25 nov 2026, fuera del repositorio):
* MutBF1: `corrida_larga_bombea` con `∀ n < Fintype.card σ` en vez de `∀ n ≤ Fintype.card σ`: falla `omega` en la no
  parada (el paso `card σ` puede ser el `halt`, como en `cuenta` de `MemoriaPeriodica`) y el palomar no recibe la
  configuración del paso `card σ`.
* MutBF2: `anbn_no_regular` sin `a ≠ b`: falla donde se cuentan las letras (`mem_anbn_iff`); y es falso, con `a = b`
  el lenguaje son las palabras de largo par en una letra, que es regular.
* MutBF3: `bombeo_finito` con `x.length + y.length < card σ`: falla `omega` (el palomar solo da `j ≤ card σ`). -/

end Controles

end Sagitta.Map.Borde.BombeoFinito
