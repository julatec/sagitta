import Sagitta.Map.Borde.BombeoFinito
import Sagitta.Map.Informacion.Homogeneidad
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Las luces de romper la CHT

Las notas del proyecto recorren las ramas con una pregunta: qué da tener
la CHT (la regla no depende del instante) y qué ilumina romperla. `Homogeneidad.lean` probó que el reloj se paga en
memoria. Este archivo formaliza tres de las filas de esa tabla; la cuarta, el cristal de tiempo, va en
`Cristal.lean`.

## 1. El bombeo es un corolario de la CHT, y su ruptura

* **(a) Con la CHT y memoria finita hay bombeo.** Es `BombeoFinito.bombeo_finito`. Aquí, la forma en una letra que
  usan (b) y (c): leyendo siempre la misma letra, la aceptación es finalmente periódica con preperíodo más período
  `≤ |σ|` (`unario_periodico`).
* **(b) Sin la CHT falla aun con un estado.** `DFAReloj` es un autómata finito cuyas reglas reciben el paso `t ∈ ℕ`.
  `deDFA_accepts`: todo `DFA` es uno de estos que no mira el paso. `primos` tiene **un solo estado** y acepta en el
  paso `t` si `t` es primo; reconoce `{0^p : p primo}` (`primos_accepts`), que no es regular (`primos_no_regular`),
  porque los primos no son finalmente periódicos (`primos_no_periodico`).
* **(c) Floquet.** Con un reloj periódico de período `P` (las reglas solo miran `t mod P`) vuelve el bombeo, con
  preperíodo más período `≤ P · |σ|` (`floquet`). La prueba es la de `Homogeneidad`: el reloj periódico es memoria
  `Fin P`, y el autómata sobre `σ × Fin P` es homogéneo. Control: `primos` no es periódico con ningún `P`
  (`primos_no_floquet`).

## 2. El salto adelante contra los factores distintos

* **(a) Con la CHT, saltar.** `potCuad x t` calcula `x^t` en cualquier monoide por cuadrados y **cuenta sus
  multiplicaciones** (la segunda componente suma uno por cada `*` que hace): `potCuad_val` da `x^t` y
  `potCuad_mult` da a lo sumo `2 · log₂ t + 2`. Si los factores son todos iguales, el producto es eso
  (`salto_constante`), y un algoritmo que lee solo el primer factor basta (`salto_lee_uno`).
* **(b) Sin ella, hay que leer los `t`.** En un monoide cancelativo con dos elementos, cambiar un factor cambia el
  producto (`prod_set_ne`). Modelo de caja negra: `NoLee A t i` dice que `A` no depende del factor `i` en las
  sucesiones de largo `t`. `hay_que_leer`: ningún algoritmo que calcula el producto de `t` factores deja de leer
  alguno. Ejemplo con permutaciones de tres elementos.

## 3. Los canales laterales

* **(a)** `filtracion tiempo = log₂ |{tiempo s : s}|`. Es `0` si y solo si el tiempo es constante
  (`filtracion_cero_iff`), y nunca pasa de `log₂ |S|` (`filtracion_le`). Ejemplo: una comparación que sale al primer
  bit distinto, sobre secretos de 3 bits, toma 3 tiempos distintos (`filtracion_compara`); la versión de tiempo
  constante filtra `0`.
* **(b) La CHT del lado del receptor.** Un receptor homogéneo, sin reloj, con estados `σ`, que solo ve los tics de una
  espera, está en `f^[w] x₀` cuando llega la señal. Si distingue un conjunto `W` de esperas, `|W| ≤ |σ|`
  (`receptor_homogeneo`); con `|σ| ≤ 2^s`, `log₂ |W| ≤ s`: la capacidad del canal de tiempo para ese receptor es a lo
  sumo `s` bits (`receptor_bits`). La cota es exacta (`receptor_justo`, con `vaiven`), y con un reloj (estados `ℕ`)
  desaparece (`receptor_con_reloj`).

## Lo que no se prueba

* Que la filtración sea `log₂` de la imagen es una definición (es la filtración de min-entropía de un canal
  determinista con secreto uniforme, un resultado conocido que se cita de memoria, sin probarlo aquí).
* (2b) es caja negra: dice que hay que **leer** los `t` factores, no que haya que hacer `t` multiplicaciones. Con `t`
  polinomial, el producto de factores distintos se reduce a una potencia (ver las notas del proyecto); eso no se
  formaliza.
* Nada de esto dice algo de `P` contra `NP`.
-/

namespace Sagitta.Map.Informacion.Rupturas

open Function
open Sagitta.Map.Continuo.Memoria
open Sagitta.Map.Borde.BombeoFinito

/-! ## 1. El bombeo -/

section Bombeo

variable {Γ σ : Type*}

/-- **(1a) Con la CHT y memoria finita hay bombeo**, en la forma de `BombeoFinito`. -/
theorem bombeo_con_cht [Fintype σ] (M : DFA Γ σ) (q : σ) (w : List Γ) (hw : Fintype.card σ ≤ w.length) :
    ∃ x y z, w = x ++ y ++ z ∧ y ≠ [] ∧ x.length + y.length ≤ Fintype.card σ ∧
      ∀ m, M.evalFrom q (x ++ (List.replicate m y).flatten ++ z) = M.evalFrom q w :=
  bombeo_finito M q w hw

/-- **(1a) en una letra**: la aceptación de `aⁿ` es finalmente periódica, con preperíodo más período `≤ |σ|`. -/
theorem unario_periodico [Fintype σ] (M : DFA Γ σ) (a : Γ) :
    ∃ μ p, 0 < p ∧ μ + p ≤ Fintype.card σ ∧
      ∀ n, μ ≤ n → (List.replicate (n + p) a ∈ M.accepts ↔ List.replicate n a ∈ M.accepts) := by
  obtain ⟨μ, p, hp, hle, hper⟩ := finalmente_periodica (fun q => M.step q a) M.start
  refine ⟨μ, p, hp, hle, fun n hn => ?_⟩
  change M.evalFrom M.start (List.replicate (n + p) a) ∈ M.accept ↔
    M.evalFrom M.start (List.replicate n a) ∈ M.accept
  rw [evalFrom_replicate, evalFrom_replicate, hper n hn]

/-- **Un autómata finito con reloj**: la transición y la aceptación reciben el paso `t ∈ ℕ`. Rompe la CHT. -/
structure DFAReloj (Γ σ : Type*) where
  step : ℕ → σ → Γ → σ
  start : σ
  acepta : ℕ → σ → Prop

namespace DFAReloj

variable (M : DFAReloj Γ σ)

/-- Leer `w` desde el paso `t` y el estado `q`. -/
def evalFrom : ℕ → σ → List Γ → σ
  | _, q, [] => q
  | t, q, a :: w => evalFrom (t + 1) (M.step t q a) w

/-- Acepta `w` si, después de leerla desde el paso `0`, la aceptación del paso `|w|` lo dice. -/
def accepts : Language Γ := {w | M.acepta w.length (M.evalFrom 0 M.start w)}

theorem evalFrom_concat (t : ℕ) (q : σ) (w : List Γ) (a : Γ) :
    M.evalFrom t q (w ++ [a]) = M.step (t + w.length) (M.evalFrom t q w) a := by
  induction w generalizing t q with
  | nil => simp [evalFrom]
  | cons b w ih =>
    simp only [List.cons_append, evalFrom, ih, List.length_cons]
    rw [show t + 1 + w.length = t + (w.length + 1) by omega]

/-- La órbita leyendo siempre `a`. -/
def orbita (a : Γ) : ℕ → σ
  | 0 => M.start
  | n + 1 => M.step n (orbita a n) a

theorem eval_replicate (a : Γ) (n : ℕ) : M.evalFrom 0 M.start (List.replicate n a) = M.orbita a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', evalFrom_concat, ih]; simp [orbita]

theorem mem_accepts_replicate (a : Γ) (n : ℕ) :
    List.replicate n a ∈ M.accepts ↔ M.acepta n (M.orbita a n) := by
  show M.acepta _ _ ↔ _
  rw [eval_replicate, List.length_replicate]

end DFAReloj

/-- Un `DFA` es un autómata con reloj que no mira el reloj. -/
def deDFA (M : DFA Γ σ) : DFAReloj Γ σ := ⟨fun _ q a => M.step q a, M.start, fun _ q => q ∈ M.accept⟩

theorem deDFA_evalFrom (M : DFA Γ σ) : ∀ (t : ℕ) (q : σ) (w : List Γ), (deDFA M).evalFrom t q w = M.evalFrom q w
  | _, q, [] => by simp [DFAReloj.evalFrom]
  | t, q, a :: w => by
    rw [DFAReloj.evalFrom, DFA.evalFrom_cons, deDFA_evalFrom M (t + 1)]
    rfl

/-- **La CHT, como caso**: el autómata con reloj que olvida el reloj acepta lo mismo que el `DFA`. -/
theorem deDFA_accepts (M : DFA Γ σ) : (deDFA M).accepts = M.accepts := by
  ext w
  rw [DFA.mem_accepts]
  show (deDFA M).evalFrom 0 M.start w ∈ M.accept ↔ _
  rw [deDFA_evalFrom]
  rfl

/-- **(1b) Sin la CHT, con un solo estado**: acepto en el paso `t` si `t` es primo. -/
def primos : DFAReloj Unit Unit := ⟨fun _ _ _ => (), (), fun t _ => Nat.Prime t⟩

theorem primos_accepts : primos.accepts = {w | Nat.Prime w.length} := rfl

/-- **Los primos no son finalmente periódicos**: si `n + p` y `n` fueran primos a la vez desde `μ`, todo
`q + k·p` sería primo para un primo `q ≥ μ`, y `q + q·p = q·(1 + p)` no lo es. -/
theorem primos_no_periodico : ¬ ∃ μ p, 0 < p ∧ ∀ n, μ ≤ n → (Nat.Prime (n + p) ↔ Nat.Prime n) := by
  rintro ⟨μ, p, hp, h⟩
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (μ + 2)
  have hall : ∀ k, Nat.Prime (q + k * p) := by
    intro k
    induction k with
    | zero => simpa using hqp
    | succ k ih =>
      rw [show q + (k + 1) * p = (q + k * p) + p by ring]
      exact (h _ (by omega)).2 ih
  have := hall q
  rw [show q + q * p = q * (1 + p) by ring] at this
  exact Nat.not_prime_mul (by omega) (by omega) this

/-- **`{0^p : p primo}` no es regular.** Un autómata de un estado con reloj lo reconoce; ninguno sin reloj, de
ninguna cantidad de estados. -/
theorem primos_no_regular : ¬ primos.accepts.IsRegular := by
  rintro ⟨τ, _, M, hM⟩
  obtain ⟨μ, p, hp, -, h⟩ := unario_periodico M ()
  apply primos_no_periodico
  refine ⟨μ, p, hp, fun n hn => ?_⟩
  have := h n hn
  rw [hM, primos_accepts] at this
  change Nat.Prime (List.replicate (n + p) ()).length ↔ Nat.Prime (List.replicate n ()).length at this
  simpa only [List.length_replicate] using this

/-- Un reloj periódico de período `P`: las reglas solo miran `t mod P`. -/
def DFAReloj.Periodico (M : DFAReloj Γ σ) (P : ℕ) : Prop :=
  (∀ t q a, M.step t q a = M.step (t % P) q a) ∧ ∀ t q, (M.acepta t q ↔ M.acepta (t % P) q)

/-- El autómata homogéneo sobre `σ × Fin P` que lleva el reloj periódico en el estado (el `homogeneizar` de
`Homogeneidad`, para un autómata finito que lee siempre `a`). -/
def floquetPaso (M : DFAReloj Γ σ) {P : ℕ} (hP : 0 < P) (a : Γ) (z : σ × Fin P) : σ × Fin P :=
  (M.step z.2 z.1 a, ⟨(z.2.val + 1) % P, Nat.mod_lt _ hP⟩)

theorem floquetPaso_iterate (M : DFAReloj Γ σ) {P : ℕ} (hP : 0 < P) (hM : M.Periodico P) (a : Γ) (n : ℕ) :
    (floquetPaso M hP a)^[n] (M.start, ⟨0, hP⟩) = (M.orbita a n, ⟨n % P, Nat.mod_lt _ hP⟩) := by
  induction n with
  | zero => simp [DFAReloj.orbita, Nat.zero_mod]
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    simp only [floquetPaso, DFAReloj.orbita, Prod.mk.injEq, Fin.mk.injEq]
    exact ⟨(hM.1 n _ a).symm, Nat.mod_add_mod n P 1⟩

/-- **(1c) Floquet**: con un reloj periódico de período `P` vuelve el bombeo, con preperíodo más período
`≤ P · |σ|`. -/
theorem floquet [Fintype σ] (M : DFAReloj Γ σ) {P : ℕ} (hP : 0 < P) (hM : M.Periodico P) (a : Γ) :
    ∃ μ p, 0 < p ∧ μ + p ≤ P * Fintype.card σ ∧
      ∀ n, μ ≤ n → (List.replicate (n + p) a ∈ M.accepts ↔ List.replicate n a ∈ M.accepts) := by
  obtain ⟨μ, p, hp, hle, hper⟩ := finalmente_periodica (floquetPaso M hP a) (M.start, ⟨0, hP⟩)
  refine ⟨μ, p, hp, ?_, fun n hn => ?_⟩
  · simpa [Fintype.card_prod, Fintype.card_fin, mul_comm] using hle
  · have e := hper n hn
    rw [floquetPaso_iterate M hP hM, floquetPaso_iterate M hP hM] at e
    simp only [Prod.mk.injEq, Fin.mk.injEq] at e
    rw [DFAReloj.mem_accepts_replicate, DFAReloj.mem_accepts_replicate, hM.2, hM.2 n, e.1, e.2]

/-- **Control**: los primos no tienen reloj periódico con ningún período. -/
theorem primos_no_floquet {P : ℕ} (hP : 0 < P) : ¬ primos.Periodico P := by
  intro hM
  obtain ⟨μ, p, hp, -, h⟩ := floquet primos hP hM ()
  apply primos_no_periodico
  refine ⟨μ, p, hp, fun n hn => ?_⟩
  have := h n hn
  rw [primos_accepts] at this
  change Nat.Prime (List.replicate (n + p) ()).length ↔ Nat.Prime (List.replicate n ()).length at this
  simpa only [List.length_replicate] using this

end Bombeo

/-! ## 2. El salto adelante contra los factores distintos -/

section Salto

variable {M : Type*} [Monoid M]

/-- **Potencia por cuadrados, contando las multiplicaciones**: la segunda componente suma uno por cada `*`. -/
def potCuad (x : M) : ℕ → M × ℕ
  | 0 => (1, 0)
  | n + 1 =>
    let r := potCuad x ((n + 1) / 2)
    if (n + 1) % 2 = 0 then (r.1 * r.1, r.2 + 1) else (r.1 * r.1 * x, r.2 + 2)
decreasing_by omega

theorem potCuad_val (x : M) (n : ℕ) : (potCuad x n).1 = x ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [potCuad]
    | n + 1 =>
      rw [potCuad]
      have h := ih ((n + 1) / 2) (by omega)
      split_ifs with he
      · simp only [h, ← pow_add]; congr 1; omega
      · simp only [h, ← pow_add, ← pow_succ]; congr 1; omega

/-- **A lo sumo `2 · log₂ t + 2` multiplicaciones.** -/
theorem potCuad_mult (x : M) (n : ℕ) : (potCuad x n).2 ≤ 2 * Nat.log 2 n + 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [potCuad]
    | n + 1 =>
      rw [potCuad]
      have h := ih ((n + 1) / 2) (by omega)
      have hl := Nat.log_div_base 2 (n + 1)
      rcases Nat.eq_zero_or_pos ((n + 1) / 2) with h0 | hpos
      · have : (potCuad x ((n + 1) / 2)).2 = 0 := by rw [h0, potCuad]
        split_ifs <;> simp only [this] <;> omega
      · have : 0 < Nat.log 2 (n + 1) := Nat.log_pos (by norm_num) (by omega)
        split_ifs <;> simp only <;> omega

/-- **Con la CHT** (todos los factores iguales), el producto es la potencia que da el salto. -/
theorem salto_constante (x : M) (t : ℕ) : (List.replicate t x).prod = (potCuad x t).1 := by
  rw [List.prod_replicate, potCuad_val]

/-- `A` **no lee el factor `i`** en las sucesiones de largo `t`: dos sucesiones que coinciden fuera de `i` dan lo
mismo. -/
def NoLee {G : Type*} (A : List G → G) (t i : ℕ) : Prop :=
  ∀ l l' : List G, l.length = t → l'.length = t → (∀ j, j ≠ i → l[j]? = l'[j]?) → A l = A l'

/-- **Con la CHT, leer uno basta**: el algoritmo que toma el primer factor y salta acierta en las sucesiones
constantes y no lee ningún factor salvo el primero. -/
theorem salto_lee_uno (t : ℕ) :
    (∀ x : M, (fun l : List M => (potCuad (l.headD 1) l.length).1) (List.replicate t x) =
        (List.replicate t x).prod) ∧
      ∀ i, i ≠ 0 → NoLee (fun l : List M => (potCuad (l.headD 1) l.length).1) t i := by
  refine ⟨fun x => ?_, fun i hi l l' hl hl' h => ?_⟩
  · rcases t with _ | t
    · simp [potCuad]
    · simp [List.replicate_succ, potCuad_val, pow_succ']
  · have h0 := h 0 (Ne.symm hi)
    have hh : l.headD 1 = l'.headD 1 := by
      rcases l with _ | ⟨a, l⟩ <;> rcases l' with _ | ⟨b, l'⟩
      · rfl
      · simp only [List.length_nil, List.length_cons] at hl hl'; omega
      · simp only [List.length_nil, List.length_cons] at hl hl'; omega
      · simpa using h0
    simp only [hl, hl', hh]

/-- **Cambiar un factor cambia el producto**, en un monoide cancelativo. -/
theorem prod_set_ne {G : Type*} [CancelMonoid G] (l : List G) (i : ℕ) (hi : i < l.length) {b : G}
    (hb : b ≠ l[i]) : (l.set i b).prod ≠ l.prod := by
  intro h
  rw [List.set_eq_take_append_cons_drop, if_pos hi] at h
  conv_rhs at h => rw [← List.take_append_drop i l, List.drop_eq_getElem_cons hi]
  simp only [List.prod_append, List.prod_cons] at h
  exact hb (mul_right_cancel (mul_left_cancel h))

/-- **Sin la CHT, hay que leer los `t`**: en un monoide cancelativo con dos elementos, ningún algoritmo que calcula el
producto de `t` factores deja de leer el factor `i`, para ningún `i < t`. -/
theorem hay_que_leer {G : Type*} [CancelMonoid G] [Nontrivial G] (A : List G → G) (t : ℕ)
    (hA : ∀ l : List G, l.length = t → A l = l.prod) (i : ℕ) (hi : i < t) : ¬ NoLee A t i := by
  intro hN
  obtain ⟨b, hb⟩ := exists_ne (1 : G)
  set l := List.replicate t (1 : G)
  have hl : l.length = t := List.length_replicate
  have hil : i < l.length := by omega
  have e := hN l (l.set i b) hl (by simp [hl]) (fun j hj => by simp [Ne.symm hj])
  rw [hA l hl, hA _ (by simp [hl])] at e
  exact prod_set_ne l i hil (b := b) (by simpa [l] using hb) e.symm

/-- Ejemplo: en las permutaciones de tres elementos (un grupo no conmutativo), cada uno de los `t` factores se lee. -/
example (A : List (Equiv.Perm (Fin 3)) → Equiv.Perm (Fin 3)) (t : ℕ) (hA : ∀ l, l.length = t → A l = l.prod) :
    ∀ i < t, ¬ NoLee A t i :=
  fun i hi => hay_que_leer A t hA i hi

end Salto

/-! ## 3. Los canales laterales -/

section Canales

/-- **La filtración de un canal de tiempo**: `log₂` del número de tiempos distintos. -/
noncomputable def filtracion {S : Type*} [Fintype S] (tiempo : S → ℕ) : ℝ :=
  Real.logb 2 ((Finset.univ.image tiempo).card)

variable {S : Type*} [Fintype S] [Nonempty S]

theorem card_image_pos (tiempo : S → ℕ) : 0 < (Finset.univ.image tiempo).card :=
  Finset.card_pos.2 (Finset.univ_nonempty.image _)

/-- **(3a) La filtración es `0` si y solo si el tiempo es constante.** -/
theorem filtracion_cero_iff (tiempo : S → ℕ) : filtracion tiempo = 0 ↔ ∀ s s', tiempo s = tiempo s' := by
  have hpos := card_image_pos tiempo
  have huno : (Finset.univ.image tiempo).card = 1 ↔ ∀ s s', tiempo s = tiempo s' := by
    constructor
    · intro h s s'
      exact Finset.card_le_one.1 (le_of_eq h) _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)) _
        (Finset.mem_image_of_mem _ (Finset.mem_univ s'))
    · intro h
      refine le_antisymm (Finset.card_le_one.2 ?_) hpos
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
      exact h s s'
  rw [filtracion, Real.logb_eq_zero, ← huno]
  have h0 : ((Finset.univ.image tiempo).card : ℝ) ≠ 0 := by positivity
  have h1 : ((Finset.univ.image tiempo).card : ℝ) ≠ -1 := by
    have : (0 : ℝ) ≤ (Finset.univ.image tiempo).card := by positivity
    intro e; linarith
  constructor
  · rintro (h | h | h | h | h | h)
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact absurd h h0
    · exact_mod_cast h
    · exact absurd h h1
  · intro h; right; right; right; right; left; exact_mod_cast h

/-- La filtración nunca pasa de `log₂ |S|`. -/
theorem filtracion_le (tiempo : S → ℕ) : filtracion tiempo ≤ Real.logb 2 (Fintype.card S) := by
  have hpos := card_image_pos tiempo
  apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos)
  have : (Finset.univ.image tiempo).card ≤ Fintype.card S := Finset.card_image_le.trans_eq Finset.card_univ
  exact_mod_cast this

/-- **El tiempo constante no filtra.** -/
theorem filtracion_constante (c : ℕ) : filtracion (fun _ : S => c) = 0 :=
  (filtracion_cero_iff _).2 fun _ _ => rfl

/-- Una comparación que sale al primer bit distinto: el número de pasos. -/
def pasosCompara : List Bool → List Bool → ℕ
  | a :: s, b :: g => if a = b then 1 + pasosCompara s g else 1
  | _, _ => 0

/-- Contra la clave `[true, true, true]`, los secretos de 3 bits toman 3 tiempos distintos (1, 2 o 3 pasos). -/
theorem compara_tres_tiempos :
    (Finset.univ.image fun s : Fin 3 → Bool => pasosCompara (List.ofFn s) [true, true, true]).card = 3 := by
  decide

/-- **La comparación temprana filtra `log₂ 3` bits**; la de tiempo constante, `0`. -/
theorem filtracion_compara :
    filtracion (fun s : Fin 3 → Bool => pasosCompara (List.ofFn s) [true, true, true]) = Real.logb 2 3 ∧
      filtracion (fun _ : Fin 3 → Bool => 3) = 0 := by
  refine ⟨?_, filtracion_constante 3⟩
  rw [filtracion, compara_tres_tiempos]
  norm_num

end Canales

section Receptor

variable {σ : Type*}

/-- **(3b) La CHT del lado del receptor**: un receptor homogéneo con estados `σ` que solo ve los tics de una espera
está en `f^[w] x₀` cuando llega la señal. Si su lectura `dec` distingue las esperas de `W`, entonces `|W| ≤ |σ|`. -/
theorem receptor_homogeneo [Fintype σ] (f : σ → σ) (x₀ : σ) {α : Type*} (dec : σ → α) (W : Finset ℕ)
    (h : Set.InjOn (fun w => dec (f^[w] x₀)) W) : W.card ≤ Fintype.card σ := by
  classical
  have hi : Set.InjOn (fun w => f^[w] x₀) W := fun a ha b hb e => h ha hb (by simp only at e ⊢; rw [e])
  calc W.card = (W.image fun w => f^[w] x₀).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ Fintype.card σ := Finset.card_le_univ _

/-- **En bits**: con `s` bits de memoria, la capacidad del canal de tiempo para ese receptor es a lo sumo `s` bits. -/
theorem receptor_bits [Fintype σ] (f : σ → σ) (x₀ : σ) {α : Type*} (dec : σ → α) (W : Finset ℕ)
    (h : Set.InjOn (fun w => dec (f^[w] x₀)) W) {s : ℕ} (hs : Fintype.card σ ≤ 2 ^ s) : Nat.log 2 W.card ≤ s := by
  calc Nat.log 2 W.card ≤ Nat.log 2 (2 ^ s) := Nat.log_mono_right ((receptor_homogeneo f x₀ dec W h).trans hs)
    _ = s := Nat.log_pow (by norm_num) s

/-- **La cota es justa**: el receptor `vaiven` de dos estados distingue las esperas `0` y `1`. -/
theorem receptor_justo : Set.InjOn (fun w => (fun q : Fin 2 => q + 1)^[w] (0 : Fin 2)) (({0, 1} : Finset ℕ) : Set ℕ) ∧
    ({0, 1} : Finset ℕ).card = Fintype.card (Fin 2) := by
  refine ⟨?_, by decide⟩
  intro a ha b hb e
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- **Con reloj, la cota desaparece**: un receptor que cuenta en `ℕ` distingue cualquier conjunto de esperas. -/
theorem receptor_con_reloj (W : Finset ℕ) : Set.InjOn (fun w => Nat.succ^[w] 0) W := by
  intro a _ b _ e
  simpa [Nat.succ_iterate] using e

end Receptor

/- Mutantes (25 nov 2026, fuera del repositorio); los seis fallaron:
* M1: `primos_no_periodico` sin `0 < p`: falla `omega` en `1 + p ≠ 1`; y es falso, con `p = 0` todo es periódico.
* M2: `floquet` con `μ + p ≤ |σ|` (sin cobrar el reloj `P`): el palomar sobre `σ × Fin P` solo da `P · |σ|`.
* M3: `potCuad_mult` con `2 · log₂ t + 1`: falla `omega` en `t = 1`, que hace 2 multiplicaciones.
* M4: `hay_que_leer` sin `Nontrivial G`: no hay un segundo factor con que cambiar (y en el monoide trivial es falso).
* M5: `filtracion_cero_iff` sin `Nonempty S`: falla al no poder acotar por abajo el número de tiempos.
* M6: `receptor_homogeneo` con `|W| < |σ|`: falla la cuenta; y `receptor_justo` muestra que es falso. -/

end Sagitta.Map.Informacion.Rupturas
