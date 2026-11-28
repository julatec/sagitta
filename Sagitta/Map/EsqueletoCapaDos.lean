import Sagitta.Map.CebollaExp
import Sagitta.Map.EscalaPolinomial
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# El esqueleto ordinal de la capa 2 (C3)

`CebollaExp.lean` mostró que la capa 2 de la cebolla junta los polinomios y las exponenciales. Aquí se abre: dentro de la
capa 2 hay una escala **bien ordenada**, de tipo `ω²`, cuyos escalones son clases de Landau.

**Los escalones.** Con la torre de exponenciales `torre h = (2^·)^[h]` (`torre 0 x = x`, `torre 1 x = 2ˣ`,
`torre 2 x = 2^(2ˣ)`, …),

  `Esq h d = O(torre h ((n+1)^(d+1)))`,

indexado por el ordinal `ω · h + d` (`indice`). El exponente es `d + 1` y no `d`: con `d = 0`, `torre h (n⁰)` sería una
constante y el primer escalón de cada fila no estaría por encima de la fila anterior.

## Lo que se prueba

1. **Crece estrictamente** (`esq_estricta`): si `(h, d) < (h', d')` lexicográficamente, `Esq h d ⊂ Esq h' d'`. El
   testigo es la función que define el escalón de arriba.
2. **El índice es fiel** (`indice_strictMono`, `indice_sobre`): `(h, d) ↦ ω · h + d` es estrictamente creciente y toca
   todos los ordinales menores que `ω · ω`. Los escalones forman un orden de tipo `ω²`.
3. **Los límites son las clases conocidas.** El límite de la fila `h` es `EsqLim h = ⋃ d, Esq h d`:
   * `EsqLim 0 = Pol` (`esqLim_cero`);
   * `EsqLim 1 = Exp` (`esqLim_uno`);
   * **la unión de todo es la capa 2** (`capa_dos_eq`).

   Con el índice de este archivo, el supremo de la fila `h` es `ω · (h + 1)`, que es también el índice del escalón
   `(h + 1, 0)`: aquí los límites no tienen un ordinal propio. `CebollaFina.lean` (C4) corre los escalones a
   `ω · h + d + 1` y deja `ω · (h + 1)` libre para `EsqLim h`; ahí `Pol` queda en `ω`, `Exp` en `ω · 2` y la capa 2 en
   `ω²`, probado.

La escala fina de C2 (`EscalaPolinomial.lean`) vive entre dos escalones consecutivos de la fila 0: si `a ≥ 1` y
`b ≥ 1`, `nᵃ · logᵇ n` está en `Esq 0 a` y no en `Esq 0 (a-1)` (`pl_entre`). Es el relleno denso que el esqueleto no ve.

## Lo que no se usó

La jerarquía de Grzegorczyk (las funciones elementales son la capa 3 de esa jerarquía, y se caracterizan por torres de
altura fija) es la fuente clásica de «capa 2 = torres de altura fija». No la leí en esta sesión; las pruebas de aquí son
propias y solo usan `Jerarquia.lean`, `CebollaExp.lean` y `Landau.lean`.
-/

namespace Sagitta.Map
namespace Tiempo

/-! ## La torre -/

/-- **La torre de exponenciales** de altura `h`. -/
def torre (h : ℕ) : ℕ → ℕ := (fun x => 2 ^ x)^[h]

theorem torre_cero : torre 0 = id := rfl

/-- La torre crece por arriba: `torre (h+1) x = 2 ^ torre h x`. -/
theorem torre_succ (h x : ℕ) : torre (h + 1) x = 2 ^ torre h x := Function.iterate_succ_apply' _ _ _

/-- Y por abajo: `torre (h+1) x = torre h (2ˣ)`. -/
theorem torre_succ' (h x : ℕ) : torre (h + 1) x = torre h (2 ^ x) := Function.iterate_succ_apply _ _ _

theorem torre_strictMono (h : ℕ) : StrictMono (torre h) :=
  StrictMono.iterate (fun _ _ hab => Nat.pow_lt_pow_right (by norm_num) hab) h

theorem torre_mono (h : ℕ) : Monotone (torre h) := (torre_strictMono h).monotone

theorem le_torre (h x : ℕ) : x ≤ torre h x := by
  induction h with
  | zero => rfl
  | succ h ih => rw [torre_succ]; exact ih.trans (Nat.lt_two_pow_self).le

theorem torre_le_succ (h x : ℕ) : torre h x ≤ torre (h + 1) x := by
  rw [torre_succ']; exact torre_mono h (Nat.lt_two_pow_self).le

theorem torre_le_de_le {h h' : ℕ} (hh : h ≤ h') (x : ℕ) : torre h x ≤ torre h' x := by
  induction hh with
  | refl => rfl
  | step _ ih => exact ih.trans (torre_le_succ _ x)

/-- Sumar una constante abajo paga una suma arriba: `torre h x + C ≤ torre h ((C+1) · x)` si `x ≥ 1`. -/
theorem torre_suma (h : ℕ) : ∀ C x, 1 ≤ x → torre h x + C ≤ torre h ((C + 1) * x) := by
  induction h with
  | zero => intro C x hx; simp only [torre_cero, id]; nlinarith
  | succ h ih =>
    intro C x hx
    rw [torre_succ, torre_succ]
    have h1 := ih C x hx
    have h2 : 2 ^ torre h x * 2 ^ C ≤ 2 ^ torre h ((C + 1) * x) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) h1
    have h3 : C < 2 ^ C := Nat.lt_two_pow_self
    have h4 : 1 ≤ 2 ^ torre h x := Nat.one_le_two_pow
    nlinarith

/-- **Una constante delante se absorbe en el argumento**: `C · torre h x ≤ torre h ((C+1) · x)` si `x ≥ 1`. -/
theorem torre_mul (h : ℕ) (C x : ℕ) (hx : 1 ≤ x) : C * torre h x ≤ torre h ((C + 1) * x) := by
  cases h with
  | zero => simp only [torre_cero, id]; nlinarith
  | succ h =>
    rw [torre_succ, torre_succ]
    calc C * 2 ^ torre h x ≤ 2 ^ C * 2 ^ torre h x := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
      _ = 2 ^ (torre h x + C) := by rw [← pow_add, add_comm]
      _ ≤ 2 ^ torre h ((C + 1) * x) := Nat.pow_le_pow_right (by norm_num) (torre_suma h C x hx)

/-! ## Los escalones -/

/-- La función que define el escalón `(h, d)`: `torre h ((n+1)^(d+1))`. El exponente es `d + 1` y no `d` para que el
primer escalón de cada fila no sea una constante: con `d = 0`, `torre h (n⁰)` no depende de `n`. -/
def tope (h d n : ℕ) : ℕ := torre h ((n + 1) ^ (d + 1))

/-- **El escalón** `(h, d)`: lo que es `O(torre h ((n+1)^(d+1)))`. -/
def Esq (h d : ℕ) : Set (ℕ → ℕ) := O (tope h d)

/-- **El límite de la fila `h`**. En la cebolla de C4 ocupa el ordinal `ω · (h + 1)` (`cebolla_omega_mul`). -/
def EsqLim (h : ℕ) : Set (ℕ → ℕ) := ⋃ d, Esq h d

/-- **Control**: cada escalón tiene a su función. -/
theorem tope_mem (h d : ℕ) : tope h d ∈ Esq h d := ⟨1, 0, fun n _ => by simp⟩

theorem uno_le_pot (n d : ℕ) : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos n)

/-- `O` mira solo la cola y crece con su argumento. -/
theorem O_sub {g g' : ℕ → ℕ} (N : ℕ) (hg : ∀ n ≥ N, g n ≤ g' n) : O g ⊆ O g' := by
  rintro f ⟨C, M, hf⟩
  exact ⟨C, max M N, fun n hn =>
    (hf n (le_of_max_le_left hn)).trans (Nat.mul_le_mul_left C (hg n (le_of_max_le_right hn)))⟩

/-- Desde algún punto, `(n+1)ᵈ ≤ 2ⁿ`. -/
theorem pot_menor_dos (d : ℕ) : ∃ N, ∀ n ≥ N, (n + 1) ^ d ≤ 2 ^ n := by
  obtain ⟨N, hN⟩ := pol_menor_dos_pow 1 d
  exact ⟨N, fun n hn => by simpa using (hN n hn).le⟩

/-- **El tope crece en orden lexicográfico**, desde algún punto. -/
theorem tope_le {h d h' d' : ℕ} (hle : toLex (h, d) ≤ toLex (h', d')) :
    ∃ N, ∀ n ≥ N, tope h d n ≤ tope h' d' n := by
  rcases Prod.Lex.toLex_le_toLex.mp hle with hlt | ⟨rfl, hd⟩
  · obtain ⟨N, hN⟩ := pot_menor_dos (d + 1)
    refine ⟨N, fun n hn => ?_⟩
    have hn1 : n ≤ (n + 1) ^ (d' + 1) := (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
    simp only [tope]
    calc torre h ((n + 1) ^ (d + 1)) ≤ torre h (2 ^ n) := torre_mono h (hN n hn)
      _ ≤ torre h (2 ^ (n + 1) ^ (d' + 1)) := torre_mono h (Nat.pow_le_pow_right (by norm_num) hn1)
      _ = torre (h + 1) ((n + 1) ^ (d' + 1)) := (torre_succ' h _).symm
      _ ≤ torre h' ((n + 1) ^ (d' + 1)) := torre_le_de_le hlt _
  · exact ⟨0, fun n _ => torre_mono h (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))⟩

/-- **Los escalones crecen** en orden lexicográfico. -/
theorem esq_mono {h d h' d' : ℕ} (hle : toLex (h, d) ≤ toLex (h', d')) : Esq h d ⊆ Esq h' d' := by
  obtain ⟨N, hN⟩ := tope_le hle
  exact O_sub N hN

/-- **El escalón de arriba no cabe en el de abajo.** -/
theorem tope_no_esq {h d h' d' : ℕ} (hlt : toLex (h, d) < toLex (h', d')) : tope h' d' ∉ Esq h d := by
  rintro ⟨C, N, hN⟩
  -- `C · tope h d ≤ torre h ((C+1) · (n+1)^(d+1))`
  have hC : ∀ n ≥ N, tope h' d' n ≤ torre h ((C + 1) * (n + 1) ^ (d + 1)) := fun n hn =>
    (hN n hn).trans (torre_mul h C _ (uno_le_pot n _))
  rcases Prod.Lex.toLex_lt_toLex.mp hlt with hh | ⟨rfl, hd⟩
  · -- otra fila: `torre h' (…) ≥ torre h (2^(n+1))`, y `2^(n+1)` le gana a cualquier polinomio
    obtain ⟨M, hM⟩ := pol_menor_dos_pow (C + 1) (d + 1)
    set n := max N M
    have h1 : torre h (2 ^ (n + 1)) ≤ tope h' d' n := by
      simp only [tope]
      calc torre h (2 ^ (n + 1)) = torre (h + 1) (n + 1) := (torre_succ' h _).symm
        _ ≤ torre (h + 1) ((n + 1) ^ (d' + 1)) := torre_mono _ (Nat.le_self_pow (by omega) _)
        _ ≤ torre h' ((n + 1) ^ (d' + 1)) := torre_le_de_le hh _
    have h2 := (torre_strictMono h).le_iff_le.mp (h1.trans (hC n (le_max_left _ _)))
    have h3 := hM n (le_max_right _ _)
    have : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)
    omega
  · -- misma fila: `(n+1)^(d'+1) ≤ (C+1) · (n+1)^(d+1)` es falso para `n > C`
    set n := max N (C + 1)
    have h2 := (torre_strictMono h).le_iff_le.mp (hC n (le_max_left _ _))
    have hn : C + 1 ≤ n := le_max_right _ _
    have h3 : (n + 1) ^ (d + 1 + 1) ≤ (n + 1) ^ (d' + 1) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    have h4 : 1 ≤ (n + 1) ^ (d + 1) := uno_le_pot n _
    rw [pow_succ] at h3
    nlinarith

/-- **El esqueleto crece estrictamente.** -/
theorem esq_estricta {h d h' d' : ℕ} (hlt : toLex (h, d) < toLex (h', d')) : Esq h d ⊂ Esq h' d' :=
  LE.le.ssubset_of_not_superset (esq_mono hlt.le) fun hs => tope_no_esq hlt (hs (tope_mem h' d'))

/-! ## El índice ordinal -/

open Ordinal in
/-- **El índice** del escalón `(h, d)`: el ordinal `ω · h + d`. -/
noncomputable def indice (p : ℕ ×ₗ ℕ) : Ordinal := ω * ((ofLex p).1 : Ordinal) + ((ofLex p).2 : Ordinal)

open Ordinal in
theorem indice_lt_fila (h d : ℕ) : indice (toLex (h, d)) < ω * ((h + 1 : ℕ) : Ordinal) := by
  simp only [indice, ofLex_toLex, Nat.cast_add, Nat.cast_one, mul_add_one]
  exact (add_lt_add_iff_left _).2 (natCast_lt_omega0 d)

open Ordinal in
/-- **El índice es estrictamente creciente.** -/
theorem indice_strictMono : StrictMono indice := by
  intro p q hlt
  obtain ⟨⟨h, d⟩, rfl⟩ : ∃ x, toLex x = p := ⟨ofLex p, rfl⟩
  obtain ⟨⟨h', d'⟩, rfl⟩ : ∃ x, toLex x = q := ⟨ofLex q, rfl⟩
  rcases Prod.Lex.toLex_lt_toLex.mp hlt with hh | ⟨he, hd⟩
  · simp only at hh
    calc indice (toLex (h, d)) < ω * ((h + 1 : ℕ) : Ordinal) := indice_lt_fila h d
      _ ≤ ω * (h' : Ordinal) := by gcongr; exact Nat.cast_le.mpr hh
      _ ≤ indice (toLex (h', d')) := le_self_add
  · simp only at he hd
    subst he
    simp only [indice, ofLex_toLex]
    exact (add_lt_add_iff_left _).2 (Nat.cast_lt.mpr hd)

open Ordinal in
/-- **El índice toca todo ordinal menor que `ω · ω`.** -/
theorem indice_sobre {α : Ordinal} (hα : α < ω * ω) : ∃ p, indice p = α := by
  have h0 : (ω : Ordinal) ≠ 0 := omega0_ne_zero
  obtain ⟨h, hh⟩ := lt_omega0.mp ((lt_mul_iff_div_lt h0).mp hα)
  obtain ⟨d, hd⟩ := lt_omega0.mp (mod_lt α h0)
  refine ⟨toLex (h, d), ?_⟩
  simp only [indice, ofLex_toLex]
  rw [← hh, ← hd, div_add_mod]

/-! ## Los límites -/

theorem tope_cero (d : ℕ) : tope 0 d = fun n => (n + 1) ^ (d + 1) := rfl

theorem tope_uno (d : ℕ) : tope 1 d = fun n => 2 ^ (n + 1) ^ (d + 1) := by
  funext n; simp only [tope, torre_succ, torre_cero, id]

/-- **El límite de la fila 0 es `Pol`** (en C4, el ordinal `ω`). -/
theorem esqLim_cero : EsqLim 0 = Pol := by
  ext f
  simp only [EsqLim, Esq, Set.mem_iUnion, pol_iff_O, tope_cero]
  constructor
  · rintro ⟨d, hd⟩; exact ⟨d + 1, hd⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, O_sub 0 (fun n _ => Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ k)) hk⟩

/-- **El límite de la fila 1 es `Exp`** (en C4, el ordinal `ω · 2`). -/
theorem esqLim_uno : EsqLim 1 = Exp := by
  ext f
  simp only [EsqLim, Esq, Set.mem_iUnion, tope_uno]
  constructor
  · rintro ⟨d, C, N, hN⟩
    let B := ∑ i ∈ Finset.range N, f i
    refine ⟨fun n => (n + 1) ^ (d + 1) + C + B, ?_, fun n => ?_⟩
    · exact pol_add (pol_add ⟨1, d + 1, fun n => by simp⟩ (pol_const C)) (pol_const B)
    · by_cases hn : N ≤ n
      · calc f n ≤ C * 2 ^ (n + 1) ^ (d + 1) := hN n hn
          _ ≤ 2 ^ C * 2 ^ (n + 1) ^ (d + 1) := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
          _ = 2 ^ ((n + 1) ^ (d + 1) + C) := by rw [← pow_add, add_comm]
          _ ≤ 2 ^ ((n + 1) ^ (d + 1) + C + B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      · have h1 : f n ≤ B := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr (by omega))
        calc f n ≤ B := h1
          _ ≤ 2 ^ B := Nat.lt_two_pow_self.le
          _ ≤ 2 ^ ((n + 1) ^ (d + 1) + C + B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rintro ⟨K, ⟨c, k, hK⟩, hf⟩
    refine ⟨k, 1, c, fun n hn => ?_⟩
    have : K n ≤ (n + 1) ^ (k + 1) := (hK n).trans (by rw [pow_succ]; nlinarith [uno_le_pot n k])
    rw [one_mul]
    exact (hf n).trans (Nat.pow_le_pow_right (by norm_num) this)

/-- `n + m + 1 ≤ (n+1)^(m+1)` si `n ≥ 1` (Bernoulli). -/
theorem bernoulli {n : ℕ} (hn : 1 ≤ n) (m : ℕ) : n + m + 1 ≤ (n + 1) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ]; nlinarith

/-- La iterada de `F 2` queda debajo de una torre: `(F 2)^[m] y ≤ torre m (2^m · y)` si `y ≥ 1`. -/
theorem iter_F_dos (m : ℕ) : ∀ y, 1 ≤ y → (F 2)^[m] y ≤ torre m (2 ^ m * y) := by
  induction m with
  | zero => intro y _; simp [torre_cero]
  | succ m ih =>
    intro y hy
    have hF : F 2 y ≤ 2 ^ (2 * y) := by
      rw [F_dos, two_mul, pow_add]; exact Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    have hF1 : 1 ≤ F 2 y := by rw [F_dos]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hm : m < 2 ^ m := Nat.lt_two_pow_self
    have he : m + 2 * y ≤ 2 ^ (m + 1) * y := by rw [pow_succ]; nlinarith
    rw [Function.iterate_succ_apply, torre_succ']
    calc (F 2)^[m] (F 2 y) ≤ torre m (2 ^ m * F 2 y) := ih _ hF1
      _ ≤ torre m (2 ^ m * 2 ^ (2 * y)) := torre_mono m (Nat.mul_le_mul_left _ hF)
      _ = torre m (2 ^ (m + 2 * y)) := by rw [pow_add]
      _ ≤ torre m (2 ^ (2 ^ (m + 1) * y)) := torre_mono m (Nat.pow_le_pow_right (by norm_num) he)

/-- Lo que es `O` de algo de la capa 2, está en la capa 2. -/
theorem O_capa_dos {g f : ℕ → ℕ} (hg : g ∈ Capa 2) (hf : f ∈ O g) : f ∈ Capa 2 := by
  obtain ⟨C, N, hN⟩ := hf
  let B := ∑ i ∈ Finset.range N, f i
  have hp : (fun x => C * x + B) ∈ Pol := pol_add (pol_mul (pol_const C) pol_id) (pol_const B)
  refine capa_abajo (capa_comp (pol_sub_capa_dos hp) hg) fun n => ?_
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (Nat.le_add_right _ _)
  · exact (Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))).trans
      (Nat.le_add_left _ _)

theorem tope_capa_dos (h d : ℕ) : tope h d ∈ Capa 2 := by
  induction h with
  | zero => exact pol_sub_capa_dos ⟨1, d + 1, fun n => by simp [tope_cero]⟩
  | succ h ih =>
    have e : tope (h + 1) d = fun n => 2 ^ tope h d n := by funext n; simp only [tope, torre_succ]
    rw [e]; exact capa_comp dos_pow_capa_dos ih

/-- **La capa 2 es la unión del esqueleto**: el ordinal `ω²`. -/
theorem capa_dos_eq : Capa 2 = ⋃ h, EsqLim h := by
  ext f
  simp only [EsqLim, Set.mem_iUnion]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, 2 * m, 1, 1, fun n hn => ?_⟩
    have h1 : (F 2)^[m] (n + m) ≤ (F 2)^[m] (n + m + 1) := ((F_strictMono 2).iterate m).monotone (Nat.le_succ _)
    have h2 := iter_F_dos m (n + m + 1) (by omega)
    have h3 : 2 ^ m * (n + m + 1) ≤ (n + 1) ^ (2 * m + 1) := by
      rw [show 2 * m + 1 = m + (m + 1) by ring, pow_add]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) m) (bernoulli hn m)
    rw [one_mul]
    exact (hm n).trans (h1.trans (h2.trans (torre_mono m h3)))
  · rintro ⟨h, d, hf⟩
    exact O_capa_dos (tope_capa_dos h d) hf

/-! ## El relleno de C2, entre dos escalones -/

/-- **La escala fina vive entre dos escalones**: `n^(a+1) · log^(b+1) n` está en `Esq 0 (a+1)` (es `O(n^(a+2))`) pero no
en `Esq 0 a` (no es `O(n^(a+1))`). Ningún escalón del esqueleto distingue `n^(a+1) · log n` de `n^(a+1) · log² n`. -/
theorem pl_entre (a b : ℕ) : pl (a + 1) (b + 1) ∉ Esq 0 a ∧ pl (a + 1) (b + 1) ∈ Esq 0 (a + 1) := by
  constructor
  · rintro ⟨C, N, hN⟩
    set n := max N (2 ^ (C * 2 ^ (a + 1) + 1))
    have hn : 2 ^ (C * 2 ^ (a + 1) + 1) ≤ n := le_max_right _ _
    have hL : C * 2 ^ (a + 1) + 1 ≤ Nat.log 2 n := log_ge_de_pow hn
    have hpos : 1 ≤ n := le_trans Nat.one_le_two_pow hn
    have h1 := hN n (le_max_left _ _)
    simp only [tope_cero, pl] at h1
    have h2 : (n + 1) ^ (a + 1) ≤ 2 ^ (a + 1) * n ^ (a + 1) := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
    have h3 : Nat.log 2 n ≤ Nat.log 2 n ^ (b + 1) := Nat.le_self_pow (by omega) _
    have h4 : 1 ≤ n ^ (a + 1) := Nat.one_le_pow _ _ hpos
    nlinarith
  · obtain ⟨N, hN⟩ := logPot_o_id (b + 1) 1
    refine ⟨1, N, fun n hn => ?_⟩
    have h1 := hN n hn
    simp only [one_mul] at h1 ⊢
    simp only [tope_cero, pl]
    calc n ^ (a + 1) * Nat.log 2 n ^ (b + 1) ≤ n ^ (a + 1) * n := Nat.mul_le_mul_left _ h1
      _ = n ^ (a + 1 + 1) := (pow_succ _ _).symm
      _ ≤ (n + 1) ^ (a + 1 + 1) := Nat.pow_le_pow_left (Nat.le_succ n) _

/-! ## Controles

Cada escalón tiene su función, una exponencial no cabe en ningún escalón polinomial, y la escala crece entre filas. Los
mutantes de la revisión del 23 nov 2026 (`Esq 1 0 ⊆ Esq 0 5`, `esq_estricta` con `(2, 0) < (1, 7)`, `pl_entre` con
`b = 0`) no se pueden probar con estos teoremas. -/

example : tope 0 0 ∈ Esq 0 0 := tope_mem 0 0
example : tope 1 0 ∉ Esq 0 9 := tope_no_esq (by decide)
example : Esq 1 7 ⊂ Esq 2 0 := esq_estricta (by decide)
example : torre 2 3 = 256 := by decide

end Tiempo
end Sagitta.Map
