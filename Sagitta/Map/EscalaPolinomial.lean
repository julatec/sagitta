import Sagitta.Map.LandauDenso

/-!
# La escala fina de los polinomios: `nᵃ · logᵇ n` (C2)

Segunda fase del refinamiento de la cebolla. `LandauDenso.lean` (C1) mostró que el orden `o` de Landau es denso y tiene
huecos, así que ninguna escala numerable lo llena. Aquí va la escala que sí se usa en la práctica para medir tiempos
polinomiales: las funciones

  `pl a b n = nᵃ · (log₂ n)ᵇ`,

indexadas por pares `(a, b)` en **orden lexicográfico**: primero manda el grado `a`, y a igual grado manda la potencia
del logaritmo `b`.

## Lo que se prueba

1. **La escala es estricta** (`pl_o_de_lt`): si `(a, b) < (a', b')` lexicográficamente, `pl a b ∈ o (pl a' b')`. Los
   dos casos son distintos:
   * mismo grado, `b < b'`: sobra un factor `log n`, que pasa a toda constante;
   * grado menor, `a < a'`: sobra un factor `n`, que pasa a toda potencia del logaritmo (`logPot_o_id`, por
     `pol_menor_dos_pow` de `Landau.lean`: un polinomio en `L` queda debajo de `2ᴸ ≤ n`).
2. **Y es fiel** (`pl_o_iff`): `pl a b ∈ o (pl a' b')` **si y solo si** `(a, b) < (a', b')`. La vuelta usa que `o` es
   irreflexiva y asimétrica entre funciones que a la larga son positivas (`o_asimetrica`).
3. **Todo queda en `Pol`** (`pl_pol`), y la escala entera vive debajo de `2ⁿ` (`pl_o_dos_pow`): es el piso de la capa
   2, que `CebollaExp.lean` mostró que junta `Pol` y `Exp`.

Con `nlog k = pl 1 k` (`nlog_eq_pl`), la sucesión de `LandauDenso.lean` es la fila `a = 1` de esta escala. El tipo de
orden de la escala es `ω · ω = ω²` (pares de naturales en orden lexicográfico); C3 lo usa como el primer tramo del
esqueleto ordinal.
-/

namespace Sagitta.Map
namespace Tiempo

/-- **La escala**: `nᵃ · (log₂ n)ᵇ`. -/
def pl (a b n : ℕ) : ℕ := n ^ a * Nat.log 2 n ^ b

theorem nlog_eq_pl (k : ℕ) : nlog k = pl 1 k := by funext n; simp [nlog, pl]

/-! ## Herramientas sobre `o` -/

/-- `o` mira solo la cola: si `f ≤ f'` y `g' ≤ g` desde algún punto, `f' ∈ o g'` da `f ∈ o g`. -/
theorem o_de_cola {f f' g g' : ℕ → ℕ} (h : f' ∈ o g') (M : ℕ) (hf : ∀ n ≥ M, f n ≤ f' n)
    (hg : ∀ n ≥ M, g' n ≤ g n) : f ∈ o g := fun c => by
  obtain ⟨N, hN⟩ := h c
  refine ⟨max N M, fun n hn => ?_⟩
  calc c * f n ≤ c * f' n := Nat.mul_le_mul_left c (hf n (le_of_max_le_right hn))
    _ ≤ g' n := hN n (le_of_max_le_left hn)
    _ ≤ g n := hg n (le_of_max_le_right hn)

/-- **Irreflexiva**: una función que a la larga es positiva no es despreciable frente a sí misma. -/
theorem o_irrefl {g : ℕ → ℕ} (M : ℕ) (hg : ∀ n ≥ M, 1 ≤ g n) : g ∉ o g := fun h => by
  obtain ⟨N, hN⟩ := h 2
  have a := hN (max N M) (le_max_left _ _)
  have b := hg (max N M) (le_max_right _ _)
  omega

/-- **Asimétrica**: si `g` a la larga es positiva, `f ∈ o g` y `g ∈ o f` no pueden valer juntas. -/
theorem o_asimetrica {f g : ℕ → ℕ} (M : ℕ) (hg : ∀ n ≥ M, 1 ≤ g n) (h₁ : f ∈ o g) (h₂ : g ∈ o f) : False := by
  obtain ⟨N₁, h₁⟩ := h₁ 1
  obtain ⟨N₂, h₂⟩ := h₂ 2
  have a := h₁ (max (max N₁ N₂) M) (le_trans (le_max_left _ _) (le_max_left _ _))
  have b := h₂ (max (max N₁ N₂) M) (le_trans (le_max_right _ _) (le_max_left _ _))
  have c := hg (max (max N₁ N₂) M) (le_max_right _ _)
  omega

/-! ## El logaritmo -/

theorem log_ge_de_pow {c n : ℕ} (h : 2 ^ c ≤ n) : c ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) h

theorem pow_log_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)

/-- **Toda potencia del logaritmo es despreciable frente a `n`.** -/
theorem logPot_o_id (b : ℕ) : (fun n => Nat.log 2 n ^ b) ∈ o (fun n => n) := fun c => by
  obtain ⟨L₀, hL₀⟩ := pol_menor_dos_pow c b
  refine ⟨2 ^ L₀, fun n hn => ?_⟩
  have hL : L₀ ≤ Nat.log 2 n := log_ge_de_pow hn
  have h1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) hn
  have := hL₀ (Nat.log 2 n) hL
  calc c * Nat.log 2 n ^ b ≤ c * (Nat.log 2 n + 1) ^ b :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.le_succ _) b)
    _ ≤ 2 ^ Nat.log 2 n := this.le
    _ ≤ n := pow_log_le h1

/-! ## 1. La escala es estricta -/

/-- **Mismo grado, más logaritmo**: `pl a b ∈ o (pl a b')` si `b < b'`. -/
theorem pl_o_log {a b b' : ℕ} (h : b < b') : pl a b ∈ o (pl a b') := fun c => by
  refine ⟨2 ^ (c + 1), fun n hn => ?_⟩
  have hL : c + 1 ≤ Nat.log 2 n := log_ge_de_pow hn
  obtain ⟨d, rfl⟩ : ∃ d, b' = b + 1 + d := ⟨b' - (b + 1), by omega⟩
  have hd : 1 ≤ Nat.log 2 n ^ d := Nat.one_le_pow _ _ (by omega)
  simp only [pl]
  calc c * (n ^ a * Nat.log 2 n ^ b) = n ^ a * Nat.log 2 n ^ b * c := by ring
    _ ≤ n ^ a * Nat.log 2 n ^ b * (Nat.log 2 n * Nat.log 2 n ^ d) :=
        Nat.mul_le_mul_left _ (by nlinarith)
    _ = n ^ a * Nat.log 2 n ^ (b + 1 + d) := by ring

/-- **Grado menor**: `pl a b ∈ o (pl a' b')` si `a < a'`, cualesquiera sean `b` y `b'`. -/
theorem pl_o_grado {a a' b b' : ℕ} (h : a < a') : pl a b ∈ o (pl a' b') := fun c => by
  obtain ⟨N, hN⟩ := logPot_o_id b c
  refine ⟨max N 2, fun n hn => ?_⟩
  have h2 : 2 ≤ n := le_of_max_le_right hn
  have hc := hN n (le_of_max_le_left hn)
  have hL : 1 ≤ Nat.log 2 n := log_ge_de_pow (by simpa using h2)
  have hb' : 1 ≤ Nat.log 2 n ^ b' := Nat.one_le_pow _ _ (by omega)
  obtain ⟨d, rfl⟩ : ∃ d, a' = a + 1 + d := ⟨a' - (a + 1), by omega⟩
  have hd : 1 ≤ n ^ d := Nat.one_le_pow _ _ (by omega)
  simp only [pl]
  calc c * (n ^ a * Nat.log 2 n ^ b) = n ^ a * (c * Nat.log 2 n ^ b) := by ring
    _ ≤ n ^ a * n := Nat.mul_le_mul_left _ hc
    _ ≤ n ^ a * n * (n ^ d * Nat.log 2 n ^ b') := Nat.le_mul_of_pos_right _ (by positivity)
    _ = n ^ (a + 1 + d) * Nat.log 2 n ^ b' := by ring

/-- **La escala es estricta en el orden lexicográfico.** -/
theorem pl_o_de_lt {a b a' b' : ℕ} (h : toLex (a, b) < toLex (a', b')) : pl a b ∈ o (pl a' b') := by
  rcases Prod.Lex.lt_iff.mp h with h | ⟨rfl, h⟩
  · exact pl_o_grado h
  · exact pl_o_log h

/-! ## 2. Y es fiel -/

theorem pl_pos {a b n : ℕ} (hn : 2 ≤ n) : 1 ≤ pl a b n := by
  have hL : 1 ≤ Nat.log 2 n := log_ge_de_pow (by simpa using hn)
  exact Nat.one_le_iff_ne_zero.mpr (by simp only [pl]; positivity)

/-- **Control**: ningún escalón es despreciable frente a sí mismo. -/
theorem pl_no_o_propia (a b : ℕ) : pl a b ∉ o (pl a b) := o_irrefl 2 fun _ hn => pl_pos hn

/-- **La escala es fiel**: `pl a b ∈ o (pl a' b')` exactamente cuando `(a, b) < (a', b')` lexicográficamente. Es un
encaje de orden de `ℕ ×ₗ ℕ` (tipo `ω²`) en el orden de Landau. -/
theorem pl_o_iff {a b a' b' : ℕ} : pl a b ∈ o (pl a' b') ↔ toLex (a, b) < toLex (a', b') := by
  refine ⟨fun h => ?_, pl_o_de_lt⟩
  rcases lt_trichotomy (toLex (a, b)) (toLex (a', b')) with hlt | heq | hgt
  · exact hlt
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (toLex.injective heq)
    exact absurd h (pl_no_o_propia a b)
  · exact (o_asimetrica 2 (fun _ hn => pl_pos hn) h (pl_o_de_lt hgt)).elim

/-- La escala como función del orden lexicográfico. -/
def escalaPl (p : ℕ ×ₗ ℕ) : ℕ → ℕ := pl (ofLex p).1 (ofLex p).2

/-- **El encaje**: `p < q` en `ℕ ×ₗ ℕ` si y solo si `escalaPl p ∈ o (escalaPl q)`. -/
theorem escalaPl_o_iff (p q : ℕ ×ₗ ℕ) : escalaPl p ∈ o (escalaPl q) ↔ p < q := by
  simpa [escalaPl] using (pl_o_iff (a := (ofLex p).1) (b := (ofLex p).2) (a' := (ofLex q).1) (b' := (ofLex q).2))

/-- El encaje es inyectivo: escalones distintos son funciones distintas. -/
theorem escalaPl_inyectiva : Function.Injective escalaPl := fun p q h => by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · have := (escalaPl_o_iff p q).mpr hlt
    rw [h] at this
    exact absurd this (pl_no_o_propia _ _)
  · exact heq
  · have := (escalaPl_o_iff q p).mpr hgt
    rw [h] at this
    exact absurd this (pl_no_o_propia _ _)

/-! ## 3. Todo en `Pol`, todo debajo de `2ⁿ` -/

/-- **Cada escalón es polinomial**: `nᵃ · logᵇ n ≤ (n+1)^(a+b)`. -/
theorem pl_pol (a b : ℕ) : pl a b ∈ Pol := by
  refine ⟨1, a + b, fun n => ?_⟩
  have hl : Nat.log 2 n ≤ n + 1 := (Nat.log_le_self 2 n).trans (Nat.le_succ n)
  simp only [pl, one_mul, pow_add]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_succ n) a) (Nat.pow_le_pow_left hl b)

/-- **Toda la escala queda debajo de `2ⁿ`.** -/
theorem pl_o_dos_pow (a b : ℕ) : pl a b ∈ o (fun n => 2 ^ n) := fun c => by
  obtain ⟨N, hN⟩ := pol_menor_dos_pow c (a + b)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨_, _, h⟩ := pl_pol a b
  have hl : Nat.log 2 n ≤ n + 1 := (Nat.log_le_self 2 n).trans (Nat.le_succ n)
  have : pl a b n ≤ (n + 1) ^ (a + b) := by
    simp only [pl, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_succ n) a) (Nat.pow_le_pow_left hl b)
  exact (Nat.mul_le_mul_left c this).trans (hN n hn).le

/-! ## Controles -/

/-- `pl 2 0` es `n²` y `pl 1 1` es `n · log n`. -/
example : pl 2 0 10 = 100 ∧ pl 1 1 16 = 64 := by
  refine ⟨by simp [pl], ?_⟩
  simp only [pl, pow_one]
  rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]; norm_num

/-- `n · log² n ≺ n²`: el logaritmo nunca alcanza un grado más. -/
example : pl 1 2 ∈ o (pl 2 0) := pl_o_grado (by norm_num)

/-- Y la vuelta es falsa: `n²` no es despreciable frente a `n · log² n`. -/
example : pl 2 0 ∉ o (pl 1 2) := fun h => by
  have := pl_o_iff.mp h
  simp [Prod.Lex.lt_iff] at this

end Tiempo
end Sagitta.Map
