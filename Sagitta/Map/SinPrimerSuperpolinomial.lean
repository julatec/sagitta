import Sagitta.Map.LandauDenso
import Mathlib.Data.Nat.Sqrt

/-!
# No hay un primer superpolinomial

En la cebolla, el anillo que está justo encima de `Pol` es denso y no tiene borde inferior: para toda función que
crece y escapa de `Pol`, su raíz cuadrada también escapa de `Pol` y es despreciable frente a ella. Iterando, se arma
una escalera infinita que baja hacia `Pol` sin entrar nunca.

## Lo que se prueba

* `raiz_no_pol`: si `f ∉ Pol`, entonces `√f ∉ Pol` (raíz entera, `Nat.sqrt`).
* `raiz_o`: si `f` tiende a infinito, `√f ∈ o f`.
* `sin_primer_superpolinomial`: para toda `f` que tiende a infinito y escapa de `Pol` hay otra `g` con las mismas dos
  propiedades y `g ∈ o f`.
* `ninguna_es_la_minima`: no existe una superpolinomial que tienda a infinito y quede, salvo constante, debajo de
  todas las demás (`EsO f g` para toda `g`).
* `escalera_hacia_pol`: la escalera `f, √f, √√f, …`: cada peldaño escapa de `Pol` y es despreciable frente al
  anterior.

Controles: la hipótesis no es vacía (`iterada doblar`, que ya se sabe fuera de `Pol`, tiende a infinito:
`control_iterada`); sin «tiende a infinito», `raiz_o` falla (`sin_tender_falla`); y la raíz de algo en `Pol` sigue en `Pol`
(`raiz_pol`): la escalera baja hacia `Pol` desde arriba, pero no cruza el borde en ninguno de los dos sentidos.

## La lectura

Una prueba de `P ≠ NP` no puede decir «SAT necesita al menos el primer superpolinomial»: ese primero no existe. Tiene que
decir que **todo** el corte de costos de SAT queda por encima de `Pol`. Y `P ≠ NP` no obliga a que SAT tenga un
algoritmo óptimo: el corte podría ser una escalera como `escalera_hacia_pol`, que se acerca a `Pol` sin entrar. Esto es
una lectura; no se prueba nada sobre SAT.

## Lo que NO se prueba

* Nada sobre algoritmos: aquí solo hay funciones. Que existan problemas cuyos costos formen una escalera así es la
  aceleración de Blum (`AceleracionBlum.lean`, condicional; la existencia, en curso).
* Que `√` sea la única forma de bajar: cualquier `g` con `g ∉ Pol` y `g ∈ o f` sirve; la raíz es solo un testigo.
* Nada sobre `P` contra `NP`.
-/

namespace Sagitta.Map
namespace Tiempo
namespace SinPrimerSuperpolinomial

/-- **Tiende a infinito**: desde algún punto supera cualquier cota. -/
def TiendeInf (f : ℕ → ℕ) : Prop := ∀ M, ∃ N, ∀ n ≥ N, M ≤ f n

/-- La raíz entera, punto a punto. -/
def raiz (f : ℕ → ℕ) : ℕ → ℕ := fun n => Nat.sqrt (f n)

/-- **Si la raíz está en `Pol`, la función también.** `f < (√f + 1)²`. -/
theorem pol_de_raiz {f : ℕ → ℕ} (h : raiz f ∈ Pol) : f ∈ Pol := by
  obtain ⟨c, k, hc⟩ := h
  refine ⟨(c + 1) ^ 2, 2 * k, fun n => ?_⟩
  have h1 : f n < (Nat.sqrt (f n) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' (f n); simpa [pow_two] using this
  have h2 : Nat.sqrt (f n) + 1 ≤ (c + 1) * (n + 1) ^ k := by
    have := hc n
    have h1k : 1 ≤ (n + 1) ^ k := one_le_succ_pow n k
    simp only [raiz] at this
    nlinarith
  calc f n ≤ (Nat.sqrt (f n) + 1) ^ 2 := h1.le
    _ ≤ ((c + 1) * (n + 1) ^ k) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = (c + 1) ^ 2 * (n + 1) ^ (2 * k) := by rw [mul_pow, ← pow_mul, mul_comm k 2]

/-- **La raíz de una superpolinomial es superpolinomial.** -/
theorem raiz_no_pol {f : ℕ → ℕ} (hf : f ∉ Pol) : raiz f ∉ Pol := fun h => hf (pol_de_raiz h)

/-- **Control: la raíz no saca de `Pol`.** Lo que está en `Pol` sigue en `Pol` al sacarle la raíz. -/
theorem raiz_pol {f : ℕ → ℕ} (hf : f ∈ Pol) : raiz f ∈ Pol := by
  obtain ⟨c, k, hc⟩ := hf
  exact ⟨c, k, fun n => (Nat.sqrt_le_self (f n)).trans (hc n)⟩

/-- **La raíz de algo que tiende a infinito tiende a infinito.** -/
theorem raiz_tiende {f : ℕ → ℕ} (hf : TiendeInf f) : TiendeInf (raiz f) := fun M => by
  obtain ⟨N, hN⟩ := hf (M * M)
  exact ⟨N, fun n hn => Nat.le_sqrt.mpr (hN n hn)⟩

/-- **La raíz es despreciable**: si `f` tiende a infinito, `√f ∈ o f`. -/
theorem raiz_o {f : ℕ → ℕ} (hf : TiendeInf f) : raiz f ∈ o f := fun c => by
  obtain ⟨N, hN⟩ := raiz_tiende hf c
  refine ⟨N, fun n hn => ?_⟩
  have hc : c ≤ Nat.sqrt (f n) := hN n hn
  calc c * raiz f n ≤ Nat.sqrt (f n) * Nat.sqrt (f n) := Nat.mul_le_mul_right _ hc
    _ ≤ f n := Nat.sqrt_le (f n)

/-- **No hay un primer superpolinomial.** Debajo de toda superpolinomial que tiende a infinito hay otra, despreciable
frente a ella. -/
theorem sin_primer_superpolinomial {f : ℕ → ℕ} (hf : f ∉ Pol) (ht : TiendeInf f) :
    ∃ g, g ∉ Pol ∧ TiendeInf g ∧ g ∈ o f :=
  ⟨raiz f, raiz_no_pol hf, raiz_tiende ht, raiz_o ht⟩

/-- **Ninguna superpolinomial es la mínima**, ni siquiera salvo constante. -/
theorem ninguna_es_la_minima :
    ¬ ∃ f, f ∉ Pol ∧ TiendeInf f ∧ ∀ g, g ∉ Pol → TiendeInf g → EsO f g := by
  rintro ⟨f, hf, ht, hmin⟩
  obtain ⟨g, hg, hgt, hgo⟩ := sin_primer_superpolinomial hf ht
  obtain ⟨C, N₁, hC⟩ := hmin g hg hgt
  obtain ⟨N₂, hN₂⟩ := hgo (C + 1)
  obtain ⟨N₃, hN₃⟩ := hgt 1
  let n := max N₁ (max N₂ N₃)
  have a := hC n (le_max_left _ _)
  have b := hN₂ n ((le_max_left _ _).trans (le_max_right _ _))
  have d := hN₃ n ((le_max_right _ _).trans (le_max_right _ _))
  nlinarith

/-- **La escalera hacia `Pol`**: `f, √f, √√f, …`. -/
def escalera (f : ℕ → ℕ) (k : ℕ) : ℕ → ℕ := raiz^[k] f

theorem escalera_succ (f : ℕ → ℕ) (k : ℕ) : escalera f (k + 1) = raiz (escalera f k) :=
  Function.iterate_succ_apply' raiz k f

/-- **Cada peldaño escapa de `Pol`, tiende a infinito y es despreciable frente al anterior.** -/
theorem escalera_hacia_pol {f : ℕ → ℕ} (hf : f ∉ Pol) (ht : TiendeInf f) (k : ℕ) :
    escalera f k ∉ Pol ∧ TiendeInf (escalera f k) ∧ escalera f (k + 1) ∈ o (escalera f k) := by
  induction k with
  | zero => exact ⟨hf, ht, by rw [escalera_succ]; exact raiz_o ht⟩
  | succ k ih =>
    obtain ⟨h1, h2, -⟩ := ih
    rw [escalera_succ]
    refine ⟨raiz_no_pol h1, raiz_tiende h2, ?_⟩
    rw [escalera_succ, escalera_succ]
    exact raiz_o (raiz_tiende h2)

/-! ## Controles -/

/-- **La hipótesis no es vacía**: `iterada doblar` (fuera de `Pol`, por `Landau.lean`) tiende a infinito. -/
theorem control_iterada : iterada doblar ∉ Pol ∧ TiendeInf (iterada doblar) := by
  have key : ∀ j m, m ≤ doblar^[j] m := fun j => by
    induction j with
    | zero => intro m; simp
    | succ j ih =>
      intro m; rw [Function.iterate_succ_apply']; exact (ih m).trans (by simp only [doblar]; omega)
  exact ⟨iterada_doblar_no_pol, fun M => ⟨M, fun n hn => hn.trans (key n n)⟩⟩

/-- **Sin «tiende a infinito», `raiz_o` falla**: con `f` que vale `1` en los pares, `√f ∉ o f`. -/
theorem sin_tender_falla : raiz (fun n => if n % 2 = 0 then 1 else 2 ^ n) ∉ o (fun n => if n % 2 = 0 then 1 else 2 ^ n) := by
  intro h
  obtain ⟨N, hN⟩ := h 2
  have := hN (2 * N) (by omega)
  simp [raiz, Nat.mul_mod_right] at this

end SinPrimerSuperpolinomial
end Tiempo
end Sagitta.Map
