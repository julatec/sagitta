import Mathlib.Data.Nat.Digits.Defs

/-!
# La sucesión de Goodstein

Definición computable, los ejemplos de la presentación comprobados por cálculo, y el teorema enunciado
como proposición. La prueba necesita la buena fundación de `ε₀`; no está hecha aquí.
-/

namespace Sagitta.Map

/-- Escribe `n` en base `b` hereditaria y cambia la base por `b + 1`. El primer argumento es
combustible para la recursión sobre los exponentes; `n` siempre alcanza. -/
def subeBaseAux (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | comb + 1, n =>
    ((Nat.digits b n).zipIdx).foldl
      (fun acc di => acc + di.1 * (b + 1) ^ subeBaseAux b comb di.2) 0

/-- Cambia la base `b` por `b + 1` en la escritura hereditaria de `n`. -/
def subeBase (b n : ℕ) : ℕ := subeBaseAux b n n

/-- La sucesión de Goodstein de `m`: en el paso `k` se sube la base de `k + 2` a `k + 3` y se resta 1. -/
def goodstein (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => subeBase (k + 2) (goodstein m k) - 1

/-! Los ejemplos de la presentación, comprobados por cálculo al compilar. -/

#guard subeBase 2 4 = 27
#guard (List.range 6).map (goodstein 3) = [3, 3, 3, 2, 1, 0]
#guard (List.range 5).map (goodstein 4) = [4, 26, 41, 60, 83]

/-- **Teorema de Goodstein** (1944), como proposición: toda sucesión llega a 0. Es verdadero; su prueba
usa la buena fundación de `ε₀` y no es demostrable en la aritmética de Peano (Kirby y Paris, 1982). -/
def TeoremaGoodstein : Prop := ∀ m : ℕ, ∃ k : ℕ, goodstein m k = 0

/-- El caso `m = 3`, por cálculo. -/
theorem goodstein_tres : ∃ k : ℕ, goodstein 3 k = 0 := ⟨5, by decide⟩

end Sagitta.Map
