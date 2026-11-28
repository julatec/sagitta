import Sagitta.Map.Completitud.Puente
import Mathlib.Tactic.NormNum.Prime

/-!
# El teorema fundamental de la aritmética y S¹₂

La pregunta de José (24 nov 2026): ¿dónde queda la descomposición en primos del teorema fundamental de la aritmética?
En el mapa de Sagitta es casi la jugada: total (siempre hay factorización), con respuesta **única**, verificable, con
tamaños parejos, y con una flecha (de `N` a sus factores) que se cree profunda. Y su mitad de **existencia** choca con
la aritmética del tiempo polinomial: por el teorema de testigos de Buss, una prueba en S¹₂ daría un algoritmo
polinomial.

Este archivo dice eso con el teorema de Buss que Sagitta ya tiene con derivaciones (`buss_deriva`,
`Sagitta/Map/Completitud/Puente.lean`), sobre la función `Nat.minFac` de Mathlib (el menor factor primo). Encontrar el menor
factor primo es el paso de la factorización: con él se divide y se repite, y hay a lo sumo `log₂ N` rondas.

## Lo que se prueba

* `buss_menorFactor`: si una fórmula `φ ∈ Σᵇ₁` tiene en ℕ como gráfico a `Nat.minFac`, y S¹₂ deriva
  `∀x ∃!y φ(x, y)`, entonces `Nat.minFac` es de tiempo polinomial (`EsPolinomial`). Es `buss_deriva` aplicado.
* **`s12_no_demuestra_factor`** (el contrapositivo): si encontrar el menor factor primo **no** es polinomial, S¹₂ no
  deriva `∀x ∃!y φ(x, y)` para **ninguna** fórmula `Σᵇ₁` que lo defina. El enunciado es verdadero en ℕ (`minFac` es una
  función): es un teorema verdadero que S¹₂ no alcanza, si factorizar es difícil.
* `existeUnico_verdadero`: en ℕ, `∀x ∃!y φ(x, y)` vale para toda `φ` cuyo gráfico sea una función. Separa «verdadero»
  de «demostrable en S¹₂».

## Actualización (25 nov 2026, noche): la pieza 1 ya está

`SigmaIgualNP` quedó probado (`Sagitta/Map/SigmaFagin/Palabras.lean`, 12bfb35) y el gráfico de `Nat.minFac` está en NP por
certificados de Pratt (`Sagitta/Map/Borde/Pratt.lean`, 0295010). Ahí está `s12_no_demuestra_factor_sin_formula`: si
`Nat.minFac` no es polinomial, **existe** una `φ ∈ Σᵇ₁` con gráfico exacto `minFac` y S¹₂ no deriva su `∀x ∃!y`. Queda
solo la pieza 2, que factorizar sea difícil. Lo de abajo se deja como estaba, para la historia.

## Lo que NO se prueba (las dos piezas abiertas, dichas con precisión)

1. **Que exista una `φ ∈ Σᵇ₁` con gráfico `Nat.minFac`.** El gráfico está en NP (el testigo es la factorización
   completa de `N`, con certificados de primalidad de Pratt), así que la fórmula existe si `Σᵇ₁ = NP` sobre ℕ, que es
   `SigmaIgualNP` (`Sagitta/Map/SigmaNP.lean`, abierto en Sagitta). Escribirla a mano
   pide la fase A y B de ese plan (bits, sucesiones y la exponenciación modular como fórmulas). Aquí es una hipótesis.
2. **Que factorizar sea difícil.** Es una conjetura (el mejor algoritmo clásico conocido es subexponencial; Shor lo
   hace en tiempo polinomial cuántico). Aquí es una hipótesis, y el teorema dice qué pasa si vale.

No es nuevo: es la lectura clásica del teorema de testigos de Buss sobre la factorización (aparece, por ejemplo, en el
trabajo de Jeřábek sobre factorización y aritmética acotada; sin verificar aquí). Lo propio es tenerlo sobre la S¹₂ y
las derivaciones de Sagitta, con `Nat.minFac` de Mathlib.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map.Acotada.FactorizacionS12

open Sagitta.Map Sagitta.Map.Acotada

/-- **Buss para el menor factor primo**: si S¹₂ deriva que todo `x` tiene un único `y` con `φ(x, y)`, y en ℕ ese `y`
es `Nat.minFac x`, encontrar el menor factor primo es de tiempo polinomial. -/
theorem buss_menorFactor {φ : L.Formula (Fin 2)} (hφ : EsSigma1 φ)
    (hg : ∀ n : ℕ, φ.Realize ![n, Nat.minFac n]) (h : DerivaS12 (cierre (existeUnico φ))) :
    EsPolinomial Nat.minFac :=
  buss_deriva hφ h hg

/-- **La existencia en la factorización no se demuestra en S¹₂, si factorizar es difícil.** Si encontrar el menor
factor primo no es polinomial, ninguna fórmula `Σᵇ₁` que lo defina tiene su `∀x ∃!y` derivable en S¹₂. -/
theorem s12_no_demuestra_factor (hdura : ¬ EsPolinomial Nat.minFac) {φ : L.Formula (Fin 2)} (hφ : EsSigma1 φ)
    (hg : ∀ n : ℕ, φ.Realize ![n, Nat.minFac n]) :
    ¬ DerivaS12 (cierre (existeUnico φ)) :=
  fun h => hdura (buss_menorFactor hφ hg h)

/-- En ℕ, si el gráfico de `φ` es exactamente una función `f`, el enunciado `∀x ∃!y φ(x, y)` es verdadero: lo que
falla en S¹₂ es la demostración, no la verdad. -/
theorem existeUnico_verdadero {φ : L.Formula (Fin 2)} {f : ℕ → ℕ}
    (hgraf : ∀ n m : ℕ, φ.Realize ![n, m] ↔ m = f n) :
    ∀ n : ℕ, ∃! m : ℕ, φ.Realize ![n, m] :=
  fun n => ⟨f n, (hgraf n (f n)).2 rfl, fun m hm => (hgraf n m).1 hm⟩

/-! ## Controles -/

/-- `Nat.minFac` hace lo que dice: el menor factor primo de 91 es 7, el de 97 (primo) es 97, y el de 2^10 es 2. -/
example : Nat.minFac 91 = 7 ∧ Nat.minFac 97 = 97 ∧ Nat.minFac (2 ^ 10) = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- Con el menor factor primo se factoriza: el cociente `N / minFac N` es más chico (para `N ≥ 2`), así que repetir
termina en a lo sumo `log₂ N` rondas. -/
example (N : ℕ) (hN : 2 ≤ N) : N / Nat.minFac N < N :=
  Nat.div_lt_self (by omega) (Nat.Prime.one_lt (Nat.minFac_prime (by omega)))

/- Mutante probado (24 nov 2026, fuera del repositorio): quitar la hipótesis `hφ : EsSigma1 φ` de `buss_menorFactor` deja
la prueba sin completar: `buss_deriva` la pide. Es un mutante débil (falla porque falta un argumento), como todo mutante
de un corolario de una línea; lo que la hipótesis significa es que el teorema de Buss solo vale para fórmulas Σᵇ₁:
con una fórmula cualquiera, S¹₂ puede demostrar la totalidad de funciones que no son polinomiales. -/

end Sagitta.Map.Acotada.FactorizacionS12
