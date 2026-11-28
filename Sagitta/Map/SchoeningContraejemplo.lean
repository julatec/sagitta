import Sagitta.Map.Schoening

/-!
# El lema de Schöning sin factor polinomial es falso

Muestra que el **Lema 1 de Moser–Scheder** (arXiv 1008.4067), tomado al pie de la letra **sin el factor polinomial**
que su notación `O*` esconde, es **falso** en el modelo contado de `Sagitta.Map.Schoening`. El lema diría: si `β` es solución
de una 3-CNF y `α` está a distancia `r` de `β`, la caminata de `3n` pasos acierta con proporción `≥ (1/2)^r`.

## La fórmula

Con `n = 8` variables, `formulaContra 8` tiene 392 cláusulas de tres literales, en tres bloques y en este orden:
`x_a ∨ ¬x_b ∨ ¬x_c` (`b < c`, `a ∉ {b, c}`), `x_a ∨ x_b ∨ ¬x_c` (`a < b`, `c ∉ {a, b}`) y `x_a ∨ x_b ∨ x_c`
(`a < b < c`). `β` = todo verdadero es solución (la única, según el cómputo externo). Desde `α` = todo verdadero salvo `x₀` (distancia 1), con
`t = 24` pasos aciertan exactamente `140 310 845 217` de las `3^24 = 282 429 536 481` sucesiones: proporción
`≈ 0,4968 < 1/2` (`proporcion_contra`, `schoening_sin_factor_contraejemplo`, `schoening_sin_factor_falso`). Con
`n = 7` la misma familia da `≈ 0,50003`, que no alcanza.

## Cómo se cuenta

No se enumeran las `3^24` sucesiones. `aciertosRec` cuenta por recursión sobre la primera elección y coincide con
`aciertos` (`aciertosRec_eq`, por `aciertos_succ`). Para memoizar, las 256 asignaciones se codifican por sus bits
(`deBits`) y se lleva un vector de 256 valores por paso (`vectorContra`), que coincide con `aciertosRec`
(`vectorContra_eq`). La tabla de transiciones (`tablaContra`) se generó afuera, pero el kernel la comprueba contra
`pasoCaminata` (`tablaContra_ok`). Todo con `decide +kernel`, sin `native_decide`: los axiomas son solo `propext`,
`Classical.choice` y `Quot.sound`.

## Cuánto tarda

En una Mac de 16 GB, el kernel tarda ≈ 4 s en comprobar la tabla y ≈ 15 s en calcular el vector a los 24 pasos; el
archivo entero compila en ≈ 30 s.
-/

namespace Sagitta.Map
namespace Tiempo

/-! ## La fórmula y la asignación -/

/-- **La fórmula del contraejemplo**, con `n` variables, en tres bloques y en este orden:
* `x_a ∨ ¬x_b ∨ ¬x_c` con `b < c` y `a ∉ {b, c}`;
* `x_a ∨ x_b ∨ ¬x_c` con `a < b` y `c ∉ {a, b}`;
* `x_a ∨ x_b ∨ x_c` con `a < b < c`.

Cada cláusula tiene un literal positivo primero, así que «todo verdadero» es solución. Para `n = 8` son 392 cláusulas. -/
def formulaContra (n : ℕ) : List Clausula :=
  let R := List.range n
  (R.flatMap fun a => R.flatMap fun b =>
      (R.filter fun c => decide (b < c) && a != b && a != c).map fun c => [(a, true), (b, false), (c, false)]) ++
  (R.flatMap fun a => R.flatMap fun b =>
      (R.filter fun c => decide (a < b) && c != a && c != b).map fun c => [(a, true), (b, true), (c, false)]) ++
  (R.flatMap fun a => R.flatMap fun b =>
      (R.filter fun c => decide (a < b) && decide (b < c)).map fun c => [(a, true), (b, true), (c, true)])

/-- La asignación codificada por los bits de `s`: la variable `i` vale el bit `i`. -/
def deBits (n s : ℕ) : Fin n → Bool := fun i => s.testBit i

/-- **La solución**: todo verdadero. -/
def betaContra : Fin 8 → Bool := fun _ => true

/-- **El arranque**: todo verdadero salvo `x₀`. Está a distancia 1 de la solución. -/
def alfaContra : Fin 8 → Bool := deBits 8 254

/-! ## La cuenta con memoria -/

/-- **Los aciertos por recursión**: el caso `0` mira si ya es solución y el caso `t + 1` suma sobre la primera
elección. Es la misma cuenta que `aciertos`, sin enumerar sucesiones. -/
def aciertosRec (F : List Clausula) (k : ℕ) : ℕ → (Fin n → Bool) → ℕ
  | 0, α => if solCNF F (List.ofFn α) = true then 1 else 0
  | t + 1, α => ∑ j : Fin k, aciertosRec F k t (pasoCaminata F α j)

/-- La tabla de transiciones de la fórmula con 8 variables: en la posición `s`, los códigos de las tres asignaciones
a las que lleva un paso desde `deBits 8 s`. Generada afuera; `tablaContra_ok` la comprueba en el kernel. -/
def tablaContra : List (ℕ × ℕ × ℕ) := [
  (1, 2, 4), (3, 5, 0), (3, 6, 0), (7, 2, 1), (5, 6, 0), (7, 4, 1), (7, 4, 2), (15, 6, 5),
  (9, 10, 0), (11, 8, 1), (11, 8, 2), (15, 10, 9), (13, 8, 4), (15, 12, 9), (15, 12, 10), (31, 14, 13),
  (17, 18, 0), (19, 16, 1), (19, 16, 2), (23, 18, 17), (21, 16, 4), (23, 20, 17), (23, 20, 18), (31, 22, 21),
  (25, 16, 8), (27, 24, 17), (27, 24, 18), (31, 26, 25), (29, 24, 20), (31, 28, 25), (31, 28, 26), (63, 30, 29),
  (33, 34, 0), (35, 32, 1), (35, 32, 2), (39, 34, 33), (37, 32, 4), (39, 36, 33), (39, 36, 34), (47, 38, 37),
  (41, 32, 8), (43, 40, 33), (43, 40, 34), (47, 42, 41), (45, 40, 36), (47, 44, 41), (47, 44, 42), (63, 46, 45),
  (49, 32, 16), (51, 48, 33), (51, 48, 34), (55, 50, 49), (53, 48, 36), (55, 52, 49), (55, 52, 50), (63, 54, 53),
  (57, 48, 40), (59, 56, 49), (59, 56, 50), (63, 58, 57), (61, 56, 52), (63, 60, 57), (63, 60, 58), (127, 62, 61),
  (65, 66, 0), (67, 64, 1), (67, 64, 2), (71, 66, 65), (69, 64, 4), (71, 68, 65), (71, 68, 66), (79, 70, 69),
  (73, 64, 8), (75, 72, 65), (75, 72, 66), (79, 74, 73), (77, 72, 68), (79, 76, 73), (79, 76, 74), (95, 78, 77),
  (81, 64, 16), (83, 80, 65), (83, 80, 66), (87, 82, 81), (85, 80, 68), (87, 84, 81), (87, 84, 82), (95, 86, 85),
  (89, 80, 72), (91, 88, 81), (91, 88, 82), (95, 90, 89), (93, 88, 84), (95, 92, 89), (95, 92, 90), (127, 94, 93),
  (97, 64, 32), (99, 96, 65), (99, 96, 66), (103, 98, 97), (101, 96, 68), (103, 100, 97), (103, 100, 98), (111, 102, 101),
  (105, 96, 72), (107, 104, 97), (107, 104, 98), (111, 106, 105), (109, 104, 100), (111, 108, 105), (111, 108, 106), (127, 110, 109),
  (113, 96, 80), (115, 112, 97), (115, 112, 98), (119, 114, 113), (117, 112, 100), (119, 116, 113), (119, 116, 114), (127, 118, 117),
  (121, 112, 104), (123, 120, 113), (123, 120, 114), (127, 122, 121), (125, 120, 116), (127, 124, 121), (127, 124, 122), (255, 126, 125),
  (129, 130, 0), (131, 128, 1), (131, 128, 2), (135, 130, 129), (133, 128, 4), (135, 132, 129), (135, 132, 130), (143, 134, 133),
  (137, 128, 8), (139, 136, 129), (139, 136, 130), (143, 138, 137), (141, 136, 132), (143, 140, 137), (143, 140, 138), (159, 142, 141),
  (145, 128, 16), (147, 144, 129), (147, 144, 130), (151, 146, 145), (149, 144, 132), (151, 148, 145), (151, 148, 146), (159, 150, 149),
  (153, 144, 136), (155, 152, 145), (155, 152, 146), (159, 154, 153), (157, 152, 148), (159, 156, 153), (159, 156, 154), (191, 158, 157),
  (161, 128, 32), (163, 160, 129), (163, 160, 130), (167, 162, 161), (165, 160, 132), (167, 164, 161), (167, 164, 162), (175, 166, 165),
  (169, 160, 136), (171, 168, 161), (171, 168, 162), (175, 170, 169), (173, 168, 164), (175, 172, 169), (175, 172, 170), (191, 174, 173),
  (177, 160, 144), (179, 176, 161), (179, 176, 162), (183, 178, 177), (181, 176, 164), (183, 180, 177), (183, 180, 178), (191, 182, 181),
  (185, 176, 168), (187, 184, 177), (187, 184, 178), (191, 186, 185), (189, 184, 180), (191, 188, 185), (191, 188, 186), (255, 190, 189),
  (193, 128, 64), (195, 192, 129), (195, 192, 130), (199, 194, 193), (197, 192, 132), (199, 196, 193), (199, 196, 194), (207, 198, 197),
  (201, 192, 136), (203, 200, 193), (203, 200, 194), (207, 202, 201), (205, 200, 196), (207, 204, 201), (207, 204, 202), (223, 206, 205),
  (209, 192, 144), (211, 208, 193), (211, 208, 194), (215, 210, 209), (213, 208, 196), (215, 212, 209), (215, 212, 210), (223, 214, 213),
  (217, 208, 200), (219, 216, 209), (219, 216, 210), (223, 218, 217), (221, 216, 212), (223, 220, 217), (223, 220, 218), (255, 222, 221),
  (225, 192, 160), (227, 224, 193), (227, 224, 194), (231, 226, 225), (229, 224, 196), (231, 228, 225), (231, 228, 226), (239, 230, 229),
  (233, 224, 200), (235, 232, 225), (235, 232, 226), (239, 234, 233), (237, 232, 228), (239, 236, 233), (239, 236, 234), (255, 238, 237),
  (241, 224, 208), (243, 240, 225), (243, 240, 226), (247, 242, 241), (245, 240, 228), (247, 244, 241), (247, 244, 242), (255, 246, 245),
  (249, 240, 232), (251, 248, 241), (251, 248, 242), (255, 250, 249), (253, 248, 244), (255, 252, 249), (255, 252, 250), (255, 255, 255)]

/-- La tabla dice la verdad: cada código es menor que 256 y es el paso de la caminata. -/
theorem tablaContra_ok : ∀ s < 256,
    (tablaContra.getD s (0, 0, 0)).1 < 256 ∧ (tablaContra.getD s (0, 0, 0)).2.1 < 256 ∧
    (tablaContra.getD s (0, 0, 0)).2.2 < 256 ∧
    List.ofFn (deBits 8 (tablaContra.getD s (0, 0, 0)).1) = List.ofFn (pasoCaminata (formulaContra 8) (deBits 8 s) (0 : Fin 3)) ∧
    List.ofFn (deBits 8 (tablaContra.getD s (0, 0, 0)).2.1) = List.ofFn (pasoCaminata (formulaContra 8) (deBits 8 s) (1 : Fin 3)) ∧
    List.ofFn (deBits 8 (tablaContra.getD s (0, 0, 0)).2.2) = List.ofFn (pasoCaminata (formulaContra 8) (deBits 8 s) (2 : Fin 3)) := by
  decide +kernel

/-- `aciertosRec` cuenta lo mismo que `aciertos`. -/
theorem aciertosRec_eq (F : List Clausula) (k : ℕ) :
    ∀ (t : ℕ) (α : Fin n → Bool), aciertosRec F k t α = aciertos F k t α
  | 0, α => by
    unfold aciertosRec aciertos
    by_cases h : solCNF F (List.ofFn α) = true
    · simp [h, caminata]
    · simp [h, caminata]
  | t + 1, α => by
    rw [aciertos_succ]
    simp only [aciertosRec]
    exact Finset.sum_congr rfl fun j _ => aciertosRec_eq F k t _

/-- Un paso de la cuenta sobre el vector de 256 valores: en la posición `s` se suman los valores de los tres
destinos. -/
def pasoVector (v : List ℕ) : List ℕ :=
  (List.range 256).map fun s =>
    let d := tablaContra.getD s (0, 0, 0)
    v.getD d.1 0 + v.getD d.2.1 0 + v.getD d.2.2 0

/-- El vector inicial: `1` en las soluciones, `0` en lo demás. -/
def vectorCero : List ℕ :=
  (List.range 256).map fun s => if solCNF (formulaContra 8) (List.ofFn (deBits 8 s)) = true then 1 else 0

/-- El vector a los `t` pasos. -/
def vectorContra (t : ℕ) : List ℕ := pasoVector^[t] vectorCero

private theorem getD_map_rango256 {f : ℕ → ℕ} {s : ℕ} (hs : s < 256) : ((List.range 256).map f).getD s 0 = f s := by
  simp [List.getD_eq_getElem?_getD, hs]

/-- **El vector memoizado cuenta los aciertos**: su entrada `s` es `aciertosRec` desde `deBits 8 s`. -/
theorem vectorContra_eq : ∀ (t s : ℕ), s < 256 →
    (vectorContra t).getD s 0 = aciertosRec (formulaContra 8) 3 t (deBits 8 s)
  | 0, s, hs => by
    simp only [vectorContra, Function.iterate_zero, id, vectorCero, aciertosRec]
    exact getD_map_rango256 hs
  | t + 1, s, hs => by
    have h := tablaContra_ok s hs
    obtain ⟨h0, h1, h2, e0, e1, e2⟩ := h
    have f0 := List.ofFn_injective e0
    have f1 := List.ofFn_injective e1
    have f2 := List.ofFn_injective e2
    have ih0 := vectorContra_eq t _ h0
    have ih1 := vectorContra_eq t _ h1
    have ih2 := vectorContra_eq t _ h2
    rw [f0] at ih0
    rw [f1] at ih1
    rw [f2] at ih2
    simp only [vectorContra, Function.iterate_succ_apply'] at ih0 ih1 ih2 ⊢
    rw [pasoVector, getD_map_rango256 hs]
    simp only [aciertosRec, Fin.sum_univ_three]
    rw [ih0, ih1, ih2]

/-- **La cuenta, hecha en el kernel**: desde `x₀` falso, 140 310 845 217 de las `3^24` sucesiones aciertan. -/
theorem vectorContra_valor : (vectorContra 24).getD 254 0 = 140310845217 := by
  decide +kernel

/-- **Los aciertos exactos** desde `alfaContra` con 24 pasos. -/
theorem aciertos_contra : aciertos (formulaContra 8) 3 24 alfaContra = 140310845217 := by
  rw [← aciertosRec_eq, alfaContra, ← vectorContra_eq 24 254 (by norm_num), vectorContra_valor]

/-! ## El contraejemplo -/

/-- Todas las cláusulas tienen exactamente tres literales. -/
theorem formulaContra_tres : ∀ c ∈ formulaContra 8, c.length = 3 := by
  decide +kernel

/-- Todo verdadero es solución. -/
theorem betaContra_sol : solCNF (formulaContra 8) (List.ofFn betaContra) = true := by
  decide +kernel

/-- `alfaContra` está a distancia 1 de la solución. -/
theorem hamming_contra : hammingDist alfaContra betaContra = 1 := by
  decide +kernel

/-- Desde `alfaContra`, la proporción con `24` pasos es `140310845217 / 3^24 ≈ 0,4968`. -/
theorem proporcion_contra :
    proporcion (formulaContra 8) 3 (3 * 8) alfaContra = 140310845217 / 3 ^ 24 := by
  rw [proporcion, aciertos_contra]
  norm_num

/-- **El contraejemplo**: una 3-CNF con 8 variables y solución `β`, y una `α` a distancia 1 de `β`, desde la que la
caminata de `3n = 24` pasos acierta con proporción menor que `1/2 = (1/2)^dist(α, β)`. -/
theorem schoening_sin_factor_contraejemplo :
    ∃ (F : List Clausula) (β α : Fin 8 → Bool), (∀ c ∈ F, c.length = 3) ∧ solCNF F (List.ofFn β) = true ∧
      hammingDist α β = 1 ∧ proporcion F 3 (3 * 8) α < (1 / 2) ^ hammingDist α β := by
  refine ⟨formulaContra 8, betaContra, alfaContra, formulaContra_tres, betaContra_sol, hamming_contra, ?_⟩
  rw [proporcion_contra, hamming_contra]
  norm_num

/-- **La hipótesis falla para esta fórmula**: no es cierto que desde toda `α` la proporción con `3n` pasos sea al
menos `(1/2)^dist(α, β)`. -/
theorem schoening_sin_factor_falla :
    ¬ ∀ α : Fin 8 → Bool, (1 / 2 : ℝ) ^ hammingDist α betaContra ≤ proporcion (formulaContra 8) 3 (3 * 8) α := by
  intro h
  have := h alfaContra
  rw [proporcion_contra, hamming_contra] at this
  norm_num at this

/-- **El lema 1 de Moser–Scheder sin el factor polinomial es falso**, enunciado en general: no vale que, para toda
3-CNF `F` con solución `β`, desde toda `α` la caminata de `3n` pasos acierte con proporción `≥ (1/2)^dist(α, β)`.
Falla ya con `n = 8`. -/
theorem schoening_sin_factor_falso :
    ¬ ∀ (F : List Clausula) (β : Fin 8 → Bool), (∀ c ∈ F, c.length ≤ 3) → solCNF F (List.ofFn β) = true →
      ∀ α : Fin 8 → Bool, (1 / 2 : ℝ) ^ hammingDist α β ≤ proporcion F 3 (3 * 8) α := by
  intro h
  exact schoening_sin_factor_falla
    (h _ _ (fun c hc => (formulaContra_tres c hc).le) betaContra_sol)

end Tiempo
end Sagitta.Map
