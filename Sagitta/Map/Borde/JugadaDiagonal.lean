import Sagitta.Map.Landau
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card

/-!
# La jugada diagonal: cabe en SAT, pero se normaliza

La idea de José (24 nov 2026): para la jugada que le falta al P-bombeo (`Sagitta/Map/Borde/PBombeo.lean`), usar un programa
que hable de sí mismo, como uno que se imprime al revés (`ejemplos/quine-al-reves/`). Con autorreferencia, una
instancia puede hablar de sus rivales: «encontrá una `x` que ningún programa corto y rápido, corrido sobre mí,
produce». Este archivo prueba, en un modelo abstracto, las tres cosas que pasan con esa jugada.

## El modelo

Los rivales de un nivel `ℓ` son `2^ℓ` programas (`Fin (2 ^ ℓ)`). Lo único que importa de ellos es qué entregan sobre la
instancia: `sal : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool`, una palabra de `ℓ + 1` bits por rival. El verificador diagonal
acepta una `x` de `ℓ + 1` bits si ningún rival la entregó (`Diagonal`). No se modelan las máquinas, el teorema de
recursión ni Cook–Levin: se modela lo que la cuenta necesita de ellos.

## Lo que se prueba

1. **La jugada existe para su propio verificador** (`diagonal_existe`, `ningun_rival_acierta`): siempre hay una `x`
   que el verificador diagonal acepta (hay `2^(ℓ+1)` palabras y solo `2^ℓ` rivales: palomar), y ninguna salida de un
   rival es aceptada. La diagonal le gana a todos.
2. **El verificador tiene que leer a todos los rivales** (`verificador_lee_todo`): si un verificador correcto solo
   mira las salidas de los rivales de un conjunto `S`, entonces `S` son todos. Su costo es al menos `2^ℓ`
   (`costo_verificador`), y crece con el nivel: no hay un polinomio fijo en el largo de la palabra (`ℓ + 1`) que lo
   acote. Es la razón de que la familia diagonal se salga de NP: la autorreferencia hace que la instancia conozca a sus
   rivales; NP le prohíbe al verificador conocerlos.
3. **La cuenta de Cook–Levin: la victoria se normaliza** (`profundidad_normalizada`). Si la fórmula que codifica al
   verificador mide al menos lo que cuesta correrlo (`2^ℓ · t ≤ N`: Cook–Levin escribe la corrida entera), entonces la
   profundidad de los rivales vencidos, `ℓ + log₂ t` (largo más logaritmo del tiempo: su `kt`), no pasa de `log₂ N`.
   Medida contra el tamaño de su propia fórmula, la instancia diagonal solo le gana a profundidades `≤ 1 · log N`: la
   constante no crece con el nivel. Por eso la jugada, metida en SAT, no da `JugadaProfundidad` (que pide superar
   `c · log N` para toda `c`).

## Lo que NO se prueba

* Nada sobre máquinas concretas: ni el teorema de recursión (que en Mathlib está como punto fijo de códigos), ni
  Cook–Levin (que cslib-frontier tiene), ni que la cota `N ≥ 2^ℓ · t` sea la de una reducción particular. La hipótesis
  de la parte 3 es exactamente lo que Cook–Levin cumple en su versión más eficiente (casi lineal), salvo factores
  logarítmicos que solo cambian la constante.
* La salida conocida del callejón: si los rivales tienen poca memoria, simularlos cuesta menos que `t` (alternancia) y
  queda una victoria real pequeña (las cotas de tiempo y espacio para SAT de Fortnow y de Williams). No está aquí.
-/

namespace Sagitta.Map.Borde.JugadaDiagonal

variable {ℓ : ℕ}

/-- **El verificador diagonal**: acepta una palabra si ningún rival la entregó. -/
def Diagonal (sal : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) (x : Fin (ℓ + 1) → Bool) : Prop :=
  ∀ p, sal p ≠ x

instance (sal : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) (x : Fin (ℓ + 1) → Bool) : Decidable (Diagonal sal x) := by
  unfold Diagonal; infer_instance

/-! ## 1. La jugada existe para su propio verificador -/

/-- **La diagonal existe**: hay una palabra que ningún rival entregó (palomar: `2^(ℓ+1)` palabras, `2^ℓ` rivales). -/
theorem diagonal_existe (sal : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) : ∃ x, Diagonal sal x := by
  by_contra h
  simp only [Diagonal, not_exists, not_forall, not_not] at h
  have hsub : (Finset.univ : Finset (Fin (ℓ + 1) → Bool)) ⊆ Finset.univ.image sal := by
    intro x _
    obtain ⟨p, hp⟩ := h x
    exact Finset.mem_image.2 ⟨p, Finset.mem_univ _, hp⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.image sal).card ≤ 2 ^ ℓ := by
    calc (Finset.univ.image sal).card ≤ (Finset.univ : Finset (Fin (2 ^ ℓ))).card := Finset.card_image_le
      _ = 2 ^ ℓ := by simp
  have h3 : (Finset.univ : Finset (Fin (ℓ + 1) → Bool)).card = 2 ^ (ℓ + 1) := by simp
  have h4 : 2 ^ ℓ < 2 ^ (ℓ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- **Ningún rival acierta**: la salida de un rival nunca es aceptada por el verificador diagonal. -/
theorem ningun_rival_acierta (sal : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) (p : Fin (2 ^ ℓ)) :
    ¬ Diagonal sal (sal p) :=
  fun h => h p rfl

/-! ## 2. El verificador tiene que leer a todos los rivales -/

/-- Un verificador **solo mira** las salidas de los rivales de `S`: si dos asignaciones de salidas coinciden en `S`,
responde lo mismo. -/
def SoloMira (S : Finset (Fin (2 ^ ℓ)))
    (ver : (Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) → (Fin (ℓ + 1) → Bool) → Bool) : Prop :=
  ∀ sal sal' x, (∀ p ∈ S, sal p = sal' p) → ver sal x = ver sal' x

/-- **El verificador lee a todos**: si un verificador decide `Diagonal` para toda asignación de salidas y solo mira
los rivales de `S`, entonces `S` contiene a todos los rivales. -/
theorem verificador_lee_todo (S : Finset (Fin (2 ^ ℓ)))
    (ver : (Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) → (Fin (ℓ + 1) → Bool) → Bool)
    (hmira : SoloMira S ver) (hcorr : ∀ sal x, ver sal x = decide (Diagonal sal x)) :
    ∀ p, p ∈ S := by
  intro p
  by_contra hp
  let x : Fin (ℓ + 1) → Bool := fun _ => false
  let y : Fin (ℓ + 1) → Bool := fun _ => true
  have hxy : y ≠ x := fun h => by simpa [x, y] using congrFun h 0
  let sal1 : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool := fun _ => y
  let sal2 : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool := Function.update sal1 p x
  have hacuerdo : ∀ q ∈ S, sal1 q = sal2 q := by
    intro q hq
    have hqp : q ≠ p := fun h => hp (h ▸ hq)
    simp [sal2, Function.update_of_ne hqp]
  have h1 : Diagonal sal1 x := fun _ => hxy
  have h2 : ¬ Diagonal sal2 x := fun h => h p (by simp [sal2])
  have := hmira sal1 sal2 x hacuerdo
  rw [hcorr, hcorr] at this
  simp [h1, h2] at this

/-- **El costo del verificador** es al menos el número de rivales, `2^ℓ`: crece con el nivel. -/
theorem costo_verificador (S : Finset (Fin (2 ^ ℓ)))
    (ver : (Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) → (Fin (ℓ + 1) → Bool) → Bool)
    (hmira : SoloMira S ver) (hcorr : ∀ sal x, ver sal x = decide (Diagonal sal x)) :
    2 ^ ℓ ≤ S.card := by
  have hS : S = Finset.univ := Finset.eq_univ_of_forall (verificador_lee_todo S ver hmira hcorr)
  simp [hS]

/-- Ningún polinomio fijo en el largo de la palabra (`ℓ + 1`) acota ese costo: para todo `k`, desde algún nivel,
`2^ℓ > (ℓ + 1)^k` (con `pol_menor_dos_pow` de `Sagitta/Map/Landau.lean`). -/
theorem costo_no_polinomial (k : ℕ) : ∃ L, ∀ ℓ, L ≤ ℓ → (ℓ + 1) ^ k < 2 ^ ℓ := by
  obtain ⟨L, hL⟩ := Sagitta.Map.Tiempo.pol_menor_dos_pow 1 k
  exact ⟨L, fun ℓ hℓ => by simpa using hL ℓ hℓ⟩

/-! ## 3. La cuenta de Cook–Levin: la victoria se normaliza -/

/-- **La profundidad vencida no pasa de `log₂ N`.** Si la fórmula mide al menos lo que cuesta correr al verificador
(`2^ℓ` rivales, `t` pasos cada uno), la `kt` de los rivales vencidos (`ℓ + log₂ t`) es a lo sumo `log₂ N`. -/
theorem profundidad_normalizada {ℓ t N : ℕ} (ht : 0 < t) (hN : 2 ^ ℓ * t ≤ N) :
    ℓ + Nat.log 2 t ≤ Nat.log 2 N := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ (ℓ + Nat.log 2 t) = 2 ^ ℓ * 2 ^ Nat.log 2 t := pow_add _ _ _
    _ ≤ 2 ^ ℓ * t := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 ht.ne')
    _ ≤ N := hN

/-- **Por eso no da la jugada de profundidad para SAT**: para la constante `c = 2`, la profundidad vencida queda
estrictamente debajo de `2 · log₂ N` en cuanto `N ≥ 2`; ninguna instancia diagonal, medida contra su fórmula, supera
`c · log N` para `c ≥ 2`. -/
theorem no_supera_dos_log {ℓ t N : ℕ} (ht : 0 < t) (hN : 2 ^ ℓ * t ≤ N) (hN2 : 2 ≤ N) :
    ℓ + Nat.log 2 t < 2 * Nat.log 2 N := by
  have h := profundidad_normalizada ht hN
  have hpos : 0 < Nat.log 2 N := Nat.log_pos (by norm_num) hN2
  omega

/-! ## Controles -/

/-- La diagonal no es trivial: con un solo rival (`ℓ = 0`) que entrega `[true]`, la palabra aceptada es `[false]` y
`[true]` no lo es. -/
example : Diagonal (ℓ := 0) (fun _ _ => true) (fun _ => false) ∧
    ¬ Diagonal (ℓ := 0) (fun _ _ => true) (fun _ => true) := by
  refine ⟨fun p h => ?_, fun h => h 0 rfl⟩
  simpa using congrFun h 0

/-- El costo crece de verdad: con `ℓ = 3`, un verificador correcto mira al menos 8 rivales. -/
example (S : Finset (Fin (2 ^ 3)))
    (ver : (Fin (2 ^ 3) → Fin (3 + 1) → Bool) → (Fin (3 + 1) → Bool) → Bool)
    (hmira : SoloMira S ver) (hcorr : ∀ sal x, ver sal x = decide (Diagonal sal x)) : 8 ≤ S.card :=
  costo_verificador S ver hmira hcorr

/-- La cuenta de Cook–Levin con números: 16 rivales (`ℓ = 4`) de 8 pasos dan una fórmula de al menos 128 y una
profundidad vencida de `4 + 3 = 7 = log₂ 128`: justo `1 · log N`. -/
example : 4 + Nat.log 2 8 ≤ Nat.log 2 128 := profundidad_normalizada (by norm_num) (by norm_num)

/- Mutante probado (24 nov 2026, fuera del repositorio): en `profundidad_normalizada`, cambiar la hipótesis de Cook–Levin
`2 ^ ℓ * t ≤ N` por `2 ^ ℓ ≤ N` (la fórmula mide solo el número de rivales, no el costo de simularlos) hace fallar la
prueba: el tiempo de los rivales ya no queda pagado en el tamaño de la fórmula. Es justamente la salida conocida
(simular más barato que `t`), que aquí no se modela. -/

end Sagitta.Map.Borde.JugadaDiagonal
