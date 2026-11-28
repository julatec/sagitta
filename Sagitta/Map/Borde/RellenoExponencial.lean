import Sagitta.Map.Borde.RellenoReloj
import CslibFrontier.Computability.Complexity.Classes.Hierarchy
import CslibFrontier.Computability.Complexity.Classes.EXP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# El relleno exponencial: lo difícil sí se «destruye» si se cambia la unidad

La «primera ley» del libro Sagitta dice: **lo difícil no se crea ni se destruye, solo se traslada**. En
`RellenoReloj.lean` se probó la mitad que vale: con relleno **polinomial**, rellenar es una equivalencia polinomial y la
pertenencia a P no cambia (`relleno_equivalente`, `relleno_P_iff`, `relleno_intermedio`), y en el modelo de costo
aditivo, el trabajo por instancia es el mismo más la guardia (`trabajo_no_se_destruye`). Acá va la otra mitad, la que
pone el borde de la ley: con relleno **exponencial**, y midiendo por el largo de la entrada, la ley **falla**, y falla
en las máquinas de cslib-frontier, no en un modelo de costo.

## El contraejemplo

* `A = diagonalL = {x | diagonal x = true}`, la diagonal de la jerarquía de tiempo de cslib-frontier
  (`Classes/Hierarchy.lean`). `A ∉ P` es `diagonal_notMem_P`; `A ∈ EXP` es `setOf_diagonal_mem_EXP`.
* `relleno expo A`, con `expo n = 2^n` y el `relleno` de `RellenoReloj.lean`: las palabras
  `y = frame x ++ 1^(2^|x|)` con `x ∈ A` (largo exacto `2|x| + 1 + 2^|x|`, `length_rellenar_expo`).
* La máquina (`decisor`, `computableInO_decisor`): primero una **guardia barata**, `|unframe y| ≤ log₂ |y|`
  (`computableInO_guarda`: desenmarcar con `ComputableInO.unframe`, los dos largos en binario con `lengthNat`, y el
  logaritmo binario `binary_log_two` vuelto a binario con `unary_to_binary`; tiempo lineal). Si no pasa, rechaza: una
  palabra rellenada siempre la pasa (`guarda_rellenar`). Si pasa, `2^|x| ≤ |y| + 1` (`pow_le_of_guarda`) y recién
  entonces escribe el relleno (`unary_two_pow`, `computableInO_rellenar`), lo compara con `y` (`eqWords`,
  `computableInO_esRelleno`) y corre `diagonal x`, que cuesta `2^(4|x|) = (2^|x|)^4 ≤ (|y| + 1)^4`
  (`computableInO_diagonal`, `cotas_de_guarda`). Es la idea de `Padding/Translation.lean` de cslib-frontier
  (`DTIME_comp_subset_of_subset`: cobrar la computación lenta solo en las entradas que alcanzan para pagarla), con
  otra guardia: la de allá calcula `G` en binario y por eso solo admite rellenos cuasi-polinomiales; esta compara
  contra `log₂ |y|`, que sí se calcula barato con un relleno exponencial.
* Resultado: `diagonalRellena_mem_P` y **`existe_dificil_con_relleno_facil`**:
  `∃ A, A ∉ P encBits ∧ relleno expo A ∈ P encBits`.

## Las dos caras, en un solo enunciado

`PrimeraLey g` es la ley medida por clases: para todo `L ≠ Σ*`, `L ∈ P ↔ relleno g L ∈ P`.

* **Con `g` polinomial (en unario), vale**: `primeraLey_de_polinomial`, que es `relleno_P_iff` de `RellenoReloj.lean`
  (las dos reducciones de Karp, en otro archivo pero en la misma `P` de cslib-frontier).
* **Con `g = 2^n`, falla**: `no_primeraLey_expo`, con la diagonal como testigo.
* No hay contradicción: `expo_no_polinomial` (`2^n` no es polinomial en unario) sale como corolario, y
  `no_reduce_a_relleno_expo` dice que rellenar exponencialmente no es una reducción polinomial.

## Lo que el archivo deja claro

El **trabajo absoluto** por instancia no cambia: sobre `rellenar expo x` el decisor contesta `diagonal x`
(`decisor_rellenar`) y corre la diagonal entera, con sus `2^(4|x|)` pasos; en el modelo de costo aditivo eso es
`trabajo_no_se_destruye` de `RellenoReloj.lean`. Lo que cambia es la **unidad de medida**: los mismos pasos, divididos
por un largo exponencialmente mayor, son polinomiales. La CLASE cambia aunque el trabajo no. Entonces la «primera ley»
vale en dos lecturas y solo en ellas: **con relleno polinomial** (la clase se conserva) o **midiendo trabajo absoluto**
(la cuenta de pasos se conserva). Medida por clases con relleno exponencial, lo difícil se «destruye»: no porque
desaparezca el trabajo, sino porque la vara con que se mide se estiró.

## Lo probado y lo abierto

**Probado** (sin `sorry` ni axiomas nuevos; `#print axioms` en `Axiomas.lean`): todo lo de arriba, incluida la cota de
la máquina con guardia en las máquinas multicinta de cslib-frontier (no quedó ninguna hipótesis con nombre).

**No probado**:

* Una **cota inferior** de tiempo para el decisor sobre las palabras rellenadas. «El trabajo absoluto no cambia» se
  prueba aquí como «contesta lo mismo y corre la misma diagonal» (`decisor_rellenar`) más la cota superior; que ninguna
  máquina pueda hacerlo más rápido en esas palabras no se enuncia. En el modelo de costo de `RellenoReloj.lean`, el
  costo es un dato y la igualdad sí es exacta.
* La versión con espacio, o con clases de tiempo intermedias (`DTIME` de cada `g`): solo se trata P.

## Antecedentes

El argumento de relleno y traslación suele atribuirse a Hartmanis y Stearns (Trans. AMS 117, 1965) en la jerarquía de
tiempo, y Book (J. Comput. System Sci. 9, 1974, «Comparing complexity classes») lo usó para comparar clases por
relleno. **Ninguno de los dos artículos se leyó para este archivo**: las referencias se dan como contexto, sin afirmar
qué lema exacto aparece en cada uno; la de Hartmanis–Stearns está en la bibliografía de Sagitta (verificada en
Crossref, ver `RellenoReloj.lean`), la de Book no se verificó. La forma con máquinas que se reusa es la de cslib-frontier
(`Padding/Translation.lean`, que cita a Fortnow y Santhanam, §3.3, Lema 5) y la diagonal de `Classes/Hierarchy.lean`
(Arora y Barak, Teorema 3.1).
-/

namespace Sagitta.Map.Borde.RellenoExponencial

open Turing.MultiTapeTM Cslib.Complexity
open Sagitta.Map.Borde.RellenoReloj (relleno rellenar unframe_rellenar length_rellenar largoRelleno)

/-! ## 1. La diagonal rellenada y la máquina con guardia -/

/-- El problema difícil: la diagonal de la jerarquía de tiempo de cslib-frontier. -/
def diagonalL : Set (List Bool) := {x | diagonal x = true}

/-- El relleno exponencial: `g(n) = 2^n` unos después del marco. -/
def expo (n : ℕ) : ℕ := 2 ^ n

/-- La diagonal rellenada exponencialmente, con el `relleno` de `RellenoReloj.lean`. -/
def diagonalRellena : Set (List Bool) := relleno expo diagonalL

/-- La guardia barata: `|unframe y| ≤ log₂ |y|`. -/
def guarda (y : List Bool) : Bool := decide ((unframe y).length ≤ Nat.log 2 y.length)

/-- El decisor de la diagonal rellenada. -/
def decisor (y : List Bool) : Bool :=
  if guarda y then (if decide (y = rellenar expo (unframe y)) then diagonal (unframe y) else false)
  else false

theorem guarda_rellenar (x : List Bool) : guarda (rellenar expo x) = true := by
  simp only [guarda, unframe_rellenar, length_rellenar, largoRelleno, decide_eq_true_eq]
  exact Nat.le_log_of_pow_le (by norm_num) (by unfold expo; omega)

theorem pow_le_of_guarda {y : List Bool} (h : guarda y = true) :
    2 ^ (unframe y).length ≤ y.length + 1 := by
  simp only [guarda, decide_eq_true_eq] at h
  rcases Nat.eq_zero_or_pos y.length with h0 | hpos
  · rw [h0] at h ⊢
    simp at h
    simp [h]
  · calc 2 ^ (unframe y).length ≤ 2 ^ Nat.log 2 y.length := Nat.pow_le_pow_right (by norm_num) h
      _ ≤ y.length := Nat.pow_log_le_self 2 (by omega)
      _ ≤ _ := Nat.le_succ _

theorem decisor_iff (y : List Bool) : decisor y = true ↔ y ∈ diagonalRellena := by
  unfold decisor diagonalRellena relleno diagonalL
  by_cases hg : guarda y = true
  · by_cases he : y = rellenar expo (unframe y)
    · have hd : decide (y = rellenar expo (unframe y)) = true := decide_eq_true he
      simp only [hg, hd, ite_true, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩
    · simp [hg, he]
  · have : ¬ y = rellenar expo (unframe y) := fun he => hg (he ▸ guarda_rellenar _)
    simp [hg, this]

theorem computableInO_guarda :
    ComputableInO guarda encBits encBool (fun y => y.length) fun y => y.length := by
  have hp : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ Nat.log 2 p.2))
      (encPair encNat encNat) encBool :=
    ComputableInPolyTime.binary_le' (.fst encNat encNat)
      (ComputableInPolyTime.unary_to_binary.comp
        (ComputableInPolyTime.binary_log_two.comp (.snd encNat encNat)))
  have h := hp.natPair_inO.comp
    ((ComputableInO.lengthNat.comp ComputableInO.unframe).prod ComputableInO.lengthNat)
  refine h.mono 6 (fun y => ?_) fun y => ?_
  all_goals
    have := length_unframe_le y
    simp only [Function.comp_apply]
    omega

/-- Escribir el relleno exponencial de la palabra enmarcada: desenmarcar, volver a enmarcar, y escribir `2^|x|` unos
(`unary_two_pow`, que dobla `|x|` veces). -/
theorem computableInO_rellenar :
    ComputableInO (fun y => rellenar expo (unframe y)) encBits encBits
      (fun y => y.length + ((unframe y).length + 1) * 2 ^ (unframe y).length)
      (fun y => y.length + 2 ^ (unframe y).length) := by
  have hf : ComputableInO (fun y => unframe y) encBits (encFramed encBits)
      (fun y => y.length) fun y => y.length := by
    have h := (ComputableInO.of_linear
      (.of_frame (f := id) (encIn := encBits) (encMid := encFramed encBits) fun _ => rfl)).comp
      ComputableInO.unframe
    refine h.mono 2 (fun y => ?_) fun y => ?_
    all_goals
      have := length_unframe_le y
      simp only [encBits_apply]
      omega
  have hp := ComputableInO.unary_two_pow.comp (ComputableInO.lengthUnary.comp ComputableInO.unframe)
  have h := hf.append hp (g := fun y => rellenar expo (unframe y)) (encOut := encBits) fun y => by
    simp [rellenar, expo, encFramed]
  refine h.mono 3 (fun y => ?_) fun y => ?_
  all_goals
    have := length_unframe_le y
    simp only [Function.comp_apply]
    nlinarith [Nat.one_le_two_pow (n := (unframe y).length)]

/-- La comparación `y = rellenar expo (unframe y)`, con la palabra escrita y comparada (`eqWords`, cuadrática). -/
theorem computableInO_esRelleno :
    ComputableInO (fun y => decide (y = rellenar expo (unframe y))) encBits encBool
      (fun y => y.length + ((unframe y).length + 1) * 2 ^ (unframe y).length +
        ((2 * y.length + 1 + (2 * (unframe y).length + 1 + 2 ^ (unframe y).length)) + 1) ^ 2)
      (fun y => y.length + 2 ^ (unframe y).length +
        ((2 * y.length + 1 + (2 * (unframe y).length + 1 + 2 ^ (unframe y).length)) + 1) ^ 2) := by
  have hid : ComputableInO (fun y : List Bool => y) encBits encBits (fun y => y.length) fun y => y.length :=
    ComputableInO.of_eq fun _ => rfl
  have h := ComputableInDegree.eqWords.inO.comp (hid.prod computableInO_rellenar)
  refine h.mono 2 (fun y => ?_) fun y => ?_
  all_goals
    have hl := length_rellenar expo (unframe y)
    simp only [length_encPair, encBits_apply, largoRelleno, expo] at hl ⊢
    rw [hl]
    generalize ((unframe y).length + 1) * 2 ^ (unframe y).length = a
    generalize (2 * y.length + 1 + (2 * (unframe y).length + 1 + 2 ^ (unframe y).length) + 1) ^ 2 = b
    generalize 2 ^ (unframe y).length = P
    omega

/-- Las cuentas de la máquina con guardia: si la guardia pasó, cada término cabe en `(|y| + 1)^4`. -/
theorem cotas_de_guarda {y : List Bool} (hg : guarda y = true) :
    ((unframe y).length + 1) * 2 ^ (unframe y).length ≤ (y.length + 1) ^ 4 ∧
    (2 * y.length + 1 + (2 * (unframe y).length + 1 + 2 ^ (unframe y).length) + 1) ^ 2 ≤
      25 * (y.length + 1) ^ 4 ∧
    2 ^ (4 * (unframe y).length) ≤ (y.length + 1) ^ 4 ∧
    2 ^ (2 * (unframe y).length) ≤ (y.length + 1) ^ 4 ∧
    2 ^ (unframe y).length ≤ (y.length + 1) ^ 4 ∧
    y.length ≤ (y.length + 1) ^ 4 := by
  have hm := length_unframe_le y
  have hP := pow_le_of_guarda hg
  have h24 : (y.length + 1) ^ 2 ≤ (y.length + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h14 : y.length + 1 ≤ (y.length + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  refine ⟨?_, ?_, ?_, ?_, by omega, by omega⟩
  · calc ((unframe y).length + 1) * 2 ^ (unframe y).length ≤ (y.length + 1) * (y.length + 1) :=
          Nat.mul_le_mul (by omega) hP
      _ = (y.length + 1) ^ 2 := (sq _).symm
      _ ≤ _ := h24
  · have h5 : 2 * y.length + 1 + (2 * (unframe y).length + 1 + 2 ^ (unframe y).length) + 1 ≤
        5 * (y.length + 1) := by omega
    calc _ ≤ (5 * (y.length + 1)) ^ 2 := Nat.pow_le_pow_left h5 2
      _ = 25 * (y.length + 1) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h24
  · rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hP 4
  · rw [mul_comm, pow_mul]
    exact (Nat.pow_le_pow_left hP 2).trans h24

/-- **La máquina con guardia**: decide la diagonal rellenada en tiempo y espacio `O((|y| + 1)^4)`. Primero la guardia
(lineal); si no pasa, rechaza sin mirar más. Si pasa, `2^|x| ≤ |y| + 1`, y entonces escribir el relleno, compararlo y
correr la diagonal (`2^(4|x|)` pasos, `computableInO_diagonal`) cuesta a lo sumo una constante por `(|y| + 1)^4`. -/
theorem computableInO_decisor :
    ComputableInO decisor encBits encBool (fun y => (y.length + 1) ^ 4) fun y => (y.length + 1) ^ 4 := by
  have hdiag := computableInO_diagonal.comp ComputableInO.unframe
  have hin := computableInO_esRelleno.ite hdiag
    (ComputableInO.const (encIn := encBits) (encMid := encBool) false)
  have hdec := computableInO_guarda.ite hin
    (ComputableInO.const (encIn := encBits) (encMid := encBool) false)
  refine hdec.mono 30 (fun y => ?_) fun y => ?_
  all_goals
    simp only [encBits_apply]
    have h14 : y.length + 1 ≤ (y.length + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
    split_ifs with hg he
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cotas_de_guarda hg
      generalize ((unframe y).length + 1) * 2 ^ (unframe y).length = a at *
      generalize (2 * y.length + 1 + (2 * (unframe y).length + 1 + 2 ^ (unframe y).length) + 1) ^ 2 = b at *
      generalize 2 ^ (4 * (unframe y).length) = c at *
      generalize 2 ^ (2 * (unframe y).length) = d at *
      generalize 2 ^ (unframe y).length = e at *
      generalize (y.length + 1) ^ 4 = q at *
      omega
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cotas_de_guarda hg
      generalize ((unframe y).length + 1) * 2 ^ (unframe y).length = a at *
      generalize (2 * y.length + 1 + (2 * (unframe y).length + 1 + 2 ^ (unframe y).length) + 1) ^ 2 = b at *
      generalize 2 ^ (4 * (unframe y).length) = c at *
      generalize 2 ^ (2 * (unframe y).length) = d at *
      generalize 2 ^ (unframe y).length = e at *
      generalize (y.length + 1) ^ 4 = q at *
      omega
    · generalize (y.length + 1) ^ 4 = q at *
      omega

/-- **La diagonal rellenada exponencialmente está en P**, en las máquinas de cslib-frontier. -/
theorem diagonalRellena_mem_P : diagonalRellena ∈ Cslib.Complexity.P encBits :=
  ⟨decisor, computableInO_decisor.computableInPolyTime
      (PolyBounded.of_forall_le 1 4 fun y => by simp [encBits_apply])
      (PolyBounded.of_forall_le 1 4 fun y => by simp [encBits_apply]),
    fun y => (decisor_iff y).symm⟩

/-! ## 2. La cara difícil: la diagonal no está en P -/

/-- La diagonal no está en P (`diagonal_notMem_P` de cslib-frontier, la jerarquía de tiempo). -/
theorem diagonalL_notMem_P : diagonalL ∉ Cslib.Complexity.P encBits := diagonal_notMem_P

/-- La diagonal está en EXP (`setOf_diagonal_mem_EXP`): es difícil, pero no tanto. -/
theorem diagonalL_mem_EXP : diagonalL ∈ EXP encBits := setOf_diagonal_mem_EXP

/-- Hay palabras fuera de la diagonal (si no, sería `Σ*`, que está en P). -/
theorem exists_notMem_diagonalL : ∃ x₀, x₀ ∉ diagonalL := by
  by_contra h
  push Not at h
  exact diagonalL_notMem_P (Set.eq_univ_of_forall h ▸ univ_mem_P)

/-! ## 3. El contraejemplo -/

/-- **El contraejemplo a la «primera ley» medida por largo de entrada.** Hay un problema fuera de P cuyo relleno
exponencial (el `relleno` de `RellenoReloj.lean`, con `g(n) = 2^n`) está en P. Todo en las máquinas de cslib-frontier. -/
theorem existe_dificil_con_relleno_facil :
    ∃ A : Set (List Bool), A ∉ Cslib.Complexity.P encBits ∧ relleno expo A ∈ Cslib.Complexity.P encBits :=
  ⟨diagonalL, diagonalL_notMem_P, diagonalRellena_mem_P⟩

/-- **El trabajo por instancia no cambia**: en una palabra rellenada, el decisor contesta exactamente lo que contesta
la diagonal sobre la palabra original; la máquina corre `diagonal x` entera (los `2^(4|x|)` pasos de
`computableInO_diagonal`), más la guardia y la comparación. Lo que cambia es contra qué largo se mide. -/
theorem decisor_rellenar (x : List Bool) : decisor (rellenar expo x) = diagonal x := by
  simp [decisor, guarda_rellenar, unframe_rellenar]

/-- El largo de la palabra rellenada: `|x|` se paga con `2|x| + 1 + 2^|x|` bits. -/
theorem length_rellenar_expo (x : List Bool) :
    (rellenar expo x).length = 2 * x.length + 1 + 2 ^ x.length :=
  length_rellenar expo x

/-- El relleno exponencial **no es** una reducción polinomial de la diagonal a su relleno: si lo fuera, la diagonal
estaría en P. -/
theorem no_reduce_a_relleno_expo :
    ¬ Sagitta.Map.Borde.TresInterruptores.Reduce diagonalL diagonalRellena := fun h =>
  diagonalL_notMem_P (h.mem_P diagonalRellena_mem_P)

/-! ## 4. Las dos caras: cuándo vale la «primera ley» -/

/-- **La «primera ley» para un relleno `g`**, medida por clases: rellenar con `g` no cambia la pertenencia a P, para
todo problema que no sea `Σ*` (la excepción de `relleno_univ_no_reduce`). -/
def PrimeraLey (g : ℕ → ℕ) : Prop :=
  ∀ L : Set (List Bool), (∃ x₀, x₀ ∉ L) →
    (L ∈ Cslib.Complexity.P encBits ↔ relleno g L ∈ Cslib.Complexity.P encBits)

/-- **Con relleno polinomial, la ley vale** (`relleno_P_iff` de `RellenoReloj.lean`: las dos reducciones de Karp). -/
theorem primeraLey_de_polinomial {g : ℕ → ℕ} (hg : ComputableInPolyTime g encUnary encUnary) : PrimeraLey g :=
  fun _ hL => Sagitta.Map.Borde.RellenoReloj.relleno_P_iff hg hL

/-- **Con relleno exponencial, la ley falla**: la diagonal es el contraejemplo. -/
theorem no_primeraLey_expo : ¬ PrimeraLey expo := fun h =>
  diagonalL_notMem_P ((h diagonalL exists_notMem_diagonalL).2 diagonalRellena_mem_P)

/-- Como consecuencia, `2^n` no se calcula en tiempo polinomial en unario (lo que ya se sabía por el largo de la
salida); el contraejemplo no contradice `relleno_P_iff`, cae fuera de su hipótesis. -/
theorem expo_no_polinomial : ¬ ComputableInPolyTime expo encUnary encUnary := fun hg =>
  no_primeraLey_expo (primeraLey_de_polinomial hg)

end Sagitta.Map.Borde.RellenoExponencial
