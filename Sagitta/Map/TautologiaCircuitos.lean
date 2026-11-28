import Sagitta.Map.EspejoEF
import Sagitta.Map.Circuitos

/-!
# La tautología de cota inferior para circuitos

Una prueba de P ≠ NP es **un solo objeto**, de tamaño constante. Pero si se la hace dentro de `S¹₂` y se la baja al
espejo proposicional (`EspejoEF.lean`), lo que aparece es una **familia** de tautologías, una por cada `n`, y cada una
habla de una tabla de verdad entera, que tiene `2ⁿ` filas. Este archivo formaliza esa familia.

## Qué se prueba

* **La fórmula `Calcula(f, s, n)`** (`Calcula`). Sus variables (`vOp`, `vA`, `vB`, `vS`, `vV`) describen un circuito de
  `s` compuertas sobre `n` entradas —el tipo de cada compuerta en dos bits (`codOp`), sus dos cables y el de salida en
  registros de `n + s` bits— y, por cada una de las `2ⁿ` entradas, el valor de cada compuerta. Dice tres cosas:
  la descripción es válida (cada compuerta `k` lee cables `< n + k`: no hay ciclos; la salida existe; `validez`), los
  valores se propagan bien en las `2ⁿ` entradas (`propagacion`) y la salida coincide con `f` en todas (`salida`).
  Las entradas no son variables: en la fila `x` son las constantes de los bits de `x` (`valF`). Leer «el cable cuyo
  número está en el registro» es una disyunción sobre los `n + s` cables con el comparador `eqF` de `EspejoEF`.
* **Corrección** (`satisfacible_calcula_iff`, `satisfacible_calcula_iff_hasta`): `Calcula(f, s, n)` es satisfacible si
  y solo si algún circuito bien formado de `s` (o de `≤ s`, rellenando) compuertas calcula `f`. Los circuitos son los de
  `Shannon.lean` (el único modelo del repo) con la condición `BienFormado`; la semántica pasa por `Consistente`: en un
  circuito bien formado hay una sola asignación consistente de los cables, y es la que calcula `cables`.
* **La tautología** `CotaInferior(f, s, n) := ¬ Calcula(f, s, n)` (`tautologia_cotaInferior_iff`): es tautología si y
  solo si ningún circuito bien formado de `≤ s` compuertas calcula `f`.
* **Su tamaño**: `2ⁿ ≤ tam ≤ 800 · 2ⁿ · (n + s + 1)³` (`dos_pow_le_tam`, `tam_cotaInferior`). Polinomial en el tamaño
  `N = 2ⁿ` de la tabla de verdad y en `s`; exponencial en `n`. El `2ⁿ` no se puede quitar: ninguna cota
  `c · (n + s + 1)ᵈ` sirve (`tam_no_polinomial`).
* **Controles**: el «y» de dos bits con una compuerta hace satisfacible `Calcula` (también evaluando la fórmula misma con
  `decide +kernel`, `calcula_y2_en_asig`), así que `CotaInferior(y, 1, 2)` no es tautología; `CotaInferior(xor, 0, 2)`
  sí lo es (sin compuertas solo hay proyecciones), y `CotaInferior(xor, 4, 2)` no.
* **La conexión con P/poly** (`fuera_de_PsobrePoly`): si para todo polinomio `p` hay un `n ≥ 1` donde
  `CotaInferior(L|ₙ, p(n) + 2, n)` es tautología, entonces `L ∉ P/poly` (`Circuitos.lean`). El `+ 2` viene de
  `bienFormar`: un circuito cualquiera del modelo de Shannon (donde leer un cable adelantado da `false`) se vuelve bien
  formado con dos compuertas más, que fabrican la constante `false`.

## La lectura

Tomá `f` = la función característica de SAT restringida a `n` bits y `s = n^k`. Una prueba de «SAT no tiene circuitos
de tamaño `n^k`» hecha en `S¹₂` daría, por la traducción de Cook (de memoria, ver `EspejoEF.lean`), pruebas de tamaño
polinomial **en el tamaño de la fórmula** en Frege extendido para la familia `CotaInferior(SAT|ₙ, n^k, n)`. Ese tamaño ya
es `2ⁿ · poly(n)`: la prueba de P ≠ NP es una constante, pero sus instancias son estas tautologías, y para probarlas hay
que razonar sobre tablas de verdad enteras, objetos exponenciales en `n`. Es la forma proposicional del problema
«`P ≠ NP` es demostrable en aritmética acotada».

## Las barreras (de memoria, sin cotejar con las fuentes)

* **Razborov y Rudich (1994–1997), pruebas naturales**: una prueba de cota inferior que sea «natural» —que use una
  propiedad de las tablas de verdad que sea constructiva (decidible en tiempo polinomial en `2ⁿ`) y amplia (la cumple una
  fracción grande de las funciones)— rompería los generadores pseudoaleatorios que se creen seguros. Casi todas las cotas
  inferiores conocidas son naturales.
* **Razborov (1995), la versión lógica**: si existen generadores pseudoaleatorios suficientemente fuertes, la teoría
  `S²₂(α)` —y con ella `S¹₂(α)`— no demuestra cotas inferiores superpolinomiales para circuitos. La versión proposicional
  es que, bajo supuestos criptográficos, las tautologías de esta familia (con `f` dura y `s` polinomial) no tienen pruebas
  cortas en el sistema que hace de espejo de la teoría; para sistemas débiles (Resolución y parecidos) hay resultados sin
  supuestos, de Razborov, Krajíček y otros, y Pich y Santhanam siguieron la línea. Todo esto, de memoria: qué sistema y
  qué supuesto exactos corresponden a cada enunciado hay que cotejarlo con las fuentes.

## Lo que NO se prueba

* **Nada sobre la dificultad** de estas tautologías en ningún sistema de pruebas: ni cotas inferiores ni superiores al
  tamaño de sus pruebas, en Frege, EF ni ningún otro. Razborov, Razborov–Rudich y lo de arriba son contexto de memoria.
* **Nada sobre P contra NP**: no se prueba que alguna `CotaInferior(SAT|ₙ, n^k, n)` sea tautología. `fuera_de_PsobrePoly`
  solo traduce la pregunta.
* La equivalencia es con circuitos **bien formados** del modelo de Shannon; con el modelo sin esa condición, la familia
  correcta es la de `s + 2` (`bienFormar`), y no se prueba la vuelta exacta.
-/

namespace Sagitta.Map
namespace Extraccion
namespace TautologiaCircuitos

open EspejoEF Shannon

variable {n s : ℕ}

/-! ## 1. Circuitos bien formados y su semántica -/

/-- Un circuito **bien formado**: cada compuerta lee solo entradas o compuertas anteriores (no hay ciclos ni
lecturas adelantadas). -/
def BienFormado (C : Circuito n s) : Prop :=
  ∀ k : Fin s, ((C.1 k).2.1 : ℕ) < n + k ∧ ((C.1 k).2.2 : ℕ) < n + k

instance (C : Circuito n s) : Decidable (BienFormado C) := by unfold BienFormado; infer_instance

/-- Unos valores `v` de los cables son **consistentes** con el circuito en la entrada `x`: las entradas valen lo que
dice `x` y cada compuerta vale su operación aplicada a los cables que lee. -/
def Consistente (C : Circuito n s) (x : Fin n → Bool) (v : Fin (n + s) → Bool) : Prop :=
  (∀ w : Fin (n + s), (h : (w : ℕ) < n) → v w = x ⟨w, h⟩) ∧
  ∀ k : Fin s, v (cableDe k) = (C.1 k).1.aplica (v (C.1 k).2.1) (v (C.1 k).2.2)

/-- En un circuito bien formado, lo que lee la compuerta `k` es el valor final del cable. -/
theorem lee_bienFormado {C : Circuito n s} (x : Fin n → Bool) {k : ℕ} {a : Fin (n + s)} (h : (a : ℕ) < n + k) :
    lee C x k a = cables C x a := by
  simp [lee, h]

/-- Los cables de un circuito bien formado son consistentes. -/
theorem cables_consistente {C : Circuito n s} (hC : BienFormado C) (x : Fin n → Bool) :
    Consistente C x (cables C x) := by
  refine ⟨fun w h => cables_entrada C x w h, fun k => ?_⟩
  rw [cables_compuerta, lee_bienFormado x (hC k).1, lee_bienFormado x (hC k).2]

/-- **Unicidad.** En un circuito bien formado hay una sola asignación consistente de los cables. -/
theorem consistente_unico {C : Circuito n s} (hC : BienFormado C) {x : Fin n → Bool} {v v' : Fin (n + s) → Bool}
    (hv : Consistente C x v) (hv' : Consistente C x v') : v = v' := by
  funext ⟨w, hw⟩
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h : w < n
    · rw [hv.1 ⟨w, hw⟩ h, hv'.1 ⟨w, hw⟩ h]
    · have hk : w - n < s := by omega
      have e : (⟨w, hw⟩ : Fin (n + s)) = cableDe ⟨w - n, hk⟩ := by
        ext; simp only [cableDe]; omega
      rw [e, hv.2, hv'.2]
      have h1 := (hC ⟨w - n, hk⟩).1
      have h2 := (hC ⟨w - n, hk⟩).2
      simp only at h1 h2
      have i1 := ih _ (by omega) (C.1 ⟨w - n, hk⟩).2.1.isLt
      have i2 := ih _ (by omega) (C.1 ⟨w - n, hk⟩).2.2.isLt
      simp only [Fin.eta] at i1 i2
      rw [i1, i2]

theorem cables_de_consistente {C : Circuito n s} (hC : BienFormado C) {x : Fin n → Bool}
    {v : Fin (n + s) → Bool} (hv : Consistente C x v) : cables C x = v :=
  consistente_unico hC (cables_consistente hC x) hv

/-! ## 2. Las variables proposicionales

Cinco familias, separadas por la etiqueta del par de Cantor (`Nat.pair`), así que nunca se pisan:
* `vOp k i`: los dos bits del tipo de la compuerta `k`;
* `vA k j`, `vB k j`: el bit `j` del primer y del segundo cable que lee la compuerta `k`;
* `vS j`: el bit `j` del cable de salida;
* `vV x k`: el valor de la compuerta `k` en la entrada número `x` (una por cada una de las `2ⁿ` entradas). -/

def vOp (k i : ℕ) : ℕ := Nat.pair 0 (Nat.pair k i)
def vA (k j : ℕ) : ℕ := Nat.pair 1 (Nat.pair k j)
def vB (k j : ℕ) : ℕ := Nat.pair 2 (Nat.pair k j)
def vS (j : ℕ) : ℕ := Nat.pair 3 j
def vV (x k : ℕ) : ℕ := Nat.pair 4 (Nat.pair x k)

/-- Un registro de `W` bits en las variables `v 0, …, v (W-1)`. -/
def reg (v : ℕ → ℕ) (W : ℕ) : Bits := fun j => if j < W then .atom (v j) else fals

/-- El número que guarda un registro bajo la asignación `σ`. -/
def leerReg (σ : ℕ → Bool) (v : ℕ → ℕ) (W : ℕ) : ℕ := numDe (fun j => σ (v j)) W

theorem evalB_reg (σ : ℕ → Bool) (v : ℕ → ℕ) (W j : ℕ) :
    evalB σ (reg v W j) = (leerReg σ v W).testBit j := by
  rw [leerReg, testBit_numDe]
  unfold reg
  split <;> simp_all [evalB]

theorem leerReg_lt (σ : ℕ → Bool) (v : ℕ → ℕ) (W : ℕ) : leerReg σ v W < 2 ^ W := numDe_lt _ _

theorem tam_reg (v : ℕ → ℕ) (W j : ℕ) : tam (reg v W j) ≤ 3 := by
  unfold reg; split <;> simp [tam]

/-- El valor del cable `w` en la entrada número `x`: si es una entrada, la constante del bit; si es la compuerta
`k = w - n`, su variable. -/
def valF (n x w : ℕ) : FP := if w < n then (if x.testBit w then verd else fals) else .atom (vV x (w - n))

/-- Lo mismo, como booleano bajo `σ`. -/
def valB (σ : ℕ → Bool) (n x w : ℕ) : Bool := if w < n then x.testBit w else σ (vV x (w - n))

theorem evalB_valF (σ : ℕ → Bool) (n x w : ℕ) : evalB σ (valF n x w) = valB σ n x w := by
  unfold valF valB
  split
  · split <;> simp_all
  · rfl

theorem tam_valF (n x w : ℕ) : tam (valF n x w) ≤ 3 := by
  unfold valF; split
  · split <;> simp
  · simp [tam]

/-- **Leer un cable por su índice**: el cable cuyo número está en el registro `R`. Es una disyunción sobre los
`n + s` cables: «`R = w` y el cable `w` vale». -/
def leerF (n s x : ℕ) (R : Bits) : FP :=
  disjL ((List.range (n + s)).map fun w => .and (eqF R (cte w) (n + s)) (valF n x w))

theorem evalB_leerF (σ : ℕ → Bool) {x : ℕ} {R : Bits} {r : ℕ} (hr : r < n + s)
    (hR : ∀ i, evalB σ (R i) = r.testBit i) : evalB σ (leerF n s x R) = valB σ n x r := by
  have hW : n + s < 2 ^ (n + s) := Nat.lt_two_pow_self
  rw [Bool.eq_iff_iff, leerF, evalB_disjL]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
    simp only [evalB, Bool.and_eq_true] at h
    rw [eqF_eval σ (by omega) (by omega) hR (evalB_cte σ w), decide_eq_true_iff] at h
    rw [← evalB_valF, h.1]; exact h.2
  · intro h
    refine ⟨_, ⟨r, hr, rfl⟩, ?_⟩
    simp only [evalB, Bool.and_eq_true]
    rw [eqF_eval σ (by omega) (by omega) hR (evalB_cte σ r), evalB_valF]
    exact ⟨by simp, h⟩

/-- «`r < c`», con `r` en el registro `R` de `W` bits. -/
def ltF (R : Bits) (W : ℕ) : ℕ → FP
  | 0 => fals
  | c + 1 => leF R (cte c) W

theorem evalB_ltF (σ : ℕ → Bool) {R : Bits} {r c W : ℕ} (hr : r < 2 ^ W) (hc : c ≤ 2 ^ W)
    (hR : ∀ i, evalB σ (R i) = r.testBit i) : evalB σ (ltF R W c) = decide (r < c) := by
  cases c with
  | zero => simp [ltF]
  | succ c =>
    rw [ltF, leF_eval σ hr (by omega) hR (evalB_cte σ c)]
    simp only [decide_eq_decide]; omega

/-! ## 3. El tipo de una compuerta, en dos bits -/

/-- La codificación: `y = 00`, `o = 01`, `no = 10`. -/
def codOp : Op → Bool × Bool
  | .y => (false, false)
  | .o => (false, true)
  | .no => (true, false)

/-- La decodificación es total (las cuatro combinaciones significan algo): `1·` es `no`. -/
def decOp (p q : Bool) : Op := if p then .no else if q then .o else .y

theorem decOp_codOp (op : Op) : decOp (codOp op).1 (codOp op).2 = op := by cases op <;> rfl

/-- La compuerta como fórmula: con los bits de tipo `P`, `Q` y los dos valores leídos `A`, `B`. -/
def opF (P Q A B : FP) : FP :=
  .or (.and P (neg A)) (.and (neg P) (.or (.and Q (.or A B)) (.and (neg Q) (.and A B))))

theorem evalB_opF (σ : ℕ → Bool) (P Q A B : FP) :
    evalB σ (opF P Q A B) = (decOp (evalB σ P) (evalB σ Q)).aplica (evalB σ A) (evalB σ B) := by
  simp only [opF, evalB, evalB_neg]
  cases evalB σ P <;> cases evalB σ Q <;> cases evalB σ A <;> cases evalB σ B <;> rfl

theorem tam_opF (P Q A B : FP) : tam (opF P Q A B) = 2 * tam P + 2 * tam Q + 3 * tam A + 2 * tam B + 14 := by
  simp only [opF, tam, tam_neg]; omega

/-! ## 4. La fórmula `Calcula(f, s, n)` -/

/-- El registro del primer cable que lee la compuerta `k` (ancho `n + s`). -/
def regA (n s k : ℕ) : Bits := reg (vA k) (n + s)
/-- El registro del segundo cable. -/
def regB (n s k : ℕ) : Bits := reg (vB k) (n + s)
/-- El registro del cable de salida. -/
def regS (n s : ℕ) : Bits := reg vS (n + s)

/-- **Validez de la descripción**: la salida es un cable que existe, y cada compuerta `k` lee cables `< n + k`. -/
def validez (n s : ℕ) : List FP :=
  ltF (regS n s) (n + s) (n + s) ::
    (List.range s).map fun k => .and (ltF (regA n s k) (n + s) (n + k)) (ltF (regB n s k) (n + s) (n + k))

/-- **Propagación**: en cada una de las `2ⁿ` entradas, cada compuerta vale su tipo aplicado a lo que lee. -/
def propagacion (n s : ℕ) : List FP :=
  (List.range (2 ^ n) ×ˢ List.range s).map fun p =>
    iffP (valF n p.1 (n + p.2))
      (opF (.atom (vOp p.2 0)) (.atom (vOp p.2 1)) (leerF n s p.1 (regA n s p.2)) (leerF n s p.1 (regB n s p.2)))

/-- La entrada número `x`, como vector de `n` bits. -/
def entradaDe (n x : ℕ) : Fin n → Bool := fun i => x.testBit i

/-- **Salida**: en cada entrada, el cable de salida coincide con la tabla de verdad de `f`. -/
def salida (s : ℕ) (f : (Fin n → Bool) → Bool) : List FP :=
  (List.range (2 ^ n)).map fun x =>
    if f (entradaDe n x) then leerF n s x (regS n s) else neg (leerF n s x (regS n s))

/-- **`Calcula(f, s, n)`**: «la descripción es un circuito bien formado de `s` compuertas, los valores se propagan
bien en las `2ⁿ` entradas y la salida coincide con `f` en todas». -/
def Calcula (f : (Fin n → Bool) → Bool) (s : ℕ) : FP :=
  .and (conjL (validez n s)) (.and (conjL (propagacion n s)) (conjL (salida s f)))

/-- **`CotaInferior(f, s, n) := ¬ Calcula(f, s, n)`**. -/
def CotaInferior (f : (Fin n → Bool) → Bool) (s : ℕ) : FP := neg (Calcula f s)

/-- Satisfacible: alguna asignación la hace verdadera. -/
def Satisfacible (p : FP) : Prop := ∃ σ : ℕ → Bool, p.eval σ = true

/-! ## 5. Lo que dice la fórmula, asignación por asignación -/

section Lectura

variable (σ : ℕ → Bool)

/-- El tipo de la compuerta `k` según `σ`. -/
def opDe (k : ℕ) : Op := decOp (σ (vOp k 0)) (σ (vOp k 1))
/-- El primer cable de la compuerta `k` según `σ`. -/
def aDe (n s k : ℕ) : ℕ := leerReg σ (vA k) (n + s)
/-- El segundo cable. -/
def bDe (n s k : ℕ) : ℕ := leerReg σ (vB k) (n + s)
/-- El cable de salida. -/
def outDe (n s : ℕ) : ℕ := leerReg σ vS (n + s)

/-- La parte de validez, leída. -/
def Valida (n s : ℕ) : Prop :=
  outDe σ n s < n + s ∧ ∀ k < s, aDe σ n s k < n + k ∧ bDe σ n s k < n + k

/-- La parte de propagación, leída. -/
def Propaga (n s : ℕ) : Prop :=
  ∀ x < 2 ^ n, ∀ k < s,
    valB σ n x (n + k) = (opDe σ k).aplica (valB σ n x (aDe σ n s k)) (valB σ n x (bDe σ n s k))

/-- La parte de salida, leída. -/
def Coincide (s : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x < 2 ^ n, valB σ n x (outDe σ n s) = f (entradaDe n x)

theorem evalB_validez : evalB σ (conjL (validez n s)) = true ↔ Valida σ n s := by
  have hW : n + s < 2 ^ (n + s) := Nat.lt_two_pow_self
  rw [evalB_conjL]
  simp only [validez, List.mem_cons, List.mem_map, List.mem_range, forall_eq_or_imp, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, Valida, regS]
  rw [evalB_ltF σ (leerReg_lt σ vS _) hW.le (evalB_reg σ vS _), decide_eq_true_iff]
  refine and_congr Iff.rfl (forall_congr' fun k => imp_congr_right fun hk => ?_)
  simp only [evalB, Bool.and_eq_true, regA, regB]
  rw [evalB_ltF σ (leerReg_lt σ _ _) (by omega) (evalB_reg σ _ _),
    evalB_ltF σ (leerReg_lt σ _ _) (by omega) (evalB_reg σ _ _)]
  simp [aDe, bDe]

theorem evalB_propagacion (hV : Valida σ n s) :
    evalB σ (conjL (propagacion n s)) = true ↔ Propaga σ n s := by
  rw [evalB_conjL]
  simp only [propagacion, List.mem_map, List.mem_product, List.mem_range, forall_exists_index, and_imp,
    Prod.forall, Propaga]
  constructor
  · intro h x hx k hk
    have := h _ x k hx hk rfl
    rw [evalB_iffP, evalB_valF, evalB_opF, regA, regB,
      evalB_leerF σ (r := aDe σ n s k) (by have := (hV.2 k hk).1; omega) (evalB_reg σ _ _),
      evalB_leerF σ (r := bDe σ n s k) (by have := (hV.2 k hk).2; omega) (evalB_reg σ _ _)] at this
    simpa [evalB, opDe] using this
  · rintro h _ x k hx hk rfl
    rw [evalB_iffP, evalB_valF, evalB_opF, regA, regB,
      evalB_leerF σ (r := aDe σ n s k) (by have := (hV.2 k hk).1; omega) (evalB_reg σ _ _),
      evalB_leerF σ (r := bDe σ n s k) (by have := (hV.2 k hk).2; omega) (evalB_reg σ _ _)]
    simpa [evalB, opDe] using h x hx k hk

theorem evalB_salida (f : (Fin n → Bool) → Bool) (hV : Valida σ n s) :
    evalB σ (conjL (salida s f)) = true ↔ Coincide σ s f := by
  rw [evalB_conjL]
  simp only [salida, List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Coincide]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  have hl := evalB_leerF σ (x := x) (r := outDe σ n s) hV.1 (evalB_reg σ vS _)
  rw [regS]
  split <;> rename_i hf <;> simp [hl, hf, outDe]

/-- **La fórmula, leída.** `Calcula(f, s, n)` es verdadera bajo `σ` si y solo si la descripción es válida, se
propaga y coincide con `f`. -/
theorem evalB_calcula (f : (Fin n → Bool) → Bool) :
    evalB σ (Calcula f s) = true ↔ Valida σ n s ∧ Propaga σ n s ∧ Coincide σ s f := by
  simp only [Calcula, evalB, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hV := (evalB_validez σ).mp h1
    exact ⟨hV, (evalB_propagacion σ hV).mp h2, (evalB_salida σ f hV).mp h3⟩
  · rintro ⟨hV, hP, hO⟩
    exact ⟨(evalB_validez σ).mpr hV, (evalB_propagacion σ hV).mpr hP, (evalB_salida σ f hV).mpr hO⟩

end Lectura

/-! ## 6. Corrección: `Calcula(f, s, n)` es satisfacible si y solo si hay circuito -/

section Correccion

/-- El circuito que describe una asignación válida. -/
def circuitoDe (σ : ℕ → Bool) (hV : Valida σ n s) : Circuito n s :=
  (fun k => (opDe σ k, ⟨aDe σ n s k, by have := (hV.2 k k.isLt).1; omega⟩,
      ⟨bDe σ n s k, by have := (hV.2 k k.isLt).2; omega⟩),
    ⟨outDe σ n s, hV.1⟩)

theorem circuitoDe_bienFormado (σ : ℕ → Bool) (hV : Valida σ n s) : BienFormado (circuitoDe σ hV) :=
  fun k => hV.2 k k.isLt

/-- El número de una entrada. -/
def numEntrada (y : Fin n → Bool) : ℕ := numDe (fun j => if h : j < n then y ⟨j, h⟩ else false) n

theorem entradaDe_numEntrada (y : Fin n → Bool) : entradaDe n (numEntrada y) = y := by
  funext i; simp [entradaDe, numEntrada, testBit_numDe, i.isLt]

theorem numEntrada_lt (y : Fin n → Bool) : numEntrada y < 2 ^ n := numDe_lt _ _

theorem calcula_circuitoDe (σ : ℕ → Bool) {f : (Fin n → Bool) → Bool} (hV : Valida σ n s) (hP : Propaga σ n s)
    (hO : Coincide σ s f) : calcula (circuitoDe σ hV) = f := by
  funext y
  have hx := numEntrada_lt y
  have hcons : Consistente (circuitoDe σ hV) y (fun w => valB σ n (numEntrada y) w) := by
    constructor
    · intro w h
      simp only [valB, h, ite_true]
      conv_rhs => rw [← entradaDe_numEntrada y]
      rfl
    · intro k
      exact hP _ hx k k.isLt
  have := cables_de_consistente (circuitoDe_bienFormado σ hV) hcons
  simp only [calcula, this]
  have h2 := hO _ hx
  rw [entradaDe_numEntrada] at h2
  exact h2

/-- La asignación que describe un circuito: su tipo, sus cables y sus valores en cada entrada. -/
def asig (C : Circuito n s) : ℕ → Bool := fun m =>
  if (Nat.unpair m).1 = 0 then
    (if h : (Nat.unpair (Nat.unpair m).2).1 < s then
      (if (Nat.unpair (Nat.unpair m).2).2 = 0 then (codOp (C.1 ⟨_, h⟩).1).1 else (codOp (C.1 ⟨_, h⟩).1).2)
    else false)
  else if (Nat.unpair m).1 = 1 then
    (if h : (Nat.unpair (Nat.unpair m).2).1 < s then
      ((C.1 ⟨_, h⟩).2.1 : ℕ).testBit (Nat.unpair (Nat.unpair m).2).2 else false)
  else if (Nat.unpair m).1 = 2 then
    (if h : (Nat.unpair (Nat.unpair m).2).1 < s then
      ((C.1 ⟨_, h⟩).2.2 : ℕ).testBit (Nat.unpair (Nat.unpair m).2).2 else false)
  else if (Nat.unpair m).1 = 3 then (C.2 : ℕ).testBit (Nat.unpair m).2
  else
    (if h : n + (Nat.unpair (Nat.unpair m).2).2 < n + s then
      cables C (entradaDe n (Nat.unpair (Nat.unpair m).2).1) ⟨_, h⟩ else false)

theorem opDe_asig (C : Circuito n s) (k : Fin s) : opDe (asig C) k = (C.1 k).1 := by
  simp [opDe, asig, vOp, Nat.unpair_pair, decOp_codOp]

theorem numDe_fin {W : ℕ} {f : ℕ → Bool} {a : ℕ} (ha : a < 2 ^ W) (hf : ∀ j, f j = a.testBit j) :
    numDe f W = a := by
  rw [show f = fun j => a.testBit j from funext hf]; exact numDe_testBit ha

theorem aDe_asig (C : Circuito n s) (k : Fin s) : aDe (asig C) n s k = (C.1 k).2.1 := by
  have := (C.1 k).2.1.isLt
  exact numDe_fin (by have := @Nat.lt_two_pow_self (n + s); omega) fun j => by simp [asig, vA, Nat.unpair_pair]

theorem bDe_asig (C : Circuito n s) (k : Fin s) : bDe (asig C) n s k = (C.1 k).2.2 := by
  have := (C.1 k).2.2.isLt
  exact numDe_fin (by have := @Nat.lt_two_pow_self (n + s); omega) fun j => by simp [asig, vB, Nat.unpair_pair]

theorem outDe_asig (C : Circuito n s) : outDe (asig C) n s = C.2 := by
  have := C.2.isLt
  exact numDe_fin (by have := @Nat.lt_two_pow_self (n + s); omega) fun j => by simp [asig, vS, Nat.unpair_pair]

theorem valB_asig (C : Circuito n s) (x : ℕ) {w : ℕ} (hw : w < n + s) :
    valB (asig C) n x w = cables C (entradaDe n x) ⟨w, hw⟩ := by
  unfold valB
  split_ifs with h
  · rw [cables_entrada C _ _ h]; rfl
  · simp only [asig, vV, Nat.unpair_pair]
    simp only [show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide,
      show (4 : ℕ) ≠ 3 by decide, ite_false]
    rw [dite_eq_left (by omega)]
    exact congrArg _ (Fin.ext (by simp only; omega))

/-- **Corrección, meta 1 (con exactamente `s` compuertas).** `Calcula(f, s, n)` es satisfacible si y solo si algún
circuito bien formado de `s` compuertas calcula `f`. -/
theorem satisfacible_calcula_iff (f : (Fin n → Bool) → Bool) (s : ℕ) :
    Satisfacible (Calcula f s) ↔ ∃ C : Circuito n s, BienFormado C ∧ calcula C = f := by
  simp only [Satisfacible, ← evalB_eq, evalB_calcula]
  constructor
  · rintro ⟨σ, hV, hP, hO⟩
    exact ⟨circuitoDe σ hV, circuitoDe_bienFormado σ hV, calcula_circuitoDe σ hV hP hO⟩
  · rintro ⟨C, hC, rfl⟩
    have hcons := fun x => cables_consistente hC (entradaDe n x)
    refine ⟨asig C, ⟨?_, fun k hk => ?_⟩, fun x _ k hk => ?_, fun x _ => ?_⟩
    · rw [outDe_asig]; exact C.2.isLt
    · rw [aDe_asig C ⟨k, hk⟩, bDe_asig C ⟨k, hk⟩]; exact hC ⟨k, hk⟩
    · rw [opDe_asig C ⟨k, hk⟩, aDe_asig C ⟨k, hk⟩, bDe_asig C ⟨k, hk⟩, valB_asig C x (by omega),
        valB_asig C x (C.1 ⟨k, hk⟩).2.1.isLt, valB_asig C x (C.1 ⟨k, hk⟩).2.2.isLt]
      exact (hcons x).2 ⟨k, hk⟩
    · rw [outDe_asig, valB_asig C x C.2.isLt]; rfl

/-- Rellenar un circuito de `t` compuertas hasta `s ≥ t`: las compuertas de más hacen «y» del cable 0 consigo. -/
def rellenar {t : ℕ} (s : ℕ) (hts : t ≤ s) (C : Circuito n t) : Circuito n s :=
  (fun k => if hk : (k : ℕ) < t then
      ((C.1 ⟨k, hk⟩).1, ⟨(C.1 ⟨k, hk⟩).2.1, by have := (C.1 ⟨k, hk⟩).2.1.isLt; omega⟩,
        ⟨(C.1 ⟨k, hk⟩).2.2, by have := (C.1 ⟨k, hk⟩).2.2.isLt; omega⟩)
    else (Op.y, ⟨0, by have := C.2.isLt; omega⟩, ⟨0, by have := C.2.isLt; omega⟩),
    ⟨C.2, by have := C.2.isLt; omega⟩)

theorem rellenar_bienFormado {t : ℕ} (hts : t ≤ s) {C : Circuito n t} (hC : BienFormado C) :
    BienFormado (rellenar s hts C) := by
  intro k
  simp only [rellenar]
  split_ifs with hk
  · exact hC ⟨k, hk⟩
  · have := C.2.isLt; simp only; omega

theorem calcula_rellenar {t : ℕ} (hts : t ≤ s) {C : Circuito n t} (hC : BienFormado C) :
    calcula (rellenar s hts C) = calcula C := by
  funext y
  have h0 : 0 < n + t := by have := C.2.isLt; omega
  let v : Fin (n + s) → Bool := fun w => if h : (w : ℕ) < n + t then cables C y ⟨w, h⟩ else cables C y ⟨0, h0⟩
  have hcons : Consistente (rellenar s hts C) y v := by
    constructor
    · intro w h
      simp only [v, dite_eq_left (show (w : ℕ) < n + t by omega)]
      exact cables_entrada C y _ h
    · intro k
      simp only [rellenar]
      split_ifs with hk
      · have hk' : n + (k : ℕ) < n + t := by omega
        have e := (cables_consistente hC y).2 ⟨k, hk⟩
        simp only [v, cableDe, dite_eq_left hk', dite_eq_left (C.1 ⟨k, hk⟩).2.1.isLt, dite_eq_left (C.1 ⟨k, hk⟩).2.2.isLt]
        simpa [cableDe] using e
      · simp only [v, cableDe, dite_eq_right (show ¬ (n + (k : ℕ) < n + t) by omega), dite_eq_left h0, Op.aplica,
          Bool.and_self]
  have := cables_de_consistente (rellenar_bienFormado hts hC) hcons
  change cables (rellenar s hts C) y (rellenar s hts C).2 = cables C y C.2
  rw [this]
  simp only [v, rellenar, dite_eq_left C.2.isLt]

/-- **Corrección, meta 1 (con a lo sumo `s` compuertas).** `Calcula(f, s, n)` es satisfacible si y solo si algún
circuito bien formado de `≤ s` compuertas calcula `f`. -/
theorem satisfacible_calcula_iff_hasta (f : (Fin n → Bool) → Bool) (s : ℕ) :
    Satisfacible (Calcula f s) ↔ ∃ t ≤ s, ∃ C : Circuito n t, BienFormado C ∧ calcula C = f := by
  rw [satisfacible_calcula_iff]
  constructor
  · rintro ⟨C, hC, hf⟩; exact ⟨s, le_rfl, C, hC, hf⟩
  · rintro ⟨t, hts, C, hC, rfl⟩
    exact ⟨rellenar s hts C, rellenar_bienFormado hts hC, calcula_rellenar hts hC⟩

/-- **Meta 2, la tautología de cota inferior.** `CotaInferior(f, s, n)` es tautología si y solo si ningún circuito
bien formado de `≤ s` compuertas calcula `f`. -/
theorem tautologia_cotaInferior_iff (f : (Fin n → Bool) → Bool) (s : ℕ) :
    Tautologia (CotaInferior f s) ↔ ∀ t ≤ s, ∀ C : Circuito n t, BienFormado C → calcula C ≠ f := by
  have h := satisfacible_calcula_iff_hasta f s
  simp only [Satisfacible, ← evalB_eq] at h
  simp only [Tautologia, ← evalB_eq, CotaInferior, evalB_neg, Bool.not_eq_true']
  constructor
  · intro hT t hts C hC hf
    obtain ⟨σ, hσ⟩ := h.mpr ⟨t, hts, C, hC, hf⟩
    simp [hT σ] at hσ
  · intro hN σ
    by_contra hσ
    simp only [Bool.not_eq_false] at hσ
    obtain ⟨t, hts, C, hC, hf⟩ := h.mp ⟨σ, hσ⟩
    exact hN t hts C hC hf

end Correccion

/-! ## 7. El tamaño: `2ⁿ · poly(n + s)` -/

section Tamano

theorem tam_leF {A B : Bits} {W : ℕ} (hA : ∀ i, tam (A i) ≤ 3) (hB : ∀ i, tam (B i) ≤ 3) :
    tam (leF A B W) ≤ 30 * W + 3 := by
  have := tam_menorAcc W A B verd 3 3 (fun i _ => hA i) (fun i _ => hB i) (by simp)
  unfold leF; omega

theorem tam_eqF {A B : Bits} {W : ℕ} (hA : ∀ i, tam (A i) ≤ 3) (hB : ∀ i, tam (B i) ≤ 3) :
    tam (eqF A B W) ≤ 60 * W + 7 := by
  have h1 := tam_leF (W := W) hA hB
  have h2 := tam_leF (W := W) hB hA
  simp only [eqF, tam]; omega

theorem tam_ltF {R : Bits} {W : ℕ} (hR : ∀ i, tam (R i) ≤ 3) (c : ℕ) : tam (ltF R W c) ≤ 30 * W + 3 := by
  cases c with
  | zero => simp [ltF]
  | succ c => have := tam_leF (W := W) hR (tam_cte c); simp only [ltF]; omega

/-- El tamaño de leer un cable: `(n + s)` términos de tamaño lineal en `n + s`. -/
def cotaLeer (M : ℕ) : ℕ := M * (60 * M + 12) + 1

theorem tam_leerF {R : Bits} (x : ℕ) (hR : ∀ i, tam (R i) ≤ 3) : tam (leerF n s x R) ≤ cotaLeer (n + s) := by
  have := tam_disjL (B := 60 * (n + s) + 11)
    ((List.range (n + s)).map fun w => .and (eqF R (cte w) (n + s)) (valF n x w)) (by
      simp only [List.mem_map, List.mem_range]
      rintro _ ⟨w, _, rfl⟩
      have := tam_eqF (W := n + s) hR (tam_cte w)
      have := tam_valF n x w
      simp only [tam]; omega)
  simp only [List.length_map, List.length_range] at this
  unfold leerF cotaLeer; omega

theorem tam_regA (k i : ℕ) : tam (regA n s k i) ≤ 3 := tam_reg _ _ _
theorem tam_regB (k i : ℕ) : tam (regB n s k i) ≤ 3 := tam_reg _ _ _
theorem tam_regS (i : ℕ) : tam (regS n s i) ≤ 3 := tam_reg _ _ _

theorem tam_validez : tam (conjL (validez n s)) ≤ (s + 1) * (60 * (n + s) + 8) + 3 := by
  have := tam_conjL (B := 60 * (n + s) + 7) (validez n s) (by
    simp only [validez, List.mem_cons, List.mem_map, List.mem_range]
    rintro _ (rfl | ⟨k, _, rfl⟩)
    · have := tam_ltF (W := n + s) (tam_regS (n := n) (s := s)) (n + s); omega
    · have := tam_ltF (W := n + s) (tam_regA (n := n) (s := s) k) (n + k)
      have := tam_ltF (W := n + s) (tam_regB (n := n) (s := s) k) (n + k)
      simp only [tam]; omega)
  simpa [validez] using this

theorem tam_propagacion : tam (conjL (propagacion n s)) ≤ 2 ^ n * s * (10 * cotaLeer (n + s) + 50) + 3 := by
  have := tam_conjL (B := 10 * cotaLeer (n + s) + 49) (propagacion n s) (by
    simp only [propagacion, List.mem_map, List.mem_product, List.mem_range, Prod.exists]
    rintro _ ⟨x, k, -, rfl⟩
    have := tam_leerF (n := n) (s := s) x (tam_regA (n := n) (s := s) k)
    have := tam_leerF (n := n) (s := s) x (tam_regB (n := n) (s := s) k)
    have := tam_valF n x (n + k)
    simp only [tam_iffP, tam_opF, tam]; omega)
  simpa [propagacion, List.length_product] using this

theorem tam_salida (f : (Fin n → Bool) → Bool) :
    tam (conjL (salida s f)) ≤ 2 ^ n * (cotaLeer (n + s) + 3) + 3 := by
  have := tam_conjL (B := cotaLeer (n + s) + 2) (salida s f) (by
    simp only [salida, List.mem_map, List.mem_range]
    rintro _ ⟨x, -, rfl⟩
    have := tam_leerF (n := n) (s := s) x (tam_regS (n := n) (s := s))
    split
    · omega
    · rw [tam_neg]; omega)
  simpa [salida] using this

/-- **Meta 2, el tamaño (cota superior).** `tam (CotaInferior(f, s, n)) ≤ 800 · 2ⁿ · (n + s + 1)³`: polinomial en el
tamaño `N = 2ⁿ` de la tabla de verdad y en `s`, exponencial en `n`. -/
theorem tam_cotaInferior (f : (Fin n → Bool) → Bool) (s : ℕ) :
    tam (CotaInferior f s) ≤ 800 * 2 ^ n * (n + s + 1) ^ 3 := by
  have hV := tam_validez (n := n) (s := s)
  have hP := tam_propagacion (n := n) (s := s)
  have hO := tam_salida (s := s) f
  have e : tam (CotaInferior f s) =
      tam (conjL (validez n s)) + tam (conjL (propagacion n s)) + tam (conjL (salida s f)) + 4 := by
    simp only [CotaInferior, Calcula, tam_neg, tam]; omega
  rw [e]
  set N := 2 ^ n with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  set M := n + s
  set K := M + 1
  have hsK : s ≤ K := by omega
  have hL : cotaLeer M ≤ 60 * K ^ 2 := by simp only [cotaLeer, K]; nlinarith
  have hK1 : 1 ≤ K := by omega
  have hKK : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right hK1 (by omega)
  have hNK : 1 ≤ N * K ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have a : N * s * (10 * cotaLeer M + 50) ≤ 650 * (N * K ^ 3) := by
    have : 10 * cotaLeer M + 50 ≤ 650 * K ^ 2 := by nlinarith
    calc N * s * (10 * cotaLeer M + 50) ≤ N * K * (650 * K ^ 2) := by gcongr
      _ = 650 * (N * K ^ 3) := by ring
  have b : N * (cotaLeer M + 3) ≤ 63 * (N * K ^ 3) := by
    have : cotaLeer M + 3 ≤ 63 * K ^ 3 := by nlinarith
    calc N * (cotaLeer M + 3) ≤ N * (63 * K ^ 3) := by gcongr
      _ = 63 * (N * K ^ 3) := by ring
  have c : (s + 1) * (60 * M + 8) ≤ 68 * (N * K ^ 3) := by
    have h1 : (s + 1) * (60 * M + 8) ≤ K * (68 * K) := by gcongr <;> omega
    have h2 : K * (68 * K) ≤ 68 * K ^ 3 := by nlinarith
    have h3 : K ^ 3 ≤ N * K ^ 3 := Nat.le_mul_of_pos_left _ hN1
    omega
  have : 800 * N * K ^ 3 = 800 * (N * K ^ 3) := by ring
  omega

theorem uno_le_tam (p : FP) : 1 ≤ tam p := by cases p <;> simp [tam]

theorem length_le_tam_conjL (l : List FP) : l.length ≤ tam (conjL l) := by
  induction l with
  | nil => simp [conjL]
  | cons a l ih =>
    have := uno_le_tam a
    simp only [conjL, List.foldr_cons, tam, List.length_cons] at ih ⊢; omega

/-- **El tamaño (cota inferior).** La tautología tiene al menos `2ⁿ` símbolos: una condición de salida por cada
fila de la tabla de verdad. -/
theorem dos_pow_le_tam (f : (Fin n → Bool) → Bool) (s : ℕ) : 2 ^ n ≤ tam (CotaInferior f s) := by
  have := length_le_tam_conjL (salida s f)
  have hl : (salida s f).length = 2 ^ n := by simp [salida]
  simp only [CotaInferior, Calcula, tam_neg, tam]; omega

/-- **El `2ⁿ` no se puede quitar.** Ninguna cota polinomial en `n + s` acota el tamaño de la familia. -/
theorem tam_no_polinomial :
    ¬ ∃ c d : ℕ, ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), tam (CotaInferior f s) ≤ c * (n + s + 1) ^ d := by
  rintro ⟨c, d, h⟩
  obtain ⟨N, hN⟩ := mul_pow_lt_dos_pow (c * 2 ^ d) d
  have h1 := h (N + 1) 0 (fun _ => false)
  have h2 := dos_pow_le_tam (fun _ : Fin (N + 1) → Bool => false) 0
  have h3 : (N + 1 + 0 + 1) ^ d ≤ 2 ^ d * (N + 1) ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
  have h4 := hN (N + 1) (by omega)
  have h5 : c * (N + 1 + 0 + 1) ^ d ≤ c * 2 ^ d * (N + 1) ^ d := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left c h3
  omega

end Tamano

/-! ## 8. Controles -/

section Controles

/-- El «y» de dos bits. -/
def y2 : (Fin 2 → Bool) → Bool := fun x => x 0 && x 1
/-- El «o exclusivo» de dos bits. -/
def xor2 : (Fin 2 → Bool) → Bool := fun x => x 0 ^^ x 1

/-- Una compuerta «y» sobre las dos entradas; la salida es el cable 2. -/
def circuitoY : Circuito 2 1 := (![(Op.y, 0, 1)], 2)

theorem circuitoY_calcula : BienFormado circuitoY ∧ calcula circuitoY = y2 := by decide

/-- La fórmula misma, evaluada por `decide` en la asignación que describe al circuito. -/
theorem calcula_y2_en_asig : evalB (asig circuitoY) (Calcula y2 1) = true := by decide +kernel

/-- **Control 1.** `Calcula(y, 1, 2)` es satisfacible. -/
theorem calcula_y2_satisfacible : Satisfacible (Calcula y2 1) :=
  (satisfacible_calcula_iff _ _).mpr ⟨circuitoY, circuitoY_calcula⟩

/-- **Control 1.** Así que `CotaInferior(y, 1, 2)` no es tautología. -/
theorem cotaInferior_y2_no_tautologia : ¬ Tautologia (CotaInferior y2 1) := by
  rw [tautologia_cotaInferior_iff]
  intro h
  exact h 1 le_rfl circuitoY circuitoY_calcula.1 circuitoY_calcula.2

/-- Sin compuertas solo se calculan proyecciones: ninguna es el «o exclusivo». Por `decide`, recorriendo los dos
circuitos de cero compuertas. -/
theorem sin_compuertas_no_xor2 : ∀ C : Circuito 2 0, BienFormado C → calcula C ≠ xor2 := by decide

/-- **Control 2, una cota inferior verdadera de juguete.** `CotaInferior(xor, 0, 2)` es tautología. -/
theorem cotaInferior_xor2_tautologia : Tautologia (CotaInferior xor2 0) := by
  rw [tautologia_cotaInferior_iff]
  intro t ht C hC
  obtain rfl : t = 0 := by omega
  exact sin_compuertas_no_xor2 C hC

/-- El «o exclusivo» de `Shannon.lean` (cuatro compuertas) está bien formado, así que `CotaInferior(xor, 4, 2)` no es
tautología: la familia distingue `s = 0` de `s = 4`. -/
theorem cotaInferior_xor2_cuatro_no_tautologia : ¬ Tautologia (CotaInferior xor2 4) := by
  rw [tautologia_cotaInferior_iff]
  intro h
  exact h 4 le_rfl circuitoXor (by decide) (by decide)

end Controles

/-! ## 9. Del modelo de Shannon a circuitos bien formados, y la conexión con P/poly -/

section BienFormar

variable {t : ℕ}

/-- A dónde va el cable `a` que lee la compuerta `j` al agregar dos compuertas al principio: una entrada se queda;
una compuerta ya calculada se corre dos lugares; una lectura adelantada (que en el modelo vale `false`) pasa a leer la
constante `false`, el cable `n + 1`. -/
def mover (j : ℕ) (a : Fin (n + t)) : Fin (n + (t + 2)) :=
  if (a : ℕ) < n then ⟨a, by omega⟩
  else if (a : ℕ) < n + j then ⟨a + 2, by have := a.isLt; omega⟩
  else ⟨n + 1, by omega⟩

/-- **Hacer bien formado un circuito cualquiera del modelo de Shannon**, con dos compuertas más: la `0` es `¬x₀`, la
`1` es `x₀ ∧ ¬x₀ = false`, y después van las de `C`, con sus lecturas movidas. Pide al menos una entrada. -/
def bienFormar (hn : 0 < n) (C : Circuito n t) : Circuito n (t + 2) :=
  (fun k =>
    if h0 : (k : ℕ) = 0 then (Op.no, ⟨0, by omega⟩, ⟨0, by omega⟩)
    else if h1 : (k : ℕ) = 1 then (Op.y, ⟨0, by omega⟩, ⟨n, by omega⟩)
    else
      ((C.1 ⟨k - 2, by have := k.isLt; omega⟩).1, mover (k - 2) (C.1 ⟨k - 2, by have := k.isLt; omega⟩).2.1,
        mover (k - 2) (C.1 ⟨k - 2, by have := k.isLt; omega⟩).2.2),
    mover t C.2)

theorem mover_lt {j : ℕ} (a : Fin (n + t)) : ((mover j a : Fin (n + (t + 2))) : ℕ) < n + (j + 2) := by
  unfold mover; split_ifs <;> simp only <;> omega

theorem bienFormar_bienFormado (hn : 0 < n) (C : Circuito n t) : BienFormado (bienFormar hn C) := by
  intro k
  simp only [bienFormar]
  split_ifs with h0 h1
  · simp only; omega
  · simp only; omega
  · have h2 := mover_lt (n := n) (t := t) (j := (k : ℕ) - 2) (C.1 ⟨k - 2, by have := k.isLt; omega⟩).2.1
    have h3 := mover_lt (n := n) (t := t) (j := (k : ℕ) - 2) (C.1 ⟨k - 2, by have := k.isLt; omega⟩).2.2
    refine ⟨?_, ?_⟩ <;> simp only <;> omega

theorem calcula_bienFormar (hn : 0 < n) (C : Circuito n t) : calcula (bienFormar hn C) = calcula C := by
  funext y
  let v : Fin (n + (t + 2)) → Bool := fun w =>
    if h : (w : ℕ) < n then cables C y ⟨w, by omega⟩
    else if (w : ℕ) = n then !cables C y ⟨0, by omega⟩
    else if (w : ℕ) = n + 1 then false
    else cables C y ⟨w - 2, by have := w.isLt; omega⟩
  -- lo que lee la compuerta `j` de `C`, visto en `v` a través de `mover`
  have hmov : ∀ (j : ℕ), j ≤ t → ∀ a : Fin (n + t), v (mover j a) = lee C y j a := by
    intro j hj a
    unfold mover lee
    split_ifs with h1 h2 h3 <;> simp only [v] <;> split_ifs <;> first | omega | rfl
  have hcons : Consistente (bienFormar hn C) y v := by
    constructor
    · intro w h
      simp only [v, dite_eq_left h]
      exact cables_entrada C y _ h
    · intro k
      simp only [bienFormar]
      split_ifs with h0 h1
      · have hn0 : ((⟨0, by omega⟩ : Fin (n + (t + 2))) : ℕ) < n := hn
        simp only [v, cableDe, h0, Op.aplica]
        simp [hn]
      · simp only [v, cableDe, h1, Op.aplica]
        simp [hn]
      · have hk2 := k.isLt
        have e1 : n + (k : ℕ) - 2 = n + (k - 2) := by omega
        have hc := cables_compuerta C y ⟨k - 2, by omega⟩
        rw [hmov (k - 2) (by omega), hmov (k - 2) (by omega), ← hc]
        simp only [v, cableDe]
        rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        exact congrArg _ (Fin.ext (by simp only; omega))
  have := cables_de_consistente (bienFormar_bienFormado hn C) hcons
  change cables (bienFormar hn C) y (bienFormar hn C).2 = cables C y C.2
  rw [this]
  have := hmov t le_rfl C.2
  simp only [bienFormar]
  rw [this]
  simp [lee, C.2.isLt]

/-- **Lo que dice la familia sobre P/poly.** Si para todo polinomio `p` hay algún `n ≥ 1` en el que la tautología
`CotaInferior(L restringido a n bits, p(n) + 2, n)` vale, entonces `L` no tiene circuitos polinomiales. Con `L = SAT`
eso es `NP ⊄ P/poly`. Es solo la traducción: no dice nada de si esas tautologías valen. -/
theorem fuera_de_PsobrePoly {L : Problema}
    (h : ∀ p : Polynomial ℕ, ∃ n ≥ 1, Tautologia (CotaInferior (rebanada L n) (p.eval n + 2))) :
    L ∉ PsobrePoly := by
  intro hL
  obtain ⟨p, hp⟩ := hL
  obtain ⟨n, hn, hT⟩ := h p
  rw [tautologia_cotaInferior_iff] at hT
  have hle : sucesion L n ≤ ((p.eval n : ℕ) : ℕ∞) := hp n
  apply absurd hle
  apply not_le.mpr
  apply lt_tamMin
  intro t ht C hC
  exact hT (t + 2) (by omega) (bienFormar hn C) (bienFormar_bienFormado hn C) (by rw [calcula_bienFormar, hC])

end BienFormar

end TautologiaCircuitos
end Extraccion
end Sagitta.Map
