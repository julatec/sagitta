import Sagitta.Map.Clases
import Mathlib.Data.Part
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# La tasa de aproximación: el primer fallo de cada máquina

Formalización de la **Definición 5** y el **Lema 6** de S. Ben-David y S. Halevi, «On the Independence of P versus
NP», Technion, informe técnico 699 (revisado), noviembre de 1991. No hay nada propio: es un ejercicio.

Sea `C` una clase de problemas con una enumeración `M 0, M 1, M 2, …` de sus miembros, y `L` un problema.

* **Definición 5.** La *tasa de aproximación* de `L` por `C` es
  `R(i) = máx_{j < i} mín { |x| : M j x ≠ L x }`:
  hasta qué largo de entrada hay que llegar para que cada una de las primeras `i` máquinas ya haya fallado.
* **Lema 6.** `R` es total si y solo si `L ∉ C`.

`R` es una función parcial: `R(i)` solo está definida si las máquinas `0, …, i-1` fallan todas. Por eso `tasa` va a
`Part ℕ`.

## Lo que este archivo no hace

* No construye la enumeración. En el artículo es una «enumeración canónica» de máquinas con reloj; aquí `M` es un
  parámetro cualquiera, y la conexión con `P` lleva la hipótesis `Set.range M = P`. Que `P` tenga una enumeración
  (es numerable) no está probado en este proyecto.
* No dice nada de demostrabilidad. El Teorema 4 del artículo (la teoría demuestra `P ≠ NP` si y solo si `R` está
  dominada por la jerarquía de Wainer) necesita la aritmética de Peano formalizada, que aquí no hay.
-/

namespace Sagitta.Map
namespace PrimerFallo

set_option linter.style.openClassical false
open Classical

variable (M : ℕ → Problema) (L : Problema)

/-- La máquina `j` se equivoca en alguna entrada de largo `n`. -/
def FallaEn (j n : ℕ) : Prop := ∃ x : List Bool, x.length = n ∧ M j x ≠ L x

/-- La máquina `j` se equivoca en alguna entrada. -/
def Falla (j : ℕ) : Prop := ∃ n, FallaEn M L j n

/-- Fallar en alguna entrada es no ser el problema `L`. -/
theorem falla_iff (j : ℕ) : Falla M L j ↔ M j ≠ L := by
  constructor
  · rintro ⟨n, x, -, hx⟩ h
    exact hx (by rw [h])
  · intro h
    obtain ⟨x, hx⟩ := Function.ne_iff.mp h
    exact ⟨x.length, x, rfl, hx⟩

/-- **El primer fallo** de la máquina `j`: el menor largo en que se equivoca. Vale `0` si no se equivoca nunca; ese
caso no se usa, porque `tasa` solo está definida cuando hay fallo. -/
noncomputable def primerFallo (j : ℕ) : ℕ := if h : Falla M L j then Nat.find h else 0

/-- En el largo `primerFallo`, la máquina `j` se equivoca. -/
theorem falla_en_primerFallo {j : ℕ} (h : Falla M L j) : FallaEn M L j (primerFallo M L j) := by
  simp only [primerFallo, h, ↓reduceDIte]
  exact Nat.find_spec h

/-- Antes de su primer fallo, la máquina `j` acierta en todo: coincide con `L` en las entradas más cortas. -/
theorem acierta_antes {j : ℕ} (h : Falla M L j) {x : List Bool} (hx : x.length < primerFallo M L j) :
    M j x = L x := by
  simp only [primerFallo, h, ↓reduceDIte] at hx
  by_contra hne
  exact Nat.find_min h hx ⟨x, rfl, hne⟩

/-- **Definición 5 (Ben-David y Halevi).** La tasa de aproximación de `L` por la enumeración `M`: el mayor de los
primeros fallos de las máquinas `0, …, i-1`. Está definida solo si todas ellas fallan. -/
noncomputable def tasa (i : ℕ) : Part ℕ :=
  ⟨∀ j < i, Falla M L j, fun _ => (Finset.range i).sup (primerFallo M L)⟩

theorem tasa_dom (i : ℕ) : (tasa M L i).Dom ↔ ∀ j < i, Falla M L j := Iff.rfl

/-- Lo que significa el valor: cada una de las primeras `i` máquinas ya falló en alguna entrada de largo a lo sumo
`R(i)`. -/
theorem falla_antes_de_tasa {i : ℕ} (h : (tasa M L i).Dom) {j : ℕ} (hj : j < i) :
    ∃ x : List Bool, x.length ≤ (tasa M L i).get h ∧ M j x ≠ L x := by
  obtain ⟨x, hx, hne⟩ := falla_en_primerFallo M L (h j hj)
  refine ⟨x, ?_, hne⟩
  rw [hx]
  exact Finset.le_sup (f := primerFallo M L) (Finset.mem_range.mpr hj)

/-- La tasa es creciente donde está definida. -/
theorem tasa_mono {i i' : ℕ} (hii : i ≤ i') (h : (tasa M L i).Dom) (h' : (tasa M L i').Dom) :
    (tasa M L i).get h ≤ (tasa M L i').get h' :=
  Finset.sup_mono (Finset.range_mono hii)

/-- **Lema 6 (Ben-David y Halevi).** La tasa de aproximación es total si y solo si `L` no es ninguno de los
problemas de la enumeración. -/
theorem tasa_total_iff : (∀ i, (tasa M L i).Dom) ↔ L ∉ Set.range M := by
  constructor
  · rintro h ⟨j, rfl⟩
    exact (falla_iff M (M j) j).mp (h (j + 1) j (Nat.lt_succ_self j)) rfl
  · intro h i j _
    exact (falla_iff M L j).mpr fun e => h ⟨j, e⟩

/-! ## Con la clase `P` -/

/-- El Lema 6 para `P`: si `M` enumera exactamente los problemas de `P`, la tasa de aproximación de `L` es total si
y solo si `L ∉ P`. -/
theorem tasa_total_iff_no_en_P (hM : Set.range M = P) : (∀ i, (tasa M L i).Dom) ↔ L ∉ P := by
  rw [tasa_total_iff, hM]

/-- **`P ≠ NP`, dicho con la tasa.** Dado `P ⊆ NP` y una enumeración de `P`: `P ≠ NP` si y solo si algún problema
de `NP` tiene tasa de aproximación total. Es la afirmación «para todo `i` existe…» cuyo ritmo de crecimiento mide
si una teoría puede demostrarla. -/
theorem pDistintoNP_iff_tasa_total (hM : Set.range M = P) (hsub : PSubNP) :
    PDistintoNP ↔ ∃ L ∈ NP, ∀ i, (tasa M L i).Dom := by
  constructor
  · intro hne
    by_contra hno
    apply hne
    refine Set.Subset.antisymm hsub fun L hL => ?_
    by_contra hLP
    exact hno ⟨L, hL, (tasa_total_iff_no_en_P M L hM).mpr hLP⟩
  · rintro ⟨L, hL, htot⟩ e
    exact (tasa_total_iff_no_en_P M L hM).mp htot (by rw [show P = NP from e]; exact hL)

/-! ## El Lema 7: si los fallos están lejos, hay un algoritmo

**Lema 7 (Ben-David y Halevi).** Si la inversa de la tasa está acotada por `g`, entonces SAT se decide en tiempo
`n^(1 + log g(n)) · g(n)`. El algoritmo: para `i = 1, …, g(|x|)`, usar la máquina `i` como oráculo de SAT para
hallar una asignación de `x`, y verificarla; aceptar si alguna sirve.

Aquí va en tres partes, todas sobre funciones, sin máquinas de Turing:

1. `buena`: si la tasa en `i` pasa de `m` (o no está definida), alguna de las primeras `i` máquinas coincide con `L`
   en todas las entradas de largo a lo sumo `m`.
2. `decide7_correcto`: el algoritmo decide `L`, para cualquier problema con verificador y con una forma de hallar el
   certificado usando un oráculo de decisión (la *autorreducción*, que para SAT es fijar las variables una por una).
3. `costo7_le`: la cuenta del tiempo, con la convención del artículo de que la máquina `i` corre `n^(log i)` pasos y
   de que hallar el certificado hace `n` consultas de largo a lo sumo `n`.

Lo que no hace: la autorreducción es una hipótesis (`Autorreduccion`), no se construye para ningún problema; y el
costo es una suma de cotas, no pasos de una máquina. De aquí no sale `L ∈ DTIME(…)` con las definiciones de
`Clases.lean`. -/

/-- **Alguna máquina es buena hasta `m`.** Si, cada vez que la tasa en `i` está definida, pasa de `m`, entonces una
de las máquinas `0, …, i-1` coincide con `L` en todas las entradas de largo a lo sumo `m`. Cubre los dos casos: si
la tasa no está definida, una de esas máquinas *es* `L`. -/
theorem buena {i m : ℕ} (h : ∀ hd : (tasa M L i).Dom, m < (tasa M L i).get hd) :
    ∃ j < i, ∀ z : List Bool, z.length ≤ m → M j z = L z := by
  by_cases hd : (tasa M L i).Dom
  · have hlt : m < (Finset.range i).sup (primerFallo M L) := h hd
    obtain ⟨j, hj, hjm⟩ := Finset.lt_sup_iff.mp hlt
    have hji : j < i := Finset.mem_range.mp hj
    exact ⟨j, hji, fun z hz => acierta_antes M L (hd j hji) (lt_of_le_of_lt hz hjm)⟩
  · have hd' : ∃ j, j < i ∧ ¬ Falla M L j := by
      by_contra hno
      exact hd fun j hj => by_contra fun hf => hno ⟨j, hj, hf⟩
    obtain ⟨j, hji, hj⟩ := hd'
    have hjL : M j = L := by
      by_contra hne
      exact hj ((falla_iff M L j).mpr hne)
    exact ⟨j, hji, fun z _ => by rw [hjL]⟩

/-- **Autorreducción.** Un verificador `V` para `L` y una forma de hallar el certificado con un oráculo de decisión:
si el oráculo coincide con `L` en las entradas de largo a lo sumo `s |x|` y `x` está en `L`, lo que `hallar` entrega
lo acepta el verificador. Para SAT, `hallar` fija las variables una por una y `s n = n`. -/
structure Autorreduccion (L : Problema) where
  /-- El verificador. -/
  V : List Bool → List Bool → Bool
  /-- Hallar un certificado consultando un oráculo de decisión. -/
  hallar : Problema → List Bool → List Bool
  /-- Hasta qué largo llegan las consultas. -/
  s : ℕ → ℕ
  /-- Lo que el verificador acepta es de `L`. -/
  solido : ∀ x y, V x y = true → L x = true
  /-- Con un oráculo correcto hasta el largo `s |x|`, `hallar` entrega un certificado válido. -/
  completo : ∀ (O : Problema) (x : List Bool), (∀ z : List Bool, z.length ≤ s x.length → O z = L z) →
    L x = true → V x (hallar O x) = true

variable {L}

/-- **El algoritmo del Lema 7.** Probar las primeras `g |x|` máquinas como oráculo, y verificar lo que cada una
permita hallar. -/
def decide7 (A : Autorreduccion L) (g : ℕ → ℕ) (x : List Bool) : Bool :=
  (List.range (g x.length)).any fun i => A.V x (A.hallar (M i) x)

/-- **El algoritmo decide `L`**, si para cada largo alguna de las primeras `g n` máquinas es buena hasta `s n`.
No confía en ninguna máquina: solo acepta lo que el verificador aprueba. -/
theorem decide7_correcto (A : Autorreduccion L) (g : ℕ → ℕ)
    (hg : ∀ n, ∃ j < g n, ∀ z : List Bool, z.length ≤ A.s n → M j z = L z) (x : List Bool) :
    decide7 M A g x = L x := by
  cases hL : L x with
  | true =>
    obtain ⟨j, hj, hbuena⟩ := hg x.length
    exact List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, A.completo (M j) x hbuena hL⟩
  | false =>
    rw [decide7, List.any_eq_false]
    intro i _ hV
    rw [A.solido x _ hV] at hL
    exact Bool.noConfusion hL

/-- **El Lema 7, en su parte de corrección.** Si la tasa en `g n` pasa de `s n` para todo `n` (es decir, la inversa
de la tasa está acotada por `g`), el algoritmo decide `L`. -/
theorem decide7_de_tasa (A : Autorreduccion L) (g : ℕ → ℕ)
    (hg : ∀ n, ∀ hd : (tasa M L (g n)).Dom, A.s n < (tasa M L (g n)).get hd) (x : List Bool) :
    decide7 M A g x = L x :=
  decide7_correcto M A g (fun n => buena M L (hg n)) x

/-- El costo del algoritmo en entradas de largo `n`, con las convenciones del artículo: `g n` máquinas, `n`
consultas a cada una, y la máquina `i` corre `n^(log i)` pasos en entradas de largo a lo sumo `n`. -/
def costo7 (g : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range (g n), n * n ^ Nat.log 2 i

/-- **El Lema 7, en su parte de tiempo:** el costo no pasa de `g(n) · n^(1 + log g(n))`. -/
theorem costo7_le (g : ℕ → ℕ) (n : ℕ) : costo7 g n ≤ g n * n ^ (1 + Nat.log 2 (g n)) := by
  have hterm : ∀ i ∈ Finset.range (g n), n * n ^ Nat.log 2 i ≤ n ^ (1 + Nat.log 2 (g n)) := by
    intro i hi
    rw [pow_add, pow_one]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hn (Nat.log_mono_right (Finset.mem_range.mp hi).le))
  calc costo7 g n ≤ (Finset.range (g n)).card • n ^ (1 + Nat.log 2 (g n)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = g n * n ^ (1 + Nat.log 2 (g n)) := by simp

end PrimerFallo
end Sagitta.Map
