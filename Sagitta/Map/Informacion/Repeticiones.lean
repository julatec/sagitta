import Sagitta.Map.DiagonalGodel
import Sagitta.Map.Borde.JugadaDiagonal
import Sagitta.Map.Continuo.MemoriaPeriodica
import Sagitta.Map.Informacion.Reversible
import Mathlib.Computability.RE
import Mathlib.InformationTheory.Coding.Kraft
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lo que se repite

Es el paso de Lean de «Lo que se repite» (ver las notas del proyecto).
Tres de las siete repeticiones, en Lean, como identificaciones y no como analogías.

## Lo que se prueba

1. **El teorema del punto fijo de Lawvere, en conjuntos** (§ 1). Mathlib ya lo tiene:
   `Function.exists_fixed_point_of_surjective` (si `e : A → A → B` es sobreyectiva, toda `f : B → B` tiene un punto
   fijo), y lo cita en la documentación como la raíz de `cantor_surjective`. Aquí se usa tal cual (`lawvere`) y se
   prueba la forma **débil** que en realidad hace falta (`lawvere_debil`): basta que una sola función, la diagonal
   modificada `x ↦ f (e x x)`, esté representada por algún `a` (`Representa`). La versión de Mathlib sale de la débil
   (`lawvere_de_debil`).
2. **Los corolarios** (§ 2–4).
   * **Cantor** (`cantor_bool`, `cantor_prop`): no hay sobreyección `A → (A → Bool)` ni `A → (A → Prop)`; la `f` sin
     punto fijo es la negación. `cantor_surjective` de Mathlib es `cantor_prop` (`cantor_de_mathlib`).
   * **La parada, en abstracto** (`parada_indecidible`): un tipo `P` de programas, `Para p q` («`p` para sobre `q`»), y
     una clase `Adm` de decisoras admisibles cerrada por **el programa que niega** (`Niega`: para toda decisora
     admisible `h` hay un `d` que para sobre `q` exactamente cuando `h q q = false`). Entonces ninguna decisora
     admisible decide la parada. Es Lawvere con `e = h` y `f = not`. La misma conclusión sale del lema diagonal común,
     `DiagonalGodel.diagonal_comun` (`parada_por_diagonal_comun`). Y el modelo no es vacío: con los
     códigos de Mathlib (`Nat.Partrec.Code`, numerados por `ℕ`) y las decisoras computables, el programa que niega
     existe (`niega_codigos`), así que sale que ninguna `h` computable decide la parada de los códigos
     (`parada_codigos`).
   * **Control**: si toda decisora es admisible, `Niega` es contradictoria (`niega_todo_falso`, con la decisora
     clásica). El contenido del teorema está en la restricción `Adm`: es lo que hace la computabilidad.
   * **La jugada diagonal no es una instancia de Lawvere, es el palomar** (§ 4). En `Borde/JugadaDiagonal.lean` hay
     `2^ℓ` rivales y palabras de `ℓ + 1` bits: `sal : Fin (2^ℓ) → (Fin (ℓ+1) → Bool)` no es de la forma `A → (A → B)`.
     Restringida a los primeros `ℓ + 1` rivales sí lo es (`A = Fin (ℓ + 1)`, `e = sal ∘ incluir`, `f = not`), y la
     diagonal de Cantor les gana a esos (`cantor_vence_primeros`, `cantor_primeros_no_sobre`); pero para `ℓ ≥ 2`
     quedan rivales sin diagonalizar (`quedan_rivales`), y hay una `sal` en la que un rival entrega justo la palabra
     de Cantor (`cantor_no_basta`, con `ℓ = 2`). `diagonal_existe` se prueba por **cuenta** (`2^(ℓ+1)` palabras contra
     `2^ℓ` rivales), no por diagonal: es la tercera repetición, no la segunda.
3. **Solomonoff es Gibbs** (§ 5). Familia finita de programas `P`, largos `ℓ : P → ℕ`, salidas `U : P → X`.
   `Z β = Σ_p e^(−β ℓ(p))`, `masaGibbs β S = Σ_{p ∈ S} e^(−β ℓ(p))`, `m x = Σ_{U p = x} 2^(−ℓ(p))`.
   * `solomonoff_es_gibbs`: `m x` es la masa de Gibbs de `U⁻¹ x` a `β = ln 2`; `suma_m`: `Σ_x m x = Z (ln 2)`.
   * `energia_libre_eq`: la energía libre `−(1/β) ln (masa)` a `β = ln 2` es `−log₂ m x`.
   * `cota_energia_libre`: `−log₂ m x ≤ ℓ p` para todo `p` con `U p = x` (en el modelo finito, `K ≥ −log₂ m`).
   * **Kraft**: Mathlib la tiene (`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`). Con
     ella, si los programas son palabras binarias sin prefijos (`codigo` inyectiva, `ℓ = largo`), `Z (ln 2) ≤ 1`
     (`kraft_Z`) y `m` es una semimedida (`semimedida`).
4. **Poincaré es el palomar** (§ 6). `recurrencia`: en `σ` finito toda órbita repite un estado antes de `|σ| + 1`
   pasos (es `MemoriaPeriodica.orbita_repite`). `poincare`: si el paso es inyectivo (biyección), la órbita vuelve
   **exactamente al estado inicial** en a lo sumo `|σ|` pasos, y vuelve infinitas veces (`poincare_infinitas`).
   `orbita_es_ciclo`: para una permutación, estar en la órbita del grupo (`Reversible.mem_orbita_iff_sameCycle`) es
   ser alcanzado hacia adelante. Control: sin inyectividad no hay retorno (`sin_retorno`).

## Lo que NO se prueba

* Lawvere en categorías cartesianas cerradas: solo la forma de conjuntos (la categoría de tipos).
* La distribución de Solomonoff de verdad (sobre una máquina universal sin prefijos, con infinitos programas) ni la
  igualdad `K = −log₂ m + O(1)` (el teorema de codificación de Levin): solo la cota fácil, en el modelo finito.
* Poincaré en espacios de medida: solo la forma discreta.
-/

namespace Sagitta.Map.Informacion.Repeticiones

open Finset Function

/-! ## 1. El teorema del punto fijo de Lawvere -/

section Lawvere

variable {A B : Type*}

/-- `e` **representa** a `g` si alguna fila de `e` es `g`. -/
def Representa (e : A → A → B) (g : A → B) : Prop := ∃ a, ∀ x, e a x = g x

/-- **Lawvere, forma débil**: si `e` representa la diagonal modificada `x ↦ f (e x x)`, `f` tiene un punto fijo. -/
theorem lawvere_debil (e : A → A → B) (f : B → B) (h : Representa e (fun x => f (e x x))) :
    ∃ b, f b = b := by
  obtain ⟨a, ha⟩ := h
  exact ⟨e a a, (ha a).symm⟩

/-- **Lawvere** (en Mathlib: `Function.exists_fixed_point_of_surjective`). -/
theorem lawvere (e : A → A → B) (he : Surjective e) (f : B → B) : ∃ b, f b = b :=
  exists_fixed_point_of_surjective e he f

/-- La forma de Mathlib sale de la débil: una sobreyección representa cualquier función. -/
theorem lawvere_de_debil (e : A → A → B) (he : Surjective e) (f : B → B) : ∃ b, f b = b :=
  lawvere_debil e f (let ⟨a, ha⟩ := he (fun x => f (e x x)); ⟨a, fun x => congrFun ha x⟩)

/-- **Contrapositiva**: si `f` no tiene punto fijo, ninguna `e` representa la diagonal modificada. -/
theorem lawvere_contra (e : A → A → B) (f : B → B) (hf : ∀ b, f b ≠ b) :
    ¬ Representa e (fun x => f (e x x)) := fun h =>
  let ⟨b, hb⟩ := lawvere_debil e f h
  hf b hb

end Lawvere

/-! ## 2. Cantor -/

section Cantor

variable {A : Type*}

theorem not_sin_punto_fijo (b : Bool) : (!b) ≠ b := by cases b <;> decide

theorem Not_sin_punto_fijo (p : Prop) : (¬ p) ≠ p := fun h => by
  have : ¬ p ↔ p := Iff.of_eq h
  tauto

/-- **Cantor con `Bool`**: no hay sobreyección `A → (A → Bool)`; la `f` sin punto fijo es `not`. -/
theorem cantor_bool (e : A → A → Bool) : ¬ Surjective e := fun he =>
  let ⟨b, hb⟩ := lawvere e he (fun b => !b)
  not_sin_punto_fijo b hb

/-- **Cantor con `Prop`**: la `f` sin punto fijo es `Not`. -/
theorem cantor_prop (e : A → A → Prop) : ¬ Surjective e := fun he =>
  let ⟨p, hp⟩ := lawvere e he Not
  Not_sin_punto_fijo p hp

/-- `cantor_surjective` de Mathlib es `cantor_prop` (`Set A` es `A → Prop`). -/
theorem cantor_de_mathlib (f : A → Set A) : ¬ Surjective f := fun hf =>
  cantor_prop (fun a x => x ∈ f a) fun g =>
    let ⟨a, ha⟩ := hf {x | g x}
    ⟨a, by funext x; change (x ∈ f a) = g x; rw [ha]; rfl⟩

end Cantor

/-! ## 3. La parada, en abstracto -/

section Parada

variable {P : Type*} (Para : P → P → Prop) (Adm : (P → P → Bool) → Prop)

/-- `h` **decide** la parada. -/
def Decide (h : P → P → Bool) : Prop := ∀ p q, h p q = true ↔ Para p q

/-- **El programa que niega**: para toda decisora admisible `h` hay un `d` que para sobre `q` exactamente cuando
`h q q = false` (cuando `h` dice que `q` no para sobre sí mismo). -/
def Niega : Prop := ∀ h, Adm h → ∃ d, ∀ q, Para d q ↔ h q q = false

/-- **La parada es indecidible**, como corolario de Lawvere con `e = h` y `f = not`. -/
theorem parada_indecidible (hn : Niega Para Adm) : ¬ ∃ h, Adm h ∧ Decide Para h := by
  rintro ⟨h, ha, hh⟩
  obtain ⟨d, hd⟩ := hn h ha
  have hr : Representa h (fun q => !(h q q)) := ⟨d, fun q => by
    have hq : h d q = true ↔ h q q = false := (hh d q).trans (hd q)
    cases h1 : h d q <;> cases h2 : h q q <;> simp_all⟩
  exact lawvere_contra h (fun b => !b) not_sin_punto_fijo hr

open Sagitta.Map.Tiempo.DiagonalGodel in
/-- **La misma conclusión desde la diagonal común** (`DiagonalGodel.diagonal_comun`), con
`Q q := Para q q`, `cert q := h q q = true` y el punto `d`. -/
theorem parada_por_diagonal_comun {P : Type} (Para : P → P → Prop) (Adm : (P → P → Bool) → Prop)
    (hn : Niega Para Adm) : ¬ ∃ h, Adm h ∧ Decide Para h := by
  rintro ⟨h, ha, hh⟩
  obtain ⟨d, hd⟩ := hn h ha
  refine diagonal_comun (fun q => Para q q) (fun q => h q q = true) (e := d) ?_ (fun x => hh x x)
  rw [hd d]
  simp

/-- **Control**: si toda decisora es admisible, el programa que niega no puede existir (la decisora clásica lo
refuta). El contenido está en la restricción `Adm`. -/
theorem niega_todo_falso : ¬ Niega Para (fun _ => True) := by
  classical
  intro hn
  exact parada_indecidible Para _ hn ⟨fun p q => decide (Para p q), trivial, fun p q => by simp⟩

/-! ### El modelo no es vacío: los códigos de Mathlib -/

open Nat.Partrec Encodable

/-- La parada de los códigos de Mathlib, numerados por `ℕ`: el programa `p` para sobre la entrada `q`. -/
def ParaCodigo (p q : ℕ) : Prop := (Code.eval (Denumerable.ofNat Code p) q).Dom

/-- Las decisoras admisibles son las computables. -/
def Computable2 (h : ℕ → ℕ → Bool) : Prop := Computable₂ h

/-- **El programa que niega existe** para toda decisora computable: `q ↦ si h q q entonces diverge, si no 0`. -/
theorem niega_codigos : Niega ParaCodigo Computable2 := by
  intro h hh
  have hc : Computable fun n => h n n := hh.comp Computable.id Computable.id
  have hf : Partrec fun n : ℕ => cond (h n n) (Part.none : Part ℕ) (Part.some 0) :=
    Partrec.cond hc Partrec.none (Computable.const 0).partrec
  obtain ⟨c, hcf⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  refine ⟨encode c, fun q => ?_⟩
  simp only [ParaCodigo, Denumerable.ofNat_encode, hcf]
  cases h q q <;> simp

/-- **Ninguna decisora computable decide la parada de los códigos.** -/
theorem parada_codigos : ¬ ∃ h, Computable₂ h ∧ Decide ParaCodigo h :=
  parada_indecidible ParaCodigo Computable2 niega_codigos

end Parada

/-! ## 4. La jugada diagonal: Lawvere solo para los primeros rivales -/

section Jugada

open Sagitta.Map.Borde.JugadaDiagonal

theorem lt_dos_pow (ℓ : ℕ) : ℓ + 1 ≤ 2 ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

/-- Los primeros `ℓ + 1` rivales, como índices de palabras. -/
def incluir (ℓ : ℕ) (i : Fin (ℓ + 1)) : Fin (2 ^ ℓ) := ⟨i, lt_of_lt_of_le i.2 (lt_dos_pow ℓ)⟩

/-- La palabra de Cantor: invierte el bit `i` del rival `i`. -/
def cantor {ℓ : ℕ} (sal : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) : Fin (ℓ + 1) → Bool :=
  fun i => !(sal (incluir ℓ i) i)

/-- **La diagonal de Cantor les gana a los primeros `ℓ + 1` rivales.** -/
theorem cantor_vence_primeros {ℓ : ℕ} (sal : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) (i : Fin (ℓ + 1)) :
    sal (incluir ℓ i) ≠ cantor sal := fun h => by
  have := congrFun h i
  simp [cantor] at this

/-- La misma cosa dicha como Lawvere: `A = Fin (ℓ + 1)`, `e = sal ∘ incluir`, `f = not`; `e` no es sobreyectiva. -/
theorem cantor_primeros_no_sobre {ℓ : ℕ} (sal : Fin (2 ^ ℓ) → Fin (ℓ + 1) → Bool) :
    ¬ Surjective (fun i => sal (incluir ℓ i)) :=
  cantor_bool _

/-- Para `ℓ ≥ 2` hay más rivales que bits: quedan rivales que la diagonal de Cantor no mira. -/
theorem quedan_rivales {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : ℓ + 1 < 2 ^ ℓ := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

/-- Un `sal` con `ℓ = 2`: los rivales 0, 1, 2 entregan `000`, y el rival 3 entrega `111`, que es justo la palabra de
Cantor. -/
def salTrampa : Fin (2 ^ 2) → Fin (2 + 1) → Bool := fun p _ => decide (p = 3)

/-- **La diagonal de Cantor no basta**: en `salTrampa` un rival la entrega, así que no es una palabra `Diagonal`. -/
theorem cantor_no_basta : ¬ Diagonal salTrampa (cantor salTrampa) := by
  intro h
  exact h 3 (by funext i; fin_cases i <;> decide)

/-- La que sí funciona es la de la cuenta (`diagonal_existe`): repetición del palomar, no de la diagonal. -/
theorem jugada_por_cuenta : ∃ x, Diagonal salTrampa x := diagonal_existe salTrampa

end Jugada

/-! ## 5. Solomonoff es Gibbs -/

section Solomonoff

variable {P X : Type*} [Fintype P] [DecidableEq X] (ℓ : P → ℕ) (U : P → X)

/-- La función de partición, con el largo como energía. -/
noncomputable def Z (β : ℝ) : ℝ := ∑ p, Real.exp (-β * ℓ p)

/-- La masa de Gibbs (sin normalizar) de un conjunto de programas. -/
noncomputable def masaGibbs (β : ℝ) (S : Finset P) : ℝ := ∑ p ∈ S, Real.exp (-β * ℓ p)

/-- La distribución de Solomonoff del modelo finito: `m x = Σ_{U p = x} 2^(−ℓ p)`. -/
noncomputable def m (x : X) : ℝ := ∑ p ∈ univ.filter (fun p => U p = x), (1 / 2 : ℝ) ^ ℓ p

/-- La energía libre `−(1/β) ln (masa)`. -/
noncomputable def energiaLibre (β : ℝ) (S : Finset P) : ℝ := -Real.log (masaGibbs ℓ β S) / β

theorem exp_log_dos (n : ℕ) : Real.exp (-Real.log 2 * n) = (1 / 2 : ℝ) ^ n := by
  rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log two_pos, one_div, inv_pow]

/-- **Solomonoff es Gibbs**: `m x` es la masa de Gibbs de `U⁻¹ x` a `β = ln 2`. -/
theorem solomonoff_es_gibbs (x : X) :
    m ℓ U x = masaGibbs ℓ (Real.log 2) (univ.filter (fun p => U p = x)) :=
  Finset.sum_congr rfl fun p _ => (exp_log_dos (ℓ p)).symm

/-- Y `Z (ln 2)` es la masa de todos los programas. -/
theorem Z_es_masa (β : ℝ) : Z ℓ β = masaGibbs ℓ β univ := rfl

/-- **La normalización**: `Σ_x m x = Z (ln 2)`. -/
theorem suma_m [Fintype X] : ∑ x, m ℓ U x = Z ℓ (Real.log 2) := by
  simp only [solomonoff_es_gibbs, masaGibbs, Z]
  exact Finset.sum_fiberwise univ U _

theorem m_pos {x : X} {p : P} (hp : U p = x) : (1 / 2 : ℝ) ^ ℓ p ≤ m ℓ U x :=
  Finset.single_le_sum (f := fun p => (1 / 2 : ℝ) ^ ℓ p) (fun _ _ => by positivity)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)

/-- **La energía libre a `β = ln 2` es `−log₂ m x`.** -/
theorem energia_libre_eq (x : X) :
    energiaLibre ℓ (Real.log 2) (univ.filter (fun p => U p = x)) = -Real.logb 2 (m ℓ U x) := by
  rw [energiaLibre, ← solomonoff_es_gibbs, Real.logb, neg_div]

/-- **`K ≥ −log₂ m`, en el modelo finito**: la energía libre no pasa de la energía de ningún programa que produce
`x` (en particular del más corto). -/
theorem cota_energia_libre {x : X} {p : P} (hp : U p = x) : -Real.logb 2 (m ℓ U x) ≤ ℓ p := by
  have h1 := m_pos ℓ U hp
  have h2 : 0 < (1 / 2 : ℝ) ^ ℓ p := by positivity
  have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) h2 h1
  have h4 : Real.logb 2 ((1 / 2 : ℝ) ^ ℓ p) = -(ℓ p : ℝ) := by
    rw [Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    ring
  linarith

/-- **Kraft** (Mathlib): si los programas son palabras binarias sin prefijos y el largo es el de la palabra,
`Z (ln 2) ≤ 1`. -/
theorem kraft_Z (codigo : P → List Bool) (hinj : Injective codigo)
    (hpf : InformationTheory.IsPrefixFree (Set.range codigo)) (hℓ : ∀ p, ℓ p = (codigo p).length) :
    Z ℓ (Real.log 2) ≤ 1 := by
  have hS : InformationTheory.IsPrefixFree ((univ.image codigo : Finset (List Bool)) : Set (List Bool)) := by
    simpa [Finset.coe_image] using hpf
  have hk := InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one hS
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at hk
  simp only [Fintype.card_bool, Nat.cast_ofNat] at hk
  calc Z ℓ (Real.log 2) = ∑ p, (1 / 2 : ℝ) ^ (codigo p).length := by
        simp only [Z]
        exact Finset.sum_congr rfl fun p _ => by rw [exp_log_dos, hℓ]
    _ ≤ 1 := hk

/-- **`m` es una semimedida**: con programas sin prefijos, `Σ_x m x ≤ 1`. -/
theorem semimedida [Fintype X] (codigo : P → List Bool) (hinj : Injective codigo)
    (hpf : InformationTheory.IsPrefixFree (Set.range codigo)) (hℓ : ∀ p, ℓ p = (codigo p).length) :
    ∑ x, m ℓ U x ≤ 1 := by
  rw [suma_m]
  exact kraft_Z ℓ codigo hinj hpf hℓ

end Solomonoff

/-! ## 6. Poincaré es el palomar -/

section Poincare

open Sagitta.Map.Continuo.Memoria

variable {σ : Type*} [Fintype σ]

/-- **Recurrencia**: en `σ` finito la órbita de cualquier paso repite un estado antes de `|σ| + 1` pasos. Es
`MemoriaPeriodica.orbita_repite`, el palomar. -/
theorem recurrencia (f : σ → σ) (x : σ) :
    ∃ i j, i < j ∧ j ≤ Fintype.card σ ∧ f^[i] x = f^[j] x :=
  orbita_repite f x

/-- **Poincaré discreta**: si el paso es inyectivo (una biyección de `σ` finito), la órbita vuelve exactamente al
estado inicial en a lo sumo `|σ|` pasos. -/
theorem poincare (f : σ → σ) (hf : Injective f) (x : σ) :
    ∃ n, 0 < n ∧ n ≤ Fintype.card σ ∧ f^[n] x = x := by
  obtain ⟨i, j, hij, hj, he⟩ := recurrencia f x
  refine ⟨j - i, by omega, by omega, ?_⟩
  have : f^[i] (f^[j - i] x) = f^[i] x := by
    rw [← iterate_add_apply, show i + (j - i) = j by omega, he]
  exact hf.iterate i this

end Poincare

section PoincareFinito

variable {σ : Type*} [Finite σ]

/-- Y vuelve infinitas veces. -/
theorem poincare_infinitas (f : σ → σ) (hf : Injective f) (x : σ) (N : ℕ) :
    ∃ n, N ≤ n ∧ f^[n] x = x := by
  have := Fintype.ofFinite σ
  obtain ⟨n, hn, -, hx⟩ := poincare f hf x
  refine ⟨n * N, Nat.le_mul_of_pos_left N hn, ?_⟩
  exact (show IsPeriodicPt f n x from hx).mul_const N

/-- **Las órbitas de una permutación son ciclos**: estar en la órbita del grupo generado (con pasos hacia atrás,
`Reversible.mem_orbita_iff_sameCycle`) es ser alcanzado con pasos hacia adelante. -/
theorem orbita_es_ciclo (f : Equiv.Perm σ) (x y : σ) :
    y ∈ MulAction.orbit (Subgroup.zpowers f) x ↔ ∃ n : ℕ, f^[n] x = y := by
  rw [Sagitta.Map.Informacion.Reversible.mem_orbita_iff_sameCycle]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [Equiv.Perm.iterate_eq_pow]; exact hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [Equiv.Perm.iterate_eq_pow, zpow_natCast]⟩

/-- **Control**: sin inyectividad no hay retorno. En `Fin 2` con el paso constante `1`, el `0` no vuelve nunca. -/
theorem sin_retorno : ¬ ∃ n, 0 < n ∧ (fun _ : Fin 2 => (1 : Fin 2))^[n] 0 = 0 := by
  rintro ⟨n, hn, h⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [iterate_succ_apply'] at h
  exact absurd h (by decide)

end PoincareFinito

end Sagitta.Map.Informacion.Repeticiones
