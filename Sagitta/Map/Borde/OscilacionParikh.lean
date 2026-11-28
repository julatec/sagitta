import Sagitta.Map.Borde.SatEnElBorde
import Sagitta.Map.Completitud.Puente

/-!
# La oscilación no se demuestra con Parikh

**Lo que se formaliza es conocido.** Es un paso de la prueba del teorema 1.1 de J. Bydžovský, J. Krajíček e
I. C. Oliveira, «Consistency of circuit lower bounds with bounded theories», *Logical Methods in Computer Science* 16
(2020), sección 3: si `S¹₂` o `T¹₂` demuestra que un problema rellenable tiene circuitos de tamaño `m^k` en infinitos
largos `m` (la oración `UB^{i.o.}_k`), Parikh acota esos largos por un polinomio y el relleno da circuitos en todo
largo. La búsqueda bibliográfica de Sagitta lo encontró ahí; no es una observación propia. Lo
propio es la formalización en Lean, sobre el relleno de `Relleno.lean`.

## El argumento

«SAT oscila en circuitos» (`Oscila (sucNat satMarco)`, de `Tricotomia.lean`) tiene dos mitades: no está en P/poly, y
hay un polinomio `c·(m+1)^k` con infinitos largos buenos. La segunda es un enunciado `∀ x ∃ y φ(x, y)`: para todo `x`
hay un `y` con `|y| ≥ |x|` y un circuito de tamaño `c·(|y|+1)^k` para SAT en el largo `|y|` (`Buenos`). Una teoría
con la propiedad de Parikh que lo demuestre lo demuestra con `y` acotado por una función de largo polinomial; si la
teoría es sana, esa cota es verdadera, y los largos buenos quedan a distancia polinomial (`Denso`). Con el relleno,
eso es P/poly (`psobrePoly_de_denso`), y SAT no oscila.

## 1. La versión abstracta

* `Enunciado`: la matriz `ψ(x, y)` de un `∀ x ∃ y ψ`. `Verdadero ψ`: vale en ℕ.
* `CotaPol β`: el largo de `β x` es a lo sumo polinomial en el de `x` (lo que da un término con *smash*).
  `Acotar β ψ`: el enunciado con `y ≤ β x`.
* `ParikhSana C Th`: `Th` (lo que la teoría demuestra) es **sana** (todo lo de `Th` es verdadero) y tiene la
  **propiedad de Parikh** para la clase `C` (si demuestra `ψ ∈ C`, demuestra `Acotar β ψ` para una `β` de largo
  polinomial).
* `denso_de_acotado`: una cota de largo polinomial verdadera para `Buenos L c k` da `Denso L c k a b`.
* `denso_de_parikh`, `psobrePoly_de_parikh`: si `Th` demuestra `Buenos L c k`, los largos buenos son densos y, si
  `L` es rellenable, `L ∈ P/poly`. Para SAT, `satBits_de_parikh` y su contrapositivo `no_demuestra_de_fuera`.
* `verdadero_buenos_iff`, `no_sobre_iff_verdadero`: `Buenos L c k` verdadero es exactamente «infinitos largos
  buenos para `c·(m+1)^k`»; la mitad «no está arriba» de la oscilación es `∃ c k, Verdadero (Buenos L c k)`.
* **`oscila_no_se_demuestra`**: si SAT oscila, ninguna teoría sana con Parikh demuestra `Buenos satMarco c k`, para
  ningún `c`, `k`. **`verdadero_no_demostrable`**: si SAT oscila, hay un `Buenos satMarco c k` verdadero que ninguna de
  esas teorías demuestra. **`no_oscila_de_demuestra`**: si una de ellas lo demuestra, SAT no oscila (y está en P/poly).

## 2. La versión concreta: S¹₂

* `EsAcotada`: las fórmulas acotadas del lenguaje de Buss (cuantificadores `∀ x ≤ t`, `∃ x ≤ t`, sin restricción de
  clase). `abs_acotada`: dicen lo mismo en una subestructura cerrada hacia abajo (la misma prueba de `abs_aguda`).
* **`parikh_existe`**: Parikh para `∀ x ∃ y φ` con `φ` acotada, **sin unicidad**. Es la prueba de
  `parikh_de_monotonas` (compacidad, el segmento de lo que acota un término es modelo de S¹₂), con `abs_acotada` en
  vez de `abs_formula`; `parikh` de `Parikh.lean` es la versión `∃!` con `φ` en `Σᵇ₁`.
* `cota_termino`: en ℕ, todo término `t(x)` tiene largo a lo sumo polinomial en `|x|`.
* `ThS12`: los `ψ` definidos en ℕ por una fórmula acotada `φ` con `S¹₂ ⊢ ∀ x ∃ y φ` (por modelos; con derivaciones
  formales es `demuestraExiste_iff`). **`parikhSana_S12`**: `ParikhSana univ ThS12`.
* **`s12_no_demuestra_oscila`**: si SAT oscila, para toda fórmula acotada `φ` que defina en ℕ a `Buenos satMarco c k`,
  `S¹₂ ⊬ ∀ x ∃ y φ` (`s12_no_deriva_oscila`, con el cálculo `Deriva`).

## Lo que no

* **La fórmula** ya no queda abierta (25 nov 2026, noche). Aquí `FormulaBuenos` sigue siendo la hipótesis de
  `s12_oscila_de_formula`, pero `Sagitta/Map/Borde/FormulaBuenosEnsamble.lean` la prueba para todo `c`, `k`
  (`FormulaBuenos.formulaBuenos`): una fórmula acotada, `Σᵇ₃` en forma, armada con tres piezas `Σᵇ₁` que salen de
  `Σᵇ₁ = NP` (la forma de un código de circuito, su evaluación y SAT enmarcado; `Sagitta/Map/Borde/FormulaBuenos.lean`).
  Con ella, `FormulaBuenos.s12_oscila_sin_hipotesis` y `t12_oscila_sin_hipotesis` dicen lo mismo sin la hipótesis, y
  `s12_no_demuestra_oscila` ya no puede ser vacío.
* `ThS12` es «lo que S¹₂ demuestra» restringido a la forma `∀ x ∃ y φ` con `φ` acotada. Para `T¹₂` está hecho en
  `Sagitta/Map/Borde/ParikhT12.lean` (25 nov, continuación), con la prueba de Parikh separada de la teoría; ahí se dice
  qué falta para PV.
* No se prueba que SAT oscile ni que no oscile. Tampoco el resto del teorema de Bydžovský–Krajíček–Oliveira (la
  consistencia de cotas inferiores, el colapso de Cook–Krajíček).
* Nada sobre P ≠ NP: para «SAT no tiene circuitos polinomiales» no se sabe nada parecido.
-/

open FirstOrder FirstOrder.Language Filter Set

namespace Sagitta.Map.Borde.OscilacionParikh

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Finitud
open Sagitta.Map.Tiempo.Relleno Sagitta.Map.Borde.Tricotomia
open Sagitta.Map.Borde.SatEnElBorde

/-! ## 1. La versión abstracta -/

/-- La matriz `ψ(x, y)` de un enunciado `∀ x ∃ y ψ(x, y)` sobre ℕ. -/
abbrev Enunciado := ℕ → ℕ → Prop

/-- `∀ x ∃ y ψ(x, y)` vale en ℕ. -/
def Verdadero (ψ : Enunciado) : Prop := ∀ x, ∃ y, ψ x y

/-- **Una función de largo polinomial**: `|f x| ≤ c·(|x|+1)^d`. Es lo que cumple un término de Buss (con *smash*). -/
def PolLargo (f : ℕ → ℕ) : Prop := ∃ c d, ∀ x, f x ≤ c * (Nat.size x + 1) ^ d

/-- **`β` acota con largo polinomial**: `|β x|` es a lo sumo polinomial en `|x|`. -/
def CotaPol (β : ℕ → ℕ) : Prop := PolLargo fun x => Nat.size (β x)

/-- El enunciado con la `y` acotada: `∀ x ∃ y ≤ β x, ψ(x, y)`. -/
def Acotar (β : ℕ → ℕ) (ψ : Enunciado) : Enunciado := fun x y => y ≤ β x ∧ ψ x y

/-- **Una teoría sana con la propiedad de Parikh**, vista por los `∀∃` que demuestra (`Th`). Sana: lo que demuestra es
verdadero en ℕ. Parikh, para la clase `C`: si demuestra `∀ x ∃ y ψ` con `ψ ∈ C`, también demuestra la versión con la `y`
acotada por una función de largo polinomial. -/
structure ParikhSana (C Th : Set Enunciado) : Prop where
  sana : ∀ ψ ∈ Th, Verdadero ψ
  parikh : ∀ ψ ∈ Th, ψ ∈ C → ∃ β, CotaPol β ∧ Acotar β ψ ∈ Th

/-- **«Los largos buenos no se acaban»**, como matriz: `|x| ≤ |y|` y el óptimo de `L` en el largo `|y|` no pasa de
`c·(|y|+1)^k`. `∀ x ∃ y Buenos` es la mitad «hay infinitos largos buenos» de la oscilación. -/
def Buenos (P : Problema) (c k : ℕ) : Enunciado := fun x y =>
  Nat.size x ≤ Nat.size y ∧ sucNat P (Nat.size y) ≤ c * (Nat.size y + 1) ^ k

theorem size_dos_pow (n : ℕ) : Nat.size (2 ^ n) = n + 1 := Nat.size_pow

theorem pow_dos_le (n d : ℕ) : (n + 2) ^ d ≤ 2 ^ d * (n + 1) ^ d := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d

/-- Todo largo es el largo de algún número. -/
theorem existe_size (m : ℕ) : ∃ y, Nat.size y = m := by
  cases m with
  | zero => exact ⟨0, Nat.size_zero⟩
  | succ k => exact ⟨2 ^ k, Nat.size_pow⟩

/-- **Una cota verdadera de largo polinomial da densidad.** Para el largo `n` se usa `x = 2^n` (de largo `n+1`); el `y`
que da la cota tiene largo bueno `m = |y|` entre `n` y `e·2^d·(n+1)^d`. -/
theorem denso_de_acotado {P : Problema} {c k : ℕ} {β : ℕ → ℕ} (hβ : CotaPol β)
    (h : Verdadero (Acotar β (Buenos P c k))) : ∃ a b, Denso P c k a b := by
  obtain ⟨e, d, he⟩ := hβ
  refine ⟨e * 2 ^ d, d, 0, fun n _ => ?_⟩
  obtain ⟨y, hyβ, hx, hy⟩ := h (2 ^ n)
  rw [size_dos_pow] at hx
  refine ⟨Nat.size y, by omega, ?_, hy⟩
  calc Nat.size y ≤ Nat.size (β (2 ^ n)) := Nat.size_le_size hyβ
    _ ≤ e * (Nat.size (2 ^ n) + 1) ^ d := he _
    _ = e * (n + 2) ^ d := by rw [size_dos_pow]
    _ ≤ e * (2 ^ d * (n + 1) ^ d) := Nat.mul_le_mul_left _ (pow_dos_le n d)
    _ = e * 2 ^ d * (n + 1) ^ d := by ring

/-- **Lo que una teoría sana con Parikh demuestra de los largos buenos, los hace densos.** -/
theorem denso_de_parikh {C Th : Set Enunciado} (hT : ParikhSana C Th) {P : Problema} {c k : ℕ}
    (hC : Buenos P c k ∈ C) (hD : Buenos P c k ∈ Th) : ∃ a b, Denso P c k a b := by
  obtain ⟨β, hβ, hA⟩ := hT.parikh _ hD hC
  exact denso_de_acotado hβ (hT.sana _ hA)

/-- **Con el relleno, P/poly.** -/
theorem psobrePoly_de_parikh {C Th : Set Enunciado} (hT : ParikhSana C Th) {P : Problema} (hP : Rellenable P)
    {c k : ℕ} (hC : Buenos P c k ∈ C) (hD : Buenos P c k ∈ Th) : P ∈ PsobrePoly := by
  obtain ⟨a, b, h⟩ := denso_de_parikh hT hC hD
  exact psobrePoly_de_denso hP h

/-- **Para SAT**: si una teoría sana con Parikh demuestra que los largos buenos de `satMarco` no se acaban, `satBits`
tiene circuitos polinomiales. -/
theorem satBits_de_parikh {C Th : Set Enunciado} (hT : ParikhSana C Th) {c k : ℕ}
    (hC : Buenos satMarco c k ∈ C) (hD : Buenos satMarco c k ∈ Th) : CookS12.satBits ∈ PsobrePoly := by
  obtain ⟨a, b, h⟩ := denso_de_parikh hT hC hD
  exact satBits_de_denso h

/-- **El contrapositivo**: si `satBits` no tiene circuitos polinomiales, ninguna teoría sana con Parikh demuestra que
los largos buenos de `satMarco` no se acaban. -/
theorem no_demuestra_de_fuera {C Th : Set Enunciado} (hT : ParikhSana C Th) (hs : CookS12.satBits ∉ PsobrePoly)
    {c k : ℕ} (hC : Buenos satMarco c k ∈ C) : Buenos satMarco c k ∉ Th :=
  fun hD => hs (satBits_de_parikh hT hC hD)

/-! ### `Buenos` es la mitad de la oscilación -/

/-- `∀ x ∃ y Buenos P c k` es «infinitos largos buenos para `c·(m+1)^k`». -/
theorem verdadero_buenos_iff {P : Problema} {c k : ℕ} :
    Verdadero (Buenos P c k) ↔ {m | sucNat P m ≤ c * (m + 1) ^ k}.Infinite := by
  constructor
  · intro h
    refine Set.infinite_of_forall_exists_gt fun a => ?_
    obtain ⟨y, hx, hy⟩ := h (2 ^ (a + 1))
    rw [size_dos_pow] at hx
    exact ⟨Nat.size y, hy, by omega⟩
  · intro h x
    obtain ⟨m, hm, hlt⟩ := h.exists_gt (Nat.size x)
    obtain ⟨y, rfl⟩ := existe_size m
    exact ⟨y, hlt.le, hm⟩

/-- **No estar arriba del borde es que algún `Buenos` sea verdadero.** -/
theorem no_sobre_iff_verdadero (P : Problema) :
    ¬ Sobre (sucNat P) ↔ ∃ c k, Verdadero (Buenos P c k) := by
  rw [no_sobre_iff_buenos]
  exact exists₂_congr fun c k => verdadero_buenos_iff.symm

/-- **El teorema.** Si SAT (enmarcado) oscila en circuitos, ninguna teoría sana con la propiedad de Parikh demuestra
que sus largos buenos no se acaban, para ningún polinomio. -/
theorem oscila_no_se_demuestra {C Th : Set Enunciado} (hT : ParikhSana C Th) (hO : Oscila (sucNat satMarco))
    {c k : ℕ} (hC : Buenos satMarco c k ∈ C) : Buenos satMarco c k ∉ Th := fun hD =>
  hO.1 ((bajo_sucNat_iff satMarco).2 (psobrePoly_de_parikh hT rellenable_satMarco hC hD))

/-- **Verdadero y no demostrable.** Si SAT oscila, hay un `c·(m+1)^k` para el que «los largos buenos no se acaban» es
verdadero, y ninguna teoría sana con Parikh (para una clase que lo contenga) lo demuestra. -/
theorem verdadero_no_demostrable (hO : Oscila (sucNat satMarco)) :
    ∃ c k, Verdadero (Buenos satMarco c k) ∧
      ∀ C Th : Set Enunciado, ParikhSana C Th → Buenos satMarco c k ∈ C → Buenos satMarco c k ∉ Th := by
  obtain ⟨c, k, hv⟩ := (no_sobre_iff_verdadero satMarco).1 hO.2
  exact ⟨c, k, hv, fun _ _ hT hC => oscila_no_se_demuestra hT hO hC⟩

/-- **Al revés**: si una teoría sana con Parikh demuestra que los largos buenos no se acaban, SAT no oscila; más aún,
`satBits` y `satMarco` están en P/poly. -/
theorem no_oscila_de_demuestra {C Th : Set Enunciado} (hT : ParikhSana C Th) {c k : ℕ}
    (hC : Buenos satMarco c k ∈ C) (hD : Buenos satMarco c k ∈ Th) :
    ¬ Oscila (sucNat satMarco) ∧ CookS12.satBits ∈ PsobrePoly ∧ satMarco ∈ PsobrePoly :=
  ⟨fun hO => oscila_no_se_demuestra hT hO hC hD, satBits_de_parikh hT hC hD,
    psobrePoly_de_parikh hT rellenable_satMarco hC hD⟩

/-! ## 2. La versión concreta: S¹₂ -/

section S12

open Sagitta.Map.Acotada Sagitta.Map.Acotada.Parikh

variable {α : Type}

/-- **Las fórmulas acotadas** del lenguaje de Buss: atómicas, `→`, `⊥`, y los cuantificadores `∀ x ≤ t`, `∃ x ≤ t`
con cualquier término. Contiene a `Σᵇ₁`, `Πᵇ₁` y toda la jerarquía `Σᵇᵢ`. -/
inductive EsAcotada : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | falso {n : ℕ} : EsAcotada (BoundedFormula.falsum : L.BoundedFormula α n)
  | igual {n : ℕ} (t u : L.Term (α ⊕ Fin n)) : EsAcotada (BoundedFormula.equal t u)
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      EsAcotada (BoundedFormula.rel R ts)
  | imp {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsAcotada φ → EsAcotada ψ → EsAcotada (φ.imp ψ)
  | todo {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsAcotada φ → EsAcotada (paraTodoAcotado t φ)
  | existe {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsAcotada φ → EsAcotada (existeAcotado t φ)

theorem EsAcotada.inf {n : ℕ} {φ ψ : L.BoundedFormula α n} (h1 : EsAcotada φ) (h2 : EsAcotada ψ) :
    EsAcotada (φ ⊓ ψ) :=
  .imp (.imp h1 (.imp h2 .falso)) .falso

/-- Una agudamente acotada es acotada. -/
theorem EsAcotada.de_aguda {n : ℕ} {φ : L.BoundedFormula α n} (h : EsAguda φ) : EsAcotada φ := by
  induction h with
  | falso => exact .falso
  | igual t u => exact .igual t u
  | rel R ts => exact .rel R ts
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | todoAgudo t _ ih => exact .todo _ ih
  | existeAgudo t _ ih => exact .existe _ ih

/-- **Las fórmulas acotadas dicen lo mismo en una subestructura cerrada hacia abajo.** -/
theorem abs_acotada {M : Type} [L.Structure M] {S : L.Substructure M}
    (hdown : ∀ y z : M, z ∈ S → le y z → y ∈ S) {n : ℕ} {φ : L.BoundedFormula α n} (hφ : EsAcotada φ) :
    ∀ (v : α → S) (xs : Fin n → S), φ.Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) ↔ φ.Realize v xs := by
  induction hφ with
  | falso => intro v xs; exact BoundedFormula.IsQF.falsum.realize_embedding S.subtype
  | igual t u => intro v xs; exact (BoundedFormula.IsAtomic.equal t u).isQF.realize_embedding S.subtype
  | rel R ts => intro v xs; exact (BoundedFormula.IsAtomic.rel R ts).isQF.realize_embedding S.subtype
  | imp _ _ ih1 ih2 => intro v xs; rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, ih1, ih2]
  | todo t _ ih => exact abs_todo hdown ih
  | existe t _ ih => exact abs_existe hdown ih

theorem abs_formula_acotada {M : Type} [L.Structure M] {S : L.Substructure M}
    (hdown : ∀ y z : M, z ∈ S → le y z → y ∈ S) {φ : L.Formula α} (hφ : EsAcotada φ) (v : α → S) :
    φ.Realize (Subtype.val ∘ v) ↔ φ.Realize v := by
  have := abs_acotada hdown hφ v default
  rw [Subsingleton.elim (Subtype.val ∘ (default : Fin 0 → S)) default] at this
  exact this

/-- **Parikh para `∀ x ∃ y φ` con `φ` acotada, sin unicidad.** Si en todo modelo de S¹₂ cada `x` tiene una `y` con
`φ(x, y)`, hay un término `t` tal que en todo modelo de S¹₂ cada `x` tiene una con `y ≤ t(x)`. La prueba es la de
`parikh_de_monotonas`: por compacidad, un `c` sin salida bajo ningún término; el segmento de lo que acotan los términos
de `c` es modelo de S¹₂ (`segmento_S12`, con `monotonas`), da una salida para `c`, y la salida está bajo un término. -/
theorem parikh_existe {φ : L.Formula (Fin 2)} (hφ : EsAcotada φ)
    (htot : ∀ (M : Type) [L.Structure M], EsModeloS12 M → ∀ x : M, ∃ y : M, φ.Realize ![x, y]) :
    ∃ t : L.Term (Fin 1), ∀ (M : Type) [L.Structure M], EsModeloS12 M →
      ∀ x : M, ∃ y : M, le y (t.realize ![x]) ∧ φ.Realize ![x, y] := by
  by_contra hno
  push Not at hno
  obtain ⟨N, _, hN, c, hc⟩ := existe_c_sin_cota φ fun t => by
    obtain ⟨N, i, hN, x, hx⟩ := hno t
    exact ⟨N, i, hN, x, fun y hy hφy => hx y hy hφy⟩
  have hm := monotonas hN
  set S := segmento hN.basic hm c
  have hdown : ∀ y z : N, z ∈ S → le y z → y ∈ S := fun _ _ hz hyz => segmento_abajo hN.basic hm c hz hyz
  have hSS := segmento_S12 hN hm c
  let cS : S := ⟨c, c_mem_segmento hN.basic hm c⟩
  obtain ⟨y, hy⟩ := htot S hSS cS
  have hyN : φ.Realize ![c, (y : N)] := by
    have := (abs_formula_acotada hdown hφ ![cS, y]).2 hy
    rwa [show (Subtype.val ∘ ![cS, y] : Fin 2 → N) = ![c, (y : N)] from by
      funext i; match i with | 0 => rfl | 1 => rfl] at this
  obtain ⟨t, ht⟩ := (mem_segmento.1 y.2 : ∃ t : L.Term (Fin 1), le (y : N) (t.realize ![c]))
  exact hc t y ht hyN

/-! ### Los términos tienen largo polinomial en ℕ -/

theorem size_succ_le (n : ℕ) : Nat.size (n + 1) ≤ Nat.size n + 1 := by
  rw [Nat.size_le]; have := Nat.lt_size_self n; rw [pow_succ]; omega

theorem size_add_le (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  rw [Nat.size_le]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2 ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_succ]; omega

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_size_le (a : ℕ) : Nat.size (Nat.size a) ≤ Nat.size a :=
  Nat.size_le.2 Nat.lt_two_pow_self

theorem polLargo_mono {f g : ℕ → ℕ} (h : ∀ x, f x ≤ g x) (hg : PolLargo g) : PolLargo f := by
  obtain ⟨c, d, hc⟩ := hg
  exact ⟨c, d, fun x => (h x).trans (hc x)⟩

theorem polLargo_const (k : ℕ) : PolLargo fun _ => k := ⟨k, 0, fun _ => by simp⟩

theorem polLargo_size : PolLargo Nat.size := ⟨1, 1, fun _ => by simp⟩

theorem polLargo_add {f g : ℕ → ℕ} (hf : PolLargo f) (hg : PolLargo g) : PolLargo fun x => f x + g x := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 + c2, d1 + d2, fun x => ?_⟩
  change f x + g x ≤ _
  have e1 : (Nat.size x + 1) ^ d1 ≤ (Nat.size x + 1) ^ (d1 + d2) := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (Nat.size x + 1) ^ d2 ≤ (Nat.size x + 1) ^ (d1 + d2) := Nat.pow_le_pow_right (by omega) (by omega)
  have := h1 x; have := h2 x
  have := Nat.mul_le_mul_left c1 e1; have := Nat.mul_le_mul_left c2 e2
  rw [add_mul]; omega

theorem polLargo_mul {f g : ℕ → ℕ} (hf : PolLargo f) (hg : PolLargo g) : PolLargo fun x => f x * g x := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 * c2, d1 + d2, fun x => ?_⟩
  calc f x * g x ≤ (c1 * (Nat.size x + 1) ^ d1) * (c2 * (Nat.size x + 1) ^ d2) := Nat.mul_le_mul (h1 x) (h2 x)
    _ = c1 * c2 * (Nat.size x + 1) ^ (d1 + d2) := by ring

/-- **En ℕ, un término de Buss tiene largo polinomial** en el de su variable. El *smash* es lo que lleva el grado:
`|x # y| = |x|·|y| + 1`. -/
theorem cota_termino (t : L.Term (Fin 1)) : CotaPol fun x => t.realize ![x] := by
  unfold CotaPol
  induction t with
  | var i =>
    refine polLargo_mono (fun x => ?_) polLargo_size
    rw [Fin.fin_one_eq_zero i]; rfl
  | func f ts ih =>
    cases f with
    | cero => exact polLargo_mono (fun x => by change Nat.size 0 ≤ 0; simp) (polLargo_const 0)
    | suc =>
      exact polLargo_mono (fun x => size_succ_le ((ts 0).realize ![x])) (polLargo_add (ih 0) (polLargo_const 1))
    | long =>
      exact polLargo_mono (fun x => size_size_le ((ts 0).realize ![x])) (ih 0)
    | mitad =>
      exact polLargo_mono (fun x => Nat.size_le_size (Nat.div_le_self ((ts 0).realize ![x]) 2)) (ih 0)
    | suma =>
      exact polLargo_mono (fun x => size_add_le ((ts 0).realize ![x]) ((ts 1).realize ![x]))
        (polLargo_add (polLargo_add (ih 0) (ih 1)) (polLargo_const 1))
    | prod =>
      exact polLargo_mono (fun x => size_mul_le ((ts 0).realize ![x]) ((ts 1).realize ![x]))
        (polLargo_add (ih 0) (ih 1))
    | smash =>
      refine polLargo_mono (fun x => ?_) (polLargo_add (polLargo_mul (ih 0) (ih 1)) (polLargo_const 1))
      change Nat.size (2 ^ (Nat.size ((ts 0).realize ![x]) * Nat.size ((ts 1).realize ![x]))) ≤ _
      rw [Nat.size_pow]

/-! ### Lo que S¹₂ demuestra, como teoría abstracta -/

/-- `φ(x, y)` define en ℕ la matriz `ψ`. -/
def Define (φ : L.Formula (Fin 2)) (ψ : Enunciado) : Prop := ∀ x y : ℕ, φ.Realize ![x, y] ↔ ψ x y

/-- **`S¹₂ ⊢ ∀ x ∃ y φ(x, y)`**, por modelos (`demuestraExiste_iff` lo pasa a derivaciones). -/
def DemuestraExiste (φ : L.Formula (Fin 2)) : Prop :=
  ∀ (M : Type) [L.Structure M], EsModeloS12 M → ∀ x : M, ∃ y : M, φ.Realize ![x, y]

/-- **Lo que S¹₂ demuestra**, en la forma `∀ x ∃ y φ` con `φ` acotada, leído en ℕ. -/
def ThS12 : Set Enunciado := {ψ | ∃ φ : L.Formula (Fin 2), EsAcotada φ ∧ Define φ ψ ∧ DemuestraExiste φ}

/-- La fórmula `y ≤ t(x) ∧ φ(x, y)`. -/
def acotF (φ : L.Formula (Fin 2)) (t : L.Term (Fin 1)) : L.Formula (Fin 2) :=
  leF (Term.var (Sum.inl 1)) (t.relabel fun _ => Sum.inl 0) ⊓ φ

theorem esAcotada_acotF {φ : L.Formula (Fin 2)} (hφ : EsAcotada φ) (t : L.Term (Fin 1)) :
    EsAcotada (acotF φ t) :=
  EsAcotada.inf (.rel _ _) hφ

theorem realize_acotF {M : Type} [L.Structure M] (φ : L.Formula (Fin 2)) (t : L.Term (Fin 1)) (x y : M) :
    (acotF φ t).Realize ![x, y] ↔ le y (t.realize ![x]) ∧ φ.Realize ![x, y] := by
  rw [acotF, Formula.Realize, BoundedFormula.realize_inf, realize_leF]
  have e : (Sum.elim ![x, y] (default : Fin 0 → M) ∘ fun _ : Fin 1 => (Sum.inl 0 : Fin 2 ⊕ Fin 0)) = ![x] := by
    funext i; fin_cases i; rfl
  simp only [Term.realize_var, Sum.elim_inl, Term.realize_relabel, e]
  rfl

/-- **S¹₂ es una teoría sana con la propiedad de Parikh** (para toda la clase): sana porque ℕ es modelo de S¹₂, y
Parikh por `parikh_existe` y `cota_termino`. -/
theorem parikhSana_S12 : ParikhSana Set.univ ThS12 where
  sana := by
    rintro ψ ⟨φ, -, hdef, hdem⟩ x
    obtain ⟨y, hy⟩ := hdem ℕ nat_esModeloS12 x
    exact ⟨y, (hdef x y).1 hy⟩
  parikh := by
    rintro ψ ⟨φ, hφ, hdef, hdem⟩ -
    obtain ⟨t, ht⟩ := parikh_existe hφ hdem
    refine ⟨fun x => t.realize ![x], cota_termino t, acotF φ t, esAcotada_acotF hφ t, fun x y => ?_,
      fun M _ hM x => ?_⟩
    · rw [realize_acotF, hdef]; rfl
    · obtain ⟨y, hle, hy⟩ := ht M hM x
      exact ⟨y, (realize_acotF φ t x y).2 ⟨hle, hy⟩⟩

/-- **Con S¹₂.** Si SAT (enmarcado) oscila en circuitos, ninguna fórmula acotada que defina en ℕ «los largos buenos
de `satMarco` para `c·(m+1)^k`» tiene `S¹₂ ⊢ ∀ x ∃ y φ`. -/
theorem s12_no_demuestra_oscila (hO : Oscila (sucNat satMarco)) (c k : ℕ) {φ : L.Formula (Fin 2)}
    (hφ : EsAcotada φ) (hdef : Define φ (Buenos satMarco c k)) : ¬ DemuestraExiste φ := fun hdem =>
  oscila_no_se_demuestra parikhSana_S12 hO (Set.mem_univ _) ⟨φ, hφ, hdef, hdem⟩

/-- `∃ y φ(x, y)`, con `x` libre. -/
noncomputable def existeY (φ : L.Formula (Fin 2)) : L.Formula (Fin 1) :=
  Formula.iExs (Fin 1) (φ.relabel Acotada.xy)

/-- **Por modelos es por derivaciones**: `DemuestraExiste φ` es `S¹₂ ⊢ ∀ x ∃ y φ(x, y)` en el cálculo `Deriva`. -/
theorem demuestraExiste_iff (φ : L.Formula (Fin 2)) :
    DemuestraExiste φ ↔ DerivaS12 (cierre (existeY φ)) := by
  rw [← deriva_formula_iff]
  refine forall_congr' fun M => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [forall_fin1]
  refine forall_congr' fun x => ?_
  rw [existeY, Formula.Realize, BoundedFormula.realize_iExs]
  simp only [Formula.realize_relabel, comp_xy]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨![y], hy⟩
  · rintro ⟨i, hi⟩; exact ⟨i 0, hi⟩

/-- **Con derivaciones formales**: si SAT oscila, `S¹₂ ⊬ ∀ x ∃ y φ` para toda fórmula acotada `φ` que defina los
largos buenos de `satMarco`. -/
theorem s12_no_deriva_oscila (hO : Oscila (sucNat satMarco)) (c k : ℕ) {φ : L.Formula (Fin 2)}
    (hφ : EsAcotada φ) (hdef : Define φ (Buenos satMarco c k)) : ¬ DerivaS12 (cierre (existeY φ)) := by
  rw [← demuestraExiste_iff]; exact s12_no_demuestra_oscila hO c k hφ hdef

/-- **La fórmula.** Hay una fórmula acotada del lenguaje de Buss que define en ℕ «`|x| ≤ |y|` y SAT enmarcado tiene en
el largo `|y|` un circuito de tamaño `≤ c·(|y|+1)^k`». La usa el artículo de Bydžovský, Krajíček y Oliveira; aquí queda
como enunciado, y `FormulaBuenos.formulaBuenos` (en `Sagitta/Map/Borde/FormulaBuenosEnsamble.lean`) lo prueba para todo `c`,
`k`, con lo que `s12_oscila_de_formula` vale sin hipótesis (`FormulaBuenos.s12_oscila_sin_hipotesis`). -/
def FormulaBuenos (c k : ℕ) : Prop := ∃ φ : L.Formula (Fin 2), EsAcotada φ ∧ Define φ (Buenos satMarco c k)

/-- **Condicionado a la fórmula**: si SAT oscila, con `c`, `k` que tengan infinitos largos buenos, hay una fórmula
acotada verdadera en ℕ (`∀ x ∃ y φ`) que S¹₂ no deriva. -/
theorem s12_oscila_de_formula (hO : Oscila (sucNat satMarco)) (hF : ∀ c k, FormulaBuenos c k) :
    ∃ φ : L.Formula (Fin 2), EsAcotada φ ∧ (∀ x : ℕ, ∃ y : ℕ, φ.Realize ![x, y]) ∧
      ¬ DerivaS12 (cierre (existeY φ)) := by
  obtain ⟨c, k, hv⟩ := (no_sobre_iff_verdadero satMarco).1 hO.2
  obtain ⟨φ, hφ, hdef⟩ := hF c k
  refine ⟨φ, hφ, fun x => ?_, s12_no_deriva_oscila hO c k hφ hdef⟩
  obtain ⟨y, hy⟩ := hv x
  exact ⟨y, (hdef x y).2 hy⟩

end S12

/-! ## Controles -/

section Controles

/-- **La hipótesis no es vacía**: la «teoría» de los `∀∃` que tienen testigo de largo polinomial es sana y tiene Parikh
para toda la clase. -/
def ThPol : Set Enunciado := {ψ | ∃ β, CotaPol β ∧ Verdadero (Acotar β ψ)}

theorem parikhSana_ThPol : ParikhSana Set.univ ThPol where
  sana := by
    rintro ψ ⟨β, -, h⟩ x
    obtain ⟨y, -, hy⟩ := h x
    exact ⟨y, hy⟩
  parikh := by
    rintro ψ ⟨β, hβ, h⟩ -
    refine ⟨β, hβ, β, hβ, fun x => ?_⟩
    obtain ⟨y, hyβ, hy⟩ := h x
    exact ⟨y, hyβ, hyβ, hy⟩

/-- **Sin la sana no sale.** Todo enunciado, como teoría, tiene la propiedad de Parikh (con `β = id`, que acota con
largo polinomial), y contiene «los largos buenos de `espaciado` no se acaban», que es incluso verdadero; pero
`espaciado` es rellenable y no está en P/poly (`control_densidad`). -/
theorem control_sin_sana :
    (∀ ψ ∈ (Set.univ : Set Enunciado), ψ ∈ (Set.univ : Set Enunciado) →
        ∃ β, CotaPol β ∧ Acotar β ψ ∈ (Set.univ : Set Enunciado)) ∧
      ¬ (∀ ψ ∈ (Set.univ : Set Enunciado), Verdadero ψ) ∧
      Rellenable espaciado ∧ Buenos espaciado 1 1 ∈ (Set.univ : Set Enunciado) ∧ espaciado ∉ PsobrePoly := by
  refine ⟨fun ψ _ _ => ⟨id, ⟨1, 1, fun x => by simp⟩, Set.mem_univ _⟩, fun h => ?_, control_densidad.1,
    Set.mem_univ _, control_densidad.2.2⟩
  obtain ⟨y, hy⟩ := h (fun _ _ => False) (Set.mem_univ _) 0
  exact hy

/-- **Sin Parikh no sale.** La teoría de todas las verdades es sana y contiene «los largos buenos de `espaciado` no se
acaban» (es verdadero: infinitos largos buenos), pero no tiene la propiedad de Parikh: si la tuviera, `espaciado`
estaría en P/poly. -/
theorem control_sin_parikh : ¬ ParikhSana Set.univ {ψ | Verdadero ψ} := fun hT =>
  control_densidad.2.2 (psobrePoly_de_parikh hT control_densidad.1 (Set.mem_univ _)
    (verdadero_buenos_iff.2 control_densidad.2.1))

/-- La cota de `denso_de_acotado` es la que sale: con `β = id`, para `Buenos` de un problema con óptimo `≤ 1` en todo
largo, la densidad sale con `a = 1·2^1`, `b = 1`. -/
example {P : Problema} (h : ∀ m, sucNat P m ≤ 1) : ∃ a b, Denso P 1 0 a b :=
  denso_de_acotado (β := id) ⟨1, 1, fun x => by simp⟩ fun x => ⟨x, le_rfl, le_rfl, by simpa using h _⟩

/-- `Buenos` en ℕ: `x = 2^n` tiene largo `n+1`. -/
example : Nat.size (2 ^ 3) = 4 := size_dos_pow 3

section ControlS12

open Sagitta.Map.Acotada Sagitta.Map.Acotada.Parikh

/-- **`ThS12` no es vacía**: S¹₂ demuestra `∀ x ∃ y (x ≤ y)` (con `y = x`, por el axioma de reflexividad que da
`le_refl'`). Por `parikhSana_S12`, la `y` se acota por un término, como debe. -/
theorem control_ThS12 : (fun x y : ℕ => x ≤ y) ∈ ThS12 :=
  ⟨leF (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1)), .rel _ _,
    fun x y => by rw [Formula.Realize, realize_leF]; exact Iff.rfl,
    fun M _ hM x => ⟨x, by rw [Formula.Realize, realize_leF]; exact le_refl' hM.basic x⟩⟩

end ControlS12

/- Mutantes probados (25 nov 2026, en /tmp/claude-noche):
* `MutOsc1.lean`: el campo `sana` debilitado a «vale para algún `x`» (`∃ x ∃ y, ψ x y`). `denso_de_parikh` deja de
  compilar (y con él los controles que lo usan): la cota `Acotar β ψ ∈ Th` ya no dice nada de cada largo, y
  `denso_de_acotado` pide que sea verdadera para todo `x`.
* `MutOsc2.lean`: `EsAcotada` con un constructor más, `todoLibre` (`∀ x` sin cota). `abs_acotada` deja de compilar
  (falta ese caso, y no hay `abs_todo` para él): un `∀` sin cota no baja al segmento, y sin eso `parikh_existe` no se
  sigue. -/

end Controles

end Sagitta.Map.Borde.OscilacionParikh
