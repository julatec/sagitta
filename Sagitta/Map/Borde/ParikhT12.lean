import Sagitta.Map.Borde.OscilacionParikh
import Sagitta.Map.T12
import Sagitta.Map.Arranque2

/-!
# La oscilación tampoco se demuestra en T¹₂

`OscilacionParikh.lean` dejó dicho: «para `T¹₂` u otra teoría acotada, la prueba de `parikh_existe` sirve igual si el
segmento es modelo de esa teoría; no se hace». Aquí se hace para T¹₂, y se separa la prueba de Parikh de la teoría:
qué tiene que cumplir una clase de modelos para que el argumento corra.

## Lo que se prueba

* **`existe_c_sin_cota_de`**: la compacidad de `Parikh.existe_c_sin_cota`, para cualquier clase de modelos `P` que sea
  la de los modelos de una teoría de primer orden `T` (`M ⊨ T ↔ P M`) y cuyos modelos cumplan BASIC.
* **`parikh_existe_de`**: Parikh sin unicidad para `∀ x ∃ y φ` con `φ` acotada (`EsAcotada`), para toda clase `P` con
  tres propiedades: (1) axiomatizada por una teoría (compacidad), (2) sus modelos cumplen BASIC y tienen las funciones
  monótonas (`Monotonas`), (3) el segmento de lo que acotan los términos de `c` vuelve a estar en `P`. Es la prueba de
  `OscilacionParikh.parikh_existe`, con la teoría como parámetro. `parikh_existe_S12` la recupera para S¹₂.
* **`segmento_T12`**: el segmento de un modelo de T¹₂ es modelo de T¹₂. La misma idea que `Parikh.segmento_S12`:
  la inducción se hace en el modelo grande sobre `x ≤ w → φ(x)`, que es `Σᵇ₁`, y el paso de `x` a `x+1` no sale del
  segmento porque `x ≤ x+1 ≤ w` y el segmento es cerrado hacia abajo.
* `monotonas_T12`: con `Arranque2.t12ContieneS12` (T¹₂ demuestra S¹₂) y `Parikh.monotonas`.
* **`parikh_existe_T12`**, `ThT12`, **`parikhSana_T12`**: T¹₂ es sana y tiene Parikh para toda la clase.
  `thS12_sub_thT12`: lo que S¹₂ demuestra lo demuestra T¹₂.
* **`t12_no_demuestra_oscila`**: si SAT oscila, ninguna fórmula acotada que defina en ℕ `Buenos satMarco c k` tiene
  `T¹₂ ⊢ ∀ x ∃ y φ`. Es el caso `T¹₂` del teorema 1.1 de Bydžovský–Krajíček–Oliveira (2020), que el artículo enuncia
  para `S¹₂` y `T¹₂` (no es una observación propia).

## Lo que no

* **`FormulaBuenos`** sigue abierta, igual que en `OscilacionParikh.lean`: sin la fórmula, el teorema podría ser vacío.
* **PV** no se hace, y no por la prueba: el lenguaje de Sagitta es el de Buss (`0, S, |·|, ⌊·/2⌋, +, ·, #, ≤`) y PV
  tiene un símbolo para cada función de tiempo polinomial (Cook 1975). Faltan, en este orden: el lenguaje de PV y sus
  axiomas (las ecuaciones de las definiciones por recursión limitada sobre notación); `cota_termino` para los términos
  de PV (cada función de PV tiene salida de largo polinomial: sale de la recursión limitada); y la cerradura del
  segmento, que con PV es distinta: las funciones de PV no son monótonas, así que el segmento no es cerrado por ellas
  sin más; hay que usar que PV demuestra `f(x) ≤ t(x)` para un término de Buss `t` (las cotas de la recursión
  limitada). Por otro lado PV es universal: toda subestructura de un modelo es modelo, así que la tercera condición
  de `parikh_existe_de` es gratis una vez que el segmento es subestructura. Para un `∀ x ∃ y φ` con `φ` abierta, la
  vía corta es Herbrand: PV da un término testigo directamente.
* No se prueba nada sobre `S²₂`, `T²₂` ni más arriba: la prueba sirve igual (el segmento es modelo de cualquier teoría
  de inducción acotada), pero cada una pide su `EsModelo` y su teoría de Mathlib, que no están en el repo.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map.Borde.ParikhT12

open Sagitta.Map Sagitta.Map.Acotada Sagitta.Map.Acotada.Parikh
open Sagitta.Map.Borde.OscilacionParikh Sagitta.Map.Borde.SatEnElBorde
open Sagitta.Map.Borde.Tricotomia Sagitta.Map.Tiempo.Relleno

/-! ## 1. Compacidad y Parikh, con la teoría como parámetro -/

section Abstracto

variable (P : ∀ (M : Type) [L.Structure M], Prop) (T : L.Theory)

/-- **Compacidad, para una clase axiomatizada.** Si para cada término hay un modelo en `P` con un `x` sin salida bajo
ese término, hay uno con un `c` sin salida bajo **ningún** término. Es `Parikh.existe_c_sin_cota` con `T` en lugar de
`S12`. -/
theorem existe_c_sin_cota_de (hT : ∀ (M : Type) [L.Structure M], M ⊨ T ↔ P M)
    (hb : ∀ (M : Type) [L.Structure M], P M → EsModeloBASIC M) (φ : L.Formula (Fin 2))
    (hno : ∀ t : L.Term (Fin 1), ∃ (N : Type) (_ : L.Structure N), P N ∧
      ∃ x : N, ∀ y : N, le y (t.realize ![x]) → ¬ φ.Realize ![x, y]) :
    ∃ (N : Type) (_ : L.Structure N), P N ∧
      ∃ c : N, ∀ (t : L.Term (Fin 1)) (y : N), le y (t.realize ![c]) → ¬ φ.Realize ![c, y] := by
  classical
  let T' : L[[Fin 1]].Theory :=
    (L.lhomWithConstants (Fin 1)).onTheory T ∪ Set.range fun t => Formula.equivSentence (sinCota φ t)
  have hfin : T'.IsFinitelySatisfiable := by
    intro T0 hT0
    let F : Finset (L.Term (Fin 1)) := T0.biUnion fun σ =>
      if hσ : ∃ t, Formula.equivSentence (sinCota φ t) = σ then {hσ.choose} else ∅
    obtain ⟨N, _, hN, x, hx⟩ := hno (sumaTerminos F.toList)
    let _ : (constantsOn (Fin 1)).Structure N := constantsOn.structure fun _ => x
    have : Nonempty N := ⟨x⟩
    have hS : N ⊨ T := (hT N).2 hN
    have hT' : N ⊨ (L.lhomWithConstants (Fin 1)).onTheory T :=
      (LHom.onTheory_model (L.lhomWithConstants (Fin 1)) T).mpr hS
    have hM : N ⊨ (↑T0 : L[[Fin 1]].Theory) := by
      refine (Theory.model_iff _).mpr fun σ hσ => ?_
      rcases hT0 hσ with hσ' | hσ'
      · exact Theory.realize_sentence_of_mem _ hσ'
      · have hex : ∃ t, Formula.equivSentence (sinCota φ t) = σ := hσ'
        have htF : hex.choose ∈ F := by
          simp only [F, Finset.mem_biUnion]
          exact ⟨σ, hσ, by simp only [hex, ↓reduceDIte]; exact Finset.mem_singleton_self _⟩
        rw [← hex.choose_spec, Formula.realize_equivSentence]
        have hv : (fun a : Fin 1 => (L.con a : N)) = ![x] := by funext a; match a with | 0 => rfl
        rw [hv, realize_sinCota]
        intro y hy
        exact hx y ((hb N hN).b8 _ _ _ hy
          (le_sumaTerminos (hb N hN) x _ _ (Finset.mem_toList.2 htF)))
    exact ⟨Theory.ModelType.of _ N⟩
  obtain ⟨N⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfin
  let _ : L.Structure N := (L.lhomWithConstants (Fin 1)).reduct N
  have hS : N ⊨ T :=
    (LHom.onTheory_model (L.lhomWithConstants (Fin 1)) T).mp (Theory.Model.mono N.is_model Set.subset_union_left)
  refine ⟨N, inferInstance, (hT N).1 hS, (L.con (0 : Fin 1) : N), fun t y hy => ?_⟩
  have hσ : N ⊨ Formula.equivSentence (sinCota φ t) := Theory.realize_sentence_of_mem T' (Or.inr ⟨t, rfl⟩)
  rw [Formula.realize_equivSentence] at hσ
  have hv : (fun a : Fin 1 => (L.con a : N)) = ![(L.con (0 : Fin 1) : N)] := by
    funext a; match a with | 0 => rfl
  rw [hv, realize_sinCota] at hσ
  exact hσ y hy

/-- **Parikh sin unicidad, para toda clase que cumpla las tres condiciones**: axiomatizada (`hT`), con BASIC y
funciones monótonas (`hb`, `hmon`), y cerrada por segmentos (`hseg`). -/
theorem parikh_existe_de (hT : ∀ (M : Type) [L.Structure M], M ⊨ T ↔ P M)
    (hb : ∀ (M : Type) [L.Structure M], P M → EsModeloBASIC M)
    (hmon : ∀ (M : Type) [L.Structure M], P M → Monotonas M)
    (hseg : ∀ (M : Type) [L.Structure M] (hM : P M) (c : M), P (segmento (hb M hM) (hmon M hM) c))
    {φ : L.Formula (Fin 2)} (hφ : EsAcotada φ)
    (htot : ∀ (M : Type) [L.Structure M], P M → ∀ x : M, ∃ y : M, φ.Realize ![x, y]) :
    ∃ t : L.Term (Fin 1), ∀ (M : Type) [L.Structure M], P M →
      ∀ x : M, ∃ y : M, le y (t.realize ![x]) ∧ φ.Realize ![x, y] := by
  by_contra hno
  push Not at hno
  obtain ⟨N, _, hN, c, hc⟩ := existe_c_sin_cota_de P T hT hb φ fun t => by
    obtain ⟨N, i, hN, x, hx⟩ := hno t
    exact ⟨N, i, hN, x, fun y hy hφy => hx y hy hφy⟩
  set S := segmento (hb N hN) (hmon N hN) c
  have hdown : ∀ y z : N, z ∈ S → le y z → y ∈ S := fun _ _ hz hyz =>
    segmento_abajo (hb N hN) (hmon N hN) c hz hyz
  have hSS := hseg N hN c
  let cS : S := ⟨c, c_mem_segmento (hb N hN) (hmon N hN) c⟩
  obtain ⟨y, hy⟩ := htot S hSS cS
  have hyN : φ.Realize ![c, (y : N)] := by
    have := (abs_formula_acotada hdown hφ ![cS, y]).2 hy
    rwa [show (Subtype.val ∘ ![cS, y] : Fin 2 → N) = ![c, (y : N)] from by
      funext i; match i with | 0 => rfl | 1 => rfl] at this
  obtain ⟨t, ht⟩ := (mem_segmento.1 y.2 : ∃ t : L.Term (Fin 1), le (y : N) (t.realize ![c]))
  exact hc t y ht hyN

end Abstracto

/-- **S¹₂ cumple las tres condiciones** (`modelo_S12_iff`, `monotonas`, `segmento_S12`): se recupera
`OscilacionParikh.parikh_existe`. -/
theorem parikh_existe_S12 {φ : L.Formula (Fin 2)} (hφ : EsAcotada φ)
    (htot : ∀ (M : Type) [L.Structure M], EsModeloS12 M → ∀ x : M, ∃ y : M, φ.Realize ![x, y]) :
    ∃ t : L.Term (Fin 1), ∀ (M : Type) [L.Structure M], EsModeloS12 M →
      ∀ x : M, ∃ y : M, le y (t.realize ![x]) ∧ φ.Realize ![x, y] :=
  parikh_existe_de (fun M _ => EsModeloS12 M) S12 modelo_S12_iff (fun _ _ hM => hM.basic)
    (fun _ _ hM => monotonas hM) (fun _ _ hM c => segmento_S12 hM (monotonas hM) c) hφ htot

/-! ## 2. El segmento de un modelo de T¹₂ es modelo de T¹₂ -/

section SegmentoT12

variable {M : Type} [L.Structure M]

theorem coe_suc (S : L.Substructure M) (x : S) : ((suc x : S) : M) = suc (x : M) := by
  change Structure.funMap (L := L) (Fun.suc : L.Functions 1) (fun i => ((![x] i : S) : M)) =
    Structure.funMap (L := L) (Fun.suc : L.Functions 1) ![(x : M)]
  congr 1; funext i; match i with | 0 => rfl

/-- **El segmento de `c` es modelo de T¹₂.** BASIC pasa por universal; IND, por la fórmula `x ≤ w → φ(x)` en el
modelo grande: el paso de `x` a `x + 1` con `x + 1 ≤ w` tiene `x ≤ w`, así que `x` está en el segmento. -/
theorem segmento_T12 (hM : EsModeloT12 M) (hm : Monotonas M) (c : M) :
    EsModeloT12 (segmento hM.basic hm c) := by
  set S := segmento hM.basic hm c
  have hdown : ∀ y z : M, z ∈ S → le y z → y ∈ S := fun _ _ hz hyz => segmento_abajo hM.basic hm c hz hyz
  refine ⟨basic_subestructura hM.basic S, ?_⟩
  intro k φ hφ v h0 hpaso w
  let φ' : L.Formula (Fin (k + 2)) := φ.subst (fun i => Term.var (Fin.castSucc i))
  let ψ : L.Formula (Fin (k + 2)) :=
    (Relations.formula₂ (Rel.le : L.Relations 2) (Term.var 0) (Term.var (Fin.last (k + 1)))).imp φ'
  have hψ : EsSigma1 ψ := .imp (.aguda (.rel _ _)) (hφ.subst _)
  let u : Fin (k + 1) → M := Fin.snoc (Subtype.val ∘ v) (w : M)
  have hcons : ∀ x : M, (fun i : Fin (k + 1) => ((Fin.cons x u : Fin (k + 2) → M) (Fin.castSucc i))) =
      Fin.cons x (Subtype.val ∘ v) := by
    intro x; funext i
    refine Fin.cases rfl (fun j => ?_) i
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
    simp only [u, Fin.snoc_castSucc]
  have hlast : ∀ x : M, (Fin.cons x u : Fin (k + 2) → M) (Fin.last (k + 1)) = (w : M) := by
    intro x; rw [← Fin.succ_last, Fin.cons_succ]; simp only [u, Fin.snoc_last]
  have hψr : ∀ x : M, ψ.Realize (Fin.cons x u) ↔ (le x (w : M) → φ.Realize (Fin.cons x (Subtype.val ∘ v))) := by
    intro x
    simp only [ψ, φ', Formula.realize_imp, Formula.realize_rel₂, Term.realize_var, formula_realize_subst]
    rw [hcons x, hlast x, Fin.cons_zero]
    rfl
  have habs : ∀ y : S, φ.Realize (Fin.cons (y : M) (Subtype.val ∘ v)) ↔ φ.Realize (Fin.cons y v) := by
    intro y
    rw [← Fin.comp_cons]
    exact abs_formula hdown hφ (Fin.cons y v)
  have key := hM.ind (k + 1) ψ hψ u ((hψr cero).2 fun _ => by
      have := (habs cero).2 h0
      rwa [coe_cero] at this) (fun x hx => by
      rw [hψr] at hx ⊢
      intro hxw
      -- `x ≤ x + 1 ≤ w`: `x` está en el segmento.
      have hxw' : le x (w : M) := hM.basic.b8 _ _ _ (le_suc hM.basic x) hxw
      have hxS : x ∈ S := hdown x w w.2 hxw'
      have h1 : φ.Realize (Fin.cons (⟨x, hxS⟩ : S) v) := (habs ⟨x, hxS⟩).1 (hx hxw')
      have h2 := hpaso _ h1
      rw [← habs, coe_suc] at h2
      exact h2) (w : M)
  exact (habs w).1 ((hψr w).1 key (le_refl' hM.basic _))

end SegmentoT12

theorem monotonas_T12 {M : Type} [L.Structure M] (hM : EsModeloT12 M) : Monotonas M :=
  monotonas (Arranque.t12ContieneS12 M hM)

/-- **Parikh para T¹₂**, para `∀ x ∃ y φ` con `φ` acotada, sin unicidad. -/
theorem parikh_existe_T12 {φ : L.Formula (Fin 2)} (hφ : EsAcotada φ)
    (htot : ∀ (M : Type) [L.Structure M], EsModeloT12 M → ∀ x : M, ∃ y : M, φ.Realize ![x, y]) :
    ∃ t : L.Term (Fin 1), ∀ (M : Type) [L.Structure M], EsModeloT12 M →
      ∀ x : M, ∃ y : M, le y (t.realize ![x]) ∧ φ.Realize ![x, y] :=
  parikh_existe_de (fun M _ => EsModeloT12 M) T12 modelo_T12_iff (fun _ _ hM => hM.basic)
    (fun _ _ hM => monotonas_T12 hM) (fun _ _ hM c => segmento_T12 hM (monotonas_T12 hM) c) hφ htot

/-! ## 3. T¹₂ como teoría sana con Parikh, y la oscilación -/

/-- **`T¹₂ ⊢ ∀ x ∃ y φ(x, y)`**, por modelos. -/
def DemuestraExisteT12 (φ : L.Formula (Fin 2)) : Prop :=
  ∀ (M : Type) [L.Structure M], EsModeloT12 M → ∀ x : M, ∃ y : M, φ.Realize ![x, y]

/-- **Lo que T¹₂ demuestra**, en la forma `∀ x ∃ y φ` con `φ` acotada, leído en ℕ. -/
def ThT12 : Set Enunciado := {ψ | ∃ φ : L.Formula (Fin 2), EsAcotada φ ∧ Define φ ψ ∧ DemuestraExisteT12 φ}

/-- Lo que S¹₂ demuestra lo demuestra T¹₂ (`t12ContieneS12`). -/
theorem thS12_sub_thT12 : ThS12 ⊆ ThT12 := by
  rintro ψ ⟨φ, hφ, hdef, hdem⟩
  exact ⟨φ, hφ, hdef, fun M _ hM => hdem M (Arranque.t12ContieneS12 M hM)⟩

/-- **T¹₂ es una teoría sana con la propiedad de Parikh** para toda la clase. -/
theorem parikhSana_T12 : ParikhSana Set.univ ThT12 where
  sana := by
    rintro ψ ⟨φ, -, hdef, hdem⟩ x
    obtain ⟨y, hy⟩ := hdem ℕ nat_esModeloT12 x
    exact ⟨y, (hdef x y).1 hy⟩
  parikh := by
    rintro ψ ⟨φ, hφ, hdef, hdem⟩ -
    obtain ⟨t, ht⟩ := parikh_existe_T12 hφ hdem
    refine ⟨fun x => t.realize ![x], cota_termino t, acotF φ t, esAcotada_acotF hφ t, fun x y => ?_,
      fun M _ hM x => ?_⟩
    · rw [realize_acotF, hdef]; rfl
    · obtain ⟨y, hle, hy⟩ := ht M hM x
      exact ⟨y, (realize_acotF φ t x y).2 ⟨hle, hy⟩⟩

/-- **Con T¹₂.** Si SAT (enmarcado) oscila en circuitos, ninguna fórmula acotada que defina en ℕ «los largos buenos
de `satMarco` para `c·(m+1)^k`» tiene `T¹₂ ⊢ ∀ x ∃ y φ`. -/
theorem t12_no_demuestra_oscila (hO : Oscila (Tiempo.Finitud.sucNat satMarco)) (c k : ℕ) {φ : L.Formula (Fin 2)}
    (hφ : EsAcotada φ) (hdef : Define φ (Buenos satMarco c k)) : ¬ DemuestraExisteT12 φ := fun hdem =>
  oscila_no_se_demuestra parikhSana_T12 hO (Set.mem_univ _) ⟨φ, hφ, hdef, hdem⟩

/-- **Al revés, con T¹₂**: si T¹₂ demuestra que los largos buenos de SAT no se acaban, SAT está en P/poly. -/
theorem t12_demuestra_implica_ppoly {c k : ℕ} {φ : L.Formula (Fin 2)} (hφ : EsAcotada φ)
    (hdef : Define φ (Buenos satMarco c k)) (hdem : DemuestraExisteT12 φ) :
    CookS12.satBits ∈ PsobrePoly :=
  satBits_de_parikh parikhSana_T12 (Set.mem_univ _) ⟨φ, hφ, hdef, hdem⟩

/-! ## Controles -/

/-- `ThT12` no es vacía: contiene lo de `OscilacionParikh.control_ThS12`. -/
example : (fun x y : ℕ => x ≤ y) ∈ ThT12 := thS12_sub_thT12 control_ThS12

/- Mutantes (25 nov 2026, fuera del repositorio):
* MutT1: en `segmento_T12`, la guarda `x ≤ w` cambiada por `x ≤ x`: falla al leer `ψ` (`hψr`); la guarda es la que
  deja al paso dentro del segmento. Es un fallo de forma, por eso el MutT3.
* MutT2: `parikh_existe_de` sin `hseg`: falla donde se pide la salida de `c` en el segmento (`htot S hSS cS`).
* MutT3: `segmento_T12` con un modelo de `T⁰₂` (inducción solo para agudas): falla al aplicar la inducción del
  modelo grande a `x ≤ w → φ(x)`, que es `Σᵇ₁` y no aguda. -/

end Sagitta.Map.Borde.ParikhT12
