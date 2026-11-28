import Sagitta.Map.Secuentes
import Sagitta.Map.Definibles
import Mathlib.ModelTheory.Substructures
import Mathlib.ModelTheory.Satisfiability

/-!
# El teorema de Parikh para S¹₂

Parikh (1971); Buss (1986): si S¹₂ demuestra `∀ x ∃! y φ(x, y)` con `φ` en `Σᵇ₁`, lo demuestra con la `y` acotada por
un término. Es `CotaDeParikh` de `Definibles.lean`: une la definibilidad informal de Buss (p. 3) con la formal (p. 33).

La prueba es por modelos:

1. **Compacidad.** Si ningún término sirve, hay un modelo de S¹₂ con un `c` para el que **ningún** término acota la
   salida: `∀ t, ∀ y ≤ t(c), ¬ φ(c, y)`.
2. **El segmento inicial** de lo que acota un término de `c` es una subestructura, cerrada hacia abajo. Es modelo de
   BASIC porque BASIC es universal, y de PIND porque las fórmulas `Σᵇ₁` dicen lo mismo en el segmento que en el
   modelo (sus cuantificadores están acotados).
3. En el segmento, S¹₂ da una salida para `c`. Es una salida en el modelo, acotada por un término. Contradicción.

Para que el segmento sea cerrado por las funciones, las funciones tienen que ser **monótonas**. Aquí eso queda como
hipótesis con nombre (`Monotonas`), y el teorema es `parikh_de_monotonas`. Probar que todo modelo de S¹₂ es monótono
es la parte aritmética, aparte.
-/

open FirstOrder FirstOrder.Language Set

namespace Sagitta.Map
namespace Acotada
namespace Parikh

/-! ## Monotonía -/

/-- **Las funciones de Buss son monótonas** en `M`. -/
structure Monotonas (M : Type) [L.Structure M] : Prop where
  suc : ∀ x y : M, le x y → le (suc x) (suc y)
  long : ∀ x y : M, le x y → le (long x) (long y)
  mitad : ∀ x y : M, le x y → le (mitad x) (mitad y)
  suma : ∀ x y x' y' : M, le x x' → le y y' → le (suma x y) (suma x' y')
  prod : ∀ x y x' y' : M, le x x' → le y y' → le (prod x y) (prod x' y')
  smash : ∀ x y x' y' : M, le x x' → le y y' → le (smash x y) (smash x' y')

variable {M : Type} [L.Structure M]

theorem le_refl' (h : EsModeloBASIC M) (x : M) : le x x := by
  rcases h.b6 x x with h | h <;> exact h

theorem fin1_eq {β : Type} (x : Fin 1 → β) : x = ![x 0] := by
  funext i; match i with | 0 => rfl

theorem fin2_eq {β : Type} (x : Fin 2 → β) : x = ![x 0, x 1] := by
  funext i; match i with | 0 => rfl | 1 => rfl

/-- **Toda función del lenguaje es monótona**, si lo son las seis. -/
theorem fun_mono (h : EsModeloBASIC M) (hm : Monotonas M) :
    ∀ {n} (f : L.Functions n) (x y : Fin n → M), (∀ i, le (x i) (y i)) →
      le (Structure.funMap f x) (Structure.funMap f y) := by
  intro n f x y hxy
  cases f with
  | cero =>
    have : x = y := funext fun i => i.elim0
    subst this; exact le_refl' h _
  | suc => rw [fin1_eq x, fin1_eq y]; exact hm.suc _ _ (hxy 0)
  | long => rw [fin1_eq x, fin1_eq y]; exact hm.long _ _ (hxy 0)
  | mitad => rw [fin1_eq x, fin1_eq y]; exact hm.mitad _ _ (hxy 0)
  | suma => rw [fin2_eq x, fin2_eq y]; exact hm.suma _ _ _ _ (hxy 0) (hxy 1)
  | prod => rw [fin2_eq x, fin2_eq y]; exact hm.prod _ _ _ _ (hxy 0) (hxy 1)
  | smash => rw [fin2_eq x, fin2_eq y]; exact hm.smash _ _ _ _ (hxy 0) (hxy 1)

/-! ## El segmento inicial de `c` -/

/-- **Lo que acota un término de `c`.** Con funciones monótonas, es una subestructura. -/
def segmento (h : EsModeloBASIC M) (hm : Monotonas M) (c : M) : L.Substructure M where
  carrier := {y | ∃ t : L.Term (Fin 1), le y (t.realize ![c])}
  fun_mem := by
    intro n f x hx
    choose t ht using hx
    exact ⟨Term.func f t, fun_mono h hm f _ _ ht⟩

theorem mem_segmento {h : EsModeloBASIC M} {hm : Monotonas M} {c y : M} :
    y ∈ segmento h hm c ↔ ∃ t : L.Term (Fin 1), le y (t.realize ![c]) := Iff.rfl

theorem c_mem_segmento (h : EsModeloBASIC M) (hm : Monotonas M) (c : M) : c ∈ segmento h hm c :=
  ⟨Term.var 0, le_refl' h c⟩

/-- **El segmento es cerrado hacia abajo.** -/
theorem segmento_abajo (h : EsModeloBASIC M) (hm : Monotonas M) (c : M) {y z : M}
    (hz : z ∈ segmento h hm c) (hyz : le y z) : y ∈ segmento h hm c := by
  obtain ⟨t, ht⟩ := hz
  exact ⟨t, h.b8 _ _ _ hyz ht⟩

/-! ## BASIC es universal, y vale en toda subestructura -/

/-- Lo que no tiene cuantificadores. -/
macro "sinCuantificadores" : tactic => `(tactic|
  repeat (first
    | exact BoundedFormula.IsQF.falsum
    | apply BoundedFormula.IsQF.imp
    | exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | exact (BoundedFormula.IsAtomic.rel _ _).isQF))

/-- Universal: `∀` delante de algo sin cuantificadores. -/
macro "universal" : tactic => `(tactic|
  (repeat apply BoundedFormula.IsUniversal.all
   apply BoundedFormula.IsUniversal.of_isQF
   sinCuantificadores))

instance basic_universal : teoriaBASIC.IsUniversal := ⟨by
  intro σ hσ
  simp only [teoriaBASIC, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [axB1, axB2, axB3, axB4, axB5, axB6, axB7, axB8, axB9, axB10, axB11, axB12, axB13, axB14, axB15,
      axB16, axB17, axB18, axB19, axB20, axB21, axB22, axB23, axB24, axB25, axB26, axB27, axB28, axB29, axB30, axB31,
      axB32]
    universal⟩

/-- **Toda subestructura de un modelo de BASIC es modelo de BASIC.** -/
theorem basic_subestructura (h : EsModeloBASIC M) (S : L.Substructure M) : EsModeloBASIC S := by
  have : M ⊨ teoriaBASIC := (modelo_basic_iff M).2 h
  exact (modelo_basic_iff S).1 inferInstance


/-! ## Aritmética mínima: la mitad no pasa del número -/

theorem le_suma_der (h : EsModeloBASIC M) (x y : M) : le y (suma x y) := by
  rw [h.b21]; exact h.b19 y x

/-- **`⌊x/2⌋ ≤ x`**, desde BASIC. -/
theorem mitad_le (h : EsModeloBASIC M) (x : M) : le (mitad x) x := by
  have hm := (h.b32 (mitad x) x).1 rfl
  have h2 : le (mitad x) (doble (mitad x)) := by
    have e : doble (mitad x) = suma (prod (mitad x) (suc cero)) (mitad x) := by
      rw [doble, h.b28, h.b27]
    rw [e]; exact le_suma_der h _ _
  rcases hm with e | e
  · rw [e] at h2; exact h2
  · have h3 := h.b8 _ _ _ h2 (h.b1 _ _ (le_refl' h _))
    rw [e] at h3; exact h3

/-! ## Los cuantificadores acotados, leídos -/

section Leer

variable {α : Type} {n : ℕ}

theorem realize_leF (t u : L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) :
    (leF t u).Realize v xs ↔ le (t.realize (Sum.elim v xs)) (u.realize (Sum.elim v xs)) := by
  change Structure.RelMap (L := L) (Rel.le : L.Relations 2) (fun i => (![t, u] i).realize (Sum.elim v xs)) ↔ _
  unfold le
  rw [show (fun i => (![t, u] i).realize (Sum.elim v xs)) =
      ![t.realize (Sum.elim v xs), u.realize (Sum.elim v xs)] from by
    funext i; match i with | 0 => rfl | 1 => rfl]

theorem realize_nueva (v : α → M) (xs : Fin n → M) (z : M) :
    (nueva : L.Term (α ⊕ Fin (n + 1))).realize (Sum.elim v (Fin.snoc xs z)) = z := by
  simp [nueva, Term.realize_var, Fin.snoc_last]

theorem realize_sube (s : L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) (z : M) :
    (sube s).realize (Sum.elim v (Fin.snoc xs z)) = s.realize (Sum.elim v xs) := by
  rw [sube, Term.realize_relabel]
  congr 1
  funext a
  rcases a with a | i
  · rfl
  · simp [Fin.snoc_castSucc]

theorem realize_paraTodo (s : L.Term (α ⊕ Fin n)) (ψ : L.BoundedFormula α (n + 1)) (v : α → M) (xs : Fin n → M) :
    (paraTodoAcotado s ψ).Realize v xs ↔
      ∀ z, le z (s.realize (Sum.elim v xs)) → ψ.Realize v (Fin.snoc xs z) := by
  rw [paraTodoAcotado, BoundedFormula.realize_all]
  refine forall_congr' fun z => ?_
  rw [BoundedFormula.realize_imp, realize_leF, realize_nueva, realize_sube]

theorem realize_existe (s : L.Term (α ⊕ Fin n)) (ψ : L.BoundedFormula α (n + 1)) (v : α → M) (xs : Fin n → M) :
    (existeAcotado s ψ).Realize v xs ↔
      ∃ z, le z (s.realize (Sum.elim v xs)) ∧ ψ.Realize v (Fin.snoc xs z) := by
  rw [existeAcotado, BoundedFormula.realize_ex]
  refine exists_congr fun z => ?_
  rw [BoundedFormula.realize_inf, realize_leF, realize_nueva, realize_sube]

end Leer

/-! ## Las fórmulas `Σᵇ₁` dicen lo mismo en una subestructura cerrada hacia abajo -/

section Absoluto

variable (S : L.Substructure M)

theorem le_coe (x y : S) : le (x : M) (y : M) ↔ le x y := by
  unfold le
  rw [show (![(x : M), (y : M)] : Fin 2 → M) = fun i => ((![x, y] : Fin 2 → S) i : M) from by
    funext i; match i with | 0 => rfl | 1 => rfl]
  rfl

theorem coe_term {β : Type} (t : L.Term β) (w : β → S) : t.realize (Subtype.val ∘ w) = ((t.realize w : S) : M) :=
  HomClass.realize_term S.subtype

variable {S} (hdown : ∀ y z : M, z ∈ S → le y z → y ∈ S)
include hdown

variable {α : Type}

theorem abs_todo {n : ℕ} {s : L.Term (α ⊕ Fin n)} {ψ : L.BoundedFormula α (n + 1)}
    (ih : ∀ (v : α → S) (xs : Fin (n + 1) → S), ψ.Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) ↔ ψ.Realize v xs)
    (v : α → S) (xs : Fin n → S) :
    (paraTodoAcotado s ψ).Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) ↔ (paraTodoAcotado s ψ).Realize v xs := by
  rw [realize_paraTodo, realize_paraTodo]
  have hs : s.realize (Sum.elim (Subtype.val ∘ v) (Subtype.val ∘ xs)) = ((s.realize (Sum.elim v xs) : S) : M) := by
    rw [← Sum.comp_elim]; exact coe_term S s _
  constructor
  · intro h z hz
    rw [← ih, Fin.comp_snoc]
    exact h z (by rw [hs]; exact (le_coe S _ _).2 hz)
  · intro h z hz
    rw [hs] at hz
    have hzS : z ∈ S := hdown z _ (s.realize (Sum.elim v xs)).2 hz
    have := h ⟨z, hzS⟩ ((le_coe S ⟨z, hzS⟩ _).1 hz)
    rw [← ih, Fin.comp_snoc] at this
    exact this

theorem abs_existe {n : ℕ} {s : L.Term (α ⊕ Fin n)} {ψ : L.BoundedFormula α (n + 1)}
    (ih : ∀ (v : α → S) (xs : Fin (n + 1) → S), ψ.Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) ↔ ψ.Realize v xs)
    (v : α → S) (xs : Fin n → S) :
    (existeAcotado s ψ).Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) ↔ (existeAcotado s ψ).Realize v xs := by
  rw [realize_existe, realize_existe]
  have hs : s.realize (Sum.elim (Subtype.val ∘ v) (Subtype.val ∘ xs)) = ((s.realize (Sum.elim v xs) : S) : M) := by
    rw [← Sum.comp_elim]; exact coe_term S s _
  constructor
  · rintro ⟨z, hz, hψ⟩
    rw [hs] at hz
    have hzS : z ∈ S := hdown z _ (s.realize (Sum.elim v xs)).2 hz
    refine ⟨⟨z, hzS⟩, (le_coe S ⟨z, hzS⟩ _).1 hz, ?_⟩
    rw [← ih, Fin.comp_snoc]; exact hψ
  · rintro ⟨z, hz, hψ⟩
    refine ⟨z, by rw [hs]; exact (le_coe S _ _).2 hz, ?_⟩
    rw [← ih, Fin.comp_snoc] at hψ; exact hψ

theorem abs_aguda {n : ℕ} {φ : L.BoundedFormula α n} (hφ : EsAguda φ) :
    ∀ (v : α → S) (xs : Fin n → S), φ.Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) ↔ φ.Realize v xs := by
  induction hφ with
  | falso => intro v xs; exact BoundedFormula.IsQF.falsum.realize_embedding S.subtype
  | igual t u => intro v xs; exact (BoundedFormula.IsAtomic.equal t u).isQF.realize_embedding S.subtype
  | rel R ts => intro v xs; exact (BoundedFormula.IsAtomic.rel R ts).isQF.realize_embedding S.subtype
  | imp _ _ ih1 ih2 => intro v xs; rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, ih1, ih2]
  | todoAgudo t _ ih => exact abs_todo hdown ih
  | existeAgudo t _ ih => exact abs_existe hdown ih

mutual

theorem abs_sigma : ∀ {n : ℕ} {φ : L.BoundedFormula α n}, EsSigma1 φ →
    ∀ (v : α → S) (xs : Fin n → S), φ.Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) ↔ φ.Realize v xs
  | _, _, .aguda h => abs_aguda hdown h
  | _, _, .existe _ h => abs_existe hdown (abs_sigma h)
  | _, _, .todoAgudo _ h => abs_todo hdown (abs_sigma h)
  | _, _, .y h1 h2 => fun v xs => by
      rw [BoundedFormula.realize_inf, BoundedFormula.realize_inf, abs_sigma h1, abs_sigma h2]
  | _, _, .o h1 h2 => fun v xs => by
      rw [BoundedFormula.realize_sup, BoundedFormula.realize_sup, abs_sigma h1, abs_sigma h2]
  | _, _, .no h => fun v xs => by
      rw [BoundedFormula.realize_not, BoundedFormula.realize_not, abs_pi h]
  | _, _, .imp h1 h2 => fun v xs => by
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, abs_pi h1, abs_sigma h2]

theorem abs_pi : ∀ {n : ℕ} {φ : L.BoundedFormula α n}, EsPi1 φ →
    ∀ (v : α → S) (xs : Fin n → S), φ.Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) ↔ φ.Realize v xs
  | _, _, .aguda h => abs_aguda hdown h
  | _, _, .todo _ h => abs_todo hdown (abs_pi h)
  | _, _, .existeAgudo _ h => abs_existe hdown (abs_pi h)
  | _, _, .y h1 h2 => fun v xs => by
      rw [BoundedFormula.realize_inf, BoundedFormula.realize_inf, abs_pi h1, abs_pi h2]
  | _, _, .o h1 h2 => fun v xs => by
      rw [BoundedFormula.realize_sup, BoundedFormula.realize_sup, abs_pi h1, abs_pi h2]
  | _, _, .no h => fun v xs => by
      rw [BoundedFormula.realize_not, BoundedFormula.realize_not, abs_sigma h]
  | _, _, .imp h1 h2 => fun v xs => by
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, abs_sigma h1, abs_pi h2]

end

/-- **Para fórmulas `Σᵇ₁` sin variables ligadas.** -/
theorem abs_formula {φ : L.Formula α} (hφ : EsSigma1 φ) (v : α → S) :
    φ.Realize (Subtype.val ∘ v) ↔ φ.Realize v := by
  have := abs_sigma hdown hφ v default
  rw [Subsingleton.elim (Subtype.val ∘ (default : Fin 0 → S)) default] at this
  exact this

end Absoluto


/-! ## El segmento es un modelo de S¹₂ -/

theorem coe_cero (S : L.Substructure M) : ((cero : S) : M) = cero := by
  change Structure.funMap (L := L) (Fun.cero : L.Functions 0) (fun i => (((![] : Fin 0 → S)) i : M)) =
    Structure.funMap (L := L) (Fun.cero : L.Functions 0) ![]
  congr 1; funext i; exact i.elim0

theorem coe_mitad (S : L.Substructure M) (x : S) : ((mitad x : S) : M) = mitad (x : M) := by
  change Structure.funMap (L := L) (Fun.mitad : L.Functions 1) (fun i => ((![x] i : S) : M)) =
    Structure.funMap (L := L) (Fun.mitad : L.Functions 1) ![(x : M)]
  congr 1; funext i; match i with | 0 => rfl

/-- **El segmento de `c` es un modelo de S¹₂.** BASIC pasa por universal; PIND, por la fórmula
`x ≤ w → φ(x)` en el modelo grande, que no necesita salir del segmento. -/
theorem segmento_S12 (hM : EsModeloS12 M) (hm : Monotonas M) (c : M) :
    EsModeloS12 (segmento hM.basic hm c) := by
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
  have key := hM.pind (k + 1) ψ hψ u ((hψr cero).2 fun _ => by
      have := (habs cero).2 h0
      rwa [coe_cero] at this) (fun x hx => by
      rw [hψr] at hx ⊢
      intro hxw
      have hxS : x ∈ S := hdown x w w.2 hxw
      have h1 := hx (hM.basic.b8 _ _ _ (mitad_le hM.basic x) hxw)
      have h2 : φ.Realize (Fin.cons (mitad (⟨x, hxS⟩ : S)) v) := by
        rw [← habs, coe_mitad]; exact h1
      exact (habs ⟨x, hxS⟩).2 (hpaso _ h2)) (w : M)
  exact (habs w).1 ((hψr w).1 key (le_refl' hM.basic _))


/-! ## Compacidad: un `c` sin cota -/

/-- **`∀ y (y ≤ t(x₀) → ¬ φ(x₀, y))`**: ninguna salida de `x₀` cabe bajo `t`. -/
noncomputable def sinCota (φ : L.Formula (Fin 2)) (t : L.Term (Fin 1)) : L.Formula (Fin 1) :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₂ (Rel.le : L.Relations 2) (Term.var (Sum.inr 0)) (t.relabel Sum.inl)).imp
      (φ.subst ![Term.var (Sum.inl 0), Term.var (Sum.inr 0)]).not)

theorem realize_sinCota (φ : L.Formula (Fin 2)) (t : L.Term (Fin 1)) (x : M) :
    (sinCota φ t).Realize ![x] ↔ ∀ y : M, le y (t.realize ![x]) → ¬ φ.Realize ![x, y] := by
  have he1 : ∀ i : Fin 1 → M, (fun a => Term.realize (fun a => Sum.elim ![x] i a)
      ((![Term.var (Sum.inl 0), Term.var (Sum.inr 0)] : Fin 2 → L.Term (Fin 1 ⊕ Fin 1)) a)) = ![x, i 0] := by
    intro i; funext a; match a with | 0 => rfl | 1 => rfl
  have he2 : ∀ i : Fin 1 → M, Term.realize ((fun a => Sum.elim ![x] i a) ∘ Sum.inl) t = t.realize ![x] := by
    intro i; congr 1
  rw [sinCota, Formula.realize_iAlls]
  constructor
  · intro h y hy
    have := h ![y]
    simp only [Formula.realize_imp, Formula.realize_rel₂, Formula.realize_not, formula_realize_subst,
      Term.realize_var, Term.realize_relabel] at this
    rw [he1, he2] at this
    exact this hy
  · intro h i
    simp only [Formula.realize_imp, Formula.realize_rel₂, Formula.realize_not, formula_realize_subst,
      Term.realize_var, Term.realize_relabel]
    rw [he1, he2]
    exact h (i 0)

/-- La suma de una lista de términos. -/
noncomputable def sumaTerminos : List (L.Term (Fin 1)) → L.Term (Fin 1)
  | [] => tC
  | t :: l => tMs t (sumaTerminos l)

theorem le_sumaTerminos (h : EsModeloBASIC M) (x : M) :
    ∀ (l : List (L.Term (Fin 1))) (t : L.Term (Fin 1)), t ∈ l →
      le (t.realize ![x]) ((sumaTerminos l).realize ![x])
  | [], _, ht => absurd ht List.not_mem_nil
  | s :: l, t, ht => by
    have e : (sumaTerminos (s :: l)).realize ![x] = suma (s.realize ![x]) ((sumaTerminos l).realize ![x]) := by
      simp only [sumaTerminos, tMs, Term.realize_functions_apply₂]; rfl
    rw [e]
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h.b19 _ _
    · exact h.b8 _ _ _ (le_sumaTerminos h x l t ht) (le_suma_der h _ _)

/-- **Compacidad.** Si para cada término hay un modelo de S¹₂ con un `x` sin salida bajo ese término, hay uno con un
`c` sin salida bajo **ningún** término. -/
theorem existe_c_sin_cota (φ : L.Formula (Fin 2))
    (hno : ∀ t : L.Term (Fin 1), ∃ (N : Type) (_ : L.Structure N), EsModeloS12 N ∧
      ∃ x : N, ∀ y : N, le y (t.realize ![x]) → ¬ φ.Realize ![x, y]) :
    ∃ (N : Type) (_ : L.Structure N), EsModeloS12 N ∧
      ∃ c : N, ∀ (t : L.Term (Fin 1)) (y : N), le y (t.realize ![c]) → ¬ φ.Realize ![c, y] := by
  classical
  let T' : L[[Fin 1]].Theory :=
    (L.lhomWithConstants (Fin 1)).onTheory S12 ∪ Set.range fun t => Formula.equivSentence (sinCota φ t)
  have hfin : T'.IsFinitelySatisfiable := by
    intro T0 hT0
    let F : Finset (L.Term (Fin 1)) := T0.biUnion fun σ =>
      if hσ : ∃ t, Formula.equivSentence (sinCota φ t) = σ then {hσ.choose} else ∅
    obtain ⟨N, _, hN, x, hx⟩ := hno (sumaTerminos F.toList)
    let _ : (constantsOn (Fin 1)).Structure N := constantsOn.structure fun _ => x
    have : Nonempty N := ⟨x⟩
    have hS : N ⊨ S12 := (modelo_S12_iff N).2 hN
    have hT : N ⊨ (L.lhomWithConstants (Fin 1)).onTheory S12 :=
      (LHom.onTheory_model (L.lhomWithConstants (Fin 1)) S12).mpr hS
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
        exact hx y (hN.basic.b8 _ _ _ hy
          (le_sumaTerminos hN.basic x _ _ (Finset.mem_toList.2 htF)))
    exact ⟨Theory.ModelType.of _ N⟩
  obtain ⟨N⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfin
  let _ : L.Structure N := (L.lhomWithConstants (Fin 1)).reduct N
  have hS : N ⊨ S12 :=
    (LHom.onTheory_model (L.lhomWithConstants (Fin 1)) S12).mp (Theory.Model.mono N.is_model Set.subset_union_left)
  refine ⟨N, inferInstance, (modelo_S12_iff N).1 hS, (L.con (0 : Fin 1) : N), fun t y hy => ?_⟩
  have hσ : N ⊨ Formula.equivSentence (sinCota φ t) := Theory.realize_sentence_of_mem T' (Or.inr ⟨t, rfl⟩)
  rw [Formula.realize_equivSentence] at hσ
  have hv : (fun a : Fin 1 => (L.con a : N)) = ![(L.con (0 : Fin 1) : N)] := by
    funext a; match a with | 0 => rfl
  rw [hv, realize_sinCota] at hσ
  exact hσ y hy

/-! ## El teorema, con la monotonía como hipótesis -/

/-- **Parikh para S¹₂, si las funciones son monótonas en todo modelo de S¹₂.** -/
theorem parikh_de_monotonas (hmon : ∀ (M : Type) [L.Structure M], EsModeloS12 M → Monotonas M) : CotaDeParikh := by
  intro φ hφ htot
  suffices hex : ∃ t : L.Term (Fin 1), ∀ (M : Type) [L.Structure M], EsModeloS12 M →
      ∀ x : M, ∃ y : M, le y (t.realize ![x]) ∧ φ.Realize ![x, y] by
    obtain ⟨t, ht⟩ := hex
    refine ⟨t, fun M _ hM => ⟨ht M hM, fun x y z hy hz => ?_⟩⟩
    obtain ⟨w, -, hw⟩ := htot M hM x
    exact (hw y hy).trans (hw z hz).symm
  by_contra hno
  push Not at hno
  obtain ⟨N, _, hN, c, hc⟩ := existe_c_sin_cota φ fun t => by
    obtain ⟨N, i, hN, x, hx⟩ := hno t
    exact ⟨N, i, hN, x, fun y hy hφy => hx y hy hφy⟩
  have hm := hmon N hN
  set S := segmento hN.basic hm c
  have hdown : ∀ y z : N, z ∈ S → le y z → y ∈ S := fun _ _ hz hyz => segmento_abajo hN.basic hm c hz hyz
  have hSS := segmento_S12 hN hm c
  let cS : S := ⟨c, c_mem_segmento hN.basic hm c⟩
  obtain ⟨y, hy, -⟩ := htot S hSS cS
  have hyN : φ.Realize ![c, (y : N)] := by
    have := (abs_formula hdown hφ ![cS, y]).2 hy
    rwa [show (Subtype.val ∘ ![cS, y] : Fin 2 → N) = ![c, (y : N)] from by
      funext i; match i with | 0 => rfl | 1 => rfl] at this
  obtain ⟨t, ht⟩ := (mem_segmento.1 y.2 : ∃ t : L.Term (Fin 1), le (y : N) (t.realize ![c]))
  exact hc t y ht hyN


/-! ## La monotonía, desde BASIC y PIND -/

section Monotonia

variable (h : EsModeloBASIC M)
include h

theorem le_suc (x : M) : le x (suc x) := h.b1 _ _ (le_refl' h x)

theorem suc_ne_cero (w : M) : suc w ≠ cero := by
  intro e
  have hw : le w cero := e ▸ le_suc h w
  have : w = cero := h.b7 _ _ hw (h.b3 w)
  subst this
  exact h.b2 cero e.symm

theorem cero_o_uno_le (x : M) : x = cero ∨ le uno x := by
  by_cases hx : x = cero
  · exact .inl hx
  · exact .inr ((h.b4 cero x).1 ⟨h.b3 x, Ne.symm hx⟩)

/-- Si `a ≤ S b` y `a ≠ S b`, entonces `a ≤ b`. -/
theorem le_de_lt_suc {a b : M} (hab : le a (suc b)) (hne : a ≠ suc b) : le a b := by
  rcases h.b6 a b with hba | hab'
  · by_cases e : b = a
    · exact e ▸ le_refl' h a
    · have h1 : le (suc b) a := (h.b4 b a).1 ⟨hba, e⟩
      exact absurd (h.b7 _ _ hab h1) hne
  · exact hab'

theorem suma_uno (a : M) : suma a uno = suc a := by
  rw [uno, h.b23, h.b22]

theorem prod_uno (a : M) : prod a uno = a := by
  rw [uno, h.b27, h.b26, h.b21, h.b22]

theorem prod_cero_izq (a : M) : prod cero a = cero := by
  rw [h.b28, h.b26]

theorem suc_mono (x y : M) (hxy : le x y) : le (suc x) (suc y) := by
  by_cases e : x = y
  · exact e ▸ le_refl' h _
  · exact h.b8 _ _ _ ((h.b4 x y).1 ⟨hxy, e⟩) (le_suc h y)

theorem suma_mono (x y x' y' : M) (hx : le x x') (hy : le y y') : le (suma x y) (suma x' y') := by
  have h1 : le (suma x y) (suma x y') := (h.b25 x y y').2 hy
  have h2 : le (suma y' x) (suma y' x') := (h.b25 y' x x').2 hx
  rw [h.b21 y' x, h.b21 y' x'] at h2
  exact h.b8 _ _ _ h1 h2

theorem prod_mono_der (x y y' : M) (hy : le y y') : le (prod x y) (prod x y') := by
  rcases cero_o_uno_le h x with rfl | hx
  · rw [prod_cero_izq h, prod_cero_izq h]; exact le_refl' h _
  · exact (h.b30 x y y' hx).2 hy

theorem prod_mono (x y x' y' : M) (hx : le x x') (hy : le y y') : le (prod x y) (prod x' y') := by
  have h1 := prod_mono_der h x y y' hy
  have h2 := prod_mono_der h y' x x' hx
  rw [h.b28 y' x, h.b28 y' x'] at h2
  exact h.b8 _ _ _ h1 h2

theorem doble_le_suc (m : M) : le (doble m) (suc (doble m)) := le_suc h _

theorem mitad_mono (x y : M) (hxy : le x y) : le (mitad x) (mitad y) := by
  rcases h.b6 (mitad x) (mitad y) with hyx | hxy'
  · by_cases e : mitad y = mitad x
    · exact e ▸ le_refl' h _
    · exfalso
      obtain ⟨h1, -⟩ := h.b20 _ _ hyx e
      have hy : le y (suc (doble (mitad y))) := by
        rcases (h.b32 (mitad y) y).1 rfl with e' | e'
        · rw [e']; rw [← e']; exact doble_le_suc h _
        · rw [e']; exact le_refl' h _
      have hx : le (doble (mitad x)) x := by
        rcases (h.b32 (mitad x) x).1 rfl with e' | e'
        · rw [e']; exact le_refl' h _
        · have := doble_le_suc h (mitad x); rw [e'] at this; exact this
      have hyx' : le y x := h.b8 _ _ _ hy (h.b8 _ _ _ h1 hx)
      have := h.b7 _ _ hxy hyx'
      exact e (by rw [this])
  · exact hxy'

theorem smash_ne_cero (x y : M) : smash x y ≠ cero := by
  intro e
  have := h.b13 x y
  rw [e, h.b9] at this
  exact suc_ne_cero h _ this.symm

theorem uno_le_smash (x y : M) : le uno (smash x y) := by
  rcases cero_o_uno_le h (smash x y) with e | e
  · exact absurd e (smash_ne_cero h x y)
  · exact e

/-- **El paso del smash**: `⌊z/2⌋ # y ≤ z # y`, porque `|z| = |⌊z/2⌋| + |1|`. -/
theorem smash_paso (z y : M) (hz : z ≠ cero) : le (smash (mitad z) y) (smash z y) := by
  have hl : long z = suma (long (mitad z)) (long uno) := by
    rw [h.b11, suma_uno h, h.b31 z hz]
  rw [h.b18 z y (mitad z) uno hl]
  have := (h.b30 (smash (mitad z) y) uno (smash uno y) (uno_le_smash h _ _)).2 (uno_le_smash h _ _)
  rwa [prod_uno h] at this

end Monotonia

/-- **`|x| ≤ |z| → x # y ≤ z # y`**, por PIND sobre `z`. -/
theorem smash_mono_long {M : Type} [L.Structure M] (hM : EsModeloS12 M) (x y z : M)
    (hl : le (long x) (long z)) : le (smash x y) (smash z y) := by
  have h := hM.basic
  let ψ : L.Formula (Fin 3) :=
    (Relations.formula₂ (Rel.le : L.Relations 2) (tLg (Term.var 1)) (tLg (Term.var 0))).imp
      (Relations.formula₂ (Rel.le : L.Relations 2) (tSm (Term.var 1) (Term.var 2)) (tSm (Term.var 0) (Term.var 2)))
  have hψ : EsSigma1 ψ := .imp (.aguda (.rel _ _)) (.aguda (.rel _ _))
  have hr : ∀ w : M, ψ.Realize (Fin.cons w ![x, y]) ↔ (le (long x) (long w) → le (smash x y) (smash w y)) := by
    intro w
    simp only [ψ, Formula.realize_imp, Formula.realize_rel₂, tLg, tSm, Term.realize_functions_apply₁,
      Term.realize_functions_apply₂, Term.realize_var]
    rfl
  have base : ∀ w : M, w = cero → le (long x) (long w) → le (smash x y) (smash w y) := by
    rintro w rfl hxw
    rw [h.b9] at hxw
    have e : long x = long (cero : M) := by rw [h.b9]; exact h.b7 _ _ hxw (h.b3 _)
    rw [h.b17 x cero y e]; exact le_refl' h _
  have key := hM.pind 2 ψ hψ ![x, y] ((hr cero).2 (base cero rfl)) (fun w hw => by
      rw [hr] at hw ⊢
      intro hxw
      by_cases hw0 : w = cero
      · exact base w hw0 hxw
      by_cases e : long x = long w
      · rw [h.b17 x w y e]; exact le_refl' h _
      · rw [h.b31 w hw0] at hxw e
        exact h.b8 _ _ _ (hw (le_de_lt_suc h hxw e)) (smash_paso h w y hw0)) z
  exact (hr z).1 key hl

/-- **Todo modelo de S¹₂ es monótono.** -/
theorem monotonas {M : Type} [L.Structure M] (hM : EsModeloS12 M) : Monotonas M := by
  have h := hM.basic
  refine ⟨suc_mono h, h.b12, mitad_mono h, suma_mono h, prod_mono h, fun x y x' y' hx hy => ?_⟩
  have h1 : le (smash x y) (smash x' y) := smash_mono_long hM x y x' (h.b12 _ _ hx)
  have h2 : le (smash y x') (smash y' x') := smash_mono_long hM y x' y' (h.b12 _ _ hy)
  rw [h.b16 y x', h.b16 y' x'] at h2
  exact h.b8 _ _ _ h1 h2

/-- **El teorema de Parikh para S¹₂** (Parikh 1971; Buss 1986): si S¹₂ demuestra `∀ x ∃! y φ` con `φ` en `Σᵇ₁`, lo
demuestra con la salida acotada por un término. -/
theorem parikh : CotaDeParikh :=
  parikh_de_monotonas fun _ _ hM => monotonas hM

end Parikh
end Acotada
end Sagitta.Map
