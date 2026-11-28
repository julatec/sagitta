import Sagitta.Map.Informacion.Reversible
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Cuánto vale la simetría

La pregunta es de José (25 nov 2026): qué se puede hacer con un grupo de simetría. La parte que se formaliza aquí es
**medirla en bits**: si un grupo finito `G` actúa sobre un conjunto finito de estados `σ`, describir un estado
«salvo simetría» cuesta `log₂` del número de órbitas, y la simetría ahorra a lo sumo `log₂ |G|` bits.

## Lo que se prueba

1. **La información módulo `G`** (§ 1). `orbitas G σ` es el número de órbitas (`Nat.card` del cociente por
   `orbitRel`). Burnside en la forma de Mathlib, `Σ_g |Fix g| = órbitas · |G|` (`burnside`); como `Fix 1 = σ`,
   `|σ| ≤ órbitas · |G|` (`card_le_orbitas_mul`), y por otro lado `órbitas ≤ |σ|` (`orbitas_le_card`). En bits:
   `log₂ |σ| − log₂ |G| ≤ log₂ órbitas ≤ log₂ |σ|` (`ahorro_acotado`).
2. **Testigos salvo simetría** (§ 2). Si `P` es invariante bajo `G`, los testigos son unión de órbitas
   (`testigos_union_de_orbitas`), forman un `SubMulAction` y describir uno salvo `G` cuesta `log₂` de sus órbitas,
   con las mismas cotas (`ahorro_testigos`).
3. **El palomar con su grupo** (§ 3). Las asignaciones inyectivas `Fin n → Fin n` (los emparejamientos perfectos)
   bajo `Equiv.Perm (Fin n)` actuando sobre los agujeros (`g • f = g ∘ f`) forman **una sola** órbita
   (`palomar_una_orbita`): el testigo salvo simetría cuesta `0` bits (`palomar_cero_bits`), contra `log₂ n!` sin
   ella (`palomar_testigos_card`: hay `n!`). Con `n + 1` palomas no hay testigos (`palomar_sin_testigos`, del
   palomar de Mathlib `Fintype.card_le_of_injective`).
4. **Romper la simetría cuesta** (§ 4). Una forma canónica `c` (constante en cada órbita, con `c x` en la órbita de
   `x`; por ejemplo el mínimo de la órbita en un orden, como los predicados *lex-leader*) existe siempre
   (`existe_canonica`), su imagen tiene exactamente tantos elementos como órbitas (`card_image_canonica`), y por eso
   borra exactamente `log₂ |σ| − log₂ órbitas` bits en el sentido de `Reversible.bitsBorrados`
   (`canonica_borra`). Curie: la forma canónica es invariante, gana toda la simetría (`canonica_invariante`), y no
   borra nada solo si la acción es trivial (`canonica_no_borra_iff`): ganar simetría exige borrar.
5. **Un ejemplo** (§ 5). Las `2³` cadenas de 3 bits bajo las rotaciones `ℤ/3`: los puntos fijos son `8, 2, 2`
   (`ejemplo_fijos`), Burnside da `(8 + 2 + 2)/3 = 4` órbitas (`ejemplo_orbitas`), 3 bits contra 2 salvo simetría
   (`ejemplo_bits`), y la forma canónica (la rotación de código mínimo) borra 1 bit (`ejemplo_borra_un_bit`).

## Antecedentes (de memoria)

Burnside (1897) y Pólya (1937) para contar órbitas; Krishnamurthy (1985) para el palomar corto con una regla de
simetría, contra la cota exponencial de resolución de Haken (1985); Crawford, Ginsberg, Luks y Roy (1996) para los
predicados de ruptura de simetría *lex-leader*.

## Lo que NO se prueba

* Ninguna cota de prueba: que la regla de simetría da pruebas cortas del palomar (Krishnamurthy) no se formaliza;
  aquí solo está la razón algebraica (una órbita de testigos, ninguno con `n + 1`).
* Nada sobre cuánto cuesta *calcular* la forma canónica (el isomorfismo de grafos vive ahí).
* Nada sobre P contra NP.
-/

namespace Sagitta.Map.Informacion.Simetria

open Finset MulAction
open Sagitta.Map.Informacion.Reversible (bitsBorrados logb_nat_mono logb_nat_nonneg logb_dos_pow)

/-! ## 1. La información módulo `G` -/

section Orbitas

variable (G σ : Type*) [Group G] [MulAction G σ]

/-- El número de órbitas de `G` en `σ`. -/
noncomputable def orbitas : ℕ := Nat.card (orbitRel.Quotient G σ)

/-- La información de un estado salvo simetría: `log₂` del número de órbitas. -/
noncomputable def infoSalvo : ℝ := Real.logb 2 (orbitas G σ)

variable [Fintype G] [Finite σ]

/-- **Burnside** (Mathlib `sum_card_fixedBy_eq_card_orbits_mul_card_group`): `Σ_g |Fix g| = órbitas · |G|`. -/
theorem burnside : ∑ g : G, Nat.card (fixedBy σ g) = orbitas G σ * Fintype.card G := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  have : Fintype (orbitRel.Quotient G σ) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G σ
  simp only [orbitas, Nat.card_eq_fintype_card]
  convert h

/-- Del término `g = 1` de Burnside: `|σ| ≤ órbitas · |G|`. -/
theorem card_le_orbitas_mul : Nat.card σ ≤ orbitas G σ * Fintype.card G := by
  classical
  rw [← burnside]
  have h1 : Nat.card (fixedBy σ (1 : G)) = Nat.card σ := by
    rw [MulAction.fixedBy_one_eq_univ (M := G) (α := σ), Nat.card_univ]
  calc Nat.card σ = Nat.card (fixedBy σ (1 : G)) := h1.symm
    _ ≤ ∑ g : G, Nat.card (fixedBy σ g) :=
      Finset.single_le_sum (f := fun g => Nat.card (fixedBy σ g)) (fun _ _ => Nat.zero_le _) (mem_univ _)

omit [Fintype G] in
/-- Hay a lo sumo tantas órbitas como estados. -/
theorem orbitas_le_card : orbitas G σ ≤ Nat.card σ :=
  Nat.card_le_card_of_surjective _ Quotient.mk''_surjective

/-- **La simetría ahorra a lo sumo `log₂ |G|` bits**: `log₂ |σ| − log₂ |G| ≤ log₂ órbitas ≤ log₂ |σ|`. -/
theorem ahorro_acotado :
    Real.logb 2 (Nat.card σ) - Real.logb 2 (Fintype.card G) ≤ infoSalvo G σ ∧
      infoSalvo G σ ≤ Real.logb 2 (Nat.card σ) := by
  refine ⟨?_, logb_nat_mono (orbitas_le_card G σ)⟩
  have hG : 0 < Fintype.card G := Fintype.card_pos
  rcases Nat.eq_zero_or_pos (orbitas G σ) with h0 | hpos
  · have : Nat.card σ = 0 := by
      have := card_le_orbitas_mul G σ
      rw [h0, zero_mul] at this
      omega
    rw [this, infoSalvo, h0]
    simp only [Nat.cast_zero, Real.logb_zero, zero_sub, neg_nonpos]
    exact logb_nat_nonneg _
  · have h := logb_nat_mono (card_le_orbitas_mul G σ)
    rw [Nat.cast_mul, Real.logb_mul (by exact_mod_cast hpos.ne') (by exact_mod_cast hG.ne')] at h
    unfold infoSalvo
    linarith

end Orbitas

/-! ## 2. Testigos salvo simetría -/

section Testigos

variable {G σ : Type*} [Group G] [MulAction G σ]

/-- Los testigos de una propiedad invariante, como sub-acción. -/
def testigos (P : σ → Prop) (hP : ∀ (g : G) x, P (g • x) ↔ P x) : SubMulAction G σ where
  carrier := {x | P x}
  smul_mem' g x hx := (hP g x).mpr hx

/-- Si `G` respeta `P`, el conjunto de testigos es unión de órbitas. -/
theorem testigos_union_de_orbitas (P : σ → Prop) (hP : ∀ (g : G) x, P (g • x) ↔ P x) {x y : σ}
    (hx : P x) (hy : y ∈ orbit G x) : P y := by
  obtain ⟨g, rfl⟩ := hy
  exact (hP g x).mpr hx

variable [Fintype G] [Finite σ]

/-- **Describir un testigo salvo `G`** cuesta `log₂` de las órbitas de testigos, entre
`log₂ |T| − log₂ |G|` y `log₂ |T|`. -/
theorem ahorro_testigos (P : σ → Prop) (hP : ∀ (g : G) x, P (g • x) ↔ P x) :
    Real.logb 2 (Nat.card (testigos P hP)) - Real.logb 2 (Fintype.card G) ≤ infoSalvo G (testigos P hP) ∧
      infoSalvo G (testigos P hP) ≤ Real.logb 2 (Nat.card (testigos P hP)) :=
  ahorro_acotado G (testigos P hP)

end Testigos

/-! ## 3. El palomar con su grupo -/

section Palomar

variable (m n : ℕ)

/-- Las asignaciones de `m` palomas a `n` agujeros que cumplen el palomar: nadie comparte agujero. -/
abbrev Asignacion := Fin m → Fin n

/-- El grupo simétrico de los agujeros actúa por composición: `(g • f) i = g (f i)`. Respeta la inyectividad. -/
theorem inyectiva_invariante (g : Equiv.Perm (Fin n)) (f : Asignacion m n) :
    Function.Injective (g • f) ↔ Function.Injective f := by
  have : (g • f) = g ∘ f := rfl
  rw [this]
  exact ⟨fun h => h.of_comp, fun h => g.injective.comp h⟩

/-- Los emparejamientos perfectos (testigos de `PHP^n_n`). -/
abbrev Emparejamientos := testigos (G := Equiv.Perm (Fin n)) (fun f : Asignacion n n => Function.Injective f)
  (inyectiva_invariante n n)

/-- **Una sola órbita**: dos emparejamientos perfectos difieren en una permutación de los agujeros. -/
theorem palomar_transitivo (f f' : Emparejamientos n) : ∃ g : Equiv.Perm (Fin n), g • f = f' := by
  have hf : Function.Bijective (f : Asignacion n n) := Finite.injective_iff_bijective.mp f.2
  have hf' : Function.Bijective (f' : Asignacion n n) := Finite.injective_iff_bijective.mp f'.2
  refine ⟨(Equiv.ofBijective _ hf).symm.trans (Equiv.ofBijective _ hf'), ?_⟩
  apply Subtype.ext
  funext i
  change (Equiv.ofBijective _ hf') ((Equiv.ofBijective _ hf).symm ((f : Asignacion n n) i)) =
    (f' : Asignacion n n) i
  have : (Equiv.ofBijective _ hf).symm ((f : Asignacion n n) i) = i :=
    (Equiv.ofBijective _ hf).symm_apply_apply i
  rw [this]
  rfl

theorem palomar_una_orbita : orbitas (Equiv.Perm (Fin n)) (Emparejamientos n) = 1 := by
  have : IsPretransitive (Equiv.Perm (Fin n)) (Emparejamientos n) := ⟨fun f f' => palomar_transitivo n f f'⟩
  have hne : Nonempty (Emparejamientos n) := ⟨⟨id, Function.injective_id⟩⟩
  have : Subsingleton (orbitRel.Quotient (Equiv.Perm (Fin n)) (Emparejamientos n)) :=
    (pretransitive_iff_subsingleton_quotient _ _).mp this
  have : Nonempty (orbitRel.Quotient (Equiv.Perm (Fin n)) (Emparejamientos n)) :=
    ⟨Quotient.mk'' (Classical.arbitrary _)⟩
  exact Nat.card_unique

/-- El testigo salvo simetría cuesta `0` bits. -/
theorem palomar_cero_bits : infoSalvo (Equiv.Perm (Fin n)) (Emparejamientos n) = 0 := by
  simp [infoSalvo, palomar_una_orbita]

/-- Sin la simetría hay `n!` testigos: `log₂ n!` bits. -/
theorem palomar_testigos_card : Nat.card (Emparejamientos n) = n.factorial := by
  classical
  have e : (Emparejamientos n) ≃ (Fin n ↪ Fin n) := Equiv.subtypeInjectiveEquivEmbedding (Fin n) (Fin n)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp [Nat.descFactorial_self]

/-- **El palomar**: con `n + 1` palomas no hay testigos. -/
theorem palomar_sin_testigos (f : Asignacion (n + 1) n) : ¬ Function.Injective f := fun h => by
  have := Fintype.card_le_of_injective f h
  simp at this

end Palomar

/-! ## 4. Romper la simetría cuesta -/

section Canonica

variable {G σ : Type*} [Group G] [MulAction G σ]

/-- Una **forma canónica**: constante en cada órbita, y `c x` en la órbita de `x`. -/
structure EsCanonica (G : Type*) [Group G] [MulAction G σ] (c : σ → σ) : Prop where
  invariante : ∀ (g : G) x, c (g • x) = c x
  en_orbita : ∀ x, c x ∈ orbit G x

/-- Siempre hay una (por elección: un representante por órbita). -/
theorem existe_canonica : ∃ c : σ → σ, EsCanonica G c := by
  refine ⟨fun x => (Quotient.mk'' x : orbitRel.Quotient G σ).out, ⟨fun g x => ?_, fun x => ?_⟩⟩
  · rw [show (Quotient.mk'' (g • x) : orbitRel.Quotient G σ) = Quotient.mk'' x from Quotient.sound ⟨g, rfl⟩]
  · have : (orbitRel G σ) (Quotient.mk'' x : orbitRel.Quotient G σ).out x :=
      Quotient.exact (Quotient.out_eq _)
    exact orbitRel_apply.mp this

/-- Curie para la forma canónica: es invariante, gana toda la simetría. -/
theorem canonica_invariante {c : σ → σ} (hc : EsCanonica G c) (g : G) : c ∘ (fun x : σ => g • x) = c :=
  funext fun x => hc.invariante g x

variable [DecidableEq σ] [Fintype σ]

/-- La imagen de una forma canónica tiene exactamente tantos elementos como órbitas. -/
theorem card_image_canonica {c : σ → σ} (hc : EsCanonica G c) :
    ((univ : Finset σ).image c).card = orbitas G σ := by
  -- El cociente se identifica con la imagen.
  have hconst : ∀ x y, (orbitRel G σ) x y → c x = c y := by
    intro x y ⟨g, hg⟩
    rw [← hg, hc.invariante]
  let φ : orbitRel.Quotient G σ → ((univ : Finset σ).image c) :=
    Quotient.lift (fun x => ⟨c x, mem_image_of_mem c (mem_univ x)⟩) (fun x y h => Subtype.ext (hconst x y h))
  have hφi : Function.Injective φ := by
    intro a b hab
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    have hxy : c x = c y := congrArg Subtype.val hab
    apply Quotient.sound
    -- x ~ c x = c y ~ y
    have h1 : c x ∈ orbit G x := hc.en_orbita x
    have h2 : c y ∈ orbit G y := hc.en_orbita y
    rw [hxy] at h1
    change x ∈ orbit G y
    obtain ⟨g, hg⟩ := h1
    obtain ⟨k, hk⟩ := h2
    change g • x = c y at hg
    change k • y = c y at hk
    exact ⟨g⁻¹ * k, by change (g⁻¹ * k) • y = x; rw [mul_smul, hk, ← hg, inv_smul_smul]⟩
  have hφs : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, -, rfl⟩ := mem_image.mp hz
    exact ⟨Quotient.mk'' x, rfl⟩
  rw [orbitas, Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩), Nat.card_eq_fintype_card, Fintype.card_coe]

/-- **Romper la simetría cuesta**: la forma canónica borra exactamente `log₂ |σ| − log₂ órbitas` bits. -/
theorem canonica_borra {c : σ → σ} (hc : EsCanonica G c) :
    bitsBorrados c (univ : Finset σ) = Real.logb 2 (Fintype.card σ) - infoSalvo G σ := by
  rw [bitsBorrados, card_image_canonica hc, card_univ, infoSalvo]

/-- **Ganar simetría exige borrar**: la forma canónica no borra nada si y solo si la acción es trivial. -/
theorem canonica_no_borra_iff {c : σ → σ} (hc : EsCanonica G c) :
    bitsBorrados c (univ : Finset σ) = 0 ↔ ∀ (g : G) (x : σ), g • x = x := by
  rw [Sagitta.Map.Informacion.Reversible.bitsBorrados_eq_cero_iff, coe_univ, Set.injOn_univ]
  constructor
  · intro hinj g x
    exact hinj (hc.invariante g x)
  · intro htriv x y hxy
    obtain ⟨g, hg⟩ := hc.en_orbita x
    obtain ⟨k, hk⟩ := hc.en_orbita y
    change g • x = c x at hg
    change k • y = c y at hk
    rw [htriv] at hg hk
    rw [hg, hk]
    exact hxy

end Canonica

/-! ## 5. Un ejemplo: cadenas de 3 bits bajo rotación

Una cadena de 3 bits es su número en `Fin 8`; rotarla una posición es `x ↦ 2x mod 8 + ⌊x/4⌋`. Las rotaciones son
`ℤ/3`, escrito `Multiplicative (Fin 3)`, y `k` actúa rotando `k` veces. -/

section Ejemplo

/-- Las rotaciones `ℤ/3`. -/
abbrev Rot := Multiplicative (Fin 3)

/-- Rotar la cadena `b₂b₁b₀` a `b₁b₀b₂`. -/
def rot (x : Fin 8) : Fin 8 := ⟨(2 * x.val) % 8 + x.val / 4, by omega⟩

theorem rot_suma : ∀ g h : Fin 3, ∀ x : Fin 8, rot^[(g + h).val] x = rot^[g.val] (rot^[h.val] x) := by
  decide

instance : MulAction Rot (Fin 8) where
  smul g x := rot^[(Multiplicative.toAdd g).val] x
  one_smul _ := rfl
  mul_smul g h x := rot_suma (Multiplicative.toAdd g) (Multiplicative.toAdd h) x

theorem smul_def (g : Rot) (x : Fin 8) : g • x = rot^[(Multiplicative.toAdd g).val] x := rfl

/-- Los puntos fijos: `8` para la identidad, `2` para cada rotación propia (`000` y `111`). -/
theorem ejemplo_fijos :
    ((univ : Finset (Fin 8)).filter fun x => rot^[0] x = x).card = 8 ∧
    ((univ : Finset (Fin 8)).filter fun x => rot^[1] x = x).card = 2 ∧
    ((univ : Finset (Fin 8)).filter fun x => rot^[2] x = x).card = 2 := by
  decide

/-- La forma canónica: la rotación de número mínimo (un predicado *lex-leader*). -/
def canon (x : Fin 8) : Fin 8 := min x (min (rot x) (rot (rot x)))

theorem canon_es_canonica : EsCanonica Rot canon := by
  have h1 : ∀ k : Fin 3, ∀ x : Fin 8, canon (rot^[k.val] x) = canon x := by decide
  have h2 : ∀ x : Fin 8, ∃ k : Fin 3, rot^[k.val] x = canon x := by decide
  refine ⟨fun g x => h1 _ x, fun x => ?_⟩
  obtain ⟨k, hk⟩ := h2 x
  exact ⟨Multiplicative.ofAdd k, hk⟩

/-- **Cuatro órbitas**: `000`, `111`, las de un uno y las de dos unos. -/
theorem ejemplo_orbitas : orbitas Rot (Fin 8) = 4 := by
  rw [← card_image_canonica canon_es_canonica]
  decide

/-- Y Burnside lo confirma: `Σ_g |Fix g| = 4 · 3 = 8 + 2 + 2`. -/
theorem ejemplo_burnside : ∑ g : Rot, Nat.card (fixedBy (Fin 8) g) = 8 + 2 + 2 := by
  rw [burnside, ejemplo_orbitas]
  rfl

/-- **3 bits contra 2 salvo simetría.** -/
theorem ejemplo_bits : Real.logb 2 (Fintype.card (Fin 8)) = 3 ∧ infoSalvo Rot (Fin 8) = 2 := by
  refine ⟨by rw [Fintype.card_fin]; exact_mod_cast logb_dos_pow 3, ?_⟩
  rw [infoSalvo, ejemplo_orbitas]
  exact_mod_cast logb_dos_pow 2

/-- **La forma canónica borra 1 bit.** -/
theorem ejemplo_borra_un_bit : bitsBorrados canon (univ : Finset (Fin 8)) = 1 := by
  rw [canonica_borra canon_es_canonica, ejemplo_bits.1, ejemplo_bits.2]
  norm_num

end Ejemplo

end Sagitta.Map.Informacion.Simetria
