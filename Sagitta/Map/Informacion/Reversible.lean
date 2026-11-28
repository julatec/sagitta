import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Group.Action.Option
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# La reversibilidad como simetría

La idea es de José (25 nov 2026), y la caja «Una simetría y su conservación» de las notas del proyecto la
anuncia: con tiempo reversible, sacar el grupo y, por la forma discreta de Noether, lo que conserva; después romper la
simetría quitando la reversibilidad y medir lo que se pierde. Todo es sobre un conjunto finito de configuraciones `σ`.

## Lo que se prueba

1. **El grupo** (§ 1). Una máquina reversible es un paso `f : Equiv.Perm σ`. Su grupo es `Subgroup.zpowers f`, que
   actúa sobre `σ`; los pasos hacia adelante y hacia atrás son los `f ^ n`, `n : ℤ` (`paso_en_grupo`,
   `paso_atras`). Las órbitas son los ciclos: `mem_orbita_iff_sameCycle`.
2. **Noether discreto** (§ 2). `Q ∘ f = Q` si y solo si `Q` es constante en cada órbita (`conserva_iff_constante_orbitas`).
   Es el «simetría ⇒ invariante» discreto. *Honestidad:* el teorema de Noether propiamente dicho es para simetrías
   continuas (grupos de Lie a un parámetro) de un lagrangiano, y da una corriente conservada; aquí el grupo es `ℤ`
   (o un cíclico finito), no hay lagrangiano y el enunciado es casi tautológico. Es su forma discreta, no el teorema.
3. **Lo que se conserva: la información** (§ 3). `card (S.image (f ^ n)) = card S` para todo `S` y todo `n : ℤ`
   (`card_image_zpow`), luego `log₂` del tamaño tampoco cambia (`bitsBorrados_perm`); el empuje de una distribución es
   la misma lista de pesos permutada y la entropía de Shannon `Σ −μ log μ` se conserva (`entropia_empuje`).
4. **Romper la simetría** (§ 4). Para `g : α → β` cualquiera, `bitsBorrados g S = log₂ |S| − log₂ |g S|`: es `≥ 0`
   (`bitsBorrados_nonneg`), es `0` si y solo si `g` es inyectiva en `S` (`bitsBorrados_eq_cero_iff`), y a lo largo de
   una corrida `g^[n]` se acumula en telescopio (`bitsBorrados_iterate_succ`, `bitsBorrados_iterate_suma`); la imagen
   solo achica (`card_image_iterate_antitone`). `ℕ` actúa por `g^[n]`, pero sin inyectividad no hay inverso
   (`sin_inverso`): ya no hay grupo.
5. **El precio de decidir** (§ 5). Un decisor `d : α → Bool` borra al menos `log₂ N − 1` bits (`decidir_borra`). En
   general, para cualquier estado final `e : α → σ'`, `log₂ N ≤ bitsBorrados e + log₂ |σ'|` (`borrar_o_guardar`): o
   se borra (calor, Landauer) o se guarda (espacio, Bennett). Si no se borra nada, `|σ'| ≥ N` (`guardar_cuesta_espacio`).
6. **Un ejemplo** (§ 6). En `Fin 8`, la rotación `finRotate 8` no borra nada; «dividir por 2» borra exactamente un bit
   por paso durante tres pasos y después ninguno: `8 → 4 → 2 → 1 → 1`.
7. **Noether discreto, forma de Koopman** (§ 7). `koopman f φ = φ ∘ f` sobre `σ → ℂ`, lineal aunque `f` no lo sea.
   (a) `Q ∘ f = Q` si y solo si, para todo `θ`, la multiplicación por `exp(iθQ)` conmuta con `koopman f`
   (`koopman_noether`). Vale para **toda** `f`, reversible o no: la simetría «de fase» y su carga no ven la
   reversibilidad. (b) `koopman f` preserva la norma `ℓ²` si y solo si `f` es biyectiva (`koopman_isometria_iff`);
   en las indicadoras, la norma al cuadrado es el tamaño (`norma2_indicadora`), así que lo que la unitariedad conserva
   es la información del punto 3. (c) Sin reversibilidad (a) sigue y (b) falla, y la falta de unitariedad se mide con
   los bits borrados: para `T = g S`, `‖K_g 1_T‖² = |g⁻¹(g S)| ≥ |S| = 2^(bits borrados) · ‖1_T‖²`
   (`koopman_mide_borrado`), con igualdad si `S` está saturado (`S = g⁻¹(g S)`, `koopman_mide_borrado_saturado`).
   (d) **Curie exacto**: si `f` conmuta con la acción de un grupo `G` y es inyectiva, el estabilizador de `f x` es el
   de `x` (`curie_inyectiva`); sin inyectividad solo `Stab x ≤ Stab (f x)` (`curie_le`), y un estado puede ganar
   simetría al borrar (`curie_estricta_sin_inyectividad`: `Option Bool` con `Perm Bool`, y `f` constante en `none`).

## Antecedentes (verificados en Crossref el 25 nov 2026, no leídos)

El operador de composición `φ ↦ φ ∘ f` es el de Koopman (1931) y Koopman–von Neumann (1932), que vuelve lineal una
dinámica no lineal; la mecánica discreta variacional, con su Noether discreto para simetrías continuas de un
lagrangiano discreto, es de Marsden y West (Acta Numerica, 2001); el Noether para procesos de Markov (simetrías que
conmutan con el generador y cantidades conservadas) es de Baez y Fong (J. Math. Phys., 2013). Koopman: PNAS 17 (1931);
Koopman–von Neumann: PNAS 18 (1932). Lo propio aquí es la formalización y el vínculo de la
falta de unitariedad con el precio de decidir.

## Lo que NO se prueba

* Nada de Landauer como ley física: «calor» es la interpretación del `log₂` que cae, no un teorema.
* Ninguna cota de tiempo para la versión de Bennett: solo el espacio (el tamaño de `σ'`).
* Nada sobre P contra NP.
-/

namespace Sagitta.Map.Informacion.Reversible

open Finset

/-! ## 1. El grupo -/

section Grupo

variable {σ : Type*}

/-- Los pasos hacia adelante y hacia atrás son elementos del grupo generado. -/
theorem paso_en_grupo (f : Equiv.Perm σ) (n : ℤ) : f ^ n ∈ Subgroup.zpowers f :=
  Subgroup.zpow_mem_zpowers f n

/-- Deshacer `n` pasos es dar `−n` pasos. -/
theorem paso_atras (f : Equiv.Perm σ) (n : ℤ) : (f ^ n)⁻¹ = f ^ (-n) := (zpow_neg f n).symm

/-- **Las órbitas son los ciclos.** -/
theorem mem_orbita_iff_sameCycle (f : Equiv.Perm σ) (x y : σ) :
    y ∈ MulAction.orbit (Subgroup.zpowers f) x ↔ f.SameCycle x y := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨f ^ k, paso_en_grupo f k⟩, rfl⟩

end Grupo

/-! ## 2. La forma discreta de Noether -/

section Noether

variable {σ β : Type*}

/-- Lo que se conserva en un paso se conserva en todos, hacia adelante y hacia atrás. -/
theorem conserva_zpow (f : Equiv.Perm σ) (Q : σ → β) (h : Q ∘ f = Q) (n : ℤ) (x : σ) :
    Q ((f ^ n) x) = Q x := by
  have h1 : ∀ y, Q (f y) = Q y := fun y => congrFun h y
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ih, h1]
  | pred k ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    simpa using (h1 (f⁻¹ x)).symm

/-- **Noether discreto.** Una cantidad se conserva si y solo si es constante en cada órbita del grupo. -/
theorem conserva_iff_constante_orbitas (f : Equiv.Perm σ) (Q : σ → β) :
    Q ∘ f = Q ↔ ∀ x y, y ∈ MulAction.orbit (Subgroup.zpowers f) x → Q y = Q x := by
  constructor
  · intro h x y hy
    obtain ⟨k, rfl⟩ := (mem_orbita_iff_sameCycle f x y).mp hy
    exact conserva_zpow f Q h k x
  · intro h
    funext x
    exact h x (f x) ((mem_orbita_iff_sameCycle f x (f x)).mpr ⟨1, by simp⟩)

end Noether

/-! ## 3 y 4. La información: lo que se conserva y lo que se borra -/

section Bits

/-- `log₂` de un natural es monótono (con `log₂ 0 = 0`). -/
theorem logb_nat_mono {a b : ℕ} (h : a ≤ b) : Real.logb 2 a ≤ Real.logb 2 b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.cast_zero, Real.logb_zero]
    exact div_nonneg (Real.log_natCast_nonneg b) (Real.log_nonneg one_le_two)
  · exact Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast ha) (by exact_mod_cast h)

theorem logb_nat_nonneg (a : ℕ) : 0 ≤ Real.logb 2 a := by
  simpa using logb_nat_mono (Nat.zero_le a)

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]

/-- **Los bits borrados** por `g` en el conjunto `S`: lo que cae `log₂` del tamaño. -/
noncomputable def bitsBorrados (g : α → β) (S : Finset α) : ℝ :=
  Real.logb 2 S.card - Real.logb 2 (S.image g).card

/-- Borrar no crea: los bits borrados son `≥ 0`. -/
theorem bitsBorrados_nonneg (g : α → β) (S : Finset α) : 0 ≤ bitsBorrados g S :=
  sub_nonneg.mpr (logb_nat_mono card_image_le)

/-- No se borra nada si y solo si `g` es inyectiva en `S`. -/
theorem bitsBorrados_eq_cero_iff (g : α → β) (S : Finset α) :
    bitsBorrados g S = 0 ↔ Set.InjOn g S := by
  rw [← card_image_iff]
  constructor
  · intro h
    by_contra hne
    have hlt : (S.image g).card < S.card := lt_of_le_of_ne card_image_le hne
    have hpos : 0 < (S.image g).card := by
      rcases S.eq_empty_or_nonempty with rfl | hS
      · simp at hlt
      · exact card_pos.mpr (hS.image g)
    have := Real.logb_lt_logb one_lt_two (Nat.cast_pos.mpr hpos) (Nat.cast_lt.mpr hlt)
    unfold bitsBorrados at h
    linarith
  · intro h
    simp [bitsBorrados, h]

/-- **Una permutación no borra nada**, en ningún número de pasos. -/
theorem card_image_zpow {σ : Type*} [DecidableEq σ] (f : Equiv.Perm σ) (n : ℤ) (S : Finset σ) :
    (S.image (f ^ n)).card = S.card :=
  card_image_of_injective _ (f ^ n).injective

theorem bitsBorrados_perm {σ : Type*} [DecidableEq σ] (f : Equiv.Perm σ) (n : ℤ) (S : Finset σ) :
    bitsBorrados (f ^ n) S = 0 := by
  simp [bitsBorrados, card_image_zpow]

/-- Componer: lo que borra `h ∘ g` es lo que borra `g` más lo que borra `h` en la imagen. -/
theorem bitsBorrados_comp (g : α → β) (h : β → γ) (S : Finset α) :
    bitsBorrados (h ∘ g) S = bitsBorrados g S + bitsBorrados h (S.image g) := by
  simp only [bitsBorrados, ← image_image]
  ring

/-- **El telescopio**, un paso: correr `n + 1` pasos borra lo de `n` más lo del último. -/
theorem bitsBorrados_iterate_succ {σ : Type*} [DecidableEq σ] (g : σ → σ) (n : ℕ) (S : Finset σ) :
    bitsBorrados g^[n + 1] S = bitsBorrados g^[n] S + bitsBorrados g (S.image g^[n]) := by
  rw [Function.iterate_succ']
  exact bitsBorrados_comp _ _ S

/-- **El telescopio** entero: los bits borrados por la corrida son la suma de los de cada paso. -/
theorem bitsBorrados_iterate_suma {σ : Type*} [DecidableEq σ] (g : σ → σ) (n : ℕ) (S : Finset σ) :
    bitsBorrados g^[n] S = ∑ k ∈ range n, bitsBorrados g (S.image g^[k]) := by
  induction n with
  | zero => simp [bitsBorrados]
  | succ n ih => rw [bitsBorrados_iterate_succ, ih, sum_range_succ]

/-- La imagen solo achica. -/
theorem card_image_iterate_antitone {σ : Type*} [DecidableEq σ] (g : σ → σ) (S : Finset σ) (n : ℕ) :
    (S.image g^[n + 1]).card ≤ (S.image g^[n]).card := by
  rw [Function.iterate_succ', ← image_image]
  exact card_image_le

/-- **Sin inyectividad no hay grupo**: ningún paso deshace a `g`. -/
theorem sin_inverso {σ : Type*} (g : σ → σ) (hg : ¬ Function.Injective g) :
    ¬ ∃ h : σ → σ, Function.LeftInverse h g :=
  fun ⟨_, hh⟩ => hg hh.injective

/-- **La entropía de Shannon se conserva**: el empuje por una permutación es la misma lista de pesos. -/
theorem entropia_empuje {σ : Type*} [Fintype σ] (f : Equiv.Perm σ) (μ : σ → ℝ) :
    ∑ y, Real.negMulLog (μ (f.symm y)) = ∑ x, Real.negMulLog (μ x) :=
  Equiv.sum_comp f.symm (fun x => Real.negMulLog (μ x))

end Bits

/-! ## 5. El precio de decidir -/

section Decidir

variable {α σ' : Type*} [Fintype α] [Fintype σ'] [DecidableEq σ']

/-- **Borrar o guardar.** Para cualquier estado final `e`, `log₂ N ≤ bits borrados + log₂ |σ'|`. -/
theorem borrar_o_guardar (e : α → σ') :
    Real.logb 2 (Fintype.card α) ≤ bitsBorrados e univ + Real.logb 2 (Fintype.card σ') := by
  have := logb_nat_mono (card_le_univ (univ.image e))
  unfold bitsBorrados
  rw [card_univ] at *
  linarith

/-- **El precio de decidir**: un decisor que solo guarda la respuesta borra al menos `log₂ N − 1` bits. -/
theorem decidir_borra (d : α → Bool) :
    Real.logb 2 (Fintype.card α) - 1 ≤ bitsBorrados d univ := by
  have h := borrar_o_guardar d
  have h2 : Real.logb 2 (Fintype.card Bool) = 1 := by simp
  linarith

/-- **Guardar cuesta espacio** (Bennett): si no se borra nada, hacen falta `N` configuraciones. -/
theorem guardar_cuesta_espacio (e : α → σ') (h : bitsBorrados e univ = 0) :
    Fintype.card α ≤ Fintype.card σ' := by
  rw [bitsBorrados_eq_cero_iff] at h
  exact Fintype.card_le_of_injective e (fun a b hab => h (mem_coe.mpr (mem_univ a))
    (mem_coe.mpr (mem_univ b)) hab)

end Decidir

/-! ## 6. Un ejemplo con números: `Fin 8` -/

section Ejemplo

/-- Dividir por dos. -/
def mitad (x : Fin 8) : Fin 8 := ⟨x.val / 2, by omega⟩

theorem logb_dos_pow (k : ℕ) : Real.logb 2 ((2 ^ k : ℕ) : ℝ) = k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- El ciclo de largo 8 no borra nada, en ningún conjunto. -/
theorem rotar_conserva (S : Finset (Fin 8)) : bitsBorrados (finRotate 8) S = 0 := by
  simpa using bitsBorrados_perm (finRotate 8) 1 S

theorem mitad_tamanos :
    ((univ : Finset (Fin 8)).image mitad^[0]).card = 2 ^ 3 ∧
    ((univ : Finset (Fin 8)).image mitad^[1]).card = 2 ^ 2 ∧
    ((univ : Finset (Fin 8)).image mitad^[2]).card = 2 ^ 1 ∧
    ((univ : Finset (Fin 8)).image mitad^[3]).card = 2 ^ 0 ∧
    ((univ : Finset (Fin 8)).image mitad^[4]).card = 2 ^ 0 := by
  decide

/-- **Dividir por dos borra un bit por paso** mientras quede algo que borrar: `8 → 4 → 2 → 1`. -/
theorem mitad_borra_un_bit (k : ℕ) (hk : k < 3) :
    bitsBorrados mitad ((univ : Finset (Fin 8)).image mitad^[k]) = 1 := by
  have e : ∀ k, (univ : Finset (Fin 8)).image mitad^[k + 1] =
      ((univ : Finset (Fin 8)).image mitad^[k]).image mitad := fun k => by
    rw [Function.iterate_succ', ← image_image]
  obtain ⟨h0, h1, h2, h3, -⟩ := mitad_tamanos
  unfold bitsBorrados
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · rw [← e, h0, h1, logb_dos_pow, logb_dos_pow]; norm_num
  · rw [← e, h1, h2, logb_dos_pow, logb_dos_pow]; norm_num
  · rw [← e, h2, h3, logb_dos_pow, logb_dos_pow]; norm_num

/-- Y después, nada: el punto fijo `0` ya no tiene qué borrar. -/
theorem mitad_despues_nada :
    bitsBorrados mitad ((univ : Finset (Fin 8)).image mitad^[3]) = 0 := by
  rw [bitsBorrados_eq_cero_iff]
  decide

/-- La corrida de tres pasos borra los tres bits de `Fin 8`. -/
theorem mitad_tres_pasos : bitsBorrados mitad^[3] (univ : Finset (Fin 8)) = 3 := by
  rw [bitsBorrados_iterate_suma, sum_range_succ, sum_range_succ, sum_range_one,
    mitad_borra_un_bit 0 (by norm_num), mitad_borra_un_bit 1 (by norm_num), mitad_borra_un_bit 2 (by norm_num)]
  norm_num

end Ejemplo

/-! ## 7. Noether discreto, forma de Koopman -/

section Koopman

variable {σ : Type*}

/-- **El operador de Koopman**: `φ ↦ φ ∘ f`. Lineal aunque `f` no lo sea. -/
noncomputable def koopman (f : σ → σ) : (σ → ℂ) →ₗ[ℂ] (σ → ℂ) := LinearMap.funLeft ℂ ℂ f

/-- La multiplicación por `φ`. -/
noncomputable def mult (φ : σ → ℂ) : (σ → ℂ) →ₗ[ℂ] (σ → ℂ) := LinearMap.mulLeft ℂ φ

@[simp] theorem koopman_apply (f : σ → σ) (φ : σ → ℂ) : koopman f φ = φ ∘ f := rfl
@[simp] theorem mult_apply (φ ψ : σ → ℂ) : mult φ ψ = φ * ψ := rfl

/-- Una multiplicación conmuta con Koopman si y solo si su función es invariante. -/
theorem conmuta_iff (f : σ → σ) (φ : σ → ℂ) :
    (koopman f).comp (mult φ) = (mult φ).comp (koopman f) ↔ φ ∘ f = φ := by
  constructor
  · intro h
    have := LinearMap.congr_fun h 1
    simpa [koopman_apply, mult_apply] using this
  · intro h
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.comp_apply, koopman_apply, mult_apply]
    funext x
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [← congrFun h x]
    rfl

/-- La fase `exp(iθQ)`. -/
noncomputable def fase (θ : ℝ) (Q : σ → ℝ) : σ → ℂ := fun x => Complex.exp (((θ * Q x : ℝ) : ℂ) * Complex.I)

/-- Si las fases coinciden para todo `θ`, los valores coinciden (con `θ = π / (a − b)` alcanza). -/
theorem eq_of_fases (a b : ℝ)
    (h : ∀ θ : ℝ, Complex.exp (((θ * a : ℝ) : ℂ) * Complex.I) = Complex.exp (((θ * b : ℝ) : ℂ) * Complex.I)) :
    a = b := by
  by_contra hab
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  set θ := Real.pi / (a - b)
  have hθ : θ * a = θ * b + Real.pi := by
    simp only [θ]; field_simp; ring
  have := h θ
  rw [hθ, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at this
  have : (2 : ℂ) * Complex.exp (((θ * b : ℝ) : ℂ) * Complex.I) = 0 := by linear_combination -this
  simp at this

/-- **Noether discreto, forma de Koopman.** `Q` se conserva si y solo si todas sus fases `exp(iθQ)` conmutan con
el operador de Koopman. Vale para toda `f`, reversible o no. -/
theorem koopman_noether (f : σ → σ) (Q : σ → ℝ) :
    Q ∘ f = Q ↔ ∀ θ : ℝ, (koopman f).comp (mult (fase θ Q)) = (mult (fase θ Q)).comp (koopman f) := by
  simp only [conmuta_iff]
  constructor
  · intro h θ
    funext x
    change Complex.exp (((θ * Q (f x) : ℝ) : ℂ) * Complex.I) = _
    rw [show Q (f x) = Q x from congrFun h x]
    rfl
  · intro h
    funext x
    exact eq_of_fases _ _ (fun θ => congrFun (h θ) x)

variable [Fintype σ]

/-- La norma `ℓ²` al cuadrado. -/
noncomputable def norma2 (φ : σ → ℂ) : ℝ := ∑ x, Complex.normSq (φ x)

/-- La indicadora de un predicado. -/
noncomputable def ind (p : σ → Prop) [DecidablePred p] : σ → ℂ := fun x => if p x then 1 else 0

theorem norma2_ind (p : σ → Prop) [DecidablePred p] : norma2 (ind p) = (univ.filter p).card := by
  simp [norma2, ind, apply_ite Complex.normSq, sum_boole]

/-- En una indicadora, la norma al cuadrado es el tamaño: la información del § 3. -/
theorem norma2_indicadora [DecidableEq σ] (S : Finset σ) : norma2 (ind (· ∈ S)) = S.card := by
  rw [norma2_ind]; simp

/-- **(b) Unitariedad ⟺ reversibilidad.** -/
theorem koopman_isometria_iff (f : σ → σ) :
    (∀ φ, norma2 (koopman f φ) = norma2 φ) ↔ Function.Bijective f := by
  classical
  constructor
  · intro h
    have hfib : ∀ y, (univ.filter (fun x => f x = y)).card = 1 := by
      intro y
      have := h (ind (· = y))
      have e : koopman f (ind (· = y)) = ind (fun x => f x = y) := rfl
      have hy : (univ.filter (fun x : σ => x = y)).card = 1 :=
        card_eq_one.mpr ⟨y, by ext; simp⟩
      rw [e, norma2_ind, norma2_ind, hy] at this
      exact_mod_cast this
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · obtain ⟨c, hc⟩ := card_eq_one.mp (hfib (f b))
      have ha : a ∈ univ.filter (fun x => f x = f b) := by simp [hab]
      have hb : b ∈ univ.filter (fun x => f x = f b) := by simp
      rw [hc, mem_singleton] at ha hb
      rw [ha, hb]
    · obtain ⟨c, hc⟩ := card_eq_one.mp (hfib y)
      have : c ∈ univ.filter (fun x => f x = y) := by rw [hc]; exact mem_singleton_self c
      exact ⟨c, (mem_filter.mp this).2⟩
  · intro hf φ
    exact Equiv.sum_comp (Equiv.ofBijective f hf) (fun y => Complex.normSq (φ y))

/-- **(c) La falta de unitariedad mide lo borrado.** Con `T = g S`:
`‖K_g 1_T‖² = |g⁻¹ T|` y `|S| = 2^(bits borrados) · ‖1_T‖²`, así que
`2^(bits borrados) · ‖1_T‖² ≤ ‖K_g 1_T‖²`. -/
theorem koopman_mide_borrado [DecidableEq σ] (g : σ → σ) (S : Finset σ) (hS : S.Nonempty) :
    (2 : ℝ) ^ bitsBorrados g S * norma2 (ind (· ∈ S.image g)) =
        S.card ∧
      (S.card : ℝ) ≤ norma2 (koopman g (ind (· ∈ S.image g))) := by
  have hpos : (0 : ℝ) < (S.image g).card := by exact_mod_cast card_pos.mpr (hS.image g)
  have hpos' : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  constructor
  · rw [norma2_indicadora, bitsBorrados, Real.rpow_sub two_pos, Real.rpow_logb two_pos (by norm_num) hpos',
      Real.rpow_logb two_pos (by norm_num) hpos]
    field_simp
  · have e : koopman g (ind (· ∈ S.image g)) = ind (fun x => g x ∈ S.image g) := rfl
    rw [e, norma2_ind]
    exact_mod_cast card_le_card (fun x hx => mem_filter.mpr ⟨mem_univ x, mem_image_of_mem g hx⟩)

/-- Con igualdad si `S` está saturado: `S = g⁻¹(g S)`. -/
theorem koopman_mide_borrado_saturado [DecidableEq σ] (g : σ → σ) (S : Finset σ)
    (hsat : ∀ x, g x ∈ S.image g → x ∈ S) :
    norma2 (koopman g (ind (· ∈ S.image g))) = S.card := by
  have e : koopman g (ind (· ∈ S.image g)) = ind (fun x => g x ∈ S.image g) := rfl
  rw [e, norma2_ind]
  congr 2
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hsat x, mem_image_of_mem g⟩

/-- En el ejemplo de `Fin 8`, «dividir por dos» en todo `Fin 8`: `‖K 1_T‖² = 8 = 2^1 · 4`. -/
theorem mitad_koopman : norma2 (koopman mitad (ind (· ∈ (univ : Finset (Fin 8)).image mitad))) = 8 := by
  rw [koopman_mide_borrado_saturado mitad univ (fun x _ => mem_univ x)]
  simp

end Koopman

/-! ## (d) El principio de Curie -/

section Curie

variable {G σ : Type*} [Group G] [MulAction G σ]

/-- Un paso equivariante nunca quita simetría: `Stab x ≤ Stab (f x)`. -/
theorem curie_le (f : σ → σ) (hf : ∀ (g : G) x, f (g • x) = g • f x) (x : σ) :
    MulAction.stabilizer G x ≤ MulAction.stabilizer G (f x) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← hf, hg]

/-- **Curie exacto**: si además es inyectivo, conserva la simetría de cada estado. -/
theorem curie_inyectiva (f : σ → σ) (hf : ∀ (g : G) x, f (g • x) = g • f x) (hinj : Function.Injective f)
    (x : σ) : MulAction.stabilizer G (f x) = MulAction.stabilizer G x := by
  refine le_antisymm (fun g hg => ?_) (curie_le f hf x)
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  exact hinj (by rw [hf, hg])

/-- **Borrar puede ganar simetría.** `Perm Bool` actúa en `Option Bool`; la constante `none` es equivariante, y el
estabilizador de `some true` es trivial mientras el de su imagen es todo. -/
theorem curie_estricta_sin_inyectividad :
    ∃ f : Option Bool → Option Bool, (∀ (g : Equiv.Perm Bool) x, f (g • x) = g • f x) ∧
      MulAction.stabilizer (Equiv.Perm Bool) (some true) ≠
        MulAction.stabilizer (Equiv.Perm Bool) (f (some true)) := by
  refine ⟨fun _ => none, fun g x => (Option.smul_none g).symm, fun h => ?_⟩
  have hs : Equiv.swap true false ∈ MulAction.stabilizer (Equiv.Perm Bool) (none : Option Bool) :=
    MulAction.mem_stabilizer_iff.mpr (Option.smul_none _)
  rw [← h, MulAction.mem_stabilizer_iff, Option.smul_some, Equiv.Perm.smul_def] at hs
  simp at hs

end Curie

end Sagitta.Map.Informacion.Reversible
