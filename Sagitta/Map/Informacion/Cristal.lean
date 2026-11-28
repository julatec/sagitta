import Sagitta.Map.Continuo.MemoriaPeriodica
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log

/-!
# El cristal de tiempo computacional

La idea del cristal de tiempo computacional (ver las notas del proyecto): por la CHT la ley es la
misma en cada paso (simétrica bajo `t ↦ t + 1`); con memoria finita el estado termina en un ciclo de largo `λ` y solo
es simétrico bajo `t ↦ t + λ`. Si `λ > 1`, la simetría se rompió sola. Este archivo lo prueba.

Notación: la trayectoria es `t ↦ f^[t] x`, con `f : σ → σ` la regla (la misma en cada paso) y `σ` finito. Un `μ` con
`f^[μ] x` periódico es un instante dentro del ciclo; `λ = minimalPeriod f (f^[μ] x)` es el largo del ciclo.

* **(a) Cristalizar** (`cristaliza`): hay `μ` y `λ ≥ 1` con `μ + λ ≤ |σ|`, `λ` el período mínimo del ciclo, y
  `x(t + λ) = x(t)` para todo `t ≥ μ`. Sale de `MemoriaPeriodica.finalmente_periodica`.
* **(b) La ruptura espontánea.** La ley es invariante bajo cualquier traslación (`ley_invariante`: la trayectoria
  trasladada cumple la misma regla). El estado no: las traslaciones que dejan fija la trayectoria final son
  exactamente los múltiplos de `λ` (`traslaciones_fijas`, `traslaciones_fijas_eq`), y si `λ > 1` el estado cambia en
  el ciclo (`ruptura`).
* **(c) El reloj propio.** La fase `φ(t) = (t − μ) mod λ` en `ZMod λ` avanza de a uno (`fase_succ`) y **se lee del
  estado** (`fase_se_lee`: hay `g : σ → ZMod λ` con `g (x t) = φ t` para todo `t ≥ μ`). Por eso el ciclo cabe en el
  estado: `λ ≤ |σ|` (`ciclo_le_card`), y con `|σ| ≤ 2^s`, `log₂ λ ≤ s` (`ciclo_bits`).
* **(d) Un juguete de robustez.** Tres copias de un bit; el paso pone las tres en `NO(mayoría)`; un adversario
  invierte a lo sumo una copia por paso. La mayoría oscila con período 2 para siempre (`robusto`, `periodo_dos`,
  `fase_robusta`), sea cual sea el adversario y el estado inicial. Controles: con una sola copia, una corrupción
  rompe el período (`una_copia_se_rompe`); con tres copias y dos corrupciones por paso, también (`dos_corrupciones`).
  Es la corrección de errores como robustez del cristal. **Es un juguete**: no es el cristal de Toom ni la
  construcción de Gács (que son autómatas celulares con ruido local en todo el espacio); aquí el ruido es acotado por
  paso y la corrección es una mayoría global de tres bits.

## Lo que no se prueba

* Nada de física. El cristal es una analogía; lo que se prueba es la combinatoria del ciclo.
* La robustez de (d) es contra un adversario acotado (una copia por paso), no contra ruido aleatorio ni local.
-/

namespace Sagitta.Map.Informacion.Cristal

open Function
open Sagitta.Map.Continuo.Memoria

variable {σ : Type*} (f : σ → σ) (x : σ)

/-! ## (a) La CHT más la memoria finita cristalizan -/

/-- Si `f^[μ] x` es periódico con período `q`, la trayectoria desde `μ` lo es. -/
theorem desde_mu {μ q : ℕ} (hq : IsPeriodicPt f q (f^[μ] x)) {t : ℕ} (ht : μ ≤ t) : f^[t + q] x = f^[t] x := by
  rw [show t + q = (t - μ) + (q + μ) by omega, iterate_add_apply, iterate_add_apply, hq.eq, ← iterate_add_apply,
    show t - μ + μ = t by omega]

/-- **Cristalizar**: hay un transitorio `μ` y un ciclo de período mínimo `λ ≥ 1` con `μ + λ ≤ |σ|`, y la trayectoria
es periódica con período `λ` desde `μ`. -/
theorem cristaliza [Fintype σ] :
    ∃ μ p, 0 < p ∧ μ + p ≤ Fintype.card σ ∧ f^[μ] x ∈ periodicPts f ∧ minimalPeriod f (f^[μ] x) = p ∧
      ∀ t, μ ≤ t → f^[t + p] x = f^[t] x := by
  obtain ⟨μ, q, hq, hle, hper⟩ := finalmente_periodica f x
  have hy : IsPeriodicPt f q (f^[μ] x) := by
    change f^[q] (f^[μ] x) = f^[μ] x
    rw [← iterate_add_apply, add_comm]; exact hper μ le_rfl
  have hpos := hy.minimalPeriod_pos hq
  have hle' := hy.minimalPeriod_le hq
  exact ⟨μ, _, hpos, by omega, mk_mem_periodicPts hq hy, rfl, fun t ht =>
    desde_mu f x (isPeriodicPt_minimalPeriod f _) ht⟩

/-! ## (b) La ruptura espontánea -/

/-- **La ley es invariante bajo traslaciones**: la trayectoria trasladada `k` pasos cumple la misma regla. -/
theorem ley_invariante (k t : ℕ) : f^[(t + 1) + k] x = f (f^[t + k] x) := by
  rw [show t + 1 + k = (t + k) + 1 by omega, iterate_succ_apply']

/-- **Las traslaciones que fijan la trayectoria final son los múltiplos de `λ`.** -/
theorem traslaciones_fijas {μ : ℕ} (k : ℕ) :
    (∀ t, μ ≤ t → f^[t + k] x = f^[t] x) ↔ minimalPeriod f (f^[μ] x) ∣ k := by
  constructor
  · intro h
    apply IsPeriodicPt.minimalPeriod_dvd
    change f^[k] (f^[μ] x) = f^[μ] x
    rw [← iterate_add_apply, add_comm]; exact h μ le_rfl
  · rintro ⟨m, rfl⟩ t ht
    exact desde_mu f x ((isPeriodicPt_minimalPeriod f _).mul_const m) ht

theorem traslaciones_fijas_eq (μ : ℕ) :
    {k | ∀ t, μ ≤ t → f^[t + k] x = f^[t] x} = {k | minimalPeriod f (f^[μ] x) ∣ k} :=
  Set.ext fun k => traslaciones_fijas f x k

/-- **La ruptura**: si el ciclo tiene largo `λ > 1`, el estado no es invariante bajo `t ↦ t + 1`: en cada instante
del ciclo, `x(t + 1) ≠ x(t)`. -/
theorem ruptura {μ : ℕ} (hl : 1 < minimalPeriod f (f^[μ] x)) {t : ℕ} (ht : μ ≤ t) : f^[t + 1] x ≠ f^[t] x := by
  intro e
  have hfix : f (f^[t] x) = f^[t] x := by rw [← iterate_succ_apply' f t x]; exact e
  have hp : IsPeriodicPt f 1 (f^[t] x) := by simpa [IsPeriodicPt, IsFixedPt] using hfix
  -- `f^[t] x` está en el ciclo de `f^[μ] x`, y tiene el mismo período mínimo.
  have hmem : f^[μ] x ∈ periodicPts f :=
    minimalPeriod_pos_iff_mem_periodicPts.1 (by omega)
  have e2 : f^[t] x = f^[t - μ] (f^[μ] x) := by rw [← iterate_add_apply, show t - μ + μ = t by omega]
  have := minimalPeriod_apply_iterate hmem (t - μ)
  rw [← e2] at this
  have h1 := hp.minimalPeriod_dvd
  rw [this, Nat.dvd_one] at h1
  omega

/-! ## (c) El reloj propio -/

/-- La fase: `(t − μ) mod λ`. -/
def fase (μ p t : ℕ) : ZMod p := ((t - μ : ℕ) : ZMod p)

/-- **La fase avanza de a uno** en el ciclo. -/
theorem fase_succ (μ p : ℕ) {t : ℕ} (ht : μ ≤ t) : fase μ p (t + 1) = fase μ p t + 1 := by
  simp only [fase]
  rw [show t + 1 - μ = (t - μ) + 1 by omega]
  push_cast; ring

/-- **La fase se lee del estado**: hay una función del estado a `ZMod λ` que da la fase en todo instante del ciclo. -/
theorem fase_se_lee {μ : ℕ} (hμ : f^[μ] x ∈ periodicPts f) :
    ∃ g : σ → ZMod (minimalPeriod f (f^[μ] x)), ∀ t, μ ≤ t → g (f^[t] x) = fase μ (minimalPeriod f (f^[μ] x)) t := by
  classical
  set y := f^[μ] x
  set p := minimalPeriod f y
  have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts hμ
  have hinj : Set.InjOn (fun n => f^[n] y) (Set.Iio p) := iterate_injOn_Iio_minimalPeriod
  refine ⟨fun z => ((invFunOn (fun n => f^[n] y) (Set.Iio p) z : ℕ) : ZMod p), fun t ht => ?_⟩
  set r := (t - μ) % p
  have hr : r < p := Nat.mod_lt _ hp
  have ey : f^[t] x = f^[r] y := by
    rw [iterate_mod_minimalPeriod_eq, ← iterate_add_apply, show t - μ + μ = t by omega]
  have hex : ∃ a ∈ Set.Iio p, (fun n => f^[n] y) a = f^[t] x := ⟨r, hr, ey.symm⟩
  have h1 := invFunOn_eq hex
  have h2 := invFunOn_mem hex
  have hrr : invFunOn (fun n => f^[n] y) (Set.Iio p) (f^[t] x) = r := hinj h2 (show r ∈ Set.Iio p from hr) (h1.trans ey)
  simp only [hrr, fase, r]
  exact ZMod.natCast_mod _ _

/-- **El ciclo cabe en el estado**: `λ ≤ |σ|`. -/
theorem ciclo_le_card [Fintype σ] (y : σ) : minimalPeriod f y ≤ Fintype.card σ := by
  classical
  have hinj : Set.InjOn (fun n => f^[n] y) (Set.Iio (minimalPeriod f y)) := iterate_injOn_Iio_minimalPeriod
  have h : Set.InjOn (fun n => f^[n] y) ↑(Finset.range (minimalPeriod f y)) := by
    simpa [Finset.coe_range] using hinj
  calc minimalPeriod f y = (Finset.range (minimalPeriod f y)).card := (Finset.card_range _).symm
    _ = ((Finset.range (minimalPeriod f y)).image fun n => f^[n] y).card := (Finset.card_image_of_injOn h).symm
    _ ≤ Fintype.card σ := Finset.card_le_univ _

/-- **En bits**: el estado lleva al menos `log₂ λ` bits de reloj; con `|σ| ≤ 2^s`, `log₂ λ ≤ s`. -/
theorem ciclo_bits [Fintype σ] (y : σ) {s : ℕ} (hs : Fintype.card σ ≤ 2 ^ s) : Nat.log 2 (minimalPeriod f y) ≤ s :=
  calc Nat.log 2 (minimalPeriod f y) ≤ Nat.log 2 (2 ^ s) := Nat.log_mono_right ((ciclo_le_card f y).trans hs)
    _ = s := Nat.log_pow (by norm_num) s

/-- Un ejemplo: la rotación de `Fin 3` desde `0` tiene `μ = 0` y `λ = 3`: período de la regla 1, del estado 3. -/
theorem rotacion_tres : minimalPeriod (fun q : Fin 3 => q + 1) 0 = 3 := by
  have h3 : IsPeriodicPt (fun q : Fin 3 => q + 1) 3 0 := by decide
  have hd := h3.minimalPeriod_dvd
  have hle := h3.minimalPeriod_le (by norm_num)
  have hpos := h3.minimalPeriod_pos (by norm_num)
  have h1 : minimalPeriod (fun q : Fin 3 => q + 1) 0 ≠ 1 := by
    intro e
    have := isPeriodicPt_minimalPeriod (fun q : Fin 3 => q + 1) 0
    rw [e] at this
    exact absurd this (by decide)
  have : minimalPeriod (fun q : Fin 3 => q + 1) 0 ∣ 3 := hd
  rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h
  · exact absurd h h1
  · exact h

/-! ## (d) Un juguete de robustez -/

/-- Tres copias de un bit. -/
abbrev Tres := Fin 3 → Bool

def mayoria (z : Tres) : Bool := (z 0 && z 1) || (z 0 && z 2) || (z 1 && z 2)

/-- El paso: las tres copias pasan a `NO(mayoría)`. -/
def pasoNM (z : Tres) : Tres := fun _ => !mayoria z

/-- Cuántas copias invierte una máscara. -/
def peso (m : Tres) : ℕ := (Finset.univ.filter fun i => m i = true).card

/-- La corrida con un adversario: después de cada paso, la máscara `adv t` invierte las copias que marca. -/
def corrida (adv : ℕ → Tres) (z₀ : Tres) : ℕ → Tres
  | 0 => z₀
  | t + 1 => fun i => xor (adv t i) (pasoNM (corrida adv z₀ t) i)

/-- Una corrupción no le cambia la mayoría a tres copias iguales. -/
theorem mayoria_resiste : ∀ (m : Tres) (b : Bool), peso m ≤ 1 → mayoria (fun i => xor (m i) b) = b := by
  decide

/-- **Robusto**: con a lo sumo una copia corrompida por paso, la mayoría se invierte en cada paso. -/
theorem robusto (adv : ℕ → Tres) (h : ∀ t, peso (adv t) ≤ 1) (z₀ : Tres) (t : ℕ) :
    mayoria (corrida adv z₀ (t + 1)) = !mayoria (corrida adv z₀ t) :=
  mayoria_resiste (adv t) _ (h t)

/-- **Período 2 para siempre.** -/
theorem periodo_dos (adv : ℕ → Tres) (h : ∀ t, peso (adv t) ≤ 1) (z₀ : Tres) (t : ℕ) :
    mayoria (corrida adv z₀ (t + 2)) = mayoria (corrida adv z₀ t) := by
  rw [robusto adv h z₀ (t + 1), robusto adv h z₀ t, Bool.not_not]

/-- **La fase sobrevive**: la mayoría en el paso `t` es la inicial invertida según la paridad de `t`. -/
theorem fase_robusta (adv : ℕ → Tres) (h : ∀ t, peso (adv t) ≤ 1) (z₀ : Tres) (t : ℕ) :
    mayoria (corrida adv z₀ t) = xor (mayoria z₀) (decide (t % 2 = 1)) := by
  induction t with
  | zero => simp [corrida]
  | succ t ih =>
    rw [robusto adv h z₀ t, ih]
    rcases Nat.mod_two_eq_zero_or_one t with e | e
    · have e' : (t + 1) % 2 = 1 := by omega
      simp [e, e']
    · have e' : (t + 1) % 2 = 0 := by omega
      simp [e, e']

/-- **Control: con una sola copia, una corrupción rompe el período.** -/
def corrida1 (adv : ℕ → Bool) (z₀ : Bool) : ℕ → Bool
  | 0 => z₀
  | t + 1 => xor (adv t) (!corrida1 adv z₀ t)

theorem una_copia_se_rompe (z₀ : Bool) : ∃ adv : ℕ → Bool, corrida1 adv z₀ 1 = corrida1 adv z₀ 0 :=
  ⟨fun _ => true, by cases z₀ <;> rfl⟩

/-- **Control: con tres copias y dos corrupciones por paso, también se rompe.** -/
theorem dos_corrupciones : ∃ adv : ℕ → Tres, (∀ t, peso (adv t) ≤ 2) ∧
    mayoria (corrida adv (fun _ => false) 1) = mayoria (corrida adv (fun _ => false) 0) := by
  have hp : peso ![true, true, false] ≤ 2 := by decide
  exact ⟨fun _ => ![true, true, false], fun _ => hp, by decide⟩

/- Mutantes (25 nov 2026, fuera del repositorio); los cinco fallaron:
* M7: `cristaliza` con `μ + λ < |σ|`: falla `omega` (el palomar da `≤`; `rotacion_tres` tiene `0 + 3 = 3`).
* M8: `traslaciones_fijas` con `λ = k` en vez de `λ ∣ k`: falla `apply` (y es falso con `k = 2λ`).
* M9: `ruptura` sin `1 < λ`: falla `omega` al final; y es falso en un punto fijo.
* M10: `fase_se_lee` para todo `t`, sin `μ ≤ t`: falla `omega` en `t − μ + μ = t` (antes del ciclo no hay fase).
* M11: `mayoria_resiste` con dos corrupciones: `decide` prueba que es falso (es `dos_corrupciones`). -/

end Sagitta.Map.Informacion.Cristal
