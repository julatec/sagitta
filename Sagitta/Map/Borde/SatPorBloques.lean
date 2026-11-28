import Sagitta.Map.Borde.SatEnElBorde

/-!
# SAT por bloques: la oscilación forzada (fase B2b)

La idea de José (24 nov 2026): forzar la oscilación con largos infinitos. Para un conjunto de largos `B : Set ℕ`, el
problema `porBloques B` es SAT enmarcado (`satMarco` de `Relleno.lean`) en los largos de `B` y la constante «no» fuera
de `B`. Es la trampa de los largos pares de `existe_solo_en_el_limite` (`Infinito.lean`), con SAT en vez de la función
difícil de Shannon, y con el conjunto de largos como parámetro. `porBloques B` no es rellenable en general: por eso
escapa de `tricotomia_rellenable` (`SatEnElBorde.lean`) y de la jugada de relleno de `PBombeo.lean`, que exigen relleno.

## Lo que se prueba (circuitos)

* `sucNat_dentro`, `sucNat_fuera`: en un largo de `B` el costo de `porBloques B` es **exactamente** el de `satMarco`; fuera
  de `B` es a lo sumo una compuerta.
* (i) **El lado fácil es gratis** (`no_sobre_de_complemento`, `constante_en_complemento`): si `Bᶜ` es infinito, el costo
  no está arriba; en todo largo infinito concentrado en `Bᶜ` el circuito óptimo tiene a lo sumo una compuerta. Así que
  `porBloques B` está en P/poly u oscila (`psobrePoly_u_oscila`), nunca arriba.
* (ii) **Oscilar es SAT difícil en `B`** (`fuera_iff_sat_dificil_en`): `porBloques B ∉ PsobrePoly` si y solo si hay un
  largo infinito concentrado en `B` donde el costo de `satMarco` le gana a todo polinomio.
* (iii) **La versión no constructiva de Ladner** (`ladner_no_constructivo`): si `satBits ∉ PsobrePoly`, hay un `B` con
  `Bᶜ` infinito tal que `porBloques B` está fuera de P/poly, y por lo tanto oscila. Los largos de `B` son los `g m` donde
  el costo pasa de `m·(n+1)^m`, como en la prueba de `fuera_de_pol_iff`, separados por al menos un largo.
* **No es más difícil que SAT** (`dentro_fija_sat`, `sucNat_porBloques_le`, `porBloques_de_sat`): en los largos de
  `B` la rebanada se obtiene de la de `satMarco` fijando entradas (`SeObtieneFijando`, con la identidad), y si `satMarco`
  está en P/poly, `porBloques B` también.

## Lo que NO da, y por qué es Ladner

El `B` de (iii) **no se decide en tiempo polinomial**: para saber si un largo está en `B` hay que saber si SAT es difícil
en ese largo, que es tan difícil como el problema mismo. Así que `porBloques B` no está en NP, y (iii) no es el teorema de
Ladner (1975), que da un problema de NP que no está en P ni es NP-completo si P ≠ NP. Lo que Ladner pone es exactamente
lo que falta aquí: un `B` barato, que se calcula con un reloj de unos `log n` pasos que simula la búsqueda de un
resolvedor o una reducción que falla (la «diagonalización perezosa»). Es otra fase del plan (ver las notas del proyecto), y no se intenta.

La distancia entre (iii) y Ladner es la distancia entre el ultrafiltro no constructivo de `Infinito.lean` (elegir los
largos difíciles sin decir cómo se reconocen) y un reloj barato. Tampoco se hace B3 (pasar de circuitos a tiempo).
-/

open Filter Set

namespace Sagitta.Map.Borde.SatPorBloques

open Sagitta.Map Sagitta.Map.Tiempo Sagitta.Map.Tiempo.Finitud
open Sagitta.Map.Tiempo.Infinito Sagitta.Map.Tiempo.Relleno Sagitta.Map.Borde.Tricotomia
open Sagitta.Map.Borde.SatEnElBorde

open Classical in
/-- **SAT por bloques**: `satMarco` en los largos de `B`, «no» fuera. -/
noncomputable def porBloques (B : Set ℕ) : Problema := fun x => if x.length ∈ B then satMarco x else false

theorem rebanada_dentro {B : Set ℕ} {n : ℕ} (h : n ∈ B) : rebanada (porBloques B) n = rebanada satMarco n := by
  funext x; simp [rebanada, porBloques, h]

theorem rebanada_fuera {B : Set ℕ} {n : ℕ} (h : n ∉ B) : rebanada (porBloques B) n = fun _ => false := by
  funext x; simp [rebanada, porBloques, h]

/-- En los largos de `B`, el costo es exactamente el de SAT. -/
theorem sucNat_dentro {B : Set ℕ} {n : ℕ} (h : n ∈ B) : sucNat (porBloques B) n = sucNat satMarco n := by
  simp only [sucNat, sucesion, rebanada_dentro h]

/-- Fuera de `B`, una compuerta. -/
theorem sucNat_fuera {B : Set ℕ} {n : ℕ} (h : n ∉ B) : sucNat (porBloques B) n ≤ 1 := by
  have : sucesion (porBloques B) n ≤ 1 := by
    rw [sucesion, rebanada_fuera h, tamMin]
    exact iInf_le_of_le 1 (iInf_le_of_le (Shannon.falso n) (iInf_le_of_le (calcula_falso n) (by norm_num)))
  rw [sucesion_eq] at this; exact_mod_cast this

/-! ## (i) El lado fácil es gratis -/

/-- En todo largo infinito concentrado fuera de `B`, el circuito óptimo tiene a lo sumo una compuerta. -/
theorem constante_en_complemento (B : Set ℕ) (U : Ultrafilter ℕ) (hU : ∀ᶠ n in (U : Filter ℕ), n ∉ B) :
    ∀ᶠ n in (U : Filter ℕ), sucNat (porBloques B) n ≤ 1 :=
  hU.mono fun _ hn => sucNat_fuera hn

/-- **Con infinitos largos fuera de `B`, el costo nunca está arriba.** -/
theorem no_sobre_de_complemento {B : Set ℕ} (hB : Bᶜ.Infinite) : ¬ Sobre (sucNat (porBloques B)) := by
  rw [no_sobre_iff_buenos]
  refine ⟨1, 0, hB.mono fun n hn => ?_⟩
  simp only [pow_zero, mul_one, mem_ofPred_eq]
  exact sucNat_fuera hn

/-- Así que SAT por bloques está en P/poly u oscila. -/
theorem psobrePoly_u_oscila {B : Set ℕ} (hB : Bᶜ.Infinite) :
    porBloques B ∈ PsobrePoly ∨ Oscila (sucNat (porBloques B)) := by
  by_cases h : porBloques B ∈ PsobrePoly
  · exact Or.inl h
  · exact Or.inr ⟨fun hb => h ((bajo_sucNat_iff _).1 hb), no_sobre_de_complemento hB⟩

/-! ## (ii) Oscilar es SAT difícil en `B` -/

/-- **Fuera de P/poly si y solo si SAT es difícil en un largo infinito dentro de `B`.** -/
theorem fuera_iff_sat_dificil_en (B : Set ℕ) :
    porBloques B ∉ PsobrePoly ↔ ∃ U : Ultrafilter ℕ, LargoInfinito U ∧ (∀ᶠ n in (U : Filter ℕ), n ∈ B) ∧
      ∀ c k, ∀ᶠ n in (U : Filter ℕ), c * (n + 1) ^ k < sucNat satMarco n := by
  rw [fuera_iff_largo_infinito]
  constructor
  · rintro ⟨U, hU, h⟩
    have hB : ∀ᶠ n in (U : Filter ℕ), n ∈ B := (h 2 0).mono fun n hn => by
      by_contra hnB
      have := sucNat_fuera hnB
      simp at hn
      omega
    refine ⟨U, hU, hB, fun c k => ((h c k).and hB).mono fun n hn => ?_⟩
    rw [← sucNat_dentro hn.2]
    exact hn.1
  · rintro ⟨U, hU, hB, h⟩
    refine ⟨U, hU, fun c k => ((h c k).and hB).mono fun n hn => ?_⟩
    rw [sucNat_dentro hn.2]
    exact hn.1

/-! ## (iii) La versión no constructiva de Ladner -/

/-- Los largos donde el costo de SAT pasa de `m·(n+1)^m` son infinitos, para cada `m`, si SAT está fuera de P/poly. -/
theorem dificiles_infinitos (h : CookS12.satBits ∉ PsobrePoly) (m : ℕ) :
    {n | m * (n + 1) ^ m < sucNat satMarco n}.Infinite := by
  intro hfin
  have hm : satMarco ∉ PsobrePoly := fun hm => h (satBits_de_satMarco hm)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  apply hm
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff]
  exact pol_de_casi (c := m) (k := m) (N := N + 1) fun n hn => by
    by_contra hc
    have := hN (show n ∈ {n | m * (n + 1) ^ m < sucNat satMarco n} from Nat.lt_of_not_le hc)
    omega

/-- **La versión no constructiva de Ladner.** Si SAT no tiene circuitos polinomiales, hay un conjunto de largos `B`, con
infinitos largos afuera, tal que SAT por bloques tampoco los tiene; así que oscila. -/
theorem ladner_no_constructivo (h : CookS12.satBits ∉ PsobrePoly) :
    ∃ B : Set ℕ, Bᶜ.Infinite ∧ porBloques B ∉ PsobrePoly ∧ Oscila (sucNat (porBloques B)) := by
  choose f hf using fun m a => (dificiles_infinitos h m).exists_gt a
  -- `g 0` difícil para `0`; `g (m+1)` difícil para `m+1` y mayor que `g m + 1`.
  let g : ℕ → ℕ := fun m => Nat.rec (f 0 0) (fun m gm => f (m + 1) (gm + 1)) m
  have hg0 : g 0 = f 0 0 := rfl
  have hgs : ∀ m, g (m + 1) = f (m + 1) (g m + 1) := fun _ => rfl
  have hdif : ∀ m, m * (g m + 1) ^ m < sucNat satMarco (g m) := by
    intro m; cases m with
    | zero => rw [hg0]; exact (hf 0 0).1
    | succ m => rw [hgs]; exact (hf (m + 1) _).1
  have hsalto : ∀ m, g m + 1 < g (m + 1) := fun m => by rw [hgs]; exact (hf (m + 1) _).2
  have hmono : StrictMono g := strictMono_nat_of_lt_succ fun m => by have := hsalto m; omega
  let B : Set ℕ := range g
  have hfuera : ∀ m, g m + 1 ∉ B := by
    rintro m ⟨j, hj⟩
    rcases Nat.lt_or_ge m j with hmj | hmj
    · have := hmono.monotone (show m + 1 ≤ j by omega)
      have := hsalto m
      omega
    · have := hmono.monotone hmj
      omega
  have hBc : Bᶜ.Infinite :=
    infinite_of_injective_forall_mem (f := fun m => g m + 1) (fun a b hab => hmono.injective (by simpa using hab))
      hfuera
  have hnot : porBloques B ∉ PsobrePoly := by
    intro hp
    rw [psobrePoly_iff_grado, gradoPol_lt_top_iff] at hp
    obtain ⟨c, k, hck⟩ := hp
    set m := max c k
    have h1 := hck (g m)
    rw [sucNat_dentro (mem_range_self m)] at h1
    have h2 := hdif m
    have h3 : c * (g m + 1) ^ k ≤ m * (g m + 1) ^ m :=
      Nat.mul_le_mul (le_max_left c k) (Nat.pow_le_pow_right (by omega) (le_max_right c k))
    omega
  exact ⟨B, hBc, hnot, ⟨fun hb => hnot ((bajo_sucNat_iff _).1 hb), no_sobre_de_complemento hBc⟩⟩

/-! ## No es más difícil que SAT -/

/-- En los largos de `B`, la rebanada se obtiene de la de SAT fijando entradas (con la identidad). -/
theorem dentro_fija_sat {B : Set ℕ} {n : ℕ} (h : n ∈ B) :
    SeObtieneFijando (rebanada (porBloques B) n) (rebanada satMarco n) :=
  ⟨fun i => .inl i, fun x => by rw [rebanada_dentro h]; rfl⟩

theorem sucNat_porBloques_le (B : Set ℕ) (n : ℕ) : sucNat (porBloques B) n ≤ sucNat satMarco n + 1 := by
  by_cases h : n ∈ B
  · rw [sucNat_dentro h]; omega
  · have := sucNat_fuera h; omega

/-- **Si SAT enmarcado tiene circuitos polinomiales, SAT por bloques también.** -/
theorem porBloques_de_sat (B : Set ℕ) (h : satMarco ∈ PsobrePoly) : porBloques B ∈ PsobrePoly := by
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff] at h ⊢
  obtain ⟨c, k, hck⟩ := h
  refine ⟨c + 1, k, fun n => ?_⟩
  have h1 := sucNat_porBloques_le B n
  have h2 := hck n
  have h3 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-! ## Controles -/

/-- Con `B` vacío, SAT por bloques es la constante «no»: está en P/poly (la rama fácil de (i) es real). -/
example : porBloques ∅ ∈ PsobrePoly := by
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff]
  exact ⟨1, 0, fun n => by simpa using sucNat_fuera (B := ∅) (n := n) (notMem_empty n)⟩

/-- Con `B` todo, SAT por bloques es SAT enmarcado: el costo coincide en cada largo. La hipótesis `Bᶜ` infinito de
(i) no se puede quitar: con `B = univ` el lado fácil desaparece. -/
example (n : ℕ) : sucNat (porBloques univ) n = sucNat satMarco n := sucNat_dentro (mem_univ n)

/-- El complemento de `univ` no es infinito; (i) no se aplica. -/
example : ¬ (univ : Set ℕ)ᶜ.Infinite := by simp

/- Mutante probado (25 nov 2026, en /tmp/claude-noche/MutBlo.lean): en `ladner_no_constructivo`, cambiar
`g (m+1) = f (m+1) (g m + 1)` por `g (m+1) = f (m+1) (g m)` rompe `hsalto` (y con él `hfuera`): sin el `+ 1`, los
largos de `B` pueden quedar pegados y `Bᶜ` dejaría de ser infinito por construcción. -/

end Sagitta.Map.Borde.SatPorBloques
