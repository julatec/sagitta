import Sagitta.Map.EsqueletoCapaDos
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.Order.SuccPred

/-!
# La cebolla fina: un solo índice ordinal hasta `ω² + ω` (C4)

`Jerarquia.lean` indexó la cebolla por `ℕ∞` (las capas `F k` y la unión `ω`); `EsqueletoCapaDos.lean` (C3) abrió la capa
2 en un esqueleto de tipo `ω²`. Aquí se pegan las dos cosas en **una sola función de los ordinales**,

  `cebolla : Ordinal.{0} → Set (ℕ → ℕ)`,

que hasta `ω² + ω` recorre:

| ordinal | clase |
|---|---|
| `0` | `Capa 0` (`n + O(1)`) |
| `ω · h + d + 1` | `Esq h d = O(torre h ((n+1)^(d+1)))`; en `1`, `O(n)` |
| `ω · (h + 1)` | `EsqLim h`: `Pol` en `ω` (h = 0), `Exp` en `ω · 2` (h = 1) |
| `ω²` | `Capa 2` |
| `ω² + k + 1` | `Capa (k + 3)` |
| `ω² + ω` | la unión de todas las capas; `Fω` queda fuera |

**La construcción.** Los escalones (`Escalon`) viven solo en `0` y en los sucesores (`Escalon.ord`), y `cebolla α` es la unión
de los escalones con índice `≤ α`. En un ordinal límite no hay escalón propio, así que la cebolla es la unión de lo de
abajo **por construcción**.

## Lo que se prueba

1. **Crece estrictamente** hasta `ω² + ω` (`cebolla_strictMono`). Cada escalón tiene un testigo que no está en ningún
   escalón anterior (`testigo_no`).
2. **Los valores en los límites son las clases conocidas** (`cebolla_omega_mul`, `cebolla_pol`, `cebolla_exp`,
   `cebolla_omega_sq`, `cebolla_tope`).
3. **Los valores en los sucesores** (`cebolla_cero`, `cebolla_esq`, `cebolla_capa`): en `0`, `Capa 0`; en
   `ω · h + d + 1`, `Esq h d`; en `ω² + k + 1`, `Capa (k + 3)`.
4. **La topología**: con la topología del orden en los ordinales, `α ≤ ω² + ω` es un punto **aislado** si y solo si la
   cebolla **salta** en `α`, es decir, si `cebolla α` es más que la unión de lo de abajo (`aislado_iff_salta`). En los
   puntos de acumulación del tramo (`ω · (h + 1)`, `ω²`, `ω² + ω`) la cebolla es continua; en los aislados, salta.

   No es un hecho independiente: la continuidad en los límites vale **por construcción** (ahí no hay escalones), y el
   salto en los sucesores es `cebolla_strictMono`. Lo que el teorema dice es que la elección de índices es la correcta:
   cada clase nueva cae en un punto aislado y cada clase límite, en un punto de acumulación.

Es la misma imagen que en `Jerarquia.lean`, pero con un esqueleto ordinal más fino dentro de la capa 2. El relleno denso
(C1, C2) no cabe en ningún índice bien ordenado: vive entre escalones (`pl_entre`).
-/

open Ordinal Order Set

namespace Sagitta.Map
namespace Tiempo

/-! ## Los escalones -/

/-- **Los escalones de la cebolla fina**: la base, los del esqueleto de la capa 2 y las capas de arriba. -/
inductive Escalon
  | base
  | esq (h d : ℕ)
  | capa (k : ℕ)

namespace Escalon

/-- **El índice ordinal** de cada escalón: siempre `0` o un sucesor. -/
noncomputable def ord : Escalon → Ordinal.{0}
  | base => 0
  | esq h d => succ (indice (toLex (h, d)))
  | capa k => succ (ω * ω + (k : Ordinal.{0}))

/-- **La clase** de cada escalón. -/
def clase : Escalon → Set (ℕ → ℕ)
  | base => Capa 0
  | esq h d => Esq h d
  | capa k => Capa (k + 3)

/-- **El testigo** de cada escalón: está en él y en ningún escalón anterior. -/
def testigo : Escalon → ℕ → ℕ
  | base => fun n => n
  | esq h d => fun n => 2 * tope h d n
  | capa k => F (k + 3)

end Escalon

open Escalon

/-! ## Hechos de las clases -/

theorem capa_cero_sub_esq : Capa 0 ⊆ Esq 0 0 := by
  rintro f ⟨m, hm⟩
  refine ⟨2 * m + 1, 0, fun n _ => ?_⟩
  have : (F 0)^[m] (n + m) = n + m + m := by simp [F, Nat.succ_iterate]
  have h := hm n
  rw [this] at h
  simp only [tope_cero, zero_add, pow_one]
  nlinarith

theorem esq_sub_capa_dos (h d : ℕ) : Esq h d ⊆ Capa 2 := fun _ hf =>
  capa_dos_eq ▸ mem_iUnion.mpr ⟨h, mem_iUnion.mpr ⟨d, hf⟩⟩

theorem testigo_mem : ∀ s : Escalon, testigo s ∈ clase s
  | base => capa_id 0
  | esq _ _ => ⟨2, 0, fun _ _ => le_rfl⟩
  | capa k => F_mem_capa (k + 3)

/-- Si el doble de algo está en `O g`, la mitad también. -/
theorem doble_no {g : ℕ → ℕ} {f : ℕ → ℕ} (hf : f ∉ O g) : (fun n => 2 * f n) ∉ O g := by
  rintro ⟨C, N, hN⟩
  exact hf ⟨C, N, fun n hn => by have := hN n hn; simp only at this; omega⟩

theorem testigo_esq_no_esq {h d h' d' : ℕ} (hlt : toLex (h', d') < toLex (h, d)) :
    testigo (esq h d) ∉ Esq h' d' := doble_no (tope_no_esq hlt)

theorem testigo_esq_no_base (h d : ℕ) : testigo (esq h d) ∉ Capa 0 := by
  intro hc
  -- `2n ≤ 2 · tope h d n`, y `2n` (`F 1`) no está en la capa 0
  refine F_succ_no_capa 0 (capa_abajo hc fun n => ?_)
  rw [F_uno]
  simp only [testigo, doblar]
  exact Nat.mul_le_mul_left 2 ((Nat.le_succ n).trans ((Nat.le_self_pow (Nat.succ_ne_zero d) _).trans (le_torre h _)))

theorem testigo_capa_no {k : ℕ} {s : Escalon} (hs : s.clase ⊆ Capa (k + 2)) : testigo (capa k) ∉ s.clase :=
  fun h => F_succ_no_capa (k + 2) (hs h)

/-! ## El orden de los índices -/

theorem indice_lt_omega_sq (h d : ℕ) : indice (toLex (h, d)) < ω * ω :=
  (indice_lt_fila h d).trans_le (by gcongr; exact (natCast_lt_omega0 _).le)

theorem ord_esq_le (h d : ℕ) : (esq h d).ord ≤ ω * ω := succ_le_of_lt (indice_lt_omega_sq h d)

theorem lt_ord_capa (k : ℕ) : ω * ω < (capa k).ord := lt_succ_of_le le_self_add

theorem ord_esq_lt_iff {h d h' d' : ℕ} : (esq h' d').ord < (esq h d).ord ↔ toLex (h', d') < toLex (h, d) := by
  simp only [ord, succ_lt_succ_iff]; exact indice_strictMono.lt_iff_lt

theorem ord_capa_lt_iff {k k' : ℕ} : (capa k').ord < (capa k).ord ↔ k' < k := by
  simp only [ord, succ_lt_succ_iff, add_lt_add_iff_left, Nat.cast_lt]

/-- **El testigo de un escalón no está en ningún escalón de índice menor.** -/
theorem testigo_no : ∀ {s t : Escalon}, t.ord < s.ord → testigo s ∉ t.clase
  | base, t, h => absurd h (not_lt_zero (a := _))
  | esq h d, base, _ => testigo_esq_no_base h d
  | esq h d, esq h' d', hlt => testigo_esq_no_esq (ord_esq_lt_iff.mp hlt)
  | esq h d, capa k, hlt => absurd ((lt_ord_capa k).trans hlt) (not_lt.mpr (ord_esq_le h d))
  | capa k, base, _ => testigo_capa_no (capa_mono' (by omega))
  | capa k, esq h d, _ => testigo_capa_no ((esq_sub_capa_dos h d).trans (capa_mono' (by omega)))
  | capa k, capa k', hlt => testigo_capa_no (capa_mono' (by have := ord_capa_lt_iff.mp hlt; omega))

/-! ## La cebolla -/

/-- **La cebolla fina**: la unión de los escalones con índice `≤ α`. -/
def cebolla (α : Ordinal.{0}) : Set (ℕ → ℕ) := ⋃ (s : Escalon) (_ : s.ord ≤ α), s.clase

theorem mem_cebolla {α : Ordinal.{0}} {f : ℕ → ℕ} : f ∈ cebolla α ↔ ∃ s : Escalon, s.ord ≤ α ∧ f ∈ s.clase := by
  simp [cebolla]

theorem cebolla_mono : Monotone cebolla := fun _ _ hab _ hf => by
  obtain ⟨s, hs, hf⟩ := mem_cebolla.mp hf
  exact mem_cebolla.mpr ⟨s, hs.trans hab, hf⟩

/-- El ordinal `ω² + ω`, el tope de la cebolla fina. -/
noncomputable def tope2 : Ordinal.{0} := ω * ω + ω

/-- **Todo sucesor hasta `ω² + ω` es el índice de un escalón.** -/
theorem existe_paso {α : Ordinal.{0}} (hα : α < tope2) : ∃ s : Escalon, s.ord = succ α := by
  rcases lt_or_ge α (ω * ω) with h | h
  · obtain ⟨⟨q, r⟩, hp⟩ := indice_sobre h
    exact ⟨esq q r, by simp only [ord]; rw [show toLex (q, r) = toLex (q, r) from rfl, ← hp]; rfl⟩
  · have e := Ordinal.add_sub_cancel_of_le h
    have hk : α - ω * ω < ω := by
      rw [← e] at hα
      exact lt_of_add_lt_add_left hα
    obtain ⟨k, hk⟩ := lt_omega0.mp hk
    refine ⟨capa k, ?_⟩
    simp only [ord]
    rw [← hk, e]

/-- **La cebolla crece estrictamente hasta `ω² + ω`.** -/
theorem cebolla_strictMono {α β : Ordinal.{0}} (hab : α < β) (hβ : β ≤ tope2) : cebolla α ⊂ cebolla β := by
  obtain ⟨s, hs⟩ := existe_paso (hab.trans_le hβ)
  refine (cebolla_mono hab.le).ssubset_of_not_superset fun hsub => ?_
  have hw : testigo s ∈ cebolla β := mem_cebolla.mpr ⟨s, hs ▸ succ_le_of_lt hab, testigo_mem s⟩
  obtain ⟨t, ht, hwt⟩ := mem_cebolla.mp (hsub hw)
  exact testigo_no (ht.trans_lt (hs ▸ lt_succ α)) hwt

/-! ## La topología: aislado si y solo si salta -/

/-- Lo que queda estrictamente debajo de `α`. -/
def debajo (α : Ordinal.{0}) : Set (ℕ → ℕ) := ⋃ (β : Ordinal.{0}) (_ : β < α), cebolla β

theorem debajo_sub (α : Ordinal.{0}) : debajo α ⊆ cebolla α := by
  intro f hf
  simp only [debajo, mem_iUnion] at hf
  obtain ⟨β, hβ, hf⟩ := hf
  exact cebolla_mono hβ.le hf

/-- Ningún escalón está en un límite. -/
theorem ord_ne_limite {α : Ordinal.{0}} (hα : IsSuccLimit α) (s : Escalon) : s.ord ≠ α := by
  cases s with
  | base => exact (hα.ne_bot).symm
  | esq h d => exact hα.succ_ne _
  | capa k => exact hα.succ_ne _

/-- **En un límite, la cebolla es la unión de lo de abajo** (es continua). -/
theorem cebolla_limite {α : Ordinal.{0}} (hα : IsSuccLimit α) : cebolla α = debajo α := by
  refine Subset.antisymm (fun f hf => ?_) (debajo_sub α)
  obtain ⟨s, hs, hf⟩ := mem_cebolla.mp hf
  have hlt : s.ord < α := lt_of_le_of_ne hs (ord_ne_limite hα s)
  simp only [debajo, mem_iUnion]
  exact ⟨s.ord, hlt, mem_cebolla.mpr ⟨s, le_rfl, hf⟩⟩

/-- **En un punto que no es límite, la cebolla salta** (hasta `ω² + ω`). -/
theorem cebolla_salta {α : Ordinal.{0}} (hα : ¬ IsSuccLimit α) (hle : α ≤ tope2) : debajo α ≠ cebolla α := by
  intro heq
  rcases eq_or_ne α 0 with rfl | h0
  · -- en `0` no hay nada debajo, y la base no es vacía
    have : testigo base ∈ cebolla 0 := mem_cebolla.mpr ⟨base, le_rfl, testigo_mem base⟩
    rw [← heq] at this
    simp only [debajo, mem_iUnion] at this
    obtain ⟨β, hβ, _⟩ := this
    exact (not_lt_zero (a := β)) hβ
  · -- `α = succ β`: lo de abajo es `cebolla β`, y `cebolla β ⊂ cebolla α`
    rw [not_isSuccLimit_iff] at hα
    obtain ⟨β, rfl⟩ : ∃ β, succ β = α := by
      rcases hα with hmin | hpre
      · exact absurd (hmin.eq_bot) h0
      · rw [not_isSuccPrelimit_iff] at hpre
        obtain ⟨β, hβ⟩ := hpre
        exact ⟨β, hβ.succ_eq⟩
    have hd : debajo (succ β) ⊆ cebolla β := by
      intro f hf
      simp only [debajo, mem_iUnion] at hf
      obtain ⟨γ, hγ, hf⟩ := hf
      exact cebolla_mono (lt_succ_iff.mp hγ) hf
    have := cebolla_strictMono (lt_succ β) hle
    rw [← heq] at this
    exact (this.trans_subset hd).ne rfl

/-- **Aislado si y solo si salta.** Con la topología del orden, un ordinal `α ≤ ω² + ω` es un punto aislado exactamente
cuando la cebolla en `α` es más que la unión de lo de abajo. -/
theorem aislado_iff_salta {α : Ordinal.{0}} (hle : α ≤ tope2) : IsOpen ({α} : Set Ordinal.{0}) ↔ debajo α ≠ cebolla α := by
  rw [SuccOrder.isOpen_singleton_iff]
  refine ⟨fun h => cebolla_salta h hle, fun h hl => h (cebolla_limite hl).symm⟩

/-! ## Los valores en los límites -/

theorem esq_le_lim {h h' d' : ℕ} (hh : h' ≤ h) : Esq h' d' ⊆ EsqLim h := fun f hf =>
  mem_iUnion.mpr ⟨d', esq_mono (Prod.Lex.toLex_le_toLex.mpr (by
    rcases hh.lt_or_eq with h1 | rfl
    · exact Or.inl h1
    · exact Or.inr ⟨rfl, le_rfl⟩)) hf⟩

theorem ord_esq_le_fila {h h' d' : ℕ} : (esq h' d').ord ≤ ω * ((h + 1 : ℕ) : Ordinal.{0}) ↔ h' ≤ h := by
  constructor
  · intro hle
    by_contra hlt
    push Not at hlt
    have : ω * ((h + 1 : ℕ) : Ordinal.{0}) ≤ indice (toLex (h', d')) := by
      simp only [indice, ofLex_toLex]
      exact (by gcongr; exact Nat.cast_le.mpr hlt : ω * ((h + 1 : ℕ) : Ordinal.{0}) ≤ ω * (h' : Ordinal.{0})).trans
        le_self_add
    exact absurd hle (not_le.mpr (this.trans_lt (lt_succ _)))
  · intro hh
    exact succ_le_of_lt ((indice_lt_fila h' d').trans_le (by gcongr))

/-- **En `ω · (h + 1)`, la cebolla es el límite de la fila `h`.** -/
theorem cebolla_omega_mul (h : ℕ) : cebolla (ω * ((h + 1 : ℕ) : Ordinal.{0})) = EsqLim h := by
  ext f
  rw [mem_cebolla]
  constructor
  · rintro ⟨s, hs, hf⟩
    cases s with
    | base => exact esq_le_lim (Nat.zero_le h) (capa_cero_sub_esq hf)
    | esq h' d' => exact esq_le_lim (ord_esq_le_fila.mp hs) hf
    | capa k =>
      have : ω * ((h + 1 : ℕ) : Ordinal.{0}) < ω * ω := mul_lt_mul_of_pos_left (natCast_lt_omega0 _) omega0_pos
      exact absurd hs (not_le.mpr (this.trans (lt_ord_capa k)))
  · intro hf
    obtain ⟨d, hf⟩ := mem_iUnion.mp hf
    exact ⟨esq h d, ord_esq_le_fila.mpr le_rfl, hf⟩

/-- **`Pol` está en `ω`.** -/
theorem cebolla_pol : cebolla ω = Pol := by
  have := cebolla_omega_mul 0
  simp only [zero_add, Nat.cast_one, mul_one] at this
  rw [this, esqLim_cero]

/-- **`Exp` está en `ω · 2`.** -/
theorem cebolla_exp : cebolla (ω * 2) = Exp := by
  have := cebolla_omega_mul 1
  simp only [Nat.reduceAdd, Nat.cast_ofNat] at this
  rw [this, esqLim_uno]

/-- **La capa 2 está en `ω²`.** -/
theorem cebolla_omega_sq : cebolla (ω * ω) = Capa 2 := by
  ext f
  rw [mem_cebolla, capa_dos_eq]
  simp only [EsqLim, mem_iUnion]
  constructor
  · rintro ⟨s, hs, hf⟩
    cases s with
    | base => exact ⟨0, 0, capa_cero_sub_esq hf⟩
    | esq h d => exact ⟨h, d, hf⟩
    | capa k => exact absurd hs (not_le.mpr (lt_ord_capa k))
  · rintro ⟨h, d, hf⟩
    exact ⟨esq h d, ord_esq_le h d, hf⟩

/-- **En `ω² + ω`, la unión de todas las capas**; y la diagonal `Fω` queda fuera. -/
theorem cebolla_tope : cebolla tope2 = ⋃ k, Capa k := by
  ext f
  rw [mem_cebolla, mem_iUnion]
  constructor
  · rintro ⟨s, _, hf⟩
    cases s with
    | base => exact ⟨0, hf⟩
    | esq h d => exact ⟨2, esq_sub_capa_dos h d hf⟩
    | capa k => exact ⟨k + 3, hf⟩
  · rintro ⟨k, hf⟩
    refine ⟨capa k, ?_, capa_mono' (by omega) hf⟩
    simp only [ord, tope2]
    exact succ_le_of_lt ((add_lt_add_iff_left _).2 (natCast_lt_omega0 k))

theorem Fω_no_cebolla : Fω ∉ cebolla tope2 := by
  rw [cebolla_tope]
  simp only [mem_iUnion, not_exists]
  exact Fω_no_capa

/-- Algunos puntos del tramo: `ω · (h+1)`, `ω²` y `ω² + ω` son límites; `1` y `ω² + 1` no. No se prueba que esos sean
todos los límites del tramo. -/
theorem limites_del_tramo (h : ℕ) :
    IsSuccLimit (ω * ((h + 1 : ℕ) : Ordinal.{0})) ∧ IsSuccLimit (ω * ω : Ordinal.{0}) ∧ IsSuccLimit tope2 ∧
      ¬ IsSuccLimit (1 : Ordinal.{0}) ∧ ¬ IsSuccLimit (ω * ω + 1 : Ordinal.{0}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isSuccLimit_mul_left isSuccLimit_omega0 (by exact_mod_cast Nat.succ_pos h)
  · exact isSuccLimit_mul_left isSuccLimit_omega0 omega0_pos
  · exact isSuccLimit_add (ω * ω) isSuccLimit_omega0
  · rw [show (1 : Ordinal.{0}) = succ 0 by simp]; exact not_isSuccLimit_succ 0
  · rw [← Order.succ_eq_add_one]; exact not_isSuccLimit_succ _

/-! ## Los valores en los sucesores -/

theorem capa_cero_sub_esq' (h d : ℕ) : Capa 0 ⊆ Esq h d :=
  capa_cero_sub_esq.trans (esq_mono (Prod.Lex.toLex_le_toLex.mpr (by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exact Or.inr ⟨rfl, Nat.zero_le d⟩
    · exact Or.inl hh)))

/-- **En `0`, la capa 0.** -/
theorem cebolla_cero : cebolla 0 = Capa 0 := by
  ext f
  rw [mem_cebolla]
  constructor
  · rintro ⟨s, hs, hf⟩
    cases s with
    | base => exact hf
    | esq h d => exact absurd hs (not_le.mpr (lt_of_lt_of_le (Order.bot_lt_succ _) le_rfl))
    | capa k => exact absurd hs (not_le.mpr (Order.bot_lt_succ _))
  · intro hf; exact ⟨base, le_rfl, hf⟩

/-- **En `ω · h + d + 1`, el escalón `Esq h d`.** -/
theorem cebolla_esq (h d : ℕ) : cebolla (esq h d).ord = Esq h d := by
  ext f
  rw [mem_cebolla]
  constructor
  · rintro ⟨s, hs, hf⟩
    cases s with
    | base => exact capa_cero_sub_esq' h d hf
    | esq h' d' =>
      rcases hs.lt_or_eq with hlt | heq
      · exact esq_mono (ord_esq_lt_iff.mp hlt).le hf
      · have : toLex (h', d') = toLex (h, d) :=
          indice_strictMono.injective (Order.succ_injective heq)
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (toLex.injective this)
        exact hf
    | capa k => exact absurd hs (not_le.mpr ((ord_esq_le h d).trans_lt (lt_ord_capa k)))
  · intro hf; exact ⟨esq h d, le_rfl, hf⟩

/-- **En `ω² + k + 1`, la capa `k + 3`.** -/
theorem cebolla_capa (k : ℕ) : cebolla (capa k).ord = Capa (k + 3) := by
  ext f
  rw [mem_cebolla]
  constructor
  · rintro ⟨s, hs, hf⟩
    cases s with
    | base => exact capa_mono' (by omega) hf
    | esq h d => exact capa_mono' (by omega) (esq_sub_capa_dos h d hf)
    | capa k' =>
      have : k' ≤ k := by
        rcases hs.lt_or_eq with hlt | heq
        · exact (ord_capa_lt_iff.mp hlt).le
        · have := Order.succ_injective heq
          simp only [add_right_inj, Nat.cast_inj] at this
          omega
      exact capa_mono' (by omega) hf
  · intro hf; exact ⟨capa k, le_rfl, hf⟩

/-! ## Controles

Positivos: la cebolla es continua en `ω`, salta en `1`, y `ω²` no es aislado. Los mutantes de la revisión del 23 nov 2026
(que `ω` sea aislado; que un escalón tenga índice menor que sí mismo; `aislado_iff_salta` o `cebolla_strictMono` pasado
`ω² + ω`) no se pueden probar con estos teoremas; quedan anotados aquí y no en el código, porque un mutante no compila. -/

example : debajo ω = cebolla ω := (cebolla_limite isSuccLimit_omega0).symm

example : debajo 1 ≠ cebolla 1 :=
  cebolla_salta (limites_del_tramo 0).2.2.2.1
    (((one_lt_omega0.trans_le (le_mul_left _ omega0_pos)).le).trans (le_self_add (b := ω)))

example : ¬ IsOpen ({ω * ω} : Set Ordinal.{0}) := by
  rw [SuccOrder.isOpen_singleton_iff, not_not]; exact (limites_del_tramo 0).2.1

/-- Control de los sucesores: `O(n)` está en `1`. -/
example : cebolla (esq 0 0).ord = O (fun n => (n + 1) ^ 1) := by rw [cebolla_esq]; rfl

end Tiempo
end Sagitta.Map
