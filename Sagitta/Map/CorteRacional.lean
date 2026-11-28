import Sagitta.Map.AceleracionBlum
import Sagitta.Map.Levin
import Sagitta.Map.BlumExiste

/-!
# Racionales e irracionales: el corte de costos de un problema

La analogía (José, 24 nov 2026). El conjunto de cotas de tiempo que **algún** algoritmo alcanza para un problema es un
corte del orden de Landau, como un corte de Dedekind en la recta.

* **Racional**: el corte tiene mínimo, hay un algoritmo óptimo.
* **Irracional**: no lo tiene. Para todo algoritmo hay otro estrictamente mejor: es la aceleración de Blum
  (`AceleracionBlum.lean`).
* Las aproximaciones son la escalera de algoritmos, y la **descripción** de cada uno hace de los decimales: crece sin cota.

## Lo que se prueba

1. **Una escalera estricta no repite** (`cadena_inyectiva`). Si cada costo es despreciable frente al anterior y todos
   son positivos, los peldaños son distintos.
2. **La descripción crece sin cota: es un palomar** (`no_acotado_de_inyectiva`). Hay finitos objetos de cada tamaño.
   * Programas (`descripcion_no_acotada`): el código de los programas de una escalera estricta no está acotado. Con la
     aceleración de Blum (`blum_descripcion`): hay una escalera de programas de `f` cuyo código crece sin cota. Y sin
     hipótesis (`existe_irracional`, con `BlumExiste.blum`): hay una `f` computable así.
   * Pruebas o certificados (`certificados_no_acotados`): en cualquier sistema con finitas pruebas de cada tamaño, si
     cada peldaño necesita una prueba que lo nombre, el largo de las pruebas tampoco está acotado.
3. **Levin está debajo de toda la escalera** (`levin_bajo_escalera`). Si los programas `i_k` resuelven la búsqueda
   (con verificador `V`) con presupuestos `t_k`, la búsqueda universal (`costoLevin`) cuesta a lo sumo `8 · 2^(i_k) · t_k`
   para **todo** `k` a la vez: está en `O(t_k)` para todo `k` (`levin_en_O`). El corte de una búsqueda con verificación
   **tiene mínimo**. Es racional.
4. **La descripción se paga en la constante** (`constantes_no_acotadas`). Si la escalera es estricta y el presupuesto
   de cada peldaño es el de su programa, los índices `i_k` no están acotados, y las constantes `8 · 2^(i_k)` tampoco. Los
   decimales infinitos no desaparecen: se vuelven el factor que Levin paga para cada peldaño.

## Lo que no

* La medida de Levin es la de `Levin.lean`: presupuesto de `evaln`, no pasos de una máquina. De aquí no sale nada
  sobre `P` ni `NP`; sale la **forma** del argumento.
* Que el corte de la búsqueda tenga mínimo no dice **dónde** está. `P ≠ NP` diría que, para SAT, ese mínimo queda
  fuera de `Pol`, y con él todo el corte (`SinPrimerSuperpolinomial.lean`).
* La aceleración de Blum vive en problemas **sin** verificación barata, construidos por diagonalización. No se sabe
  que ningún problema natural la tenga.
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map
namespace Tiempo
namespace CorteRacional

open AceleracionBlum

/-! ## 1. Una escalera estricta no repite -/

/-- `o` es transitiva: lo despreciable frente a lo despreciable es despreciable. -/
theorem o_trans {f g h : ℕ → ℕ} (hfg : f ∈ o g) (hgh : g ∈ o h) : f ∈ o h := fun c => by
  obtain ⟨N₁, h₁⟩ := hfg c
  obtain ⟨N₂, h₂⟩ := hgh 1
  exact ⟨max N₁ N₂, fun n hn => by
    have := h₁ n (le_of_max_le_left hn); have := h₂ n (le_of_max_le_right hn); omega⟩

/-- Más abajo en la escalera es despreciable frente a todo lo de arriba. -/
theorem cadena_o {t : ℕ → ℕ → ℕ} (ht : ∀ k, t (k + 1) ∈ o (t k)) {i j : ℕ} (hij : i < j) : t j ∈ o (t i) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact o_trans (ht j) (ih h)
    · exact ht i

/-- **Una escalera estricta de costos positivos no repite peldaño.** -/
theorem cadena_inyectiva {t : ℕ → ℕ → ℕ} (ht : ∀ k, t (k + 1) ∈ o (t k)) (hpos : ∀ k n, 0 < t k n) :
    Function.Injective t := by
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h' := cadena_o ht h
    rw [← hij] at h'
    obtain ⟨N, hN⟩ := h' 2
    have := hN N le_rfl; have := hpos i N; omega
  · have h' := cadena_o ht h
    rw [hij] at h'
    obtain ⟨N, hN⟩ := h' 2
    have := hN N le_rfl; have := hpos j N; omega

/-! ## 2. El palomar de la descripción -/

/-- **El palomar**: una sucesión sin repetidos, en un tipo con finitos objetos de cada tamaño, tiene tamaños sin cota. -/
theorem no_acotado_de_inyectiva {α : Type*} {g : ℕ → α} (hg : Function.Injective g) (tam : α → ℕ)
    (hfin : ∀ m, {a | tam a ≤ m}.Finite) : ∀ m, ∃ k, m < tam (g k) := by
  intro m
  by_contra hno
  push Not at hno
  exact Set.infinite_of_injective_forall_mem hg (s := {a | tam a ≤ m}) hno (hfin m)

theorem codigos_finitos (m : ℕ) : {c : Code | Encodable.encode c ≤ m}.Finite :=
  (Set.finite_Iic m).preimage Encodable.encode_injective.injOn

/-- **La descripción de una escalera estricta de programas crece sin cota.** -/
theorem descripcion_no_acotada {f : ℕ → ℕ} {s : ℕ → Code} (hs : ∀ k, Computa (s k) f)
    (ho : ∀ k, costo (s (k + 1)) ∈ o (costo (s k))) : ∀ m, ∃ k, m < Encodable.encode (s k) := by
  have hinj : Function.Injective fun k => costo (s k) :=
    cadena_inyectiva ho fun k n => lt_of_le_of_lt (Nat.zero_le n) (costo_gt (hs k) n)
  exact no_acotado_de_inyectiva (fun i j h => hinj (by simp only [h])) _ codigos_finitos

/-- **Con la aceleración de Blum**: hay una escalera de programas de `f`, cada uno despreciable frente al anterior, y su
código crece sin cota. Los «decimales» de un irracional. -/
theorem blum_descripcion {r : ℕ → ℕ → ℕ} {f : ℕ → ℕ} (hr : ∀ n x, (n + 1) * x ≤ r n x)
    (h : TieneAceleracion r f) :
    ∃ s : ℕ → Code, (∀ k, Computa (s k) f) ∧ (∀ k, costo (s (k + 1)) ∈ o (costo (s k))) ∧
      ∀ m, ∃ k, m < Encodable.encode (s k) := by
  obtain ⟨s, hs, ho⟩ := escalera_de_aceleracion hr h
  exact ⟨s, hs, ho, descripcion_no_acotada hs ho⟩

/-- **Sin hipótesis**: hay una función computable (con valores 0 y 1) cuyos programas forman una escalera estricta con
código sin cota. Es `BlumExiste.blum` más el palomar: un irracional de verdad, con sus decimales. -/
theorem existe_irracional : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧
    ∃ s : ℕ → Code, (∀ k, Computa (s k) f) ∧ (∀ k, costo (s (k + 1)) ∈ o (costo (s k))) ∧
      ∀ m, ∃ k, m < Encodable.encode (s k) := by
  obtain ⟨f, h1, h2, h3⟩ := BlumExiste.blum BlumExiste.computable_lineal
  exact ⟨f, h1, h2, blum_descripcion (fun _ _ => le_rfl) h3⟩

/-- **Las pruebas también crecen.** En un sistema con finitas pruebas de cada tamaño, si cada peldaño `k` tiene una
prueba `π k` que lo nombra (`concl (π k) = s k`), el tamaño de las pruebas no está acotado. -/
theorem certificados_no_acotados {P : Type*} (tam : P → ℕ) (hfin : ∀ m, {p | tam p ≤ m}.Finite) (concl : P → Code)
    {f : ℕ → ℕ} {s : ℕ → Code} (hs : ∀ k, Computa (s k) f) (ho : ∀ k, costo (s (k + 1)) ∈ o (costo (s k)))
    (π : ℕ → P) (hπ : ∀ k, concl (π k) = s k) : ∀ m, ∃ k, m < tam (π k) := by
  have hinj : Function.Injective fun k => costo (s k) :=
    cadena_inyectiva ho fun k n => lt_of_le_of_lt (Nat.zero_le n) (costo_gt (hs k) n)
  refine no_acotado_de_inyectiva (fun i j h => hinj ?_) tam hfin
  have : s i = s j := by rw [← hπ i, ← hπ j, h]
  simp only [this]

/-! ## 3. Levin debajo de toda la escalera -/

open Levin

theorem costoHasta_mono {T T' : ℕ} (h : T ≤ T') : costoHasta T ≤ costoHasta T' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

/-- El costo de la búsqueda universal sobre `x`: lo repartido hasta la primera ronda que entrega una respuesta. Si
nunca entrega, `0` (no se usa). -/
noncomputable def costoLevin (V : ℕ → ℕ → Bool) (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ T, (buscar V x T).isSome then costoHasta (Nat.find h) else 0

/-- **Levin, para un programa**: si el programa `i` resuelve `x` con presupuesto `k ≥ 1`, la búsqueda cuesta menos que
`8 · 2ⁱ · k`. -/
theorem costoLevin_le {V : ℕ → ℕ → Bool} {x i k y : ℕ} (hk : 1 ≤ k) (h : correr i k x = some y) (hV : V x y = true) :
    costoLevin V x < 8 * 2 ^ i * k := by
  classical
  obtain ⟨T, y', hT, -, hc⟩ := levin hk h hV
  have hex : ∃ T, (buscar V x T).isSome := ⟨T, by simp [hT]⟩
  rw [costoLevin, dite_eq_left_of_eq_true (eq_true hex)]
  exact lt_of_le_of_lt (costoHasta_mono (Nat.find_min' hex (by simp [hT]))) hc

/-- **Debajo de toda la escalera.** Si los programas `i k` resuelven toda entrada con presupuestos `t k ≥ 1`, la
búsqueda universal cuesta menos que `8 · 2^(i k) · t k` para **todo** `k`. -/
theorem levin_bajo_escalera {V : ℕ → ℕ → Bool} {i : ℕ → ℕ} {t : ℕ → ℕ → ℕ} (ht1 : ∀ k x, 1 ≤ t k x)
    (hres : ∀ k x, ∃ y, correr (i k) (t k x) x = some y ∧ V x y = true) (k x : ℕ) :
    costoLevin V x < 8 * 2 ^ i k * t k x := by
  obtain ⟨y, hy, hV⟩ := hres k x
  exact costoLevin_le (ht1 k x) hy hV

/-- **El corte tiene mínimo**: la búsqueda universal está en `O(t k)` para todo `k` a la vez. -/
theorem levin_en_O {V : ℕ → ℕ → Bool} {i : ℕ → ℕ} {t : ℕ → ℕ → ℕ} (ht1 : ∀ k x, 1 ≤ t k x)
    (hres : ∀ k x, ∃ y, correr (i k) (t k x) x = some y ∧ V x y = true) (k : ℕ) :
    EsO (costoLevin V) (t k) :=
  ⟨8 * 2 ^ i k, 0, fun x _ => (levin_bajo_escalera ht1 hres k x).le⟩

/-- **La descripción se paga en la constante.** Si la escalera es estricta y el presupuesto de cada peldaño es una
función de su programa (`t k = presupuesto (i k)`), los índices no repiten, así que las constantes `8 · 2^(i k)` de
Levin no están acotadas. -/
theorem constantes_no_acotadas {i : ℕ → ℕ} {t : ℕ → ℕ → ℕ} (presupuesto : ℕ → ℕ → ℕ)
    (hpres : ∀ k, t k = presupuesto (i k)) (ho : ∀ k, t (k + 1) ∈ o (t k)) (ht1 : ∀ k x, 1 ≤ t k x) :
    ∀ M, ∃ k, M < 8 * 2 ^ i k := by
  have hinj : Function.Injective t := cadena_inyectiva ho fun k n => ht1 k n
  have hi : Function.Injective i := fun a b h => hinj (by rw [hpres a, hpres b, h])
  intro M
  obtain ⟨k, hk⟩ := no_acotado_de_inyectiva hi id (fun m => Set.finite_Iic m) M
  refine ⟨k, lt_of_lt_of_le hk ?_⟩
  have : i k < 2 ^ i k := Nat.lt_two_pow_self
  simp only [id]; omega

/-! ## Controles -/

/-- Una escalera con un peldaño repetido no es estricta: `t k = 1` constante no cumple `t (k+1) ∈ o (t k)`. -/
example : ¬ ∀ k, (fun _ _ => 1 : ℕ → ℕ → ℕ) (k + 1) ∈ o ((fun _ _ => 1 : ℕ → ℕ → ℕ) k) := fun h => by
  obtain ⟨N, hN⟩ := h 0 2
  have := hN N le_rfl; simp at this

/-- Sin el palomar no hay cota que valga: los tamaños de `id` sobre ℕ crecen sin cota. -/
example : ∀ m, ∃ k, m < (id : ℕ → ℕ) k :=
  no_acotado_de_inyectiva Function.injective_id id (fun m => Set.finite_Iic m)

end CorteRacional
end Tiempo
end Sagitta.Map
