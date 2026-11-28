import CslibFrontier.Logics.Propositional.CuttingPlanes.Interpolation
import CslibFrontier.Logics.Propositional.CuttingPlanes.Resolution
import CslibFrontier.Logics.Propositional.Resolution.CliqueColoring
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Planos de corte con coeficientes acotados sobre clique–coloreo

Peldaño «planos de corte» de la escalera. `DetectorResolucion.lean` usó la cota de Haken para
resolución sobre el palomar. Para planos de corte el palomar no sirve: planos de corte lo refutan en
`(n + 1)(n + 2)²` líneas (`CuttingPlanes.refutableInSize_pigeonhole_succ`, `Separation.lean` de
cslib-frontier; ese teorema cuenta líneas, no acota los coeficientes). Aquí se usa
la fórmula de clique–coloreo `Clique_{n,k}(p, q) ∧ Color_{n,r}(p, z)`: el grafo de aristas `p` tiene
un `k`-clique y es `r`-coloreable.

## Lo que se prueba

* **La partición** (`toIneqs_cliqueColoring`): las desigualdades de la fórmula son las del clique,
  sobre `p` y `q`, más las del coloreo, sobre `p` y `z`. Compartidas: las aristas. De `A`: el
  clique. De `B`: el coloreo.
* **Monotonía** (`coeff_arista_nonneg`, `coeff_arista_le_one`): en el clique, cada arista tiene
  coeficiente `0` o `1`. Lo que pide la interpolación monótona es solo que no sea negativo.
* **Interpolación** (`existe_separador`): una refutación por planos de corte de `k'` líneas con
  coeficientes a lo sumo `M` da un circuito monótono que separa los grafos con `k`-clique de los
  `r`-coloreables, con a lo sumo `(k' · 2^(2t) + 1) · 2^(2t+1)` compuertas, donde
  `t ≥ ⌈log₂(2 M k n + 1)⌉ + 1` y `t ≥ ⌈log₂ E⌉ (⌈log₂(2 M E + 1)⌉ + 1)`, con `E = n(n−1)/2`. Es
  el Teorema 6.4 de Krajíček (1997) en la forma de cslib-frontier
  (`IsProof.exists_monotone_circuit_of_abs_coeff_le`): `2^t` es `(M N)^O(1) · (M n)^O(log n)`.
  La variante `existe_separador'` (sobre `IsProof.exists_monotone_circuit`) solo acota los
  coeficientes de las variables `q` en la refutación; los de `p` y `z` pueden ser grandes, y la
  segunda condición sobre `t` queda `t ≥ ⌈log₂ E⌉ (⌈log₂(2E + 1)⌉ + 1)`.
* **Las cotas** (`cota_alon_boppana`, `cota_raiz`, `cota_bits`): con las cotas monótonas de
  cslib-frontier (Alon–Boppana), `2^l < (s · 2^(2t) + 1) · 2^(2t+1)` para refutaciones de `s`
  líneas. Con `2(M + 1) n² + 1 ≤ 2^b`, `n ≥ 2^40` y `k = ⌊√n⌋ + 1`:
  `2^⌊⌊√⌊√n⌋⌋/2⌋ < (s + 1) · 2^(4(b+1)² + 1)`. Con `M` polinomial en `n`, `b = O(log n)`, y
  `s ≥ 2^(Ω(n^{1/4}) − O(log² n))`. Es la cota de Krajíček, Corolario 7.3(2): planos de corte con
  coeficientes polinomiales.
* **Superpolinomial** (`sin_refutacion_polinomial`): no hay `p` y `q` polinomiales tales que, para
  infinitos `j`, la fórmula con `n = 2^(4j)` y `k = 2^(2j) + 1` tenga una refutación de a lo sumo
  `p n` líneas con coeficientes a lo sumo `q n`.
* **Controles**: la fórmula es insatisfacible; las aristas aparecen con coeficiente `1`; toda
  instancia con `r < k` tiene alguna refutación con alguna cota de coeficientes
  (`refutaAcotada_of_not_sat`, por la completitud de planos de corte de cslib-frontier); las cinco
  hipótesis de `cota_bits` se cumplen a la vez en `n = 2^40`; el enunciado que niega
  `sin_refutacion_polinomial` se cumple si no se piden polinomios, así que la negación no es
  trivial; una refutación concreta (`refuta_cero`, `n = 0`) cumple las hipótesis de
  `existe_separador` y de `existe_separador'`.

## Lo que no se prueba

* **No es la cota de Pudlák** (1997) para coeficientes arbitrarios. Pudlák interpola con circuitos
  monótonos *reales*. Aquí los coeficientes entran en `t`: con coeficientes de `b ≥ n^{1/8}` bits,
  `4(b+1)²` ya alcanza a `n^{1/4}` y la cota no dice nada.
* La completitud sí está (`CuttingPlanes.exists_refutableInSize_iff_not_satisfiable`, en
  cslib-frontier): hay refutaciones. Lo que no está es una cota polinomial de sus coeficientes ni de
  su tamaño. Por eso `sin_refutacion_polinomial` habla de «a lo sumo `p n` líneas con coeficientes
  a lo sumo `q n`», no del tamaño mínimo.
* Las constantes son malas. La cota solo dice algo para `n` enorme: en `n = 2^40`,
  `2^(2^10/2) = 2^512` está muy por debajo de `2^(4(b+1)² + 1)` con `b ≥ 83`.
* Se cuentan líneas, no bits. El tamaño en bits de una refutación es al menos su número de líneas,
  así que la cota también vale para bits.
-/

open Cslib Cslib.Logic.PL Cslib.Circuits Cslib.Circuits.Clique Cslib.BitString.Graph

namespace Sagitta.Map
namespace Tiempo
namespace PlanosDeCorteClique

/-! ### Renombrar desigualdades -/

section Renombrar

variable {V W : Type*}

/-- Renombrar es aditivo. -/
theorem relabel_add (f : V → W) (I J : Ineq V) :
    (I + J).relabel f = I.relabel f + J.relabel f :=
  Ineq.ext Finsupp.mapDomain_add rfl

/-- Renombrar como homomorfismo aditivo. -/
noncomputable def relabelHom (f : V → W) : Ineq V →+ Ineq W where
  toFun := Ineq.relabel f
  map_zero' := Ineq.ext (Finsupp.mapDomain_zero (f := f)) rfl
  map_add' := relabel_add f

/-- Renombrar una suma finita. -/
theorem relabel_sum (f : V → W) {ι : Type*} (s : Finset ι) (g : ι → Ineq V) :
    (∑ i ∈ s, g i).relabel f = ∑ i ∈ s, (g i).relabel f :=
  map_sum (relabelHom f) g s

/-- Renombrar `0 ≥ 1` da `0 ≥ 1`. -/
theorem relabel_contra (f : V → W) : (Ineq.contra : Ineq V).relabel f = Ineq.contra :=
  Ineq.ext (Finsupp.mapDomain_zero (f := f)) rfl

/-- Renombrar la desigualdad de un literal. -/
theorem literal_toIneq_map (f : V → W) (l : Literal V) :
    Literal.toIneq (Prod.map f id l) = l.toIneq.relabel f := by
  obtain ⟨v, b⟩ := l
  cases b <;>
    exact Ineq.ext (by simp only [Prod.map_apply, id, Literal.toIneq_false,
      Literal.toIneq_true, Ineq.coeff_leOne, Ineq.coeff_nonneg, Ineq.coeff_relabel,
      Finsupp.mapDomain_single]) rfl

/-- Con un renombre inyectivo, la desigualdad de la cláusula renombrada es la desigualdad
renombrada. -/
theorem clause_toIneq_relabel [DecidableEq V] [DecidableEq W] {f : V → W}
    (hf : Function.Injective f) (c : Clause V) :
    (c.relabel f).toIneq = c.toIneq.relabel f := by
  have hinj : Function.Injective (Prod.map f (id : Bool → Bool)) :=
    by
      intro a b h
      simp only [Prod.map, Prod.mk.injEq] at h
      exact Prod.ext (hf h.1) h.2
  have himg : (c.map (Prod.map f id)).toFinset = c.toFinset.image (Prod.map f id) := by
    ext; simp
  rw [Clause.relabel, Clause.toIneq, Clause.toIneq, relabel_add, relabel_contra, relabel_sum,
    himg, Finset.sum_image (fun x _ y _ h => hinj h)]
  simp only [literal_toIneq_map]

/-- Las desigualdades de una fórmula renombrada. -/
theorem toIneqs_relabel [DecidableEq V] [DecidableEq W] {f : V → W}
    (hf : Function.Injective f) (φ : CNF V) :
    (φ.relabel f).toIneqs = Ineq.relabel f '' φ.toIneqs := by
  ext I
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact ⟨d.toIneq, ⟨d, hd, rfl⟩, (clause_toIneq_relabel hf d).symm⟩
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d.relabel f, List.mem_map.2 ⟨d, hd, rfl⟩, clause_toIneq_relabel hf d⟩

/-- Las desigualdades de una concatenación. -/
theorem toIneqs_append [DecidableEq V] (φ ψ : CNF V) :
    (φ ++ ψ).toIneqs = φ.toIneqs ∪ ψ.toIneqs := by
  ext I
  simp only [CNF.toIneqs, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨c, hc | hc, rfl⟩
    exacts [Or.inl ⟨c, hc, rfl⟩, Or.inr ⟨c, hc, rfl⟩]
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    exacts [⟨c, Or.inl hc, rfl⟩, ⟨c, Or.inr hc, rfl⟩]

end Renombrar

/-! ### La partición de las variables -/

variable {n k r : ℕ}

/-- **La partición.** Las desigualdades de `Clique_{n,k} ∧ Color_{n,r}` son las del clique, sobre
las aristas `p` y las variables `q`, más las del coloreo, sobre las aristas y las variables `z`.
Es la forma que pide la interpolación de cslib-frontier. -/
theorem toIneqs_cliqueColoring :
    (CNF.cliqueColoring n k r).toIneqs =
      Ineq.relabel (Sum.map id Sum.inl) '' (CNF.clique n k).toIneqs ∪
        Ineq.relabel (Sum.map id Sum.inr) '' (CNF.coloring n r).toIneqs := by
  rw [CNF.cliqueColoring, CNF.appendShared, toIneqs_append,
    toIneqs_relabel (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩),
    toIneqs_relabel (Sum.map_injective.2 ⟨Function.injective_id, Sum.inr_injective⟩)]

/-- **Las aristas tienen coeficiente no negativo en el clique.** Las aristas solo aparecen en
positivo. Es lo que pide la interpolación monótona. -/
theorem coeff_arista_nonneg {E : Ineq (Fin (edgeCount n) ⊕ Fin k × Fin n)}
    (hE : E ∈ (CNF.clique n k).toIneqs) (i : Fin (edgeCount n)) : 0 ≤ E.coeff (.inl i) := by
  obtain ⟨c, hc, rfl⟩ := hE
  rw [Clause.toIneq, Ineq.coeff_add, Ineq.coeff_sum]
  rw [Finsupp.add_apply, Finset.sum_apply', Ineq.coeff_contra, Finsupp.zero_apply, zero_add]
  refine Finset.sum_nonneg fun l hl => ?_
  obtain ⟨v, b⟩ := l
  cases b
  · have hv : v ≠ .inl i := by
      rintro rfl
      exact absurd (CNF.eq_true_of_mem_clique hc (List.mem_toFinset.1 hl)) (by simp)
    simp [hv]
  · simp only [Literal.toIneq_true, Ineq.coeff_nonneg, Finsupp.single_apply]
    split_ifs <;> simp

/-- **Las aristas tienen coeficiente a lo sumo `1` en el clique.** La cláusula pasa por
`toFinset`: el literal positivo de una arista aparece a lo sumo una vez. -/
theorem coeff_arista_le_one {E : Ineq (Fin (edgeCount n) ⊕ Fin k × Fin n)}
    (hE : E ∈ (CNF.clique n k).toIneqs) (i : Fin (edgeCount n)) : E.coeff (.inl i) ≤ 1 := by
  obtain ⟨c, hc, rfl⟩ := hE
  rw [Clause.toIneq, Ineq.coeff_add, Ineq.coeff_sum]
  rw [Finsupp.add_apply, Finset.sum_apply', Ineq.coeff_contra, Finsupp.zero_apply, zero_add]
  have hterm : ∀ l ∈ c.toFinset,
      (Literal.toIneq l).coeff (.inl i) = if l = (.inl i, true) then 1 else 0 := by
    intro l hl
    obtain ⟨v, b⟩ := l
    cases b
    · have hv : v ≠ .inl i := by
        rintro rfl
        exact absurd (CNF.eq_true_of_mem_clique hc (List.mem_toFinset.1 hl)) (by simp)
      simp [hv]
    · simp only [Literal.toIneq_true, Ineq.coeff_nonneg, Finsupp.single_apply, Prod.mk.injEq,
        and_true]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs <;> simp


/-! ### Refutaciones con coeficientes acotados -/

/-- `Γ` tiene una refutación por planos de corte de a lo sumo `s` líneas, con todos los
coeficientes de valor absoluto a lo sumo `M`. -/
def RefutaAcotada {V : Type*} (Γ : Set (Ineq V)) (s M : ℕ) : Prop :=
  ∃ ls, CuttingPlanes.IsProof Γ ls ∧ Ineq.contra ∈ ls ∧ ls.length ≤ s ∧
    ∀ I ∈ ls, ∀ w, |I.coeff w| ≤ M

/-- **Interpolación monótona para clique–coloreo.** Una refutación por planos de corte de
`Clique_{n,k} ∧ Color_{n,r}` con coeficientes a lo sumo `M` da un circuito monótono que separa los
grafos con `k`-clique de los `r`-coloreables. Su tamaño es a lo sumo
`(|ls| · 2^(2t) + 1) · 2^(2t+1)`, con `t` como en Krajíček 6.4. -/
theorem existe_separador
    {ls : List (Ineq (Fin (edgeCount n) ⊕ (Fin k × Fin n ⊕ Fin n × Fin r)))}
    (h : CuttingPlanes.IsProof (CNF.cliqueColoring n k r).toIneqs ls) (hc : Ineq.contra ∈ ls)
    {M t : ℕ} (hM : ∀ I ∈ ls, ∀ w, |I.coeff w| ≤ M)
    (ht₂ : Nat.clog 2 (2 * M * (k * n) + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 (edgeCount n) * (Nat.clog 2 (2 * M * edgeCount n + 1) + 1) ≤ t) :
    ∃ C : Circuit Monotone.signature (edgeCount n) 1,
      C.size ≤ (ls.length * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      Separates k r fun x => C.eval Monotone.interpretation x 0 := by
  rw [toIneqs_cliqueColoring] at h
  have hcard : Fintype.card (Fin k × Fin n) = k * n := by simp
  obtain ⟨C, hsize, hU, hV⟩ := CuttingPlanes.IsProof.exists_monotone_circuit_of_abs_coeff_le h hc
    (fun E hE i => coeff_arista_nonneg hE i) hM (by rw [hcard]; exact ht₂) ht₃
  refine ⟨C, hsize, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨q, hq⟩ := (CNF.exists_eval_clique_iff x).2 hx
    exact hU x q ((CNF.holds_toIneqs_iff _ _).2 hq)
  · obtain ⟨z, hz⟩ := (CNF.exists_eval_coloring_iff x).2 hx
    exact hV x z ((CNF.holds_toIneqs_iff _ _).2 hz)

/-- **Interpolación monótona, con cota solo sobre `q`.** Como `existe_separador`, pero `M` acota
solo los coeficientes de las variables `q` (privadas del clique) en la refutación. Los de `p` y `z`
pueden ser grandes. Las aristas del clique tienen coeficiente `0` o `1`, así que la segunda
condición sobre `t` usa `1` en lugar de `M`. -/
theorem existe_separador'
    {ls : List (Ineq (Fin (edgeCount n) ⊕ (Fin k × Fin n ⊕ Fin n × Fin r)))}
    (h : CuttingPlanes.IsProof (CNF.cliqueColoring n k r).toIneqs ls) (hc : Ineq.contra ∈ ls)
    {M t : ℕ} (hM : ∀ I ∈ ls, ∀ y, |I.coeff (.inr (.inl y))| ≤ M)
    (ht₂ : Nat.clog 2 (2 * M * (k * n) + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 (edgeCount n) * (Nat.clog 2 (2 * 1 * edgeCount n + 1) + 1) ≤ t) :
    ∃ C : Circuit Monotone.signature (edgeCount n) 1,
      C.size ≤ (ls.length * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      Separates k r fun x => C.eval Monotone.interpretation x 0 := by
  rw [toIneqs_cliqueColoring] at h
  have hcard : Fintype.card (Fin k × Fin n) = k * n := by simp
  obtain ⟨C, hsize, hU, hV⟩ := CuttingPlanes.IsProof.exists_monotone_circuit (M₀ := 1) h hc
    (fun E hE i => coeff_arista_nonneg hE i)
    (fun E hE i => by
      rw [abs_of_nonneg (coeff_arista_nonneg hE i)]
      exact_mod_cast coeff_arista_le_one hE i)
    hM (by rw [hcard]; exact ht₂) ht₃
  refine ⟨C, hsize, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨q, hq⟩ := (CNF.exists_eval_clique_iff x).2 hx
    exact hU x q ((CNF.holds_toIneqs_iff _ _).2 hq)
  · obtain ⟨z, hz⟩ := (CNF.exists_eval_coloring_iff x).2 hx
    exact hV x z ((CNF.holds_toIneqs_iff _ _).2 hz)

/-- **Cota inferior, forma de Alon–Boppana.** Para `2 ≤ l`, `2 l² ≤ r < k` y
`8 l (⌊log₂ n⌋ + 3) k ≤ n`, toda refutación de `Clique_{n,k} ∧ Color_{n,r}` con `s` líneas y
coeficientes a lo sumo `M` cumple `2^l < (s · 2^(2t) + 1) · 2^(2t+1)`. -/
theorem cota_alon_boppana {l s M t : ℕ} (hl : 2 ≤ l) (hr : 2 * l ^ 2 ≤ r) (hrk : r < k)
    (hn : 8 * l * (Nat.log 2 n + 3) * k ≤ n)
    (h : RefutaAcotada (CNF.cliqueColoring n k r).toIneqs s M)
    (ht₂ : Nat.clog 2 (2 * M * (k * n) + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 (edgeCount n) * (Nat.clog 2 (2 * M * edgeCount n + 1) + 1) ≤ t) :
    2 ^ l < (s * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) := by
  obtain ⟨ls, hp, hc, hs, hM⟩ := h
  obtain ⟨C, hsize, hC⟩ := existe_separador hp hc hM ht₂ ht₃
  calc 2 ^ l < C.size := Monotone.two_pow_lt_size_of_separates hl hr hrk hn hC
    _ ≤ (ls.length * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) := hsize
    _ ≤ (s * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) := by gcongr

/-- **Cota inferior, forma de Krajíček 7.3.** Para `n ≥ 2^40` y `⌊√n⌋ < k ≤ ⌊√n⌋ + 2`, toda
refutación de `Clique_{n,k} ∧ Color_{n,k-1}` con `s` líneas y coeficientes a lo sumo `M` cumple
`2^⌊⌊√⌊√n⌋⌋/2⌋ < (s · 2^(2t) + 1) · 2^(2t+1)`. -/
theorem cota_raiz {s M t : ℕ} (hn : 2 ^ 40 ≤ n) (hk : n.sqrt < k) (hk' : k ≤ n.sqrt + 2)
    (h : RefutaAcotada (CNF.cliqueColoring n k (k - 1)).toIneqs s M)
    (ht₂ : Nat.clog 2 (2 * M * (k * n) + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 (edgeCount n) * (Nat.clog 2 (2 * M * edgeCount n + 1) + 1) ≤ t) :
    2 ^ (n.sqrt.sqrt / 2) < (s * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) := by
  obtain ⟨ls, hp, hc, hs, hM⟩ := h
  obtain ⟨C, hsize, hC⟩ := existe_separador hp hc hM ht₂ ht₃
  calc 2 ^ (n.sqrt.sqrt / 2) < C.size := Monotone.two_pow_lt_size_of_separates_sqrt hn hk hk' hC
    _ ≤ (ls.length * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) := hsize
    _ ≤ (s * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) := by gcongr

/-- El `t` de Krajíček cabe en `(b + 1)²` cuando `2 (M + 1) n² + 1 ≤ 2^b` y `k ≤ n`. -/
theorem t_cabe {M b : ℕ} (hkn : k ≤ n) (hb : 2 * (M + 1) * n ^ 2 + 1 ≤ 2 ^ b) :
    Nat.clog 2 (2 * M * (k * n) + 1) + 1 ≤ (b + 1) ^ 2 ∧
      Nat.clog 2 (edgeCount n) * (Nat.clog 2 (2 * M * edgeCount n + 1) + 1) ≤ (b + 1) ^ 2 := by
  have hE : edgeCount n ≤ n ^ 2 := (edgeCount_eq_choose n).trans_le (Nat.choose_le_pow n 2)
  have hkn2 : k * n ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right n hkn
  have hMn : 2 * M * n ^ 2 + 1 ≤ 2 ^ b := le_trans (by nlinarith) hb
  have h₁ : Nat.clog 2 (2 * M * (k * n) + 1) ≤ b :=
    Nat.clog_le_of_le_pow (le_trans (by gcongr) hMn)
  have h₂ : Nat.clog 2 (2 * M * edgeCount n + 1) ≤ b :=
    Nat.clog_le_of_le_pow (le_trans (by gcongr) hMn)
  have h₃ : Nat.clog 2 (edgeCount n) ≤ b :=
    Nat.clog_le_of_le_pow (le_trans hE (le_trans (by nlinarith) hb))
  constructor
  · nlinarith
  · calc Nat.clog 2 (edgeCount n) * (Nat.clog 2 (2 * M * edgeCount n + 1) + 1)
        ≤ b * (b + 1) := Nat.mul_le_mul h₃ (by omega)
      _ ≤ (b + 1) ^ 2 := by nlinarith

/-- `(s · X + 1) · 2X ≤ (s + 1) · 2X²` con `X = 2^(2T)`. -/
theorem acota_tamano (s T : ℕ) :
    (s * 2 ^ (2 * T) + 1) * 2 ^ (2 * T + 1) ≤ (s + 1) * 2 ^ (4 * T + 1) := by
  have hX : 1 ≤ 2 ^ (2 * T) := Nat.one_le_two_pow
  have e₁ : 2 ^ (2 * T + 1) = 2 ^ (2 * T) * 2 := pow_succ 2 (2 * T)
  have e₂ : 2 ^ (4 * T + 1) = 2 ^ (2 * T) * 2 ^ (2 * T) * 2 := by
    rw [show 4 * T + 1 = 2 * T + 2 * T + 1 by ring, pow_succ, pow_add]
  rw [e₁, e₂]
  nlinarith

/-- **Cota inferior con coeficientes de `b` bits.** Si `2 (M + 1) n² + 1 ≤ 2^b`, para
`n ≥ 2^40` y `⌊√n⌋ < k ≤ ⌊√n⌋ + 2`, toda refutación de `Clique_{n,k} ∧ Color_{n,k-1}` con `s`
líneas y coeficientes a lo sumo `M` cumple `2^⌊⌊√⌊√n⌋⌋/2⌋ < (s + 1) · 2^(4(b+1)² + 1)`. Con `M`
polinomial en `n`, `b = O(log n)`: el número de líneas es `2^(Ω(n^{1/4}) − O(log² n))`. -/
theorem cota_bits {s M b : ℕ} (hn : 2 ^ 40 ≤ n) (hk : n.sqrt < k) (hk' : k ≤ n.sqrt + 2)
    (hb : 2 * (M + 1) * n ^ 2 + 1 ≤ 2 ^ b)
    (h : RefutaAcotada (CNF.cliqueColoring n k (k - 1)).toIneqs s M) :
    2 ^ (n.sqrt.sqrt / 2) < (s + 1) * 2 ^ (4 * (b + 1) ^ 2 + 1) := by
  have hkn : k ≤ n := by
    have h1 := Nat.sqrt_le_self n
    have h2 : n.sqrt + 2 ≤ n := by
      have : 2 ≤ n.sqrt := Nat.le_sqrt.2 (by omega)
      have := Nat.sqrt_le' n
      nlinarith
    omega
  obtain ⟨ht₂, ht₃⟩ := t_cabe (M := M) hkn hb
  exact (cota_raiz hn hk hk' h ht₂ ht₃).trans_le (acota_tamano s _)


/-! ### Superpolinomial: la sucesión `n = 2^(4j)` -/

/-- `⌊√(2^(4j))⌋ = 2^(2j)`. -/
theorem sqrt_dos_pow_cuatro (j : ℕ) : Nat.sqrt (2 ^ (4 * j)) = 2 ^ (2 * j) := by
  rw [show 4 * j = 2 * j + 2 * j by ring, pow_add, Nat.sqrt_eq]

/-- `⌊√(2^(2j))⌋ = 2^j`. -/
theorem sqrt_dos_pow_dos (j : ℕ) : Nat.sqrt (2 ^ (2 * j)) = 2 ^ j := by
  rw [two_mul, pow_add, Nat.sqrt_eq]

/-- Una cota `c · (N + 1)^d` en `N = 2^(4j)` queda bajo `2^(c + (4j+1) d)`, con lugar para
sumar uno. -/
theorem cota_pol_en_pow (c d j x : ℕ) (hx : x ≤ c * (2 ^ (4 * j) + 1) ^ d) :
    x + 1 ≤ 2 ^ (c + (4 * j + 1) * d) := by
  have hN : 2 ^ (4 * j) + 1 ≤ 2 ^ (4 * j + 1) := by
    rw [pow_succ]; have := Nat.one_le_two_pow (n := 4 * j); omega
  have hpow : (2 ^ (4 * j) + 1) ^ d ≤ 2 ^ ((4 * j + 1) * d) := by
    rw [pow_mul 2 (4 * j + 1) d]; exact Nat.pow_le_pow_left hN d
  have hc : c < 2 ^ c := Nat.lt_two_pow_self
  have : c * (2 ^ (4 * j) + 1) ^ d < 2 ^ c * 2 ^ ((4 * j + 1) * d) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left c hpow)
      (Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos _))
  rw [pow_add]
  omega

/-- Pasar de la cota sobre `2^Y` a una sobre los exponentes, sin desplegar potencias. -/
theorem exponente_lt {Y s P E : ℕ} (hc : 2 ^ Y < (s + 1) * 2 ^ E) (hs : s + 1 ≤ 2 ^ P) :
    Y < P + E := by
  have h : 2 ^ Y < 2 ^ (P + E) := by
    rw [pow_add]
    exact hc.trans_le (Nat.mul_le_mul_right _ hs)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h

/-- Si `2A + 2 < X`, entonces `⌊X/2⌋ ≥ A`. -/
theorem mitad_no_lt {X A : ℕ} (h : 2 * A + 2 < X) : ¬ X / 2 < A := by omega

/-- Con `x + 1 ≤ 2^a` y `N = 2^(4j)`: `2 (x + 1) N² + 1 ≤ 2^(a + 8j + 2)`. -/
theorem cota_b_en_pow (a j x : ℕ) (hx : x + 1 ≤ 2 ^ a) :
    2 * (x + 1) * (2 ^ (4 * j)) ^ 2 + 1 ≤ 2 ^ (a + 8 * j + 2) := by
  have hN2 : (2 ^ (4 * j)) ^ 2 = 2 ^ (8 * j) := by
    rw [← pow_mul, show 4 * j * 2 = 8 * j by ring]
  have hY : 1 ≤ 2 ^ (8 * j) := Nat.one_le_two_pow
  rw [hN2, pow_add, pow_add]
  generalize 2 ^ (8 * j) = Y at *
  generalize 2 ^ a = A at *
  nlinarith

/-- **Sin refutaciones polinomiales con coeficientes polinomiales.** No hay funciones `p` y `q`
acotadas por polinomios tales que, para infinitos `j`, la fórmula `Clique_{n,k} ∧ Color_{n,k-1}`
con `n = 2^(4j)` y `k = 2^(2j) + 1 = ⌊√n⌋ + 1` tenga una refutación por planos de corte de a lo sumo
`p n` líneas con coeficientes a lo sumo `q n`. Pedirlo para infinitos `j` (y no para todos) hace
el teorema más fuerte: la prueba solo usa un `j` grande. -/
theorem sin_refutacion_polinomial :
    ¬ ∃ p q : ℕ → ℕ, PolynomiallyBounded p ∧ PolynomiallyBounded q ∧ ∃ᶠ j in Filter.atTop,
      RefutaAcotada (CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).toIneqs
        (p (2 ^ (4 * j))) (q (2 ^ (4 * j))) := by
  rintro ⟨p, q, hp, hq, h⟩
  obtain ⟨c₁, d₁, hp'⟩ := polynomiallyBounded_iff_le.1 hp
  obtain ⟨c₂, d₂, hq'⟩ := polynomiallyBounded_iff_le.1 hq
  have hg : PolynomiallyBounded fun j =>
      2 * (c₁ + (4 * j + 1) * d₁ + 4 * (c₂ + (4 * j + 1) * d₂ + 8 * j + 3) ^ 2 + 1) + 2 := by
    fun_prop
  obtain ⟨j, hRj, hj, hj10⟩ :=
    (h.and_eventually (hg.eventually_lt_two_pow.and (Filter.eventually_ge_atTop 10))).exists
  set N := 2 ^ (4 * j) with hNdef
  set b := c₂ + (4 * j + 1) * d₂ + 8 * j + 2 with hbdef
  have hs := cota_pol_en_pow c₁ d₁ j (p N) (hp' N)
  have hb : 2 * (q N + 1) * N ^ 2 + 1 ≤ 2 ^ b :=
    cota_b_en_pow _ j _ (cota_pol_en_pow c₂ d₂ j (q N) (hq' N))
  have hN40 : 2 ^ 40 ≤ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : N.sqrt = 2 ^ (2 * j) := sqrt_dos_pow_cuatro j
  have hR : RefutaAcotada (CNF.cliqueColoring N (2 ^ (2 * j) + 1) (2 ^ (2 * j) + 1 - 1)).toIneqs
      (p N) (q N) := by rw [Nat.add_sub_cancel]; exact hRj
  have hcota := cota_bits (k := 2 ^ (2 * j) + 1) hN40 (by rw [hsq]; omega) (by rw [hsq]; omega)
    hb hR
  rw [hsq, sqrt_dos_pow_dos] at hcota
  have hexp := exponente_lt hcota hs
  refine mitad_no_lt ?_ hexp
  have hb1 : b + 1 = c₂ + (4 * j + 1) * d₂ + 8 * j + 3 := by rw [hbdef]
  rw [hb1]
  linarith


/-! ### Controles: las hipótesis se cumplen -/

/-- La fórmula de la sucesión es insatisfacible: hay algo que refutar. -/
example (j : ℕ) :
    ¬ (CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).Satisfiable :=
  CNF.not_satisfiable_cliqueColoring (by omega)

/-- Hay una desigualdad del clique con una arista de coeficiente `1`: la partición no es trivial
(`n = 2`, `k = 2`, la cláusula (1c) de los miembros `0 < 1` en los vértices `0 ≠ 1`). -/
example : ∃ E ∈ (CNF.clique 2 2).toIneqs, ∃ i, E.coeff (.inl i) = 1 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  refine ⟨(CNF.cliqueEdgeClause (0 : Fin 2) 1 h01).toIneq,
    CNF.toIneq_mem_toIneqs (CNF.mem_clique.2 (Or.inr (Or.inr ⟨0, 1, by decide, 0, 1, h01, rfl⟩))),
    edgeEquiv 2 (edge h01), ?_⟩
  rw [Clause.toIneq_of_nodup (by simp [CNF.cliqueEdgeClause])]
  simp [CNF.cliqueEdgeClause]

/-- `0 ≥ 1` está entre las desigualdades de `Clique_{0,1} ∧ Color_{0,0}`: el miembro `0` no tiene
vértice, y su cláusula (1a) es vacía. -/
theorem contra_mem_cero :
    (Ineq.contra : Ineq _) ∈ (CNF.cliqueColoring 0 1 0).toIneqs := by
  rw [toIneqs_cliqueColoring]
  refine Or.inl ⟨Ineq.contra, ⟨CNF.cliqueMemberClause 0 0,
    CNF.mem_clique.2 (Or.inl ⟨0, rfl⟩), ?_⟩, relabel_contra _⟩
  simp [CNF.cliqueMemberClause]

/-- La hipótesis `RefutaAcotada` se cumple: `Clique_{0,1} ∧ Color_{0,0}` se refuta en una línea
con coeficientes `0`. -/
theorem refuta_cero : RefutaAcotada (CNF.cliqueColoring 0 1 0).toIneqs 1 0 :=
  ⟨[Ineq.contra], CuttingPlanes.IsProof.nil.hyp contra_mem_cero, List.mem_singleton_self _,
    le_rfl, by simp⟩

/-- `existe_separador` se aplica a esa refutación, con `t = 1`. -/
example : ∃ C : Circuit Monotone.signature (edgeCount 0) 1,
    Separates 1 0 fun x => C.eval Monotone.interpretation x 0 := by
  obtain ⟨ls, hp, hc, -, hM⟩ := refuta_cero
  obtain ⟨C, -, hC⟩ := existe_separador (t := 1) hp hc hM (by simp) (by simp)
  exact ⟨C, hC⟩

/-- `existe_separador'` también se aplica a `refuta_cero`, con `t = 1`. -/
example : ∃ C : Circuit Monotone.signature (edgeCount 0) 1,
    Separates 1 0 fun x => C.eval Monotone.interpretation x 0 := by
  obtain ⟨ls, hp, hc, -, hM⟩ := refuta_cero
  obtain ⟨C, -, hC⟩ :=
    existe_separador' (t := 1) hp hc (fun I hI y => hM I hI _) (by simp) (by simp)
  exact ⟨C, hC⟩

/-- **Hay refutaciones con alguna cota.** Con `r < k`, la fórmula es insatisfacible; por la
completitud de planos de corte (cslib-frontier) tiene una refutación de `s` líneas. Sus coeficientes
quedan bajo `M`, la suma de todos los valores absolutos. Ni `s` ni `M` están acotados aquí. -/
theorem refutaAcotada_of_not_sat (hr : r < k) :
    ∃ s M, RefutaAcotada (CNF.cliqueColoring n k r).toIneqs s M := by
  classical
  obtain ⟨s, ls, hp, hc, hlen⟩ :=
    CuttingPlanes.exists_refutableInSize_iff_not_satisfiable.2
      (CNF.not_satisfiable_cliqueColoring hr)
  refine ⟨s, ∑ I ∈ ls.toFinset, ∑ w, (I.coeff w).natAbs, ls, hp, hc, hlen, fun I hI w => ?_⟩
  have h1 : (I.coeff w).natAbs ≤ ∑ w, (I.coeff w).natAbs :=
    Finset.single_le_sum (f := fun w => (I.coeff w).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ w)
  have h2 : ∑ w, (I.coeff w).natAbs ≤ ∑ J ∈ ls.toFinset, ∑ w, (J.coeff w).natAbs :=
    Finset.single_le_sum (f := fun J => ∑ w, (J.coeff w).natAbs) (fun _ _ => Nat.zero_le _)
      (List.mem_toFinset.2 hI)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1.trans h2

/-- Las cinco hipótesis de `cota_bits` se cumplen a la vez: `n = 2^40`, `k = 2^20 + 1`, una
refutación con `s` líneas y coeficientes `≤ M`, y `b = 2 (M + 1) n² + 1`. -/
example : ∃ s M b, 2 ^ 40 ≤ 2 ^ 40 ∧ (2 ^ 40 : ℕ).sqrt < 2 ^ 20 + 1 ∧
    2 ^ 20 + 1 ≤ (2 ^ 40 : ℕ).sqrt + 2 ∧ 2 * (M + 1) * (2 ^ 40) ^ 2 + 1 ≤ 2 ^ b ∧
    RefutaAcotada (CNF.cliqueColoring (2 ^ 40) (2 ^ 20 + 1) (2 ^ 20 + 1 - 1)).toIneqs s M := by
  obtain ⟨s, M, h⟩ :=
    refutaAcotada_of_not_sat (n := 2 ^ 40) (k := 2 ^ 20 + 1) (r := 2 ^ 20 + 1 - 1) (by norm_num)
  have hs : (2 ^ 40 : ℕ).sqrt = 2 ^ 20 := sqrt_dos_pow_cuatro 10
  exact ⟨s, M, 2 * (M + 1) * (2 ^ 40) ^ 2 + 1, le_rfl, by rw [hs]; omega, by rw [hs]; omega,
    Nat.lt_two_pow_self.le, h⟩

/-- El enunciado que niega `sin_refutacion_polinomial` se cumple si no se piden polinomios: hay
`p` y `q` con refutación para todo `j` (y por tanto para infinitos). La negación no es trivial. -/
example : ∃ p q : ℕ → ℕ, ∃ᶠ j in Filter.atTop,
    RefutaAcotada (CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).toIneqs
      (p (2 ^ (4 * j))) (q (2 ^ (4 * j))) := by
  classical
  have h : ∀ N, ∃ s M, (∃ j, N = 2 ^ (4 * j)) →
      RefutaAcotada (CNF.cliqueColoring N (N.sqrt + 1) N.sqrt).toIneqs s M := fun N =>
    let ⟨s, M, h⟩ := refutaAcotada_of_not_sat (n := N) (k := N.sqrt + 1) (r := N.sqrt) (by omega)
    ⟨s, M, fun _ => h⟩
  choose p q hpq using h
  refine ⟨p, q, Filter.Frequently.of_forall fun j => ?_⟩
  have := hpq (2 ^ (4 * j)) ⟨j, rfl⟩
  rwa [sqrt_dos_pow_cuatro] at this

/-- Los parámetros de `cota_alon_boppana` se cumplen: `l = 2`, `r = 8`, `k = 9`, `n = 2^12`. -/
example : 2 ≤ 2 ∧ 2 * 2 ^ 2 ≤ 8 ∧ 8 < 9 ∧ 8 * 2 * (Nat.log 2 (2 ^ 12) + 3) * 9 ≤ 2 ^ 12 := by
  rw [Nat.log_pow (by norm_num)]
  norm_num

/-- Los parámetros de `cota_bits` se cumplen: `n = 2^40`, `k = 2^20 + 1`, `M = 1`, `b = 83`. -/
example : 2 ^ 40 ≤ 2 ^ 40 ∧ (2 ^ 40 : ℕ).sqrt < 2 ^ 20 + 1 ∧
    2 ^ 20 + 1 ≤ (2 ^ 40 : ℕ).sqrt + 2 ∧ 2 * (1 + 1) * (2 ^ 40) ^ 2 + 1 ≤ 2 ^ 83 := by
  have h := sqrt_dos_pow_cuatro 10
  norm_num at h
  norm_num [h]

/-- En la sucesión, `n = 2^(4j) ≥ 2^40` desde `j = 10`, y `k = ⌊√n⌋ + 1`. -/
example (j : ℕ) (hj : 10 ≤ j) : 2 ^ 40 ≤ 2 ^ (4 * j) ∧
    (2 ^ (4 * j)).sqrt < 2 ^ (2 * j) + 1 ∧ 2 ^ (2 * j) + 1 ≤ (2 ^ (4 * j)).sqrt + 2 := by
  rw [sqrt_dos_pow_cuatro]
  exact ⟨Nat.pow_le_pow_right (by norm_num) (by omega), by omega, by omega⟩

end PlanosDeCorteClique
end Tiempo
end Sagitta.Map
