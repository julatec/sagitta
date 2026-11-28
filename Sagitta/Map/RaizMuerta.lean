import Sagitta.Map.ArbolElecciones
import CslibFrontier.Logics.Propositional.Resolution.TreeLikePigeonhole
import CslibFrontier.Computability.DecisionTree.Leaves

/-!
# La raíz muerta: una cota inferior incondicional (E2)

Segunda pieza del plan. En `ArbolElecciones.lean` se vio que, sin
detector, certificar que no hay solución cuesta todo el árbol. Con el detector «hay una cláusula falsa» (`detCNF`), a
veces cuesta poco. Aquí se prueba que, para el principio del palomar, **no** cuesta poco: la vuelta atrás visita
`2^Ω(n log n)` nodos, con cualquier orden fijo de las variables.

## Cómo

La cota inferior ya está en cslib-frontier: todo árbol de decisión que encuentra una cláusula falsa de `PHP^m_n` tiene
más de `(n + 1 − h)^h / 2` hojas (`Cslib.Logic.PL.CNF.pow_lt_two_mul_leafCount_pigeonhole`, la cota de Beyersdorff,
Galesi y Lauria). Lo que falta es el puente:

1. **La corrida es un árbol de decisión** (`arbol`): en cada nodo donde el detector no dice nada, pregunta la variable
   siguiente; donde lo dice, deja una hoja con la cláusula falsa (`clFalsa`).
2. **Encuentra cláusulas falsas** (`arbol_encuentra`): si la raíz está muerta, para toda asignación la hoja a la que se
   llega tiene una cláusula de la fórmula falsa en esa asignación.
3. **No tiene más hojas que nodos visita la búsqueda** (`hojas_le_nodos`).
4. **Se lleva a las variables del palomar** (`encuentra_traer`) con la inversa del orden elegido.

## Lo que la cota no dice

Vale para el detector «hay una cláusula falsa», que es el de la vuelta atrás sin aprendizaje. Un detector más listo
puede costar mucho menos: uno perfecto declara la raíz muerta en un solo nodo. Que ningún detector de tiempo
polinomial lo logre es, otra vez, una forma de P ≠ NP.
-/

open Cslib Cslib.Logic.PL

namespace Sagitta.Map
namespace Tiempo

/-! ## La corrida como árbol de decisión -/

/-- La primera cláusula falsa en `p`, o la vacía si no hay. -/
def clFalsa (F : List Clausula) (p : List Bool) : Clausula := (F.find? (falsificada p)).getD []

/-- **La corrida de la vuelta atrás, como árbol de decisión.** -/
def arbol (F : List Clausula) : ℕ → List Bool → DecisionTree ℕ Clausula
  | 0, p => .leaf (clFalsa F p)
  | k + 1, p =>
    if detCNF F p then .leaf (clFalsa F p) else .node p.length (arbol F k (p ++ [false])) (arbol F k (p ++ [true]))

theorem clFalsa_spec {F : List Clausula} {p : List Bool} (h : detCNF F p = true) :
    clFalsa F p ∈ F ∧ falsificada p (clFalsa F p) = true := by
  simp only [detCNF, List.any_eq_true] at h
  obtain ⟨c, hc, hf⟩ := h
  cases hfind : F.find? (falsificada p) with
  | none => exact absurd hfind (List.find?_isSome.mpr ⟨c, hc, hf⟩ |> Option.isSome_iff_ne_none.mp)
  | some c' =>
    simp only [clFalsa, hfind, Option.getD_some]
    exact ⟨List.mem_of_find?_eq_some hfind, List.find?_some hfind⟩

/-- `σ` sigue el camino `p`. -/
def Sigue (σ : ℕ → Bool) (p : List Bool) : Prop := ∀ i (h : i < p.length), σ i = p[i]

theorem sigue_snoc {σ : ℕ → Bool} {p : List Bool} (h : Sigue σ p) : Sigue σ (p ++ [σ p.length]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
  · rw [List.getElem_append_left hlt]; exact h i hlt
  · subst heq; simp

/-- Una cláusula falsa en `p` es falsa en toda asignación que sigue `p`. -/
theorem eval_falsificada {σ : ℕ → Bool} {p : List Bool} {c : Clausula} (hs : Sigue σ p)
    (hf : falsificada p c = true) : Clause.eval σ c = false := by
  simp only [Clause.eval, List.any_eq_false]
  intro l hl
  simp only [falsificada, List.all_eq_true] at hf
  have hfl := hf l hl
  split at hfl
  · rename_i v hv
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hv
    simp only [Literal.eval, beq_iff_eq]
    rw [hs l.1 hlt, hget]
    simpa using hfl
  · exact absurd hfl (by simp)

/-- En una asignación completa sin solución, el detector ya ve una cláusula falsa. -/
theorem det_de_completa {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N) {p : List Bool}
    (hp : p.length = N) (hs : solCNF F p = false) : detCNF F p = true := by
  simp only [solCNF, List.all_eq_false] at hs
  obtain ⟨c, hc, hsat⟩ := hs
  simp only [detCNF, List.any_eq_true]
  refine ⟨c, hc, ?_⟩
  have hsat' : ∀ l ∈ c, p[l.1]? ≠ some l.2 := fun l hl heq =>
    hsat (by simp only [satisface, List.any_eq_true, beq_iff_eq]; exact ⟨l, hl, heq⟩)
  simp only [falsificada, List.all_eq_true]
  intro l hl
  have hlt : l.1 < p.length := hp ▸ hvar c hc l hl
  have hne := hsat' l hl
  rw [List.getElem?_eq_getElem hlt] at hne ⊢
  simp only [ne_eq, Option.some.injEq] at hne
  simpa using hne

/-- **El árbol encuentra cláusulas falsas** debajo de todo nodo muerto. -/
theorem arbol_encuentra {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = N → ¬ Vivo (solCNF F) k p →
      ∀ σ : ℕ → Bool, Sigue σ p → (arbol F k p).eval σ ∈ F ∧ Clause.eval σ ((arbol F k p).eval σ) = false
  | 0, p, hl, hm, σ, hs => by
    have hsol : solCNF F p = false := by
      cases h : solCNF F p
      · rfl
      · exact absurd ((vivo_cero _ p).mpr h) hm
    have hd := det_de_completa hvar (by simpa using hl) hsol
    obtain ⟨h1, h2⟩ := clFalsa_spec hd
    exact ⟨h1, eval_falsificada hs h2⟩
  | k + 1, p, hl, hm, σ, hs => by
    by_cases hd : detCNF F p = true
    · simp only [arbol, hd, ite_true, DecisionTree.eval_leaf]
      obtain ⟨h1, h2⟩ := clFalsa_spec hd
      exact ⟨h1, eval_falsificada hs h2⟩
    · simp only [arbol, hd, Bool.false_eq_true, ite_false, DecisionTree.eval_node]
      have hb : ∀ b, ¬ Vivo (solCNF F) k (p ++ [b]) := fun b h =>
        hm ((vivo_succ _ k p).mpr (by cases b <;> simp [h]))
      have hl' : (p ++ [σ p.length]).length + k = N := by simp; omega
      have ih := arbol_encuentra hvar k (p ++ [σ p.length]) hl' (hb _) σ (sigue_snoc hs)
      cases hσ : σ p.length
      · simpa [hσ] using ih
      · simpa [hσ] using ih

/-- **El árbol no tiene más hojas que nodos visita la búsqueda.** -/
theorem hojas_le_nodos (F : List Clausula) :
    ∀ (k : ℕ) (p : List Bool), ¬ Vivo (solCNF F) k p →
      (arbol F k p).leafCount ≤ nodos (solCNF F) (detCNF F) k p
  | 0, p, _ => by
    simp only [arbol, DecisionTree.leafCount, nodos]
    unfold buscar; split <;> simp
  | k + 1, p, hm => by
    by_cases hd : detCNF F p = true
    · simp only [arbol, hd, ite_true, DecisionTree.leafCount, nodos]
      unfold buscar; simp [hd]
    · have hb : ∀ b, ¬ Vivo (solCNF F) k (p ++ [b]) := fun b h =>
        hm ((vivo_succ _ k p).mpr (by cases b <;> simp [h]))
      have ha : (buscar (solCNF F) (detCNF F) k (p ++ [false])).1 = false := by
        cases h : (buscar (solCNF F) (detCNF F) k (p ++ [false])).1
        · rfl
        · exact absurd ((buscar_correcto (detCNF_sano F) k _).mp h) (hb false)
      have i0 := hojas_le_nodos F k (p ++ [false]) (hb false)
      have i1 := hojas_le_nodos F k (p ++ [true]) (hb true)
      simp only [arbol, hd, Bool.false_eq_true, ite_false, DecisionTree.leafCount]
      unfold nodos at i0 i1 ⊢
      simp only [buscar, hd, ha, Bool.false_eq_true, ite_false]
      omega

/-! ## Sin solución, la raíz está muerta -/

/-- Si la fórmula (como `CNF ℕ`) no es satisfacible, la raíz está muerta. -/
theorem raiz_muerta {F : List Clausula} (hF : ¬ CNF.Satisfiable (F : CNF ℕ)) (N : ℕ) :
    ¬ Vivo (solCNF F) N [] := by
  rintro ⟨q, -, hq⟩
  apply hF
  refine ⟨fun i => q.getD i false, ?_⟩
  simp only [List.nil_append, solCNF, List.all_eq_true] at hq
  simp only [CNF.eval, List.all_eq_true]
  intro c hc
  have := hq c hc
  simp only [satisface, List.any_eq_true, beq_iff_eq] at this
  obtain ⟨l, hl, hget⟩ := this
  simp only [Clause.eval, List.any_eq_true]
  refine ⟨l, hl, ?_⟩
  simp [Literal.eval, List.getD_eq_getElem?_getD, hget]

/-! ## Traer el árbol a las variables originales -/

theorem leafCount_map {ι β γ : Type*} (g : β → γ) (t : DecisionTree ι β) : (t.map g).leafCount = t.leafCount := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ => simp [DecisionTree.map, DecisionTree.leafCount, ih₀, ih₁]

/-- **Un árbol que encuentra cláusulas falsas de `φ.relabel f` da uno que las encuentra en `φ`**, con las mismas hojas. -/
theorem encuentra_traer {V : Type*} [Nonempty V] {φ : CNF V} {f : V → ℕ} (hf : Function.Injective f)
    {t : DecisionTree ℕ (Clause ℕ)} (ht : t.FindsFalsifiedClause (φ.relabel f)) :
    ((t.mapQueries (Function.invFun f)).map (Clause.relabel (Function.invFun f))).FindsFalsifiedClause φ := by
  have hgf : Function.invFun f ∘ f = id := funext (Function.leftInverse_invFun hf)
  intro σ
  simp only [DecisionTree.eval_map, DecisionTree.eval_mapQueries]
  obtain ⟨hmem, hev⟩ := ht (σ ∘ Function.invFun f)
  simp only [CNF.relabel, List.mem_map] at hmem
  obtain ⟨c, hc, hcf⟩ := hmem
  rw [← hcf]
  have hback : (c.relabel f).relabel (Function.invFun f) = c := by
    simp only [Clause.relabel, List.map_map]
    conv_rhs => rw [← List.map_id c]
    congr 1
    funext l
    simp [Prod.map, Function.leftInverse_invFun hf l.1]
  rw [hback]
  refine ⟨hc, ?_⟩
  rw [← hcf, Clause.eval_relabel] at hev
  rwa [Function.comp_assoc, hgf, Function.comp_id] at hev

/-! ## El palomar -/

/-- **La vuelta atrás con el detector «hay una cláusula falsa», sobre el palomar, visita más de `(n + 1 − h)^h / 2`
nodos**, con cualquier orden fijo `f` de las variables. Con `h = n/2` es `2^Ω(n log n)`. -/
theorem palomar_nodos {m n : ℕ} (h : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    (n + 1 - h) ^ h < 2 * nodos (solCNF ((CNF.pigeonhole m n).relabel f))
      (detCNF ((CNF.pigeonhole m n).relabel f)) N [] := by
  have : Nonempty (Fin m × Fin n) := ⟨(⟨0, by omega⟩, ⟨0, hn⟩)⟩
  set F : List Clausula := (CNF.pigeonhole m n).relabel f
  have hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N := by
    intro c hc l hl
    simp only [F, CNF.relabel, List.mem_map] at hc
    obtain ⟨c', -, rfl⟩ := hc
    simp only [Clause.relabel, List.mem_map] at hl
    obtain ⟨l', -, rfl⟩ := hl
    exact hN l'.1
  have hunsat : ¬ CNF.Satisfiable (F : CNF ℕ) := by
    rw [CNF.satisfiable_relabel hf]; exact CNF.not_satisfiable_pigeonhole hnm
  have hm := raiz_muerta hunsat N
  have ht : (arbol F N []).FindsFalsifiedClause (F : CNF ℕ) := fun σ =>
    arbol_encuentra hvar N [] (by simp) hm σ (fun i hi => absurd hi (by simp))
  have ht' := encuentra_traer hf ht
  have hlow := CNF.pow_lt_two_mul_leafCount_pigeonhole h hnm ht'
  rw [leafCount_map, DecisionTree.leafCount_mapQueries] at hlow
  have := hojas_le_nodos F N [] hm
  omega

/-- **Con `h = n/2`**: más de `(n/2 + 1)^(n/2) / 2` nodos. -/
theorem palomar_nodos_mitad {m n : ℕ} (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    (n / 2 + 1) ^ (n / 2) < 2 * nodos (solCNF ((CNF.pigeonhole m n).relabel f))
      (detCNF ((CNF.pigeonhole m n).relabel f)) N [] :=
  lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) _) (palomar_nodos (n / 2) hnm hn hf hN)

end Tiempo
end Sagitta.Map
