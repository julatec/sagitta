import Sagitta.Map.Programa

/-!
# Los axiomas BASIC y el lema del testigo para S¹₂

`Testigo.lean` tiene una regla permisiva, `Deriv.aritm`: acepta cualquier hecho verdadero entre átomos. Aquí se
escriben los axiomas de la teoría de verdad y se dice cuándo una derivación usa solo esos.

## Qué hay

* **Los 32 axiomas BASIC** de Buss, leídos de «First-Order Proof Theory of Arithmetic» (*Handbook of Proof
  Theory*, 1998), cap. II, §1.3.3. Están partidos en secuentes de átomos: un axioma con «y» o con «si y solo si»
  da varios. Salen 44 secuentes.
* **Los axiomas de la igualdad**, 9 secuentes: reflexividad y sustitución en cada símbolo.
* **`Ax.valido`**: cada uno vale en los naturales.
* **`Deriv.basico`**: un axioma, con sus variables sustituidas por términos, como derivación.
* **`Deriv.EsDeS12`**: la derivación no usa más hechos que instancias de esos axiomas y la contradicción entre un
  átomo y su contrario.
* **`lema_del_testigo`**: el enunciado junto de lo que `Testigo.lean` y `Programa.lean` prueban.

## Qué teoría es

Las fórmulas del cálculo son las Σᵇ₁ en forma normal de negación, y la inducción es la de bits sobre esas
fórmulas. Una derivación con `EsDeS12` es entonces una derivación de S¹₂ **en la que toda fórmula es Σᵇ₁**. Buss
llega a ese caso desde una derivación cualquiera eliminando los cortes libres; ese paso no está aquí.

## Qué no hay

* **La eliminación de cortes libres**, que es lo que conecta con derivaciones de S¹₂ con fórmulas arbitrarias.
* **Los ejemplos de `Testigo.lean` derivados desde BASIC.** Usan hechos más cómodos. Aquí hay uno pequeño que sí
  sale solo de los axiomas.
-/

namespace Sagitta.Map
namespace Extraccion

open Formula

/-- Un secuente de átomos: si valen los de la izquierda, vale alguno de la derecha. -/
structure Sec : Type where
  ant : List Lit
  suc : List Lit

/-- El secuente vale en los naturales. -/
def Sec.Valido (s : Sec) : Prop :=
  ∀ ρ : Entorno, (∀ q ∈ s.ant, q.vale ρ = true) → ∃ q ∈ s.suc, q.vale ρ = true

theorem Lit.vale_le (t u : Termino) (ρ : Entorno) : (Lit.mk .le t u).vale ρ = true ↔ t.val ρ ≤ u.val ρ :=
  Rel.vale_le

theorem Lit.vale_eq (t u : Termino) (ρ : Entorno) : (Lit.mk .eq t u).vale ρ = true ↔ t.val ρ = u.val ρ :=
  Rel.vale_eq

theorem Lit.vale_neq (t u : Termino) (ρ : Entorno) : (Lit.mk .neq t u).vale ρ = true ↔ t.val ρ ≠ u.val ρ :=
  Rel.vale_neq

private theorem v0 {p : Lit} (h : ∀ ρ, p.vale ρ = true) : Sec.Valido ⟨[], [p]⟩ :=
  fun ρ _ => ⟨p, List.mem_cons_self, h ρ⟩

private theorem v1 {q p : Lit} (h : ∀ ρ, q.vale ρ = true → p.vale ρ = true) : Sec.Valido ⟨[q], [p]⟩ :=
  fun ρ hq => ⟨p, List.mem_cons_self, h ρ (hq _ List.mem_cons_self)⟩

private theorem v2 {q q' p : Lit} (h : ∀ ρ, q.vale ρ = true → q'.vale ρ = true → p.vale ρ = true) :
    Sec.Valido ⟨[q, q'], [p]⟩ :=
  fun ρ hq => ⟨p, List.mem_cons_self,
    h ρ (hq _ List.mem_cons_self) (hq _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

private theorem v3 {q q' q'' p : Lit}
    (h : ∀ ρ, q.vale ρ = true → q'.vale ρ = true → q''.vale ρ = true → p.vale ρ = true) :
    Sec.Valido ⟨[q, q', q''], [p]⟩ :=
  fun ρ hq => ⟨p, List.mem_cons_self,
    h ρ (hq _ List.mem_cons_self) (hq _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hq _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

private theorem v02 {p p' : Lit} (h : ∀ ρ, p.vale ρ = true ∨ p'.vale ρ = true) : Sec.Valido ⟨[], [p, p']⟩ :=
  fun ρ _ => (h ρ).elim (fun hp => ⟨p, List.mem_cons_self, hp⟩)
    (fun hp => ⟨p', List.mem_cons_of_mem _ List.mem_cons_self, hp⟩)

private theorem v12 {q p p' : Lit} (h : ∀ ρ, q.vale ρ = true → p.vale ρ = true ∨ p'.vale ρ = true) :
    Sec.Valido ⟨[q], [p, p']⟩ :=
  fun ρ hq => (h ρ (hq _ List.mem_cons_self)).elim (fun hp => ⟨p, List.mem_cons_self, hp⟩)
    (fun hp => ⟨p', List.mem_cons_of_mem _ List.mem_cons_self, hp⟩)

theorem size_doble (a : ℕ) (h : a ≠ 0) : Nat.size (2 * a) = Nat.size a + 1 := by
  rw [size_mitad (2 * a) (by omega)]
  have e : 2 * a / 2 = a := by omega
  rw [e]

theorem size_doble_mas (a : ℕ) : Nat.size (2 * a + 1) = Nat.size a + 1 := by
  rw [size_mitad (2 * a + 1) (by omega)]
  have e : (2 * a + 1) / 2 = a := by omega
  rw [e]

/-! ## Los axiomas -/

section
open Termino

private abbrev A : Termino := .var 0
private abbrev B : Termino := .var 1
private abbrev C : Termino := .var 2
private abbrev D : Termino := .var 3
private abbrev uno : Termino := .suc .cero
/-- `2 · t`, con `2 = S(S0)`. -/
private abbrev doble (t : Termino) : Termino := .prod (.suc (.suc .cero)) t
private abbrev le (t u : Termino) : Lit := ⟨.le, t, u⟩
private abbrev ig (t u : Termino) : Lit := ⟨.eq, t, u⟩
private abbrev dif (t u : Termino) : Lit := ⟨.neq, t, u⟩

/-- **Los axiomas**, uno por secuente. Los `b…` son los BASIC en el orden del Handbook (primera columna y luego
segunda); una letra al final distingue las partes de un axioma con «y» o «si y solo si». Los `e…` son los de la
igualdad. -/
inductive Ax : Type
  | b1 | b2 | b3 | b4a | b4b | b4c | b5 | b6 | b7 | b8 | b9 | b10 | b11a | b11b | b12 | b13 | b14
  | b15a | b15b | b16 | b17 | b18 | b19 | b20a | b20b | b21 | b22 | b23 | b24 | b25a | b25b | b26 | b27
  | b28 | b29 | b30a | b30b | b31 | b32a | b32b | b32c
  | eRefl | eLe | eEq | eSuc | eSuma | eProd | eMitad | eLargo | eSmash

/-- El secuente de cada axioma. Las variables son `a, b, c, d` = `0, 1, 2, 3`. -/
def Ax.sec : Ax → Sec
  | .b1 => ⟨[le A B], [le A (.suc B)]⟩
  | .b2 => ⟨[], [dif A (.suc A)]⟩
  | .b3 => ⟨[], [le .cero A]⟩
  | .b4a => ⟨[le A B, dif A B], [le (.suc A) B]⟩
  | .b4b => ⟨[le (.suc A) B], [le A B]⟩
  | .b4c => ⟨[le (.suc A) B], [dif A B]⟩
  | .b5 => ⟨[dif A .cero], [dif (doble A) .cero]⟩
  | .b6 => ⟨[], [le A B, le B A]⟩
  | .b7 => ⟨[le A B, le B A], [ig A B]⟩
  | .b8 => ⟨[le A B, le B C], [le A C]⟩
  | .b9 => ⟨[], [ig (.largo .cero) .cero]⟩
  | .b10 => ⟨[], [ig (.largo uno) uno]⟩
  | .b11a => ⟨[dif A .cero], [ig (.largo (doble A)) (.suc (.largo A))]⟩
  | .b11b => ⟨[dif A .cero], [ig (.largo (.suc (doble A))) (.suc (.largo A))]⟩
  | .b12 => ⟨[le A B], [le (.largo A) (.largo B)]⟩
  | .b13 => ⟨[], [ig (.largo (.smash A B)) (.suc (.prod (.largo A) (.largo B)))]⟩
  | .b14 => ⟨[], [ig (.smash .cero A) uno]⟩
  | .b15a => ⟨[dif A .cero], [ig (.smash uno (doble A)) (doble (.smash uno A))]⟩
  | .b15b => ⟨[dif A .cero], [ig (.smash uno (.suc (doble A))) (doble (.smash uno A))]⟩
  | .b16 => ⟨[], [ig (.smash A B) (.smash B A)]⟩
  | .b17 => ⟨[ig (.largo A) (.largo B)], [ig (.smash A C) (.smash B C)]⟩
  | .b18 => ⟨[ig (.largo A) (.suma (.largo B) (.largo C))], [ig (.smash A D) (.prod (.smash B D) (.smash C D))]⟩
  | .b19 => ⟨[], [le A (.suma A B)]⟩
  | .b20a => ⟨[le A B, dif A B], [le (.suc (doble A)) (doble B)]⟩
  | .b20b => ⟨[le A B, dif A B], [dif (.suc (doble A)) (doble B)]⟩
  | .b21 => ⟨[], [ig (.suma A B) (.suma B A)]⟩
  | .b22 => ⟨[], [ig (.suma A .cero) A]⟩
  | .b23 => ⟨[], [ig (.suma A (.suc B)) (.suc (.suma A B))]⟩
  | .b24 => ⟨[], [ig (.suma (.suma A B) C) (.suma A (.suma B C))]⟩
  | .b25a => ⟨[le (.suma A B) (.suma A C)], [le B C]⟩
  | .b25b => ⟨[le B C], [le (.suma A B) (.suma A C)]⟩
  | .b26 => ⟨[], [ig (.prod A .cero) .cero]⟩
  | .b27 => ⟨[], [ig (.prod A (.suc B)) (.suma (.prod A B) A)]⟩
  | .b28 => ⟨[], [ig (.prod A B) (.prod B A)]⟩
  | .b29 => ⟨[], [ig (.prod A (.suma B C)) (.suma (.prod A B) (.prod A C))]⟩
  | .b30a => ⟨[le uno A, le (.prod A B) (.prod A C)], [le B C]⟩
  | .b30b => ⟨[le uno A, le B C], [le (.prod A B) (.prod A C)]⟩
  | .b31 => ⟨[dif A .cero], [ig (.largo A) (.suc (.largo (.mitad A)))]⟩
  | .b32a => ⟨[ig A (.mitad B)], [ig (doble A) B, ig (.suc (doble A)) B]⟩
  | .b32b => ⟨[ig (doble A) B], [ig A (.mitad B)]⟩
  | .b32c => ⟨[ig (.suc (doble A)) B], [ig A (.mitad B)]⟩
  | .eRefl => ⟨[], [ig A A]⟩
  | .eLe => ⟨[ig A B, ig C D, le A C], [le B D]⟩
  | .eEq => ⟨[ig A B, ig C D, ig A C], [ig B D]⟩
  | .eSuc => ⟨[ig A B], [ig (.suc A) (.suc B)]⟩
  | .eSuma => ⟨[ig A B, ig C D], [ig (.suma A C) (.suma B D)]⟩
  | .eProd => ⟨[ig A B, ig C D], [ig (.prod A C) (.prod B D)]⟩
  | .eMitad => ⟨[ig A B], [ig (.mitad A) (.mitad B)]⟩
  | .eLargo => ⟨[ig A B], [ig (.largo A) (.largo B)]⟩
  | .eSmash => ⟨[ig A B, ig C D], [ig (.smash A C) (.smash B D)]⟩

/-- Abrir el valor de los átomos de un axioma. -/
local macro "abre" : tactic =>
  `(tactic| simp only [Lit.vale_le, Lit.vale_eq, Lit.vale_neq, Termino.val, Nat.zero_add, Nat.reduceAdd, ne_eq])

/-- **Los axiomas valen en los naturales.** -/
theorem Ax.valido : ∀ a : Ax, a.sec.Valido
  | .b1 => v1 fun ρ => by abre; omega
  | .b2 => v0 fun ρ => by abre; omega
  | .b3 => v0 fun ρ => by abre; omega
  | .b4a => v2 fun ρ => by abre; omega
  | .b4b => v1 fun ρ => by abre; omega
  | .b4c => v1 fun ρ => by abre; omega
  | .b5 => v1 fun ρ => by abre; omega
  | .b6 => v02 fun ρ => by abre; omega
  | .b7 => v2 fun ρ => by abre; omega
  | .b8 => v2 fun ρ => by abre; omega
  | .b9 => v0 fun ρ => by abre; rfl
  | .b10 => v0 fun ρ => by abre; rfl
  | .b11a => v1 fun ρ => by abre; exact size_doble _
  | .b11b => v1 fun ρ => by abre; exact fun _ => size_doble_mas _
  | .b12 => v1 fun ρ => by abre; exact Nat.size_le_size
  | .b13 => v0 fun ρ => by abre; exact Nat.size_pow
  | .b14 => v0 fun ρ => by abre; simp
  | .b15a => v1 fun ρ => by
      abre; intro h
      rw [Nat.size_one, Nat.one_mul, Nat.one_mul, size_doble _ h, Nat.pow_succ, Nat.mul_comm]
  | .b15b => v1 fun ρ => by
      abre; intro _
      rw [Nat.size_one, Nat.one_mul, Nat.one_mul, size_doble_mas, Nat.pow_succ, Nat.mul_comm]
  | .b16 => v0 fun ρ => by abre; rw [Nat.mul_comm]
  | .b17 => v1 fun ρ => by abre; intro h; rw [h]
  | .b18 => v1 fun ρ => by abre; intro h; rw [h, Nat.add_mul, Nat.pow_add]
  | .b19 => v0 fun ρ => by abre; omega
  | .b20a => v2 fun ρ => by abre; omega
  | .b20b => v2 fun ρ => by abre; omega
  | .b21 => v0 fun ρ => by abre; omega
  | .b22 => v0 fun ρ => by abre; omega
  | .b23 => v0 fun ρ => by abre; omega
  | .b24 => v0 fun ρ => by abre; omega
  | .b25a => v1 fun ρ => by abre; omega
  | .b25b => v1 fun ρ => by abre; omega
  | .b26 => v0 fun ρ => by abre; exact Nat.mul_zero _
  | .b27 => v0 fun ρ => by abre; exact Nat.mul_succ _ _
  | .b28 => v0 fun ρ => by abre; exact Nat.mul_comm _ _
  | .b29 => v0 fun ρ => by abre; exact Nat.mul_add _ _ _
  | .b30a => v2 fun ρ => by abre; exact fun h₁ h₂ => Nat.le_of_mul_le_mul_left h₂ h₁
  | .b30b => v2 fun ρ => by abre; exact fun _ h₂ => Nat.mul_le_mul_left _ h₂
  | .b31 => v1 fun ρ => by abre; exact size_mitad _
  | .b32a => v12 fun ρ => by abre; omega
  | .b32b => v1 fun ρ => by abre; omega
  | .b32c => v1 fun ρ => by abre; omega
  | .eRefl => v0 fun ρ => by abre
  | .eLe => v3 fun ρ => by abre; omega
  | .eEq => v3 fun ρ => by abre; omega
  | .eSuc => v1 fun ρ => by abre; omega
  | .eSuma => v2 fun ρ => by abre; omega
  | .eProd => v2 fun ρ => by abre; intro h₁ h₂; rw [h₁, h₂]
  | .eMitad => v1 fun ρ => by abre; intro h; rw [h]
  | .eLargo => v1 fun ρ => by abre; intro h; rw [h]
  | .eSmash => v2 fun ρ => by abre; intro h₁ h₂; rw [h₁, h₂]

end

/-! ## Los axiomas como derivaciones -/

/-- Un secuente válido sigue valiendo con sus variables sustituidas por términos. -/
theorem Sec.Valido.subst {s : Sec} (h : s.Valido) (σ : ℕ → Termino) :
    ∀ ρ : Entorno, (∀ q ∈ s.ant.map (Lit.subst σ), q.vale ρ = true) →
      ∃ q ∈ s.suc.map (Lit.subst σ), q.vale ρ = true := by
  intro ρ hq
  obtain ⟨p, hp, hv⟩ := h (Termino.entornoDe σ ρ) fun q hq' => by
    rw [← Lit.vale_subst]; exact hq _ (List.mem_map_of_mem hq')
  exact ⟨p.subst σ, List.mem_map_of_mem hp, by rw [Lit.vale_subst]; exact hv⟩

/-- **Un axioma como derivación**, con sus variables sustituidas por los términos de `σ`. -/
def Deriv.basico (a : Ax) (σ : ℕ → Termino) :
    Deriv ((a.sec.ant.map (Lit.subst σ)).map atomo) ((a.sec.suc.map (Lit.subst σ)).map atomo) :=
  .aritm _ _ (a.valido.subst σ)

/-- La contradicción entre un átomo y su contrario. -/
def Deriv.absurdo (l : Lit) : Deriv [atomo l, atomo l.neg] [] :=
  .aritm [l, l.neg] [] fun ρ h => by
    have h₁ := h l List.mem_cons_self
    have h₂ := h l.neg (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨r, t, u⟩ := l
    cases r <;> simp_all [Lit.vale, Lit.neg, Rel.vale, Rel.neg]

/-- **La derivación es de S¹₂**: sus únicos hechos son instancias de los axiomas y contradicciones entre un átomo y
su contrario. -/
def Deriv.EsDeS12 : {Γ Δ : List Formula} → Deriv Γ Δ → Prop
  | _, _, .id _ => True
  | _, _, .aritm ps qs _ =>
      (∃ (a : Ax) (σ : ℕ → Termino), ps = a.sec.ant.map (Lit.subst σ) ∧ qs = a.sec.suc.map (Lit.subst σ)) ∨
        (∃ l : Lit, ps = [l, l.neg] ∧ qs = [])
  | _, _, .debilIzq _ d => d.EsDeS12
  | _, _, .debilDer _ d => d.EsDeS12
  | _, _, .contrIzq d => d.EsDeS12
  | _, _, .contrDer d => d.EsDeS12
  | _, _, .cambIzq d => d.EsDeS12
  | _, _, .cambDer d => d.EsDeS12
  | _, _, .corte _ d₁ d₂ => d₁.EsDeS12 ∧ d₂.EsDeS12
  | _, _, .casos _ d₁ d₂ => d₁.EsDeS12 ∧ d₂.EsDeS12
  | _, _, .conjDer d₁ d₂ => d₁.EsDeS12 ∧ d₂.EsDeS12
  | _, _, .conjIzq d => d.EsDeS12
  | _, _, .disyDer d => d.EsDeS12
  | _, _, .disyIzq d₁ d₂ => d₁.EsDeS12 ∧ d₂.EsDeS12
  | _, _, .exDer _ _ _ d₀ d => d₀.EsDeS12 ∧ d.EsDeS12
  | _, _, .exIzq _ _ d => d.EsDeS12
  | _, _, .ptDer _ _ d => d.EsDeS12
  | _, _, .ptIzq _ _ _ d₀ d => d₀.EsDeS12 ∧ d.EsDeS12
  | _, _, .pind _ _ d => d.EsDeS12

theorem Deriv.basico_esDeS12 (a : Ax) (σ : ℕ → Termino) : (Deriv.basico a σ).EsDeS12 :=
  .inl ⟨a, σ, rfl, rfl⟩

theorem Deriv.absurdo_esDeS12 (l : Lit) : (Deriv.absurdo l).EsDeS12 := .inr ⟨l, rfl, rfl⟩

/-! ## El lema del testigo -/

/-- **El lema del testigo.** De una derivación de «existe `x ≤ t` con `φ`» sale un programa limitado que:

1. para todo entorno entrega un `x` bajo la cota y que cumple `φ`;
2. para toda entrada, válida o no, entrega algo de peso polinomial en el peso de la entrada.

Vale para toda derivación del cálculo, y en particular para las de S¹₂ (`Deriv.EsDeS12`), que son las derivaciones
de esa teoría en las que toda fórmula es Σᵇ₁. -/
theorem lema_del_testigo {t : Termino} {φ : Formula} (d : Deriv [] [ex t φ]) :
    ∃ p : Prog, p.Limitado ∧
      (∀ (n : ℕ) (ρ : Entorno), Chico n ρ →
        (p.correr n ρ []).2.valor ≤ t.val ρ ∧ Vale φ (ext (p.correr n ρ []).2.valor ρ)) ∧
      ∃ q : Polynomial ℕ, ∀ (n : ℕ) (ρ : Entorno) (a : List Arbol), Chico n ρ →
        (p.correr n ρ a).2.peso ≤ q.eval (n + pesoL a) := by
  refine ⟨d.borrar, d.borrar_limitado, fun n ρ hρ => ?_, programa_limitado d⟩
  have h := programa_atestigua d hρ
  generalize (d.borrar.correr n ρ []).2 = w at h ⊢
  cases w with
  | hoja => exact h.elim
  | cons _ _ => exact h.elim
  | nodo b w => exact ⟨h.1, (vale_iff_testigo φ _).mpr ⟨w, h.2⟩⟩

/-! ## Un ejemplo que sale solo de los axiomas

«Existe `y ≤ Sa` con `a ≤ y`», exhibiendo `y = Sa`. Usa el axioma 6 (`a ≤ b ∨ b ≤ a`, con `b = a`) para la
reflexividad, y el axioma 1 (`a ≤ b ⊃ a ≤ Sb`). -/

/-- `t ≤ t`, del axioma 6 con las dos variables iguales y una contracción. -/
def reflexiva (t : Termino) : Deriv [] [atomo ⟨.le, t, t⟩] :=
  .contrDer (.basico .b6 fun _ => t)

/-- `a ≤ Sa`, del axioma 1 y la reflexividad, por corte. -/
def menorQueSucesor : Deriv [] [atomo ⟨.le, .var 0, .suc (.var 0)⟩] :=
  .corte (atomo ⟨.le, .var 0, .var 0⟩)
    (.cambDer (.debilDer _ (reflexiva (.var 0))))
    (.basico .b1 fun _ => .var 0)

def ejemploS12 : Deriv [] [ex (.suc (.var 0)) (atomo ⟨.le, .var 1, .var 0⟩)] :=
  .exDer _ (.suc (.var 0)) _ (reflexiva _) menorQueSucesor

theorem ejemploS12_esDeS12 : ejemploS12.EsDeS12 :=
  ⟨Deriv.basico_esDeS12 _ _, Deriv.basico_esDeS12 _ _, Deriv.basico_esDeS12 _ _⟩

/-- El programa extraído entrega el sucesor. -/
example : ejemploS12.borrar.correr 3 (fun _ => 5) [] = (0, .nodo 6 .hoja) := by decide

end Extraccion
end Sagitta.Map
