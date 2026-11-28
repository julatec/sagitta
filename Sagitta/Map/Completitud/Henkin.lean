import Sagitta.Map.Completitud.Derivadas
import Mathlib.ModelTheory.Encoding

/-!
# Completitud, fase F2: Lindenbaum con testigos de Henkin

Segunda fase del teorema de completitud. Un conjunto
de fórmulas es **consistente** si ninguna lista finita de sus fórmulas deriva el secuente vacío. Aquí se extiende un
conjunto consistente a uno **maximal** (de cada fórmula, ella o su negación) y **de Henkin** (todo `¬∀ψ` tiene un
testigo `¬ψ(c)`).

**La idea que lo abarata.** Los testigos son **variables libres**, no constantes nuevas. El punto de partida usa
finitas variables libres (`Acotado S N`: todas `< N`), y cada paso agrega finitas fórmulas, así que siempre hay una
variable fresca. No hace falta extender el lenguaje ni renombrar derivaciones.

## Lo que se prueba

* `consis_insert`: si `S` es consistente, `S ∪ {φ}` o `S ∪ {¬φ}` lo es.
* `consis_testigo`: si `S` es consistente, contiene `¬∀ψ` y `c` no aparece libre en `S`, agregar `¬ψ(c)` lo deja
  consistente. Es la regla `∀` a la derecha, con `c` como variable propia.
* `lindenbaum`: todo `S` consistente con variables libres acotadas está contenido en un `T` consistente, completo
  (`φ ∈ T ∨ ¬φ ∈ T`) y de Henkin.
* Propiedades del maximal (`Maximal`): cerrado por derivación, `→` como implicación, `⊥` afuera, `∀ψ` adentro si y solo
  si todas sus instancias lo están.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-! ## Las fórmulas se pueden enumerar -/

/-- Un código para cada símbolo de función. -/
def codFun : (Σ n, Fun n) → ℕ
  | ⟨_, .cero⟩ => 0
  | ⟨_, .suc⟩ => 1
  | ⟨_, .long⟩ => 2
  | ⟨_, .mitad⟩ => 3
  | ⟨_, .suma⟩ => 4
  | ⟨_, .prod⟩ => 5
  | ⟨_, .smash⟩ => 6

theorem codFun_inj : Function.Injective codFun := by
  rintro ⟨_, a⟩ ⟨_, b⟩ h
  cases a <;> cases b <;> simp_all [codFun]

instance : Countable (Σ n, Fun n) := codFun_inj.countable

instance : Countable (Σ n, Rel n) :=
  (show Function.Injective fun (_ : Σ n, Rel n) => (0 : ℕ) from
    fun ⟨_, a⟩ ⟨_, b⟩ _ => by cases a; cases b; rfl).countable

instance : Countable L.Symbols := by
  unfold Language.Symbols; infer_instance

instance : Countable (L.Formula ℕ) := inferInstance

/-! ## Consistencia -/

/-- **`S` refuta**: una lista de fórmulas de `S` deriva el secuente vacío. -/
def Refuta (S : Set (L.Formula ℕ)) : Prop := ∃ Γ : List (L.Formula ℕ), (∀ φ ∈ Γ, φ ∈ S) ∧ Der Γ []

/-- **`S` es consistente**. -/
def Consis (S : Set (L.Formula ℕ)) : Prop := ¬ Refuta S

/-- **Las variables libres de `S` son todas menores que `N`.** -/
def Acotado (S : Set (L.Formula ℕ)) (N : ℕ) : Prop := ∀ φ ∈ S, ∀ a ∈ φ.freeVarFinset, a < N

/-- Una cota para las variables libres de una fórmula. -/
def cota (φ : L.Formula ℕ) : ℕ := φ.freeVarFinset.sup id + 1

theorem lt_cota {φ : L.Formula ℕ} {a : ℕ} (h : a ∈ φ.freeVarFinset) : a < cota φ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) h)

theorem Acotado.mono {S : Set (L.Formula ℕ)} {N N' : ℕ} (h : Acotado S N) (hN : N ≤ N') : Acotado S N' :=
  fun φ hφ a ha => lt_of_lt_of_le (h φ hφ a ha) hN

theorem Acotado.insert {S : Set (L.Formula ℕ)} {N : ℕ} (h : Acotado S N) (φ : L.Formula ℕ) :
    Acotado (insert φ S) (max N (cota φ)) := by
  intro ψ hψ a ha
  rcases hψ with rfl | hψ
  · exact lt_of_lt_of_le (lt_cota ha) (le_max_right _ _)
  · exact lt_of_lt_of_le (h ψ hψ a ha) (le_max_left _ _)

open Classical in
/-- Sacar `φ` de una lista que está en `insert φ S`. -/
theorem quitar {S : Set (L.Formula ℕ)} {φ : L.Formula ℕ} {Γ : List (L.Formula ℕ)} (hΓ : ∀ χ ∈ Γ, χ ∈ insert φ S) :
    (∀ χ ∈ Γ.filter (fun χ => !decide (χ = φ)), χ ∈ S) ∧ Γ ⊆ φ :: Γ.filter (fun χ => !decide (χ = φ)) := by
  constructor
  · intro χ hχ
    rw [List.mem_filter] at hχ
    rcases hΓ χ hχ.1 with h | h
    · exact absurd h (by simpa using hχ.2)
    · exact h
  · intro χ hχ
    by_cases h : χ = φ
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hχ, by simp [h]⟩)

/-- Si `S ∪ {φ}` refuta, hay una lista de `S` que con `φ` adelante deriva el vacío. -/
theorem refuta_insert {S : Set (L.Formula ℕ)} {φ : L.Formula ℕ} (h : Refuta (insert φ S)) :
    ∃ Γ : List (L.Formula ℕ), (∀ χ ∈ Γ, χ ∈ S) ∧ Der (φ :: Γ) [] := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  obtain ⟨h1, h2⟩ := quitar hΓ
  exact ⟨_, h1, hd.debil h2 (List.Subset.refl _)⟩

/-- **De `φ` o de `¬φ`, uno se puede agregar.** -/
theorem consis_insert {S : Set (L.Formula ℕ)} (hS : Consis S) (φ : L.Formula ℕ) :
    Consis (insert φ S) ∨ Consis (insert φ.not S) := by
  by_contra h
  push Not at h
  obtain ⟨Γ₁, h₁, d₁⟩ := refuta_insert (not_not.1 h.1)
  obtain ⟨Γ₂, h₂, d₂⟩ := refuta_insert (not_not.1 h.2)
  apply hS
  refine ⟨Γ₁ ++ Γ₂, fun χ hχ => ?_, ?_⟩
  · rcases List.mem_append.1 hχ with hχ | hχ
    exacts [h₁ χ hχ, h₂ χ hχ]
  · exact Der.corte φ.not ((Der.negDer d₁).debil (List.subset_append_left _ _) (List.Subset.refl _))
      (d₂.debil (List.cons_subset_cons _ (List.subset_append_right _ _)) (List.Subset.refl _))

/-- **El paso de Henkin**: un testigo fresco para `¬∀ψ` no rompe la consistencia. -/
theorem consis_testigo {S : Set (L.Formula ℕ)} (hS : Consis S) {ψ : L.BoundedFormula ℕ 1}
    (hψ : (BoundedFormula.all ψ).not ∈ S) {c : ℕ} (hc : ∀ φ ∈ S, c ∉ φ.freeVarFinset) :
    Consis (insert (instanciar ψ (Term.var c)).not S) := by
  intro h
  obtain ⟨Γ, hΓ, hd⟩ := refuta_insert h
  -- `Γ ⇒ ψ(c)`, y como `c` no está en `Γ` ni en `ψ`, `Γ ⇒ ∀ψ`.
  have h1 : Der Γ [instanciar ψ (Term.var c)] := Der.deNegIzq hd
  have hcψ : c ∉ ψ.freeVarFinset := by
    have := hc _ hψ
    simpa [BoundedFormula.not, BoundedFormula.freeVarFinset] using this
  have h2 : Der Γ [BoundedFormula.all ψ] :=
    h1.elim fun d => ⟨.todoDer ψ c hcψ (fun φ hφ => hc φ (hΓ φ hφ)) (fun _ h => absurd h List.not_mem_nil) d⟩
  apply hS
  refine ⟨(BoundedFormula.all ψ).not :: Γ, fun χ hχ => ?_, Der.negIzq h2⟩
  rcases List.mem_cons.1 hχ with rfl | hχ
  exacts [hψ, hΓ χ hχ]

/-! ## Lindenbaum -/

/-- Si `φ` es `¬∀ψ`, el `ψ`. -/
def esNoTodo : L.Formula ℕ → Option (L.BoundedFormula ℕ 1)
  | .imp (.all ψ) .falsum => some ψ
  | _ => none

theorem esNoTodo_spec {φ : L.Formula ℕ} {ψ : L.BoundedFormula ℕ 1} (h : esNoTodo φ = some ψ) :
    φ = (BoundedFormula.all ψ).not := by
  unfold esNoTodo at h
  split at h
  · cases h; rfl
  · cases h

theorem esNoTodo_not (ψ : L.BoundedFormula ℕ 1) : esNoTodo (BoundedFormula.all ψ).not = some ψ := rfl

/-- Un estado de la construcción: el conjunto y una cota para sus variables libres. -/
structure Estado where
  S : Set (L.Formula ℕ)
  N : ℕ

/-- Agregar `χ` y, si es `¬∀ψ`, su testigo `¬ψ(N)` con `N` fresca. -/
def Estado.agregar (e : Estado) (χ : L.Formula ℕ) : Estado :=
  let N := max e.N (cota χ)
  match esNoTodo χ with
  | some ψ => ⟨insert (instanciar ψ (Term.var N)).not (insert χ e.S), max (N + 1) (cota (instanciar ψ (Term.var N)).not)⟩
  | none => ⟨insert χ e.S, N⟩

open Classical in
/-- Un paso: decidir `φ`, quedándose con la opción consistente. -/
noncomputable def Estado.paso (e : Estado) (φ : L.Formula ℕ) : Estado :=
  if Consis (insert φ e.S) then e.agregar φ else e.agregar φ.not

theorem Estado.sub_agregar (e : Estado) (χ : L.Formula ℕ) : e.S ⊆ (e.agregar χ).S ∧ χ ∈ (e.agregar χ).S := by
  unfold Estado.agregar
  split
  · exact ⟨fun _ h => Or.inr (Or.inr h), Or.inr (Or.inl rfl)⟩
  · exact ⟨fun _ h => Or.inr h, Or.inl rfl⟩

theorem Estado.acotado_agregar {e : Estado} (h : Acotado e.S e.N) (χ : L.Formula ℕ) :
    Acotado (e.agregar χ).S (e.agregar χ).N := by
  unfold Estado.agregar
  split
  · dsimp only
    exact ((h.insert χ).insert _).mono (by omega)
  · exact h.insert χ

/-- **Agregar mantiene la consistencia**, si agregar `χ` solo la mantenía. -/
theorem Estado.consis_agregar {e : Estado} (hb : Acotado e.S e.N) (χ : L.Formula ℕ) (h : Consis (insert χ e.S)) :
    Consis (e.agregar χ).S := by
  unfold Estado.agregar
  split
  · rename_i ψ hψ
    have hχ := esNoTodo_spec hψ
    refine consis_testigo h (hχ ▸ Or.inl rfl) fun φ hφ hc => ?_
    have := (hb.insert χ) φ hφ _ hc
    omega
  · exact h

theorem Estado.consis_paso {e : Estado} (hb : Acotado e.S e.N) (hc : Consis e.S) (φ : L.Formula ℕ) :
    Consis (e.paso φ).S := by
  unfold Estado.paso
  split
  · exact e.consis_agregar hb φ (by assumption)
  · rename_i h
    exact e.consis_agregar hb φ.not ((consis_insert hc φ).resolve_left h)

theorem Estado.acotado_paso {e : Estado} (hb : Acotado e.S e.N) (φ : L.Formula ℕ) :
    Acotado (e.paso φ).S (e.paso φ).N := by
  unfold Estado.paso; split <;> exact e.acotado_agregar hb _

theorem Estado.sub_paso (e : Estado) (φ : L.Formula ℕ) :
    e.S ⊆ (e.paso φ).S ∧ (φ ∈ (e.paso φ).S ∨ φ.not ∈ (e.paso φ).S) := by
  unfold Estado.paso
  split
  · exact ⟨(e.sub_agregar φ).1, Or.inl (e.sub_agregar φ).2⟩
  · exact ⟨(e.sub_agregar φ.not).1, Or.inr (e.sub_agregar φ.not).2⟩

/-- **Agregar `¬∀ψ` agrega un testigo.** -/
theorem Estado.testigo_agregar (e : Estado) (ψ : L.BoundedFormula ℕ 1) :
    ∃ c, (instanciar ψ (Term.var c)).not ∈ (e.agregar (BoundedFormula.all ψ).not).S := by
  refine ⟨max e.N (cota (BoundedFormula.all ψ).not), ?_⟩
  unfold Estado.agregar
  rw [esNoTodo_not]
  exact Or.inl rfl

/-! ## La cadena y su límite -/

/-- Una enumeración de las fórmulas. -/
noncomputable def enum : ℕ → L.Formula ℕ := Classical.choose (exists_surjective_nat (L.Formula ℕ))

theorem enum_sobre : Function.Surjective enum := Classical.choose_spec (exists_surjective_nat (L.Formula ℕ))

/-- **La cadena**: en el paso `n` se decide la `n`-ésima fórmula. -/
noncomputable def cadena (e₀ : Estado) : ℕ → Estado
  | 0 => e₀
  | n + 1 => (cadena e₀ n).paso (enum n)

/-- **El límite**: la unión de la cadena. -/
noncomputable def limite (e₀ : Estado) : Set (L.Formula ℕ) := ⋃ n, (cadena e₀ n).S

variable {e₀ : Estado}

theorem cadena_acotada (hb : Acotado e₀.S e₀.N) : ∀ n, Acotado (cadena e₀ n).S (cadena e₀ n).N
  | 0 => hb
  | n + 1 => Estado.acotado_paso (cadena_acotada hb n) _

theorem cadena_consis (hb : Acotado e₀.S e₀.N) (hc : Consis e₀.S) : ∀ n, Consis (cadena e₀ n).S
  | 0 => hc
  | n + 1 => Estado.consis_paso (cadena_acotada hb n) (cadena_consis hb hc n) _

theorem cadena_mono {m n : ℕ} (h : m ≤ n) : (cadena e₀ m).S ⊆ (cadena e₀ n).S := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (Estado.sub_paso _ _).1

theorem mem_limite {φ : L.Formula ℕ} {n : ℕ} (h : φ ∈ (cadena e₀ n).S) : φ ∈ limite e₀ :=
  Set.mem_iUnion.2 ⟨n, h⟩

theorem sub_limite : e₀.S ⊆ limite e₀ := fun _ h => mem_limite (n := 0) h

/-- Una lista dentro del límite está dentro de un paso. -/
theorem lista_en_paso : ∀ Γ : List (L.Formula ℕ), (∀ φ ∈ Γ, φ ∈ limite e₀) → ∃ n, ∀ φ ∈ Γ, φ ∈ (cadena e₀ n).S
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | φ :: Γ, h => by
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (h φ List.mem_cons_self)
    obtain ⟨n, hn⟩ := lista_en_paso Γ fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)
    refine ⟨max m n, fun ψ hψ => ?_⟩
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact cadena_mono (le_max_left _ _) hm
    · exact cadena_mono (le_max_right _ _) (hn ψ hψ)

theorem limite_consis (hb : Acotado e₀.S e₀.N) (hc : Consis e₀.S) : Consis (limite e₀) := by
  rintro ⟨Γ, hΓ, hd⟩
  obtain ⟨n, hn⟩ := lista_en_paso Γ hΓ
  exact cadena_consis hb hc n ⟨Γ, hn, hd⟩

theorem limite_completo (φ : L.Formula ℕ) : φ ∈ limite e₀ ∨ φ.not ∈ limite e₀ := by
  obtain ⟨m, rfl⟩ := enum_sobre φ
  rcases (Estado.sub_paso (cadena e₀ m) (enum m)).2 with h | h
  · exact Or.inl (mem_limite (n := m + 1) h)
  · exact Or.inr (mem_limite (n := m + 1) h)

/-- `φ` y `¬φ` juntos refutan. -/
theorem refuta_par {S : Set (L.Formula ℕ)} {φ : L.Formula ℕ} (h₁ : φ ∈ S) (h₂ : φ.not ∈ S) : Refuta S :=
  ⟨[φ.not, φ], by intro χ hχ; simp at hχ; rcases hχ with rfl | rfl <;> assumption,
    Der.negIzq (Der.ax φ)⟩

theorem limite_henkin (hb : Acotado e₀.S e₀.N) (hc : Consis e₀.S) {ψ : L.BoundedFormula ℕ 1}
    (h : (BoundedFormula.all ψ).not ∈ limite e₀) : ∃ c, (instanciar ψ (Term.var c)).not ∈ limite e₀ := by
  obtain ⟨m, hm⟩ := enum_sobre (BoundedFormula.all ψ).not
  have hpaso : (cadena e₀ (m + 1)) = (cadena e₀ m).paso (enum m) := rfl
  by_cases hC : Consis (insert (enum m) (cadena e₀ m).S)
  · have : (cadena e₀ m).paso (enum m) = (cadena e₀ m).agregar (enum m) := by
      unfold Estado.paso; simp only [hC, ↓reduceIte]
    obtain ⟨c, hc'⟩ := (cadena e₀ m).testigo_agregar ψ
    refine ⟨c, mem_limite (n := m + 1) ?_⟩
    rw [hpaso, this, hm]; exact hc'
  · exfalso
    have : (cadena e₀ m).paso (enum m) = (cadena e₀ m).agregar (enum m).not := by
      unfold Estado.paso; simp only [hC, ↓reduceIte]
    have hn : (enum m).not ∈ limite e₀ := mem_limite (n := m + 1) (by
      rw [hpaso, this]; exact ((cadena e₀ m).sub_agregar _).2)
    rw [hm] at hn
    exact limite_consis hb hc (refuta_par h hn)

/-! ## El maximal -/

/-- **Un conjunto maximal de Henkin**: consistente, completo y con testigos. -/
structure Maximal (T : Set (L.Formula ℕ)) : Prop where
  consis : Consis T
  completo : ∀ φ, φ ∈ T ∨ φ.not ∈ T
  henkin : ∀ ψ : L.BoundedFormula ℕ 1, (BoundedFormula.all ψ).not ∈ T → ∃ c, (instanciar ψ (Term.var c)).not ∈ T

/-- **Lindenbaum con testigos de Henkin**: todo conjunto consistente con variables libres acotadas está dentro de un
maximal. -/
theorem lindenbaum {S : Set (L.Formula ℕ)} {N : ℕ} (hb : Acotado S N) (hc : Consis S) :
    ∃ T, S ⊆ T ∧ Maximal T :=
  ⟨limite ⟨S, N⟩, sub_limite (e₀ := ⟨S, N⟩), ⟨limite_consis hb hc, limite_completo, fun _ h => limite_henkin hb hc h⟩⟩

namespace Maximal

variable {T : Set (L.Formula ℕ)} (hT : Maximal T)
include hT

theorem no_ambos {φ : L.Formula ℕ} (h₁ : φ ∈ T) (h₂ : φ.not ∈ T) : False := hT.consis (refuta_par h₁ h₂)

/-- **Cerrado por derivación.** -/
theorem cerrado {Γ : List (L.Formula ℕ)} {φ : L.Formula ℕ} (hΓ : ∀ χ ∈ Γ, χ ∈ T) (hd : Der Γ [φ]) : φ ∈ T := by
  rcases hT.completo φ with h | h
  · exact h
  · exfalso
    exact hT.consis ⟨φ.not :: Γ, by intro χ hχ; rcases List.mem_cons.1 hχ with rfl | hχ; exacts [h, hΓ χ hχ],
      Der.negIzq hd⟩

theorem not_mem_iff {φ : L.Formula ℕ} : φ.not ∈ T ↔ φ ∉ T :=
  ⟨fun h h' => hT.no_ambos h' h, fun h => (hT.completo φ).resolve_left h⟩

theorem falsum_no : (BoundedFormula.falsum : L.Formula ℕ) ∉ T := fun h =>
  hT.consis ⟨[BoundedFormula.falsum], by simpa using h, ⟨.falso⟩⟩

theorem imp_iff {φ ψ : L.Formula ℕ} : φ.imp ψ ∈ T ↔ (φ ∈ T → ψ ∈ T) := by
  constructor
  · intro h hφ
    refine hT.cerrado (Γ := [φ.imp ψ, φ]) (by intro χ hχ; simp at hχ; rcases hχ with rfl | rfl <;> assumption) ?_
    exact Der.impIzq (Der.axDe List.mem_cons_self (List.mem_cons_self))
      (Der.axDe List.mem_cons_self List.mem_cons_self)
  · intro h
    by_cases hφ : φ ∈ T
    · refine hT.cerrado (Γ := [ψ]) (by simpa using h hφ) (Der.impDer ?_)
      exact Der.axDe (by simp) List.mem_cons_self
    · refine hT.cerrado (Γ := [φ.not]) (by simpa using (hT.not_mem_iff).2 hφ) (Der.impDer ?_)
      exact (Der.negIzq (Der.ax φ)).debil (by intro χ hχ; simp at hχ ⊢; tauto) (List.nil_subset _)

theorem all_iff {ψ : L.BoundedFormula ℕ 1} : BoundedFormula.all ψ ∈ T ↔ ∀ t, instanciar ψ t ∈ T := by
  constructor
  · intro h t
    exact hT.cerrado (Γ := [BoundedFormula.all ψ]) (by simpa using h)
      ((Der.ax (instanciar ψ t)).elim fun d => ⟨.todoIzq ψ t d⟩)
  · intro h
    by_contra hn
    obtain ⟨c, hc⟩ := hT.henkin ψ ((hT.not_mem_iff).2 hn)
    exact hT.no_ambos (h (Term.var c)) hc

end Maximal

/-! ## Controles -/

/-- El paso de Henkin no es vacío: `esNoTodo` reconoce `¬∀ψ` y nada más. -/
example (ψ : L.BoundedFormula ℕ 1) : esNoTodo (BoundedFormula.all ψ).not = some ψ ∧
    esNoTodo (BoundedFormula.all ψ) = none := ⟨rfl, rfl⟩

end Acotada
end Sagitta.Map
