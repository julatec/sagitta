import Sagitta.Map.Secuentes

/-!
# Completitud, fase F1: reglas derivadas de `Deriva`

Primera fase del teorema de completitud para el cálculo de secuentes de S¹₂. Aquí no hay modelos: solo reglas que se derivan de las de
`Deriva`, escritas como proposiciones (`Der Γ Δ := Nonempty (Deriva Γ Δ)`), que es lo que piden las fases siguientes.

## Lo que se prueba

* **Estructurales**: debilitar desde sublistas a los dos lados (`Der.debil`), cortar (`Der.corte`).
* **La negación** (`¬φ` es `φ → ⊥` en Mathlib): a la derecha (`Der.negDer`) y a la izquierda (`Der.negIzq`), sus
  vueltas (`Der.deNegIzq`, `Der.deNegDer`) y el tercero excluido (`Der.tercero`).
* **La igualdad**: reflexiva, simétrica y transitiva (`Der.igualRefl`, `Der.igualSimm`, `Der.igualTrans`), y
  congruente: cambiar un argumento de una función (`Der.congrFun1`) o de una relación (`Der.congrRel1`) por uno igual.
  Para eso, cómo se sustituye en una igualdad y en una relación (`formula_subst_equal`, `formula_subst_rel`).
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

/-- **`Γ ⇒ Δ` es derivable**, como proposición. -/
def Der (Γ Δ : List (L.Formula ℕ)) : Prop := Nonempty (Deriva Γ Δ)

/-! ## Sustitución en fórmulas atómicas -/

theorem subst_relabel_inl {α β : Type} (a : L.Term α) (f : α → L.Term β) :
    (a.relabel (Sum.inl : α → α ⊕ Fin 0)).subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)) =
      (a.subst f).relabel Sum.inl := by
  induction a with
  | var x => simp [Term.relabel, Term.subst]
  | func g ts ih => simp [Term.relabel, Term.subst, ih]

theorem formula_subst_equal {α β : Type} (a b : L.Term α) (f : α → L.Term β) :
    (Term.equal a b).subst f = Term.equal (a.subst f) (b.subst f) :=
  congrArg₂ BoundedFormula.equal (subst_relabel_inl a f) (subst_relabel_inl b f)

theorem formula_subst_rel {α β : Type} {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term α) (f : α → L.Term β) :
    (R.formula ts).subst f = R.formula (fun i => (ts i).subst f) :=
  congrArg (BoundedFormula.rel R) (funext fun i => subst_relabel_inl (ts i) f)

theorem llenar_equal {k : ℕ} (a b : L.Term (Fin (k + 1))) (ps : Fin k → L.Term ℕ) (t : L.Term ℕ) :
    llenar (Term.equal a b) ps t =
      Term.equal (a.subst (Fin.cons (α := fun _ => L.Term ℕ) t ps)) (b.subst (Fin.cons (α := fun _ => L.Term ℕ) t ps)) :=
  formula_subst_equal _ _ _

theorem llenar_rel {k n : ℕ} (R : L.Relations n) (us : Fin n → L.Term (Fin (k + 1))) (ps : Fin k → L.Term ℕ)
    (t : L.Term ℕ) :
    llenar (R.formula us) ps t = R.formula (fun i => (us i).subst (Fin.cons (α := fun _ => L.Term ℕ) t ps)) :=
  formula_subst_rel _ _ _

/-- Una lista con `[a] ⊆ l`. -/
theorem sing {α : Type} {a : α} {l : List α} (h : a ∈ l) : [a] ⊆ l := by
  intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ h

namespace Der

variable {Γ Δ Γ' Δ' : List (L.Formula ℕ)} {φ ψ : L.Formula ℕ}

/-! ## Estructurales -/

theorem debil (h : Der Γ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : Der Γ' Δ' :=
  h.elim fun d => ⟨.debil d (Encaja.deSub hΓ) (Encaja.deSub hΔ)⟩

theorem corte (φ : L.Formula ℕ) (h₁ : Der Γ (φ :: Δ)) (h₂ : Der (φ :: Γ) Δ) : Der Γ Δ :=
  h₁.elim fun d₁ => h₂.elim fun d₂ => ⟨.corte φ d₁ d₂⟩

theorem ax (φ : L.Formula ℕ) : Der [φ] [φ] := ⟨.ax φ⟩

/-- `φ` en los dos lados. -/
theorem axDe (hΓ : φ ∈ Γ) (hΔ : φ ∈ Δ) : Der Γ Δ :=
  (ax φ).debil (sing hΓ) (sing hΔ)

theorem falsoIzq (hΓ : (BoundedFormula.falsum : L.Formula ℕ) ∈ Γ) : Der Γ Δ :=
  debil (show Der [BoundedFormula.falsum] [] from ⟨.falso⟩) (sing hΓ) (List.nil_subset _)

theorem impIzq (h₁ : Der Γ (φ :: Δ)) (h₂ : Der (ψ :: Γ) Δ) : Der (φ.imp ψ :: Γ) Δ :=
  h₁.elim fun d₁ => h₂.elim fun d₂ => ⟨.impIzq d₁ d₂⟩

theorem impDer (h : Der (φ :: Γ) (ψ :: Δ)) : Der Γ (φ.imp ψ :: Δ) :=
  h.elim fun d => ⟨.impDer d⟩

/-! ## La negación -/

/-- `¬φ` a la derecha: de `φ, Γ ⇒ Δ` sale `Γ ⇒ ¬φ, Δ`. -/
theorem negDer (h : Der (φ :: Γ) Δ) : Der Γ (φ.not :: Δ) :=
  impDer (h.debil (List.Subset.refl _) (List.subset_cons_self _ _))

/-- `¬φ` a la izquierda: de `Γ ⇒ φ, Δ` sale `¬φ, Γ ⇒ Δ`. -/
theorem negIzq (h : Der Γ (φ :: Δ)) : Der (φ.not :: Γ) Δ :=
  impIzq h (falsoIzq (List.mem_cons_self))

/-- Tercero excluido: `⇒ φ, ¬φ`. -/
theorem tercero (φ : L.Formula ℕ) : Der [] [φ, φ.not] :=
  (negDer (ax φ)).debil (List.Subset.refl _) (by intro x hx; simp at hx ⊢; tauto)

/-- La vuelta de `negIzq`: de `¬φ, Γ ⇒ Δ` sale `Γ ⇒ φ, Δ`. -/
theorem deNegIzq (h : Der (φ.not :: Γ) Δ) : Der Γ (φ :: Δ) :=
  corte φ.not ((tercero φ).debil (List.nil_subset _) (by intro x hx; simp at hx ⊢; tauto))
    (h.debil (List.Subset.refl _) (List.subset_cons_self _ _))

/-- La vuelta de `negDer`: de `Γ ⇒ ¬φ, Δ` sale `φ, Γ ⇒ Δ`. -/
theorem deNegDer (h : Der Γ (φ.not :: Δ)) : Der (φ :: Γ) Δ :=
  corte φ.not (h.debil (List.subset_cons_self _ _) (List.Subset.refl _))
    (negIzq (axDe List.mem_cons_self List.mem_cons_self) |>.debil
      (by intro x hx; simp at hx ⊢; tauto) (List.Subset.refl _))

/-! ## La igualdad -/

theorem igualRefl (t : L.Term ℕ) : Der Γ (Term.equal t t :: Δ) :=
  debil (show Der [] [Term.equal t t] from ⟨.igualRefl t⟩) (List.nil_subset _) (sing List.mem_cons_self)

/-- La regla de sustitución, con `A` atómica, desde un contexto cualquiera. -/
theorem sust {k : ℕ} (A : L.Formula (Fin (k + 1))) (hA : A.IsAtomic) (ps : Fin k → L.Term ℕ) {s t : L.Term ℕ}
    (hs : Term.equal s t ∈ Γ) (hA' : llenar A ps s ∈ Γ) (hΔ : llenar A ps t ∈ Δ) : Der Γ Δ :=
  debil (show Der _ _ from ⟨.igualSust A hA ps s t⟩)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption) (sing hΔ)

/-- Un término sobre `Fin (k+1)` que es la variable `0`. -/
abbrev x0 {k : ℕ} : L.Term (Fin (k + 1)) := Term.var 0


/-- **Simetría**: `s = t ⇒ t = s`. -/
theorem igualSimm (s t : L.Term ℕ) : Der [Term.equal s t] [Term.equal t s] := by
  -- `A(x) := x = p₀`, con `p₀ = s`: de `s = t` y `A(s)` sale `A(t)`.
  have := sust (Γ := [Term.equal s t, Term.equal s s]) (Δ := [Term.equal t s])
    (Term.equal x0 (Term.var 1)) (by exact BoundedFormula.IsAtomic.equal _ _) ![s]
    List.mem_cons_self (by simp [llenar_equal]) (by simp [llenar_equal])
  exact corte (Term.equal s s) (igualRefl s) (this.debil (by intro x hx; simp at hx ⊢; tauto) (List.Subset.refl _))

/-- **Transitividad**: `s = t, t = u ⇒ s = u`. -/
theorem igualTrans (s t u : L.Term ℕ) : Der [Term.equal s t, Term.equal t u] [Term.equal s u] := by
  -- `A(x) := p₀ = x`, con `p₀ = s`: de `t = u` y `A(t)` sale `A(u)`.
  exact sust (Γ := [Term.equal s t, Term.equal t u]) (Δ := [Term.equal s u])
    (Term.equal (Term.var 1) x0) (by exact BoundedFormula.IsAtomic.equal _ _) ![s] (s := t) (t := u)
    (by simp) (by simp [llenar_equal]) (by simp [llenar_equal])

/-! ## Congruencia, un argumento a la vez -/

/-- Los argumentos de un símbolo con el `i`-ésimo cambiado por la variable `0` y los demás por los parámetros. -/
def conHueco {n : ℕ} (i : Fin n) : Fin n → L.Term (Fin (n + 1)) :=
  fun j => if j = i then Term.var 0 else Term.var j.succ

theorem conHueco_subst {n : ℕ} (i : Fin n) (ts : Fin n → L.Term ℕ) (x : L.Term ℕ) :
    (fun j => (conHueco i j).subst (Fin.cons (α := fun _ => L.Term ℕ) x ts)) = Function.update ts i x := by
  funext j
  rw [Function.update_apply]
  unfold conHueco
  split <;> simp [Term.subst]

theorem subst_vars_succ {n : ℕ} (ts : Fin n → L.Term ℕ) (x : L.Term ℕ) :
    (fun j : Fin n => (Term.var j.succ : L.Term (Fin (n + 1))).subst (Fin.cons (α := fun _ => L.Term ℕ) x ts)) = ts := by
  funext j; simp [Term.subst]

/-- **Congruencia en una función**: `tᵢ = t ⇒ f(t⃗) = f(t⃗[i := t])`. -/
theorem congrFun1 {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term ℕ) (i : Fin n) (t : L.Term ℕ) :
    Der [Term.equal (ts i) t] [Term.equal (Term.func f ts) (Term.func f (Function.update ts i t))] := by
  -- `A(x) := f(t⃗[i := x]) = f(t⃗)`: `A(tᵢ)` es reflexiva y `A(t)` es la simétrica de lo que se busca.
  let A : L.Formula (Fin (n + 1)) := Term.equal (Term.func f (conHueco i)) (Term.func f fun j => Term.var j.succ)
  have hA : ∀ x, llenar A ts x = Term.equal (Term.func f (Function.update ts i x)) (Term.func f ts) := by
    intro x
    rw [llenar_equal]
    simp only [Term.subst]
    rw [conHueco_subst]
    simp only [Fin.cons_succ]
  have hupd : Function.update ts i (ts i) = ts := Function.update_eq_self i ts
  have h1 : Der [Term.equal (ts i) t, llenar A ts (ts i)] [llenar A ts t] :=
    sust A (BoundedFormula.IsAtomic.equal _ _) ts List.mem_cons_self (by simp) (by simp)
  rw [hA, hA, hupd] at h1
  have h2 := corte _ (igualRefl (Γ := [Term.equal (ts i) t]) (Δ := [Term.equal (Term.func f (Function.update ts i t))
    (Term.func f ts)]) (Term.func f ts)) (h1.debil (by intro x hx; simp at hx ⊢; tauto) (List.Subset.refl _))
  exact corte _ (h2.debil (List.Subset.refl _) (by intro x hx; simp at hx ⊢; tauto))
    ((igualSimm _ _).debil (by intro x hx; simp at hx ⊢; tauto) (List.Subset.refl _))

/-- **Congruencia en una relación**: `tᵢ = t, R(t⃗) ⇒ R(t⃗[i := t])`. -/
theorem congrRel1 {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term ℕ) (i : Fin n) (t : L.Term ℕ) :
    Der [Term.equal (ts i) t, R.formula ts] [R.formula (Function.update ts i t)] := by
  let A : L.Formula (Fin (n + 1)) := R.formula (conHueco i)
  have hA : ∀ x, llenar A ts x = R.formula (Function.update ts i x) := by
    intro x; rw [llenar_rel, conHueco_subst]
  have h1 : Der [Term.equal (ts i) t, llenar A ts (ts i)] [llenar A ts t] :=
    sust A (BoundedFormula.IsAtomic.rel _ _) ts List.mem_cons_self (by simp) (by simp)
  rwa [hA, hA, Function.update_eq_self] at h1

/-! ## Controles -/

/-- La regla de sustitución hace algo: de `s = t` sale `t = s` con términos distintos. -/
example : Der [Term.equal (tSc tC) tC] [Term.equal tC (tSc tC)] := igualSimm _ _

/-- Y el tercero excluido no es vacío: con `φ = ⊥`, `⇒ ⊥, ¬⊥`. -/
example : Der [] [BoundedFormula.falsum, (BoundedFormula.falsum : L.Formula ℕ).not] := tercero _

end Der

end Acotada
end Sagitta.Map
