import Sagitta.Map.Clases
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Componer dos máquinas de Turing (piloto de `CierrePolinomial`)

Si `f` y `g` se calculan en tiempo polinomial, `g ∘ f` también. Mathlib solo trae la identidad; aquí se construye
la máquina compuesta sobre el modelo de pilas `Turing.FinTM2` y se prueba que calcula `g ∘ f` en tiempo polinomial.

**La máquina.** Tiene las pilas de la primera, las de la segunda y una auxiliar. Corre la primera; donde ella se
detendría, salta a la transferencia: pasa su pila de salida a la auxiliar y de ahí a la pila de entrada de la
segunda (dos traspasos, porque cada uno invierte el orden); y corre la segunda.
-/

open Turing Turing.TM2 Turing.TM2.Stmt Function

namespace Sagitta.Map
namespace Componer

variable (M₁ M₂ : FinTM2)

instance : Fintype M₁.K := M₁.kFin
instance : Fintype M₁.Λ := M₁.ΛFin
instance : Fintype M₁.σ := M₁.σFin
instance : Fintype (M₁.Γ M₁.k₀) := M₁.Γk₀Fin

/-- El alfabeto por el que se pasan los datos: el de entrada de la segunda máquina. -/
abbrev Medio : Type := M₂.Γ M₂.k₀

/-- Las pilas: las de `M₁`, las de `M₂` y una auxiliar. -/
abbrev KK : Type := M₁.K ⊕ (M₂.K ⊕ Unit)

/-- El alfabeto de cada pila. -/
@[reducible] def ΓΓ : KK M₁ M₂ → Type
  | Sum.inl k => M₁.Γ k
  | Sum.inr (Sum.inl k) => M₂.Γ k
  | Sum.inr (Sum.inr _) => Medio M₂

/-- Las etiquetas: las de `M₁`, las de `M₂` y las dos de la transferencia. -/
abbrev ΛΛ : Type := M₁.Λ ⊕ (M₂.Λ ⊕ Bool)

/-- El estado: el de `M₁`, el de `M₂` y el símbolo que se está pasando. -/
abbrev σσ : Type := M₁.σ × M₂.σ × Option (Medio M₂)

variable {M₁ M₂}

/-- Primera transferencia: de la pila de salida de `M₁` a la auxiliar. -/
abbrev T1 : ΛΛ M₁ M₂ := Sum.inr (Sum.inr false)
/-- Segunda transferencia: de la auxiliar a la pila de entrada de `M₂`. -/
abbrev T2 : ΛΛ M₁ M₂ := Sum.inr (Sum.inr true)
/-- La pila auxiliar. -/
abbrev aux : KK M₁ M₂ := Sum.inr (Sum.inr ())

/-- Las pilas de la máquina compuesta, a partir de las de cada parte. -/
@[reducible] def comb (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (A : List (Medio M₂)) :
    ∀ k : KK M₁ M₂, List (ΓΓ M₁ M₂ k)
  | Sum.inl k => S₁ k
  | Sum.inr (Sum.inl k) => S₂ k
  | Sum.inr (Sum.inr _) => A

theorem comb_update_izq (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (A : List (Medio M₂))
    (k : M₁.K) (x : List (M₁.Γ k)) :
    update (comb S₁ S₂ A) (Sum.inl k) x = comb (update S₁ k x) S₂ A := by
  funext j
  rcases j with j | j | j
  · by_cases h : j = k
    · subst h
      exact (update_self (β := fun k => List (ΓΓ M₁ M₂ k)) _ _ _).trans
        (update_self (β := fun k => List (M₁.Γ k)) j x S₁).symm
    · exact (update_of_ne (β := fun k => List (ΓΓ M₁ M₂ k)) (Sum.inl_injective.ne h) _ _).trans
        (update_of_ne h _ _).symm
  · exact update_of_ne (β := fun k => List (ΓΓ M₁ M₂ k)) (by simp) _ _
  · exact update_of_ne (β := fun k => List (ΓΓ M₁ M₂ k)) (by simp) _ _

theorem comb_update_der (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (A : List (Medio M₂))
    (k : M₂.K) (x : List (M₂.Γ k)) :
    update (comb S₁ S₂ A) (Sum.inr (Sum.inl k)) x = comb S₁ (update S₂ k x) A := by
  funext j
  rcases j with j | j | j
  · exact update_of_ne (β := fun k => List (ΓΓ M₁ M₂ k)) (by simp) _ _
  · by_cases h : j = k
    · subst h
      exact (update_self (β := fun k => List (ΓΓ M₁ M₂ k)) _ _ _).trans
        (update_self (β := fun k => List (M₂.Γ k)) j x S₂).symm
    · exact (update_of_ne (β := fun k => List (ΓΓ M₁ M₂ k))
        (fun e => h (Sum.inl_injective (Sum.inr_injective e))) _ _).trans (update_of_ne h _ _).symm
  · exact update_of_ne (β := fun k => List (ΓΓ M₁ M₂ k)) (by simp) _ _

theorem comb_update_aux (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (A B : List (Medio M₂)) :
    update (comb S₁ S₂ A) aux B = comb S₁ S₂ B := by
  funext j
  rcases j with j | j | j
  · exact update_of_ne (β := fun k => List (ΓΓ M₁ M₂ k)) (by simp) _ _
  · exact update_of_ne (β := fun k => List (ΓΓ M₁ M₂ k)) (by simp) _ _
  · exact update_self (β := fun k => List (ΓΓ M₁ M₂ k)) _ _ _

/-- Una instrucción de `M₁`, en la máquina compuesta. Donde `M₁` se detiene, salta a la transferencia. -/
def tr₁ : TM2.Stmt M₁.Γ M₁.Λ M₁.σ → TM2.Stmt (ΓΓ M₁ M₂) (ΛΛ M₁ M₂) (σσ M₁ M₂)
  | push k f q => push (Sum.inl k) (fun v => f v.1) (tr₁ q)
  | peek k f q => peek (Sum.inl k) (fun v o => (f v.1 o, v.2)) (tr₁ q)
  | pop k f q => pop (Sum.inl k) (fun v o => (f v.1 o, v.2)) (tr₁ q)
  | load a q => load (fun v => (a v.1, v.2)) (tr₁ q)
  | branch f q₁ q₂ => branch (fun v => f v.1) (tr₁ q₁) (tr₁ q₂)
  | goto f => goto (fun v => Sum.inl (f v.1))
  | halt => goto (fun _ => T1)

/-- Una instrucción de `M₂`, en la máquina compuesta. -/
def tr₂ : TM2.Stmt M₂.Γ M₂.Λ M₂.σ → TM2.Stmt (ΓΓ M₁ M₂) (ΛΛ M₁ M₂) (σσ M₁ M₂)
  | push k f q => push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (tr₂ q)
  | peek k f q => peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (tr₂ q)
  | pop k f q => pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (tr₂ q)
  | load a q => load (fun v => (v.1, a v.2.1, v.2.2)) (tr₂ q)
  | branch f q₁ q₂ => branch (fun v => f v.2.1) (tr₂ q₁) (tr₂ q₂)
  | goto f => goto (fun v => Sum.inr (Sum.inl (f v.2.1)))
  | halt => halt

/-- Una configuración de `M₁`, vista en la máquina compuesta. Si `M₁` se detuvo, la compuesta está por transferir. -/
def emb₁ (w : M₂.σ × Option (Medio M₂)) (S₂ : ∀ k, List (M₂.Γ k)) (A : List (Medio M₂))
    (c : TM2.Cfg M₁.Γ M₁.Λ M₁.σ) : TM2.Cfg (ΓΓ M₁ M₂) (ΛΛ M₁ M₂) (σσ M₁ M₂) :=
  ⟨some (match c.l with | some l => Sum.inl l | none => T1), (c.var, w), comb c.stk S₂ A⟩

/-- Una configuración de `M₂`, vista en la máquina compuesta. -/
def emb₂ (v₁ : M₁.σ) (o : Option (Medio M₂)) (S₁ : ∀ k, List (M₁.Γ k)) (A : List (Medio M₂))
    (c : TM2.Cfg M₂.Γ M₂.Λ M₂.σ) : TM2.Cfg (ΓΓ M₁ M₂) (ΛΛ M₁ M₂) (σσ M₁ M₂) :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (v₁, c.var, o), comb S₁ c.stk A⟩

theorem tr₁_stepAux (w : M₂.σ × Option (Medio M₂)) (S₂ : ∀ k, List (M₂.Γ k)) (A : List (Medio M₂)) :
    ∀ (q : TM2.Stmt M₁.Γ M₁.Λ M₁.σ) (v : M₁.σ) (S₁ : ∀ k, List (M₁.Γ k)),
      stepAux (tr₁ (M₂ := M₂) q) (v, w) (comb S₁ S₂ A) = emb₁ w S₂ A (stepAux q v S₁) := by
  intro q
  induction q with
  | push k f q ih =>
    intro v S₁
    simp only [tr₁, stepAux]
    exact (congrArg (stepAux (tr₁ (M₂ := M₂) q) (v, w)) (comb_update_izq S₁ S₂ A k (f v :: S₁ k))).trans (ih v _)
  | peek k f q ih => intro v S₁; simp only [tr₁, stepAux]; exact ih _ _
  | pop k f q ih =>
    intro v S₁
    simp only [tr₁, stepAux]
    exact (congrArg (stepAux (tr₁ (M₂ := M₂) q) (f v (S₁ k).head?, w))
      (comb_update_izq S₁ S₂ A k (S₁ k).tail)).trans (ih _ _)
  | load a q ih => intro v S₁; simp only [tr₁, stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S₁
    simp only [tr₁, stepAux]
    cases f v
    · exact ih₂ v S₁
    · exact ih₁ v S₁
  | goto f => intro v S₁; rfl
  | halt => intro v S₁; rfl

theorem tr₂_stepAux (v₁ : M₁.σ) (o : Option (Medio M₂)) (S₁ : ∀ k, List (M₁.Γ k)) (A : List (Medio M₂)) :
    ∀ (q : TM2.Stmt M₂.Γ M₂.Λ M₂.σ) (v : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k)),
      stepAux (tr₂ (M₁ := M₁) q) (v₁, v, o) (comb S₁ S₂ A) = emb₂ v₁ o S₁ A (stepAux q v S₂) := by
  intro q
  induction q with
  | push k f q ih =>
    intro v S₂
    simp only [tr₂, stepAux]
    exact (congrArg (stepAux (tr₂ (M₁ := M₁) q) (v₁, v, o))
      (comb_update_der S₁ S₂ A k (f v :: S₂ k))).trans (ih v _)
  | peek k f q ih => intro v S₂; simp only [tr₂, stepAux]; exact ih _ _
  | pop k f q ih =>
    intro v S₂
    simp only [tr₂, stepAux]
    exact (congrArg (stepAux (tr₂ (M₁ := M₁) q) (v₁, f v (S₂ k).head?, o))
      (comb_update_der S₁ S₂ A k (S₂ k).tail)).trans (ih _ _)
  | load a q ih => intro v S₂; simp only [tr₂, stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S₂
    simp only [tr₂, stepAux]
    cases f v
    · exact ih₂ v S₂
    · exact ih₁ v S₂
  | goto f => intro v S₂; rfl
  | halt => intro v S₂; rfl

/-! ## La máquina compuesta -/

variable (M₁ M₂) in
/-- **La máquina compuesta.** `e` convierte un símbolo de salida de `M₁` en uno de entrada de `M₂`; `x₀` es un
símbolo cualquiera, que nunca se llega a escribir. -/
@[reducible] def compuesta (e : M₁.Γ M₁.k₁ → Medio M₂) (x₀ : Medio M₂) : FinTM2 where
  K := KK M₁ M₂
  k₀ := Sum.inl M₁.k₀
  k₁ := Sum.inr (Sum.inl M₂.k₁)
  Γ := ΓΓ M₁ M₂
  Λ := ΛΛ M₁ M₂
  main := Sum.inl M₁.main
  σ := σσ M₁ M₂
  initialState := (M₁.initialState, M₂.initialState, none)
  Γk₀Fin := M₁.Γk₀Fin
  m := fun
    | Sum.inl l => tr₁ (M₁.m l)
    | Sum.inr (Sum.inl l) => tr₂ (M₂.m l)
    | Sum.inr (Sum.inr false) =>
        pop (Sum.inl M₁.k₁) (fun v o => (v.1, v.2.1, o.map e))
          (branch (fun v => v.2.2.isSome)
            (push aux (fun v => v.2.2.getD x₀) (goto fun _ => T1))
            (goto fun _ => T2))
    | Sum.inr (Sum.inr true) =>
        pop aux (fun v o => (v.1, v.2.1, o))
          (branch (fun v => v.2.2.isSome)
            (push (Sum.inr (Sum.inl M₂.k₀)) (fun v => v.2.2.getD x₀) (goto fun _ => T2))
            (goto fun _ => Sum.inr (Sum.inl M₂.main)))

/-! ## Llegar en `n` pasos -/

/-- `f` lleva de `a` a `b` en exactamente `n` pasos. -/
def Llega {τ : Type} (f : τ → Option τ) (n : ℕ) (a b : τ) : Prop :=
  (flip bind f)^[n] (some a) = some b

theorem Llega.uno {τ : Type} {f : τ → Option τ} {a b : τ} (h : f a = some b) : Llega f 1 a b := h

theorem Llega.trans {τ : Type} {f : τ → Option τ} {n m : ℕ} {a b c : τ}
    (h₁ : Llega f n a b) (h₂ : Llega f m b c) : Llega f (m + n) a c := by
  unfold Llega at *
  rw [iterate_add_apply, h₁, h₂]

theorem iterate_none {τ : Type} (f : τ → Option τ) (n : ℕ) : (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply]; exact ih

/-- Si cada paso de `f` se corresponde con un paso de `f'` a través de `g`, también `n` pasos. -/
theorem Llega.sim {τ τ' : Type} {f : τ → Option τ} {f' : τ' → Option τ'} (g : τ → τ')
    (hpaso : ∀ a b, f a = some b → f' (g a) = some (g b)) :
    ∀ (n : ℕ) (a b : τ), Llega f n a b → Llega f' n (g a) (g b) := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have : a = b := Option.some.inj h
    subst this
    rfl
  | succ n ih =>
    intro a b h
    unfold Llega at h ⊢
    rw [iterate_succ_apply] at h ⊢
    change (flip bind f)^[n] (f a) = some b at h
    change (flip bind f')^[n] (f' (g a)) = some (g b)
    cases hfa : f a with
    | none => rw [hfa, iterate_none] at h; exact absurd h (by simp)
    | some a' =>
      rw [hfa] at h
      rw [hpaso a a' hfa]
      exact ih a' b h


/-! ## Las fases -/

section Fases

variable (e : M₁.Γ M₁.k₁ → Medio M₂) (x₀ : Medio M₂)

/-- Fase 1: un paso de `M₁` es un paso de la compuesta. -/
theorem paso₁ (w : M₂.σ × Option (Medio M₂)) (S₂ : ∀ k, List (M₂.Γ k)) (A : List (Medio M₂))
    (c c' : TM2.Cfg M₁.Γ M₁.Λ M₁.σ) (h : TM2.step M₁.m c = some c') :
    TM2.step (compuesta M₁ M₂ e x₀).m (emb₁ w S₂ A c) = some (emb₁ w S₂ A c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (tr₁_stepAux w S₂ A (M₁.m l) v S)

/-- Fase 3: un paso de `M₂` es un paso de la compuesta. -/
theorem paso₂ (v₁ : M₁.σ) (o : Option (Medio M₂)) (S₁ : ∀ k, List (M₁.Γ k)) (A : List (Medio M₂))
    (c c' : TM2.Cfg M₂.Γ M₂.Λ M₂.σ) (h : TM2.step M₂.m c = some c') :
    TM2.step (compuesta M₁ M₂ e x₀).m (emb₂ v₁ o S₁ A c) = some (emb₂ v₁ o S₁ A c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (tr₂_stepAux v₁ o S₁ A (M₂.m l) v S)

/-- La configuración de la máquina compuesta, con sus tipos a la vista. -/
abbrev CC (M₁ M₂ : FinTM2) : Type := TM2.Cfg (ΓΓ M₁ M₂) (ΛΛ M₁ M₂) (σσ M₁ M₂)

/-- Lo que hace un paso del primer traspaso. -/
theorem t1_stepAux (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (Medio M₂)) (S₁ : ∀ k, List (M₁.Γ k))
    (S₂ : ∀ k, List (M₂.Γ k)) (A : List (Medio M₂)) :
    stepAux ((compuesta M₁ M₂ e x₀).m T1) (v₁, v₂, o) (comb S₁ S₂ A) =
      bif (Option.map e (S₁ M₁.k₁).head?).isSome then
        (⟨some T1, (v₁, v₂, Option.map e (S₁ M₁.k₁).head?),
          comb (update S₁ M₁.k₁ (S₁ M₁.k₁).tail) S₂
            ((Option.map e (S₁ M₁.k₁).head?).getD x₀ :: A)⟩ : CC M₁ M₂)
      else
        ⟨some T2, (v₁, v₂, Option.map e (S₁ M₁.k₁).head?),
          comb (update S₁ M₁.k₁ (S₁ M₁.k₁).tail) S₂ A⟩ := by
  have h : stepAux ((compuesta M₁ M₂ e x₀).m T1) (v₁, v₂, o) (comb S₁ S₂ A) =
      bif (Option.map e (S₁ M₁.k₁).head?).isSome then
        (⟨some T1, (v₁, v₂, Option.map e (S₁ M₁.k₁).head?),
          update (update (comb S₁ S₂ A) (Sum.inl M₁.k₁) (S₁ M₁.k₁).tail) aux
            ((Option.map e (S₁ M₁.k₁).head?).getD x₀ :: A)⟩ : CC M₁ M₂)
      else
        ⟨some T2, (v₁, v₂, Option.map e (S₁ M₁.k₁).head?),
          update (comb S₁ S₂ A) (Sum.inl M₁.k₁) (S₁ M₁.k₁).tail⟩ := rfl
  rw [h, comb_update_izq, comb_update_aux]

/-- Lo que hace un paso del segundo traspaso. -/
theorem t2_stepAux (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (Medio M₂)) (S₁ : ∀ k, List (M₁.Γ k))
    (S₂ : ∀ k, List (M₂.Γ k)) (A : List (Medio M₂)) :
    stepAux ((compuesta M₁ M₂ e x₀).m T2) (v₁, v₂, o) (comb S₁ S₂ A) =
      bif (A.head?).isSome then
        (⟨some T2, (v₁, v₂, A.head?),
          comb S₁ (update S₂ M₂.k₀ ((A.head?).getD x₀ :: S₂ M₂.k₀)) A.tail⟩ : CC M₁ M₂)
      else
        ⟨some (Sum.inr (Sum.inl M₂.main)), (v₁, v₂, A.head?), comb S₁ S₂ A.tail⟩ := by
  have h : stepAux ((compuesta M₁ M₂ e x₀).m T2) (v₁, v₂, o) (comb S₁ S₂ A) =
      bif (A.head?).isSome then
        (⟨some T2, (v₁, v₂, A.head?),
          update (update (comb S₁ S₂ A) aux A.tail) (Sum.inr (Sum.inl M₂.k₀))
            ((A.head?).getD x₀ :: S₂ M₂.k₀)⟩ : CC M₁ M₂)
      else
        ⟨some (Sum.inr (Sum.inl M₂.main)), (v₁, v₂, A.head?), update (comb S₁ S₂ A) aux A.tail⟩ := rfl
  rw [h, comb_update_aux, comb_update_der]

/-- **Primer traspaso.** En `|s| + 1` pasos, la pila de salida de `M₁` pasa, invertida, a la auxiliar. -/
theorem traspaso₁ (v₁ : M₁.σ) (v₂ : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k)) :
    ∀ (s : List (M₁.Γ M₁.k₁)) (S₁ : ∀ k, List (M₁.Γ k)) (o : Option (Medio M₂)) (A : List (Medio M₂)),
      S₁ M₁.k₁ = s →
      Llega (TM2.step (compuesta M₁ M₂ e x₀).m) (s.length + 1)
        (⟨some T1, (v₁, v₂, o), comb S₁ S₂ A⟩ : CC M₁ M₂)
        ⟨some T2, (v₁, v₂, none), comb (update S₁ M₁.k₁ []) S₂ ((s.map e).reverse ++ A)⟩ := by
  intro s
  induction s with
  | nil =>
    intro S₁ o A hs
    apply Llega.uno
    show some (stepAux ((compuesta M₁ M₂ e x₀).m T1) (v₁, v₂, o) (comb S₁ S₂ A)) = _
    rw [t1_stepAux, hs]
    rfl
  | cons x s ih =>
    intro S₁ o A hs
    have h1 : Llega (TM2.step (compuesta M₁ M₂ e x₀).m) 1
        (⟨some T1, (v₁, v₂, o), comb S₁ S₂ A⟩ : CC M₁ M₂)
        ⟨some T1, (v₁, v₂, some (e x)), comb (update S₁ M₁.k₁ s) S₂ (e x :: A)⟩ := by
      apply Llega.uno
      show some (stepAux ((compuesta M₁ M₂ e x₀).m T1) (v₁, v₂, o) (comb S₁ S₂ A)) = _
      rw [t1_stepAux, hs]
      rfl
    have h2 := ih (update S₁ M₁.k₁ s) (some (e x)) (e x :: A) (update_self _ _ _)
    rw [update_idem] at h2
    have := h1.trans h2
    simpa [List.reverse_cons, List.append_assoc] using this

/-- **Segundo traspaso.** En `|A| + 1` pasos, la auxiliar pasa, invertida, a la pila de entrada de `M₂`. -/
theorem traspaso₂ (v₁ : M₁.σ) (v₂ : M₂.σ) (S₁ : ∀ k, List (M₁.Γ k)) :
    ∀ (A : List (Medio M₂)) (S₂ : ∀ k, List (M₂.Γ k)) (o : Option (Medio M₂)),
      Llega (TM2.step (compuesta M₁ M₂ e x₀).m) (A.length + 1)
        (⟨some T2, (v₁, v₂, o), comb S₁ S₂ A⟩ : CC M₁ M₂)
        ⟨some (Sum.inr (Sum.inl M₂.main)), (v₁, v₂, none),
          comb S₁ (update S₂ M₂.k₀ (A.reverse ++ S₂ M₂.k₀)) []⟩ := by
  intro A
  induction A with
  | nil =>
    intro S₂ o
    apply Llega.uno
    show some (stepAux ((compuesta M₁ M₂ e x₀).m T2) (v₁, v₂, o) (comb S₁ S₂ [])) = _
    rw [t2_stepAux]
    simp [update_eq_self]
  | cons x A ih =>
    intro S₂ o
    have h1 : Llega (TM2.step (compuesta M₁ M₂ e x₀).m) 1
        (⟨some T2, (v₁, v₂, o), comb S₁ S₂ (x :: A)⟩ : CC M₁ M₂)
        ⟨some T2, (v₁, v₂, some x), comb S₁ (update S₂ M₂.k₀ (x :: S₂ M₂.k₀)) A⟩ := by
      apply Llega.uno
      show some (stepAux ((compuesta M₁ M₂ e x₀).m T2) (v₁, v₂, o) (comb S₁ S₂ (x :: A))) = _
      rw [t2_stepAux]
      rfl
    have h2 := ih (update S₂ M₂.k₀ (x :: S₂ M₂.k₀)) (some x)
    rw [update_idem, update_self] at h2
    have := h1.trans h2
    simpa [List.reverse_cons, List.append_assoc] using this

end Fases

/-! ## Cuánto crece una pila -/

section Crecimiento

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- El máximo número de `push` que una instrucción puede hacer en un paso. -/
def maxPush : TM2.Stmt Γ Λ σ → ℕ
  | push _ _ q => maxPush q + 1
  | peek _ _ q => maxPush q
  | pop _ _ q => maxPush q
  | load _ q => maxPush q
  | branch _ q₁ q₂ => max (maxPush q₁) (maxPush q₂)
  | goto _ => 0
  | halt => 0

theorem length_update_le (S : ∀ k, List (Γ k)) (k' : K) (x : List (Γ k')) (d : ℕ)
    (h : x.length ≤ (S k').length + d) (k : K) : (update S k' x k).length ≤ (S k).length + d := by
  by_cases hk : k = k'
  · subst hk; rw [update_self]; exact h
  · rw [update_of_ne hk]; omega

/-- En un paso, cada pila crece a lo sumo `maxPush`. -/
theorem stepAux_length_le (k : K) :
    ∀ (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)),
      ((stepAux q v S).stk k).length ≤ (S k).length + maxPush q := by
  intro q
  induction q with
  | push k' f q ih =>
    intro v S
    have h1 := ih v (update S k' (f v :: S k'))
    have h2 := length_update_le S k' (f v :: S k') 1 (by simp) k
    simp only [stepAux, maxPush]
    omega
  | peek k' f q ih => intro v S; simpa only [stepAux, maxPush] using ih _ S
  | pop k' f q ih =>
    intro v S
    have h1 := ih (f v (S k').head?) (update S k' (S k').tail)
    have h2 := length_update_le S k' (S k').tail 0 (by simp) k
    simp only [stepAux, maxPush]
    omega
  | load a q ih => intro v S; simpa only [stepAux, maxPush] using ih _ S
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    have h1 := ih₁ v S
    have h2 := ih₂ v S
    simp only [stepAux, maxPush]
    cases f v <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega
  | goto f => intro v S; simp [stepAux, maxPush]
  | halt => intro v S; simp [stepAux, maxPush]

/-- Una medida que crece a lo sumo `d` por paso, crece a lo sumo `n · d` en `n` pasos. -/
theorem Llega.medida {τ : Type} {f : τ → Option τ} (μ : τ → ℕ) (d : ℕ)
    (hpaso : ∀ a b, f a = some b → μ b ≤ μ a + d) :
    ∀ (n : ℕ) (a b : τ), Llega f n a b → μ b ≤ μ a + n * d := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have : a = b := Option.some.inj h
    subst this
    simp
  | succ n ih =>
    intro a b h
    unfold Llega at h
    rw [iterate_succ_apply] at h
    change (flip bind f)^[n] (f a) = some b at h
    cases hfa : f a with
    | none => rw [hfa, iterate_none] at h; exact absurd h (by simp)
    | some a' =>
      rw [hfa] at h
      have h1 := ih a' b h
      have h2 := hpaso a a' hfa
      have : (n + 1) * d = n * d + d := by ring
      omega

end Crecimiento

/-- El máximo de `push` por paso, sobre todas las etiquetas de la máquina. -/
def maxPushTM (M : FinTM2) : ℕ := Finset.univ.sup (fun l => maxPush (M.m l))

/-- En `n` pasos de una máquina, cada pila crece a lo sumo `n · maxPushTM`. -/
theorem crece (M : FinTM2) (k : M.K) (n : ℕ) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : Llega (TM2.step M.m) n c c') : (c'.stk k).length ≤ (c.stk k).length + n * maxPushTM M := by
  refine Llega.medida (fun c => (c.stk k).length) (maxPushTM M) ?_ n c c' h
  intro a b hab
  obtain ⟨l, v, S⟩ := a
  cases l with
  | none => simp [TM2.step] at hab
  | some l =>
    simp only [TM2.step, Option.some.injEq] at hab
    subst hab
    have h1 := stepAux_length_le k (M.m l) v S
    have h2 : maxPush (M.m l) ≤ maxPushTM M :=
      Finset.le_sup (f := fun l => maxPush (M.m l)) (Finset.mem_univ l)
    exact le_trans h1 (Nat.add_le_add_left h2 _)

theorem initList_stk (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = update (fun _ => []) M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem haltList_stk (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk = update (fun _ => []) M.k₁ s := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp [haltList]
  · simp [haltList, h]


/-! ## El armado -/

theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

theorem comb_vacio :
    (fun _ => [] : ∀ k : KK M₁ M₂, List (ΓΓ M₁ M₂ k)) = comb (fun _ => []) (fun _ => []) [] := by
  funext k
  rcases k with k | k | k <;> rfl

theorem update_vacio {K : Type} [DecidableEq K] {Γ : K → Type} (k : K) :
    update (fun _ => [] : ∀ k, List (Γ k)) k [] = fun _ => [] :=
  update_eq_self k (fun _ => [])

section Armado

variable (e : M₁.Γ M₁.k₁ → Medio M₂) (x₀ : Medio M₂)

theorem init_stk (inp : List (M₁.Γ M₁.k₀)) :
    (initList (compuesta M₁ M₂ e x₀) inp).stk = comb (initList M₁ inp).stk (fun _ => []) [] := by
  rw [initList_stk, initList_stk]
  exact (congrArg (fun S => update S (Sum.inl M₁.k₀) inp) comb_vacio).trans (comb_update_izq _ _ _ _ _)

theorem halt_stk (out : List (M₂.Γ M₂.k₁)) :
    (haltList (compuesta M₁ M₂ e x₀) out).stk = comb (fun _ => []) (haltList M₂ out).stk [] := by
  rw [haltList_stk, haltList_stk]
  exact (congrArg (fun S => update S (Sum.inr (Sum.inl M₂.k₁)) out) comb_vacio).trans
    (comb_update_der _ _ _ _ _)

/-- **La corrida completa**: fase 1, los dos traspasos y fase 3. -/
theorem corrida (inp : List (M₁.Γ M₁.k₀)) (s : List (M₁.Γ M₁.k₁)) (out : List (M₂.Γ M₂.k₁)) (n₁ n₂ : ℕ)
    (h₁ : Llega (TM2.step M₁.m) n₁ (initList M₁ inp) (haltList M₁ s))
    (h₂ : Llega (TM2.step M₂.m) n₂ (initList M₂ (s.map e)) (haltList M₂ out)) :
    Llega (TM2.step (compuesta M₁ M₂ e x₀).m) (n₂ + ((s.length + 1) + ((s.length + 1) + n₁)))
      (initList (compuesta M₁ M₂ e x₀) inp : CC M₁ M₂) (haltList (compuesta M₁ M₂ e x₀) out) := by
  have f1 := Llega.sim (emb₁ (M₂.initialState, none) (fun _ => []) []) (paso₁ e x₀ _ _ _) n₁ _ _ h₁
  have f2 := traspaso₁ e x₀ M₁.initialState M₂.initialState (fun _ => []) s
    (update (fun _ => []) M₁.k₁ s) none [] (update_self _ _ _)
  have f3 := traspaso₂ e x₀ M₁.initialState M₂.initialState (fun _ => []) ((s.map e).reverse)
    (fun _ => []) none
  have f4 := Llega.sim (emb₂ M₁.initialState none (fun _ => []) []) (paso₂ e x₀ _ _ _ _) n₂ _ _ h₂
  have e0 : (initList (compuesta M₁ M₂ e x₀) inp : CC M₁ M₂) =
      emb₁ (M₂.initialState, none) (fun _ => []) [] (initList M₁ inp) := by
    show (⟨_, _, (initList (compuesta M₁ M₂ e x₀) inp).stk⟩ : CC M₁ M₂) = _
    rw [init_stk]
    rfl
  have e1 : emb₁ (M₂.initialState, none) (fun _ => []) [] (haltList M₁ s) =
      (⟨some T1, (M₁.initialState, M₂.initialState, none),
        comb (update (fun _ => []) M₁.k₁ s) (fun _ => []) []⟩ : CC M₁ M₂) := by
    show (⟨_, _, comb (haltList M₁ s).stk _ _⟩ : CC M₁ M₂) = _
    rw [haltList_stk]
    rfl
  have e3 : emb₂ M₁.initialState none (fun _ => []) [] (initList M₂ (s.map e)) =
      (⟨some (Sum.inr (Sum.inl M₂.main)), (M₁.initialState, M₂.initialState, none),
        comb (fun _ => []) (update (fun _ => []) M₂.k₀ (s.map e)) []⟩ : CC M₁ M₂) := by
    show (⟨_, _, comb _ (initList M₂ (s.map e)).stk _⟩ : CC M₁ M₂) = _
    rw [initList_stk]
    rfl
  have e4 : emb₂ M₁.initialState none (fun _ => []) [] (haltList M₂ out) =
      (haltList (compuesta M₁ M₂ e x₀) out : CC M₁ M₂) := by
    show _ = (⟨_, _, (haltList (compuesta M₁ M₂ e x₀) out).stk⟩ : CC M₁ M₂)
    rw [halt_stk]
    rfl
  rw [← e0, e1] at f1
  rw [update_idem, update_vacio, List.append_nil] at f2
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, List.length_map] at f3
  rw [e3, e4] at f4
  exact ((f1.trans f2).trans f3).trans f4

end Armado

/-! ## El teorema -/

open Polynomial in
/-- **La composición de dos funciones de tiempo polinomial es de tiempo polinomial.** -/
noncomputable def componer {α β γ αΓ βΓ γΓ : Type} [Inhabited βΓ] {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (g ∘ f) where
  tm := compuesta hf.tm hg.tm (fun x => hg.inputAlphabet.symm (hf.outputAlphabet x))
    (hg.inputAlphabet.symm default)
  inputAlphabet := hf.inputAlphabet
  outputAlphabet := hg.outputAlphabet
  time := hg.time.comp (X + C (maxPushTM hf.tm) * hf.time) +
    (2 * (X + C (maxPushTM hf.tm) * hf.time + 1) + hf.time)
  outputsFun a := by
    have h₁ := hf.outputsFun a
    have h₂ := hg.outputsFun (f a)
    set e : hf.tm.Γ hf.tm.k₁ → Medio hg.tm := fun x => hg.inputAlphabet.symm (hf.outputAlphabet x)
    set s := List.map hf.outputAlphabet.invFun (eb (f a)) with hs
    have hse : s.map e = List.map hg.inputAlphabet.invFun (eb (f a)) := by
      simp [hs, e, List.map_map, Function.comp_def]
    have l₁ : Llega (TM2.step hf.tm.m) h₁.steps (initList hf.tm (List.map hf.inputAlphabet.invFun (ea a)))
        (haltList hf.tm s) := h₁.evals_in_steps
    have l₂ : Llega (TM2.step hg.tm.m) h₂.steps (initList hg.tm (s.map e))
        (haltList hg.tm (List.map hg.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hse]; exact h₂.evals_in_steps
    have run := corrida e (hg.inputAlphabet.symm default) _ s _ _ _ l₁ l₂
    -- La salida de la primera máquina no crece más que polinomialmente.
    have hcrece := crece hf.tm hf.tm.k₁ _ _ _ l₁
    rw [haltList_stk, update_self, initList_stk] at hcrece
    have hini := length_update_le (fun _ => [] : ∀ k, List (hf.tm.Γ k)) hf.tm.k₀
      (List.map hf.inputAlphabet.invFun (ea a)) (ea a).length (by simp) hf.tm.k₁
    have hslen : s.length = (eb (f a)).length := by simp [hs]
    have ht₁ := h₁.steps_le_m
    have ht₂ := h₂.steps_le_m
    have hB : (eb (f a)).length ≤ (ea a).length + maxPushTM hf.tm * hf.time.eval (ea a).length := by
      have := Nat.mul_le_mul_right (maxPushTM hf.tm) ht₁
      simp only [List.length_nil, zero_add] at hini
      rw [Nat.mul_comm (maxPushTM hf.tm)]
      omega
    have hmono := eval_mono hg.time hB
    refine ⟨⟨_, run⟩, ?_⟩
    simp only [eval_add, eval_mul, eval_comp, eval_C, eval_X, eval_one, eval_ofNat]
    omega

/-- **Primera propiedad de `CierrePolinomial`, probada:** el tiempo polinomial se cierra por composición. -/
theorem esPolinomial_comp {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] (f : α → β) (g : β → γ)
    (hf : EsPolinomial f) (hg : EsPolinomial g) : EsPolinomial (g ∘ f) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  exact ⟨componer hf hg⟩

end Componer
end Sagitta.Map
