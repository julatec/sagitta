import Sagitta.Map.Pares

/-!
# Aplicar una función al primer componente de un par

Si `f` es de tiempo polinomial, `fun q => (f q.1, q.2)` también. Es la tercera pieza de los pares, y la única que
envuelve una máquina ajena.

**La máquina.** Tiene las pilas de la máquina `M` de `f`, más dos de bits: `E`, que es la entrada y la salida, y una
auxiliar `T`. La entrada trae `delimita u ++ w`.

* **A**: lee el bloque y pasa `u` a `T`; queda al revés. En `E` queda `w`, que nadie toca hasta el final.
* **B**: pasa `T` a la pila de entrada de `M`; `u` queda derecho.
* corre `M`. Donde `M` se detendría, salta a C.
* **C**: pasa la pila de salida de `M` a `T`, al revés, y escribe el cierre del bloque sobre `w`.
* **D**: saca de `T` y escribe cada bit con su marca. Queda `delimita (salida) ++ w`.
-/

open Turing Turing.TM2 Turing.TM2.Stmt Function

namespace Sagitta.Map
namespace Primero

open Componer (Llega)
open Pares (envolver envolver_bloque)

variable (M : FinTM2)

/-- Las pilas: las de `M`, la de entrada y salida (`false`) y la auxiliar (`true`). -/
abbrev KP : Type := M.K ⊕ Bool

/-- El alfabeto de cada pila. -/
@[reducible] def ΓP : KP M → Type
  | Sum.inl k => M.Γ k
  | Sum.inr _ => Bool

/-- Las etiquetas: las de `M` y las cuatro de los bucles. -/
abbrev ΛP : Type := M.Λ ⊕ Fin 4

/-- El estado: el de `M` y el bit que se está pasando. -/
abbrev σP : Type := M.σ × Option Bool

variable {M}

/-- La pila de entrada y salida. -/
abbrev E : KP M := Sum.inr false
/-- La pila auxiliar. -/
abbrev T : KP M := Sum.inr true

/-- Las pilas de la máquina, a partir de las de `M` y las dos de bits. -/
@[reducible] def comb (S : ∀ k, List (M.Γ k)) (i t : List Bool) : ∀ k : KP M, List (ΓP M k)
  | Sum.inl k => S k
  | Sum.inr false => i
  | Sum.inr true => t

theorem comb_update_M (S : ∀ k, List (M.Γ k)) (i t : List Bool) (k : M.K) (x : List (M.Γ k)) :
    update (comb S i t) (Sum.inl k) x = comb (update S k x) i t := by
  funext j
  rcases j with j | j | j
  · by_cases h : j = k
    · subst h
      exact (update_self (β := fun k => List (ΓP M k)) _ _ _).trans
        (update_self (β := fun k => List (M.Γ k)) j x S).symm
    · exact (update_of_ne (β := fun k => List (ΓP M k)) (Sum.inl_injective.ne h) _ _).trans
        (update_of_ne h _ _).symm
  · exact update_of_ne (β := fun k => List (ΓP M k)) (by simp) _ _
  · exact update_of_ne (β := fun k => List (ΓP M k)) (by simp) _ _

theorem comb_update_E (S : ∀ k, List (M.Γ k)) (i t z : List Bool) :
    update (comb S i t) E z = comb S z t := by
  funext j
  rcases j with j | j | j
  · exact update_of_ne (β := fun k => List (ΓP M k)) (by simp) _ _
  · exact update_self (β := fun k => List (ΓP M k)) _ _ _
  · exact update_of_ne (β := fun k => List (ΓP M k)) (by simp) _ _

theorem comb_update_T (S : ∀ k, List (M.Γ k)) (i t z : List Bool) :
    update (comb S i t) T z = comb S i z := by
  funext j
  rcases j with j | j | j
  · exact update_of_ne (β := fun k => List (ΓP M k)) (by simp) _ _
  · exact update_of_ne (β := fun k => List (ΓP M k)) (by simp) _ _
  · exact update_self (β := fun k => List (ΓP M k)) _ _ _

/-- Una instrucción de `M`, en la máquina envolvente. Donde `M` se detiene, salta al bucle C. -/
def tr : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ΓP M) (ΛP M) (σP M)
  | push k f q => push (Sum.inl k) (fun v => f v.1) (tr q)
  | peek k f q => peek (Sum.inl k) (fun v o => (f v.1 o, v.2)) (tr q)
  | pop k f q => pop (Sum.inl k) (fun v o => (f v.1 o, v.2)) (tr q)
  | load a q => load (fun v => (a v.1, v.2)) (tr q)
  | branch f q₁ q₂ => branch (fun v => f v.1) (tr q₁) (tr q₂)
  | goto f => goto (fun v => Sum.inl (f v.1))
  | halt => goto (fun _ => Sum.inr 2)

/-- La configuración de la máquina envolvente, con sus tipos a la vista. -/
abbrev CPr (M : FinTM2) : Type := TM2.Cfg (ΓP M) (ΛP M) (σP M)

/-- Una configuración de `M`, vista en la máquina envolvente. -/
def emb (w : Option Bool) (i t : List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) : CPr M :=
  ⟨some (match c.l with | some l => Sum.inl l | none => Sum.inr 2), (c.var, w), comb c.stk i t⟩

theorem tr_stepAux (w : Option Bool) (i t : List Bool) :
    ∀ (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)),
      stepAux (tr q) (v, w) (comb S i t) = emb w i t (stepAux q v S) := by
  intro q
  induction q with
  | push k f q ih =>
    intro v S
    simp only [tr, stepAux]
    exact (congrArg (stepAux (tr q) (v, w)) (comb_update_M S i t k (f v :: S k))).trans (ih v _)
  | peek k f q ih => intro v S; simp only [tr, stepAux]; exact ih _ _
  | pop k f q ih =>
    intro v S
    simp only [tr, stepAux]
    exact (congrArg (stepAux (tr q) (f v (S k).head?, w)) (comb_update_M S i t k (S k).tail)).trans (ih _ _)
  | load a q ih => intro v S; simp only [tr, stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [tr, stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => intro v S; rfl
  | halt => intro v S; rfl

variable (M) in
/-- **La máquina envolvente.** `ein` convierte un bit en un símbolo de entrada de `M`; `eout`, un símbolo de salida
de `M` en un bit. -/
@[reducible] def primero (ein : Bool → M.Γ M.k₀) (eout : M.Γ M.k₁ → Bool) : FinTM2 where
  K := KP M
  k₀ := E
  k₁ := E
  Γ := ΓP M
  Λ := ΛP M
  main := Sum.inr 0
  σ := σP M
  initialState := (M.initialState, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fun
    | Sum.inl l => tr (M.m l)
    | Sum.inr 0 =>
        pop E (fun v o => (v.1, o))
          (branch (fun v => v.2 == some true)
            (pop E (fun v o => (v.1, o)) (push T (fun v => v.2.getD false) (goto fun _ => Sum.inr 0)))
            (goto fun _ => Sum.inr 1))
    | Sum.inr 1 =>
        pop T (fun v o => (v.1, o))
          (branch (fun v => v.2.isSome)
            (push (Sum.inl M.k₀) (fun v => ein (v.2.getD false)) (goto fun _ => Sum.inr 1))
            (goto fun _ => Sum.inl M.main))
    | Sum.inr 2 =>
        pop (Sum.inl M.k₁) (fun v o => (v.1, o.map eout))
          (branch (fun v => v.2.isSome)
            (push T (fun v => v.2.getD false) (goto fun _ => Sum.inr 2))
            (push E (fun _ => false) (goto fun _ => Sum.inr 3)))
    | Sum.inr 3 =>
        pop T (fun v o => (v.1, o))
          (branch (fun v => v.2.isSome)
            (push E (fun v => v.2.getD false) (push E (fun _ => true) (goto fun _ => Sum.inr 3)))
            halt)

section Bucles

variable (ein : Bool → M.Γ M.k₀) (eout : M.Γ M.k₁ → Bool)

/-- Fase central: un paso de `M` es un paso de la envolvente. -/
theorem paso (w : Option Bool) (i t : List Bool) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : TM2.step M.m c = some c') :
    TM2.step (primero M ein eout).m (emb w i t c) = some (emb w i t c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (tr_stepAux w i t (M.m l) v S)

/-! ### Bucle A: leer el bloque -/

theorem pasoA_bit (v₁ : M.σ) (p : Option Bool) (S : ∀ k, List (M.Γ k)) (b : Bool) (r t : List Bool) :
    TM2.step (primero M ein eout).m (⟨some (Sum.inr 0), (v₁, p), comb S (true :: b :: r) t⟩ : CPr M) =
      some ⟨some (Sum.inr 0), (v₁, some b), comb S r (b :: t)⟩ := by
  have h : stepAux ((primero M ein eout).m (Sum.inr 0)) (v₁, p) (comb S (true :: b :: r) t) =
      (⟨some (Sum.inr 0), (v₁, some b),
        update (update (update (comb S (true :: b :: r) t) E (b :: r)) E r) T (b :: t)⟩ : CPr M) := rfl
  refine congrArg some (h.trans ?_)
  rw [comb_update_E, comb_update_E, comb_update_T]

theorem pasoA_fin (v₁ : M.σ) (p : Option Bool) (S : ∀ k, List (M.Γ k)) (r t : List Bool) :
    TM2.step (primero M ein eout).m (⟨some (Sum.inr 0), (v₁, p), comb S (false :: r) t⟩ : CPr M) =
      some ⟨some (Sum.inr 1), (v₁, some false), comb S r t⟩ := by
  have h : stepAux ((primero M ein eout).m (Sum.inr 0)) (v₁, p) (comb S (false :: r) t) =
      (⟨some (Sum.inr 1), (v₁, some false), update (comb S (false :: r) t) E r⟩ : CPr M) := rfl
  refine congrArg some (h.trans ?_)
  rw [comb_update_E]

theorem bucleA (v₁ : M.σ) (S : ∀ k, List (M.Γ k)) (r : List Bool) :
    ∀ (u t : List Bool) (p : Option Bool),
      Llega (TM2.step (primero M ein eout).m) (u.length + 1)
        (⟨some (Sum.inr 0), (v₁, p), comb S (CodBits.delimita u ++ r) t⟩ : CPr M)
        ⟨some (Sum.inr 1), (v₁, some false), comb S r (u.reverse ++ t)⟩
  | [], t, p => Llega.uno (pasoA_fin ein eout v₁ p S r t)
  | b :: u, t, p => by
    have h1 := Llega.uno (pasoA_bit ein eout v₁ p S b (CodBits.delimita u ++ r) t)
    have := h1.trans (bucleA v₁ S r u (b :: t) (some b))
    simpa [CodBits.delimita, List.reverse_cons, List.append_assoc] using this

/-! ### Bucle B: cargar la entrada de `M` -/

theorem pasoB_bit (v₁ : M.σ) (p : Option Bool) (S : ∀ k, List (M.Γ k)) (c : Bool) (i t : List Bool) :
    TM2.step (primero M ein eout).m (⟨some (Sum.inr 1), (v₁, p), comb S i (c :: t)⟩ : CPr M) =
      some ⟨some (Sum.inr 1), (v₁, some c), comb (update S M.k₀ (ein c :: S M.k₀)) i t⟩ := by
  have h : stepAux ((primero M ein eout).m (Sum.inr 1)) (v₁, p) (comb S i (c :: t)) =
      (⟨some (Sum.inr 1), (v₁, some c),
        update (update (comb S i (c :: t)) T t) (Sum.inl M.k₀) (ein c :: S M.k₀)⟩ : CPr M) := rfl
  refine congrArg some (h.trans ?_)
  rw [comb_update_T, comb_update_M]

theorem pasoB_fin (v₁ : M.σ) (p : Option Bool) (S : ∀ k, List (M.Γ k)) (i : List Bool) :
    TM2.step (primero M ein eout).m (⟨some (Sum.inr 1), (v₁, p), comb S i []⟩ : CPr M) =
      some ⟨some (Sum.inl M.main), (v₁, none), comb S i []⟩ := by
  have h : stepAux ((primero M ein eout).m (Sum.inr 1)) (v₁, p) (comb S i []) =
      (⟨some (Sum.inl M.main), (v₁, none), update (comb S i []) T []⟩ : CPr M) := rfl
  refine congrArg some (h.trans ?_)
  rw [comb_update_T]

theorem bucleB (v₁ : M.σ) (i : List Bool) :
    ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (p : Option Bool),
      Llega (TM2.step (primero M ein eout).m) (t.length + 1)
        (⟨some (Sum.inr 1), (v₁, p), comb S i t⟩ : CPr M)
        ⟨some (Sum.inl M.main), (v₁, none), comb (update S M.k₀ ((t.map ein).reverse ++ S M.k₀)) i []⟩
  | [], S, p => by
    have := Llega.uno (pasoB_fin ein eout v₁ p S i)
    simpa [update_eq_self] using this
  | c :: t, S, p => by
    have h1 := Llega.uno (pasoB_bit ein eout v₁ p S c i t)
    have h2 := bucleB v₁ i t (update S M.k₀ (ein c :: S M.k₀)) (some c)
    rw [update_idem, update_self] at h2
    have := h1.trans h2
    simpa [List.reverse_cons, List.append_assoc] using this

/-! ### Bucle C: recoger la salida de `M` -/

/-- Lo que hace un paso del bucle C. -/
theorem c_stepAux (v₁ : M.σ) (p : Option Bool) (S : ∀ k, List (M.Γ k)) (i t : List Bool) :
    stepAux ((primero M ein eout).m (Sum.inr 2)) (v₁, p) (comb S i t) =
      bif (Option.map eout (S M.k₁).head?).isSome then
        (⟨some (Sum.inr 2), (v₁, Option.map eout (S M.k₁).head?),
          comb (update S M.k₁ (S M.k₁).tail) i ((Option.map eout (S M.k₁).head?).getD false :: t)⟩ : CPr M)
      else
        ⟨some (Sum.inr 3), (v₁, Option.map eout (S M.k₁).head?),
          comb (update S M.k₁ (S M.k₁).tail) (false :: i) t⟩ := by
  have h : stepAux ((primero M ein eout).m (Sum.inr 2)) (v₁, p) (comb S i t) =
      bif (Option.map eout (S M.k₁).head?).isSome then
        (⟨some (Sum.inr 2), (v₁, Option.map eout (S M.k₁).head?),
          update (update (comb S i t) (Sum.inl M.k₁) (S M.k₁).tail) T
            ((Option.map eout (S M.k₁).head?).getD false :: t)⟩ : CPr M)
      else
        ⟨some (Sum.inr 3), (v₁, Option.map eout (S M.k₁).head?),
          update (update (comb S i t) (Sum.inl M.k₁) (S M.k₁).tail) E (false :: i)⟩ := rfl
  rw [h, comb_update_M, comb_update_T, comb_update_E]

theorem bucleC (v₁ : M.σ) (i : List Bool) :
    ∀ (s : List (M.Γ M.k₁)) (S : ∀ k, List (M.Γ k)) (p : Option Bool) (t : List Bool), S M.k₁ = s →
      Llega (TM2.step (primero M ein eout).m) (s.length + 1)
        (⟨some (Sum.inr 2), (v₁, p), comb S i t⟩ : CPr M)
        ⟨some (Sum.inr 3), (v₁, none), comb (update S M.k₁ []) (false :: i) ((s.map eout).reverse ++ t)⟩ := by
  intro s
  induction s with
  | nil =>
    intro S p t hs
    apply Llega.uno
    show some (stepAux ((primero M ein eout).m (Sum.inr 2)) (v₁, p) (comb S i t)) = _
    rw [c_stepAux, hs]
    rfl
  | cons x s ih =>
    intro S p t hs
    have h1 : Llega (TM2.step (primero M ein eout).m) 1
        (⟨some (Sum.inr 2), (v₁, p), comb S i t⟩ : CPr M)
        ⟨some (Sum.inr 2), (v₁, some (eout x)), comb (update S M.k₁ s) i (eout x :: t)⟩ := by
      apply Llega.uno
      show some (stepAux ((primero M ein eout).m (Sum.inr 2)) (v₁, p) (comb S i t)) = _
      rw [c_stepAux, hs]
      rfl
    have h2 := ih (update S M.k₁ s) (some (eout x)) (eout x :: t) (update_self _ _ _)
    rw [update_idem] at h2
    have := h1.trans h2
    simpa [List.reverse_cons, List.append_assoc] using this

/-! ### Bucle D: rearmar el bloque -/

theorem pasoD_bit (v₁ : M.σ) (p : Option Bool) (S : ∀ k, List (M.Γ k)) (c : Bool) (i t : List Bool) :
    TM2.step (primero M ein eout).m (⟨some (Sum.inr 3), (v₁, p), comb S i (c :: t)⟩ : CPr M) =
      some ⟨some (Sum.inr 3), (v₁, some c), comb S (true :: c :: i) t⟩ := by
  have h : stepAux ((primero M ein eout).m (Sum.inr 3)) (v₁, p) (comb S i (c :: t)) =
      (⟨some (Sum.inr 3), (v₁, some c),
        update (update (update (comb S i (c :: t)) T t) E (c :: i)) E (true :: c :: i)⟩ : CPr M) := rfl
  refine congrArg some (h.trans ?_)
  rw [comb_update_T, comb_update_E, comb_update_E]

theorem pasoD_fin (v₁ : M.σ) (p : Option Bool) (S : ∀ k, List (M.Γ k)) (i : List Bool) :
    TM2.step (primero M ein eout).m (⟨some (Sum.inr 3), (v₁, p), comb S i []⟩ : CPr M) =
      some ⟨none, (v₁, none), comb S i []⟩ := by
  have h : stepAux ((primero M ein eout).m (Sum.inr 3)) (v₁, p) (comb S i []) =
      (⟨none, (v₁, none), update (comb S i []) T []⟩ : CPr M) := rfl
  refine congrArg some (h.trans ?_)
  rw [comb_update_T]

theorem bucleD (v₁ : M.σ) (S : ∀ k, List (M.Γ k)) :
    ∀ (t i : List Bool) (p : Option Bool),
      Llega (TM2.step (primero M ein eout).m) (t.length + 1)
        (⟨some (Sum.inr 3), (v₁, p), comb S i t⟩ : CPr M) ⟨none, (v₁, none), comb S (envolver t i) []⟩
  | [], i, p => Llega.uno (pasoD_fin ein eout v₁ p S i)
  | c :: t, i, p =>
    (Llega.uno (pasoD_bit ein eout v₁ p S c i t)).trans (bucleD v₁ S t (true :: c :: i) (some c))

end Bucles

/-! ## El armado -/

section Armado

variable (ein : Bool → M.Γ M.k₀) (eout : M.Γ M.k₁ → Bool)

theorem comb_vacio : (fun _ => [] : ∀ k : KP M, List (ΓP M k)) = comb (fun _ => []) [] [] := by
  funext k
  rcases k with k | k | k <;> rfl

theorem init_eq (inp : List Bool) :
    (initList (primero M ein eout) inp : CPr M) =
      ⟨some (Sum.inr 0), (M.initialState, none), comb (fun _ => []) inp []⟩ := by
  show (⟨_, _, (initList (primero M ein eout) inp).stk⟩ : CPr M) = _
  rw [Componer.initList_stk]
  congr 1
  exact (congrArg (fun S => update S E inp) comb_vacio).trans (comb_update_E _ _ _ _)

theorem halt_eq (out : List Bool) :
    (haltList (primero M ein eout) out : CPr M) =
      ⟨none, (M.initialState, none), comb (fun _ => []) out []⟩ := by
  show (⟨_, _, (haltList (primero M ein eout) out).stk⟩ : CPr M) = _
  rw [Componer.haltList_stk]
  congr 1
  exact (congrArg (fun S => update S E out) comb_vacio).trans (comb_update_E _ _ _ _)

/-- **La corrida completa**: de `delimita u ++ w` a `delimita (salida de M sobre u) ++ w`. -/
theorem corrida (u w : List Bool) (s : List (M.Γ M.k₁)) (n : ℕ)
    (h : Llega (TM2.step M.m) n (initList M (u.map ein)) (haltList M s)) :
    Llega (TM2.step (primero M ein eout).m)
      ((s.length + 1) + ((s.length + 1) + (n + ((u.length + 1) + (u.length + 1)))))
      (initList (primero M ein eout) (CodBits.delimita u ++ w) : CPr M)
      (haltList (primero M ein eout) (CodBits.delimita (s.map eout) ++ w)) := by
  have a := bucleA ein eout M.initialState (fun _ => []) w u [] none
  have b := bucleB ein eout M.initialState w (u.reverse ++ []) (fun _ => []) (some false)
  have m := Llega.sim (emb none w []) (paso ein eout none w []) n _ _ h
  have c := bucleC ein eout M.initialState w s (update (fun _ => []) M.k₁ s) none [] (update_self _ _ _)
  have d := bucleD ein eout M.initialState (fun _ => []) ((s.map eout).reverse ++ []) (false :: w) none
  have e1 : emb none w [] (initList M (u.map ein)) =
      (⟨some (Sum.inl M.main), (M.initialState, none),
        comb (update (fun _ => []) M.k₀ (u.map ein)) w []⟩ : CPr M) := by
    show (⟨_, _, comb (initList M (u.map ein)).stk _ _⟩ : CPr M) = _
    rw [Componer.initList_stk]
    rfl
  have e2 : emb none w [] (haltList M s) =
      (⟨some (Sum.inr 2), (M.initialState, none), comb (update (fun _ => []) M.k₁ s) w []⟩ : CPr M) := by
    show (⟨_, _, comb (haltList M s).stk _ _⟩ : CPr M) = _
    rw [Componer.haltList_stk]
    rfl
  rw [e1, e2] at m
  simp only [List.append_nil, List.map_reverse, List.reverse_reverse, List.length_reverse] at a b
  rw [update_idem, Componer.update_vacio, List.append_nil] at c
  simp only [List.append_nil, List.length_reverse, List.length_map] at d
  rw [envolver_bloque] at d
  rw [init_eq, halt_eq]
  exact (((a.trans b).trans m).trans c).trans d

end Armado

/-! ## El teorema -/

open Polynomial in
/-- Aplicar una función de tiempo polinomial al primer componente de un par es de tiempo polinomial. -/
noncomputable def primeroComputable {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] {f : α → β}
    (hf : TM2ComputableInPolyTime (CodBits.toEncoding (α := α)).encode
      (CodBits.toEncoding (α := β)).encode f) :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := α × γ)).encode
      (CodBits.toEncoding (α := β × γ)).encode (fun q : α × γ => (f q.1, q.2)) where
  tm := primero hf.tm hf.inputAlphabet.symm hf.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * (X + C (Componer.maxPushTM hf.tm) * hf.time + 1) + (hf.time + (2 * X + 2))
  outputsFun q := by
    have h₁ := hf.outputsFun q.1
    set s := List.map hf.outputAlphabet.invFun ((CodBits.toEncoding (α := β)).encode (f q.1)) with hs
    have l₁ : Llega (TM2.step hf.tm.m) h₁.steps
        (initList hf.tm ((CodBits.cod q.1).map hf.inputAlphabet.symm)) (haltList hf.tm s) :=
      h₁.evals_in_steps
    have run := corrida hf.inputAlphabet.symm hf.outputAlphabet (CodBits.cod q.1) (CodBits.cod q.2) s _ l₁
    have hso : s.map hf.outputAlphabet = CodBits.cod (f q.1) := by
      simp only [hs, List.map_map]
      have : (⇑hf.outputAlphabet ∘ hf.outputAlphabet.invFun) = id := by
        funext x; exact hf.outputAlphabet.apply_symm_apply x
      rw [this, List.map_id]
      rfl
    rw [hso] at run
    have hin : List.map (Equiv.refl Bool).invFun ((CodBits.toEncoding (α := α × γ)).encode q) =
        CodBits.delimita (CodBits.cod q.1) ++ CodBits.cod q.2 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hout : List.map (Equiv.refl Bool).invFun
        ((CodBits.toEncoding (α := β × γ)).encode (f q.1, q.2)) =
        CodBits.delimita (CodBits.cod (f q.1)) ++ CodBits.cod q.2 := by
      simp only [Equiv.refl]; rw [List.map_id]; rfl
    have hlen : ((CodBits.toEncoding (α := α × γ)).encode q).length =
        2 * (CodBits.cod q.1).length + 1 + (CodBits.cod q.2).length := by
      show (CodBits.delimita (CodBits.cod q.1) ++ CodBits.cod q.2).length = _
      rw [List.length_append, Basicas.delimita_length]
    -- La salida de `M` no crece más que polinomialmente.
    have hcrece := Componer.crece hf.tm hf.tm.k₁ _ _ _ l₁
    rw [Componer.haltList_stk, update_self, Componer.initList_stk] at hcrece
    have hini := Componer.length_update_le (fun _ => [] : ∀ k, List (hf.tm.Γ k)) hf.tm.k₀
      ((CodBits.cod q.1).map hf.inputAlphabet.symm) (CodBits.cod q.1).length (by simp) hf.tm.k₁
    simp only [List.length_nil, zero_add] at hini
    have ht₁ : h₁.steps ≤ hf.time.eval (CodBits.cod q.1).length := h₁.steps_le_m
    have hmono : hf.time.eval (CodBits.cod q.1).length ≤
        hf.time.eval ((CodBits.toEncoding (α := α × γ)).encode q).length :=
      Componer.eval_mono hf.time (by omega)
    have hmul := Nat.mul_le_mul_right (Componer.maxPushTM hf.tm) (le_trans ht₁ hmono)
    rw [hin, hout]
    refine ⟨⟨_, run⟩, ?_⟩
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, eval_ofNat]
    rw [Nat.mul_comm (Componer.maxPushTM hf.tm)]
    omega

theorem esPolinomial_primero {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] {f : α → β}
    (hf : EsPolinomial f) : EsPolinomial (fun q : α × γ => (f q.1, q.2)) := by
  obtain ⟨hf⟩ := hf
  exact ⟨primeroComputable hf⟩

/-- **Cuarta propiedad de `CierrePolinomial`, probada:** el tiempo polinomial se cierra por pares.
`(f a, g a) = primero f ∘ intercambiar ∘ primero g ∘ duplicar`. -/
theorem esPolinomial_pares {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] (f : α → β) (g : α → γ)
    (hf : EsPolinomial f) (hg : EsPolinomial g) : EsPolinomial (fun a => (f a, g a)) := by
  have h1 : EsPolinomial (fun a : α => (a, a)) := Pares.esPolinomial_dup
  have h2 : EsPolinomial (fun q : α × α => (g q.1, q.2)) := esPolinomial_primero hg
  have h3 : EsPolinomial (fun q : γ × α => (q.2, q.1)) := Pares.esPolinomial_swap
  have h4 : EsPolinomial (fun q : α × γ => (f q.1, q.2)) := esPolinomial_primero hf
  exact Componer.esPolinomial_comp _ _
    (Componer.esPolinomial_comp _ _ (Componer.esPolinomial_comp _ _ h1 h2) h3) h4

end Primero
end Sagitta.Map
