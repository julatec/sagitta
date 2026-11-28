import Sagitta.Map.Bucle
import Sagitta.Map.Componer

/-!
# La máquina del bucle «mientras»

Si el paso `g : α → Bool × α` se calcula en tiempo polinomial, el bucle para en un número polinomial de pasos y los
estados intermedios no crecen más que un polinomio, el bucle `Bucle.mientras g (q |x|)` se calcula en tiempo
polinomial (`esPolinomial_mientras`).

**La máquina.** Tiene las pilas de la máquina `M` del paso y una auxiliar de bits. La entrada y la salida van en la
pila de entrada de `M`. Cada vuelta:

1. corre `M`; donde `M` se detendría, salta a leer la bandera;
2. saca de la pila de salida de `M` los tres símbolos `true, b, false` del bloque autodelimitado, y recuerda `b`;
3. pasa el resto de la salida de `M` a la auxiliar y de ahí a la pila de entrada de `M` (dos traspasos, porque cada
   uno invierte el orden);
4. si `b`, vuelve a empezar; si no, se detiene.

Como la corrida de `M` termina con las demás pilas vacías y la variable en el estado inicial, cada vuelta arranca
limpia. Una vuelta cuesta lo que tarda `M` más `2 |x'| + 5`, y hay a lo sumo `q |x|` vueltas.
-/

open Turing Turing.TM2 Turing.TM2.Stmt Function

namespace Sagitta.Map
namespace MientrasMaquina

open Componer (Llega)

/-- Las etapas propias del bucle, fuera de las de `M`: las tres de la bandera (0, 1, 2), la ida a la auxiliar (3)
y la vuelta a la pila de entrada (4). -/
abbrev Etapa : Type := Fin 5

variable (M : FinTM2)

/-- Las pilas: las de `M` y una auxiliar. -/
abbrev KK : Type := M.K ⊕ Unit

/-- El alfabeto de cada pila. -/
@[reducible] def ΓΓ : KK M → Type
  | Sum.inl k => M.Γ k
  | Sum.inr _ => Bool

/-- Las etiquetas: las de `M` y las del bucle. -/
abbrev ΛΛ : Type := M.Λ ⊕ Etapa

/-- El estado: el de `M`, la bandera leída y el símbolo que se está pasando. -/
abbrev σσ : Type := M.σ × Bool × Option Bool

/-- Las pilas de la máquina del bucle, a partir de las de `M` y la auxiliar. -/
@[reducible] def comb (S : ∀ k, List (M.Γ k)) (A : List Bool) : ∀ k : KK M, List (ΓΓ M k)
  | Sum.inl k => S k
  | Sum.inr _ => A

/-- Las configuraciones de la máquina del bucle. -/
abbrev CC : Type := TM2.Cfg (ΓΓ M) (ΛΛ M) (σσ M)

variable {M}

/-- La pila auxiliar. -/
abbrev aux : KK M := Sum.inr ()

/-- Las pilas vacías de `M`. -/
abbrev vacias : ∀ k, List (M.Γ k) := fun _ => []

theorem comb_update_izq (S : ∀ k, List (M.Γ k)) (A : List Bool) (k : M.K) (x : List (M.Γ k)) :
    update (comb M S A) (Sum.inl k) x = comb M (update S k x) A := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      exact (update_self (β := fun k => List (ΓΓ M k)) _ _ _).trans
        (update_self (β := fun k => List (M.Γ k)) j x S).symm
    · exact (update_of_ne (β := fun k => List (ΓΓ M k)) (Sum.inl_injective.ne h) _ _).trans
        (update_of_ne h _ _).symm
  · exact update_of_ne (β := fun k => List (ΓΓ M k)) (by simp) _ _

theorem comb_update_aux (S : ∀ k, List (M.Γ k)) (A B : List Bool) :
    update (comb M S A) aux B = comb M S B := by
  funext j
  rcases j with j | j
  · exact update_of_ne (β := fun k => List (ΓΓ M k)) (by simp) _ _
  · exact update_self (β := fun k => List (ΓΓ M k)) _ _ _

theorem comb_vacio : (fun _ => [] : ∀ k : KK M, List (ΓΓ M k)) = comb M vacias [] := by
  funext k
  rcases k with k | k <;> rfl

/-- Una instrucción de `M`, en la máquina del bucle. Donde `M` se detiene, salta a leer la bandera. -/
def tr : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ΓΓ M) (ΛΛ M) (σσ M)
  | push k f q => push (Sum.inl k) (fun v => f v.1) (tr q)
  | peek k f q => peek (Sum.inl k) (fun v o => (f v.1 o, v.2)) (tr q)
  | pop k f q => pop (Sum.inl k) (fun v o => (f v.1 o, v.2)) (tr q)
  | load a q => load (fun v => (a v.1, v.2)) (tr q)
  | branch f q₁ q₂ => branch (fun v => f v.1) (tr q₁) (tr q₂)
  | goto f => goto (fun v => Sum.inl (f v.1))
  | halt => goto (fun _ => Sum.inr (0 : Etapa))

/-- Una configuración de `M`, vista en la máquina del bucle. Si `M` se detuvo, el bucle está por leer la bandera. -/
def emb (w : Bool × Option Bool) (A : List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) : CC M :=
  ⟨some (match c.l with | some l => Sum.inl l | none => Sum.inr (0 : Etapa)), (c.var, w), comb M c.stk A⟩

theorem tr_stepAux (w : Bool × Option Bool) (A : List Bool) :
    ∀ (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)),
      stepAux (tr q) (v, w) (comb M S A) = emb w A (stepAux q v S) := by
  intro q
  induction q with
  | push k f q ih =>
    intro v S
    simp only [tr, stepAux]
    exact (congrArg (stepAux (tr q) (v, w)) (comb_update_izq S A k (f v :: S k))).trans (ih v _)
  | peek k f q ih => intro v S; simp only [tr, stepAux]; exact ih _ _
  | pop k f q ih =>
    intro v S
    simp only [tr, stepAux]
    exact (congrArg (stepAux (tr q) (f v (S k).head?, w)) (comb_update_izq S A k (S k).tail)).trans (ih _ _)
  | load a q ih => intro v S; simp only [tr, stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [tr, stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => intro v S; rfl
  | halt => intro v S; rfl

/-! ## La máquina -/

variable (M) in
/-- **La máquina del bucle.** `iA` y `oA` son los alfabetos de entrada y de salida de `M`, vistos como bits. -/
@[reducible] def maquina (iA : M.Γ M.k₀ ≃ Bool) (oA : M.Γ M.k₁ ≃ Bool) : FinTM2 where
  K := KK M
  k₀ := Sum.inl M.k₀
  k₁ := Sum.inl M.k₀
  Γ := ΓΓ M
  Λ := ΛΛ M
  main := Sum.inl M.main
  σ := σσ M
  initialState := (M.initialState, false, none)
  Γk₀Fin := M.Γk₀Fin
  m := fun
    | Sum.inl l => tr (M.m l)
    | Sum.inr 0 => pop (Sum.inl M.k₁) (fun v _ => v) (goto fun _ => Sum.inr 1)
    | Sum.inr 1 =>
        pop (Sum.inl M.k₁) (fun v o => (v.1, (o.map oA).getD false, v.2.2)) (goto fun _ => Sum.inr 2)
    | Sum.inr 2 => pop (Sum.inl M.k₁) (fun v _ => v) (goto fun _ => Sum.inr 3)
    | Sum.inr 3 =>
        pop (Sum.inl M.k₁) (fun v o => (v.1, v.2.1, o.map oA))
          (branch (fun v => v.2.2.isSome)
            (push aux (fun v => v.2.2.getD false) (goto fun _ => Sum.inr 3))
            (goto fun _ => Sum.inr 4))
    | Sum.inr 4 =>
        pop aux (fun v o => (v.1, v.2.1, o))
          (branch (fun v => v.2.2.isSome)
            (push (Sum.inl M.k₀) (fun v => iA.symm (v.2.2.getD false)) (goto fun _ => Sum.inr 4))
            (branch (fun v => v.2.1) (goto fun _ => Sum.inl M.main) halt))

/-! ## Las fases de una vuelta -/

section Fases

variable (iA : M.Γ M.k₀ ≃ Bool) (oA : M.Γ M.k₁ ≃ Bool)

/-- Un paso de `M` es un paso del bucle. -/
theorem paso (w : Bool × Option Bool) (A : List Bool) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : TM2.step M.m c = some c') :
    TM2.step (maquina M iA oA).m (emb w A c) = some (emb w A c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (tr_stepAux w A (M.m l) v S)

/-- Primera etapa de la bandera: se descarta el `true` que abre el bloque. -/
theorem bandera₁ (v : σσ M) (o : M.Γ M.k₁) (s : List (M.Γ M.k₁)) (A : List Bool) :
    Llega (TM2.step (maquina M iA oA).m) 1
      (⟨some (Sum.inr 0), v, comb M (update vacias M.k₁ (o :: s)) A⟩ : CC M)
      ⟨some (Sum.inr 1), v, comb M (update vacias M.k₁ s) A⟩ := by
  apply Componer.Llega.uno
  have h : TM2.step (maquina M iA oA).m
      (⟨some (Sum.inr 0), v, comb M (update vacias M.k₁ (o :: s)) A⟩ : CC M) =
      some ⟨some (Sum.inr 1), v, update (comb M (update vacias M.k₁ (o :: s)) A) (Sum.inl M.k₁)
        ((update vacias M.k₁ (o :: s)) M.k₁).tail⟩ := rfl
  rw [h, comb_update_izq, update_self, update_idem]
  rfl

/-- Segunda etapa de la bandera: se lee `b`. -/
theorem bandera₂ (v : σσ M) (o : M.Γ M.k₁) (s : List (M.Γ M.k₁)) (A : List Bool) :
    Llega (TM2.step (maquina M iA oA).m) 1
      (⟨some (Sum.inr 1), v, comb M (update vacias M.k₁ (o :: s)) A⟩ : CC M)
      ⟨some (Sum.inr 2), (v.1, oA o, v.2.2), comb M (update vacias M.k₁ s) A⟩ := by
  apply Componer.Llega.uno
  have h : TM2.step (maquina M iA oA).m
      (⟨some (Sum.inr 1), v, comb M (update vacias M.k₁ (o :: s)) A⟩ : CC M) =
      some ⟨some (Sum.inr 2),
        (v.1, (((update vacias M.k₁ (o :: s)) M.k₁).head?.map oA).getD false, v.2.2),
        update (comb M (update vacias M.k₁ (o :: s)) A) (Sum.inl M.k₁)
        ((update vacias M.k₁ (o :: s)) M.k₁).tail⟩ := rfl
  rw [h, comb_update_izq, update_self, update_idem]
  rfl

/-- Tercera etapa de la bandera: se descarta el `false` que cierra el bloque. -/
theorem bandera₃ (v : σσ M) (o : M.Γ M.k₁) (s : List (M.Γ M.k₁)) (A : List Bool) :
    Llega (TM2.step (maquina M iA oA).m) 1
      (⟨some (Sum.inr 2), v, comb M (update vacias M.k₁ (o :: s)) A⟩ : CC M)
      ⟨some (Sum.inr 3), v, comb M (update vacias M.k₁ s) A⟩ := by
  apply Componer.Llega.uno
  have h : TM2.step (maquina M iA oA).m
      (⟨some (Sum.inr 2), v, comb M (update vacias M.k₁ (o :: s)) A⟩ : CC M) =
      some ⟨some (Sum.inr 3), v, update (comb M (update vacias M.k₁ (o :: s)) A) (Sum.inl M.k₁)
        ((update vacias M.k₁ (o :: s)) M.k₁).tail⟩ := rfl
  rw [h, comb_update_izq, update_self, update_idem]
  rfl

/-- Lo que hace un paso de la ida. -/
theorem ida_stepAux (v₁ : M.σ) (b : Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) (A : List Bool) :
    stepAux ((maquina M iA oA).m (Sum.inr 3)) (v₁, b, o) (comb M S A) =
      bif (Option.map oA (S M.k₁).head?).isSome then
        (⟨some (Sum.inr 3), (v₁, b, Option.map oA (S M.k₁).head?),
          comb M (update S M.k₁ (S M.k₁).tail) ((Option.map oA (S M.k₁).head?).getD false :: A)⟩ : CC M)
      else
        ⟨some (Sum.inr 4), (v₁, b, Option.map oA (S M.k₁).head?), comb M (update S M.k₁ (S M.k₁).tail) A⟩ := by
  have h : stepAux ((maquina M iA oA).m (Sum.inr 3)) (v₁, b, o) (comb M S A) =
      bif (Option.map oA (S M.k₁).head?).isSome then
        (⟨some (Sum.inr 3), (v₁, b, Option.map oA (S M.k₁).head?),
          update (update (comb M S A) (Sum.inl M.k₁) (S M.k₁).tail) aux
            ((Option.map oA (S M.k₁).head?).getD false :: A)⟩ : CC M)
      else
        ⟨some (Sum.inr 4), (v₁, b, Option.map oA (S M.k₁).head?),
          update (comb M S A) (Sum.inl M.k₁) (S M.k₁).tail⟩ := rfl
  rw [h, comb_update_izq, comb_update_aux]

/-- **La ida.** En `|s| + 1` pasos, la pila de salida de `M` pasa, invertida, a la auxiliar. -/
theorem ida (v₁ : M.σ) (b : Bool) :
    ∀ (s : List (M.Γ M.k₁)) (S : ∀ k, List (M.Γ k)) (o : Option Bool) (A : List Bool),
      S M.k₁ = s →
      Llega (TM2.step (maquina M iA oA).m) (s.length + 1)
        (⟨some (Sum.inr 3), (v₁, b, o), comb M S A⟩ : CC M)
        ⟨some (Sum.inr 4), (v₁, b, none), comb M (update S M.k₁ []) ((s.map oA).reverse ++ A)⟩ := by
  intro s
  induction s with
  | nil =>
    intro S o A hs
    apply Componer.Llega.uno
    show some (stepAux ((maquina M iA oA).m (Sum.inr 3)) (v₁, b, o) (comb M S A)) = _
    rw [ida_stepAux, hs]
    rfl
  | cons x s ih =>
    intro S o A hs
    have h1 : Llega (TM2.step (maquina M iA oA).m) 1
        (⟨some (Sum.inr 3), (v₁, b, o), comb M S A⟩ : CC M)
        ⟨some (Sum.inr 3), (v₁, b, some (oA x)), comb M (update S M.k₁ s) (oA x :: A)⟩ := by
      apply Componer.Llega.uno
      show some (stepAux ((maquina M iA oA).m (Sum.inr 3)) (v₁, b, o) (comb M S A)) = _
      rw [ida_stepAux, hs]
      rfl
    have h2 := ih (update S M.k₁ s) (some (oA x)) (oA x :: A) (update_self _ _ _)
    rw [update_idem] at h2
    have := h1.trans h2
    simpa [List.reverse_cons, List.append_assoc] using this

/-- Lo que hace un paso de la vuelta. -/
theorem vuelta_stepAux (v₁ : M.σ) (b : Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) (A : List Bool) :
    stepAux ((maquina M iA oA).m (Sum.inr 4)) (v₁, b, o) (comb M S A) =
      bif A.head?.isSome then
        (⟨some (Sum.inr 4), (v₁, b, A.head?),
          comb M (update S M.k₀ (iA.symm (A.head?.getD false) :: S M.k₀)) A.tail⟩ : CC M)
      else
        bif b then (⟨some (Sum.inl M.main), (v₁, b, A.head?), comb M S A.tail⟩ : CC M)
        else ⟨none, (v₁, b, A.head?), comb M S A.tail⟩ := by
  have h : stepAux ((maquina M iA oA).m (Sum.inr 4)) (v₁, b, o) (comb M S A) =
      bif A.head?.isSome then
        (⟨some (Sum.inr 4), (v₁, b, A.head?),
          update (update (comb M S A) aux A.tail) (Sum.inl M.k₀)
            (iA.symm (A.head?.getD false) :: S M.k₀)⟩ : CC M)
      else
        bif b then (⟨some (Sum.inl M.main), (v₁, b, A.head?), update (comb M S A) aux A.tail⟩ : CC M)
        else ⟨none, (v₁, b, A.head?), update (comb M S A) aux A.tail⟩ := rfl
  rw [h, comb_update_aux, comb_update_izq]

/-- **La vuelta.** En `|A| + 1` pasos, la auxiliar pasa, invertida, a la pila de entrada de `M`; al vaciarse, el
bucle vuelve a empezar si la bandera es `true` y se detiene si es `false`. -/
theorem vuelta (v₁ : M.σ) (b : Bool) :
    ∀ (A : List Bool) (S : ∀ k, List (M.Γ k)) (o : Option Bool),
      Llega (TM2.step (maquina M iA oA).m) (A.length + 1)
        (⟨some (Sum.inr 4), (v₁, b, o), comb M S A⟩ : CC M)
        ⟨bif b then some (Sum.inl M.main) else none, (v₁, b, none),
          comb M (update S M.k₀ ((A.map iA.symm).reverse ++ S M.k₀)) []⟩ := by
  intro A
  induction A with
  | nil =>
    intro S o
    apply Componer.Llega.uno
    show some (stepAux ((maquina M iA oA).m (Sum.inr 4)) (v₁, b, o) (comb M S [])) = _
    rw [vuelta_stepAux]
    cases b <;> simp [update_eq_self]
  | cons x A ih =>
    intro S o
    have h1 : Llega (TM2.step (maquina M iA oA).m) 1
        (⟨some (Sum.inr 4), (v₁, b, o), comb M S (x :: A)⟩ : CC M)
        ⟨some (Sum.inr 4), (v₁, b, some x), comb M (update S M.k₀ (iA.symm x :: S M.k₀)) A⟩ := by
      apply Componer.Llega.uno
      show some (stepAux ((maquina M iA oA).m (Sum.inr 4)) (v₁, b, o) (comb M S (x :: A))) = _
      rw [vuelta_stepAux]
      rfl
    have h2 := ih (update S M.k₀ (iA.symm x :: S M.k₀)) (some x)
    rw [update_idem, update_self] at h2
    have := h1.trans h2
    simpa [List.reverse_cons, List.append_assoc] using this

end Fases

/-! ## Una vuelta -/

section Vuelta

variable (iA : M.Γ M.k₀ ≃ Bool) (oA : M.Γ M.k₁ ≃ Bool)

/-- La configuración al empezar o terminar una vuelta: `x` en la pila de entrada de `M`, lo demás vacío. -/
def cfg (l : Option (ΛΛ M)) (b : Bool) (x : List Bool) : CC M :=
  ⟨l, (M.initialState, b, none), comb M (update vacias M.k₀ (x.map iA.symm)) []⟩

/-- **Una vuelta**: corre `M`, lee la bandera `b` y devuelve el estado nuevo `y` a la pila de entrada. -/
theorem ronda (b₀ b : Bool) (x y : List Bool) (t : ℕ)
    (h : Llega (TM2.step M.m) t (initList M (x.map iA.symm))
      (haltList M ((true :: b :: false :: y).map oA.symm))) :
    Llega (TM2.step (maquina M iA oA).m) (2 * y.length + t + 5)
      (cfg iA (some (Sum.inl M.main)) b₀ x) (cfg iA (bif b then some (Sum.inl M.main) else none) b y) := by
  have f1 := Componer.Llega.sim (emb (b₀, none) []) (paso iA oA (b₀, none) []) t _ _ h
  have e0 : emb (b₀, none) [] (initList M (x.map iA.symm)) = cfg iA (some (Sum.inl M.main)) b₀ x := by
    show (⟨_, _, comb M (initList M _).stk []⟩ : CC M) = _
    rw [Componer.initList_stk]
    rfl
  have e1 : emb (b₀, none) [] (haltList M ((true :: b :: false :: y).map oA.symm)) =
      (⟨some (Sum.inr 0), (M.initialState, b₀, none),
        comb M (update vacias M.k₁ (oA.symm true :: oA.symm b :: oA.symm false :: y.map oA.symm)) []⟩ : CC M) := by
    show (⟨_, _, comb M (haltList M _).stk []⟩ : CC M) = _
    rw [Componer.haltList_stk]
    rfl
  rw [e0, e1] at f1
  have f2 := bandera₁ iA oA (M.initialState, b₀, none) (oA.symm true)
    (oA.symm b :: oA.symm false :: y.map oA.symm) []
  have f3 := bandera₂ iA oA (M.initialState, b₀, none) (oA.symm b) (oA.symm false :: y.map oA.symm) []
  have f4 := bandera₃ iA oA (M.initialState, b, none) (oA.symm false) (y.map oA.symm) []
  simp only [Equiv.apply_symm_apply] at f3
  have f5 := ida iA oA M.initialState b (y.map oA.symm) (update vacias M.k₁ (y.map oA.symm)) none []
    (update_self _ _ _)
  rw [update_idem, Componer.update_vacio] at f5
  simp only [List.map_map, Equiv.self_comp_symm, List.map_id, List.append_nil] at f5
  have f6 := vuelta iA oA M.initialState b y.reverse vacias none
  simp only [List.map_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] at f6
  have := ((((f1.trans f2).trans f3).trans f4).trans f5).trans f6
  have hn : y.length + 1 + ((List.map (⇑oA.symm) y).length + 1 + (1 + (1 + (1 + t)))) =
      2 * y.length + t + 5 := by simp; omega
  rw [hn] at this
  exact this

theorem init_stk (x : List Bool) :
    (initList (maquina M iA oA) (x.map iA.symm)).stk = comb M (update vacias M.k₀ (x.map iA.symm)) [] := by
  rw [Componer.initList_stk]
  exact (congrArg (fun S => update S (Sum.inl M.k₀) (x.map iA.symm)) comb_vacio).trans (comb_update_izq _ _ _ _)

theorem halt_stk (x : List Bool) :
    (haltList (maquina M iA oA) (x.map iA.symm)).stk = comb M (update vacias M.k₀ (x.map iA.symm)) [] := by
  rw [Componer.haltList_stk]
  exact (congrArg (fun S => update S (Sum.inl M.k₀) (x.map iA.symm)) comb_vacio).trans (comb_update_izq _ _ _ _)

/-- La configuración inicial del bucle es el comienzo de una vuelta. -/
theorem init_eq (x : List Bool) :
    (initList (maquina M iA oA) (x.map iA.symm) : CC M) = cfg iA (some (Sum.inl M.main)) false x := by
  show (⟨_, _, (initList (maquina M iA oA) (x.map iA.symm)).stk⟩ : CC M) = _
  rw [init_stk]
  rfl

/-- La configuración final del bucle es el final de una vuelta con la bandera en `false`. -/
theorem halt_eq (x : List Bool) :
    (haltList (maquina M iA oA) (x.map iA.symm) : CC M) = cfg iA none false x := by
  show (⟨_, _, (haltList (maquina M iA oA) (x.map iA.symm)).stk⟩ : CC M) = _
  rw [halt_stk]
  rfl

end Vuelta

/-! ## El bucle entero -/

section Bucle

variable {α : Type} [CodBits α] (g : α → Bool × α) (iA : M.Γ M.k₀ ≃ Bool) (oA : M.Γ M.k₁ ≃ Bool)

theorem cod_par (p : Bool × α) : CodBits.cod p = true :: p.1 :: false :: CodBits.cod p.2 := rfl

omit [CodBits α] in
theorem sigue_succ (k : ℕ) (a : α) : (g ((Bucle.sigue g)^[k] a)).2 = (Bucle.sigue g)^[k + 1] a :=
  (iterate_succ_apply' (Bucle.sigue g) k a).symm

open Polynomial in
/-- **La corrida del bucle**, con su costo: a lo sumo `q · (p ∘ r + 2 r + 5)` pasos. -/
theorem corre (p q r : Polynomial ℕ)
    (hM : ∀ x : α, ∃ t ≤ p.eval (CodBits.cod x).length,
      Llega (TM2.step M.m) t (initList M ((CodBits.cod x).map iA.symm))
        (haltList M ((CodBits.cod (g x)).map oA.symm)))
    (a : α)
    (hpara : Bucle.Para g (q.eval (CodBits.cod a).length) a)
    (hlargo : ∀ k, k ≤ q.eval (CodBits.cod a).length →
      (CodBits.cod ((Bucle.sigue g)^[k] a)).length ≤ r.eval (CodBits.cod a).length) :
    ∃ N ≤ (q * (p.comp r + 2 * r + 5)).eval (CodBits.cod a).length,
      Llega (TM2.step (maquina M iA oA).m) N
        (initList (maquina M iA oA) ((CodBits.cod a).map iA.symm))
        (haltList (maquina M iA oA)
          ((CodBits.cod (Bucle.mientras g (q.eval (CodBits.cod a).length) a)).map iA.symm)) := by
  set n := (CodBits.cod a).length with hn
  set C := p.eval (r.eval n) + 2 * r.eval n + 5 with hC
  -- Una vuelta desde el estado `j`, con su costo acotado por `C`.
  have hr : ∀ j < q.eval n, ∀ b₀ : Bool, ∃ N ≤ C,
      Llega (TM2.step (maquina M iA oA).m) N
        (cfg iA (some (Sum.inl M.main)) b₀ (CodBits.cod ((Bucle.sigue g)^[j] a)))
        (cfg iA (bif (g ((Bucle.sigue g)^[j] a)).1 then some (Sum.inl M.main) else none)
          (g ((Bucle.sigue g)^[j] a)).1 (CodBits.cod ((Bucle.sigue g)^[j + 1] a))) := by
    intro j hj b₀
    obtain ⟨t, ht, h⟩ := hM ((Bucle.sigue g)^[j] a)
    rw [cod_par] at h
    have hv := ronda iA oA b₀ _ _ _ t h
    rw [sigue_succ] at hv
    refine ⟨_, ?_, hv⟩
    have h1 := hlargo j hj.le
    have h2 := hlargo (j + 1) hj
    have h3 := Componer.eval_mono p h1
    omega
  -- Las vueltas que siguen.
  have hit : ∀ k, k ≤ q.eval n → (∀ j < k, (g ((Bucle.sigue g)^[j] a)).1 = true) →
      ∃ N b', N ≤ k * C ∧ Llega (TM2.step (maquina M iA oA).m) N
        (cfg iA (some (Sum.inl M.main)) false (CodBits.cod a))
        (cfg iA (some (Sum.inl M.main)) b' (CodBits.cod ((Bucle.sigue g)^[k] a))) := by
    intro k
    induction k with
    | zero => intro _ _; exact ⟨0, false, by simp, rfl⟩
    | succ k ih =>
      intro hk hant
      obtain ⟨N, b', hN, hl⟩ := ih (by omega) (fun j hj => hant j (by omega))
      obtain ⟨N', hN', hv⟩ := hr k (by omega) b'
      rw [hant k (by omega)] at hv
      refine ⟨N' + N, true, ?_, hl.trans hv⟩
      rw [Nat.succ_mul]
      omega
  -- La primera vuelta que dice que no siga.
  classical
  have hex : ∃ k, (g ((Bucle.sigue g)^[k] a)).1 = false := by
    obtain ⟨k, _, hk⟩ := hpara
    exact ⟨k, hk⟩
  obtain ⟨k₀, hk₀, hf₀⟩ := hpara
  have hk : Nat.find hex < q.eval n := lt_of_le_of_lt (Nat.find_min' hex hf₀) hk₀
  have hfk : (g ((Bucle.sigue g)^[Nat.find hex] a)).1 = false := Nat.find_spec hex
  have hant : ∀ j < Nat.find hex, (g ((Bucle.sigue g)^[j] a)).1 = true := fun j hj => by
    simpa using Nat.find_min hex hj
  obtain ⟨N, b', hN, hl⟩ := hit (Nat.find hex) hk.le hant
  obtain ⟨N', hN', hv⟩ := hr (Nat.find hex) hk b'
  rw [hfk] at hv
  have hres : Bucle.mientras g (q.eval n) a = (Bucle.sigue g)^[Nat.find hex + 1] a :=
    Bucle.mientras_eq_de_para hfk hant hk
  rw [hres, init_eq, halt_eq]
  refine ⟨N' + N, ?_, hl.trans hv⟩
  have h1 : (Nat.find hex + 1) * C ≤ q.eval n * C := Nat.mul_le_mul_right _ hk
  simp only [eval_mul, eval_add, eval_comp, eval_ofNat]
  rw [Nat.succ_mul] at h1
  simp only [← hC]
  omega

end Bucle

/-! ## El teorema -/

open Polynomial in
/-- **La máquina del bucle, con su tiempo polinomial.** -/
noncomputable def mientrasComputable {α : Type} [CodBits α] (g : α → Bool × α)
    (hg : TM2ComputableInPolyTime (CodBits.toEncoding (α := α)).encode
      (CodBits.toEncoding (α := Bool × α)).encode g)
    (q r : Polynomial ℕ)
    (hpara : ∀ a, Bucle.Para g (q.eval (CodBits.cod a).length) a)
    (hlargo : ∀ a k, k ≤ q.eval (CodBits.cod a).length →
      (CodBits.cod ((Bucle.sigue g)^[k] a)).length ≤ r.eval (CodBits.cod a).length) :
    TM2ComputableInPolyTime (CodBits.toEncoding (α := α)).encode (CodBits.toEncoding (α := α)).encode
      (fun a => Bucle.mientras g (q.eval (CodBits.cod a).length) a) where
  tm := maquina hg.tm hg.inputAlphabet hg.outputAlphabet
  inputAlphabet := hg.inputAlphabet
  outputAlphabet := hg.inputAlphabet
  time := q * (hg.time.comp r + 2 * r + 5)
  outputsFun a := by
    have hM : ∀ x : α, ∃ t ≤ hg.time.eval (CodBits.cod x).length,
        Llega (TM2.step hg.tm.m) t (initList hg.tm ((CodBits.cod x).map hg.inputAlphabet.symm))
          (haltList hg.tm ((CodBits.cod (g x)).map hg.outputAlphabet.symm)) := fun x =>
      ⟨(hg.outputsFun x).steps, (hg.outputsFun x).steps_le_m, (hg.outputsFun x).evals_in_steps⟩
    have hc := corre g hg.inputAlphabet hg.outputAlphabet hg.time q r hM a (hpara a) (hlargo a)
    exact ⟨⟨hc.choose, hc.choose_spec.2⟩, hc.choose_spec.1⟩

/-- **El bucle «mientras» es de tiempo polinomial** si el paso lo es, si para en `q(|a|)` pasos y si los estados
intermedios miden a lo sumo `r(|a|)`. -/
theorem esPolinomial_mientras {α : Type} [CodBits α] (g : α → Bool × α) (hg : EsPolinomial g)
    (q r : Polynomial ℕ)
    (hpara : ∀ a, Bucle.Para g (q.eval (CodBits.cod a).length) a)
    (hlargo : ∀ a k, k ≤ q.eval (CodBits.cod a).length →
      (CodBits.cod ((Bucle.sigue g)^[k] a)).length ≤ r.eval (CodBits.cod a).length) :
    EsPolinomial (fun a => Bucle.mientras g (q.eval (CodBits.cod a).length) a) := by
  obtain ⟨hg⟩ := hg
  exact ⟨mientrasComputable g hg q r hpara hlargo⟩

end MientrasMaquina
end Sagitta.Map
