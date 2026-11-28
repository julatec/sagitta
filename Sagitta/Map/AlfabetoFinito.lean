import Sagitta.Map.Clases
import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Transfer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List

/-!
# Alfabetos finitos: la ida del puente con cslib-frontier

`Turing.FinTM2` de Mathlib solo exige finito el alfabeto de la pila de entrada. El puente de
cslib-frontier (`computableInPolyTime_iff_tm2`) pide finitos todos los alfabetos.

La observación: una máquina solo apila `f v`, con `f` escrito en el programa y `v` en el estado
interno, que es finito. Hay finitos programas (uno por etiqueta), así que los símbolos que puede
llegar a apilar son finitos. Se restringe cada alfabeto a esos símbolos (más todo el de entrada y el
de salida) y se obtiene una máquina equivalente, paso a paso.

## Qué se prueba

* `apilables_finite`: lo que un enunciado puede apilar es finito.
* `restringida`: la máquina con los alfabetos recortados.
* `proyectar_paso`: un paso de la recortada, proyectado, es un paso de la original.
* `restringir`: toda `TM2ComputableInPolyTime` tiene una con todos los alfabetos finitos,
  si el alfabeto de salida es finito (en el proyecto, `Bool`).
* `esPolinomialCon_iff`: el puente en los dos sentidos.
-/

open Computability Turing

namespace Sagitta.Map
namespace AlfabetoFinito

section Generico

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Los símbolos que un enunciado puede apilar, cada uno con su pila. -/
def apilables : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ apilables q
  | .peek _ _ q => apilables q
  | .pop _ _ q => apilables q
  | .load _ q => apilables q
  | .branch _ q₁ q₂ => apilables q₁ ∪ apilables q₂
  | .goto _ => ∅
  | .halt => ∅

/-- Con estado interno finito, un enunciado apila finitos símbolos. -/
theorem apilables_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (apilables q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek _ _ q ih => exact ih
  | pop _ _ q ih => exact ih
  | load _ q ih => exact ih
  | branch _ q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

/-- Traduce un enunciado al alfabeto recortado `A`. Pide que `A` tenga todo lo que se apila. -/
def traducir (A : ∀ k, Set (Γ k)) :
    (q : TM2.Stmt Γ Λ σ) → (∀ x ∈ apilables q, x.2 ∈ A x.1) → TM2.Stmt (fun k => ↥(A k)) Λ σ
  | .push k f q, h =>
    .push k (fun v => ⟨f v, h ⟨k, f v⟩ (Or.inl ⟨v, rfl⟩)⟩)
      (traducir A q fun x hx => h x (Or.inr hx))
  | .peek k f q, h => .peek k (fun v o => f v (o.map Subtype.val)) (traducir A q h)
  | .pop k f q, h => .pop k (fun v o => f v (o.map Subtype.val)) (traducir A q h)
  | .load f q, h => .load f (traducir A q h)
  | .branch f q₁ q₂, h =>
    .branch f (traducir A q₁ fun x hx => h x (Or.inl hx))
      (traducir A q₂ fun x hx => h x (Or.inr hx))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

/-- Olvida el recorte: cada símbolo vuelve a su alfabeto original. -/
def proyectar (A : ∀ k, Set (Γ k)) (c : TM2.Cfg (fun k => ↥(A k)) Λ σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l, c.var, fun k => (c.stk k).map Subtype.val⟩

/-- Proyectar no pierde información. -/
theorem proyectar_injective (A : ∀ k, Set (Γ k)) : Function.Injective (proyectar A (Λ := Λ) (σ := σ)) := by
  rintro ⟨l, v, S⟩ ⟨l', v', S'⟩ h
  simp only [proyectar, TM2.Cfg.mk.injEq] at h
  obtain ⟨rfl, rfl, hS⟩ := h
  congr
  funext k
  exact (List.map_injective_iff.2 Subtype.val_injective) (congrFun hS k)

variable [DecidableEq K]

/-- **Un tramo de enunciado**: la recortada y la original hacen lo mismo, salvo la proyección. -/
theorem proyectar_stepAux (A : ∀ k, Set (Γ k)) (q : TM2.Stmt Γ Λ σ) (h) (v : σ)
    (S : ∀ k, List (A k)) :
    proyectar A (TM2.stepAux (traducir A q h) v S) =
      TM2.stepAux q v (fun k => (S k).map Subtype.val) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [traducir, TM2.stepAux, ih]
    congr 1
    funext k'
    rw [Function.apply_update (fun k (l : List (A k)) => l.map Subtype.val)]
    rfl
  | peek k f q ih =>
    simp only [traducir, TM2.stepAux, List.head?_map]
    exact ih h _ _
  | pop k f q ih =>
    simp only [traducir, TM2.stepAux, List.head?_map]
    rw [ih h]
    congr 1
    funext k'
    rw [Function.apply_update (fun k (l : List (A k)) => l.map Subtype.val)]
    simp [List.map_tail]
  | load f q ih =>
    simp only [traducir, TM2.stepAux]
    exact ih h _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [traducir, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

/-- **Un paso**: proyectar conmuta con el paso de la máquina. -/
theorem proyectar_paso (A : ∀ k, Set (Γ k)) (m : Λ → TM2.Stmt Γ Λ σ)
    (h : ∀ l, ∀ x ∈ apilables (m l), x.2 ∈ A x.1) (c : TM2.Cfg (fun k => ↥(A k)) Λ σ) :
    TM2.step m (proyectar A c) =
      (TM2.step (fun l => traducir A (m l) (h l)) c).map (proyectar A) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · simp only [proyectar, TM2.step, Option.map_some]
    exact congrArg some (proyectar_stepAux A (m l) (h l) v S).symm

/-- **Muchos pasos**: la proyección de la corrida recortada es la corrida original. -/
theorem proyectar_iterar (A : ∀ k, Set (Γ k)) (m : Λ → TM2.Stmt Γ Λ σ)
    (h : ∀ l, ∀ x ∈ apilables (m l), x.2 ∈ A x.1) (n : ℕ) (c : Option (TM2.Cfg (fun k => ↥(A k)) Λ σ)) :
    (flip bind (TM2.step m))^[n] (c.map (proyectar A)) =
      ((flip bind (TM2.step (fun l => traducir A (m l) (h l))))^[n] c).map (proyectar A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rcases (flip bind (TM2.step (fun l => traducir A (m l) (h l))))^[n] c with _ | c'
    · rfl
    · simp only [flip, Option.map_some]
      exact proyectar_paso A m h c'

end Generico

/-! ## La máquina recortada -/

section Maquina

variable (tm : FinTM2)

/-- Lo que la máquina conserva en la pila `k`: lo que algún programa apila, y todo si `k` es la pila
de entrada o la de salida. -/
def alcance (k : tm.K) : Set (tm.Γ k) :=
  {g | (⟨k, g⟩ : Σ k, tm.Γ k) ∈ ⋃ l, apilables (tm.m l) ∨ k = tm.k₀ ∨ k = tm.k₁}

theorem apilables_sub (l : tm.Λ) : ∀ x ∈ apilables (tm.m l), x.2 ∈ alcance tm x.1 :=
  fun _ hx => Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩)

/-- **La máquina recortada**: mismas pilas, etiquetas y estado; cada alfabeto, su alcance. -/
noncomputable def restringida : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ k := ↥(alcance tm k)
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := @Fintype.ofFinite _ (@Subtype.finite _ (@Finite.of_fintype _ tm.Γk₀Fin) _)
  m l := traducir (alcance tm) (tm.m l) (apilables_sub tm l)

/-- **Todos los alfabetos de la recortada son finitos**, si el de salida lo es. -/
theorem restringida_finite [Finite (tm.Γ tm.k₁)] (k : (restringida tm).K) :
    Finite ((restringida tm).Γ k) := by
  change Finite ↥(alcance tm k)
  have := tm.Γk₀Fin
  by_cases h₀ : k = tm.k₀
  · subst h₀; exact Subtype.finite
  by_cases h₁ : k = tm.k₁
  · subst h₁; exact Subtype.finite
  have := tm.σFin
  have := tm.ΛFin
  have hU : (⋃ l, apilables (tm.m l)).Finite := Set.finite_iUnion fun l => apilables_finite _
  have hpre := hU.preimage (f := fun g : tm.Γ k => (⟨k, g⟩ : Σ k, tm.Γ k))
    (sigma_mk_injective.injOn)
  refine Set.Finite.to_subtype (hpre.subset ?_)
  rintro g (hg | hg | hg)
  · exact hg
  · exact absurd hg h₀
  · exact absurd hg h₁

/-- Todo símbolo de la pila de entrada está en el alcance. -/
theorem mem_alcance_k₀ (g : tm.Γ tm.k₀) : g ∈ alcance tm tm.k₀ := Or.inr (Or.inl rfl)

/-- Todo símbolo de la pila de salida está en el alcance. -/
theorem mem_alcance_k₁ (g : tm.Γ tm.k₁) : g ∈ alcance tm tm.k₁ := Or.inr (Or.inr rfl)

/-- La configuración inicial, proyectada. -/
theorem proyectar_initList (s : List ((restringida tm).Γ (restringida tm).k₀)) :
    proyectar (alcance tm) (initList (restringida tm) s) = initList tm (s.map Subtype.val) := by
  simp only [proyectar, initList]
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h
    simp [restringida]
    rfl
  · simp [restringida, h]

/-- La configuración final, proyectada. -/
theorem proyectar_haltList (s : List ((restringida tm).Γ (restringida tm).k₁)) :
    proyectar (alcance tm) (haltList (restringida tm) s) = haltList tm (s.map Subtype.val) := by
  simp only [proyectar, haltList]
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h
    simp [restringida]
    rfl
  · simp [restringida, h]

/-- **La corrida recortada llega donde la original**, en los mismos pasos. -/
theorem iterar_restringida {s : List ((restringida tm).Γ (restringida tm).k₀)}
    {s' : List ((restringida tm).Γ (restringida tm).k₁)} (n : ℕ)
    (e : (flip bind (TM2.step tm.m))^[n] (some (initList tm (s.map Subtype.val))) =
      some (haltList tm (s'.map Subtype.val))) :
    (flip bind (restringida tm).step)^[n] (some (initList (restringida tm) s)) =
      some (haltList (restringida tm) s') := by
  have hit := proyectar_iterar (alcance tm) tm.m (apilables_sub tm) n
    (some (initList (restringida tm) s))
  have e2 : Option.map (proyectar (alcance tm))
      ((flip bind (TM2.step fun l => traducir (alcance tm) (tm.m l) (apilables_sub tm l)))^[n]
        (some (initList (restringida tm) s))) =
      Option.map (proyectar (alcance tm)) (some (haltList (restringida tm) s')) := by
    have h1 : Option.map (proyectar (alcance tm)) (some (initList (restringida tm) s)) =
        some (initList tm (s.map Subtype.val)) := congrArg some (proyectar_initList tm s)
    have h2 : Option.map (proyectar (alcance tm)) (some (haltList (restringida tm) s')) =
        some (haltList tm (s'.map Subtype.val)) := congrArg some (proyectar_haltList tm s')
    exact hit.symm.trans ((congrArg (flip bind (TM2.step tm.m))^[n] h1).trans (e.trans h2.symm))
  exact Option.map_injective (proyectar_injective _) e2

/-- **La recortada corre igual que la original**, en los mismos pasos. -/
noncomputable def outputsInTime_restringida {s : List ((restringida tm).Γ (restringida tm).k₀)}
    {s' : List ((restringida tm).Γ (restringida tm).k₁)} {t : ℕ}
    (h : TM2OutputsInTime tm (s.map Subtype.val) (some (s'.map Subtype.val)) t) :
    TM2OutputsInTime (restringida tm) s (some s') t where
  steps := h.steps
  steps_le_m := h.steps_le_m
  evals_in_steps := iterar_restringida tm h.steps h.evals_in_steps

end Maquina

/-! ## La restricción de una máquina polinomial -/

variable {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}

/-- **Meta 1**: toda máquina polinomial de Mathlib tiene una equivalente con todos los alfabetos
finitos, si el alfabeto de salida es finito. -/
theorem restringir [Finite βΓ] (h : TM2ComputableInPolyTime ea eb f) :
    ∃ h' : TM2ComputableInPolyTime ea eb f, ∀ k, Finite (h'.tm.Γ k) := by
  have : Finite (h.tm.Γ h.tm.k₁) := Finite.of_equiv _ h.outputAlphabet.symm
  let ia : (restringida h.tm).Γ (restringida h.tm).k₀ ≃ αΓ :=
    (Equiv.subtypeUnivEquiv (mem_alcance_k₀ h.tm)).trans h.inputAlphabet
  let oa : (restringida h.tm).Γ (restringida h.tm).k₁ ≃ βΓ :=
    (Equiv.subtypeUnivEquiv (mem_alcance_k₁ h.tm)).trans h.outputAlphabet
  refine ⟨⟨⟨restringida h.tm, ia, oa⟩, h.time, fun a => outputsInTime_restringida h.tm ?_⟩,
    restringida_finite h.tm⟩
  have hi : ∀ l : List αΓ, (l.map ia.invFun).map Subtype.val = l.map h.inputAlphabet.invFun := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => exact congrArg₂ List.cons rfl ih
  have ho : ∀ l : List βΓ, (l.map oa.invFun).map Subtype.val = l.map h.outputAlphabet.invFun := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => exact congrArg₂ List.cons rfl ih
  have := h.outputsFun a
  rw [← hi, ← ho] at this
  exact this

/-! ## El puente en los dos sentidos -/

open Turing.MultiTapeTM

/-- Una codificación de Mathlib en bits, vista como incrustación (lo que pide cslib-frontier). -/
def incrustar {γ : Type} (e : Encoding γ Bool) : γ ↪ List Bool := ⟨e.encode, e.encode_injective⟩

/-- **Meta 2**: polinomial en Mathlib es lo mismo que polinomial en las máquinas multicinta de
cslib-frontier, con las mismas codificaciones. -/
theorem esPolinomialCon_iff {ea : Encoding α Bool} {eb : Encoding β Bool} :
    EsPolinomialCon ea eb f ↔ ComputableInPolyTime f (incrustar ea) (incrustar eb) := by
  rw [computableInPolyTime_iff_tm2]
  constructor
  · rintro ⟨h⟩
    exact restringir h
  · rintro ⟨h, -⟩
    exact ⟨h⟩

/-- La forma con las codificaciones canónicas. -/
theorem esPolinomial_iff [CodBits α] [CodBits β] :
    EsPolinomial f ↔ ComputableInPolyTime f (incrustar (CodBits.toEncoding (α := α)))
      (incrustar (CodBits.toEncoding (α := β))) :=
  esPolinomialCon_iff

/-! ## P ⊆ NP ∩ coNP -/

/-- `delimita` de `Codificacion` es `frame` de cslib-frontier. -/
theorem delimita_eq_frame (l : List Bool) : CodBits.delimita l = frame l := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [CodBits.delimita, ih, frame_cons]

theorem incrustar_bits : incrustar (CodBits.toEncoding (α := List Bool)) = encBits :=
  Function.Embedding.ext fun _ => rfl

theorem incrustar_bool : incrustar (CodBits.toEncoding (α := Bool)) = encBool :=
  Function.Embedding.ext fun _ => rfl

/-- **Los pares de `CodBits` son los `encPair` de cslib-frontier.** -/
theorem incrustar_par : incrustar (CodBits.toEncoding (α := List Bool × List Bool)) =
    encPair encBits encBits :=
  Function.Embedding.ext fun p => by
    change CodBits.delimita p.1 ++ p.2 = frame p.1 ++ p.2
    rw [delimita_eq_frame]

/-- Un problema de P, leído en la Mathlib, es polinomial en cslib-frontier. -/
theorem computable_of_mem_P {L : Problema} (h : L ∈ P) : ComputableInPolyTime L encBits encBool := by
  have := esPolinomial_iff.mp h
  rwa [incrustar_bits, incrustar_bool] at this

theorem mem_P_of_computable {L : Problema} (h : ComputableInPolyTime L encBits encBool) : L ∈ P := by
  change EsPolinomial L
  rw [esPolinomial_iff, incrustar_bits, incrustar_bool]
  exact h

/-- **P ⊆ NP**: el verificador ignora el certificado. -/
theorem pSubNP : PSubNP := by
  intro L hL
  have hV : ComputableInPolyTime (fun p : List Bool × List Bool => L p.1) (encPair encBits encBits)
      encBool := (computable_of_mem_P hL).comp (ComputableInPolyTime.fst encBits encBits)
  refine ⟨0, fun p => L p.1, ?_, fun x => ⟨fun hx => ⟨[], by simp, hx⟩, fun ⟨_, _, hy⟩ => hy⟩⟩
  show EsPolinomial _
  rw [esPolinomial_iff, incrustar_par, incrustar_bool]
  exact hV

/-- P es cerrada bajo complemento. -/
theorem compl_mem_P {L : Problema} (h : L ∈ P) : (fun x => !L x) ∈ P :=
  mem_P_of_computable (ComputableInPolyTime.bool_not.comp (computable_of_mem_P h))

/-- **P ⊆ coNP.** -/
theorem pSubCoNP : P ⊆ coNP := fun _ hL => pSubNP (compl_mem_P hL)

/-- **P ⊆ NP ∩ coNP.** -/
theorem pSubNPInterCoNP : P ⊆ NP ∩ coNP := fun _ hL => ⟨pSubNP hL, pSubCoNP hL⟩

/-- Las dos formas de P = NP dicen lo mismo, ahora sin hipótesis. -/
theorem pIgualNP_iff_verificarImplicaResolver' : PIgualNP ↔ VerificarImplicaResolver :=
  pIgualNP_iff_verificarImplicaResolver pSubNP

/-! ## Controles -/

/-- La hipótesis de `restringir` se cumple: la máquina identidad de Mathlib en `Bool`. -/
example : ∃ h' : TM2ComputableInPolyTime (CodBits.cod (α := Bool)) (CodBits.cod (α := Bool)) id,
    ∀ k, Finite (h'.tm.Γ k) :=
  restringir (Turing.idComputableInPolyTime _)

/-- P no es vacía: la constante `true` está, y entonces en NP y en coNP. -/
example : (fun _ : List Bool => true) ∈ NP ∩ coNP :=
  pSubNPInterCoNP (mem_P_of_computable (ComputableInPolyTime.const true))

/-- `delimita` y `frame` coinciden en un ejemplo. -/
example : CodBits.delimita [true, false] = frame [true, false] := by decide

example : CodBits.delimita [true, false] = [true, true, true, false, false] := by decide

/-- Una máquina con una pila de trabajo de alfabeto `ℕ` (infinito): solo apila `7`.
Sirve para ver que el recorte hace trabajo; la identidad de arriba ya era finita. -/
def tmInf : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ k := if k then ℕ else Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ := TM2.Stmt.push true (fun _ => (7 : ℕ)) TM2.Stmt.halt

instance : Finite (tmInf.Γ tmInf.k₁) := inferInstanceAs (Finite Bool)

/-- El alfabeto original de la pila de trabajo es infinito. -/
example : ¬ Finite (tmInf.Γ true) := fun h => (Infinite.not_finite (α := ℕ)) h

/-- El recortado es finito. -/
example : Finite ((restringida tmInf).Γ true) := restringida_finite tmInf true

/-- El alcance no es vacío: contiene el `7` que la máquina apila. -/
example : (7 : ℕ) ∈ (alcance tmInf true : Set ℕ) :=
  Or.inl (Set.mem_iUnion.2 ⟨(), Or.inl ⟨(), rfl⟩⟩)

end AlfabetoFinito
end Sagitta.Map
