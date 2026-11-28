import Sagitta.Map.Cobham
import Mathlib.Tactic.DeriveCountable

/-!
# Los programas de Cobham son numerables

Lo usa la construcción del modelo saturado (`Saturacion.lean`), que recorre todos los programas en una lista
infinita. El generador automático de Mathlib no sirve aquí porque `Cob.comp` recibe una *función* de programas;
se codifica cada programa como un árbol binario de números, que sí es derivable, y se prueba que el código es
inyectivo.
-/

namespace Sagitta.Map
namespace Cobham

/-- Árboles binarios con números en las hojas. -/
inductive Bin : Type
  | hoja (k : ℕ)
  | par (a b : Bin)
  deriving Countable

/-- Una fila de `m` árboles, anidada a la derecha. -/
def lista : (m : ℕ) → (Fin m → Bin) → Bin
  | 0, _ => .hoja 0
  | m + 1, g => .par (g 0) (lista m (Fin.tail g))

theorem lista_inj : ∀ (m : ℕ) (g g' : Fin m → Bin), lista m g = lista m g' → g = g'
  | 0, _, _, _ => funext fun i => i.elim0
  | m + 1, g, g', h => by
      simp only [lista, Bin.par.injEq] at h
      have ht := lista_inj m _ _ h.2
      funext i
      refine Fin.cases h.1 (fun j => ?_) i
      exact congrFun ht j

/-- **El código de un programa.** Lleva la aridad, para poder recuperarla. -/
def toBin : {n : ℕ} → Cob n → Bin
  | n, .cero => .par (.hoja 0) (.hoja n)
  | n, .proy i => .par (.hoja 1) (.par (.hoja n) (.hoja i.val))
  | _, .suc => .par (.hoja 2) (.hoja 0)
  | _, .suma => .par (.hoja 3) (.hoja 0)
  | _, .resta => .par (.hoja 4) (.hoja 0)
  | _, .prod => .par (.hoja 5) (.hoja 0)
  | _, .mitad => .par (.hoja 6) (.hoja 0)
  | _, .largo => .par (.hoja 7) (.hoja 0)
  | _, .smash => .par (.hoja 8) (.hoja 0)
  | _, .cond => .par (.hoja 9) (.hoja 0)
  | n, .comp (m := m) f gs =>
      .par (.hoja 10) (.par (.hoja n) (.par (.hoja m) (.par (toBin f) (lista m fun i => toBin (gs i)))))
  | _, .rn (n := n) g h k => .par (.hoja 11) (.par (.hoja n) (.par (toBin g) (.par (toBin h) (toBin k))))

/-- **El código es inyectivo**, aun entre aridades distintas. -/
theorem toBin_inj {n : ℕ} (c : Cob n) :
    ∀ {n' : ℕ} (c' : Cob n'), toBin c = toBin c' → (⟨n, c⟩ : Σ n, Cob n) = ⟨n', c'⟩ := by
  induction c with
  | cero =>
    intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> try omega
    obtain ⟨-, rfl⟩ := h; rfl
  | proy i =>
    intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> try omega
    rename_i i'
    obtain ⟨-, rfl, hi⟩ := h
    rw [Fin.ext hi]
  | suc => intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> first | omega | rfl
  | suma => intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> first | omega | rfl
  | resta => intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> first | omega | rfl
  | prod => intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> first | omega | rfl
  | mitad => intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> first | omega | rfl
  | largo => intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> first | omega | rfl
  | smash => intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> first | omega | rfl
  | cond => intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> first | omega | rfl
  | comp f gs ihf ihg =>
    intro n' c' h; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at h <;> try omega
    rename_i m' f' gs'
    obtain ⟨-, rfl, rfl, hf, hg⟩ := h
    have e := ihf f' hf
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e
    subst e
    have := lista_inj _ _ _ hg
    have hgs : gs = gs' := by
      funext i
      have := ihg i (gs' i) (congrFun this i)
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using this
    subst hgs; rfl
  | rn g h k ihg ihh ihk =>
    intro n' c' e; cases c' <;> simp only [toBin, Bin.par.injEq, Bin.hoja.injEq] at e <;> try omega
    rename_i g' h' k'
    obtain ⟨-, hn, eg, eh, ek⟩ := e
    subst hn
    have e1 := ihg g' eg; have e2 := ihh h' eh; have e3 := ihk k' ek
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e1 e2 e3
    subst e1 e2 e3; rfl

instance : Countable (Σ n, Cob n) :=
  Function.Injective.countable (f := fun c : Σ n, Cob n => toBin c.2) fun a b h => by
    obtain ⟨n, c⟩ := a; obtain ⟨n', c'⟩ := b; exact toBin_inj c c' h

instance (n : ℕ) : Countable (Cob n) :=
  Function.Injective.countable (f := fun c : Cob n => (⟨n, c⟩ : Σ n, Cob n)) fun _ _ h => by
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h

end Cobham
end Sagitta.Map
