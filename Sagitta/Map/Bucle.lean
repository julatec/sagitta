import Sagitta.Map.Clases

/-!
# El bucle «mientras», como función

Un paso `g a = (b, a')` dice si hay que seguir (`b`) y cuál es el estado nuevo (`a'`). `mientras g n a` corre a lo
sumo `n` pasos: si el paso dice que no siga, devuelve el estado que el paso dejó; si se acaba el combustible,
devuelve el estado que tiene.

`MientrasMaquina.lean` construye la máquina de Turing que lo corre, y prueba que es de tiempo polinomial si el paso lo
es, si el bucle para en un número polinomial de pasos y si los estados intermedios no crecen más que un polinomio.
Este archivo solo trae la función y sus propiedades.
-/

namespace Sagitta.Map
namespace Bucle

variable {α : Type}

/-- El estado que deja un paso. -/
def sigue (g : α → Bool × α) (a : α) : α := (g a).2

/-- **El bucle**, con a lo sumo `n` pasos. -/
def mientras (g : α → Bool × α) : ℕ → α → α
  | 0, a => a
  | n + 1, a => if (g a).1 then mientras g n (g a).2 else (g a).2

/-- **El bucle para en a lo sumo `n` pasos desde `a`**: entre los primeros `n` pasos hay uno que dice que no siga. -/
def Para (g : α → Bool × α) (n : ℕ) (a : α) : Prop :=
  ∃ k < n, (g ((sigue g)^[k] a)).1 = false

theorem mientras_succ (g : α → Bool × α) (n : ℕ) (a : α) :
    mientras g (n + 1) a = if (g a).1 then mientras g n (g a).2 else (g a).2 := rfl

theorem para_succ {g : α → Bool × α} {n : ℕ} {a : α} (h : Para g (n + 1) a) (hb : (g a).1 = true) :
    Para g n (g a).2 := by
  obtain ⟨k, hk, hf⟩ := h
  cases k with
  | zero => simp [hb] at hf
  | succ k =>
    refine ⟨k, by omega, ?_⟩
    rwa [Function.iterate_succ_apply] at hf

/-- Con combustible de sobra, el resultado no depende de cuánto sobra. -/
theorem mientras_estable {g : α → Bool × α} :
    ∀ {n m : ℕ} {a : α}, Para g n a → n ≤ m → mientras g m a = mientras g n a
  | 0, _, _, h, _ => by obtain ⟨k, hk, _⟩ := h; omega
  | n + 1, m, a, h, hnm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [mientras_succ, mientras_succ]
    by_cases hb : (g a).1 = true
    · simp only [hb, ↓reduceIte]
      exact mientras_estable (para_succ h hb) (by omega)
    · simp [hb]

/-- Si el bucle para en `n` pasos, el resultado es el estado que deja el primer paso que dice que no siga. -/
theorem mientras_eq_de_para {g : α → Bool × α} {n : ℕ} {a : α} {k : ℕ}
    (hk : (g ((sigue g)^[k] a)).1 = false) (hantes : ∀ j < k, (g ((sigue g)^[j] a)).1 = true) (hkn : k < n) :
    mientras g n a = (sigue g)^[k + 1] a := by
  induction k generalizing n a with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Function.iterate_zero, id] at hk
    simp [mientras_succ, hk, sigue]
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h0 : (g a).1 = true := by simpa using hantes 0 (by omega)
    rw [mientras_succ, ite_eq_left h0, Function.iterate_succ_apply]
    refine ih (by rwa [Function.iterate_succ_apply] at hk) (fun j hj => ?_) (by omega)
    have := hantes (j + 1) (by omega)
    rwa [Function.iterate_succ_apply] at this

end Bucle
end Sagitta.Map
