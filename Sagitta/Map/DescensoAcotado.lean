import Sagitta.Map.DescensoCreciente

/-!
# Crecimiento polinomial: el ordinal vuelve a colapsar

Queda una pregunta: si el estado puede crecer, pero solo polinomialmente, ¿un costo en un
orden bien fundado vuelve a reducirse a un natural? Hay dos maneras de pedir «crecimiento polinomial», y en las dos
la respuesta es sí.

**Atribución.** Esto es un ejercicio, no un resultado. El teorema de verdad es de Beckmann, Buss y Pollett,
«Ordinal notations and well-orderings in bounded arithmetic», Ann. Pure Appl. Logic 120 (2003) 197–223: el costo de
PLS puede tomar valores ordinales por debajo de `Γ₀` sin agrandar la clase. Llega muchísimo más lejos que `ω²` y se
prueba dentro de la aritmética acotada (`T¹₂`, `S²₂`). Lo de aquí es el caso más pequeño, por una cuenta directa.

1. **Por conteo, sin instancia** (`colapsa_por_conteo`). Si desde cualquier estado `s` la trayectoria nunca pasa de
   largo `q(|s|)`, entonces «los pasos que faltan» es un costo natural con los mismos óptimos, y vale menos de
   `2^(2·q(|s|) + 1)`. Es el mismo enunciado que `Creciente.no_colapsa`, con la respuesta contraria: lo que decide
   es el crecimiento. Ese costo existe, pero no se dice cómo calcularlo rápido.
2. **Con instancia, como en PLS** (`BusquedaOmega2.a_naturales`). Si cada instancia `x` acota el largo de sus
   soluciones, y la segunda coordenada del costo queda por debajo de `B(|x|)`, el costo `a·B(|x|) + b` da los mismos
   óptimos. Si el costo es polinomial, `B = 2^r(|x|)` sirve y el nuevo costo también es polinomial (esa parte, en
   prosa). Es la forma en que se plantean los problemas de `TFNP`, así que ahí el costo en `ω²` no sale de PLS.
-/

namespace Sagitta.Map
namespace Acotado

open Classical

/-! ## 1. Por conteo -/

section Conteo

variable {α : Type} [LinearOrder α] [WellFoundedLT α] (c : List Bool → α) (v : List Bool → List Bool)

/-- Un óptimo local. -/
def EsOptimo (s : List Bool) : Prop := c s ≤ c (v s)

/-- Los pasos que faltan para el primer óptimo. Existe por la buena fundación. -/
noncomputable def pasos (s : List Bool) : ℕ := Nat.find (Creciente.termina_gen c v s)

theorem pasos_optimo {s : List Bool} (h : EsOptimo c v s) : pasos c v s = 0 :=
  (Nat.find_eq_zero _).mpr h

theorem pasos_no_optimo {s : List Bool} (h : ¬ EsOptimo c v s) : pasos c v s = pasos c v (v s) + 1 := by
  unfold pasos
  rw [Nat.find_comp_succ (Creciente.termina_gen c v s) (Creciente.termina_gen c v (v s)) h]
  rfl

/-- «Los pasos que faltan» tiene los mismos óptimos. -/
theorem pasos_mismos_optimos (s : List Bool) : pasos c v s ≤ pasos c v (v s) ↔ EsOptimo c v s := by
  by_cases h : EsOptimo c v s
  · simp [pasos_optimo c v h, h]
  · rw [pasos_no_optimo c v h]
    simp [h]

/-- Antes del primer óptimo, el costo baja estrictamente. -/
theorem costo_baja (s : List Bool) {i j : ℕ} (hij : i < j) (hj : j ≤ pasos c v s) :
    c (v^[j] s) < c (v^[i] s) := by
  replace hj : j ≤ Nat.find (Creciente.termina_gen c v s) := hj
  induction j, hij using Nat.le_induction with
  | base =>
    have hno : ¬ EsOptimo c v (v^[i] s) := Nat.find_min (Creciente.termina_gen c v s) (by omega)
    rw [Function.iterate_succ_apply']
    exact not_le.mp hno
  | succ j hij ih =>
    have hno : ¬ EsOptimo c v (v^[j] s) := Nat.find_min (Creciente.termina_gen c v s) (by omega)
    rw [Function.iterate_succ_apply']
    exact lt_trans (not_le.mp hno) (ih (by omega))

/-- **El conteo.** Si la trayectoria desde `s` no pasa de largo `L`, faltan menos de `(L + 1)·2^L` pasos: los
estados de la trayectoria son distintos y caben en las cadenas de largo `≤ L`. -/
theorem pasos_lt (s : List Bool) (L : ℕ) (hL : ∀ k, (v^[k] s).length ≤ L) :
    pasos c v s < (L + 1) * 2 ^ L := by
  set m := pasos c v s
  let f : Fin (m + 1) → Fin (L + 1) × (Fin L → Bool) :=
    fun i => (⟨(v^[i] s).length, by have := hL i; omega⟩, fun k => (v^[i] s).getD k false)
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f, Prod.mk.injEq, Fin.mk.injEq] at hij
    obtain ⟨hlen, hget⟩ := hij
    have hst : v^[i.val] s = v^[j.val] s := by
      apply List.ext_getElem hlen
      intro k hk₁ hk₂
      have := congrFun hget ⟨k, by have := hL i; omega⟩
      simpa [List.getElem?_eq_getElem hk₁, List.getElem?_eq_getElem hk₂] using this
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · have := costo_baja c v s h (by omega)
      rw [hst] at this
      exact lt_irrefl _ this
    · have := costo_baja c v s h (by omega)
      rw [hst] at this
      exact lt_irrefl _ this
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool] at this
  omega

/-- **Colapsa por conteo.** Si desde todo estado `s` la trayectoria no pasa de largo `q(|s|)`, hay un costo natural
con los mismos óptimos y menor que `2^(2·q(|s|) + 1)`. Compárese con `Creciente.no_colapsa`. -/
theorem colapsa_por_conteo (q : ℕ → ℕ) (hq : ∀ s k, (v^[k] s).length ≤ q s.length) :
    ∃ c' : List Bool → ℕ, (∀ s, c' s < 2 ^ (2 * q s.length + 1)) ∧
      (∀ s, c' s ≤ c' (v s) ↔ EsOptimo c v s) := by
  refine ⟨pasos c v, fun s => ?_, pasos_mismos_optimos c v⟩
  have h1 := pasos_lt c v s (q s.length) (hq s)
  have h2 : q s.length + 1 ≤ 2 ^ (q s.length + 1) := (Nat.lt_two_pow_self).le
  calc pasos c v s < (q s.length + 1) * 2 ^ q s.length := h1
    _ ≤ 2 ^ (q s.length + 1) * 2 ^ q s.length := Nat.mul_le_mul_right _ h2
    _ = 2 ^ (2 * q s.length + 1) := by rw [← pow_add]; congr 1; ring

end Conteo

/-! ## 2. Con instancia, como en PLS -/

/-- Una búsqueda local con costo en `ω²` y una instancia: el vecino y el costo ven la instancia `x`. La segunda
coordenada del costo de una solución factible queda por debajo de `B(|x|)`. -/
structure BusquedaOmega2 where
  factible : List Bool × List Bool → Bool
  vecino : List Bool × List Bool → List Bool
  costo : List Bool × List Bool → Omega2
  vecino_factible : ∀ x s, factible (x, s) = true → factible (x, vecino (x, s)) = true
  B : ℕ → ℕ
  acotada : ∀ x s, factible (x, s) = true → (ofLex (costo (x, s))).2 < B x.length

namespace BusquedaOmega2

variable (P : BusquedaOmega2)

/-- El costo natural: `a·B(|x|) + b`. -/
def costoNat (q : List Bool × List Bool) : ℕ :=
  (ofLex (P.costo q)).1 * P.B q.1.length + (ofLex (P.costo q)).2

/-- **Con instancia, ω² colapsa.** Para cada solución factible, el costo natural compara igual que el ordinal: los
óptimos son los mismos. -/
theorem a_naturales (x s : List Bool) (hs : P.factible (x, s) = true) :
    P.costoNat (x, s) ≤ P.costoNat (x, P.vecino (x, s)) ↔ P.costo (x, s) ≤ P.costo (x, P.vecino (x, s)) := by
  unfold costoNat
  rw [mul_add_le_iff (P.acotada x s hs) (P.acotada x _ (P.vecino_factible x s hs)), Prod.Lex.le_iff]

end BusquedaOmega2

end Acotado
end Sagitta.Map
