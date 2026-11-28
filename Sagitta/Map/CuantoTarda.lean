import Sagitta.Map.PLSConcreto

/-!
# Cuánto tarda el algoritmo estándar

Johnson, Papadimitriou y Yannakakis (1988, p. 83) observan que el algoritmo estándar siempre termina, pero que
para muchos problemas tarda un tiempo exponencial, y que la prueba de su lema 1 «contiene un ejemplo». Aquí están
las dos mitades, sobre los descensos de este proyecto:

1. **Cota superior** (`pasos_exponencial`). Si el costo se calcula en tiempo polinomial, la ruta tarda menos de
   `2^q(n)` pasos, con `q` un polinomio. La ruta no tarda más que el costo inicial (`pasos_le_costo`), y un número
   que una máquina escribe en tiempo polinomial tiene un número polinomial de bits (`valor_exponencial`).
2. **El ejemplo** (`pasos_sin_certificado`). En el descenso exhaustivo, si no hay certificado, la ruta recorre todas
   las cadenas permitidas: exactamente `2^(M + 1) − 2` pasos, donde `M` es la cota del largo.

Así, «exponencial» es la respuesta exacta: nunca más, y a veces eso.
-/

open Computability Turing

namespace Sagitta.Map
namespace CuantoTarda

open Comparar (val val_encodeNat)
open Componer (Llega)
open Enumera

/-! ## 1. La cota superior -/

theorem val_lt : ∀ l : List Bool, val l < 2 ^ l.length
  | [] => by simp [val]
  | b :: l => by
    have := val_lt l
    simp only [val, List.length_cons, pow_succ]
    split_ifs <;> omega

open Polynomial in
/-- **Un número calculado en tiempo polinomial es a lo sumo exponencial.** La máquina escribe a lo sumo un número
fijo de símbolos por paso, así que el resultado tiene un número polinomial de bits. -/
theorem valor_exponencial {α : Type} [CodBits α] {f : α → ℕ} (hf : EsPolinomial f) :
    ∃ q : Polynomial ℕ, ∀ a, f a < 2 ^ q.eval (CodBits.cod a).length := by
  obtain ⟨hf⟩ := hf
  refine ⟨X + C (Componer.maxPushTM hf.tm) * hf.time, fun a => ?_⟩
  have h := hf.outputsFun a
  have l₁ : Llega (TM2.step hf.tm.m) h.steps
      (initList hf.tm (List.map hf.inputAlphabet.invFun (CodBits.cod a)))
      (haltList hf.tm (List.map hf.outputAlphabet.invFun (encodeNat (f a)))) := h.evals_in_steps
  have hcrece := Componer.crece hf.tm hf.tm.k₁ _ _ _ l₁
  rw [Componer.haltList_stk, Function.update_self, Componer.initList_stk] at hcrece
  have hini := Componer.length_update_le (fun _ => [] : ∀ k, List (hf.tm.Γ k)) hf.tm.k₀
    (List.map hf.inputAlphabet.invFun (CodBits.cod a)) (CodBits.cod a).length (by simp) hf.tm.k₁
  simp only [List.length_nil, zero_add, List.length_map] at hini hcrece
  have hval : f a < 2 ^ (encodeNat (f a)).length := by
    have := val_lt (encodeNat (f a))
    rwa [val_encodeNat] at this
  have ht : h.steps ≤ hf.time.eval (CodBits.cod a).length := h.steps_le_m
  have hmul := Nat.mul_le_mul_right (Componer.maxPushTM hf.tm) ht
  refine lt_of_lt_of_le hval (Nat.pow_le_pow_right (by norm_num) ?_)
  simp only [eval_add, eval_mul, eval_C, eval_X]
  rw [Nat.mul_comm (Componer.maxPushTM hf.tm)]
  omega

/-- **El algoritmo estándar tarda a lo sumo un tiempo exponencial.** Para un descenso con costo polinomial, la ruta
tarda menos de `2^q(…)` pasos, con `q` un polinomio en el largo de la instancia y de su solución inicial. -/
theorem pasos_exponencial (D : DescensoInstancia) (hc : EsPolinomial D.costo) :
    ∃ q : Polynomial ℕ, ∀ x, D.pasos x < 2 ^ q.eval (2 * x.length + 1 + (D.inicial x).length) := by
  obtain ⟨q, hq⟩ := valor_exponencial hc
  refine ⟨q, fun x => ?_⟩
  have h := hq (x, D.inicial x)
  have hlen : (CodBits.cod (x, D.inicial x)).length = 2 * x.length + 1 + (D.inicial x).length := by
    show (CodBits.delimita x ++ D.inicial x).length = _
    rw [List.length_append, Basicas.delimita_length]
  rw [hlen] at h
  exact lt_of_le_of_lt (D.pasos_le_costo x) h

/-! ## 2. El ejemplo exponencial -/

/-- **Sin certificado, la ruta recorre todo.** El descenso exhaustivo tarda exactamente `2^(M + 1) − 2` pasos: una
por cada cadena de largo a lo sumo `M`, menos la primera. -/
theorem pasos_sin_certificado (V : List Bool × List Bool → Bool) (M : List Bool → ℕ) (x : List Bool)
    (hno : ∀ y : List Bool, y.length ≤ M x → V (x, y) = false) :
    (exhaustivo V M).pasos x = 2 ^ (M x + 1) - 2 := by
  have hdos : 2 ≤ 2 ^ (M x + 1) := by
    have := Nat.one_le_two_pow (n := M x)
    rw [pow_succ]
    omega
  -- Hasta la última, todas las cadenas tienen largo permitido.
  have hlargo : ∀ j ≤ 2 ^ (M x + 1) - 2, (sig^[j] ([] : List Bool)).length ≤ M x := by
    intro j hj
    have h1 := (num_cotas (sig^[j] ([] : List Bool))).1
    rw [num_iter] at h1
    have h2 : 2 ^ (sig^[j] ([] : List Bool)).length < 2 ^ (M x + 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega
  -- La ruta coincide con la lista.
  have hruta : ∀ j ≤ 2 ^ (M x + 1) - 2, (exhaustivo V M).ruta x j = sig^[j] [] := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [DescensoInstancia.ruta_succ, ih (by omega)]
      show (if V (x, sig^[j] []) = true ∨ M x < (sig (sig^[j] [])).length then _ else _) = _
      have hV : ¬ V (x, sig^[j] []) = true := by
        rw [hno _ (hlargo j (by omega))]
        simp
      have hl := hlargo (j + 1) hj
      rw [Function.iterate_succ_apply'] at hl
      rw [ite_eq_right (by push Not; exact ⟨hV, hl⟩), Function.iterate_succ_apply']
  apply DescensoInstancia.pasos_eq
  · rw [hruta _ le_rfl, exhaustivo_esOptimo_iff]
    right
    have h1 := (num_cotas (sig (sig^[2 ^ (M x + 1) - 2] ([] : List Bool)))).2
    rw [num_sig, num_iter] at h1
    have h2 : 2 ^ (M x + 1) < 2 ^ ((sig (sig^[2 ^ (M x + 1) - 2] ([] : List Bool))).length + 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega
  · intro j hj
    rw [hruta j hj.le, exhaustivo_esOptimo_iff]
    have hV : ¬ V (x, sig^[j] []) = true := by
      rw [hno _ (hlargo j hj.le)]
      simp
    have hl := hlargo (j + 1) hj
    rw [Function.iterate_succ_apply'] at hl
    push Not
    exact ⟨hV, hl⟩

end CuantoTarda
end Sagitta.Map
