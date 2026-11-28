import Sagitta.Map.Consumo
import Sagitta.Map.RaizMuertaFuerte

/-!
# Medir los árboles que vienen de problemas de NP: el detector parte Ω

`Consumo.lean` midió el árbol **completo**: el tiempo paga la masa de Ω, `2ⁿ`, y la memoria, `n + 1`. Un problema de NP
no obliga a recorrerlo entero: la vuelta atrás de `ArbolElecciones.lean` (`buscar`) poda donde el detector dice
«muerto». Aquí se mide lo que de veras recorre, con las dos medidas de `Consumo.lean`, cuando la raíz está muerta (el
caso `x ∉ L`, el que obliga a mirar todo: no hay solución que la detenga antes).

## El detector parte Ω en cilindros

Los lugares donde la búsqueda se detiene (`cortes`) son prefijos `q`, y cada uno es un **cilindro** de Ω: todas las ramas
que empiezan por `q`. Con `N` variables, el cilindro de `q` pesa `2^(N − |q|)`.

* **Son una partición de Ω** (`kraft`, `cortes_cubren`): las masas suman exactamente `2^k` (la igualdad de Kraft) y toda
  rama cae en alguno.
* **Cada pieza está certificada** (`cortes_certificados`): el detector la declaró muerta, o es una hoja.
* **La búsqueda paga por pieza, no por masa** (`nodos_piezas`): con la raíz muerta, `nodos + 1 = 2 · piezas`.
  El tiempo es la medida de **conteo de piezas**, no la de conteo de ramas.
* **La memoria no cambia** (`espacio_podado_le`): podar o no, la pila no pasa de `k + 1`. Lo que un detector ahorra es
  solo tiempo (en árbol, `NP ⊆ PSPACE` no depende del detector).

## El atajo, dicho con medida

Un detector polinomial que diera atajo partiría Ω, una masa `2ⁿ`, en un número **polinomial** de cilindros certificados.
Los dos extremos (`cortes_nunca`, `cortes_perfecto`): sin detector, `2ᵏ` piezas de masa 1; con detector perfecto, una pieza
de masa `2ᵏ`. Y lo de en medio:

* **Si las piezas son chicas, son muchas** (`piezas_de_masa_acotada`): si ninguna pesa más de `2^d`, hay al menos
  `2^(k−d)`. Es la demora de `DemoraEfectiva.lean`, dicha con la medida: un detector que solo mata cerca de las hojas no da
  atajo.
* **El palomar no se parte en pocas piezas** (`palomar_piezas`): con el detector «hay una cláusula falsa», en cualquier
  orden de las variables, las piezas son más de `(n + 1 − h)^h / 4`. Es `palomar_nodos` de `RaizMuerta.lean` (la cota de
  Beyersdorff, Galesi y Lauria vía cslib-frontier) pasada por `nodos_piezas`.

## Lo que no

Solo la raíz muerta. Con la raíz viva la búsqueda se detiene al encontrar y los cortes no cubren Ω; ese costo ya está en
`costo_vivoN`. Y que **ningún** detector polinomial parta Ω en pocas piezas para SAT es otra vez P ≠ NP.
-/

namespace Sagitta.Map
namespace Consumo

open Tiempo Cslib.Logic.PL

namespace Arbol

/-- Las hojas del árbol. -/
def hojas : Arbol → ℕ
  | hoja => 1
  | nodo l r => hojas l + hojas r

/-- En un árbol binario, el tiempo de recorrerlo es dos veces las hojas, menos uno. -/
theorem tiempo_hojas (t : Arbol) : tiempo t + 1 = 2 * hojas t := by
  induction t with
  | hoja => rfl
  | nodo l r ihl ihr => simp only [tiempo_nodo, hojas]; omega

end Arbol

variable (sol det : List Bool → Bool)

/-- El árbol que recorre la vuelta atrás cuando nada la detiene: poda donde el detector dice «muerto». -/
def podado : ℕ → List Bool → Arbol
  | 0, _ => .hoja
  | k + 1, p => if det p = true then .hoja else .nodo (podado k (p ++ [false])) (podado k (p ++ [true]))

/-- Los cortes: los prefijos donde la búsqueda se detiene. Cada uno es un cilindro de Ω. -/
def cortes : ℕ → List Bool → List (List Bool)
  | 0, p => [p]
  | k + 1, p => if det p = true then [p] else cortes k (p ++ [false]) ++ cortes k (p ++ [true])

/-! ## La búsqueda con la raíz muerta recorre el árbol podado -/

theorem no_vivo_hijo {k : ℕ} {p : List Bool} (hm : ¬ Vivo sol (k + 1) p) (b : Bool) :
    ¬ Vivo sol k (p ++ [b]) := fun h => hm ((vivo_succ sol k p).2 (by cases b <;> simp [h]))

/-- Con la raíz muerta, la vuelta atrás visita exactamente los nodos del árbol podado. -/
theorem nodos_eq_tiempo : ∀ (k : ℕ) (p : List Bool), ¬ Vivo sol k p →
    nodos sol det k p = (podado det k p).tiempo
  | 0, p, _ => by by_cases hd : det p = true <;> simp [nodos, buscar, podado, hd]
  | k + 1, p, hm => by
    by_cases hd : det p = true
    · simp [nodos, buscar, podado, hd]
    · have hf : (buscar sol det k (p ++ [false])).1 = false := by
        cases h : (buscar sol det k (p ++ [false])).1
        · rfl
        · exact absurd (buscar_vivo sol det k _ h) (no_vivo_hijo sol hm false)
      have e0 := nodos_eq_tiempo k (p ++ [false]) (no_vivo_hijo sol hm false)
      have e1 := nodos_eq_tiempo k (p ++ [true]) (no_vivo_hijo sol hm true)
      simp only [nodos] at e0 e1
      simp only [nodos, buscar, hd, hf, podado, Bool.false_eq_true, ite_false, Arbol.tiempo_nodo, e0, e1]
      omega

theorem length_cortes : ∀ (k : ℕ) (p : List Bool), (cortes det k p).length = (podado det k p).hojas
  | 0, _ => rfl
  | k + 1, p => by
    by_cases hd : det p = true
    · simp [cortes, podado, hd, Arbol.hojas]
    · simp [cortes, podado, hd, Arbol.hojas, length_cortes k]

/-- **Se paga por pieza, no por masa.** Con la raíz muerta, `nodos + 1 = 2 · piezas`. -/
theorem nodos_piezas {k : ℕ} {p : List Bool} (hm : ¬ Vivo sol k p) :
    nodos sol det k p + 1 = 2 * (cortes det k p).length := by
  rw [nodos_eq_tiempo sol det k p hm, length_cortes, Arbol.tiempo_hojas]

/-- **La memoria no cambia**: con o sin poda, la pila no pasa de `k + 1`. -/
theorem espacio_podado_le : ∀ (k : ℕ) (p : List Bool), (podado det k p).espacio ≤ k + 1
  | 0, _ => le_rfl
  | k + 1, p => by
    by_cases hd : det p = true
    · simp [podado, hd]
    · have h0 := espacio_podado_le k (p ++ [false])
      have h1 := espacio_podado_le k (p ++ [true])
      simp only [podado, hd, Bool.false_eq_true, ite_false, Arbol.espacio_nodo]
      omega

/-! ## Los cortes son una partición certificada de Ω -/

/-- Cada corte extiende al nodo de partida, y no pasa de las `k` variables. -/
theorem cortes_prefijo : ∀ (k : ℕ) (p q : List Bool), q ∈ cortes det k p →
    p <+: q ∧ q.length ≤ p.length + k
  | 0, p, q, h => by simp [cortes] at h; subst h; simp
  | k + 1, p, q, h => by
    by_cases hd : det p = true
    · simp [cortes, hd] at h; subst h; simp
    · simp only [cortes, hd, Bool.false_eq_true, ite_false, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨h1, h2⟩ := cortes_prefijo k _ q h
        exact ⟨(List.prefix_append p [false]).trans h1, by simp at h2; omega⟩
      · obtain ⟨h1, h2⟩ := cortes_prefijo k _ q h
        exact ⟨(List.prefix_append p [true]).trans h1, by simp at h2; omega⟩

/-- **Cada pieza está certificada**: el detector la declaró muerta, o es una hoja. -/
theorem cortes_certificados : ∀ (k : ℕ) (p q : List Bool), q ∈ cortes det k p →
    det q = true ∨ q.length = p.length + k
  | 0, p, q, h => by simp [cortes] at h; subst h; simp
  | k + 1, p, q, h => by
    by_cases hd : det p = true
    · simp [cortes, hd] at h; subst h; exact Or.inl hd
    · simp only [cortes, hd, Bool.false_eq_true, ite_false, List.mem_append] at h
      rcases h with h | h <;>
      · rcases cortes_certificados k _ q h with h' | h'
        · exact Or.inl h'
        · right; simp at h'; omega

/-- **Cubren Ω**: toda rama de largo `k` cae en algún cilindro de corte. -/
theorem cortes_cubren : ∀ (k : ℕ) (p w : List Bool), w.length = k →
    ∃ q ∈ cortes det k p, q <+: p ++ w
  | 0, p, w, hw => ⟨p, by simp [cortes], List.prefix_append _ _⟩
  | k + 1, p, w, hw => by
    by_cases hd : det p = true
    · exact ⟨p, by simp [cortes, hd], List.prefix_append _ _⟩
    · obtain ⟨b, w', rfl⟩ : ∃ b w', w = b :: w' := by
        cases w with
        | nil => simp at hw
        | cons b w' => exact ⟨b, w', rfl⟩
      obtain ⟨q, hq, hpre⟩ := cortes_cubren k (p ++ [b]) w' (by simpa using hw)
      refine ⟨q, ?_, by simpa using hpre⟩
      simp only [cortes, hd, Bool.false_eq_true, ite_false, List.mem_append]
      cases b
      · exact Or.inl hq
      · exact Or.inr hq

/-- **La igualdad de Kraft**: las masas de los cilindros de corte suman la masa de Ω. -/
theorem kraft : ∀ (k : ℕ) (p : List Bool),
    ((cortes det k p).map fun q => 2 ^ (p.length + k - q.length)).sum = 2 ^ k
  | 0, p => by simp [cortes]
  | k + 1, p => by
    by_cases hd : det p = true
    · simp [cortes, hd]
    · have h0 := kraft k (p ++ [false])
      have h1 := kraft k (p ++ [true])
      simp only [List.length_append, List.length_singleton] at h0 h1
      simp only [cortes, hd, Bool.false_eq_true, ite_false, List.map_append, List.sum_append]
      rw [show p.length + (k + 1) = p.length + 1 + k by omega, h0, h1, pow_succ]
      ring

/-! ## Los extremos y lo de en medio -/

/-- Sin detector: `2ᵏ` piezas, cada una de masa 1. -/
theorem cortes_nunca : ∀ (k : ℕ) (p : List Bool), (cortes nunca k p).length = 2 ^ k
  | 0, _ => rfl
  | k + 1, p => by simp [cortes, nunca, cortes_nunca k, pow_succ]; ring

/-- Con detector perfecto en la raíz: una pieza, toda la masa. -/
theorem cortes_perfecto {k : ℕ} {p : List Bool} (hd : det p = true) : cortes det (k + 1) p = [p] := by
  simp [cortes, hd]

/-- **Si las piezas son chicas, son muchas**: si ninguna pesa más de `2^d`, hay al menos `2^k / 2^d`. -/
theorem piezas_de_masa_acotada {k d : ℕ} {p : List Bool}
    (hd : ∀ q ∈ cortes det k p, p.length + k - q.length ≤ d) :
    2 ^ k ≤ (cortes det k p).length * 2 ^ d := by
  rw [← kraft det k p]
  calc ((cortes det k p).map fun q => 2 ^ (p.length + k - q.length)).sum
      ≤ ((cortes det k p).map fun _ => 2 ^ d).sum :=
        List.sum_le_sum fun q hq => Nat.pow_le_pow_right (by norm_num) (hd q hq)
    _ = (cortes det k p).length * 2 ^ d := by simp

/-- **El palomar no se parte en pocas piezas**: con el detector «hay una cláusula falsa», en cualquier orden inyectivo
de las variables, `(n + 1 − h)^h < 4 · piezas`. -/
theorem palomar_piezas {m n : ℕ} (h : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    (n + 1 - h) ^ h < 4 * (cortes (detCNF ((CNF.pigeonhole m n).relabel f)) N []).length := by
  have hlow := palomar_nodos h hnm hn hf hN
  have hunsat : ¬ CNF.Satisfiable (((CNF.pigeonhole m n).relabel f : List Clausula) : CNF ℕ) := by
    rw [CNF.satisfiable_relabel hf]; exact CNF.not_satisfiable_pigeonhole hnm
  have := nodos_piezas _ (detCNF ((CNF.pigeonhole m n).relabel f)) (raiz_muerta hunsat N)
  omega

/-! ## Controles -/

/-- La CNF `x₀ ∧ ¬x₀` con dos variables: el detector la mata en cuanto fija `x₀`. Dos piezas de masa 2. -/
example : cortes (detCNF [[(0, true)], [(0, false)]]) 2 [] = [[false], [true]] := by decide

example : nodos (solCNF [[(0, true)], [(0, false)]]) (detCNF [[(0, true)], [(0, false)]]) 2 [] = 3 := by decide

end Consumo
end Sagitta.Map
