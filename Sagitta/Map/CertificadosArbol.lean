import Sagitta.Map.Clases
import Sagitta.Map.ArbolElecciones

/-!
# Los certificados de NP como árbol de elecciones (A1)

Primer paso de «lo angélico con tope `p(|x|)`» sobre las máquinas de `Clases.lean`. Allí NP va por verificadores: `L ∈ NP`
si hay un polinomio `p` y un verificador polinomial `V` con `L x = true ↔ ∃ y, |y| ≤ p(|x|) ∧ V (x, y) = true`. Aquí ese
«existe un certificado» se lee como la raíz viva del árbol de elecciones de `ArbolElecciones.lean`.

## Lo que se prueba

* **Un certificado es un prefijo** (`solCert`): las hojas del árbol tienen largo exacto `p(|x|)`, y NP pide largo a lo
  sumo `p(|x|)`. La solución en una hoja es «algún prefijo suyo es certificado».
* **NP es la raíz viva** (`vivo_solCert_iff`, `np_iff_raiz_viva`): `x` está en `L` si y solo si la raíz del árbol de
  profundidad `p(|x|)` está viva. Es lo angélico de `FormaDelTiempo.lean` sobre la NP de `Clases.lean`.
* **La búsqueda decide** (`buscar_decide_np`): la vuelta atrás sobre ese árbol responde `L x`, con cualquier detector sano.
* **El tope** (`nodos_le_arbol`, `nodos_np_le`): visita a lo sumo `2^(p(|x|)+1) − 1` nodos, y en cada hoja evalúa el
  verificador en a lo sumo `p(|x|) + 1` prefijos. Sin detector y con `x ∉ L`, los visita todos (`nodos_np_no`).

## Lo que no

Esto cuenta evaluaciones del verificador, no pasos de una máquina. Llevarlo a las máquinas TM2 de `Clases.lean` (que la
búsqueda con un detector de demora `O(log n)` sea `EsPolinomial`) es la fase A4.
-/

namespace Sagitta.Map
namespace Tiempo

/-- **La solución en el árbol de certificados**: algún prefijo de la hoja es certificado de `x`. -/
def solCert (V : List Bool × List Bool → Bool) (x : List Bool) (q : List Bool) : Bool :=
  (List.range (q.length + 1)).any fun j => V (x, q.take j)

/-- **La raíz está viva si y solo si hay un certificado de largo a lo sumo `K`.** -/
theorem vivo_solCert_iff (V : List Bool × List Bool → Bool) (x : List Bool) (K : ℕ) :
    Vivo (solCert V x) K [] ↔ ∃ y : List Bool, y.length ≤ K ∧ V (x, y) = true := by
  constructor
  · rintro ⟨q, hq, hs⟩
    simp only [List.nil_append, solCert, List.any_eq_true, List.mem_range] at hs
    obtain ⟨j, hj, hv⟩ := hs
    exact ⟨q.take j, by simp [List.length_take]; omega, hv⟩
  · rintro ⟨y, hy, hv⟩
    refine ⟨y ++ List.replicate (K - y.length) false, by simp; omega, ?_⟩
    simp only [List.nil_append, solCert, List.any_eq_true, List.mem_range]
    exact ⟨y.length, by simp; omega, by simpa using hv⟩

/-- **NP es la raíz viva.** Para `L ∈ NP` hay un polinomio y un verificador polinomial tales que `x ∈ L` si y solo si la
raíz del árbol de certificados de profundidad `p(|x|)` está viva. -/
theorem np_iff_raiz_viva {L : Problema} (hL : L ∈ NP) :
    ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool), EsPolinomial V ∧
      ∀ x, L x = true ↔ Vivo (solCert V x) (p.eval x.length) [] := by
  obtain ⟨p, V, hV, h⟩ := hL
  exact ⟨p, V, hV, fun x => (h x).trans (vivo_solCert_iff V x _).symm⟩

/-- **La búsqueda decide**: con cualquier detector sano, la vuelta atrás sobre el árbol de certificados responde `L x`. -/
theorem buscar_decide_np {L : Problema} {p : Polynomial ℕ} {V : List Bool × List Bool → Bool}
    (h : ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true)
    {det : List Bool → Bool} (x : List Bool) (hs : Sano (solCert V x) det) :
    (buscar (solCert V x) det (p.eval x.length) []).1 = L x := by
  have hb := buscar_correcto hs (p.eval x.length) []
  rw [vivo_solCert_iff, ← h x] at hb
  cases hL : L x <;> cases hc : (buscar (solCert V x) det (p.eval x.length) []).1 <;> simp_all

/-! ## El tope -/

/-- **Ninguna búsqueda visita más que el árbol entero**: `2^(k+1) − 1` nodos, con cualquier detector. -/
theorem nodos_le_arbol (sol det : List Bool → Bool) : ∀ (k : ℕ) (p : List Bool), nodos sol det k p + 1 ≤ 2 ^ (k + 1)
  | 0, p => by unfold nodos buscar; split <;> simp
  | k + 1, p => by
    have h0 := nodos_le_arbol sol det k (p ++ [false])
    have h1 := nodos_le_arbol sol det k (p ++ [true])
    unfold nodos at h0 h1 ⊢
    rw [pow_succ]
    unfold buscar
    split
    · have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      simp only; omega
    · split <;> simp only <;> omega

/-- **El tope para NP**: la búsqueda sobre el árbol de certificados visita a lo sumo `2^(p(|x|)+1) − 1` nodos. -/
theorem nodos_np_le (V : List Bool × List Bool → Bool) (det : List Bool → Bool) (x : List Bool) (p : Polynomial ℕ) :
    nodos (solCert V x) det (p.eval x.length) [] + 1 ≤ 2 ^ (p.eval x.length + 1) :=
  nodos_le_arbol _ _ _ _

/-- **Sin detector, si `x ∉ L` se visita todo el árbol**: `2^(p(|x|)+1) − 1` nodos exactos. -/
theorem nodos_np_no {L : Problema} {p : Polynomial ℕ} {V : List Bool × List Bool → Bool}
    (h : ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true)
    (x : List Bool) (hx : L x = false) :
    nodos (solCert V x) nunca (p.eval x.length) [] + 1 = 2 ^ (p.eval x.length + 1) := by
  refine sin_detector_muerto _ _ [] fun hv => ?_
  rw [vivo_solCert_iff, ← h x, hx] at hv
  exact Bool.false_ne_true hv

/-- **En cada hoja, a lo sumo `K + 1` evaluaciones del verificador**: los prefijos de largo `0` a `K`. -/
theorem evaluaciones_por_hoja (V : List Bool × List Bool → Bool) (x q : List Bool) :
    ((List.range (q.length + 1)).map fun j => V (x, q.take j)).length = q.length + 1 := by
  simp

/-! ## Controles -/

/-- Un verificador de juguete: el certificado es `[true, true]`. -/
def verifJuguete (p : List Bool × List Bool) : Bool := p.2 == [true, true]

/-- Con profundidad 3, la raíz está viva: la hoja `[true, true, false]` tiene el certificado como prefijo. -/
example : solCert verifJuguete [] [true, true, false] = true := by decide

/-- Con profundidad 1 no cabe el certificado, y la búsqueda a ciegas recorre los 3 nodos. -/
example : (buscar (solCert verifJuguete []) nunca 1 []).1 = false ∧ nodos (solCert verifJuguete []) nunca 1 [] = 3 := by
  decide

end Tiempo
end Sagitta.Map
