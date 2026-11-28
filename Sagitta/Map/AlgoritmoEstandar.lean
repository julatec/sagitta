import Sagitta.Map.BusquedaNP
import Sagitta.Map.DescensoCreciente

/-!
# El problema del algoritmo estándar

PLS pide *cualquier* óptimo local. El **problema del algoritmo estándar** pide uno en particular: el óptimo al que
llega la ruta que sale de la solución inicial y sigue al vecino. Aquí se define, y se prueba que la búsqueda de un
certificado de NP se reduce a él.

1. **La definición** (`DescensoInstancia.destino`, `AlgoritmoEstandar`). Para un descenso con instancia, el destino
   de `x` es el primer óptimo de la ruta. Es una función: existe y es único. Para un problema de PLS, el destino es
   una de sus soluciones (`ProblemaPLS.destino_esSolucion`): el problema del algoritmo estándar refina a PLS.

2. **La reducción** (`hay_certificado_iff`). Dado un verificador `V` y una cota `M` del largo de los certificados, el
   descenso `exhaustivo V M` recorre las cadenas por largo y, dentro de cada largo, en orden. Su destino es un
   certificado **si y solo si existe alguno**. Así, para todo `L` de NP: `x ∈ L` si y solo si `V` acepta el destino
   (`np_por_destino`).

El descenso `exhaustivo` es explícito y calculable (los `#guard` lo corren). Que su costo y su vecino son de tiempo
polinomial es cierto (sumar uno, comparar, llamar a `V`), pero no se prueba aquí, como en el resto del proyecto. Sin
esa restricción el teorema sería trivial (bastaría poner la respuesta en la solución inicial); por eso importa que
el descenso sea este, concreto, y no uno cualquiera.

**Atribución.** El problema del algoritmo estándar y la reducción de esta sección son de Johnson, Papadimitriou y
Yannakakis, «How easy is local search?», J. Comput. Syst. Sci. 37 (1988) 79–100: la definición está en la p. 83, y
el lema 1 (pp. 83–84) dice que hay un problema de PLS cuyo problema del algoritmo estándar es NP-difícil, con esta
misma construcción (recorrer las asignaciones en orden, con costo cero en las que satisfacen). Lo de aquí es su
formalización, no un resultado nuevo. Cotejado contra el PDF del artículo el 23 nov 2026.

Con `BusquedaNP.lean` queda el contraste: como problema de PLS (cualquier óptimo), la búsqueda de NP no se puede
codificar salvo que NP ⊆ coNP; como problema del algoritmo estándar (el óptimo de la ruta), sí.
-/

namespace Sagitta.Map

/-! ## 1. La definición -/

/-- Un descenso con instancia, sin exigir nada del tiempo: solución inicial, vecino y costo natural. -/
structure DescensoInstancia where
  inicial : List Bool → List Bool
  vecino : List Bool × List Bool → List Bool
  costo : List Bool × List Bool → ℕ

namespace DescensoInstancia

variable (D : DescensoInstancia)

/-- Un paso, para la instancia `x`. -/
def paso (x s : List Bool) : List Bool := D.vecino (x, s)

/-- La ruta: el estado después de `k` pasos desde la solución inicial. -/
def ruta (x : List Bool) (k : ℕ) : List Bool := (D.paso x)^[k] (D.inicial x)

/-- Un óptimo local. -/
def EsOptimo (x s : List Bool) : Prop := D.costo (x, s) ≤ D.costo (x, D.vecino (x, s))

instance (x s : List Bool) : Decidable (D.EsOptimo x s) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem ruta_succ (x : List Bool) (k : ℕ) : D.ruta x (k + 1) = D.vecino (x, D.ruta x k) :=
  Function.iterate_succ_apply' _ _ _

/-- La ruta llega a un óptimo, por la buena fundación de `ℕ`. -/
theorem termina (x : List Bool) : ∃ k, D.EsOptimo x (D.ruta x k) := by
  obtain ⟨k, -, h⟩ := Creciente.desciende_gen (fun s => D.costo (x, s)) (D.paso x) (D.inicial x)
  exact ⟨k, h⟩

/-- Cuántos pasos tarda la ruta en llegar a su primer óptimo. -/
def pasos (x : List Bool) : ℕ := Nat.find (D.termina x)

/-- **El destino**: el primer óptimo de la ruta. -/
def destino (x : List Bool) : List Bool := D.ruta x (D.pasos x)

theorem destino_esOptimo (x : List Bool) : D.EsOptimo x (D.destino x) := Nat.find_spec (D.termina x)

/-- Si la ruta llega a un óptimo en el paso `k` y a ninguno antes, tarda exactamente `k` pasos. -/
theorem pasos_eq {x : List Bool} {k : ℕ} (h : D.EsOptimo x (D.ruta x k))
    (hmin : ∀ j < k, ¬ D.EsOptimo x (D.ruta x j)) : D.pasos x = k :=
  (Nat.find_eq_iff (D.termina x)).mpr ⟨h, hmin⟩

/-- El destino es el primer óptimo: si la ruta llega a un óptimo en el paso `k` y a ninguno antes, es ese. -/
theorem destino_eq {x : List Bool} {k : ℕ} (h : D.EsOptimo x (D.ruta x k))
    (hmin : ∀ j < k, ¬ D.EsOptimo x (D.ruta x j)) : D.destino x = D.ruta x k := by
  unfold destino
  rw [D.pasos_eq h hmin]

/-- **La ruta no tarda más que el costo inicial.** Es la cota del algoritmo estándar: cada paso que no se detiene
baja el costo. -/
theorem pasos_le_costo (x : List Bool) : D.pasos x ≤ D.costo (x, D.inicial x) := by
  obtain ⟨k, hk, h⟩ := Creciente.desciende_gen (fun s => D.costo (x, s)) (D.paso x) (D.inicial x)
  exact le_trans (Nat.find_min' (D.termina x) h) hk

/-- **El problema del algoritmo estándar**: dada `x`, hallar el destino de su ruta. -/
def AlgoritmoEstandar : Busqueda := fun x y => y = D.destino x

end DescensoInstancia

/-- El descenso de un problema de PLS. -/
def ProblemaPLS.aDescenso (P : ProblemaPLS) : DescensoInstancia := ⟨P.inicial, P.vecino, P.costo⟩

/-- **El algoritmo estándar refina a PLS**: el destino es una solución del problema de PLS. -/
theorem ProblemaPLS.destino_esSolucion (P : ProblemaPLS) (x : List Bool) :
    P.EsSolucion x (P.aDescenso.destino x) := by
  have hfact : ∀ k, P.factible (x, P.aDescenso.ruta x k) = true := by
    intro k
    induction k with
    | zero => exact P.inicial_factible x
    | succ k ih => rw [DescensoInstancia.ruta_succ]; exact P.vecino_factible x _ ih
  exact ⟨hfact _, P.aDescenso.destino_esOptimo x⟩

/-! ## 2. Enumerar las cadenas -/

namespace Enumera

/-- La cadena siguiente: por largo y, dentro de cada largo, en orden (el primer bit es el menos significativo).
`[]`, `[0]`, `[1]`, `[0,0]`, `[1,0]`, `[0,1]`, `[1,1]`, `[0,0,0]`, … -/
def sig : List Bool → List Bool
  | [] => [false]
  | false :: bs => true :: bs
  | true :: bs => false :: sig bs

/-- La posición de una cadena en esa lista. -/
def num : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2 else 1) + 2 * num bs

#guard (List.range 8).map (fun k => sig^[k] []) =
  [[], [false], [true], [false, false], [true, false], [false, true], [true, true], [false, false, false]]

theorem num_sig : ∀ l : List Bool, num (sig l) = num l + 1
  | [] => rfl
  | false :: bs => by simp only [sig, num, Bool.false_eq_true, ↓reduceIte]; omega
  | true :: bs => by simp only [sig, num, num_sig bs, Bool.false_eq_true, ↓reduceIte]; omega

theorem num_iter (k : ℕ) : num (sig^[k] []) = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', num_sig, ih]

/-- La posición determina el largo: `2^largo ≤ posición + 1 < 2^(largo + 1)`. -/
theorem num_cotas : ∀ l : List Bool, 2 ^ l.length ≤ num l + 1 ∧ num l + 1 < 2 ^ (l.length + 1)
  | [] => by simp [num]
  | b :: bs => by
    have := num_cotas bs
    simp only [num, List.length_cons, pow_succ] at this ⊢
    split_ifs <;> omega

theorem length_le_of_num_le {a b : List Bool} (h : num a ≤ num b) : a.length ≤ b.length := by
  have ha := (num_cotas a).1
  have hb := (num_cotas b).2
  have : 2 ^ a.length < 2 ^ (b.length + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
  omega

theorem num_inj : ∀ a b : List Bool, num a = num b → a = b
  | [], [], _ => rfl
  | [], b :: bs, h => by simp only [num] at h; split_ifs at h <;> omega
  | a :: as, [], h => by simp only [num] at h; split_ifs at h <;> omega
  | a :: as, b :: bs, h => by
    simp only [num] at h
    have : a = b ∧ num as = num bs := by cases a <;> cases b <;> simp at h ⊢ <;> omega
    rw [this.1, num_inj as bs this.2]

/-- Toda cadena aparece en la lista, en su posición. -/
theorem sig_iter_num (y : List Bool) : sig^[num y] [] = y := num_inj _ _ (num_iter _)

end Enumera

/-! ## 3. La reducción -/

open Enumera
open Comparar (val)

/-! ### El costo, como cadena de bits

El costo del descenso exhaustivo no se define con una fórmula sino con una cadena: el complemento de la cadena
actual, un cero, tantos unos como le falten para llegar a la cota, y un uno. Leída como número (bit menos
significativo primero) vale `2^(k+2) − 2 − posición`, que baja en uno con cada cadena. Una máquina la escribe sin
hacer ninguna cuenta: complementa, y rellena comparando largos. -/

/-- Los bits del costo de la cadena `s`, con cota de largo `k`. -/
def costoBits (k : ℕ) (s : List Bool) : List Bool :=
  s.map not ++ false :: (List.replicate (k - s.length) true ++ [true])

theorem val_append : ∀ a b : List Bool, val (a ++ b) = val a + 2 ^ a.length * val b
  | [], b => by simp [val]
  | c :: a, b => by
    simp only [List.cons_append, val, val_append a b, List.length_cons, pow_succ]
    ring

theorem val_map_not : ∀ s : List Bool, val (s.map not) + val s + 1 = 2 ^ s.length
  | [] => by simp [val]
  | c :: s => by
    have := val_map_not s
    cases c <;> simp only [List.map_cons, val, List.length_cons, pow_succ, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte] <;> omega

theorem val_unos : ∀ j : ℕ, val (List.replicate j true) + 1 = 2 ^ j
  | 0 => by simp [val]
  | j + 1 => by
    have := val_unos j
    simp only [List.replicate_succ, val, ↓reduceIte, pow_succ]
    omega

/-- La posición de una cadena y su valor en binario: `posición + 1 = valor + 2^largo`. -/
theorem num_eq_val : ∀ s : List Bool, num s + 1 = val s + 2 ^ s.length
  | [] => by simp [num, val]
  | c :: s => by
    have := num_eq_val s
    cases c <;> simp only [num, val, List.length_cons, pow_succ, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- **El costo, en cuentas.** Para una cadena de largo permitido, el costo más su posición da siempre lo mismo. -/
theorem val_costoBits {k : ℕ} {s : List Bool} (h : s.length ≤ k) :
    val (costoBits k s) + num s + 2 = 2 ^ (k + 2) := by
  have h1 := val_map_not s
  have h2 := num_eq_val s
  have h3 := val_unos (k - s.length + 1)
  have h4 : val (false :: (List.replicate (k - s.length) true ++ [true])) + 2 = 2 ^ (k - s.length + 2) := by
    have : List.replicate (k - s.length) true ++ [true] = List.replicate (k - s.length + 1) true := by
      rw [List.replicate_succ']
    rw [val, this]
    simp only [Bool.false_eq_true, ↓reduceIte, pow_succ] at h3 ⊢
    omega
  have h5 : 2 ^ s.length * 2 ^ (k - s.length + 2) = 2 ^ (k + 2) := by
    rw [← pow_add]
    congr 1
    omega
  unfold costoBits
  rw [val_append, List.length_map]
  have h6 : 2 ^ s.length * (val (false :: (List.replicate (k - s.length) true ++ [true])) + 2) =
      2 ^ (k + 2) := by rw [h4, h5]
  rw [Nat.mul_add] at h6
  omega

/-- **El descenso exhaustivo** de un verificador `V`, con certificados de largo a lo sumo `M x`: empieza en la
cadena vacía y pasa a la siguiente, hasta dar con un certificado o agotar los largos permitidos. El costo es el
número que escribe `costoBits`: baja en uno con cada cadena, y no mira a `V`. -/
def exhaustivo (V : List Bool × List Bool → Bool) (M : List Bool → ℕ) : DescensoInstancia where
  inicial _ := []
  vecino q := if V q = true ∨ M q.1 < (sig q.2).length then q.2 else sig q.2
  costo q := val (costoBits (M q.1) q.2)

-- Con el certificado `[1, 0, 1]` y largo a lo sumo 3, el destino es ese certificado.
#guard (exhaustivo (fun q => q.2 == [true, false, true]) (fun _ => 3)).destino [] = [true, false, true]
-- Sin certificado, el destino es la última cadena permitida: no es un certificado.
#guard (exhaustivo (fun _ => false) (fun _ => 3)).destino [] = [true, true, true]

section Reduccion

variable (V : List Bool × List Bool → Bool) (M : List Bool → ℕ)

theorem exhaustivo_esOptimo_iff (x s : List Bool) :
    (exhaustivo V M).EsOptimo x s ↔ (V (x, s) = true ∨ M x < (sig s).length) := by
  unfold DescensoInstancia.EsOptimo
  show val (costoBits (M x) s) ≤
      val (costoBits (M x) (if V (x, s) = true ∨ M x < (sig s).length then s else sig s)) ↔ _
  by_cases h : V (x, s) = true ∨ M x < (sig s).length
  · rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => le_refl _⟩
  · rw [ite_eq_right h]
    refine ⟨fun hle => absurd hle ?_, fun h' => absurd h' h⟩
    push Not at h
    obtain ⟨-, hlen⟩ := h
    have hss : s.length ≤ (sig s).length := length_le_of_num_le (by rw [num_sig]; omega)
    have c1 := val_costoBits (k := M x) (s := s) (by omega)
    have c2 := val_costoBits (k := M x) (s := sig s) hlen
    rw [num_sig] at c2
    omega

/-- La ruta nunca pasa del largo permitido. -/
theorem exhaustivo_ruta_largo (x : List Bool) :
    ∀ k, ((exhaustivo V M).ruta x k).length ≤ M x := by
  intro k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [DescensoInstancia.ruta_succ]
    show (if V (x, _) = true ∨ M x < (sig _).length then _ else sig _).length ≤ _
    split_ifs with h
    · exact ih
    · push Not at h
      exact h.2

/-- **La reducción.** Hay un certificado de largo permitido si y solo si el destino del descenso exhaustivo es un
certificado. -/
theorem hay_certificado_iff (x : List Bool) :
    (∃ y : List Bool, y.length ≤ M x ∧ V (x, y) = true) ↔
      V (x, (exhaustivo V M).destino x) = true := by
  constructor
  · rintro ⟨y, hy, hVy⟩
    -- El primer certificado de la lista.
    have hex : ∃ k, V (x, sig^[k] []) = true := ⟨num y, by rw [sig_iter_num]; exact hVy⟩
    have hk₀ := Nat.find_spec hex
    have hle : Nat.find hex ≤ num y := Nat.find_min' hex (by rw [sig_iter_num]; exact hVy)
    -- Hasta ahí, todas las cadenas tienen largo permitido.
    have hlargo : ∀ j ≤ Nat.find hex, (sig^[j] ([] : List Bool)).length ≤ M x := by
      intro j hj
      have : num (sig^[j] ([] : List Bool)) ≤ num y := by rw [num_iter]; omega
      exact le_trans (length_le_of_num_le this) hy
    -- Y la ruta del descenso coincide con la lista.
    have hruta : ∀ j ≤ Nat.find hex, (exhaustivo V M).ruta x j = sig^[j] [] := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        rw [DescensoInstancia.ruta_succ, ih (by omega)]
        show (if V (x, sig^[j] []) = true ∨ M x < (sig (sig^[j] [])).length then _ else _) = _
        have hno : ¬ V (x, sig^[j] []) = true := Nat.find_min hex (by omega)
        have hl := hlargo (j + 1) hj
        rw [Function.iterate_succ_apply'] at hl
        rw [ite_eq_right (by push Not; exact ⟨hno, hl⟩), Function.iterate_succ_apply']
    have hdest : (exhaustivo V M).destino x = sig^[Nat.find hex] [] := by
      rw [← hruta _ le_rfl]
      apply DescensoInstancia.destino_eq
      · rw [hruta _ le_rfl, exhaustivo_esOptimo_iff]
        exact Or.inl hk₀
      · intro j hj
        rw [hruta j hj.le, exhaustivo_esOptimo_iff]
        have hno : ¬ V (x, sig^[j] []) = true := Nat.find_min hex hj
        have hl := hlargo (j + 1) hj
        rw [Function.iterate_succ_apply'] at hl
        push Not
        exact ⟨hno, hl⟩
    rw [hdest]
    exact hk₀
  · intro h
    exact ⟨_, exhaustivo_ruta_largo V M x _, h⟩

end Reduccion

/-- **NP por el algoritmo estándar.** Si `L` tiene verificador `V` con certificados de largo a lo sumo `p(|x|)`,
entonces `x ∈ L` si y solo si `V` acepta el destino del descenso exhaustivo. Decidir `L` se reduce a hallar ese
destino. -/
theorem np_por_destino {L : Problema} {p : Polynomial ℕ} {V : List Bool × List Bool → Bool}
    (hL : ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true) (x : List Bool) :
    L x = true ↔ V (x, (exhaustivo V (fun x => p.eval x.length)).destino x) = true := by
  rw [hL x]
  exact hay_certificado_iff V (fun x => p.eval x.length) x

end Sagitta.Map
