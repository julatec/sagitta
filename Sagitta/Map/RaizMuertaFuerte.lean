import Sagitta.Map.RaizMuerta
import Sagitta.Map.DemoraEfectiva

/-!
# La raíz muerta con detectores más fuertes

`RaizMuerta.lean` prueba (`palomar_nodos`) que la vuelta atrás con el detector «hay una cláusula falsa» (`detCNF`)
visita más de `(n + 1 − j)^j / 2` nodos sobre el palomar `PHP^m_n`. Aquí se muestra que **comprar demora con
anticipación no esquiva la cota**: si el detector mira `h` niveles hacia abajo con `detCNF` (el `anticipa` de
`DemoraEfectiva.lean`), el **total de llamadas a `detCNF`** sigue siendo más de `(n + 1 − j)^j / 2`, para todo `h`.

## Cómo

La idea es la misma de `RaizMuerta`, con una hipótesis abstracta en el medio:

* `Certifica F N det c`: cada vez que `det` declara muerto a un prefijo `p` (de largo `≤ N`), hay un árbol de
  decisión de a lo sumo `c p` hojas que, para toda asignación que sigue `p`, llega a una cláusula de `F` falsa en esa
  asignación. Es decir: la evaluación del detector se puede ver como un subárbol de decisión de tamaño `c p`.
* `arbol_cubre` (general, para cualquier `F`): si `Certifica F N det c` y `1 ≤ c`, debajo de todo nodo muerto hay un
  árbol de decisión que encuentra cláusulas falsas con a lo sumo `peso … c` hojas (`peso` de `DemoraEfectiva`: la
  suma de `c p` sobre los nodos que visita la vuelta atrás con `det`). No necesita que `det` sea sano: la vuelta atrás
  solo dice «encontré» con una solución en la mano (`buscar_vivo`).
* `palomar_certificado`: sobre el palomar, `(n + 1 − j)^j < 2 · peso … c`, para **todo** detector certificado con
  costo `c`. Vía la cota de Beyersdorff, Galesi y Lauria de cslib-frontier.
* Instancias:
  - `certifica_detCNF`: el propio `detCNF` está certificado con costo `1`; `palomar_certificado` con `c = 1` da de
    nuevo `palomar_nodos` (`palomar_nodos'`, como control).
  - `certifica_anticipa`: `anticipa (solCNF F) (detCNF F) N h` está certificado con costo `llamadas … h` (las
    llamadas a `detCNF` o a `solCNF` que hace su evaluación con corto circuito).
* **El resultado** (`palomar_anticipa_llamadas`): la búsqueda con `anticipa … h` hace, en total, más de
  `(n + 1 − j)^j / 2` llamadas a `detCNF`/`solCNF`, **sin depender de `h`**. Como cada evaluación cuesta a lo sumo
  `2^(h+1)` llamadas (`llamadas_cota`), queda `palomar_anticipa_nodos`:
  `(n + 1 − j)^j < nodos(anticipa … h) · 2^(h+2)`. O sea, los nodos pueden bajar a lo sumo en el factor `2^(h+1)`
  que se paga en cada llamada; con `h = O(log n)` siguen siendo `2^Ω(n log n)` (con `j = n/2`:
  `palomar_anticipa_mitad`).

## Lo que NO se prueba

* **Propagación unitaria**: no está. El detector «la propagación unitaria a partir de `p` llega a una cláusula falsa»
  también se certifica con un árbol de a lo sumo (variables propagadas + 1) hojas (cada literal propagado es una
  pregunta cuya otra rama falsifica la cláusula unitaria), así que caería bajo `palomar_certificado`; pero ni la
  definición de la propagación sobre `Clausula` ni ese certificado están escritos. cslib-frontier tiene
  `DPLL.unitLiteral?` sobre `CNF ℕ` con trail de literales, no sobre prefijos `List Bool`, y no tiene el certificado
  como árbol. Queda como trabajo pendiente; `Certifica` es la interfaz que habría que cumplir.
* El contenido es la cota de resolución tree-like de cslib-frontier; lo que se agrega es el puente (la búsqueda con un
  detector certificado *es* un árbol de decisión que encuentra cláusulas falsas). Es la observación clásica de que
  DPLL con detectores «locales» es resolución tree-like; no dice nada de detectores arbitrarios de tiempo polinomial.
* Contar llamadas o nodos no es tiempo de máquina de Turing: `llamadas` y `peso` son contadores del modelo.
* El orden de las variables es fijo (cualquiera, vía `relabel f`) y no hay aprendizaje.
-/

open Cslib Cslib.Logic.PL

namespace Sagitta.Map
namespace Tiempo

/-! ## La vuelta atrás solo dice «encontré» con una solución en la mano -/

/-- **Sin hipótesis sobre `det`**: si la vuelta atrás dice que encontró, el nodo está vivo. -/
theorem buscar_vivo (sol det : List Bool → Bool) :
    ∀ (k : ℕ) (p : List Bool), (buscar sol det k p).1 = true → Vivo sol k p
  | 0, p, h => by
    rw [vivo_cero]
    by_cases hd : det p = true
    · simp [buscar, hd] at h
    · simpa [buscar, hd] using h
  | k + 1, p, h => by
    rw [vivo_succ]
    by_cases hd : det p = true
    · simp [buscar, hd] at h
    · by_cases ha : (buscar sol det k (p ++ [false])).1 = true
      · exact .inl (buscar_vivo sol det k _ ha)
      · simp only [buscar, hd, ha, Bool.false_eq_true, ite_false] at h
        exact .inr (buscar_vivo sol det k _ h)

/-! ## Detectores certificados por árboles de decisión -/

/-- `t` **encuentra cláusulas falsas de `F` debajo de `p`**: para toda asignación que sigue `p`, la hoja a la que se
llega es una cláusula de `F` falsa en ella. -/
def EncuentraDebajo (F : List Clausula) (p : List Bool) (t : DecisionTree ℕ Clausula) : Prop :=
  ∀ σ : ℕ → Bool, Sigue σ p → t.eval σ ∈ F ∧ Clause.eval σ (t.eval σ) = false

/-- **Detector certificado con costo `c`**: cada vez que `det` dispara en un prefijo de largo `≤ N`, hay un árbol de
decisión de a lo sumo `c p` hojas que encuentra cláusulas falsas debajo de `p`. -/
def Certifica (F : List Clausula) (N : ℕ) (det : List Bool → Bool) (c : List Bool → ℕ) : Prop :=
  ∀ p : List Bool, p.length ≤ N → det p = true → ∃ t, t.leafCount ≤ c p ∧ EncuentraDebajo F p t

/-- **La búsqueda con un detector certificado cabe en un árbol de decisión**: debajo de todo nodo muerto hay un árbol
que encuentra cláusulas falsas con a lo sumo `peso … c` hojas. -/
theorem arbol_cubre {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N) {det : List Bool → Bool}
    {c : List Bool → ℕ} (hc1 : ∀ p, 1 ≤ c p) (hcert : Certifica F N det c) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = N → ¬ Vivo (solCNF F) k p →
      ∃ t, t.leafCount ≤ peso (solCNF F) det c k p ∧ EncuentraDebajo F p t
  | 0, p, hl, hm => by
    by_cases hd : det p = true
    · obtain ⟨t, ht, he⟩ := hcert p (by omega) hd
      exact ⟨t, by simpa [peso] using ht, he⟩
    · have hsol : solCNF F p = false := by
        cases h : solCNF F p
        · rfl
        · exact absurd ((vivo_cero _ p).mpr h) hm
      have hdc := det_de_completa hvar (by omega) hsol
      obtain ⟨h1, h2⟩ := clFalsa_spec hdc
      refine ⟨.leaf (clFalsa F p), by simpa [peso, DecisionTree.leafCount] using hc1 p, ?_⟩
      intro σ hs
      exact ⟨h1, eval_falsificada hs h2⟩
  | k + 1, p, hl, hm => by
    by_cases hd : det p = true
    · obtain ⟨t, ht, he⟩ := hcert p (by omega) hd
      exact ⟨t, by simpa [peso, hd] using ht, he⟩
    · have hb : ∀ b, ¬ Vivo (solCNF F) k (p ++ [b]) := fun b h =>
        hm ((vivo_succ _ k p).mpr (by cases b <;> simp [h]))
      have ha : (buscar (solCNF F) det k (p ++ [false])).1 = false := by
        cases h : (buscar (solCNF F) det k (p ++ [false])).1
        · rfl
        · exact absurd (buscar_vivo _ _ k _ h) (hb false)
      obtain ⟨t0, h0, e0⟩ := arbol_cubre hvar hc1 hcert k (p ++ [false]) (by simp; omega) (hb false)
      obtain ⟨t1, h1, e1⟩ := arbol_cubre hvar hc1 hcert k (p ++ [true]) (by simp; omega) (hb true)
      refine ⟨.node p.length t0 t1, ?_, ?_⟩
      · simp only [DecisionTree.leafCount, peso, hd, ha, Bool.false_eq_true, ite_false]
        omega
      · intro σ hs
        simp only [DecisionTree.eval_node]
        have hs' := sigue_snoc hs
        cases hσ : σ p.length
        · rw [hσ] at hs'; simpa using e0 σ hs'
        · rw [hσ] at hs'; simpa using e1 σ hs'

/-- **Cota general en el palomar**: la búsqueda con cualquier detector certificado con costo `c ≥ 1` paga, sumando
`c` sobre los nodos visitados, más de `(n + 1 − j)^j / 2`. -/
theorem palomar_certificado {m n : ℕ} (j : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) {det : List Bool → Bool} {c : List Bool → ℕ}
    (hc1 : ∀ p, 1 ≤ c p) (hcert : Certifica ((CNF.pigeonhole m n).relabel f) N det c) :
    (n + 1 - j) ^ j < 2 * peso (solCNF ((CNF.pigeonhole m n).relabel f)) det c N [] := by
  have : Nonempty (Fin m × Fin n) := ⟨(⟨0, by omega⟩, ⟨0, hn⟩)⟩
  set F : List Clausula := (CNF.pigeonhole m n).relabel f
  have hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N := by
    intro c hc l hl
    simp only [F, CNF.relabel, List.mem_map] at hc
    obtain ⟨c', -, rfl⟩ := hc
    simp only [Clause.relabel, List.mem_map] at hl
    obtain ⟨l', -, rfl⟩ := hl
    exact hN l'.1
  have hunsat : ¬ CNF.Satisfiable (F : CNF ℕ) := by
    rw [CNF.satisfiable_relabel hf]; exact CNF.not_satisfiable_pigeonhole hnm
  obtain ⟨t, hle, he⟩ := arbol_cubre hvar hc1 hcert N [] (by simp) (raiz_muerta hunsat N)
  have ht : t.FindsFalsifiedClause (F : CNF ℕ) := fun σ => he σ (fun i hi => absurd hi (by simp))
  have hlow := CNF.pow_lt_two_mul_leafCount_pigeonhole j hnm (encuentra_traer hf ht)
  rw [leafCount_map, DecisionTree.leafCount_mapQueries] at hlow
  omega

/-! ## Instancia 1: `detCNF` mismo (control) -/

/-- `detCNF` está certificado con costo `1`: la hoja con la cláusula falsa. -/
theorem certifica_detCNF (F : List Clausula) (N : ℕ) : Certifica F N (detCNF F) (fun _ => 1) := by
  intro p _ hd
  obtain ⟨h1, h2⟩ := clFalsa_spec hd
  exact ⟨.leaf (clFalsa F p), le_refl _, fun σ hs => ⟨h1, eval_falsificada hs h2⟩⟩

/-- **`palomar_nodos` de nuevo, como caso particular** (`c = 1`, `peso = nodos`). -/
theorem palomar_nodos' {m n : ℕ} (j : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    (n + 1 - j) ^ j < 2 * nodos (solCNF ((CNF.pigeonhole m n).relabel f))
      (detCNF ((CNF.pigeonhole m n).relabel f)) N [] := by
  have := palomar_certificado j hnm hn hf hN (fun _ => le_refl 1) (certifica_detCNF _ N)
  rwa [peso_uno] at this

/-! ## Instancia 2: anticipar `h` niveles con `detCNF` -/

/-- **`anticipa … h` con `detCNF` está certificado con costo `llamadas … h`**: la evaluación con corto circuito, vista
como árbol de decisión, tiene a lo sumo tantas hojas como llamadas hace. -/
theorem certifica_anticipa {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N) :
    ∀ h : ℕ, Certifica F N (anticipa (solCNF F) (detCNF F) N h) (llamadas (solCNF F) (detCNF F) N h)
  | 0, p, _, ha => by
    have hd : detCNF F p = true := by simpa [anticipa] using ha
    obtain ⟨h1, h2⟩ := clFalsa_spec hd
    exact ⟨.leaf (clFalsa F p), by simp [llamadas, DecisionTree.leafCount],
      fun σ hs => ⟨h1, eval_falsificada hs h2⟩⟩
  | h + 1, p, hp, ha => by
    by_cases hd : detCNF F p = true
    · obtain ⟨h1, h2⟩ := clFalsa_spec hd
      exact ⟨.leaf (clFalsa F p), by simp [llamadas, hd, DecisionTree.leafCount],
        fun σ hs => ⟨h1, eval_falsificada hs h2⟩⟩
    · have hd' : detCNF F p = false := by simpa using hd
      by_cases hlt : p.length < N
      · have hab : anticipa (solCNF F) (detCNF F) N h (p ++ [false]) = true ∧
            anticipa (solCNF F) (detCNF F) N h (p ++ [true]) = true := by
          simpa [anticipa, hd', hlt] using ha
        obtain ⟨t0, h0, e0⟩ := certifica_anticipa hvar h (p ++ [false]) (by simp; omega) hab.1
        obtain ⟨t1, h1, e1⟩ := certifica_anticipa hvar h (p ++ [true]) (by simp; omega) hab.2
        refine ⟨.node p.length t0 t1, ?_, ?_⟩
        · simp only [DecisionTree.leafCount, llamadas, hd', hlt, hab.1, Bool.false_eq_true, ite_false,
            ite_true]
          omega
        · intro σ hs
          simp only [DecisionTree.eval_node]
          have hs' := sigue_snoc hs
          cases hσ : σ p.length
          · rw [hσ] at hs'; simpa using e0 σ hs'
          · rw [hσ] at hs'; simpa using e1 σ hs'
      · have hsol : solCNF F p = false := by simpa [anticipa, hd', hlt] using ha
        exact absurd (det_de_completa hvar (by omega) hsol) hd

theorem llamadas_pos (sol det : List Bool → Bool) (N : ℕ) : ∀ h p, 1 ≤ llamadas sol det N h p
  | 0, _ => by simp [llamadas]
  | h + 1, p => by
    unfold llamadas
    split
    · omega
    · split
      · omega
      · omega

/-- **El resultado: anticipar no esquiva la cota.** La búsqueda con `anticipa … h` (que mira `h` niveles hacia abajo
con `detCNF`) hace en total más de `(n + 1 − j)^j / 2` llamadas a `detCNF`/`solCNF`, para todo `h`. -/
theorem palomar_anticipa_llamadas {m n : ℕ} (j h : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    let F : List Clausula := (CNF.pigeonhole m n).relabel f
    (n + 1 - j) ^ j <
      2 * peso (solCNF F) (anticipa (solCNF F) (detCNF F) N h) (llamadas (solCNF F) (detCNF F) N h) N [] := by
  intro F
  have hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N := by
    intro c hc l hl
    simp only [F, CNF.relabel, List.mem_map] at hc
    obtain ⟨c', -, rfl⟩ := hc
    simp only [Clause.relabel, List.mem_map] at hl
    obtain ⟨l', -, rfl⟩ := hl
    exact hN l'.1
  exact palomar_certificado j hnm hn hf hN (llamadas_pos _ _ N h) (certifica_anticipa hvar h)

/-- **En nodos**: `(n + 1 − j)^j < nodos(anticipa … h) · 2^(h+2)`. Anticipar `h` niveles baja los nodos a lo sumo en
el factor `2^(h+1)` que cuesta cada evaluación. -/
theorem palomar_anticipa_nodos {m n : ℕ} (j h : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    let F : List Clausula := (CNF.pigeonhole m n).relabel f
    (n + 1 - j) ^ j < nodos (solCNF F) (anticipa (solCNF F) (detCNF F) N h) N [] * 2 ^ (h + 2) := by
  intro F
  have h1 := palomar_anticipa_llamadas j h hnm hn hf hN
  have h2 := llamadas_busqueda (solCNF F) (detCNF F) N h N []
  have e : 2 ^ (h + 2) = 2 * 2 ^ (h + 1) := by ring
  rw [e]
  calc (n + 1 - j) ^ j < 2 * peso (solCNF F) (anticipa (solCNF F) (detCNF F) N h)
        (llamadas (solCNF F) (detCNF F) N h) N [] := h1
    _ ≤ 2 * (nodos (solCNF F) (anticipa (solCNF F) (detCNF F) N h) N [] * 2 ^ (h + 1)) :=
        Nat.mul_le_mul_left 2 h2
    _ = _ := by ring

/-- **Con `j = n/2`**: `(n/2 + 1)^(n/2) < nodos(anticipa … h) · 2^(h+2)`. -/
theorem palomar_anticipa_mitad {m n : ℕ} (h : ℕ) (hnm : n < m) (hn : 0 < n) {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ v, f v < N) :
    let F : List Clausula := (CNF.pigeonhole m n).relabel f
    (n / 2 + 1) ^ (n / 2) < nodos (solCNF F) (anticipa (solCNF F) (detCNF F) N h) N [] * 2 ^ (h + 2) :=
  lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) _) (palomar_anticipa_nodos (n / 2) h hnm hn hf hN)

/-! ## Controles -/

-- `detCNF` sobre `todoTrue4` con 4 variables: 9 nodos. La raíz está viva, así que anticipar 4 niveles no la descarta:
-- siguen siendo 9 nodos.
example : nodos (solCNF todoTrue4) (detCNF todoTrue4) 4 [] = 9 := by decide
example : nodos (solCNF todoTrue4) (anticipa (solCNF todoTrue4) (detCNF todoTrue4) 4 4) 4 [] = 9 := by decide
-- Una contradicción profunda: `x3 ∧ ¬x3`. Sin anticipar, la raíz no está detectada y se visitan 31 nodos; anticipando
-- 4 niveles, la raíz se declara muerta en 1 nodo, y esa sola evaluación cuesta 31 llamadas: el costo no desaparece.
def contra3 : List Clausula := [[(3, true)], [(3, false)]]
example : nodos (solCNF contra3) (detCNF contra3) 4 [] = 31 := by decide
example : nodos (solCNF contra3) (anticipa (solCNF contra3) (detCNF contra3) 4 4) 4 [] = 1 := by decide
example : peso (solCNF contra3) (anticipa (solCNF contra3) (detCNF contra3) 4 4)
    (llamadas (solCNF contra3) (detCNF contra3) 4 4) 4 [] = 31 := by decide
-- Con `h = 0,1,2,3,4` los nodos son 31, 15, 7, 3, 1 y las llamadas 31, 38, 37, 34, 31: bajan los nodos, no las llamadas.
example : nodos (solCNF contra3) (anticipa (solCNF contra3) (detCNF contra3) 4 2) 4 [] = 7 := by decide
example : peso (solCNF contra3) (anticipa (solCNF contra3) (detCNF contra3) 4 2)
    (llamadas (solCNF contra3) (detCNF contra3) 4 2) 4 [] = 37 := by decide
-- `Certifica` no es trivial: en `contra3`, ningún detector que dispare en la raíz está certificado con costo 1 (en `[]`
-- ninguna hoja sirve: `x3` y `¬x3` no son falsas en toda asignación), pero `detCNF` sí.
theorem no_certifica_raiz {det : List Bool → Bool} (hd : det [] = true) :
    ¬ Certifica contra3 4 det (fun _ => 1) := by
  intro h
  obtain ⟨t, ht, he⟩ := h [] (by simp) hd
  cases t with
  | leaf c =>
    have h0 := (he (fun _ => false) (fun i hi => absurd hi (by simp))).1
    have hf := (he (fun _ => false) (fun i hi => absurd hi (by simp))).2
    have ht' := (he (fun _ => true) (fun i hi => absurd hi (by simp))).2
    simp only [contra3, List.mem_cons, List.not_mem_nil, or_false] at h0
    rcases h0 with rfl | rfl <;> simp_all [DecisionTree.eval, Clause.eval, Literal.eval]
  | node i t0 t1 => simp [DecisionTree.leafCount] at ht; have := t0.leafCount_pos; have := t1.leafCount_pos; omega

example : ¬ Certifica contra3 4 (fun _ => true) (fun _ => 1) := no_certifica_raiz rfl
example : Certifica contra3 4 (detCNF contra3) (fun _ => 1) := certifica_detCNF _ _

-- Mutante 2, refutado: anticipar con costo 1 por evaluación no está certificado. El costo `llamadas` de
-- `certifica_anticipa` hace falta.
example : ¬ Certifica contra3 4 (anticipa (solCNF contra3) (detCNF contra3) 4 4) (fun _ => 1) :=
  no_certifica_raiz (by decide)

-- Mutante 3, refutado: sin `1 ≤ c`, el detector que nunca dispara está certificado con costo 0 y su peso es 0, así
-- que la cota `(n+1−j)^j < 2 · peso` de `palomar_certificado` sería falsa. La hipótesis hace falta.
example : Certifica contra3 4 (fun _ => false) (fun _ => 0) ∧
    peso (solCNF contra3) (fun _ => false) (fun _ => 0) 4 [] = 0 :=
  ⟨fun _ _ h => absurd h (by simp), by decide⟩

-- Mutante 1, refutado: sin el factor `2^(h+2)`, los nodos solos no tienen cota que valga para todo `h`: en `contra3`
-- bajan de 31 (`h = 0`) a 1 (`h = 4`), como muestran los controles de arriba.

/- Mutantes probados fuera del repositorio (todos fallan, como debe ser):
1–3. Refutados arriba con `example`s (no solo «la táctica no cierra»): los nodos sin `2^(h+2)` no tienen cota
uniforme; anticipar no está certificado con costo 1; sin `1 ≤ c` la cota es falsa.
4. El control de `contra3` con `h = 4` diciendo `1` llamada en vez de `31`: `decide` lo refuta.
Axiomas de `palomar_certificado`, `palomar_anticipa_llamadas`, `palomar_anticipa_nodos`, `palomar_anticipa_mitad`,
`certifica_anticipa` y `palomar_nodos'`: `propext`, `Classical.choice`, `Quot.sound`.
-/

end Tiempo
end Sagitta.Map
