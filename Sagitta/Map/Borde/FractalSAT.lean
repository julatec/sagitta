import Sagitta.Map.Borde.RelojDeLadner
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# El fractal de SAT: autosimilitud, poda y la trampa

José (25 nov 2026) vio que la autorreducibilidad de SAT es autosimilitud: SAT es el punto fijo de su propia recursión,
como un fractal es el punto fijo de sus copias contraídas (Hutchinson 1981). Propuso también que un «mundo fractal»
podría ser el axioma perdido. La prueba de la trampa pide distinguir un axioma más evidente que P ≠ NP de
una reformulación. Este archivo formaliza las dos cosas: la autosimilitud (§ 1–3) y la trampa (§ 4–5).

La autorreducibilidad como **búsqueda** ya está en `Informacion/TorreCHT.lean` (`buscar`, `buscar_correcto`,
`sat_enP_iff_busqueda`): allí la pieza es el algoritmo; aquí es la **ecuación** que SAT satisface, y su árbol.

## 1. SAT como punto fijo (Hutchinson)

`fijar b φ` sustituye la variable `0` por `b` y corre las demás un lugar (`eval_fijar`: es evaluar `φ` en `pegar b σ`).
El operador `T L = {φ | φ sin variables y verdadera, o fijar 0 φ ∈ L o fijar 1 φ ∈ L}` (`T`):

* `sat_punto_fijo`: `T SAT = SAT`, por `satisfacible_fijar` (la autorreducibilidad de un paso).
* `iterado_olvida_el_inicio`: si las variables de `φ` son `< n`, entonces `φ ∈ T^[n+1] X ↔ φ` es satisfacible, **para
  todo `X`**. Es la contracción de Hutchinson: cada aplicación de `T` borra un nivel de la dependencia del inicio.
* `punto_fijo_unico`: todo `L` con `T L = L` es SAT. El caso base (fórmulas sin variables) está dentro de `T`.
* `T_monotono`.

## 2. El árbol de autorreducción

El nodo `p` (una lista de bits) es la fórmula con las primeras `|p|` variables fijadas (`fijarLista`). Las soluciones de
`φ` en `n` variables son una `Finset` de listas de largo `n` (`soluciones`), y `N(d)` cuenta los prefijos de largo `d`
que se extienden a una solución (`prefijos`, `cuenta`):

* `nodo_satisfacible_iff`: el nodo `p` es satisfacible si y solo si `p` es uno de esos prefijos. Así `N(d)` es la
  cantidad de nodos vivos del árbol en el nivel `d`.
* `cuenta_mono` (`N(d) ≤ N(d+1)`), `cuenta_tope` (`N(n) = #soluciones`), `cuenta_le_pow` (`N(d) ≤ 2^d`).
* `dimCajas S d = log₂ N(d) / d`, la «dimensión de conteo de cajas» en la métrica de prefijos, **solo como definición**,
  con sus cotas triviales `dimCajas_nonneg` y `dimCajas_le_uno`. No se prueba nada sobre su límite.

## 3. La poda (el corazón combinatorio de Mahaney)

`podar h` deja un representante por cada valor de `h`; `nivel h d` poda los hijos del nivel anterior. Si `h` va a un
conjunto `R` y respeta la satisfacibilidad entre nodos del mismo largo:

* `nivel_correcto`: la raíz es satisfacible si y solo si alguna hoja del nivel `n` lo es (y las hojas tienen largo `n`,
  `nivel_largo`).
* `nodos_totales`: se visitan a lo sumo `n · |R|` nodos en los niveles `1..n` (`nivel_tamano`: `≤ |R|` por nivel).
* `poda_sat`: la instancia de SAT (el nodo `p` es `fijarLista p φ`).

Es el lema de Mahaney (1982) sin el censo: el censo de un conjunto ralo es lo que fabrica `h`; aquí `h` es un dato.

## 4. La trampa, formal: un mundo fractal es P ≠ NP reformulado

`Intermedio L`: `L ∈ NP`, `L ∉ P` y `L` no es NP-completo (sobre `encBits`, con las definiciones de cslib).

* `intermedio_implica_P_ne_NP`: la dirección trivial (si `L ∉ P` y `L ∈ NP`, ya `P ≠ NP`).
* `completo_de_P_eq_NP`: si `P = NP` (para toda codificación, como la entiende cslib), todo `L ∈ NP` no trivial es
  NP-completo: la reducción decide y manda a un sí o a un no fijos. Así, sin intermedios ni `P = NP`, la tricotomía
  es una dicotomía.
* `intermedio_iff_P_ne_NP`: con Ladner (1975), que cslib-frontier tiene demostrado
  (`RelojDeLadner.ladner_cslib`), **existir un intermedio es equivalente a `P ≠ NP`**. Aceptar un «mundo fractal»
  (estructura a toda escala entre P y NP-completo) como axioma es aceptar `P ≠ NP` con otras palabras: no pasa la
  pregunta 1 de la trampa (¿es distinto de lo que se quiere probar?).

## 5. La hipótesis de la medida, en un modelo abstracto

`IdealSigma X`: una noción de clase despreciable (cerrada por subconjuntos y uniones numerables). La hipótesis
`HipotesisMedida I`: P es despreciable y NP no.

* `medida_implica_P_ne_NP`: trivial (si `P = NP`, NP sería despreciable).
* `elegir_despues_reformula`: **si el ideal se puede elegir después de ver NP, la hipótesis es `P ≠ NP`**: existe un
  ideal que anula P y no NP si y solo si `P ≠ NP` (el ideal de los subconjuntos de P). El contenido de Lutz está en
  fijar el ideal **antes**, por un criterio que no nombra a NP.
* `idealMartingalas F e`: el ideal de las clases donde triunfa alguna martingala de una familia numerable `F` fijada de
  antemano (la forma de la medida p de Lutz, sin la restricción de tiempo de las martingalas). `una_martingala_no_lo_anula_todo`:
  una sola martingala no triunfa en todas las sucesiones (Ville: el camino que no le deja ganar).
* `lutz_estructura`: con un ideal así, la hipótesis da `P ≠ NP`.

Esto es la **estructura lógica** de la hipótesis de Lutz (1997), no su medida p: las martingalas aquí no tienen cota de
tiempo y P no se prueba despreciable. La hipótesis es **más fuerte** que P ≠ NP, no una reformulación: implica
P ≠ NP, y con el ideal fijado de antemano no se sigue de P ≠ NP (`elegir_despues_reformula` muestra que solo se sigue
si el ideal se elige mirando a NP). Pasa en lo formal la pregunta 1 (es otra cosa) y la 2 (implica, no equivale) de la
trampa; la 4 (¿hay evidencia de que sea verdadera?) es empírica y no se decide en Lean.

## Lo que NO se prueba

* Que `dimCajas` tenga límite, ni su valor para ninguna familia de fórmulas.
* El censo de Mahaney (que un conjunto ralo NP-difícil da la `h`), ni la medida p de Lutz.
* Ladner se usa, no se reprueba: es el de cslib-frontier vía `RelojDeLadner.ladner_cslib`.
-/

namespace Sagitta.Map.Borde.FractalSAT

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

/-! ## 1. SAT como punto fijo -/

section PuntoFijo

/-- La asignación que pone `b` en la variable `0` y corre `σ` un lugar. -/
def pegar (b : Bool) (σ : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | v + 1 => σ v

/-- Una cláusula con la variable `0` fijada (sin el literal que la satisface): borra los literales de `0` y corre. -/
def fijarClausula (c : Clause ℕ) : Clause ℕ :=
  (c.filter (fun l => decide (l.1 ≠ 0))).map (fun l => (l.1 - 1, l.2))

/-- **Fijar la variable `0` en `b`**: se van las cláusulas que el literal `(0, b)` satisface; en las demás se borra la
variable `0` y se corren las otras. -/
def fijar (b : Bool) (φ : CNF ℕ) : CNF ℕ :=
  (φ.filter (fun c => decide ((0, b) ∉ c))).map fijarClausula

theorem eval_fijarClausula (b : Bool) (σ : ℕ → Bool) :
    ∀ c : Clause ℕ, (0, b) ∉ c → Clause.eval σ (fijarClausula c) = Clause.eval (pegar b σ) c
  | [], _ => rfl
  | ⟨v, s⟩ :: c, h => by
    have ih := eval_fijarClausula b σ c (fun h' => h (List.mem_cons_of_mem _ h'))
    cases v with
    | zero =>
      have hs : s ≠ b := fun e => h (by simp [e])
      simp only [fijarClausula, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, Clause.eval_cons] at ih ⊢
      rw [ih]
      simp [Literal.eval, pegar, Ne.symm hs]
    | succ w =>
      simp only [fijarClausula, List.filter_cons, ne_eq, Nat.add_one_ne_zero, not_false_eq_true,
        decide_true, ↓reduceIte, List.map_cons, Clause.eval_cons] at ih ⊢
      rw [ih]
      simp [pegar]

/-- **Fijar es evaluar en `pegar b σ`.** -/
theorem eval_fijar (b : Bool) (σ : ℕ → Bool) : ∀ φ : CNF ℕ, (fijar b φ).eval σ = φ.eval (pegar b σ)
  | [] => rfl
  | c :: φ => by
    have ih := eval_fijar b σ φ
    by_cases h : (0, b) ∈ c
    · have hc : Clause.eval (pegar b σ) c = true :=
        (Clause.eval_eq_true_iff _ _).2 ⟨(0, b), h, by simp [pegar]⟩
      simp only [fijar, List.filter_cons, h, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte] at ih ⊢
      rw [ih, CNF.eval_cons, hc, Bool.true_and]
    · simp only [fijar, List.filter_cons, h, not_false_eq_true, decide_true, ↓reduceIte,
        List.map_cons, CNF.eval_cons] at ih ⊢
      rw [ih, eval_fijarClausula b σ c h]

theorem pegar_cabeza_cola (σ : ℕ → Bool) : pegar (σ 0) (fun v => σ (v + 1)) = σ := by
  funext v; cases v <;> rfl

/-- **La autorreducibilidad de un paso**: `φ` es satisfacible si y solo si lo es con `0` fijada en `0` o en `1`. -/
theorem satisfacible_fijar (φ : CNF ℕ) :
    φ.Satisfiable ↔ (fijar false φ).Satisfiable ∨ (fijar true φ).Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    have : φ.eval (pegar (σ 0) (fun v => σ (v + 1))) = true := by rw [pegar_cabeza_cola]; exact hσ
    cases h0 : σ 0
    · exact Or.inl ⟨fun v => σ (v + 1), by rw [eval_fijar]; rw [h0] at this; exact this⟩
    · exact Or.inr ⟨fun v => σ (v + 1), by rw [eval_fijar]; rw [h0] at this; exact this⟩
  · rintro (⟨σ, hσ⟩ | ⟨σ, hσ⟩) <;> exact ⟨_, by rw [eval_fijar] at hσ; exact hσ⟩

/-- Las variables de `φ` son `< n`. -/
def Acotada (n : ℕ) (φ : CNF ℕ) : Prop := ∀ v ∈ φ.vars, v < n

theorem acotada_fijar {n : ℕ} {φ : CNF ℕ} (h : Acotada (n + 1) φ) (b : Bool) : Acotada n (fijar b φ) := by
  intro v hv
  rw [CNF.mem_vars] at hv
  obtain ⟨c, hc, s, hvs⟩ := hv
  simp only [fijar, List.mem_map, List.mem_filter] at hc
  obtain ⟨c', ⟨hc', _⟩, rfl⟩ := hc
  simp only [fijarClausula, List.mem_map, List.mem_filter, decide_eq_true_eq] at hvs
  obtain ⟨⟨w, s'⟩, ⟨hw, hw0⟩, e⟩ := hvs
  simp only [Prod.mk.injEq] at e
  have := h w (CNF.mem_vars.2 ⟨c', hc', s', hw⟩)
  simp only at hw0
  omega

theorem existe_cota (φ : CNF ℕ) : ∃ n, Acotada n φ :=
  ⟨φ.vars.sum + 1, fun _ hv => Nat.lt_succ_of_le (List.le_sum_of_mem hv)⟩

/-- Sin variables, el valor no depende de la asignación. -/
theorem satisfacible_sin_variables {φ : CNF ℕ} (h : φ.vars = []) :
    φ.Satisfiable ↔ φ.eval (fun _ => false) = true :=
  ⟨fun ⟨σ, hσ⟩ => by rw [← hσ]; exact CNF.eval_congr (by simp [h]), fun e => ⟨_, e⟩⟩

/-- **El operador de Hutchinson de SAT**: el caso base (sin variables, se evalúa) y dos copias contraídas. -/
def T (L : Set (CNF ℕ)) : Set (CNF ℕ) :=
  {φ | if φ.vars = [] then φ.eval (fun _ => false) = true else (fijar false φ ∈ L ∨ fijar true φ ∈ L)}

theorem T_monotono {L L' : Set (CNF ℕ)} (h : L ⊆ L') : T L ⊆ T L' := by
  intro φ hφ
  simp only [T, Set.mem_ofPred_eq] at hφ ⊢
  split_ifs at hφ ⊢
  · exact hφ
  · exact hφ.imp (fun h' => h h') (fun h' => h h')

/-- **SAT es un punto fijo de `T`.** -/
theorem sat_punto_fijo : T SAT = SAT := by
  ext φ
  simp only [T, Set.mem_ofPred_eq, SAT]
  split_ifs with h
  · exact (satisfacible_sin_variables h).symm
  · exact (satisfacible_fijar φ).symm

/-- **La contracción**: `n + 1` aplicaciones de `T` deciden las fórmulas de variables `< n`, empezando donde sea. -/
theorem iterado_olvida_el_inicio (X : Set (CNF ℕ)) :
    ∀ n (φ : CNF ℕ), Acotada n φ → (φ ∈ T^[n + 1] X ↔ φ.Satisfiable)
  | 0, φ, hφ => by
    have h : φ.vars = [] := List.eq_nil_iff_forall_not_mem.2 fun v hv => Nat.not_lt_zero _ (hφ v hv)
    rw [Function.iterate_one]
    simp only [T, Set.mem_ofPred_eq, h, ↓reduceIte]
    exact (satisfacible_sin_variables h).symm
  | n + 1, φ, hφ => by
    rw [Function.iterate_succ_apply']
    simp only [T, Set.mem_ofPred_eq]
    split_ifs with h
    · exact (satisfacible_sin_variables h).symm
    · rw [iterado_olvida_el_inicio X n _ (acotada_fijar hφ false),
        iterado_olvida_el_inicio X n _ (acotada_fijar hφ true)]
      exact (satisfacible_fijar φ).symm

/-- **SAT es el único punto fijo de `T`** (con el caso base fijado dentro de `T`). -/
theorem punto_fijo_unico {L : Set (CNF ℕ)} (hL : T L = L) : L = SAT := by
  ext φ
  obtain ⟨n, hn⟩ := existe_cota φ
  have hit : T^[n + 1] L = L := Function.iterate_fixed hL _
  rw [← hit, iterado_olvida_el_inicio L n φ hn]
  rfl

end PuntoFijo

/-! ## 2. El árbol de autorreducción -/

section Arbol

/-- El nodo `p` del árbol: las primeras `|p|` variables fijadas, en orden. -/
def fijarLista : List Bool → CNF ℕ → CNF ℕ
  | [], φ => φ
  | b :: p, φ => fijarLista p (fijar b φ)

/-- La asignación del nodo: los bits de `p` y después `σ`. -/
def pegarLista : List Bool → (ℕ → Bool) → ℕ → Bool
  | [], σ => σ
  | b :: p, σ => pegar b (pegarLista p σ)

theorem eval_fijarLista : ∀ (p : List Bool) (φ : CNF ℕ) (σ : ℕ → Bool),
    (fijarLista p φ).eval σ = φ.eval (pegarLista p σ)
  | [], _, _ => rfl
  | b :: p, φ, σ => by simp only [fijarLista, pegarLista]; rw [eval_fijarLista p, eval_fijar]

theorem pegarLista_apply : ∀ (p : List Bool) (σ : ℕ → Bool) (v : ℕ),
    pegarLista p σ v = if h : v < p.length then p[v] else σ (v - p.length)
  | [], σ, v => by simp [pegarLista]
  | b :: p, σ, 0 => by simp [pegarLista, pegar]
  | b :: p, σ, v + 1 => by
    simp only [pegarLista, pegar, pegarLista_apply p σ v, List.length_cons, List.getElem_cons_succ]
    by_cases h : v < p.length
    · simp [h]
    · simp [h, show ¬ v + 1 < p.length + 1 by omega]

theorem fijarLista_snoc : ∀ (p : List Bool) (b : Bool) (φ : CNF ℕ),
    fijarLista (p ++ [b]) φ = fijar b (fijarLista p φ)
  | [], _, _ => rfl
  | c :: p, b, φ => fijarLista_snoc p b (fijar c φ)

/-- **El árbol es autosimilar**: cada nodo es satisfacible si y solo si alguno de sus dos hijos lo es. -/
theorem nodo_autorreducible (φ : CNF ℕ) (p : List Bool) :
    (fijarLista p φ).Satisfiable ↔
      (fijarLista (p ++ [false]) φ).Satisfiable ∨ (fijarLista (p ++ [true]) φ).Satisfiable := by
  rw [fijarLista_snoc, fijarLista_snoc]; exact satisfacible_fijar _

/-- Todas las listas de bits de largo `n`. -/
def todas : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (todas n).image (List.cons false) ∪ (todas n).image (List.cons true)

theorem mem_todas : ∀ {n : ℕ} {p : List Bool}, p ∈ todas n ↔ p.length = n
  | 0, p => by simp [todas, List.length_eq_zero_iff]
  | n + 1, [] => by simp [todas]
  | n + 1, b :: p => by
    cases b <;> simp [todas, mem_todas]

theorem card_todas : ∀ n, (todas n).card = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    rw [todas, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (List.cons_injective),
      Finset.card_image_of_injective _ (List.cons_injective), card_todas n]
    · ring
    · rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨_, _, rfl⟩ := h1
      obtain ⟨_, _, e⟩ := h2
      simp at e

/-- La asignación de una hoja (una lista de bits), con `false` después. -/
def asig (p : List Bool) (v : ℕ) : Bool := p.getD v false

/-- Las soluciones de `φ` en `n` variables: las hojas satisfacibles del árbol. -/
def soluciones (φ : CNF ℕ) (n : ℕ) : Finset (List Bool) := (todas n).filter fun p => φ.eval (asig p) = true

/-- Los prefijos de largo `d` de un conjunto de hojas. -/
def prefijos (S : Finset (List Bool)) (d : ℕ) : Finset (List Bool) := S.image (List.take d)

/-- **`N(d)`**: cuántos prefijos de largo `d` se extienden a una hoja de `S`. -/
def cuenta (S : Finset (List Bool)) (d : ℕ) : ℕ := (prefijos S d).card

theorem prefijos_succ (S : Finset (List Bool)) (d : ℕ) :
    prefijos S d = (prefijos S (d + 1)).image (List.take d) := by
  simp only [prefijos, Finset.image_image]
  apply Finset.image_congr
  intro a _
  simp [Function.comp, List.take_take]

/-- **`N` no decrece**: cada prefijo vivo de largo `d` tiene al menos un hijo vivo. -/
theorem cuenta_mono (S : Finset (List Bool)) (d : ℕ) : cuenta S d ≤ cuenta S (d + 1) := by
  unfold cuenta; rw [prefijos_succ S d]; exact Finset.card_image_le

theorem cuenta_monotona (S : Finset (List Bool)) : Monotone (cuenta S) :=
  monotone_nat_of_le_succ (cuenta_mono S)

/-- **`N(n) = #soluciones`**: en el fondo del árbol, los prefijos son las hojas. -/
theorem cuenta_tope {S : Finset (List Bool)} {n : ℕ} (hS : ∀ a ∈ S, a.length = n) : cuenta S n = S.card := by
  unfold cuenta prefijos
  have : S.image (List.take n) = S.image id :=
    Finset.image_congr fun a ha => List.take_of_length_le (hS a ha).le
  rw [this, Finset.image_id]

theorem cuenta_soluciones (φ : CNF ℕ) (n : ℕ) : cuenta (soluciones φ n) n = (soluciones φ n).card :=
  cuenta_tope fun _ ha => mem_todas.1 (Finset.mem_filter.1 ha).1

theorem prefijos_sub_todas {S : Finset (List Bool)} {n d : ℕ} (hS : ∀ a ∈ S, a.length = n) (hd : d ≤ n) :
    prefijos S d ⊆ todas d := by
  intro p hp
  simp only [prefijos, Finset.mem_image] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  rw [mem_todas, List.length_take, hS a ha]; omega

/-- **`N(d) ≤ 2^d`.** -/
theorem cuenta_le_pow {S : Finset (List Bool)} {n d : ℕ} (hS : ∀ a ∈ S, a.length = n) (hd : d ≤ n) :
    cuenta S d ≤ 2 ^ d :=
  (card_todas d) ▸ Finset.card_le_card (prefijos_sub_todas hS hd)

/-- **El nodo `p` está vivo si y solo si `p` se extiende a una solución.** -/
theorem nodo_satisfacible_iff {φ : CNF ℕ} {n : ℕ} (hφ : Acotada n φ) {p : List Bool} (hp : p.length ≤ n) :
    (fijarLista p φ).Satisfiable ↔ p ∈ prefijos (soluciones φ n) p.length := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [eval_fijarLista] at hσ
    refine Finset.mem_image.2 ⟨p ++ List.ofFn (fun i : Fin (n - p.length) => σ i), ?_, by simp⟩
    refine Finset.mem_filter.2 ⟨mem_todas.2 (by simp; omega), ?_⟩
    rw [← hσ]
    refine CNF.eval_congr fun v hv => ?_
    have hvn := hφ v hv
    rw [pegarLista_apply, asig]
    by_cases h : v < p.length
    · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · simp only [h, ↓reduceDIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp [show v - p.length < n - p.length by omega]
  · intro hp'
    simp only [prefijos, Finset.mem_image, soluciones, Finset.mem_filter, mem_todas] at hp'
    obtain ⟨a, ⟨ha, hev⟩, e⟩ := hp'
    have hpa : p.length ≤ a.length := by
      have := congrArg List.length e
      rw [List.length_take] at this
      omega
    refine ⟨fun v => asig a (v + p.length), ?_⟩
    rw [eval_fijarLista, ← hev]
    congr 1
    funext v
    rw [pegarLista_apply]
    by_cases h : v < p.length
    · simp only [h, ↓reduceDIte, asig, List.getD_eq_getElem?_getD]
      rw [List.getElem_of_eq e.symm h, List.getElem_take,
        List.getElem?_eq_getElem (show v < a.length by omega), Option.getD_some]
    · simp only [h, ↓reduceDIte]
      congr 1; omega

/-- **La dimensión de conteo de cajas** en la métrica de prefijos, en el nivel `d`: `log₂ N(d) / d`. Solo la
definición. -/
noncomputable def dimCajas (S : Finset (List Bool)) (d : ℕ) : ℝ := Real.logb 2 (cuenta S d) / d

theorem dimCajas_nonneg (S : Finset (List Bool)) (d : ℕ) : 0 ≤ dimCajas S d := by
  unfold dimCajas
  apply div_nonneg _ (Nat.cast_nonneg d)
  rcases Nat.eq_zero_or_pos (cuenta S d) with h | h
  · simp [h]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

theorem dimCajas_le_uno {S : Finset (List Bool)} {n d : ℕ} (hS : ∀ a ∈ S, a.length = n) (hd : d ≤ n) :
    dimCajas S d ≤ 1 := by
  unfold dimCajas
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · simp [h0]
  rw [div_le_one (by exact_mod_cast hpos)]
  rcases Nat.eq_zero_or_pos (cuenta S d) with h | h
  · simp [h]
  calc Real.logb 2 (cuenta S d) ≤ Real.logb 2 ((2 : ℝ) ^ d) :=
        Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h) (by exact_mod_cast cuenta_le_pow hS hd)
    _ = d := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

end Arbol

/-! ## 3. La poda -/

section Poda

variable {β : Type} [DecidableEq β]

/-- Un representante por cada valor de `h`. -/
def podar (h : List Bool → β) : List (List Bool) → List (List Bool)
  | [] => []
  | x :: xs => if (podar h xs).any (fun y => decide (h y = h x)) then podar h xs else x :: podar h xs

theorem podar_sub (h : List Bool → β) : ∀ (l : List (List Bool)), ∀ y ∈ podar h l, y ∈ l
  | [], _, hy => hy
  | x :: xs, y, hy => by
    unfold podar at hy
    split_ifs at hy
    · exact List.mem_cons_of_mem _ (podar_sub h xs y hy)
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (podar_sub h xs y hy)

theorem podar_cubre (h : List Bool → β) : ∀ (l : List (List Bool)), ∀ x ∈ l, ∃ y ∈ podar h l, h y = h x
  | [], _, hx => absurd hx List.not_mem_nil
  | x :: xs, z, hz => by
    unfold podar
    split_ifs with hany
    · rcases List.mem_cons.1 hz with rfl | hz
      · obtain ⟨y, hy, e⟩ := List.any_eq_true.1 hany
        exact ⟨y, hy, of_decide_eq_true e⟩
      · exact podar_cubre h xs z hz
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨z, List.mem_cons_self, rfl⟩
      · obtain ⟨y, hy, e⟩ := podar_cubre h xs z hz
        exact ⟨y, List.mem_cons_of_mem _ hy, e⟩

theorem podar_nodup (h : List Bool → β) : ∀ (l : List (List Bool)), ((podar h l).map h).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    unfold podar
    split_ifs with hany
    · exact podar_nodup h xs
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => hany ?_, podar_nodup h xs⟩
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      exact List.any_eq_true.2 ⟨y, hy, decide_eq_true e⟩

/-- **A lo sumo `|R|` representantes.** -/
theorem podar_largo (h : List Bool → β) {R : Finset β} (hR : ∀ x, h x ∈ R) (l : List (List Bool)) :
    (podar h l).length ≤ R.card := by
  have hn := podar_nodup h l
  rw [← List.length_map (f := h), ← List.toFinset_card_of_nodup hn]
  exact Finset.card_le_card fun b hb => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hb)
    exact hR y

/-- Los hijos de un nivel. -/
def hijos (F : List (List Bool)) : List (List Bool) := F.flatMap fun p => [p ++ [false], p ++ [true]]

/-- **El nivel `d` de la búsqueda podada.** -/
def nivel (h : List Bool → β) : ℕ → List (List Bool)
  | 0 => [[]]
  | d + 1 => podar h (hijos (nivel h d))

theorem nivel_largo (h : List Bool → β) : ∀ d, ∀ q ∈ nivel h d, q.length = d
  | 0, q, hq => by simp [nivel] at hq; simp [hq]
  | d + 1, q, hq => by
    have := podar_sub h _ q hq
    simp only [hijos, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at this
    obtain ⟨p, hp, rfl | rfl⟩ := this <;> simp [nivel_largo h d p hp]

theorem nivel_tamano (h : List Bool → β) {R : Finset β} (hR : ∀ x, h x ∈ R) (d : ℕ) :
    (nivel h (d + 1)).length ≤ R.card := podar_largo h hR _

/-- **La búsqueda podada es correcta** (Mahaney en abstracto): si cada nodo es satisfacible exactamente cuando lo es
algún hijo (hasta el nivel `n`) y `h` respeta la satisfacibilidad en cada nivel, la raíz es satisfacible si y solo si
alguna hoja del nivel `d ≤ n` lo es. -/
theorem nivel_correcto (h : List Bool → β) (sat : List Bool → Prop) {n : ℕ}
    (hred : ∀ p : List Bool, p.length < n → (sat p ↔ sat (p ++ [false]) ∨ sat (p ++ [true])))
    (hh : ∀ u v : List Bool, u.length = v.length → h u = h v → (sat u ↔ sat v)) :
    ∀ d ≤ n, ((∃ q ∈ nivel h d, sat q) ↔ sat [])
  | 0, _ => by simp [nivel]
  | d + 1, hd => by
    rw [← nivel_correcto h sat hred hh d (by omega)]
    have hl := nivel_largo h
    constructor
    · rintro ⟨q, hq, hs⟩
      have := podar_sub h _ q hq
      simp only [hijos, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at this
      obtain ⟨p, hp, e⟩ := this
      refine ⟨p, hp, (hred p (by rw [hl d p hp]; omega)).2 ?_⟩
      rcases e with rfl | rfl
      · exact Or.inl hs
      · exact Or.inr hs
    · rintro ⟨p, hp, hs⟩
      have hpl : p.length < n := by rw [hl d p hp]; omega
      have hhijo : ∃ c ∈ hijos (nivel h d), sat c := by
        rcases (hred p hpl).1 hs with hs | hs
        · exact ⟨_, List.mem_flatMap.2 ⟨p, hp, by simp⟩, hs⟩
        · exact ⟨_, List.mem_flatMap.2 ⟨p, hp, by simp⟩, hs⟩
      obtain ⟨c, hc, hcs⟩ := hhijo
      obtain ⟨y, hy, e⟩ := podar_cubre h _ c hc
      refine ⟨y, hy, (hh y c ?_ e).2 hcs⟩
      rw [nivel_largo h (d + 1) y hy]
      have := List.mem_flatMap.1 hc
      obtain ⟨p', hp', hc'⟩ := this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> simp [hl d p' hp']

/-- **Se visitan a lo sumo `n · |R|` nodos** en los niveles `1..n`. -/
theorem nodos_totales (h : List Bool → β) {R : Finset β} (hR : ∀ x, h x ∈ R) (n : ℕ) :
    ∑ d ∈ Finset.range n, (nivel h (d + 1)).length ≤ n * R.card := by
  calc ∑ d ∈ Finset.range n, (nivel h (d + 1)).length ≤ ∑ _d ∈ Finset.range n, R.card :=
        Finset.sum_le_sum fun d _ => nivel_tamano h hR d
    _ = n * R.card := by simp

/-- **La poda, para SAT**: el nodo `p` es `fijarLista p φ`; con cualquier `h` a un conjunto de tamaño `≤ m` que respete
la satisfacibilidad de los nodos de igual largo, `φ` es satisfacible si y solo si sobrevive una hoja del nivel `n`, y la
búsqueda guarda a lo sumo `n · m` nodos. -/
theorem poda_sat (φ : CNF ℕ) (h : List Bool → β) {R : Finset β} (hR : ∀ x, h x ∈ R) {m : ℕ} (hm : R.card ≤ m)
    (hh : ∀ u v : List Bool, u.length = v.length → h u = h v →
      ((fijarLista u φ).Satisfiable ↔ (fijarLista v φ).Satisfiable)) (n : ℕ) :
    (φ.Satisfiable ↔ ∃ q ∈ nivel h n, (fijarLista q φ).Satisfiable) ∧
      ∑ d ∈ Finset.range n, (nivel h (d + 1)).length ≤ n * m :=
  ⟨(nivel_correcto h (fun p => (fijarLista p φ).Satisfiable) (n := n)
      (fun p _ => nodo_autorreducible φ p) hh n le_rfl).symm,
    (nodos_totales h hR n).trans (Nat.mul_le_mul_left n hm)⟩

end Poda

/-! ## 4. La trampa, formal -/

section Trampa

/-- **Un lenguaje intermedio**: en NP, fuera de P y no NP-completo (con las definiciones de cslib, sobre `encBits`). -/
def Intermedio (L : Set (List Bool)) : Prop :=
  L ∈ Cslib.Complexity.NP encBits ∧ L ∉ Cslib.Complexity.P encBits ∧ ¬ NPComplete encBits L

/-- **La dirección trivial**: un intermedio ya da `P ≠ NP`. -/
theorem intermedio_implica_P_ne_NP {L : Set (List Bool)} (h : Intermedio L) : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits :=
  fun e => h.2.1 (e ▸ h.1)

/-- **Si `P = NP`, todo `L ∈ NP` no trivial es NP-completo**: la reducción decide el problema de origen y manda a un
sí (`y₁ ∈ L`) o a un no (`y₀ ∉ L`) fijos. -/
theorem completo_de_P_eq_NP (hPNP : ∀ {α : Type} (enc : α ↪ List Bool), Cslib.Complexity.P enc = Cslib.Complexity.NP enc) {β : Type}
    {encB : β ↪ List Bool} {L : Set β} (hL : L ∈ Cslib.Complexity.NP encB) {y₁ y₀ : β} (h₁ : y₁ ∈ L) (h₀ : y₀ ∉ L) :
    NPComplete encB L := by
  refine ⟨hL, fun α enc A hA => ?_⟩
  change A ∈ Cslib.Complexity.NP enc at hA
  rw [← hPNP enc] at hA
  obtain ⟨g, hg, hgA⟩ := hA
  refine ⟨fun a => if g a = true then y₁ else y₀, by fun_prop, fun a => ?_⟩
  rw [hgA a]
  by_cases hga : g a = true <;> simp [hga, h₁, h₀]

/-- Con `P = NP` en el sentido de cslib (para toda codificación), un intermedio da contradicción. -/
theorem intermedio_contradice_P_eq_NP {L : Set (List Bool)} (h : Intermedio L) :
    ¬ ∀ {α : Type} (enc : α ↪ List Bool), Cslib.Complexity.P enc = Cslib.Complexity.NP enc :=
  fun e => intermedio_implica_P_ne_NP h (e encBits)

/-- **Ladner (1975)**, el de cslib-frontier, en la forma de este archivo. -/
theorem ladner (h : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits) : ∃ L, Intermedio L :=
  Sagitta.Map.Borde.RelojDeLadner.ladner_cslib (enc := encBits) h

/-- **Un mundo con intermedios es `P ≠ NP`**: la dirección trivial y Ladner. Por eso «aceptar un mundo fractal» (que
entre P y los NP-completos haya estructura) como axioma es aceptar `P ≠ NP` reformulado: no pasa la trampa. -/
theorem intermedio_iff_P_ne_NP : (∃ L, Intermedio L) ↔ Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits :=
  ⟨fun ⟨_, h⟩ => intermedio_implica_P_ne_NP h, ladner⟩

end Trampa

/-! ## 5. La hipótesis de la medida -/

section Medida

/-- **Una noción de clase despreciable**: cerrada por subconjuntos y por uniones numerables. -/
structure IdealSigma (X : Type) where
  nulo : Set X → Prop
  vacio : nulo ∅
  mono : ∀ {A B : Set X}, A ⊆ B → nulo B → nulo A
  union : ∀ f : ℕ → Set X, (∀ i, nulo (f i)) → nulo (⋃ i, f i)

/-- **La hipótesis de la medida**: P es despreciable y NP no. -/
def HipotesisMedida (I : IdealSigma (Set (List Bool))) : Prop := I.nulo (Cslib.Complexity.P encBits) ∧ ¬ I.nulo (Cslib.Complexity.NP encBits)

/-- **La hipótesis de la medida da `P ≠ NP`**: si fueran iguales, NP sería despreciable. -/
theorem medida_implica_P_ne_NP {I : IdealSigma (Set (List Bool))} (h : HipotesisMedida I) :
    Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits :=
  fun e => h.2 (e ▸ h.1)

/-- El ideal de los subconjuntos de `A`. -/
def idealDe {X : Type} (A : Set X) : IdealSigma X where
  nulo S := S ⊆ A
  vacio := Set.empty_subset A
  mono h hB := h.trans hB
  union _ hf := Set.iUnion_subset hf

/-- **Elegir el ideal después es reformular**: hay un ideal que anula `A` y no `B` si y solo si `B ⊄ A`. -/
theorem existe_ideal_iff {X : Type} (A B : Set X) :
    (∃ I : IdealSigma X, I.nulo A ∧ ¬ I.nulo B) ↔ ¬ B ⊆ A :=
  ⟨fun ⟨I, hA, hB⟩ hBA => hB (I.mono hBA hA), fun h => ⟨idealDe A, subset_rfl, h⟩⟩

/-- **…y para P y NP, es exactamente `P ≠ NP`.** -/
theorem elegir_despues_reformula :
    (∃ I : IdealSigma (Set (List Bool)), HipotesisMedida I) ↔ Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits := by
  rw [show (∃ I, HipotesisMedida I) ↔ _ from existe_ideal_iff (Cslib.Complexity.P encBits) (Cslib.Complexity.NP encBits)]
  exact ⟨fun h e => h (e ▸ subset_rfl), fun h hsub => h (P_subset_NP.antisymm hsub)⟩

/-- **Una martingala** (sin cota de tiempo): el capital de apostar a los bits, con apuestas justas. -/
structure Martingala where
  d : List Bool → ℝ
  nonneg : ∀ w, 0 ≤ d w
  promedio : ∀ w, d (w ++ [false]) + d (w ++ [true]) = 2 * d w

/-- Los primeros `n` bits de una sucesión. -/
def prefijo (x : ℕ → Bool) (n : ℕ) : List Bool := List.ofFn fun i : Fin n => x i

/-- La martingala **triunfa** en `x`: su capital no está acotado a lo largo de `x`. -/
def Exito (m : Martingala) (x : ℕ → Bool) : Prop := ∀ c : ℝ, ∃ n, c < m.d (prefijo x n)

open Classical in
/-- La sucesión característica de `L` en la enumeración `e` de las palabras. -/
noncomputable def caracteristica (e : ℕ → List Bool) (L : Set (List Bool)) : ℕ → Bool := fun n => decide (e n ∈ L)

/-- **El ideal de una familia numerable de martingalas**, fijada de antemano: las clases en cuyos lenguajes triunfa
alguna. -/
def idealMartingalas (F : ℕ → Martingala) (e : ℕ → List Bool) : IdealSigma (Set (List Bool)) where
  nulo C := ∀ L ∈ C, ∃ i, Exito (F i) (caracteristica e L)
  vacio := fun _ h => absurd h (Set.notMem_empty _)
  mono hAB hB L hL := hB L (hAB hL)
  union _ hf L hL := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hL
    exact hf i L hi

/-- **La estructura lógica de Lutz**: con un ideal de martingalas fijado de antemano, que P sea despreciable y NP no da
`P ≠ NP`. -/
theorem lutz_estructura (F : ℕ → Martingala) (e : ℕ → List Bool) (h : HipotesisMedida (idealMartingalas F e)) :
    Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits :=
  medida_implica_P_ne_NP h

/-- El camino que no le deja ganar a la martingala: en cada paso, el bit donde el capital no sube. -/
noncomputable def camino (m : Martingala) : ℕ → List Bool
  | 0 => []
  | k + 1 => let w := camino m k; if m.d (w ++ [false]) ≤ m.d w then w ++ [false] else w ++ [true]

theorem camino_acotado (m : Martingala) : ∀ k, m.d (camino m k) ≤ m.d []
  | 0 => le_rfl
  | k + 1 => by
    have ih := camino_acotado m k
    have hp := m.promedio (camino m k)
    simp only [camino]
    split_ifs with h
    · exact h.trans ih
    · linarith [not_le.1 h]

theorem camino_largo (m : Martingala) : ∀ k, (camino m k).length = k
  | 0 => rfl
  | k + 1 => by simp only [camino]; split_ifs <;> simp [camino_largo m k]

theorem camino_prefijo (m : Martingala) : ∀ k j, camino m k <+: camino m (k + j)
  | _, 0 => List.prefix_refl _
  | k, j + 1 => (camino_prefijo m k j).trans (by
      show camino m (k + j) <+: camino m (k + j + 1)
      simp only [camino]; split_ifs <;> exact List.prefix_append _ _)

/-- La sucesión del camino. -/
noncomputable def sucesionCamino (m : Martingala) (i : ℕ) : Bool := (camino m (i + 1)).getD i false

theorem prefijo_camino (m : Martingala) (n : ℕ) : prefijo (sucesionCamino m) n = camino m n := by
  apply List.ext_getElem
  · simp [prefijo, camino_largo]
  · intro i h1 h2
    simp only [prefijo, List.getElem_ofFn, sucesionCamino]
    rw [camino_largo] at h2
    obtain ⟨j, hj⟩ : ∃ j, n = i + 1 + j := ⟨n - (i + 1), by omega⟩
    obtain ⟨t, ht⟩ := camino_prefijo m (i + 1) j
    have hl : i < (camino m (i + 1)).length := by rw [camino_largo]; omega
    subst hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    simp only [← ht, List.getElem_append_left hl]

/-- **Una martingala no anula todo** (Ville): en el camino que elige, su capital nunca pasa del inicial. -/
theorem una_martingala_no_lo_anula_todo (m : Martingala) : ∃ x, ¬ Exito m x := by
  refine ⟨sucesionCamino m, fun h => ?_⟩
  obtain ⟨n, hn⟩ := h (m.d [])
  rw [prefijo_camino] at hn
  exact absurd (camino_acotado m n) (not_le.2 hn)

end Medida

/- Mutantes probados (25 nov 2026, fuera del repositorio):
1. `punto_fijo_unico` sin el caso base en `T` (`T' L = {φ | fijar 0 φ ∈ L ∨ fijar 1 φ ∈ L}`): falso; todo el universo
   es punto fijo y `[[]]` (la cláusula vacía) no es satisfacible (se prueba la negación).
2. `iterado_olvida_el_inicio` con `n` iteraciones en vez de `n + 1`: falso en `n = 0`, `X = ∅`, `φ = []`.
3. `nodo_satisfacible_iff` sin `Acotada n φ`: falso con `φ = [[x₅]]`, `n = 0`, `p = []` (la fórmula es satisfacible y
   no tiene soluciones en cero variables).
4. `cuenta_mono` al revés (`N(d+1) ≤ N(d)`): falso con `S = {[0], [1]}`, `d = 0` (por `decide`).
5. `nivel_correcto` sin que `h` respete la satisfacibilidad: con `h` constante y `sat p := p ≠ [1]`, la poda se queda
   con `[1]` y pierde la solución (se prueba la negación de la equivalencia).
6. `existe_ideal_iff` con la inclusión al revés: falso con `A = ∅`, `B = univ`.
7. `completo_de_P_eq_NP` sin `y₀ ∉ L`: la prueba no cierra (no hay un «no» adonde mandar).
8. `una_martingala_no_lo_anula_todo` con el camino que elige el bit donde el capital sube: `camino_acotado` ya no sale
   (`linarith` falla en las dos ramas). -/

end Sagitta.Map.Borde.FractalSAT
