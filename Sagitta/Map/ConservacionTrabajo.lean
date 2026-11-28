import Sagitta.Map.Decidir
import Sagitta.Map.BombeoDetector

/-!
# La conservación del trabajo: lo que no se paga al buscar se pagó al llenar la tabla

## Qué se prueba

* **La tabla perfecta** (`tabla_perfecta`). Para todo `sol` y todo `N` hay un detector de memoria (`memoriaTabla`)
  cuya alarma es una tabla ya llena con «¿está muerto?» (`tablaLlena`). Es sano, tiene demora 0, y con él la vuelta
  atrás visita a lo sumo `2N + 1` nodos. La cota es exacta (`tabla_perfecta_exacta`). La búsqueda solo consulta la
  tabla en prefijos de largo `≤ N` (`buscar_congr`), y esos son `2^(N+1) − 1` (`card_prefijosHasta`).
  Lectura: la memoria superpolinomial **ya llena** trivializa la búsqueda.
* **La conservación en caja negra** (`trabajo_se_conserva`, la meta central). El oráculo es `f : α → Bool`, con `α`
  finito: la fórmula vista como caja negra. El proceso tiene dos fases.
  - Fase 1, llenado (`Llenado α τ`): un árbol de preguntas que, en vez de responder, produce una tabla `T : τ`. Por
    construcción, `T` depende solo de lo que se preguntó (`tablaDe_congr`).
  - Fase 2, consulta: `Q : τ → Pregunta α`. Lee `T` gratis y sigue preguntando.
  - La composición (`encadenar`) es un `Pregunta α`, y su costo es la suma de las dos fases (`costo_encadenar`).
  Si la composición decide «¿hay una opción buena?», con el oráculo todo `false` se cumple
  `(preguntas del llenado) + (preguntas de la consulta) ≥ |α|`. Lo que la consulta no pregunta lo preguntó el llenado
  (`no_lo_pregunto_la_consulta`).
* **La versión abstracta** (`trabajo_se_conserva_gen`): el llenado es cualquier función `llenar` con un conjunto de
  preguntas `preguntados`, y la hipótesis es `DependeDeLo`: la tabla depende solo de lo preguntado.
* **El control de esa hipótesis** (`tabla_gratis`, `tabla_gratis_no_depende`, `tabla_gratis_rompe`). Si la tabla se
  arma mirando `f` entero sin contar (consejo no uniforme), la consulta cuesta 0 y el teorema es falso. La hipótesis
  `DependeDeLo` es la que lo hace funcionar.
* **Llenar la raíz ya cuesta todo** (`llenar_raiz_cuesta`, `llenar_raiz_exacto`). En el árbol de `N` elecciones, como
  caja negra, todo llenado que acierte la entrada de la raíz de la tabla hace al menos `2^N` preguntas. La tabla
  perfecta de la primera parte acierta esa entrada (`raiz_tablaLlena`).
* **Controles de que nada es vacío**: el trabajo puede ir entero al llenado (`todo_en_el_llenado`), entero a la
  consulta (`todo_en_la_consulta`) o repartido (`repartido_tres`), y la suma no baja de `|α|`.

## La lectura

El trabajo se conserva. Lo que el detector no paga en demora lo pagó quien llenó la tabla. La tabla perfecta hace la
búsqueda lineal, pero llenarla en caja negra cuesta, ya en su primera entrada, lo mismo que buscar a ciegas.

## Lo que NO se prueba (especulación, marcada como tal)

* Que para SAT se cumpla «llenado + búsqueda ≥ 2^((1 − o(1)) n)» se parece a la hipótesis del tiempo exponencial
  fuerte, SETH (R. Impagliazzo y R. Paturi; de memoria, sin verificar). No se prueba aquí.
* Aquí solo va la caja negra. El argumento del adversario relativiza (Baker, Gill y Solovay, 1975), así que no dice
  nada de una fórmula dada por su texto, que se puede leer sin preguntar.
* El contraste del **encuentro a medio camino** no se formaliza. Con estructura aditiva («¿hay `i`, `j` con
  `a_i + b_j = s`?») ordenar y combinar una tabla de `n` entradas decide con unas `2n log n` operaciones contra `n²`.
  Referencias de memoria y sin verificar: E. Horowitz y S. Sahni, 1974 (suma de subconjuntos); R. Schroeppel y
  A. Shamir, 1981. En la caja negra no hay esa estructura, y no hay atajo.
-/

namespace Sagitta.Map.Tiempo.ConservacionTrabajo

open Sagitta.Map.Tiempo.BombeoDetector
open Pregunta

/-! ## Parte 1: la tabla perfecta -/

/-- **La tabla llena**: en cada prefijo, `true` si está muerto con lo que falta hasta `N`. -/
def tablaLlena (sol : List Bool → Bool) (N : ℕ) (p : List Bool) : Bool := !vivoB sol (N - p.length) p

/-- **Un detector de memoria que es una tabla.** El estado es el prefijo leído; la alarma, la tabla `T`. -/
def memoriaTabla (T : List Bool → Bool) : Memoria (List Bool) := ⟨[], fun p b => p ++ [b], T⟩

theorem foldl_snoc : ∀ (p acc : List Bool), p.foldl (fun q b => q ++ [b]) acc = acc ++ p
  | [], acc => by simp
  | b :: p, acc => by simp [foldl_snoc p (acc ++ [b])]

/-- La memoria de la tabla dice lo que dice la tabla. -/
theorem det_memoriaTabla (T : List Bool → Bool) (p : List Bool) : (memoriaTabla T).det p = T p := by
  simp only [Memoria.det, Memoria.estado, memoriaTabla]
  rw [foldl_snoc, List.nil_append]

theorem det_memoriaTabla' (T : List Bool → Bool) : (memoriaTabla T).det = T := funext (det_memoriaTabla T)

/-- **La tabla perfecta**: sana, de demora 0, y la búsqueda visita a lo sumo `2N + 1` nodos. -/
theorem tabla_perfecta (sol : List Bool → Bool) (N : ℕ) :
    SanoN sol (memoriaTabla (tablaLlena sol N)).det N ∧ DemoraN sol (memoriaTabla (tablaLlena sol N)).det N 0 ∧
      nodos sol (memoriaTabla (tablaLlena sol N)).det N [] ≤ 2 * N + 1 := by
  have ho : ∀ p : List Bool, p.length ≤ N →
      ((memoriaTabla (tablaLlena sol N)).det p = true ↔ ¬ Vivo sol (N - p.length) p) := by
    intro p _
    rw [det_memoriaTabla, tablaLlena, ← vivoB_iff]
    simp
  obtain ⟨hs, hd⟩ := oraculo_perfecto ho
  refine ⟨hs, hd, ?_⟩
  by_cases hv : Vivo sol N []
  · have := costo_vivoN hs hd N [] (by simp) hv
    simpa [mul_comm] using this
  · have := costo_muertoN hd (k := N) (p := []) (by simp) hv
    omega

/-- **La búsqueda solo mira la tabla en prefijos de largo `≤ N`.** Dos detectores que coinciden ahí buscan igual. -/
theorem buscar_congr (sol : List Bool → Bool) {det det' : List Bool → Bool} {N : ℕ}
    (h : ∀ p : List Bool, p.length ≤ N → det p = det' p) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = N → buscar sol det k p = buscar sol det' k p
  | 0, p, hk => by simp [buscar, h p (by omega)]
  | k + 1, p, hk => by
    have hf := buscar_congr sol h k (p ++ [false]) (by simp; omega)
    have ht := buscar_congr sol h k (p ++ [true]) (by simp; omega)
    simp only [buscar, h p (by omega), hf, ht]

/-- **Las entradas de la tabla**: los prefijos de largo `≤ n`. -/
def prefijosHasta : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => insert [] ((prefijosHasta n).image (List.cons false) ∪ (prefijosHasta n).image (List.cons true))

theorem mem_prefijosHasta : ∀ {n : ℕ} {q : List Bool}, q ∈ prefijosHasta n ↔ q.length ≤ n
  | 0, q => by cases q <;> simp [prefijosHasta]
  | n + 1, [] => by simp [prefijosHasta]
  | n + 1, b :: q => by
    have ih := @mem_prefijosHasta n q
    cases b <;> simp [prefijosHasta, ih]

/-- **La tabla tiene `2^(N+1) − 1` entradas.** -/
theorem card_prefijosHasta : ∀ n : ℕ, (prefijosHasta n).card + 1 = 2 ^ (n + 1)
  | 0 => by simp [prefijosHasta]
  | n + 1 => by
    have ih := card_prefijosHasta n
    have hnil : [] ∉ (prefijosHasta n).image (List.cons false) ∪ (prefijosHasta n).image (List.cons true) := by
      simp
    have hdis : Disjoint ((prefijosHasta n).image (List.cons false)) ((prefijosHasta n).image (List.cons true)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_image] at hx hy
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨b, -, hb⟩ := hy
      simp at hb
    rw [prefijosHasta, Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (List.cons_injective), Finset.card_image_of_injective _ (List.cons_injective),
      pow_succ]
    omega

/-- **Con la tabla de esas entradas basta**: una tabla que coincide con la perfecta en los `2^(N+1) − 1` prefijos
de largo `≤ N` busca igual que ella. -/
theorem basta_la_tabla (sol T : List Bool → Bool) (N : ℕ)
    (h : ∀ p ∈ prefijosHasta N, T p = tablaLlena sol N p) :
    nodos sol (memoriaTabla T).det N [] = nodos sol (memoriaTabla (tablaLlena sol N)).det N [] := by
  unfold nodos
  rw [buscar_congr sol (det := (memoriaTabla T).det) (det' := (memoriaTabla (tablaLlena sol N)).det) (N := N)
    (fun p hp => by
    rw [det_memoriaTabla, det_memoriaTabla]; exact h p (mem_prefijosHasta.2 hp)) N [] (by simp)]

/-- La única solución es todo `true`, con 4 variables. -/
def soloUnos4 (q : List Bool) : Bool := q == [true, true, true, true]

/-- **Control: la cota `2N + 1` se alcanza.** Con la única solución en todo `true`, la tabla perfecta visita 9 nodos. -/
theorem tabla_perfecta_exacta : nodos soloUnos4 (memoriaTabla (tablaLlena soloUnos4 4)).det 4 [] = 2 * 4 + 1 := by
  rw [det_memoriaTabla']
  decide

/-- **Control: la tabla perfecta encuentra.** -/
example : (buscar soloUnos4 (memoriaTabla (tablaLlena soloUnos4 4)).det 4 []).1 = true := by
  rw [det_memoriaTabla']
  decide

/-- **Control: la tabla para 4 variables tiene 31 entradas.** -/
example : (prefijosHasta 4).card = 31 := by
  have := card_prefijosHasta 4
  omega

/-! ## Parte 2: la conservación en caja negra -/

/-- **Un llenado**: un árbol de preguntas que, en vez de responder, produce una tabla `T : τ`. Por construcción, la
tabla depende solo de las respuestas que recibió. -/
inductive Llenado (α τ : Type) : Type
  | fin (T : τ) : Llenado α τ
  | preg (i : α) (sig : Bool → Llenado α τ) : Llenado α τ

namespace Llenado

variable {α τ : Type}

/-- La tabla que produce el llenado con el oráculo `f`. -/
def tablaDe : Llenado α τ → (α → Bool) → τ
  | fin T, _ => T
  | preg i sig, f => tablaDe (sig (f i)) f

/-- Las opciones que pregunta el llenado con el oráculo `f`. -/
def vistosLl : Llenado α τ → (α → Bool) → List α
  | fin _, _ => []
  | preg i sig, f => i :: vistosLl (sig (f i)) f

/-- **El costo del llenado**: cuántas preguntas hace. -/
def costoLl (L : Llenado α τ) (f : α → Bool) : ℕ := (vistosLl L f).length

/-- **La tabla depende solo de lo preguntado.** -/
theorem tablaDe_congr : ∀ (L : Llenado α τ) (f g : α → Bool), (∀ i ∈ vistosLl L f, f i = g i) →
    tablaDe L f = tablaDe L g
  | fin _, _, _, _ => rfl
  | preg i sig, f, g, h => by
    have hi : f i = g i := h i List.mem_cons_self
    simp only [tablaDe]
    rw [← hi]
    exact tablaDe_congr (sig (f i)) f g (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- **Un algoritmo de preguntas, visto como llenado**: guarda en la tabla `g` de su respuesta. -/
def deP (g : Bool → τ) : Pregunta α → Llenado α τ
  | .resp b => fin (g b)
  | .preg i sig => preg i fun b => deP g (sig b)

theorem tablaDe_deP (g : Bool → τ) (f : α → Bool) : ∀ t : Pregunta α, tablaDe (deP g t) f = g (corre t f)
  | .resp _ => rfl
  | .preg i sig => tablaDe_deP g f (sig (f i))

theorem costoLl_deP (g : Bool → τ) (f : α → Bool) : ∀ t : Pregunta α, costoLl (deP g t) f = costo t f
  | .resp _ => rfl
  | .preg i sig => by
    have := costoLl_deP g f (sig (f i))
    simp only [costoLl, costo, vistos, List.length_cons] at this ⊢
    simp only [deP, vistosLl, List.length_cons]
    omega

end Llenado

open Llenado

/-- **Las dos fases, encadenadas**: primero el llenado, después la consulta con la tabla en la mano. Es un `Pregunta`. -/
def encadenar {α τ : Type} : Llenado α τ → (τ → Pregunta α) → Pregunta α
  | .fin T, Q => Q T
  | .preg i sig, Q => .preg i fun b => encadenar (sig b) Q

variable {α τ : Type}

theorem corre_encadenar (Q : τ → Pregunta α) (f : α → Bool) :
    ∀ L : Llenado α τ, corre (encadenar L Q) f = corre (Q (tablaDe L f)) f
  | .fin _ => rfl
  | .preg i sig => corre_encadenar Q f (sig (f i))

theorem vistos_encadenar (Q : τ → Pregunta α) (f : α → Bool) :
    ∀ L : Llenado α τ, vistos (encadenar L Q) f = vistosLl L f ++ vistos (Q (tablaDe L f)) f
  | .fin _ => rfl
  | .preg i sig => by
    simp only [encadenar, vistos, vistosLl, tablaDe, List.cons_append]
    rw [vistos_encadenar Q f (sig (f i))]

/-- **El costo de las dos fases es la suma.** -/
theorem costo_encadenar (L : Llenado α τ) (Q : τ → Pregunta α) (f : α → Bool) :
    costo (encadenar L Q) f = costoLl L f + costo (Q (tablaDe L f)) f := by
  simp [costo, costoLl, vistos_encadenar]

/-- **El trabajo se conserva.** Si llenar y después consultar decide «¿hay una opción buena?», con el oráculo todo
`false` las preguntas del llenado más las de la consulta son al menos `|α|`. -/
theorem trabajo_se_conserva [Fintype α] (L : Llenado α τ) (Q : τ → Pregunta α)
    (h : DecideExiste (encadenar L Q)) :
    Fintype.card α ≤ costoLl L (fun _ => false) + costo (Q (tablaDe L (fun _ => false))) (fun _ => false) := by
  classical
  rw [← costo_encadenar]
  exact costo_adversario _ h

/-- **Lo que la consulta no pregunta lo preguntó el llenado.** -/
theorem no_lo_pregunto_la_consulta (L : Llenado α τ) (Q : τ → Pregunta α)
    (h : DecideExiste (encadenar L Q)) (i : α) (hi : i ∉ vistos (Q (tablaDe L (fun _ => false))) (fun _ => false)) :
    i ∈ vistosLl L (fun _ => false) := by
  classical
  have := adversario _ h i
  rw [vistos_encadenar, List.mem_append] at this
  exact this.resolve_right hi

/-! ### La versión abstracta y su hipótesis -/

/-- **La tabla depende solo de lo preguntado**: dos oráculos que coinciden en lo que el llenado preguntó con el
primero dan la misma tabla. -/
def DependeDeLo (llenar : (α → Bool) → τ) (preguntados : (α → Bool) → Finset α) : Prop :=
  ∀ f g : α → Bool, (∀ i ∈ preguntados f, f i = g i) → llenar f = llenar g

/-- **Un llenado en árbol cumple la hipótesis**, con lo que pregunta. -/
theorem llenado_depende [DecidableEq α] (L : Llenado α τ) :
    DependeDeLo (tablaDe L) (fun f => (vistosLl L f).toFinset) :=
  fun f g h => tablaDe_congr L f g fun i hi => h i (List.mem_toFinset.2 hi)

/-- **El trabajo se conserva, en abstracto.** Con un llenado cualquiera cuya tabla depende solo de lo preguntado, y
una consulta que con esa tabla decide «¿hay una opción buena?», lo preguntado al llenar más lo preguntado al consultar
cubre todas las opciones. -/
theorem trabajo_se_conserva_gen [Fintype α] (llenar : (α → Bool) → τ)
    (preguntados : (α → Bool) → Finset α) (hdep : DependeDeLo llenar preguntados) (Q : τ → Pregunta α)
    (hdec : ∀ f, corre (Q (llenar f)) f = true ↔ ∃ i, f i = true) :
    Fintype.card α ≤ (preguntados (fun _ => false)).card + costo (Q (llenar (fun _ => false))) (fun _ => false) := by
  classical
  set f0 : α → Bool := fun _ => false
  have hcub : (Finset.univ : Finset α) ⊆ preguntados f0 ∪ (vistos (Q (llenar f0)) f0).toFinset := by
    intro i _
    by_contra hi
    simp only [Finset.mem_union, List.mem_toFinset, not_or] at hi
    obtain ⟨hp, hv⟩ := hi
    let g : α → Bool := Function.update f0 i true
    have hfg : ∀ j, j ≠ i → f0 j = g j := fun j hj => by simp [g, Function.update_of_ne hj]
    have hT : llenar f0 = llenar g := hdep f0 g fun j hj => hfg j fun e => hp (e ▸ hj)
    have hc : corre (Q (llenar f0)) f0 = corre (Q (llenar f0)) g :=
      corre_congr _ f0 g fun j hj => hfg j fun e => hv (e ▸ hj)
    have h0 : corre (Q (llenar f0)) f0 = false := by
      cases hc0 : corre (Q (llenar f0)) f0
      · rfl
      · obtain ⟨j, hj⟩ := (hdec f0).1 hc0; simp [f0] at hj
    have h1 : corre (Q (llenar g)) g = true := (hdec g).2 ⟨i, by simp [g]⟩
    rw [← hT, ← hc, h0] at h1
    exact Bool.false_ne_true h1
  calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
    _ ≤ (preguntados f0 ∪ (vistos (Q (llenar f0)) f0).toFinset).card := Finset.card_le_card hcub
    _ ≤ (preguntados f0).card + (vistos (Q (llenar f0)) f0).toFinset.card := Finset.card_union_le _ _
    _ ≤ (preguntados f0).card + costo (Q (llenar f0)) f0 := Nat.add_le_add_left (List.toFinset_card_le _) _

/-! ### El control: una tabla «gratis» -/

/-- **La consulta con consejo**: si la tabla es el oráculo entero, responde sin preguntar. -/
def consultaGratis [Fintype α] (T : α → Bool) : Pregunta α := .resp (decide (∃ i, T i = true))

/-- **Con una tabla gratis, la consulta decide y cuesta 0.** La tabla se arma mirando `f` sin contar. -/
theorem tabla_gratis [Fintype α] :
    (∀ f : α → Bool, corre (consultaGratis (id f)) f = true ↔ ∃ i, f i = true) ∧
      ∀ f : α → Bool, costo (consultaGratis (id f)) f = 0 := by
  refine ⟨fun f => ?_, fun f => rfl⟩
  simp [consultaGratis, corre]

/-- **Esa tabla no depende solo de lo preguntado**: con nada preguntado, no cumple la hipótesis. -/
theorem tabla_gratis_no_depende [Nonempty α] : ¬ DependeDeLo (id : (α → Bool) → α → Bool) (fun _ => ∅) := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty α›
  have := congrFun (h (fun _ => false) (fun _ => true) (by simp)) i
  simp at this

/-- **Y sin la hipótesis el teorema es falso**: con la tabla gratis, nada preguntado al llenar y nada al consultar,
la suma es 0 y no alcanza a `|α|`. -/
theorem tabla_gratis_rompe [Fintype α] [Nonempty α] :
    ¬ Fintype.card α ≤ ((fun _ => ∅ : (α → Bool) → Finset α) (fun _ => false)).card +
        costo (consultaGratis (id (fun _ : α => false))) (fun _ => false) := by
  have := Fintype.card_pos (α := α)
  simp [consultaGratis, costo, vistos]

/-! ### Los controles de que el teorema no es vacío -/

/-- **Todo el trabajo en el llenado**: llenar es barrer y guardar la respuesta; consultar es leerla. La consulta
cuesta 0 y el llenado `|α|` con el oráculo todo `false`. -/
theorem todo_en_el_llenado [Fintype α] :
    DecideExiste (encadenar (deP id (barrer (Finset.univ : Finset α).toList)) (fun T => .resp T)) ∧
      costoLl (deP id (barrer (Finset.univ : Finset α).toList)) (fun _ => false) = Fintype.card α ∧
      costo ((fun T => (.resp T : Pregunta α)) (tablaDe (deP id (barrer (Finset.univ : Finset α).toList))
        (fun _ => false))) (fun _ => false) = 0 := by
  classical
  refine ⟨fun f => ?_, ?_, rfl⟩
  · rw [corre_encadenar, tablaDe_deP]
    exact barrer_alcanza.1 f
  · rw [costoLl_deP]
    have hle := (barrer_alcanza (α := α)).2 (fun _ => false)
    have hge := costo_adversario _ (barrer_alcanza (α := α)).1
    omega

/-- **Todo el trabajo en la consulta**: el llenado no pregunta nada y la consulta barre. -/
theorem todo_en_la_consulta [Fintype α] :
    DecideExiste (encadenar (.fin () : Llenado α Unit) (fun _ => barrer (Finset.univ : Finset α).toList)) ∧
      costoLl (.fin () : Llenado α Unit) (fun _ => false) = 0 :=
  ⟨barrer_alcanza.1, rfl⟩

/-- **Repartido**: con tres opciones, el llenado mira la primera y guarda si era buena; la consulta, si la tabla dice
que no, barre las otras dos. Una pregunta más dos, y la suma es `|α| = 3`. -/
theorem repartido_tres :
    DecideExiste (encadenar (deP id (barrer [(0 : Fin 3)]))
        (fun T => if T then .resp true else barrer [(1 : Fin 3), 2])) ∧
      costoLl (deP id (barrer [(0 : Fin 3)])) (fun _ => false) = 1 ∧
      costo ((fun T : Bool => if T then (.resp true : Pregunta (Fin 3)) else barrer [(1 : Fin 3), 2])
        (tablaDe (deP id (barrer [(0 : Fin 3)])) (fun _ => false))) (fun _ => false) = 2 := by
  refine ⟨fun f => ?_, rfl, rfl⟩
  rw [corre_encadenar, tablaDe_deP]
  have h0 := corre_barrer f [(0 : Fin 3)]
  have h12 := corre_barrer f [(1 : Fin 3), 2]
  constructor
  · intro hc
    split at hc
    · rename_i hT
      obtain ⟨i, -, hi⟩ := h0.1 (by simpa using hT)
      exact ⟨i, hi⟩
    · obtain ⟨i, -, hi⟩ := h12.1 hc
      exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    split
    · rfl
    · rename_i hT
      apply h12.2
      refine ⟨i, ?_, hi⟩
      have : i ≠ 0 := fun e => hT (h0.2 ⟨0, by simp, e ▸ hi⟩)
      fin_cases i <;> simp_all

/-! ### Llenar la raíz ya cuesta todo -/

/-- **Llenar bien la entrada de la raíz cuesta `2^N` preguntas.** En el árbol de `N` elecciones visto como caja negra
(`f` dice si cada rama es solución), todo llenado cuya tabla acierta en la raíz («muerta si y solo si no hay
solución») pregunta al menos `2^N` veces con el oráculo todo `false`. La consulta que lee la raíz es gratis. -/
theorem llenar_raiz_cuesta (N : ℕ) (L : Llenado (List.Vector Bool N) (List Bool → Bool))
    (h : ∀ f, tablaDe L f [] = true ↔ ¬ ∃ v, f v = true) : 2 ^ N ≤ costoLl L (fun _ => false) := by
  have hdec : DecideExiste (encadenar L fun T => .resp (!T [])) := by
    intro f
    rw [corre_encadenar]
    simp only [corre, Bool.not_eq_true']
    rw [← not_iff_not, ← h f]
    simp
  have := trabajo_se_conserva L _ hdec
  rw [card_vector, Fintype.card_bool] at this
  simpa [costo, vistos] using this

/-- **Y alcanza**: barrer las `2^N` ramas y escribir la raíz acierta, con exactamente `2^N` preguntas. La hipótesis
de `llenar_raiz_cuesta` se cumple y la cota es exacta. -/
theorem llenar_raiz_exacto (N : ℕ) :
    (∀ f, tablaDe (deP (fun b (_ : List Bool) => !b) (barrer (Finset.univ : Finset (List.Vector Bool N)).toList)) f [] = true ↔
      ¬ ∃ v, f v = true) ∧
    costoLl (deP (fun b (_ : List Bool) => !b) (barrer (Finset.univ : Finset (List.Vector Bool N)).toList)) (fun _ => false) =
      2 ^ N := by
  classical
  have hdec := (barrer_alcanza (α := List.Vector Bool N)).1
  refine ⟨fun f => ?_, ?_⟩
  · rw [tablaDe_deP, Bool.not_eq_true', ← not_iff_not, ← hdec f]
    simp
  · rw [costoLl_deP]
    have hle := (barrer_alcanza (α := List.Vector Bool N)).2 (fun _ => false)
    have hge := costo_adversario _ hdec
    rw [card_vector, Fintype.card_bool] at hle hge
    omega

/-- Las soluciones de un oráculo sobre las ramas, como función sobre listas. -/
def solDe {N : ℕ} (f : List.Vector Bool N → Bool) (q : List Bool) : Bool :=
  if h : q.length = N then f ⟨q, h⟩ else false

/-- **La tabla perfecta acierta en la raíz.** Armada mirando `f` sin contar, es la tabla «gratis» de la primera parte:
por `llenar_raiz_cuesta`, llenarla preguntando cuesta al menos `2^N`. -/
theorem raiz_tablaLlena {N : ℕ} (f : List.Vector Bool N → Bool) :
    tablaLlena (solDe f) N [] = true ↔ ¬ ∃ v, f v = true := by
  rw [tablaLlena, Bool.not_eq_true', ← Bool.not_eq_true, vivoB_iff]
  apply not_congr
  constructor
  · rintro ⟨q, hq, hs⟩
    simp only [List.nil_append, List.length_nil, Nat.sub_zero] at hq hs
    refine ⟨⟨q, hq⟩, ?_⟩
    simpa [solDe, hq] using hs
  · rintro ⟨⟨q, hq⟩, hs⟩
    exact ⟨q, by simpa using hq, by simpa [solDe, hq] using hs⟩

end Sagitta.Map.Tiempo.ConservacionTrabajo
