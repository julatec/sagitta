import Sagitta.Map.CuboCostos
import Sagitta.Map.Informacion.MemoriaProfundidad
import Sagitta.Map.Informacion.Homogeneidad
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace

/-!
# El espacio de cslib y el cubo

Una piedra angular (25 nov 2026): varias cotas de Sagitta quedaron dichas en un modelo abstracto de memoria (el
`Automata` de `CuboCostos`, con `|σ| ≤ 2^S`; el sistema `δ : σ → Option σ` de `MemoriaPeriodica` y de
`MemoriaProfundidad`; el autómata homogéneo de `Homogeneidad`). Este archivo es el puente con el **espacio** de las
máquinas de Turing de varias cintas de cslib (`Turing.MultiTapeTM`, con `RunsInSpace`: celdas de las cintas de trabajo
visitadas, sumadas sobre las cintas).

## Lo que ya estaba en cslib (y no se repite)

* El conteo: `Turing.encard_fitsIn_le` y `MultiTapeTM.encard_cores_le` (cslib, `ConfigBound.lean`): un almacén (estado
  y cintas de trabajo) cuyas celdas no blancas y cabezales caben en ventanas `[-wᵢ, wᵢ]` toma a lo sumo
  `storageBound Γ Q k s = (|Q| + 1) · (2s + 1)^k · (|Γ| + 1)^(2s + k)` valores, y eso es `≤ base · 2^(exp · s)`
  (`storageBound_le_base_mul_pow`).
* El corolario de tiempo: `MultiTapeTM.haltsAt_le_card` (cslib-frontier, `LogSpace.lean`): una máquina que para dentro
  del espacio `s` para antes de `(n + 2) · storageBound Γ Q k s` pasos. Es el `DSPACE(s) ⊆ DTIME(2^O(s))` de siempre.

## Lo que se prueba aquí: el puente

1. **La ventana** (`deVentana`, `deVentana_toBounded`): el almacén restringido a la ventana uniforme `[-S, S]` en cada
   cinta (`BoundedStorage`, un tipo finito) se puede volver a extender, y la vuelta es exacta sobre los almacenes que
   caben. Una máquina con `RunsInSpace input S` cabe en esa ventana en todo instante (`cabe`).
2. **La máquina es un `Automata` del cubo** (`automata`): estados `σ = Fin (n + 2) × BoundedStorage` (posición del
   cabezal de entrada y almacén en la ventana), la **consulta es la posición del cabezal de entrada** y la **respuesta es
   el símbolo de la entrada en esa celda** (`simboloEn`): la entrada hace de verificador. La salida es una `lectura`
   del estado final. Corre igual que la máquina (`corre_automata`, `corre_automata_none`).
3. **El tamaño, con la constante a la vista** (`card_estados`, `card_estados_bits`):
   `|σ| ≤ (n + 2) · storageBound Γ Q k (k·S) ≤ 2^bitsEspacio`, con
   `bitsEspacio = ⌈log₂(n + 2)⌉ + ⌈log₂ base⌉ + exp · k · S`, `base = (|Q| + 1) · 2^((|Γ| + 1)k + k)` y
   `exp = 2(|Γ| + 1) + k`. Es el `2^(c·S + log|Q| + log n)` del enunciado; el `k · log S` de los cabezales queda dentro de
   `exp · k · S` (se pierde un factor `k` en el exponente por usar la ventana uniforme).
4. **Lo que pasa a valer para máquinas de cslib**:
   * la ley del cubo con verificador informativo (`ley_cubo_mt`, `ley_cubo_mt_log`): si máquinas de espacio `S`
     indexadas por `|P| ≤ 2^L` programas y `|C| ≤ 2^s` citas hallan cada `y` de `Y` leyendo `enc y` (largo `n`) en a lo
     sumo `t` pasos, `|Y| ≤ 2^L · 2^s · min (2^(b·t)) 2^bitsEspacio`, con `|Γ| + 1 ≤ 2^b`;
   * parar o ciclar (`parar_o_ciclar_mt`): o para en a lo sumo `|σ|` pasos, o no para nunca y la sucesión de
     núcleos (`Cfg.core`: lo que la máquina todavía puede leer) es finalmente periódica, con preperíodo más período
     `≤ |σ| + 1`;
   * **espacio `S` da tiempo `2^O(S)`** (`para_pronto_mt`): si para, para antes de `2^bitsEspacio` pasos. Sale del puente y
     de `MemoriaProfundidad.para_antes_de_dos_pow`; coincide (con otra constante) con `haltsAt_le_card` de cslib-frontier;
   * la memoria acota la profundidad (`memoria_acota_profundidad_mt`), con la misma hipótesis `Simula` de
     `MemoriaProfundidad`, ahora con `s = bitsEspacio`;
   * la CHT: la máquina es un autómata **homogéneo** (`paso_automata`: el paso de `Homogeneidad` sigue a la máquina), así
     que no sabe la hora (`no_sabe_la_hora_mt`: si un núcleo se repite antes de parar, desde ahí todo se repite).

## Controles y mutantes

* `control_ventana`: sin `FitsIn` la vuelta de la ventana pierde celdas (refutación concreta).
* `control_cabezal_entrada`: sin el término `⌈log₂(n + 2)⌉` la cota en bits es falsa (refutación concreta, `n = 0`).
* `control_paraYa`: las hipótesis no son vacías: una máquina sin cintas de trabajo corre en espacio `0`, para en el paso
  `1`, y el corolario se aplica.
* Mutantes (en el área de trabajo de la sesión, 25 nov 2026; los seis fallan): `para_pronto_mt` sin `RunsInSpace`
  (falla: no hay ventana, `traza_none_iff` pide `hs`); `parar_o_ciclar_mt` con `i + p ≤ N` en vez de `N + 1` (falla en
  `omega`: el estado de parada es uno más); `ley_cubo_mt` con `2^(bitsEspacio − 1)` (falla: la cota del espacio es
  `|σ|`, no la mitad); `corre_automata` sin `u ≤ t` (falla en `omega`); `no_sabe_la_hora_mt` sin «no paró antes de
  `j`» (falla en `assumption`); `memoria_acota_profundidad_mt` con `prof x + 4` (falla: la constante es `3`).

## Lo que NO se prueba

* **La salida de la cinta de salida.** El núcleo no incluye la cinta de salida (la máquina no la lee: cslib la deja fuera
  de `Cfg.core`). La `lectura` del autómata ve el estado y las cintas de trabajo al parar; una máquina que decide con la
  cinta de salida hay que modificarla para que deje la respuesta en una cinta de trabajo. No se formaliza esa
  modificación.
* **Ventanas por cinta.** Se usa la ventana uniforme `[-S, S]` en cada una de las `k` cintas, así que el exponente es
  `exp · k · S` y no `exp · S` como en `encard_storages_le` de cslib (que usa la ventana de la corrida más larga). Para
  `O(S)` da igual.
* Nada sobre P contra NP; nada nuevo en el conteo (es de cslib). Lo propio es el puente y que las leyes de Sagitta valgan
  para las máquinas de cslib con la constante explícita.
-/

namespace Sagitta.Map.Informacion.EspacioCubo

open Turing Turing.MultiTapeTM
open Sagitta.Map.Tiempo.CuboCostos
open Sagitta.Map.Continuo.Memoria
open Sagitta.Map.Continuo.Regreso (Para)

variable {k : ℕ} {Symbol State : Type}

/-! ## 1. La ventana -/

/-- La ventana uniforme: `S` celdas a cada lado del origen en cada una de las `k` cintas. -/
abbrev ventana (k S : ℕ) : Fin k → ℕ := fun _ => S

/-- **Volver de la ventana a la cinta entera**: fuera de la ventana, blanco. -/
def deVentana {w : Fin k → ℕ} (b : BoundedStorage Symbol State w) : Storage Symbol State k :=
  ⟨b.1, fun j z => if h : z ∈ window (w j) then b.2.1 j ⟨z, h⟩ else none, fun j => (b.2.2 j : ℤ)⟩

/-- **La vuelta es exacta sobre lo que cabe.** -/
theorem deVentana_toBounded {w : Fin k → ℕ} {x : Storage Symbol State k} (h : x.FitsIn w) :
    deVentana (x.toBounded w) = x := by
  apply Storage.ext
  · rfl
  · funext j z
    simp only [deVentana, Storage.toBounded]
    split_ifs with hz
    · rfl
    · by_contra hne
      exact hz (mem_window.mpr (h.cell_le j z fun e => hne e.symm))
  · funext j
    simp only [deVentana, Storage.toBounded]
    rw [dite_eq_left_of_eq_true (eq_true (mem_window.mpr (h.pos_le j)))]

/-- Por eso restringir a la ventana es inyectivo sobre lo que cabe. -/
theorem toBounded_inj {w : Fin k → ℕ} {x y : Storage Symbol State k} (hx : x.FitsIn w) (hy : y.FitsIn w)
    (h : x.toBounded w = y.toBounded w) : x = y := by
  rw [← deVentana_toBounded hx, ← deVentana_toBounded hy, h]

/-! ## 2. El paso sobre el núcleo -/

section Paso

variable (tm : MultiTapeTM k Symbol State)

/-- **El núcleo siguiente**: desde la posición del cabezal de entrada, el almacén y el símbolo leído en la entrada. Es
`Action.apply` sin la cinta de salida. -/
noncomputable def pasoNucleo {n : ℕ} (x : Fin (n + 2) × Storage Symbol State k) (r : Option Symbol) :
    Fin (n + 2) × Storage Symbol State k :=
  match x.2.state with
  | none => x
  | some q =>
    (moveInputPos x.1 (tm.tr q r fun i => x.2.workTapes i (x.2.workTapePos i)).inputTape,
      ⟨(tm.tr q r fun i => x.2.workTapes i (x.2.workTapePos i)).state,
        fun i => match ((tm.tr q r fun i => x.2.workTapes i (x.2.workTapePos i)).workTapes i).1 with
          | none => x.2.workTapes i
          | some s => Function.update (x.2.workTapes i) (x.2.workTapePos i) s,
        fun i => x.2.workTapePos i + ((tm.tr q r fun i => x.2.workTapes i (x.2.workTapePos i)).workTapes i).2⟩)

/-- El símbolo de la entrada `w` en la posición `i` del cabezal (corrida en uno: `0` y `|w| + 1` son blancos). -/
def simboloEn (w : List Symbol) (i : ℕ) : Option Symbol := if i = 0 then none else w[i - 1]?

variable {tm}

theorem inputSymbol_eq {input : List Symbol} (c : Cfg k Symbol State input) :
    c.inputSymbol = simboloEn input c.inputPos.val := by
  unfold Cfg.inputSymbol simboloEn
  have hlt := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have e : c.inputPos = 0 := Fin.ext h0
    simp [e]
  · have e : c.inputPos ≠ 0 := fun e => h0 (by simp [e])
    simp only [e, h0, dite_false, ite_false]
    by_cases h1 : c.inputPos.val = input.length + 1
    · simp only [h1, dite_true]
      exact (List.getElem?_eq_none (by omega)).symm
    · simp only [h1, dite_false]
      exact (List.getElem?_eq_getElem (by omega)).symm

/-- **El paso de la máquina, visto en el núcleo**, depende solo del núcleo y del símbolo leído. -/
theorem core_step {input : List Symbol} (c : Cfg k Symbol State input) :
    (tm.step c).core = pasoNucleo tm c.core c.inputSymbol := by
  rcases c with ⟨q, i, w, p, o⟩
  cases q with
  | none => rw [step_of_halt rfl]; rfl
  | some q => rw [step_of_state rfl]; rfl

end Paso

/-! ## 3. La máquina como autómata del cubo -/

/-- Los estados del autómata: la posición del cabezal de entrada y el almacén en la ventana. Un tipo finito. -/
abbrev Estados (Symbol State : Type) (k n S : ℕ) := Fin (n + 2) × BoundedStorage Symbol State (ventana k S)

/-- El almacén al empezar: el estado inicial, las cintas en blanco y los cabezales en `0`. -/
def almacenInicial (q₀ : State) : Storage Symbol State k := ⟨some q₀, fun _ _ => none, fun _ => 0⟩

variable (tm : MultiTapeTM k Symbol State)

/-- **La máquina de cslib como `Automata` del cubo.** Consulta la posición de su cabezal de entrada y oye el símbolo de
la entrada que está ahí; da un paso de la máquina sobre el almacén en la ventana; cuando el estado es el de parada,
devuelve la `lectura` del estado. -/
noncomputable def automata {Y : Type} (n S : ℕ) (lectura : Estados Symbol State k n S → Y) :
    Automata (Estados Symbol State k n S) ℕ (Option Symbol) Y where
  inicio := (1, (almacenInicial tm.q₀).toBounded (ventana k S))
  consulta x := x.1.val
  δ x r := ((pasoNucleo tm (x.1, deVentana x.2) r).1, (pasoNucleo tm (x.1, deVentana x.2) r).2.toBounded (ventana k S))
  salida x := if x.2.1.isNone then some (lectura x) else none

/-- La configuración vista en la ventana, con el largo de la entrada fijado en `n`. -/
def enVentana {input : List Symbol} {n : ℕ} (h : input.length = n) (S : ℕ) (c : Cfg k Symbol State input) :
    Estados Symbol State k n S :=
  (Fin.cast (by rw [h]) c.inputPos, c.storage.toBounded (ventana k S))

variable {tm}

/-- **Con espacio `S`, la máquina cabe en la ventana en todo instante.** -/
theorem cabe {input : List Symbol} {S : ℕ} (hs : tm.RunsInSpace input S) (t : ℕ) :
    (tm.runFrom (tm.initCfg input) t).storage.FitsIn (ventana k S) := by
  let p := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  have hp := p.storage_fitsIn
  refine Storage.FitsIn_mono (fun j => ?_) hp
  calc p.spaceUsedByTape j ≤ ∑ i, p.spaceUsedByTape i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ S := hs p

theorem inicio_automata {Y : Type} {input : List Symbol} {n : ℕ} (h : input.length = n) (S : ℕ)
    (lectura : Estados Symbol State k n S → Y) :
    (automata tm n S lectura).inicio = enVentana h S (tm.initCfg input) := by
  subst h
  rfl

/-- **Un paso del autómata es un paso de la máquina**, mientras el almacén quepa en la ventana. -/
theorem delta_automata {Y : Type} {input : List Symbol} {n : ℕ} (h : input.length = n) {S : ℕ}
    (lectura : Estados Symbol State k n S → Y) {c : Cfg k Symbol State input} (hc : c.storage.FitsIn (ventana k S)) :
    (automata tm n S lectura).δ (enVentana h S c)
        (simboloEn input ((automata tm n S lectura).consulta (enVentana h S c))) =
      enVentana h S (tm.step c) := by
  subst h
  have e1 : deVentana (c.storage.toBounded (ventana k S)) = c.storage := deVentana_toBounded hc
  have e2 := core_step (tm := tm) c
  rw [inputSymbol_eq] at e2
  simp only [automata, enVentana, Fin.cast_eq_self, e1]
  have e3 : ((c.inputPos, c.storage) : Fin (input.length + 2) × Storage Symbol State k) = c.core := rfl
  rw [e3, ← e2]
  rfl

/-! ## 4. La corrida del autómata es la de la máquina -/

section Corrida

variable {input : List Symbol} {n S : ℕ} (h : input.length = n)

/-- La salida del autómata en una configuración vista en la ventana: la `lectura` si el estado es el de parada. -/
theorem salida_enVentana {Y : Type} (lectura : Estados Symbol State k n S → Y) (c : Cfg k Symbol State input) :
    (automata tm n S lectura).salida (enVentana h S c) =
      if c.state.isNone then some (lectura (enVentana h S c)) else none := rfl

theorem salida_vivo {Y : Type} (lectura : Estados Symbol State k n S → Y) {c : Cfg k Symbol State input}
    (hc : ¬ c.Halted) : (automata tm n S lectura).salida (enVentana h S c) = none := by
  rw [salida_enVentana]
  cases hst : c.state with
  | none => exact absurd hst hc
  | some q => rfl

/-- **Paso a paso**: el autómata, con la entrada como verificador, sigue a la máquina. -/
theorem paso_enVentana {Y : Type} (lectura : Estados Symbol State k n S → Y) (hs : tm.RunsInSpace input S) (j : ℕ) :
    (automata tm n S lectura).δ (enVentana h S (tm.runFrom (tm.initCfg input) j))
        (simboloEn input ((automata tm n S lectura).consulta (enVentana h S (tm.runFrom (tm.initCfg input) j)))) =
      enVentana h S (tm.runFrom (tm.initCfg input) (j + 1)) := by
  rw [delta_automata h lectura (cabe hs j), runFrom_succ]

/-- **El autómata devuelve lo que la máquina deja al parar.** Si la máquina para en el paso `u ≤ t`, el autómata con
presupuesto `t` devuelve la lectura de la configuración del paso `u`. -/
theorem corre_automata {Y : Type} (lectura : Estados Symbol State k n S → Y) (hs : tm.RunsInSpace input S) {u t : ℕ}
    (hu : tm.HaltsAt (tm.initCfg input) u) (ht : u ≤ t) :
    (automata tm n S lectura).corre (simboloEn input) t (automata tm n S lectura).inicio =
      some (lectura (enVentana h S (tm.runFrom (tm.initCfg input) u))) := by
  have aux : ∀ m j, j ≤ u → u ≤ j + m →
      (automata tm n S lectura).corre (simboloEn input) m (enVentana h S (tm.runFrom (tm.initCfg input) j)) =
        some (lectura (enVentana h S (tm.runFrom (tm.initCfg input) u))) := by
    intro m
    induction m with
    | zero =>
      intro j hj hjm
      obtain rfl : j = u := by omega
      rw [Automata.corre_cero, salida_enVentana, hu.halted]
      rfl
    | succ m ih =>
      intro j hj hjm
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · refine Automata.corre_some ?_ _
        rw [salida_enVentana, hu.halted]
        rfl
      · have hno := salida_vivo (tm := tm) h lectura (hu.not_halted hlt)
        rw [Automata.corre_none hno, paso_enVentana h lectura hs]
        exact ih (j + 1) (by omega) (by omega)
  rw [inicio_automata h]
  exact aux t 0 (Nat.zero_le _) (by omega)

include h in
/-- **Si la máquina no para en `t` pasos, el autómata no devuelve nada en `t` consultas.** -/
theorem corre_automata_none {Y : Type} (lectura : Estados Symbol State k n S → Y) (hs : tm.RunsInSpace input S)
    {t : ℕ} (hno : ∀ j ≤ t, ¬ (tm.runFrom (tm.initCfg input) j).Halted) :
    (automata tm n S lectura).corre (simboloEn input) t (automata tm n S lectura).inicio = none := by
  have aux : ∀ m j, j + m ≤ t →
      (automata tm n S lectura).corre (simboloEn input) m (enVentana h S (tm.runFrom (tm.initCfg input) j)) = none := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Automata.corre_cero]
      exact salida_vivo (tm := tm) h lectura (hno j (by omega))
    | succ m ih =>
      intro j hj
      have hn := salida_vivo (tm := tm) h lectura (hno j (by omega))
      rw [Automata.corre_none hn, paso_enVentana h lectura hs]
      exact ih (j + 1) (by omega)
  rw [inicio_automata h]
  exact aux t 0 (by omega)

end Corrida

/-! ## 5. El tamaño del autómata -/

section Tamano

variable [Fintype Symbol] [Fintype State]

/-- **Los bits de memoria efectiva** de una máquina de `k` cintas con espacio `S` sobre entradas de largo `n`:
`⌈log₂(n + 2)⌉ + ⌈log₂ base⌉ + exp · k · S`, con `base = (|Q| + 1) · 2^((|Γ| + 1)k + k)` y `exp = 2(|Γ| + 1) + k`. -/
def bitsEspacio (Symbol State : Type) [Fintype Symbol] [Fintype State] (k n S : ℕ) : ℕ :=
  Nat.clog 2 (n + 2) + Nat.clog 2 (storageBoundBase Symbol State k) + storageBoundExp Symbol k * (k * S)

/-- **El conteo**: `|σ| ≤ (n + 2) · storageBound Γ Q k (k·S)`. Es el de cslib con la ventana uniforme. -/
theorem card_estados (n S : ℕ) :
    Fintype.card (Estados Symbol State k n S) ≤ (n + 2) * storageBound Symbol State k (k * S) := by
  rw [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (card_boundedStorage_le (by simp))

/-- **En bits**: `|σ| ≤ 2^bitsEspacio`. -/
theorem card_estados_bits (n S : ℕ) :
    Fintype.card (Estados Symbol State k n S) ≤ 2 ^ bitsEspacio Symbol State k n S := by
  refine (card_estados n S).trans ?_
  unfold bitsEspacio
  rw [pow_add, pow_add, mul_assoc]
  exact Nat.mul_le_mul (Nat.le_pow_clog one_lt_two _)
    ((storageBound_le_base_mul_pow _).trans (Nat.mul_le_mul_right _ (Nat.le_pow_clog one_lt_two _)))

/-- Más espacio, más bits: `bitsEspacio` es monótono en `S` (lineal, con pendiente `exp · k`). -/
theorem bitsEspacio_mono {n S S' : ℕ} (h : S ≤ S') :
    bitsEspacio Symbol State k n S ≤ bitsEspacio Symbol State k n S' := by
  unfold bitsEspacio
  have := Nat.mul_le_mul_left (storageBoundExp Symbol k) (Nat.mul_le_mul_left k h)
  omega

end Tamano

/-! ## 6. La ley del cubo para máquinas de cslib -/

/-- **La ley del cubo para máquinas de cslib con espacio `S`.** Máquinas `M p c` de `k` cintas (las mismas `Γ` y `Q`
finitas), indexadas por `|P| ≤ 2^L` programas y `|C| ≤ 2^s` citas, que con espacio `S` hallan cada `y` de `Y` leyendo su
codificación `enc y` (de largo `n`) y parando en a lo sumo `t` pasos, con la respuesta en el estado final: entonces
`|Y| ≤ 2^L · 2^s · min (2^(b·t)) 2^bitsEspacio`, con `|Γ| + 1 ≤ 2^b`. Es `ley_cubo_general` por el puente. -/
theorem ley_cubo_mt {P C Y : Type} [Fintype P] [Fintype C] [Fintype Y] [Fintype Symbol] [Fintype State]
    {L s b n S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hR : Fintype.card Symbol + 1 ≤ 2 ^ b)
    (M : P → C → MultiTapeTM k Symbol State) (lectura : P → C → Estados Symbol State k n S → Y)
    (enc : Y → List Symbol) (hlen : ∀ y, (enc y).length = n)
    (h : ∀ y, ∃ p c u, u ≤ t ∧ (M p c).RunsInSpace (enc y) S ∧ (M p c).HaltsAt ((M p c).initCfg (enc y)) u ∧
      lectura p c (enVentana (hlen y) S ((M p c).runFrom ((M p c).initCfg (enc y)) u)) = y) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * min (2 ^ (b * t)) (2 ^ bitsEspacio Symbol State k n S) := by
  refine ley_cubo_general hP hC (card_estados_bits n S) (by rwa [Fintype.card_option]) (fun y => simboloEn (enc y))
    (fun p c => automata (M p c) n S (lectura p c)) (fun y => ?_)
  obtain ⟨p, c, u, hut, hs, hu, hl⟩ := h y
  exact ⟨p, c, (corre_automata (hlen y) (lectura p c) hs hu hut).trans (congrArg some hl)⟩

/-- **La ley del cubo para máquinas de cslib, en bits**: `⌈log₂ |Y|⌉ ≤ L + s + min (b·t) bitsEspacio`. -/
theorem ley_cubo_mt_log {P C Y : Type} [Fintype P] [Fintype C] [Fintype Y] [Fintype Symbol] [Fintype State]
    {L s b n S t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hR : Fintype.card Symbol + 1 ≤ 2 ^ b)
    (M : P → C → MultiTapeTM k Symbol State) (lectura : P → C → Estados Symbol State k n S → Y)
    (enc : Y → List Symbol) (hlen : ∀ y, (enc y).length = n)
    (h : ∀ y, ∃ p c u, u ≤ t ∧ (M p c).RunsInSpace (enc y) S ∧ (M p c).HaltsAt ((M p c).initCfg (enc y)) u ∧
      lectura p c (enVentana (hlen y) S ((M p c).runFrom ((M p c).initCfg (enc y)) u)) = y) :
    Nat.clog 2 (Fintype.card Y) ≤ L + s + min (b * t) (bitsEspacio Symbol State k n S) := by
  refine ley_cubo_general_log hP hC (card_estados_bits n S) (by rwa [Fintype.card_option]) (fun y => simboloEn (enc y))
    (fun p c => automata (M p c) n S (lectura p c)) (fun y => ?_)
  obtain ⟨p, c, u, hut, hs, hu, hl⟩ := h y
  exact ⟨p, c, (corre_automata (hlen y) (lectura p c) hs hu hut).trans (congrArg some hl)⟩

/-! ## 7. Parar o ciclar, y espacio `S` da tiempo `2^O(S)` -/

section Sistema

variable (tm) in
/-- **La máquina con su entrada como sistema determinista sobre un tipo finito** (el de `MemoriaPeriodica`): un paso del
autómata con la entrada fija; `none` cuando el estado siguiente es el de parada. -/
noncomputable def sistema (n S : ℕ) (input : List Symbol) :
    Estados Symbol State k n S → Option (Estados Symbol State k n S) := fun x =>
  if ((automata tm n S fun _ => ()).δ x (simboloEn input x.1.val)).2.1.isNone then none
  else some ((automata tm n S fun _ => ()).δ x (simboloEn input x.1.val))

variable {input : List Symbol} {S : ℕ}

/-- **La traza del sistema es la corrida de la máquina**: `none` desde que para, y la configuración vista en la ventana
mientras no. -/
theorem traza_sistema (hs : tm.RunsInSpace input S) (m : ℕ) :
    traza (sistema tm input.length S input) (enVentana rfl S (tm.initCfg input)) m =
      if (tm.runFrom (tm.initCfg input) m).state.isNone then none
      else some (enVentana rfl S (tm.runFrom (tm.initCfg input) m)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [traza, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]
    by_cases hm : (tm.runFrom (tm.initCfg input) m).state.isNone
    · have e : tm.runFrom (tm.initCfg input) (m + 1) = tm.runFrom (tm.initCfg input) m := by
        rw [runFrom_succ, step_of_halt (Option.isNone_iff_eq_none.mp hm)]
      rw [if_pos hm, e, if_pos hm]
      rfl
    · rw [if_neg hm]
      have hp : (automata tm input.length S fun _ => ()).δ (enVentana rfl S (tm.runFrom (tm.initCfg input) m))
          (simboloEn input (enVentana rfl S (tm.runFrom (tm.initCfg input) m)).1.val) =
            enVentana rfl S (tm.runFrom (tm.initCfg input) (m + 1)) :=
        paso_enVentana rfl (fun _ => ()) hs m
      change sistema tm input.length S input (enVentana rfl S (tm.runFrom (tm.initCfg input) m)) = _
      unfold sistema
      rw [hp]
      rfl

theorem traza_none_iff (hs : tm.RunsInSpace input S) (m : ℕ) :
    traza (sistema tm input.length S input) (enVentana rfl S (tm.initCfg input)) m = none ↔
      (tm.runFrom (tm.initCfg input) m).Halted := by
  rw [traza_sistema hs]
  by_cases hm : (tm.runFrom (tm.initCfg input) m).state.isNone
  · simp only [if_pos hm, true_iff]; exact Option.isNone_iff_eq_none.mp hm
  · simp only [if_neg hm, reduceCtorEq, false_iff]
    exact fun e => hm (Option.isNone_iff_eq_none.mpr e)

variable [Fintype Symbol] [Fintype State]

/-- **Parar o ciclar, para máquinas de cslib con espacio `S`.** O la máquina para en a lo sumo
`N = (n + 2) · storageBound Γ Q k (k·S)` pasos, o no para nunca y la sucesión de sus núcleos (lo que todavía puede leer:
cabezal de entrada, estado y cintas de trabajo) es finalmente periódica, con preperíodo más período a lo sumo `N + 1`. -/
theorem parar_o_ciclar_mt (hs : tm.RunsInSpace input S) :
    (∃ m ≤ (input.length + 2) * storageBound Symbol State k (k * S), (tm.runFrom (tm.initCfg input) m).Halted) ∨
    ((∀ m, ¬ (tm.runFrom (tm.initCfg input) m).Halted) ∧
      ∃ i p, 0 < p ∧ i + p ≤ (input.length + 2) * storageBound Symbol State k (k * S) + 1 ∧
        ∀ m, i ≤ m → (tm.runFrom (tm.initCfg input) (m + p)).core = (tm.runFrom (tm.initCfg input) m).core) := by
  have hc := card_estados (Symbol := Symbol) (State := State) (k := k) input.length S
  rcases Sagitta.Map.Informacion.MemoriaProfundidad.parar_o_ciclar
      (sistema tm input.length S input) (enVentana rfl S (tm.initCfg input)) with ⟨m, hm, e⟩ | ⟨hno, i, p, hp, hip, hper⟩
  · exact Or.inl ⟨m, hm.trans hc, (traza_none_iff hs m).mp e⟩
  · refine Or.inr ⟨fun m hm => hno m ((traza_none_iff hs m).mpr hm), i, p, hp, by omega, fun m hm => ?_⟩
    have e := hper m hm
    rw [traza_sistema hs, traza_sistema hs] at e
    have h1 : ¬ (tm.runFrom (tm.initCfg input) (m + p)).state.isNone := fun h =>
      hno (m + p) ((traza_none_iff hs _).mpr (Option.isNone_iff_eq_none.mp h))
    have h2 : ¬ (tm.runFrom (tm.initCfg input) m).state.isNone := fun h =>
      hno m ((traza_none_iff hs _).mpr (Option.isNone_iff_eq_none.mp h))
    rw [if_neg h1, if_neg h2, Option.some_inj] at e
    simp only [enVentana, Fin.cast_eq_self, Prod.mk.injEq] at e
    exact Prod.ext e.1 (toBounded_inj (cabe hs _) (cabe hs _) e.2)

/-- **Espacio `S` da tiempo `2^O(S)`, por el puente.** Una máquina de cslib con espacio `S` que para, para antes de
`2^bitsEspacio` pasos. Sale de `MemoriaProfundidad.para_antes_de_dos_pow` sobre el sistema del puente. -/
theorem para_pronto_mt (hs : tm.RunsInSpace input S) (hpara : ∃ t, (tm.runFrom (tm.initCfg input) t).Halted) :
    ∃ m ≤ 2 ^ bitsEspacio Symbol State k input.length S, (tm.runFrom (tm.initCfg input) m).Halted := by
  obtain ⟨t, ht⟩ := hpara
  obtain ⟨m, hm, e⟩ := Sagitta.Map.Informacion.MemoriaProfundidad.para_antes_de_dos_pow
    (sistema tm input.length S input) (enVentana rfl S (tm.initCfg input)) (card_estados_bits input.length S)
    ⟨t, (traza_none_iff hs t).mpr ht⟩
  exact ⟨m, hm, (traza_none_iff hs m).mp e⟩

/-- **El mismo corolario con la constante de cslib-frontier**: el paso de parada `u` cumple a la vez la cota del puente
y la de `haltsAt_le_card`. -/
theorem para_pronto_mt_cslib (hs : tm.RunsInSpace input S) {u : ℕ} (hu : tm.HaltsAt (tm.initCfg input) u) :
    u ≤ 2 ^ bitsEspacio Symbol State k input.length S ∧
      u ≤ (input.length + 2) * storageBound Symbol State k S := by
  refine ⟨?_, haltsAt_le_card hs hu⟩
  obtain ⟨m, hm, e⟩ := para_pronto_mt hs ⟨u, hu.halted⟩
  exact (hu.le_of_halted e).trans hm

/-- **La memoria acota la profundidad, para máquinas de cslib.** Si la máquina para dentro del espacio `S` y un código
`p` que produce `x` no tarda más que ella (en cada paso en que la máquina ya paró, la evaluación de `p` cabe), entonces
`prof x + 3 ≤ |p| + bitsEspacio`. Es `MemoriaProfundidad.memoria_acota_profundidad` por el puente. -/
theorem memoria_acota_profundidad_mt (hs : tm.RunsInSpace input S)
    (hpara : ∃ t, (tm.runFrom (tm.initCfg input) t).Halted) {p : Nat.Partrec.Code} {x : ℕ}
    (hp : Sagitta.Map.Tiempo.KolmogorovTiempo.Produce p x)
    (hsim : ∀ m, (tm.runFrom (tm.initCfg input) m).Halted → (Nat.Partrec.Code.evaln m p 0).isSome) :
    Sagitta.Map.Informacion.Profundidad.prof x + 3 ≤
      Sagitta.Map.Tiempo.KolmogorovTiempo.largo p + bitsEspacio Symbol State k input.length S := by
  obtain ⟨t, ht⟩ := hpara
  exact Sagitta.Map.Informacion.MemoriaProfundidad.memoria_acota_profundidad
    (sistema tm input.length S input) (enVentana rfl S (tm.initCfg input)) (card_estados_bits input.length S)
    ⟨t, (traza_none_iff hs t).mpr ht⟩ hp (fun m e => hsim m ((traza_none_iff hs m).mp e))

end Sistema

/-! ## 8. La CHT: la máquina es un autómata homogéneo -/

section Homogeneo

open Sagitta.Map.Informacion.Homogeneidad (paso no_sabe_la_hora)

variable {input : List Symbol} {n S : ℕ}

/-- **El paso homogéneo de `Homogeneidad` sigue a la máquina**, también después de parar. -/
theorem paso_automata (h : input.length = n) {Y : Type} (lectura : Estados Symbol State k n S → Y)
    (hs : tm.RunsInSpace input S) (t : ℕ) :
    (paso (automata tm n S lectura) (simboloEn input))^[t] (enVentana h S (tm.initCfg input)) =
      enVentana h S (tm.runFrom (tm.initCfg input) t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    exact paso_enVentana h lectura hs t

/-- **Una máquina de cslib no sabe la hora** (la CHT, por el puente): si el núcleo del paso `j` repite el del paso
`i ≤ j` y la máquina no paró antes de `j`, el autómata devuelve lo mismo con `i + t` y con `j + t` consultas. -/
theorem no_sabe_la_hora_mt (h : input.length = n) {Y : Type} (lectura : Estados Symbol State k n S → Y)
    (hs : tm.RunsInSpace input S) {i j : ℕ} (hij : i ≤ j)
    (hj : ∀ m < j, ¬ (tm.runFrom (tm.initCfg input) m).Halted)
    (hcore : (tm.runFrom (tm.initCfg input) i).core = (tm.runFrom (tm.initCfg input) j).core) (t : ℕ) :
    (automata tm n S lectura).corre (simboloEn input) (i + t) (automata tm n S lectura).inicio =
      (automata tm n S lectura).corre (simboloEn input) (j + t) (automata tm n S lectura).inicio := by
  rw [inicio_automata h]
  refine no_sabe_la_hora _ _ (fun m hm => ?_) hij ?_ t
  · rw [paso_automata h lectura hs]
    exact salida_vivo (tm := tm) h lectura (hj m hm)
  · rw [paso_automata h lectura hs, paso_automata h lectura hs]
    have e1 : (tm.runFrom (tm.initCfg input) i).inputPos = (tm.runFrom (tm.initCfg input) j).inputPos :=
      congrArg Prod.fst hcore
    have e2 : (tm.runFrom (tm.initCfg input) i).storage = (tm.runFrom (tm.initCfg input) j).storage :=
      congrArg Prod.snd hcore
    simp only [enVentana, e1, e2]

end Homogeneo

/-! ## 9. Controles -/

section Controles

/-- **Control de la ventana**: sin `FitsIn`, la vuelta de la ventana pierde celdas. Una cinta con un símbolo en la celda
`1` y la ventana `[0, 0]`: la vuelta deja la celda en blanco. -/
theorem control_ventana : ¬ ∀ x : Storage Unit Unit 1, deVentana (x.toBounded (ventana 1 0)) = x := by
  intro h
  have := congrArg (fun y => y.workTapes 0 1) (h ⟨none, fun _ z => if z = 1 then some () else none, fun _ => 0⟩)
  simp [deVentana, Storage.toBounded, window] at this

/-- **Control del cabezal de entrada**: sin el término `⌈log₂(n + 2)⌉` la cota en bits es falsa. Sin cintas de trabajo y
con `Γ = Q = ∅`, el almacén es uno solo, la base es `1`, y aun así hay `n + 2 = 2` estados. -/
theorem control_cabezal_entrada : ¬ Fintype.card (Estados Empty Empty 0 0 0) ≤
    2 ^ (Nat.clog 2 (storageBoundBase Empty Empty 0) + storageBoundExp Empty 0 * (0 * 0)) := by
  simp [Estados, BoundedStorage, storageBoundBase, storageBoundExp]

/-- Una máquina sin cintas de trabajo que para en el primer paso. -/
noncomputable def paraYa : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ => ⟨0, fun i => i.elim0, none, none⟩

/-- **Control positivo**: las hipótesis del puente se cumplen en una máquina de verdad. `paraYa` corre en espacio `0`
(no tiene cintas de trabajo), para en el paso `1`, y el corolario da el corte `2^bitsEspacio`. -/
theorem control_paraYa (input : List Bool) :
    paraYa.RunsInSpace input 0 ∧ paraYa.HaltsAt (paraYa.initCfg input) 1 ∧
      ∃ m ≤ 2 ^ bitsEspacio Bool Unit 0 input.length 0, (paraYa.runFrom (paraYa.initCfg input) m).Halted := by
  have hs : paraYa.RunsInSpace input 0 := MultiTapeNTM.runsInSpace_zero_tapes _ _ _
  have h1 : (paraYa.runFrom (paraYa.initCfg input) 1).Halted := by
    rw [runFrom_one, step_of_state (q := ()) rfl]
    simp only [paraYa, tr_ofTr]
    rfl
  refine ⟨hs, ⟨h1, fun s hs1 => ?_⟩, para_pronto_mt hs ⟨1, h1⟩⟩
  obtain rfl : s = 0 := by omega
  simp [runFrom, Cfg.Halted]

end Controles

end Sagitta.Map.Informacion.EspacioCubo
