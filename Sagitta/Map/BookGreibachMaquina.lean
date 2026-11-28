import Sagitta.Map.SimulacionLineal
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-!
# La máquina de Book y Greibach, primera parte: las pasadas por cinta, como máquinas de cslib

Tercer ladrillo hacia la jerarquía no determinista **fina** (`NTIME(f) ⊊ NTIME(g)` si `f(n+1) ∈ o(g(n))`,
Seiferas–Fischer–Meyer 1978, Žák 1983), que la prueba de Williams (NEXP ⊄ ACC⁰) necesita.
`Sagitta/Map/SimulacionLineal.lean` probó el corazón lógico de la simulación de Book y Greibach (una traza es válida
si y solo si es consistente cinta por cinta, `validaC_iff`) y dejó el costo de cada pasada **declarado**
(`Pasada`). Acá la pasada deja de ser un modelo de costo: es una `MultiTapeTM` de cslib, con una sola cinta de
trabajo, y su tiempo se prueba sobre la semántica de la biblioteca (`runFrom`, `RunsInTime`, `RunsInSpace`).

## 1. El mapa de construcción de cslib-frontier (meta 1)

Hay tres niveles para escribir una máquina y probar su tiempo; los tres se probaron o se leyeron para elegir:

* **Máquina cruda.** `Turing.MultiTapeTM.ofTr q₀ tr` (cslib, `MultiTape/Deterministic.lean`) arma una máquina
  determinista desde una función de transición `estado → símbolo de entrada → símbolos de trabajo → Action`.
  La semántica es `MultiTapeTM.step` (`step_of_state`, `step_of_halt`) y `runFrom c t = step^[t] c`; todo
  camino de cómputo de la versión no determinista es ese iterado (`runPath_apply_eq_runFrom`,
  `computationPath_last_eq_runFrom`), `runsInTime_of_halted` da la cota de tiempo y `RunPath.InWindow.space_le`
  la de espacio. Costo de escribir una: la transición más **un lema de invariante por fase** (acá `acumula` y
  `corre`), demostrado por inducción sobre lo que se lee; cada paso exige reconstruir la configuración con
  `Cfg.ext` y la posición de la cabeza de entrada (`Fin (n + 2)`, `moveInputPos`). Es lo que se hizo aquí.
* **Combinadores con cota `O(·)`.** `Turing.MultiTapeTM.ComputableInO f encIn encOut T S`
  (`MultiTape/ResourceBounds.lean`): hay una máquina con tiempo `c (T + 1)` y espacio `c (S + 1)`. Se compone
  con `ComputableInO.comp'` (secuencia: las cotas se suman), `prod`, `and'`, `or'`, `not'`, `ite`
  (`Complexity/BigO/FunProp.lean`, `FunPropLists.lean`), `const`, `of_bounds`, `mono`. Para transformar una
  cadena en tiempo lineal sin cinta de trabajo están los **transductores finitos**
  (`MultiTapeTM.Transducer`, con `Transducer.computableInTimeAndSpace`, `Combinators/Transducer.lean`), y para
  recorrer una cadena con un acumulador, los pliegues (`Complexity/Fold.lean`; `foldl_bits_finite` si el
  acumulador es finito, `Complexity/Streaming.lean`). **Ninguno de estos combinadores da memoria de acceso
  secuencial no acotada en tiempo lineal**: un pliegue con un acumulador de tamaño `m` paga `m` por ronda, así que
  simular una cinta con un acumulador cuesta `O(t²)`. Por eso la pasada tiene que ser una máquina cruda: su
  cinta de trabajo **es** la cinta simulada.
* **Ramificación no determinista.** No hay un combinador «adivinar»: el no determinismo entra por
  `Cslib.Complexity.setOf_exists_mem_NTIME` (`Classes/Time/Verifier.lean`), que convierte un verificador
  `ComputableInO` sobre pares `(a, w)`, más un largo de certificado `ℓ a` calculable en unario, en `NTIME`.
  `exists_verifier_of_mem_NTIME` es el converso, pero su verificador reproduce la máquina con sus `k` cintas
  (`checkChoices`): no reduce cintas. **Reloj**: el largo `ℓ a` en unario es el reloj; la construibilidad está en
  `Classes/Constructible` (`UnaryClock.lean`, `TwoPow.lean`) y `Complexity/BigO/Constructible.lean`.
  **Copia de cintas**: `ComputableInO.id'` (copiar en tiempo lineal), `of_eq`.

**La ruta elegida**, y por qué: la pasada por una cinta como máquina cruda (es lo único que exige una cinta de
trabajo real), y todo lo demás con combinadores: la proyección de la traza sobre la cinta `i` es un transductor
finito, la composición es `comp'` y la conjunción de las `k` pasadas es `and'`. Así cada pieza nueva queda en
`ComputableInO`, que es lo que consume `setOf_exists_mem_NTIME`.

## 2. Qué se construye y qué se prueba

* **La pasada** (`pasada : MultiTapeTM 1 Bool EstadoPasada`, con `EstadoPasada` finito). Lee la sucesión de
  pasos de una cinta (`List Paso`, cada paso es lo que `SimulacionLineal` llama `PasoCinta`: la lectura
  declarada y la operación) codificada con siete bits por paso (`encPasos`), y lleva en su única cinta de trabajo
  la cinta simulada. Al séptimo bit de cada paso compara la lectura declarada con el símbolo bajo la cabeza,
  escribe y mueve.
  - `corre`: desde el principio de cualquier paso, en exactamente `7 · |es| + 1` pasos se para con salida
    `[decide (ConsistenteCinta T es)]`.
  - `pasada_decide`, `pasada_computa`: desde la configuración inicial de cslib, tiempo `7 · |es| + 1` y
    espacio `2 · (7 · |es| + 1) + 1`, con `ComputesInTimeAndSpace`.
  - `consistente_computableInO`: **la consistencia de una cinta se decide en tiempo lineal**, en el sentido de
    `ComputableInO` (con constante 16).
  - `corre_exacto`, `pasada_tiempo_exacto`: sobre una sucesión consistente no vacía, la máquina no se para en
    `7 · |es|` pasos. La cota es exacta: lineal, y no menos.
* **Las `k` pasadas** (meta 2, la parte de cintas de trabajo). La traza de las `k` cintas (`List (PasoK k)`) se
  codifica con `7 k + 1` bits por paso (`encPasosK`). `proyector k i` es un transductor finito que deja pasar
  solo el bloque de la cinta `i` (`run_proyector_codPasosK`), así que
  - `proyeccion_computableInO`: proyectar es lineal;
  - `consistenteK_computableInO`: la pasada por la cinta `i` sobre la traza entera es lineal;
  - `trabajoOk_computableInO`: **las `k` pasadas juntas** (`TrabajoOk`: cada cinta de trabajo consistente
    desde la vacía) se deciden en tiempo `O(|traza|)`, con la constante que depende de `k`.
* **El enlace** con `SimulacionLineal`: `accepts_iff_pasadas` reescribe `accepts_iff_por_cinta` con la condición
  de las cintas de trabajo dada por la máquina: `Accepts ↔ ∃ τ` de largo `≤ t` con control, parada, cinta de
  entrada, salida y `decide (TrabajoOk k (trabajoDe τ)) = true`.

**La cota de tiempo, exacta.** Para `es : List Paso`, la pasada para en el paso `7 · |es| + 1` (`corre`) y no
antes si `es` es consistente (`pasada_tiempo_exacto`); `consistente_computableInO` la absorbe como
`16 · (|es| + 1)`. Para las `k` pasadas, `trabajoOk_computableInO` da `c_k · (|es| + 1)` con un `c_k` que no se
calcula explícitamente (sale de los combinadores; crece con `k` porque cada pasada lee los `7 k + 1` bits de
cada paso, y hay `k` pasadas: del orden de `k²`).

Metas del encargo: la **1** (mapa) completa; la **2 parcial**: las pasadas de las cintas de trabajo son máquinas
de tiempo lineal, pero el verificador entero de trazas no está armado (falta lo de abajo). La **3** y la **4**,
no.

## Dónde encaja en el programa de Williams, y qué falta

Las piezas de Williams son: la jerarquía no determinista fina, el lema del testigo fácil
(Impagliazzo–Kabanets–Wigderson), la reducción sucinta con `n + O(log n)` bits y un algoritmo de ACC-SAT más
rápido que `2^n`. Esto es un paso dentro de la primera. Faltan, en orden:

1. **Las otras verificaciones del verificador de trazas**, para una máquina fija: (a) la codificación de una
   entrada entera `EntradaC k Bool State` (estado, lecturas, acción) en un ancho fijo, con `State` finito
   codificado por `Fintype.equivFin`; (b) el control (`ControlC`), la parada (`estadoFinal`) y la salida, que
   son autómatas finitos sobre esa codificación (`foldl_bits_finite` o un transductor); (c) la proyección de la
   traza completa a la parte de trabajo (`trabajoDe`), otro transductor; (d) **la cinta de entrada**
   (`EntradaOk`): es la única que no sale de lo hecho, porque el verificador recibe el par `(x, τ)` y tiene que
   leer `x` con una cabeza que va y viene; la máquina natural copia `x` a una cinta de trabajo y corre una pasada
   como `pasada`, pero con los bordes que recortan (`moveInputPos`), que es otra máquina cruda; (e) la
   conjunción y el paso a `setOf_exists_mem_NTIME`, con el largo del certificado escrito en unario (exige `t`
   construible en tiempo).
2. **La versión universal** (meta 3): lo mismo con la descripción `d` como dato. La pasada sirve tal cual (el
   alfabeto de las cintas de trabajo de `NTIME` es binario, así que la cinta simulada siempre cabe en una cinta
   de cslib); lo que cambia es que el proyector y el control dependen de `d`: un transductor no puede saltar un
   bloque de ancho `k(d)` sin contar, así que la proyección pasa a ser una máquina con un contador en una cinta
   de trabajo (tiempo `O(|d| · |τ|)`), y el control tiene que buscar cada transición en la tabla de `d`
   (`Universal.Desc`). Nada de eso está.
3. **La diagonal perezosa no determinista** (meta 4): `Classes/Hierarchy/LazyDiagonal.lean` diagonaliza contra
   verificadores **deterministas** corridos con `Universal.universal` (sobrecosto polinomial, `accBound`); hay
   que cambiarla para que copie un paso adelante con la universal de trazas y niegue con la corrida
   determinista solo en el borde del intervalo (`JerarquiaFina.intervalo_existe` ya tiene la aritmética).
4. Los testigos fáciles, la reducción sucinta y ACC-SAT.

## Lo que NO se prueba

* **No hay ninguna NTM con un número fijo de cintas que simule a otra.** Lo construido son verificadores
  deterministas de partes de la traza; ninguno adivina nada, y no se usa `setOf_exists_mem_NTIME`.
* **No está el verificador entero**: ni el control, ni la parada, ni la salida, ni la cinta de entrada, ni la
  codificación de las entradas `EntradaC`, están hechos como máquinas. `accepts_iff_pasadas` sigue teniendo esas
  cuatro condiciones como proposiciones, no como programas con tiempo medido.
* **Nada universal**: `pasada` y `proyector k i` son máquinas fijas; el número de cintas `k` es un parámetro de
  Lean, no un dato que la máquina lea.
* **El número de cintas no se ve en el enunciado**: `ComputableInO` cuantifica existencialmente las cintas, así
  que `trabajoOk_computableInO` no dice cuántas usa su máquina (la pasada usa una; los combinadores, las suyas).
  Lo que importa para la universal, que el número de cintas no dependa de la máquina simulada, no se afirma.
* **Ni jerarquía fina, ni nada sobre P contra NP o NEXP contra ACC⁰.**

## Fuentes

* R. V. Book y S. A. Greibach, «Quasi-realtime languages», *Mathematical Systems Theory* 4(1):97–111, 1970,
  doi:10.1007/BF01705890; y R. V. Book, S. A. Greibach y B. Wegbreit, «Time- and tape-bounded Turing acceptors
  and AFLs», *Journal of Computer and System Sciences* 4(6):606–621, 1970, doi:10.1016/S0022-0000(70)80031-9
  (verificados en Crossref; no los leí: la idea de adivinar la traza y verificarla por cinta es de memoria, y la
  máquina y las pruebas de aquí son propias).
* Žák 1983 y Seiferas–Fischer–Meyer 1978: ver `JerarquiaFina` (verificados allá en Crossref; no los leí).
-/

namespace Sagitta.Map.Tiempo.BookGreibachMaquina

open Turing Sagitta.Map.Tiempo.SimulacionLineal

/-- Un paso de la traza proyectado sobre una cinta de trabajo binaria. -/
abbrev Paso := PasoCinta (Option Bool)

/-- Un símbolo de cinta (`none` es el blanco) en dos bits. -/
def codOpt : Option Bool → List Bool
  | none => [false, false]
  | some b => [true, b]

/-- Lo que se escribe (o no) en tres bits. -/
def codEscribe : Option (Option Bool) → List Bool
  | none => [false, false, false]
  | some o => true :: codOpt o

/-- El movimiento de la cabeza en dos bits. -/
def codMueve : SignType → List Bool
  | .zero => [false, false]
  | .pos => [true, true]
  | .neg => [true, false]

/-- Un paso de una cinta en siete bits: lectura, escritura, movimiento. -/
def codPaso (e : Paso) : List Bool := codOpt e.lee ++ codEscribe e.op.escribe ++ codMueve e.op.mueve

/-- La decodificación de siete bits (total: lo que no es un paso codificado da un paso cualquiera). -/
def decPaso : List Bool → Paso
  | [l0, l1, e0, e1, e2, m0, m1] =>
    ⟨if l0 then some l1 else none,
     ⟨if e0 then some (if e1 then some e2 else none) else none,
      if m0 then (if m1 then .pos else .neg) else .zero⟩⟩
  | _ => ⟨none, ⟨none, .zero⟩⟩

theorem length_codPaso (e : Paso) : (codPaso e).length = 7 := by
  rcases e with ⟨l, ⟨w, m⟩⟩
  rcases l with _ | b <;> rcases w with _ | _ | b' <;> cases m <;> rfl

theorem decPaso_codPaso (e : Paso) : decPaso (codPaso e) = e := by
  rcases e with ⟨l, ⟨w, m⟩⟩
  rcases l with _ | b <;> rcases w with _ | _ | b' <;> cases m <;>
    (try cases b) <;> (try cases b') <;> rfl

/-- Una sucesión de pasos, paso tras paso. -/
def codPasos (es : List Paso) : List Bool := es.flatMap codPaso

@[simp] theorem codPasos_nil : codPasos [] = [] := rfl
@[simp] theorem codPasos_cons (e : Paso) (es : List Paso) :
    codPasos (e :: es) = codPaso e ++ codPasos es := by simp [codPasos]

theorem length_codPasos (es : List Paso) : (codPasos es).length = 7 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [length_codPaso, ih]; ring

theorem codPasos_injective : Function.Injective codPasos := by
  intro a
  induction a with
  | nil =>
    intro b h
    have := congrArg List.length h
    rw [length_codPasos, length_codPasos] at this
    exact (List.length_eq_zero_iff.mp (by simpa using this.symm)).symm
  | cons e es ih =>
    intro b h
    cases b with
    | nil =>
      have := congrArg List.length h
      simp [length_codPasos, length_codPaso] at this
    | cons e' es' =>
      simp only [codPasos_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_codPaso, length_codPaso])
      have he : e = e' := by rw [← decPaso_codPaso e, h1, decPaso_codPaso]
      rw [he, ih h2]

/-- La codificación de una sucesión de pasos: siete bits por paso. -/
def encPasos : List Paso ↪ List Bool := ⟨codPasos, codPasos_injective⟩

/-- Los estados de la pasada: los bits leídos del paso en curso (menos de siete). -/
abbrev EstadoPasada := {l : List Bool // l.length < 7}

instance : Finite EstadoPasada := by
  refine Finite.of_injective (fun q : EstadoPasada =>
    ((⟨q.1.length, q.2⟩ : Fin 7), fun i : Fin 7 => q.1.getD i false)) ?_
  intro q q' h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨hl, hg⟩ := h
  apply Subtype.ext
  apply List.ext_getElem hl
  intro n h1 h2
  have := congrFun hg ⟨n, by have := q.2; omega⟩
  simpa [List.getD_eq_getElem, h1, h2] using this

/-- El estado inicial: ningún bit leído del paso en curso. -/
def q0 : EstadoPasada := ⟨[], by simp⟩

/-- La transición de la pasada. Con la entrada terminada, para con salida `[true]` si no quedó un paso a
medias. Con un bit, si el paso no está completo, lo guarda y avanza; al séptimo bit decodifica el paso, compara
la lectura declarada con el símbolo bajo la cabeza de trabajo y, si coinciden, escribe y mueve como dice el paso;
si no, para con salida `[false]`. -/
def trPasada (q : EstadoPasada) : Option Bool → (Fin 1 → Option Bool) → Action 1 Bool EstadoPasada
  | none, _ => ⟨0, fun _ => (none, 0), some q.1.isEmpty, none⟩
  | some b, w =>
    if h : (q.1 ++ [b]).length < 7 then ⟨1, fun _ => (none, 0), none, some ⟨q.1 ++ [b], h⟩⟩
    else if w 0 = (decPaso (q.1 ++ [b])).lee then
      ⟨1, fun _ => ((decPaso (q.1 ++ [b])).op.escribe, (decPaso (q.1 ++ [b])).op.mueve), none, some q0⟩
    else ⟨0, fun _ => (none, 0), some false, none⟩

/-- **La pasada de Book–Greibach sobre una cinta**, como máquina de cslib: una cinta de trabajo. -/
def pasada : MultiTapeTM 1 Bool EstadoPasada := MultiTapeTM.ofTr q0 trPasada

/-- La cinta vacía con la cabeza en `0`, como arrancan las cintas de trabajo de cslib. -/
def cintaVacia : Cinta (Option Bool) := ⟨fun _ => none, 0⟩

/-- La configuración de la pasada que lleva la cinta simulada `T` en su cinta de trabajo. -/
def cfgDe {w : List Bool} (q : Option EstadoPasada) (p : Fin (w.length + 2)) (T : Cinta (Option Bool))
    (out : List Bool) : Cfg 1 Bool EstadoPasada w :=
  ⟨q, p, fun _ => T.celdas, fun _ => T.cabeza, out⟩

theorem step_cfgDe {w : List Bool} (q : EstadoPasada) (p : Fin (w.length + 2)) (T : Cinta (Option Bool))
    (out : List Bool) :
    pasada.step (cfgDe q p T out) =
      (trPasada q (cfgDe (w := w) q p T out).inputSymbol (fun _ => T.leer)).apply (cfgDe q p T out) := by
  rw [MultiTapeTM.step_of_state (q := q) rfl]
  simp only [pasada, MultiTapeTM.tr_ofTr]
  rfl

theorem val_move_one {n : ℕ} (P : Fin (n + 2)) (h : P.val ≠ n + 1) :
    (moveInputPos P 1).val = P.val + 1 := by
  have h1 := val_moveInputPos_eq P 1
  have hP := P.isLt
  simp only [SignType.coe_one] at h1
  omega

theorem runFrom_add {w : List Bool} (c : Cfg 1 Bool EstadoPasada w) (m n : ℕ) :
    pasada.runFrom c (m + n) = pasada.runFrom (pasada.runFrom c n) m :=
  Function.iterate_add_apply _ _ _ _

theorem runFrom_one {w : List Bool} (c : Cfg 1 Bool EstadoPasada w) :
    pasada.runFrom c 1 = pasada.step c := rfl

theorem runFrom_halted {w : List Bool} (c : Cfg 1 Bool EstadoPasada w) (h : c.state = none) (n : ℕ) :
    pasada.runFrom c n = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom, ih,
      MultiTapeTM.step_of_halt h]

/-- Leer los bits de un paso sin tocar la cinta: el estado acumula los bits. -/
theorem acumula {w : List Bool} (pre bs suf : List Bool) (hw : w = pre ++ bs ++ suf)
    (q : EstadoPasada) (hq : q.1.length + bs.length < 7) (T : Cinta (Option Bool)) :
    pasada.runFrom (cfgDe (w := w) (some q) ⟨pre.length + 1, by subst hw; simp⟩ T [])
        bs.length =
      cfgDe (some ⟨q.1 ++ bs, by simpa using hq⟩) ⟨pre.length + bs.length + 1, by subst hw; simp⟩
        T [] := by
  induction bs generalizing pre q with
  | nil => simp [MultiTapeTM.runFrom]
  | cons b bs ih =>
    change MultiTapeTM.runFrom _ (bs.length + 1) = _
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply, ← MultiTapeTM.runFrom]
    have hsym : (cfgDe (w := w) (some q) ⟨pre.length + 1, by subst hw; simp⟩ T []).inputSymbol
        = some b := by
      rw [inputSymbolInner pre.length (by simp [cfgDe]; omega) (by subst hw; simp)]
      subst hw; simp
    have hlt : (q.1 ++ [b]).length < 7 := by simp at hq ⊢; omega
    rw [step_cfgDe, hsym]
    simp only [trPasada, hlt, dite_true]
    have := ih (pre ++ [b]) (by subst hw; simp) ⟨q.1 ++ [b], hlt⟩ (by simp at hq ⊢; omega)
    convert this using 2
    · simp only [cfgDe, Action.apply]
      congr 1
      · apply Fin.ext
        rw [val_move_one _ (by subst hw; simp)]
        simp
      funext i; simp
    · simp
    · simp; omega

/-- La consistencia de una cinta binaria es decidible (por recursión sobre la sucesión). -/
instance decConsistente : (T : Cinta (Option Bool)) → (es : List Paso) →
    Decidable (ConsistenteCinta T es)
  | _, [] => isTrue trivial
  | T, e :: es =>
    haveI := decConsistente (T.aplicar e.op) es
    decidable_of_iff _ (consistente_cons T e es).symm

theorem inputSymbol_cfgDe {w : List Bool} (q : Option EstadoPasada) (P : Fin (w.length + 2))
    (T : Cinta (Option Bool)) (out : List Bool) (n : ℕ) (hP : P.val = n + 1) (hn : n < w.length) :
    (cfgDe (w := w) q P T out).inputSymbol = some w[n] :=
  inputSymbolInner n (by simp [cfgDe, hP]; omega) hn

theorem inputSymbol_cfgDe_fin {w : List Bool} (q : Option EstadoPasada) (P : Fin (w.length + 2))
    (T : Cinta (Option Bool)) (out : List Bool) (hP : P.val = w.length + 1) :
    (cfgDe (w := w) q P T out).inputSymbol = none :=
  inputSymbol_eq_none_of_boundary (Or.inr (by simpa [cfgDe] using hP))

/-- El séptimo bit de un paso, cuando la lectura declarada coincide con la cinta: se escribe, se
mueve la cabeza y se vuelve al estado inicial. -/
theorem paso_bueno {w : List Bool} (bs : List Bool) (hq : bs.length < 7) (b : Bool)
    (P P' : Fin (w.length + 2)) (T : Cinta (Option Bool)) (e : Paso)
    (h7 : ¬ (bs ++ [b]).length < 7) (hdec : decPaso (bs ++ [b]) = e) (hle : T.leer = e.lee)
    (hP : P'.val = P.val + 1) (hP2 : P.val ≠ w.length + 1) :
    (trPasada ⟨bs, hq⟩ (some b) (fun _ => T.leer)).apply (cfgDe (some ⟨bs, hq⟩) P T []) =
      cfgDe (some q0) P' (T.aplicar e.op) [] := by
  simp only [trPasada, h7, dite_false, hdec, hle, ite_true]
  simp only [cfgDe, Action.apply, Cinta.aplicar]
  congr 1
  · apply Fin.ext
    rw [val_move_one _ hP2, hP]
  funext i; cases e.op.escribe <;> rfl

/-- El séptimo bit de un paso, cuando la lectura declarada no coincide: se para con salida
`[false]`. -/
theorem paso_malo {w : List Bool} (bs : List Bool) (hq : bs.length < 7) (b : Bool)
    (P : Fin (w.length + 2)) (T : Cinta (Option Bool)) (e : Paso)
    (h7 : ¬ (bs ++ [b]).length < 7) (hdec : decPaso (bs ++ [b]) = e) (hle : ¬ T.leer = e.lee) :
    ((trPasada ⟨bs, hq⟩ (some b) (fun _ => T.leer)).apply (cfgDe (some ⟨bs, hq⟩) P T [])).state
        = none ∧
      ((trPasada ⟨bs, hq⟩ (some b) (fun _ => T.leer)).apply (cfgDe (some ⟨bs, hq⟩) P T [])).output
        = [false] := by
  simp only [trPasada, h7, dite_false, hdec, hle, ite_false]
  simp [cfgDe, Action.apply]

/-- **Lo que hace la pasada**, desde el principio de un paso: en `7 · |es| + 1` pasos se para, y su
salida es `[true]` si y solo si la sucesión `es` es consistente con la cinta `T`. -/
theorem corre {w : List Bool} (es : List Paso) : ∀ (pre : List Bool) (hw : w = pre ++ codPasos es)
    (T : Cinta (Option Bool)),
    (pasada.runFrom (cfgDe (w := w) (some q0) ⟨pre.length + 1, by subst hw; simp⟩ T [])
        (7 * es.length + 1)).state = none ∧
    (pasada.runFrom (cfgDe (w := w) (some q0) ⟨pre.length + 1, by subst hw; simp⟩ T [])
        (7 * es.length + 1)).output = [decide (ConsistenteCinta T es)] := by
  induction es with
  | nil =>
    intro pre hw T
    rw [List.length_nil, Nat.mul_zero, Nat.zero_add, runFrom_one, step_cfgDe, inputSymbol_cfgDe_fin _ _ _ _ (by subst hw; simp)]
    simp [trPasada, q0, cfgDe, Action.apply]
  | cons e es ih =>
    intro pre hw T
    have hne : codPaso e ≠ [] := by
      intro h; have := length_codPaso e; rw [h] at this; simp at this
    set bs := (codPaso e).dropLast with hbs
    set b := (codPaso e).getLast hne with hb
    have hcod : codPaso e = bs ++ [b] := (List.dropLast_append_getLast hne).symm
    have hbslen : bs.length = 6 := by simp [hbs, length_codPaso]
    have hw' : w = pre ++ bs ++ ([b] ++ codPasos es) := by
      rw [hw, codPasos_cons, hcod]; simp
    have hacc := acumula pre bs ([b] ++ codPasos es) hw' q0 (by simp [q0, hbslen]) T
    have hcount : 7 * (e :: es).length + 1 = (7 * es.length + 1) + 1 + bs.length := by
      simp [hbslen]; ring
    have h7 : ¬ (bs ++ [b]).length < 7 := by simp [hbslen]
    have hdec : decPaso (bs ++ [b]) = e := by rw [← hcod, decPaso_codPaso]
    have hwb : w[pre.length + bs.length]'(by rw [hw']; simp) = b := by
      subst hw'; simp
    have hpos : (pre.length + bs.length) < w.length := by rw [hw']; simp
    rw [hcount, runFrom_add, runFrom_add, hacc, runFrom_one, step_cfgDe, inputSymbol_cfgDe _ _ _ _ _ rfl hpos, hwb]
    by_cases hle : T.leer = e.lee
    · have hPw : (pre ++ codPaso e).length + 1 < w.length + 2 := by rw [hw]; simp
      rw [paso_bueno _ _ b _ ⟨(pre ++ codPaso e).length + 1, hPw⟩ T e (by simpa [q0] using h7)
        (by simpa [q0] using hdec) hle (by simp [length_codPaso, hbslen]) (by simp; omega)]
      have := ih (pre ++ codPaso e) (by rw [hw]; simp) (T.aplicar e.op)
      have hd : decide (ConsistenteCinta T (e :: es)) =
          decide (ConsistenteCinta (T.aplicar e.op) es) :=
        decide_eq_decide.mpr (by rw [consistente_cons]; simp [hle])
      rw [hd]
      exact this
    · obtain ⟨hs, ho⟩ := paso_malo (w := w) (q0.1 ++ bs) (by simp [q0, hbslen]) b
        ⟨pre.length + bs.length + 1, by omega⟩ T e (by simpa [q0] using h7)
        (by simpa [q0] using hdec) hle
      rw [runFrom_halted _ hs]
      refine ⟨hs, ?_⟩
      have hd : decide (ConsistenteCinta T (e :: es)) = false :=
        decide_eq_false (by rw [consistente_cons]; simp [hle])
      rw [ho, hd]

/-- **El tiempo es exacto**: sobre una sucesión consistente, después de `7 · |es|` pasos la pasada sigue
corriendo, al final de la entrada y con la cinta simulada ya actualizada. Con `corre`, el tiempo de parada
es exactamente `7 · |es| + 1`: lineal, y no menos. -/
theorem corre_exacto {w : List Bool} (es : List Paso) : ∀ (pre : List Bool) (hw : w = pre ++ codPasos es)
    (T : Cinta (Option Bool)), ConsistenteCinta T es → ∀ P : Fin (w.length + 2),
    P.val = pre.length + 7 * es.length + 1 →
    pasada.runFrom (cfgDe (w := w) (some q0) ⟨pre.length + 1, by subst hw; simp⟩ T [])
        (7 * es.length) = cfgDe (some q0) P (T.correr (es.map PasoCinta.op)) [] := by
  induction es with
  | nil =>
    intro pre hw T _ P hP
    simp only [List.length_nil, Nat.mul_zero, MultiTapeTM.runFrom, Function.iterate_zero, id_eq,
      List.map_nil, Cinta.correr]
    congr 1
    apply Fin.ext
    simp [hP]
  | cons e es ih =>
    intro pre hw T hc P hP
    rw [consistente_cons] at hc
    have hne : codPaso e ≠ [] := by
      intro h; have := length_codPaso e; rw [h] at this; simp at this
    set bs := (codPaso e).dropLast with hbs
    set b := (codPaso e).getLast hne with hb
    have hcod : codPaso e = bs ++ [b] := (List.dropLast_append_getLast hne).symm
    have hbslen : bs.length = 6 := by simp [hbs, length_codPaso]
    have hw' : w = pre ++ bs ++ ([b] ++ codPasos es) := by
      rw [hw, codPasos_cons, hcod]; simp
    have hacc := acumula pre bs ([b] ++ codPasos es) hw' q0 (by simp [q0, hbslen]) T
    have hcount : 7 * (e :: es).length = 7 * es.length + 1 + bs.length := by
      simp [hbslen]; ring
    have h7 : ¬ (bs ++ [b]).length < 7 := by simp [hbslen]
    have hdec : decPaso (bs ++ [b]) = e := by rw [← hcod, decPaso_codPaso]
    have hwb : w[pre.length + bs.length]'(by rw [hw']; simp) = b := by
      subst hw'; simp
    have hpos : (pre.length + bs.length) < w.length := by rw [hw']; simp
    rw [hcount, runFrom_add, runFrom_add, hacc, runFrom_one, step_cfgDe,
      inputSymbol_cfgDe _ _ _ _ _ rfl hpos, hwb]
    have hPw : (pre ++ codPaso e).length + 1 < w.length + 2 := by rw [hw]; simp
    rw [paso_bueno _ _ b _ ⟨(pre ++ codPaso e).length + 1, hPw⟩ T e (by simpa [q0] using h7)
      (by simpa [q0] using hdec) hc.1 (by simp [length_codPaso, hbslen]) (by simp; omega)]
    rw [ih (pre ++ codPaso e) (by rw [hw]; simp) (T.aplicar e.op) hc.2 P
      (by simp [length_codPaso] at hP ⊢; omega)]
    rfl

theorem initCfg_eq (es : List Paso) :
    pasada.initCfg (codPasos es) =
      cfgDe (w := codPasos es) (some q0) ⟨([] : List Bool).length + 1, by simp⟩ cintaVacia [] := by
  simp only [MultiTapeNTM.initCfg, Cfg.init, cfgDe, cintaVacia, pasada, MultiTapeTM.q₀_ofTr]
  congr 1

/-- **La pasada decide la consistencia en `7 · |es| + 1` pasos**, desde la cinta vacía. -/
theorem pasada_decide (es : List Paso) :
    (pasada.runFrom (pasada.initCfg (codPasos es)) (7 * es.length + 1)).state = none ∧
    (pasada.runFrom (pasada.initCfg (codPasos es)) (7 * es.length + 1)).output =
      [decide (ConsistenteCinta cintaVacia es)] := by
  rw [initCfg_eq]
  exact corre es [] (by simp) cintaVacia

/-- **Control: la pasada no para antes.** Sobre una sucesión consistente y no vacía, en el paso
`7 · |es|` la máquina todavía corre: la cota `7 · |es| + 1` es exacta, no solo una cota superior. -/
theorem pasada_no_para_antes (es : List Paso) (hc : ConsistenteCinta cintaVacia es) :
    (pasada.runFrom (pasada.initCfg (codPasos es)) (7 * es.length)).state = some q0 := by
  rw [initCfg_eq, corre_exacto es [] (by simp) cintaVacia hc
    ⟨[].length + 7 * es.length + 1, by simp [length_codPasos]⟩ rfl]
  rfl

/-- Una máquina determinista que corre en tiempo `t` está parada en el paso `t`. -/
theorem halted_of_runsInTime {w : List Bool} {t : ℕ} (h : pasada.RunsInTime w t) :
    (pasada.runFrom (pasada.initCfg w) t).state = none := by
  have := h (MultiTapeNTM.ComputationPath.ofDeterministic pasada w t) le_rfl
  rwa [MultiTapeTM.computationPath_last_eq_runFrom] at this

/-- **Control: la cota de tiempo `7 · |es| + 1` no se puede bajar a `7 · |es|`** en ninguna sucesión
consistente y no vacía. -/
theorem pasada_tiempo_exacto (es : List Paso) (hc : ConsistenteCinta cintaVacia es) :
    pasada.RunsInTime (codPasos es) (7 * es.length + 1) ∧
      ¬ pasada.RunsInTime (codPasos es) (7 * es.length) := by
  refine ⟨MultiTapeTM.runsInTime_of_halted (pasada_decide es).1, fun h => ?_⟩
  have h1 := halted_of_runsInTime h
  rw [pasada_no_para_antes es hc] at h1
  exact Option.some_ne_none _ h1

/-- La cabeza de trabajo se mueve a lo sumo una celda por paso. -/
theorem pos_runFrom_le {w : List Bool} (c : Cfg 1 Bool EstadoPasada w) (n : ℕ) (i : Fin 1) :
    |(pasada.runFrom c n).workTapePos i - c.workTapePos i| ≤ n := by
  induction n with
  | zero => simp [MultiTapeTM.runFrom]
  | succ n ih =>
    have h1 : |(pasada.runFrom c (n + 1)).workTapePos i - (pasada.runFrom c n).workTapePos i| ≤ 1 := by
      rw [show n + 1 = 1 + n by ring, runFrom_add, runFrom_one]
      rcases hq : (pasada.runFrom c n).state with _ | q
      · rw [MultiTapeTM.step_of_halt hq]; simp
      · rw [MultiTapeTM.step_of_state hq]; exact workTapePos_apply_le _ _ i
    have := abs_sub_le ((pasada.runFrom c (n + 1)).workTapePos i)
      ((pasada.runFrom c n).workTapePos i) (c.workTapePos i)
    push_cast
    linarith

/-- **El espacio de la pasada**: todo camino de cómputo visita a lo sumo `2 (7 |es| + 1) + 1` celdas. -/
theorem pasada_runsInSpace (es : List Paso) :
    pasada.RunsInSpace (codPasos es) (2 * (7 * es.length + 1) + 1) := by
  intro p
  have hhalt := (pasada_decide es).1
  have hw : MultiTapeNTM.RunPath.InWindow p.toRunPath (7 * es.length + 1) := by
    intro c hc i
    obtain ⟨n, rfl⟩ := hc
    have hn := MultiTapeTM.runPath_apply_eq_runFrom p.toRunPath n
    rw [p.head_eq] at hn
    rw [hn]
    have hb : |(pasada.runFrom (pasada.initCfg (codPasos es)) n).workTapePos i| ≤
        7 * es.length + 1 := by
      rcases le_or_gt (n : ℕ) (7 * es.length + 1) with hle | hgt
      · have := pos_runFrom_le (pasada.initCfg (codPasos es)) n i
        simp only [MultiTapeNTM.initCfg, Cfg.init, sub_zero] at this
        simp only [MultiTapeNTM.initCfg, Cfg.init]
        omega
      · rw [MultiTapeTM.runFrom_eq_of_halt _ _ hgt.le hhalt]
        have := pos_runFrom_le (pasada.initCfg (codPasos es)) (7 * es.length + 1) i
        simp only [MultiTapeNTM.initCfg, Cfg.init, sub_zero] at this
        simp only [MultiTapeNTM.initCfg, Cfg.init]
        omega
    rw [window, Finset.mem_Icc]
    constructor <;> [skip; skip] <;> (have := abs_le.mp hb; omega)
  have := MultiTapeNTM.RunPath.InWindow.space_le hw
  change MultiTapeNTM.RunPath.space p.toRunPath ≤ _
  simpa using this

/-- **La pasada, en el lenguaje de cslib**: calcula `[decide (consistente)]` en tiempo
`7 · |es| + 1` y espacio `14 · |es| + 3`. -/
theorem pasada_computa (es : List Paso) :
    pasada.ComputesInTimeAndSpace (codPasos es) [decide (ConsistenteCinta cintaVacia es)]
      (7 * es.length + 1) (2 * (7 * es.length + 1) + 1) :=
  ⟨⟨_, (pasada_decide es).1, (pasada_decide es).2⟩,
    MultiTapeTM.runsInTime_of_halted (pasada_decide es).1, pasada_runsInSpace es⟩

/-- **La consistencia de una cinta se decide en tiempo lineal** (`ComputableInO` de cslib-frontier). -/
theorem consistente_computableInO :
    MultiTapeTM.ComputableInO (fun es : List Paso => decide (ConsistenteCinta cintaVacia es))
      encPasos MultiTapeTM.encBool (fun es => es.length) (fun es => es.length) := by
  refine ⟨16, ⟨1, EstadoPasada, inferInstance, pasada, fun es => ?_⟩, fun es => ?_⟩
  · have h := pasada_computa es
    exact ⟨h.1, h.2.1.mono (by dsimp only; omega), h.2.2.mono (by dsimp only; omega)⟩
  · simp [MultiTapeTM.encBool_apply]; omega

/-! ## Las `k` cintas: una pasada por cinta sobre la traza entera -/

section VariasCintas

variable (k : ℕ)

/-- Un paso de la traza sobre las `k` cintas de trabajo. -/
abbrev PasoK := Fin k → Paso

/-- Un paso de `k` cintas: un bit de marca y los `k` bloques de siete bits, en orden. -/
def codPasoK (f : PasoK k) : List Bool := true :: codPasos (List.ofFn f)

theorem length_codPasoK (f : PasoK k) : (codPasoK k f).length = 7 * k + 1 := by
  simp [codPasoK, length_codPasos]

theorem codPasoK_injective : Function.Injective (codPasoK k) := by
  intro f g h
  simp only [codPasoK, List.cons.injEq, true_and] at h
  exact List.ofFn_injective (codPasos_injective h)

/-- La traza de las cintas de trabajo, codificada paso tras paso. -/
def codPasosK (es : List (PasoK k)) : List Bool := es.flatMap (codPasoK k)

@[simp] theorem codPasosK_nil : codPasosK k [] = [] := rfl
@[simp] theorem codPasosK_cons (e : PasoK k) (es : List (PasoK k)) :
    codPasosK k (e :: es) = codPasoK k e ++ codPasosK k es := by simp [codPasosK]

theorem length_codPasosK (es : List (PasoK k)) :
    (codPasosK k es).length = (7 * k + 1) * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [length_codPasoK, ih]; ring

theorem codPasosK_injective : Function.Injective (codPasosK k) := by
  intro a
  induction a with
  | nil =>
    intro b h
    have := congrArg List.length h
    rw [length_codPasosK, length_codPasosK] at this
    cases b with
    | nil => rfl
    | cons _ _ => simp at this
  | cons e es ih =>
    intro b h
    cases b with
    | nil =>
      have := congrArg List.length h
      simp [length_codPasosK, length_codPasoK] at this
    | cons e' es' =>
      simp only [codPasosK_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_codPasoK, length_codPasoK])
      rw [codPasoK_injective k h1, ih h2]

/-- La codificación de la traza de las cintas de trabajo: `7 k + 1` bits por paso. -/
def encPasosK : List (PasoK k) ↪ List Bool := ⟨codPasosK k, codPasosK_injective k⟩

/-- Lo que el proyector deja pasar en la posición `q` de un paso: el bloque de la cinta `i`. -/
def enBloque (i q : ℕ) : Prop := 7 * i + 1 ≤ q ∧ q < 7 * i + 8

instance (i q : ℕ) : Decidable (enBloque i q) := by unfold enBloque; infer_instance

/-- **El proyector sobre la cinta `i`**: un transductor finito que cuenta la posición dentro del paso y
copia solo el bloque de la cinta `i`. -/
def proyector (i : ℕ) : MultiTapeTM.Transducer Bool (Fin (7 * k + 1)) where
  q₀ := 0
  step q a := (if h : q.val + 1 < 7 * k + 1 then ⟨q.val + 1, h⟩ else 0,
    if enBloque i q.val then [a] else [])
  final _ := []
  length_step_le q a := by dsimp only; split_ifs <;> simp
  length_final_le _ := by simp

/-- Lo que deja pasar el proyector de una palabra que empieza en la posición `q`. -/
def selec (i : ℕ) : ℕ → List Bool → List Bool
  | _, [] => []
  | q, a :: u => (if enBloque i q then [a] else []) ++ selec i (q + 1) u

theorem selec_append (i q : ℕ) (u v : List Bool) :
    selec i q (u ++ v) = selec i q u ++ selec i (q + u.length) v := by
  induction u generalizing q with
  | nil => simp [selec]
  | cons a u ih => simp [selec, ih]; ring_nf

theorem selec_antes (i q : ℕ) (u : List Bool) (h : q + u.length ≤ 7 * i + 1) : selec i q u = [] := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    simp only [List.length_cons] at h
    rw [selec, ite_eq_right (by unfold enBloque; omega), ih (q + 1) (by omega)]
    rfl

theorem selec_dentro (i q : ℕ) (u : List Bool) (h1 : 7 * i + 1 ≤ q) (h2 : q + u.length ≤ 7 * i + 8) :
    selec i q u = u := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    simp only [List.length_cons] at h2
    rw [selec, ite_eq_left ⟨h1, by omega⟩, ih (q + 1) (by omega) (by omega)]
    rfl

theorem selec_despues (i q : ℕ) (u : List Bool) (h : 7 * i + 8 ≤ q) : selec i q u = [] := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    rw [selec, ite_eq_right (by unfold enBloque; omega), ih (q + 1) (by omega)]
    rfl

theorem run_proyector (i : ℕ) (q : ℕ) (hq : q < 7 * k + 1) (u v : List Bool)
    (hu : q + u.length = 7 * k + 1) :
    (proyector k i).run ⟨q, hq⟩ (u ++ v) = selec i q u ++ (proyector k i).run 0 v := by
  induction u generalizing q with
  | nil => simp at hu; omega
  | cons a u ih =>
    have hstep : (proyector k i).step ⟨q, hq⟩ a =
        ((if h : q + 1 < 7 * k + 1 then ⟨q + 1, h⟩ else 0), if enBloque i q then [a] else []) := rfl
    rw [List.cons_append, MultiTapeTM.Transducer.run_cons, hstep, selec, List.append_assoc]
    congr 1
    by_cases h : q + 1 < 7 * k + 1
    · rw [dite_eq_left h]
      exact ih (q + 1) h (by simp at hu; omega)
    · rw [dite_eq_right h]
      have hu0 : u = [] := by simp at hu; apply List.eq_nil_of_length_eq_zero; omega
      subst hu0
      simp [selec]

/-- El proyector, sobre un paso: deja exactamente el bloque de la cinta `i`. -/
theorem selec_codPasoK (i : Fin k) (f : PasoK k) : selec i 0 (codPasoK k f) = codPaso (f i) := by
  have hdesc : List.ofFn f = (List.ofFn f).take i ++ [f i] ++ (List.ofFn f).drop (i + 1) := by
    rw [List.append_assoc, List.singleton_append]
    have : f i = (List.ofFn f)[(i : ℕ)]'(by simp) := by simp
    rw [this, List.cons_getElem_drop_succ, List.take_append_drop]
  have hlen : ((List.ofFn f).take i).length = i := by simp
  rw [codPasoK, hdesc]
  simp only [codPasos, List.flatMap_append, List.flatMap_singleton]
  rw [← codPasos, ← codPasos]
  have hA : (codPasos ((List.ofFn f).take i)).length = 7 * i := by rw [length_codPasos, hlen]
  simp only [selec, enBloque]
  simp only [List.append_assoc, selec_append]
  rw [selec_antes _ _ _ (by rw [hA]; omega), selec_dentro _ _ _ (by rw [hA]; omega)
    (by rw [hA, length_codPaso]; omega), selec_despues _ _ _ (by rw [hA, length_codPaso]; omega)]
  simp

/-- **El proyector calcula la proyección**: de la traza de las `k` cintas, la sucesión de pasos de la
cinta `i`. -/
theorem run_proyector_codPasosK (i : Fin k) (es : List (PasoK k)) :
    (proyector k i).run (proyector k i).q₀ (codPasosK k es) = codPasos (es.map (· i)) := by
  induction es with
  | nil => rfl
  | cons f es ih =>
    rw [codPasosK_cons, List.map_cons, codPasos_cons]
    have h0 : (proyector k i).q₀ = ⟨0, by omega⟩ := rfl
    rw [h0, run_proyector k i 0 (by omega) _ _ (by rw [length_codPasoK]; omega),
      selec_codPasoK, ← ih]
    rfl

/-- La proyección sobre la cinta `i`, en tiempo lineal. -/
theorem proyeccion_computableInO (i : Fin k) :
    MultiTapeTM.ComputableInO (fun es : List (PasoK k) => es.map (· i)) (encPasosK k) encPasos
      (fun es => es.length) (fun es => es.length) := by
  refine MultiTapeTM.ComputableInO.of_bounds
    (MultiTapeTM.Transducer.computableInTimeAndSpace (proyector k i)
      (fun es => (run_proyector_codPasosK k i es).symm)) (28 * k + 20) (fun es => ?_)
    (fun _ => Nat.zero_le _) (fun es => ?_)
  · change 4 * (codPasosK k es).length + 8 ≤ _
    rw [length_codPasosK]; nlinarith
  · change (codPasos _).length ≤ _
    rw [length_codPasos, List.length_map]; nlinarith

/-- **La pasada por la cinta `i` sobre la traza entera**, en tiempo lineal: proyectar y pasar. -/
theorem consistenteK_computableInO (i : Fin k) :
    MultiTapeTM.ComputableInO
      (fun es : List (PasoK k) => decide (ConsistenteCinta cintaVacia (es.map (· i))))
      (encPasosK k) MultiTapeTM.encBool (fun es => es.length) (fun es => es.length) := by
  have h := MultiTapeTM.ComputableInO.comp' consistente_computableInO (proyeccion_computableInO k i)
  refine h.mono 2 (fun es => ?_) (fun es => ?_) <;> simp <;> omega

/-- La condición de las cintas de trabajo: cada una, consistente desde la cinta vacía. -/
def TrabajoOk (es : List (PasoK k)) : Prop := ∀ i, ConsistenteCinta cintaVacia (es.map (· i))

instance (es : List (PasoK k)) : Decidable (TrabajoOk k es) := by unfold TrabajoOk; infer_instance

theorem all_computableInO (L : List (Fin k)) :
    MultiTapeTM.ComputableInO
      (fun es : List (PasoK k) => L.all fun i => decide (ConsistenteCinta cintaVacia (es.map (· i))))
      (encPasosK k) MultiTapeTM.encBool (fun es => es.length) (fun es => es.length) := by
  induction L with
  | nil =>
    refine (MultiTapeTM.ComputableInO.const (encIn := encPasosK k) (encMid := MultiTapeTM.encBool)
      true).mono (7 * k + 1) (fun es => ?_) (fun es => ?_)
    all_goals (change (codPasosK k es).length ≤ _; rw [length_codPasosK]; nlinarith)
  | cons i L ih =>
    have h := MultiTapeTM.ComputableInO.and' (consistenteK_computableInO k i) ih
    simp only [List.all_cons]
    exact h.mono 2 (fun es => by omega) (fun es => by omega)

/-- **Las `k` pasadas de Book–Greibach, en tiempo lineal**: decidir que la traza es consistente en
cada cinta de trabajo cuesta `O(|traza|)`, con la constante que depende de `k`. -/
theorem trabajoOk_computableInO :
    MultiTapeTM.ComputableInO (fun es : List (PasoK k) => decide (TrabajoOk k es))
      (encPasosK k) MultiTapeTM.encBool (fun es => es.length) (fun es => es.length) := by
  have h := all_computableInO k (List.finRange k)
  have he : (fun es : List (PasoK k) => decide (TrabajoOk k es)) =
      fun es => (List.finRange k).all fun i => decide (ConsistenteCinta cintaVacia (es.map (· i))) := by
    funext es
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
    simp [TrabajoOk]
  rw [he]
  exact h

end VariasCintas

/-! ## El enlace con las trazas de `SimulacionLineal` -/

section Enlace

variable {k : ℕ} {State : Type}

/-- La parte de cintas de trabajo de una traza de una máquina de cslib. -/
def trabajoDe (τ : List (EntradaC k Bool State)) : List (PasoK k) :=
  τ.map fun e i => ⟨e.lee.workTapeSymbols i, ⟨(e.acc.workTapes i).1, (e.acc.workTapes i).2⟩⟩

theorem proyeccionC_eq (i : Fin k) (τ : List (EntradaC k Bool State)) :
    proyeccionC i τ = (trabajoDe τ).map (· i) := by
  simp [proyeccionC, trabajoDe]

/-- **Book–Greibach sobre cslib, con las `k` pasadas como máquina**: con tiempo `t`, la máquina acepta
exactamente cuando hay una traza de largo `≤ t` que pasa el control, la parada, la cinta de entrada y la
salida, y cuya parte de trabajo hace que la máquina de `trabajoOk_computableInO` (tiempo lineal) diga
`true`. -/
theorem accepts_iff_pasadas (ntm : MultiTapeNTM k Bool State) {input : List Bool} {t : ℕ}
    (ht : ntm.RunsInTime input t) :
    ntm.Accepts input ↔ ∃ τ : List (EntradaC k Bool State), τ.length ≤ t ∧
      ControlC ntm (some ntm.q₀) τ ∧ estadoFinal (some ntm.q₀) τ = none ∧
      EntradaOk input 1 τ ∧ decide (TrabajoOk k (trabajoDe τ)) = true ∧
      (τ.map fun e => e.acc.output.toList).flatten = [true] := by
  rw [accepts_iff_por_cinta ntm ht]
  refine exists_congr fun τ => ?_
  have : (∀ i, ConsistenteCinta ⟨fun _ => none, 0⟩ (proyeccionC i τ)) ↔ TrabajoOk k (trabajoDe τ) := by
    simp only [TrabajoOk, proyeccionC_eq]
    rfl
  rw [this, decide_eq_true_iff]

end Enlace

/-! ## Controles -/

section Controles

/-- Escribir `1` y después leerlo: consistente. -/
def pasosBuenos : List Paso := [⟨none, ⟨some (some true), 0⟩⟩, ⟨some true, ⟨none, 1⟩⟩]

/-- Escribir `1`, moverse y leer `1` donde no hay nada: inconsistente. -/
def pasosMalos : List Paso := [⟨none, ⟨some (some true), 1⟩⟩, ⟨some true, ⟨none, 0⟩⟩]

theorem control_buenos : ConsistenteCinta cintaVacia pasosBuenos := by
  simp [pasosBuenos, cintaVacia, Cinta.leer, Cinta.aplicar]

theorem control_malos : ¬ ConsistenteCinta cintaVacia pasosMalos := by
  simp [pasosMalos, cintaVacia, Cinta.leer, Cinta.aplicar]

/-- **Control concreto**: sobre los 14 bits de `pasosBuenos` la pasada para en el paso 15 con `[true]`,
y en el paso 14 todavía corre. -/
theorem control_pasada_buenos :
    (pasada.runFrom (pasada.initCfg (codPasos pasosBuenos)) 15).output = [true] ∧
      (pasada.runFrom (pasada.initCfg (codPasos pasosBuenos)) 14).state ≠ none := by
  refine ⟨?_, ?_⟩
  · have := (pasada_decide pasosBuenos).2
    rw [decide_eq_true control_buenos] at this
    exact this
  · intro h
    have h2 : (pasada.runFrom (pasada.initCfg (codPasos pasosBuenos))
        (7 * pasosBuenos.length)).state = none := h
    rw [pasada_no_para_antes _ control_buenos] at h2
    exact Option.some_ne_none _ h2

/-- **Control concreto**: sobre `pasosMalos` la salida es `[false]`. -/
theorem control_pasada_malos :
    (pasada.runFrom (pasada.initCfg (codPasos pasosMalos)) 15).output = [false] := by
  have := (pasada_decide pasosMalos).2
  rw [decide_eq_false control_malos] at this
  exact this

/-- **Control de las `k` pasadas**: con dos cintas, una traza que es consistente en la cinta `0` pero no
en la `1` no pasa. -/
def trazaDosCintas : List (PasoK 2) := [fun i => if i = 0 then ⟨none, ⟨none, 0⟩⟩ else ⟨some true, ⟨none, 0⟩⟩]

theorem control_dos_cintas :
    ConsistenteCinta cintaVacia (trazaDosCintas.map (· 0)) ∧ ¬ TrabajoOk 2 trazaDosCintas := by
  refine ⟨?_, fun h => ?_⟩
  · simp [trazaDosCintas, cintaVacia, Cinta.leer]
  · have := h 1
    simp [trazaDosCintas, cintaVacia, Cinta.leer] at this

end Controles

end Sagitta.Map.Tiempo.BookGreibachMaquina
