import Mathlib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.Time

/-!
# La simulación lineal de Book y Greibach: adivinar la traza y verificarla cinta por cinta

Segundo ladrillo hacia la jerarquía no determinista **fina** (`NTIME(f) ⊊ NTIME(g)` si `f(n+1) ∈ o(g(n))`), que
`Sagitta/Map/JerarquiaFina.lean` dejó bloqueada: la diagonal perezosa de cslib-frontier simula con sobrecosto polinomial
y la fina pide sobrecosto lineal. La herramienta clásica es la simulación de Book y Greibach (1970): una máquina no
determinista de `k` cintas que corre en tiempo `t` se simula, con un número fijo de cintas, en tiempo `O(t)`,
adivinando la traza entera (estado, símbolos leídos y acción de cada paso) y verificándola **una cinta a la vez**.
Este archivo prueba el corazón lógico de esa simulación, en un modelo propio y sobre las máquinas de cslib-frontier;
no construye la máquina simuladora.

## 1. El mapa de cslib-frontier (por qué su sobrecosto es polinomial)

* **Las máquinas.** `Turing.MultiTapeNTM k Symbol State` (cslib, `Machines/Turing/MultiTape/Nondeterministic.lean`)
  es un estado inicial `q₀` y una relación `Tr q (símbolo de entrada) (símbolos de trabajo) acción`. La configuración
  `Turing.Cfg` tiene una cinta de entrada de solo lectura (posición en `Fin (n + 2)`, recortada en los bordes,
  `moveInputPos`), `k` cintas de trabajo `ℤ → Option Symbol` con su cabeza en `ℤ`, y una salida de solo escritura.
  `Turing.Action.apply` actúa **cinta por cinta**: escribe en la celda bajo cada cabeza y mueve cada cabeza a lo sumo
  una celda (`Turing.workTapePos_apply_le`). Esa independencia es lo que explota Book–Greibach.
* **El tiempo.** `MultiTapeNTM.RunsInTime input t`: todo camino de cómputo de al menos `t` pasos terminó.
  `MultiTapeNTM.DecidesInTime` lo pide en cada instancia, y `MultiTapeNTM.DecidableInTime A enc t` cuantifica
  **existencialmente** `k`, `State` (finito) y la máquina (cslib-frontier,
  `Machines/Turing/MultiTape/Complexity/Nondeterministic.lean`). `Cslib.Complexity.NTIME enc t`
  (`Complexity/Classes/Time.lean`) es `DecidableInTime` con `c₁ · t + c₂`. Como `k` es existencial por lenguaje, la
  biblioteca no tiene una clase «`NTIME` con un número fijo de cintas»; el número de cintas importa solo cuando una
  **misma** máquina tiene que simular a todas, que es lo que hace la diagonal.
* **Los verificadores.** `Cslib.Complexity.exists_verifier_of_mem_NTIME` (`Classes/Time/Verifier.lean`) ya da, para
  cada problema de `NTIME t`, un verificador **determinista de tiempo lineal** en el par codificado, con
  certificados de todo largo `≥ c · t + c`: el certificado son las elecciones (`MultiTapeNTM.checkChoices`) y se
  reproducen con la tabla de elecciones. Y `Cslib.Complexity.setOf_exists_mem_NTIME` es el converso: adivinar y
  verificar en tiempo explícito. Ese verificador lineal **no es universal**: es otra máquina para cada problema, con
  las `k` cintas del problema.
* **La universal.** `Turing.MultiTapeTM.Universal.universal` corre una descripción (`Universal.Desc`) sobre una
  entrada con un reloj, de forma **determinista**, y `Universal.computableInO_universal_polynomialBound`
  (`Universal/ResourceBound.lean`) la acota en tiempo `O((I + 1)^4 · (t + 1)^2)`, con `I` el largo de la entrada
  codificada y `t` el reloj. La configuración simulada vive codificada en las cintas de la universal y cada paso
  simulado la recorre: de ahí el reloj al cuadrado y la potencia del tamaño.
* **La diagonal perezosa.** `Cslib.Complexity.Diagonal.lazyAccepts β c y v` (`Hierarchy/LazyDiagonal.lean`) corre
  con la universal el verificador **determinista** descrito por `c` sobre `(y, v)` durante `β y v` pasos, y
  `Diagonal.exists_computableInO_lazyAccepts` (`Hierarchy/LazyDiagonalVerifier.lean`) la acota por
  `((|c| + 1)^D + |y| + |v| + 1)^4 · β²`. En `Hierarchy/NondeterministicTime.lean` eso es el `accBound d D` privado,
  `(…)^4 · (|y| + 1)^(2d+6)`, con reloj `(m + 1)^(d+3)` y certificados de largo `(m + 1)^(d+2)`: la brecha
  `6d + 14` de `NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le` es ese sobrecosto, y lo mismo, con `accBound D`, en
  `Hierarchy/NondeterministicExponentialTime.lean` (`8k + 16`). Lo más cercano a Book–Greibach en la biblioteca es
  `Universal.budgetedNUniversal` (`Universal/NondeterministicBudget.lean`): adivina las transiciones de una
  descripción una por una, pero guarda la configuración simulada entera y está pensado para espacio, no para tiempo
  lineal.
* **Qué habría que cambiar.** Reemplazar en la diagonal la corrida determinista `lazyAccepts` por una verificación
  no determinista de traza: adivinar la traza de la máquina descrita y verificar el control contra la tabla de la
  descripción, la cinta de entrada y cada cinta de trabajo con una pasada por cinta (este archivo dice que eso es
  equivalente a correrla), todo en una máquina con un número **fijo** de cintas y tiempo `poly(|c|) · t`. Con eso, la
  diagonal copia un paso adelante por `c_M · f(n + 1)`, que es lo que `JerarquiaFina.intervalo_existe` pide.

## 2. Qué se prueba, en el modelo propio (§2)

Un modelo chico de máquina no determinista de `k` cintas (`MaquinaK`, `Conf`, `MaquinaK.Corre`) con cintas
`ℤ → C` (`Cinta`) y operaciones locales (`OpCinta`: escribir o no, mover a lo sumo una celda), y trazas adivinadas
(`Entrada`: estado, `k` lecturas, acción).

* **(a)** `corre_iff`: de `c` se llega a `c'` en exactamente `t` pasos si y solo si hay una traza de largo `t`
  válida desde `c` que lleva a `c'`.
* **(b)** `valida_iff`, **la clave**: una traza es válida (`ValidaTraza`, en cada paso la configuración real tiene
  el estado y los símbolos declarados) si y solo si su parte de control es válida (`ControlTraza`, que no mira
  ninguna cinta) y, **para cada cinta por separado**, su proyección es consistente (`ConsistenteCinta`).
  `consistente_iff_ultima` lo dice en la forma declarativa: la lectura `j` coincide con la **última escritura** en
  la celda donde está la cabeza en el paso `j`, o con el contenido inicial si nadie escribió ahí
  (`Cinta.correr_celdas`, `Cinta.correr_cabeza`). `finalTraza_cintas`: la cinta `i` final depende solo de la
  proyección `i`.
* **(c)** En un **modelo de costo declarado** (`Pasada`: una cinta simulada y la proyección leída como flujo, un
  paso por entrada), la pasada decide la consistencia en exactamente `|τ|` pasos (`Pasada.iterar`), no en menos
  (`Pasada.resto_iterar`), y cada paso es local: la cabeza se mueve a lo sumo una celda y solo cambia la celda que
  leyó (`Pasada.paso_local`). El total, `k` pasadas más la de control, es `(k + 1) · t` (`costo_verificacion`).

## 3. Qué se prueba sobre cslib-frontier (§3)

Las mismas piezas sobre `Turing.MultiTapeNTM` y `Turing.Cfg`, con la cinta de entrada (`EntradaOk`) y la salida
aparte:

* `validaC_iff`: validez global = control (`ControlC`) ∧ cinta de entrada (`EntradaOk`) ∧ cada cinta de trabajo
  consistente (`ConsistenteCinta (cintaDe c i) (proyeccionC i τ)`, reusando el modelo de §2).
* `accepts_iff_traza`, `accepts_iff_traza_le`: la máquina acepta si y solo si hay una traza válida que termina
  parada con salida `[true]`; si corre en tiempo `t`, de largo a lo sumo `t`.
* `accepts_iff_por_cinta` y `mem_NTIME_iff_trazas`: **el certificado de Book–Greibach para `NTIME`**. Un problema
  está en `NTIME enc t` si y solo si alguna máquina con tiempo `c₁ · t + c₂` lo decide y en cada instancia la
  pertenencia se certifica con una traza de largo `≤ c₁ · t + c₂` que pasa por separado el control, el estado
  final, la cinta de entrada, cada cinta de trabajo y la salida emitida.

Metas del encargo: la 1 (mapa) y la 2 completas; la 3 **solo en lo semántico** (la traza como certificado, cinta
por cinta, sobre las máquinas de la biblioteca); la 4 no.

## La lectura, en el lenguaje del proyecto

Simular una máquina cuesta caro cuando el simulador tiene que **llevar** la configuración: cada paso simulado
recorre lo que se lleva, y el costo se multiplica. Book y Greibach no la llevan: la **adivinan** paso a paso y
después solo **comprueban**. Lo que este archivo aísla es por qué comprobar es barato: el único acoplamiento entre
las cintas pasa por el control finito, así que «la traza entera es coherente» se parte en `k + 1` preguntas que no
se hablan entre sí, y cada una se contesta con una pasada que mira una sola cinta. El no determinismo paga la
adivinanza; la independencia de las cintas paga la verificación. Es la misma forma que la diagonal perezosa:
negar es caro, copiar es barato, y la cuenta cierra solo si copiar cuesta lineal.

## Dónde encaja en el programa de Williams, y qué falta

Las piezas de Williams (NEXP ⊄ ACC⁰) son: la jerarquía no determinista fina, el lema del testigo fácil
(Impagliazzo–Kabanets–Wigderson), la reducción sucinta con `n + O(log n)` bits y el algoritmo de ACC-SAT más rápido
que `2^n`. Este archivo es un paso **dentro** de la primera: la parte lógica de la simulación lineal. Después de
esto falta: (1) la máquina simuladora de Book–Greibach sobre cslib-frontier, con número fijo de cintas y tiempo
`poly(|c|) · t`, y con ella la diagonal perezosa fina (`JerarquiaFina` §2 ya tiene la aritmética de intervalos);
(2) los testigos fáciles; (3) la reducción sucinta; (4) ACC-SAT.

## Lo que NO se prueba

* **No se construye ninguna máquina.** No hay una `MultiTapeNTM` con número fijo de cintas que simule a otra en
  tiempo `O(t)`, ni un verificador en el sentido de `ComputableInO` (`Classes/Time/Verifier.lean`) que chequee
  trazas. `mem_NTIME_iff_trazas` caracteriza la pertenencia por trazas, pero el chequeo es una proposición, no un
  programa con tiempo medido.
* **El costo de §2 (c) es declarado.** `Pasada` es un modelo de costo: cuenta pasos de una pasada que consume una
  entrada por paso. Que una máquina de Turing de dos cintas haga cada paso en tiempo constante exige que las
  entradas de la traza tengan ancho constante (cierto para una máquina fija con estados y alfabeto finitos, pero
  el ancho crece con la descripción en la universal) y volver a rebobinar entre pasadas; nada de eso se modela.
  `Pasada.paso_local` es la evidencia de localidad, no una prueba de costo en máquinas.
* **No hay universal no determinista lineal ni jerarquía fina** (meta 4). Lo que la bloquea, con precisión:
  (i) construir con los combinadores de cslib-frontier la verificadora de trazas de una descripción `Universal.Desc`
  (buscar cada transición declarada en la tabla, `EntradaOk` sobre la entrada, una pasada por cinta de trabajo con
  `k` leído de la descripción) y acotarla en `ComputableInO` por `poly(|c|) · t`; (ii) cambiar la diagonal perezosa
  para que diagonalice contra máquinas no deterministas por traza en lugar de contra verificadores deterministas
  corridos con `universal`; (iii) construibilidad en tiempo de `f` y `g` generales (la biblioteca la tiene para
  potencias, `timeConstructible_succ_pow`); (iv) el factor logarítmico de escribir en unario el largo del
  certificado, que `JerarquiaFina` ya señaló.
* **Ninguna afirmación sobre el número exacto de cintas** de la simulación de Book–Greibach ni sobre su constante;
  el modelo dice `(k + 1) · t` pasos de pasadas, no cuántas cintas usa una máquina real.
* **Nada sobre P contra NP**, ni sobre NEXP contra ACC⁰.

## Fuentes

* R. V. Book y S. A. Greibach, «Quasi-realtime languages», *Mathematical Systems Theory* 4(1):97–111, 1970,
  doi:10.1007/BF01705890 (verificado en Crossref; no lo leí: la idea de adivinar la traza y verificarla por cinta es
  de memoria, y las pruebas de aquí son propias).
* S. Žák, «A Turing machine time hierarchy», *Theoretical Computer Science* 26(3):327–333, 1983,
  doi:10.1016/0304-3975(83)90015-4, y J. I. Seiferas, M. J. Fischer y A. R. Meyer, *J. ACM* 25:146–167, 1978,
  doi:10.1145/322047.322061 (verificados en Crossref por `JerarquiaFina`; no los leí).
* Williams, Impagliazzo–Kabanets–Wigderson: de memoria (ver `JerarquiaFina`).
-/

namespace Sagitta.Map.Tiempo.SimulacionLineal

/-! ## 2. El corazón de Book–Greibach, sin máquinas de cslib -/

section Abstracto

variable {C : Type*}

/-- Lo que una máquina le hace a una cinta en un paso: escribir (o no) en la celda bajo la cabeza, y
mover la cabeza a lo sumo una celda. -/
structure OpCinta (C : Type*) where
  /-- el símbolo que se escribe, si se escribe -/
  escribe : Option C
  /-- el movimiento de la cabeza -/
  mueve : SignType

/-- Una cinta infinita en las dos direcciones, con su cabeza. -/
structure Cinta (C : Type*) where
  /-- el contenido de cada celda -/
  celdas : ℤ → C
  /-- la posición de la cabeza -/
  cabeza : ℤ

/-- El símbolo bajo la cabeza. -/
def Cinta.leer (T : Cinta C) : C := T.celdas T.cabeza

/-- El efecto de una operación sobre una cinta. -/
def Cinta.aplicar (T : Cinta C) (o : OpCinta C) : Cinta C :=
  ⟨match o.escribe with
    | none => T.celdas
    | some s => Function.update T.celdas T.cabeza s,
   T.cabeza + (o.mueve : ℤ)⟩

/-- Correr una lista de operaciones sobre una cinta. -/
def Cinta.correr : Cinta C → List (OpCinta C) → Cinta C
  | T, [] => T
  | T, o :: os => (T.aplicar o).correr os

/-- La proyección de un paso sobre una cinta: lo que la traza dice que se leyó y lo que se hizo. -/
structure PasoCinta (C : Type*) where
  /-- el símbolo que la traza dice que se leyó -/
  lee : C
  /-- la operación sobre la cinta -/
  op : OpCinta C

/-- **Consistencia de una cinta.** Corriendo las operaciones desde `T`, cada lectura declarada coincide
con el símbolo que de verdad está bajo la cabeza. -/
def ConsistenteCinta : Cinta C → List (PasoCinta C) → Prop
  | _, [] => True
  | T, e :: es => T.leer = e.lee ∧ ConsistenteCinta (T.aplicar e.op) es

@[simp] theorem consistente_nil (T : Cinta C) : ConsistenteCinta T [] := trivial

@[simp] theorem consistente_cons (T : Cinta C) (e : PasoCinta C) (es : List (PasoCinta C)) :
    ConsistenteCinta T (e :: es) ↔ T.leer = e.lee ∧ ConsistenteCinta (T.aplicar e.op) es := Iff.rfl

/-! ### La consistencia, celda por celda: «cada lectura es la última escritura» -/

/-- Las escrituras de una lista de operaciones que arranca con la cabeza en `p`: pares (celda, símbolo),
en orden. -/
def escrituras : ℤ → List (OpCinta C) → List (ℤ × C)
  | _, [] => []
  | p, o :: os => (o.escribe.map fun s => (p, s)).toList ++ escrituras (p + (o.mueve : ℤ)) os

/-- La posición de la cabeza después de una lista de operaciones que arranca en `p`. -/
def posicion (p : ℤ) (os : List (OpCinta C)) : ℤ := p + (os.map fun o => (o.mueve : ℤ)).sum

/-- La última escritura en la celda `x`, si la hubo. -/
def ultimaEn (x : ℤ) (ws : List (ℤ × C)) : Option C :=
  ((ws.filter fun w => decide (w.1 = x)).getLast?).map Prod.snd

theorem ultimaEn_append (x : ℤ) (a b : List (ℤ × C)) :
    ultimaEn x (a ++ b) = (ultimaEn x b).or (ultimaEn x a) := by
  simp only [ultimaEn, List.filter_append, List.getLast?_append, Option.map_or]

theorem Cinta.correr_cabeza (T : Cinta C) (os : List (OpCinta C)) :
    (T.correr os).cabeza = posicion T.cabeza os := by
  induction os generalizing T with
  | nil => simp [Cinta.correr, posicion]
  | cons o os ih =>
    rw [Cinta.correr, ih]
    simp only [posicion, Cinta.aplicar, List.map_cons, List.sum_cons]
    ring

/-- **El contenido de una celda es su última escritura, o el contenido inicial.** -/
theorem Cinta.correr_celdas (T : Cinta C) (os : List (OpCinta C)) (x : ℤ) :
    (T.correr os).celdas x = (ultimaEn x (escrituras T.cabeza os)).getD (T.celdas x) := by
  induction os generalizing T with
  | nil => simp [Cinta.correr, escrituras, ultimaEn]
  | cons o os ih =>
    rw [Cinta.correr, ih, escrituras, ultimaEn_append]
    simp only [Cinta.aplicar]
    rcases o with ⟨_ | s, m⟩
    · simp [ultimaEn]
    · by_cases hx : T.cabeza = x
      · subst hx; simp [ultimaEn]
      · simp [ultimaEn, hx, Function.update_of_ne (Ne.symm hx)]

/-- La consistencia, dicha paso por paso: la lectura `j` coincide con lo que hay bajo la cabeza después de
correr los primeros `j` pasos. -/
theorem consistente_iff_forall (T : Cinta C) (es : List (PasoCinta C)) :
    ConsistenteCinta T es ↔ ∀ j (hj : j < es.length),
      (T.correr ((es.take j).map PasoCinta.op)).leer = es[j].lee := by
  induction es generalizing T with
  | nil => simp
  | cons e es ih =>
    rw [consistente_cons, ih]
    constructor
    · rintro ⟨h0, h⟩ j hj
      cases j with
      | zero => simpa [Cinta.correr] using h0
      | succ j =>
        simpa [Cinta.correr] using h j (by simpa using hj)
    · intro h
      have h0 := h 0 (by simp)
      rw [List.getElem_cons_zero] at h0
      refine ⟨by simpa [Cinta.correr] using h0, fun j hj => ?_⟩
      have := h (j + 1) (by simpa using hj)
      rw [List.getElem_cons_succ] at this
      simpa [Cinta.correr] using this

/-- **Consistencia = cada lectura es la última escritura en su celda, o el contenido inicial.** La forma
declarativa de la verificación por cinta: la lectura `j` de la traza coincide con la última escritura,
entre los primeros `j` pasos, en la celda donde está la cabeza en el paso `j`; si nadie escribió ahí,
con el contenido inicial. -/
theorem consistente_iff_ultima (T : Cinta C) (es : List (PasoCinta C)) :
    ConsistenteCinta T es ↔ ∀ j (hj : j < es.length),
      es[j].lee =
        (ultimaEn (posicion T.cabeza ((es.take j).map PasoCinta.op))
            (escrituras T.cabeza ((es.take j).map PasoCinta.op))).getD
          (T.celdas (posicion T.cabeza ((es.take j).map PasoCinta.op))) := by
  rw [consistente_iff_forall]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  rw [Cinta.leer, Cinta.correr_celdas, Cinta.correr_cabeza, eq_comm]

/-! ### Una máquina de `k` cintas y sus trazas -/

/-- Lo que hace una máquina de `k` cintas en un paso: una operación por cinta y el estado siguiente
(`none` para parar). -/
structure Accion (k : ℕ) (C Q : Type*) where
  /-- la operación sobre cada cinta -/
  ops : Fin k → OpCinta C
  /-- el estado siguiente, o `none` para parar -/
  sig : Option Q

/-- Una máquina no determinista de `k` cintas: una relación entre el estado, los `k` símbolos leídos y la
acción. -/
structure MaquinaK (k : ℕ) (C Q : Type*) where
  /-- las transiciones permitidas -/
  δ : Q → (Fin k → C) → Accion k C Q → Prop

/-- Una configuración: el estado (o `none`, parada) y las `k` cintas. -/
structure Conf (k : ℕ) (C Q : Type*) where
  /-- el estado, o `none` si paró -/
  estado : Option Q
  /-- las cintas -/
  cintas : Fin k → Cinta C

variable {k : ℕ} {Q : Type*}

/-- Los `k` símbolos bajo las cabezas. -/
def Conf.lee (c : Conf k C Q) : Fin k → C := fun i => (c.cintas i).leer

/-- El efecto de una acción sobre una configuración. -/
def Conf.aplicar (c : Conf k C Q) (a : Accion k C Q) : Conf k C Q :=
  ⟨a.sig, fun i => (c.cintas i).aplicar (a.ops i)⟩

/-- Un paso desde una configuración que no ha parado. -/
def MaquinaK.Paso (M : MaquinaK k C Q) (c c' : Conf k C Q) : Prop :=
  ∃ q a, c.estado = some q ∧ M.δ q c.lee a ∧ c' = c.aplicar a

/-- `Corre c t c'`: de `c` se llega a `c'` en exactamente `t` pasos. -/
inductive MaquinaK.Corre (M : MaquinaK k C Q) : Conf k C Q → ℕ → Conf k C Q → Prop
  | refl (c) : M.Corre c 0 c
  | paso {c c' c'' n} : M.Paso c c' → M.Corre c' n c'' → M.Corre c (n + 1) c''

/-- Una entrada de la traza adivinada: el estado, los `k` símbolos leídos y la acción. -/
structure Entrada (k : ℕ) (C Q : Type*) where
  /-- el estado en que se da el paso -/
  q : Q
  /-- los símbolos que se dicen leídos -/
  lee : Fin k → C
  /-- la acción -/
  acc : Accion k C Q

/-- La configuración a la que lleva una traza, aplicando sus acciones. -/
def finalTraza : Conf k C Q → List (Entrada k C Q) → Conf k C Q
  | c, [] => c
  | c, e :: es => finalTraza (c.aplicar e.acc) es

/-- **Validez global de una traza**: en cada paso la configuración real está en el estado declarado, tiene
bajo las cabezas los símbolos declarados y la transición está permitida. -/
def ValidaTraza (M : MaquinaK k C Q) : Conf k C Q → List (Entrada k C Q) → Prop
  | _, [] => True
  | c, e :: es => c.estado = some e.q ∧ c.lee = e.lee ∧ M.δ e.q e.lee e.acc ∧
      ValidaTraza M (c.aplicar e.acc) es

/-- **La parte de control de una traza**: los estados encadenan y cada transición declarada está permitida.
No mira ninguna cinta. -/
def ControlTraza (M : MaquinaK k C Q) : Option Q → List (Entrada k C Q) → Prop
  | _, [] => True
  | s, e :: es => s = some e.q ∧ M.δ e.q e.lee e.acc ∧ ControlTraza M e.acc.sig es

/-- La proyección de una traza sobre la cinta `i`. -/
def proyeccion (i : Fin k) (τ : List (Entrada k C Q)) : List (PasoCinta C) :=
  τ.map fun e => ⟨e.lee i, e.acc.ops i⟩

/-- **(b) Consistencia global = control y consistencia por cinta.** Una traza es válida exactamente
cuando su parte de control lo es y, para cada cinta por separado, su proyección es consistente. -/
theorem valida_iff (M : MaquinaK k C Q) (c : Conf k C Q) (τ : List (Entrada k C Q)) :
    ValidaTraza M c τ ↔ ControlTraza M c.estado τ ∧ ∀ i, ConsistenteCinta (c.cintas i) (proyeccion i τ) := by
  induction τ generalizing c with
  | nil => simp [ValidaTraza, ControlTraza, proyeccion]
  | cons e es ih =>
    simp only [ValidaTraza, ControlTraza, proyeccion, List.map_cons, consistente_cons]
    rw [ih]
    simp only [Conf.aplicar, proyeccion, funext_iff, Conf.lee, forall_and]
    tauto

/-- **(a) Una corrida es una traza válida.** De `c` se llega a `c'` en `t` pasos exactamente cuando hay una
traza de largo `t`, válida desde `c`, que lleva a `c'`. -/
theorem corre_iff (M : MaquinaK k C Q) (c c' : Conf k C Q) (t : ℕ) :
    M.Corre c t c' ↔ ∃ τ : List (Entrada k C Q), τ.length = t ∧ ValidaTraza M c τ ∧ finalTraza c τ = c' := by
  constructor
  · intro h
    induction h with
    | refl c => exact ⟨[], rfl, trivial, rfl⟩
    | paso hp _ ih =>
      obtain ⟨q, a, hq, hδ, rfl⟩ := hp
      obtain ⟨τ, hl, hv, hf⟩ := ih
      exact ⟨⟨q, _, a⟩ :: τ, by simp [hl], ⟨hq, rfl, hδ, hv⟩, hf⟩
  · rintro ⟨τ, rfl, hv, rfl⟩
    induction τ generalizing c with
    | nil => exact .refl c
    | cons e es ih =>
      obtain ⟨hq, hl, hδ, hv⟩ := hv
      exact .paso ⟨e.q, e.acc, hq, hl ▸ hδ, rfl⟩ (ih _ hv)

/-- **(a) + (b): la simulación por traza, cinta por cinta.** -/
theorem corre_iff_por_cinta (M : MaquinaK k C Q) (c c' : Conf k C Q) (t : ℕ) :
    M.Corre c t c' ↔ ∃ τ : List (Entrada k C Q), τ.length = t ∧ ControlTraza M c.estado τ ∧
      (∀ i, ConsistenteCinta (c.cintas i) (proyeccion i τ)) ∧ finalTraza c τ = c' := by
  rw [corre_iff]
  simp only [valida_iff, and_assoc]

/-- El estado al que lleva una traza depende solo de su parte de control. -/
theorem finalTraza_estado (c : Conf k C Q) (e : Entrada k C Q) (es : List (Entrada k C Q)) :
    (finalTraza c (e :: es)).estado = ((e :: es).getLast (List.cons_ne_nil _ _)).acc.sig := by
  induction es generalizing c e with
  | nil => rfl
  | cons e' es ih => exact ih _ e'

/-- La cinta `i` a la que lleva una traza depende solo de su proyección sobre la cinta `i`. -/
theorem finalTraza_cintas (c : Conf k C Q) (τ : List (Entrada k C Q)) (i : Fin k) :
    (finalTraza c τ).cintas i = (c.cintas i).correr ((proyeccion i τ).map PasoCinta.op) := by
  induction τ generalizing c with
  | nil => rfl
  | cons e es ih =>
    rw [finalTraza, ih]
    rfl

/-! ### (c) El costo: una pasada por cinta -/

/-- **El modelo de costo declarado.** Una pasada lee la proyección de una cinta como un flujo y lleva una sola
cinta simulada: en cada paso consume una entrada, compara la lectura declarada con la celda bajo la cabeza
y aplica la operación. -/
structure Pasada (C : Type*) where
  /-- la cinta simulada -/
  cinta : Cinta C
  /-- lo que falta de la proyección -/
  resto : List (PasoCinta C)
  /-- si todas las lecturas hasta aquí coincidieron -/
  ok : Bool

/-- Un paso de la pasada. Con la proyección agotada, la pasada se queda quieta. -/
def Pasada.paso [DecidableEq C] : Pasada C → Pasada C
  | ⟨T, [], b⟩ => ⟨T, [], b⟩
  | ⟨T, e :: es, b⟩ => ⟨T.aplicar e.op, es, b && decide (T.leer = e.lee)⟩

variable [DecidableEq C]

/-- **Un paso de la pasada es local**: la cabeza se mueve a lo sumo una celda y solo cambia la celda que
estaba bajo ella. Es lo que deja hacerlo en tiempo constante con una cinta de trabajo, si las entradas de
la traza tienen ancho constante. -/
theorem Pasada.paso_local (P : Pasada C) :
    |(Pasada.paso P).cinta.cabeza - P.cinta.cabeza| ≤ 1 ∧
      ∀ x, x ≠ P.cinta.cabeza → (Pasada.paso P).cinta.celdas x = P.cinta.celdas x := by
  rcases P with ⟨T, _ | ⟨e, es⟩, b⟩
  · simp [Pasada.paso]
  · refine ⟨?_, fun x hx => ?_⟩
    · simp only [Pasada.paso, Cinta.aplicar, add_sub_cancel_left]
      rcases e.op.mueve with _ | _ | _ <;> simp
    · simp only [Pasada.paso, Cinta.aplicar]
      rcases e.op.escribe with _ | s
      · rfl
      · exact Function.update_of_ne hx _ _

/-- **(c) La pasada decide la consistencia en exactamente `|es|` pasos.** -/
theorem Pasada.iterar (T : Cinta C) (es : List (PasoCinta C)) (b : Bool) :
    (Pasada.paso^[es.length] ⟨T, es, b⟩).resto = [] ∧
      ((Pasada.paso^[es.length] ⟨T, es, b⟩).ok = true ↔ b = true ∧ ConsistenteCinta T es) := by
  induction es generalizing T b with
  | nil => simp
  | cons e es ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    obtain ⟨h1, h2⟩ := ih (T.aplicar e.op) (b && decide (T.leer = e.lee))
    refine ⟨h1, ?_⟩
    simp only [Pasada.paso]
    rw [h2]
    simp [and_assoc]

/-- **(c) Y no en menos**: antes de `|es|` pasos la pasada todavía no consumió toda la proyección. -/
theorem Pasada.resto_iterar (T : Cinta C) (es : List (PasoCinta C)) (b : Bool) (n : ℕ)
    (hn : n ≤ es.length) :
    (Pasada.paso^[n] ⟨T, es, b⟩).resto.length = es.length - n := by
  induction n generalizing T es b with
  | zero => simp
  | succ n ih =>
    rcases es with _ | ⟨e, es⟩
    · simp at hn
    · rw [Function.iterate_succ_apply]
      simp only [Pasada.paso]
      rw [ih _ _ _ (by simp at hn; omega)]
      simp

omit [DecidableEq C] in
/-- **(c) El costo total de verificar una traza de largo `t`**: una pasada de `t` pasos por cada una de las
`k` cintas. La parte de control es una pasada más, sin cinta (mira una entrada a la vez), y suma `t`. Es una cuenta de
entradas consumidas en el modelo `Pasada` (costo declarado), no tiempo de máquina. -/
theorem costo_verificacion (τ : List (Entrada k C Q)) :
    (∑ i : Fin k, (proyeccion i τ).length) + τ.length = (k + 1) * τ.length := by
  simp [proyeccion]
  ring

end Abstracto

/-! ## 3. Sobre las máquinas de cslib-frontier: la traza como certificado -/

section Cslib

open Turing

variable {k : ℕ} {Symbol State : Type*}

/-- Una entrada de la traza de una `MultiTapeNTM` de cslib: el estado, los símbolos bajo las cabezas
(entrada y `k` cintas de trabajo) y la acción. -/
structure EntradaC (k : ℕ) (Symbol State : Type*) where
  /-- el estado en que se da el paso -/
  q : State
  /-- los símbolos que se dicen leídos -/
  lee : HeadSymbols k Symbol
  /-- la acción -/
  acc : Action k Symbol State

variable {input : List Symbol}

/-- La configuración a la que lleva una traza. -/
def finalC : Cfg k Symbol State input → List (EntradaC k Symbol State) → Cfg k Symbol State input
  | c, [] => c
  | c, e :: es => finalC (e.acc.apply c) es

/-- **Validez global** de una traza para una máquina de cslib. -/
def ValidaC (ntm : MultiTapeNTM k Symbol State) :
    Cfg k Symbol State input → List (EntradaC k Symbol State) → Prop
  | _, [] => True
  | c, e :: es => c.state = some e.q ∧ c.headSymbols = e.lee ∧
      ntm.Tr e.q e.lee.inputSymbol e.lee.workTapeSymbols e.acc ∧ ValidaC ntm (e.acc.apply c) es

/-- **La parte de control**: estados encadenados y transiciones permitidas. No mira ninguna cinta. -/
def ControlC (ntm : MultiTapeNTM k Symbol State) : Option State → List (EntradaC k Symbol State) → Prop
  | _, [] => True
  | s, e :: es => s = some e.q ∧ ntm.Tr e.q e.lee.inputSymbol e.lee.workTapeSymbols e.acc ∧
      ControlC ntm e.acc.state es

/-- El estado al que llega la parte de control. -/
def estadoFinal : Option State → List (EntradaC k Symbol State) → Option State
  | s, [] => s
  | _, e :: es => estadoFinal e.acc.state es

/-- El símbolo bajo la cabeza de entrada en la posición `pos` (desplazada en uno, como en cslib). -/
def simboloEn (w : List Symbol) (pos : Fin (w.length + 2)) : Option Symbol :=
  if h₁ : pos = 0 then none
  else if h₂ : pos = w.length + 1 then none
  else w[pos.val - 1]'(by grind)

theorem inputSymbol_eq (c : Cfg k Symbol State input) : c.inputSymbol = simboloEn input c.inputPos := by
  unfold Cfg.inputSymbol simboloEn
  split_ifs <;> rfl

/-- **La cinta de entrada**: cada lectura declarada coincide con el símbolo de la entrada en la posición de la
cabeza, que se mueve con los movimientos declarados. -/
def EntradaOk (input : List Symbol) :
    Fin (input.length + 2) → List (EntradaC k Symbol State) → Prop
  | _, [] => True
  | pos, e :: es => simboloEn input pos = e.lee.inputSymbol ∧
      EntradaOk input (moveInputPos pos e.acc.inputTape) es

/-- La cinta de trabajo `i` de una configuración, como cinta del modelo abstracto. -/
def cintaDe (c : Cfg k Symbol State input) (i : Fin k) : Cinta (Option Symbol) :=
  ⟨c.workTapes i, c.workTapePos i⟩

/-- La proyección de una traza sobre la cinta de trabajo `i`. -/
def proyeccionC (i : Fin k) (τ : List (EntradaC k Symbol State)) : List (PasoCinta (Option Symbol)) :=
  τ.map fun e => ⟨e.lee.workTapeSymbols i, ⟨(e.acc.workTapes i).1, (e.acc.workTapes i).2⟩⟩

theorem cintaDe_apply (c : Cfg k Symbol State input) (a : Action k Symbol State) (i : Fin k) :
    cintaDe (a.apply c) i = (cintaDe c i).aplicar ⟨(a.workTapes i).1, (a.workTapes i).2⟩ := by
  simp only [cintaDe, Action.apply, Cinta.aplicar]
  rcases (a.workTapes i).1 <;> rfl

/-- **(b) en cslib: consistencia global = control, entrada y cada cinta de trabajo por separado.** -/
theorem validaC_iff (ntm : MultiTapeNTM k Symbol State) (c : Cfg k Symbol State input)
    (τ : List (EntradaC k Symbol State)) :
    ValidaC ntm c τ ↔ ControlC ntm c.state τ ∧ EntradaOk input c.inputPos τ ∧
      ∀ i, ConsistenteCinta (cintaDe c i) (proyeccionC i τ) := by
  induction τ generalizing c with
  | nil => simp [ValidaC, ControlC, EntradaOk, proyeccionC]
  | cons e es ih =>
    simp only [ValidaC, ControlC, EntradaOk, proyeccionC, List.map_cons, consistente_cons]
    rw [ih]
    simp only [proyeccionC, cintaDe_apply, HeadSymbols.ext_iff, Cfg.headSymbols_inputSymbol,
      Cfg.headSymbols_workTapeSymbols, funext_iff, inputSymbol_eq, forall_and, Action.apply_state,
      Action.apply_inputPos]
    have hl : ∀ i, (cintaDe c i).leer = c.workTapeSymbols i := fun _ => rfl
    simp only [hl]
    tauto

theorem finalC_append (c : Cfg k Symbol State input) (τ σ : List (EntradaC k Symbol State)) :
    finalC c (τ ++ σ) = finalC (finalC c τ) σ := by
  induction τ generalizing c with
  | nil => rfl
  | cons e es ih => exact ih _

theorem validaC_append (ntm : MultiTapeNTM k Symbol State) (c : Cfg k Symbol State input)
    (τ σ : List (EntradaC k Symbol State)) :
    ValidaC ntm c (τ ++ σ) ↔ ValidaC ntm c τ ∧ ValidaC ntm (finalC c τ) σ := by
  induction τ generalizing c with
  | nil => simp [ValidaC, finalC]
  | cons e es ih =>
    simp only [List.cons_append, ValidaC, ih, finalC]
    tauto

theorem finalC_state (c : Cfg k Symbol State input) (τ : List (EntradaC k Symbol State)) :
    (finalC c τ).state = estadoFinal c.state τ := by
  induction τ generalizing c with
  | nil => rfl
  | cons e es ih => exact ih _

/-- La salida a la que lleva una traza: lo que había más lo que emiten sus acciones, en orden. -/
theorem finalC_output (c : Cfg k Symbol State input) (τ : List (EntradaC k Symbol State)) :
    (finalC c τ).output = c.output ++ (τ.map fun e => e.acc.output.toList).flatten := by
  induction τ generalizing c with
  | nil => simp [finalC]
  | cons e es ih =>
    rw [finalC, ih]
    simp [Action.apply]

/-- Una serie de pasos «corriendo» de la máquina es una traza válida. -/
theorem exists_traza_of_relSeries (ntm : MultiTapeNTM k Symbol State)
    (p : RelSeries (ntm.runningStepRel input)) :
    ∃ τ : List (EntradaC k Symbol State), τ.length = p.length ∧ ValidaC ntm p.head τ ∧
      finalC p.head τ = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton x => exact ⟨[], rfl, trivial, rfl⟩
  | snoc p x hx ih =>
    obtain ⟨τ, hl, hv, hf⟩ := ih
    obtain ⟨hnh, hstep⟩ := hx
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hnh
    simp only [MultiTapeNTM.Step, hq] at hstep
    obtain ⟨a, htr, rfl⟩ := hstep
    refine ⟨τ ++ [⟨q, p.last.headSymbols, a⟩], by simp [hl], ?_, ?_⟩
    · rw [RelSeries.head_snoc, validaC_append, hf]
      exact ⟨hv, hq, rfl, htr, trivial⟩
    · rw [RelSeries.head_snoc, finalC_append, hf, RelSeries.last_snoc]
      rfl

/-- Una traza válida desde la configuración inicial es un camino de cómputo, del mismo largo. -/
theorem exists_computationPath_of_traza (ntm : MultiTapeNTM k Symbol State)
    (τ : List (EntradaC k Symbol State)) (hv : ValidaC ntm (ntm.initCfg input) τ) :
    ∃ p : ntm.ComputationPath input, p.time = τ.length ∧ p.last = finalC (ntm.initCfg input) τ := by
  induction τ using List.reverseRecOn with
  | nil => exact ⟨⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩, rfl, rfl⟩
  | append_singleton τ e ih =>
    rw [validaC_append] at hv
    obtain ⟨hv, hq, hl, htr, -⟩ := hv
    obtain ⟨p, hpt, hpl⟩ := ih hv
    have hstep : ntm.Step p.last (e.acc.apply p.last) := by
      rw [hpl]
      simp only [MultiTapeNTM.Step, hq]
      refine ⟨e.acc, ?_, rfl⟩
      rw [← hl] at htr
      exact htr
    obtain ⟨p', hp't, hp'l⟩ := p.exists_snoc hstep
    refine ⟨p', by simp [hp't, hpt], ?_⟩
    rw [hp'l, hpl, finalC_append]
    rfl

/-- **(a) en cslib: aceptar es tener una traza válida que termina parada con salida `[true]`.** -/
theorem accepts_iff_traza (ntm : MultiTapeNTM k Bool State) (input : List Bool) :
    ntm.Accepts input ↔ ∃ τ : List (EntradaC k Bool State), ValidaC ntm (ntm.initCfg input) τ ∧
      (finalC (ntm.initCfg input) τ).state = none ∧ (finalC (ntm.initCfg input) τ).output = [true] := by
  constructor
  · rintro ⟨p, hh, ho⟩
    obtain ⟨q, hqh, hql, -, -⟩ := MultiTapeNTM.RunPath.exists_running p.toRunPath hh
    obtain ⟨τ, -, hv, hf⟩ := exists_traza_of_relSeries ntm q
    rw [hqh, p.head_eq] at hv hf
    exact ⟨τ, hv, by rw [hf, hql]; exact hh, by rw [hf, hql]; exact ho⟩
  · rintro ⟨τ, hv, hs, ho⟩
    obtain ⟨p, -, hp⟩ := exists_computationPath_of_traza ntm τ hv
    exact ⟨p, by rw [hp]; exact hs, by rw [hp]; exact ho⟩

/-- **(a) con el tiempo**: si la máquina corre en tiempo `t` sobre `input`, acepta exactamente cuando hay una
traza válida de largo a lo sumo `t` que termina parada con salida `[true]`. -/
theorem accepts_iff_traza_le (ntm : MultiTapeNTM k Bool State) {input : List Bool} {t : ℕ}
    (ht : ntm.RunsInTime input t) :
    ntm.Accepts input ↔ ∃ τ : List (EntradaC k Bool State), τ.length ≤ t ∧
      ValidaC ntm (ntm.initCfg input) τ ∧
      (finalC (ntm.initCfg input) τ).state = none ∧ (finalC (ntm.initCfg input) τ).output = [true] := by
  constructor
  · rintro ⟨p, hh, ho⟩
    obtain ⟨p', hp't, hp'l⟩ := ht.exists_time_eq p hh
    obtain ⟨q, hqh, hql, hqlen, -⟩ := MultiTapeNTM.RunPath.exists_running p'.toRunPath (hp'l ▸ hh)
    obtain ⟨τ, hτl, hv, hf⟩ := exists_traza_of_relSeries ntm q
    rw [hqh, p'.head_eq] at hv hf
    refine ⟨τ, ?_, hv, by rw [hf, hql, hp'l]; exact hh, by rw [hf, hql, hp'l]; exact ho⟩
    rw [hτl]
    exact hqlen.trans (le_of_eq hp't)
  · rintro ⟨τ, -, hv, hs, ho⟩
    exact (accepts_iff_traza ntm input).mpr ⟨τ, hv, hs, ho⟩

/-- **Book–Greibach sobre cslib, como certificado**: con tiempo `t`, la máquina acepta exactamente cuando hay
una traza de largo a lo sumo `t` que pasa, por separado, cinco verificaciones: el control (estados y
transiciones), el estado final (parada), la cinta de entrada, cada una de las `k` cintas de trabajo y la
salida emitida. Ninguna mira más de una cinta. -/
theorem accepts_iff_por_cinta (ntm : MultiTapeNTM k Bool State) {input : List Bool} {t : ℕ}
    (ht : ntm.RunsInTime input t) :
    ntm.Accepts input ↔ ∃ τ : List (EntradaC k Bool State), τ.length ≤ t ∧
      ControlC ntm (some ntm.q₀) τ ∧ estadoFinal (some ntm.q₀) τ = none ∧
      EntradaOk input 1 τ ∧
      (∀ i, ConsistenteCinta ⟨fun _ => none, 0⟩ (proyeccionC i τ)) ∧
      (τ.map fun e => e.acc.output.toList).flatten = [true] := by
  rw [accepts_iff_traza_le ntm ht]
  refine exists_congr fun τ => ?_
  rw [validaC_iff, finalC_state, finalC_output]
  simp only [MultiTapeNTM.initCfg, Cfg.init, List.nil_append, cintaDe]
  tauto

/-- **La traza como certificado de `NTIME` de cslib-frontier** (sin la máquina de Book–Greibach: el número de cintas y
el ancho de cada entrada siguen siendo los de cada problema). Un problema está en `NTIME enc t`
exactamente cuando alguna máquina con tiempo `O(t)` lo decide y, en cada instancia, la pertenencia se
certifica con una traza de largo `O(t)` que se verifica cinta por cinta. -/
theorem mem_NTIME_iff_trazas {α : Type} {enc : α ↪ List Bool} {A : Set α} {t : ℕ → ℕ} :
    A ∈ Cslib.Complexity.NTIME enc t ↔
      ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State),
        ∀ a, ntm.RunsInTime (enc a) (c₁ * t (enc a).length + c₂) ∧
          (a ∈ A ↔ ∃ τ : List (EntradaC k Bool State), τ.length ≤ c₁ * t (enc a).length + c₂ ∧
            ControlC ntm (some ntm.q₀) τ ∧ estadoFinal (some ntm.q₀) τ = none ∧
            EntradaOk (enc a) 1 τ ∧
            (∀ i, ConsistenteCinta ⟨fun _ => none, 0⟩ (proyeccionC i τ)) ∧
            (τ.map fun e => e.acc.output.toList).flatten = [true]) := by
  constructor
  · rintro ⟨c₁, c₂, k, State, hfin, ntm, hd⟩
    refine ⟨c₁, c₂, k, State, hfin, ntm, fun a => ⟨(hd a).1, ?_⟩⟩
    rw [(hd a).2, accepts_iff_por_cinta ntm (hd a).1]
  · rintro ⟨c₁, c₂, k, State, hfin, ntm, h⟩
    refine ⟨c₁, c₂, k, State, hfin, ntm, fun a => ⟨(h a).1, ?_⟩⟩
    rw [(h a).2, accepts_iff_por_cinta ntm (h a).1]

/-! ### Controles -/

/-- La acción que para en seguida con salida `[true]`. -/
def accionAceptar : Action 0 Bool Unit := ⟨0, fun i => i.elim0, some true, none⟩

/-- Una máquina que acepta todo en un paso. -/
def maquinaAceptaTodo : MultiTapeNTM 0 Bool Unit := ⟨(), fun _ _ _ a => a = accionAceptar⟩

/-- Una máquina sin transiciones: no acepta nada. -/
def maquinaSinTransiciones : MultiTapeNTM 0 Bool Unit := ⟨(), fun _ _ _ _ => False⟩

/-- Control: la hipótesis no es vacía. `maquinaAceptaTodo` corre en tiempo `1` y acepta con una traza de largo
exactamente `1`, que pasa las verificaciones por separado: la cota `τ.length ≤ t` se alcanza. -/
theorem control_traza_alcanza (input : List Bool) :
    maquinaAceptaTodo.RunsInTime input 1 ∧
      ∃ τ : List (EntradaC 0 Bool Unit), τ.length = 1 ∧
        ControlC maquinaAceptaTodo (some maquinaAceptaTodo.q₀) τ ∧ estadoFinal (some maquinaAceptaTodo.q₀) τ = none ∧
        EntradaOk input 1 τ ∧ (∀ i, ConsistenteCinta ⟨fun _ => none, 0⟩ (proyeccionC i τ)) ∧
        (τ.map fun e => e.acc.output.toList).flatten = [true] := by
  have ht : maquinaAceptaTodo.RunsInTime input 1 :=
    MultiTapeNTM.runsInTime_one_of_forall_step_initCfg fun c hc => by
      simp only [MultiTapeNTM.Step, MultiTapeNTM.initCfg, Cfg.init] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      subst ha
      rfl
  refine ⟨ht, [⟨(), ⟨simboloEn input 1, fun i => i.elim0⟩, accionAceptar⟩], rfl, ⟨rfl, rfl, trivial⟩, rfl,
    ⟨rfl, trivial⟩, fun i => i.elim0, rfl⟩

/-- Control: y entonces acepta, por el teorema (no por cálculo directo). -/
theorem control_maquinaAceptaTodo_acepta (input : List Bool) : maquinaAceptaTodo.Accepts input := by
  obtain ⟨ht, τ, hl, h⟩ := control_traza_alcanza input
  exact (accepts_iff_por_cinta maquinaAceptaTodo ht).mpr ⟨τ, hl.le, h⟩

/-- Control: el otro lado tampoco es vacío. Sin transiciones no hay traza que termine parada. -/
theorem control_maquinaSinTransiciones_rechaza (input : List Bool) : ¬ maquinaSinTransiciones.Accepts input := by
  rw [accepts_iff_traza]
  rintro ⟨τ, hv, hs, -⟩
  rcases τ with _ | ⟨e, es⟩
  · simp [finalC, MultiTapeNTM.initCfg, Cfg.init] at hs
  · exact hv.2.2.1

end Cslib

/-! ### Controles del modelo abstracto -/

section ControlesAbstractos

/-- Una cinta de naturales en blanco (`0`), con la cabeza en `0`. -/
def cintaCeros : Cinta ℕ := ⟨fun _ => 0, 0⟩

/-- Control del orden: escribir `1`, luego `2` en la misma celda y leer `1`. La lectura coincide con
**una** escritura anterior en la celda, pero no con la **última**, y la proyección no es consistente. -/
theorem control_orden_importa :
    ¬ ConsistenteCinta cintaCeros
      [⟨0, ⟨some 1, 0⟩⟩, ⟨1, ⟨some 2, 0⟩⟩, ⟨1, ⟨none, 0⟩⟩] := by
  simp [ConsistenteCinta, cintaCeros, Cinta.leer, Cinta.aplicar]

/-- Control del movimiento: escribir `1`, moverse a la derecha y leer `1` no es consistente (la celda nueva
está en blanco); sin moverse, sí. -/
theorem control_movimiento_importa :
    ¬ ConsistenteCinta cintaCeros [⟨0, ⟨some 1, 1⟩⟩, ⟨1, ⟨none, 0⟩⟩] ∧
      ConsistenteCinta cintaCeros [⟨0, ⟨some 1, 0⟩⟩, ⟨1, ⟨none, 0⟩⟩] := by
  simp [ConsistenteCinta, cintaCeros, Cinta.leer, Cinta.aplicar]

/-- Una máquina de una cinta sin transiciones. -/
def maquinaSinPasos : MaquinaK 1 ℕ Unit := ⟨fun _ _ _ => False⟩

/-- Control: la parte de control no se puede omitir. La traza de un paso que lee el blanco es consistente
en la única cinta, pero no es válida: la transición no existe. -/
theorem control_control_necesario :
    let τ : List (Entrada 1 ℕ Unit) := [⟨(), fun _ => 0, ⟨fun _ => ⟨none, 0⟩, none⟩⟩]
    (∀ i, ConsistenteCinta cintaCeros (proyeccion i τ)) ∧
      ¬ ValidaTraza maquinaSinPasos ⟨some (), fun _ => cintaCeros⟩ τ := by
  refine ⟨fun i => ?_, fun h => h.2.2.1⟩
  simp [proyeccion, ConsistenteCinta, cintaCeros, Cinta.leer]

/-- Control: la pasada sobre tres pasos no termina en dos. -/
theorem control_pasada_no_antes :
    (Pasada.paso^[2] (⟨cintaCeros, [⟨0, ⟨none, 0⟩⟩, ⟨0, ⟨none, 0⟩⟩, ⟨0, ⟨none, 0⟩⟩], true⟩ : Pasada ℕ)).resto
      ≠ [] := by
  intro h
  have := Pasada.resto_iterar cintaCeros [⟨0, ⟨none, 0⟩⟩, ⟨0, ⟨none, 0⟩⟩, ⟨0, ⟨none, 0⟩⟩] true 2 (by simp)
  rw [h] at this
  simp at this

end ControlesAbstractos

section ControlCintas
open Turing

/-- Acepta solo si la cinta de trabajo 0 tiene `true` bajo la cabeza (nunca, en blanco). -/
def maquinaCintaTrue : MultiTapeNTM 1 Bool Unit :=
  ⟨(), fun _ _ w a => w 0 = some true ∧ a = ⟨0, fun _ => (none, 0), some true, none⟩⟩

/-- **Control (del revisor): la consistencia de las cintas de trabajo es necesaria.** Sin ella, `accepts_iff_por_cinta`
sería falso: una máquina de una cinta que solo acepta si lee `true` en una cinta en blanco tendría una traza «aceptante». -/
theorem control_cintas_de_trabajo_necesarias : ¬ ∀ (input : List Bool),
    maquinaCintaTrue.Accepts input ↔ ∃ τ : List (EntradaC 1 Bool Unit),
      ControlC maquinaCintaTrue (some maquinaCintaTrue.q₀) τ ∧
      estadoFinal (some maquinaCintaTrue.q₀) τ = none ∧
      EntradaOk input 1 τ ∧
      (τ.map fun e => e.acc.output.toList).flatten = [true] := by
  intro h
  have hno : ¬ maquinaCintaTrue.Accepts [] := by
    rw [accepts_iff_traza]
    rintro ⟨τ, hv, hs, -⟩
    rcases τ with _ | ⟨e, es⟩
    · simp [finalC, MultiTapeNTM.initCfg, Cfg.init] at hs
    · obtain ⟨-, hl, ⟨htr, -⟩, -⟩ := hv
      rw [← hl] at htr
      simp [Cfg.workTapeSymbols, MultiTapeNTM.initCfg, Cfg.init, Cfg.headSymbols] at htr
  exact hno ((h []).mpr ⟨[⟨(), ⟨simboloEn [] 1, fun _ => some true⟩, ⟨0, fun _ => (none, 0), some true, none⟩⟩],
    ⟨rfl, ⟨rfl, rfl⟩, trivial⟩, rfl, ⟨rfl, trivial⟩, rfl⟩)

/-- Y con la condición, la traza mentirosa no pasa: la cinta de trabajo sí se ejercita. -/
example : ¬ ConsistenteCinta ⟨fun _ => none, 0⟩ (proyeccionC (0 : Fin 1)
    [(⟨(), ⟨simboloEn ([] : List Bool) 1, fun _ => some true⟩, ⟨0, fun _ => (none, 0), some true, none⟩⟩ :
      EntradaC 1 Bool Unit)]) := by
  simp [proyeccionC, ConsistenteCinta, Cinta.leer]

end ControlCintas

end Sagitta.Map.Tiempo.SimulacionLineal
