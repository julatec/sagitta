# Bitácora: Bennett (1973) sobre las máquinas de cslib

Rama `bennett` (desde `main` en `9eaabf1`). Meta: descargar la hipótesis `Bennett` de
`Sagitta/Arrow/TM/Instance.lean` con el plan de ocho pasos. Esta bitácora la lleva cada paso.

## Pasos 1 y 2 — 26 nov 2026 (cerrados)

Archivo: `Sagitta/Arrow/TM/Bennett/History.lean`, importado por `Sagitta.lean`. Cero `sorry`;
`#print axioms` de los seis teoremas centrales: solo `propext`, `Classical.choice`, `Quot.sound`;
un mutante por teorema (seis, con `fail_if_success`). `lake build Sagitta` pasa.

### Paso 1: las definiciones que se tocan

- `Turing.Action` (cslib, `MultiTape/Configuration.lean`): movimiento de la cabeza de entrada
  (`SignType`), por cinta de trabajo `Option (Option Symbol) × SignType` (escribir o no, mover),
  `output : Option Symbol`, `state : Option State`.
- `Turing.Cfg k Symbol State input`: estado (`none` = detenida), `inputPos : Fin (|input| + 2)`
  (desplazada en uno: 0 y |input|+1 son blancos), cintas `Fin k → ℤ → Option Symbol` (funciones
  arbitrarias, sin soporte finito), posiciones, y la **salida** (`List Symbol`). `Cfg.init` pone la
  cabeza de entrada en 1.
- `Action.apply`: mueve la entrada con **recorte** (`moveInputPos`), escribe con
  `Function.update`, suma el movimiento, y **agrega** al final de la salida
  (`output ++ a.output.toList`).
- `MultiTapeTM.tr q r w` es total (de `ofTr` o de la relación determinista); `step` =
  `(tr q (inputSymbol) (workTapeSymbols)).apply`; detenida, `step c = c`. `runFrom c t = step^[t] c`.
- `Cfg.core` (Sagitta, `TM/Dynamics.lean`) deja fuera la salida, pero **`IsReversible`**
  (`TM/Instance.lean`) es sobre la `Cfg` completa, salida incluida: inyectividad de `step` sobre
  **todas** las configuraciones no detenidas, no solo las alcanzables. Se dejó así.

**Representación elegida.** Ni cuádruplas ni una clase nueva: se trabaja directo con
`IsReversible` y un lema local, `apply_injective`: una misma acción, aplicada a dos
configuraciones en el mismo estado que leen lo mismo donde la acción escribe, y cuya cabeza de
entrada no se mueve desde un blanco, da el mismo resultado solo si eran iguales. Es la
«reversibilidad local» de Bennett en el vocabulario de cslib.

### Hallazgo: una máquina reversible no puede salirse de un blanco de la entrada

`IsReversible.staysOnBlank`: con la entrada vacía, las posiciones 0 y 1 leen blanco; dos
configuraciones que solo difieren ahí toman la misma acción, y cualquier movimiento las manda a la
misma posición. Luego toda máquina con `IsReversible` cumple `StaysOnBlank`: nunca mueve la cabeza
de entrada mientras lee un blanco. Una vez que sale de la entrada, se queda ahí.

Consecuencia para el plan: la máquina con historia **no** puede simular cualquier `M`; necesita
`StaysOnBlank M`, y `histTM_isReversible_iff` muestra que esa hipótesis es **necesaria** (con un
código inyectivo, `histTM M` es reversible si y solo si `M` cumple `StaysOnBlank`). Hace falta un
paso nuevo (abajo, 2b).

### Hallazgo: la guarda y el sumidero

Escribir el registro sobre una celda borra lo que tenía, así que la historia se escribe solo sobre
celdas en blanco. Pero `IsReversible` exige inyectividad también en las configuraciones con
basura en la historia, que ninguna corrida alcanza. Ahí la máquina no puede detenerse (perdería el
estado) ni quedarse en el lugar (la configuración puede ser imagen de un paso bueno). Va a un
**sumidero** `.inr q`: el primer paso agrega `false` a la salida, y el sumidero agrega `true` para
siempre. Agregar es inyectivo y el último símbolo dice de dónde se vino. Como el sumidero no se
alcanza desde la configuración inicial, no ensucia la salida de ninguna corrida.

### Paso 2: la máquina con historia

- `Record k State = State × Option Bool × (Fin k → Option Bool)`: lo que un paso olvida.
- `histTM tm code : MultiTapeTM (k + h) Bool (State ⊕ State)`: las `k` cintas de `tm` y `h` de
  historia; en `.inl q` con las celdas de historia en blanco, la acción de `tm` y `code (q, r, w)`
  escrito un bit por cinta de historia, cabezas a la derecha. `oneHot`: un código inyectivo con
  `h = Nat.card (Record k State)`.
- `proj`: olvida las cintas de historia (y el sumidero).

### Teoremas (rama `bennett`)

- `Sagitta.Arrow.TM.IsReversible.staysOnBlank` — reversible ⟹ no sale de un blanco.
- `Sagitta.Arrow.TM.Bennett.apply_injective` — reversibilidad local de una acción.
- `Sagitta.Arrow.TM.Bennett.histTM_simulates` — tras `t` pasos, `proj` de `histTM` = `tm` tras `t`
  pasos (sin hipótesis). Más `histTM_halted_iff` y `runFrom_clean` (desde cualquier configuración
  limpia).
- `Sagitta.Arrow.TM.Bennett.histTM_isReversible` — `StaysOnBlank tm` y código inyectivo ⟹
  `IsReversible (histTM tm code)`.
- `Sagitta.Arrow.TM.Bennett.histTM_isReversible_iff` — y la hipótesis es necesaria.
- `Sagitta.Arrow.TM.Bennett.history` — empaquetado: para `Finite State` y `StaysOnBlank tm`, existe
  una máquina reversible con estados finitos que proyecta a `tm` paso a paso.

### Siguiente

- **2b (nuevo).** Forma normal de la entrada: toda `M` tiene una `M'` con `StaysOnBlank` que la
  simula (copiar la entrada de izquierda a derecha a una cinta de trabajo hasta leer el blanco,
  volver la cabeza de trabajo, y simular `M` leyendo la copia), con la copia hecha de forma
  reversible o con su propia historia. Sin esto el paso 2 no aplica a la `M` de
  `ComputableInPolyTime`.
- **3.** La copia de la salida a una cinta limpia. Ojo: la salida de cslib es solo de escritura y
  `ComputesFunInTimeAndSpace` la mira; la máquina con historia escribe en ella lo que `M` escribe,
  así que la etapa de deshacer no puede «desescribir» la salida. Hay que decidir si `M₁` simula la
  salida de `M` en una cinta de trabajo (y la salida real se escribe solo en la copia).
- Luego 4 (la inversa), 5 (componer), 6–7.

## Paso 3 — 26 nov 2026 (cerrado)

Archivo: `Sagitta/Arrow/TM/Bennett/Copy.lean`, importado por `Sagitta.lean`. Cero `sorry`;
`#print axioms` de los cinco teoremas centrales: solo `propext`, `Classical.choice`, `Quot.sound`;
un mutante por teorema (cinco, con `fail_if_success`). `lake build Sagitta` pasa.

### La máquina de copia

`copyTM src dst : MultiTapeTM k Bool CopyState` (dos estados, `fwd` y `back`; `Finite`):

- **Ida** (`fwd`): mientras `src` lee un símbolo `b`, aplica a la celda de `dst` el
  **intercambio** del blanco con `b` (`Equiv.swap none (some b)`, la versión de tres valores del
  XOR de Bennett) y mueve las dos cabezas a la derecha. Sobre un destino limpio el intercambio
  escribe `b`; sobre cualquier otra celda sigue siendo una biyección, así que no se olvida nada y
  **no hace falta guarda ni sumidero** (a diferencia de la máquina con historia). Al leer el blanco
  del final, retrocede uno y pasa a `back`.
- **Vuelta** (`back`): mientras `src` lee un símbolo, retrocede las dos cabezas. Al leer el blanco
  de antes de la palabra, avanza uno y se detiene. Las cabezas quedan donde empezaron, que es lo
  que necesita la inversa del paso 4 (`M₁⁻¹` arranca con las cabezas de `M₁` en su lugar).
- La cabeza de entrada nunca se mueve (cumple `StaysOnBlank` trivialmente); `src` nunca se escribe.

**Por qué es reversible.** El sucesor dice el estado y la dirección; la celda de `src` que se dejó
atrás (no se escribe) dice el símbolo leído, y con él el intercambio de `dst` se deshace. El cruce
«ida que lee blanco» contra «vuelta que lee símbolo» (las dos van a `back` retrocediendo) lo separa
la misma celda de `src`.

### La salida de cslib

La salida de cslib es solo de agregar y `ComputesFunInTimeAndSpace` la lee. Se resolvió la duda del
paso 2: en Bennett, `M₁` tiene que dejar la salida simulada de `M` en una **cinta de trabajo**, y
la copia es lo único que toca la salida real. Por eso hay una segunda máquina, `emitTM src`: la
misma, con la cinta de salida como destino (la cinta limpia es la salida vacía de la configuración
inicial). Agregar es inyectivo, así que tampoco necesita guarda.

### Teoremas (rama `bennett`)

- `Sagitta.Arrow.TM.Bennett.copyTM_isReversible` — `src ≠ dst` ⟹ `IsReversible (copyTM src dst)`,
  en todas las configuraciones en marcha, no solo las alcanzables.
- `Sagitta.Arrow.TM.Bennett.copyTM_self_not_isReversible` — y la hipótesis es necesaria:
  `¬IsReversible (copyTM i i)`.
- `Sagitta.Arrow.TM.Bennett.copyTM_correct` — con `w` en `src` desde la cabeza, blanco antes y
  después, y `|w|` celdas en blanco en `dst` desde la cabeza: tras `2|w| + 2` pasos la máquina está
  detenida, `dst` tiene `w` desde su cabeza (`copyTape`) y todo lo demás (cabezas, `src`, otras
  cintas, entrada, salida) quedó igual. Igualdad de configuraciones completa.
- `Sagitta.Arrow.TM.Bennett.emitTM_isReversible` — sin hipótesis.
- `Sagitta.Arrow.TM.Bennett.emitTM_correct` — lo mismo con la salida: tras `2|w| + 2` pasos,
  `output = output ++ w` y nada más cambió.
- Auxiliares: `copy_fwd`, `copy_back`, `emit_fwd`, `emit_back` (las dos fases),
  `workTapePos_eq_of_apply`, `workTapes_eq_of_apply`, `copyTape_step`.

### Lo que no está

- No se probó que la máquina siga en marcha antes del paso `2|w| + 2` (no hace falta para
  `RunsInTime`, que solo pide estar detenida a tiempo).
- Espacio: la copia usa las celdas `p - 1 … p + |w|` de `src` y `d … d + |w| - 1` de `dst`; no se
  enunció como cota.
- Las máquinas están sobre `k` cintas con `src`/`dst` como índices; empalmarlas con `histTM` (que
  usa `Fin (k + h)`) es trabajo del paso 5.

### Siguiente

- **2b.** Sigue pendiente: la forma normal de la entrada (`StaysOnBlank`) para cualquier `M`.
- **2c (nuevo, sale de este paso).** Que `M₁` escriba la salida de `M` en una cinta de trabajo,
  con blanco antes y después y la cabeza al principio al terminar, para que `emitTM` la copie. O
  bien: una variante de `histTM` que redirija `Action.output` a una cinta de trabajo (el registro
  ya guarda lo leído; escribir y avanzar en una cinta limpia es otra escritura sobre blanco).
- **4.** La inversa: de `IsReversible` (inyectividad de `step`) a una máquina que deshace los
  pasos. `copyTM` es casi su propia inversa (el intercambio es involutivo), que sirve de caso de
  prueba.
- Luego 5 (componer `M₁`, `emitTM`, `M₁⁻¹`), 6–7.

## Paso 4 — 26 nov 2026 (cerrado, solo para M₁)

Archivos: `Sagitta/Arrow/TM/Bennett/Inverse.lean` y `Sagitta/Arrow/TM/Bennett/Uncompute.lean`,
importados por `Sagitta.lean`. Cero `sorry`; `#print axioms` de los trece teoremas centrales: solo
`propext`, `Classical.choice`, `Quot.sound`; un mutante por teorema (trece, con
`fail_if_success`). `lake build Sagitta` pasa.

### Por qué no el lema general

Se probó solo para `M₁ = histTM` (lo que permitía el pedido). En cslib una acción **escribe bajo
las cabezas y después las mueve**: para deshacerla hay que mover primero y reescribir después, así
que un paso cuesta al menos dos de la inversa, y para saber qué reescribir hace falta lo que el paso
leyó, que `IsReversible` (inyectividad global de `step`) determina solo de forma global. Pasar de
eso a una tabla finita de transiciones locales es la forma de cuádruplas de Bennett, una
construcción aparte. En `histTM` el registro de la cinta de historia *es* esa información local.

### Dos inversas

- **`invTM`** (`Inverse.lean`), la simple: `rewind` (mover las cabezas de historia al último
  registro), `read` (leer el registro `(q, r, w)` con `decode`, borrarlo, retroceder cada cabeza lo
  que avanzó la acción `tm.tr q r w`), `restore` (reescribir `w`). `t` pasos se deshacen en
  `2t + 2`. Correcta (`invTM_correct`) con `StaysOnBlank tm`, pero **no es reversible**: olvida el
  estado de la máquina directa, y dos registros distintos pueden dar la misma configuración.
- **`uncTM`** (`Uncompute.lean`), la reversible, la que necesita el paso 5: el estado `back q`
  lleva el estado `q` de la máquina directa (`none` si se detuvo), así que borrar el registro no
  pierde nada. `peek q` revisa que el registro lleve a `q`; `restore` revisa que la entrada lea `r`
  y cada cabeza lo que el paso dejó (`expected`). Lo que no cuadra va a un **sumidero** `.inr s`
  (agrega `false` una vez y `true` siempre), como en `histTM`. Se detiene solo al no encontrar
  registro estando en el estado inicial. `t` pasos se deshacen en `3t + 2`.

### Hallazgo: la inversa reversible no puede mover la cabeza de entrada

La inversa de un paso que mete la cabeza de entrada en el blanco del final la **saca** de un
blanco, y una máquina reversible nunca hace eso (`IsReversible.staysOnBlank`, paso 1). Así que
`uncTM` nunca mueve la cabeza de entrada, y su corrección pide `InputFixed tm` (`tm` nunca la
mueve), más fuerte que `StaysOnBlank`. Consecuencia para 2b: la forma normal no es solo «no salir
de un blanco» sino **copiar la entrada a una cinta de trabajo y simular sobre la copia**, y esa
copia (que deja la cabeza de entrada en el blanco final) **no se deshace**: queda como parte de la
configuración final de la máquina de Bennett.

### La salida

La salida de cslib solo crece; ninguna inversa la deshace. `invTM` y `uncTM` no la tocan y la dejan
como la dejó la corrida directa (los teoremas la llevan como `out`). Confirma 2c: `M₁` debe dejar la
salida simulada en una cinta de trabajo.

### Teoremas (rama `bennett`)

`Inverse.lean`:
- `Sagitta.Arrow.TM.Bennett.moveInputPos_neg` — mover y deshacer el movimiento devuelve la cabeza,
  salvo recorte (desde el interior no hay).
- `Sagitta.Arrow.TM.Bennett.invTM_back` — dos pasos de la inversa deshacen un paso limpio.
- `Sagitta.Arrow.TM.Bennett.invTM_runBack` — `2t` pasos deshacen `t`.
- `Sagitta.Arrow.TM.Bennett.invTM_correct` — desde la configuración tras `t` pasos (en `rewind`),
  `2t + 2` pasos llevan a la inicial, detenida, salida intacta (`atRest`).
- `Sagitta.Arrow.TM.Bennett.invTM_correct_of_tm`, `Sagitta.Arrow.TM.Bennett.inverse` (con
  `oneHot`; `oneHot_pos`).

`Uncompute.lean`:
- `Sagitta.Arrow.TM.Bennett.uncTM_isReversible` — `IsReversible (uncTM tm code)`, **sin
  hipótesis** (ni sobre `tm` ni sobre `code`).
- `Sagitta.Arrow.TM.Bennett.uncTM_back` — tres pasos deshacen un paso limpio (de `mirror` a
  `mirror`).
- `Sagitta.Arrow.TM.Bennett.uncTM_finish` — los dos últimos: sin registro en el estado inicial, se
  detiene.
- `Sagitta.Arrow.TM.Bennett.uncTM_runBack` — `3t` pasos deshacen `t`.
- `Sagitta.Arrow.TM.Bennett.uncTM_correct` — `3t + 2` pasos de `mirror (corrida t)` a la
  inicial detenida (`halted`), con `InputFixed tm`, código inyectivo y `0 < h`.
- `Sagitta.Arrow.TM.Bennett.uncTM_correct_of_tm` — la hipótesis sobre `tm`.
- `Sagitta.Arrow.TM.Bennett.uncompute` — empaquetado con `oneHot`: reversible y correcta.
- Auxiliares: `decode_code`, `decode_blank`, `decode_some`, `histTM_step_good`,
  `inputSymbol_congr`, `InputFixed.staysOnBlank`.

### Lo que no está

- El lema general (arriba).
- Que la inversa siga en marcha antes del último paso (no hace falta para `RunsInTime`).
- `mirror` usa el estado de la máquina directa; empalmar el final de `M₁` (detenida, estado
  `none` → `back none`) con el comienzo de `uncTM` y la copia en una sola máquina es el paso 5.

### Siguiente

- **2b, revisado.** Forma normal con `InputFixed`: copiar la entrada a una cinta de trabajo
  (reversible, como `copyTM` pero leyendo la cinta de entrada) y simular `M` sobre la copia sin
  mover la cabeza de entrada.
- **2c.** `M₁` con la salida de `M` en una cinta de trabajo.
- **5.** Componer `histTM` → `copyTM`/`emitTM` → `uncTM` en una máquina reversible: el empalme
  de estados (los finales de una fase son los iniciales de la siguiente) tiene que conservar la
  inyectividad; mirar antes el PR de composición TM2 de Mathlib (#44441). Ojo: `copyTM` deja la
  cabeza donde empezó, y `uncTM` espera las cabezas de `histTM` donde las dejó la corrida.

## Pasos 5 y 6 — 26 nov 2026 (cerrados, con las hipótesis de 2b y 2c como hipótesis)

Archivos: `Sagitta/Arrow/TM/Bennett/Compose.lean` (paso 5) y `Sagitta/Arrow/TM/Bennett/Machine.lean`
(paso 6), importados por `Sagitta.lean`. Cero `sorry`; `#print axioms` de los dieciséis teoremas
centrales: solo `propext`, `Classical.choice`, `Quot.sound`; un mutante por teorema (dieciséis, con
`fail_if_success`). `lake build Sagitta` pasa. No se vendorizó nada nuevo: `Turing.MultiTapeTM.seq`
(`Cslib/.../Plumbing/Sequential.lean`, con `combine` y `handOver` de `Deterministic.lean`) ya estaba
en la clausura vendorizada.

### Qué había hecho

- **cslib ya tiene la composición secuencial**: `MultiTapeTM.seq` redirige el paso de detención de la
  primera máquina al estado inicial de la segunda, sin paso extra. Se usa **sin modificar**. Sus
  teoremas (`exists_runPath_seq`, `transformsTapes_seq`) hablan de corridas, tiempo y espacio, nunca
  de inyectividad; la nota de la bitácora sobre `Sequential`/`ClearWork` se confirma: no la preservan
  por sí solas.
- **El PR #44441 de Mathlib no sirve aquí**: es `TM2ComputableInPolyTime.comp` sobre el modelo TM2
  de pilas de Mathlib (abierto, bloqueado por #44440), no sobre `MultiTapeTM` de cslib, y no dice
  nada de reversibilidad ni inyectividad (leído en GitHub el 26 nov 2026).

### Paso 5: cuándo `seq` conserva la reversibilidad

Dentro de cada máquina la compuesta da el mismo paso con los estados reetiquetados de forma
inyectiva; la inyectividad solo puede romperse en la **entrega**: un paso de detención de `tm₀`
(redirigido a `tm₁.q₀`) contra un paso de `tm₁` que **entra** a `tm₁.q₀`.

- `HandOff tm₀ tm₁`: ninguna configuración de entrega es también imagen de un paso en marcha de
  `tm₁`. `seq_isReversible`: `tm₀`, `tm₁` reversibles y `HandOff` ⟹ `seq` reversible.
  `seq_not_isReversible`: la hipótesis es necesaria (un choque da dos configuraciones en marcha con
  el mismo sucesor).
- `NoReentry tm₁` (ninguna transición entra al estado inicial) implica `HandOff`
  (`HandOff.of_noReentry`). `uncTM_noReentry`: la inversa lo cumple (nada vuelve a `back none`).
- **Hallazgo: la emisión vuelve a entrar a su estado inicial** (`emitTM_not_noReentry`: `fwd → fwd`),
  y ningún envoltorio genérico lo arregla: un estado previo que no hace nada choca con los pasos de
  `tm₁` hacia `q₀` en configuraciones basura, porque `IsReversible` mira todas. La salida es local,
  como la de Bennett: una **compuerta** `gateTM src` (tres estados: `start` mueve la cabeza de `src`
  a la izquierda; `check` exige blanco y vuelve, si no va a un sumidero que agrega `false` y luego
  `true`). Tras la compuerta, la celda a la izquierda de la cabeza de `src` es blanca; tras un paso
  `fwd` de la emisión, tiene el símbolo emitido: `gate_emit_handOff`. `gateTM_isReversible`,
  `gateTM_run` (2 pasos, nada cambia), `gate_emit_noReentry`.
- Corridas: `seq_runFrom_left`, `seq_runFrom_right`, `seq_runFrom` (exacta, con la primera detención
  en `t₀`) y `seq_runFrom_of_le` (con cotas: si `tm₀` se detuvo para `t₀` y `tm₁` para `t₁`, la
  compuesta se detuvo para `t₀ + t₁`; usa la primera detención con `Nat.find`, así que no hace falta
  saber que la emisión sigue en marcha antes de su último paso).

### Paso 6: la máquina de Bennett

`bennettTM tm code src := ((histTM tm code).seq (emitStage (mainTape h src))).seq (uncTM tm code)`,
con `emitStage src := (gateTM src).seq (emitTM src)`; estados finitos si los de `tm` lo son.

- `bennettTM_isReversible`: `StaysOnBlank tm` y código inyectivo ⟹ reversible.
- `bennettTM_correct`: si `tm` nunca mueve la cabeza de entrada (`InputFixed`), se detiene en el paso
  `t` (en marcha antes) y deja `w` en su cinta de trabajo `src` desde la cabeza, con blanco antes y
  después, entonces para todo `T ≥ 4 t + 2 |w| + 6` la máquina de Bennett está en
  `⟨none, 1, todo en blanco, cabezas en 0, salida de tm ++ w⟩`: **cintas auxiliares limpias**, la
  de historia incluida. El tiempo es el `4n + 4l + 5` de Bennett con la copia de un solo sentido:
  `t` (historia) + 2 (compuerta) + `2|w| + 2` (emisión) + `3t + 2` (deshacer).
- `runsInSpace_of_halted`: toda máquina que se detiene para `T` corre en espacio `k (2T + 1)`
  (una cabeza avanza una celda por paso).
- `bennettTM_computesInTimeAndSpace`: lo mismo en el vocabulario de cslib,
  `ComputesInTimeAndSpace input (salida ++ w) T ((k + h)(2T + 1))` con `T = 4t + 2|w| + 6`:
  **tiempo O(T) y espacio O(T)**.
- Auxiliar: `emitStage_run`, `natAbs_workTapePos_runFrom_le`, `seq_tr_inl`, `seq_tr_inr`,
  `seq_step_left`, `seq_step_right`, `apply_relabel`, `mapState_injective`.

### Lo que no está (el bloqueo para el paso 7)

La hipótesis `Bennett` habla de **cualquier** `M` con `ComputableInPolyTime`, y el teorema pide dos
cosas que una `M` cualquiera no cumple:

- **2b**: `InputFixed M`. Hace falta la forma normal: copiar la entrada a una cinta de trabajo y
  simular `M` sobre la copia. Esa copia mueve la cabeza de entrada y no se deshace (paso 4): queda
  al final, y la configuración final de Bennett tendrá la cabeza de entrada en el blanco del final y
  la copia de la entrada en una cinta (o hay que borrarla con otra copia reversible, el `XOR`).
- **2c**: que `M` deje `w = encOut (f a)` en una cinta de trabajo, con salida vacía y blanco antes
  y después, en vez de en la cinta de salida. Una variante de `histTM` que redirija
  `Action.output` a una cinta de trabajo (escribir y avanzar sobre blanco) lo resuelve; la
  condición de blanco a la izquierda la da la cinta limpia.
- Además, `ComputesFunInTimeAndSpace` pide la salida **exacta** `encOut (f a)`: con 2c la salida de
  `M` simulada es vacía y la de Bennett es `w`. Las cotas polinomiales salen de
  `4t + 2|w| + 6` con `|w| ≤ t` (lo escribe `M` en `t` pasos; no se probó).

### Siguiente

- **2c** primero (es local a `histTM`), después **2b** (la forma normal de la entrada), y con eso
  el **paso 7**: probar `Bennett` de `Sagitta/Arrow/TM/Instance.lean`.

## Paso 7 — 26 nov 2026 (cerrado): `Bennett` es un teorema

Archivos: `Sagitta/Arrow/TM/Bennett/Prepare.lean` (2b, la parte reversible),
`Sagitta/Arrow/TM/Bennett/Normal.lean` (2b y 2c, la forma normal) y
`Sagitta/Arrow/TM/Bennett/Discharge.lean` (el paso 7), importados por `Sagitta.lean`. Cero `sorry`;
`#print axioms` de los diecinueve teoremas centrales bajo `#guard_msgs`: solo `propext`,
`Classical.choice`, `Quot.sound`; un mutante por teorema (diecinueve, con `fail_if_success`).
`lake build` completo pasa (6947 trabajos, 5 min 50 s con `LEAN_NUM_THREADS=3`). No se vendorizó
nada nuevo: `inputFromTape`, `outputToTape`, `rewindWork`, `extendTapes`/`tapeEmb` (cslib),
`length_output_runFrom_le` y el cierre de `PolynomiallyBounded` (cslib-frontier) ya estaban en la
clausura vendorizada, y se usan sin modificar.

### 2c y 2b sin escribir máquinas nuevas de simulación

cslib ya tenía las dos redirecciones, con sus homomorfismos de pasos:

- `outputToTape tm`: lo que `tm` manda a la salida va a una cinta de trabajo nueva (`outTape`), con
  la cabeza en la frontera; `outCfgHom`.
- `inputFromTape tm`: lee la entrada de una **cinta de entrada virtual** (la palabra desde la celda
  0) con una **cinta bandera** que marca la celda −1, con el recorte de la cabeza de entrada
  resuelto por la bandera (`clampMove`), y nunca toca la cabeza de entrada real; `inCfgHom`.

La forma normal es `normTM tm := nopTM.seq (tm.outputToTape.inputFromTape.seq rewindOut)`:

- `rewindOut` = `rewindWork` de cslib puesto en `outTape` con `extendTapes (tapeEmb _)`: deja la
  palabra desde la cabeza, como la pide la emisión del paso 6.
- `nopTM` (un paso que no hace nada) para que **nada vuelva a entrar al estado inicial**
  (`normTM_noReentry`), que es lo que hace distinguible la entrega desde la máquina que prepara
  (`seq_noReentry`, `histTM_noReentry`, `bennettTM_noReentry'`).
- `normTM_inputFixed` y `normTM_inputBlind`: nunca mueve ni lee la cabeza de entrada, así que corre
  igual esté donde esté (`runFrom_setInputPos`).
- `normTM_run`: desde las cintas preparadas (`prepTapes`), con la cabeza de entrada en cualquier
  lado, si `tm` se detuvo para `t` con salida `y`, la forma normal se detuvo para `1 + t + |y| + 2`
  con `y` en `outTape` desde la celda 0, la cabeza en 0 y la salida real vacía.

### Lo que faltaba: preparar la entrada virtual de forma reversible

`prepTM vip flag` (cuatro estados): `fwd` intercambia la celda de `vip` con el símbolo leído (el
XOR de Bennett) y avanza la entrada; en el blanco final exige `vip` en blanco (si no, sumidero) y
retrocede; `back` vuelve sobre la palabra; `mark` intercambia la celda −1 de `flag` con `true` y se
detiene. La cabeza de entrada **queda en el blanco final** y ahí se queda: ninguna máquina
reversible la puede sacar de ahí (`IsReversible.staysOnBlank`), y la forma normal no la necesita.

- `prepTM_isReversible`: `vip ≠ flag` ⟹ reversible en toda configuración en marcha. La entrada al
  bucle `back` se distingue de su iteración por la celda de `vip` (blanco contra símbolo), que
  ninguno de los dos escribe; por eso `fwd` es el estado inicial (nadie entra a él salvo él mismo,
  y su iteración se reconoce por la cabeza de entrada).
- `prepTM_correct`: en `2 |x| + 3` pasos, `x` en `vip` (`tapeOfList x`), la marca en `flag`, las
  cabezas en 0, la entrada en el blanco final, nada más cambió.

### El paso 7

- `bennettTM_correct_from`: el teorema del paso 6 desde **cualquier configuración limpia** con las
  cintas de historia en blanco, no solo la inicial (la misma prueba, con `runFrom_clean` y
  `uncTM_runBack` desde `c₀`).
- `revTM M := (prepTM vip flag).seq (bennettTM (normTM M) oneHot outTape)`, estados finitos.
- `revTM_isReversible`: sin hipótesis.
- `revTM_correct`: si `M` se detuvo para `t` con salida `y`, `revTM M` se detuvo con salida
  **exactamente** `y` para `2 |x| + 3 + 4 (1 + t + |y| + 2) + 2 |y| + 6`. La salida exacta sale de que
  la forma normal no escribe en la salida real.
- `Sagitta.Arrow.TM.bennett_holds : Bennett`. Tiempo `T(n) = 2 n + 10 t(n) + 21` (con
  `|y| ≤ t`, `length_output_runFrom_le`), espacio `(k + 3 + h)(2 T(n) + 1)`; los dos polinomiales
  por el cierre de cslib-frontier.
- `reversible_verifier_holds` y `decision_bennett_holds`: las versiones sin `hB`. Las viejas
  (`reversible_verifier`, `decision_bennett`) se conservan. La definición `Bennett` se conserva en
  `Instance.lean` (su docstring dice dónde se prueba).
- README: `Bennett` deja de ser hipótesis; las únicas hipótesis con nombre son HD (≡ flecha) y
  `Law22`.

### Teoremas (rama `bennett`)

`Prepare.lean`: `prepTM_isReversible`, `prepTM_correct` (auxiliares `prep_mark_inj`,
`prep_fwd_inj`, `prep_fwd`, `prep_back`).

`Normal.lean`: `step_setInputPos`, `runFrom_setInputPos`, `seq_noReentry`, `histTM_noReentry`,
`normTM_inputFixed`, `normTM_inputBlind`, `normTM_noReentry`, `inCfg_outCfg_initCfg`,
`redirTM_run`, `normTM_run`.

`Discharge.lean`: `bennettTM_correct_from`, `bennettTM_noReentry'`, `revTM_isReversible`,
`revTM_correct`, `Sagitta.Arrow.TM.halted_of_runsInTime`, **`Sagitta.Arrow.TM.bennett_holds`**,
`Sagitta.Arrow.TM.reversible_verifier_holds`, `Sagitta.Arrow.TM.decision_bennett_holds`.

### Lo que no está

- Cotas más finas: el espacio sale de «una cabeza avanza una celda por paso» (`O(T)`), no de las
  `h` cintas de historia sobre `t` celdas; `h` es el tamaño del código one-hot (enorme, pero
  constante). El `4n + 4l + 5` exacto de Bennett no se enunció (era opcional).
- El lema general de la inversa para cualquier máquina reversible en forma de cuádruplas (paso 4):
  no hizo falta.

### Bloqueo

Ninguno.

### Siguiente

- **Fusionar `bennett` a `main`: lo decide José.** La rama está lista (build completo verde, cero
  `sorry`, axiomas estándar), sin fusionar y sin remote.
- **8 (si sale, otro proyecto).** Bennett 1989: usar `bennettMoves` de los guijarros reversibles de
  cslib-frontier para elegir qué configuraciones guardar (espacio `O(S log T)`), el puente entre los
  guijarros y las máquinas.
