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
