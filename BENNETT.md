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
