import Sagitta.Map.LeyTresMemorias
import Sagitta.Map.UniversoCerrado

/-!
# El plano de costos

La idea es de José (24 nov 2026). Pasar de los reales a los complejos: agregar una dimensión cierra el sistema. Aquí
la dimensión que se agrega a la cuenta del tiempo es la descripción.

## El plano, la región, la frontera y la recta

* **El plano de costos** tiene dos ejes (`Punto = ℕ × ℕ`, con el orden producto):
  * el **eje de la memoria** `x`: descripción del resolvedor más cita, `L + s` bits;
  * el **eje del tiempo** `y`: el tiempo de ejecución en bits, `⌈log₂(t+1)⌉`.
* **La región** (`Region O`): los puntos que se alcanzan con el verificador `O`, en el modelo de caja negra de
  `LeyTresMemorias` (`ArbolV`, `Resuelve`). `(x, y)` se alcanza (`Alcanzable`) si hay un resolvedor con `|P| ≤ 2^L`,
  `|C| ≤ 2^s`, que resuelve en `t` consultas, con `L + s ≤ x` y `⌈log₂(t+1)⌉ ≤ y`. Es **cerrada hacia arriba**
  (`region_cerrada_arriba`).
* **La frontera** (`Frontera O`): los puntos minimales de Pareto de la región.
* **La recta.** Con el verificador de sí o no sobre `N = 2^m` candidatos (`siNo m`):
  * toda la región cumple `x + y ≥ m` (`region_sobre_recta`, de `ley_si_no`);
  * todo punto entero `(m − k, k)` de la recta se alcanza (`punto_en_recta`), con la **mezcla exacta**: cita de
    `m − k` bits y `2^k − 1` consultas (`mezclaExacta`; el último candidato se devuelve sin preguntar, como en
    `fuerza_bruta`);
  * así que la región **es** el semiplano `x + y ≥ m` (`region_es_semiplano`) y la frontera **es** la recta
    `x + y = m` (`frontera_es_recta`).
  * **El redondeo, exacto**: con el tiempo medido como `⌈log₂(t+1)⌉` no hay ninguno. La mezcla de `LeyTresMemorias`
    tal cual (`mezcla`, `t = 2^k`) da `⌈log₂(2^k + 1)⌉ = k + 1` (`clog_mezcla`) y queda a distancia `1`, en
    `(m − k, k + 1)` (`mezcla_a_distancia_uno`). El `+1` de `t + 1` es la consulta que sobra si se pregunta también
    por el último candidato. En el tiempo lineal la recta exacta dice `t + 1 ≥ 2^(m − x)`.
  * La región se transporta por biyecciones de las instancias (`alcanza_equiv`, con `mapear`): solo importa `N`.
* **El verificador gira la recta** (`recta_girada`): con un verificador de `b` bits, en el plano (memoria, tiempo lineal
  `t`), `⌈log₂ N⌉ ≤ x + b·t` (es `ley_log`). Los bloques con cita la alcanzan con igualdad en todos sus puntos
  `(b·j, k)` (`bloques_en_recta_girada`): pasar un bloque del tiempo a la cita cuesta exactamente `b` bits. *Lectura*:
  el verificador fija la tasa de cambio entre los ejes, como la regla `i² = −1` ata las dos componentes de un complejo.
  Eso es analogía, no teorema.
* **La proyección de Levin** (modelo de rondas de `UniversoCerrado` y `Levin`). Un proceso cerrado `(i, k)` es el punto
  `(i, ⌈log₂ k⌉)` (`puntoProceso`). La búsqueda universal produce el punto `(código de L, i + ⌈log₂ k⌉ + 3)`: su memoria
  es una constante que solo depende del verificador (`levin_punto_constante`, con `levin_es_programa`) y su tiempo en
  bits es la proyección diagonal de pendiente `−1` (`proyDiagonal`) más `3` (`proyeccion_levin`, de `levin_en_bits`,
  que sale de `costoLevin_le`). Contra todos los procesos a la vez, `log₂ costoLevin < kt + 3`, con `kt` el mínimo de
  `x + y` (`levin_bajo_la_frontera`). *Lectura*: la búsqueda universal mueve la memoria del resolvedor al tiempo con
  tasa 1 en logaritmos; por eso cualquier punto de la frontera se lleva al eje del tiempo pagando su memoria.
* **Blum no toca el eje del tiempo.** Con la `f` de `BlumExiste.blum` (la de `existe_irracional`), los programas de `f`
  son puntos (código, costo):
  * para todo programa `i` y toda cota `M` hay un programa `j` con `costo j ∈ o(costo i)` (más rápido en casi toda
    entrada, por todo factor) y código mayor que `M` (`mas_rapido_y_mas_largo`);
  * las descripciones no están acotadas (`descripciones_no_acotadas`) y no hay programa óptimo (`sin_optimo`);
  * **sin esquina**, el enunciado preciso (`sin_esquina`): no hay ninguna cota `M` tal que los programas de código
    `≤ M` alcancen, salvo constante, a todo programa de `f`. Ni un conjunto finito de descripciones llega a la
    frontera del tiempo. Todo junto: `blum_en_el_plano`. Control: la constante `0` sí tiene esquina
    (`cero_tiene_esquina`).

## La lectura de José

Los complejos cierran los reales agregando una dimensión: `x² + 1 = 0` no tiene solución en la recta y sí en el plano.
Aquí la descripción cierra la cuenta del tiempo: medido solo en tiempo, un problema puede no tener costo (Blum: no hay
mínimo); medido en el plano, con la descripción como segunda coordenada, la frontera existe y es una recta (con
verificador), y Levin la proyecta sobre el eje del tiempo con pendiente `−1`. Lo que en una dimensión parecía
complejidad que se escapa, en dos es memoria que se paga.

## Controles y mutantes

* Controles: la región no es vacía (`region_no_vacia`), los puntos de la recta se alcanzan (`punto_en_recta`) y uno
  debajo no (`debajo_no`, y el ejemplo `(1, 1)` con `m = 3`).
* Mutantes refutados aquí: la recta con `m + 1` (`mutante_recta_mas_uno`), la región sin cerrar hacia arriba
  (`mutante_no_cerrada`), la recta lineal sin girar (`mutante_sin_girar`), la frontera de Blum con descripción acotada
  (`mutante_blum_acotada`). Levin sin el `+3` **no** se refuta: solo el paso aritmético (`mutante_bits_sin_tres`).

## Lo que NO se prueba

* **Que los complejos sean más que una analogía de estructura.** Los costos no forman un cuerpo: no hay inversos, ni
  producto que rote, ni conjugación. Lo que se comparte es la forma: agregar una coordenada cierra algo que en una no
  cerraba.
* **Que agregar dimensiones algebraicas ayude contra las barreras.** La aritmetización (extender a un cuerpo, a
  polinomios de bajo grado) choca con la barrera de algebrización (Aaronson y Wigderson, 2008; de memoria, sin
  verificar aquí). La dimensión de este plano es la **descripción**, no un cuerpo, y tampoco esquiva esa barrera: no se
  afirma nada al respecto.
* **Que las medidas sean tiempo de máquina.** El tiempo del plano es número de consultas a una caja negra (`pasos` de
  `ArbolV`); el de Levin es el costo por rondas del presupuesto de `evaln`; el de Blum es `pasos` de
  `AceleracionBlum`, una medida de Blum. Ninguna es tiempo de una máquina de Turing, y las tres son distintas entre sí.
* **La caja negra relativiza**: el verificador es un oráculo que se evalúa gratis. Todo vale igual relativo a cualquier
  oráculo (Baker, Gill y Solovay, 1975), así que no puede separar ni colapsar clases.
* **Nada sobre P contra NP.** En qué punto de la frontera cae SAT sigue abierto.
-/

namespace Sagitta.Map.Tiempo.PlanoCostos

open Sagitta.Map.Tiempo.LeyTresMemorias
open Sagitta.Map.Tiempo.LeyTresMemorias.ArbolV

/-! ## 1. El plano y la región -/

/-- **Un punto del plano de costos**: `(x, y)`, con `x` en el eje de la memoria (bits de programa más bits de cita)
y `y` en el eje del tiempo (`⌈log₂(t+1)⌉`, el tiempo en bits). El orden es el producto: `p ≤ q` si `q` tiene a la vez
más memoria y más tiempo. -/
abbrev Punto := ℕ × ℕ

/-- **El punto `(x, y)` se alcanza** con el verificador `O`: hay un resolvedor `A : P → C → ArbolV Q R Y` con
`|P| ≤ 2^L`, `|C| ≤ 2^s`, que resuelve en `t` consultas (`Resuelve`, de `LeyTresMemorias`), con `L + s ≤ x` y
`⌈log₂(t+1)⌉ ≤ y`. -/
def Alcanzable {Q R Y : Type} (O : Y → Q → R) (x y : ℕ) : Prop :=
  ∃ (P C : Type) (_ : Fintype P) (_ : Fintype C) (A : P → C → ArbolV Q R Y) (L s t : ℕ),
    Fintype.card P ≤ 2 ^ L ∧ Fintype.card C ≤ 2 ^ s ∧ Resuelve O A t ∧ L + s ≤ x ∧ Nat.clog 2 (t + 1) ≤ y

/-- **La región**: los puntos que se alcanzan. -/
def Region {Q R Y : Type} (O : Y → Q → R) : Set Punto := {p | Alcanzable O p.1 p.2}

/-- **La frontera**: los puntos minimales de Pareto de la región. Un punto de la región está en la frontera si ningún
otro punto de la región tiene a la vez menos (o igual) memoria y menos (o igual) tiempo. -/
def Frontera {Q R Y : Type} (O : Y → Q → R) : Set Punto :=
  {p | p ∈ Region O ∧ ∀ q ∈ Region O, q ≤ p → q = p}

/-- **La región es cerrada hacia arriba**: si se alcanza `p`, se alcanza todo punto con más memoria y más tiempo. Las
cotas `L + s ≤ x` y `⌈log₂(t+1)⌉ ≤ y` son desigualdades: sobrar no cuesta. -/
theorem region_cerrada_arriba {Q R Y : Type} (O : Y → Q → R) {p q : Punto} (hp : p ∈ Region O) (hpq : p ≤ q) :
    q ∈ Region O := by
  obtain ⟨P, C, iP, iC, A, L, s, t, hP, hC, hA, hx, hy⟩ := hp
  exact ⟨P, C, iP, iC, A, L, s, t, hP, hC, hA, le_trans hx hpq.1, le_trans hy hpq.2⟩

/-- **Los puntos de la frontera están en la región.** -/
theorem frontera_sub_region {Q R Y : Type} (O : Y → Q → R) : Frontera O ⊆ Region O := fun _ h => h.1

/-! ### La región depende solo de cuántas instancias hay

Con el verificador de sí o no, renombrar las instancias por una biyección no cambia la región. Se usa para llevar las
mezclas de `LeyTresMemorias`, que viven en un producto `Fin (2^j) × Fin (2^k)`, a `Fin (2^m)`. -/

/-- **Renombrar un árbol**: las consultas y las salidas pasan por `g`. -/
def mapear {Y Y' : Type} (g : Y' → Y) : ArbolV Y' Bool Y' → ArbolV Y Bool Y
  | .hoja y => .hoja (g y)
  | .preg q sig => .preg (g q) fun r => mapear g (sig r)

theorem mapear_corre_pasos {Y Y' : Type} [DecidableEq Y] [DecidableEq Y'] (e : Y ≃ Y') (y : Y) :
    ∀ A : ArbolV Y' Bool Y',
      (mapear e.symm A).corre (igual y) = e.symm (A.corre (igual (e y))) ∧
        (mapear e.symm A).pasos (igual y) = A.pasos (igual (e y))
  | .hoja z => by simp [mapear, corre, pasos]
  | .preg q sig => by
      have hq : igual y (e.symm q) = igual (e y) q := by
        simp only [igual]; congr 1; exact propext (Equiv.symm_apply_eq e)
      simp only [mapear, corre, pasos, hq]
      obtain ⟨h1, h2⟩ := mapear_corre_pasos e y (sig (igual (e y) q))
      exact ⟨h1, by rw [h2]⟩

/-- **La región del verificador de sí o no es invariante por biyección.** -/
theorem alcanza_equiv {Y Y' : Type} [DecidableEq Y] [DecidableEq Y'] (e : Y ≃ Y') {x y : ℕ}
    (h : Alcanzable (igual (Y := Y')) x y) : Alcanzable (igual (Y := Y)) x y := by
  obtain ⟨P, C, iP, iC, A, L, s, t, hP, hC, hA, hx, hy⟩ := h
  refine ⟨P, C, iP, iC, fun p c => mapear e.symm (A p c), L, s, t, hP, hC, fun z => ?_, hx, hy⟩
  obtain ⟨p, c, h1, h2⟩ := hA (e z)
  obtain ⟨k1, k2⟩ := mapear_corre_pasos e z (A p c)
  exact ⟨p, c, by rw [k1, h1, Equiv.symm_apply_apply], by rw [k2]; exact h2⟩

/-! ## 2. Con el verificador de sí o no, la frontera es la recta -/

/-- **El verificador de sí o no sobre `N = 2^m` candidatos.** -/
abbrev siNo (m : ℕ) : Fin (2 ^ m) → Fin (2 ^ m) → Bool := igual

/-- **Toda la región queda arriba de la recta**: `x + y ≥ m`. Sale de `ley_si_no` (en bits, `ley_si_no_log`):
`m = ⌈log₂ 2^m⌉ ≤ L + s + ⌈log₂(t+1)⌉ ≤ x + y`. -/
theorem region_sobre_recta {m x y : ℕ} (h : Alcanzable (siNo m) x y) : m ≤ x + y := by
  obtain ⟨P, C, iP, iC, A, L, s, t, hP, hC, hA, hx, hy⟩ := h
  have := ley_si_no_log hP hC A hA
  rw [Fintype.card_fin, Nat.clog_pow 2 m one_lt_two] at this
  omega

/-- **La mezcla exacta**: la cita da los bits altos `c`; el resolvedor pregunta por todos los valores de los bits bajos
menos el último, y si todos dicen «no», devuelve el último sin preguntar. Es la mezcla de `LeyTresMemorias` (`mezcla`)
con el truco de `fuerza_bruta`: `2^k − 1` consultas en vez de `2^k`. -/
def mezclaExacta (j n : ℕ) : Unit → Fin (2 ^ j) → ArbolV (Fin (2 ^ j) × Fin (n + 1)) Bool (Fin (2 ^ j) × Fin (n + 1)) :=
  fun _ c => barrer ((todosMenosUltimo n).map fun i => (c, i)) (c, Fin.last n)

/-- **La mezcla exacta resuelve en `n` consultas.** -/
theorem mezclaExacta_resuelve (j n : ℕ) :
    Resuelve (P := Unit) (C := Fin (2 ^ j)) igual (mezclaExacta j n) n := by
  rintro ⟨c, i⟩
  refine ⟨(), c, ?_⟩
  have hmem : (c, i) ∈ (todosMenosUltimo n).map (fun i => (c, i)) ∨ (c, i) = (c, Fin.last n) := by
    induction i using Fin.lastCases with
    | last => exact Or.inr rfl
    | cast i => exact Or.inl (List.mem_map.2 ⟨i.castSucc, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)
  have := barrer_halla (c, i) _ _ hmem
  rwa [List.length_map, todosMenosUltimo, List.length_ofFn] at this

/-- **Los puntos enteros de la recta se alcanzan, sin redondeo**: para `k ≤ m`, el punto `(m − k, k)`. La cita es de
`m − k` bits y el tiempo `2^k − 1` consultas, así que `⌈log₂(t+1)⌉ = k` exacto. -/
theorem punto_en_recta {m k : ℕ} (hk : k ≤ m) : Alcanzable (siNo m) (m - k) k := by
  have hcard : Fintype.card (Fin (2 ^ m)) = Fintype.card (Fin (2 ^ (m - k)) × Fin (2 ^ k - 1 + 1)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_add, Nat.sub_add_cancel hk]
  refine alcanza_equiv (Fintype.equivOfCardEq hcard) ?_
  refine ⟨Unit, Fin (2 ^ (m - k)), inferInstance, inferInstance, mezclaExacta (m - k) (2 ^ k - 1), 0, m - k,
    2 ^ k - 1, by simp, by simp, mezclaExacta_resuelve _ _, by omega, ?_⟩
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.clog_pow 2 k one_lt_two]

/-- **La región es exactamente el semiplano `x + y ≥ m`.** -/
theorem region_es_semiplano (m x y : ℕ) : Alcanzable (siNo m) x y ↔ m ≤ x + y := by
  refine ⟨region_sobre_recta, fun h => ?_⟩
  have hp : ((m - min y m, min y m) : Punto) ∈ Region (siNo m) := punto_en_recta (min_le_right y m)
  refine region_cerrada_arriba (siNo m) (q := (x, y)) hp ⟨?_, min_le_left y m⟩
  change m - min y m ≤ x
  omega

/-- **La frontera es la recta `x + y = m`**, exactamente: con el tiempo medido como `⌈log₂(t+1)⌉` no hay redondeo. -/
theorem frontera_es_recta (m : ℕ) (p : Punto) : p ∈ Frontera (siNo m) ↔ p.1 + p.2 = m := by
  obtain ⟨x, y⟩ := p
  constructor
  · rintro ⟨hp, hmin⟩
    have h1 : m ≤ x + y := region_sobre_recta hp
    by_contra hne
    by_cases hx : 0 < x
    · have hq : ((x - 1, y) : Punto) ∈ Region (siNo m) := (region_es_semiplano m _ _).2 (by simp; omega)
      have := hmin _ hq ⟨by simp, le_rfl⟩
      simp [Prod.ext_iff] at this; omega
    · have hq : ((x, y - 1) : Punto) ∈ Region (siNo m) := (region_es_semiplano m _ _).2 (by simp; omega)
      have := hmin _ hq ⟨le_rfl, by simp⟩
      simp [Prod.ext_iff] at this; omega
  · intro h
    have h' : x + y = m := h
    refine ⟨(region_es_semiplano m x y).2 (by omega), fun q hq hqp => ?_⟩
    have h1 := region_sobre_recta hq
    have h2 : q.1 ≤ x := hqp.1
    have h3 : q.2 ≤ y := hqp.2
    exact Prod.ext (by change q.1 = x; omega) (by change q.2 = y; omega)

/-- **El redondeo de la mezcla de `LeyTresMemorias`**: con `t = 2^k` consultas (barrer todos los valores bajos), el
tiempo en bits es `⌈log₂(2^k + 1)⌉ = k + 1`: la mezcla original queda a distancia 1 de la recta. -/
theorem clog_mezcla (k : ℕ) : Nat.clog 2 (2 ^ k + 1) = k + 1 := by
  apply le_antisymm
  · apply Nat.clog_le_of_le_pow
    rw [pow_succ]; have := Nat.one_le_two_pow (n := k); omega
  · by_contra hlt
    have h1 : Nat.clog 2 (2 ^ k + 1) ≤ k := by omega
    have h2 := Nat.le_pow_clog one_lt_two (2 ^ k + 1)
    have h3 : 2 ^ Nat.clog 2 (2 ^ k + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h1
    omega

/-- **La mezcla de `LeyTresMemorias` alcanza `(j, k + 1)`**, a un paso de la recta `x + y = j + k`. -/
theorem mezcla_a_distancia_uno (j k : ℕ) : Alcanzable (siNo (j + k)) j (k + 1) := by
  have hcard : Fintype.card (Fin (2 ^ (j + k))) = Fintype.card (Fin (2 ^ j) × Fin (2 ^ k)) := by
    simp [pow_add]
  refine alcanza_equiv (Fintype.equivOfCardEq hcard) ?_
  exact ⟨Unit, Fin (2 ^ j), inferInstance, inferInstance, _, 0, j, 2 ^ k, by simp, by simp, mezcla j k, by omega,
    (clog_mezcla k).le⟩

/-! ## 3. El verificador gira la recta -/

/-- **Alcanzar en tiempo lineal**: como `Alcanzable`, pero el segundo eje es el número de consultas `t`, sin logaritmo. -/
def AlcanzableLineal {Q R Y : Type} (O : Y → Q → R) (x t : ℕ) : Prop :=
  ∃ (P C : Type) (_ : Fintype P) (_ : Fintype C) (A : P → C → ArbolV Q R Y) (L s : ℕ),
    Fintype.card P ≤ 2 ^ L ∧ Fintype.card C ≤ 2 ^ s ∧ Resuelve O A t ∧ L + s ≤ x

/-- **La recta girada**: con un verificador cualquiera de `b` bits, en el plano (memoria, tiempo lineal),
`⌈log₂ N⌉ ≤ x + b·t`. La pendiente es `−1/b`: una consulta vale `b` bits de memoria. Es `ley_log`. -/
theorem recta_girada {Q R Y : Type} [Fintype R] [Fintype Y] {b x t : ℕ}
    (hR : Fintype.card R ≤ 2 ^ b) (O : Y → Q → R) (h : AlcanzableLineal O x t) :
    Nat.clog 2 (Fintype.card Y) ≤ x + b * t := by
  classical
  obtain ⟨P, C, iP, iC, A, L, s, hP, hC, hA, hx⟩ := h
  have := ley_log hP hC hR O A hA
  omega

/-- **El verificador de bloques con cita**: la solución es un par `(c, z)` de `j + k` bloques de `b` bits; la consulta
`i` devuelve el bloque `i` de la parte `z`. La parte `c` no se puede consultar: solo llega por la cita. -/
def bloqueBajo {j k b : ℕ} (y : (Fin j → Fin (2 ^ b)) × (Fin k → Fin (2 ^ b))) : Fin k → Fin (2 ^ b) := y.2

/-- El árbol de la cita `c`: lee los `k` bloques de `z` y devuelve `(c, z)`. -/
def leerConCita (j k b : ℕ) (c : Fin j → Fin (2 ^ b)) :
    ArbolV (Fin k) (Fin (2 ^ b)) ((Fin j → Fin (2 ^ b)) × (Fin k → Fin (2 ^ b))) :=
  leer (List.finRange k) fun rs => (c, fun i => rs.getD i ⟨0, Nat.two_pow_pos b⟩)

theorem leerConCita_resuelve (j k b : ℕ) :
    Resuelve (P := Unit) (C := Fin j → Fin (2 ^ b)) bloqueBajo (fun _ c => leerConCita j k b c) k := by
  rintro ⟨c, z⟩
  refine ⟨(), c, ?_, ?_⟩
  · unfold leerConCita
    rw [corre_leer]
    ext i
    · rfl
    · simp [bloqueBajo, List.getD_eq_getElem?_getD]
  · unfold leerConCita
    rw [pasos_leer, List.length_finRange]

/-- **Los bloques alcanzan toda la recta girada**: con `N = 2^(b·(j+k))`, el punto `(b·j, k)` (cita de `j` bloques y
`k` consultas) se alcanza y cumple `⌈log₂ N⌉ = b·j + b·k`, con igualdad. Pasar un bloque del tiempo a la cita cuesta
exactamente `b` bits: esa es la pendiente. -/
theorem bloques_en_recta_girada (j k b : ℕ) :
    AlcanzableLineal (bloqueBajo (j := j) (k := k) (b := b)) (b * j) k ∧
      Nat.clog 2 (Fintype.card ((Fin j → Fin (2 ^ b)) × (Fin k → Fin (2 ^ b)))) = b * j + b * k := by
  refine ⟨⟨Unit, Fin j → Fin (2 ^ b), inferInstance, inferInstance, _, 0, b * j, by simp,
    by simp [← pow_mul], leerConCita_resuelve j k b, by omega⟩, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_mul, ← pow_add]
  exact Nat.clog_pow 2 _ one_lt_two

/-! ## 4. La proyección de Levin

En el modelo de rondas de `UniversoCerrado` y `Levin`: un proceso cerrado `p = (i, k)` (programa número `i`, presupuesto
`k` de `evaln`) es el punto `(i, ⌈log₂ k⌉)`. La búsqueda universal es un único programa (`levin_es_programa`), así que su
memoria es una constante que depende solo del verificador; su tiempo, en bits, es a lo sumo `i + ⌈log₂ k⌉ + 3`. -/

section Levin

open Nat.Partrec Nat.Partrec.Code
open Sagitta.Map.Tiempo.UniversoCerrado Sagitta.Map.Tiempo.CorteRacional

/-- **El punto de un proceso cerrado**: `(i, ⌈log₂ k⌉)`, descripción por tiempo en bits. -/
def puntoProceso (p : Proceso) : Punto := (p.i, Nat.clog 2 p.k)

/-- **La diagonal**: la proyección de pendiente `−1` sobre el eje del tiempo manda `(x, y)` a `(0, x + y)`. -/
def proyDiagonal (p : Punto) : Punto := (0, p.1 + p.2)

/-- **La proyección de Levin**: si el proceso `p` resuelve el universo, el costo de la búsqueda universal, en bits,
queda a lo sumo `3` arriba de la proyección diagonal del punto de `p`: `⌈log₂ costoLevin⌉ ≤ (i + ⌈log₂ k⌉) + 3`.
Es `levin_en_bits` (que sale de `costoLevin_le`). -/
theorem proyeccion_levin {U : Universo} {p : Proceso} (h : Correcto U p) :
    Nat.clog 2 (costoLevin U.V U.x) ≤ (proyDiagonal (puntoProceso p)).2 + 3 := by
  obtain ⟨y, hy, hV⟩ := h
  exact levin_en_bits (Correcto.k_pos ⟨y, hy, hV⟩) hy hV

/-- **La memoria de Levin es una constante.** Si el verificador es primitivo recursivo, hay un código `L` (uno solo
para todas las entradas y todos los procesos) que entrega solo respuestas aceptadas, termina en toda entrada resoluble,
y cuyo costo por rondas, en bits, es a lo sumo `i + ⌈log₂ k⌉ + 3` para **todo** proceso `(i, k)` correcto. El punto de
la búsqueda es `(código de L, i + ⌈log₂ k⌉ + 3)`: la memoria del resolvedor pasó al tiempo con tasa 1. -/
theorem levin_punto_constante {V : ℕ → ℕ → Bool} (hV : Primrec₂ V) : ∃ L : Code,
    (∀ x y, y ∈ eval L x → V x y = true) ∧
    ∀ x (p : Proceso), Correcto ⟨V, x⟩ p →
      (eval L x).Dom ∧ Nat.clog 2 (costoLevin V x) ≤ (proyDiagonal (puntoProceso p)).2 + 3 := by
  obtain ⟨L, hacc, hres⟩ := levin_es_programa hV
  exact ⟨L, hacc, fun x p hp => ⟨(hres x ⟨p, hp⟩).1, proyeccion_levin (U := ⟨V, x⟩) hp⟩⟩

/-- **Contra toda la frontera a la vez**: `log₂ costoLevin < kt + 3`, y `kt` es el mínimo de `x + y` sobre los puntos
de los procesos correctos (`kt_le`, `kt_alcanzado`). Levin proyecta el mejor punto sobre la diagonal. -/
theorem levin_bajo_la_frontera {U : Universo} (h : Resoluble U) :
    Nat.log 2 (costoLevin U.V U.x) < kt U + 3 ∧
      ∃ p, Correcto U p ∧ kt U = (proyDiagonal (puntoProceso p)).2 ∧
        ∀ q, Correcto U q → (proyDiagonal (puntoProceso p)).2 ≤ (proyDiagonal (puntoProceso q)).2 := by
  obtain ⟨p, hp, he⟩ := kt_alcanzado h
  refine ⟨log_levin_lt_kt h, p, hp, he, fun q hq => ?_⟩
  change p.i + Nat.clog 2 p.k ≤ q.i + Nat.clog 2 q.k
  rw [← he]; exact kt_le hq

/-- **El paso aritmético no admite menos que `+3`**: `c < 8 · 2^i · k` no implica `⌈log₂ c⌉ ≤ i + ⌈log₂ k⌉ + 2`
(con `c = 7`, `i = 0`, `k = 1`). Esto refuta el atajo de la prueba, no la cota de Levin misma. -/
theorem mutante_bits_sin_tres :
    ¬ ∀ c i k : ℕ, c < 8 * 2 ^ i * k → Nat.clog 2 c ≤ i + Nat.clog 2 k + 2 := by
  intro h
  have h1 := h 7 0 1 (by norm_num)
  simp only [Nat.clog_one_right] at h1
  have h2 := Nat.le_pow_clog one_lt_two 7
  have h3 : 2 ^ Nat.clog 2 7 ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Levin

/-! ## 5. Blum no toca el eje del tiempo

Para la `f` de `BlumExiste.blum` (la misma de `existe_irracional`), los programas de `f` son puntos
`(código, costo)`: la descripción en un eje y la función de costo en el otro, comparada por `o` (casi toda entrada). -/

section Blum

open Nat.Partrec Nat.Partrec.Code
open Sagitta.Map.Tiempo.AceleracionBlum Sagitta.Map.Tiempo.CorteRacional

/-- Acotado y luego despreciable es despreciable: si `f = O(g)` y `g ∈ o(h)`, entonces `f ∈ o(h)`. -/
theorem O_de_o {f g h : ℕ → ℕ} (h1 : EsO f g) (h2 : g ∈ o h) : f ∈ o h := fun c => by
  obtain ⟨C, N₁, h1⟩ := h1
  obtain ⟨N₂, h2⟩ := h2 (c * C)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have a := h1 n (le_of_max_le_left hn)
  have b := h2 n (le_of_max_le_right hn)
  calc c * f n ≤ c * (C * g n) := Nat.mul_le_mul_left _ a
    _ = c * C * g n := by ring
    _ ≤ h n := b

variable {f : ℕ → ℕ}

/-- La aceleración lineal de Blum. -/
abbrev Rapida (f : ℕ → ℕ) : Prop := TieneAceleracion (fun n x => (n + 1) * x) f

/-- **La escalera desde cualquier programa**: si `f` tiene aceleración, desde todo programa `i` de `f` baja una
escalera de programas de `f`, cada uno despreciable frente al anterior. -/
theorem escalera_desde (hB : Rapida f) {i : Code} (hi : Computa i f) :
    ∃ s : ℕ → Code, s 0 = i ∧ (∀ k, Computa (s k) f) ∧ ∀ k, costo (s (k + 1)) ∈ o (costo (s k)) := by
  have paso : ∀ c : {c // Computa c f}, ∃ d : {c // Computa c f}, costo d.1 ∈ o (costo c.1) := fun c =>
    let ⟨j, hj, ho⟩ := acelera_o (fun _ _ => le_rfl) hB c.2
    ⟨⟨j, hj⟩, ho⟩
  choose F hF using paso
  let s : ℕ → {c // Computa c f} := fun k => F^[k] ⟨i, hi⟩
  refine ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k => ?_⟩
  simp only [s, Function.iterate_succ_apply']
  exact hF _

/-- **Para todo punto hay otro más rápido y más largo**: para todo programa `i` de `f` y toda cota `M`, hay un programa
`j` de `f` con costo despreciable frente al de `i` (en casi toda entrada, por todo factor constante) y código mayor que
`M`. -/
theorem mas_rapido_y_mas_largo (hB : Rapida f) {i : Code} (hi : Computa i f) (M : ℕ) :
    ∃ j, Computa j f ∧ costo j ∈ o (costo i) ∧ M < Encodable.encode j := by
  obtain ⟨s, h0, hs, ho⟩ := escalera_desde hB hi
  have hinj : Function.Injective fun k => costo (s k) :=
    cadena_inyectiva ho fun k n => lt_of_le_of_lt (Nat.zero_le n) (costo_gt (hs k) n)
  have hinj' : Function.Injective fun k => s (k + 1) := fun a b h => by
    have : (fun k => costo (s k)) (a + 1) = (fun k => costo (s k)) (b + 1) := by
      change costo (s (a + 1)) = costo (s (b + 1)); rw [show s (a + 1) = s (b + 1) from h]
    have := hinj this; omega
  obtain ⟨k, hk⟩ := no_acotado_de_inyectiva hinj' Encodable.encode codigos_finitos M
  refine ⟨s (k + 1), hs _, ?_, hk⟩
  have := cadena_o (t := fun k => costo (s k)) ho (Nat.succ_pos k)
  rw [h0] at this; exact this

/-- **La frontera de Blum no tiene esquina en el eje del tiempo**, enunciado preciso: no hay ninguna cota `M` de
descripción tal que los programas de `f` con código `≤ M` alcancen, salvo una constante, a todo programa de `f`. Es más
fuerte que `sin_optimo` (que lo dice para un solo programa): ni siquiera un conjunto finito de programas sirve. Para
acercarse a la frontera del tiempo hay que pagar descripción sin cota. -/
theorem sin_esquina (hB : Rapida f) :
    ¬ ∃ M, ∀ j, Computa j f → ∃ i, Computa i f ∧ Encodable.encode i ≤ M ∧ EsO (costo i) (costo j) := by
  rintro ⟨M, hM⟩
  have paso : ∀ c : {c // Computa c f ∧ Encodable.encode c ≤ M},
      ∃ d : {c // Computa c f ∧ Encodable.encode c ≤ M}, costo d.1 ∈ o (costo c.1) := fun c => by
    obtain ⟨j, hj, ho⟩ := acelera_o (fun _ _ => le_rfl) hB c.2.1
    obtain ⟨i, hi, hiM, hO⟩ := hM j hj
    exact ⟨⟨i, hi, hiM⟩, O_de_o hO ho⟩
  choose F hF using paso
  obtain ⟨i₀, hi₀⟩ := hB.1
  obtain ⟨c₀, hc₀, hc₀M, -⟩ := hM i₀ hi₀
  let s : ℕ → {c // Computa c f ∧ Encodable.encode c ≤ M} := fun k => F^[k] ⟨c₀, hc₀, hc₀M⟩
  have ho : ∀ k, costo (s (k + 1)).1 ∈ o (costo (s k).1) := fun k => by
    simp only [s, Function.iterate_succ_apply']; exact hF _
  have hinj : Function.Injective fun k => costo (s k).1 :=
    cadena_inyectiva ho fun k n => lt_of_le_of_lt (Nat.zero_le n) (costo_gt (s k).2.1 n)
  have hinj' : Function.Injective fun k => (s k).1 := fun a b h => hinj (by
    change costo (s a).1 = costo (s b).1; rw [show (s a).1 = (s b).1 from h])
  obtain ⟨k, hk⟩ := no_acotado_de_inyectiva hinj' Encodable.encode codigos_finitos M
  have hle : Encodable.encode (s k).1 ≤ M := (s k).2.2
  exact absurd hle (not_le.2 hk)

/-- **Las descripciones de la frontera no están acotadas**: hay programas de `f` con código tan grande como se quiera,
y cada uno más rápido que uno dado. -/
theorem descripciones_no_acotadas (hB : Rapida f) (M : ℕ) : ∃ j, Computa j f ∧ M < Encodable.encode j := by
  obtain ⟨i, hi⟩ := hB.1
  obtain ⟨j, hj, -, hk⟩ := mas_rapido_y_mas_largo hB hi M
  exact ⟨j, hj, hk⟩

/-- **Blum, en el plano.** Hay una función computable `f` de valores `0` y `1` tal que: (a) todo punto (programa de
`f`) tiene otro con costo despreciable frente al suyo y código mayor que cualquier cota dada; (b) no hay programa
óptimo salvo constante (`sin_optimo`); (c) ninguna cota de descripción alcanza la frontera del tiempo (`sin_esquina`). -/
theorem blum_en_el_plano : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧
    (∀ i, Computa i f → ∀ M, ∃ j, Computa j f ∧ costo j ∈ o (costo i) ∧ M < Encodable.encode j) ∧
    (¬ ∃ i, Computa i f ∧ ∀ j, Computa j f → EsO (costo i) (costo j)) ∧
    ¬ ∃ M, ∀ j, Computa j f → ∃ i, Computa i f ∧ Encodable.encode i ≤ M ∧ EsO (costo i) (costo j) := by
  obtain ⟨f, h1, h2, h3⟩ := BlumExiste.blum BlumExiste.computable_lineal
  exact ⟨f, h1, h2, fun i hi M => mas_rapido_y_mas_largo h3 hi M, sin_optimo (fun _ _ => le_rfl) h3, sin_esquina h3⟩

/-- **Control de que `sin_esquina` no es vacío**: la constante `0` sí tiene esquina, con `M` el código de `Code.zero`
(`cero_optimo`). -/
theorem cero_tiene_esquina :
    ∃ M, ∀ j, Computa j (fun _ => 0) → ∃ i, Computa i (fun _ => 0) ∧ Encodable.encode i ≤ M ∧
      EsO (costo i) (costo j) :=
  ⟨Encodable.encode Code.zero, fun j hj => ⟨Code.zero, computa_cero, le_rfl,
    ⟨1, 0, fun n _ => by rw [one_mul]; exact cero_optimo hj n⟩⟩⟩

end Blum

/-! ## 6. Controles y mutantes refutados -/

/-- **La región no es vacía**: la fuerza bruta (exacta) da `(0, m)` y el certificado sin verificar `(m, 0)`. -/
theorem region_no_vacia (m : ℕ) : ((0, m) : Punto) ∈ Region (siNo m) ∧ ((m, 0) : Punto) ∈ Region (siNo m) := by
  refine ⟨?_, ?_⟩
  · change Alcanzable (siNo m) 0 m; simpa using punto_en_recta (m := m) le_rfl
  · change Alcanzable (siNo m) m 0; simpa using punto_en_recta (m := m) (Nat.zero_le m)

/-- **Un punto debajo de la recta no se alcanza**: con `m = 3`, `(1, 1)` no está en la región. -/
theorem debajo_no (m x y : ℕ) (h : x + y < m) : ¬ Alcanzable (siNo m) x y := fun h' => by
  have := region_sobre_recta h'; omega

example : ((1, 1) : Punto) ∉ Region (siNo 3) := debajo_no 3 1 1 (by norm_num)

/-- **Mutante: la recta con `m + 1`** es falso: el punto `(m, 0)` (certificado sin verificar) está en la región y
tiene `x + y = m`. -/
theorem mutante_recta_mas_uno : ¬ ∀ m x y, Alcanzable (siNo m) x y → m + 1 ≤ x + y := fun h => by
  have := h 0 0 0 (by simpa using punto_en_recta (m := 0) le_rfl); omega

/-- **Mutante: la región sin cerrar hacia arriba** es falso: no hay un punto alcanzado con otro, más arriba, fuera. -/
theorem mutante_no_cerrada (m : ℕ) : ¬ ∃ p q : Punto, p ∈ Region (siNo m) ∧ p ≤ q ∧ q ∉ Region (siNo m) :=
  fun ⟨_, _, hp, hpq, hq⟩ => hq (region_cerrada_arriba _ hp hpq)

/-- **Mutante: la recta lineal sin girar** (`⌈log₂ N⌉ ≤ x + t`, pendiente 1 en vez de `b`) es falso para `b = 2`: los
bloques alcanzan `(0, 1)` con `N = 4`. -/
theorem mutante_sin_girar :
    ¬ (AlcanzableLineal (bloqueBajo (j := 0) (k := 1) (b := 2)) 0 1 →
      Nat.clog 2 (Fintype.card ((Fin 0 → Fin (2 ^ 2)) × (Fin 1 → Fin (2 ^ 2)))) ≤ 0 + 1) := fun h => by
  have ⟨h1, h2⟩ := bloques_en_recta_girada 0 1 2
  have := h (by simpa using h1); omega

/-- **Mutante: la frontera de Blum con descripción acotada** es falso: es la negación de `sin_esquina`. -/
theorem mutante_blum_acotada : ¬ ∀ f : ℕ → ℕ, Computable f → (∀ n, f n ≤ 1) →
    ∃ M, ∀ j, AceleracionBlum.Computa j f → ∃ i, AceleracionBlum.Computa i f ∧ Encodable.encode i ≤ M ∧
      EsO (AceleracionBlum.costo i) (AceleracionBlum.costo j) := fun h => by
  obtain ⟨f, h1, h2, h3⟩ := BlumExiste.blum BlumExiste.computable_lineal
  exact sin_esquina h3 (h f h2 h1)

end Sagitta.Map.Tiempo.PlanoCostos
