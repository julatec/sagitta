import Sagitta.Map.CorteRacional
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log

/-!
# La ley de las tres memorias

La idea es de José (24 nov 2026). Para hallar una solución oculta hay tres memorias que se comunican a través del
tiempo de ejecución, y su suma se conserva:

* la **memoria del resolvedor**: el largo `L` de su descripción (el programa);
* la **memoria de la cita**: lo que se le pasa por instancia, de `s` bits (una caja, una pista, una parte del
  certificado);
* la **memoria del verificador**: cuánto informa cada consulta, `b` bits.

El tiempo `t` es la cantidad de consultas al verificador.

## El modelo

* Hay una instancia por cada solución oculta `y : Y`, con `N = |Y|` (por ejemplo `Y = Fin (2^m)`).
* El verificador es una caja negra `O y : Q → R`: la instancia `y` responde la consulta `q` con `O y q`. El de sí o
  no es `igual y z = decide (z = y)`.
* Un algoritmo es un árbol de consultas (`ArbolV Q R Y`) que termina devolviendo un candidato. Su tiempo con el
  verificador de `y` es la cantidad de consultas en el camino que recorre (`pasos`).
* Un resolvedor es una familia `A : P → C → ArbolV Q R Y`: programas `p : P`, con `|P| ≤ 2^L`, y citas `c : C`,
  con `|C| ≤ 2^s`. `Resuelve O A t` dice: **para toda `y` hay un par `(p, c)` cuyo árbol devuelve `y` en a lo sumo
  `t` consultas**.

**Qué cuantificación es «la descripción del resolvedor».** El caso honesto es **un único programa** por familia:
`P = Unit`, o un programa fijo `p` (`ley_programa_fijo`). Ese programa es el mismo para toda `y`, así que no informa
nada de cuál es: la ley le da `L = 0`. El programa **solo cuenta en la ley si se elige según la instancia**, y
entonces `|P| ≤ 2^L` es la cota de cuántos resolvedores distintos hay: con un intérprete fijo `U`, los programas
son las palabras de `L` bits (`ley_palabras`). «La solución en el programa» (`L = m`) es exactamente eso: un programa
distinto por instancia. La cita, en cambio, depende de `y` por definición; si no dependiera, no contaría
(`cita_fija`).

## Lo que se prueba

1. **La ley con un verificador de sí o no** (`ley_si_no`, `ley_si_no_log`):
   `N ≤ 2^L · 2^s · (t+1)`, o sea `L + s + ⌈log₂(t+1)⌉ ≥ ⌈log₂ N⌉`. El núcleo es `halla_le_si_no`: un árbol de sí o
   no de profundidad `t` contra el verificador de igualdad halla a lo sumo `t+1` soluciones, porque cada «no» descarta
   una sola.
2. **El verificador informativo** (`ley`, `ley_log`): si cada consulta devuelve hasta `b` bits,
   `N ≤ 2^L · 2^s · 2^(b·t)`, o sea `L + s + b·t ≥ ⌈log₂ N⌉`. Vale para **cualquier** verificador de `b` bits. Uno
   que devuelve un bloque de `y` por consulta la alcanza con igualdad (`bloques_alcanza`, `bloques_en_la_recta`).
3. **Los cuatro puntos que alcanzan la ley** (controles): fuerza bruta (`fuerza_bruta`, con igualdad en `t = N − 1`),
   el certificado como cita (`certificado_cita`, `s = m`), la solución en el programa (`solucion_programa`, `L = m`)
   y la mezcla (`mezcla`, `s = m − k`, `t = 2^k`), cada uno con su teorema de que funciona y de dónde queda respecto
   de la recta.
4. **El puente con Levin.** Dentro del modelo, la tasa `2^L` se alcanza del otro lado: un único programa que prueba
   los `|P|` programas uno tras otro, cortados a `t` consultas y verificando cada salida con una consulta más, resuelve
   en `|P|·(t+1)` consultas (`levin_caja`). Borrar `L` bits de programa cuesta un factor `2^L` en tiempo
   (`levin_caja_ley`). Con la búsqueda universal de `Levin.lean` la misma cuenta, en bits, dice que el tiempo de la
   búsqueda es a lo sumo la descripción `i` del programa imitado más el tiempo de ese programa más 3
   (`levin_en_bits`, `levin_escalera_en_bits`).
5. **Mutantes refutados** (sección final): sin el `+1`, sin la cita, con la cita fija, y con `2^t` en lugar de `t+1`
   para el verificador de igualdad son falsos; `t+1` para un verificador de sí o no cualquiera, también.

## La lectura

La información que identifica la solución sale de tres lugares: del programa (si se eligió según la instancia), de
la cita, o de lo que se aprende corriendo. Lo que se aprende corriendo está acotado por el verificador: cada consulta
informa a lo sumo `b` bits, y una de igualdad informa todavía menos (`log₂(t+1)` en `t` consultas, no `t`). El
verificador pone la tasa de cambio entre tiempo y descripción.

## Lo que NO se prueba

* **Es caja negra**: la instancia solo se ve por el verificador. El argumento relativiza (como el adversario de
  `Decidir.lean`; Baker, Gill y Solovay, 1975) y no dice nada de una instancia dada por su texto.
* **En caja blanca la entrada ya contiene la información**: la solución está determinada por la entrada, así que no
  falta información, falta cómputo. La ley deja de ser de información y pasa a ser de cómputo: es la complejidad de
  Kolmogorov con tiempo acotado (la `Kt` de Levin) y la metacomplejidad, que son investigación abierta (de memoria y
  sin verificar: Liu y Pass, 2020, que ligan las funciones de un solo sentido con la dificultad de `Kt`; Hirahara,
  varios trabajos desde 2018). Nada de eso se formaliza aquí.
* **Nada sobre `P` contra `NP`.**
* El puente con `Levin.lean` es de forma, no de medida: allá el costo es presupuesto de `evaln`, no consultas a una
  caja negra. La versión exacta dentro de este modelo es `levin_caja`.
-/

namespace Sagitta.Map.Tiempo.LeyTresMemorias

/-! ## El modelo -/

/-- **Un árbol de consultas al verificador**: o devuelve un candidato `y : Y`, o consulta `q : Q` y sigue según la
respuesta `r : R`. Es adaptativo. -/
inductive ArbolV (Q R Y : Type) : Type
  | hoja (y : Y) : ArbolV Q R Y
  | preg (q : Q) (sig : R → ArbolV Q R Y) : ArbolV Q R Y

namespace ArbolV

variable {Q R Y : Type}

/-- Lo que devuelve el árbol con el verificador `O`. -/
def corre : ArbolV Q R Y → (Q → R) → Y
  | hoja y, _ => y
  | preg q sig, O => corre (sig (O q)) O

/-- **El tiempo**: cuántas consultas hace el árbol con el verificador `O`. -/
def pasos : ArbolV Q R Y → (Q → R) → ℕ
  | hoja _, _ => 0
  | preg q sig, O => pasos (sig (O q)) O + 1

end ArbolV

open ArbolV

/-- **El verificador de sí o no**: la instancia `y` responde «¿es `z`?». -/
def igual {Y : Type} [DecidableEq Y] (y : Y) : Y → Bool := fun z => decide (z = y)

/-- **Un resolvedor resuelve en tiempo `t`**: para toda solución oculta `y` hay un programa `p` y una cita `c` cuyo
árbol, con el verificador de `y`, devuelve `y` en a lo sumo `t` consultas. -/
def Resuelve {P C Q R Y : Type} (O : Y → Q → R) (A : P → C → ArbolV Q R Y) (t : ℕ) : Prop :=
  ∀ y, ∃ p c, (A p c).corre (O y) = y ∧ (A p c).pasos (O y) ≤ t

/-! ## Cuántas soluciones halla un árbol -/

/-- **El palomar del verificador**: si cada consulta tiene a lo sumo `2^b` respuestas, un árbol que hace a lo sumo
`t` consultas halla a lo sumo `(2^b)^t` soluciones. Cada solución hallada queda determinada por la sucesión de
respuestas que recibe. -/
theorem halla_le {Q R Y : Type} [Fintype R] [DecidableEq Y] {b : ℕ} (hR : Fintype.card R ≤ 2 ^ b)
    (O : Y → Q → R) : ∀ (A : ArbolV Q R Y) (t : ℕ) (S : Finset Y),
    (S.filter fun y => A.corre (O y) = y ∧ A.pasos (O y) ≤ t).card ≤ (2 ^ b) ^ t
  | .hoja z, t, S => by
      calc _ ≤ ({z} : Finset Y).card := Finset.card_le_card fun y hy => by
              rw [Finset.mem_filter] at hy; simp only [corre] at hy; simp [hy.2.1.symm]
        _ = 1 := Finset.card_singleton z
        _ ≤ _ := Nat.one_le_pow _ _ (by positivity)
  | .preg q sig, 0, S => by
      simp [pasos]
  | .preg q sig, t + 1, S => by
      classical
      calc _ ≤ (Finset.univ.biUnion fun r : R => (S.filter fun y => O y q = r).filter
              fun y => (sig r).corre (O y) = y ∧ (sig r).pasos (O y) ≤ t).card := by
            apply Finset.card_le_card
            intro y hy
            rw [Finset.mem_filter] at hy; simp only [corre, pasos] at hy
            simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
            exact ⟨O y q, ⟨hy.1, rfl⟩, hy.2.1, by omega⟩
        _ ≤ ∑ r : R, ((S.filter fun y => O y q = r).filter
              fun y => (sig r).corre (O y) = y ∧ (sig r).pasos (O y) ≤ t).card := Finset.card_biUnion_le
        _ ≤ ∑ _r : R, (2 ^ b) ^ t := Finset.sum_le_sum fun r _ => halla_le hR O (sig r) t _
        _ = Fintype.card R * (2 ^ b) ^ t := by simp
        _ ≤ 2 ^ b * (2 ^ b) ^ t := Nat.mul_le_mul_right _ hR
        _ = (2 ^ b) ^ (t + 1) := (pow_succ' _ _).symm

/-- **Cada «no» descarta una sola**: contra el verificador de igualdad, un árbol que hace a lo sumo `t` consultas
halla a lo sumo `t + 1` soluciones. Si la consulta es `q`, la única solución que oye «sí» es `q`; todas las demás
oyen «no» y siguen el mismo camino. -/
theorem halla_le_si_no {Y : Type} [DecidableEq Y] : ∀ (A : ArbolV Y Bool Y) (t : ℕ) (S : Finset Y),
    (S.filter fun y => A.corre (igual y) = y ∧ A.pasos (igual y) ≤ t).card ≤ t + 1
  | .hoja z, t, S => by
      calc _ ≤ ({z} : Finset Y).card := Finset.card_le_card fun y hy => by
              rw [Finset.mem_filter] at hy; simp only [corre] at hy; simp [hy.2.1.symm]
        _ = 1 := Finset.card_singleton z
        _ ≤ t + 1 := by omega
  | .preg q sig, 0, S => by
      simp [pasos]
  | .preg q sig, t + 1, S => by
      calc _ ≤ (insert q (S.filter fun y => (sig false).corre (igual y) = y ∧
              (sig false).pasos (igual y) ≤ t)).card := by
            apply Finset.card_le_card
            intro y hy
            rw [Finset.mem_filter] at hy; simp only [corre, pasos] at hy
            by_cases hq : q = y
            · simp [hq]
            · have hf : igual y q = false := by simp [igual, hq]
              rw [hf] at hy
              exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy.1, hy.2.1, by omega⟩)
        _ ≤ _ + 1 := Finset.card_insert_le _ _
        _ ≤ t + 1 + 1 := Nat.add_le_add_right (halla_le_si_no (sig false) t S) 1

/-- **El palomar de los resolvedores**: si cada índice `i` halla a lo sumo `K` instancias y toda instancia la halla
algún índice, hay a lo sumo `|ι| · K` instancias. -/
theorem cubrir {ι Y : Type} [Fintype ι] [Fintype Y] (bien : ι → Y → Prop) [∀ i y, Decidable (bien i y)] (K : ℕ)
    (hK : ∀ i, (Finset.univ.filter (bien i)).card ≤ K) (h : ∀ y, ∃ i, bien i y) :
    Fintype.card Y ≤ Fintype.card ι * K := by
  classical
  calc Fintype.card Y = (Finset.univ : Finset Y).card := Finset.card_univ.symm
    _ ≤ (Finset.univ.biUnion fun i => Finset.univ.filter (bien i)).card := by
        apply Finset.card_le_card
        intro y _
        obtain ⟨i, hi⟩ := h y
        exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
    _ ≤ ∑ i, (Finset.univ.filter (bien i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : ι, K := Finset.sum_le_sum fun i _ => hK i
    _ = Fintype.card ι * K := by simp

/-! ## 1. La ley con un verificador de sí o no -/

/-- **La ley de las tres memorias, verificador de sí o no**: `N ≤ 2^L · 2^s · (t+1)`. -/
theorem ley_si_no {P C Y : Type} [Fintype P] [Fintype C] [Fintype Y] [DecidableEq Y] {L s t : ℕ}
    (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (A : P → C → ArbolV Y Bool Y)
    (h : Resuelve igual A t) : Fintype.card Y ≤ 2 ^ L * 2 ^ s * (t + 1) := by
  have hc := cubrir (ι := P × C)
    (fun pc y => (A pc.1 pc.2).corre (igual y) = y ∧ (A pc.1 pc.2).pasos (igual y) ≤ t) (t + 1)
    (fun pc => halla_le_si_no _ t _) (fun y => by obtain ⟨p, c, hy⟩ := h y; exact ⟨(p, c), hy⟩)
  rw [Fintype.card_prod] at hc
  calc Fintype.card Y ≤ Fintype.card P * Fintype.card C * (t + 1) := hc
    _ ≤ 2 ^ L * 2 ^ s * (t + 1) := by gcongr

/-- **En bits**: `⌈log₂ N⌉ ≤ L + s + ⌈log₂(t+1)⌉`. -/
theorem ley_si_no_log {P C Y : Type} [Fintype P] [Fintype C] [Fintype Y] [DecidableEq Y] {L s t : ℕ}
    (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (A : P → C → ArbolV Y Bool Y)
    (h : Resuelve igual A t) : Nat.clog 2 (Fintype.card Y) ≤ L + s + Nat.clog 2 (t + 1) := by
  apply Nat.clog_le_of_le_pow
  calc Fintype.card Y ≤ 2 ^ L * 2 ^ s * (t + 1) := ley_si_no hP hC A h
    _ ≤ 2 ^ L * 2 ^ s * 2 ^ Nat.clog 2 (t + 1) := by gcongr; exact Nat.le_pow_clog one_lt_two _
    _ = 2 ^ (L + s + Nat.clog 2 (t + 1)) := by rw [pow_add, pow_add]

/-- **El caso honesto: un único programa.** Un programa fijo no informa nada de la instancia: `N ≤ 2^s · (t+1)`, la
ley con `L = 0`, cualquiera sea el largo del programa. -/
theorem ley_programa_fijo {C Y : Type} [Fintype C] [Fintype Y] [DecidableEq Y] {s t : ℕ}
    (hC : Fintype.card C ≤ 2 ^ s) (A : C → ArbolV Y Bool Y)
    (h : ∀ y, ∃ c, (A c).corre (igual y) = y ∧ (A c).pasos (igual y) ≤ t) :
    Fintype.card Y ≤ 2 ^ s * (t + 1) := by
  have := ley_si_no (P := Unit) (L := 0) (by simp) hC (fun _ c => A c)
    (fun y => by obtain ⟨c, hc⟩ := h y; exact ⟨(), c, hc⟩)
  simpa using this

/-- **Programas como palabras**: un intérprete fijo `U` y programas de `L` bits, elegidos según la instancia, con
citas de `s` bits. Es la ley con `|P| = 2^L` y `|C| = 2^s` exactos. -/
theorem ley_palabras {Y : Type} [Fintype Y] [DecidableEq Y] {L s t : ℕ}
    (U : (Fin L → Bool) → (Fin s → Bool) → ArbolV Y Bool Y) (h : Resuelve igual U t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * (t + 1) :=
  ley_si_no (by simp) (by simp) U h

/-- **Si la cita no depende de la instancia, no cuenta**: con una cita `c` fija para toda `y`,
`N ≤ 2^L · (t+1)`; la `s` desaparece. -/
theorem cita_fija {P C Y : Type} [Fintype P] [Fintype Y] [DecidableEq Y] {L t : ℕ}
    (hP : Fintype.card P ≤ 2 ^ L) (A : P → C → ArbolV Y Bool Y)
    (h : ∃ c, ∀ y, ∃ p, (A p c).corre (igual y) = y ∧ (A p c).pasos (igual y) ≤ t) :
    Fintype.card Y ≤ 2 ^ L * (t + 1) := by
  obtain ⟨c, hc⟩ := h
  have := ley_si_no (C := Unit) (s := 0) hP (by simp) (fun p _ => A p c)
    (fun y => by obtain ⟨p, hp⟩ := hc y; exact ⟨p, (), hp⟩)
  simpa using this

/-! ## 2. El verificador informativo -/

/-- **La ley de las tres memorias**: con un verificador cualquiera cuyas respuestas caben en `b` bits,
`N ≤ 2^L · 2^s · 2^(b·t)`. -/
theorem ley {P C Q R Y : Type} [Fintype P] [Fintype C] [Fintype R] [Fintype Y] [DecidableEq Y] {L s b t : ℕ}
    (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hR : Fintype.card R ≤ 2 ^ b)
    (O : Y → Q → R) (A : P → C → ArbolV Q R Y) (h : Resuelve O A t) :
    Fintype.card Y ≤ 2 ^ L * 2 ^ s * 2 ^ (b * t) := by
  have hc := cubrir (ι := P × C)
    (fun pc y => (A pc.1 pc.2).corre (O y) = y ∧ (A pc.1 pc.2).pasos (O y) ≤ t) ((2 ^ b) ^ t)
    (fun pc => halla_le hR O _ t _) (fun y => by obtain ⟨p, c, hy⟩ := h y; exact ⟨(p, c), hy⟩)
  rw [Fintype.card_prod, ← pow_mul] at hc
  calc Fintype.card Y ≤ Fintype.card P * Fintype.card C * 2 ^ (b * t) := hc
    _ ≤ 2 ^ L * 2 ^ s * 2 ^ (b * t) := by gcongr

/-- **En bits**: `⌈log₂ N⌉ ≤ L + s + b·t`. -/
theorem ley_log {P C Q R Y : Type} [Fintype P] [Fintype C] [Fintype R] [Fintype Y] [DecidableEq Y]
    {L s b t : ℕ} (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (hR : Fintype.card R ≤ 2 ^ b)
    (O : Y → Q → R) (A : P → C → ArbolV Q R Y) (h : Resuelve O A t) :
    Nat.clog 2 (Fintype.card Y) ≤ L + s + b * t := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add, pow_add]
  exact ley hP hC hR O A h

/-- **Leer en orden**: consultar la lista `qs` y devolver una función de las respuestas. -/
def leer {Q R Y : Type} : List Q → (List R → Y) → ArbolV Q R Y
  | [], k => .hoja (k [])
  | q :: qs, k => .preg q fun r => leer qs fun rs => k (r :: rs)

theorem corre_leer {Q R Y : Type} (O : Q → R) : ∀ (qs : List Q) (k : List R → Y),
    (leer qs k).corre O = k (qs.map O)
  | [], _ => rfl
  | q :: qs, k => by simp only [leer, corre]; rw [corre_leer O qs]; rfl

theorem pasos_leer {Q R Y : Type} (O : Q → R) : ∀ (qs : List Q) (k : List R → Y),
    (leer qs k).pasos O = qs.length
  | [], _ => rfl
  | q :: qs, k => by simp only [leer, pasos]; rw [pasos_leer O qs]; rfl

/-- **El verificador de bloques**: la solución es una sucesión de `t` bloques de `b` bits, y la consulta `i` devuelve
el bloque `i`. -/
def bloque {t b : ℕ} (y : Fin t → Fin (2 ^ b)) : Fin t → Fin (2 ^ b) := y

/-- El árbol que lee los `t` bloques y los devuelve. -/
def leerBloques (t b : ℕ) : ArbolV (Fin t) (Fin (2 ^ b)) (Fin t → Fin (2 ^ b)) :=
  leer (List.finRange t) fun rs i => rs.getD i ⟨0, Nat.two_pow_pos b⟩

/-- **El verificador de bloques alcanza la ley**: sin programa ni cita, en `t` consultas, resuelve las `2^(b·t)`
instancias. -/
theorem bloques_alcanza (t b : ℕ) :
    Resuelve (P := Unit) (C := Unit) bloque (fun _ _ => leerBloques t b) t := by
  intro y
  refine ⟨(), (), ?_, ?_⟩
  · unfold leerBloques
    rw [corre_leer]
    funext i
    simp [bloque, List.getD_eq_getElem?_getD]
  · unfold leerBloques
    rw [pasos_leer, List.length_finRange]

/-- **Y queda en la recta, con igualdad**: `N = 2^0 · 2^0 · 2^(b·t)`. -/
theorem bloques_en_la_recta (t b : ℕ) :
    Fintype.card (Fin t → Fin (2 ^ b)) = 2 ^ 0 * 2 ^ 0 * 2 ^ (b * t) := by
  simp [← pow_mul]

/-! ## 3. Controles: los cuatro puntos que alcanzan la ley -/

/-- **Barrer**: preguntar por cada candidato de `zs`; si todos dicen «no», devolver `d`. -/
def barrer {Y : Type} : List Y → Y → ArbolV Y Bool Y
  | [], d => .hoja d
  | z :: zs, d => .preg z fun b => if b then .hoja z else barrer zs d

theorem barrer_halla {Y : Type} [DecidableEq Y] (y : Y) : ∀ (zs : List Y) (d : Y), (y ∈ zs ∨ y = d) →
    (barrer zs d).corre (igual y) = y ∧ (barrer zs d).pasos (igual y) ≤ zs.length
  | [], d, h => by
      simp only [List.not_mem_nil, false_or] at h
      subst h; simp [barrer, corre, pasos]
  | z :: zs, d, h => by
      by_cases hz : z = y
      · subst hz; simp [barrer, corre, pasos, igual]
      · have hf : igual y z = false := by simp [igual, hz]
        have h' : y ∈ zs ∨ y = d := by
          rcases h with h | h
          · rcases List.mem_cons.1 h with h | h
            · exact absurd h.symm hz
            · exact Or.inl h
          · exact Or.inr h
        obtain ⟨h1, h2⟩ := barrer_halla y zs d h'
        simp only [barrer, corre, pasos, hf, Bool.false_eq_true, ite_false, List.length_cons]
        exact ⟨h1, by omega⟩

/-- Los candidatos de la fuerza bruta: todos menos el último. -/
def todosMenosUltimo (n : ℕ) : List (Fin (n + 1)) := List.ofFn fun i : Fin n => i.castSucc

/-- **Fuerza bruta** (`L = s = 0`): preguntar por cada candidato menos el último resuelve las `N = n + 1` instancias
en `t = n = N − 1` consultas. -/
theorem fuerza_bruta (n : ℕ) :
    Resuelve (P := Unit) (C := Unit) igual (fun _ _ => barrer (todosMenosUltimo n) (Fin.last n)) n := by
  intro y
  refine ⟨(), (), ?_⟩
  have hmem : y ∈ todosMenosUltimo n ∨ y = Fin.last n := by
    induction y using Fin.lastCases with
    | last => exact Or.inr rfl
    | cast i => exact Or.inl (List.mem_ofFn.2 ⟨i, rfl⟩)
  have := barrer_halla y _ _ hmem
  rwa [todosMenosUltimo, List.length_ofFn] at this

/-- **Y queda en la recta, con igualdad**: `N = 2^0 · 2^0 · (t + 1)` con `t = n`. -/
theorem fuerza_bruta_en_la_recta (n : ℕ) : Fintype.card (Fin (n + 1)) = 2 ^ 0 * 2 ^ 0 * (n + 1) := by simp

/-- **Fuerza bruta con `t = N`** (barrer todos, como pide la lectura ingenua): también resuelve, a una consulta de la
recta. -/
theorem fuerza_bruta_N (n : ℕ) :
    Resuelve (P := Unit) (C := Unit) igual (fun _ _ => barrer (List.finRange (n + 1)) 0) (n + 1) := by
  intro y
  refine ⟨(), (), ?_⟩
  have := barrer_halla y (List.finRange (n + 1)) 0 (Or.inl (List.mem_finRange y))
  rwa [List.length_finRange] at this

/-- **Verificar y devolver**: consultar el candidato `z` (la verificación) y devolverlo. -/
def verificarYDevolver {Y : Type} (z : Y) : ArbolV Y Bool Y := .preg z fun _ => .hoja z

theorem verificarYDevolver_halla {Y : Type} [DecidableEq Y] (y : Y) :
    (verificarYDevolver y).corre (igual y) = y ∧ (verificarYDevolver y).pasos (igual y) ≤ 1 := by
  simp [verificarYDevolver, corre, pasos]

/-- **El certificado como cita** (`s = m`, `t = 1`): la cita es la solución, y el resolvedor la verifica con una
consulta y la devuelve. -/
theorem certificado_cita (m : ℕ) :
    Resuelve (P := Unit) (C := Fin (2 ^ m)) igual (fun _ c => verificarYDevolver c) 1 :=
  fun y => ⟨(), y, verificarYDevolver_halla y⟩

/-- **Queda a un bit de la recta** (el bit de la consulta de verificación): `2 · N = 2^0 · 2^m · (1 + 1)`. Sin
verificar (`t = 0`, `certificado_cita_cero`) queda exactamente en ella. -/
theorem certificado_en_la_recta (m : ℕ) : 2 * Fintype.card (Fin (2 ^ m)) = 2 ^ 0 * 2 ^ m * (1 + 1) := by
  simp; ring

/-- **El certificado sin verificar** (`s = m`, `t = 0`): `N = 2^0 · 2^m · (0 + 1)`, en la recta. -/
theorem certificado_cita_cero (m : ℕ) :
    Resuelve (P := Unit) (C := Fin (2 ^ m)) igual (fun _ c => .hoja c) 0 ∧
      Fintype.card (Fin (2 ^ m)) = 2 ^ 0 * 2 ^ m * (0 + 1) :=
  ⟨fun y => ⟨(), y, by simp [corre, pasos]⟩, by simp⟩

/-- **La solución en el programa** (`L = m`, `t = 1`): un programa distinto por instancia, que trae la solución
escrita; la verifica y la devuelve. -/
theorem solucion_programa (m : ℕ) :
    Resuelve (P := Fin (2 ^ m)) (C := Unit) igual (fun p _ => verificarYDevolver p) 1 :=
  fun y => ⟨y, (), verificarYDevolver_halla y⟩

/-- **En la recta** sin verificar (`t = 0`), y a un bit de ella verificando. -/
theorem solucion_programa_en_la_recta (m : ℕ) :
    Resuelve (P := Fin (2 ^ m)) (C := Unit) igual (fun p _ => .hoja p) 0 ∧
      Fintype.card (Fin (2 ^ m)) = 2 ^ m * 2 ^ 0 * (0 + 1) ∧
      2 * Fintype.card (Fin (2 ^ m)) = 2 ^ m * 2 ^ 0 * (1 + 1) :=
  ⟨fun y => ⟨y, (), by simp [corre, pasos]⟩, by simp, by simp; ring⟩

/-- Los candidatos de la mezcla: la parte alta `c` es la cita; la parte baja se barre. -/
def candidatos (j k : ℕ) (c : Fin (2 ^ j)) : List (Fin (2 ^ j) × Fin (2 ^ k)) :=
  (List.finRange (2 ^ k)).map fun i => (c, i)

/-- **La mezcla** (`m = j + k`, `s = j = m − k`, `t = 2^k`): la cita da los `j` bits altos de la solución y el
resolvedor barre los `2^k` valores de los bajos. -/
theorem mezcla (j k : ℕ) :
    Resuelve (P := Unit) (C := Fin (2 ^ j)) igual
      (fun _ c => barrer (candidatos j k c) (c, ⟨0, Nat.two_pow_pos k⟩)) (2 ^ k) := by
  rintro ⟨c, i⟩
  refine ⟨(), c, ?_⟩
  have hm : (c, i) ∈ candidatos j k c := List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩
  have := barrer_halla (c, i) (candidatos j k c) (c, ⟨0, Nat.two_pow_pos k⟩) (Or.inl hm)
  rwa [candidatos, List.length_map, List.length_finRange] at this

/-- **Casi en la recta**: `N = 2^(j+k) ≤ 2^0 · 2^j · (2^k + 1) ≤ 2 · N`. -/
theorem mezcla_en_la_recta (j k : ℕ) :
    Fintype.card (Fin (2 ^ j) × Fin (2 ^ k)) = 2 ^ (j + k) ∧
      2 ^ (j + k) ≤ 2 ^ 0 * 2 ^ j * (2 ^ k + 1) ∧ 2 ^ 0 * 2 ^ j * (2 ^ k + 1) ≤ 2 * 2 ^ (j + k) := by
  refine ⟨by simp [pow_add], ?_, ?_⟩
  · rw [pow_add]; simp
  · rw [pow_add]; simp
    have := Nat.one_le_two_pow (n := k)
    nlinarith [Nat.two_pow_pos j]

/-! ## 4. El puente con Levin -/

/-- **Cortar** un árbol a `t` consultas: si no terminó, devolver `d`. -/
def cortar {Q R Y : Type} (d : Y) : ℕ → ArbolV Q R Y → ArbolV Q R Y
  | _, .hoja y => .hoja y
  | 0, .preg _ _ => .hoja d
  | t + 1, .preg q sig => .preg q fun r => cortar d t (sig r)

theorem cortar_pasos {Q R Y : Type} (d : Y) (O : Q → R) : ∀ (t : ℕ) (A : ArbolV Q R Y),
    (cortar d t A).pasos O ≤ t
  | 0, .hoja y => by simp [cortar, pasos]
  | 0, .preg q sig => by simp [cortar, pasos]
  | t + 1, .hoja y => by simp [cortar, pasos]
  | t + 1, .preg q sig => by
      simp only [cortar, pasos]; have := cortar_pasos d O t (sig (O q)); omega

theorem cortar_corre {Q R Y : Type} (d : Y) (O : Q → R) : ∀ (t : ℕ) (A : ArbolV Q R Y),
    A.pasos O ≤ t → (cortar d t A).corre O = A.corre O
  | 0, .hoja y, _ => by simp [cortar, corre]
  | 0, .preg q sig, h => by simp [pasos] at h
  | t + 1, .hoja y, _ => by simp [cortar, corre]
  | t + 1, .preg q sig, h => by
      simp only [cortar, corre]
      simp only [pasos] at h
      exact cortar_corre d O t (sig (O q)) (by omega)

/-- **Encadenar**: correr `A` y seguir con `k` aplicado a lo que devuelve. -/
def ligar {Q R Y Z : Type} : ArbolV Q R Y → (Y → ArbolV Q R Z) → ArbolV Q R Z
  | .hoja y, k => k y
  | .preg q sig, k => .preg q fun r => ligar (sig r) k

theorem ligar_corre {Q R Y Z : Type} (O : Q → R) (k : Y → ArbolV Q R Z) :
    ∀ A : ArbolV Q R Y, (ligar A k).corre O = (k (A.corre O)).corre O
  | .hoja _ => rfl
  | .preg q sig => by simp only [ligar, corre]; exact ligar_corre O k (sig (O q))

theorem ligar_pasos {Q R Y Z : Type} (O : Q → R) (k : Y → ArbolV Q R Z) :
    ∀ A : ArbolV Q R Y, (ligar A k).pasos O = A.pasos O + (k (A.corre O)).pasos O
  | .hoja _ => by simp [ligar, pasos, corre]
  | .preg q sig => by
      simp only [ligar, pasos, corre]; rw [ligar_pasos O k (sig (O q))]; omega

/-- **La búsqueda universal en la caja**: probar los árboles de la lista uno tras otro, cada uno cortado a `t`
consultas, y verificar su salida con una consulta más. -/
def universal {Y : Type} (d : Y) (t : ℕ) : List (ArbolV Y Bool Y) → ArbolV Y Bool Y
  | [] => .hoja d
  | A :: As => ligar (cortar d t A) fun o => .preg o fun b => if b then .hoja o else universal d t As

theorem universal_halla {Y : Type} [DecidableEq Y] (d y : Y) (t : ℕ) : ∀ As : List (ArbolV Y Bool Y),
    (∃ A ∈ As, A.corre (igual y) = y ∧ A.pasos (igual y) ≤ t) →
    (universal d t As).corre (igual y) = y ∧ (universal d t As).pasos (igual y) ≤ As.length * (t + 1)
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | A :: As, ⟨B, hB, hBy, hBt⟩ => by
      have hc := cortar_pasos d (igual y) t A
      simp only [universal]
      rw [ligar_corre, ligar_pasos]
      set o := (cortar d t A).corre (igual y) with ho
      by_cases hoy : o = y
      · have hv : igual y o = true := by simp [igual, hoy]
        simp only [corre, pasos, hv, ite_true, List.length_cons]
        exact ⟨hoy, by nlinarith⟩
      · have hv : igual y o = false := by simp [igual, hoy]
        have hBA : B ∈ As := by
          rcases List.mem_cons.1 hB with h | h
          · subst h; exact absurd (by rw [ho, cortar_corre d _ t B hBt, hBy]) hoy
          · exact h
        obtain ⟨h1, h2⟩ := universal_halla d y t As ⟨B, hBA, hBy, hBt⟩
        simp only [corre, pasos, hv, Bool.false_eq_true, ite_false, List.length_cons]
        refine ⟨h1, ?_⟩
        nlinarith

/-- **Levin dentro de la caja**: un resolvedor con programas `P` en tiempo `t` se vuelve un resolvedor con **un solo
programa** (la búsqueda universal) en tiempo `|P| · (t + 1)`, con la misma cita. -/
theorem levin_caja {P C Y : Type} [Fintype P] [DecidableEq Y] (d : Y) {t : ℕ} (A : P → C → ArbolV Y Bool Y)
    (h : Resuelve igual A t) :
    Resuelve (P := Unit) igual
      (fun _ c => universal d t ((Finset.univ : Finset P).toList.map fun p => A p c))
      (Fintype.card P * (t + 1)) := by
  intro y
  obtain ⟨p, c, hp⟩ := h y
  refine ⟨(), c, ?_⟩
  have := universal_halla d y t ((Finset.univ : Finset P).toList.map fun p => A p c)
    ⟨A p c, List.mem_map.2 ⟨p, Finset.mem_toList.2 (Finset.mem_univ p), rfl⟩, hp⟩
  rwa [List.length_map, Finset.length_toList, Finset.card_univ] at this

/-- **La tasa de cambio, del otro lado**: borrar `L` bits de programa cuesta a lo sumo un factor `2^L` en tiempo:
`t' + 1 ≤ 2^L · (t + 1) + 1` con `L' = 0`. Y la ley dice que, con un solo programa, `N ≤ 2^s · (t' + 1)`: el
factor no se puede evitar en general (la solución en el programa, `solucion_programa`, lo exige entero). -/
theorem levin_caja_ley {P C Y : Type} [Fintype P] [Fintype C] [Fintype Y] [DecidableEq Y] (d : Y) {L s t : ℕ}
    (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (A : P → C → ArbolV Y Bool Y)
    (h : Resuelve igual A t) :
    Fintype.card P * (t + 1) ≤ 2 ^ L * (t + 1) ∧
      Fintype.card Y ≤ 2 ^ 0 * 2 ^ s * (Fintype.card P * (t + 1) + 1) :=
  ⟨Nat.mul_le_mul_right _ hP, ley_si_no (P := Unit) (by simp) hC _ (levin_caja d A h)⟩

/-- **De la cota de Levin a bits**: si un costo es menor que `8 · 2^i · k`, en bits es a lo sumo `i + ⌈log₂ k⌉ + 3`. -/
theorem bits_de_cota {c i k : ℕ} (h : c < 8 * 2 ^ i * k) : Nat.clog 2 c ≤ i + Nat.clog 2 k + 3 := by
  apply Nat.clog_le_of_le_pow
  have h2 : 8 * 2 ^ i * k ≤ 2 ^ (i + Nat.clog 2 k + 3) := by
    rw [pow_add, pow_add]
    have := Nat.le_pow_clog one_lt_two k
    calc 8 * 2 ^ i * k ≤ 8 * 2 ^ i * 2 ^ Nat.clog 2 k := by gcongr
      _ = 2 ^ i * 2 ^ Nat.clog 2 k * 2 ^ 3 := by ring
  omega

open Sagitta.Map.Levin Sagitta.Map.Tiempo.CorteRacional in
/-- **Levin en bits** (con `Levin.lean` y `CorteRacional.lean`): si el programa número `i` resuelve `x` con
presupuesto `k ≥ 1`, el costo de la búsqueda universal, en bits, es a lo sumo la descripción `i` del programa imitado
más el tiempo de ese programa en bits más 3. La descripción se paga como factor `2^i` en el tiempo: la tasa de cambio
de la ley, `2^L`, alcanzada del otro lado. La medida es presupuesto de `evaln`, no consultas a una caja negra. -/
theorem levin_en_bits {V : ℕ → ℕ → Bool} {x i k y : ℕ} (hk : 1 ≤ k) (h : correr i k x = some y)
    (hV : V x y = true) : Nat.clog 2 (costoLevin V x) ≤ i + Nat.clog 2 k + 3 :=
  bits_de_cota (costoLevin_le hk h hV)

open Sagitta.Map.Levin Sagitta.Map.Tiempo.CorteRacional in
/-- **Toda la escalera, en bits** (`levin_bajo_escalera`): para todo peldaño `k`, el costo de la búsqueda en bits es
a lo sumo `i_k + ⌈log₂ t_k(x)⌉ + 3`. Cada peldaño paga su descripción `i_k` en bits de tiempo. -/
theorem levin_escalera_en_bits {V : ℕ → ℕ → Bool} {i : ℕ → ℕ} {t : ℕ → ℕ → ℕ} (ht1 : ∀ k x, 1 ≤ t k x)
    (hres : ∀ k x, ∃ y, correr (i k) (t k x) x = some y ∧ V x y = true) (k x : ℕ) :
    Nat.clog 2 (costoLevin V x) ≤ i k + Nat.clog 2 (t k x) + 3 :=
  bits_de_cota (levin_bajo_escalera ht1 hres k x)

/-! ## 5. Mutantes refutados -/

/-- **Sin el `+1`** (`N ≤ 2^L · 2^s · t`) es falso: con una sola instancia, la hoja la resuelve en `t = 0`. -/
theorem mutante_sin_uno :
    ¬ ∀ (A : Unit → Unit → ArbolV (Fin 1) Bool (Fin 1)) (t : ℕ), Resuelve igual A t →
      Fintype.card (Fin 1) ≤ 2 ^ 0 * 2 ^ 0 * t := by
  intro h
  have := h (fun _ _ => .hoja 0) 0 fun y => ⟨(), (), by simp [corre, pasos, Subsingleton.elim y 0]⟩
  simp at this

/-- **Sin la cita** (`N ≤ 2^L · (t+1)`) es falso: el certificado como cita resuelve 4 instancias en `t = 0`. -/
theorem mutante_sin_cita :
    ¬ ∀ (A : Unit → Fin 4 → ArbolV (Fin 4) Bool (Fin 4)) (t : ℕ), Resuelve igual A t →
      Fintype.card (Fin 4) ≤ 2 ^ 0 * (t + 1) := by
  intro h
  have := h (fun _ c => .hoja c) 0 fun y => ⟨(), y, by simp [corre, pasos]⟩
  simp at this

/-- **Con la cita fija** el certificado deja de funcionar: ninguna cita, la misma para las 4 instancias, hace que
verificar y devolver las resuelva. -/
theorem mutante_cita_fija :
    ¬ ∃ c : Fin 4, ∀ y : Fin 4, ∃ _p : Unit,
      (verificarYDevolver c).corre (igual y) = y ∧ (verificarYDevolver c).pasos (igual y) ≤ 1 := by
  intro h
  have := cita_fija (P := Unit) (L := 0) (by simp) (fun _ c => verificarYDevolver c) h
  simp at this

/-- **`2^t` en vez de `t+1` para el verificador de igualdad** es falso: ningún resolvedor sin programa ni cita halla
4 soluciones en 2 consultas de sí o no (la ley da `4 ≤ 3`), aunque `4 = 2^2`. -/
theorem mutante_si_no_bt (A : Unit → Unit → ArbolV (Fin 4) Bool (Fin 4)) : ¬ Resuelve igual A 2 := by
  intro h
  have := ley_si_no (L := 0) (s := 0) (by simp) (by simp) A h
  simp at this

/-- **`t+1` para un verificador de sí o no cualquiera** es falso: el de bloques de un bit halla `2^t` soluciones en
`t` consultas, y con `t = 2` eso da 4 > 3. El `t+1` es del verificador de igualdad; uno de sí o no general solo cumple
`2^t` (`ley` con `b = 1`). -/
theorem mutante_t_mas_uno_general :
    ¬ ∀ (A : Unit → Unit → ArbolV (Fin 2) (Fin (2 ^ 1)) (Fin 2 → Fin (2 ^ 1))),
      Resuelve bloque A 2 → Fintype.card (Fin 2 → Fin (2 ^ 1)) ≤ 2 ^ 0 * 2 ^ 0 * (2 + 1) := by
  intro h
  have := h _ (bloques_alcanza 2 1)
  simp at this

/-- **`t` en vez de `⌈log₂(t+1)⌉`** en la forma en bits no es falso, es más débil: `⌈log₂ N⌉ ≤ L + s + t` se cumple,
pero la fuerza bruta (`t = N − 1`) queda lejísimos de esa recta. -/
theorem ley_lineal {P C Y : Type} [Fintype P] [Fintype C] [Fintype Y] [DecidableEq Y] {L s t : ℕ}
    (hP : Fintype.card P ≤ 2 ^ L) (hC : Fintype.card C ≤ 2 ^ s) (A : P → C → ArbolV Y Bool Y)
    (h : Resuelve igual A t) : Nat.clog 2 (Fintype.card Y) ≤ L + s + t := by
  have := ley_si_no_log hP hC A h
  have : Nat.clog 2 (t + 1) ≤ t := Nat.clog_le_of_le_pow Nat.lt_two_pow_self
  omega

end Sagitta.Map.Tiempo.LeyTresMemorias
