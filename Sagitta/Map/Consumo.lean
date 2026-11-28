import Sagitta.Map.Landau
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.MeasureTheory.Measure.Count

/-!
# El recurso decide: la topología del consumo del tiempo

`FormaDelTiempo.lean` dio la **forma** del tiempo: una línea si el paso es función, un árbol si es relación. Aquí va lo
que cuesta **recorrer** ese árbol con una máquina que no adivina, según el recurso que se mida.

**El álgebra.** Recorrer un árbol en profundidad (primero la rama izquierda entera, después la derecha) visita cada nodo
una vez. Lo que cuesta un nodo con dos ramas es `1 + (costo de la izquierda) ⊕ (costo de la derecha)`, y el recurso
decide qué es `⊕` (`costo`):

* el **tiempo** se gasta: las dos ramas se pagan, `⊕ = +` (`tiempo`);
* el **espacio** se recicla: la segunda rama corre en la memoria que soltó la primera, `⊕ = max` (`espacio`).

La diferencia es una sola ley: `max a a = a` (idempotente) y `a + a = 2a`. Sobre el árbol completo de `n` elecciones
binarias, un recurso idempotente cuesta `n + 1` (`costo_idempotente`) y uno que se suma cuesta al menos `2^(n+1) − 1`
(`costo_aditivo`). En la escala de Landau: el espacio queda en `Pol` (`espacio_completo_pol`), el tiempo escapa de toda
`O(K)` polinomial (`tiempo_completo_escapa`). Duplicar un árbol (`dup`) le suma un renglón al espacio y le dobla el
tiempo (`espacio_dup`, `tiempo_dup`).

**Las dos cotas que valen siempre** (`espacio_le_tiempo`, `tiempo_lt_dos_pow_espacio`):
`espacio ≤ tiempo < 2^espacio`. Son la versión en árbol de `P ⊆ PSPACE ⊆ EXP`, y el árbol completo las alcanza las dos:
no hay cota mejor que valga para **todo** árbol. P contra NP pregunta si los árboles que vienen de problemas de NP tienen
atajo, y eso esta cuenta no lo dice.

**La topología.** Un recurso a lo largo de una corrida es una función `uso : ℕ → ℕ` (paso ↦ cuánto se lleva). Se dota a
la flecha del tiempo y a la escala de la **topología de conjuntos superiores** (la de Alexandrov: abierto = cerrado hacia
arriba, «lo que ya pasó no se deshace»). Entonces:

* un recurso se **consume** si y solo si su uso es **continuo** en esa topología (`consumido_iff_continuo`, que es
  monotonía, por Mathlib);
* el reloj es continuo (`reloj_consumido`); la pila del recorrido no lo es (`pila_no_consumida`): sube y baja;
* de un recurso consumido, el total es lo último que marca (`consumido_total`); de uno reciclado, el total es el pico,
  que puede quedar atrás (`pila_pico_atras`).

La traza del recorrido (`traza`) es la pila paso a paso: mide `tiempo` de largo (`length_traza`) y su máximo es el
`espacio` (`le_espacio_de_mem_traza`, `espacio_mem_traza`). Las dos medidas salen de la **misma** corrida, leída con dos
topologías.

**Lo que no está.** Savitch (el árbol de configuraciones de una máquina de espacio `s` se recorre en espacio `s²` sin
escribirlo) necesita un paso, no un árbol dado: está en `Savitch.lean`. Las corridas de árboles de problemas de NP
están en `ConsumoNP.lean`, y Ω entero, con su medida producto, en `ConsumoOmega.lean`. `costo_idempotente`, `costo_aditivo` y
`existe_rama_espacio` usan solo `propext` y `Quot.sound`; lo demás arrastra `Classical.choice` de las bibliotecas de
Mathlib (aritmética con `max`, topología, medida), no de la idea.

**Ω, el espacio de medida** (idea de José). Las ramas (`ramas`) son el espacio muestral Ω, que es el de las corridas de
`FormaDelTiempo.lean` cortado en el tiempo `n`. El tiempo es una medida **aditiva** sobre Ω (la de conteo; la masa de Ω
es `2ⁿ`: `length_ramas_completo`, y con la de Mathlib, `medida_omega`) y el espacio, una **maxitiva** (el supremo de
los largos de rama: `largo_le_espacio`, `existe_rama_espacio`). La cota inferior `Ω(2ⁿ)` de Landau es la masa de Ω para
la medida aditiva: el adversario de `Decidir.lean` obliga a pagar Ω entero.
-/

namespace Sagitta.Map
namespace Consumo

open Tiempo

/-- El árbol de elecciones binarias: una hoja, o un paso con dos continuaciones. -/
inductive Arbol
  | hoja
  | nodo (l r : Arbol)
  deriving DecidableEq

namespace Arbol

/-- Lo que cuesta recorrer el árbol entero cuando las dos ramas se combinan con `op`. Cada nodo paga `1`. -/
def costo (op : ℕ → ℕ → ℕ) : Arbol → ℕ
  | hoja => 1
  | nodo l r => 1 + op (costo op l) (costo op r)

/-- **Tiempo**: las dos ramas se pagan. Es el número de nodos. -/
def tiempo : Arbol → ℕ := costo (· + ·)

/-- **Espacio**: la segunda rama reusa la memoria de la primera. Es la profundidad (la pila más alta). -/
def espacio : Arbol → ℕ := costo max

/-- El árbol completo de `n` elecciones binarias. -/
def completo : ℕ → Arbol
  | 0 => hoja
  | n + 1 => nodo (completo n) (completo n)

/-- Duplicar: una elección más arriba, con las dos ramas iguales. -/
def dup (t : Arbol) : Arbol := nodo t t

@[simp] theorem tiempo_hoja : tiempo hoja = 1 := rfl
@[simp] theorem tiempo_nodo (l r : Arbol) : tiempo (nodo l r) = 1 + tiempo l + tiempo r := by
  simp [tiempo, costo, Nat.add_assoc]
@[simp] theorem espacio_hoja : espacio hoja = 1 := rfl
@[simp] theorem espacio_nodo (l r : Arbol) : espacio (nodo l r) = 1 + max (espacio l) (espacio r) := rfl

theorem completo_succ (n : ℕ) : completo (n + 1) = dup (completo n) := rfl

/-! ## La ley que separa: idempotente o aditivo -/

/-- **Lo que se recicla.** Si combinar dos ramas iguales no cuesta más que una (`op a a = a`), el árbol completo de `n`
elecciones cuesta `n + 1`: lineal en las elecciones. -/
theorem costo_idempotente {op : ℕ → ℕ → ℕ} (h : ∀ a, op a a = a) (n : ℕ) :
    costo op (completo n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [completo, costo, h, ih]; omega

/-- **Lo que se consume.** Si combinar dos ramas iguales cuesta al menos las dos (`2a ≤ op a a`), el árbol completo de
`n` elecciones cuesta al menos `2^(n+1) − 1`: exponencial en las elecciones. -/
theorem costo_aditivo {op : ℕ → ℕ → ℕ} (h : ∀ a, 2 * a ≤ op a a) (n : ℕ) :
    2 ^ (n + 1) ≤ costo op (completo n) + 1 := by
  induction n with
  | zero => simp [completo, costo]
  | succ n ih =>
    have := h (costo op (completo n))
    simp only [completo, costo]
    rw [pow_succ]
    omega

theorem espacio_completo (n : ℕ) : espacio (completo n) = n + 1 :=
  costo_idempotente (fun a => max_self a) n

theorem tiempo_completo (n : ℕ) : tiempo (completo n) + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [completo, tiempo_nodo]
    rw [pow_succ]
    omega

/-- El tiempo es la instancia aditiva: la cota de `costo_aditivo` es justa. -/
example (n : ℕ) : 2 ^ (n + 1) ≤ tiempo (completo n) + 1 := costo_aditivo (fun a => by omega) n

/-- Duplicar le suma un renglón al espacio... -/
theorem espacio_dup (t : Arbol) : espacio (dup t) = espacio t + 1 := by
  simp [dup, Nat.add_comm]

/-- ...y le dobla el tiempo. -/
theorem tiempo_dup (t : Arbol) : tiempo (dup t) = 2 * tiempo t + 1 := by
  simp [dup]; omega

/-- Duplicar `k` veces: el espacio crece en `k`. -/
theorem espacio_iterate_dup (t : Arbol) (k : ℕ) : espacio (dup^[k] t) = espacio t + k := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, espacio_dup]; omega

/-- Duplicar `k` veces: el tiempo se multiplica por `2^k`. -/
theorem tiempo_iterate_dup (t : Arbol) (k : ℕ) : tiempo (dup^[k] t) + 1 = 2 ^ k * (tiempo t + 1) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, tiempo_dup, pow_succ]
    ring

/-! ## En la escala de Landau -/

/-- El espacio de recorrer `n` elecciones es polinomial (lineal). -/
theorem espacio_completo_pol : (fun n => espacio (completo n)) ∈ Pol :=
  ⟨1, 1, fun n => by simp [espacio_completo]⟩

/-- El tiempo de recorrer `n` elecciones no es polinomial. -/
theorem tiempo_completo_no_pol : (fun n => tiempo (completo n)) ∉ Pol := by
  rintro ⟨c, k, hc⟩
  obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
  have h1 : tiempo (completo N) ≤ c * (N + 1) ^ k := hc N
  have h2 := tiempo_completo N
  have h3 := hN N le_rfl
  have h4 : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
  have h5 := Nat.one_le_two_pow (n := N)
  omega

/-- Ni siquiera está en `O(K)` para ningún `K` polinomial. -/
theorem tiempo_completo_escapa : ∀ K ∈ Pol, (fun n => tiempo (completo n)) ∉ O K := by
  intro K hK hO
  apply tiempo_completo_no_pol
  obtain ⟨C, N, hCN⟩ := hO
  obtain ⟨c, k, hc⟩ := hK
  -- Debajo de `N` hay finitos valores; encima, la cota `C·K`.
  refine ⟨C * c + ∑ i ∈ Finset.range N, tiempo (completo i), k, fun n => ?_⟩
  have hpow := one_le_succ_pow n k
  by_cases hn : N ≤ n
  · calc tiempo (completo n) ≤ C * K n := hCN n hn
      _ ≤ C * (c * (n + 1) ^ k) := Nat.mul_le_mul_left _ (hc n)
      _ ≤ (C * c + ∑ i ∈ Finset.range N, tiempo (completo i)) * (n + 1) ^ k := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · have : tiempo (completo n) ≤ ∑ i ∈ Finset.range N, tiempo (completo i) :=
      Finset.single_le_sum (f := fun i => tiempo (completo i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (by omega))
    calc tiempo (completo n) ≤ (C * c + ∑ i ∈ Finset.range N, tiempo (completo i)) * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hpow

/-! ## Las dos cotas que valen para todo árbol -/

theorem uno_le_espacio (t : Arbol) : 1 ≤ espacio t := by
  cases t <;> simp

/-- Lo que se recorre en tiempo `T` cabe en espacio `T` (`P ⊆ PSPACE`, en árbol). -/
theorem espacio_le_tiempo (t : Arbol) : espacio t ≤ tiempo t := by
  induction t with
  | hoja => rfl
  | nodo l r ihl ihr => simp only [espacio_nodo, tiempo_nodo]; omega

/-- Lo que cabe en espacio `S` se recorre en tiempo menor que `2^S` (`PSPACE ⊆ EXP`, en árbol). -/
theorem tiempo_lt_dos_pow_espacio (t : Arbol) : tiempo t < 2 ^ espacio t := by
  induction t with
  | hoja => simp
  | nodo l r ihl ihr =>
    simp only [espacio_nodo, tiempo_nodo]
    have hl : 2 ^ espacio l ≤ 2 ^ max (espacio l) (espacio r) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hr : 2 ^ espacio r ≤ 2 ^ max (espacio l) (espacio r) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    rw [show 1 + max (espacio l) (espacio r) = max (espacio l) (espacio r) + 1 by omega, pow_succ]
    omega

/-- El árbol completo alcanza las dos cotas: ninguna se mejora para **todo** árbol. -/
theorem completo_alcanza (n : ℕ) :
    espacio (completo n) = n + 1 ∧ tiempo (completo n) + 1 = 2 ^ espacio (completo n) :=
  ⟨espacio_completo n, by rw [espacio_completo]; exact tiempo_completo n⟩

/-- Y el camino (una sola rama por paso) alcanza la de abajo: tiempo = espacio. -/
def camino : ℕ → Arbol
  | 0 => hoja
  | n + 1 => nodo (camino n) hoja

theorem camino_alcanza (n : ℕ) : tiempo (camino n) = 2 * n + 1 ∧ espacio (camino n) = n + 1 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [camino, tiempo_nodo, tiempo_hoja, h1]; omega
    · simp only [camino, espacio_nodo, espacio_hoja, h2]; omega

/-! ## La traza: una corrida, dos lecturas -/

/-- La pila del recorrido en profundidad, paso a paso: la altura en cada nodo visitado. -/
def traza : Arbol → List ℕ
  | hoja => [1]
  | nodo l r => 1 :: ((traza l).map (· + 1) ++ (traza r).map (· + 1))

/-- La traza dura lo que el tiempo. -/
theorem length_traza (t : Arbol) : (traza t).length = tiempo t := by
  induction t with
  | hoja => rfl
  | nodo l r ihl ihr => simp [traza, ihl, ihr]; omega

/-- Ninguna altura de la pila pasa del espacio. -/
theorem le_espacio_de_mem_traza (t : Arbol) : ∀ h ∈ traza t, h ≤ espacio t := by
  induction t with
  | hoja => simp [traza]
  | nodo l r ihl ihr =>
    intro h hh
    simp only [traza, List.mem_cons, List.mem_append, List.mem_map] at hh
    simp only [espacio_nodo]
    rcases hh with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · omega
    · have := ihl a ha; omega
    · have := ihr a ha; omega

/-- Y el espacio se alcanza: es la altura máxima de la pila. -/
theorem espacio_mem_traza (t : Arbol) : espacio t ∈ traza t := by
  induction t with
  | hoja => simp [traza]
  | nodo l r ihl ihr =>
    simp only [traza, espacio_nodo, List.mem_cons, List.mem_append, List.mem_map]
    right
    rcases le_total (espacio r) (espacio l) with h | h
    · left; exact ⟨espacio l, ihl, by omega⟩
    · right; exact ⟨espacio r, ihr, by omega⟩

/-! ## Ω: el espacio de las ramas, con dos medidas

Las ramas del árbol (`ramas`, una por hoja, cada una la lista de elecciones) son el espacio muestral Ω. Sobre él, el
tiempo se comporta como una medida **aditiva** (la de conteo: `length_ramas_le_tiempo`, y en el árbol completo
`length_ramas_completo`, la masa de Ω es `2ⁿ`) y el espacio, como una medida **maxitiva**: el supremo del largo de las
ramas (`largo_le_espacio`, `existe_rama_espacio`). La cota inferior `Ω(2ⁿ)` de Landau es la masa de Ω para la medida
aditiva: recorrer sin adivinar obliga a pagar Ω entero. -/

/-- Las ramas: cada hoja, con las elecciones que llevan a ella. -/
def ramas : Arbol → List (List Bool)
  | hoja => [[]]
  | nodo l r => (ramas l).map (false :: ·) ++ (ramas r).map (true :: ·)

/-- **Lo aditivo**: el tiempo paga al menos una vez cada rama, `μ(Ω) ≤ tiempo`. -/
theorem length_ramas_le_tiempo (t : Arbol) : (ramas t).length ≤ tiempo t := by
  induction t with
  | hoja => rfl
  | nodo l r ihl ihr => simp [ramas]; omega

/-- En el árbol completo, la masa de Ω es `2ⁿ`. -/
theorem length_ramas_completo (n : ℕ) : (ramas (completo n)).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [completo, ramas, ih, pow_succ]; ring

/-- **Lo maxitivo**: ninguna rama necesita más pila que el espacio... -/
theorem largo_le_espacio (t : Arbol) : ∀ b ∈ ramas t, b.length + 1 ≤ espacio t := by
  induction t with
  | hoja => simp [ramas]
  | nodo l r ihl ihr =>
    intro b hb
    simp only [ramas, List.mem_append, List.mem_map] at hb
    simp only [espacio_nodo]
    rcases hb with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · have := ihl a ha; simp; omega
    · have := ihr a ha; simp; omega

/-- ...y alguna la necesita toda: el espacio es el supremo sobre Ω, no la suma. -/
theorem existe_rama_espacio (t : Arbol) : ∃ b ∈ ramas t, b.length + 1 = espacio t := by
  induction t with
  | hoja => exact ⟨[], by simp [ramas], rfl⟩
  | nodo l r ihl ihr =>
    obtain ⟨bl, hbl, el⟩ := ihl
    obtain ⟨br, hbr, er⟩ := ihr
    rcases le_total (espacio r) (espacio l) with h | h
    · exact ⟨false :: bl, by simp [ramas, hbl], by simp; omega⟩
    · exact ⟨true :: br, by simp [ramas, hbr], by simp; omega⟩

end Arbol

/-! ## La topología del consumo

La flecha del tiempo `ℕ` y la escala de un recurso `ℕ` llevan la topología de conjuntos superiores: un abierto es un
conjunto cerrado hacia arriba. Un instante abierto contiene todo su futuro. -/

open Topology

/-- El uso de un recurso a lo largo de una corrida, visto entre las dos topologías de conjuntos superiores. -/
def comoFlecha (uso : ℕ → ℕ) : WithUpperSet ℕ → WithUpperSet ℕ :=
  WithUpperSet.toUpperSet ∘ uso ∘ WithUpperSet.ofUpperSet

/-- Un recurso **se consume** en una corrida si lo que lleva gastado nunca baja. -/
def Consumido (uso : ℕ → ℕ) : Prop := Monotone uso

/-- **Consumirse es ser continuo** en la topología de la flecha del tiempo. -/
theorem consumido_iff_continuo (uso : ℕ → ℕ) : Consumido uso ↔ Continuous (comoFlecha uso) := by
  rw [← Topology.IsUpperSet.monotone_iff_continuous]
  rfl

/-- El reloj: tras `k` pasos se llevan `k` pasos gastados. Se consume. -/
theorem reloj_consumido : Consumido id := monotone_id

theorem reloj_continuo : Continuous (comoFlecha id) := (consumido_iff_continuo id).1 reloj_consumido

/-- De un recurso consumido, el total es lo último que marca: nada de lo gastado vuelve. -/
theorem consumido_total {uso : ℕ → ℕ} (h : Consumido uso) (n : ℕ) :
    (Finset.range (n + 1)).sup uso = uso n :=
  le_antisymm (Finset.sup_le fun _ hk => h (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
    (Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_self n)))

open Arbol in
/-- La pila del recorrido del árbol completo de dos elecciones: `1, 2, 3, 3, 2, 3, 3`. -/
def pila (k : ℕ) : ℕ := (traza (completo 2)).getD k 0

theorem traza_completo_dos : Arbol.traza (Arbol.completo 2) = [1, 2, 3, 3, 2, 3, 3] := rfl

/-- **La pila no se consume**: baja de 3 a 2 al pasar de la rama izquierda a la derecha. -/
theorem pila_no_consumida : ¬ Consumido pila := fun h => by
  have := h (show 3 ≤ 4 by norm_num)
  simp [pila, traza_completo_dos] at this

theorem pila_no_continua : ¬ Continuous (comoFlecha pila) :=
  fun hc => pila_no_consumida ((consumido_iff_continuo pila).2 hc)

/-- De la pila, el total (el pico) puede quedar atrás: en el paso 4 marca 2, pero ya se usaron 3. -/
theorem pila_pico_atras : pila 4 < (Finset.range 5).sup pila := by
  decide

/-- Con la medida de conteo de Mathlib sobre las corridas de `n` elecciones, `Ω` pesa `2ⁿ`. -/
theorem medida_omega (n : ℕ) :
    MeasureTheory.Measure.count (Set.univ : Set (Fin n → Bool)) = 2 ^ n := by
  rw [MeasureTheory.Measure.count_univ]
  simp [ENat.card_eq_coe_fintype_card]

end Consumo
end Sagitta.Map
