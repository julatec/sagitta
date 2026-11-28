import Sagitta.Map.Savitch
import Sagitta.Map.ConsumoNP
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# La alternancia: el árbol de juego

`Consumo.lean` separó dos maneras de pagar un árbol: el tiempo determinista **suma** las ramas y la memoria toma el
**máximo**. Una máquina no determinista elige con «existe»; una **alternante** también con «para todo»: el árbol de
elecciones se vuelve un **juego** (`Juego`), con nodos de los dos jugadores. Acepta si el jugador «existe» tiene
estrategia ganadora (`valor`).

## El tiempo alternante es maxitivo

El tiempo de una máquina alternante es el largo de la jugada más larga: una medida **maxitiva** sobre las ramas del
juego, como la memoria de `Consumo.lean`. Con elecciones binarias, elegir entre `n` opciones cuesta `⌈log₂ n⌉` pasos, así
que el tiempo alternante es la profundidad ponderada (`prof`). El tiempo determinista de evaluar el juego mira las hojas,
y esas son una medida **aditiva** (`hojas`).

## Las dos inclusiones

* **APTIME ⊆ PSPACE, en árbol.** Recorrer el juego en profundidad guarda, por marco, el índice de la opción que se está
  probando: `⌈log₂ n⌉` bits. La pila más alta es la rama más pesada: es `prof`, la misma medida que el tiempo alternante.
  Sobre los árboles binarios de `Consumo.lean`, con **cualquier** reparto de jugadores (`jugarArbol`), el tiempo
  alternante es el espacio del recorrido que allá se definió por separado (`prof_jugarArbol`), y las hojas no dependen de
  quién juega (`hojas_jugarArbol`).
  El tiempo determinista, en cambio, paga todas las hojas, y son a lo sumo `2^prof` (`hojas_le_dos_pow_prof`): es
  `APTIME(t) ⊆ DTIME(2^t)`, la cota de `Consumo.tiempo_lt_dos_pow_espacio` para juegos.
* **PSPACE ⊆ APTIME: Savitch se juega** (`juegoSav`). En `alc` de `Savitch.lean`, cada nivel prueba un punto medio `w`
  **y** pregunta por las dos mitades. En el juego, «existe» propone `w` y «para todo» escoge **una** mitad
  (`valor_juegoSav`: se gana si y solo si `alc`). La recursión deja de bifurcarse: el juego tiene `(2n)^i` hojas
  (`hojas_juegoSav`), pero su profundidad ponderada es `i · (⌈log₂ n⌉ + 1)` (`prof_juegoSav`). Con `2^s` configuraciones
  y `i = s`, el tiempo alternante es `s(s + 1)` (`savitch_alternante`): lo que se decide en espacio `s` se decide en
  tiempo alternante `O(s²)`.

El «y» de Savitch suma las dos mitades (tiempo determinista); el «para todo» toma el máximo (tiempo alternante). Es la
misma ley de `Consumo.lean`, otra vez: lo que el adversario elige se paga como memoria, no como tiempo.

## Lo que no

* No hay máquina alternante: el juego es el árbol, y `prof` es el modelo de costo. La pila del recorrido en profundidad
  se lee con el mismo modelo de marcos de `Consumo.lean` y `Savitch.lean`, no como casillas de una cinta.
* Las estrategias como objetos (subárboles con una opción en cada nodo «existe»): aquí `valor` las resume.
-/

namespace Sagitta.Map
namespace Tiempo

/-- **Un juego**: una hoja con su resultado, o un nodo de `n` opciones del jugador «existe» o del jugador «para todo». -/
inductive Juego
  | hoja (b : Bool)
  | existe (n : ℕ) (f : Fin n → Juego)
  | todo (n : ℕ) (f : Fin n → Juego)

namespace Juego

/-- **Gana «existe»**: hay estrategia ganadora. -/
def valor : Juego → Bool
  | hoja b => b
  | existe n f => (List.finRange n).any fun i => valor (f i)
  | todo n f => (List.finRange n).all fun i => valor (f i)

theorem valor_existe (n : ℕ) (f : Fin n → Juego) : valor (existe n f) = true ↔ ∃ i, valor (f i) = true := by
  simp [valor]

theorem valor_todo (n : ℕ) (f : Fin n → Juego) : valor (todo n f) = true ↔ ∀ i, valor (f i) = true := by
  simp [valor]

/-- **El tiempo alternante**: la jugada más larga, con `⌈log₂ n⌉` pasos por elegir entre `n` opciones. Maxitivo. -/
def prof : Juego → ℕ
  | hoja _ => 0
  | existe n f => Nat.clog 2 n + Finset.univ.sup fun i => prof (f i)
  | todo n f => Nat.clog 2 n + Finset.univ.sup fun i => prof (f i)

/-- **Las hojas**: lo que paga el tiempo determinista en el peor caso. Aditivo. -/
def hojas : Juego → ℕ
  | hoja _ => 1
  | existe _ f => ∑ i, hojas (f i)
  | todo _ f => ∑ i, hojas (f i)

theorem suma_le_dos_pow {n : ℕ} (g : Fin n → ℕ) (p : Fin n → ℕ) (h : ∀ i, g i ≤ 2 ^ p i) :
    ∑ i, g i ≤ 2 ^ (Nat.clog 2 n + Finset.univ.sup p) := by
  calc ∑ i, g i ≤ ∑ _i : Fin n, 2 ^ (Finset.univ.sup p) :=
        Finset.sum_le_sum fun i _ => (h i).trans
          (Nat.pow_le_pow_right (by norm_num) (Finset.le_sup (Finset.mem_univ i)))
    _ = n * 2 ^ (Finset.univ.sup p) := by simp
    _ ≤ 2 ^ Nat.clog 2 n * 2 ^ (Finset.univ.sup p) :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) n)
    _ = _ := (pow_add _ _ _).symm

/-- **APTIME(t) ⊆ DTIME(2^t)**, en árbol: un juego de tiempo alternante `t` tiene a lo sumo `2^t` hojas. -/
theorem hojas_le_dos_pow_prof : ∀ g : Juego, hojas g ≤ 2 ^ prof g
  | hoja _ => by simp [hojas, prof]
  | existe n f => by
    simp only [hojas, prof]
    exact suma_le_dos_pow _ _ fun i => hojas_le_dos_pow_prof (f i)
  | todo n f => by
    simp only [hojas, prof]
    exact suma_le_dos_pow _ _ fun i => hojas_le_dos_pow_prof (f i)

/-- Un juego de puros «existe» binarios es un árbol de elecciones de NP: el tiempo alternante es la profundidad. -/
def soloExiste : ℕ → Juego
  | 0 => hoja false
  | k + 1 => existe 2 fun _ => soloExiste k

theorem prof_soloExiste (k : ℕ) : prof (soloExiste k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [soloExiste, prof, ih, Finset.sup_const Finset.univ_nonempty]
    rw [show Nat.clog 2 2 = 1 by decide]; omega

theorem hojas_soloExiste (k : ℕ) : hojas (soloExiste k) = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [soloExiste, hojas, ih, pow_succ]; ring

/-! ## El mismo árbol, jugado: tiempo alternante = espacio del recorrido -/

/-- Un árbol de `Consumo.lean` jugado: `quien p` dice si en el nodo de camino `p` elige «existe» (`true`) o «para todo»;
`res p` es el resultado en la hoja de camino `p`. -/
def jugarArbol (quien res : List Bool → Bool) : Consumo.Arbol → List Bool → Juego
  | .hoja, p => hoja (res p)
  | .nodo l r, p =>
    let f : Fin 2 → Juego := fun b => if b = 0 then jugarArbol quien res l (p ++ [false])
      else jugarArbol quien res r (p ++ [true])
    if quien p then existe 2 f else todo 2 f

theorem sup_fin_two (a b : ℕ) :
    (Finset.univ : Finset (Fin 2)).sup (fun x : Fin 2 => if x = 0 then a else b) = max a b := by
  rw [Fin.univ_succ]; simp

/-- **APTIME ⊆ PSPACE, en árbol**: con cualquier reparto de jugadores, el tiempo alternante del juego es el espacio
del recorrido en profundidad del árbol (`Consumo.Arbol.espacio`), menos la hoja. Las dos son la misma medida maxitiva. -/
theorem prof_jugarArbol (quien res : List Bool → Bool) :
    ∀ (t : Consumo.Arbol) (p : List Bool), prof (jugarArbol quien res t p) + 1 = t.espacio
  | .hoja, p => by simp [jugarArbol, prof]
  | .nodo l r, p => by
    have hl := prof_jugarArbol quien res l (p ++ [false])
    have hr := prof_jugarArbol quien res r (p ++ [true])
    have hc : Nat.clog 2 2 = 1 := by decide
    have key : ∀ (f : Fin 2 → Juego), f = (fun b => if b = 0 then jugarArbol quien res l (p ++ [false])
        else jugarArbol quien res r (p ++ [true])) →
        Nat.clog 2 2 + (Finset.univ.sup fun i => prof (f i)) + 1 = 1 + max l.espacio r.espacio := by
      rintro f rfl
      have : (fun i : Fin 2 => prof (if i = 0 then jugarArbol quien res l (p ++ [false])
          else jugarArbol quien res r (p ++ [true]))) =
          fun i : Fin 2 => if i = 0 then prof (jugarArbol quien res l (p ++ [false]))
            else prof (jugarArbol quien res r (p ++ [true])) := by
        funext i; split_ifs <;> rfl
      rw [this, sup_fin_two, hc]; omega
    simp only [jugarArbol, Consumo.Arbol.espacio_nodo]
    split_ifs <;> simp only [prof] <;> exact key _ rfl

/-- Y sus hojas son las del árbol: el tiempo determinista no depende de quién juega. -/
theorem hojas_jugarArbol (quien res : List Bool → Bool) :
    ∀ (t : Consumo.Arbol) (p : List Bool), hojas (jugarArbol quien res t p) = t.hojas
  | .hoja, p => by simp [jugarArbol, hojas, Consumo.Arbol.hojas]
  | .nodo l r, p => by
    have hl := hojas_jugarArbol quien res l (p ++ [false])
    have hr := hojas_jugarArbol quien res r (p ++ [true])
    simp only [jugarArbol, Consumo.Arbol.hojas]
    split_ifs <;> simp [hojas, Fin.sum_univ_two, hl, hr]

end Juego

/-! ## Savitch, jugado -/

open Juego

variable {C : Type*} (R : Paso C) [DecidableEq C] [∀ c d, Decidable (d ∈ R c)] {n : ℕ} (e : Fin n → C)

/-- **El juego de Savitch**: «existe» propone un punto medio `e j`; «para todo» escoge una mitad. -/
def juegoSav : ℕ → C → C → Juego
  | 0, u, v => hoja (decide (u = v ∨ v ∈ R u))
  | i + 1, u, v => existe n fun j => todo 2 fun b =>
      if b = 0 then juegoSav i u (e j) else juegoSav i (e j) v

/-- **Se gana si y solo si se llega**: el juego de Savitch vale lo que `alc`. -/
theorem valor_juegoSav [Fintype C] (he : Function.Surjective e) :
    ∀ (i : ℕ) (u v : C), valor (juegoSav R e i u v) = alc R i u v
  | 0, u, v => by simp [juegoSav, valor, alc]
  | i + 1, u, v => by
    rw [Bool.eq_iff_iff, alc]
    simp only [juegoSav, valor_existe, valor_todo, Fin.forall_fin_two, Fin.isValue, ite_true,
      show ((1 : Fin 2) = 0) = False by decide, ite_false, valor_juegoSav he i, decide_eq_true_eq]
    constructor
    · rintro ⟨j, h1, h2⟩; exact ⟨e j, h1, h2⟩
    · rintro ⟨w, h1, h2⟩
      obtain ⟨j, rfl⟩ := he w
      exact ⟨j, h1, h2⟩

/-- **El tiempo alternante de Savitch**: cada nivel elige un punto medio (`⌈log₂ n⌉` pasos) y una mitad (uno). No se
bifurca: es lineal en los niveles. -/
theorem prof_juegoSav (hn : 1 ≤ n) : ∀ (i : ℕ) (u v : C), prof (juegoSav R e i u v) = i * (Nat.clog 2 n + 1)
  | 0, u, v => by simp [juegoSav, prof]
  | i + 1, u, v => by
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩
    simp only [juegoSav, prof]
    have : ∀ j : Fin n, (Finset.univ : Finset (Fin 2)).sup (fun b : Fin 2 =>
        prof (if b = 0 then juegoSav R e i u (e j) else juegoSav R e i (e j) v)) = i * (Nat.clog 2 n + 1) := by
      intro j; rw [Fin.univ_succ]; simp [prof_juegoSav hn i]
    simp only [this, Finset.sup_const hne]
    rw [show Nat.clog 2 2 = 1 by decide]
    ring

/-- **El tiempo determinista de Savitch**: el juego tiene `(2n)^i` hojas. -/
theorem hojas_juegoSav : ∀ (i : ℕ) (u v : C), hojas (juegoSav R e i u v) = (2 * n) ^ i
  | 0, u, v => by simp [juegoSav, hojas]
  | i + 1, u, v => by
    have : ∀ j : Fin n, (∑ b : Fin 2,
        hojas (if b = 0 then juegoSav R e i u (e j) else juegoSav R e i (e j) v)) = 2 * (2 * n) ^ i := by
      intro j; rw [Fin.sum_univ_two]; simp [hojas_juegoSav i]; ring
    simp only [juegoSav, hojas, this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring

/-- **PSPACE ⊆ APTIME, en número**: con `2^s` configuraciones y `s` niveles, el tiempo alternante es `s(s+1)`. -/
theorem savitch_alternante (s : ℕ) (e : Fin (2 ^ s) → C) (u v : C) :
    prof (juegoSav R e s u v) = s * (s + 1) := by
  rw [prof_juegoSav R e Nat.one_le_two_pow, Nat.clog_pow 2 s (by norm_num)]

/-! ## Controles -/

/-- El ciclo de tres configuraciones de `Savitch.lean`, jugado: desde 0 se llega a 2 en dos pasos. -/
example : valor (juegoSav ciclo3 (id : Fin 3 → Fin 3) 1 0 2) = true := by decide
example : valor (juegoSav ciclo3 (id : Fin 3 → Fin 3) 0 0 2) = false := by decide
example : prof (juegoSav ciclo3 (id : Fin 3 → Fin 3) 1 0 2) = 3 := by decide

end Tiempo
end Sagitta.Map
