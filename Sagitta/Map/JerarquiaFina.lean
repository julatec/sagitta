import Sagitta.Map.LandauDenso
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicExponentialTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# La jerarquía no determinista: el corazón de la diagonal perezosa y los exponentes enteros

Primer ladrillo hacia la prueba de Williams («algoritmos ⇒ cotas») sobre cslib-frontier. Williams necesita una
jerarquía de tiempo **no determinista fina**: que `NTIME(2^n)` no quepa en `NTIME(2^n / s(n))` para un ahorro
`s` superpolinomial, o, en la forma clásica, `NTIME(f) ⊊ NTIME(g)` cuando `f(n+1) ∈ o(g(n))` (Seiferas, Fischer y
Meyer, 1978; Žák, 1983). cslib-frontier trae la versión **gruesa**: `NTIME(2^(k·n)) ⊊ NTIME(2^(e·n))` con
`8·k + 16 ≤ e` (`Cslib.Complexity.NTIME_two_pow_ssubset_NTIME_two_pow_of_le`), por diagonal perezosa
(`Cslib.Complexity.Diagonal.lazyLanguage`). Este archivo no llega a la fina; prueba dos cosas por debajo.

## Qué se prueba

1. **El corazón combinatorio de la diagonal perezosa, sin máquinas** (§1). Si en un intervalo `[a, b]` la diagonal
   `D` copia a la máquina `M` un paso adelante (`D m ↔ M (m+1)` para `m < b`), en el extremo niega lo que `M` hace en
   el comienzo (`D b ↔ ¬ M a`) y `M` decide a `D` en todo el intervalo, hay contradicción (`diagonal_perezosa`). La
   prueba es una cadena de equivalencias (`cadena`). Variantes: la diagonal armada contra una sucesión de máquinas,
   cada una con su intervalo (`diagonalPerezosa`, `diagonalPerezosa_distinta`), y la forma no determinista, donde la
   negación del extremo es un «para todo certificado» que se resuelve por fuerza bruta (`diagonal_perezosa_nd`).
2. **Dónde entra `f(n+1) ∈ o(g(n))`** (§2), en abstracto. El costo de la diagonal en `[a, b]` es `f(m+1)` (copiar)
   salvo en `b`, donde es la fuerza bruta; si copiar cabe en `g` y la fuerza bruta cabe en `g b`, la diagonal cabe
   en `g` en todo el intervalo (`costoDiagonal_le`). Si `f(n+1) ∈ o(g(n))` y `g` no está acotada, siempre hay un
   intervalo así, tan lejos como se quiera y contra cualquier constante de simulación (`intervalo_existe`): es la
   elección de parámetros de Žák. Esto es aritmética de costos **declarados**, no de máquinas.
3. **La jerarquía exponencial en todo exponente entero, sobre las máquinas de cslib-frontier** (§3):
   `NTIME(2^(a·n)) ⊊ NTIME(2^(b·n))` para `a < b` (`NTIME_two_pow_ssubset_NTIME_two_pow`). Mejora la constante
   gruesa `8·k + 16` a `k + 1`, que es la mejor posible entre exponentes enteros. La prueba es por relleno
   **lineal** (`rellenoLineal`, `rellenoLineal_mem_NTIME`, `mem_NTIME_of_rellenoLineal_mem`) y la amplificación que
   cslib-frontier usa para el caso polinomial, apoyada en la diagonal gruesa. Lo de máquinas (guardas, escritura en
   unario, verificadores) es de cslib-frontier; lo nuevo es el relleno lineal y sus cuentas de costo.

## La lectura, en el lenguaje del proyecto

La diagonal perezosa es la forma de diagonalizar contra el **no determinismo** sin complementarlo: una máquina
no determinista no puede negar barato lo que otra acepta (eso sería un «para todo certificado»), así que la diagonal
no niega en cada longitud, solo **una vez por intervalo**, al final, cuando la entrada es tan larga que la fuerza bruta
sobre los certificados del comienzo cabe en el presupuesto. En el resto del intervalo se limita a copiar un paso
adelante, y la cadena de copias lleva la contradicción del final al comienzo. §1 aísla esa cadena: es lógica pura,
y por eso vale para cualquier modelo. §2 dice qué tiene que cumplir el modelo para que la cadena quepa en el tiempo:
en el modelo de costo declarado de `costoDiagonal` (copiar cuesta `f (m+1)`), la condición que cierra la cuenta es
`f(n+1) ∈ o(g(n))`; el `+1` es el paso adelante. Es una lectura, no un teorema de que esa condición sea necesaria.

## Dónde encaja en el programa de Williams, y qué falta

El argumento de Williams (NEXP ⊄ ACC⁰) tiene cuatro piezas. cslib-frontier tiene el paso de verificación
(`Cslib.Complexity.AlgorithmsToLowerBounds`: adivinar un circuito testigo y correr el algoritmo de SAT sobre el
circuito de la cláusula violada) y lo cierra con la jerarquía **gruesa**. Falta, y aquí **no** se prueba:

* **la jerarquía fina** que pide el ahorro de Williams: con ahorro solo polinomial sobre la fuerza bruta, la
  diferencia entre `NTIME(2^n)` y `NTIME(2^n / n^{ω(1)})` no la da ningún exponente entero. El resultado de §3 separa
  `2^(a·n)` de `2^((a+1)·n)`, un factor `2^n` entero, y no sirve para eso;
* **el lema del testigo fácil** (Impagliazzo, Kabanets y Wigderson): si NEXP ⊆ ACC⁰, los testigos de NEXP tienen
  circuitos ACC⁰ chicos;
* **la reducción sucinta** con `n + O(log n)` bits de índice de cláusula (el propio archivo de cslib-frontier advierte
  que `O(n)` bits no alcanzan con ahorro polinomial);
* **el algoritmo de ACC-SAT** más rápido que `2^n` (Yao, Beigel–Tarui, multiplicación rectangular de matrices),
  armado sobre `Cslib` (`Computability/Circuit/Boolean/ACC0.lean` tiene la clase, no el algoritmo).

## Lo que NO se prueba

* **La jerarquía fina** `NTIME(f) ⊊ NTIME(g)` con `f(n+1) ∈ o(g(n))`. Lo que la bloquea en cslib-frontier: la
  diagonal perezosa de la librería simula con la máquina universal nativa, cuyo costo es **polinomial** en el
  presupuesto (`accBound` eleva a la cuarta; el reloj es el cuadrado de la longitud), y la longitud del certificado
  se escribe en unario con un factor logarítmico de más. Para la fina hace falta una simulación universal no
  determinista con sobrecosto **lineal** (la de Book–Greibach: adivinar la traza y verificarla cinta por cinta) y
  una noción de construibilidad en tiempo para `f` y `g` generales. Ninguna de las dos está; las dos son trabajo de
  máquinas, no de este archivo.
* **Exponentes racionales o reales** (`2^(1.5·n)` contra `2^(1.6·n)`): el relleno lineal entero no los alcanza.
* §2 **no** es un teorema de máquinas: los costos son funciones declaradas, y que una máquina concreta los cumpla es
  justamente lo que falta en el primer punto.
* **Nada sobre P contra NP**, ni sobre NEXP contra ACC⁰.

## Fuentes

* S. Žák, «A Turing machine time hierarchy», *Theoretical Computer Science* 26(3):327–333, 1983,
  doi:10.1016/0304-3975(83)90015-4 (verificado en Crossref; no lo leí, las pruebas de aquí son propias o de
  cslib-frontier).
* J. I. Seiferas, M. J. Fischer y A. R. Meyer, «Separating nondeterministic time complexity classes», *J. ACM*
  25:146–167, 1978, doi:10.1145/322047.322061 (verificado en Crossref; no lo leí).
* R. Williams, «Nonuniform ACC circuit lower bounds», *J. ACM* 61(1):1–32, 2014, doi:10.1145/2559903 (verificado en
  Crossref; el contenido, de memoria).
* Impagliazzo–Kabanets–Wigderson (testigo fácil), Book–Greibach (simulación lineal), Yao y Beigel–Tarui: de memoria.
-/

namespace Sagitta.Map.Tiempo.JerarquiaFina

open Turing Turing.MultiTapeTM Cslib.Complexity

/-! ## 1. El corazón combinatorio, sin máquinas -/

/-- **La cadena.** Si en el intervalo `[a, b]` la diagonal `D` copia a la máquina `M` un paso adelante
(`D m ↔ M (m + 1)` para `m < b`) y `M` decide a `D` en todo el intervalo, entonces `D` vale en cada punto del
intervalo lo mismo que en el comienzo. -/
theorem cadena {D M : ℕ → Prop} {a b : ℕ}
    (copia : ∀ m, a ≤ m → m < b → (D m ↔ M (m + 1)))
    (decide : ∀ m, a ≤ m → m ≤ b → (D m ↔ M m)) :
    ∀ m, a ≤ m → m ≤ b → (D a ↔ D m) := by
  intro m ham hmb
  induction m, ham using Nat.le_induction with
  | base => exact Iff.rfl
  | succ m ham ih =>
    exact (ih (by omega)).trans ((copia m ham (by omega)).trans (decide (m + 1) (by omega) hmb).symm)

/-- **La diagonal perezosa (Žák), en abstracto.** Ninguna máquina `M` decide en todo un intervalo `[a, b]` a una
diagonal `D` que copia a `M` un paso adelante dentro del intervalo y que en el extremo `b` niega lo que `M` hace en
el comienzo `a`. -/
theorem diagonal_perezosa {D M : ℕ → Prop} {a b : ℕ} (hab : a ≤ b)
    (copia : ∀ m, a ≤ m → m < b → (D m ↔ M (m + 1)))
    (niega : D b ↔ ¬ M a)
    (decide : ∀ m, a ≤ m → m ≤ b → (D m ↔ M m)) : False := by
  have h := cadena copia decide b hab le_rfl
  rw [niega, ← decide a le_rfl hab] at h
  exact iff_not_self h

/-- **La forma no determinista.** La máquina acepta `m` cuando algún certificado `v` cumple `R m v`. La negación del
extremo es «ningún certificado de `a` sirve», un «para todo» que la diagonal resuelve por fuerza bruta. -/
theorem diagonal_perezosa_nd {V : Type*} {D : ℕ → Prop} {R : ℕ → V → Prop} {a b : ℕ} (hab : a ≤ b)
    (copia : ∀ m, a ≤ m → m < b → (D m ↔ ∃ v, R (m + 1) v))
    (niega : D b ↔ ∀ v, ¬ R a v)
    (decide : ∀ m, a ≤ m → m ≤ b → (D m ↔ ∃ v, R m v)) : False :=
  diagonal_perezosa (M := fun m => ∃ v, R m v) hab copia (niega.trans not_exists.symm) decide

/-- **La diagonal contra una sucesión de máquinas.** La máquina `i` acepta `acepta i m` en la longitud `m` y tiene su
intervalo `[ini i, fin i]`; en la entrada `(i, m)` la diagonal copia a `i` un paso adelante antes de `fin i` y, desde
ahí, niega lo que `i` hace en `ini i`. La entrada lleva el índice `i`: es una familia de diagonales, una por máquina.
No se modela el reparto de las longitudes en intervalos disjuntos que hace de la diagonal de Žák un solo lenguaje. -/
def diagonalPerezosa {ι : Type*} (acepta : ι → ℕ → Prop) (ini fin : ι → ℕ) (i : ι) (m : ℕ) : Prop :=
  if m < fin i then acepta i (m + 1) else ¬ acepta i (ini i)

/-- **Ninguna máquina de la sucesión decide la diagonal en su intervalo.** -/
theorem diagonalPerezosa_distinta {ι : Type*} (acepta : ι → ℕ → Prop) (ini fin : ι → ℕ) (i : ι)
    (h : ini i ≤ fin i) :
    ¬ ∀ m, ini i ≤ m → m ≤ fin i → (diagonalPerezosa acepta ini fin i m ↔ acepta i m) := fun hd =>
  diagonal_perezosa h (fun m _ hm => by simp only [diagonalPerezosa, hm, ↓reduceIte])
    (by simp only [diagonalPerezosa, lt_irrefl, ↓reduceIte]) hd

/-! ### Controles de §1: cada par de hipótesis se puede cumplir; las tres juntas, no -/

/-- Copia y decide, sin negación: `D = M = verdadero`. -/
theorem control_sin_niega : ∃ D M : ℕ → Prop, (∀ m, 0 ≤ m → m < 5 → (D m ↔ M (m + 1))) ∧
    (∀ m, 0 ≤ m → m ≤ 5 → (D m ↔ M m)) :=
  ⟨fun _ => True, fun _ => True, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

/-- Niega y decide, sin copia: `M m := (m = 0)`, `D = M`, en `[0, 1]`. -/
theorem control_sin_copia : ∃ D M : ℕ → Prop, (D 1 ↔ ¬ M 0) ∧ (∀ m, 0 ≤ m → m ≤ 1 → (D m ↔ M m)) :=
  ⟨fun m => m = 0, fun m => m = 0, by simp, fun _ _ _ => Iff.rfl⟩

/-- Copia y niega, sin decidir: `M` falsa y `D m := (m = 1)`, en `[0, 1]`. -/
theorem control_sin_decide : ∃ D M : ℕ → Prop, (∀ m, 0 ≤ m → m < 1 → (D m ↔ M (m + 1))) ∧ (D 1 ↔ ¬ M 0) :=
  ⟨fun m => m = 1, fun _ => False, fun m _ hm => by simp only [iff_false]; omega, by simp⟩

/-! ## 2. Dónde entra `f(n+1) ∈ o(g(n))`: el costo declarado de la diagonal -/

/-- El costo de la diagonal en la longitud `m` del intervalo `[a, b]`: copiar el paso siguiente, `f (m + 1)`, salvo en
el extremo, donde se paga la fuerza bruta `bruta`. -/
def costoDiagonal (f : ℕ → ℕ) (b bruta m : ℕ) : ℕ := if m < b then f (m + 1) else bruta

/-- **La diagonal cabe en `g` en todo el intervalo** si copiar un paso adelante cabe y la fuerza bruta cabe en el
extremo. -/
theorem costoDiagonal_le {f g : ℕ → ℕ} {a b bruta : ℕ}
    (copiaBarata : ∀ m, a ≤ m → m < b → f (m + 1) ≤ g m) (bruta_cabe : bruta ≤ g b) :
    ∀ m, a ≤ m → m ≤ b → costoDiagonal f b bruta m ≤ g m := by
  intro m ham hmb
  unfold costoDiagonal
  split_ifs with h
  · exact copiaBarata m ham h
  · rwa [show m = b by omega]

/-- Control: la cota se alcanza en el extremo cuando `g b` es exactamente la fuerza bruta. -/
theorem costoDiagonal_alcanza (f : ℕ → ℕ) (b bruta : ℕ) : costoDiagonal f b bruta b = bruta := by
  simp [costoDiagonal]

/-- **La elección de parámetros de Žák.** Si `f(n+1) ∈ o(g(n))` y `g` no está acotada, para cada constante de
simulación `c`, cada punto de partida `a₀` y cada costo de fuerza bruta `bruta a` hay un intervalo `[a, b]` con
`a ≥ a₀` donde copiar (con la constante `c`) cabe en `g` y la fuerza bruta del comienzo cabe en `g b`. -/
theorem intervalo_existe {f g : ℕ → ℕ} (hfg : (fun n => f (n + 1)) ∈ o g)
    (hg : ∀ N A, ∃ m, A ≤ m ∧ N ≤ g m) (c a₀ : ℕ) (bruta : ℕ → ℕ) :
    ∃ a, a₀ ≤ a ∧ ∃ b, a ≤ b ∧ (∀ m, a ≤ m → m < b → c * f (m + 1) ≤ g m) ∧ bruta a ≤ g b := by
  obtain ⟨N, hN⟩ := hfg c
  obtain ⟨b, hb, hgb⟩ := hg (bruta (max a₀ N)) (max a₀ N)
  exact ⟨max a₀ N, le_max_left _ _, b, hb, fun m ham _ => hN m (le_trans (le_max_right _ _) ham), hgb⟩

/-- Control: la hipótesis `f(n+1) ∈ o(g(n))` no es vacía (`f = 1`, `g = n`). -/
theorem control_o_no_vacia : (fun n => (fun _ : ℕ => 1) (n + 1)) ∈ o (fun n => n) := fun c =>
  ⟨c, fun n hn => by simpa using hn⟩

/-! ## 3. La jerarquía exponencial en todo exponente entero, sobre cslib-frontier -/

/-- **El lenguaje rellenado linealmente.** Las palabras `x` que llevan enmarcada al comienzo una palabra
`y = unframe x` de `A` y que miden al menos `(k + 1) · (|y| + 1)`. -/
def rellenoLineal (A : Set (List Bool)) (k : ℕ) : Set (List Bool) :=
  {x | (k + 1) * ((unframe x).length + 1) ≤ x.length ∧ unframe x ∈ A}

/-- Aritmética del certificado: `c · X + c ≤ 2^(c+1) · X` si `X ≥ 1`. -/
theorem cuenta_certificado (c X : ℕ) (hX : 1 ≤ X) : c * X + c ≤ 2 ^ (c + 1) * X := by
  have : c < 2 ^ c := Nat.lt_two_pow_self
  have h2 : 2 * c ≤ 2 ^ (c + 1) := by rw [pow_succ]; omega
  calc c * X + c ≤ 2 * c * X := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ h2

/-- **Rellenar baja el exponente.** Si `A` está en `NTIME(2^(b·k·n))`, su relleno lineal con factor `k + 1` está en
`NTIME(2^(b·n))`. Se prueba la guarda de longitud (tiempo polinomial, absorbido por `2^n`), se escribe en unario la
longitud `2^(b·k·|y| + c + 1)` del certificado y se corre el verificador lineal de `A`. Escribir esa longitud cuesta
`(L + 1) · 2^L`, un factor `|y|` de más; el relleno con `k + 1` en vez de `k` lo paga. -/
theorem rellenoLineal_mem_NTIME {A : Set (List Bool)} {b k : ℕ} (hb : 1 ≤ b)
    (hA : A ∈ NTIME encBits (fun n => 2 ^ (b * k * n))) :
    rellenoLineal A k ∈ NTIME encBits (fun n => 2 ^ (b * n)) := by
  classical
  obtain ⟨V, c, hV, hc⟩ := exists_verifier_of_mem_NTIME hA
  let guard (x : List Bool) : Bool := decide ((k + 1) * ((unframe x).length + 1) ≤ x.length)
  let E (x : List Bool) : ℕ := if guard x then b * k * (unframe x).length + (c + 1) else 0
  let V' (p : List Bool × List Bool) : Bool := if guard p.1 then V (unframe p.1, p.2) else false
  have hset : rellenoLineal A k =
      {x | ∃ w : List Bool, w.length = 2 ^ E x ∧ V' (x, w) = true} := by
    ext x
    by_cases hg : (k + 1) * ((unframe x).length + 1) ≤ x.length
    · have hgx : guard x = true := decide_eq_true hg
      simp only [rellenoLineal, Set.mem_ofPred_eq, hg, true_and, E, V', hgx, ↓reduceIte]
      refine hc (unframe x) _ ?_
      simp only [encBits_apply]; rw [pow_add]
      have := cuenta_certificado c (2 ^ (b * k * (unframe x).length)) Nat.one_le_two_pow
      linarith
    · have hgx : guard x = false := decide_eq_false hg
      simp [rellenoLineal, hg, V', hgx]
  rw [hset]
  have hEp : ComputableInPolyTime E encBits encUnary := by simp only [E, guard]; fun_prop
  obtain ⟨TE, SE, hTE, -, hEO⟩ := hEp.exists_computableInO
  obtain ⟨CE, hCE⟩ := hTE.exists_le_mul_two_pow
  have hℓ := ComputableInO.unary_two_pow.comp hEO
  have hgp : ComputableInPolyTime guard encBits encBool := by simp only [guard]; fun_prop
  obtain ⟨Tg, Sg, hTg, -, hgO⟩ := hgp.exists_computableInO
  obtain ⟨Cg, hCg⟩ := hTg.exists_le_mul_two_pow
  have hpair := (ComputableInO.unframe.comp (ComputableInO.fst encBits encBits)).prod
    (ComputableInO.snd encBits encBits)
  have hV' := (hgO.comp (ComputableInO.fst encBits encBits)).ite (hV.comp hpair)
      (ComputableInO.const (encIn := encPair encBits encBits) (encMid := encBool) false)
  refine setOf_exists_mem_NTIME hℓ hV' (C := (b * k + c + 2) * 2 ^ (c + 1) + CE + Cg + 4 * 2 ^ (c + 1) + 12) fun x w hw => ?_
  simp only [Function.comp_apply, encBits_apply, length_encPair] at hw ⊢
  set n := x.length with hn
  set m := (unframe x).length with hm
  have hmn : m ≤ n := length_unframe_le x
  set G := 2 ^ (b * n) with hG
  have h2n : 2 ^ n ≤ G := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left n hb)
  have hnG : n + 1 ≤ G := Nat.lt_two_pow_self.trans_le h2n
  have hTE' : TE x ≤ CE * G := (hCE x).trans (Nat.mul_le_mul_left _ h2n)
  have hTg' : Tg x ≤ Cg * G := (hCg x).trans (Nat.mul_le_mul_left _ h2n)
  by_cases hg : (k + 1) * (m + 1) ≤ n
  · have hgx : guard x = true := decide_eq_true hg
    have hE : E x = b * k * m + (c + 1) := by simp only [E, hgx, ↓reduceIte, hm]
    rw [hE] at hw ⊢
    simp only [hgx, ↓reduceIte]
    set P := 2 ^ (b * k * m) with hPdef
    have hP : 2 ^ (m + 1) * P ≤ G := by
      rw [hPdef, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hm1 : m + 1 ≤ 2 ^ (m + 1) := Nat.lt_two_pow_self.le
    have hL : (b * k * m + (c + 1) + 1) * 2 ^ (b * k * m + (c + 1)) ≤
        (b * k + c + 2) * 2 ^ (c + 1) * G := by
      rw [pow_add, ← hPdef]
      calc (b * k * m + (c + 1) + 1) * (P * 2 ^ (c + 1))
          ≤ ((b * k + c + 2) * (m + 1)) * (P * 2 ^ (c + 1)) :=
            Nat.mul_le_mul_right _ (by nlinarith)
        _ = (b * k + c + 2) * 2 ^ (c + 1) * ((m + 1) * P) := by ring
        _ ≤ (b * k + c + 2) * 2 ^ (c + 1) * (2 ^ (m + 1) * P) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm1)
        _ ≤ _ := Nat.mul_le_mul_left _ hP
    have hw' : w.length ≤ 2 ^ (c + 1) * G := by
      rw [hw, pow_add, ← hPdef, mul_comm]
      exact Nat.mul_le_mul_left _ ((Nat.le_mul_of_pos_left P Nat.one_le_two_pow).trans hP)
    have hC : ((b * k + c + 2) * 2 ^ (c + 1) + CE + Cg + 4 * 2 ^ (c + 1) + 12) * G =
        (b * k + c + 2) * 2 ^ (c + 1) * G + CE * G + Cg * G + 4 * (2 ^ (c + 1) * G) + 12 * G := by
      ring
    nlinarith
  · have hgx : guard x = false := decide_eq_false hg
    have hE : E x = 0 := by simp only [E, hgx, Bool.false_eq_true, ↓reduceIte]
    rw [hE] at hw ⊢
    simp only [hgx, Bool.false_eq_true, ↓reduceIte]
    simp only [pow_zero] at hw
    have hC : ((b * k + c + 2) * 2 ^ (c + 1) + CE + Cg + 4 * 2 ^ (c + 1) + 12) * G =
        (b * k + c + 2) * 2 ^ (c + 1) * G + CE * G + Cg * G + 4 * (2 ^ (c + 1) * G) + 12 * G := by
      ring
    have h0 : 0 ≤ (b * k + c + 2) * 2 ^ (c + 1) * G + 4 * (2 ^ (c + 1) * G) := Nat.zero_le _
    nlinarith

/-- El relleno de `y`: `frame y` seguido de unos hasta medir exactamente `(k + 1) · (|y| + 1)`. -/
def rellenarLineal (k : ℕ) (y : List Bool) : List Bool :=
  frame y ++ List.replicate ((k - 1) * (y.length + 1) + 1) true

/-- La longitud del relleno. -/
theorem length_rellenarLineal {k : ℕ} (hk : 1 ≤ k) (y : List Bool) :
    (rellenarLineal k y).length = (k + 1) * (y.length + 1) := by
  simp only [rellenarLineal, List.length_append, length_frame, List.length_replicate]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- El relleno de `y` está en el relleno lineal de `A` exactamente cuando `y ∈ A`. -/
theorem rellenarLineal_mem_iff {A : Set (List Bool)} {k : ℕ} (hk : 1 ≤ k) (y : List Bool) :
    rellenarLineal k y ∈ rellenoLineal A k ↔ y ∈ A := by
  change (k + 1) * ((unframe (rellenarLineal k y)).length + 1) ≤ (rellenarLineal k y).length ∧
    unframe (rellenarLineal k y) ∈ A ↔ y ∈ A
  have hu : unframe (rellenarLineal k y) = y := unframe_frame_append _ _
  rw [hu, length_rellenarLineal hk]
  exact and_iff_right le_rfl

/-- **Desrellenar sube el exponente, con un grado de pérdida.** Si el relleno lineal de `A` (factor `k + 1`) está en
`NTIME(2^(a·n))`, entonces `A` está en `NTIME(2^((a·(k+1) + 1)·n))`: se rellena `y` (tiempo polinomial), se adivina un
certificado de longitud `2^(a·(k+1)·(|y|+1) + c + 1)` y se corre el verificador del relleno. El `+ 1` del exponente
paga, de nuevo, el factor `|y|` de escribir en unario la longitud del certificado. -/
theorem mem_NTIME_of_rellenoLineal_mem {A : Set (List Bool)} {a k : ℕ} (hk : 1 ≤ k)
    (hB : rellenoLineal A k ∈ NTIME encBits (fun n => 2 ^ (a * n))) :
    A ∈ NTIME encBits (fun n => 2 ^ ((a * (k + 1) + 1) * n)) := by
  classical
  obtain ⟨V, c, hV, hc⟩ := exists_verifier_of_mem_NTIME hB
  let E (y : List Bool) : ℕ := a * (k + 1) * (y.length + 1) + (c + 1)
  let V' (p : List Bool × List Bool) : Bool := V (rellenarLineal k p.1, p.2)
  have hset : A = {y | ∃ w : List Bool, w.length = 2 ^ E y ∧ V' (y, w) = true} := by
    ext y
    rw [← rellenarLineal_mem_iff (A := A) hk y]
    refine hc (rellenarLineal k y) _ ?_
    change c * 2 ^ (a * (rellenarLineal k y).length) + c ≤ 2 ^ (a * (k + 1) * (y.length + 1) + (c + 1))
    rw [length_rellenarLineal hk, pow_add, show a * ((k + 1) * (y.length + 1)) = a * (k + 1) * (y.length + 1) by ring]
    have := cuenta_certificado c (2 ^ (a * (k + 1) * (y.length + 1))) Nat.one_le_two_pow
    linarith
  rw [hset]
  have hEp : ComputableInPolyTime E encBits encUnary := by simp only [E]; fun_prop
  obtain ⟨TE, SE, hTE, -, hEO⟩ := hEp.exists_computableInO
  obtain ⟨CE, hCE⟩ := hTE.exists_le_mul_two_pow
  have hℓ := ComputableInO.unary_two_pow.comp hEO
  have hrp : ComputableInPolyTime (rellenarLineal k) encBits encBits := by
    unfold rellenarLineal; fun_prop
  obtain ⟨Tr, Sr, hTr, -, hrO⟩ := hrp.exists_computableInO
  obtain ⟨Cr, hCr⟩ := hTr.exists_le_mul_two_pow
  have hpair := (hrO.comp (ComputableInO.fst encBits encBits)).prod
    (ComputableInO.snd encBits encBits)
  have hV' := hV.comp hpair
  refine setOf_exists_mem_NTIME hℓ hV' (C := (a * (k + 1) + c + 2) * 2 ^ (a * (k + 1) + (c + 1)) + CE + Cr +
    3 * 2 ^ (a * (k + 1) + (c + 1)) + 2 * (k + 1) + 10) fun y w hw => ?_
  simp only [Function.comp_apply, encBits_apply, length_encPair] at hw ⊢
  set m := y.length with hm
  set R := a * (k + 1) with hR
  set G := 2 ^ ((R + 1) * m) with hG
  set Q := 2 ^ (R + (c + 1)) with hQ
  set P := 2 ^ (R * m) with hP
  have hGP : G = 2 ^ m * P := by rw [hG, hP, ← pow_add]; ring_nf
  have h2m : 2 ^ m ≤ G := by rw [hGP]; exact Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
  have hmG : m + 1 ≤ G := Nat.lt_two_pow_self.trans_le h2m
  have hm1 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have hPG : (m + 1) * P ≤ G := by rw [hGP]; exact Nat.mul_le_mul_right _ hm1
  have hEy : E y = R * m + (R + (c + 1)) := by simp only [E, ← hm, ← hR]; ring
  have h2E : 2 ^ E y = Q * P := by rw [hEy, pow_add, hQ, hP]; ring
  have hTE' : TE y ≤ CE * G := (hCE y).trans (Nat.mul_le_mul_left _ h2m)
  have hTr' : Tr y ≤ Cr * G := (hCr y).trans (Nat.mul_le_mul_left _ h2m)
  have hL : (E y + 1) * 2 ^ E y ≤ (R + c + 2) * Q * G := by
    rw [h2E, hEy]
    calc (R * m + (R + (c + 1)) + 1) * (Q * P) ≤ ((R + c + 2) * (m + 1)) * (Q * P) :=
          Nat.mul_le_mul_right _ (by nlinarith)
      _ = (R + c + 2) * Q * ((m + 1) * P) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hPG
  have hw' : w.length ≤ Q * G := by
    rw [hw, h2E]
    exact Nat.mul_le_mul_left _ ((Nat.le_mul_of_pos_left P (Nat.succ_pos m)).trans hPG)
  have hrl : (rellenarLineal k y).length ≤ (k + 1) * G := by
    rw [length_rellenarLineal hk]; exact Nat.mul_le_mul_left _ hmG
  have hC : ((R + c + 2) * Q + CE + Cr + 3 * Q + 2 * (k + 1) + 10) * G =
      (R + c + 2) * Q * G + CE * G + Cr * G + 3 * (Q * G) + 2 * ((k + 1) * G) + 10 * G := by
    ring
  nlinarith

/-- **Un colapso exponencial se propaga hacia arriba por relleno lineal**, con un grado de pérdida: si
`NTIME(2^(b·n)) ⊆ NTIME(2^(a·n))`, entonces `NTIME(2^(b·k·n)) ⊆ NTIME(2^((a·(k+1)+1)·n))` para todo `k ≥ 1`. -/
theorem NTIME_two_pow_mul_subset_of_subset {a b k : ℕ} (hb : 1 ≤ b) (hk : 1 ≤ k)
    (h : NTIME encBits (fun n => 2 ^ (b * n)) ⊆ NTIME encBits (fun n => 2 ^ (a * n))) :
    NTIME encBits (fun n => 2 ^ (b * k * n)) ⊆
      NTIME encBits (fun n => 2 ^ ((a * (k + 1) + 1) * n)) :=
  fun _ hA => mem_NTIME_of_rellenoLineal_mem hk (h (rellenoLineal_mem_NTIME hb hA))

/-- **La jerarquía no determinista exponencial, en todo exponente entero.** Para `a < b`,
`NTIME(2^(a·n)) ⊊ NTIME(2^(b·n))` sobre palabras de bits, con las máquinas multicinta nativas de cslib-frontier.
Mejora la constante `8·k + 16 ≤ e` de `NTIME_two_pow_ssubset_NTIME_two_pow_of_le` a `k + 1 ≤ e`, la mejor posible en
exponentes enteros. La prueba copia la amplificación del caso polinomial (`NTIME_succ_pow_ssubset_NTIME_succ_pow`):
un colapso en `(a, b)` se propaga por relleno lineal y arrastraría todas las clases desde `a·(3a+2)` hacia abajo,
contra la jerarquía gruesa entre `a·(3a+2)` y `a·(24a+32)`. El caso `a = 0` (tiempo constante) va aparte: el
colapso llevaría `2^(16·n)` hasta `2^(0·n)`. -/
theorem NTIME_two_pow_ssubset_NTIME_two_pow {a b : ℕ} (hab : a < b) :
    NTIME encBits (fun n => 2 ^ (a * n)) ⊂ NTIME encBits (fun n => 2 ^ (b * n)) := by
  have hsub {d e : ℕ} (h : d ≤ e) :
      NTIME encBits (fun n => 2 ^ (d * n)) ⊆ NTIME encBits (fun n => 2 ^ (e * n)) :=
    NTIME_mono fun n => Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)
  refine ⟨hsub hab.le, fun hcollapse => ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- `a = 0`: un colapso a tiempo constante arrastraría `2^(16·n)` hasta `2^(0·n)`
    have h := NTIME_two_pow_mul_subset_of_subset (k := 16) (by omega) (by omega) hcollapse
    exact (NTIME_two_pow_ssubset_NTIME_two_pow_of_le (k := 0) (e := 16) (by omega)).2
      ((hsub (by nlinarith)).trans (h.trans ((hsub (by omega)).trans hcollapse)))
  -- un paso de la amplificación, del exponente `a * (k + 3)` al `a * (k + 2)`
  have hstep (k : ℕ) (hk : 3 * a ≤ k) :
      NTIME encBits (fun n => 2 ^ (a * (k + 3) * n)) ⊆
        NTIME encBits (fun n => 2 ^ (a * (k + 2) * n)) := by
    have hup : a * (k + 3) ≤ b * k := by nlinarith
    have hdown : a * (k + 1) + 1 ≤ a * (k + 2) := by nlinarith
    exact (hsub hup).trans ((NTIME_two_pow_mul_subset_of_subset (by omega) (by omega)
      hcollapse).trans (hsub hdown))
  -- todo exponente `a * j` con `j ≥ 3 * a + 2` cae al exponente `a * (3 * a + 2)`
  have htail (j : ℕ) (hj : 3 * a + 2 ≤ j) :
      NTIME encBits (fun n => 2 ^ (a * j * n)) ⊆
        NTIME encBits (fun n => 2 ^ (a * (3 * a + 2) * n)) := by
    induction j, hj using Nat.le_induction with
    | base => exact Set.Subset.refl _
    | succ j hj ih =>
      have h := hstep (j - 2) (by omega)
      rw [show j - 2 + 3 = j + 1 by omega, show j - 2 + 2 = j by omega] at h
      exact h.trans ih
  exact (NTIME_two_pow_ssubset_NTIME_two_pow_of_le (k := a * (3 * a + 2))
    (e := a * (24 * a + 32)) (by nlinarith)).2 (htail _ (by omega))

/-- Control: la desigualdad estricta es necesaria; una clase no está estrictamente contenida en sí misma. -/
theorem control_no_estricta (a : ℕ) :
    ¬ NTIME encBits (fun n => 2 ^ (a * n)) ⊂ NTIME encBits (fun n => 2 ^ (a * n)) :=
  fun h => h.2 h.1

/-- Control: el escalón mínimo `b = a + 1` se alcanza; por ejemplo, `NTIME(2^n) ⊊ NTIME(2^(2n))`, que la versión
gruesa de cslib-frontier no daba (pedía `e ≥ 24`). -/
theorem control_escalon_minimo :
    NTIME encBits (fun n => 2 ^ (1 * n)) ⊂ NTIME encBits (fun n => 2 ^ (2 * n)) :=
  NTIME_two_pow_ssubset_NTIME_two_pow (by norm_num)

end Sagitta.Map.Tiempo.JerarquiaFina
