import Sagitta.Map.Testigo
import CslibFrontier.Logics.Propositional.Frege

/-!
# El espejo proposicional de S¹₂: la mitad semántica de la traducción de Cook

La completitud de primer orden no se puede usar como «bootstrap» dentro de `S¹₂`. Lo que sí baja a nivel polinomial es un
**espejo proposicional**: cada teorema acotado de la teoría se vuelve una familia de tautologías, una por cada largo de
la entrada, con pruebas cortas en un sistema proposicional. Este archivo formaliza la parte más chica de ese espejo que
sale honesta: la traducción de una clase `Σᵇ₀` restringida y su corrección semántica (meta 2), y pruebas de Frege de largo
constante para lo que sale por reglas puramente lógicas (meta 3, la versión mínima).

## Por qué la completitud no vive dentro de S¹₂ (de memoria, sin cotejar con la fuente)

* El teorema de completitud construye un **modelo** de una teoría consistente: un objeto infinito, armado por Henkin y
  Lindenbaum. En aritmética de segundo orden equivale a `WKL₀` sobre `RCA₀` (Simpson); en aritmética acotada no hay
  ni siquiera cómo hablar de ese modelo.
* Peor: `S¹₂` (de hecho `S₂`, y también `IΔ₀ + Ω₁`) **no demuestra `Con(Q)`** (Pudlák, 1985; Wilkie y Paris, 1987). Si
  demostrara la completitud en una forma usable, de la existencia de un modelo de `Q` sacaría `Con(Q)`.
* La completitud que está en `Completitud/Teorema.lean` (`demuestra_iff_deriva`) se prueba en la metateoría de Lean, no
  dentro de `S¹₂`. Por eso aquí no se usa.

## Por qué el espejo proposicional sí funciona (de memoria, sin cotejar)

* **Cook (1975)**: si `PV ⊢ ∀x φ(x)` con `φ` abierta (o `S¹₂ ⊢ ∀x φ(x)` con `φ` en `Σᵇ₁`, por conservación), la familia
  `⟦φ⟧ₙ` tiene pruebas en **Frege extendido (EF)** de tamaño polinomial en `n`, y se construyen en tiempo polinomial.
  Paris y Wilkie (1985) hicieron lo mismo para `IΔ₀(R)` con Frege de profundidad acotada y tamaño cuasipolinomial.
* **Krajíček y Pudlák (1990)**: `S¹₂ ⊢ RFN(EF)` (la reflexión, o corrección, de EF: «si `π` es una prueba en EF de `τ`,
  `τ` es verdadera»), y **EF p-simula a todo sistema de pruebas cuya corrección demuestre `S¹₂`**. EF es, en ese sentido,
  el sistema proposicional de `S¹₂`.
* La razón de fondo: la traducción solo usa objetos finitos (los bits de `x` de largo `n`), y la prueba proposicional
  se arma siguiendo la prueba de la teoría regla por regla. No hace falta construir ningún modelo.

## Qué está probado aquí

* **La traducción** (`trad`, `traduce`). La clase (`EsSb0`): átomos `≤`, `=`, `≰`, `≠` entre términos simples
  (`EsSimple`: variables, `0`, sucesor, suma y `⌊t/2⌋`), «y», «o», y solo **cuantificadores agudos**: «para todo
  `x ≤ |t|`» y «existe `x ≤ |t|`». Es un fragmento de las fórmulas de `Testigo.lean` (la misma `Formula`, la misma `Vale`).
  Los términos se traducen a vectores de bits (`bitsT`): la suma con un sumador de acarreo en cascada (`sumador`), cuyo
  acarreo aparece una sola vez por bit; la comparación recorre los bits con un acumulador (`menorAcc`). El cuantificador
  agudo es una conjunción (o disyunción) de `W + 1` casos, con `W` el ancho de `t`; cada caso pregunta `k ≤ |t|` con los
  bits de `t` (`geLargo`).
* **Corrección** (`traduce_eval`, asignación por asignación; `traduce_tautologia`): `⟦φ⟧ₙ` es tautología **si y solo si**
  `φ(x)` vale para todo `x` con `|x| ≤ n`.
* **Tamaño** (`tam_traduce`, `traduce_acotada`): `|⟦φ⟧ₙ| ≤ cotaF φ n`, y `cotaF φ` es un polinomio (`cotaF_acotada`).
  Se cuentan símbolos (`tam`). El grado crece con el anidamiento de sumas: sin variables de extensión, cada nivel de
  sumador multiplica por `O(n)`. Con EF se nombraría cada acarreo con una variable nueva y el tamaño sería lineal.
* **Pruebas cortas, versión mínima** (`pruebas_cortas`): para `φ` sin cuantificadores, `⟦φ⟧ₙ` es una sustitución de un
  esqueleto proposicional fijo (`trad_eq_subst`), y las pruebas de Frege se conservan al sustituir (`isProof_subst`). Si
  el esqueleto tiene una prueba de `m` líneas, **toda la familia** tiene pruebas de `m` líneas, sin importar `n`. Ejemplo:
  `x ≤ x ∨ x ≰ x` en `222` líneas para todo `n` (`terceroX_corto`, con `tercero_excluido`). Es el caso de los teoremas
  que salen por reglas lógicas; una verdad aritmética como `⌊x/2⌋ ≤ x` no entra (`esqueleto_mitadMenor_sin_prueba`).
* **La cadena hasta la verdad** (`vale_de_esqueleto`): prueba del esqueleto → prueba de `⟦φ⟧ₙ` → tautología (corrección
  de Frege, cslib) → `φ(x)` para todo `x` (la corrección de la traducción).

## La reflexión y la simulación (solo enunciadas, de memoria)

* `S¹₂ ⊢ ∀π ∀τ (Prf_EF(π, τ) → Taut(τ))` (Krajíček–Pudlák). Aquí no hay EF: cslib-frontier trae Frege
  (`Cslib.Logic.PL.Frege`), sin la regla de extensión, y nada de reflexión.
* Si `S¹₂ ⊢ RFN(P)` para un sistema `P`, EF p-simula a `P`. Las definiciones de p-simulación ya están (en
  `SistemaDePruebas.lean`, `PSimula`, y en cslib-frontier, `Cslib.Complexity.ProofSystem.PSimulates`); el teorema no.
* Lo de la meta 3 se conecta así: lo probado es el caso trivial de la traducción de pruebas, el de las reglas lógicas sin
  cuantificadores, donde Frege basta (EF solo agrega la extensión) y el número de líneas no crece. Las reglas
  aritméticas (`Deriv.aritm`), el corte con fórmulas acotadas y la inducción `PIND` son los que piden EF.

## La conexión con P contra NP (de memoria, sin cotejar)

* Si `S¹₂` demostrara una cota inferior de circuitos para SAT (por ejemplo, «ningún circuito de tamaño `n^k` resuelve SAT
  en los largos `n`»), las instancias de esa cota se volverían tautologías («este circuito no resuelve SAT») con pruebas
  cortas en EF. Es la ruta de Razborov («lower bounds as tautologies») y Krajíček.
* Razborov (1995) mostró que, si existen generadores pseudoaleatorios suficientemente fuertes, ciertos fragmentos de la
  aritmética acotada no demuestran cotas inferiores superpolinomiales de circuitos (el fenómeno de las «pruebas
  naturales» de Razborov y Rudich, llevado a la teoría). Que esas tautologías sean difíciles para EF se conjetura bajo
  supuestos criptográficos, pero no está probado.
* La escalera de detectores se paró en **Frege**, no en EF: no se conoce
  ninguna cota inferior superpolinomial para Frege (`ConFregeDificil` en `DetectorFrege.lean`). EF está un peldaño más arriba
  (simula a Frege) y es el sistema que le corresponde a `S¹₂`. Ahí tampoco se conoce ninguna cota.

## Lo que NO se prueba

* **La traducción de pruebas**: que cada derivación de `Testigo.lean` (o de `Secuentes.lean`) dé pruebas cortas de
  `⟦φ⟧ₙ`. Solo está el caso de las reglas lógicas sin cuantificadores, y condicionado a una prueba del esqueleto.
* Ni **EF**, ni la **reflexión** `S¹₂ ⊢ RFN(EF)`, ni la **simulación** de Krajíček–Pudlák: solo enunciadas.
* Los términos con producto, `|t|` y `#` (`prod`, `largo`, `smash`) y el «existe `x ≤ t`» con cota no aguda: quedan fuera de
  la clase (se traducen como `⊥`). Con ellos la traducción ya no es polinomial con fórmulas, o hace falta Paris–Wilkie.
* El tamaño de las pruebas de la meta 3 se cuenta en **líneas**, no en símbolos.
* **Nada sobre P contra NP**.

## Controles

* `chequeo_mitadMenor`, `chequeo_mitadDoble`, `chequeo_largoMenor`, `chequeo_sucMayor` (`decide`, `n = 3`): `x/2 ≤ x`,
  `⌊(x+x)/2⌋ = x`, `∀ i ≤ |x|, i ≤ x` y `x + 1 ≰ x`. Con `tautologia_de_chequeo` son tautologías sobre **todas** las asignaciones.
* `no_taut_mitadMayor` (`x ≤ x/2`, falla en `x = 1`) y `no_taut_existeFalso` (`∃ i ≤ |x|, x ≤ i + i`, falla en `x = 7`):
  sus traducciones no son tautologías; `mitadMayor_falla` lo dice del lado aritmético.
-/

open Cslib.Logic.PL

namespace Sagitta.Map
namespace Extraccion
namespace EspejoEF

open Cerradura (Acotada)

/-! ## Fórmulas proposicionales, su valor y su tamaño -/

/-- Las fórmulas proposicionales de cslib con átomos en `ℕ`: el átomo `j` es el bit `j` de la entrada. -/
abbrev FP := Proposition ℕ

/-- Verdadero: `⊥ → ⊥`. -/
def verd : FP := .imp .falsum .falsum
/-- Falso. -/
def fals : FP := .falsum
/-- Negación: `p → ⊥`. -/
def neg (p : FP) : FP := .imp p .falsum
/-- O exclusivo. -/
def xorP (p q : FP) : FP := .or (.and p (neg q)) (.and (neg p) q)
/-- Equivalencia. -/
def iffP (p q : FP) : FP := .or (.and p q) (.and (neg p) (neg q))
/-- Mayoría: el acarreo de un sumador. El acarreo de entrada `c` aparece una sola vez. -/
def maj (a b c : FP) : FP := .or (.and a b) (.and c (.or a b))

/-- El valor, como función booleana estructural (para que `decide` corra). -/
def evalB (σ : ℕ → Bool) : FP → Bool
  | .atom i => σ i
  | .falsum => false
  | .and a b => evalB σ a && evalB σ b
  | .or a b => evalB σ a || evalB σ b
  | .imp a b => !evalB σ a || evalB σ b

/-- `evalB` es el valor de cslib en `Bool`. -/
theorem evalB_eq (σ : ℕ → Bool) (p : FP) : evalB σ p = p.eval σ := by
  induction p with
  | atom i => rfl
  | falsum => rfl
  | and a b iha ihb => simp [evalB, iha, ihb]
  | or a b iha ihb => simp [evalB, iha, ihb]
  | imp a b iha ihb => simp [evalB, iha, ihb]

/-- Una tautología: verdadera con toda asignación. -/
def Tautologia (p : FP) : Prop := ∀ σ : ℕ → Bool, p.eval σ = true

/-- El tamaño: número de símbolos (átomos, `⊥` y conectivos). -/
def tam : FP → ℕ
  | .atom _ => 1
  | .falsum => 1
  | .and a b => tam a + tam b + 1
  | .or a b => tam a + tam b + 1
  | .imp a b => tam a + tam b + 1

@[simp] theorem evalB_verd (σ : ℕ → Bool) : evalB σ verd = true := rfl
@[simp] theorem evalB_fals (σ : ℕ → Bool) : evalB σ fals = false := rfl
@[simp] theorem evalB_neg (σ : ℕ → Bool) (p : FP) : evalB σ (neg p) = !evalB σ p := by
  simp [neg, evalB]
@[simp] theorem evalB_xorP (σ : ℕ → Bool) (p q : FP) : evalB σ (xorP p q) = (evalB σ p ^^ evalB σ q) := by
  simp only [xorP, neg, evalB]; cases evalB σ p <;> cases evalB σ q <;> rfl
@[simp] theorem evalB_iffP (σ : ℕ → Bool) (p q : FP) : evalB σ (iffP p q) = (evalB σ p == evalB σ q) := by
  simp only [iffP, neg, evalB]; cases evalB σ p <;> cases evalB σ q <;> rfl
@[simp] theorem evalB_maj (σ : ℕ → Bool) (a b c : FP) :
    evalB σ (maj a b c) = (evalB σ a && evalB σ b || evalB σ c && (evalB σ a || evalB σ b)) := by
  simp [maj, evalB]

@[simp] theorem tam_verd : tam verd = 3 := rfl
@[simp] theorem tam_fals : tam fals = 1 := rfl
@[simp] theorem tam_neg (p : FP) : tam (neg p) = tam p + 2 := by simp only [neg, tam]
@[simp] theorem tam_xorP (p q : FP) : tam (xorP p q) = 2 * tam p + 2 * tam q + 7 := by
  simp only [xorP, neg, tam]; omega
@[simp] theorem tam_iffP (p q : FP) : tam (iffP p q) = 2 * tam p + 2 * tam q + 7 := by
  simp only [iffP, neg, tam]; omega
@[simp] theorem tam_maj (a b c : FP) : tam (maj a b c) = 2 * tam a + 2 * tam b + tam c + 4 := by
  simp only [maj, tam]; omega

/-! ## Listas: conjunción y disyunción grandes -/

/-- Conjunción de una lista (termina en `verd`). -/
def conjL (l : List FP) : FP := l.foldr .and verd
/-- Disyunción de una lista (termina en `fals`). -/
def disjL (l : List FP) : FP := l.foldr .or fals

theorem evalB_conjL (σ : ℕ → Bool) (l : List FP) : evalB σ (conjL l) = true ↔ ∀ p ∈ l, evalB σ p = true := by
  induction l with
  | nil => simp [conjL]
  | cons a l ih =>
    change (evalB σ a && evalB σ (conjL l)) = true ↔ _
    rw [Bool.and_eq_true, ih]; simp

theorem evalB_disjL (σ : ℕ → Bool) (l : List FP) : evalB σ (disjL l) = true ↔ ∃ p ∈ l, evalB σ p = true := by
  induction l with
  | nil => simp [disjL, fals, evalB]
  | cons a l ih =>
    change (evalB σ a || evalB σ (disjL l)) = true ↔ _
    rw [Bool.or_eq_true, ih]; simp

theorem tam_conjL {B : ℕ} (l : List FP) (h : ∀ p ∈ l, tam p ≤ B) : tam (conjL l) ≤ l.length * (B + 1) + 3 := by
  induction l with
  | nil => simp [conjL]
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih fun p hp => h p (by simp [hp])
    simp only [conjL, List.foldr_cons, tam, List.length_cons] at hl ⊢
    rw [Nat.succ_mul]; omega

theorem tam_disjL {B : ℕ} (l : List FP) (h : ∀ p ∈ l, tam p ≤ B) : tam (disjL l) ≤ l.length * (B + 1) + 1 := by
  induction l with
  | nil => simp [disjL]
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih fun p hp => h p (by simp [hp])
    simp only [disjL, List.foldr_cons, tam, List.length_cons] at hl ⊢
    rw [Nat.succ_mul]; omega

/-! ## Números como vectores de bits -/

/-- Un vector de bits: la fórmula del bit `j`, para cada `j`. -/
abbrev Bits := ℕ → FP

/-- Las fórmulas constantes de los bits de `k`. -/
def cte (k : ℕ) : Bits := fun j => if k.testBit j then verd else fals

theorem evalB_cte (σ : ℕ → Bool) (k j : ℕ) : evalB σ (cte k j) = k.testBit j := by
  unfold cte; split <;> simp_all

theorem tam_cte (k j : ℕ) : tam (cte k j) ≤ 3 := by
  unfold cte; split <;> simp

/-- **El sumador con acarreo en cascada**, como fórmula: el bit `j` de `a + b + c`. El acarreo se arrastra con
`maj`, donde aparece una sola vez: por eso el tamaño crece linealmente con `j` y no se duplica en cada bit. -/
def sumador : Bits → Bits → FP → ℕ → FP
  | A, B, C, 0 => xorP (xorP (A 0) (B 0)) C
  | A, B, C, j + 1 => sumador (fun i => A (i + 1)) (fun i => B (i + 1)) (maj (A 0) (B 0) C) j

/-- Lo aritmético del sumador: el bit 0 y la mitad de `a + b + c`. -/
theorem suma_bit_cero (a b : ℕ) (c : Bool) :
    (a + b + c.toNat).testBit 0 = ((a.testBit 0 ^^ b.testBit 0) ^^ c) := by
  simp only [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    cases c <;> simp [ha, hb, Nat.add_mod]

theorem suma_mitad (a b : ℕ) (c : Bool) :
    (a + b + c.toNat) / 2 = a / 2 + b / 2 +
      (a.testBit 0 && b.testBit 0 || c && (a.testBit 0 || b.testBit 0)).toNat := by
  simp only [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    cases c <;> simp [ha, hb] <;> omega

/-- **Corrección del sumador.** -/
theorem sumador_eval (σ : ℕ → Bool) : ∀ (j : ℕ) (A B : Bits) (C : FP) (a b : ℕ) (c : Bool),
    (∀ i, evalB σ (A i) = a.testBit i) → (∀ i, evalB σ (B i) = b.testBit i) → evalB σ C = c →
    evalB σ (sumador A B C j) = (a + b + c.toNat).testBit j
  | 0, A, B, C, a, b, c, hA, hB, hC => by
    simp only [sumador, evalB_xorP, hA, hB, hC, suma_bit_cero]
  | j + 1, A, B, C, a, b, c, hA, hB, hC => by
    rw [sumador, Nat.testBit_succ, suma_mitad]
    apply sumador_eval σ j
    · intro i; rw [hA, Nat.testBit_div_two]
    · intro i; rw [hB, Nat.testBit_div_two]
    · simp [hA, hB, hC]

/-- **Tamaño del sumador**: lineal en `j`. -/
theorem tam_sumador : ∀ (j : ℕ) (A B : Bits) (C : FP) (S c₀ : ℕ),
    (∀ i ≤ j, tam (A i) ≤ S) → (∀ i ≤ j, tam (B i) ≤ S) → tam C ≤ c₀ →
    tam (sumador A B C j) ≤ 2 * c₀ + (j + 1) * (10 * S + 30)
  | 0, A, B, C, S, c₀, hA, hB, hC => by
    have := hA 0 le_rfl; have := hB 0 le_rfl
    simp only [sumador, tam_xorP]; omega
  | j + 1, A, B, C, S, c₀, hA, hB, hC => by
    have h0 := hA 0 (Nat.zero_le _); have h1 := hB 0 (Nat.zero_le _)
    have ih := tam_sumador j (fun i => A (i + 1)) (fun i => B (i + 1)) (maj (A 0) (B 0) C) S (4 * S + c₀ + 4)
      (fun i hi => hA (i + 1) (by omega)) (fun i hi => hB (i + 1) (by omega)) (by simp only [tam_maj]; omega)
    rw [sumador]
    have e : (j + 1 + 1) * (10 * S + 30) = (j + 1) * (10 * S + 30) + (10 * S + 30) := Nat.succ_mul _ _
    omega

/-- **La comparación**, recorriendo los bits desde el 0 con un acumulador: «`a < b`, o `a = b` y `C`». El
acumulador aparece una sola vez en el paso. -/
def menorAcc : Bits → Bits → FP → ℕ → FP
  | _, _, C, 0 => C
  | A, B, C, W + 1 =>
      menorAcc (fun i => A (i + 1)) (fun i => B (i + 1)) (.or (.and (neg (A 0)) (B 0)) (.and (iffP (A 0) (B 0)) C)) W

theorem menorAcc_eval (σ : ℕ → Bool) : ∀ (W : ℕ) (A B : Bits) (C : FP) (a b : ℕ),
    a < 2 ^ W → b < 2 ^ W → (∀ i, evalB σ (A i) = a.testBit i) → (∀ i, evalB σ (B i) = b.testBit i) →
    (evalB σ (menorAcc A B C W) = true ↔ (a < b ∨ (a = b ∧ evalB σ C = true)))
  | 0, A, B, C, a, b, ha, hb, _, _ => by
    simp only [menorAcc]
    have : a = 0 := by simpa using ha
    have : b = 0 := by simpa using hb
    subst a b; simp
  | W + 1, A, B, C, a, b, ha, hb, hA, hB => by
    rw [menorAcc]
    rw [menorAcc_eval σ W _ _ _ (a / 2) (b / 2) (by rw [pow_succ] at ha; omega) (by rw [pow_succ] at hb; omega)
      (fun i => by rw [hA, Nat.testBit_div_two]) (fun i => by rw [hB, Nat.testBit_div_two])]
    simp only [evalB, evalB_neg, evalB_iffP, hA, hB, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h₁ | h₁ <;> rcases Nat.mod_two_eq_zero_or_one b with h₂ | h₂ <;>
      cases evalB σ C <;> simp [h₁, h₂] <;> omega

theorem tam_menorAcc : ∀ (W : ℕ) (A B : Bits) (C : FP) (S c₀ : ℕ),
    (∀ i < W, tam (A i) ≤ S) → (∀ i < W, tam (B i) ≤ S) → tam C ≤ c₀ →
    tam (menorAcc A B C W) ≤ c₀ + W * (6 * S + 12)
  | 0, _, _, C, S, c₀, _, _, hC => by simpa [menorAcc] using hC
  | W + 1, A, B, C, S, c₀, hA, hB, hC => by
    have h0 := hA 0 (by omega); have h1 := hB 0 (by omega)
    have ih := tam_menorAcc W (fun i => A (i + 1)) (fun i => B (i + 1))
      (.or (.and (neg (A 0)) (B 0)) (.and (iffP (A 0) (B 0)) C)) S (c₀ + 6 * S + 12)
      (fun i hi => hA (i + 1) (by omega)) (fun i hi => hB (i + 1) (by omega))
      (by simp only [tam, tam_neg, tam_iffP]; omega)
    rw [menorAcc]
    have e : (W + 1) * (6 * S + 12) = W * (6 * S + 12) + (6 * S + 12) := Nat.succ_mul _ _
    omega

/-- `a ≤ b` en `W` bits. -/
def leF (A B : Bits) (W : ℕ) : FP := menorAcc A B verd W
/-- `a = b` en `W` bits. -/
def eqF (A B : Bits) (W : ℕ) : FP := .and (leF A B W) (leF B A W)

theorem leF_eval (σ : ℕ → Bool) {W : ℕ} {A B : Bits} {a b : ℕ} (ha : a < 2 ^ W) (hb : b < 2 ^ W)
    (hA : ∀ i, evalB σ (A i) = a.testBit i) (hB : ∀ i, evalB σ (B i) = b.testBit i) :
    evalB σ (leF A B W) = decide (a ≤ b) := by
  have h := menorAcc_eval σ W A B verd a b ha hb hA hB
  simp only [evalB_verd, and_true] at h
  rw [Bool.eq_iff_iff, leF, h]; simp; omega

theorem eqF_eval (σ : ℕ → Bool) {W : ℕ} {A B : Bits} {a b : ℕ} (ha : a < 2 ^ W) (hb : b < 2 ^ W)
    (hA : ∀ i, evalB σ (A i) = a.testBit i) (hB : ∀ i, evalB σ (B i) = b.testBit i) :
    evalB σ (eqF A B W) = decide (a = b) := by
  simp only [eqF, evalB, leF_eval σ ha hb hA hB, leF_eval σ hb ha hB hA]
  rw [Bool.eq_iff_iff]; simp; omega

/-! ## Términos -/

/-- Los términos que se traducen: variables, `0`, sucesor, suma y mitad. -/
def EsSimple : Termino → Prop
  | .var _ => True
  | .cero => True
  | .suc t => EsSimple t
  | .suma t u => EsSimple t ∧ EsSimple u
  | .mitad t => EsSimple t
  | .prod _ _ => False
  | .largo _ => False
  | .smash _ _ => False

/-- **Los bits de un término**, dados los bits de las variables (`E i`). Fuera de la clase, `fals`. -/
def bitsT (E : ℕ → Bits) : Termino → Bits
  | .var i => E i
  | .cero => fun _ => fals
  | .suc t => sumador (bitsT E t) (fun _ => fals) verd
  | .suma t u => sumador (bitsT E t) (bitsT E u) fals
  | .mitad t => fun j => bitsT E t (j + 1)
  | .prod _ _ => fun _ => fals
  | .largo _ => fun _ => fals
  | .smash _ _ => fun _ => fals

/-- **El ancho de un término**: si las variables miden menos de `2^w`, el término mide menos de `2^(anchoT w t)`. -/
def anchoT (w : ℕ) : Termino → ℕ
  | .var _ => w
  | .cero => 0
  | .suc t => anchoT w t + 1
  | .suma t u => max (anchoT w t) (anchoT w u) + 1
  | .mitad t => anchoT w t
  | .prod _ _ => 0
  | .largo _ => 0
  | .smash _ _ => 0

/-- **Corrección de los términos.** -/
theorem bitsT_eval (σ : ℕ → Bool) {E : ℕ → Bits} {ρ : Entorno} {w : ℕ}
    (hE : ∀ i j, evalB σ (E i j) = (ρ i).testBit j) (hw : ∀ i, ρ i < 2 ^ w) :
    ∀ t : Termino, EsSimple t →
      (∀ j, evalB σ (bitsT E t j) = (t.val ρ).testBit j) ∧ t.val ρ < 2 ^ anchoT w t
  | .var i, _ => ⟨hE i, hw i⟩
  | .cero, _ => ⟨fun j => by simp [bitsT, Termino.val], by simp [Termino.val, anchoT]⟩
  | .suc t, ht => by
    obtain ⟨h₁, h₂⟩ := bitsT_eval σ hE hw t ht
    refine ⟨fun j => ?_, ?_⟩
    · have := sumador_eval σ j (bitsT E t) (fun _ => fals) verd (t.val ρ) 0 true h₁ (by simp) rfl
      simpa [bitsT, Termino.val] using this
    · simp only [Termino.val, anchoT, pow_succ]; omega
  | .suma t u, ⟨ht, hu⟩ => by
    obtain ⟨h₁, h₂⟩ := bitsT_eval σ hE hw t ht
    obtain ⟨h₃, h₄⟩ := bitsT_eval σ hE hw u hu
    refine ⟨fun j => ?_, ?_⟩
    · have := sumador_eval σ j (bitsT E t) (bitsT E u) fals (t.val ρ) (u.val ρ) false h₁ h₃ rfl
      simpa [bitsT, Termino.val] using this
    · have e₁ : 2 ^ anchoT w t ≤ 2 ^ max (anchoT w t) (anchoT w u) :=
        Nat.pow_le_pow_right (by decide) (le_max_left _ _)
      have e₂ : 2 ^ anchoT w u ≤ 2 ^ max (anchoT w t) (anchoT w u) :=
        Nat.pow_le_pow_right (by decide) (le_max_right _ _)
      simp only [Termino.val, anchoT, pow_succ]; omega
  | .mitad t, ht => by
    obtain ⟨h₁, h₂⟩ := bitsT_eval σ hE hw t ht
    refine ⟨fun j => ?_, ?_⟩
    · simp only [bitsT, Termino.val, h₁, Nat.testBit_div_two]
    · simp only [Termino.val, anchoT]; exact lt_of_le_of_lt (Nat.div_le_self _ _) h₂

/-- **Cota del tamaño de los bits de un término**, para los bits `j ≤ J`. -/
def cotaBits : Termino → ℕ → ℕ
  | .var _, _ => 3
  | .cero, _ => 1
  | .suc t, J => 6 + (J + 1) * (10 * (cotaBits t J + 1) + 30)
  | .suma t u, J => 2 + (J + 1) * (10 * (cotaBits t J + cotaBits u J) + 30)
  | .mitad t, J => cotaBits t (J + 1)
  | .prod _ _, _ => 1
  | .largo _, _ => 1
  | .smash _ _, _ => 1

theorem tam_bitsT {E : ℕ → Bits} (hE : ∀ i j, tam (E i j) ≤ 3) :
    ∀ (t : Termino) (j J : ℕ), j ≤ J → tam (bitsT E t j) ≤ cotaBits t J
  | .var i, j, _, _ => hE i j
  | .cero, _, _, _ => by simp [bitsT, cotaBits]
  | .suc t, j, J, hj => by
    have h := tam_sumador j (bitsT E t) (fun _ => fals) verd (cotaBits t J + 1) 3
      (fun i hi => by have := tam_bitsT hE t i J (by omega); omega) (fun _ _ => by simp) (by simp)
    have hm : (j + 1) * (10 * (cotaBits t J + 1) + 30) ≤ (J + 1) * (10 * (cotaBits t J + 1) + 30) :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [bitsT, cotaBits]; omega
  | .suma t u, j, J, hj => by
    have h := tam_sumador j (bitsT E t) (bitsT E u) fals (cotaBits t J + cotaBits u J) 1
      (fun i hi => by have := tam_bitsT hE t i J (by omega); omega)
      (fun i hi => by have := tam_bitsT hE u i J (by omega); omega) (by simp)
    have hm : (j + 1) * (10 * (cotaBits t J + cotaBits u J) + 30) ≤
        (J + 1) * (10 * (cotaBits t J + cotaBits u J) + 30) := Nat.mul_le_mul_right _ (by omega)
    simp only [bitsT, cotaBits]; omega
  | .mitad t, j, J, hj => by simpa [bitsT, cotaBits] using tam_bitsT hE t (j + 1) (J + 1) (by omega)
  | .prod _ _, _, _, _ => by simp [bitsT, cotaBits]
  | .largo _, _, _, _ => by simp [bitsT, cotaBits]
  | .smash _ _, _, _, _ => by simp [bitsT, cotaBits]

theorem acotada_de_le {f g : ℕ → ℕ} (hg : Acotada g) (h : ∀ n, f n ≤ g n) : Acotada f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩

theorem acotada_const (c : ℕ) : Acotada fun _ => c := Termino.acotada_const c
theorem acotada_id : Acotada fun n => n := Termino.acotada_id

theorem cotaBits_acotada : ∀ t : Termino, Acotada (cotaBits t)
  | .var _ => acotada_const 3
  | .cero => acotada_const 1
  | .suc t => Cerradura.suma (acotada_const 6) (Cerradura.producto (Cerradura.suma acotada_id (acotada_const 1))
      (Cerradura.suma (Cerradura.producto (acotada_const 10) (Cerradura.suma (cotaBits_acotada t) (acotada_const 1)))
        (acotada_const 30)))
  | .suma t u => Cerradura.suma (acotada_const 2) (Cerradura.producto (Cerradura.suma acotada_id (acotada_const 1))
      (Cerradura.suma (Cerradura.producto (acotada_const 10) (Cerradura.suma (cotaBits_acotada t) (cotaBits_acotada u)))
        (acotada_const 30)))
  | .mitad t => by
    have := Cerradura.composicion (cotaBits_acotada t) (Cerradura.suma acotada_id (acotada_const 1))
    exact this
  | .prod _ _ => acotada_const 1
  | .largo _ => acotada_const 1
  | .smash _ _ => acotada_const 1

theorem anchoT_acotada : ∀ t : Termino, Acotada fun w => anchoT w t
  | .var _ => acotada_id
  | .cero => acotada_const 0
  | .suc t => Cerradura.suma (anchoT_acotada t) (acotada_const 1)
  | .suma t u => acotada_de_le (Cerradura.suma (Cerradura.suma (anchoT_acotada t) (anchoT_acotada u)) (acotada_const 1))
      fun w => by simp only [anchoT]; omega
  | .mitad t => anchoT_acotada t
  | .prod _ _ => acotada_const 0
  | .largo _ => acotada_const 0
  | .smash _ _ => acotada_const 0

/-! ## «`k ≤ |v|`» con los bits de `v` -/

/-- `k ≤ |v|`: para `k = 0`, verdadero; para `k + 1`, algún bit `j ≥ k` de `v` (de los `W` primeros) vale `1`. -/
def geLargo (B : Bits) (W : ℕ) : ℕ → FP
  | 0 => verd
  | k + 1 => disjL ((List.range W).map fun j => if k ≤ j then B j else fals)

theorem geLargo_eval (σ : ℕ → Bool) {B : Bits} {W v : ℕ} (hv : v < 2 ^ W)
    (hB : ∀ j, evalB σ (B j) = v.testBit j) (k : ℕ) :
    evalB σ (geLargo B W k) = true ↔ k ≤ Nat.size v := by
  cases k with
  | zero => simp [geLargo]
  | succ k =>
    rw [geLargo, evalB_disjL, Nat.succ_le_iff, Nat.lt_size]
    constructor
    · rintro ⟨p, hp, hpv⟩
      simp only [List.mem_map, List.mem_range] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      split at hpv
      · rw [hB] at hpv
        exact le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.ge_two_pow_of_testBit hpv)
      · simp at hpv
    · intro hk
      by_contra hno
      have : v < 2 ^ k := by
        apply Nat.lt_pow_two_of_testBit
        intro j hj
        by_cases hjW : j < W
        · cases hvj : v.testBit j
          · rfl
          · exact absurd ⟨if k ≤ j then B j else fals, List.mem_map.mpr ⟨j, List.mem_range.mpr hjW, rfl⟩,
              by simp [show k ≤ j by omega, hB, hvj]⟩ hno
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
      omega

theorem tam_geLargo {B : Bits} {W S : ℕ} (hB : ∀ j < W, tam (B j) ≤ S) (k : ℕ) :
    tam (geLargo B W k) ≤ W * (S + 2) + 3 := by
  cases k with
  | zero => simp [geLargo]
  | succ k =>
    rw [geLargo]
    have := tam_disjL (B := S + 1) ((List.range W).map fun j => if k ≤ j then B j else fals) (by
      intro p hp
      simp only [List.mem_map, List.mem_range] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      split
      · have := hB j hj; omega
      · simp)
    simp only [List.length_map, List.length_range] at this
    have e : W * (S + 1 + 1) = W * (S + 2) := rfl
    omega

/-! ## La traducción -/

/-- Agregar al frente una variable ligada con valor constante `k`. -/
def extE (k : ℕ) (E : ℕ → Bits) : ℕ → Bits
  | 0 => cte k
  | i + 1 => E i

/-- La traducción de un átomo: compara en el ancho mayor de los dos lados. -/
def atomoP (E : ℕ → Bits) (w : ℕ) (l : Lit) : FP :=
  match l.rel with
  | .le => leF (bitsT E l.izq) (bitsT E l.der) (max (anchoT w l.izq) (anchoT w l.der))
  | .eq => eqF (bitsT E l.izq) (bitsT E l.der) (max (anchoT w l.izq) (anchoT w l.der))
  | .nle => neg (leF (bitsT E l.izq) (bitsT E l.der) (max (anchoT w l.izq) (anchoT w l.der)))
  | .neq => neg (eqF (bitsT E l.izq) (bitsT E l.der) (max (anchoT w l.izq) (anchoT w l.der)))

/-- **La traducción `⟦φ⟧`** con ancho `w` para las variables y sus bits `E`. El «para todo `x ≤ |t|`» es una
conjunción de `W + 1` casos, con `W` el ancho de `t`; el «existe `x ≤ |t|`», una disyunción. Un «existe» con cota
que no sea un largo queda fuera de la clase y se traduce como `fals`. -/
def trad : Formula → ℕ → (ℕ → Bits) → FP
  | .atomo l, w, E => atomoP E w l
  | .conj φ ψ, w, E => .and (trad φ w E) (trad ψ w E)
  | .disy φ ψ, w, E => .or (trad φ w E) (trad ψ w E)
  | .pt t φ, w, E =>
      conjL ((List.range (anchoT w t + 1)).map fun k =>
        .imp (geLargo (bitsT E t) (anchoT w t) k) (trad φ (w + anchoT w t) (extE k E)))
  | .ex t φ, w, E =>
      match t with
      | .largo u =>
        disjL ((List.range (anchoT w u + 1)).map fun k =>
          .and (geLargo (bitsT E u) (anchoT w u) k) (trad φ (w + anchoT w u) (extE k E)))
      | _ => fals

/-- **La clase Σᵇ₀ que se traduce**: átomos entre términos simples, «y», «o», y solo cuantificadores agudos: «para
todo `x ≤ |t|`» y «existe `x ≤ |t|`» con `t` simple. -/
def EsSb0 : Formula → Prop
  | .atomo l => EsSimple l.izq ∧ EsSimple l.der
  | .conj φ ψ => EsSb0 φ ∧ EsSb0 ψ
  | .disy φ ψ => EsSb0 φ ∧ EsSb0 ψ
  | .pt t φ => EsSimple t ∧ EsSb0 φ
  | .ex t φ => (∃ u, t = .largo u ∧ EsSimple u) ∧ EsSb0 φ

theorem atomoP_eval (σ : ℕ → Bool) {E : ℕ → Bits} {ρ : Entorno} {w : ℕ}
    (hE : ∀ i j, evalB σ (E i j) = (ρ i).testBit j) (hw : ∀ i, ρ i < 2 ^ w) (l : Lit)
    (hl : EsSimple l.izq ∧ EsSimple l.der) : evalB σ (atomoP E w l) = l.vale ρ := by
  obtain ⟨h₁, h₂⟩ := bitsT_eval σ hE hw l.izq hl.1
  obtain ⟨h₃, h₄⟩ := bitsT_eval σ hE hw l.der hl.2
  have e₁ : l.izq.val ρ < 2 ^ max (anchoT w l.izq) (anchoT w l.der) :=
    lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have e₂ : l.der.val ρ < 2 ^ max (anchoT w l.izq) (anchoT w l.der) :=
    lt_of_lt_of_le h₄ (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  obtain ⟨r, t, u⟩ := l
  cases r <;> simp only [atomoP, Lit.vale, Rel.vale, evalB_neg, leF_eval σ e₁ e₂ h₁ h₃, eqF_eval σ e₁ e₂ h₁ h₃]

theorem extE_eval (σ : ℕ → Bool) {E : ℕ → Bits} {ρ : Entorno} (hE : ∀ i j, evalB σ (E i j) = (ρ i).testBit j)
    (k : ℕ) : ∀ i j, evalB σ (extE k E i j) = (ext k ρ i).testBit j
  | 0, j => evalB_cte σ k j
  | i + 1, j => hE i j

theorem ext_lt {ρ : Entorno} {w W k : ℕ} (hw : ∀ i, ρ i < 2 ^ w) (hk : k ≤ W) : ∀ i, ext k ρ i < 2 ^ (w + W)
  | 0 => lt_of_le_of_lt hk (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega)))
  | i + 1 => lt_of_lt_of_le (hw i) (Nat.pow_le_pow_right (by decide) (by omega))

/-- **Corrección de la traducción**: con bits de las variables que corresponden al entorno, la fórmula
proposicional vale si y solo si la fórmula acotada vale. -/
theorem trad_eval (σ : ℕ → Bool) : ∀ (φ : Formula), EsSb0 φ → ∀ (w : ℕ) (E : ℕ → Bits) (ρ : Entorno),
    (∀ i j, evalB σ (E i j) = (ρ i).testBit j) → (∀ i, ρ i < 2 ^ w) →
    (evalB σ (trad φ w E) = true ↔ Formula.Vale φ ρ)
  | .atomo l, hφ, w, E, ρ, hE, hw => by
    rw [trad, atomoP_eval σ hE hw l hφ]; rfl
  | .conj φ ψ, ⟨h₁, h₂⟩, w, E, ρ, hE, hw => by
    simp only [trad, evalB, Bool.and_eq_true, Formula.Vale, trad_eval σ φ h₁ w E ρ hE hw,
      trad_eval σ ψ h₂ w E ρ hE hw]
  | .disy φ ψ, ⟨h₁, h₂⟩, w, E, ρ, hE, hw => by
    simp only [trad, evalB, Bool.or_eq_true, Formula.Vale, trad_eval σ φ h₁ w E ρ hE hw,
      trad_eval σ ψ h₂ w E ρ hE hw]
  | .pt t φ, ⟨ht, hφ⟩, w, E, ρ, hE, hw => by
    obtain ⟨hb, hv⟩ := bitsT_eval σ hE hw t ht
    have hsz : Nat.size (t.val ρ) ≤ anchoT w t := Nat.size_le.mpr hv
    rw [trad, evalB_conjL, Formula.Vale]
    simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h x hx
      have := h x (by omega)
      simp only [evalB, Bool.or_eq_true, Bool.not_eq_true'] at this
      rcases this with h' | h'
      · have := (geLargo_eval σ hv hb x).not.mp (by simp [h'])
        exact absurd hx this
      · exact (trad_eval σ φ hφ _ _ _ (extE_eval σ hE x) (ext_lt hw (by omega))).mp h'
    · intro h k hk
      simp only [evalB, Bool.or_eq_true, Bool.not_eq_true']
      by_cases hkt : k ≤ Nat.size (t.val ρ)
      · exact Or.inr ((trad_eval σ φ hφ _ _ _ (extE_eval σ hE k) (ext_lt hw (by omega))).mpr (h k hkt))
      · left
        cases hg : evalB σ (geLargo (bitsT E t) (anchoT w t) k)
        · rfl
        · exact absurd ((geLargo_eval σ hv hb k).mp hg) hkt
  | .ex t φ, ⟨⟨u, htu, hu⟩, hφ⟩, w, E, ρ, hE, hw => by
    subst htu
    obtain ⟨hb, hv⟩ := bitsT_eval σ hE hw u hu
    have hsz : Nat.size (u.val ρ) ≤ anchoT w u := Nat.size_le.mpr hv
    rw [trad, evalB_disjL, Formula.Vale]
    simp only [List.mem_map, List.mem_range, Termino.val]
    constructor
    · rintro ⟨p, ⟨k, hk, rfl⟩, hp⟩
      simp only [evalB, Bool.and_eq_true] at hp
      exact ⟨k, (geLargo_eval σ hv hb k).mp hp.1,
        (trad_eval σ φ hφ _ _ _ (extE_eval σ hE k) (ext_lt hw (by omega))).mp hp.2⟩
    · rintro ⟨k, hk, hφk⟩
      refine ⟨_, ⟨k, by omega, rfl⟩, ?_⟩
      simp only [evalB, Bool.and_eq_true]
      exact ⟨(geLargo_eval σ hv hb k).mpr hk,
        (trad_eval σ φ hφ _ _ _ (extE_eval σ hE k) (ext_lt hw (by omega))).mpr hφk⟩

/-! ## El tamaño de la traducción -/

/-- El cuerpo de un largo (para acotar el «existe»). -/
def cuerpoLargo : Termino → Termino
  | .largo u => u
  | t => t

/-- Cota del tamaño de un átomo con ancho `w`. -/
def cotaAtomo (l : Lit) (w : ℕ) : ℕ :=
  2 * (3 + (anchoT w l.izq + anchoT w l.der) *
    (6 * (cotaBits l.izq (anchoT w l.izq + anchoT w l.der) + cotaBits l.der (anchoT w l.izq + anchoT w l.der)) + 12)) + 3

/-- **Cota del tamaño de la traducción**, como función del ancho `w`. -/
def cotaF : Formula → ℕ → ℕ
  | .atomo l, w => cotaAtomo l w
  | .conj φ ψ, w => cotaF φ w + cotaF ψ w + 1
  | .disy φ ψ, w => cotaF φ w + cotaF ψ w + 1
  | .pt t φ, w => (anchoT w t + 1) * (anchoT w t * (cotaBits t (anchoT w t) + 2) + 3 + cotaF φ (w + anchoT w t) + 2) + 3
  | .ex t φ, w => (anchoT w (cuerpoLargo t) + 1) *
      (anchoT w (cuerpoLargo t) * (cotaBits (cuerpoLargo t) (anchoT w (cuerpoLargo t)) + 2) + 3 +
        cotaF φ (w + anchoT w (cuerpoLargo t)) + 2) + 3

theorem tam_atomoP {E : ℕ → Bits} (hE : ∀ i j, tam (E i j) ≤ 3) (w : ℕ) (l : Lit) :
    tam (atomoP E w l) ≤ cotaAtomo l w := by
  obtain ⟨r, t, u⟩ := l
  simp only [cotaAtomo]
  have hmax : max (anchoT w t) (anchoT w u) ≤ anchoT w t + anchoT w u := by omega
  generalize anchoT w t + anchoT w u = W at hmax ⊢
  have hA : ∀ i < max (anchoT w t) (anchoT w u), tam (bitsT E t i) ≤ cotaBits t W + cotaBits u W :=
    fun i hi => by have := tam_bitsT hE t i W (by omega); omega
  have hB : ∀ i < max (anchoT w t) (anchoT w u), tam (bitsT E u i) ≤ cotaBits t W + cotaBits u W :=
    fun i hi => by have := tam_bitsT hE u i W (by omega); omega
  generalize cotaBits t W + cotaBits u W = S at hA hB ⊢
  have h₁ := tam_menorAcc _ _ _ verd S 3 hA hB (by simp)
  have h₂ := tam_menorAcc _ _ _ verd S 3 hB hA (by simp)
  have hm : max (anchoT w t) (anchoT w u) * (6 * S + 12) ≤ W * (6 * S + 12) := Nat.mul_le_mul_right _ hmax
  cases r <;> simp only [atomoP, leF, eqF, tam, tam_neg] at h₁ h₂ ⊢ <;> omega

theorem tam_extE {E : ℕ → Bits} (hE : ∀ i j, tam (E i j) ≤ 3) (k : ℕ) : ∀ i j, tam (extE k E i j) ≤ 3
  | 0, j => tam_cte k j
  | i + 1, j => hE i j

/-- Lo común al «para todo» y al «existe»: la lista de los `W + 1` casos. -/
theorem tam_casos {E : ℕ → Bits} (hE : ∀ i j, tam (E i j) ≤ 3) (t : Termino) (w : ℕ) (φ : Formula)
    (ih : ∀ w' E', (∀ i j, tam (E' i j) ≤ 3) → tam (trad φ w' E') ≤ cotaF φ w') (c : FP → FP → FP)
    (hc : ∀ a b, tam (c a b) = tam a + tam b + 1) :
    ∀ p ∈ (List.range (anchoT w t + 1)).map (fun k => c (geLargo (bitsT E t) (anchoT w t) k)
      (trad φ (w + anchoT w t) (extE k E))),
      tam p ≤ anchoT w t * (cotaBits t (anchoT w t) + 2) + 3 + cotaF φ (w + anchoT w t) + 1 := by
  intro p hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨k, -, rfl⟩ := hp
  rw [hc]
  have h₁ := tam_geLargo (B := bitsT E t) (W := anchoT w t) (S := cotaBits t (anchoT w t))
    (fun j hj => tam_bitsT hE t j _ (by omega)) k
  have h₂ := ih (w + anchoT w t) (extE k E) (tam_extE hE k)
  omega

/-- **Cota del tamaño.** -/
theorem tam_trad : ∀ (φ : Formula) (w : ℕ) (E : ℕ → Bits), (∀ i j, tam (E i j) ≤ 3) → tam (trad φ w E) ≤ cotaF φ w
  | .atomo l, w, E, hE => tam_atomoP hE w l
  | .conj φ ψ, w, E, hE => by
    have := tam_trad φ w E hE; have := tam_trad ψ w E hE
    simp only [trad, tam, cotaF]; omega
  | .disy φ ψ, w, E, hE => by
    have := tam_trad φ w E hE; have := tam_trad ψ w E hE
    simp only [trad, tam, cotaF]; omega
  | .pt t φ, w, E, hE => by
    have h := tam_conjL _ (tam_casos hE t w φ (fun w' E' hE' => tam_trad φ w' E' hE') Proposition.imp
      (fun _ _ => by simp only [tam]))
    simp only [List.length_map, List.length_range] at h
    simp only [trad, cotaF]; exact h
  | .ex t φ, w, E, hE => by
    cases t with
    | largo u =>
      have h := tam_disjL _ (tam_casos hE u w φ (fun w' E' hE' => tam_trad φ w' E' hE') Proposition.and
        (fun _ _ => by simp only [tam]))
      simp only [List.length_map, List.length_range] at h
      have e : ∀ X Y : ℕ, X * (Y + 1 + 1) = X * (Y + 2) := fun _ _ => rfl
      rw [e] at h
      simp only [trad, cotaF, cuerpoLargo]; omega
    | _ => simp [trad, cotaF]

theorem cotaAtomo_acotada (l : Lit) : Acotada (cotaAtomo l) := by
  have hW := Cerradura.suma (anchoT_acotada l.izq) (anchoT_acotada l.der)
  have hS := Cerradura.suma (Cerradura.composicion (cotaBits_acotada l.izq) hW)
    (Cerradura.composicion (cotaBits_acotada l.der) hW)
  exact Cerradura.suma (Cerradura.producto (acotada_const 2) (Cerradura.suma (acotada_const 3)
    (Cerradura.producto hW (Cerradura.suma (Cerradura.producto (acotada_const 6) hS) (acotada_const 12)))))
    (acotada_const 3)

theorem casos_acotada (t : Termino) {g : ℕ → ℕ} (hg : Acotada g) :
    Acotada fun w => (anchoT w t + 1) * (anchoT w t * (cotaBits t (anchoT w t) + 2) + 3 + g (w + anchoT w t) + 2) + 3 := by
  have hW := anchoT_acotada t
  exact Cerradura.suma (Cerradura.producto (Cerradura.suma hW (acotada_const 1))
    (Cerradura.suma (Cerradura.suma (Cerradura.suma (Cerradura.producto hW
      (Cerradura.suma (Cerradura.composicion (cotaBits_acotada t) hW) (acotada_const 2))) (acotada_const 3))
      (Cerradura.composicion hg (Cerradura.suma acotada_id hW))) (acotada_const 2))) (acotada_const 3)

/-- **La cota es un polinomio** en el ancho. -/
theorem cotaF_acotada : ∀ φ : Formula, Acotada (cotaF φ)
  | .atomo l => cotaAtomo_acotada l
  | .conj φ ψ => Cerradura.suma (Cerradura.suma (cotaF_acotada φ) (cotaF_acotada ψ)) (acotada_const 1)
  | .disy φ ψ => Cerradura.suma (Cerradura.suma (cotaF_acotada φ) (cotaF_acotada ψ)) (acotada_const 1)
  | .pt t φ => casos_acotada t (cotaF_acotada φ)
  | .ex t φ => casos_acotada (cuerpoLargo t) (cotaF_acotada φ)

/-! ## La familia `⟦φ⟧ₙ` -/

/-- Los bits de la entrada `x` de largo `n`: el átomo `j` para `j < n`, `fals` después. -/
def entrada (n : ℕ) : Bits := fun j => if j < n then .atom j else fals

/-- Las variables: la `0` es la entrada; las demás (libres, si las hay) valen `0`. -/
def entradaE (n : ℕ) : ℕ → Bits
  | 0 => entrada n
  | _ + 1 => fun _ => fals

/-- **`⟦φ⟧ₙ`**: la traducción proposicional de `φ(x)` para `x` de largo `n`. -/
def traduce (φ : Formula) (n : ℕ) : FP := trad φ n (entradaE n)

/-- El número cuyos `n` bits bajos son `σ 0, …, σ (n-1)`. -/
def numDe (σ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.bit (σ 0) (numDe (fun i => σ (i + 1)) n)

theorem testBit_numDe : ∀ (n : ℕ) (σ : ℕ → Bool) (j : ℕ), (numDe σ n).testBit j = (decide (j < n) && σ j)
  | 0, σ, j => by simp [numDe]
  | n + 1, σ, 0 => by simp [numDe]
  | n + 1, σ, j + 1 => by
    rw [numDe, Nat.testBit_bit_succ, testBit_numDe n]; simp

theorem numDe_lt : ∀ (n : ℕ) (σ : ℕ → Bool), numDe σ n < 2 ^ n
  | 0, _ => by simp [numDe]
  | n + 1, σ => by
    have := numDe_lt n (fun i => σ (i + 1))
    rw [numDe, Nat.bit_val, pow_succ]; cases σ 0 <;> simp <;> omega

theorem numDe_testBit {n x : ℕ} (hx : x < 2 ^ n) : numDe (fun j => x.testBit j) n = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_numDe]
  by_cases hj : j < n
  · simp [hj]
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- El entorno con la entrada `x` y las demás variables en `0`. -/
def entorno (x : ℕ) : Entorno := ext x fun _ => 0

theorem entradaE_eval (σ : ℕ → Bool) (n : ℕ) :
    ∀ i j, evalB σ (entradaE n i j) = (entorno (numDe σ n) i).testBit j
  | 0, j => by
    simp only [entradaE, entrada, entorno, ext, testBit_numDe]
    by_cases hj : j < n <;> simp [hj, evalB]
  | _ + 1, j => by simp [entradaE, entorno, ext]

theorem entorno_lt {n x : ℕ} (hx : x < 2 ^ n) : ∀ i, entorno x i < 2 ^ n
  | 0 => hx
  | _ + 1 => Nat.two_pow_pos _

/-- **Corrección, asignación por asignación**: `⟦φ⟧ₙ` vale con `σ` si y solo si `φ` vale en el número que forman
los `n` primeros bits de `σ`. -/
theorem traduce_eval {φ : Formula} (hφ : EsSb0 φ) (n : ℕ) (σ : ℕ → Bool) :
    (traduce φ n).eval σ = true ↔ Formula.Vale φ (entorno (numDe σ n)) := by
  rw [← evalB_eq]
  exact trad_eval σ φ hφ n (entradaE n) _ (entradaE_eval σ n) (entorno_lt (numDe_lt n σ))

/-- **Meta 2, corrección**: `⟦φ⟧ₙ` es tautología si y solo si `φ(x)` vale para todo `x` de largo a lo sumo `n`. -/
theorem traduce_tautologia {φ : Formula} (hφ : EsSb0 φ) (n : ℕ) :
    Tautologia (traduce φ n) ↔ ∀ x, Nat.size x ≤ n → Formula.Vale φ (entorno x) := by
  constructor
  · intro h x hx
    have hx' := Nat.size_le.mp hx
    have := (traduce_eval hφ n (fun j => x.testBit j)).mp (h _)
    rwa [numDe_testBit hx'] at this
  · intro h σ
    exact (traduce_eval hφ n σ).mpr (h _ (Nat.size_le.mpr (numDe_lt n σ)))

theorem tam_entradaE (n : ℕ) : ∀ i j, tam (entradaE n i j) ≤ 3
  | 0, j => by simp only [entradaE, entrada]; split <;> simp [tam]
  | _ + 1, _ => by simp [entradaE]

/-- **Meta 2, tamaño**: `|⟦φ⟧ₙ| ≤ cotaF φ n`, un polinomio en `n` (para toda `φ`, en la clase o no). -/
theorem tam_traduce (φ : Formula) (n : ℕ) : tam (traduce φ n) ≤ cotaF φ n :=
  tam_trad φ n (entradaE n) (tam_entradaE n)

theorem traduce_acotada (φ : Formula) : Acotada fun n => tam (traduce φ n) :=
  acotada_de_le (cotaF_acotada φ) (tam_traduce φ)

/-! ## Meta 3: lo que sale por reglas lógicas tiene pruebas de Frege de largo constante -/

/-- Los átomos del esqueleto: dos términos y la relación (`true` es `≤`, `false` es `=`). -/
abbrev AtomoE := Termino × Termino × Bool

/-- El esqueleto de un literal: `≤` e `=` son átomos; sus negaciones, la negación del átomo. -/
def esqLit (l : Lit) : Proposition AtomoE :=
  match l.rel with
  | .le => .atom (l.izq, l.der, true)
  | .eq => .atom (l.izq, l.der, false)
  | .nle => .imp (.atom (l.izq, l.der, true)) .falsum
  | .neq => .imp (.atom (l.izq, l.der, false)) .falsum

/-- **El esqueleto proposicional** de una fórmula sin cuantificadores: los átomos aritméticos se vuelven
variables proposicionales. -/
def esqueleto : Formula → Proposition AtomoE
  | .atomo l => esqLit l
  | .conj φ ψ => .and (esqueleto φ) (esqueleto ψ)
  | .disy φ ψ => .or (esqueleto φ) (esqueleto ψ)
  | .pt _ _ => .falsum
  | .ex _ _ => .falsum

/-- Sin cuantificadores. -/
def SinCuantif : Formula → Prop
  | .atomo _ => True
  | .conj φ ψ => SinCuantif φ ∧ SinCuantif ψ
  | .disy φ ψ => SinCuantif φ ∧ SinCuantif ψ
  | .pt _ _ => False
  | .ex _ _ => False

/-- Lo que reemplaza a cada átomo del esqueleto: la comparación en bits. -/
def sustAtomo (E : ℕ → Bits) (w : ℕ) : AtomoE → FP
  | (t, u, true) => leF (bitsT E t) (bitsT E u) (max (anchoT w t) (anchoT w u))
  | (t, u, false) => eqF (bitsT E t) (bitsT E u) (max (anchoT w t) (anchoT w u))

/-- **Sin cuantificadores, la traducción es una sustitución del esqueleto.** -/
theorem trad_eq_subst (E : ℕ → Bits) (w : ℕ) :
    ∀ φ : Formula, SinCuantif φ → trad φ w E = (esqueleto φ).subst (sustAtomo E w)
  | .atomo ⟨r, t, u⟩, _ => by cases r <;> rfl
  | .conj φ ψ, ⟨h₁, h₂⟩ => by
    rw [trad, trad_eq_subst E w φ h₁, trad_eq_subst E w ψ h₂]; rfl
  | .disy φ ψ, ⟨h₁, h₂⟩ => by
    rw [trad, trad_eq_subst E w φ h₁, trad_eq_subst E w ψ h₂]; rfl

/-- Los axiomas de Frege son esquemas: se conservan al sustituir átomos. -/
theorem isAxiom_subst {V W : Type} (f : V → Proposition W) {φ : Proposition V} (h : Frege.IsAxiom φ) :
    Frege.IsAxiom (φ.subst f) := by
  cases h with
  | k φ ψ => exact .k _ _
  | s φ ψ χ => exact .s _ _ _
  | dne φ => exact .dne _
  | andElimL φ ψ => exact .andElimL _ _
  | andElimR φ ψ => exact .andElimR _ _
  | andIntro φ ψ => exact .andIntro _ _
  | orIntroL φ ψ => exact .orIntroL _ _
  | orIntroR φ ψ => exact .orIntroR _ _
  | orElim φ ψ χ => exact .orElim _ _ _

/-- **Las pruebas de Frege se conservan al sustituir átomos**, línea por línea. -/
theorem isProof_subst {V W : Type} (f : V → Proposition W) {Γ L : List (Proposition V)} (h : Frege.IsProof Γ L) :
    Frege.IsProof (Γ.map (·.subst f)) (L.map (·.subst f)) := by
  induction h with
  | nil => exact .nil
  | hyp _ hφ ih => exact ih.hyp (List.mem_map_of_mem hφ)
  | ax _ hφ ih => exact ih.ax (isAxiom_subst f hφ)
  | @mp L φ ψ _ h₁ h₂ ih =>
    exact ih.mp (φ := φ.subst f) (List.mem_map_of_mem h₁) (List.mem_map_of_mem (f := (·.subst f)) h₂)

theorem derivable_subst {V W : Type} (f : V → Proposition W) {Γ : List (Proposition V)} {φ : Proposition V}
    {m : ℕ} (h : Frege.DerivableInSize Γ φ m) : Frege.DerivableInSize (Γ.map (·.subst f)) (φ.subst f) m := by
  obtain ⟨L, hL, hφ, hlen⟩ := h
  exact ⟨L.map (·.subst f), isProof_subst f hL, List.mem_map_of_mem hφ, by simpa using hlen⟩

/-- **Meta 3.** Si el esqueleto de `φ` (sin cuantificadores) tiene una prueba de Frege de `m` líneas, toda la
familia `⟦φ⟧ₙ` tiene pruebas de Frege de `m` líneas: el número de líneas no crece con `n`. -/
theorem pruebas_cortas {φ : Formula} (hq : SinCuantif φ) {m : ℕ}
    (h : Frege.DerivableInSize [] (esqueleto φ) m) (n : ℕ) : Frege.DerivableInSize [] (traduce φ n) m := by
  rw [traduce, trad_eq_subst _ _ φ hq]
  simpa using derivable_subst (sustAtomo (entradaE n) n) h

/-- **La cadena entera, de la prueba a la verdad**: una prueba de Frege del esqueleto, sustituida, es una prueba de
`⟦φ⟧ₙ`; por la corrección de Frege (cslib) es tautología; por la meta 2, `φ(x)` vale para todo `x`. -/
theorem vale_de_esqueleto {φ : Formula} (hq : SinCuantif φ) (hφ : EsSb0 φ) {m : ℕ}
    (h : Frege.DerivableInSize [] (esqueleto φ) m) (x : ℕ) : Formula.Vale φ (entorno x) := by
  have ht : Tautologia (traduce φ (Nat.size x)) := by
    intro σ
    obtain ⟨L, hL, hmem, -⟩ := pruebas_cortas hq h (Nat.size x)
    exact hL.eval (by simp) _ hmem
  exact (traduce_tautologia hφ _).mp ht x le_rfl

/-- El tercero excluido, `p ∨ ¬p`, en `222` líneas de Frege (para cualquier `p`): desde `¬(p ∨ ¬p)` se llega a `⊥`
en `11` líneas, la deducción de cslib lo vuelve `¬¬(p ∨ ¬p)` (`10 · 2` por línea) y la doble negación cierra. -/
theorem tercero_excluido {V : Type} (p : Proposition V) :
    Frege.DerivableInSize [] (.or p (.imp p .falsum)) 222 := by
  set q : Proposition V := .or p (.imp p .falsum)
  have hbot : Frege.DerivableInSize ([] ++ [Proposition.imp q .falsum]) .falsum 11 := by
    have h := Frege.DerivableInSize.hyp (Γ := [] ++ [Proposition.imp q .falsum]) (φ := Proposition.imp q .falsum)
      (by simp)
    have a := (Frege.DerivableInSize.ax (Γ := [] ++ [Proposition.imp q .falsum])
      (Frege.IsAxiom.orIntroL p (Proposition.imp p .falsum))).trans h
    have b := (Frege.DerivableInSize.ax (Γ := [] ++ [Proposition.imp q .falsum])
      (Frege.IsAxiom.orIntroR p (Proposition.imp p .falsum))).mp a
    exact (h.mp b).mono (by omega)
  obtain ⟨M, hM, hb, hlen⟩ := hbot
  obtain ⟨L, g, hL⟩ := Frege.IsProof.deduction (Γ := []) (Δ := [Proposition.imp q .falsum]) hM (L := []) .nil
  have hnn : Frege.DerivableInSize [] (Proposition.imp (Proposition.imp q .falsum) .falsum) 220 :=
    ⟨L, g.proof, by simpa using hL _ hb, g.length_of_nil.trans (by simp; omega)⟩
  exact ((Frege.DerivableInSize.ax (Frege.IsAxiom.dne q)).mp hnn).mono (by omega)

/-! ## Controles -/

/-- Revisar `⟦φ⟧ₙ` en las `2^n` asignaciones que vienen de un número de largo `n`: un cómputo. -/
def chequeo (φ : Formula) (n : ℕ) : Bool :=
  (List.range (2 ^ n)).all fun x => evalB (fun j => x.testBit j) (traduce φ n)

/-- Si el chequeo pasa, `⟦φ⟧ₙ` es tautología (sobre **todas** las asignaciones, no solo las `2^n` revisadas). -/
theorem tautologia_de_chequeo {φ : Formula} (hφ : EsSb0 φ) {n : ℕ} (h : chequeo φ n = true) :
    Tautologia (traduce φ n) := by
  rw [traduce_tautologia hφ]
  intro x hx
  have hx' := Nat.size_le.mp hx
  have h₁ := List.all_eq_true.mp h x (List.mem_range.mpr hx')
  rw [evalB_eq, traduce_eval hφ, numDe_testBit hx'] at h₁
  exact h₁

/-- `x / 2 ≤ x`. -/
def mitadMenor : Formula := .atomo ⟨.le, .mitad (.var 0), .var 0⟩
/-- `⌊(x + x) / 2⌋ = x`: usa el sumador. -/
def mitadDoble : Formula := .atomo ⟨.eq, .mitad (.suma (.var 0) (.var 0)), .var 0⟩
/-- `∀ i ≤ |x|, i ≤ x`: usa el cuantificador agudo (dentro, la variable `0` es `i` y la `1` es `x`). -/
def largoMenor : Formula := .pt (.var 0) (.atomo ⟨.le, .var 0, .var 1⟩)
/-- `∃ i ≤ |x|, x ≤ i + i`: falsa para `x = 7` (`|7| = 3`, y `7 > 6`). -/
def existeFalso : Formula := .ex (.largo (.var 0)) (.atomo ⟨.le, .var 1, .suma (.var 0) (.var 0)⟩)
/-- `x + 1 ≰ x`: usa el acarreo desde el bit 0 (con `x = 1`, `3`, `7`). -/
def sucMayor : Formula := .atomo ⟨.nle, .suc (.var 0), .var 0⟩
/-- `x ≤ x / 2`: falsa para `x = 1`. -/
def mitadMayor : Formula := .atomo ⟨.le, .var 0, .mitad (.var 0)⟩
/-- `x ≤ x ∨ x > x`: el tercero excluido sobre un átomo. -/
def terceroX : Formula := .disy (.atomo ⟨.le, .var 0, .var 0⟩) (.atomo ⟨.nle, .var 0, .var 0⟩)

theorem chequeo_mitadMenor : chequeo mitadMenor 3 = true := by decide
theorem chequeo_mitadDoble : chequeo mitadDoble 3 = true := by decide
theorem chequeo_largoMenor : chequeo largoMenor 3 = true := by decide
theorem chequeo_sucMayor : chequeo sucMayor 3 = true := by decide

theorem taut_mitadMenor : Tautologia (traduce mitadMenor 3) :=
  tautologia_de_chequeo (by simp [mitadMenor, EsSb0, EsSimple]) chequeo_mitadMenor
theorem taut_mitadDoble : Tautologia (traduce mitadDoble 3) :=
  tautologia_de_chequeo (by simp [mitadDoble, EsSb0, EsSimple]) chequeo_mitadDoble
theorem taut_largoMenor : Tautologia (traduce largoMenor 3) :=
  tautologia_de_chequeo (by simp [largoMenor, EsSb0, EsSimple]) chequeo_largoMenor
theorem taut_sucMayor : Tautologia (traduce sucMayor 3) :=
  tautologia_de_chequeo (by simp [sucMayor, EsSb0, EsSimple]) chequeo_sucMayor

/-- **Control negativo**: `⟦x ≤ x/2⟧₃` no es tautología; la asignación de `x = 1` la hace falsa. -/
theorem no_taut_mitadMayor : ¬ Tautologia (traduce mitadMayor 3) := by
  intro h
  have := h (fun j => (1 : ℕ).testBit j)
  rw [← evalB_eq] at this
  exact absurd this (by decide)

/-- **Control negativo con cuantificador**: `⟦∃ i ≤ |x|, x ≤ i + i⟧₃` falla en `x = 7`. -/
theorem no_taut_existeFalso : ¬ Tautologia (traduce existeFalso 3) := by
  intro h
  have := h (fun j => (7 : ℕ).testBit j)
  rw [← evalB_eq] at this
  exact absurd this (by decide)

/-- La corrección dice lo mismo del lado aritmético: `x ≤ x/2` falla para algún `x` de largo `≤ 3`. -/
theorem mitadMayor_falla : ¬ ∀ x, Nat.size x ≤ 3 → Formula.Vale mitadMayor (entorno x) :=
  fun h => no_taut_mitadMayor ((traduce_tautologia (by simp [mitadMayor, EsSb0, EsSimple]) 3).mpr h)

/-- **Control de la meta 3**: `⟦x ≤ x ∨ x > x⟧ₙ` tiene una prueba de Frege de `222` líneas para todo `n`. -/
theorem terceroX_corto (n : ℕ) : Frege.DerivableInSize [] (traduce terceroX n) 222 :=
  pruebas_cortas (by simp [terceroX, SinCuantif]) (tercero_excluido _) n

/-- Y la cadena entera da la verdad: `x ≤ x ∨ x > x` para todo `x`. -/
theorem terceroX_vale (x : ℕ) : Formula.Vale terceroX (entorno x) :=
  vale_de_esqueleto (by simp [terceroX, SinCuantif]) (by simp [terceroX, EsSb0, EsSimple]) (tercero_excluido _) x

/-- La meta 3 no se aplica a una verdad aritmética: el esqueleto de `x/2 ≤ x` es una variable sola, que no es
tautología, así que no tiene prueba de Frege de ningún tamaño. -/
theorem esqueleto_mitadMenor_sin_prueba (m : ℕ) : ¬ Frege.DerivableInSize [] (esqueleto mitadMenor) m := by
  rintro ⟨L, hL, hmem, -⟩
  have := hL.eval (σ := fun _ => false) (by simp) _ hmem
  simp [esqueleto, mitadMenor, esqLit] at this

end EspejoEF
end Extraccion
end Sagitta.Map
