import Sagitta.Map.Completitud.Puente
import Sagitta.Map.Teoria
import Sagitta.Map.Infinito
import Sagitta.Map.CookS12
import Mathlib.ModelTheory.Ultraproducts

/-!
# El largo infinito de S¹₂: el que sí puede mentir

`Infinito.lean` se va al infinito por un ultrapoder de ℕ: un largo infinito es un ultrafiltro no principal. Ese
infinito es **demasiado honesto**: por Łoś, el ultrapoder satisface exactamente las mismas sentencias que ℕ, y por eso
solo da «infinitas veces» (`ambos_a_la_vez`), nunca una prueba. Aquí se cruza al otro lado, con la completitud
(`Completitud/Teorema.lean`, `Completitud/Puente.lean`): los modelos de S¹₂ que no son ℕ.

## Lo que se prueba

* **Irse al infinito en un modelo de S¹₂** (`no_deriva_iff_contraejemplo`): para una fórmula `φ(x)` de `L` con una
  variable libre, `S¹₂ ⊬ ∀x φ(x)` si y solo si hay un modelo **numerable** de S¹₂ con un elemento `a` donde `φ(a)` falla.
* **Ese `a` es no estándar** (`contraejemplo_no_estandar`, `largo_infinito_s12`), si S¹₂ demuestra cada instancia
  numérica `φ(n̄)`: `a` no es el valor de ningún numeral, y de hecho es **mayor que todos** (`mayor_que_todo_numeral`,
  por los axiomas BASIC: los numerales forman un segmento inicial, `segmento_inicial`).
* **La hipótesis**: se eligió «S¹₂ demuestra cada `φ(n̄)`» (`∀ n, DerivaS12 (instancia φ n)`) y no «`φ(n)` vale en ℕ».
  La primera es la que hace funcionar el argumento para **cualquier** `φ`, y es la natural: dice que la teoría ve cada
  caso finito, aunque no el enunciado general. La segunda alcanza cuando `φ` tiene todos sus cuantificadores acotados
  (`EsAcotada`), por la completitud para sentencias acotadas verdaderas; esa completitud **no** se prueba aquí: queda
  como `CompletitudAcotada` (una `Prop`), y `largo_infinito_s12_de_verdad` la toma como hipótesis.
* **La cota en todo largo es falsa** (`cota_falsa_en_uno`, `cotaInferiorSAT_vacia`): en el largo `1` toda función se
  calcula con una compuerta, así que «SAT necesita más de `n^k` compuertas en el largo `n`» falla en `n = 1` para todo
  `k`. Pedirla en **todo** largo (`cotaInferiorSAT`) deja hipótesis contradictorias: ninguna `φ` cumple a la vez
  `Expresa φ (cotaInferiorSAT k)` y «S¹₂ demuestra cada `φ(n̄)`». Esa versión se conserva solo para dejarlo demostrado.
* **La instancia de circuitos, como parámetro** (`cota_inferior_largo_infinito`), **y por qué todavía no dice nada de
  circuitos** (revisión adversaria, 24 nov). Con la cota pedida desde un largo `n₀` (`cotaInferiorSATDesde k n₀`), para
  una `φ` que la exprese en ℕ, si S¹₂ demuestra cada instancia pero no `∀n φ(n)`, la cota vale en ℕ desde `n₀` y hay un
  modelo numerable de S¹₂ con un largo no estándar donde `φ` falla. Pero `Expresa` es **extensional**: con las
  instancias demostradas, `φ` ya es verdadera en ℕ en todo `n`, y entonces «`φ` expresa la cota» equivale a «la cota vale
  en ℕ», sea cual sea `φ` (`expresa_solo_pide_verdad`). Cualquier `φ` verdadera con instancias demostrables y cierre no
  demostrable (del estilo de Gödel, sin relación con SAT) cumple las hipótesis si la cota vale. El teorema **no agrega
  contenido de circuitos** sobre `largo_infinito_s12`; para que `φ(a)` hable de circuitos en el modelo hace falta una
  codificación **intensional** de fórmulas y circuitos en `L`, que no está. Con `n₀ ≤ 1` las hipótesis son
  contradictorias (`desde_chico_vacia`), y con `k = 0` la cota en ℕ es trivial; lo abierto son las cotas en ℕ para `k`
  grande, no la existencia de una `φ` extensional.
* **El contraste con el ultrapoder** (`ultrapoder_honesto`, `contraste`): todo ultrapoder de ℕ es un modelo de S¹₂, tiene
  elementos no estándar si el ultrafiltro es no principal, y aun así **ninguna** `φ` verdadera en ℕ para todo `n` falla
  en él. El modelo del primer punto, en cambio, no satisface `∀x φ(x)`: no es elementalmente equivalente a ℕ.

## La lectura, para circuitos

**Esto es una lectura que el archivo no prueba.** Con una codificación intensional de circuitos en `L` (que no está),
si S¹₂ demostrara cada caso de la cota inferior de circuitos para SAT pero no la cota general, habría un modelo de S¹₂
con un largo infinito donde, **según el modelo**, SAT tiene circuitos chicos, aunque en ℕ no los tenga. Ese sería el
largo infinito que puede mentir. Lo que sí está probado es la mitad genérica: `largo_infinito_s12` (el contraejemplo
no estándar existe para cualquier `φ`) y el contraste con el ultrapoder (`contraste`), que no puede mentir.

El resultado conocido en esta dirección es Razborov 1995: bajo una hipótesis criptográfica (generadores pseudoaleatorios fuertes),
ciertos fragmentos de la aritmética acotada no demuestran cotas inferiores superpolinomiales de circuitos. Aquí **no** se
formaliza; su formulación (con el circuito como un objeto de segunda clase) no es la de este repo, y se cita solo como la
referencia de lo que este archivo deja planteado.

## Lo que no

* **La codificación** de fórmulas, circuitos y su evaluación dentro de `L`, que haría falta para escribir la fórmula
  `φ` de la cota inferior. El repo no la tiene y no se inventa una a medida: `cota_inferior_largo_infinito` es una
  implicación cuyas hipótesis toman la `φ` como parámetro, y `Expresa` solo fija lo que `φ` debe significar en ℕ. No se
  exhibe ninguna `φ` que las cumpla. Qué significa `φ(a)` en un
  modelo no estándar depende de la codificación y no se dice aquí.
* **`CompletitudAcotada`**: que S¹₂ demuestra toda sentencia acotada verdadera. Es la forma del resultado estándar para
  la aritmética acotada, pero **no se verificó** que el BASIC de este repo alcance para él; pide que los términos
  cerrados se evalúen bien sobre numerales, y eso no está. Si BASIC no alcanzara, la hipótesis sería falsa y
  `largo_infinito_s12_de_verdad` no diría nada.
* **Que `EsAcotada` contenga a `Σᵇᵢ`/`Πᵇᵢ`**: solo está `EsAguda.acotada`.
* **El largo `|a|`**: si la fórmula tiene como variable libre un número `x` y habla del largo `|x|`, que `a` sea no
  estándar no da por sí solo que `|a|` lo sea. Por eso la variable libre de `cotaInferiorSAT` es el largo mismo.
* **Una `φ` con contenido de circuitos.** Por `expresa_solo_pide_verdad`, las hipótesis de
  `cota_inferior_largo_infinito` no la piden: alcanza cualquier `φ` verdadera. Con `cotaInferiorSAT` (todo largo) o con
  `n₀ ≤ 1` no hay ninguna (`cotaInferiorSAT_vacia`, `desde_chico_vacia`).
-/

open FirstOrder FirstOrder.Language Filter

namespace Sagitta.Map
namespace Acotada
namespace LargoS12

/-! ## Numerales y elementos estándar -/

/-- **El numeral `n̄`**: `S(S(⋯S(0)))`, un término cerrado. -/
def numeral : ℕ → L.Term Empty
  | 0 => Term.func (Fun.cero : L.Functions 0) ![]
  | n + 1 => Term.func (Fun.suc : L.Functions 1) ![numeral n]

/-- **El valor del numeral `n̄`** en una estructura. -/
def valor (M : Type) [L.Structure M] (n : ℕ) : M := (numeral n).realize (Empty.elim : Empty → M)

section Valor

variable {M : Type} [L.Structure M]

theorem valor_cero : valor M 0 = cero := by
  unfold valor numeral cero
  rw [Term.realize_func]
  congr 1; funext i; exact i.elim0

theorem valor_succ (n : ℕ) : valor M (n + 1) = suc (valor M n) := by
  unfold valor suc
  rw [numeral, Term.realize_func]
  congr 1; funext i; fin_cases i; rfl

/-- En ℕ, el numeral `n̄` vale `n`. -/
@[simp] theorem valor_nat (n : ℕ) : valor ℕ n = n := by
  induction n with
  | zero => rw [valor_cero]; rfl
  | succ n ih => rw [valor_succ, ih]; rfl

/-- **Un elemento estándar**: el valor de algún numeral. -/
def EsEstandar (a : M) : Prop := ∃ n : ℕ, a = valor M n

/-- **Los numerales son un segmento inicial** en todo modelo de BASIC: lo que está debajo de un numeral es un numeral. -/
theorem segmento_inicial (hB : EsModeloBASIC M) : ∀ (n : ℕ) (x : M), le x (valor M n) → EsEstandar x
  | 0, x, h => ⟨0, by rw [valor_cero] at h ⊢; exact hB.b7 _ _ h (hB.b3 x)⟩
  | n + 1, x, h => by
    rw [valor_succ] at h
    rcases hB.b6 x (valor M n) with h1 | h1
    · by_cases he : valor M n = x
      · exact ⟨n, he.symm⟩
      · have h2 : le (suc (valor M n)) x := (hB.b4 (valor M n) x).1 ⟨h1, he⟩
        exact ⟨n + 1, by rw [valor_succ]; exact hB.b7 _ _ h h2⟩
    · exact segmento_inicial hB n x h1

/-- **Un elemento no estándar es mayor que todo numeral**: es un largo infinito, visto desde adentro del modelo. -/
theorem mayor_que_todo_numeral (hB : EsModeloBASIC M) {a : M} (ha : ¬ EsEstandar a) (n : ℕ) :
    le (valor M n) a ∧ valor M n ≠ a := by
  refine ⟨?_, fun h => ha ⟨n, h.symm⟩⟩
  rcases hB.b6 (valor M n) a with h | h
  · exact absurd (segmento_inicial hB n a h) ha
  · exact h

/-- En ℕ todo es estándar. -/
theorem nat_estandar (a : ℕ) : EsEstandar a := ⟨a, (valor_nat a).symm⟩

end Valor

/-! ## Las instancias numéricas -/

/-- **La instancia `φ(n̄)`**: la sentencia que resulta de poner el numeral en la variable libre. -/
def instancia (φ : L.Formula (Fin 1)) (n : ℕ) : L.Sentence := φ.subst fun _ => numeral n

theorem realize_instancia {M : Type} [L.Structure M] (φ : L.Formula (Fin 1)) (n : ℕ) :
    M ⊨ instancia φ n ↔ φ.Realize ![valor M n] := by
  rw [instancia, Sentence.Realize, Formula.Realize, BoundedFormula.realize_subst, Formula.Realize]
  apply iff_of_eq; congr 1
  · funext i; rw [Fin.fin_one_eq_zero i]
    change (numeral n).realize _ = (numeral n).realize _
    congr 1; funext e; exact e.elim

/-- Lo que S¹₂ demuestra de cada `n̄` vale en ℕ para cada `n`. -/
theorem verdad_de_instancias {φ : L.Formula (Fin 1)} (h : ∀ n, DerivaS12 (instancia φ n)) (n : ℕ) :
    φ.Realize ![n] := by
  have := verdadero_de_demuestra ((demuestra_iff_deriva _).2 (h n))
  rwa [realize_instancia, valor_nat] at this

/-! ## 1. Irse al infinito en un modelo de S¹₂ -/

/-- **`S¹₂ ⊬ ∀x φ(x)` si y solo si hay un modelo numerable de S¹₂ con un `a` donde `φ(a)` falla.** -/
theorem no_deriva_iff_contraejemplo (φ : L.Formula (Fin 1)) :
    ¬ DerivaS12 (cierre φ) ↔
      ∃ (M : Type) (_ : L.Structure M), Countable M ∧ EsModeloS12 M ∧ ∃ a : M, ¬ φ.Realize ![a] := by
  rw [no_deriva_iff_numerable]
  refine exists_congr fun M => exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [realize_cierre, forall_fin1, not_forall]

/-- **El contraejemplo es no estándar** si S¹₂ demuestra cada instancia numérica: en un modelo de S¹₂, `φ(n̄)` vale,
así que `φ` solo puede fallar fuera de los numerales. -/
theorem contraejemplo_no_estandar {φ : L.Formula (Fin 1)} (hinst : ∀ n, DerivaS12 (instancia φ n))
    {M : Type} [L.Structure M] (hM : EsModeloS12 M) {a : M} (ha : ¬ φ.Realize ![a]) : ¬ EsEstandar a := by
  rintro ⟨n, rfl⟩
  exact ha ((realize_instancia φ n).1 ((demuestra_iff_deriva _).2 (hinst n) M hM))

/-- **El largo infinito de S¹₂.** Si S¹₂ demuestra cada `φ(n̄)`, entonces `S¹₂ ⊬ ∀x φ(x)` si y solo si hay un modelo
numerable de S¹₂ con un elemento `a` **no estándar**, mayor que todo numeral, donde `φ(a)` falla. -/
theorem largo_infinito_s12 (φ : L.Formula (Fin 1)) (hinst : ∀ n, DerivaS12 (instancia φ n)) :
    ¬ DerivaS12 (cierre φ) ↔
      ∃ (M : Type) (_ : L.Structure M), Countable M ∧ EsModeloS12 M ∧
        ∃ a : M, ¬ φ.Realize ![a] ∧ ¬ EsEstandar a ∧ ∀ n : ℕ, le (valor M n) a ∧ valor M n ≠ a := by
  rw [no_deriva_iff_contraejemplo]
  constructor
  · rintro ⟨M, _, hc, hM, a, ha⟩
    have hs := contraejemplo_no_estandar hinst hM ha
    exact ⟨M, inferInstance, hc, hM, a, ha, hs, mayor_que_todo_numeral hM.basic hs⟩
  · rintro ⟨M, _, hc, hM, a, ha, -⟩
    exact ⟨M, inferInstance, hc, hM, a, ha⟩

/-! ## Con la verdad en ℕ en lugar de las instancias demostradas -/

/-- **Fórmulas acotadas**: todos los cuantificadores de la forma `∀ x ≤ t` o `∃ x ≤ t`, con `t` cualquier término; la
idea es la clase `Δ₀` del lenguaje `L`. Está pensada para contener a `Σᵇᵢ` y `Πᵇᵢ` (sus conectivos se arman con `imp` y
`falsum`), pero aquí solo se demuestra que contiene a las agudas (`EsAguda.acotada`). -/
inductive EsAcotada {α : Type} : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | falso {n : ℕ} : EsAcotada (BoundedFormula.falsum : L.BoundedFormula α n)
  | igual {n : ℕ} (t u : L.Term (α ⊕ Fin n)) : EsAcotada (BoundedFormula.equal t u)
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) : EsAcotada (BoundedFormula.rel R ts)
  | imp {n : ℕ} {φ ψ : L.BoundedFormula α n} : EsAcotada φ → EsAcotada ψ → EsAcotada (φ.imp ψ)
  | todo {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsAcotada φ → EsAcotada (paraTodoAcotado t φ)
  | existe {n : ℕ} (t : L.Term (α ⊕ Fin n)) {φ : L.BoundedFormula α (n + 1)} :
      EsAcotada φ → EsAcotada (existeAcotado t φ)

/-- Las agudas son acotadas. -/
theorem EsAguda.acotada {α : Type} {n : ℕ} {φ : L.BoundedFormula α n} (h : EsAguda φ) : EsAcotada φ := by
  induction h with
  | falso => exact .falso
  | igual t u => exact .igual t u
  | rel R ts => exact .rel R ts
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2
  | todoAgudo t _ ih => exact .todo _ ih
  | existeAgudo t _ ih => exact .existe _ ih

/-- **Completitud para sentencias acotadas (sin probar aquí, y sin verificar que valga).** Si `φ(x)` es acotada y `φ(n)`
vale en ℕ, S¹₂ demuestra `φ(n̄)`. Es la forma de la completitud `Δ₀` de la aritmética acotada; lo que pide es que BASIC
evalúe bien los términos cerrados sobre numerales (`+`, `·`, `|·|`, `⌊·/2⌋`, `#`) y que los cuantificadores acotados
recorran solo numerales, que es `segmento_inicial`. Lo primero no está en el repo, y no se comprobó que los axiomas
BASIC de este repo alcancen: si no alcanzaran, esta `Prop` sería falsa. -/
def CompletitudAcotada : Prop :=
  ∀ φ : L.Formula (Fin 1), EsAcotada φ → ∀ n : ℕ, φ.Realize ![n] → DerivaS12 (instancia φ n)

/-- **El largo infinito, con la verdad en ℕ**: para `φ` acotada y verdadera en ℕ en cada `n`, con la completitud para
sentencias acotadas como hipótesis. -/
theorem largo_infinito_s12_de_verdad (hc : CompletitudAcotada) {φ : L.Formula (Fin 1)} (hφ : EsAcotada φ)
    (hv : ∀ n : ℕ, φ.Realize ![n]) :
    ¬ DerivaS12 (cierre φ) ↔
      ∃ (M : Type) (_ : L.Structure M), Countable M ∧ EsModeloS12 M ∧
        ∃ a : M, ¬ φ.Realize ![a] ∧ ¬ EsEstandar a ∧ ∀ n : ℕ, le (valor M n) a ∧ valor M n ≠ a :=
  largo_infinito_s12 φ fun n => hc φ hφ n (hv n)

/-! ## 2. La instancia de circuitos, como parámetro -/

/-- **`φ` expresa `P` en ℕ**: lo único que se le pide a una fórmula propuesta. Qué significa `φ` en un modelo no
estándar depende de cómo se codifique y no lo fija esta definición. -/
def Expresa (φ : L.Formula (Fin 1)) (P : ℕ → Prop) : Prop := ∀ n : ℕ, φ.Realize ![n] ↔ P n

/-- **La cota inferior en el largo `n`**: SAT (`CookS12.satBits`) no tiene circuitos de `n^k` compuertas o menos en el
largo `n` (el tamaño mínimo, `Finitud.sucNat`, pasa de `n^k`). Es un enunciado sobre ℕ, no una fórmula de `L`.

**Pedida en todo largo es falsa**: falla en `n = 1` (`cota_falsa_en_uno`). Se conserva para dejar demostrado que la
versión «en todo largo» de la instancia de circuitos es vacía (`cotaInferiorSAT_vacia`); la que se usa es
`cotaInferiorSATDesde`. -/
def cotaInferiorSAT (k n : ℕ) : Prop := n ^ k < Tiempo.Finitud.sucNat CookS12.satBits n

/-- En el largo `1` toda función booleana se calcula con un circuito de una compuerta. -/
theorem uno_bit (f : (Fin 1 → Bool) → Bool) : ∃ C : Shannon.Circuito 1 1, Shannon.calcula C = f := by
  revert f; decide

/-- El tamaño mínimo de cualquier problema en el largo `1` es a lo sumo `1`. -/
theorem sucNat_uno (P : Problema) : Tiempo.Finitud.sucNat P 1 ≤ 1 := by
  obtain ⟨C, hC⟩ := uno_bit (rebanada P 1)
  have h : sucesion P 1 ≤ (1 : ℕ∞) :=
    iInf_le_of_le 1 (iInf_le_of_le C (iInf_le_of_le hC le_rfl))
  rw [Tiempo.Finitud.sucesion_eq] at h
  exact_mod_cast h

/-- **La cota en todo largo falla en `n = 1`**, para todo `k`. -/
theorem cota_falsa_en_uno (k : ℕ) : ¬ cotaInferiorSAT k 1 := by
  unfold cotaInferiorSAT
  have := sucNat_uno CookS12.satBits
  simp only [one_pow]; omega

/-- **`cotaInferiorSAT` deja hipótesis vacías**: ninguna `φ` la expresa en ℕ y a la vez tiene todas sus instancias
demostradas en S¹₂. Por eso la instancia de circuitos se plantea con `cotaInferiorSATDesde`. -/
theorem cotaInferiorSAT_vacia (k : ℕ) (φ : L.Formula (Fin 1)) (hexp : Expresa φ (cotaInferiorSAT k))
    (hinst : ∀ n, DerivaS12 (instancia φ n)) : False :=
  cota_falsa_en_uno k ((hexp 1).1 (verdad_de_instancias hinst 1))

/-- **La cota inferior desde el largo `n₀`**: para `n ≥ n₀`, SAT necesita más de `n^k` compuertas en el largo `n`; para
`n < n₀` no se pide nada. Con `k = 0` es trivial (dos compuertas); para `k` grande es una cota inferior de circuitos
para SAT que no se sabe demostrar. Con `n₀ ≤ 1` falla siempre en `n = 1`. -/
def cotaInferiorSATDesde (k n₀ n : ℕ) : Prop := n₀ ≤ n → cotaInferiorSAT k n

/-- Con `n₀ = 2` la versión «desde» ya no choca con el largo `1`: ahí vale sin condiciones. -/
theorem cotaInferiorSATDesde_uno (k : ℕ) : cotaInferiorSATDesde k 2 1 := by
  intro h; omega

/-- **Si S¹₂ demuestra cada caso de la cota inferior pero no la cota, hay un largo infinito donde falla.** Para
cualquier fórmula `φ` que exprese en ℕ «desde el largo `n₀`, SAT necesita más de `n^k` compuertas en el largo `n`»
(`cotaInferiorSATDesde k n₀`): si S¹₂ demuestra cada caso `φ(n̄)` pero no `∀n φ(n)`, la cota vale en ℕ en todo largo
`n ≥ n₀`, y hay un modelo numerable de S¹₂ con un largo `a` no estándar, mayor que todo numeral, donde `φ(a)` falla.
**No dice nada de circuitos en el modelo**: `Expresa` es extensional, y con las instancias demostradas solo pide que la
cota valga en ℕ (`expresa_solo_pide_verdad`); `φ` puede ser cualquier fórmula verdadera. La segunda conclusión es
`largo_infinito_s12` y la primera sale de `hexp`. Que `φ(a)` signifique «en el largo `a`, SAT tiene circuitos chicos»
pide una codificación intensional que no está. Con `n₀ ≤ 1` las hipótesis son contradictorias (`desde_chico_vacia`). -/
theorem cota_inferior_largo_infinito (k n₀ : ℕ) (φ : L.Formula (Fin 1))
    (hexp : Expresa φ (cotaInferiorSATDesde k n₀))
    (hinst : ∀ n, DerivaS12 (instancia φ n)) (hno : ¬ DerivaS12 (cierre φ)) :
    (∀ n : ℕ, n₀ ≤ n → cotaInferiorSAT k n) ∧
      ∃ (M : Type) (_ : L.Structure M), Countable M ∧ EsModeloS12 M ∧
        ∃ a : M, ¬ φ.Realize ![a] ∧ ¬ EsEstandar a ∧ ∀ n : ℕ, le (valor M n) a ∧ valor M n ≠ a :=
  ⟨fun n => (hexp n).1 (verdad_de_instancias hinst n), (largo_infinito_s12 φ hinst).1 hno⟩

/-- **`Expresa` solo pide verdad.** Si S¹₂ demuestra cada instancia de `φ`, entonces `φ` expresa la cota desde `n₀` si
y solo si la cota vale en ℕ desde `n₀`, sea cual sea `φ`. Por eso `cota_inferior_largo_infinito` no tiene contenido
de circuitos en el modelo. -/
theorem expresa_solo_pide_verdad (k n₀ : ℕ) (φ : L.Formula (Fin 1)) (hinst : ∀ n, DerivaS12 (instancia φ n)) :
    Expresa φ (cotaInferiorSATDesde k n₀) ↔ ∀ n, cotaInferiorSATDesde k n₀ n :=
  ⟨fun h n => (h n).1 (verdad_de_instancias hinst n),
   fun h n => ⟨fun _ => h n, fun _ => verdad_de_instancias hinst n⟩⟩

/-- **Desde un largo chico, vacía**: con `n₀ ≤ 1` las hipótesis de `cota_inferior_largo_infinito` se contradicen. -/
theorem desde_chico_vacia (k n₀ : ℕ) (h₀ : n₀ ≤ 1) (φ : L.Formula (Fin 1))
    (hexp : Expresa φ (cotaInferiorSATDesde k n₀)) (hinst : ∀ n, DerivaS12 (instancia φ n)) : False :=
  cota_falsa_en_uno k ((hexp 1).1 (verdad_de_instancias hinst 1) h₀)

/-! ## 3. El contraste: el ultrapoder de ℕ no miente -/

/-- **El ultrapoder de ℕ** por un ultrafiltro `U`: el modelo de `Infinito.lean`, como estructura de `L`. -/
abbrev Ultrapoder (U : Ultrafilter ℕ) : Type := (U : Filter ℕ).Product fun _ : ℕ => ℕ

/-- **El ultrapoder es un modelo de S¹₂** (Łoś: satisface lo mismo que ℕ). -/
theorem ultrapoder_esModeloS12 (U : Ultrafilter ℕ) : EsModeloS12 (Ultrapoder U) := by
  refine (modelo_S12_iff _).1 ((Theory.model_iff _).2 fun σ hσ => ?_)
  rw [Ultraproduct.sentence_realize]
  have : ℕ ⊨ S12 := (modelo_S12_iff ℕ).2 nat_esModeloS12
  exact Eventually.of_forall fun _ => Theory.realize_sentence_of_mem S12 hσ

/-- **El ultrapoder es honesto**: si `φ(n)` vale en ℕ para todo `n`, vale en **todo** elemento del ultrapoder, estándar
o no. Ningún largo infinito del ultrapoder es un contraejemplo. -/
theorem ultrapoder_honesto (U : Ultrafilter ℕ) {φ : L.Formula (Fin 1)} (hv : ∀ n : ℕ, φ.Realize ![n])
    (a : Ultrapoder U) : φ.Realize ![a] := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep a
  have e : (![Quotient.mk _ f] : Fin 1 → Ultrapoder U) =
      fun i => ((![f] : Fin 1 → ℕ → ℕ) i : Ultrapoder U) := by
    funext i; fin_cases i; rfl
  rw [e]
  refine (Ultraproduct.realize_formula_cast (M := fun _ : ℕ => ℕ) (u := U) φ ![f]).2
    (Eventually.of_forall fun m => ?_)
  have e2 : (fun i => (![f] : Fin 1 → ℕ → ℕ) i m) = ![f m] := by funext i; fin_cases i; rfl
  rw [e2]; exact hv (f m)

/-- El valor de `n̄` en el ultrapoder es la clase de la sucesión constante `n`. -/
theorem valor_ultrapoder (U : Ultrafilter ℕ) (n : ℕ) :
    valor (Ultrapoder U) n = ((fun _ : ℕ => n : ℕ → ℕ) : Ultrapoder U) := by
  have e : (Empty.elim : Empty → Ultrapoder U) = fun i => ((Empty.elim i : ℕ → ℕ) : Ultrapoder U) := by
    funext i; exact i.elim
  rw [valor, e]
  refine (Ultraproduct.term_realize_cast (M := fun _ : ℕ => ℕ) (u := U) _ (numeral n)).trans ?_
  congr 1; funext m
  have e2 : (fun i : Empty => (Empty.elim i : ℕ → ℕ) m) = (Empty.elim : Empty → ℕ) := by funext i; exact i.elim
  rw [e2]; exact valor_nat n

/-- **Un largo infinito del ultrapoder es no estándar**: la clase de la identidad no es ningún numeral, si `U` es no
principal. -/
theorem ultrapoder_no_estandar {U : Ultrafilter ℕ} (hU : Tiempo.Infinito.LargoInfinito U) :
    ¬ EsEstandar (((fun m : ℕ => m) : ℕ → ℕ) : Ultrapoder U) := by
  rintro ⟨n, hn⟩
  have hn : (((fun m : ℕ => m) : ℕ → ℕ) : Ultrapoder U) = valor (Ultrapoder U) n := hn
  rw [valor_ultrapoder] at hn
  have h1 : ∀ᶠ m in (U : Filter ℕ), m = n := Quotient.exact hn
  have h2 : ∀ᶠ m in (U : Filter ℕ), m ≠ n := hU (eventually_cofinite_ne n)
  obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
  exact hm2 hm1

/-- **El contraste.** Si S¹₂ demuestra cada `φ(n̄)` pero no `∀x φ(x)`:

* hay un modelo numerable de S¹₂ con un largo no estándar `a` donde `φ(a)` falla, y ese modelo no satisface
  `∀x φ(x)`, que sí vale en ℕ: no es elementalmente equivalente a ℕ;
* en cambio, todo ultrapoder de ℕ es un modelo de S¹₂ que satisface `∀x φ(x)`: ninguno de sus largos infinitos, que
  los tiene si el ultrafiltro es no principal, es un contraejemplo.

El largo infinito que miente vive en los modelos de la teoría, no en el ultrapoder. -/
theorem contraste (φ : L.Formula (Fin 1)) (hinst : ∀ n, DerivaS12 (instancia φ n)) (hno : ¬ DerivaS12 (cierre φ)) :
    ℕ ⊨ cierre φ ∧
    (∃ (M : Type) (_ : L.Structure M), Countable M ∧ EsModeloS12 M ∧ ¬ M ⊨ cierre φ ∧
        ∃ a : M, ¬ φ.Realize ![a] ∧ ¬ EsEstandar a) ∧
      ∀ U : Ultrafilter ℕ, EsModeloS12 (Ultrapoder U) ∧ Ultrapoder U ⊨ cierre φ ∧
        (Tiempo.Infinito.LargoInfinito U → ∃ a : Ultrapoder U, ¬ EsEstandar a) := by
  have hv := verdad_de_instancias hinst
  refine ⟨(realize_cierre φ).2 (forall_fin1.2 hv), ?_, fun U => ⟨ultrapoder_esModeloS12 U,
    (realize_cierre φ).2 (forall_fin1.2 (ultrapoder_honesto U hv)), fun hU => ⟨_, ultrapoder_no_estandar hU⟩⟩⟩
  obtain ⟨M, _, hc, hM, a, ha, hs, -⟩ := (largo_infinito_s12 φ hinst).1 hno
  refine ⟨M, inferInstance, hc, hM, fun h => ha ?_, a, ha, hs⟩
  exact forall_fin1.1 ((realize_cierre φ).1 h) a

/-! ## Controles -/

/-- En ℕ, el numeral `5̄` vale `5`. -/
example : valor ℕ 5 = 5 := valor_nat 5

/-- En ℕ no hay contraejemplos no estándar: todo es un numeral. -/
example (a : ℕ) : EsEstandar a := nat_estandar a

/-- La fórmula `x = x`: S¹₂ la demuestra, así que no hay contraejemplo en ningún modelo. -/
example : ¬ ∃ (M : Type) (_ : L.Structure M), Countable M ∧ EsModeloS12 M ∧
    ∃ a : M, ¬ (Term.equal (Term.var 0) (Term.var 0) : L.Formula (Fin 1)).Realize ![a] := by
  rintro ⟨M, _, -, -, a, ha⟩
  exact ha (by simp [Formula.Realize, Term.equal])

end LargoS12
end Acotada
end Sagitta.Map
