import Sagitta.Map.Bootstrap
import Mathlib.Computability.Halting

/-!
# La diagonal de Gödel: el gemelo lógico del bootstrap que certifica

## La pregunta

`Bootstrap.lean` probó que no hay un certificador computable de resolvedores de SAT: ni por Rice
(`no_hay_certificador`) ni por la diagonal escrita a mano (`no_hay_certificador_diagonal`), donde el teorema de
recursión (`fixed_point₂`) da un programa que se consulta a sí mismo y hace lo contrario. José ve ahí un bootstrap: una
teoría que quiere certificar sus propias pruebas. El gemelo lógico de esa diagonal es el **segundo teorema de Gödel**:
una teoría no certifica su propia consistencia. Este archivo lo formaliza en la versión abstracta, sin aritmética.

## Qué se prueba, y con qué hipótesis

**El modelo** (`SistemaHBL S C`): un tipo `S` de enunciados con una implicación `imp` y un absurdo `bot` (la negación
es `neg a := imp a bot`), un predicado de demostrabilidad `Pr : S → Prop` cerrado por *modus ponens* y que contiene los
axiomas `K` y `S` de Hilbert (lógica implicacional mínima: **no** se supone *ex falso* ni tercero excluido), un tipo
`C` de códigos con una codificación `cod : S → C` y un predicado interno de demostrabilidad `Dem : C → S`. La «caja»
es `caja a := Dem (cod a)`, el enunciado «`a` es demostrable». Las hipótesis van **aparte**, como `Prop`, para poder
sacarlas una por una:

* `D1` (necesitación): `Pr a → Pr (caja a)`;
* `D2` (distribución): `Pr (caja (a → b) → caja a → caja b)`;
* `D3` (introspección): `Pr (caja a → caja (caja a))`;
* `PuntoFijo G`: el **lema diagonal como hipótesis**, `Pr (G → ¬ caja G)` y `Pr (¬ caja G → G)`;
* `Consistente`: `¬ Pr bot`; `Con := ¬ caja bot`, el enunciado «soy consistente».

**Los teoremas.**

* `primer_teorema`: con `D1`, el punto fijo y la consistencia, `G` no es demostrable (solo usa `D1` y *modus ponens*).
* `lob`: con `D1`–`D3` y un punto fijo `ψ ↔ (caja ψ → φ)`, si `Pr (caja φ → φ)` entonces `Pr φ`.
* `con_implica_g`: con `D1`–`D3` y el punto fijo, el sistema demuestra `Con → G` (el primer teorema, internalizado).
* `segundo_teorema`: con `D1`–`D3` y el punto fijo, si el sistema demuestra `Con`, demuestra `bot`. Es `lob` con
  `φ = bot`. `segundo_teorema_iff`: con las mismas hipótesis, `Pr Con ↔ Pr bot`.
* `no_hay_certificador_de_pruebas` y `demostrabilidad_indecidible` (meta 2): si una «teoría» con enunciados
  `Primcodable` representa la parada (hay `H : Code → S` computable con `Pr (H c) ↔ eval c 0` termina: completitud
  Σ₁ **y** corrección Σ₁), su conjunto de teoremas no es decidible: se reduce a `ComputablePred.halting_problem`.
* `diagonal_comun` (meta 3): si `Q e ↔ ¬ cert e`, ningún `cert` coincide con `Q` en todas partes. De ahí salen, con la
  misma línea, el bootstrap de programas (`no_hay_certificador_comun`, con `fixed_point₂`) y Gödel I semántico
  (`godel_semantico_comun`: un sistema correcto cuyo `caja` expresa `Pr` no demuestra todas las verdades).
  `misma_diagonal` pone lado a lado `no_hay_certificador_diagonal` y `segundo_teorema`.

## La lectura en el proyecto

El bootstrap que **certifica** es contradictorio, y es la misma diagonal en dos idiomas:

| idioma | qué se supone | el punto fijo | la negación | teorema |
|---|---|---|---|---|
| programas | un certificador computable `d` de «`c` resuelve SAT» | `fixed_point₂` (teorema de recursión, probado) | «si `d` dice que resuelvo, no termino» | `no_hay_certificador_diagonal` |
| teorías | una teoría que demuestra `Con` | `G ↔ ¬ caja G` (lema diagonal, **hipótesis**) | `¬ caja` | `segundo_teorema` |

En los dos casos el esquema es el de Lawvere: algo que habla de sí mismo (el punto fijo) más una negación sin punto
fijo dan contradicción (`diagonal_comun`). La asimetría honesta: en programas el punto fijo es un teorema de Mathlib;
en teorías queda como hipótesis.

## Controles y mutantes

* **La consistencia no es vacía**: un sistema inconsistente demuestra `Con` (`inconsistente_demuestra_con`, en
  cualquier sistema por el axioma `K`), y hay uno que cumple todas las demás hipótesis (`modeloUnit`).
* **Las hipótesis no son vacías ni contradictorias**: `modeloGL` (marcos de Kripke sobre `ℕ` con `m < n`, la
  semántica de la lógica de la demostrabilidad) es consistente y cumple `D1`–`D3` y el punto fijo.
* **El punto fijo es lo que importa**: `modeloBool` es completo, decidible, consistente, cumple `D1`–`D3` y demuestra
  su propia consistencia; no tiene punto fijo (`modeloBool_sin_punto_fijo`).
* **Mutantes refutados** (se exhibe un modelo donde la conclusión falla): sin punto fijo (`modeloBool`), sin `D1`
  (`modeloSinD1`, para el primero y el segundo), sin `D2` (`modeloSinD2`), sin `D3` (`modeloCadena`, la cadena
  `n → n+1`, donde `G` es «`n` es par»), sin consistencia en el primero (`modeloUnit`), «el sistema demuestra `G`»
  (`modeloGL`), y en la meta 2 sin corrección o sin completitud Σ₁.

## Lo que NO se prueba

* **El lema diagonal para una aritmética concreta.** El punto fijo `G` queda como hipótesis; tampoco se prueban
  `D1`–`D3` para una teoría concreta (son las condiciones de Hilbert–Bernays–Löb, que en aritmética cuestan la
  formalización de la sintaxis y de la Σ₁-completitud formalizada).
* **En la meta 2 la representación de la parada es una hipótesis.** Para una teoría real saldría de la
  Σ₁-completitud (por ejemplo de `Q`) y de la corrección en `ℕ`; la versión fuerte (indecidibilidad esencial: basta
  la consistencia, sin corrección) vuelve a usar el lema diagonal y no se hace.
* **Gödel para S¹₂ — DE MEMORIA, NO PROBADO AQUÍ.** El segundo teorema vale para `S¹₂` (y para teorías más débiles,
  como `Q` ampliada por lo necesario para las condiciones de derivabilidad): `S¹₂` no demuestra su propia
  consistencia. Además, Wilkie y Paris (1987, «On the scheme of induction for bounded arithmetic formulas»,
  *Annals of Pure and Applied Logic*) muestran que `IΔ₀ + Ω₁` no demuestra siquiera la consistencia de `Q`. Ninguna de
  las dos cosas se formaliza aquí; la línea de completitud del proyecto (`Completitud/Teorema.lean`,
  `demuestra_iff_deriva`) no se usa ni se conecta con este modelo.
* **Nada sobre P contra NP.** Como en `Bootstrap.lean`, esto es computabilidad y lógica, no complejidad.
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map.Tiempo.DiagonalGodel

/-! ## 1. El modelo abstracto -/

/-- **Un sistema de pruebas abstracto** con codificación: enunciados `S`, códigos `C`, implicación, absurdo,
demostrabilidad cerrada por *modus ponens* y con los axiomas `K` y `S`, y un predicado interno `Dem` sobre códigos. -/
structure SistemaHBL (S C : Type) where
  imp : S → S → S
  bot : S
  Pr : S → Prop
  cod : S → C
  Dem : C → S
  mp : ∀ {a b : S}, Pr (imp a b) → Pr a → Pr b
  ax_k : ∀ a b : S, Pr (imp a (imp b a))
  ax_s : ∀ a b c : S, Pr (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))

namespace SistemaHBL

variable {S C : Type} (T : SistemaHBL S C)

/-- «`a` es demostrable», como enunciado: `Dem(⌜a⌝)`. -/
def caja (a : S) : S := T.Dem (T.cod a)

/-- La negación: `a → ⊥`. -/
def neg (a : S) : S := T.imp a T.bot

/-- El sistema no demuestra el absurdo. -/
def Consistente : Prop := ¬ T.Pr T.bot

/-- «Soy consistente»: `¬ Dem(⌜⊥⌝)`. -/
def Con : S := T.neg (T.caja T.bot)

/-- Condición de derivabilidad 1 (necesitación). -/
def D1 : Prop := ∀ a, T.Pr a → T.Pr (T.caja a)

/-- Condición de derivabilidad 2 (distribución). -/
def D2 : Prop := ∀ a b, T.Pr (T.imp (T.caja (T.imp a b)) (T.imp (T.caja a) (T.caja b)))

/-- Condición de derivabilidad 3 (introspección). -/
def D3 : Prop := ∀ a, T.Pr (T.imp (T.caja a) (T.caja (T.caja a)))

/-- **El lema diagonal, como hipótesis**: el sistema demuestra `ψ ↔ (caja ψ → φ)`. -/
def PuntoFijoLob (φ ψ : S) : Prop :=
  T.Pr (T.imp ψ (T.imp (T.caja ψ) φ)) ∧ T.Pr (T.imp (T.imp (T.caja ψ) φ) ψ)

/-- **El enunciado de Gödel**: el sistema demuestra `G ↔ ¬ caja G`. Es `PuntoFijoLob bot G`. -/
def PuntoFijo (G : S) : Prop := T.PuntoFijoLob T.bot G

variable {T}

/-! ## 2. Lógica implicacional mínima dentro del sistema -/

/-- Debilitar: si `⊢ a`, entonces `⊢ x → a` (axioma `K`). -/
theorem debilitar {x a : S} (h : T.Pr a) : T.Pr (T.imp x a) := T.mp (T.ax_k a x) h

/-- Aplicar bajo una hipótesis (axioma `S`). -/
theorem aplicar {x y z : S} (h1 : T.Pr (T.imp x (T.imp y z))) (h2 : T.Pr (T.imp x y)) : T.Pr (T.imp x z) :=
  T.mp (T.mp (T.ax_s x y z) h1) h2

/-- Silogismo. -/
theorem trans {a b c : S} (h1 : T.Pr (T.imp a b)) (h2 : T.Pr (T.imp b c)) : T.Pr (T.imp a c) :=
  aplicar (debilitar h2) h1

/-- Contraposición, sin tercero excluido: `⊢ a → b` da `⊢ ¬b → ¬a`. -/
theorem contraponer {a b : S} (h : T.Pr (T.imp a b)) : T.Pr (T.imp (T.neg b) (T.neg a)) := by
  have h1 : T.Pr (T.imp (T.neg b) (T.imp a (T.neg b))) := T.ax_k _ _
  have h2 : T.Pr (T.imp (T.neg b) (T.imp (T.imp a (T.neg b)) (T.imp (T.imp a b) (T.imp a T.bot)))) :=
    debilitar (T.ax_s a b T.bot)
  exact aplicar (aplicar h2 h1) (debilitar h)

/-! ## 3. Los dos teoremas de Gödel y el de Löb, en abstracto -/

/-- **Primer teorema (abstracto).** Si el sistema es consistente, el enunciado de Gödel no es demostrable. Solo usa
`D1`, *modus ponens* y la mitad `G → ¬ caja G` del punto fijo. -/
theorem primer_teorema (h1 : T.D1) {G : S} (hG : T.PuntoFijo G) (hc : T.Consistente) : ¬ T.Pr G :=
  fun hg => hc (T.mp (T.mp hG.1 hg) (h1 _ hg))

/-- **El paso interno**: de `⊢ ψ → (caja ψ → φ)` sale `⊢ caja ψ → caja φ` (usa `D1`, `D2` y `D3`). -/
theorem caja_de_auto (h1 : T.D1) (h2 : T.D2) (h3 : T.D3) {ψ φ : S}
    (h : T.Pr (T.imp ψ (T.imp (T.caja ψ) φ))) : T.Pr (T.imp (T.caja ψ) (T.caja φ)) := by
  have a1 : T.Pr (T.imp (T.caja ψ) (T.caja (T.imp (T.caja ψ) φ))) := T.mp (h2 _ _) (h1 _ h)
  have a2 : T.Pr (T.imp (T.caja ψ) (T.imp (T.caja (T.caja ψ)) (T.caja φ))) := trans a1 (h2 _ _)
  exact aplicar a2 (h3 ψ)

/-- **Teorema de Löb (abstracto).** Con `D1`–`D3` y un punto fijo `ψ ↔ (caja ψ → φ)`: si el sistema demuestra
`caja φ → φ`, demuestra `φ`. -/
theorem lob (h1 : T.D1) (h2 : T.D2) (h3 : T.D3) {φ ψ : S} (hψ : T.PuntoFijoLob φ ψ)
    (h : T.Pr (T.imp (T.caja φ) φ)) : T.Pr φ := by
  have b1 : T.Pr (T.imp (T.caja ψ) φ) := trans (caja_de_auto h1 h2 h3 hψ.1) h
  exact T.mp b1 (h1 _ (T.mp hψ.2 b1))

/-- **El primer teorema, internalizado**: el sistema demuestra `Con → G`. -/
theorem con_implica_g (h1 : T.D1) (h2 : T.D2) (h3 : T.D3) {G : S} (hG : T.PuntoFijo G) :
    T.Pr (T.imp T.Con G) :=
  trans (contraponer (caja_de_auto h1 h2 h3 hG.1)) hG.2

/-- **Segundo teorema (abstracto).** Con `D1`–`D3` y el punto fijo de Gödel: si el sistema demuestra su propia
consistencia, es inconsistente. Es `lob` con `φ = bot`. -/
theorem segundo_teorema (h1 : T.D1) (h2 : T.D2) (h3 : T.D3) {G : S} (hG : T.PuntoFijo G)
    (hcon : T.Pr T.Con) : T.Pr T.bot :=
  lob h1 h2 h3 hG hcon

/-- **Segundo teorema, otra lectura**: un sistema consistente no demuestra su consistencia. -/
theorem segundo_teorema' (h1 : T.D1) (h2 : T.D2) (h3 : T.D3) {G : S} (hG : T.PuntoFijo G)
    (hc : T.Consistente) : ¬ T.Pr T.Con :=
  fun hcon => hc (segundo_teorema h1 h2 h3 hG hcon)

/-- **Segundo teorema por el otro camino**: `Con → G` y el primer teorema. -/
theorem segundo_por_el_primero (h1 : T.D1) (h2 : T.D2) (h3 : T.D3) {G : S} (hG : T.PuntoFijo G)
    (hc : T.Consistente) : ¬ T.Pr T.Con :=
  fun hcon => primer_teorema h1 hG hc (T.mp (con_implica_g h1 h2 h3 hG) hcon)

/-- **Control: un sistema inconsistente demuestra su consistencia** (en cualquier sistema, por `K`). La hipótesis de
consistencia del segundo teorema no es vacía. -/
theorem inconsistente_demuestra_con (h : T.Pr T.bot) : T.Pr T.Con := debilitar h

/-- Con las hipótesis de Gödel, demostrar `Con` es exactamente ser inconsistente. -/
theorem segundo_teorema_iff (h1 : T.D1) (h2 : T.D2) (h3 : T.D3) {G : S} (hG : T.PuntoFijo G) :
    T.Pr T.Con ↔ T.Pr T.bot :=
  ⟨segundo_teorema h1 h2 h3 hG, inconsistente_demuestra_con⟩

end SistemaHBL

open SistemaHBL

/-! ## 4. Modelos: controles y mutantes de la meta 1 -/

/-- **`modeloBool`**: los enunciados son los booleanos, demostrable es verdadero, y `caja` es la identidad. -/
def modeloBool : SistemaHBL Bool Bool where
  imp a b := !a || b
  bot := false
  Pr a := a = true
  cod := id
  Dem := id
  mp := by intro a b h1 h2; subst h2; simpa using h1
  ax_k := by intro a b; cases a <;> cases b <;> rfl
  ax_s := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

theorem modeloBool_D1 : modeloBool.D1 := fun _ h => h
theorem modeloBool_D2 : modeloBool.D2 := by intro a b; cases a <;> cases b <;> rfl
theorem modeloBool_D3 : modeloBool.D3 := by intro a; cases a <;> rfl
theorem modeloBool_consistente : modeloBool.Consistente := Bool.false_ne_true
theorem modeloBool_demuestra_con : modeloBool.Pr modeloBool.Con := rfl

/-- **`modeloBool` es completo**: demuestra cada enunciado o su negación. -/
theorem modeloBool_completo (a : Bool) : modeloBool.Pr a ∨ modeloBool.Pr (modeloBool.neg a) := by
  cases a
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **`modeloBool` es decidible**: su demostrabilidad es un predicado computable. -/
theorem modeloBool_decidible : ComputablePred modeloBool.Pr :=
  ComputablePred.computable_iff.2 ⟨fun a => a, Computable.id, rfl⟩

/-- **`modeloBool` no tiene punto fijo de Gödel.** -/
theorem modeloBool_sin_punto_fijo (G : Bool) : ¬ modeloBool.PuntoFijo G := by
  rintro ⟨h1, h2⟩
  cases G
  · exact Bool.false_ne_true h2
  · exact Bool.false_ne_true h1

/-- **Control: sin punto fijo no hay contradicción.** Un sistema completo, decidible y consistente que cumple
`D1`–`D3` demuestra su propia consistencia. -/
theorem control_completo_decidible_sin_punto_fijo :
    modeloBool.Consistente ∧ modeloBool.D1 ∧ modeloBool.D2 ∧ modeloBool.D3 ∧
      (∀ a, modeloBool.Pr a ∨ modeloBool.Pr (modeloBool.neg a)) ∧ ComputablePred modeloBool.Pr ∧
      modeloBool.Pr modeloBool.Con ∧ ∀ G, ¬ modeloBool.PuntoFijo G :=
  ⟨modeloBool_consistente, modeloBool_D1, modeloBool_D2, modeloBool_D3, modeloBool_completo,
    modeloBool_decidible, modeloBool_demuestra_con, modeloBool_sin_punto_fijo⟩

/-- **Mutante refutado: el segundo teorema sin punto fijo** es falso. -/
theorem mutante_segundo_sin_punto_fijo :
    ¬ ∀ (S C : Type) (T : SistemaHBL S C), T.D1 → T.D2 → T.D3 → T.Pr T.Con → T.Pr T.bot :=
  fun h => modeloBool_consistente
    (h _ _ modeloBool modeloBool_D1 modeloBool_D2 modeloBool_D3 modeloBool_demuestra_con)

/-- **`modeloUnit`**: un solo enunciado, demostrable. Es inconsistente y cumple todo lo demás. -/
def modeloUnit : SistemaHBL Unit Unit where
  imp _ _ := ()
  bot := ()
  Pr _ := True
  cod _ := ()
  Dem _ := ()
  mp _ _ := trivial
  ax_k _ _ := trivial
  ax_s _ _ _ := trivial

/-- **Control y mutante: sin consistencia, el primer teorema falla.** `modeloUnit` cumple `D1`–`D3` y el punto fijo,
demuestra `G` y demuestra `Con`. -/
theorem modeloUnit_todo :
    modeloUnit.D1 ∧ modeloUnit.D2 ∧ modeloUnit.D3 ∧ modeloUnit.PuntoFijo () ∧ modeloUnit.Pr () ∧
      modeloUnit.Pr modeloUnit.Con ∧ ¬ modeloUnit.Consistente :=
  ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ => trivial, ⟨trivial, trivial⟩, trivial, trivial,
    fun h => h trivial⟩

/-- **Mutante refutado: el primer teorema sin consistencia.** -/
theorem mutante_primero_sin_consistencia :
    ¬ ∀ (S C : Type) (T : SistemaHBL S C) (G : S), T.D1 → T.PuntoFijo G → ¬ T.Pr G :=
  fun h => h _ _ modeloUnit () modeloUnit_todo.1 modeloUnit_todo.2.2.2.1 trivial

/-- **`modeloCadena`**: marcos de Kripke sobre la cadena `n → n+1` (no transitiva). Un enunciado es una propiedad de
los mundos, demostrable es valer en todos, y `caja a` vale en `n` si `a` vale en `n+1`. -/
def modeloCadena : SistemaHBL (ℕ → Prop) (ℕ → Prop) where
  imp a b := fun n => a n → b n
  bot := fun _ => False
  Pr a := ∀ n, a n
  cod := id
  Dem a := fun n => a (n + 1)
  mp h1 h2 n := h1 n (h2 n)
  ax_k _ _ _ ha _ := ha
  ax_s _ _ _ _ f g x := f x (g x)

/-- En la cadena, el enunciado de Gödel es «el mundo es par». -/
theorem modeloCadena_punto_fijo : modeloCadena.PuntoFijo (fun n => Even n) := by
  refine ⟨fun n he he1 => (Nat.even_add_one.1 he1) he, fun n h => ?_⟩
  by_contra hn
  exact h (Nat.even_add_one.2 hn)

theorem modeloCadena_no_D3 : ¬ modeloCadena.D3 := by
  intro h
  have h' : 0 + 1 + 1 = 1 := h (fun n => n = 1) 0 rfl
  omega

/-- **Mutante refutado: el segundo teorema sin `D3`.** La cadena cumple `D1`, `D2` y el punto fijo, es consistente
y demuestra su consistencia. -/
theorem mutante_segundo_sin_D3 :
    modeloCadena.D1 ∧ modeloCadena.D2 ∧ ¬ modeloCadena.D3 ∧ modeloCadena.PuntoFijo (fun n => Even n) ∧
      modeloCadena.Consistente ∧ modeloCadena.Pr modeloCadena.Con :=
  ⟨fun _ h n => h (n + 1), fun _ _ _ f g => f g, modeloCadena_no_D3, modeloCadena_punto_fijo,
    fun h => h 0, fun _ h => h⟩

/-- **`modeloSinD1`**: booleanos con `caja` constante falsa. -/
def modeloSinD1 : SistemaHBL Bool Bool where
  imp a b := !a || b
  bot := false
  Pr a := a = true
  cod := id
  Dem _ := false
  mp := by intro a b h1 h2; subst h2; simpa using h1
  ax_k := by intro a b; cases a <;> cases b <;> rfl
  ax_s := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-- **Mutante refutado: el primero y el segundo sin `D1`.** `modeloSinD1` cumple `D2`, `D3` y el punto fijo con
`G = true`, es consistente, demuestra `G` y demuestra `Con`; `D1` falla. -/
theorem mutante_sin_D1 :
    ¬ modeloSinD1.D1 ∧ modeloSinD1.D2 ∧ modeloSinD1.D3 ∧ modeloSinD1.PuntoFijo true ∧
      modeloSinD1.Consistente ∧ modeloSinD1.Pr true ∧ modeloSinD1.Pr modeloSinD1.Con :=
  ⟨fun h => Bool.false_ne_true (h true rfl), fun _ _ => rfl, fun _ => rfl, ⟨rfl, rfl⟩,
    Bool.false_ne_true, rfl, rfl⟩

/-- **`modeloSinD2`**: pares (valor de verdad, marca); `caja a` es verdadera si `a` lo es o si está marcada. El
enunciado de Gödel es el falso marcado. -/
def modeloSinD2 : SistemaHBL (Bool × Bool) (Bool × Bool) where
  imp a b := (!a.1 || b.1, false)
  bot := (false, false)
  Pr a := a.1 = true
  cod := id
  Dem a := (a.1 || a.2, false)
  mp := by
    rintro ⟨a, _⟩ ⟨b, _⟩ h1 h2
    simp only at h1 h2 ⊢
    subst h2; simpa using h1
  ax_k := by rintro ⟨a, _⟩ ⟨b, _⟩; cases a <;> cases b <;> rfl
  ax_s := by rintro ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩; cases a <;> cases b <;> cases c <;> rfl

/-- **Mutante refutado: el segundo teorema sin `D2`.** -/
theorem mutante_segundo_sin_D2 :
    modeloSinD2.D1 ∧ ¬ modeloSinD2.D2 ∧ modeloSinD2.D3 ∧ modeloSinD2.PuntoFijo (false, true) ∧
      modeloSinD2.Consistente ∧ modeloSinD2.Pr modeloSinD2.Con := by
  refine ⟨?_, ?_, ?_, ⟨rfl, rfl⟩, Bool.false_ne_true, rfl⟩
  · rintro ⟨a, b⟩ h
    change a = true at h
    subst h; rfl
  · intro h
    exact Bool.false_ne_true (h (false, true) (false, false))
  · rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- **`modeloGL`**: marcos de Kripke sobre `ℕ` con `m < n` (transitivo y conversamente bien fundado: la semántica de
la lógica de la demostrabilidad). `caja a` vale en `n` si `a` vale en todo `m < n`. -/
def modeloGL : SistemaHBL (ℕ → Prop) (ℕ → Prop) where
  imp a b := fun n => a n → b n
  bot := fun _ => False
  Pr a := ∀ n, a n
  cod := id
  Dem a := fun n => ∀ m < n, a m
  mp h1 h2 n := h1 n (h2 n)
  ax_k _ _ _ ha _ := ha
  ax_s _ _ _ _ f g x := f x (g x)

/-- En `modeloGL` el enunciado de Gödel es «`n ≠ 0`». -/
theorem modeloGL_punto_fijo : modeloGL.PuntoFijo (fun n => n ≠ 0) := by
  refine ⟨fun n hn h => h 0 (Nat.pos_of_ne_zero hn) rfl, fun n h hn => ?_⟩
  subst hn
  exact h fun m hm => absurd hm (Nat.not_lt_zero m)

/-- **Control: las hipótesis de Gödel no son vacías.** `modeloGL` es consistente y cumple `D1`–`D3` y el punto fijo;
como manda el teorema, no demuestra `G`, ni `¬G`, ni `Con`. -/
theorem modeloGL_todo :
    modeloGL.Consistente ∧ modeloGL.D1 ∧ modeloGL.D2 ∧ modeloGL.D3 ∧ modeloGL.PuntoFijo (fun n => n ≠ 0) ∧
      ¬ modeloGL.Pr (fun n => n ≠ 0) ∧ ¬ modeloGL.Pr (modeloGL.neg fun n => n ≠ 0) ∧
      ¬ modeloGL.Pr modeloGL.Con := by
  refine ⟨fun h => h 0, fun _ h n _ _ => h _, fun _ _ _ f g m hm => f m hm (g m hm),
    fun _ _ h m hm k hk => h k (lt_trans hk hm), modeloGL_punto_fijo, fun h => h 0 rfl,
    fun h => h 1 one_ne_zero, fun h => h 0 fun m hm => absurd hm (Nat.not_lt_zero m)⟩

/-- **Mutante refutado: «el sistema demuestra `G`»**, con todas las hipótesis y la consistencia. -/
theorem mutante_demuestra_G :
    ¬ ∀ (S C : Type) (T : SistemaHBL S C) (G : S), T.Consistente → T.D1 → T.D2 → T.D3 → T.PuntoFijo G →
      T.Pr G :=
  fun h => modeloGL_todo.2.2.2.2.2.1
    (h _ _ modeloGL _ modeloGL_todo.1 modeloGL_todo.2.1 modeloGL_todo.2.2.1 modeloGL_todo.2.2.2.1
      modeloGL_punto_fijo)

/-! ## 5. La versión computable: la demostrabilidad no es decidible -/

/-- **La demostrabilidad es indecidible.** Si una teoría con enunciados `Primcodable` representa la parada —hay
`H : Code → S` computable («el programa `c` termina en `0`») con completitud Σ₁ (si termina, se demuestra) y
corrección Σ₁ (si se demuestra, termina)—, su conjunto de teoremas no es un predicado computable. Se reduce a
`ComputablePred.halting_problem`. -/
theorem demostrabilidad_indecidible {S : Type} [Primcodable S] (Pr : S → Prop) (H : Code → S)
    (hH : Computable H) (hcompleta : ∀ c, (eval c 0).Dom → Pr (H c))
    (hcorrecta : ∀ c, Pr (H c) → (eval c 0).Dom) : ¬ ComputablePred Pr := by
  intro hP
  apply ComputablePred.halting_problem 0
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.1 hP
  refine ComputablePred.computable_iff.2 ⟨fun c => f (H c), hf.comp hH, ?_⟩
  funext c
  apply propext
  constructor
  · intro h
    have := hcompleta c h
    rw [hfe] at this
    exact this
  · intro h
    apply hcorrecta
    rw [hfe]
    exact h

/-- **No hay certificador de pruebas**: ningún `d : S → Bool` computable dice, de cada enunciado, si es demostrable.
Es el gemelo de `no_hay_certificador_diagonal` del lado de las teorías. -/
theorem no_hay_certificador_de_pruebas {S : Type} [Primcodable S] (Pr : S → Prop) (H : Code → S)
    (hH : Computable H) (hcompleta : ∀ c, (eval c 0).Dom → Pr (H c))
    (hcorrecta : ∀ c, Pr (H c) → (eval c 0).Dom) :
    ¬ ∃ d : S → Bool, Computable d ∧ ∀ s, d s = true ↔ Pr s := by
  rintro ⟨d, hd, hds⟩
  exact demostrabilidad_indecidible Pr H hH hcompleta hcorrecta
    (ComputablePred.computable_iff.2 ⟨d, hd, funext fun s => propext (hds s).symm⟩)

/-- **Lo mismo para un `SistemaHBL`** con enunciados codificables: la meta 2 sobre el modelo de la meta 1. -/
theorem sistema_no_decidible {S C : Type} [Primcodable S] (T : SistemaHBL S C) (H : Code → S)
    (hH : Computable H) (hcompleta : ∀ c, (eval c 0).Dom → T.Pr (H c))
    (hcorrecta : ∀ c, T.Pr (H c) → (eval c 0).Dom) : ¬ ComputablePred T.Pr :=
  demostrabilidad_indecidible T.Pr H hH hcompleta hcorrecta

/-- **Control: las hipótesis de la meta 2 se cumplen** con la «teoría» cuyos teoremas son los programas que terminan
(`H = id`). Es recursivamente enumerable (`ComputablePred.halting_problem_re`) y no decidible. -/
theorem meta2_satisfacible :
    (∀ c : Code, (eval c 0).Dom → (fun c : Code => (eval c 0).Dom) (id c)) ∧
      (∀ c : Code, (fun c : Code => (eval c 0).Dom) (id c) → (eval c 0).Dom) ∧
      REPred (fun c : Code => (eval c 0).Dom) ∧ ¬ ComputablePred (fun c : Code => (eval c 0).Dom) :=
  ⟨fun _ h => h, fun _ h => h, ComputablePred.halting_problem_re 0,
    demostrabilidad_indecidible _ id Computable.id (fun _ h => h) (fun _ h => h)⟩

/-- **Mutante refutado: sin corrección Σ₁.** La teoría que demuestra todo es completa para la parada y decidible. -/
theorem mutante_sin_correccion :
    ¬ ∀ (Pr : ℕ → Prop) (H : Code → ℕ), Computable H → (∀ c, (eval c 0).Dom → Pr (H c)) →
      ¬ ComputablePred Pr := by
  intro h
  refine h (fun _ => True) (fun _ => 0) (Computable.const 0) (fun _ _ => trivial) ?_
  exact ComputablePred.computable_iff.2 ⟨fun _ => true, Computable.const true, by funext; simp⟩

/-- **Mutante refutado: sin completitud Σ₁.** La teoría que no demuestra nada es correcta y decidible. -/
theorem mutante_sin_completitud :
    ¬ ∀ (Pr : ℕ → Prop) (H : Code → ℕ), Computable H → (∀ c, Pr (H c) → (eval c 0).Dom) →
      ¬ ComputablePred Pr := by
  intro h
  refine h (fun _ => False) (fun _ => 0) (Computable.const 0) (fun _ h => h.elim) ?_
  exact ComputablePred.computable_iff.2 ⟨fun _ => false, Computable.const false, by funext; simp⟩

/-! ## 6. El puente: la misma diagonal en dos idiomas -/

/-- **El lema diagonal común (esquema de Lawvere).** Si hay un punto `e` que dice lo contrario de lo que el
certificador dice de él (`Q e ↔ ¬ cert e`), el certificador no coincide con `Q`. -/
theorem diagonal_comun {X : Type} (Q cert : X → Prop) {e : X} (he : Q e ↔ ¬ cert e) :
    ¬ ∀ x, cert x ↔ Q x := fun h => by
  have := h e
  tauto

open Sagitta.Map.Tiempo.Bootstrap in
/-- **(a) desde el lema común: programas.** El teorema de recursión da el `e` que dice lo contrario del certificador;
`diagonal_comun` cierra. Es `no_hay_certificador_diagonal` rehecho con la diagonal abstracta. -/
theorem no_hay_certificador_comun :
    ¬ ∃ d : Code → Bool, Computable d ∧ ∀ c, d c = true ↔ ResuelveBusquedaSAT c := by
  rintro ⟨d, hd, hdc⟩
  obtain ⟨L, hL, -⟩ := construir_es_resolver
  have hf : Nat.Partrec (eval L) := Partrec.nat_iff.1 (eval_part.comp (Computable.const L) Computable.id)
  have hP : Partrec₂ fun (c : Code) (x : ℕ) => cond (d c) (Part.none : Part ℕ) (eval L x) :=
    (Partrec.cond (hd.comp Computable.fst) ((Partrec.nat_iff.2 Nat.Partrec.none).comp Computable.snd).to₂
      ((Partrec.nat_iff.2 hf).comp Computable.snd).to₂).to₂
  obtain ⟨e, he⟩ := fixed_point₂ hP
  have hdiag : ResuelveBusquedaSAT e ↔ ¬ (d e = true) := by
    cases hde : d e with
    | true =>
      have hev : eval e = fun _ => Part.none := by rw [he]; funext x; simp [hde]
      exact ⟨fun hr => absurd hr (vacio_no_resuelve hev), fun h => absurd rfl h⟩
    | false =>
      have hev : eval e = eval L := by rw [he]; funext x; simp [hde]
      exact ⟨fun _ => Bool.false_ne_true, fun _ => (resuelve_extensional hev).2 hL⟩
  exact diagonal_comun (fun c => ResuelveBusquedaSAT c) (fun c => d c = true) hdiag hdc

/-- **(b) desde el lema común: Gödel I semántico.** Si `V` es una valuación que respeta `imp` y `bot`, en la que
`caja a` vale si y solo si `a` es demostrable, y el sistema es correcto respecto de `V`, el punto fijo de Gödel da un
enunciado verdadero y no demostrable; en particular `Pr` no coincide con la verdad. -/
theorem godel_semantico_comun {S C : Type} (T : SistemaHBL S C) (V : S → Prop)
    (hV_imp : ∀ a b, V (T.imp a b) ↔ (V a → V b)) (hV_bot : ¬ V T.bot)
    (hV_caja : ∀ a, V (T.caja a) ↔ T.Pr a) (hcorr : ∀ a, T.Pr a → V a) {G : S} (hG : T.PuntoFijo G) :
    (V G ∧ ¬ T.Pr G) ∧ ¬ ∀ x, T.Pr x ↔ V x := by
  have e1 := (hV_imp _ _).1 (hcorr _ hG.1)
  have e2 := (hV_imp _ _).1 (hcorr _ hG.2)
  have hdiag : V G ↔ ¬ T.Pr G := by
    constructor
    · intro hg hp
      exact hV_bot (((hV_imp _ _).1 (e1 hg)) ((hV_caja G).2 hp))
    · intro hn
      exact e2 ((hV_imp _ _).2 fun hc => absurd ((hV_caja G).1 hc) hn)
  have hng : ¬ T.Pr G := fun hp => (hdiag.1 (hcorr G hp)) hp
  exact ⟨⟨hdiag.2 hng, hng⟩, diagonal_comun V T.Pr hdiag⟩

open Sagitta.Map.Tiempo.Bootstrap in
/-- **La misma diagonal en dos idiomas.** (a) Programas: no hay certificador computable de resolvedores de SAT
(`no_hay_certificador_diagonal`). (b) Teorías: un sistema con `D1`–`D3` y el punto fijo de Gödel que demuestra su
propia consistencia es inconsistente (`segundo_teorema`). (c) El esqueleto común: un punto que dice lo contrario del
certificador refuta al certificador (`diagonal_comun`), del que salen (a) y Gödel I semántico. -/
theorem misma_diagonal :
    (¬ ∃ d : Code → Bool, Computable d ∧ ∀ c, d c = true ↔ ResuelveBusquedaSAT c) ∧
    (∀ (S C : Type) (T : SistemaHBL S C) (G : S), T.D1 → T.D2 → T.D3 → T.PuntoFijo G →
      T.Pr T.Con → T.Pr T.bot) ∧
    (∀ (X : Type) (Q cert : X → Prop) (e : X), (Q e ↔ ¬ cert e) → ¬ ∀ x, cert x ↔ Q x) :=
  ⟨no_hay_certificador_diagonal, fun _ _ _ _ h1 h2 h3 hG hcon => segundo_teorema h1 h2 h3 hG hcon,
    fun _ Q cert _ he => diagonal_comun Q cert he⟩

end Sagitta.Map.Tiempo.DiagonalGodel
