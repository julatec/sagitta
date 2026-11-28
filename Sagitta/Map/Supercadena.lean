import Sagitta.Map.Clases
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# La supercadena común más corta, como instancia concreta de NP

Se dan varias cadenas de bits y una cota `k`. Se pregunta si hay una sola cadena de largo a lo sumo `k` que contenga
a todas como tramos contiguos. Es el primer problema concreto del proyecto: hasta aquí los problemas de NP eran
abstractos.

**De quién es.** Que el problema es NP-completo lo probaron Gallant, Maier y Storer (1980). Aquí no se formaliza eso.
Solo se formaliza la *pertenencia* a NP, que es un ejercicio: definir el verificador y comprobar la forma
«existe un certificado corto».

**Qué queda probado y qué no.**

* Probado, sin hipótesis: la corrección del verificador (`verifica_iff`), que la concatenación en cualquier orden es
  una supercadena (`concatenacion_esSupercadena`, `concatenacion_perm_esSupercadena`), que su largo no pasa del largo
  de la entrada (`suma_le_largo`), y la forma NP con cota lineal (`forma_np`).
* **Condicional:** `en_NP` toma como hipótesis `EsPolinomial verificador`, es decir, que una máquina de Turing calcula
  el verificador en tiempo polinomial. Es cierto y nada profundo (buscar cada cadena dentro del certificado), pero
  construir esa máquina con las piezas del proyecto es largo y no se hizo.

**La codificación de la entrada.** Un problema es una función de cadenas de bits. La entrada `x` se lee así: un primer
bloque autodelimitado (`CodBits.delimita`) con `k` en binario, y después un bloque autodelimitado por cada cadena.
La lectura es total: si `x` está mal formada, se toma lo que se alcance a leer (y `k = 0` si no hay ni el primer
bloque). Así no hay casos de error que arrastrar.
-/

namespace Sagitta.Map
namespace Supercadena

open CodBits

/-! ## Las definiciones -/

/-- `y` es supercadena de `cs`: contiene a cada cadena de `cs` como tramo contiguo. -/
def EsSupercadena (cs : List (List Bool)) (y : List Bool) : Prop := ∀ s ∈ cs, s <:+: y

/-- El verificador sobre la instancia ya leída: `y` mide a lo sumo `k` y contiene a cada cadena. -/
def verifica (k : ℕ) (cs : List (List Bool)) (y : List Bool) : Bool :=
  decide (y.length ≤ k) && cs.all fun s => decide (s <:+: y)

/-- **Corrección del verificador.** -/
theorem verifica_iff (k : ℕ) (cs : List (List Bool)) (y : List Bool) :
    verifica k cs y = true ↔ y.length ≤ k ∧ EsSupercadena cs y := by
  simp [verifica, EsSupercadena]

/-! ## La concatenación siempre sirve -/

/-- **Pegar todas las cadenas, sin traslapar, da una supercadena.** -/
theorem concatenacion_esSupercadena (cs : List (List Bool)) : EsSupercadena cs cs.flatten := by
  intro s hs
  induction cs with
  | nil => simp at hs
  | cons c cs ih =>
    rw [List.flatten_cons]
    rcases List.mem_cons.mp hs with rfl | h
    · exact (List.prefix_append s _).isInfix
    · exact (ih h).trans (List.suffix_append c _).isInfix

/-- **En cualquier orden.** El certificado económico es un orden de las cadenas: cualquiera da una supercadena
(después se acorta traslapando; aquí no hace falta). -/
theorem concatenacion_perm_esSupercadena {cs cs' : List (List Bool)} (h : cs'.Perm cs) :
    EsSupercadena cs cs'.flatten := fun s hs =>
  concatenacion_esSupercadena cs' s (h.mem_iff.mpr hs)

/-- El largo de la concatenación es la suma de los largos. -/
theorem largo_concatenacion (cs : List (List Bool)) : cs.flatten.length = (cs.map List.length).sum :=
  List.length_flatten

/-! ## Leer la entrada -/

/-- Un bloque leído ocupa el doble de su largo, más uno, del frente de la entrada. -/
theorem lee_largo : ∀ (l b r : List Bool), lee l = some (b, r) → 2 * b.length + 1 + r.length = l.length
  | [], b, r, h => by simp [lee] at h
  | false :: resto, b, r, h => by
    simp only [lee, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp; omega
  | [true], b, r, h => by simp [lee] at h
  | true :: c :: entrada, b, r, h => by
    simp only [lee, Option.map_eq_some_iff] at h
    obtain ⟨⟨b', r'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    have := lee_largo entrada b' r' h1
    simp; omega

/-- Lee bloques autodelimitados mientras se pueda, con combustible `n`. -/
def bloques : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | n + 1, l =>
    match lee l with
    | none => []
    | some (b, r) => b :: bloques n r

/-- Los bloques leídos caben en la entrada. -/
theorem suma_bloques_le (n : ℕ) (l : List Bool) : ((bloques n l).map List.length).sum ≤ l.length := by
  induction n generalizing l with
  | zero => simp [bloques]
  | succ n ih =>
    unfold bloques
    cases h : lee l with
    | none => simp
    | some p =>
      obtain ⟨b, r⟩ := p
      have h1 := lee_largo l b r h
      have h2 := ih r
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **La instancia leída de `x`**: la cota `k` (primer bloque, en binario) y la lista de cadenas (los demás). -/
def instancia (x : List Bool) : ℕ × List (List Bool) :=
  match lee x with
  | none => (0, [])
  | some (b, r) => (Computability.decodeNat b, bloques r.length r)

/-- **La suma de los largos de las cadenas no pasa del largo de la entrada.** -/
theorem suma_le_largo (x : List Bool) : (((instancia x).2).map List.length).sum ≤ x.length := by
  unfold instancia
  cases h : lee x with
  | none => simp
  | some p =>
    obtain ⟨b, r⟩ := p
    have h1 := lee_largo x b r h
    have h2 := suma_bloques_le r.length r
    simp only
    omega

/-! ## El problema y su forma NP -/

/-- **El verificador**: recibe la entrada cruda y el certificado. -/
def verificador : List Bool × List Bool → Bool :=
  fun p => verifica (instancia p.1).1 (instancia p.1).2 p.2

open Classical in
/-- **El problema**: ¿hay una supercadena de largo a lo sumo `k`? No es computable tal como está escrito (el «existe»
no tiene cota); que sí lo sea es lo que dice `forma_np`. -/
noncomputable def problema : Problema :=
  fun x => decide (∃ y : List Bool, y.length ≤ (instancia x).1 ∧ EsSupercadena (instancia x).2 y)

/-- **La forma NP, con cota lineal.** Si hay una supercadena de largo a lo sumo `k`, hay una que además no es más larga
que la entrada: o la dada ya es corta, o la concatenación de todas, que cabe en la entrada, también cumple la cota. -/
theorem forma_np (x : List Bool) :
    problema x = true ↔ ∃ y : List Bool, y.length ≤ x.length ∧ verificador (x, y) = true := by
  simp only [problema, decide_eq_true_eq, verificador, verifica_iff]
  constructor
  · rintro ⟨y, hk, hy⟩
    by_cases h : y.length ≤ x.length
    · exact ⟨y, h, hk, hy⟩
    · have hs := suma_le_largo x
      refine ⟨(instancia x).2.flatten, ?_, ?_, concatenacion_esSupercadena _⟩
      · rw [largo_concatenacion]; exact hs
      · rw [largo_concatenacion]; omega
  · rintro ⟨y, -, hk, hy⟩
    exact ⟨y, hk, hy⟩

/-- **La supercadena más corta está en NP**, dado que el verificador se calcula en tiempo polinomial. La hipótesis es
lo único que falta: pide la máquina de Turing del verificador. El polinomio de la cota es `X`. -/
theorem en_NP (hV : EsPolinomial verificador) : problema ∈ NP :=
  ⟨Polynomial.X, verificador, hV, fun x => by simpa using forma_np x⟩

/-! ## Un ejemplo

Tres cadenas con traslapes: `1100`, `0011`, `1111`. Pegadas miden 12; `11001111` mide 8 y las contiene a las tres. -/

/-- La entrada del ejemplo: `k = 8` y las tres cadenas. -/
def ejemplo : List Bool :=
  delimita (Computability.encodeNat 8) ++ delimita [true, true, false, false] ++
    delimita [false, false, true, true] ++ delimita [true, true, true, true]

example : instancia ejemplo =
    (8, [[true, true, false, false], [false, false, true, true], [true, true, true, true]]) := by
  decide

/-- El verificador acepta `11001111`. -/
example : verificador (ejemplo, [true, true, false, false, true, true, true, true]) = true := by decide

/-- Y rechaza la misma cadena sin su último bit: ya no contiene a `1111`. -/
example : verificador (ejemplo, [true, true, false, false, true, true, true]) = false := by decide

end Supercadena
end Sagitta.Map
