/-
Adaptado de `FormalConjecturesForMathlib/Computability/BitstringEncoding.lean`
(google-deepmind/formal-conjectures, commit 2207c54, 21 nov 2026).
Copyright 2026 The Formal Conjectures Authors. Licencia Apache 2.0 (ver `NOTICE.md`).
Cambios: nombres en español, sin el sistema de módulos, y solo las instancias que se usan aquí.
-/
import Mathlib.Computability.Encoding

/-!
# Codificación en bits

Una versión con clase de tipos de `Computability.Encoding`, fija en el alfabeto `Bool`: permite preguntar
«¿esta función se calcula en tiempo polinomial?» sin pasar la codificación a mano.
-/

open Computability

namespace Sagitta.Map

/-- Una codificación canónica de `α` como cadenas de bits. -/
class CodBits (α : Type) extends Computability.Encoding α Bool

namespace CodBits

variable {α β : Type}

/-- Codificar. -/
def cod [CodBits α] (a : α) : List Bool := toEncoding.encode a

/-- Decodificar. -/
def dec [CodBits α] (l : List Bool) : Option α := toEncoding.decode l

@[simp]
theorem dec_cod [CodBits α] (a : α) : dec (cod a) = some a :=
  toEncoding.decode_encode a

/-- `ℕ` en binario, como `Computability.encodeNat`. -/
instance : CodBits ℕ where
  encode := Computability.encodeNat
  decode l := some (Computability.decodeNat l)
  decode_encode n := congrArg some (Computability.decode_encodeNat n)

/-- `Bool` como una cadena de un bit. -/
instance : CodBits Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-- Vuelve autodelimitada una cadena: cada bit `b` pasa a `[true, b]` y el bloque cierra con `false`. -/
def delimita : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimita l

/-- Lee un bloque autodelimitado del frente de la entrada; devuelve el contenido y el resto. -/
def lee : List Bool → Option (List Bool × List Bool)
  | false :: resto => some ([], resto)
  | true :: b :: entrada => (lee entrada).map fun p => (b :: p.1, p.2)
  | _ => none

@[simp]
theorem lee_delimita (l resto : List Bool) : lee (delimita l ++ resto) = some (l, resto) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimita, lee, ih]

/-- Un par: el primer componente en un bloque autodelimitado, seguido del segundo. -/
instance [CodBits α] [CodBits β] : CodBits (α × β) where
  encode p := delimita (cod p.1) ++ cod p.2
  decode entrada :=
    match lee entrada with
    | none => none
    | some (bloque, resto) =>
      match dec bloque, dec resto with
      | some a, some b => some (a, b)
      | _, _ => none
  decode_encode p := by simp

/-- Una cadena de bits se codifica como ella misma. (El original la trata como lista de `Bool` con bloques;
aquí va directa: es polinomialmente equivalente y deja `Problema` sin envoltura.) -/
instance : CodBits (List Bool) where
  encode l := l
  decode l := some l
  decode_encode _ := rfl

end CodBits

end Sagitta.Map
