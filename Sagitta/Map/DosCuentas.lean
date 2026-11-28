import Sagitta.Map.LeyTresMemorias

/-!
# Las dos cuentas: una vez o en cada instancia

La frase es de José (24 nov 2026): **«el precio se paga sí o sí; lo que decide `P` contra `NP` es si se paga una vez
(escribir el resolvedor) o en cada instancia (correrlo)»**. Este módulo la pone, en caja negra, como teorema uniforme
en el tamaño.

## El modelo

Es el de `LeyTresMemorias.lean` (`ArbolV`, `corre`, `pasos`, `igual`, `Resuelve`), ahora para **una familia de
problemas indexada por el tamaño `m`**: para cada `m` hay `N_m = 2^m` instancias (`Y m`, con `|Y m| = 2^m`), una por
cada solución oculta, y el verificador es el de sí o no (`igual`) salvo en el control de bloques. Un resolvedor de la
familia da, para cada `m`, programas `P m` con `|P m| ≤ 2^(L m)`, citas `C m` con `|C m| ≤ 2^(s m)` y un tiempo
`t m`.

Las tres memorias del proyecto se reparten en **dos cuentas**:

* **la cuenta de una vez**: lo que se escribe **antes** de ver la instancia: el programa (aquí, el árbol `A`);
* **la cuenta por instancia**: `s + ⌈log₂(t + 1)⌉`, la cita y el tiempo de correr; el verificador pone la tasa.

**Corrección de la revisión adversarial (24 nov 2026).** En `Resuelve` (de `LeyTresMemorias`) el programa `p` se elige
**después** de ver la instancia, igual que la cita: `p` es consejo por instancia y es intercambiable con la cita
(`programa_por_instancia_es_cita`). Por eso `L` en las secciones 1 y 2 **no** es la cuenta de una vez: es parte de lo
que se paga por instancia, y los teoremas de esas secciones valen, pero con esa lectura. La cuenta de una vez de verdad
es un programa fijo antes de la instancia: `ResuelveUniforme`. Para ese, en caja negra, **la cuenta de una vez no paga
nada por instancia**, sea cual sea su largo (`una_vez_no_informa`): `2^m ≤ 2^s · (t + 1)`. Es la forma correcta de la
frase de José en caja negra, y es más fuerte que la versión con `− L`.

## Qué se prueba

1. **El precio se paga** (`precio_se_paga`, `precio_se_paga_producto`): para todo resolvedor y todo `m`,
   `L m + (s m + ⌈log₂(t m + 1)⌉) ≥ m`, o sea `2^m ≤ 2^(L m) · 2^(s m) · (t m + 1)`.
2. **La cuenta con `L` acotada** (`cuenta_por_instancia_uniforme`; ojo: `L` es consejo por instancia acotado, ver la
   corrección de arriba): con `L` constante,
   `s m + ⌈log₂(t m + 1)⌉ ≥ m − L` para todo `m`. **Una vez no alcanza** (`una_vez_no_alcanza`): si la cuenta de una
   vez está acotada por `L₀`, para `m > L₀` la cuenta por instancia no es cero. **Por instancia crece**
   (`por_instancia_crece`): sin cota. **Tiempo exponencial** (`tiempo_exponencial`, `tiempo_sin_cita`,
   `tiempo_crece`): si además la cita está acotada por `S`, `t m + 1 ≥ 2^(m − L₀ − S)`; con `s = 0`,
   `t m + 1 ≥ 2^(m − L₀)`.
3. **El contraste no uniforme** (`tabla_por_instancia`, `no_uniforme_paga`, `no_uniforme_crece`): si los programas
   pueden crecer con `m`, la cuenta por instancia se vacía (`s = 0`, `t = 0`) con `L m = m`, la solución en el
   programa; pero entonces `L m ≥ m` (o `≥ m − 1` con `t ≤ 1`): el precio se mudó a la cuenta de una vez y esa «una
   vez» ya no es una constante.
   **Matiz que el modelo obliga a decir** (`programa_por_tamano_no_informa`): en caja negra, un programa que depende
   de `m` pero no de la instancia no paga nada; cumple la misma cota que si no existiera. Lo que vacía la cuenta por
   instancia es **elegir** el programa según la instancia entre `2^(L m)`: la tabla indexada por la instancia. En
   caja blanca la tabla se indexa por el texto de la entrada y sí es un programa por tamaño; aquí no hay texto.
4. **Controles**: la fuerza bruta uniforme (`fuerza_bruta_uniforme`: `L = 0`, `s = 0`, `t = 2^m − 1`) está en la
   recta con igualdad; la tabla (`tabla_en_la_recta`: `L m = m`, `s = t = 0`), también. Con un verificador de `b`
   bits la cuenta por instancia es lineal en `m` (`bloques_lineal`: `t = k` para `m = b · k`), contra `2^m − 1` con el
   de sí o no (`verificador_decide`): **el verificador decide cuánto se paga por instancia**. La ley para `b` bits,
   uniforme: `cuenta_por_instancia_bits`.
5. **Mutantes refutados** (sección final).

## La lectura (no es teorema)

En caja negra el precio por instancia es **obligatorio** para un resolvedor uniforme: la información que identifica la
solución, `m` bits, no está en ningún lado que el resolvedor haya escrito de una vez, y solo entra por la cita o sale
del tiempo, al cambio que fija el verificador. Con el de sí o no ese cambio es pésimo (`t` consultas, `log₂(t+1)`
bits): un resolvedor uniforme sin cita paga `2^m` por instancia. En caja blanca el verificador es un texto (una
fórmula), la instancia ya contiene la información, y la pregunta es si una cuenta de una vez **constante** (un
programa) puede vaciar la cuenta por instancia hasta un polinomio en `m`: eso es `P = NP` para la búsqueda. Esta
identificación es lectura, no teorema.

## Lo que NO se prueba

* **Es caja negra y relativiza**: la instancia solo se ve por el verificador. Vale con cualquier oráculo (como el
  adversario de `Decidir.lean`; Baker, Gill y Solovay, 1975, de memoria) y por eso no puede decir nada de `P` contra
  `NP`.
* **Nada de caja blanca**: no hay entrada con texto, ni circuitos, ni tiempo de máquina; el tiempo es la cantidad de
  consultas al verificador.
* La cita no se busca ni se cobra su obtención: se da. Tampoco se cobra el costo de una consulta.
* **Nada sobre `P` contra `NP`.**
-/

namespace Sagitta.Map.Tiempo.DosCuentas

open Sagitta.Map.Tiempo.LeyTresMemorias
open Sagitta.Map.Tiempo.LeyTresMemorias.ArbolV

/-! ## Un lema de potencias -/

/-- Si `2^m ≤ 2^a · x`, entonces `2^(m − a) ≤ x`. -/
theorem dosCuentas_pow_sub_le {m a x : ℕ} (h : 2 ^ m ≤ 2 ^ a * x) : 2 ^ (m - a) ≤ x := by
  rcases Nat.le_total m a with hma | ham
  · rw [Nat.sub_eq_zero_of_le hma, pow_zero]
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx; simp at h
    · exact hx
  · have : 2 ^ a * 2 ^ (m - a) ≤ 2 ^ a * x := by rwa [← pow_add, Nat.add_sub_cancel' ham]
    exact Nat.le_of_mul_le_mul_left this (Nat.two_pow_pos a)

/-! ## 1. El precio se paga -/

section Precio

variable {Y P C : ℕ → Type} [∀ m, Fintype (Y m)] [∀ m, DecidableEq (Y m)] [∀ m, Fintype (P m)]
  [∀ m, Fintype (C m)] {L s t : ℕ → ℕ}

/-- **El precio se paga, en producto**: para todo resolvedor de la familia y todo tamaño `m`,
`2^m ≤ 2^(L m) · 2^(s m) · (t m + 1)`. Es `ley_si_no` tamaño por tamaño. -/
theorem precio_se_paga_producto (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m)) (m : ℕ) :
    2 ^ m ≤ 2 ^ L m * 2 ^ s m * (t m + 1) :=
  hY m ▸ ley_si_no (hP m) (hC m) (A m) (h m)

/-- **El precio se paga sí o sí**: (cuenta de una vez `L m`) + (cuenta por instancia `s m + ⌈log₂(t m + 1)⌉`)
`≥ m`, para todo resolvedor y todo `m`. -/
theorem precio_se_paga (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m)) (m : ℕ) :
    m ≤ L m + (s m + Nat.clog 2 (t m + 1)) := by
  have := ley_si_no_log (hP m) (hC m) (A m) (h m)
  rw [hY m, Nat.clog_pow 2 m one_lt_two] at this
  omega

/-- **Una vez no alcanza**: si la cuenta de una vez está acotada por una constante `L₀`, en todo tamaño `m > L₀` la
cuenta por instancia no es cero (`s m + ⌈log₂(t m + 1)⌉ ≥ m − L₀ ≥ 1`). -/
theorem una_vez_no_alcanza (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m))
    {L₀ : ℕ} (hL : ∀ m, L m ≤ L₀) (m : ℕ) :
    m - L₀ ≤ s m + Nat.clog 2 (t m + 1) ∧ (L₀ < m → 1 ≤ s m + Nat.clog 2 (t m + 1)) := by
  have := precio_se_paga hY hP hC A h m
  have := hL m
  omega

/-- **Por instancia crece**: si la cuenta de una vez es constante, la cuenta por instancia crece sin cota: para toda
`K` hay un tamaño desde el cual `K ≤ s m + ⌈log₂(t m + 1)⌉`. -/
theorem por_instancia_crece (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m))
    {L₀ : ℕ} (hL : ∀ m, L m ≤ L₀) (K : ℕ) :
    ∃ M, ∀ m, M ≤ m → K ≤ s m + Nat.clog 2 (t m + 1) :=
  ⟨K + L₀, fun m hm => by have := (una_vez_no_alcanza hY hP hC A h hL m).1; omega⟩

/-- **Con la cita acotada, el tiempo es exponencial**: si `L m ≤ L₀` y `s m ≤ S`, entonces
`2^(m − (L₀ + S)) ≤ t m + 1`. -/
theorem tiempo_exponencial (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m))
    {L₀ S : ℕ} (hL : ∀ m, L m ≤ L₀) (hS : ∀ m, s m ≤ S) (m : ℕ) :
    2 ^ (m - (L₀ + S)) ≤ t m + 1 := by
  apply dosCuentas_pow_sub_le
  calc 2 ^ m ≤ 2 ^ L m * 2 ^ s m * (t m + 1) := precio_se_paga_producto hY hP hC A h m
    _ ≤ 2 ^ L₀ * 2 ^ S * (t m + 1) := Nat.mul_le_mul_right _
        (Nat.mul_le_mul (Nat.pow_le_pow_right two_pos (hL m)) (Nat.pow_le_pow_right two_pos (hS m)))
    _ = 2 ^ (L₀ + S) * (t m + 1) := by rw [pow_add]

/-- **Sin cita** (`s = 0`): `t m + 1 ≥ 2^(m − L₀)`. -/
theorem tiempo_sin_cita (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ 0)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m))
    {L₀ : ℕ} (hL : ∀ m, L m ≤ L₀) (m : ℕ) :
    2 ^ (m - L₀) ≤ t m + 1 := by
  simpa using tiempo_exponencial (s := fun _ => 0) (S := 0) hY hP hC A h hL (fun _ => le_rfl) m

/-- **Y el tiempo crece sin cota** (con la cita acotada): para toda `K` hay un tamaño desde el cual `K ≤ t m`. -/
theorem tiempo_crece (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m))
    {L₀ S : ℕ} (hL : ∀ m, L m ≤ L₀) (hS : ∀ m, s m ≤ S) (K : ℕ) :
    ∃ M, ∀ m, M ≤ m → K ≤ t m := by
  refine ⟨K + (L₀ + S), fun m hm => ?_⟩
  have h1 := tiempo_exponencial hY hP hC A h hL hS m
  have h2 : m - (L₀ + S) < 2 ^ (m - (L₀ + S)) := Nat.lt_two_pow_self
  omega

end Precio

/-! ## La cuenta uniforme: un mismo juego de programas para todo tamaño -/

section Uniforme

variable {Y C : ℕ → Type} [∀ m, Fintype (Y m)] [∀ m, DecidableEq (Y m)] [∀ m, Fintype (C m)] {s t : ℕ → ℕ}

/-- **La cuenta uniforme**: con los mismos programas `P` (`|P| ≤ 2^L`, `L` constante) para todo tamaño,
`s m + ⌈log₂(t m + 1)⌉ ≥ m − L` para todo `m`. -/
theorem cuenta_por_instancia_uniforme {P : Type} [Fintype P] {L : ℕ} (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : Fintype.card P ≤ 2 ^ L) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m)) (m : ℕ) :
    m - L ≤ s m + Nat.clog 2 (t m + 1) :=
  (una_vez_no_alcanza (P := fun _ => P) (L := fun _ => L) hY (fun _ => hP) hC A h (fun _ => le_rfl) m).1

/-- **Uniforme y sin cita**: `t m + 1 ≥ 2^(m − L)`. -/
theorem tiempo_uniforme_sin_cita {P : Type} [Fintype P] {L : ℕ} (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : Fintype.card P ≤ 2 ^ L) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ 0)
    (A : ∀ m, P → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m)) (m : ℕ) :
    2 ^ (m - L) ≤ t m + 1 :=
  tiempo_sin_cita (P := fun _ => P) (L := fun _ => L) hY (fun _ => hP) hC A h (fun _ => le_rfl) m

/-- **Un único programa por tamaño no informa nada**, aunque dependa de `m`: si para cada `m` hay un solo árbol
(por cita), cualquiera sea el largo de su descripción, `2^m ≤ 2^(s m) · (t m + 1)`, la cota de `L = 0`. En caja
negra, depender del tamaño sin depender de la instancia no vacía la cuenta por instancia. -/
theorem programa_por_tamano_no_informa (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m) (A : ∀ m, C m → ArbolV (Y m) Bool (Y m))
    (h : ∀ m y, ∃ c, (A m c).corre (igual y) = y ∧ (A m c).pasos (igual y) ≤ t m) (m : ℕ) :
    2 ^ m ≤ 2 ^ s m * (t m + 1) :=
  hY m ▸ ley_programa_fijo (hC m) (A m) (h m)

end Uniforme

/-! ## 2. El contraste no uniforme: la tabla -/

/-- **La tabla por instancia** (la solución en el programa, `solucion_programa_en_la_recta`): con `P m = Fin (2^m)`
programas, `L m = m`, la cuenta por instancia se vacía: sin cita y en `t = 0` consultas. -/
theorem tabla_por_instancia (m : ℕ) :
    Resuelve (P := Fin (2 ^ m)) (C := Unit) igual (fun p _ => .hoja p) 0 :=
  (solucion_programa_en_la_recta m).1

/-- **Pero no es gratis**: si la cuenta por instancia es cero (`s m = 0`, `t m = 0`), la cuenta de una vez es
`L m ≥ m`; con `t m ≤ 1` (verificar y devolver), `L m ≥ m − 1`. El precio se mudó, no se fue. -/
theorem no_uniforme_paga {Y P C : ℕ → Type} [∀ m, Fintype (Y m)] [∀ m, DecidableEq (Y m)]
    [∀ m, Fintype (P m)] [∀ m, Fintype (C m)] {L s t : ℕ → ℕ} (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m)) (m : ℕ)
    (hs : s m = 0) : (t m = 0 → m ≤ L m) ∧ (t m ≤ 1 → m ≤ L m + 1) := by
  have := precio_se_paga hY hP hC A h m
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · rw [hs, ht] at this; simpa using this
  · have hc : Nat.clog 2 (t m + 1) ≤ 1 := Nat.clog_le_of_le_pow (by simpa using Nat.succ_le_succ ht)
    omega

/-- **La una vez de la tabla crece con `m`**: si la cuenta por instancia es cero en todo tamaño, la cuenta de una vez
no está acotada por ninguna constante. -/
theorem no_uniforme_crece {Y P C : ℕ → Type} [∀ m, Fintype (Y m)] [∀ m, DecidableEq (Y m)]
    [∀ m, Fintype (P m)] [∀ m, Fintype (C m)] {L s t : ℕ → ℕ} (hY : ∀ m, Fintype.card (Y m) = 2 ^ m)
    (hP : ∀ m, Fintype.card (P m) ≤ 2 ^ L m) (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m)
    (A : ∀ m, P m → C m → ArbolV (Y m) Bool (Y m)) (h : ∀ m, Resuelve igual (A m) (t m))
    (hs : ∀ m, s m = 0) (ht : ∀ m, t m = 0) (L₀ : ℕ) : ¬ ∀ m, L m ≤ L₀ := by
  intro hL
  have := (no_uniforme_paga hY hP hC A h (L₀ + 1) (hs _)).1 (ht _)
  have := hL (L₀ + 1)
  omega

/-! ## 3. Controles -/

/-- **La tabla en la recta**: `2^m = 2^(L m) · 2^0 · (0 + 1)` con `L m = m`, y la cuenta por instancia es cero. -/
theorem tabla_en_la_recta (m : ℕ) :
    Fintype.card (Fin (2 ^ m)) = 2 ^ m ∧ Fintype.card (Fin (2 ^ m)) = 2 ^ m * 2 ^ 0 * (0 + 1) ∧
      0 + Nat.clog 2 (0 + 1) = 0 := by
  simp

/-- La familia de la fuerza bruta: `Fin (2^m − 1 + 1)`, que tiene `2^m` elementos. -/
abbrev YFuerza (m : ℕ) : Type := Fin (2 ^ m - 1 + 1)

theorem card_YFuerza (m : ℕ) : Fintype.card (YFuerza m) = 2 ^ m := by
  simp [YFuerza, Nat.sub_add_cancel Nat.one_le_two_pow]

/-- **La fuerza bruta uniforme**: un solo programa para todo tamaño (`L = 0`), sin cita (`s = 0`), en
`t m = 2^m − 1` consultas. -/
theorem fuerza_bruta_uniforme (m : ℕ) :
    Resuelve (P := Unit) (C := Unit) igual
      (fun _ _ => barrer (todosMenosUltimo (2 ^ m - 1)) (Fin.last (2 ^ m - 1))) (2 ^ m - 1) :=
  fuerza_bruta (2 ^ m - 1)

/-- **Y está en la recta con igualdad**: la cota `tiempo_uniforme_sin_cita` (`2^(m − 0) ≤ t m + 1`) se alcanza, y la
ley en producto es una igualdad. La hipótesis de los teoremas uniformes no es vacía. -/
theorem fuerza_bruta_uniforme_en_la_recta (m : ℕ) :
    2 ^ (m - 0) = (2 ^ m - 1) + 1 ∧ Fintype.card (YFuerza m) = 2 ^ 0 * 2 ^ 0 * ((2 ^ m - 1) + 1) ∧
      (∀ m', 2 ^ (m' - 0) ≤ (2 ^ m' - 1) + 1) := by
  refine ⟨by simp [Nat.sub_add_cancel Nat.one_le_two_pow], by simp [Nat.sub_add_cancel Nat.one_le_two_pow],
    fun m' => ?_⟩
  exact tiempo_uniforme_sin_cita (Y := YFuerza) (C := fun _ => Unit) (P := Unit) (L := 0)
    (t := fun m => 2 ^ m - 1) card_YFuerza (by simp) (fun _ => by simp)
    (fun m _ _ => barrer (todosMenosUltimo (2 ^ m - 1)) (Fin.last (2 ^ m - 1))) fuerza_bruta_uniforme m'

/-- **La ley para un verificador de `b` bits, uniforme**: con `|R| ≤ 2^b` y programas fijos (`|P| ≤ 2^L`),
`s m + b · t m ≥ m − L`. La cuenta por instancia en bits es `s + b · t`. -/
theorem cuenta_por_instancia_bits {Y C : ℕ → Type} [∀ m, Fintype (Y m)] [∀ m, Fintype (C m)] {Q R P : Type} [Fintype R] [Fintype P] {L b : ℕ} {s t : ℕ → ℕ}
    (hY : ∀ m, Fintype.card (Y m) = 2 ^ m) (hP : Fintype.card P ≤ 2 ^ L)
    (hC : ∀ m, Fintype.card (C m) ≤ 2 ^ s m) (hR : Fintype.card R ≤ 2 ^ b)
    (O : ∀ m, Y m → Q → R) (A : ∀ m, P → C m → ArbolV Q R (Y m)) (h : ∀ m, Resuelve (O m) (A m) (t m))
    (m : ℕ) : m - L ≤ s m + b * t m := by
  classical
  have := ley_log hP (hC m) hR (O m) (A m) (h m)
  rw [hY m, Nat.clog_pow 2 m one_lt_two] at this
  omega

/-- **Con bloques de `b` bits la cuenta por instancia es lineal**: para `m = b · k`, sin programa ni cita, en `t = k`
consultas, y en la recta (`b · t = m`). -/
theorem bloques_lineal (b k : ℕ) :
    Resuelve (P := Unit) (C := Unit) bloque (fun _ _ => leerBloques k b) k ∧
      Fintype.card (Fin k → Fin (2 ^ b)) = 2 ^ (b * k) :=
  ⟨bloques_alcanza k b, by simp [← pow_mul]⟩

/-- **El verificador decide cuánto se paga por instancia**: con bloques de un bit, `2^m` instancias se resuelven en
`t = m` consultas; con el de sí o no, cualquier resolvedor sin programa ni cita necesita `t + 1 ≥ 2^m`. -/
theorem verificador_decide (m : ℕ) :
    Resuelve (P := Unit) (C := Unit) bloque (fun _ _ => leerBloques m 1) m ∧
      Fintype.card (Fin m → Fin (2 ^ 1)) = 2 ^ m ∧
      ∀ (A : Unit → Unit → ArbolV (Fin (2 ^ m)) Bool (Fin (2 ^ m))) (t : ℕ), Resuelve igual A t →
        2 ^ m ≤ t + 1 := by
  refine ⟨bloques_alcanza m 1, by simp, fun A t h => ?_⟩
  simpa using ley_si_no (L := 0) (s := 0) (by simp) (by simp) A h

/-! ## 4. Mutantes refutados -/

/-- **Sin uniformidad, la cuenta por instancia no crece**: la tabla la deja en cero en todo tamaño. `por_instancia_crece`
sin la hipótesis `L m ≤ L₀` es falso. -/
theorem mutante_crece_sin_uniforme :
    (∀ m, Resuelve (P := Fin (2 ^ m)) (C := Unit) igual (fun p _ => .hoja p) 0) ∧
      ¬ ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (1 : ℕ) ≤ 0 + Nat.clog 2 (0 + 1) := by
  refine ⟨tabla_por_instancia, ?_⟩
  rintro ⟨M, hM⟩
  simpa using hM M le_rfl

/-- **Sin el `− L`** (`2^m ≤ t m + 1` para todo resolvedor sin cita) es falso: con dos programas (`L = 1`) elegidos
según la instancia, las dos instancias de tamaño 1 se resuelven en `t = 0`. -/
theorem mutante_sin_menos_L :
    ¬ ∀ (A : Fin 2 → Unit → ArbolV (Fin (2 ^ 1)) Bool (Fin (2 ^ 1))) (t : ℕ), Resuelve igual A t →
      2 ^ 1 ≤ t + 1 := by
  intro h
  have := h (fun p _ => .hoja p) 0 fun y => ⟨y, (), by simp [corre, pasos]⟩
  simp at this

/-- **Sin el `− 1`** (`t m ≥ 2^m` para el uniforme sin cita) es falso: la fuerza bruta lo hace en `2^m − 1`. -/
theorem mutante_sin_menos_uno :
    ¬ ∀ (A : Unit → Unit → ArbolV (YFuerza 1) Bool (YFuerza 1)) (t : ℕ), Resuelve igual A t → 2 ^ 1 ≤ t :=
  fun h => by have := h _ _ (fuerza_bruta_uniforme 1); simp at this

/-- **Ignorar la cita** (`2^(m − L) ≤ t + 1` con `s = 1`) es falso: la mezcla con un bit de cita resuelve las 4
instancias de tamaño 2 en `t = 2`, y `4 ≤ 3` no vale. -/
theorem mutante_ignora_cita :
    ¬ ∀ (A : Unit → Fin (2 ^ 1) → ArbolV (Fin (2 ^ 1) × Fin (2 ^ 1)) Bool (Fin (2 ^ 1) × Fin (2 ^ 1)))
      (t : ℕ), Resuelve igual A t → 2 ^ (2 - 0) ≤ t + 1 :=
  fun h => by have := h _ _ (mezcla 1 1); simp at this

/-- **Lineal con el de sí o no** es falso: ningún resolvedor sin programa ni cita halla las 4 instancias de tamaño
`m = 2` en `t = m = 2` consultas de igualdad. Lo que los bloques logran, la igualdad no. -/
theorem mutante_lineal_con_igual (A : Unit → Unit → ArbolV (Fin (2 ^ 2)) Bool (Fin (2 ^ 2))) :
    ¬ Resuelve igual A 2 := by
  intro h
  have := (verificador_decide 2).2.2 A 2 h
  simp at this

/-- **Un bit más en la cota** (`m + 1 ≤ L + s + ⌈log₂(t + 1)⌉`) es falso: la fuerza bruta uniforme está en la
recta. -/
theorem mutante_un_bit_mas :
    ¬ ∀ (A : Unit → Unit → ArbolV (YFuerza 2) Bool (YFuerza 2)) (t : ℕ), Resuelve igual A t →
      2 + 1 ≤ 0 + (0 + Nat.clog 2 (t + 1)) := by
  intro h
  have := h _ _ (fuerza_bruta_uniforme 2)
  have h4 : (2 ^ 2 - 1 + 1 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, Nat.clog_pow 2 2 one_lt_two] at this
  omega

/-! ## 6. La cuenta de una vez, de verdad (corrección de la revisión) -/

section UnaVez

/-- **Resolver con un programa escrito una vez**: el árbol `A` se fija antes de ver la instancia; por instancia solo
entra la cita `c`. -/
def ResuelveUniforme {C Y : Type} [DecidableEq Y] (A : C → ArbolV Y Bool Y) (t : ℕ) : Prop :=
  ∀ y, ∃ c, (A c).corre (igual y) = y ∧ (A c).pasos (igual y) ≤ t

/-- **Un programa elegido por instancia es una cita**: si `Resuelve` vale con programas `P` y citas `C`, vale
`ResuelveUniforme` con la cita `P × C`. En `Resuelve`, `L` es cuenta por instancia. -/
theorem programa_por_instancia_es_cita {P C Y : Type} [DecidableEq Y] {A : P → C → ArbolV Y Bool Y} {t : ℕ}
    (h : Resuelve igual A t) : ResuelveUniforme (fun pc : P × C => A pc.1 pc.2) t := fun y => by
  obtain ⟨p, c, hy⟩ := h y
  exact ⟨(p, c), hy⟩

/-- **La cuenta de una vez no paga nada por instancia** (caja negra, verificador de sí o no): con un programa escrito
antes de la instancia, de cualquier largo, `2^m ≤ 2^s · (t + 1)`. -/
theorem una_vez_no_informa {C Y : Type} [Fintype C] [Fintype Y] [DecidableEq Y] {m s t : ℕ}
    (hY : Fintype.card Y = 2 ^ m) (hC : Fintype.card C ≤ 2 ^ s) (A : C → ArbolV Y Bool Y)
    (h : ResuelveUniforme A t) : 2 ^ m ≤ 2 ^ s * (t + 1) :=
  hY ▸ ley_programa_fijo hC A h

/-- **Por instancia se paga todo**: `m ≤ s + ⌈log₂(t + 1)⌉`. -/
theorem por_instancia_paga_todo {C Y : Type} [Fintype C] [Fintype Y] [DecidableEq Y] {m s t : ℕ}
    (hY : Fintype.card Y = 2 ^ m) (hC : Fintype.card C ≤ 2 ^ s) (A : C → ArbolV Y Bool Y)
    (h : ResuelveUniforme A t) : m ≤ s + Nat.clog 2 (t + 1) := by
  have h1 := una_vez_no_informa hY hC A h
  have h2 : 2 ^ s * (t + 1) ≤ 2 ^ (s + Nat.clog 2 (t + 1)) := by
    rw [pow_add]; exact Nat.mul_le_mul_left _ (Nat.le_pow_clog one_lt_two _)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans h2)

/-- **Sin cita, el tiempo es todo**: `2^m ≤ t + 1`. -/
theorem sin_cita_tiempo_todo {Y : Type} [Fintype Y] [DecidableEq Y] {m t : ℕ}
    (hY : Fintype.card Y = 2 ^ m) (A : Unit → ArbolV Y Bool Y) (h : ResuelveUniforme A t) : 2 ^ m ≤ t + 1 := by
  simpa using una_vez_no_informa (s := 0) hY (by simp) A h

end UnaVez

end Sagitta.Map.Tiempo.DosCuentas
