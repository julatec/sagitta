import Sagitta.Map.DosCuentas

/-!
# El huevo y la gallina: ¿quien nos dio el problema pagó lo mismo que quien lo resuelve?

## La pregunta de José y la respuesta

La pregunta es de José (24 nov 2026): si alguien nos dio el problema, ¿ese alguien pagó el mismo precio que quien lo
resuelve? La versión fuerte («crear y resolver cuestan lo mismo») es **falsa en caja negra**, y en caja blanca sería
negar que existan las funciones de un solo sentido. Lo que sí se conserva es otra cosa: **lo que se conserva es la
información que usó el creador, no su trabajo.**

* El creador tira `r` bits de azar (la semilla `σ`) y calcula `g σ`, la solución escondida. Paga `r` bits de azar y
  un cálculo que acá se **declara** (`Creador.trabajo`); no es tiempo de máquina.
* Quien resuelve ve solo el verificador de sí o no `igual (g σ)`. Sin la semilla, con un programa fijo y citas de `s`
  bits, paga `|imagen g| ≤ 2^s · (t + 1)` (`precio_es_la_imagen`); si `g` es inyectiva, `2^r ≤ 2^s · (t + 1)`
  (`paga_la_informacion`), o sea `r ≤ s + ⌈log₂(t + 1)⌉`. Sin cita, `2^r ≤ t + 1`.
* Con la semilla como cita (`s = r`) resuelve **sin preguntar nada**: `t = 0` (`semilla_alcanza`). La semilla es
  exactamente la información que faltaba: con `t = 0` no alcanza ninguna cita de menos de `r` bits
  (`sin_tiempo_cita_completa`).

## El modelo

Es el de `LeyTresMemorias.lean` (`ArbolV`, `corre`, `pasos`, `igual`) y `DosCuentas.lean` (`ResuelveUniforme`).

* Un **creador** (`Creador Y`) es una cantidad de bits de azar `r`, una función `g : Fin (2^r) → Y` de la semilla a
  la solución escondida, y un costo de cálculo declarado `trabajo`. Su costo es `(r, trabajo)`: `r` bits de azar más
  ese cálculo.
* La **familia** de instancias es `{igual (g σ) | σ}`; tiene `|imagen g|` instancias distintas, `2^r` si `g` es
  inyectiva (`card_familia_inyectiva`).
* **Resolver la familia** (`ResuelveFamilia g A t`): un árbol `A c` fijo antes de ver la instancia, con una cita `c`
  elegida por instancia, que devuelve `g σ` en a lo sumo `t` consultas. Un resolvedor uniforme de `DosCuentas`
  resuelve cualquier familia (`uniforme_resuelve_familia`).

## Qué se prueba

1. **Quien resuelve sin semilla paga la información del creador** (`precio_es_la_imagen`, `paga_la_informacion`,
   `paga_la_informacion_bits`, `paga_sin_cita`, `paga_la_informacion_uniforme`).
2. **Con la semilla como cita, resolver es barato** (`semilla_alcanza`: `s = r`, `t = 0`), y la semilla es justa:
   `sin_tiempo_cita_completa` (`t = 0` obliga a `s ≥ r`).
3. **La asimetría** (`creador_barato`, `resolver_caro`, `asimetria`): para todo `r`, el creador identidad sobre
   `Fin (2^r)` paga `r` bits de azar y una evaluación, y todo resolvedor uniforme sin cita necesita `t + 1 ≥ 2^r`;
   con `s` bits de cita, `2^r ≤ 2^s · (t + 1)`. La cota es justa salvo una consulta (`resolver_caro_alcanza`: barrer
   resuelve en `t = 2^r`).
4. **Lo que se conserva es información, no trabajo** (`imagen_alcanza`, `informacion_no_trabajo`, `recorte_precio`):
   el precio para quien resuelve es el log del tamaño de la imagen, de los dos lados (la cota de
   `precio_es_la_imagen` se alcanza con `t = 0` y una cita del tamaño de la imagen). Un creador constante con `r`
   bits de azar y trabajo `W` arbitrarios produce **una** instancia, que se resuelve con `t = 0` y sin cita. El
   recorte `σ ↦ σ mod 2^k` gasta `r ≥ k` bits pero solo cobra `2^k`.
5. **Mutantes refutados** (sección final), cada uno con un contraejemplo: el falso queda probado falso.

## La lectura (no es teorema)

* **En caja negra la asimetría está probada.** Es la versión relativizada de Bennett y Gill 1981: con un oráculo al
  azar, `P ≠ NP` con probabilidad 1. Acá el oráculo es el verificador de la semilla escondida: el creador la conoce
  porque la tiró, quien resuelve solo la ve por consultas de sí o no.
* **En caja blanca**, la instancia es un texto que ya determina la solución: no falta información, falta cómputo.
  Ahí «crear y resolver cuestan lo mismo» sería que **no existen funciones de un solo sentido** (invertir `g` sería tan
  barato como evaluarla). Liu y Pass (FOCS 2020) ligan la existencia de funciones de un solo sentido con la
  dificultad de la complejidad de Kolmogorov con tiempo acotado. Nada de eso se formaliza acá.

## Lo que NO se prueba

* **El costo del creador es declarado**, no es tiempo de máquina: `trabajo` es un número que acompaña a `g`, y
  ningún teorema lo mide contra un modelo de cómputo.
* **Es caja negra y relativiza**: quien resuelve ve la instancia solo por el verificador. Por eso vale con cualquier
  oráculo y no puede separar clases.
* **Nada sobre funciones de un solo sentido en caja blanca**: no hay entrada con texto, ni circuitos.
* **Nada sobre `P` contra `NP`.**
-/

namespace Sagitta.Map.Tiempo.HuevoGallina

open Sagitta.Map.Tiempo.LeyTresMemorias
open Sagitta.Map.Tiempo.LeyTresMemorias.ArbolV
open Sagitta.Map.Tiempo.DosCuentas

/-! ## El creador -/

/-- **Un creador**: tira `r` bits de azar (la semilla), calcula `g σ` (la solución escondida) y declara cuánto le costó
ese cálculo (`trabajo`). Su costo es `r` bits de azar más `trabajo`; el `trabajo` es declarado, no medido. -/
structure Creador (Y : Type) where
  /-- Los bits de azar: la semilla es un elemento de `Fin (2^r)`. -/
  r : ℕ
  /-- De la semilla a la solución escondida. -/
  g : Fin (2 ^ r) → Y
  /-- El costo declarado de calcular `g`. -/
  trabajo : ℕ

/-- Las soluciones escondidas que el creador puede producir: la imagen de `g`. La familia de instancias que ve quien
resuelve es `{igual y | y ∈ imagen}`. -/
def Creador.imagen {Y : Type} [DecidableEq Y] (K : Creador Y) : Finset Y := Finset.univ.image K.g

/-- **Resolver la familia del creador**: un programa fijo `A` (escrito antes de ver la instancia) y, por instancia, una
cita `c`; con el verificador de `g σ`, el árbol `A c` devuelve `g σ` en a lo sumo `t` consultas. -/
def ResuelveFamilia {r : ℕ} {C Y : Type} [DecidableEq Y] (g : Fin (2 ^ r) → Y) (A : C → ArbolV Y Bool Y)
    (t : ℕ) : Prop :=
  ∀ σ, ∃ c, (A c).corre (igual (g σ)) = g σ ∧ (A c).pasos (igual (g σ)) ≤ t

/-- **Un resolvedor uniforme resuelve cualquier familia**: si resuelve todas las instancias (`ResuelveUniforme` de
`DosCuentas`), resuelve las del creador. -/
theorem uniforme_resuelve_familia {r : ℕ} {C Y : Type} [DecidableEq Y] {A : C → ArbolV Y Bool Y} {t : ℕ}
    (g : Fin (2 ^ r) → Y) (h : ResuelveUniforme A t) : ResuelveFamilia g A t := fun σ => h (g σ)

/-- **Si `g` es inyectiva, hay `2^r` instancias distintas.** -/
theorem card_familia_inyectiva {Y : Type} [DecidableEq Y] (K : Creador Y) (hg : Function.Injective K.g) :
    K.imagen.card = 2 ^ K.r := by
  rw [Creador.imagen, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]

/-! ## 1. Quien resuelve sin semilla paga la información del creador -/

/-- **El precio es la imagen**: un resolvedor con programa fijo y citas de `s` bits que resuelve la familia en `t`
consultas cumple `|imagen g| ≤ 2^s · (t + 1)`. Cada cita halla a lo sumo `t + 1` soluciones (`halla_le_si_no`). -/
theorem precio_es_la_imagen {r s t : ℕ} {C Y : Type} [Fintype C] [DecidableEq Y] (hC : Fintype.card C ≤ 2 ^ s)
    (g : Fin (2 ^ r) → Y) (A : C → ArbolV Y Bool Y) (h : ResuelveFamilia g A t) :
    (Finset.univ.image g).card ≤ 2 ^ s * (t + 1) := by
  calc (Finset.univ.image g).card
        ≤ (Finset.univ.biUnion fun c => (Finset.univ.image g).filter
            fun y => (A c).corre (igual y) = y ∧ (A c).pasos (igual y) ≤ t).card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hy
          obtain ⟨c, hc⟩ := h σ
          exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_filter.2 ⟨hy, hc⟩⟩
    _ ≤ ∑ c, ((Finset.univ.image g).filter
            fun y => (A c).corre (igual y) = y ∧ (A c).pasos (igual y) ≤ t).card := Finset.card_biUnion_le
    _ ≤ ∑ _c : C, (t + 1) := Finset.sum_le_sum fun c _ => halla_le_si_no (A c) t _
    _ = Fintype.card C * (t + 1) := by simp
    _ ≤ 2 ^ s * (t + 1) := Nat.mul_le_mul_right _ hC

/-- **En bits**: `⌈log₂ |imagen g|⌉ ≤ s + ⌈log₂(t + 1)⌉`. -/
theorem precio_es_la_imagen_bits {r s t : ℕ} {C Y : Type} [Fintype C] [DecidableEq Y]
    (hC : Fintype.card C ≤ 2 ^ s) (g : Fin (2 ^ r) → Y) (A : C → ArbolV Y Bool Y) (h : ResuelveFamilia g A t) :
    Nat.clog 2 (Finset.univ.image g).card ≤ s + Nat.clog 2 (t + 1) := by
  apply Nat.clog_le_of_le_pow
  calc (Finset.univ.image g).card ≤ 2 ^ s * (t + 1) := precio_es_la_imagen hC g A h
    _ ≤ 2 ^ s * 2 ^ Nat.clog 2 (t + 1) := Nat.mul_le_mul_left _ (Nat.le_pow_clog one_lt_two _)
    _ = 2 ^ (s + Nat.clog 2 (t + 1)) := (pow_add _ _ _).symm

/-- **Quien resuelve paga la información del creador**: con `g` inyectiva, `2^r ≤ 2^s · (t + 1)`. -/
theorem paga_la_informacion {s t : ℕ} {C Y : Type} [Fintype C] [DecidableEq Y] (K : Creador Y)
    (hg : Function.Injective K.g) (hC : Fintype.card C ≤ 2 ^ s) (A : C → ArbolV Y Bool Y)
    (h : ResuelveFamilia K.g A t) : 2 ^ K.r ≤ 2 ^ s * (t + 1) := by
  have := precio_es_la_imagen hC K.g A h
  rwa [← Creador.imagen, card_familia_inyectiva K hg] at this

/-- **En bits**: `r ≤ s + ⌈log₂(t + 1)⌉`. -/
theorem paga_la_informacion_bits {s t : ℕ} {C Y : Type} [Fintype C] [DecidableEq Y] (K : Creador Y)
    (hg : Function.Injective K.g) (hC : Fintype.card C ≤ 2 ^ s) (A : C → ArbolV Y Bool Y)
    (h : ResuelveFamilia K.g A t) : K.r ≤ s + Nat.clog 2 (t + 1) := by
  have h1 := paga_la_informacion K hg hC A h
  have h2 : 2 ^ s * (t + 1) ≤ 2 ^ (s + Nat.clog 2 (t + 1)) := by
    rw [pow_add]; exact Nat.mul_le_mul_left _ (Nat.le_pow_clog one_lt_two _)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans h2)

/-- **Sin cita**: `2^r ≤ t + 1`. -/
theorem paga_sin_cita {t : ℕ} {Y : Type} [DecidableEq Y] (K : Creador Y) (hg : Function.Injective K.g)
    (A : Unit → ArbolV Y Bool Y) (h : ResuelveFamilia K.g A t) : 2 ^ K.r ≤ t + 1 := by
  simpa using paga_la_informacion (s := 0) K hg (by simp) A h

/-- **La versión con `ResuelveUniforme`**: un resolvedor uniforme (que resuelve toda instancia) con citas de `s` bits
paga lo mismo frente a cualquier creador inyectivo. -/
theorem paga_la_informacion_uniforme {s t : ℕ} {C Y : Type} [Fintype C] [DecidableEq Y] (K : Creador Y)
    (hg : Function.Injective K.g) (hC : Fintype.card C ≤ 2 ^ s) (A : C → ArbolV Y Bool Y)
    (h : ResuelveUniforme A t) : 2 ^ K.r ≤ 2 ^ s * (t + 1) :=
  paga_la_informacion K hg hC A (uniforme_resuelve_familia K.g h)

/-! ## 2. Con la semilla como cita, resolver es barato -/

/-- **La semilla resuelve sin preguntar**: con la cita `σ` (`s = r`, `|C| = 2^r`), el árbol que devuelve `g σ` resuelve
la familia en `t = 0` consultas. Es el control: la semilla es la información que faltaba. -/
theorem semilla_alcanza {Y : Type} [DecidableEq Y] (K : Creador Y) :
    ResuelveFamilia K.g (fun σ : Fin (2 ^ K.r) => .hoja (K.g σ)) 0 ∧ Fintype.card (Fin (2 ^ K.r)) = 2 ^ K.r :=
  ⟨fun σ => ⟨σ, by simp [corre, pasos]⟩, Fintype.card_fin _⟩

/-- **Y no sobra nada**: con `g` inyectiva y `t = 0`, toda cita que alcance tiene `s ≥ r` bits. La semilla es
exactamente la información que faltaba. -/
theorem sin_tiempo_cita_completa {s : ℕ} {C Y : Type} [Fintype C] [DecidableEq Y] (K : Creador Y)
    (hg : Function.Injective K.g) (hC : Fintype.card C ≤ 2 ^ s) (A : C → ArbolV Y Bool Y)
    (h : ResuelveFamilia K.g A 0) : K.r ≤ s := by
  have := paga_la_informacion K hg hC A h
  simp only [zero_add, mul_one] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

/-! ## 3. La asimetría -/

/-- **El creador identidad** sobre `Fin (2^r)`: la semilla es la solución; una evaluación (`trabajo = 1`). -/
def identidad (r : ℕ) : Creador (Fin (2 ^ r)) where
  r := r
  g := id
  trabajo := 1

/-- **El creador es barato**: `r` bits de azar, una evaluación, y es inyectivo. -/
theorem creador_barato (r : ℕ) :
    (identidad r).r = r ∧ (identidad r).trabajo = 1 ∧ Function.Injective (identidad r).g :=
  ⟨rfl, rfl, Function.injective_id⟩

/-- **Resolver es caro**: todo resolvedor uniforme sin cita de la familia del creador identidad necesita
`t + 1 ≥ 2^r`. -/
theorem resolver_caro (r : ℕ) (A : Unit → ArbolV (Fin (2 ^ r)) Bool (Fin (2 ^ r))) (t : ℕ)
    (h : ResuelveFamilia (identidad r).g A t) : 2 ^ r ≤ t + 1 :=
  paga_sin_cita (identidad r) (creador_barato r).2.2 A h

/-- **Y la cota es justa salvo una consulta**: barrer todos los candidatos resuelve en `t = 2^r`. -/
theorem resolver_caro_alcanza (r : ℕ) :
    ResuelveFamilia (identidad r).g
      (fun _ : Unit => barrer (List.finRange (2 ^ r)) ⟨0, Nat.two_pow_pos r⟩) (2 ^ r) := by
  intro σ
  refine ⟨(), ?_⟩
  have := barrer_halla ((identidad r).g σ) (List.finRange (2 ^ r)) ⟨0, Nat.two_pow_pos r⟩
    (Or.inl (List.mem_finRange _))
  rwa [List.length_finRange] at this

/-- **La asimetría**: para todo `r` hay un creador que paga `r` bits de azar y una evaluación, tal que todo resolvedor
uniforme con citas de `s` bits paga `2^r ≤ 2^s · (t + 1)` (sin cita, `2^r ≤ t + 1`), mientras que con la semilla como
cita resuelve en `t = 0`. -/
theorem asimetria (r : ℕ) :
    ∃ K : Creador (Fin (2 ^ r)), K.r = r ∧ K.trabajo = 1 ∧
      (∀ (A : Unit → ArbolV (Fin (2 ^ r)) Bool (Fin (2 ^ r))) (t : ℕ), ResuelveFamilia K.g A t → 2 ^ r ≤ t + 1) ∧
      (∀ (s t : ℕ) (C : Type) [Fintype C], Fintype.card C ≤ 2 ^ s →
        ∀ A : C → ArbolV (Fin (2 ^ r)) Bool (Fin (2 ^ r)), ResuelveFamilia K.g A t → 2 ^ r ≤ 2 ^ s * (t + 1)) ∧
      ResuelveFamilia K.g (fun σ : Fin (2 ^ K.r) => .hoja (K.g σ)) 0 :=
  ⟨identidad r, rfl, rfl, resolver_caro r,
    fun _ _ _ _ hC A h => paga_la_informacion (identidad r) (creador_barato r).2.2 hC A h,
    (semilla_alcanza (identidad r)).1⟩

/-! ## 4. Lo que se conserva es información, no trabajo -/

/-- **La cota de la imagen se alcanza**: con una cita que nombra el elemento de la imagen (`|C| = |imagen g|`), se
resuelve en `t = 0`. El precio para quien resuelve es el log del tamaño de la imagen, de los dos lados. -/
theorem imagen_alcanza {r : ℕ} {Y : Type} [DecidableEq Y] (g : Fin (2 ^ r) → Y) :
    ResuelveFamilia g (fun c : {y // y ∈ (Finset.univ : Finset (Fin (2 ^ r))).image g} => .hoja c.1) 0 ∧
      Fintype.card {y // y ∈ (Finset.univ : Finset (Fin (2 ^ r))).image g} = (Finset.univ.image g).card :=
  ⟨fun σ => ⟨⟨g σ, Finset.mem_image_of_mem g (Finset.mem_univ σ)⟩, by simp [corre, pasos]⟩,
    by simp⟩

/-- **El creador constante**: `r` bits de azar y trabajo declarado `W`, pero una sola solución. -/
def constante (r W : ℕ) : Creador Unit where
  r := r
  g := fun _ => ()
  trabajo := W

/-- **Ni los bits de azar ni el trabajo encarecen nada si la imagen es chica**: para todos `r` y `W`, el creador
constante gasta `r` bits de azar y trabajo `W`, produce una sola instancia, y se resuelve sin cita en `t = 0`. -/
theorem informacion_no_trabajo (r W : ℕ) :
    (constante r W).r = r ∧ (constante r W).trabajo = W ∧ (constante r W).imagen.card = 1 ∧
      ResuelveFamilia (constante r W).g (fun _ : Unit => .hoja ()) 0 := by
  refine ⟨rfl, rfl, ?_, fun _ => ⟨(), by simp [corre, pasos, constante]⟩⟩
  have : (constante r W).imagen = {()} := by
    ext u; simp [Creador.imagen, constante]
    exact ⟨⟨0, Nat.two_pow_pos _⟩, Finset.mem_univ _⟩
  rw [this, Finset.card_singleton]

/-- **Muchos bits, imagen chica**: el caso `W = 0` de `informacion_no_trabajo`. -/
theorem muchos_bits_imagen_chica (r : ℕ) :
    (constante r 0).r = r ∧ (constante r 0).imagen.card = 1 ∧
      ResuelveFamilia (constante r 0).g (fun _ : Unit => .hoja ()) 0 :=
  let h := informacion_no_trabajo r 0; ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- **Mucho trabajo, imagen chica**: el caso `r = 0` de `informacion_no_trabajo`, con `W` arbitrario. -/
theorem mucho_trabajo_imagen_chica (W : ℕ) :
    (constante 0 W).trabajo = W ∧ (constante 0 W).imagen.card = 1 ∧
      ResuelveFamilia (constante 0 W).g (fun _ : Unit => .hoja ()) 0 :=
  let h := informacion_no_trabajo 0 W; ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- **El recorte**: `r` bits de azar, pero solo los `k` bajos llegan a la solución (`σ ↦ σ mod 2^k`). -/
def recorte (r k : ℕ) : Creador (Fin (2 ^ k)) where
  r := r
  g := fun σ => ⟨σ.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  trabajo := 1

/-- La imagen del recorte es todo `Fin (2^k)` cuando `k ≤ r`. -/
theorem recorte_imagen {r k : ℕ} (hk : k ≤ r) : (recorte r k).imagen.card = 2 ^ k := by
  have : (recorte r k).imagen = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    have hy : y.val < 2 ^ r := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right two_pos hk)
    refine Finset.mem_image.2 ⟨⟨y.val, hy⟩, Finset.mem_univ _, ?_⟩
    ext; simp [recorte, Nat.mod_eq_of_lt y.isLt]
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- **El recorte cobra `k`, no `r`**: quien resuelve sin cita paga `2^k ≤ t + 1` (la imagen), y con una cita de `k`
bits resuelve en `t = 0`; los `r − k` bits de azar de más no le cuestan nada. -/
theorem recorte_precio {r k : ℕ} (hk : k ≤ r) :
    (recorte r k).r = r ∧
      (∀ (A : Unit → ArbolV (Fin (2 ^ k)) Bool (Fin (2 ^ k))) (t : ℕ),
        ResuelveFamilia (recorte r k).g A t → 2 ^ k ≤ t + 1) ∧
      ResuelveFamilia (recorte r k).g (fun c : Fin (2 ^ k) => .hoja c) 0 := by
  refine ⟨rfl, fun A t h => ?_, fun σ => ⟨(recorte r k).g σ, by simp [corre, pasos]⟩⟩
  have := precio_es_la_imagen (s := 0) (by simp) (recorte r k).g A h
  rw [← Creador.imagen, recorte_imagen hk] at this
  simpa using this

/-! ## 5. Mutantes refutados

Cada mutante es una versión falsa de un teorema de arriba; acá se prueba que es **falso** con un contraejemplo. -/

/-- **«Quien resuelve paga el trabajo del creador»** es falso: el creador constante con trabajo `5` se resuelve en
`t = 0`, y `5 ≤ 1` no vale. -/
theorem mutante_paga_trabajo :
    ¬ ∀ (K : Creador Unit) (A : Unit → ArbolV Unit Bool Unit) (t : ℕ), ResuelveFamilia K.g A t →
      K.trabajo ≤ t + 1 := by
  intro h
  have := h (constante 0 5) _ 0 (informacion_no_trabajo 0 5).2.2.2
  simp [constante] at this

/-- **Sin la inyectividad** (`2^r ≤ t + 1` para todo creador) es falso: el creador constante con `r = 1` se resuelve en
`t = 0`, y `2 ≤ 1` no vale. -/
theorem mutante_sin_inyectiva :
    ¬ ∀ (K : Creador Unit) (A : Unit → ArbolV Unit Bool Unit) (t : ℕ), ResuelveFamilia K.g A t →
      2 ^ K.r ≤ t + 1 := by
  intro h
  have := h (constante 1 0) _ 0 (informacion_no_trabajo 1 0).2.2.2
  simp [constante] at this

/-- **Sin la cita** (`2^r ≤ t + 1` aunque haya cita de `r` bits) es falso: con la semilla como cita, `r = 1` se
resuelve en `t = 0`. -/
theorem mutante_sin_cita :
    ¬ ∀ (A : Fin (2 ^ 1) → ArbolV (Fin (2 ^ 1)) Bool (Fin (2 ^ 1))) (t : ℕ),
      ResuelveFamilia (identidad 1).g A t → 2 ^ 1 ≤ t + 1 := by
  intro h
  have := h _ 0 (semilla_alcanza (identidad 1)).1
  simp at this

/-- **«Con la semilla también hace falta tiempo»** (`1 ≤ t`) es falso, para todo `r`: la semilla resuelve en `t = 0`. -/
theorem mutante_semilla_con_tiempo (r : ℕ) :
    ¬ ∀ (A : Fin (2 ^ r) → ArbolV (Fin (2 ^ r)) Bool (Fin (2 ^ r))) (t : ℕ),
      ResuelveFamilia (identidad r).g A t → 1 ≤ t := by
  intro h
  have := h _ 0 (semilla_alcanza (identidad r)).1
  omega

/-- **Sin el `+ 1`** (`2^r ≤ t`) es falso: con `r = 0` la única instancia se resuelve en `t = 0`. -/
theorem mutante_sin_mas_uno :
    ¬ ∀ (A : Unit → ArbolV (Fin (2 ^ 0)) Bool (Fin (2 ^ 0))) (t : ℕ),
      ResuelveFamilia (identidad 0).g A t → 2 ^ 0 ≤ t := by
  intro h
  have := h (fun _ => .hoja 0) 0 fun σ => ⟨(), by
    refine ⟨?_, by simp [pasos]⟩
    apply Fin.ext
    have := σ.isLt
    simp only [identidad, pow_zero] at this
    simp [corre, identidad]⟩
  simp at this

end Sagitta.Map.Tiempo.HuevoGallina
