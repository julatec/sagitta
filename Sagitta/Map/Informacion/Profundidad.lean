import Sagitta.Map.Informacion.NoCreacion

/-!
# La profundidad computacional

La profundidad de Bennett y de
Antunes, Fortnow, van Melkebeek y Vinodchandran es `prof_t(x) = Kᵗ(x) − K(x)`: los bits que se pagan solo por
apurarse. Este archivo la escribe en los códigos de Mathlib, con la `K` y la `Kt` de `KolmogorovTiempo.lean`, y prueba
sus cuatro leyes con las constantes a la vista.

## Qué medida de tiempo

`KolmogorovTiempo` no tiene una `Kᵗ` con tope fijo `t`. Tiene la familia `Kcon g` y, en ella, la `Kt` de **Levin**
(`g = log₂`): el menor `|p| + log₂ costo`. Aquí se usa esa: `prof x := Kt x − K x` (resta de `ℕ`). Es la profundidad
«de Levin», sin tope: el tiempo no es un parámetro, se cobra en el logaritmo. Como `K ≤ Kt` vale **exacta**
(`K_le_Kt`), la resta no trunca: `prof x + K x = Kt x` (`prof_add`), con constante `0`.

## Qué se prueba

1. **La profundidad es a lo sumo el log del tiempo del programa más corto** (`prof_le_log_costo`): hay un programa
   de largo `K x` que produce `x`, y `prof x ≤ log₂ (su costo)`. Y `prof 0 = 0` (`prof_cero`).
2. **Crecimiento lento.** El enunciado natural, `prof (f x) ≤ prof x + log₂ costo + c` para toda `f` calculable,
   **no** sale de la no creación: para restar hace falta una cota inferior de `K (f x)` en términos de `K x`, y `f`
   puede borrar. Salen dos formas:
   * **Contra `K x`** (`crece_desde_K`): si `p` lleva `x` a `f x`,
     `Kt (f x) − K x ≤ prof x + (|p| + log₂ costo p x) + 3`. Es `no_creacion_Kt` menos `K x`.
   * **Con inversa calculable** (`crecimiento_lento`): si además `r` lleva `f x` de vuelta a `x`,
     `prof (f x) ≤ prof x + log₂ costo p x + (|p| + |r| + 6)`. Los `6` son dos nodos `comp`: uno para ir
     (`no_creacion_Kt`) y otro para volver (`no_creacion`). La versión con las medidas de las funciones
     (`crecimiento_lento_fun`): `prof (f x) ≤ prof x + KtEn f x + Kfun g + 6`.
   * **Borrar puede BAJAR la profundidad**, no subirla de golpe (`control_borrar_baja`): la constante `0` lleva todo
     `x` a profundidad `0`. La inversa es lo que impide bajar; nada en la no creación impide subir más que el log.
   **El matiz del modelo.** `evaln` exige que el presupuesto supere a la entrada (`evaln_bound`), así que
   `costo p x ≥ x + 1` y `log₂ costo p x ≥ log₂ (x + 1)` (`log_costo_ge`): en estos códigos **leer la entrada cuesta su
   largo en bits**. La cota de crecimiento es honesta pero floja: su término `log₂ costo` nunca baja de `≈ |x|`. Con un
   reloj de máquina que no cobre la lectura sería `log₂` del tiempo de verdad.
3. **La forma condicional.** No había `K` condicional; aquí va en el mismo estilo (`KconC`, `KC`, `KtC`), con
   «`p` lleva `y` a `x`» (`eval p y = some x`) en lugar de «`p` produce `x`». `profC x y := KtC x y − KC x y`. El mismo
   matiz: `profC x y ≥ log₂ (y + 1)` siempre (`profC_ge`), así que se descuenta la lectura:
   `profCn x y := profC x y − log₂ (y + 1)`. Con eso, un programa que lee `y` y escribe `x` con el presupuesto mínimo
   (`y + 1`) da `profCn x y ≤ |p| − 3` (`profCn_le`). **Ejemplos `O(1)`:** la identidad (`profCn_id`,
   `profCn x x ≤ 6`) y el canje de las dos mitades de `unpair` (`canje`, una permutación de `ℕ` que es su propia
   inversa): `profCn x (canje x) ≤ 6` (`profCn_canje`). Y si `r` invierte `f`, `KC x (f x) ≤ |r|` (`KC_inversa`): la
   información para invertir es `O(1)`; lo que puede ser grande es lo que cuesta en tiempo.
4. **La tasa.** `ley` de `KolmogorovTiempo`: un programa `p` que produce `x` en `t` pasos da `Kt x ≤ |p| + log₂ t`.
   Por lo tanto (`tasa`), si `prof x ≥ d`, `2^(d + K x) ≤ 2^|p| · t`; y (`tasa_desde_corta`), con `c = |p| − 3`,
   `t ≥ 2^(d − c)`: **alcanzar `d` bits de profundidad desde una descripción de `c + 3` bits pide `2^(d − c)` pasos.**
   Aquí la entrada es `0`, así que el matiz de la lectura no entra.

## Lo que NO se prueba

* Que la profundidad sea **positiva** para algún `x` concreto, ni que no esté acotada: haría falta una cota inferior de
  `Kt` para todos los programas cortos, que `KolmogorovTiempo` tampoco tiene. Por eso el enunciado natural sin inversa
  no se refuta aquí: no hay un `x` profundo para usar de testigo.
* La profundidad con tope `t` fijo (`Kᵗ`), la de una permutación de un solo sentido (que exige funciones de un solo
  sentido) y la invariancia entre modelos: todo es relativo a los códigos de Mathlib y a `bits`.
* Nada sobre P contra NP.

## Fuentes

* C. H. Bennett, «Logical depth and physical complexity», en R. Herken (ed.), *The Universal Turing Machine: A
  Half-Century Survey*, Oxford University Press, 1988, pp. 227–257 (de memoria; no leído).
* L. Antunes, L. Fortnow, D. van Melkebeek y N. V. Vinodchandran, «Computational depth: concept and applications»,
  *Theoretical Computer Science* 354(3):391–404, 2006 (de memoria; no leído). Las pruebas de aquí son propias.
-/

namespace Sagitta.Map.Informacion.Profundidad

open Nat.Partrec Nat.Partrec.Code
open Sagitta.Map.Tiempo.KolmogorovTiempo Sagitta.Map.Tiempo.AceleracionBlum
open Sagitta.Map.Informacion.NoCreacion

/-! ## 0. El costo: cotas por arriba y por abajo -/

/-- **Leer la entrada cuesta**: el presupuesto de `evaln` supera a la entrada. -/
theorem costo_ge {c : Code} {n v : ℕ} (h : eval c n = Part.some v) : n + 1 ≤ costo c n := by
  have := evaln_bound (show v ∈ evaln (costo c n) c n from evaln_costo h)
  omega

/-- Si `evaln k c n` termina, el costo es a lo sumo `k`. -/
theorem costo_le {c : Code} {n v k : ℕ} (h : eval c n = Part.some v) (hk : (evaln k c n).isSome) :
    costo c n ≤ k := by
  have hd : (eval c n).Dom := by rw [h]; trivial
  have hp : pasos c n = costo c n :=
    (ENat.natCast_toNat (ne_of_lt ((pasos_lt_top_iff c n).2 hd))).symm
  have := (pasos_le_iff c n k).2 hk
  rw [hp] at this
  exact_mod_cast this

/-- **El matiz del modelo**: `log₂ (x + 1) ≤ log₂ costo p x`. En los códigos de Mathlib leer `x` cuesta su largo. -/
theorem log_costo_ge {p : Code} {x v : ℕ} (h : eval p x = Part.some v) :
    Nat.log 2 (x + 1) ≤ Nat.log 2 (costo p x) :=
  Nat.log_mono_right (costo_ge h)

/-! ## 1. La profundidad -/

/-- **La profundidad de Levin**: `Kt x − K x`, los bits que se pagan por apurarse. -/
noncomputable def prof (x : ℕ) : ℕ := Kt x - K x

/-- **No es negativa, y la resta no trunca**: `prof x + K x = Kt x`, con constante `0`. -/
theorem prof_add (x : ℕ) : prof x + K x = Kt x := by
  have := K_le_Kt x
  unfold prof
  omega

/-- **La profundidad es a lo sumo el log del tiempo del programa más corto.** -/
theorem prof_le_log_costo (x : ℕ) : ∃ p, Produce p x ∧ largo p = K x ∧ prof x ≤ Nat.log 2 (costo p 0) := by
  obtain ⟨p, hp, hl⟩ := K_spec x
  refine ⟨p, hp, hl, ?_⟩
  have := Kcon_le (g := Nat.log 2) hp
  have := prof_add x
  simp only [Kt] at *
  omega

/-- `0` no tiene profundidad. -/
theorem prof_cero : prof 0 = 0 := by
  have := K_cero
  unfold prof
  omega

/-- **Cota superior**: `prof x ≤ 24 · |x| + 6`. -/
theorem prof_le_size (x : ℕ) : prof x ≤ 24 * Nat.size x + 6 := by
  have := Kt_cota_superior x
  have := K_ge x
  unfold prof
  omega

/-! ## 2. El crecimiento lento -/

/-- **Crecimiento contra `K x`**: si `p` lleva `x` a `f x`,
`Kt (f x) − K x ≤ prof x + (|p| + log₂ costo p x) + 3`. Es `no_creacion_Kt` restándole `K x`. -/
theorem crece_desde_K {p : Code} {f : ℕ → ℕ} {x : ℕ} (hp : eval p x = Part.some (f x)) :
    Kt (f x) - K x ≤ prof x + (largo p + Nat.log 2 (costo p x)) + 3 := by
  have := no_creacion_Kt hp
  have := prof_add x
  omega

/-- **El crecimiento lento, con inversa.** Si `p` lleva `x` a `f x` y `r` lleva `f x` de vuelta a `x`,
`prof (f x) ≤ prof x + log₂ costo p x + (|p| + |r| + 6)`. Los `6` son los dos nodos `comp`, el de ida y el de
vuelta. Sin la inversa no hay con qué acotar `K (f x)` por abajo: borrar puede **bajar** la profundidad
(`control_borrar_baja`); lo que la ley impide es subirla de golpe. -/
theorem crecimiento_lento {p r : Code} {f : ℕ → ℕ} {x : ℕ} (hp : eval p x = Part.some (f x))
    (hr : eval r (f x) = Part.some x) :
    prof (f x) ≤ prof x + Nat.log 2 (costo p x) + (largo p + largo r + 6) := by
  have h1 := no_creacion_Kt hp
  have h2 : K x ≤ K (f x) + largo r + 3 := no_creacion (f := fun _ => x) (x := f x) hr
  have := prof_add x
  have := prof_add (f x)
  omega

/-- **El crecimiento lento con las medidas de las funciones**: si `g` deshace `f`,
`prof (f x) ≤ prof x + KtEn f x + Kfun g + 6`. `KtEn f x` es el menor `|p| + log₂ costo p x`. -/
theorem crecimiento_lento_fun {f g : ℕ → ℕ} (hf : ∃ p, Computa p f) (hg : ∃ r, Computa r g)
    (hgf : ∀ x, g (f x) = x) (x : ℕ) : prof (f x) ≤ prof x + KtEn f x + Kfun g + 6 := by
  have h1 := no_creacion_Kt' hf x
  have h2 := no_creacion_K hg (f x)
  rw [hgf] at h2
  have := prof_add x
  have := prof_add (f x)
  omega

/-- **Control: borrar baja la profundidad.** La constante `0` lleva todo `x` a profundidad `0`, y sus programas son
de tres bits: la cota de `crecimiento_lento` vale sin la inversa en este sentido, el de bajar. -/
theorem control_borrar_baja (x : ℕ) : prof ((fun _ => 0) x) = 0 ∧ prof ((fun _ => 0) x) ≤ prof x := by
  refine ⟨prof_cero, ?_⟩
  change prof 0 ≤ prof x
  rw [prof_cero]
  exact Nat.zero_le _

/-! ## 3. La forma condicional -/

/-- Todo `x` tiene un programa que lo saca de cualquier `y`: su árbol, que ignora la entrada. -/
theorem existe_cotaC (g : ℕ → ℕ) (x y : ℕ) : ∃ m, ∃ p, eval p y = Part.some x ∧ largo p + g (costo p y) ≤ m :=
  ⟨_, arbol x, eval_arbol x y, le_rfl⟩

open Classical in
/-- **La medida condicional**: el menor `largo p + g (costo p y)` sobre los `p` que llevan `y` a `x`. -/
noncomputable def KconC (g : ℕ → ℕ) (x y : ℕ) : ℕ := Nat.find (existe_cotaC g x y)

/-- **`K (x | y)`**. -/
noncomputable def KC (x y : ℕ) : ℕ := KconC (fun _ => 0) x y

/-- **`Kt (x | y)`**, con el precio de Levin. -/
noncomputable def KtC (x y : ℕ) : ℕ := KconC (Nat.log 2) x y

theorem KconC_le {g : ℕ → ℕ} {p : Code} {x y : ℕ} (h : eval p y = Part.some x) :
    KconC g x y ≤ largo p + g (costo p y) := by
  classical
  exact Nat.find_min' (existe_cotaC g x y) ⟨p, h, le_rfl⟩

theorem KconC_spec (g : ℕ → ℕ) (x y : ℕ) :
    ∃ p, eval p y = Part.some x ∧ largo p + g (costo p y) = KconC g x y := by
  classical
  obtain ⟨p, hp, hle⟩ := Nat.find_spec (existe_cotaC g x y)
  exact ⟨p, hp, le_antisymm hle (KconC_le hp)⟩

theorem KC_le {p : Code} {x y : ℕ} (h : eval p y = Part.some x) : KC x y ≤ largo p := by
  simpa [KC] using KconC_le (g := fun _ => 0) h

theorem KC_ge (x y : ℕ) : 3 ≤ KC x y := by
  obtain ⟨p, -, he⟩ := KconC_spec (fun _ => 0) x y
  have := largo_ge p
  simp only [KC] at *
  omega

/-- **`K (x | y) + log₂ (y + 1) ≤ Kt (x | y)`**: el tiempo condicional paga siempre la lectura de `y`. -/
theorem KC_add_log_le_KtC (x y : ℕ) : KC x y + Nat.log 2 (y + 1) ≤ KtC x y := by
  obtain ⟨p, hp, he⟩ := KconC_spec (Nat.log 2) x y
  have := KC_le hp
  have := log_costo_ge hp
  simp only [KtC] at *
  omega

/-- **La profundidad condicional**: `Kt (x | y) − K (x | y)`. -/
noncomputable def profC (x y : ℕ) : ℕ := KtC x y - KC x y

/-- **El piso de la lectura**: `profC x y ≥ log₂ (y + 1)`, para todo `x`. -/
theorem profC_ge (x y : ℕ) : Nat.log 2 (y + 1) ≤ profC x y := by
  have := KC_add_log_le_KtC x y
  unfold profC
  omega

/-- **La profundidad condicional sin la lectura**: `profC x y − log₂ (y + 1)`. -/
noncomputable def profCn (x y : ℕ) : ℕ := profC x y - Nat.log 2 (y + 1)

/-- **Un programa que lee `y` y escribe `x` con el presupuesto mínimo** da `profCn x y ≤ |p| − 3`. -/
theorem profCn_le {p : Code} {x y : ℕ} (h : eval p y = Part.some x) (hk : (evaln (y + 1) p y).isSome) :
    profCn x y ≤ largo p - 3 := by
  have h1 := KconC_le (g := Nat.log 2) h
  have h2 := Nat.log_mono_right (b := 2) (costo_le h hk)
  have h3 := KC_ge x y
  have h4 := KC_add_log_le_KtC x y
  simp only [profCn, profC, KtC] at *
  omega

/-- **Invertir con un programa `r`**: `K (x | f x) ≤ |r|`. La información para volver es `O(1)`. -/
theorem KC_inversa {r : Code} {f : ℕ → ℕ} {x : ℕ} (hr : eval r (f x) = Part.some x) : KC x (f x) ≤ largo r :=
  KC_le hr

theorem largo_id : largo Code.id = 9 := by
  simp [largo, bits, Code.id]

theorem evaln_id (y : ℕ) : (evaln (y + 1) Code.id y).isSome := by
  simp [evaln, Code.id, Seq.seq]

/-- **Ejemplo `O(1)`: la identidad.** `profCn x x ≤ 6`. -/
theorem profCn_id (x : ℕ) : profCn x x ≤ 6 := by
  have := profCn_le (eval_id x) (evaln_id x)
  rw [largo_id] at this
  omega

/-- **El canje**: intercambia las dos mitades de `unpair`. -/
def canje (x : ℕ) : ℕ := Nat.pair x.unpair.2 x.unpair.1

/-- El código del canje: `pair right left`. -/
def codCanje : Code := .pair .right .left

theorem eval_codCanje (x : ℕ) : eval codCanje x = Part.some (canje x) := by
  simp [codCanje, canje, Code.eval, Seq.seq]

theorem canje_canje (x : ℕ) : canje (canje x) = x := by
  simp [canje]

/-- **El canje es una permutación de `ℕ`**: su propia inversa. -/
def canjeEquiv : ℕ ≃ ℕ := ⟨canje, canje, canje_canje, canje_canje⟩

theorem largo_codCanje : largo codCanje = 9 := by
  simp [largo, bits, codCanje]

theorem evaln_codCanje (y : ℕ) : (evaln (y + 1) codCanje y).isSome := by
  simp [evaln, codCanje, Seq.seq]

/-- **Ejemplo `O(1)`: una permutación fácil de invertir.** `profCn x (canje x) ≤ 6`: para volver de `canje x` a `x`
basta el mismo canje, de nueve bits, que corre con el presupuesto mínimo. -/
theorem profCn_canje (x : ℕ) : profCn x (canje x) ≤ 6 := by
  have h : eval codCanje (canje x) = Part.some x := by rw [eval_codCanje, canje_canje]
  have := profCn_le h (evaln_codCanje (canje x))
  rw [largo_codCanje] at this
  omega

/-! ## 4. La tasa -/

/-- **La tasa.** Si `p` produce `x` en `t` pasos y `x` tiene profundidad al menos `d`,
`2^(d + K x) ≤ 2^|p| · t`. Es `ley` con `Kt = prof + K`. -/
theorem tasa {p : Code} {x t d : ℕ} (hp : Produce p x) (ht : (evaln t p 0).isSome) (hd : d ≤ prof x) :
    2 ^ (d + K x) ≤ 2 ^ largo p * t := by
  have h1 := ley hp ht
  have h2 := prof_add x
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp [evaln] at ht
  calc 2 ^ (d + K x) ≤ 2 ^ (largo p + Nat.log 2 t) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ largo p * 2 ^ Nat.log 2 t := pow_add _ _ _
    _ ≤ 2 ^ largo p * t := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 ht0)

/-- **Alcanzar `d` bits de profundidad desde una descripción corta pide `2^(d − c)` pasos**, con `c = |p| − 3`. -/
theorem tasa_desde_corta {p : Code} {x t d : ℕ} (hp : Produce p x) (ht : (evaln t p 0).isSome)
    (hd : d ≤ prof x) : 2 ^ (d - (largo p - 3)) ≤ t := by
  have h := tasa hp ht hd
  have hK := K_ge x
  have hl := largo_ge p
  have hpos : 0 < 2 ^ largo p := by positivity
  have he : d - (largo p - 3) + largo p ≤ d + K x ∨ d - (largo p - 3) = 0 := by omega
  rcases he with he | he
  · apply Nat.le_of_mul_le_mul_left _ hpos
    calc 2 ^ largo p * 2 ^ (d - (largo p - 3)) = 2 ^ (d - (largo p - 3) + largo p) := by
          rw [← pow_add, Nat.add_comm]
      _ ≤ 2 ^ (d + K x) := Nat.pow_le_pow_right (by norm_num) he
      _ ≤ 2 ^ largo p * t := h
  · rw [he, pow_zero]
    rcases Nat.eq_zero_or_pos t with rfl | h0
    · simp [evaln] at ht
    · exact h0

end Sagitta.Map.Informacion.Profundidad
