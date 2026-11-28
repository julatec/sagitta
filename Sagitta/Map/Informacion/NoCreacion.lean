import Sagitta.Map.KolmogorovTiempo
import Sagitta.Map.Informacion.Tiempo

/-!
# La ley de no creación

La conservación de Levin se escribe en su forma simple, `K(f x) ≤ K x + K f + O(1)`:
calcular no crea bits, los vuelve visibles. Este archivo la prueba donde se puede probar entera y dice qué falta en el
modelo de máquinas de cslib.

## Dos modelos, dos respuestas

* **Los códigos de Mathlib** (§ 1–3), con la `K` y la `Kt` que ya están en `KolmogorovTiempo.lean` (largo en bits,
  libre de prefijos, tres bits por nodo). Ahí la composición es un constructor: `Code.comp p q`, y su largo es
  `largo p + largo q + 3` (`largo_comp`). La ley sale **exacta, con `c = 3`**:
  `K (f x) ≤ K x + K f + 3` (`no_creacion`, `no_creacion_K`). Con tiempo, `costo_comp_le`: el presupuesto de `evaln`
  de la composición es a lo sumo el **máximo** de los dos, no la suma; y `no_creacion_Kt`:
  `Kt (f x) ≤ Kt x + (|p| + log₂ costo p x) + 3`. Que el tiempo se componga por máximo es un rasgo de `evaln`, que no
  es tiempo de máquina (`RondasAcotadas.evaln_no_acotado`); con una suma se pagaría un bit más (`clog_suma_le`).
* **Las máquinas de cslib** (§ 4–5), con `maquina`, `indiceDe` y `correrMT` de `LevinMaquinas.lean`. `Kmt x` es el
  menor índice de máquina que imprime `x` desde la cinta vacía, y `Ktmt x` el menor `i + ⌈log₂ t⌉`; las dos están bien
  definidas (`existe_impresora`, por la máquina constante de cslib). La composición de máquinas **no** está a nivel
  de descripciones: cslib-frontier compone `MultiTapeTM` (`MultiTapeTM.comp` de `KernelComp`, con
  `ComputableInBigO.comp`/`ComputableInO.comp` en tiempo `T₁ a + T₂ (g a)` salvo constantes, y
  `MultiTapeMachine.seq`, que suma las cotas de parada), pero no hay una `Desc` compuesta ni una cota del índice de
  `desc` de una máquina compuesta. Por eso aquí la ley es **condicional** a un compositor de índices (`Compositor`):
  `Kmt (f x) ≤ g (Kmt x) j` y `Ktmt (f x) ≤ g i j + clog t + clog s + clog c + 2` (`no_creacion_mt`,
  `no_creacion_ktmt`).
* **La cota que da el índice, y por qué no es aditiva** (§ 5). El número de una palabra en la codificación de Mathlib
  anida `Nat.pair`, que eleva al cuadrado en cada símbolo: una palabra de largo `n + 2` tiene número
  `≥ 2^(2^n)` (`dos_pow_dos_pow_le_encode`). Al revés, `|palabra i| ≤ log₂ log₂ i + 2` (`largo_palabra_loglog`).
  Así que el log del índice mide `≈ 2^|palabra|`: una composición que concatene descripciones, aditiva en el largo de
  la palabra, es **multiplicativa** en el log del índice. La forma aditiva «en bits» de la ley es en el largo de la
  palabra (como en § 1), no en `log₂` del índice.

## El control

La ley es una desigualdad. `control_borra`: la función constante `0` tiene un programa de `3` bits, y para todo `n`
hay `x < 2^n` con `K x ≥ n` y `K (0) = 3`; la brecha `K x − K (f x)` no está acotada (`no_es_igualdad`). Lo mismo
con `Kt`. En máquinas, `control_borra_mt`: `Kmt` de la imagen de una constante no depende de `x`, y `Kmt x` no está
acotada (`Kmt_no_acotada`, porque `Kmt` es inyectiva).

## Lo que NO se prueba

* La ley en el modelo de máquinas sin la hipótesis `Compositor`: falta construir la `Desc` compuesta (correr la
  primera, copiar su salida a una cinta, correr la segunda leyendo esa cinta como entrada) y acotar su número.
* La invariancia: todo es relativo a cada modelo; la constante `3` es la de `Code.comp` en `bits`.
* Nada sobre P contra NP.
-/

namespace Sagitta.Map.Informacion.NoCreacion

open Nat.Partrec Nat.Partrec.Code
open Sagitta.Map.Tiempo.KolmogorovTiempo Sagitta.Map.Tiempo.AceleracionBlum

/-! ## 1. La composición de códigos -/

/-- **Componer cuesta tres bits**: el nodo `comp` y los dos árboles. -/
theorem largo_comp (p q : Code) : largo (.comp p q) = largo p + largo q + 3 := by
  simp only [largo, bits, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Si `q` produce `x` y `p` lleva `x` a `y`, `comp p q` produce `y`. -/
theorem produce_comp {p q : Code} {x y : ℕ} (hq : Produce q x) (hp : eval p x = Part.some y) :
    Produce (.comp p q) y := by
  unfold Produce at *
  simp only [Code.eval, hq]
  exact (Part.bind_some x _).trans hp

/-! ## 2. La ley sin tiempo -/

/-- **La ley de no creación, con un programa dado.** Si `p` lleva `x` a `f x`, entonces
`K (f x) ≤ K x + |p| + 3`. -/
theorem no_creacion {p : Code} {f : ℕ → ℕ} {x : ℕ} (hp : eval p x = Part.some (f x)) :
    K (f x) ≤ K x + largo p + 3 := by
  obtain ⟨q, hq, hl⟩ := K_spec x
  have := K_le (produce_comp hq hp)
  rw [largo_comp] at this
  omega

open Classical in
/-- **`K` de una función total**: el menor largo de un código que la calcula (`0` si no es calculable). -/
noncomputable def Kfun (f : ℕ → ℕ) : ℕ :=
  if h : ∃ m, ∃ p, Computa p f ∧ largo p = m then Nat.find h else 0

theorem Kfun_spec {f : ℕ → ℕ} (h : ∃ p, Computa p f) : ∃ p, Computa p f ∧ largo p = Kfun f := by
  classical
  have h' : ∃ m, ∃ p, Computa p f ∧ largo p = m := let ⟨p, hp⟩ := h; ⟨_, p, hp, rfl⟩
  unfold Kfun
  rw [dif_pos h']
  exact Nat.find_spec h'

/-- **La ley de no creación**: `K (f x) ≤ K x + K f + 3`, para toda `f` calculable y todo `x`. La constante es la del
nodo `comp`. -/
theorem no_creacion_K {f : ℕ → ℕ} (h : ∃ p, Computa p f) (x : ℕ) : K (f x) ≤ K x + Kfun f + 3 := by
  obtain ⟨p, hp, hl⟩ := Kfun_spec h
  have := no_creacion (hp x)
  omega

/-! ## 3. La ley con tiempo -/

/-- Lo que `evaln` devuelve con presupuesto `costo`. -/
theorem evaln_costo {c : Code} {n v : ℕ} (h : eval c n = Part.some v) : evaln (costo c n) c n = some v := by
  have hd : (eval c n).Dom := by rw [h]; trivial
  have hp : pasos c n = costo c n :=
    (ENat.natCast_toNat (ne_of_lt ((pasos_lt_top_iff c n).2 hd))).symm
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((pasos_le_iff c n (costo c n)).1 (le_of_eq hp))
  have hm := evaln_sound hw
  rw [h, Part.mem_some_iff] at hm
  rw [hw, hm]

/-- El costo es al menos uno: `evaln 0` no termina. -/
theorem uno_le_costo {c : Code} {n v : ℕ} (h : eval c n = Part.some v) : 1 ≤ costo c n := by
  have := evaln_costo h
  rcases hk : costo c n with _ | k
  · rw [hk] at this; simp [evaln] at this
  · omega

/-- **El costo de componer, en `evaln`, es el máximo**: con el presupuesto mayor de los dos corren las dos partes. -/
theorem costo_comp_le {p q : Code} {x y : ℕ} (hq : Produce q x) (hp : eval p x = Part.some y) :
    costo (.comp p q) 0 ≤ max (costo q 0) (costo p x) := by
  have h1 := evaln_costo hq
  have h2 := evaln_costo hp
  have hu := uno_le_costo hq
  obtain ⟨k, hk⟩ : ∃ k, max (costo q 0) (costo p x) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  have e1 : evaln (k + 1) q 0 = some x := evaln_mono (hk ▸ le_max_left _ _) h1
  have e2 : evaln (k + 1) p x = some y := evaln_mono (hk ▸ le_max_right _ _) h2
  have hs : (evaln (k + 1) (.comp p q) 0).isSome := by
    simp [evaln, e1, e2]
  have hc := (pasos_le_iff _ _ _).2 hs
  rw [pasos_de_produce (produce_comp hq hp)] at hc
  rw [hk]
  exact_mod_cast hc

/-- `log₂` del máximo es a lo sumo la suma de los `log₂`. -/
theorem log_max_le (a b : ℕ) : Nat.log 2 (max a b) ≤ Nat.log 2 a + Nat.log 2 b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-- **La ley de no creación con tiempo, con un programa dado.** Si `p` lleva `x` a `f x` con costo `costo p x`,
`Kt (f x) ≤ Kt x + (|p| + log₂ (costo p x)) + 3`. -/
theorem no_creacion_Kt {p : Code} {f : ℕ → ℕ} {x : ℕ} (hp : eval p x = Part.some (f x)) :
    Kt (f x) ≤ Kt x + (largo p + Nat.log 2 (costo p x)) + 3 := by
  obtain ⟨q, hq, hl⟩ := Kcon_spec (Nat.log 2) x
  have h1 := Kcon_le (g := Nat.log 2) (produce_comp hq hp)
  have h2 := Nat.log_mono_right (b := 2) (costo_comp_le hq hp)
  have h3 := log_max_le (costo q 0) (costo p x)
  rw [largo_comp] at h1
  simp only [Kt] at hl ⊢
  omega

open Classical in
/-- **El costo `Kt` de calcular `f` en `x`**: el menor `|p| + log₂ (costo p x)` sobre los códigos que calculan `f`. -/
noncomputable def KtEn (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  if h : ∃ m, ∃ p, Computa p f ∧ largo p + Nat.log 2 (costo p x) = m then Nat.find h else 0

/-- **La ley con tiempo**: `Kt (f x) ≤ Kt x + KtEn f x + 3`. -/
theorem no_creacion_Kt' {f : ℕ → ℕ} (h : ∃ p, Computa p f) (x : ℕ) : Kt (f x) ≤ Kt x + KtEn f x + 3 := by
  classical
  have h' : ∃ m, ∃ p, Computa p f ∧ largo p + Nat.log 2 (costo p x) = m :=
    let ⟨p, hp⟩ := h; ⟨_, p, hp, rfl⟩
  obtain ⟨p, hp, hm⟩ := Nat.find_spec h'
  have := no_creacion_Kt (hp x)
  unfold KtEn
  rw [dif_pos h']
  omega

/-- Si el tiempo se compusiera por suma, se pagaría un bit: `⌈log₂ (a + b)⌉ ≤ ⌈log₂ a⌉ + ⌈log₂ b⌉ + 1`. -/
theorem clog_suma_le (a b : ℕ) : Nat.clog 2 (a + b) ≤ Nat.clog 2 a + Nat.clog 2 b + 1 := by
  apply Nat.clog_le_of_le_pow
  have ha := Nat.le_pow_clog one_lt_two a
  have hb := Nat.le_pow_clog one_lt_two b
  have h1 : 2 ^ Nat.clog 2 a ≤ 2 ^ (Nat.clog 2 a + Nat.clog 2 b) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ Nat.clog 2 b ≤ 2 ^ (Nat.clog 2 a + Nat.clog 2 b) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_succ]
  omega

/-! ## Controles en los códigos: la ley no es una igualdad -/

/-- El código `zero` calcula la constante `0`. -/
theorem computa_cero : Computa Code.zero (fun _ => 0) := fun n => eval_const 0 n

/-- **Control: borrar.** La constante `0` tiene un programa de tres bits, y para todo `n` hay un `x < 2^n` con
`K x ≥ n` cuya imagen tiene `K = 3`. La ley se cumple con holgura `n`. -/
theorem control_borra (n : ℕ) : ∃ x < 2 ^ n, n ≤ K x ∧ K ((fun _ => 0) x) = 3 ∧ Kfun (fun _ => 0) ≤ 3 := by
  obtain ⟨x, hx, hn⟩ := incompresible_K n
  refine ⟨x, hx, hn, K_cero.1, ?_⟩
  obtain ⟨p, -, hl⟩ := Kfun_spec ⟨_, computa_cero⟩
  have : Kfun (fun _ => 0) ≤ largo Code.zero := by
    classical
    unfold Kfun
    rw [dif_pos ⟨_, _, computa_cero, rfl⟩]
    exact Nat.find_min' _ ⟨_, computa_cero, rfl⟩
  simpa [largo, bits] using this

/-- **La ley no es una igualdad**: no vale `K (f x) = K x + K f + 3` para toda `f` y todo `x`. -/
theorem no_es_igualdad : ¬ ∀ (f : ℕ → ℕ), (∃ p, Computa p f) → ∀ x, K (f x) = K x + Kfun f + 3 := by
  intro h
  obtain ⟨x, -, hn, h0, -⟩ := control_borra 1
  have := h _ ⟨_, computa_cero⟩ x
  simp only at this h0
  omega

/-- **Control con tiempo**: la imagen de la constante tiene `Kt = 3`, y hay `x` con `Kt x ≥ n`. -/
theorem control_borra_Kt (n : ℕ) : ∃ x < 2 ^ n, n ≤ Kt x ∧ Kt ((fun _ => 0) x) = 3 := by
  obtain ⟨x, hx, hn⟩ := incompresible_Kt n
  exact ⟨x, hx, hn, K_cero.2⟩

/-! ## 4. Las máquinas de cslib -/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Sagitta.Map.Tiempo.LevinMaquinas

/-- La máquina `i` imprime `x` desde la cinta vacía con reloj `t`. -/
def ImprimeMT (i : ℕ) (x : List Bool) (t : ℕ) : Prop := correrMT i [] t = some x

/-- **Toda palabra tiene una máquina que la imprime**: la máquina constante de cslib, por su número. -/
theorem existe_impresora (x : List Bool) : ∃ i t, ImprimeMT i x t := by
  obtain ⟨c, k, S, hfin, tm, htm⟩ :=
    computableInTimeAndSpace_of_const (α := List Bool) (encIn := encBits) (encOut := encBits) x
  have := Fintype.ofFinite S
  let eS : S ↪ ℕ := (Fintype.equivFin S).toEmbedding.trans Fin.valEmbedding
  obtain ⟨hh, ho⟩ := parado_de_computes (htm []) le_rfl
  refine ⟨indiceDe (desc eS eBit tm), c, ?_⟩
  unfold ImprimeMT
  change correrMT _ (encBits ([] : List Bool)) ((fun _ : List Bool => c) []) = _
  rw [correrMT_de_maquina eS tm hh, ho]
  rfl

open Classical in
/-- **`K` en máquinas**: el menor índice de una máquina que imprime `x`. -/
noncomputable def Kmt (x : List Bool) : ℕ := Nat.find (p := fun i => ∃ t, ImprimeMT i x t) (existe_impresora x)

theorem existe_cota_mt (x : List Bool) : ∃ m, ∃ i t, ImprimeMT i x t ∧ i + Nat.clog 2 t ≤ m :=
  let ⟨i, t, h⟩ := existe_impresora x; ⟨_, i, t, h, le_rfl⟩

open Classical in
/-- **`Kt` en máquinas**: el menor `i + ⌈log₂ t⌉` sobre las máquinas `i` que imprimen `x` en `t` pasos. Es la medida
de `ktMT` con «imprimir desde la cinta vacía» en lugar de «resolver». -/
noncomputable def Ktmt (x : List Bool) : ℕ := Nat.find (existe_cota_mt x)

theorem Kmt_le {i t : ℕ} {x : List Bool} (h : ImprimeMT i x t) : Kmt x ≤ i := by
  classical
  exact Nat.find_min' _ ⟨t, h⟩

theorem Kmt_spec (x : List Bool) : ∃ t, ImprimeMT (Kmt x) x t := by
  classical
  exact Nat.find_spec (p := fun i => ∃ t, ImprimeMT i x t) (existe_impresora x)

theorem Ktmt_le {i t : ℕ} {x : List Bool} (h : ImprimeMT i x t) : Ktmt x ≤ i + Nat.clog 2 t := by
  classical
  exact Nat.find_min' _ ⟨i, t, h, le_rfl⟩

theorem Ktmt_spec (x : List Bool) : ∃ i t, ImprimeMT i x t ∧ i + Nat.clog 2 t = Ktmt x := by
  classical
  obtain ⟨i, t, h, hle⟩ := Nat.find_spec (existe_cota_mt x)
  exact ⟨i, t, h, le_antisymm hle (Ktmt_le h)⟩

/-- **Un compositor de índices**: `g i j` imprime lo que la máquina `j` saca de lo que la máquina `i` imprime, en la
suma de los relojes más `c`. Es lo que daría una `Desc` compuesta con un número acotado; cslib-frontier compone
`MultiTapeTM` (tiempos que se suman salvo constantes), no descripciones. -/
def Compositor (g : ℕ → ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ i j t s (x y : List Bool), correrMT i [] t = some x → correrMT j x s = some y →
    correrMT (g i j) [] (t + s + c) = some y

/-- **La ley en máquinas, condicional al compositor.** Si `g` es monótono en el primer índice y la máquina `j` lleva
`x` a `f x`, `Kmt (f x) ≤ g (Kmt x) j`. -/
theorem no_creacion_mt {g : ℕ → ℕ → ℕ} {c : ℕ} (hg : Compositor g c) {f : List Bool → List Bool}
    {j s : ℕ} {x : List Bool} (hj : correrMT j x s = some (f x)) : Kmt (f x) ≤ g (Kmt x) j := by
  obtain ⟨t, ht⟩ := Kmt_spec x
  exact Kmt_le (hg _ _ _ _ _ _ ht hj)

/-- `⌈log₂ (t + s + c)⌉ ≤ ⌈log₂ t⌉ + ⌈log₂ s⌉ + ⌈log₂ c⌉ + 2`. -/
theorem clog_suma3_le (t s c : ℕ) :
    Nat.clog 2 (t + s + c) ≤ Nat.clog 2 t + Nat.clog 2 s + Nat.clog 2 c + 2 := by
  have h1 := clog_suma_le (t + s) c
  have h2 := clog_suma_le t s
  omega

/-- **La ley con tiempo en máquinas, condicional al compositor.** Con la máquina `i` que realiza `Ktmt x` (reloj
`t`) y la máquina `j` que lleva `x` a `f x` con reloj `s`: los tiempos se suman y se paga en bits su `clog`. -/
theorem no_creacion_ktmt {g : ℕ → ℕ → ℕ} {c : ℕ} (hg : Compositor g c) {f : List Bool → List Bool}
    {j s : ℕ} {x : List Bool} (hj : correrMT j x s = some (f x)) :
    ∃ i t, ImprimeMT i x t ∧ i + Nat.clog 2 t = Ktmt x ∧
      Ktmt (f x) ≤ g i j + Nat.clog 2 t + Nat.clog 2 s + Nat.clog 2 c + 2 := by
  obtain ⟨i, t, ht, he⟩ := Ktmt_spec x
  refine ⟨i, t, ht, he, ?_⟩
  have := Ktmt_le (hg _ _ _ _ _ _ ht hj)
  have := clog_suma3_le t s c
  omega

/-- Una máquina imprime a lo sumo una palabra. -/
theorem imprime_unica {i t t' : ℕ} {x y : List Bool} (hx : ImprimeMT i x t) (hy : ImprimeMT i y t') : x = y := by
  have h1 := correrMT_mono hx (le_max_left t t')
  have h2 := correrMT_mono hy (le_max_right t t')
  rw [h1] at h2
  exact Option.some_injective _ h2

/-- `Kmt` es inyectiva: el índice mínimo determina la palabra. -/
theorem Kmt_inj {x y : List Bool} (h : Kmt x = Kmt y) : x = y := by
  obtain ⟨t, ht⟩ := Kmt_spec x
  obtain ⟨t', ht'⟩ := Kmt_spec y
  rw [h] at ht
  exact imprime_unica ht ht'

/-- **`Kmt` no está acotada**: para todo `n` hay una palabra con `Kmt ≥ n` (palomar sobre `true^k`, `k ≤ n`). -/
theorem Kmt_no_acotada (n : ℕ) : ∃ x, n ≤ Kmt x := by
  by_contra hc
  push Not at hc
  let F : Fin (n + 1) → Fin n := fun k => ⟨Kmt (List.replicate k true), hc _⟩
  have hF : Function.Injective F := by
    intro a b hab
    have := Kmt_inj (congrArg Fin.val hab)
    have := congrArg List.length this
    simp only [List.length_replicate] at this
    exact Fin.ext this
  have := Fintype.card_le_of_injective F hF
  simp at this

/-- **Control en máquinas: borrar.** Si `f` es la constante `w`, `Kmt (f x) = Kmt w` para todo `x`, mientras que
`Kmt x` toma valores tan grandes como se quiera. -/
theorem control_borra_mt (w : List Bool) (n : ℕ) : ∃ x, n + Kmt w ≤ Kmt x ∧ Kmt ((fun _ => w) x) = Kmt w :=
  let ⟨x, hx⟩ := Kmt_no_acotada (n + Kmt w); ⟨x, hx, rfl⟩

/-! ## 5. El índice crece doblemente exponencial con el largo de la palabra -/

/-- `b² ≤ pair a b`. -/
theorem mul_self_le_pair (a b : ℕ) : b * b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · omega
  · push Not at h
    nlinarith

/-- Cada símbolo eleva al cuadrado: `encode (a :: l) ≥ (encode l)² + 1`. -/
theorem encode_cons_ge (a : Bool) (l : List Bool) :
    Encodable.encode l * Encodable.encode l + 1 ≤ Encodable.encode (a :: l) := by
  rw [Encodable.encode_list_cons]
  have := mul_self_le_pair (Encodable.encode a) (Encodable.encode l)
  omega

/-- **El número de una palabra de largo `n + 2` es al menos `2^(2^n)`.** -/
theorem dos_pow_dos_pow_le_encode : ∀ (n : ℕ) (l : List Bool), l.length = n + 2 →
    2 ^ 2 ^ n ≤ Encodable.encode l
  | 0, [a, b], _ => by
    have h1 := encode_cons_ge a [b]
    have h2 := encode_cons_ge b []
    simp only [pow_zero, pow_one]
    nlinarith
  | n + 1, a :: l, hl => by
    have ih := dos_pow_dos_pow_le_encode n l (by simpa using hl)
    have h := encode_cons_ge a l
    have : 2 ^ 2 ^ (n + 1) = 2 ^ 2 ^ n * 2 ^ 2 ^ n := by rw [pow_succ, pow_mul, sq]
    rw [this]
    have := Nat.mul_le_mul ih ih
    omega

/-- **El largo de la palabra es `log₂ log₂` del índice**, más dos. -/
theorem largo_palabra_loglog (i : ℕ) : (palabra i).length ≤ Nat.log 2 (Nat.log 2 i) + 2 := by
  unfold palabra
  cases h : Encodable.decode₂ (List Bool) i with
  | none => simp
  | some w =>
    have hi := Encodable.mem_decode₂.1 h
    simp only [Option.getD_some]
    rcases Nat.lt_or_ge w.length 2 with hw | hw
    · omega
    · obtain ⟨n, hn⟩ : ∃ n, w.length = n + 2 := ⟨w.length - 2, by omega⟩
      have h1 := dos_pow_dos_pow_le_encode n w hn
      rw [hi] at h1
      have h2 := Nat.le_log_of_pow_le one_lt_two h1
      have h3 := Nat.le_log_of_pow_le one_lt_two h2
      omega

/-- **El índice de una descripción, doblemente exponencial en su largo.** -/
theorem indiceDe_ge (d : Desc) (n : ℕ) (hn : (eDesc d).length = n + 2) : 2 ^ 2 ^ n ≤ indiceDe d :=
  dos_pow_dos_pow_le_encode n _ hn

end Sagitta.Map.Informacion.NoCreacion
