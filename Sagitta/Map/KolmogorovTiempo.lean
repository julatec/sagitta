import Sagitta.Map.AceleracionBlum

/-!
# Kolmogorov con tiempo acotado: la ley de las tres memorias en caja blanca

José propone una ley de conservación entre tres memorias, la descripción del resolvedor, la cita (lo que se le pasa
por instancia) y el verificador, comunicadas por el tiempo de ejecución. En caja negra es una ley de información
(`LeyTresMemorias.lean`, otra sesión). Aquí se mira la **caja blanca**: la entrada ya contiene la información, y lo que
se conserva es el **cómputo**. La medida natural es la de Levin, `Kt(x) = min { |p| + log₂ t : p produce x en t pasos }`:
descripción más logaritmo del tiempo.

## Las definiciones, y por qué son honestas

* **Programas**: los códigos de Mathlib (`Nat.Partrec.Code`). **Pasos**: la medida de Blum `pasos` de
  `AceleracionBlum.lean` (el menor presupuesto `k` con `evaln k p 0 ≠ none`), y `costo` su valor en `ℕ`.
* **El largo** `largo p` es el largo de `bits p`: el árbol de `p` en preorden, **tres bits por nodo** para decir cuál de
  los ocho constructores es. El código es libre de prefijos (`bits_prefijo`), así que `bits` es inyectiva (`bits_inj`):
  `largo` cuenta bits de verdad, y el palomar de las cadenas de bits se le aplica tal cual.
  *Por qué no `Nat.size (encode p)`*: el número de Mathlib anida `Nat.pair`, que eleva al cuadrado en cada nivel, así
  que un árbol de profundidad `d` puede tener un número de `≈ 2^d` bits. Mediría la profundidad, no la descripción.
  *Por qué los tres bits importan*: si el largo fuera el número de nodos, sin los bits del constructor, hay más de
  `2^(L+1)` códigos de `L` nodos y el palomar se cae (ver las notas del proyecto).
* **«`p` produce `x`»** (`Produce`): `eval p 0 = Part.some x`.
* `Kcon g x`: el menor `largo p + g (costo p 0)` sobre los `p` que producen `x` (`Nat.find`). **`K = Kcon 0`** y
  **`Kt = Kcon log₂`** (`Nat.log 2`, el piso). El mínimo se alcanza (`Kcon_spec`).
* **Bien definidas**: todo `x` tiene un programa, su **árbol** (`arbol`): `pair` de los árboles de las dos mitades de
  `unpair x`. Como cada mitad es a lo sumo `√x`, el árbol tiene `O(|x|)` nodos (`largo_arbol_size`).

## Qué se prueba

1. `K_le_Kt`: `K x ≤ Kt x`; en general `K x ≤ Kcon g x` para cualquier precio del tiempo.
2. `Kt_cota_superior`: `Kt x ≤ 24 · |x| + 9`, con `|x| = Nat.size x`. **No** es `|x| + O(log |x|)`: el lenguaje de
   Mathlib no tiene literales de bits, y la constante `24` es lo que cuesta en él decir un bit. Bajarla a `1` es el
   teorema de invariancia, que aquí no está.
3. `conteo`: hay menos de `2^(L+1)` números con `K x ≤ L` (y con `Kt x ≤ L`). Por lo tanto (`incompresible_K`,
   `incompresible_Kt`) entre los `x < 2^n` hay alguno con `K x ≥ n` y `Kt x ≥ n`. Es el palomar de `EscalaLog.lean`
   pasado por `bits`; sale `≥ n` y no solo `≥ n − 1` porque `2^(L+1) − 1` cadenas no alcanzan para `2^(L+1)` números.
4. **La ley** (`ley`): si `p` produce `x` y `evaln t p 0` termina, `Kt x ≤ |p| + log₂ t`. Cada resolvedor es un punto
   y `Kt` es la recta mínima. Con la incompresibilidad (`ley_incompresible`): hay un `x < 2^n` tal que **todo**
   programa que lo produce en `t` pasos cumple `|p| + log₂ t ≥ n`. Es la forma de la ley de caja negra.
5. **Controles**: `K 0 = Kt 0 = 3` y `K 1 = 3` (`K_cero`, `K_uno`); la incompresibilidad no es universal: `2^(2^k) − 1`
   tiene `2^k` bits y `K ≤ 24k + 3` (`K_torre`, `comprimible`, y el mutante refutado `no_todo_incompresible`); y el
   término del tiempo cuenta: ese programa corto paga al menos `2^k` en `log₂ t` (`torre_lenta`, por
   `costo_comp_gt`: componer cobra el tamaño del resultado intermedio).

## La lectura

`Kt` es la ley de las tres memorias en caja blanca. La información de `x` ya está en la entrada (aquí no hay entrada:
`x` está entero en el programa), y lo que se reparte es el **cómputo**: un programa corto puede producir `x` si paga en
tiempo, y uno rápido paga en largo. La ley dice que esa suma, en escala logarítmica, no baja de `Kt x`, y que para la
mayoría de los `x` (`ley_incompresible`) no baja del largo de `x`. La torre lo muestra: `2^(2^k) − 1` cabe en `24k + 3`
bits de programa, pero ese programa paga `≥ 2^k` en `log₂ t`; el árbol, en cambio, paga `24 · 2^k` de largo y nada de
tiempo.

**Advertencia sobre la medida de tiempo.** `pasos` es el presupuesto de `evaln`, una medida de Blum válida, pero no
pasos de una máquina: `evaln` cobra el tamaño de las **entradas** de cada subllamada y la profundidad de `prec` y
`rfind'`, no el tamaño de lo que se **calcula**. Por eso el árbol de cualquier `x` corre con presupuesto `1`
(`evaln_arbol`, `costo_arbol`) y `pair` arma números enormes gratis. Consecuencia: la cota superior vale igual para
cualquier precio del tiempo (`Kcon_cota_superior`), también sin el logaritmo; no distingue `Kt` de sus mutantes.

## Lo que NO se prueba

* **La invariancia salvo constante** de `K` entre lenguajes de programación. Todo es relativo a los códigos de Mathlib
  con la codificación `bits`.
* Que `Kt` sea **estrictamente** mayor que `K` para algún `x` concreto: haría falta una cota inferior para todos los
  programas cortos. Solo se prueba que el término del tiempo cuenta para un programa dado (`torre_lenta`).
* **La dificultad de calcular** `K` o `Kt`, ni con tiempo acotado: el problema MKtP y sus parientes son metacomplejidad
  abierta. De memoria: Liu y Pass (FOCS 2020) ligan la existencia de funciones de un solo sentido a la dificultad en
  promedio de la Kolmogorov con tiempo acotado (`K^t` con `t` polinomial); Hirahara tiene reducciones del peor caso al
  caso promedio que no son de caja negra, sobre problemas de este tipo.
* **Nada sobre P contra NP.**

## Fuentes

* L. A. Levin, «Randomness conservation inequalities; information and independence in mathematical theories»,
  *Information and Control* 61(1):15–37, 1984, doi:10.1016/S0019-9958(84)80060-1 (verificada en Crossref; no leída).
* Y. Liu y R. Pass, «On One-way Functions and Kolmogorov Complexity», *FOCS 2020*, pp. 1243–1254,
  doi:10.1109/FOCS46700.2020.00118 (verificada en Crossref; no leída).
* De memoria: S. Hirahara, «Non-black-box worst-case to average-case reductions within NP», FOCS 2018.
  Las pruebas de aquí son propias.
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map
namespace Tiempo
namespace KolmogorovTiempo

open AceleracionBlum

/-! ## 1. El largo de un programa: los bits de su árbol -/

/-- **Los bits de un código**: recorrido en preorden, tres bits por nodo para decir el constructor (hay ocho). -/
def bits : Code → List Bool
  | .zero => [false, false, false]
  | .succ => [false, false, true]
  | .left => [false, true, false]
  | .right => [false, true, true]
  | .pair c d => [true, false, false] ++ (bits c ++ bits d)
  | .comp c d => [true, false, true] ++ (bits c ++ bits d)
  | .prec c d => [true, true, false] ++ (bits c ++ bits d)
  | .rfind' c => [true, true, true] ++ bits c

/-- **El código es libre de prefijos**: de `bits c ++ r` se lee de vuelta `c` y el resto `r`. -/
theorem bits_prefijo (c : Code) : ∀ (c' : Code) (r r' : List Bool), bits c ++ r = bits c' ++ r' → c = c' ∧ r = r' := by
  induction c with
  | zero | succ | left | right =>
    intro c' r r' h
    cases c' <;> simp_all [bits]
  | pair c d ihc ihd | comp c d ihc ihd | prec c d ihc ihd =>
    intro c' r r' h
    cases c' <;> simp only [bits, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
      Bool.false_eq_true, Bool.true_eq_false, false_and, and_false, true_and] at h ⊢
    obtain ⟨rfl, h2⟩ := ihc _ _ _ h
    obtain ⟨rfl, rfl⟩ := ihd _ _ _ h2
    simp
  | rfind' c ihc =>
    intro c' r r' h
    cases c' <;> simp only [bits, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
      Bool.true_eq_false, false_and, and_false, true_and] at h ⊢
    obtain ⟨rfl, rfl⟩ := ihc _ _ _ h
    simp

theorem bits_inj {c c' : Code} (h : bits c = bits c') : c = c' :=
  (bits_prefijo c c' [] [] (by simpa using h)).1

/-- **El largo de un programa**: cuántos bits ocupa su árbol. -/
def largo (c : Code) : ℕ := (bits c).length

theorem largo_ge (c : Code) : 3 ≤ largo c := by
  cases c <;> simp [largo, bits]

/-! ## 2. El palomar de las cadenas de bits -/

/-- Una cadena de bits como número, con un `1` de tope: `[]` ↦ `1`, `b :: l` ↦ `2·(l) + b`. -/
def aNum : List Bool → ℕ
  | [] => 1
  | b :: l => 2 * aNum l + (if b then 1 else 0)

theorem aNum_pos : ∀ l, 1 ≤ aNum l
  | [] => le_rfl
  | b :: l => by have := aNum_pos l; simp only [aNum]; split_ifs <;> omega

theorem aNum_lt : ∀ l, aNum l < 2 ^ (l.length + 1)
  | [] => by simp [aNum]
  | b :: l => by
    have := aNum_lt l
    simp only [aNum, List.length_cons, pow_succ] at this ⊢
    split_ifs <;> omega

theorem aNum_inj : ∀ {l l' : List Bool}, aNum l = aNum l' → l = l'
  | [], [], _ => rfl
  | [], b :: l, h => by have := aNum_pos l; simp only [aNum] at h; split_ifs at h <;> omega
  | b :: l, [], h => by have := aNum_pos l; simp only [aNum] at h; split_ifs at h <;> omega
  | b :: l, b' :: l', h => by
    simp only [aNum] at h
    have hb : b = b' ∧ aNum l = aNum l' := by
      cases b <;> cases b' <;> simp at h ⊢ <;> omega
    rw [hb.1, aNum_inj hb.2]

/-- **Control del palomar en su nivel**: hay menos de `2^(L+1)` cadenas de largo `≤ L`. -/
theorem cadenas_cota (L : ℕ) (S : Finset (List Bool)) (hS : ∀ l ∈ S, l.length ≤ L) : S.card < 2 ^ (L + 1) := by
  have h := Finset.card_le_card_of_injOn aNum (t := Finset.Ico 1 (2 ^ (L + 1)))
    (fun l hl => by
      have := aNum_lt l
      have := pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (Nat.succ_le_succ (hS l hl))
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact ⟨aNum_pos l, by omega⟩)
    (fun a _ b _ h => aNum_inj h)
  rw [Nat.card_Ico] at h
  have := Nat.one_le_two_pow (n := L + 1)
  omega

/-! ## 3. Un programa corto para cada número: el árbol de `unpair` -/

/-- Las dos mitades de `unpair n` no pasan de `√n`. -/
theorem unpair_le_sqrt (n : ℕ) : (Nat.unpair n).1 ≤ Nat.sqrt n ∧ (Nat.unpair n).2 ≤ Nat.sqrt n := by
  have h1 := Nat.sqrt_le' n
  have h2 := Nat.lt_succ_sqrt' n
  simp only [Nat.succ_eq_add_one, pow_two] at h1 h2
  have h3 : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) = Nat.sqrt n * Nat.sqrt n + 2 * Nat.sqrt n + 1 := by ring
  unfold Nat.unpair
  simp only
  split_ifs with h
  · simp only; constructor <;> omega
  · simp only; constructor <;> omega

theorem unpair_right_lt {n : ℕ} (hn : 2 ≤ n) : (Nat.unpair n).2 < n :=
  lt_of_le_of_lt (unpair_le_sqrt n).2 (Nat.sqrt_lt_self (by omega))

/-- **El árbol de `x`**: `0` es `zero`, `1` es `succ ∘ zero`, y si `x ≥ 2`, `pair` de los árboles de las dos mitades de
`unpair x`. Es una función constante: no lee su entrada. -/
def arbol : ℕ → Code
  | 0 => .zero
  | 1 => .comp .succ .zero
  | n + 2 => .pair (arbol (Nat.unpair (n + 2)).1) (arbol (Nat.unpair (n + 2)).2)
decreasing_by
  · exact Nat.unpair_lt (by omega)
  · exact unpair_right_lt (by omega)

/-- **El árbol produce `x`**, con cualquier entrada. -/
theorem eval_arbol (x : ℕ) : ∀ m, eval (arbol x) m = Part.some x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro m
    rcases x with _ | _ | n
    · rw [arbol]; exact eval_const 0 m
    · rw [arbol]; exact eval_const 1 m
    · rw [arbol]
      have ha := ih _ (Nat.unpair_lt (by omega)) m
      have hb := ih _ (unpair_right_lt (by omega)) m
      simp [eval, ha, hb, Seq.seq, Nat.pair_unpair]

/-- **Y lo produce con presupuesto `1`**: `evaln` no cobra el tamaño de lo que se calcula, solo el de las entradas. -/
theorem evaln_arbol (x : ℕ) : evaln 1 (arbol x) 0 = some x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases x with _ | _ | n
    · simp [arbol, evaln]
    · simp [arbol, evaln]
    · rw [arbol]
      have ha := ih _ (Nat.unpair_lt (by omega))
      have hb := ih _ (unpair_right_lt (by omega))
      simp [evaln, ha, hb, Seq.seq, Nat.pair_unpair]

theorem largo_arbol_chico {x : ℕ} (hx : x < 2) : largo (arbol x) + 3 ≤ 12 := by
  rcases x with _ | _ | n
  · simp [arbol, largo, bits]
  · simp [arbol, largo, bits]
  · omega

/-- **El largo del árbol**: si `x < 2^(2^d)`, el árbol de `x` ocupa menos de `12 · 2^d` bits. -/
theorem largo_arbol (d : ℕ) : ∀ x, x < 2 ^ 2 ^ d → largo (arbol x) + 3 ≤ 12 * 2 ^ d := by
  induction d with
  | zero => intro x hx; simpa using largo_arbol_chico (by simpa using hx)
  | succ d ih =>
    intro x hx
    rcases Nat.lt_or_ge x 2 with h | h
    · have := largo_arbol_chico h
      have : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
      omega
    · obtain ⟨n, rfl⟩ : ∃ n, x = n + 2 := ⟨x - 2, by omega⟩
      have hs : Nat.sqrt (n + 2) < 2 ^ 2 ^ d := by
        rw [Nat.sqrt_lt', ← pow_mul, ← pow_succ]; exact hx
      have ha := ih _ (lt_of_le_of_lt (unpair_le_sqrt (n + 2)).1 hs)
      have hb := ih _ (lt_of_le_of_lt (unpair_le_sqrt (n + 2)).2 hs)
      rw [arbol]
      simp only [largo, bits, List.length_append, List.length_cons, List.length_nil] at ha hb ⊢
      rw [pow_succ]
      omega

/-- `2^⌈log₂ s⌉ ≤ 2s + 1`. -/
theorem pow_clog_le (s : ℕ) : 2 ^ Nat.clog 2 s ≤ 2 * s + 1 := by
  rcases Nat.lt_or_ge s 2 with h | h
  · rw [Nat.clog_of_right_le_one (by omega)]; omega
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h2 : 0 < Nat.clog 2 s := Nat.clog_pos (by norm_num) h
    obtain ⟨d, hd⟩ : ∃ d, Nat.clog 2 s = d + 1 := ⟨Nat.clog 2 s - 1, by omega⟩
    rw [hd] at h1 ⊢
    simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel, pow_succ] at h1 ⊢
    omega

/-- **El largo del árbol en bits de `x`**: a lo sumo `24 · |x| + 9`, con `|x| = Nat.size x`. -/
theorem largo_arbol_size (x : ℕ) : largo (arbol x) ≤ 24 * Nat.size x + 9 := by
  have hx : x < 2 ^ 2 ^ Nat.clog 2 (Nat.size x) :=
    lt_of_lt_of_le (Nat.lt_size_self x)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_pow_clog (by norm_num) _))
  have := largo_arbol _ x hx
  have := pow_clog_le (Nat.size x)
  omega

/-! ## 4. `K` y `Kt` -/

/-- **`p` produce `x`**: con entrada `0`, el programa termina y devuelve `x`. -/
def Produce (p : Code) (x : ℕ) : Prop := eval p 0 = Part.some x

theorem produce_arbol (x : ℕ) : Produce (arbol x) x := eval_arbol x 0

/-- **Siempre hay un programa que produce `x`**: su árbol. -/
theorem existe_programa (x : ℕ) : ∃ p, Produce p x := ⟨_, produce_arbol x⟩

theorem produce_unico {p : Code} {x y : ℕ} (hx : Produce p x) (hy : Produce p y) : x = y :=
  Part.some_injective (hx.symm.trans hy)

/-- Si `p` produce algo, sus pasos son finitos y `costo` es su valor. -/
theorem pasos_de_produce {p : Code} {x : ℕ} (h : Produce p x) : pasos p 0 = costo p 0 := by
  have hd : (eval p 0).Dom := by rw [h]; trivial
  exact (ENat.natCast_toNat (ne_of_lt ((pasos_lt_top_iff p 0).2 hd))).symm

theorem costo_arbol (x : ℕ) : costo (arbol x) 0 = 1 := by
  have h := pasos_de_produce (produce_arbol x)
  have hle : pasos (arbol x) 0 ≤ (1 : ℕ) := (pasos_le_iff _ _ _).2 (by rw [evaln_arbol]; rfl)
  have hgt := pasos_gt (arbol x) 0
  rw [h] at hle hgt
  norm_cast at hle hgt
  omega

theorem existe_cota (g : ℕ → ℕ) (x : ℕ) : ∃ m, ∃ p, Produce p x ∧ largo p + g (costo p 0) ≤ m :=
  ⟨_, arbol x, produce_arbol x, le_rfl⟩

open Classical in
/-- **La medida con un precio `g` del tiempo**: el menor `largo p + g(pasos p 0)` sobre los programas que producen `x`.
`K` es `g = 0`; `Kt` es `g = log₂`. -/
noncomputable def Kcon (g : ℕ → ℕ) (x : ℕ) : ℕ := Nat.find (existe_cota g x)

/-- **Kolmogorov**: el menor largo de un programa que produce `x`. -/
noncomputable def K (x : ℕ) : ℕ := Kcon (fun _ => 0) x

/-- **Levin**: el menor `largo p + log₂ t` sobre los programas `p` que producen `x` en `t` pasos. -/
noncomputable def Kt (x : ℕ) : ℕ := Kcon (Nat.log 2) x

/-- **Cada resolvedor es un punto**: si `p` produce `x`, la medida queda debajo de su `largo + g(costo)`. -/
theorem Kcon_le {g : ℕ → ℕ} {p : Code} {x : ℕ} (h : Produce p x) : Kcon g x ≤ largo p + g (costo p 0) := by
  classical
  exact Nat.find_min' (existe_cota g x) ⟨p, h, le_rfl⟩

/-- **Y el mínimo se alcanza**: hay un programa exactamente en la recta mínima. -/
theorem Kcon_spec (g : ℕ → ℕ) (x : ℕ) : ∃ p, Produce p x ∧ largo p + g (costo p 0) = Kcon g x := by
  classical
  obtain ⟨p, hp, hle⟩ := Nat.find_spec (existe_cota g x)
  exact ⟨p, hp, le_antisymm hle (Kcon_le hp)⟩

theorem K_le {p : Code} {x : ℕ} (h : Produce p x) : K x ≤ largo p := by
  have := Kcon_le (g := fun _ => 0) h
  simpa [K] using this

theorem K_spec (x : ℕ) : ∃ p, Produce p x ∧ largo p = K x := by
  have := Kcon_spec (fun _ => 0) x
  simpa [K] using this

/-- **`K` es el piso de toda la familia**: cobrar el tiempo nunca baja la medida. -/
theorem K_le_Kcon (g : ℕ → ℕ) (x : ℕ) : K x ≤ Kcon g x := by
  obtain ⟨p, hp, he⟩ := Kcon_spec g x
  have := K_le hp
  omega

/-- **`K ≤ Kt`.** -/
theorem K_le_Kt (x : ℕ) : K x ≤ Kt x := K_le_Kcon _ x

theorem K_ge (x : ℕ) : 3 ≤ K x := by
  obtain ⟨p, -, he⟩ := K_spec x
  have := largo_ge p
  omega

/-! ## 5. La cota superior -/

/-- **Cota superior, para cualquier precio del tiempo**: `Kcon g x ≤ 24 · |x| + 9 + g 1`. -/
theorem Kcon_cota_superior (g : ℕ → ℕ) (x : ℕ) : Kcon g x ≤ 24 * Nat.size x + 9 + g 1 := by
  have := Kcon_le (g := g) (produce_arbol x)
  rw [costo_arbol] at this
  have := largo_arbol_size x
  omega

/-- **Cota superior de `Kt`**: `K x ≤ Kt x ≤ 24 · |x| + 9`. -/
theorem Kt_cota_superior (x : ℕ) : Kt x ≤ 24 * Nat.size x + 9 := by
  simpa [Kt] using Kcon_cota_superior (Nat.log 2) x

/-! ## 6. Incompresibilidad, por conteo -/

/-- **Conteo**: hay menos de `2^(L+1)` números con `Kcon g x ≤ L` (en particular con `K x ≤ L` o `Kt x ≤ L`). -/
theorem conteo (g : ℕ → ℕ) (L : ℕ) (S : Finset ℕ) (hS : ∀ x ∈ S, Kcon g x ≤ L) : S.card < 2 ^ (L + 1) := by
  classical
  choose p hp hl using K_spec
  have hinj : Set.InjOn (fun x => bits (p x)) (S : Set ℕ) := fun x _ y _ h =>
    produce_unico (hp x) (by rw [bits_inj h]; exact hp y)
  have hmaps : ∀ x ∈ S, (bits (p x)).length ≤ L := fun x hx => by
    have := hS x hx; have := K_le_Kcon g x; have := hl x
    simp only [largo] at this; omega
  have h1 := Finset.card_image_of_injOn hinj
  have h2 := cadenas_cota L (S.image fun x => bits (p x)) (by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hl
    exact hmaps x hx)
  omega

theorem conteo_K (L : ℕ) (S : Finset ℕ) (hS : ∀ x ∈ S, K x ≤ L) : S.card < 2 ^ (L + 1) := conteo _ L S hS

theorem conteo_Kt (L : ℕ) (S : Finset ℕ) (hS : ∀ x ∈ S, Kt x ≤ L) : S.card < 2 ^ (L + 1) := conteo _ L S hS

/-- **Incompresibilidad**: entre los `x < 2^n` hay alguno con `Kcon g x ≥ n`. -/
theorem incompresible (g : ℕ → ℕ) (n : ℕ) : ∃ x < 2 ^ n, n ≤ Kcon g x := by
  rcases n with _ | m
  · exact ⟨0, by norm_num, Nat.zero_le _⟩
  · by_contra hno
    push Not at hno
    have := conteo g m (Finset.range (2 ^ (m + 1))) (fun x hx => by
      have := hno x (Finset.mem_range.1 hx); omega)
    simp at this

theorem incompresible_K (n : ℕ) : ∃ x < 2 ^ n, n ≤ K x := incompresible _ n

theorem incompresible_Kt (n : ℕ) : ∃ x < 2 ^ n, n ≤ Kt x := incompresible _ n

/-! ## 7. La ley de las tres memorias, en caja blanca -/

/-- **La ley**: si `p` produce `x` y su evaluación acotada por `t` termina, `Kt x ≤ |p| + log₂ t`. -/
theorem ley {p : Code} {x t : ℕ} (hp : Produce p x) (ht : (evaln t p 0).isSome) :
    Kt x ≤ largo p + Nat.log 2 t := by
  have h1 := Kcon_le (g := Nat.log 2) hp
  have h2 : costo p 0 ≤ t := by
    have := (pasos_le_iff p 0 t).2 ht
    rw [pasos_de_produce hp] at this
    exact_mod_cast this
  have := Nat.log_mono_right (b := 2) h2
  simp only [Kt]; omega

/-- **Para `x` incompresible, todo resolvedor paga**: hay un `x < 2^n` tal que todo programa que lo produce en `t` pasos
cumple `|p| + log₂ t ≥ n`. -/
theorem ley_incompresible (n : ℕ) :
    ∃ x < 2 ^ n, ∀ p t, Produce p x → (evaln t p 0).isSome → n ≤ largo p + Nat.log 2 t := by
  obtain ⟨x, hx, hn⟩ := incompresible_Kt n
  exact ⟨x, hx, fun p t hp ht => le_trans hn (ley hp ht)⟩

/-! ## 8. Controles -/

/-- **Control: `K` y `Kt` bajos para números chicos**: `0` y `1` tienen un programa de un solo nodo. -/
theorem K_cero : K 0 = 3 ∧ Kt 0 = 3 := by
  have h0 : Produce .zero 0 := eval_const 0 0
  have hc : costo .zero 0 = 1 := by have := costo_arbol 0; rwa [arbol] at this
  have a := K_le h0
  have b := Kcon_le (g := Nat.log 2) h0
  rw [hc] at b
  have := K_ge 0; have := K_le_Kt 0
  simp only [largo, bits, List.length_cons, List.length_nil, Nat.log_one_right] at a b
  simp only [Kt] at *
  omega

theorem K_uno : K 1 = 3 := by
  have h : Produce .succ 1 := by simp [Produce, eval]
  have a := K_le h; have := K_ge 1
  simp only [largo, bits, List.length_cons, List.length_nil] at a
  omega

/-- El cuadrado de Cantor: `n ↦ pair n n = n² + 2n`. -/
def cuad : Code := .pair Code.id Code.id

/-- **La torre**: `succ`, y después `k` veces `cuad`. Produce `2^(2^k) − 1`. -/
def torre : ℕ → Code
  | 0 => .succ
  | k + 1 => .comp cuad (torre k)

theorem eval_torre (k : ℕ) : Produce (torre k) (2 ^ 2 ^ k - 1) := by
  induction k with
  | zero => simp [Produce, torre, eval]
  | succ k ih =>
    have hA : 1 ≤ 2 ^ 2 ^ k := Nat.one_le_two_pow
    obtain ⟨B, hB⟩ : ∃ B, 2 ^ 2 ^ k = B + 1 := ⟨2 ^ 2 ^ k - 1, by omega⟩
    have hsq : 2 ^ 2 ^ (k + 1) = (B + 1) * (B + 1) := by rw [pow_succ, pow_mul, hB, sq]
    rw [hB] at ih
    simp only [Produce, torre, cuad, eval, Nat.add_sub_cancel] at ih ⊢
    rw [ih, hsq]
    simp [eval_id, Seq.seq, Nat.pair]
    ring_nf; omega

theorem largo_torre (k : ℕ) : largo (torre k) = 3 + 24 * k := by
  induction k with
  | zero => simp [largo, torre, bits]
  | succ k ih =>
    simp only [largo, torre, cuad, Code.id, bits, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

/-- **Control: la incompresibilidad no es universal.** `2^(2^k) − 1` tiene `2^k` bits pero `K ≤ 24k + 3`. -/
theorem K_torre (k : ℕ) : K (2 ^ 2 ^ k - 1) ≤ 3 + 24 * k := largo_torre k ▸ K_le (eval_torre k)

theorem comprimible : K (2 ^ 2 ^ 8 - 1) ≤ 195 ∧ 256 ≤ Nat.size (2 ^ 2 ^ 8 - 1) :=
  ⟨K_torre 8, by rw [Nat.succ_le_iff, Nat.lt_size]; norm_num⟩

/-- **Mutante refutado**: «todo `x < 2^n` cumple `K x ≥ n`» es falso. El teorema `incompresible` dice **alguno**. -/
theorem no_todo_incompresible : ¬ ∀ n, ∀ x < 2 ^ n, n ≤ K x := fun h => by
  have := h 256 (2 ^ 2 ^ 8 - 1) (by norm_num)
  have := comprimible.1
  omega

/-- **Componer cobra la entrada intermedia**: si `c` produce `v` y `comp cf c` produce algo, `costo (comp cf c) 0 > v`. -/
theorem costo_comp_gt {cf c : Code} {v w : ℕ} (hc : Produce c v) (hw : Produce (.comp cf c) w) :
    v < costo (.comp cf c) 0 := by
  have hs : (evaln (costo (.comp cf c) 0) (.comp cf c) 0).isSome :=
    (pasos_le_iff _ _ _).1 (by rw [pasos_de_produce hw])
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hs
  rcases hK : costo (.comp cf c) 0 with _ | k
  · rw [hK] at hz; simp [evaln] at hz
  · rw [hK] at hz
    simp only [evaln] at hz
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hz
    obtain ⟨_, -, y, hy, hz⟩ := hz
    have : y = v := by
      have := evaln_sound hy
      rw [hc] at this
      exact (Part.mem_some_iff.1 this)
    subst this
    exact evaln_bound hz

/-- **Control: el término del tiempo cuenta.** El programa corto de `2^(2^(k+1)) − 1` paga al menos `2^k` en `log₂ t`. -/
theorem torre_lenta (k : ℕ) : 2 ^ k ≤ Nat.log 2 (costo (torre (k + 1)) 0) := by
  have h := costo_comp_gt (eval_torre k) (eval_torre (k + 1))
  have : 2 ^ 2 ^ k ≤ costo (torre (k + 1)) 0 := by
    have := @Nat.one_le_two_pow (2 ^ k); simp only [torre] at h ⊢; omega
  calc 2 ^ k = Nat.log 2 (2 ^ 2 ^ k) := (Nat.log_pow (by norm_num) _).symm
    _ ≤ _ := Nat.log_mono_right this

end KolmogorovTiempo
end Tiempo
end Sagitta.Map
