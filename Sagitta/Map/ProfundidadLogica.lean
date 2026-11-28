import Sagitta.Map.KolmogorovTiempo

/-!
# Profundidad lógica: la materia se conserva, la energía crece lento

Sobre `KolmogorovTiempo.lean` (que se importa y no se toca): programas = códigos de Mathlib, `largo` = bits libres de
prefijo del árbol, «`p` produce `x`» = `eval p 0 = x`, `costo p 0` = el menor presupuesto de `evaln`, `K` = el menor
largo. Aquí se agregan dos cosas de Levin y Bennett, cada una con su control.

## Qué se prueba

1. **No crecimiento de la información** (Levin, la «conservación de la materia»; `K_no_crece_en`, `K_no_crece`): si
   `eval q x = y`, entonces `K y ≤ K x + largo q + 3`. El programa de `y` es `comp q p`, con `p` el más corto de `x`
   (`produce_comp`: `comp q p` produce `y`), y `largo (comp q p) = 3 + largo q + largo p` (`largo_comp`): la constante
   `costoComponer = 3` son exactamente los tres bits de la etiqueta de `comp`. Controles: la hipótesis no es vacía
   (`K_no_crece_succ`); la cota está a `6` de alcanzarse para **todo** `y` (`K_no_crece_casi`, con `x = 0` y `q` el
   programa más corto de `y`); sin el `largo q` es falsa (`no_constante_sin_programa`: ninguna constante sirve); y no se
   invierte (`no_crece_no_se_invierte`): calcular destruye información, no la crea.
2. **La curva de profundidad** (Bennett): `profundidadLogica s x` = el menor `costo p 0` entre los `p` que producen `x`
   con `largo p ≤ K x + s`. Está bien definida (el programa más corto siempre califica, `profundidadLogica_spec`), es
   `≥ 1` y es **antítona** en `s` (`profundidadLogica_antitona`): más bits de descripción, menos tiempo mínimo. Liga con
   Levin: `Kt x ≤ K x + s + log₂ (profundidadLogica s x)` (`Kt_le_profundidadLogica`).
   **Control: la curva baja de verdad.** Con presupuesto `1` todas las subllamadas reciben la entrada `0`, y lo único
   que se arma es un árbol de `pair` sobre `0` y `1`; `largoUnPaso x` es una cota inferior del largo de eso (que se alcanza no está probado), y todo programa de
   costo `1` que produce `x` mide al menos eso (`largoUnPaso_le`, por inducción sobre el código). Para la torre
   `2^(2^k) − 1`, `largoUnPaso = 3 · 2^(k+1) − 3` (`largoUnPaso_torre`) mientras `K ≤ 24k + 3`; así que en toda la meseta
   `24k + s + 6 < 3 · 2^(k+1)` la profundidad es `≥ 2` (`torre_profunda`) y al final vale `1`
   (`profundidadLogica_arbol`). Para `k = 5`: `≥ 2` en `s = 65`, `= 1` en `s = largo (arbol x)` (`curva_baja_torre`), y
   el mutante «la curva crece» queda refutado (`curva_no_creciente`).
3. **Crecimiento lento**, en una forma débil (`crecimiento_lento`): si `eval q x = y`,
   `profundidadLogica (K x + s + |q| + 3 − K y) y ≤ max (profundidadLogica s x) (costo q x)`. Leído al revés
   (`profundo_no_sale_rapido`): si `y` es profundo y `q` es rápido, `x` ya era profundo. El término del tiempo de `q` es
   indispensable (`crecimiento_necesita_tiempo`: el mutante sin él es falso, con `x = 0` y `q` = la torre).

## Lo que la medida no deja ver, dicho con precisión

`evaln` cobra el tamaño de las **entradas** de cada subllamada, no el de lo que se **calcula** (el hallazgo de
`KolmogorovTiempo`). Tres consecuencias:

* **La profundidad colapsa en significancia lineal**: para todo `x`, `profundidadLogica s x = 1` en cuanto
  `s ≥ 24 · |x| + 9` (`profundidadLogica_colapsa`), porque el árbol de `x` corre con presupuesto `1`. En la medida de
  Bennett (pasos de máquina) eso no pasa: escribir `x` cuesta al menos `|x|` pasos.
* **Solo se ve el escalón `≥ 2` → `1`**: la cota inferior viene de clasificar los programas de costo `1`; para costos
  mayores no hay clasificación, así que no se sabe cuán profunda es la torre en `s = 0` (`torre_lenta` acota **un**
  programa, no todos).
* **El crecimiento lento sale con `max`, no con suma**, porque el presupuesto de `evaln` es uno solo para todas las
  subllamadas (paralelo, no secuencial); y la significancia se degrada en `K x − K y`, que Bennett evita definiendo la
  significancia por la compresibilidad del programa (`K(p) ≥ |p| − s`) y no por su distancia a `K x`.
  La forma de Bennett, «profundidad de `y` ≤ profundidad de `x` + tiempo de `q`» con significancia `s + O(|q|)`, pide
  una medida que cobre la salida y sume los tiempos de una composición (pasos de una máquina de Turing o de un
  intérprete con costo por bit escrito); con `evaln` no se puede enunciar honestamente.

## La lectura en el proyecto

`K` es la **materia**: un cómputo no la crea (`K_no_crece`), solo la mueve, y lo que entra es lo que pagó el
resolvedor en su descripción (`largo q`). La profundidad es la **energía**: lo que costó, en tiempo, llegar a `x` desde
su descripción casi mínima; no sale rápido de algo poco profundo (`crecimiento_lento`). La curva `s ↦
profundidadLogica s x` es el canje de José entre las tres memorias, en caja blanca y en un universo cerrado (no hay
entrada: `x` está entero en el programa): `s` es la memoria que se le da de más al resolvedor por encima del mínimo, y
la curva dice cuánto tiempo se ahorra con ella. En la torre, `≈ 6 · 2^k` bits de más compran bajar el tiempo a `1`; el
programa corto de `24k + 3` bits paga en tiempo. El precio se paga sí o sí; lo abierto es si una vez (en la
descripción, la memoria del resolvedor) o en cada instancia (en el tiempo).

## Lo que NO se prueba

* La **invariancia** de `K` (todo es relativo a los códigos de Mathlib con la codificación `bits`).
* Que `costo` sea tiempo de máquina: es una medida de Blum, y no cobra la salida.
* El crecimiento lento de Bennett en su forma aditiva (ver arriba), ni cuán profunda es la torre más allá de `≥ 2`.
* **Nada sobre P contra NP.**

## Fuentes

* L. A. Levin, «Randomness conservation inequalities; information and independence in mathematical theories»,
  *Information and Control* 61(1):15–37, 1984, doi:10.1016/S0019-9958(84)80060-1 (verificada en Crossref; no leída).
* C. H. Bennett, «Logical depth and physical complexity», en R. Herken (ed.), *The Universal Turing Machine: A
  Half-Century Survey*, Oxford, 1988 (Crossref fecha la edición en línea en 1990), pp. 227–258,
  doi:10.1093/oso/9780198537748.003.0008 (verificada en Crossref; no leída: las definiciones de aquí son de memoria). Las pruebas son propias.
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map.Tiempo.ProfundidadLogica

open AceleracionBlum KolmogorovTiempo

/-! ## 1. No crecimiento de la información -/

/-- **Componer produce**: si `p` produce `x` y `q` lleva `x` a `y`, `comp q p` produce `y`. -/
theorem produce_comp {q p : Code} {x y : ℕ} (hp : Produce p x) (hq : eval q x = Part.some y) :
    Produce (.comp q p) y := by
  unfold Produce at hp ⊢
  simp only [eval, hp]
  exact (Part.bind_some x _).trans hq

/-- El largo de una composición: los tres bits de la etiqueta más los dos subárboles. -/
theorem largo_comp (q p : Code) : largo (.comp q p) = 3 + largo q + largo p := by
  simp [largo, bits]; omega

/-- El costo fijo de componer: los tres bits de la etiqueta de `comp`. -/
def costoComponer : ℕ := 3

/-- **No crecimiento de la información** (Levin): `K y ≤ K x + |q| + 3` si `eval q x = y`. -/
theorem K_no_crece_en {q : Code} {x y : ℕ} (hq : eval q x = Part.some y) :
    K y ≤ K x + largo q + costoComponer := by
  obtain ⟨p, hp, hl⟩ := K_spec x
  have := K_le (produce_comp hp hq)
  rw [largo_comp] at this
  simp only [costoComponer]; omega

/-- **No crecimiento**, para una función total calculada por `q`: `K (f x) ≤ K x + |q| + 3`. -/
theorem K_no_crece {q : Code} {f : ℕ → ℕ} (hq : Computa q f) (x : ℕ) :
    K (f x) ≤ K x + largo q + costoComponer :=
  K_no_crece_en (hq x)

/-- Control: la hipótesis no es vacía. -/
theorem K_no_crece_succ (x : ℕ) : K (x + 1) ≤ K x + 6 := by
  have := K_no_crece_en (q := .succ) (x := x) (y := x + 1) (by simp [eval])
  simp [largo, bits, costoComponer] at this; omega

/-- Control: la cota está a `6` de alcanzarse, para todo `y`. -/
theorem K_no_crece_casi (y : ℕ) :
    ∃ q, eval q 0 = Part.some y ∧ K 0 + largo q + costoComponer = K y + 6 := by
  obtain ⟨q, hq, hl⟩ := K_spec y
  exact ⟨q, hq, by rw [K_cero.1, hl]; simp [costoComponer]; omega⟩

/-- **Mutante refutado**: sin el `largo q` ninguna constante sirve (un `q` constante produce un `y` incompresible). -/
theorem no_constante_sin_programa :
    ¬ ∃ c, ∀ (q : Code) (x y : ℕ), eval q x = Part.some y → K y ≤ K x + c := by
  rintro ⟨c, h⟩
  obtain ⟨y, -, hy⟩ := incompresible_K (c + 4)
  have := h (arbol y) 0 y (eval_arbol y 0)
  rw [K_cero.1] at this
  omega

/-- **Mutante refutado**: la desigualdad no se invierte; calcular (aquí, la constante `0`) destruye información. -/
theorem no_crece_no_se_invierte :
    ¬ ∀ (q : Code) (x y : ℕ), eval q x = Part.some y → K x ≤ K y + largo q + costoComponer := by
  intro h
  obtain ⟨x, -, hx⟩ := incompresible_K 10
  have := h .zero x 0 (eval_const 0 x)
  rw [K_cero.1] at this
  simp [largo, bits, costoComponer] at this
  omega

/-! ## 2. La curva de profundidad -/

theorem existe_profundo (s x : ℕ) :
    ∃ t, ∃ p, Produce p x ∧ largo p ≤ K x + s ∧ costo p 0 ≤ t := by
  obtain ⟨p, hp, hl⟩ := K_spec x
  exact ⟨_, p, hp, by omega, le_rfl⟩

open Classical in
/-- **Profundidad lógica con significancia `s`** (Bennett): el menor `costo p 0` entre los programas que producen `x`
con a lo sumo `s` bits por encima de `K x`. -/
noncomputable def profundidadLogica (s x : ℕ) : ℕ := Nat.find (existe_profundo s x)

theorem profundidadLogica_spec (s x : ℕ) :
    ∃ p, Produce p x ∧ largo p ≤ K x + s ∧ costo p 0 = profundidadLogica s x := by
  classical
  obtain ⟨p, hp, hl, hc⟩ := Nat.find_spec (existe_profundo s x)
  refine ⟨p, hp, hl, le_antisymm hc ?_⟩
  exact Nat.find_min' (existe_profundo s x) ⟨p, hp, hl, le_rfl⟩

theorem profundidadLogica_le {s x : ℕ} {p : Code} (hp : Produce p x) (hl : largo p ≤ K x + s) :
    profundidadLogica s x ≤ costo p 0 := by
  classical
  exact Nat.find_min' (existe_profundo s x) ⟨p, hp, hl, le_rfl⟩

/-- **La curva es antítona**: más bits de descripción, menos tiempo mínimo. -/
theorem profundidadLogica_antitona (x : ℕ) : Antitone fun s => profundidadLogica s x := by
  intro s s' hs
  obtain ⟨p, hp, hl, hc⟩ := profundidadLogica_spec s x
  simp only
  rw [← hc]
  exact profundidadLogica_le hp (by omega)

theorem costo_pos {p : Code} {x : ℕ} (hp : Produce p x) : 1 ≤ costo p 0 := by
  have h := pasos_gt p 0
  rw [pasos_de_produce hp] at h
  exact_mod_cast h

theorem profundidadLogica_pos (s x : ℕ) : 1 ≤ profundidadLogica s x := by
  obtain ⟨p, hp, -, hc⟩ := profundidadLogica_spec s x
  rw [← hc]; exact costo_pos hp

/-- **El piso**: si el árbol de `x` cabe en la significancia, la profundidad es `1`. -/
theorem profundidadLogica_suelo {s x : ℕ} (h : largo (arbol x) ≤ K x + s) : profundidadLogica s x = 1 := by
  have := profundidadLogica_le (produce_arbol x) h
  rw [costo_arbol] at this
  have := profundidadLogica_pos s x
  omega

theorem profundidadLogica_arbol (x : ℕ) : profundidadLogica (largo (arbol x)) x = 1 :=
  profundidadLogica_suelo (by omega)

/-- **La profundidad colapsa en significancia lineal** (límite de la medida): con `s ≥ 24 · |x| + 9`, vale `1`. -/
theorem profundidadLogica_colapsa {s x : ℕ} (h : 24 * Nat.size x + 9 ≤ s) : profundidadLogica s x = 1 :=
  profundidadLogica_suelo (by have := largo_arbol_size x; omega)

/-- **Liga con Levin**: `Kt x ≤ K x + s + log₂ (profundidadLogica s x)`. -/
theorem Kt_le_profundidadLogica (s x : ℕ) : Kt x ≤ K x + s + Nat.log 2 (profundidadLogica s x) := by
  obtain ⟨p, hp, hl, hc⟩ := profundidadLogica_spec s x
  have := Kcon_le (g := Nat.log 2) hp
  rw [hc] at this
  simp only [Kt]; omega

/-! ## 2b. Lo que se puede con presupuesto `1` -/

/-- **Cota inferior del largo con presupuesto `1`**: el árbol de `pair` sobre las hojas `0` y `1` (`succ` solo produce `1` con
entrada `0`), tres bits por nodo. -/
def largoUnPaso : ℕ → ℕ
  | 0 => 3
  | 1 => 3
  | n + 2 => 3 + largoUnPaso (Nat.unpair (n + 2)).1 + largoUnPaso (Nat.unpair (n + 2)).2
decreasing_by
  · exact Nat.unpair_lt (by omega)
  · exact unpair_right_lt (by omega)

theorem largoUnPaso_pair_eq {a b : ℕ} (h : 2 ≤ Nat.pair a b) :
    largoUnPaso (Nat.pair a b) = 3 + largoUnPaso a + largoUnPaso b := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.pair a b = n + 2 := ⟨Nat.pair a b - 2, by omega⟩
  rw [hn, largoUnPaso, ← hn, Nat.unpair_pair]

theorem largoUnPaso_pair_le (a b : ℕ) :
    largoUnPaso (Nat.pair a b) ≤ 3 + largoUnPaso a + largoUnPaso b := by
  rcases Nat.lt_or_ge (Nat.pair a b) 2 with h | h
  · have : largoUnPaso (Nat.pair a b) = 3 := by
      rcases hh : Nat.pair a b with _ | _ | n
      · simp [largoUnPaso]
      · simp [largoUnPaso]
      · omega
    omega
  · rw [largoUnPaso_pair_eq h]

/-- **Clasificación de los programas de presupuesto `1`**: todo código que termina en `evaln 1` con entrada `0` mide al
menos `largoUnPaso` de su salida. Con presupuesto `1` la guarda obliga a que toda subllamada reciba `0`. -/
theorem largoUnPaso_le : ∀ (c : Code) (x : ℕ), evaln 1 c 0 = some x → largoUnPaso x ≤ largo c := by
  intro c
  induction c with
  | zero => intro x h; obtain rfl := Option.some_inj.1 (by simpa [evaln] using h); simp [largoUnPaso, largo, bits]
  | succ => intro x h; obtain rfl := Option.some_inj.1 (by simpa [evaln] using h); simp [largoUnPaso, largo, bits]
  | left => intro x h; obtain rfl := Option.some_inj.1 (by simpa [evaln] using h); simp [largoUnPaso, largo, bits]
  | right => intro x h; obtain rfl := Option.some_inj.1 (by simpa [evaln] using h); simp [largoUnPaso, largo, bits]
  | pair cf cg ihf ihg =>
    intro x h
    rcases ha : evaln 1 cf 0 with _ | a
    · simp [evaln, ha, Seq.seq] at h
    rcases hb : evaln 1 cg 0 with _ | b
    · simp [evaln, ha, hb, Seq.seq] at h
    obtain rfl : Nat.pair a b = x := by simpa [evaln, ha, hb, Seq.seq] using h
    have := ihf a ha; have := ihg b hb
    have := largoUnPaso_pair_le a b
    simp only [largo, bits, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | comp cf cg ihf ihg =>
    intro x h
    rcases hy : evaln 1 cg 0 with _ | y
    · simp [evaln, hy] at h
    have hx : evaln 1 cf y = some x := by simpa [evaln, hy] using h
    have : y < 1 := evaln_bound hx
    obtain rfl : y = 0 := by omega
    have := ihf x hx
    simp only [largo, bits, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | prec cf cg ihf ihg =>
    intro x h
    have := ihf x (by simpa [evaln] using h)
    simp only [largo, bits, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | rfind' cf ihf =>
    intro x h
    have h00 : Nat.pair 0 0 = 0 := rfl
    rcases ha : evaln 1 cf 0 with _ | a
    · simp [evaln, h00, ha] at h
    have hx : x = 0 := by
      by_cases ha0 : a = 0
      · simpa [evaln, h00, ha, ha0, eq_comm] using h
      · simp [evaln, h00, ha, ha0] at h
    subst hx
    simp only [largoUnPaso, largo, bits, List.length_append, List.length_cons, List.length_nil]
    omega

theorem evaln_de_costo {c : Code} {n y k : ℕ} (h : eval c n = Part.some y) (hk : costo c n ≤ k) :
    evaln k c n = some y := by
  have hd : (eval c n).Dom := by rw [h]; trivial
  have he : pasos c n = costo c n := (ENat.natCast_toNat (ne_of_lt ((pasos_lt_top_iff c n).2 hd))).symm
  have hs : (evaln k c n).isSome := (pasos_le_iff c n k).1 (by rw [he]; exact_mod_cast hk)
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hs
  have := evaln_sound hz
  rw [h] at this
  rw [hz, Part.mem_some_iff.1 this]

theorem largoUnPaso_le_de_costo {p : Code} {x : ℕ} (hp : Produce p x) (h1 : costo p 0 ≤ 1) :
    largoUnPaso x ≤ largo p :=
  largoUnPaso_le p x (evaln_de_costo hp h1)

/-- **Cota inferior de la profundidad**: si `K x + s < largoUnPaso x`, ningún programa admitido corre en `1`. -/
theorem profundidadLogica_ge_dos {s x : ℕ} (h : K x + s < largoUnPaso x) : 2 ≤ profundidadLogica s x := by
  obtain ⟨p, hp, hl, hc⟩ := profundidadLogica_spec s x
  by_contra hno
  have := largoUnPaso_le_de_costo hp (by omega)
  omega

/-! ## 2c. Control: la curva baja de verdad en la torre -/

def valorTorre (k : ℕ) : ℕ := 2 ^ 2 ^ k - 1

theorem eval_cuad (n : ℕ) : eval cuad n = Part.some (Nat.pair n n) := by
  simp [cuad, eval, eval_id, Seq.seq]

theorem valorTorre_succ (k : ℕ) : valorTorre (k + 1) = Nat.pair (valorTorre k) (valorTorre k) :=
  produce_unico (eval_torre (k + 1)) (produce_comp (eval_torre k) (eval_cuad _))

theorem valorTorre_ge (k : ℕ) : 3 ≤ valorTorre (k + 1) := by
  have : 4 ≤ 2 ^ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num)
          (by calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [valorTorre]; omega

theorem largoUnPaso_torre (k : ℕ) : largoUnPaso (valorTorre k) + 3 = 3 * 2 ^ (k + 1) := by
  induction k with
  | zero => simp [valorTorre, largoUnPaso]
  | succ k ih =>
    have h2 := valorTorre_ge k
    rw [valorTorre_succ] at h2 ⊢
    rw [largoUnPaso_pair_eq (by omega), pow_succ]
    omega

theorem K_valorTorre (k : ℕ) : K (valorTorre k) ≤ 3 + 24 * k := K_torre k

/-- La meseta: mientras `24k + s + 6 < 3 · 2^(k+1)`, la torre no se produce con presupuesto `1`. -/
theorem torre_profunda {k s : ℕ} (h : 24 * k + s + 6 < 3 * 2 ^ (k + 1)) :
    2 ≤ profundidadLogica s (valorTorre k) := by
  apply profundidadLogica_ge_dos
  have := largoUnPaso_torre k
  have := K_valorTorre k
  omega

/-- **Control: la curva baja de verdad** para `x = 2^32 − 1`: `≥ 2` con `s = 65`, `1` con `s = largo (arbol x)`. -/
theorem curva_baja_torre :
    2 ≤ profundidadLogica 65 (valorTorre 5) ∧
      profundidadLogica (largo (arbol (valorTorre 5))) (valorTorre 5) = 1 :=
  ⟨torre_profunda (by norm_num), profundidadLogica_arbol _⟩

/-- **Mutante refutado**: la curva no es monótona creciente. -/
theorem curva_no_creciente : ¬ ∀ x s s', s ≤ s' → profundidadLogica s x ≤ profundidadLogica s' x := by
  intro h
  have := h (valorTorre 5) 0 (largo (arbol (valorTorre 5))) (Nat.zero_le _)
  have h2 := torre_profunda (k := 5) (s := 0) (by norm_num)
  rw [profundidadLogica_arbol] at this
  omega

/-! ## 3. Crecimiento lento -/

/-- **El costo de componer es un máximo**: `evaln` usa un solo presupuesto para las dos subllamadas. -/
theorem costo_comp_le {q p : Code} {x y : ℕ} (hp : Produce p x) (hq : eval q x = Part.some y) :
    costo (.comp q p) 0 ≤ max (costo p 0) (costo q x) := by
  have h1 := costo_pos hp
  obtain ⟨j, hj⟩ : ∃ j, max (costo p 0) (costo q x) = j + 1 := ⟨max (costo p 0) (costo q x) - 1, by omega⟩
  have ep := evaln_de_costo hp (le_max_left _ (costo q x))
  have eq := evaln_de_costo hq (le_max_right (costo p 0) _)
  rw [hj] at ep eq
  have hc : (evaln (j + 1) (.comp q p) 0).isSome := by
    simp [evaln, ep, eq]
  have := (pasos_le_iff _ 0 (j + 1)).2 hc
  rw [pasos_de_produce (produce_comp hp hq)] at this
  rw [hj]; exact_mod_cast this

/-- **Crecimiento lento**, forma débil: lo profundo no sale rápido de lo poco profundo. -/
theorem crecimiento_lento {q : Code} {x y : ℕ} (s : ℕ) (hq : eval q x = Part.some y) :
    profundidadLogica (K x + s + largo q + costoComponer - K y) y ≤
      max (profundidadLogica s x) (costo q x) := by
  obtain ⟨p, hp, hl, hc⟩ := profundidadLogica_spec s x
  have hn := K_no_crece_en hq
  have h1 := profundidadLogica_le (s := K x + s + largo q + costoComponer - K y) (produce_comp hp hq)
    (by rw [largo_comp]; simp only [costoComponer] at hn ⊢; omega)
  have h2 := costo_comp_le hp hq
  rw [hc] at h2
  omega

/-- **Al revés**: si `y` es profundo (más que `T`) y `q` corre en `T`, `x` ya era más profundo que `T`. -/
theorem profundo_no_sale_rapido {q : Code} {x y s T : ℕ} (hq : eval q x = Part.some y)
    (hrapido : costo q x ≤ T) (hprof : T < profundidadLogica (K x + s + largo q + costoComponer - K y) y) :
    T < profundidadLogica s x := by
  have := crecimiento_lento s hq
  omega

/-- **Mutante refutado**: sin el tiempo de `q`, el crecimiento lento es falso. -/
theorem crecimiento_necesita_tiempo :
    ¬ ∀ (q : Code) (x y s : ℕ), eval q x = Part.some y →
      profundidadLogica (K x + s + largo q + costoComponer - K y) y ≤ profundidadLogica s x := by
  intro h
  have hq : eval (torre 5) 0 = Part.some (valorTorre 5) := eval_torre 5
  have := h (torre 5) 0 (valorTorre 5) 0 hq
  have h0 : profundidadLogica 0 0 = 1 := profundidadLogica_suelo (by rw [K_cero.1]; simp [arbol, largo, bits])
  rw [h0, K_cero.1, largo_torre] at this
  have hK := K_valorTorre 5
  have hL := largoUnPaso_torre 5
  have hd := profundidadLogica_ge_dos
    (s := 3 + 0 + (3 + 24 * 5) + costoComponer - K (valorTorre 5)) (x := valorTorre 5)
    (by simp only [costoComponer]; omega)
  omega

end Sagitta.Map.Tiempo.ProfundidadLogica
