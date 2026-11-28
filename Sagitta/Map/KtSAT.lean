import Sagitta.Map.TerceraCuenta

/-!
# SAT en el universo cerrado: la información está, lo que cuesta es extraerla

La idea es de José (24 nov 2026): aplicar la ley de la información a SAT. Para SAT la información no falta: una
fórmula satisfacible ya determina sus soluciones. Lo que queda es **extraerlas**, o sea la profundidad. En el universo
cerrado (`UniversoCerrado.lean`) el costo de buscar es `2^kt`, salvo constantes, así que **SAT es fácil en el universo
cerrado si y solo si toda fórmula satisfacible tiene `kt` logarítmica**. La pregunta abierta queda escrita como una sola
cantidad, `ktSAT φ`.

## Qué se prueba

1. **El verificador** (`vSAT`, `primrec_vSAT`, `uSAT`, `resoluble_iff`). `vSAT x y` decodifica `x` como fórmula CNF
   (`List Clausula`, la codificación `Encodable` que ya usa `TerceraCuenta.lean`) y `y` como asignación `List Bool`
   (con `asigDeLista`), y devuelve `CNF.eval` de cslib-frontier; si algo no decodifica, `false`. Es **primitivo
   recursivo** (`Primrec₂`), así que vale todo `UniversoCerrado.lean`, también `levin_es_programa`
   (`levin_es_programa_sat`). `Resoluble (uSAT φ) ↔ φ satisfacible`: hace falta ver que basta una asignación finita
   (`satisfacible_iff`).
2. **La ley en bits, en las dos direcciones** (`ley_sat`), para `φ` satisfacible:
   `log₂ (costo cerrado) ≤ kt ≤ log₂ (costo cerrado) + 1` y `kt ≤ log₂ (costo de Levin) < kt + 3`. La cota
   `kt ≤ log₂ (costo de Levin)` (`kt_le_log_levin`) es nueva: la primera ronda que entrega algo lo entrega de un proceso
   `(i, 2^(t-i))` con `i + (t - i) = t`, y la búsqueda ya repartió `2^t`. En forma de costos:
   `costo cerrado ≤ 2^kt` y `costo de Levin < 8 · 2^kt` (`cerrado_sat`, `levin_sat`).
3. **Todo resolvedor da una cota de `kt`** (`kt_de_proceso`, `kt_de_programa`): si `(i, k)` resuelve `φ`,
   `kt ≤ i + ⌈log₂ k⌉`; para un `Code` real, con su costo de Blum de presupuesto (vía `correr_de_eval` y
   `programa_no_baja`).
4. **La equivalencia** (`facil_iff_kt`, `facilLevin_iff_kt`), con constantes explícitas: existe `C, d` con
   `costo ≤ C · (n+2)^d` para toda `φ` satisfacible, si y solo si existe `c` con `kt ≤ c · log₂ (n+2)`, con
   `n = encode φ`. Valen igual con el costo cerrado y con el de la búsqueda de Levin.
5. **La escala fina** (`facilLectura_iff_kt`, `facilLevinLectura_iff_kt`): `costo ≤ C · (n+2) · (bits+2)^d` si y solo si
   `kt ≤ bits + c · log₂ (bits+2)`, con `bits = log₂ (n+2)`.
6. **Controles.**
   * (i) **Familia fácil** (`negativa_facil`): si toda cláusula tiene un literal negativo, el programa `0` (`Code.zero`,
     que escribe `0 = encode []`, la asignación todo-falso) la resuelve con presupuesto `n + 1`: un proceso concreto, `i`
     fijo, `k` lineal. Ahí `log₂ n ≤ kt ≤ ⌈log₂ (n+1)⌉` y `costo cerrado ≤ n + 1`: la familia está en el piso.
   * (ii) **El palomar** (`palomar_fuera`): no es resoluble, su `kt` y su costo cerrado valen `0` **por convención**
     (`sInf ∅`), y el «no» se paga en la tercera cuenta, al menos `2^(n/24)` (`terceraCuenta_palomar`).
   * (iii) **`kt` no es trivial** (`bits_le_kt`, `kt_no_acotado`, `kt_no_constante`): `bits ≤ kt + 1` para toda
     fórmula satisfacible, así que `kt` no está acotada y no es constante. La cota inferior viene de la **lectura**
     (`evaln_bound`: el presupuesto supera a la entrada), no de un conteo: el conteo de procesos con `i + log k ≤ K`
     (a lo sumo `2^(K+1)` pares `(i, ⌈log₂ k⌉)`) no se aplica a una fórmula sola, porque cada proceso lee `φ`.

## La escala del «tamaño», y por qué

`encode φ` es un **número**, no su largo. Se probó que en esta medida la lectura cuesta el valor de la entrada:
`log₂ (encode φ) ≤ kt` (`log_x_le_kt`) y por lo tanto `costo ≥ encode φ`. Consecuencia, probada
(`sin_escala_de_bits`): **no hay** `c` con `kt ≤ c · log₂ (bits + 2)`, ni siquiera para la familia fácil. La escala
«polinomial en los bits» está vacía para todo problema. Por eso hay dos escalas honestas:

* **La del número** (punto 4): `kt ≤ c · log₂ n`, es decir `costo ≤ poly(n) = 2^O(bits)`. Es la que pidió José. Es
  gruesa: en tiempo real, `2^O(bits)` ya alcanza para la fuerza bruta sobre las asignaciones (lectura, no se prueba
  aquí).
* **La fina** (punto 5): `kt ≤ bits + O(log bits)`, es decir `costo ≤ n · poly(bits)`: la lectura unaria, que nadie
  evita, por un polinomio en los bits. Es la que corresponde a «SAT en tiempo polinomial» dentro de esta medida.

## La lectura para SAT

* **La información de la solución ya está en `φ`.** Una fórmula satisfacible determina sus soluciones; no hay nada que
  agregar desde afuera (ni consejo, ni tabla: el universo es cerrado). Lo que cuesta es **extraerla**: correr un programa
  corto el tiempo suficiente.
* **El costo de buscar es `2^kt`, salvo constantes**: `costo cerrado ∈ [2^(kt-1), 2^kt]` y
  `costo de Levin ∈ [2^kt, 2^(kt+3))`. La búsqueda universal no pierde más que `3` bits contra el mejor proceso.
* **«SAT es fácil en el universo cerrado» si y solo si `kt` es logarítmica**: en la escala del número, `kt = O(log n)`;
  en la fina, `kt = bits + O(log bits)`. La pregunta queda como una sola cantidad por fórmula, `ktSAT φ`, y el
  «exceso» sobre la lectura, `kt − bits`, es la profundidad de la solución.

## Lo que NO se prueba

* **Esto no es P contra NP.** Las medidas son el presupuesto de `evaln` y las rondas de la búsqueda, no tiempo de
  máquina. Ni siquiera la «escala fina» es tiempo polinomial: el presupuesto de `evaln` no está comparado con pasos de una
  máquina de Turing (ver `Levin.lean`).
* **De memoria, no se prueba aquí:** con la medida de tiempo real, la misma equivalencia es la de Levin: «la búsqueda en
  SAT es polinomial si y solo si las soluciones de SAT tienen `Kt` condicional `O(log n)` dada la fórmula». Es lectura.
* **El verificador no se cobra.** `vSAT` se evalúa gratis dentro de la búsqueda y en la definición de proceso correcto,
  como en `UniversoCerrado.lean`. Para SAT verificar es barato, pero aquí no se mide: no se usó
  `VerificadorPagado.lean`, que cobra el verificador como programa (`UniversoPagado`), y no se probó cuánto costaría
  `vSAT` como `Code`. Por eso todo esto **relativiza**.
* Nada sobre `P` contra `NP`, ni sobre `NP` contra `coNP` (el «no» del palomar se paga en otra cuenta).
* La invariancia respecto de la máquina universal (cambia `kt` en una constante aditiva; de memoria).

## Fuente, de memoria

L. A. Levin, «Universal sequential search problems», *Problemy Peredachi Informatsii* 9(3), 1973. No la leí en esta
sesión; las pruebas son propias y usan `UniversoCerrado.lean`, `Levin.lean`, `CorteRacional.lean` y
`TerceraCuenta.lean`.
-/

open Cslib Cslib.Logic.PL
open Nat.Partrec Nat.Partrec.Code
namespace Sagitta.Map.Tiempo.KtSAT
open UniversoCerrado TerceraCuenta Sagitta.Map.Levin

/-! ## 1. El verificador de SAT como función de `ℕ` -/

/-- **El verificador de SAT como función de `ℕ`.** `x` se decodifica como una fórmula CNF (`List Clausula`, la de
`ArbolElecciones.lean` y `TerceraCuenta.lean`, que es `CNF ℕ` de cslib-frontier) y `y` como una asignación (`List Bool`,
leída con `asigDeLista`: la variable `v` vale `y[v]`, falso fuera de la lista). Devuelve `CNF.eval`. Si `x` o `y` no
decodifican, `false`. -/
def vSAT (x y : ℕ) : Bool :=
  match Encodable.decode (α := List Clausula) x, Encodable.decode (α := List Bool) y with
  | some F, some σ => CNF.eval (asigDeLista σ) (F : CNF ℕ)
  | _, _ => false

/-- `Clause.eval` escrito como `foldr`, para probar que es primitivo recursivo. -/
def evalClaus (σ : List Bool) (c : Clausula) : Bool :=
  c.foldr (fun l acc => (σ.getD l.1 false == l.2) || acc) false

/-- `CNF.eval` escrito como `foldr`. -/
def evalForm (σ : List Bool) (F : List Clausula) : Bool :=
  F.foldr (fun c acc => evalClaus σ c && acc) true

/-- El `foldr` es `CNF.eval` con `asigDeLista`. -/
theorem evalForm_eq (σ : List Bool) (F : List Clausula) :
    evalForm σ F = CNF.eval (asigDeLista σ) (F : CNF ℕ) := by
  have hc : ∀ c : Clausula, evalClaus σ c = Clause.eval (asigDeLista σ) c := by
    intro c; induction c with
    | nil => rfl
    | cons l c ih => simp [evalClaus, Clause.eval, Literal.eval, asigDeLista] at ih ⊢; rw [ih]
  induction F with
  | nil => rfl
  | cons c F ih => simp [evalForm, CNF.eval] at ih ⊢; rw [hc, ih]

/-- Evaluar una cláusula es primitivo recursivo. -/
theorem primrec_evalClaus : Primrec₂ evalClaus := by
  have h := Primrec.list_foldr (f := fun q : List Bool × Clausula => q.2) (g := fun _ => false)
    (h := fun q (p : (ℕ × Bool) × Bool) => (q.1.getD p.1.1 false == p.1.2) || p.2)
    Primrec.snd (Primrec.const false)
    (Primrec.or.comp ((Primrec.dom_bool₂ (· == ·)).comp
      ((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun q => rfl


/-- Evaluar una fórmula es primitivo recursivo. -/
theorem primrec_evalForm : Primrec₂ evalForm := by
  have h := Primrec.list_foldr (f := fun q : List Bool × List Clausula => q.2) (g := fun _ => true)
    (h := fun q (p : Clausula × Bool) => evalClaus q.1 p.1 && p.2)
    Primrec.snd (Primrec.const true)
    (Primrec.and.comp (primrec_evalClaus.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun q => rfl

/-- `vSAT` como composición de `decode`, `Option.bind`, `Option.map` y `evalForm`. -/
theorem vSAT_eq (x y : ℕ) : vSAT x y =
    ((Encodable.decode (α := List Clausula) x).bind fun F =>
      (Encodable.decode (α := List Bool) y).map fun σ => evalForm σ F).getD false := by
  unfold vSAT
  cases Encodable.decode (α := List Clausula) x <;> cases Encodable.decode (α := List Bool) y <;>
    simp [evalForm_eq]

/-- **El verificador de SAT es primitivo recursivo**: lo que pide `levin_es_programa`. Toda la maquinaria de
`UniversoCerrado.lean` se aplica, incluida la que necesita `Primrec₂ V`. -/
theorem primrec_vSAT : Primrec₂ vSAT := by
  have h1 : Primrec fun q : ℕ × ℕ => Encodable.decode (α := List Clausula) q.1 :=
    Primrec.decode.comp Primrec.fst
  have h2 : Primrec₂ fun (q : ℕ × ℕ) (F : List Clausula) =>
      (Encodable.decode (α := List Bool) q.2).map fun σ => evalForm σ F :=
    Primrec.option_map (Primrec.decode.comp (Primrec.snd.comp Primrec.fst))
      (primrec_evalForm.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  have h3 := Primrec.option_getD.comp (Primrec.option_bind h1 h2) (Primrec.const false)
  exact (h3.of_eq fun q => (vSAT_eq q.1 q.2).symm).to₂


/-- Sobre codificaciones, `vSAT` es `CNF.eval`. -/
theorem vSAT_encode (F : List Clausula) (σ : List Bool) :
    vSAT (Encodable.encode F) (Encodable.encode σ) = CNF.eval (asigDeLista σ) (F : CNF ℕ) := by
  simp [vSAT, Encodable.encodek]

/-- Lo que `vSAT` acepta es una asignación (finita) que satisface la fórmula. -/
theorem vSAT_true {F : List Clausula} {y : ℕ} (h : vSAT (Encodable.encode F) y = true) :
    ∃ σ : List Bool, CNF.eval (asigDeLista σ) (F : CNF ℕ) = true := by
  unfold vSAT at h
  rw [Encodable.encodek] at h
  cases hy : Encodable.decode (α := List Bool) y with
  | none => rw [hy] at h; exact absurd h (by simp)
  | some σ => rw [hy] at h; exact ⟨σ, h⟩

/-- La fórmula tiene solución, con la definición de cslib-frontier (`CNF.Satisfiable`, asignaciones `ℕ → Bool`). -/
def Satisfacible (F : List Clausula) : Prop := CNF.Satisfiable (F : CNF ℕ)

/-- La evaluación solo depende de las variables que aparecen. -/
theorem eval_congr {σ τ : ℕ → Bool} {F : List Clausula} (h : ∀ c ∈ F, ∀ l ∈ c, σ l.1 = τ l.1) :
    CNF.eval σ (F : CNF ℕ) = CNF.eval τ (F : CNF ℕ) := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    have hc : Clause.eval σ c = Clause.eval τ c := by
      have hc' : ∀ l ∈ c, σ l.1 = τ l.1 := h c (List.mem_cons_self ..)
      clear h ih
      induction c with
      | nil => rfl
      | cons l c ihc =>
        simp only [Clause.eval, List.any_cons, Literal.eval] at ihc ⊢
        rw [hc' l (List.mem_cons_self ..), ihc fun l' hl' => hc' l' (List.mem_cons_of_mem _ hl')]
    simp only [CNF.eval, List.all_cons] at ih ⊢
    rw [hc, ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]

/-- **Basta una asignación finita.** Una fórmula satisfacible tiene una solución en `List Bool`: la restricción de
cualquier solución a las variables `0, …, N`, con `N` la suma de las variables que aparecen. -/
theorem satisfacible_iff (F : List Clausula) :
    Satisfacible F ↔ ∃ σ : List Bool, CNF.eval (asigDeLista σ) (F : CNF ℕ) = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.range ((F.flatten.map Prod.fst).sum + 1)).map σ, ?_⟩
    rw [← hσ]
    refine eval_congr fun c hc l hl => ?_
    have hle : l.1 ≤ (F.flatten.map Prod.fst).sum :=
      List.le_sum_of_mem (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩)
    have hlt : l.1 < (F.flatten.map Prod.fst).sum + 1 := by omega
    show ((List.range ((F.flatten.map Prod.fst).sum + 1)).map σ).getD l.1 false = σ l.1
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]; rfl
  · rintro ⟨σ, h⟩
    exact ⟨_, h⟩

/-- **El universo de SAT** sobre la fórmula `F`: el verificador `vSAT` y la entrada `encode F` (la misma codificación
que usa `TerceraCuenta.CorrectoJ`). -/
def uSAT (F : List Clausula) : Universo := ⟨vSAT, Encodable.encode F⟩

/-- **El universo de `F` tiene solución si y solo si `F` es satisfacible.** Si es satisfacible, el programa constante
que escribe una solución finita es un proceso cerrado correcto (`correr_universal`). -/
theorem resoluble_iff (F : List Clausula) : Resoluble (uSAT F) ↔ Satisfacible F := by
  rw [satisfacible_iff]
  constructor
  · rintro ⟨p, y, -, hV⟩
    exact vSAT_true hV
  · rintro ⟨σ, hσ⟩
    obtain ⟨i, hi⟩ := correr_universal (f := fun _ => Part.some (Encodable.encode σ))
      (Partrec.nat_iff.1 (Computable.const (Encodable.encode σ) : Computable fun _ : ℕ => Encodable.encode σ))
    obtain ⟨k, hk⟩ := (hi (Encodable.encode F) (Encodable.encode σ)).1 (Part.mem_some _)
    exact ⟨⟨i, k⟩, _, hk, by simp only [uSAT]; rw [vSAT_encode]; exact hσ⟩

/-- **La `kt` de una fórmula**: `min (i + ⌈log₂ k⌉)` sobre los procesos cerrados que entregan una asignación que la
satisface. Para una fórmula sin solución el conjunto es vacío y vale `0` por convención (`palomar_fuera`): los teoremas
piden `Satisfacible`. -/
noncomputable def ktSAT (F : List Clausula) : ℕ := kt (uSAT F)


/-! ## 2. La ley en bits, en las dos direcciones (para todo universo) -/

open AceleracionBlum CorteRacional

/-- **Costo `≤ 2^kt`**: el costo cerrado está debajo de `2^kt` (el proceso que realiza la `kt`). -/
theorem cerrado_le_pow_kt {U : Universo} (h : Resoluble U) : costoCerrado U ≤ 2 ^ kt U := by
  obtain ⟨p, hp, he⟩ := kt_alcanzado h
  rw [he]; exact le_trans (costoCerrado_le hp) (costoTotal_le_pow p)

/-- **Levin `< 8 · 2^kt`.** -/
theorem levin_lt_pow_kt {U : Universo} (h : Resoluble U) : costoLevin U.V U.x < 8 * 2 ^ kt U :=
  lt_of_lt_of_le (ley h).2 (Nat.mul_le_mul_left 8 (cerrado_le_pow_kt h))

/-- **La lectura es un piso**: `log₂ x ≤ kt`. Todo proceso correcto tiene presupuesto mayor que la entrada
(`evaln_bound`), así que `⌈log₂ k⌉ ≥ log₂ x`. En esta medida el presupuesto acota el **valor** de la entrada, no su
largo. -/
theorem log_x_le_kt {U : Universo} (h : Resoluble U) : Nat.log 2 U.x ≤ kt U := by
  obtain ⟨p, hp, he⟩ := kt_alcanzado h
  rw [he]
  have h1 : Nat.log 2 U.x ≤ Nat.log 2 p.k := Nat.log_mono_right hp.x_lt.le
  have h2 := Nat.log_le_clog 2 p.k
  omega

/-- Las rondas hasta la `T` reparten al menos `2^T` (la última ronda sola ya lo hace). -/
theorem pow_le_costoHasta (T : ℕ) : 2 ^ T ≤ costoHasta T := by
  have h1 : costoRonda T ≤ costoHasta T :=
    Finset.single_le_sum (f := costoRonda) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ T)
  have h2 := costoRonda_eq T
  rw [pow_succ] at h2
  omega

/-- **La otra punta de Levin: `kt ≤ log₂ (costo de Levin)`.** La primera ronda `T` que entrega algo lo entrega de un
programa `i ≤ t ≤ T` corrido con presupuesto `2^(t-i)`: eso es un proceso cerrado correcto con `i + ⌈log₂ 2^(t-i)⌉ = t`,
y la búsqueda ya repartió al menos `2^T`. Con `log_levin_lt_kt`, `kt ≤ log₂ costoLevin < kt + 3`: Levin mide la `kt`
salvo `3` bits. -/
theorem kt_le_log_levin {U : Universo} (h : Resoluble U) : kt U ≤ Nat.log 2 (costoLevin U.V U.x) := by
  classical
  have hex : ∃ T, (Levin.buscar U.V U.x T).isSome := by
    obtain ⟨p, y, hy, hV⟩ := h
    obtain ⟨y', hy'⟩ := buscar_halla (T := p.i + Nat.clog 2 p.k) hy hV le_rfl
    exact ⟨_, by rw [hy']; rfl⟩
  have hc : costoLevin U.V U.x = costoHasta (Nat.find hex) := by
    rw [costoLevin, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
  obtain ⟨t, ht, hr⟩ := List.exists_of_findSome?_eq_some hy
  obtain ⟨i, hi, hint⟩ := List.exists_of_findSome?_eq_some hr
  have ht' := List.mem_range.1 ht
  have hi' := List.mem_range.1 hi
  unfold Levin.intento at hint
  obtain ⟨hcorr, hV⟩ := Option.filter_eq_some_iff.1 hint
  have hk : kt U ≤ t := by
    have := kt_le (U := U) (p := ⟨i, 2 ^ (t - i)⟩) ⟨y, hcorr, hV⟩
    simp only [Nat.clog_pow 2 _ one_lt_two] at this
    omega
  rw [hc]
  refine le_trans hk (le_trans (by omega : t ≤ Nat.find hex) ?_)
  exact Nat.le_log_of_pow_le one_lt_two (pow_le_costoHasta _)


/-! ## 3. La `kt` de una fórmula: costo `≈ 2^kt` -/

/-- **(2a) Levin para SAT.** Si `F` es satisfacible, la búsqueda universal encuentra una asignación aceptada, y su costo
`c` cumple `c < 8 · 2^kt` y `kt ≤ log₂ c < kt + 3`. -/
theorem levin_sat {F : List Clausula} (h : Satisfacible F) :
    (∃ T y, Levin.buscar vSAT (Encodable.encode F) T = some y ∧ vSAT (Encodable.encode F) y = true) ∧
      costoLevin vSAT (Encodable.encode F) < 8 * 2 ^ ktSAT F ∧
      ktSAT F ≤ Nat.log 2 (costoLevin vSAT (Encodable.encode F)) ∧
      Nat.log 2 (costoLevin vSAT (Encodable.encode F)) < ktSAT F + 3 := by
  have hr := (resoluble_iff F).2 h
  exact ⟨(ley hr).1, levin_lt_pow_kt hr, kt_le_log_levin hr, log_levin_lt_kt hr⟩

/-- **El costo cerrado de SAT es `2^kt`, salvo un bit**: `costo ≤ 2^kt`, `kt ≤ log₂ costo + 1`; y la lectura es un piso,
`log₂ (encode F) ≤ kt`. -/
theorem cerrado_sat {F : List Clausula} (h : Satisfacible F) :
    costoCerrado (uSAT F) ≤ 2 ^ ktSAT F ∧ ktSAT F ≤ Nat.log 2 (costoCerrado (uSAT F)) + 1 ∧
      Nat.log 2 (Encodable.encode F) ≤ ktSAT F := by
  have hr := (resoluble_iff F).2 h
  exact ⟨cerrado_le_pow_kt hr, kt_le_log_cerrado hr, log_x_le_kt hr⟩

/-- **La ley para SAT, en una línea.** Para `F` satisfacible, `log₂ (costo cerrado) ≤ kt ≤ log₂ (costo cerrado) + 1`
y `kt ≤ log₂ (costo de Levin) < kt + 3`: buscar cuesta `2^kt`, salvo constantes, en las dos direcciones. -/
theorem ley_sat {F : List Clausula} (h : Satisfacible F) :
    Nat.log 2 (costoCerrado (uSAT F)) ≤ ktSAT F ∧ ktSAT F ≤ Nat.log 2 (costoCerrado (uSAT F)) + 1 ∧
      ktSAT F ≤ Nat.log 2 (costoLevin vSAT (Encodable.encode F)) ∧
      Nat.log 2 (costoLevin vSAT (Encodable.encode F)) < ktSAT F + 3 := by
  have hr := (resoluble_iff F).2 h
  exact ⟨log_cerrado_le_kt hr, kt_le_log_cerrado hr, kt_le_log_levin hr, log_levin_lt_kt hr⟩

/-- **(2b) Todo resolvedor da una cota de `kt`**: si el proceso `(i, k)` resuelve `F`, `ktSAT F ≤ i + ⌈log₂ k⌉`. -/
theorem kt_de_proceso {F : List Clausula} {p : Proceso} (h : Correcto (uSAT F) p) :
    ktSAT F ≤ p.i + Nat.clog 2 p.k := kt_le h

/-- **(2b) Con un `Code` real**: si el programa `c` entrega en `encode F` una asignación aceptada, `ktSAT F ≤ código de
c + ⌈log₂ (costo c)⌉`, con `costo` el costo de Blum (`pasos` de `evaln`); y `programa_no_baja`. -/
theorem kt_de_programa {F : List Clausula} {c : Code} {y : ℕ} (h : y ∈ eval c (Encodable.encode F))
    (hV : vSAT (Encodable.encode F) y = true) :
    ktSAT F ≤ encodeCode c + Nat.clog 2 (costo c (Encodable.encode F)) ∧
      costoCerrado (uSAT F) ≤ 2 ^ encodeCode c * costo c (Encodable.encode F) :=
  ⟨kt_le (U := uSAT F) (p := ⟨encodeCode c, costo c (Encodable.encode F)⟩) ⟨y, correr_de_eval h, hV⟩,
    programa_no_baja (V := vSAT) h hV⟩

/-- **La búsqueda de Levin para SAT es un programa**: un código `L`, uno solo para todas las fórmulas, que entrega solo
asignaciones aceptadas, termina en toda fórmula satisfacible, cuesta en rondas menos que `8 ·` el costo cerrado, y da
su propia cota de `kt`. Es `levin_es_programa` con `primrec_vSAT`. -/
theorem levin_es_programa_sat : ∃ L : Code,
    (∀ x y, y ∈ eval L x → vSAT x y = true) ∧
    ∀ F, Satisfacible F → (eval L (Encodable.encode F)).Dom ∧
      costoLevin vSAT (Encodable.encode F) < 8 * costoCerrado (uSAT F) ∧
      ktSAT F ≤ encodeCode L + Nat.clog 2 (costo L (Encodable.encode F)) := by
  obtain ⟨L, hL1, hL2⟩ := levin_es_programa primrec_vSAT
  refine ⟨L, hL1, fun F hF => ?_⟩
  obtain ⟨hd, h1, -⟩ := hL2 (Encodable.encode F) ((resoluble_iff F).2 hF)
  have hmem : (eval L (Encodable.encode F)).get hd ∈ eval L (Encodable.encode F) := Part.get_mem hd
  exact ⟨hd, h1, (kt_de_programa hmem (hL1 _ _ hmem)).1⟩


/-! ## 4. Aritmética de logaritmos -/

/-- `log₂ (a b) ≤ log₂ a + log₂ b + 1`. -/
theorem log_mul_le (a b : ℕ) : Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h1 := Nat.lt_pow_succ_log_self one_lt_two a
  have h2 := Nat.lt_pow_succ_log_self one_lt_two b
  have h3 : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    have : 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) = 2 ^ (Nat.log 2 a).succ * 2 ^ (Nat.log 2 b).succ := by
      rw [← pow_add]; congr 1; omega
    rw [this]; exact Nat.mul_lt_mul'' h1 h2
  have := Nat.log_lt_of_lt_pow (by positivity) h3
  omega

/-- `log₂ (a^d) ≤ d (log₂ a + 1)`. -/
theorem log_pow_le (a d : ℕ) : Nat.log 2 (a ^ d) ≤ d * (Nat.log 2 a + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ]
    have := log_mul_le (a ^ d) a
    rw [Nat.succ_mul]; omega

/-- `1 ≤ log₂ (n + 2)`. -/
theorem uno_le_log (n : ℕ) : 1 ≤ Nat.log 2 (n + 2) :=
  Nat.le_log_of_pow_le one_lt_two (by omega)

/-- De una cota de `kt` a una de costo: `t ≤ c · log₂ (n+2) → 2^t ≤ (n+2)^c`. -/
theorem pow_le_de_kt {t c n : ℕ} (ht : t ≤ c * Nat.log 2 (n + 2)) : 2 ^ t ≤ (n + 2) ^ c := by
  calc 2 ^ t ≤ 2 ^ (c * Nat.log 2 (n + 2)) := Nat.pow_le_pow_right (by norm_num) ht
    _ = (2 ^ Nat.log 2 (n + 2)) ^ c := by rw [mul_comm, pow_mul]
    _ ≤ (n + 2) ^ c := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) c

/-- De una cota de costo a una de `kt`: si `t ≤ log₂ m + 1` y `m ≤ C (n+2)^d`, entonces
`t ≤ (log₂ C + 2d + 3) · log₂ (n+2)`. -/
theorem kt_le_de_costo {t m n C d : ℕ} (ht : t ≤ Nat.log 2 m + 1) (hm : m ≤ C * (n + 2) ^ d) :
    t ≤ (Nat.log 2 C + 2 * d + 3) * Nat.log 2 (n + 2) := by
  have h1 : Nat.log 2 m ≤ Nat.log 2 (C * (n + 2) ^ d) := Nat.log_mono_right hm
  have h2 := log_mul_le C ((n + 2) ^ d)
  have h3 := log_pow_le (n + 2) d
  have hL := uno_le_log n
  set L := Nat.log 2 (n + 2)
  set lC := Nat.log 2 C
  have h4 : (lC + 2 * d + 3) * L = lC * L + d * L + d * L + 3 * L := by ring
  have h5 : lC ≤ lC * L := Nat.le_mul_of_pos_right _ hL
  have h6 : d ≤ d * L := Nat.le_mul_of_pos_right _ hL
  have h7 : d * (L + 1) = d * L + d := by ring
  omega

/-- Con el factor de lectura: `t ≤ b + c · log₂ (b+2) → 2^t ≤ (n+2) (b+2)^c`, con `b = log₂ (n+2)`. -/
theorem pow_le_de_kt_lectura {t c n : ℕ}
    (ht : t ≤ Nat.log 2 (n + 2) + c * Nat.log 2 (Nat.log 2 (n + 2) + 2)) :
    2 ^ t ≤ (n + 2) * (Nat.log 2 (n + 2) + 2) ^ c := by
  calc 2 ^ t ≤ 2 ^ (Nat.log 2 (n + 2) + c * Nat.log 2 (Nat.log 2 (n + 2) + 2)) :=
        Nat.pow_le_pow_right (by norm_num) ht
    _ = 2 ^ Nat.log 2 (n + 2) * (2 ^ Nat.log 2 (Nat.log 2 (n + 2) + 2)) ^ c := by
        rw [pow_add, mul_comm c, pow_mul]
    _ ≤ (n + 2) * (Nat.log 2 (n + 2) + 2) ^ c :=
        Nat.mul_le_mul (Nat.pow_log_le_self 2 (by omega))
          (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) c)

/-- Con el factor de lectura: si `t ≤ log₂ m + 1` y `m ≤ C (n+2) (b+2)^d`, entonces
`t ≤ b + (log₂ C + 2d + 3) · log₂ (b+2)`, con `b = log₂ (n+2)`. -/
theorem kt_le_de_costo_lectura {t m n C d : ℕ} (ht : t ≤ Nat.log 2 m + 1)
    (hm : m ≤ C * (n + 2) * (Nat.log 2 (n + 2) + 2) ^ d) :
    t ≤ Nat.log 2 (n + 2) + (Nat.log 2 C + 2 * d + 3) * Nat.log 2 (Nat.log 2 (n + 2) + 2) := by
  have h1 : Nat.log 2 m ≤ Nat.log 2 (C * (n + 2) * (Nat.log 2 (n + 2) + 2) ^ d) := Nat.log_mono_right hm
  have h2 := log_mul_le (C * (n + 2)) ((Nat.log 2 (n + 2) + 2) ^ d)
  have h2' := log_mul_le C (n + 2)
  have h3 := log_pow_le (Nat.log 2 (n + 2) + 2) d
  have hL := uno_le_log (Nat.log 2 (n + 2))
  set L := Nat.log 2 (Nat.log 2 (n + 2) + 2)
  set lC := Nat.log 2 C
  have h4 : (lC + 2 * d + 3) * L = lC * L + d * L + d * L + 3 * L := by ring
  have h5 : lC ≤ lC * L := Nat.le_mul_of_pos_right _ hL
  have h6 : d ≤ d * L := Nat.le_mul_of_pos_right _ hL
  have h7 : d * (L + 1) = d * L + d := by ring
  omega


/-! ## 5. La equivalencia: SAT fácil si y solo si `kt` logarítmico -/

/-- **«SAT es fácil en el universo cerrado»**, escala del número: hay un polinomio (`C · (n+2)^d`, que acota a todo
polinomio en `n`) tal que toda fórmula satisfacible tiene costo cerrado a lo sumo ese polinomio en `n = encode F`. -/
def FacilCerrado : Prop :=
  ∃ C d : ℕ, ∀ F, Satisfacible F → costoCerrado (uSAT F) ≤ C * (Encodable.encode F + 2) ^ d

/-- Lo mismo con el costo de la búsqueda de Levin, en rondas. -/
def FacilLevin : Prop :=
  ∃ C d : ℕ, ∀ F, Satisfacible F → costoLevin vSAT (Encodable.encode F) ≤ C * (Encodable.encode F + 2) ^ d

/-- **«`kt` logarítmico»**: hay `c` con `ktSAT F ≤ c · log₂ (encode F + 2)` para toda `F` satisfacible. -/
def KtLogaritmico : Prop :=
  ∃ c : ℕ, ∀ F, Satisfacible F → ktSAT F ≤ c * Nat.log 2 (Encodable.encode F + 2)

/-- **(3) La equivalencia, costo cerrado**: SAT es fácil en el universo cerrado si y solo si toda fórmula satisfacible
tiene `kt` logarítmico. Constantes: de `C, d` sale `c = log₂ C + 2d + 3`; de `c` sale `C = 1, d = c`. -/
theorem facil_iff_kt : FacilCerrado ↔ KtLogaritmico := by
  constructor
  · rintro ⟨C, d, h⟩
    exact ⟨_, fun F hF => kt_le_de_costo (cerrado_sat hF).2.1 (h F hF)⟩
  · rintro ⟨c, h⟩
    exact ⟨1, c, fun F hF => by
      rw [one_mul]; exact le_trans (cerrado_sat hF).1 (pow_le_de_kt (h F hF))⟩

/-- **(3) La equivalencia, búsqueda de Levin**: la búsqueda universal de SAT es polinomial si y solo si `kt` es
logarítmico. De `c` sale `C = 8, d = c`. -/
theorem facilLevin_iff_kt : FacilLevin ↔ KtLogaritmico := by
  constructor
  · rintro ⟨C, d, h⟩
    exact ⟨_, fun F hF => kt_le_de_costo (by have := (levin_sat hF).2.2.1; omega) (h F hF)⟩
  · rintro ⟨c, h⟩
    exact ⟨8, c, fun F hF =>
      le_trans (levin_sat hF).2.1.le (Nat.mul_le_mul_left 8 (pow_le_de_kt (h F hF)))⟩

/-- Los bits de la fórmula codificada, `log₂ (encode F + 2)`. -/
def bitsDe (F : List Clausula) : ℕ := Nat.log 2 (Encodable.encode F + 2)

/-- **La escala fina**: costo `≤ C · (n+2) · (bits+2)^d`. El factor `n+2` es la lectura, que esta medida cobra en
unario (`log_x_le_kt`) y nadie evita; lo que sobra es polinomial en los bits. -/
def FacilCerradoLectura : Prop :=
  ∃ C d : ℕ, ∀ F, Satisfacible F →
    costoCerrado (uSAT F) ≤ C * (Encodable.encode F + 2) * (bitsDe F + 2) ^ d

/-- Lo mismo con el costo de Levin. -/
def FacilLevinLectura : Prop :=
  ∃ C d : ℕ, ∀ F, Satisfacible F →
    costoLevin vSAT (Encodable.encode F) ≤ C * (Encodable.encode F + 2) * (bitsDe F + 2) ^ d

/-- **`kt` = lectura + logarítmico en los bits**: `ktSAT F ≤ bits + c · log₂ (bits + 2)`. -/
def KtLectura : Prop :=
  ∃ c : ℕ, ∀ F, Satisfacible F → ktSAT F ≤ bitsDe F + c * Nat.log 2 (bitsDe F + 2)

/-- **(3) La equivalencia en la escala fina, costo cerrado**: costo `≤ n · poly(bits)` si y solo si
`kt ≤ bits + O(log bits)`. -/
theorem facilLectura_iff_kt : FacilCerradoLectura ↔ KtLectura := by
  constructor
  · rintro ⟨C, d, h⟩
    exact ⟨_, fun F hF => kt_le_de_costo_lectura (cerrado_sat hF).2.1 (h F hF)⟩
  · rintro ⟨c, h⟩
    exact ⟨1, c, fun F hF => by
      rw [one_mul]; exact le_trans (cerrado_sat hF).1 (pow_le_de_kt_lectura (h F hF))⟩

/-- **(3) La equivalencia en la escala fina, Levin.** -/
theorem facilLevinLectura_iff_kt : FacilLevinLectura ↔ KtLectura := by
  constructor
  · rintro ⟨C, d, h⟩
    exact ⟨_, fun F hF => kt_le_de_costo_lectura (by have := (levin_sat hF).2.2.1; omega) (h F hF)⟩
  · rintro ⟨c, h⟩
    refine ⟨8, c, fun F hF => ?_⟩
    have := Nat.mul_le_mul_left 8 (pow_le_de_kt_lectura (h F hF))
    rw [← mul_assoc] at this
    exact le_trans (levin_sat hF).2.1.le this

/-! ## 6. Controles -/

/-- `log₂ (n + 2) ≤ log₂ n + 1`. -/
theorem log_add_two_le (n : ℕ) : Nat.log 2 (n + 2) ≤ Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Nat.log 2 2 < 2 := Nat.log_lt_of_lt_pow (by norm_num) (by norm_num)
    simp only [zero_add, Nat.log_zero_right]; omega
  have h1 := Nat.lt_pow_succ_log_self one_lt_two n
  have h2 := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 hn)
  have h3 : n + 2 < 2 ^ (Nat.log 2 n + 2) := by
    rw [pow_succ, pow_succ]; rw [pow_succ] at h1; omega
  have := Nat.log_lt_of_lt_pow (by omega) h3
  omega

/-- **(4iii) Cota inferior de `kt`**: `bits ≤ kt + 1` para toda fórmula satisfacible. No viene de un conteo sino de la
lectura (`log_x_le_kt`). -/
theorem bits_le_kt {F : List Clausula} (h : Satisfacible F) : bitsDe F ≤ ktSAT F + 1 := by
  have := (cerrado_sat h).2.2
  have := log_add_two_le (Encodable.encode F)
  unfold bitsDe; omega

/-- **(4i) Una familia fácil**: toda cláusula tiene un literal negativo. La asignación todo-falso (`[]`, codificada
como `0`) la satisface, y el programa `0` (`Code.zero`) la escribe. -/
def TodaNegativa (F : List Clausula) : Prop := ∀ c ∈ F, ∃ v, (v, false) ∈ c

/-- La asignación todo-falso satisface toda fórmula de la familia. -/
theorem eval_todo_falso {F : List Clausula} (h : TodaNegativa F) :
    CNF.eval (asigDeLista []) (F : CNF ℕ) = true := by
  simp only [CNF.eval, List.all_eq_true]
  intro c hc
  obtain ⟨v, hv⟩ := h c hc
  simp only [Clause.eval, List.any_eq_true]
  exact ⟨(v, false), hv, by simp [asigDeLista]⟩

/-- El programa `0` entrega `0` con presupuesto `x + 1`. -/
theorem correr_cero_entrega (x : ℕ) : correr 0 (x + 1) x = some 0 := by
  have h0 : (ofNatCode 0 : Code) = Code.zero := by simp [ofNatCode]
  unfold correr; rw [h0]; simp [evaln]

/-- El proceso `(0, encode F + 1)` resuelve toda fórmula de la familia: `i` fijo, `k` lineal en `n`. -/
theorem correcto_negativa {F : List Clausula} (h : TodaNegativa F) :
    Correcto (uSAT F) ⟨0, Encodable.encode F + 1⟩ := by
  refine ⟨0, correr_cero_entrega _, ?_⟩
  show vSAT (Encodable.encode F) 0 = true
  have : (0 : ℕ) = Encodable.encode ([] : List Bool) := Encodable.encode_list_nil.symm
  rw [this, vSAT_encode]; exact eval_todo_falso h

/-- **(4i) La familia fácil está en el piso.** Para toda fórmula con un literal negativo en cada cláusula:
`costo cerrado ≤ n + 1`, Levin `< 8 (n + 1)` y `log₂ n ≤ kt ≤ ⌈log₂ (n+1)⌉`: la `kt` es la de la lectura, y nada más. -/
theorem negativa_facil {F : List Clausula} (h : TodaNegativa F) :
    Satisfacible F ∧ costoCerrado (uSAT F) ≤ Encodable.encode F + 1 ∧
      ktSAT F ≤ Nat.clog 2 (Encodable.encode F + 1) ∧ Nat.log 2 (Encodable.encode F) ≤ ktSAT F ∧
      costoLevin vSAT (Encodable.encode F) < 8 * (Encodable.encode F + 1) := by
  have hc := correcto_negativa h
  have hs : Satisfacible F := (resoluble_iff F).1 ⟨_, hc⟩
  have h1 := costoCerrado_le hc
  have h2 := kt_le hc
  have h3 := levin_contra_proceso hc
  simp only [Proceso.costoTotal, pow_zero, one_mul, zero_add] at h1 h2 h3
  exact ⟨hs, h1, h2, (cerrado_sat hs).2.2, h3⟩

/-- La codificación de `[[(m, b)]]` es al menos `m`. -/
theorem le_encode_unitaria (m : ℕ) (b : Bool) : m ≤ Encodable.encode ([[(m, b)]] : List Clausula) := by
  rw [Encodable.encode_list_cons, Encodable.encode_list_cons, Encodable.encode_prod_val]
  calc m ≤ Nat.pair m (Encodable.encode b) := Nat.left_le_pair _ _
    _ ≤ Nat.pair (Nat.pair m (Encodable.encode b)) (Encodable.encode ([] : List (ℕ × Bool))) :=
        Nat.left_le_pair _ _
    _ ≤ _ := Nat.le_succ _
    _ ≤ Nat.pair _ (Encodable.encode ([] : List Clausula)) := Nat.left_le_pair _ _
    _ ≤ _ := Nat.le_succ _

/-- `[[(m, false)]]` está en la familia fácil. -/
theorem negativa_unitaria (m : ℕ) : TodaNegativa [[(m, false)]] := by
  intro c hc
  simp only [List.mem_singleton] at hc
  exact ⟨m, by simp [hc]⟩

/-- **(4iii) `kt` no está acotada**: para todo `K` hay una fórmula satisfacible (y fácil) con `kt > K`. -/
theorem kt_no_acotado (K : ℕ) : ∃ F, Satisfacible F ∧ K < ktSAT F := by
  refine ⟨[[(2 ^ (K + 1), false)]], (negativa_facil (negativa_unitaria _)).1, ?_⟩
  have h1 := (negativa_facil (negativa_unitaria (2 ^ (K + 1)))).2.2.2.1
  have h2 : K + 1 ≤ Nat.log 2 (Encodable.encode ([[(2 ^ (K + 1), false)]] : List Clausula)) :=
    Nat.le_log_of_pow_le one_lt_two (le_encode_unitaria _ _)
  omega

/-- **(4iii) `kt` no es constante**: hay dos fórmulas satisfacibles con `kt` distinta. -/
theorem kt_no_constante : ∃ F G, Satisfacible F ∧ Satisfacible G ∧ ktSAT F ≠ ktSAT G := by
  obtain ⟨G, hG, hlt⟩ := kt_no_acotado (ktSAT [])
  exact ⟨[], G, ⟨fun _ => true, rfl⟩, hG, hlt.ne⟩


/-- `L² ≤ 2^L` para `L ≥ 4`. -/
theorem cuadrado_le_pow {L : ℕ} (h : 4 ≤ L) : L * L ≤ 2 ^ L := by
  induction L, h using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    nlinarith

/-- **La escala ingenua de bits está vacía.** No hay `c` con `kt ≤ c · log₂ (bits + 2)` para toda fórmula satisfacible:
ni siquiera la familia fácil lo cumple, porque `kt ≥ bits − 1`. En esta medida «polinomial en los bits» es imposible
para todo problema, fácil o no; por eso la equivalencia se enuncia en la escala del número o en la fina. -/
theorem sin_escala_de_bits : ¬ ∃ c : ℕ, ∀ F, Satisfacible F → ktSAT F ≤ c * Nat.log 2 (bitsDe F + 2) := by
  rintro ⟨c, h⟩
  have hs := (negativa_facil (negativa_unitaria (2 ^ 2 ^ (c + 4)))).1
  have he := le_encode_unitaria (2 ^ 2 ^ (c + 4)) false
  generalize ([[(2 ^ 2 ^ (c + 4), false)]] : List Clausula) = F at hs he
  have h1 := h F hs
  have h2 := bits_le_kt hs
  have h3 : 2 ^ (c + 4) ≤ bitsDe F := Nat.le_log_of_pow_le one_lt_two (by omega)
  generalize bitsDe F = b at h1 h2 h3
  have h4 : c + 4 ≤ Nat.log 2 (b + 2) := Nat.le_log_of_pow_le one_lt_two (by omega)
  have h5 : 2 ^ Nat.log 2 (b + 2) ≤ b + 2 := Nat.pow_log_le_self 2 (by omega)
  generalize Nat.log 2 (b + 2) = L at h1 h4 h5
  have h6 := cuadrado_le_pow (by omega : 4 ≤ L)
  have h7 : (c + 4) * L ≤ L * L := Nat.mul_le_mul_right _ h4
  have h8 : (c + 4) * L = c * L + 4 * L := by ring
  omega

/-- **(4ii) El palomar no está en esta cuenta.** Su universo no es resoluble, así que `kt` y el costo cerrado valen `0`
por convención (no por ser fácil), y lo que cuesta el «no» se paga en la tercera cuenta: al menos `2^(n/24)`
(`TerceraCuenta.terceraCuenta_palomar`, Haken vía cslib-frontier). -/
theorem palomar_fuera (n : ℕ) :
    ¬ Resoluble (uSAT (formulaPal n)) ∧ ktSAT (formulaPal n) = 0 ∧ costoCerrado (uSAT (formulaPal n)) = 0 ∧
      ((2 ^ (n / 24) : ℕ) : ℕ∞) ≤ terceraCuenta (formulaPal n) := by
  have hno : ¬ Resoluble (uSAT (formulaPal n)) := fun h => palomar_insat n ((resoluble_iff _).1 h)
  have hvacio : ∀ p, ¬ Correcto (uSAT (formulaPal n)) p := fun p hp => hno ⟨p, hp⟩
  refine ⟨hno, ?_, ?_, terceraCuenta_palomar n⟩
  · unfold ktSAT kt
    have : {c | ∃ p, Correcto (uSAT (formulaPal n)) p ∧ c = p.i + Nat.clog 2 p.k} = ∅ :=
      Set.eq_empty_of_forall_notMem fun c ⟨p, hp, _⟩ => hvacio p hp
    rw [this, Nat.sInf_empty]
  · unfold costoCerrado
    have : {c | ∃ p, Correcto (uSAT (formulaPal n)) p ∧ c = p.costoTotal} = ∅ :=
      Set.eq_empty_of_forall_notMem fun c ⟨p, hp, _⟩ => hvacio p hp
    rw [this, Nat.sInf_empty]

end Sagitta.Map.Tiempo.KtSAT
