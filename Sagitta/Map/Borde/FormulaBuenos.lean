import Sagitta.Map.Borde.OscilacionParikh
import Sagitta.Map.Borde.Pratt
import Sagitta.Map.Borde.MarcoDeBits
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# `FormulaBuenos`, las piezas

`Borde/OscilacionParikh.lean` prueba `s12_no_demuestra_oscila`: si SAT oscila en circuitos, para toda fórmula acotada
`φ` que defina en ℕ a `Buenos satMarco c k`, S¹₂ no demuestra `∀ x ∃ y φ`. Le falta `FormulaBuenos c k`: que **exista**
esa fórmula. Sin ella el teorema puede ser vacío. Este archivo hace las piezas; el ensamble (escribir la `φ` con los
cuantificadores y probar `Define φ (Buenos satMarco c k)`) es el paso siguiente.

## El atajo

Desde el 25 nov `Σᵇ₁ = NP` está demostrado (`SigmaFagin.sigmaIgualNP`), así que no hace falta escribir a mano la
evaluación de circuitos en el lenguaje de Buss: basta poner cada relación en la NP de `Clases.lean` y sacar su fórmula,
como `Pratt.existe_formula_minFac` hizo con el gráfico de `minFac`. `Buenos` tiene la forma
`∃ C ∀ z (Eval(C, z) = 1 ↔ SAT(z))`, y cada pieza está en NP.

## Lo que se prueba

**1. Circuitos en bruto.** Un `Bruto` es `(n, [(op, a, b)], salida)`; `valor` calcula sus cables como `Shannon.paso`
(un cable todavía no calculado se lee `false`). `paso_eq` y `calcula_eq`: el circuito de `Shannon` y el bruto que le
coincide calculan lo mismo; `deCircuito` y `aCircuito` van y vuelven. **`sucNat_le_iff`**: `sucNat L m ≤ s` si y solo
si hay un bruto bien formado de `m` entradas y `≤ s` compuertas que calcula `L` en todo largo `m`. `existe_bruto_chico`:
el testigo puede tener operaciones de código `≤ 2`.

**2. Evaluar con certificado.** El certificado es la lista de los valores de los cables; `revisa` lo revisa compuerta
por compuerta (una conjunción sobre las compuertas, sin pliegue). `revisa_valor` (corrección: un certificado aceptado es
el honesto), `revisa_certificado` (completitud), **`verifEval_iff`**: hay certificado de largo `n + s` que muestra `b`
si y solo si el circuito está bien formado, la entrada tiene `n` bits y el circuito da `b`.

**3. En tiempo polinomial.** Con cables, operaciones y entradas en unario (`encBruto`), `valido_poly`, `revisa_poly`,
`verifEval_poly`: la revisión es polinomial en cslib-frontier.

**4. Los números como códigos.** `palabraNum c` son los bits de `c` sin el de arriba (`palabraNum (numeroDe u) = u`);
`circDe C` decodifica; el código canónico de `d` es `codigo d`. Tres relaciones, todas en NP:

* `evalCodB b C z` (**`evalProb_NP`**): `C` es código canónico de un bruto bien formado de `n` entradas, la palabra de
  `z` tiene `n` bits y el circuito da `b` en ella. Certificados de largo `|w| + 1` (`cablesTot_le`: el circuito cabe
  en su código; por eso se exige lo canónico).
* `formaCodB c k C y` (**`formaProb_NP`**, en P): `C` es código canónico de un bruto bien formado con `|y|` entradas y
  `≤ c·(|y|+1)^k` compuertas.
* **`satMarco_NP`**: SAT enmarcado está en NP (y `noSatMarco_coNP`). Es lo que `CookS12.lean` dejaba abierto para
  `satBits`: reconocer los códigos canónicos de CNF en tiempo polinomial, con el decodificador de cslib-frontier.

**5. `Buenos` con códigos.** **`buenos_iff_codigos`**: `Buenos satMarco c k x y` si y solo si `|x| ≤ |y|` y hay `C` con
`formaCodB c k C y` tal que, para toda `z` con `|z| = |y| + 1`, `evalCodB true C z ↔ satMarco (palabraNum z)`.
**`buenos_iff_acotado`**: lo mismo con los cuantificadores acotados, `|C| ≤ cotaCodigo c k y = 18·(|y| + c(|y|+1)^k +
1)²` (`largo_encBruto_le`) y `z ≤ 4y + 1` (`le_de_size`).

**6. Las fórmulas.** `esAcotada_de_sigma`, `esAcotada_de_pi`: `Σᵇ₁` y `Πᵇ₁` son acotadas (`EsAcotada`). Por
`existe_formula_par` (`Σᵇ₁ = NP` y `Pratt.formulaPar`): **`existe_formula_eval`**, **`existe_formula_forma`** (fórmulas
`Σᵇ₁` de dos variables con el gráfico exacto) y **`existe_formula_sat`** (una variable, para `z ≥ 1`).
`piezas_acotadas` las junta en la forma que usa `parikh_existe`.

## Lo que no

* **El ensamble.** Falta escribir `φ(x, y) = |x| ≤ |y| ∧ ∃ C ≤ t(y) [φ_forma(C, y) ∧ ∀ z ≤ 4y+1 (|z| = |y|+1 →
  (φ_eval(C, z) → φ_sat(z)) ∧ (φ_sat(z) → φ_eval(C, z)))]` con términos de Buss, la cota `t(y) ≥ 2^cotaCodigo`
  (con *smash*), y probar `Define φ (Buenos satMarco c k)` desde `buenos_iff_acotado`. Es el paso 2.
* La evaluación queda en NP con certificado, no en P: no hace falta para la fórmula (el uso negativo de `Eval = 1` se
  escribe como `Eval = 0`, que también es NP, o como la negación de una `Σᵇ₁`, que es acotada).
* Nada nuevo: es la ingeniería que Bydžovský, Krajíček y Oliveira (2020) dan por hecha. Lo propio es tenerla en Lean.
-/

namespace Sagitta.Map.Borde.FormulaBuenos

open Sagitta.Map Sagitta.Map.Shannon Sagitta.Map.Tiempo.Finitud

/-! ## 1. Los circuitos en bruto -/

/-- **Un circuito en bruto**: el número de entradas `n`, la lista de compuertas `(op, a, b)` y el cable de salida. Los
cables `0, …, n−1` son las entradas; la compuerta `k` escribe el cable `n + k`. -/
abbrev Bruto := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- La operación de un código: `0` es «y», `1` es «o», lo demás es «no». -/
def opDe : ℕ → Op
  | 0 => .y
  | 1 => .o
  | _ => .no

/-- El código de una operación. -/
def opCod : Op → ℕ
  | .y => 0
  | .o => 1
  | .no => 2

theorem opDe_opCod (op : Op) : opDe (opCod op) = op := by cases op <;> rfl

/-- `opDe o` aplicada, escrita con `if` (la forma que se calcula en tiempo polinomial). -/
def aplicaCod (op : ℕ) (a b : Bool) : Bool := if op = 0 then a && b else if op = 1 then a || b else !a

theorem aplicaCod_eq (op : ℕ) (a b : Bool) : aplicaCod op a b = (opDe op).aplica a b := by
  rcases op with _ | _ | op <;> rfl

/-- El total de cables, `n + s`. -/
def cablesTot (d : Bruto) : ℕ := d.1 + d.2.1.length

/-- **Bien formado**: toda compuerta lee cables que existen, y la salida es un cable que existe. -/
def valido (d : Bruto) : Bool :=
  d.2.1.all (fun g => decide (g.2.1 < cablesTot d) && decide (g.2.2 < cablesTot d)) && decide (d.2.2 < cablesTot d)

/-- **El valor del cable `j`** sobre la entrada `x`: las entradas se leen de `x`; la compuerta `k` aplica su operación
a sus dos cables, leyendo `false` en los que todavía no se calcularon (los de índice `≥ n + k`), como `Shannon.paso`. -/
def valor (d : Bruto) (x : List Bool) (j : ℕ) : Bool :=
  if j < d.1 then x.getD j false
  else if h : j - d.1 < d.2.1.length then
    (opDe (d.2.1[j - d.1]).1).aplica
      (if h1 : (d.2.1[j - d.1]).2.1 < j then valor d x (d.2.1[j - d.1]).2.1 else false)
      (if h2 : (d.2.1[j - d.1]).2.2 < j then valor d x (d.2.1[j - d.1]).2.2 else false)
  else false
termination_by j

/-- Lo que calcula un circuito en bruto: el valor de su cable de salida. -/
def evalBruto (d : Bruto) (x : List Bool) : Bool := valor d x d.2.2

theorem valor_lt {d : Bruto} {x : List Bool} {j : ℕ} (h : j < d.1) : valor d x j = x.getD j false := by
  rw [valor]; simp [h]

theorem valor_puerta {d : Bruto} {x : List Bool} {k : ℕ} (hk : k < d.2.1.length) :
    valor d x (d.1 + k) = (opDe (d.2.1[k]).1).aplica
      (if (d.2.1[k]).2.1 < d.1 + k then valor d x (d.2.1[k]).2.1 else false)
      (if (d.2.1[k]).2.2 < d.1 + k then valor d x (d.2.1[k]).2.2 else false) := by
  rw [valor]
  have e : d.1 + k - d.1 = k := by omega
  simp only [show ¬ d.1 + k < d.1 by omega, ↓reduceIte, e, hk, ↓reduceDIte, dite_eq_ite]

/-! ### Del circuito de `Shannon` al bruto, y de vuelta -/

/-- `C` y `d` describen el mismo circuito: mismas entradas, mismas compuertas (operación y cables) y misma salida. -/
structure Coinciden {n s : ℕ} (C : Circuito n s) (d : Bruto) : Prop where
  entradas : d.1 = n
  largo : d.2.1.length = s
  op : ∀ k : Fin s, (C.1 k).1 = opDe (d.2.1[k.val]'(by omega)).1
  a : ∀ k : Fin s, (C.1 k).2.1.val = (d.2.1[k.val]'(by omega)).2.1
  b : ∀ k : Fin s, (C.1 k).2.2.val = (d.2.1[k.val]'(by omega)).2.2
  salida : C.2.val = d.2.2

/-- **El paso de `Shannon` es el valor en bruto**: después de `m ≤ s` compuertas, el cable `w` vale lo que dice `valor`
si ya se calculó (`w < n + m`) y `false` si no. -/
theorem paso_eq {n s : ℕ} {C : Circuito n s} {d : Bruto} (h : Coinciden C d) (x : Fin n → Bool) :
    ∀ m ≤ s, ∀ w : Fin (n + s),
      paso C x m w = if w.val < n + m then valor d (List.ofFn x) w.val else false := by
  intro m
  induction m with
  | zero =>
    intro _ w
    simp only [paso, Nat.add_zero]
    by_cases hw : w.val < n
    · simp only [hw, ↓reduceDIte, ↓reduceIte]
      rw [valor_lt (by rw [h.entradas]; exact hw)]
      simp [List.getD_eq_getElem?_getD, hw]
    · simp only [hw, ↓reduceDIte, ↓reduceIte]
  | succ m ih =>
    intro hm w
    have hms : m < s := by omega
    rw [paso, dite_eq_left hms]
    have hk : m < d.2.1.length := by rw [h.largo]; exact hms
    by_cases hw : w = cableDe ⟨m, hms⟩
    · subst hw
      rw [Function.update_self]
      have e : (cableDe ⟨m, hms⟩ : Fin (n + s)).val = d.1 + m := by simp [cableDe, h.entradas]
      rw [ite_eq_left (by simp [cableDe]), e, valor_puerta hk, ih (by omega), ih (by omega), h.op ⟨m, hms⟩,
        h.a ⟨m, hms⟩, h.b ⟨m, hms⟩, h.entradas]
    · rw [Function.update_of_ne hw, ih (by omega)]
      have hne : w.val ≠ n + m := fun e => hw (Fin.ext (by simp [cableDe, e]))
      by_cases hlt : w.val < n + m
      · rw [ite_eq_left hlt, ite_eq_left (by omega)]
      · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- **Lo que calcula el circuito de `Shannon` es lo que calcula el bruto que le coincide.** -/
theorem calcula_eq {n s : ℕ} {C : Circuito n s} {d : Bruto} (h : Coinciden C d) (x : Fin n → Bool) :
    calcula C x = evalBruto d (List.ofFn x) := by
  rw [calcula, cables, paso_eq h x s le_rfl, ite_eq_left C.2.isLt, evalBruto, h.salida]

/-- El bruto de un circuito de `Shannon`. -/
def deCircuito {n s : ℕ} (C : Circuito n s) : Bruto :=
  (n, List.ofFn fun k => (opCod (C.1 k).1, (C.1 k).2.1.val, (C.1 k).2.2.val), C.2.val)

theorem coinciden_deCircuito {n s : ℕ} (C : Circuito n s) : Coinciden C (deCircuito C) where
  entradas := rfl
  largo := by simp [deCircuito]
  op k := by simp [deCircuito, opDe_opCod]
  a k := by simp [deCircuito]
  b k := by simp [deCircuito]
  salida := rfl

theorem valido_deCircuito {n s : ℕ} (C : Circuito n s) : valido (deCircuito C) = true := by
  simp only [valido, cablesTot, deCircuito, List.length_ofFn, Bool.and_eq_true, List.all_eq_true,
    List.mem_ofFn, decide_eq_true_eq]
  refine ⟨?_, C.2.isLt⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨(C.1 k).2.1.isLt, (C.1 k).2.2.isLt⟩

theorem valido_iff (d : Bruto) : valido d = true ↔
    (∀ g ∈ d.2.1, g.2.1 < cablesTot d ∧ g.2.2 < cablesTot d) ∧ d.2.2 < cablesTot d := by
  simp [valido]

/-- El circuito de `Shannon` de un bruto bien formado con `n` entradas. -/
def aCircuito (d : Bruto) (hv : valido d = true) : Circuito d.1 d.2.1.length :=
  (fun k => (opDe (d.2.1[k.val]).1,
      ⟨(d.2.1[k.val]).2.1, ((valido_iff d).1 hv).1 _ (List.getElem_mem _) |>.1⟩,
      ⟨(d.2.1[k.val]).2.2, ((valido_iff d).1 hv).1 _ (List.getElem_mem _) |>.2⟩),
    ⟨d.2.2, ((valido_iff d).1 hv).2⟩)

theorem coinciden_aCircuito (d : Bruto) (hv : valido d = true) : Coinciden (aCircuito d hv) d where
  entradas := rfl
  largo := rfl
  op _ := rfl
  a _ := rfl
  b _ := rfl
  salida := rfl

/-! ### La equivalencia con `sucNat` -/

/-- **El óptimo, con circuitos en bruto.** `sucNat L m ≤ s` si y solo si hay un circuito en bruto bien formado, con `m`
entradas y a lo sumo `s` compuertas, que calcula `L` en todas las entradas de largo `m`. Es la equivalencia que deja
escribir «hay un circuito de tamaño `≤ s`» con un cuantificador sobre números. -/
theorem sucNat_le_iff (L : Problema) (m s : ℕ) :
    sucNat L m ≤ s ↔ ∃ d : Bruto, valido d = true ∧ d.1 = m ∧ d.2.1.length ≤ s ∧
      ∀ x : List Bool, x.length = m → evalBruto d x = L x := by
  constructor
  · intro hs
    obtain ⟨t, ht, C, hC⟩ := MarcoDeBits.cabe_rebanada L m
    refine ⟨deCircuito C, valido_deCircuito C, rfl, by simp [deCircuito]; omega, fun x hx => ?_⟩
    subst hx
    have := congrFun hC (fun i => x[i.val])
    rw [calcula_eq (coinciden_deCircuito C), List.ofFn_getElem] at this
    rw [this, rebanada, List.ofFn_getElem]
  · rintro ⟨d, hv, rfl, hs, hL⟩
    refine MarcoDeBits.sucNat_le_de_cabe ⟨d.2.1.length, hs, aCircuito d hv, funext fun x => ?_⟩
    rw [calcula_eq (coinciden_aCircuito d hv), rebanada, hL _ (List.length_ofFn)]

/-- **El testigo es chico en sus códigos de operación**: el circuito de `sucNat_le_iff` se puede tomar con operaciones de
código `≤ 2` (el de un circuito de `Shannon`). Sirve para acotar el número que lo codifica. -/
theorem existe_bruto_chico {L : Problema} {m s : ℕ} (hs : sucNat L m ≤ s) :
    ∃ d : Bruto, valido d = true ∧ d.1 = m ∧ d.2.1.length ≤ s ∧ (∀ g ∈ d.2.1, g.1 ≤ 2) ∧
      ∀ x : List Bool, x.length = m → evalBruto d x = L x := by
  obtain ⟨t, ht, C, hC⟩ := MarcoDeBits.cabe_rebanada L m
  refine ⟨deCircuito C, valido_deCircuito C, rfl, by simp [deCircuito]; omega, ?_, fun x hx => ?_⟩
  · intro g hg
    simp only [deCircuito, List.mem_ofFn] at hg
    obtain ⟨k, rfl⟩ := hg
    cases (C.1 k).1 <;> simp [opCod]
  · subst hx
    have := congrFun hC (fun i => x[i.val])
    rw [calcula_eq (coinciden_deCircuito C), List.ofFn_getElem] at this
    rw [this, rebanada, List.ofFn_getElem]

/-! ## 2. Evaluar con certificado

No hace falta simular el circuito: el certificado es la lista de los valores de todos los cables, y se revisa compuerta
por compuerta (`revisa`). La revisión es local (cada compuerta mira dos posiciones del certificado), así que es una
conjunción sobre la lista de compuertas, sin pliegue. Un certificado aceptado es el único posible (`revisa_valor`). -/

/-- Leer el cable `a` antes de calcular el cable `t`: `false` si todavía no se calculó. -/
def lee (v : List Bool) (t a : ℕ) : Bool := if a < t then v.getD a false else false

/-- La compuerta `k`, con operación y cables `g`, está bien en el certificado `v`. -/
def puertaOK (d : Bruto) (v : List Bool) (gk : (ℕ × ℕ × ℕ) × ℕ) : Bool :=
  decide (v.getD (d.1 + gk.2) false =
    aplicaCod gk.1.1 (lee v (d.1 + gk.2) gk.1.2.1) (lee v (d.1 + gk.2) gk.1.2.2))

/-- **La revisión del certificado** `v` del circuito `d` en la entrada `x`: tiene un valor por cable, empieza con `x`, y
cada compuerta calcula su cable a partir de los anteriores. -/
def revisa (d : Bruto) (x v : List Bool) : Bool :=
  decide (v.length = cablesTot d) && decide (v.take d.1 = x) && d.2.1.zipIdx.all (puertaOK d v)

theorem mem_zipIdx_puerta (d : Bruto) {k : ℕ} (hk : k < d.2.1.length) : (d.2.1[k], k) ∈ d.2.1.zipIdx := by
  rw [List.mem_iff_getElem]
  exact ⟨k, by simpa using hk, by simp⟩

/-- **Corrección**: un certificado aceptado tiene en cada cable su valor. -/
theorem revisa_valor {d : Bruto} {x v : List Bool} (h : revisa d x v = true) :
    ∀ j < cablesTot d, v.getD j false = valor d x j := by
  simp only [revisa, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨_, htake⟩, hall⟩ := h
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjn : j < d.1
    · rw [valor_lt hjn, ← htake]
      simp [List.getD_eq_getElem?_getD, hjn]
    · obtain ⟨k, rfl⟩ : ∃ k, j = d.1 + k := ⟨j - d.1, by omega⟩
      have hk : k < d.2.1.length := by unfold cablesTot at hj; omega
      have hp := hall _ (mem_zipIdx_puerta d hk)
      simp only [puertaOK, decide_eq_true_eq] at hp
      rw [hp, valor_puerta hk, aplicaCod_eq]
      congr 1
      · simp only [lee]
        by_cases ha : (d.2.1[k]).2.1 < d.1 + k
        · rw [ite_eq_left ha, ite_eq_left ha]; exact ih _ ha (by omega)
        · rw [ite_eq_right ha, ite_eq_right ha]
      · simp only [lee]
        by_cases ha : (d.2.1[k]).2.2 < d.1 + k
        · rw [ite_eq_left ha, ite_eq_left ha]; exact ih _ ha (by omega)
        · rw [ite_eq_right ha, ite_eq_right ha]

/-- El certificado honesto: el valor de cada cable. -/
def certificado (d : Bruto) (x : List Bool) : List Bool := List.ofFn fun j : Fin (cablesTot d) => valor d x j

theorem getD_certificado {d : Bruto} {x : List Bool} {j : ℕ} (hj : j < cablesTot d) :
    (certificado d x).getD j false = valor d x j := by
  simp [certificado, List.getD_eq_getElem?_getD, hj]

/-- **Completitud**: si `x` tiene `n` bits, el certificado honesto pasa la revisión. -/
theorem revisa_certificado {d : Bruto} {x : List Bool} (hx : x.length = d.1) :
    revisa d x (certificado d x) = true := by
  simp only [revisa, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨by simp [certificado], ?_⟩, ?_⟩
  · apply List.ext_getElem (by simp [certificado, cablesTot, hx])
    intro i h1 h2
    have hi : i < d.1 := by rw [hx] at h2; exact h2
    rw [List.getElem_take, ← List.getD_eq_getElem (d := false), getD_certificado (by unfold cablesTot; omega),
      valor_lt hi, List.getD_eq_getElem]
  · rintro ⟨g, k⟩ hmem
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hmem
    simp only [List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hk : i < d.2.1.length := by simpa using hi
    simp only [puertaOK, decide_eq_true_eq]
    rw [getD_certificado (by unfold cablesTot; omega), valor_puerta hk, aplicaCod_eq]
    congr 1
    · simp only [lee]
      by_cases ha : (d.2.1[i]).2.1 < d.1 + i
      · rw [ite_eq_left ha, ite_eq_left ha, getD_certificado (by unfold cablesTot; omega)]
      · rw [ite_eq_right ha, ite_eq_right ha]
    · simp only [lee]
      by_cases ha : (d.2.1[i]).2.2 < d.1 + i
      · rw [ite_eq_left ha, ite_eq_left ha, getD_certificado (by unfold cablesTot; omega)]
      · rw [ite_eq_right ha, ite_eq_right ha]

/-- **El verificador de la evaluación**: el circuito está bien formado, el certificado pasa la revisión, y en el cable
de salida dice `b`. -/
def verifEval (b : Bool) (d : Bruto) (x v : List Bool) : Bool :=
  valido d && revisa d x v && decide (v.getD d.2.2 false = b)

/-- **La evaluación con certificado es exacta**: hay un certificado aceptado (y entonces uno de largo `n + s`) si y solo
si el circuito está bien formado, `x` tiene `n` bits y el circuito da `b` en `x`. -/
theorem verifEval_iff (b : Bool) (d : Bruto) (x : List Bool) :
    (∃ v, v.length = cablesTot d ∧ verifEval b d x v = true) ↔
      (valido d = true ∧ x.length = d.1 ∧ evalBruto d x = b) := by
  constructor
  · rintro ⟨v, -, hv⟩
    simp only [verifEval, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hval, hrev⟩, hout⟩ := hv
    have hrev' := hrev
    simp only [revisa, Bool.and_eq_true, decide_eq_true_eq] at hrev'
    obtain ⟨⟨hlen, htake⟩, -⟩ := hrev'
    refine ⟨hval, ?_, ?_⟩
    · rw [← htake, List.length_take, hlen]; unfold cablesTot; omega
    · rw [evalBruto, ← revisa_valor hrev _ ((valido_iff d).1 hval).2, hout]
  · rintro ⟨hval, hx, he⟩
    refine ⟨certificado d x, by simp [certificado], ?_⟩
    simp only [verifEval, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hval, revisa_certificado hx⟩, by rw [getD_certificado ((valido_iff d).1 hval).2, ← he]; rfl⟩

/-! ## 3. En tiempo polinomial

Los cables, las operaciones y el número de entradas van en unario: así leer el certificado en un índice es leer una
lista en un índice unario, y el código de un circuito de `n` entradas y `s` compuertas mide `O(s·(n + s))` bits, que
es polinomial. -/

section Poli

open Turing.MultiTapeTM

/-- La codificación de una compuerta: operación y cables en unario. -/
abbrev encPuerta : ℕ × ℕ × ℕ ↪ List Bool := encPair encUnary (encPair encUnary encUnary)

/-- **La codificación de un circuito en bruto**: entradas, compuertas y salida, todo en unario. -/
abbrev encBruto : Bruto ↪ List Bool := encPair encUnary (encPair (encList encPuerta) encUnary)

/-- Su decodificador (total). -/
def decBruto : Decoder encBruto :=
  Decoder.pair Decoder.unary
    (Decoder.pair (Decoder.list (Decoder.pair Decoder.unary (Decoder.pair Decoder.unary Decoder.unary)))
      Decoder.unary)

/-- Lo que revisa el verificador: el circuito, la entrada y el certificado. -/
abbrev encTerna : Bruto × List Bool × List Bool ↪ List Bool := encPair encBruto (encPair encBits encBits)

theorem cablesTot_poly : ComputableInPolyTime cablesTot encBruto encUnary := by
  unfold cablesTot
  have h1 : ComputableInPolyTime (fun d : Bruto => d.1) encBruto encUnary := by fun_prop
  have h2 : ComputableInPolyTime (fun d : Bruto => d.2.1) encBruto (encList encPuerta) := by fun_prop
  exact ComputableInPolyTime.unary_add' h1 ((ComputableInPolyTime.length_list encPuerta).comp h2)

theorem valido_poly : ComputableInPolyTime valido encBruto encBool := by
  unfold valido
  have hl : ComputableInPolyTime (fun d : Bruto => d.2.1) encBruto (encList encPuerta) := by fun_prop
  have hN := cablesTot_poly
  have htest : ComputableInPolyTime (fun p : Bruto × (ℕ × ℕ × ℕ) =>
      decide (p.2.2.1 < cablesTot p.1) && decide (p.2.2.2 < cablesTot p.1)) (encPair encBruto encPuerta) encBool := by
    have hN' := hN.comp (ComputableInPolyTime.fst encBruto encPuerta)
    have ha : ComputableInPolyTime (fun p : Bruto × (ℕ × ℕ × ℕ) => p.2.2.1) (encPair encBruto encPuerta) encUnary := by
      fun_prop
    have hb : ComputableInPolyTime (fun p : Bruto × (ℕ × ℕ × ℕ) => p.2.2.2) (encPair encBruto encPuerta) encUnary := by
      fun_prop
    exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.unary_lt' ha hN')
      (ComputableInPolyTime.unary_lt' hb hN')
  have hall := ComputableInPolyTime.allWithInput
    (test := fun (d : Bruto) (g : ℕ × ℕ × ℕ) => decide (g.2.1 < cablesTot d) && decide (g.2.2 < cablesTot d)) hl htest
  have hout : ComputableInPolyTime (fun d : Bruto => d.2.2) encBruto encUnary := by fun_prop
  exact ComputableInPolyTime.bool_and' hall (ComputableInPolyTime.unary_lt' hout hN)

theorem aplicaCod_poly : ComputableInPolyTime (fun p : ℕ × Bool × Bool => aplicaCod p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBool encBool)) encBool := by
  unfold aplicaCod
  have ho : ComputableInPolyTime (fun p : ℕ × Bool × Bool => p.1) (encPair encUnary (encPair encBool encBool))
      encUnary := by fun_prop
  have ha : ComputableInPolyTime (fun p : ℕ × Bool × Bool => p.2.1) (encPair encUnary (encPair encBool encBool))
      encBool := by fun_prop
  have hb : ComputableInPolyTime (fun p : ℕ × Bool × Bool => p.2.2) (encPair encUnary (encPair encBool encBool))
      encBool := by fun_prop
  exact ComputableInPolyTime.ite_decide (ComputableInPolyTime.decide_eq' ho (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.bool_and' ha hb)
    (ComputableInPolyTime.ite_decide (ComputableInPolyTime.decide_eq' ho (ComputableInPolyTime.const 1))
      (ComputableInPolyTime.bool_or' ha hb) (ComputableInPolyTime.bool_not.comp ha))

theorem lee_poly : ComputableInPolyTime (fun p : List Bool × ℕ × ℕ => lee p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encUnary encUnary)) encBool := by
  unfold lee
  have hv : ComputableInPolyTime (fun p : List Bool × ℕ × ℕ => p.1) (encPair encBits (encPair encUnary encUnary))
      encBits := by fun_prop
  have ht : ComputableInPolyTime (fun p : List Bool × ℕ × ℕ => p.2.1) (encPair encBits (encPair encUnary encUnary))
      encUnary := by fun_prop
  have ha : ComputableInPolyTime (fun p : List Bool × ℕ × ℕ => p.2.2) (encPair encBits (encPair encUnary encUnary))
      encUnary := by fun_prop
  exact ComputableInPolyTime.ite_decide (ComputableInPolyTime.unary_lt' ha ht)
    (ComputableInPolyTime.bitsGetDWithInput hv ha false) (ComputableInPolyTime.const false)

theorem puertaOK_poly : ComputableInPolyTime (fun p : (Bruto × List Bool × List Bool) × ((ℕ × ℕ × ℕ) × ℕ) =>
    puertaOK p.1.1 p.1.2.2 p.2) (encPair encTerna (encPair encPuerta encUnary)) encBool := by
  unfold puertaOK
  have hv : ComputableInPolyTime (fun p : (Bruto × List Bool × List Bool) × ((ℕ × ℕ × ℕ) × ℕ) => p.1.2.2)
      (encPair encTerna (encPair encPuerta encUnary)) encBits := by fun_prop
  have hn : ComputableInPolyTime (fun p : (Bruto × List Bool × List Bool) × ((ℕ × ℕ × ℕ) × ℕ) => p.1.1.1)
      (encPair encTerna (encPair encPuerta encUnary)) encUnary := by fun_prop
  have hk : ComputableInPolyTime (fun p : (Bruto × List Bool × List Bool) × ((ℕ × ℕ × ℕ) × ℕ) => p.2.2)
      (encPair encTerna (encPair encPuerta encUnary)) encUnary := by fun_prop
  have ho : ComputableInPolyTime (fun p : (Bruto × List Bool × List Bool) × ((ℕ × ℕ × ℕ) × ℕ) => p.2.1.1)
      (encPair encTerna (encPair encPuerta encUnary)) encUnary := by fun_prop
  have ha : ComputableInPolyTime (fun p : (Bruto × List Bool × List Bool) × ((ℕ × ℕ × ℕ) × ℕ) => p.2.1.2.1)
      (encPair encTerna (encPair encPuerta encUnary)) encUnary := by fun_prop
  have hb : ComputableInPolyTime (fun p : (Bruto × List Bool × List Bool) × ((ℕ × ℕ × ℕ) × ℕ) => p.2.1.2.2)
      (encPair encTerna (encPair encPuerta encUnary)) encUnary := by fun_prop
  have hnk := ComputableInPolyTime.unary_add' hn hk
  have hla := lee_poly.comp (hv.prod (hnk.prod ha))
  have hlb := lee_poly.comp (hv.prod (hnk.prod hb))
  have hap := aplicaCod_poly.comp (ho.prod (hla.prod hlb))
  exact ComputableInPolyTime.decide_eq' (ComputableInPolyTime.bitsGetDWithInput hv hnk false) hap

theorem revisa_poly : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => revisa e.1 e.2.1 e.2.2)
    encTerna encBool := by
  unfold revisa
  have hd : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => e.1) encTerna encBruto := by fun_prop
  have hx : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => e.2.1) encTerna encBits := by fun_prop
  have hv : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => e.2.2) encTerna encBits := by fun_prop
  have hn : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => e.1.1) encTerna encUnary := by fun_prop
  have hl : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => e.1.2.1) encTerna (encList encPuerta) := by
    fun_prop
  have c1 := ComputableInPolyTime.decide_eq' (ComputableInPolyTime.length_bits.comp hv) (cablesTot_poly.comp hd)
  have c2 := ComputableInPolyTime.decide_eq' (ComputableInPolyTime.bitsTakeWithInput hv hn) hx
  have hz := (ComputableInPolyTime.zipIdx encPuerta).comp hl
  have c3 := ComputableInPolyTime.allWithInput
    (test := fun (e : Bruto × List Bool × List Bool) (gk : (ℕ × ℕ × ℕ) × ℕ) => puertaOK e.1 e.2.2 gk) hz puertaOK_poly
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' c1 c2) c3

theorem verifEval_poly (b : Bool) :
    ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => verifEval b e.1 e.2.1 e.2.2) encTerna encBool := by
  unfold verifEval
  have hd : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => e.1) encTerna encBruto := by fun_prop
  have hv : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => e.2.2) encTerna encBits := by fun_prop
  have hout : ComputableInPolyTime (fun e : Bruto × List Bool × List Bool => e.1.2.2) encTerna encUnary := by fun_prop
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' (valido_poly.comp hd) revisa_poly)
    (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.bitsGetDWithInput hv hout false)
      (ComputableInPolyTime.const b))

end Poli

/-! ## 4. Los números como códigos

Un número `c ≥ 1` es `numeroDe u` para una única palabra `u` (sus bits sin el 1 de arriba, `palabraNum`). El código de
un circuito es un número `C` cuya palabra es la codificación **canónica** de un circuito en bruto (`encBruto (circDe C)
= palabraNum C`); exigir lo canónico hace que el tamaño del circuito acote el del código y al revés. -/

section Codigos

open Turing.MultiTapeTM

/-- La palabra de un número: sus bits (del menos significativo al más) sin el último. -/
def palabraNum (c : ℕ) : List Bool := (Nat.bits c).dropLast

theorem palabraNum_numeroDe (u : List Bool) : palabraNum (Acotada.numeroDe u) = u := by
  rw [palabraNum, Acotada.Pratt.numeroDe_eq_ofBits, bits_ofBits, List.rdropWhile_concat_neg _ u true (by simp),
    List.dropLast_concat]

theorem length_palabraNum (c : ℕ) : (palabraNum c).length = Nat.size c - 1 := by
  rw [palabraNum, List.length_dropLast, Nat.size_eq_bits_len]

theorem palabraNum_poly : ComputableInPolyTime palabraNum encNat encBits :=
  ComputableInDegree.bitsDropLast.computableInPolyTime.comp ComputableInPolyTime.natBits

/-- El circuito en bruto que codifica el número `C`. -/
def circDe (C : ℕ) : Bruto := decBruto.decode (palabraNum C)

/-- El código canónico de un circuito en bruto. -/
def codigo (d : Bruto) : ℕ := Acotada.numeroDe (encBruto d)

theorem circDe_codigo (d : Bruto) : circDe (codigo d) = d := by
  rw [circDe, codigo, palabraNum_numeroDe, decBruto.decode_enc]

theorem canonico_codigo (d : Bruto) : encBruto (circDe (codigo d)) = palabraNum (codigo d) := by
  rw [circDe_codigo, codigo, palabraNum_numeroDe]

theorem palabraNum_codigo (d : Bruto) : palabraNum (codigo d) = encBruto d := by
  rw [codigo, palabraNum_numeroDe]

theorem size_codigo (d : Bruto) : Nat.size (codigo d) = (encBruto d).length + 1 := by
  rw [codigo, SigmaFagin.size_numeroDe]

theorem length_le_encList {α : Type} (enc : α ↪ List Bool) (l : List α) : l.length ≤ (encList enc l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

/-- **El circuito cabe en su código**: `n + s` no pasa del largo de la codificación. -/
theorem cablesTot_le (d : Bruto) : cablesTot d ≤ (encBruto d).length := by
  have := length_le_encList encPuerta d.2.1
  simp only [cablesTot, encPair_apply, List.length_append, length_frame, encUnary_apply, List.length_replicate]
  omega

/-! ### La evaluación, como relación entre números -/

/-- **`EvalCod b C z`**: `C` es el código canónico de un circuito bien formado de `n` entradas, la palabra de `z` tiene
`n` bits, y el circuito da `b` en ella. -/
def evalCodB (b : Bool) (C z : ℕ) : Bool :=
  decide (encBruto (circDe C) = palabraNum C) && valido (circDe C) &&
    decide ((palabraNum z).length = (circDe C).1) && decide (evalBruto (circDe C) (palabraNum z) = b)

/-- `EvalCod`, como problema: la cadena `w` es el par `(C, z)` (`Pratt.parDe`). -/
def evalProb (b : Bool) : Problema := fun w => evalCodB b (Acotada.Pratt.parDe w).1 (Acotada.Pratt.parDe w).2

/-- El verificador: el código es canónico, y el certificado (los valores de los cables) pasa `verifEval`. -/
def verificadorEval (b : Bool) (q : List Bool × List Bool) : Bool :=
  decide (encBruto (circDe (Acotada.Pratt.parDe q.1).1) = palabraNum (Acotada.Pratt.parDe q.1).1) &&
    verifEval b (circDe (Acotada.Pratt.parDe q.1).1) (palabraNum (Acotada.Pratt.parDe q.1).2) q.2

theorem verificadorEval_poly (b : Bool) :
    ComputableInPolyTime (verificadorEval b) (encPair encBits encBits) encBool := by
  unfold verificadorEval
  have hpar := Acotada.Pratt.parDe_poly.comp (ComputableInPolyTime.fst encBits encBits)
  have hC := (ComputableInPolyTime.fst encNat encNat).comp hpar
  have hz := (ComputableInPolyTime.snd encNat encNat).comp hpar
  have hu := palabraNum_poly.comp hC
  have hd : ComputableInPolyTime (fun q : List Bool × List Bool => circDe (Acotada.Pratt.parDe q.1).1)
      (encPair encBits encBits) encBruto := decBruto.computableInPolyTime.comp hu
  have henc : ComputableInPolyTime (fun d : Bruto => encBruto d) encBruto encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have c1 := ComputableInPolyTime.decide_eq' (henc.comp hd) hu
  have c2 := (verifEval_poly b).comp (hd.prod ((palabraNum_poly.comp hz).prod
    (ComputableInPolyTime.snd encBits encBits)))
  exact ComputableInPolyTime.bool_and' c1 c2

theorem size_parDe_snd_le (w : List Bool) : (Acotada.Pratt.parDe w).2.size ≤ w.length + 1 := by
  rw [Nat.size_le, Acotada.Pratt.parDe_eq]
  have h1 := Nat.unpair_right_le (Acotada.numeroDe w - 1)
  have h2 := Acotada.Pratt.numeroDe_lt w
  omega

/-- **La evaluación de circuitos codificados está en NP** (la de `Clases.lean`), con certificados de largo `|w| + 1`. -/
theorem evalProb_NP (b : Bool) : evalProb b ∈ NP := by
  refine ⟨Polynomial.X + 1, verificadorEval b, Tiempo.IndiceRapido.esPolinomial_de_cslib (verificadorEval_poly b),
    fun w => ?_⟩
  simp only [evalProb, evalCodB, verificadorEval, Bool.and_eq_true, decide_eq_true_eq, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  constructor
  · rintro ⟨⟨⟨hcan, hval⟩, hlen⟩, hev⟩
    obtain ⟨v, hv, hver⟩ := (verifEval_iff b _ _).2 ⟨hval, hlen, hev⟩
    refine ⟨v, ?_, hcan, hver⟩
    have h1 := cablesTot_le (circDe (Acotada.Pratt.parDe w).1)
    have h2 := Acotada.Pratt.size_parDe_le w
    rw [hcan, length_palabraNum] at h1
    omega
  · rintro ⟨v, -, hcan, hver⟩
    have hlen : v.length = cablesTot (circDe (Acotada.Pratt.parDe w).1) := by
      have := hver
      simp only [verifEval, revisa, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.2.1.1
    obtain ⟨hval, hl, he⟩ := (verifEval_iff b _ _).1 ⟨v, hlen, hver⟩
    exact ⟨⟨⟨hcan, hval⟩, hl⟩, he⟩

/-! ### La forma: entradas y tamaño -/

/-- **`FormaCod c k C y`**: `C` es el código canónico de un circuito bien formado con `|y|` entradas y a lo sumo
`c·(|y|+1)^k` compuertas. -/
def formaCodB (c k : ℕ) (C y : ℕ) : Bool :=
  decide (encBruto (circDe C) = palabraNum C) && valido (circDe C) && decide ((circDe C).1 = Nat.size y) &&
    decide ((circDe C).2.1.length ≤ c * (Nat.size y + 1) ^ k)

/-- `FormaCod`, como problema sobre el par `(C, y)`. -/
def formaProb (c k : ℕ) : Problema := fun w => formaCodB c k (Acotada.Pratt.parDe w).1 (Acotada.Pratt.parDe w).2

theorem pow_poly {α : Type} {enc : α ↪ List Bool} {f : α → ℕ} (hf : ComputableInPolyTime f enc encNat) :
    ∀ k : ℕ, ComputableInPolyTime (fun a => f a ^ k) enc encNat
  | 0 => by simpa using ComputableInPolyTime.const (encIn := enc) (encOut := encNat) 1
  | k + 1 => by simpa [pow_succ] using ComputableInPolyTime.binary_mul' (pow_poly hf k) hf

theorem formaProb_P (c k : ℕ) : ComputableInPolyTime (fun q : List Bool × List Bool => formaProb c k q.1)
    (encPair encBits encBits) encBool := by
  unfold formaProb formaCodB
  have hpar := Acotada.Pratt.parDe_poly.comp (ComputableInPolyTime.fst encBits encBits)
  have hC := (ComputableInPolyTime.fst encNat encNat).comp hpar
  have hy := (ComputableInPolyTime.snd encNat encNat).comp hpar
  have hu := palabraNum_poly.comp hC
  have hd : ComputableInPolyTime (fun q : List Bool × List Bool => circDe (Acotada.Pratt.parDe q.1).1)
      (encPair encBits encBits) encBruto := decBruto.computableInPolyTime.comp hu
  have henc : ComputableInPolyTime (fun d : Bruto => encBruto d) encBruto encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have c1 := ComputableInPolyTime.decide_eq' (henc.comp hd) hu
  have c2 := valido_poly.comp hd
  have hn : ComputableInPolyTime (fun d : Bruto => d.1) encBruto encUnary := by fun_prop
  have hl : ComputableInPolyTime (fun d : Bruto => d.2.1.length) encBruto encUnary :=
    (ComputableInPolyTime.length_list encPuerta).comp (by fun_prop)
  have hsz : ComputableInPolyTime (fun q : List Bool × List Bool => Nat.size (Acotada.Pratt.parDe q.1).2)
      (encPair encBits encBits) encUnary := by
    have := ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.natBits.comp hy)
    simpa only [Function.comp_def, Nat.size_eq_bits_len] using this
  have c3 := ComputableInPolyTime.decide_eq' (hn.comp hd) hsz
  have hszb := ComputableInPolyTime.unary_to_binary.comp hsz
  have hcota := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const (encIn := encPair encBits encBits) c)
    (pow_poly (ComputableInPolyTime.binary_add' hszb (ComputableInPolyTime.const 1)) k)
  have c4 := ComputableInPolyTime.binary_le' (ComputableInPolyTime.unary_to_binary.comp (hl.comp hd)) hcota
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' c1 c2) c3) c4

/-- **La forma está en NP** (de hecho en P: el verificador no mira el certificado). -/
theorem formaProb_NP (c k : ℕ) : formaProb c k ∈ NP :=
  ⟨0, fun q => formaProb c k q.1, Tiempo.IndiceRapido.esPolinomial_de_cslib (formaProb_P c k),
    fun w => ⟨fun h => ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ => h⟩⟩

/-! ### SAT enmarcado en NP -/

/-- El verificador de `satMarco`: desenmarcar, decodificar la fórmula, revisar que la codificación sea la canónica, y
evaluar la fórmula con la asignación del certificado (el verificador de SAT de cslib-frontier). -/
def verificadorSat (q : List Bool × List Bool) : Bool :=
  decide (Cslib.Complexity.encCNF (Cslib.Complexity.cnfDecoder.decode (unframe q.1)) = unframe q.1) &&
    Cslib.Complexity.SAT.verifier (Cslib.Complexity.cnfDecoder.decode (unframe q.1), q.2)

theorem verificadorSat_poly : ComputableInPolyTime verificadorSat (encPair encBits encBits) encBool := by
  unfold verificadorSat
  have hu := ComputableInPolyTime.unframe.comp (ComputableInPolyTime.fst encBits encBits)
  have hφ := Cslib.Complexity.cnfDecoder.computableInPolyTime.comp hu
  have henc : ComputableInPolyTime (fun φ => Cslib.Complexity.encCNF φ) Cslib.Complexity.encCNF encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have c1 := ComputableInPolyTime.decide_eq' (henc.comp hφ) hu
  have c2 := Cslib.Complexity.SAT.computableInPolyTime_verifier.comp
    (hφ.prod (ComputableInPolyTime.snd encBits encBits))
  exact ComputableInPolyTime.bool_and' c1 c2

theorem bits_iff {β : Type} (enc : β ↪ List Bool) (B : Set β) (w : List Bool) :
    CookS12.bits enc B w = true ↔ ∃ b ∈ B, enc b = w := by
  unfold CookS12.bits
  exact @decide_eq_true_iff _ (Classical.dec _)

/-- **`satMarco` está en NP** (la de `Clases.lean`), con certificados de largo `≤ |w|`. Es la pieza que `CookS12.lean`
dejaba abierta para `satBits` (reconocer las codificaciones canónicas en tiempo polinomial), con el decodificador de
cslib-frontier. -/
theorem satMarco_NP : Tiempo.Relleno.satMarco ∈ NP := by
  refine ⟨Polynomial.X, verificadorSat, Tiempo.IndiceRapido.esPolinomial_de_cslib verificadorSat_poly, fun w => ?_⟩
  simp only [Tiempo.Relleno.satMarco, CookS12.satBits, bits_iff, verificadorSat, Bool.and_eq_true,
    decide_eq_true_eq, Polynomial.eval_X]
  constructor
  · rintro ⟨φ, hφ, he⟩
    obtain ⟨y, hy, hv⟩ := (Cslib.Complexity.SAT.isVerifier φ).1 hφ
    refine ⟨y, ?_, ?_⟩
    · have := CookS12.length_unframe_mul_dos_le w
      rw [hy, Polynomial.eval_X, he]; omega
    · rw [← he, Cslib.Complexity.cnfDecoder.decode_enc]; exact ⟨rfl, hv⟩
  · rintro ⟨y, -, he, hv⟩
    exact ⟨_, ⟨_, hv⟩, he⟩

/-- Y su complemento en coNP. -/
theorem noSatMarco_coNP : (fun w => !Tiempo.Relleno.satMarco w) ∈ coNP := by
  simpa [coNP] using satMarco_NP

end Codigos

/-! ## 5. `Buenos`, con códigos -/

/-- **`Buenos` con circuitos codificados.** Los largos de `x` e `y` están en orden y hay un código `C` de forma correcta
(`|y|` entradas, a lo sumo `c·(|y|+1)^k` compuertas) que, en toda `z` con `|z| = |y| + 1` (las palabras de `|y|`
bits), da `1` exactamente cuando `satMarco` acepta la palabra de `z`. Es la forma `∃ C ∀ z` que la fórmula escribe con
cuantificadores acotados. -/
theorem buenos_iff_codigos (c k x y : ℕ) :
    OscilacionParikh.Buenos Tiempo.Relleno.satMarco c k x y ↔ Nat.size x ≤ Nat.size y ∧
      ∃ C, formaCodB c k C y = true ∧ ∀ z, Nat.size z = Nat.size y + 1 →
        (evalCodB true C z = true ↔ Tiempo.Relleno.satMarco (palabraNum z) = true) := by
  unfold OscilacionParikh.Buenos
  refine and_congr_right fun _ => ?_
  rw [sucNat_le_iff]
  constructor
  · rintro ⟨d, hv, hn, hs, hL⟩
    refine ⟨codigo d, ?_, fun z hz => ?_⟩
    · simp only [formaCodB, Bool.and_eq_true, decide_eq_true_eq, circDe_codigo, palabraNum_codigo]
      exact ⟨⟨⟨trivial, hv⟩, hn⟩, hs⟩
    · have hlen : (palabraNum z).length = d.1 := by rw [length_palabraNum, hz, hn]; rfl
      simp only [evalCodB, Bool.and_eq_true, decide_eq_true_eq, circDe_codigo, palabraNum_codigo, hv, hlen,
        hL _ (hlen.trans hn), true_and]
  · rintro ⟨C, hF, hE⟩
    simp only [formaCodB, Bool.and_eq_true, decide_eq_true_eq] at hF
    obtain ⟨⟨⟨hcan, hv⟩, hn⟩, hs⟩ := hF
    refine ⟨circDe C, hv, hn, hs, fun u hu => ?_⟩
    have hz : Nat.size (Acotada.numeroDe u) = Nat.size y + 1 := by rw [SigmaFagin.size_numeroDe, hu]
    have := hE _ hz
    simp only [evalCodB, Bool.and_eq_true, decide_eq_true_eq, palabraNum_numeroDe, hcan, hv, hu, hn,
      true_and] at this
    exact Bool.eq_iff_iff.2 this

/-! ### Las cotas de los cuantificadores -/

open Turing.MultiTapeTM in
/-- **El código de un circuito chico es corto**: con operaciones de código `≤ 2`, la codificación de un circuito bien
formado de `N = n + s` cables mide a lo sumo `17·(N+1)²` bits. -/
theorem largo_encBruto_le (d : Bruto) (hv : valido d = true) (hop : ∀ g ∈ d.2.1, g.1 ≤ 2) :
    (encBruto d).length ≤ 17 * (cablesTot d + 1) ^ 2 := by
  obtain ⟨hg, hout⟩ := (valido_iff d).1 hv
  set N := cablesTot d with hN
  have hsum : (d.2.1.map fun g => 2 * (encPuerta g).length + 1).sum ≤ d.2.1.length * (6 * N + 7) := by
    have := List.sum_le_length_nsmul (d.2.1.map fun g => 2 * (encPuerta g).length + 1) (6 * N + 7) (by
      intro t ht
      obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 ht
      have h1 := hop g hgm
      have h2 := hg g hgm
      simp only [encPair_apply, List.length_append, Turing.MultiTapeTM.length_frame, encUnary_apply,
        List.length_replicate]
      omega)
    simpa using this
  have hl : d.2.1.length ≤ N := by rw [hN]; unfold cablesTot; omega
  have hn : d.1 ≤ N := by rw [hN]; unfold cablesTot; omega
  simp only [encPair_apply, List.length_append, Turing.MultiTapeTM.length_frame, encUnary_apply,
    List.length_replicate, Turing.MultiTapeTM.length_encList]
  simp only [encPair_apply, List.length_append, Turing.MultiTapeTM.length_frame, encUnary_apply,
    List.length_replicate] at hsum
  have : d.2.1.length * (6 * N + 7) ≤ N * (6 * N + 7) := Nat.mul_le_mul_right _ hl
  nlinarith

/-- La cota del código de un circuito de `|y|` entradas y `c·(|y|+1)^k` compuertas. -/
def cotaCodigo (c k y : ℕ) : ℕ := 18 * (Nat.size y + c * (Nat.size y + 1) ^ k + 1) ^ 2

/-- **Las palabras de `|y|` bits son números `≤ 4y + 1`**: si `|z| = |y| + 1`, `z ≤ 4y + 1`. Es la cota del `∀ z`. -/
theorem le_de_size (y z : ℕ) (h : Nat.size z = Nat.size y + 1) : z ≤ 4 * y + 1 := by
  have hz : z < 2 ^ (Nat.size y + 1) := by rw [← h]; exact Nat.lt_size_self z
  rcases Nat.eq_zero_or_pos (Nat.size y) with h0 | hpos
  · rw [h0] at hz; omega
  · have hy : 2 ^ (Nat.size y - 1) ≤ y := Nat.lt_size.1 (by omega)
    have e : 2 ^ (Nat.size y + 1) = 4 * 2 ^ (Nat.size y - 1) := by
      rw [show Nat.size y + 1 = (Nat.size y - 1) + 2 by omega, pow_add]; ring
    omega

/-- **`Buenos` con los cuantificadores acotados**: el `∃ C` se acota por `|C| ≤ cotaCodigo c k y` (y entonces
`C < 2^(cotaCodigo c k y)`), y el `∀ z` por `z ≤ 4y + 1`. Es exactamente lo que la fórmula final escribe. -/
theorem buenos_iff_acotado (c k x y : ℕ) :
    OscilacionParikh.Buenos Tiempo.Relleno.satMarco c k x y ↔ Nat.size x ≤ Nat.size y ∧
      ∃ C, Nat.size C ≤ cotaCodigo c k y ∧ formaCodB c k C y = true ∧
        ∀ z ≤ 4 * y + 1, Nat.size z = Nat.size y + 1 →
          (evalCodB true C z = true ↔ Tiempo.Relleno.satMarco (palabraNum z) = true) := by
  constructor
  · intro hB
    refine ⟨hB.1, ?_⟩
    obtain ⟨d, hv, hn, hs, hop, hL⟩ := existe_bruto_chico hB.2
    refine ⟨codigo d, ?_, ?_, fun z _ hz => ?_⟩
    · rw [size_codigo]
      have h1 := largo_encBruto_le d hv hop
      have h2 : cablesTot d + 1 ≤ Nat.size y + c * (Nat.size y + 1) ^ k + 1 := by unfold cablesTot; omega
      have h3 := Nat.pow_le_pow_left h2 2
      unfold cotaCodigo
      nlinarith
    · simp only [formaCodB, Bool.and_eq_true, decide_eq_true_eq, circDe_codigo, palabraNum_codigo]
      exact ⟨⟨⟨trivial, hv⟩, hn⟩, hs⟩
    · have hlen : (palabraNum z).length = d.1 := by rw [length_palabraNum, hz, hn]; rfl
      simp only [evalCodB, Bool.and_eq_true, decide_eq_true_eq, circDe_codigo, palabraNum_codigo, hv, hlen,
        hL _ (hlen.trans hn), true_and]
  · rintro ⟨hxy, C, -, hF, hE⟩
    exact (buenos_iff_codigos c k x y).2 ⟨hxy, C, hF, fun z hz => hE z (le_de_size y z hz) hz⟩

/-! ## 6. Las fórmulas -/

section Formulas

open FirstOrder FirstOrder.Language
open Sagitta.Map.Acotada (L EsAguda EsSigma1 EsPi1)
open Sagitta.Map.Borde.OscilacionParikh (EsAcotada)

mutual

/-- **Una `Σᵇ₁` es acotada.** -/
theorem esAcotada_de_sigma {α : Type} : ∀ {n : ℕ} {φ : L.BoundedFormula α n}, EsSigma1 φ → EsAcotada φ
  | _, _, .aguda h => .de_aguda h
  | _, _, .existe t h => .existe t (esAcotada_de_sigma h)
  | _, _, .todoAgudo _ h => .todo _ (esAcotada_de_sigma h)
  | _, _, .y h1 h2 => .inf (esAcotada_de_sigma h1) (esAcotada_de_sigma h2)
  | _, _, .o h1 h2 => .imp (.imp (esAcotada_de_sigma h1) .falso) (esAcotada_de_sigma h2)
  | _, _, .no h => .imp (esAcotada_de_pi h) .falso
  | _, _, .imp h1 h2 => .imp (esAcotada_de_pi h1) (esAcotada_de_sigma h2)

/-- **Una `Πᵇ₁` es acotada.** -/
theorem esAcotada_de_pi {α : Type} : ∀ {n : ℕ} {φ : L.BoundedFormula α n}, EsPi1 φ → EsAcotada φ
  | _, _, .aguda h => .de_aguda h
  | _, _, .todo t h => .todo t (esAcotada_de_pi h)
  | _, _, .existeAgudo _ h => .existe _ (esAcotada_de_pi h)
  | _, _, .y h1 h2 => .inf (esAcotada_de_pi h1) (esAcotada_de_pi h2)
  | _, _, .o h1 h2 => .imp (.imp (esAcotada_de_pi h1) .falso) (esAcotada_de_pi h2)
  | _, _, .no h => .imp (esAcotada_de_sigma h) .falso
  | _, _, .imp h1 h2 => .imp (esAcotada_de_sigma h1) (esAcotada_de_pi h2)

end

/-- La negación de una acotada es acotada. -/
theorem esAcotada_not {α : Type} {n : ℕ} {φ : L.BoundedFormula α n} (h : EsAcotada φ) : EsAcotada φ.not :=
  .imp h .falso

/-- **Una relación de NP entre dos números tiene una fórmula `Σᵇ₁` con su gráfico exacto.** Es el paso de
`Pratt.existe_formula_minFac` en general: `Σᵇ₁ = NP` (`SigmaFagin.sigmaIgualNP`) para el problema sobre el par
`(x, y)` de Mathlib (`Pratt.parDe`), y `Pratt.formulaPar` para volver a dos variables. -/
theorem existe_formula_par (R : ℕ → ℕ → Bool) (hR : (fun w => R (Acotada.Pratt.parDe w).1 (Acotada.Pratt.parDe w).2) ∈ NP) :
    ∃ φ : L.Formula (Fin 2), EsSigma1 φ ∧ ∀ x y : ℕ, φ.Realize ![x, y] ↔ R x y = true := by
  obtain ⟨ψ, hψ, hdef⟩ := (SigmaFagin.sigmaIgualNP _).1 hR
  refine ⟨Acotada.Pratt.formulaPar ψ, Acotada.Pratt.formulaPar_sigma hψ, fun x y => ?_⟩
  rw [Acotada.Pratt.realize_formulaPar]
  obtain ⟨w, hw⟩ := Acotada.Pratt.numeroDe_sobre (Nat.pair x y + 1) (by omega)
  rw [← hw, ← hdef w]
  simp only [Acotada.Pratt.parDe_eq, hw, Nat.add_sub_cancel, Nat.unpair_pair]

/-- **La fórmula de la evaluación**: `φ_b(C, z)` vale en ℕ exactamente cuando `C` es el código canónico de un circuito
bien formado que da `b` en la palabra de `z` (de su largo de entradas). -/
theorem existe_formula_eval (b : Bool) :
    ∃ φ : L.Formula (Fin 2), EsSigma1 φ ∧ ∀ C z : ℕ, φ.Realize ![C, z] ↔ evalCodB b C z = true :=
  existe_formula_par (evalCodB b) (evalProb_NP b)

/-- **La fórmula de la forma**: `φ(C, y)` vale exactamente cuando `C` es el código canónico de un circuito bien formado
con `|y|` entradas y a lo sumo `c·(|y|+1)^k` compuertas. -/
theorem existe_formula_forma (c k : ℕ) :
    ∃ φ : L.Formula (Fin 2), EsSigma1 φ ∧ ∀ C y : ℕ, φ.Realize ![C, y] ↔ formaCodB c k C y = true :=
  existe_formula_par (formaCodB c k) (formaProb_NP c k)

/-- **La fórmula de SAT enmarcado**: `φ(z)`, para `z ≥ 1`, vale exactamente cuando `satMarco` acepta la palabra de
`z`. Su negación (`Πᵇ₁`) dice que no la acepta. -/
theorem existe_formula_sat :
    ∃ φ : L.Formula (Fin 1), EsSigma1 φ ∧
      ∀ z : ℕ, 1 ≤ z → (φ.Realize ![z] ↔ Tiempo.Relleno.satMarco (palabraNum z) = true) := by
  obtain ⟨φ, hφ, hdef⟩ := (SigmaFagin.sigmaIgualNP _).1 satMarco_NP
  refine ⟨φ, hφ, fun z hz => ?_⟩
  obtain ⟨u, rfl⟩ := Acotada.Pratt.numeroDe_sobre z hz
  rw [palabraNum_numeroDe, hdef u]

/-- **Las tres piezas, acotadas** en el sentido de `OscilacionParikh.EsAcotada` (la clase para la que vale
`parikh_existe`), con la negación de la de SAT para su uso negativo. -/
theorem piezas_acotadas (c k : ℕ) :
    (∃ φ : L.Formula (Fin 2), EsAcotada φ ∧ ∀ C z : ℕ, φ.Realize ![C, z] ↔ evalCodB true C z = true) ∧
    (∃ φ : L.Formula (Fin 2), EsAcotada φ ∧ ∀ C y : ℕ, φ.Realize ![C, y] ↔ formaCodB c k C y = true) ∧
    (∃ φ : L.Formula (Fin 1), EsAcotada φ ∧ EsAcotada φ.not ∧
      ∀ z : ℕ, 1 ≤ z → (φ.Realize ![z] ↔ Tiempo.Relleno.satMarco (palabraNum z) = true)) := by
  obtain ⟨φ1, h1, d1⟩ := existe_formula_eval true
  obtain ⟨φ2, h2, d2⟩ := existe_formula_forma c k
  obtain ⟨φ3, h3, d3⟩ := existe_formula_sat
  exact ⟨⟨φ1, esAcotada_de_sigma h1, d1⟩, ⟨φ2, esAcotada_de_sigma h2, d2⟩,
    ⟨φ3, esAcotada_de_sigma h3, esAcotada_not (esAcotada_de_sigma h3), d3⟩⟩

end Formulas

/- Mutantes probados (25 nov 2026, fuera del repositorio; cada uno es una copia del archivo con un cambio, compilada con
`lake env lean`):

* `revisa_valor` / `verifEval_iff`: quitar de `revisa` la condición `v.take n = x`. La corrección no compila, y es
  falsa: el circuito identidad `(1, [], 0)` acepta en la entrada `[false]` el certificado `[true]`, que dice salida 1.
* `sucNat_le_iff`: quitar de `valido` la condición «la salida es un cable». `aCircuito` deja de tipar (no hay `Fin` para
  la salida) y la vuelta de la equivalencia cae.
* `satMarco_NP`: quitar de `verificadorSat` la revisión de que la codificación sea la canónica. La vuelta no compila, y
  es falsa: `[true, false]` decodifica a una CNF satisfacible sin ser el código de ninguna, así que el verificador
  mutado acepta `frame [true, false]` aunque `satMarco` la rechace.
* `le_de_size` (la cota del `∀ z`): pedir `z ≤ 2y + 1` en vez de `4y + 1`. `omega` no cierra, y es falso: `y = 2`,
  `z = 7` (`|z| = 3 = |y| + 1`).
* `revisa_valor`: `lee` con `a ≤ t` en vez de `a < t` (una compuerta lee su propio cable). La corrección no compila, y
  la evaluación deja de ser única: la compuerta `(o, 0, 0)` sin entradas acepta los certificados `[true]` y `[false]`;
  el circuito verdadero da `false`. -/

end Sagitta.Map.Borde.FormulaBuenos
