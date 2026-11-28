import Sagitta.Map.CertificadosArbol
import Sagitta.Map.DemoraEfectiva
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Transfer

/-!
# Con demora logarítmica, la búsqueda es P (A4)

La fase A4: llevar a las máquinas lo que `CertificadosArbol.lean` y `DemoraEfectiva.lean` cuentan en nodos. Si `L` tiene
verificador `V` con certificados de largo `≤ p(|x|)`, y hay un detector `det` sano (`SanoN`) con demora `DemoraN d` y
`d(n) ≤ a · log₂ (n + 1) + b`, y `V` y `det` corren en tiempo polinomial, entonces `L ∈ P` (`busqueda_en_P`).

## Las codificaciones

`V` y `det` se piden `ComputableInPolyTime` de cslib-frontier con `encPair encBits encBits` a `encBool`: el par
`(x, q)` es `frame x ++ q`, y la respuesta es un bit. Son las mismas que fija `CodBits`: `encBits` es la identidad,
`encBool b = [b]` y `frame` es `delimita` (`delimita_eq_frame`, `cod_par_eq`). Por eso las hipótesis dan también
`EsPolinomial V`, y `L ∈ NP` (`busqueda_en_NP`).

## La máquina no recorre el árbol: mira la frontera

Con `SanoN` y `DemoraN d`, la raíz está viva si y solo si alguna palabra `q` de largo `d` no es descartada por el
detector (`enFrontera_iff`): si la raíz está muerta, la demora obliga al detector a descartar todas; si está viva, el
prefijo de largo `d` de una solución no puede descartarse, porque es sano. Cuando `d ≥ N` se mira la hoja misma. Así,
la máquina (`decideFrontera`) enumera las `2^m` palabras de largo `m = min (a · log₂ (|x|+1) + b) (p(|x|))`, que son a
lo sumo `2^b · (|x|+1)^a` (`dos_pow_profFrontera_le`), y en cada una evalúa `det`, y `V` en sus prefijos si es hoja.

Esto es más simple que iterar la vuelta atrás con una pila, y da lo mismo: `decideFrontera_eq_buscar` dice que la
máquina responde lo que responde `buscar`. Lo que se aprende: con una demora `d` garantizada, la búsqueda sobra; la
frontera a profundidad `d` ya decide, a un costo de `2^d` llamadas al detector. Es la otra cara de `anticipa_perfecto`.

## Lo que se prueba

* **El puente** (`esPolinomial_problema`, `esPolinomial_verificador`): lo que cslib-frontier certifica con `encBits` y
  `encBool` es `EsPolinomial` de `Clases.lean`, vía `computableInPolyTime_iff_tm2`.
* **La frontera** (`enFrontera_iff`, `enFrontera_eq_buscar`).
* **La máquina** (`decideFrontera_polinomial`): con `bitsEnumList_of_polyBounded`, `anyWithInput` y `fun_prop`.
* **La meta** (`busqueda_en_P`).
* **Las hipótesis se cumplen** (`eco_en_P`, `eco1_en_P`): un verificador cuyo certificado es `x` mismo y un detector
  que compara el prefijo con `x`; el árbol tiene profundidad `|x|`. En `eco_en_P` la demora es 0 y solo decide la raíz.
  En `eco1_en_P` el detector (`detEco1`) nunca descarta la raíz: la demora es 1, con `b = 1`, y la máquina tiene que
  bajar un nivel. Los controles evalúan `decideFrontera` y `profFrontera` en casos concretos, no solo `enFrontera`.

## Lo que no

* No se dice nada de si existen detectores así para un problema NP-completo: es la pregunta abierta, puesta en otra
  forma. Un detector sano de demora logarítmica y tiempo polinomial para SAT daría P = NP por este teorema.
* La búsqueda con pila (`buscar` paso a paso dentro de la máquina) no se escribió: no hace falta para la meta.
-/

namespace Sagitta.Map
namespace Tiempo

open Turing.MultiTapeTM

/-! ## El puente para problemas -/

/-- `CodBits (List Bool)` es `encBits`. -/
theorem cod_bits_eq : (CodBits.toEncoding (α := List Bool)).encode = ⇑encBits := rfl

/-- `CodBits Bool` es `encBool`. -/
theorem cod_bool_eq : (CodBits.toEncoding (α := Bool)).encode = ⇑encBool := rfl

/-- `delimita` es el `frame` de cslib-frontier. -/
theorem delimita_eq_frame : ∀ l : List Bool, CodBits.delimita l = frame l
  | [] => rfl
  | b :: l => by simp [CodBits.delimita, frame, delimita_eq_frame l]

/-- `CodBits` de un par de cadenas es `encPair encBits encBits`. -/
theorem cod_par_eq :
    (CodBits.toEncoding (α := List Bool × List Bool)).encode = ⇑(encPair encBits encBits) := by
  funext q
  exact congrArg (· ++ q.2) (delimita_eq_frame q.1)

/-- **El puente para problemas**: un problema que cslib-frontier certifica en tiempo polinomial está en `P`. -/
theorem esPolinomial_problema {L : Problema} (h : ComputableInPolyTime L encBits encBool) :
    EsPolinomial L := by
  unfold EsPolinomial EsPolinomialCon
  rw [cod_bits_eq, cod_bool_eq]
  obtain ⟨h, -⟩ := computableInPolyTime_iff_tm2.mp h
  exact ⟨h⟩

/-- El mismo puente para verificadores. -/
theorem esPolinomial_verificador {V : List Bool × List Bool → Bool}
    (h : ComputableInPolyTime V (encPair encBits encBits) encBool) : EsPolinomial V := by
  unfold EsPolinomial EsPolinomialCon
  rw [cod_par_eq, cod_bool_eq]
  obtain ⟨h, -⟩ := computableInPolyTime_iff_tm2.mp h
  exact ⟨h⟩

/-! ## La frontera a profundidad `m` -/

/-- Hay una palabra `q` de largo `m` que el detector no descarta y que, si `m` llega a `N`, es solución. -/
def enFrontera (sol det : List Bool → Bool) (N m : ℕ) : Bool :=
  (Cslib.BitString.enumList m).any fun q => !det q && (decide (m < N) || sol q)

/-- **La frontera decide**: con `SanoN` y `DemoraN d`, mirar las palabras de largo `min d N` dice si la raíz vive. -/
theorem enFrontera_iff {sol det : List Bool → Bool} {N d : ℕ} (hs : SanoN sol det N)
    (hd : DemoraN sol det N d) : enFrontera sol det N (min d N) = true ↔ Vivo sol N [] := by
  unfold enFrontera
  simp only [List.any_eq_true, Cslib.BitString.mem_enumList, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, hdet, hcaso⟩
    rcases hcaso with hlt | hsol
    · by_contra hm
      have hmd : min d N = d := by omega
      rw [hmd] at hq
      have := hd [] (by simp; omega) (by simpa using hm) q hq
      simp [hdet] at this
    · by_cases hlt : min d N < N
      · by_contra hm
        have hmd : min d N = d := by omega
        rw [hmd] at hq
        have := hd [] (by simp; omega) (by simpa using hm) q hq
        simp [hdet] at this
      · exact ⟨q, by omega, by simpa using hsol⟩
  · rintro ⟨r, hr, hsol⟩
    refine ⟨r.take (min d N), by simp; omega, ?_, ?_⟩
    · by_contra hdet
      have hm := hs (r.take (min d N)) (by simp only [List.length_take]; omega) (by simpa using hdet)
      apply hm
      refine ⟨r.drop (min d N), by simp; omega, ?_⟩
      simpa using hsol
    · by_cases hlt : min d N < N
      · exact .inl hlt
      · right
        have : min d N = r.length := by omega
        rw [this, List.take_length]
        simpa using hsol

/-- La frontera responde lo mismo que la vuelta atrás. -/
theorem enFrontera_eq_buscar {sol det : List Bool → Bool} {N d : ℕ} (hs : SanoN sol det N)
    (hd : DemoraN sol det N d) : enFrontera sol det N (min d N) = (buscar sol det N []).1 := by
  have h1 := enFrontera_iff hs hd
  have h2 := buscar_correctoN hs N [] (by simp)
  cases h : enFrontera sol det N (min d N) <;> cases h' : (buscar sol det N []).1 <;> simp_all

/-! ## La máquina -/

/-- La profundidad de la frontera: `min (a · log₂ (|x| + 1) + b) (p(|x|))`. -/
def profFrontera (p : Polynomial ℕ) (a b : ℕ) (x : List Bool) : ℕ :=
  min (a * Nat.log 2 (x.length + 1) + b) (p.eval x.length)

/-- Lo que calcula la máquina. -/
def decideFrontera (V det : List Bool × List Bool → Bool) (p : Polynomial ℕ) (a b : ℕ)
    (x : List Bool) : Bool :=
  enFrontera (solCert V x) (fun q => det (x, q)) (p.eval x.length) (profFrontera p a b x)

/-- La profundidad se calcula en unario en tiempo polinomial. -/
theorem profFrontera_polinomial (p : Polynomial ℕ) (a b : ℕ) :
    ComputableInPolyTime (profFrontera p a b) encBits encUnary := by
  unfold profFrontera
  fun_prop

/-- **La frontera es polinomial**: `2^m ≤ 2^b · (|x|+1)^a`. -/
theorem dos_pow_profFrontera_le (p : Polynomial ℕ) (a b : ℕ) (x : List Bool) :
    2 ^ profFrontera p a b x ≤ 2 ^ b * (x.length + 1) ^ a := by
  unfold profFrontera
  calc 2 ^ min (a * Nat.log 2 (x.length + 1) + b) (p.eval x.length)
      ≤ 2 ^ (a * Nat.log 2 (x.length + 1) + b) := Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
    _ = 2 ^ b * (2 ^ Nat.log 2 (x.length + 1)) ^ a := by ring
    _ ≤ 2 ^ b * (x.length + 1) ^ a :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) a)

/-- La solución en una hoja (algún prefijo es certificado) es polinomial si `V` lo es. -/
theorem solCert_polinomial {V : List Bool × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair encBits encBits) encBool) :
    ComputableInPolyTime (fun q : List Bool × List Bool => solCert V q.1 q.2)
      (encPair encBits encBits) encBool := by
  unfold solCert
  fun_prop

/-- **La máquina corre en tiempo polinomial.** -/
theorem decideFrontera_polinomial {V det : List Bool × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair encBits encBits) encBool)
    (hdet : ComputableInPolyTime det (encPair encBits encBits) encBool) (p : Polynomial ℕ) (a b : ℕ) :
    ComputableInPolyTime (decideFrontera V det p a b) encBits encBool := by
  have hm := profFrontera_polinomial p a b
  have hlist := ComputableInPolyTime.bitsEnumList_of_polyBounded hm
    (PolyBounded.of_forall_le (2 ^ b) a fun x => by simpa using dos_pow_profFrontera_le p a b x)
  have hs := solCert_polinomial hV
  unfold decideFrontera enFrontera
  fun_prop

/-! ## La meta: con demora logarítmica, `L ∈ P` -/

/-- La máquina responde `L x`. -/
theorem decideFrontera_eq {L : Problema} {p : Polynomial ℕ} {V det : List Bool × List Bool → Bool}
    (hL : ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true)
    {d : ℕ → ℕ} {a b : ℕ} (hdlog : ∀ n, d n ≤ a * Nat.log 2 (n + 1) + b)
    (hsano : ∀ x, SanoN (solCert V x) (fun q => det (x, q)) (p.eval x.length))
    (hdem : ∀ x, DemoraN (solCert V x) (fun q => det (x, q)) (p.eval x.length) (d x.length))
    (x : List Bool) : decideFrontera V det p a b x = L x := by
  have hD : DemoraN (solCert V x) (fun q => det (x, q)) (p.eval x.length)
      (a * Nat.log 2 (x.length + 1) + b) := by
    have := demora_mono (hdem x) (a * Nat.log 2 (x.length + 1) + b - d x.length)
    rwa [Nat.sub_add_cancel (hdlog x.length)] at this
  have h := (enFrontera_iff (hsano x) hD).trans (vivo_solCert_iff V x _)
  rw [← hL x] at h
  unfold decideFrontera profFrontera
  cases h1 : enFrontera (solCert V x) (fun q => det (x, q)) (p.eval x.length)
      (min (a * Nat.log 2 (x.length + 1) + b) (p.eval x.length)) <;>
    cases h2 : L x <;> simp_all

/-- La máquina calcula lo mismo que la vuelta atrás `buscar`. -/
theorem decideFrontera_eq_buscar {p : Polynomial ℕ} {V det : List Bool × List Bool → Bool}
    {d : ℕ → ℕ} {a b : ℕ} (hdlog : ∀ n, d n ≤ a * Nat.log 2 (n + 1) + b)
    (hsano : ∀ x, SanoN (solCert V x) (fun q => det (x, q)) (p.eval x.length))
    (hdem : ∀ x, DemoraN (solCert V x) (fun q => det (x, q)) (p.eval x.length) (d x.length))
    (x : List Bool) :
    decideFrontera V det p a b x = (buscar (solCert V x) (fun q => det (x, q)) (p.eval x.length) []).1 := by
  have hD : DemoraN (solCert V x) (fun q => det (x, q)) (p.eval x.length)
      (a * Nat.log 2 (x.length + 1) + b) := by
    have := demora_mono (hdem x) (a * Nat.log 2 (x.length + 1) + b - d x.length)
    rwa [Nat.sub_add_cancel (hdlog x.length)] at this
  exact enFrontera_eq_buscar (hsano x) hD

/-- **A4: con un detector sano, polinomial y de demora logarítmica, `L ∈ P`.** -/
theorem busqueda_en_P {L : Problema} {p : Polynomial ℕ} {V det : List Bool × List Bool → Bool}
    (hL : ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true)
    (hV : ComputableInPolyTime V (encPair encBits encBits) encBool)
    (hdet : ComputableInPolyTime det (encPair encBits encBits) encBool)
    {d : ℕ → ℕ} {a b : ℕ} (hdlog : ∀ n, d n ≤ a * Nat.log 2 (n + 1) + b)
    (hsano : ∀ x, SanoN (solCert V x) (fun q => det (x, q)) (p.eval x.length))
    (hdem : ∀ x, DemoraN (solCert V x) (fun q => det (x, q)) (p.eval x.length) (d x.length)) :
    L ∈ P := by
  have hfun : decideFrontera V det p a b = L := funext (decideFrontera_eq hL hdlog hsano hdem)
  have h := decideFrontera_polinomial hV hdet p a b
  rw [hfun] at h
  exact esPolinomial_problema h

/-- Las mismas hipótesis dan `L ∈ NP`. -/
theorem busqueda_en_NP {L : Problema} {p : Polynomial ℕ} {V : List Bool × List Bool → Bool}
    (hL : ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true)
    (hV : ComputableInPolyTime V (encPair encBits encBits) encBool) : L ∈ NP :=
  ⟨p, V, esPolinomial_verificador hV, hL⟩

/-! ## Las hipótesis se cumplen: un ejemplo -/

/-- Verificador de ejemplo: el certificado es `x` mismo, y `x` tiene algún `1`. -/
def verifEco (q : List Bool × List Bool) : Bool := q.1.any id && q.2 == q.1

/-- Detector de ejemplo: muerto si `x` no tiene `1` o si el prefijo se aparta de `x`. -/
def detEco (q : List Bool × List Bool) : Bool := !(q.1.any id && q.1.take q.2.length == q.2)

/-- En el ejemplo, una hoja es solución si y solo si es `x` y `x` tiene un `1`. -/
theorem solCert_eco {x r : List Bool} (hr : r.length = x.length) :
    solCert verifEco x r = true ↔ x.any id = true ∧ r = x := by
  simp only [solCert, verifEco, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨j, hj, hany, htake⟩
    refine ⟨by simpa using hany, ?_⟩
    have hl := congrArg List.length htake
    simp only [List.length_take] at hl
    rw [List.take_of_length_le (by omega)] at htake
    exact htake
  · rintro ⟨hany, rfl⟩
    exact ⟨r.length, by omega, by simpa using hany, by simp⟩

/-- En el ejemplo, un prefijo vive si y solo si es prefijo de `x` y `x` tiene un `1`. -/
theorem vivo_eco {x q : List Bool} (hq : q.length ≤ x.length) :
    Vivo (solCert verifEco x) (x.length - q.length) q ↔ x.any id = true ∧ x.take q.length = q := by
  constructor
  · rintro ⟨s, hs, hsol⟩
    obtain ⟨hany, he⟩ := (solCert_eco (by simp; omega)).mp hsol
    exact ⟨hany, by rw [← he]; simp⟩
  · rintro ⟨hany, ht⟩
    refine ⟨x.drop q.length, by simp, (solCert_eco (by simp; omega)).mpr ⟨hany, ?_⟩⟩
    conv_rhs => rw [← List.take_append_drop q.length x]
    rw [ht]

/-- El detector del ejemplo es sano. -/
theorem eco_sano (x : List Bool) :
    SanoN (solCert verifEco x) (fun q => detEco (x, q)) (Polynomial.X.eval x.length) := by
  intro q hq hd hv
  simp only [Polynomial.eval_X] at hq hv
  rw [vivo_eco hq] at hv
  simp [detEco, hv.1, hv.2] at hd

/-- El detector del ejemplo tiene demora 0. -/
theorem eco_demora (x : List Bool) :
    DemoraN (solCert verifEco x) (fun q => detEco (x, q)) (Polynomial.X.eval x.length) 0 := by
  intro q hq hm r hr
  simp only [Polynomial.eval_X] at hq hm
  rw [List.length_eq_zero_iff.mp hr, List.append_nil]
  rw [vivo_eco (by omega)] at hm
  simp only [detEco, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  by_cases hany : x.any id = true
  · exact .inr fun h => hm ⟨hany, h⟩
  · exact .inl (by simpa using hany)

/-- El verificador del ejemplo define «tiene algún `1`». -/
theorem eco_L (x : List Bool) : x.any id = true ↔
    ∃ y : List Bool, y.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧ verifEco (x, y) = true := by
  simp only [Polynomial.eval_X, verifEco, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h; exact ⟨x, le_rfl, h, rfl⟩
  · rintro ⟨y, -, h, -⟩; exact h

/-- El verificador del ejemplo es polinomial. -/
theorem verifEco_polinomial : ComputableInPolyTime verifEco (encPair encBits encBits) encBool := by
  unfold verifEco
  fun_prop

/-- El detector del ejemplo es polinomial. -/
theorem detEco_polinomial : ComputableInPolyTime detEco (encPair encBits encBits) encBool := by
  unfold detEco
  fun_prop

/-- **Las hipótesis de `busqueda_en_P` se cumplen** en un ejemplo con árbol de profundidad `|x|`. -/
theorem eco_en_P : (fun x : List Bool => x.any id) ∈ P :=
  busqueda_en_P (p := Polynomial.X) (d := fun _ => 0) (a := 0) (b := 0) eco_L verifEco_polinomial
    detEco_polinomial (fun _ => by simp) eco_sano eco_demora

/-- Detector de ejemplo que nunca descarta la raíz: así la demora es 1, no 0. -/
def detEco1 (q : List Bool × List Bool) : Bool := !q.2.isEmpty && detEco q

/-- El segundo detector es sano: descarta menos que `detEco`. -/
theorem eco1_sano (x : List Bool) :
    SanoN (solCert verifEco x) (fun q => detEco1 (x, q)) (Polynomial.X.eval x.length) := by
  intro q hq hd
  simp only [detEco1, Bool.and_eq_true] at hd
  exact eco_sano x q hq hd.2

/-- El segundo detector tiene demora 1. -/
theorem eco1_demora (x : List Bool) :
    DemoraN (solCert verifEco x) (fun q => detEco1 (x, q)) (Polynomial.X.eval x.length) 1 := by
  intro p hp hm r hr
  simp only [Polynomial.eval_X] at hp hm
  rw [vivo_eco (by omega)] at hm
  have hne : (p ++ r).isEmpty = false := by
    cases r with
    | nil => simp at hr
    | cons _ _ => simp
  simp only [detEco1, hne, Bool.not_false, Bool.true_and, detEco, Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_eq_false_iff_ne]
  by_cases hany : x.any id = true
  · refine .inr fun h => hm ⟨hany, ?_⟩
    have h2 := congrArg (List.take p.length) h
    simpa [List.take_take, List.length_append, hr] using h2
  · exact .inl (by simpa using hany)

/-- **Las hipótesis se cumplen con demora 1**: la raíz no decide y la frontera tiene profundidad 1. -/
theorem eco1_en_P : (fun x : List Bool => x.any id) ∈ P :=
  busqueda_en_P (p := Polynomial.X) (d := fun _ => 1) (a := 0) (b := 1) eco_L verifEco_polinomial
    (by unfold detEco1 detEco; fun_prop) (fun _ => by simp) eco1_sano eco1_demora

/-! ## Controles -/

/-- El segundo detector no descarta la raíz, aunque `[false, false]` no tenga un `1`. -/
example : detEco1 ([false, false], []) = false := by decide

/-- Por eso la frontera de profundidad 0 se equivoca con él. -/
example : enFrontera (solCert verifEco [false, false]) (fun q => detEco1 ([false, false], q)) 2 0 = true := by
  decide

/-- La profundidad que calcula la máquina con `a = 0`, `b = 1`. -/
example : profFrontera Polynomial.X 0 1 [false, false] = 1 := by
  simp [profFrontera, Polynomial.eval_X]

/-- La máquina, con profundidad 1, acierta: `[false, false]` no tiene un `1`. -/
example : decideFrontera verifEco detEco1 Polynomial.X 0 1 [false, false] = false := by
  rw [decideFrontera, Polynomial.eval_X, show profFrontera Polynomial.X 0 1 [false, false] = 1 by
    simp [profFrontera, Polynomial.eval_X]]
  decide

/-- Y `[false, true]` sí. -/
example : decideFrontera verifEco detEco1 Polynomial.X 0 1 [false, true] = true := by
  rw [decideFrontera, Polynomial.eval_X, show profFrontera Polynomial.X 0 1 [false, true] = 1 by
    simp [profFrontera, Polynomial.eval_X]]
  decide

/-- Con `a = 1` la profundidad crece con `|x|`: `log₂ 3 = 1`. -/
example : profFrontera Polynomial.X 1 0 [false, false] = 1 := by
  rw [profFrontera, Polynomial.eval_X]; decide

/-- Y con `a = 1`, `b = 0` la máquina también acierta. -/
example : decideFrontera verifEco detEco1 Polynomial.X 1 0 [false, false] = false := by
  rw [decideFrontera, Polynomial.eval_X, show profFrontera Polynomial.X 1 0 [false, false] = 1 by
    rw [profFrontera, Polynomial.eval_X]; decide]
  decide

/-- Con demora 0 basta la raíz: `[true, false]` tiene un `1`. -/
example : enFrontera (solCert verifEco [true, false]) (fun q => detEco ([true, false], q)) 2 0 = true := by
  decide

/-- `[false, false]` no tiene: la raíz se descarta. -/
example : enFrontera (solCert verifEco [false, false]) (fun q => detEco ([false, false], q)) 2 0 = false := by
  decide

/-- Mirando las hojas se llega a lo mismo. -/
example : enFrontera (solCert verifEco [true, false]) (fun q => detEco ([true, false], q)) 2 2 = true := by
  decide

/-- Con profundidad 3 y sin detector, la frontera encuentra el certificado de juguete. -/
example : enFrontera (solCert verifJuguete []) nunca 3 3 = true := by decide

/-- Con profundidad 1 no cabe. -/
example : enFrontera (solCert verifJuguete []) nunca 1 1 = false := by decide

end Tiempo
end Sagitta.Map
