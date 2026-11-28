import Sagitta.Map.Informacion.BuscarPolinomial
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

/-!
# El tiempo como información

Quedaron cinco cosas en cola para Lean (25 nov 2026). Este archivo las prueba en orden.

## 1. La vuelta de la equivalencia con `Kt` (§ 1)

`ProgramasCortos A`: hay un `c` tal que toda instancia `a ∈ A` (de largo `n`) la resuelve una máquina de cslib de
número `i ≤ c · log₂ (n+2) + c` en `t ≤ (n+2)^c` pasos. Es la forma «programa corto y rápido» de `Kt` logarítmica.

* `cortos_implica_kt` y `kt_implica_cortos`: `ProgramasCortos A ↔ KtMTLog A` (`cortos_iff_kt`).
* **`cortos_implica_levin_pol`** (la vuelta): programas cortos y rápidos ⇒ la búsqueda de Levin (`buscarMT`) halla
  con costo contable polinomial (`BusquedaUniversalPol`, el costo de `costoHastaMT`: la cota de la universal de cslib
  más el verificador, intento por intento).
* **`cortos_implica_pasos`**: lo mismo en pasos simulados (`Levin.costoHasta`), con la cota explícita
  `< 8 · 2^c · (n+2)^(2c)`.
* **`levin_equivalencias`**, la equivalencia junta: búsqueda en P ⇒ programas cortos ⇔ `ktMT` logarítmica ⇔ búsqueda
  de Levin polinomial (costo contable).

**El círculo, cerrado (25 nov, noche).** `BuscarPolinomial` prueba que `buscarMT` misma es una función de cslib en
tiempo polinomial (`buscarMT_poly`), con lo que la hipótesis `hImpl` de `kt_implica_enP_condicional` queda descargada
(`levin_pol_implica_enP`). **`levin_circulo`**: con el verificador en P, búsqueda en P ⇔ programas cortos ⇔ `ktMT`
logarítmica ⇔ búsqueda de Levin polinomial; **`sat_circulo`**, para SAT, sin hipótesis. La única hipótesis que queda
es la del problema (el verificador en P), no la de una implementación.

## 2. El canal de tiempo (§ 2)

* **`capacidad_canal_tiempo`**: toda codificación inyectiva de los `2ⁿ` mensajes de `n` bits en esperas `t ≤ T`
  cumple `2ⁿ ≤ T + 1`; `capacidad_canal_tiempo_log`: `n ≤ log₂ (T+1)`.
* `control_canal_identidad`: con `T = 2ⁿ − 1` se alcanza, con la identidad.

## 3. La fuerza bruta es ese canal (§ 3)

`tiempoBusqueda V`: la búsqueda en orden sobre `Fin (2ⁿ)` (prueba `0, 1, 2, …` y para en el primer `w` con `V w`)
devuelve el paso en que paró. **`fuerza_bruta_es_canal`**: el tiempo es `(primer testigo) + 1` (`Nat.find`), cabe en
`2ⁿ`, y `decodificar n : ℕ → Fin (2ⁿ)` —que **no recibe a `V`**, solo `t`— recupera el primer testigo.
`mismo_tiempo_mismo_testigo`: dos verificadores que paran a la misma hora tienen el mismo primer testigo.
`busqueda_codifica`: con el verificador «`x = w`» la fuerza bruta es una codificación inyectiva de los mensajes en
esperas `≤ 2ⁿ`, la del § 2 corrida en uno.

## 4. La filtración plantada (§ 4)

Una cláusula de 3 literales sobre 3 variables fijas es un vector de signos `s : Fin 3 → Bool` (el literal `j` es
verdadero si la variable `j` vale `s j`); la escondida `h` la satisface si `s j = h j` para algún `j`.

* `card_plantadas`: de las 8 cláusulas, la escondida satisface 7.
* **`coincide_cuatro`**: entre esas 7, cada literal coincide con la escondida en exactamente 4.
  `prob_cuatro_septimos`: la probabilidad es `4/7 > 1/2`.
* `suma_voto`: el voto `±1` de un literal suma `4 − 3 = 1` sobre las 7; **`esperanza_voto`**: con `k` cláusulas
  plantadas independientes y uniformes, la suma de votos sobre los `7^k` casos es `k · 7^(k−1)`, o sea esperanza `k/7`
  a favor (`esperanza_voto_racional`).

## 5. En característica 2 el permanente es el determinante (§ 5)

**`det_eq_permanent`**: en un anillo conmutativo de característica 2, `Matrix.det M = Matrix.permanent M`, porque el
signo de toda permutación es `±1` y `−1 = 1`. `det_eq_permanent_zmod2` sobre `ZMod 2`. Control: sobre `ℤ` la matriz
de unos `2 × 2` tiene determinante 0 y permanente 2 (`control_det_ne_permanent_int`).

## Lo que NO se prueba

* La vuelta hasta `BusquedaEnP` pide el verificador en P (`hV`); sin él no vale (ver `BuscarPolinomial`).
* El canal es sin ruido y de resolución 1: un reloj real con resolución `δ` lleva `log₂ (T/δ)` bits, y eso no está.
* La filtración es la de una cláusula y la esperanza de un voto; no hay concentración (Chernoff) ni el porcentaje de
  bits que acierta la votación en una fórmula entera.
* Que `det = perm` en `𝔽₂` no dice nada del permanente en característica 0 (Valiant): es la razón de que el
  permanente módulo 2 sea fácil, nada más.
-/

namespace Sagitta.Map.Informacion.Tiempo

open Sagitta.Map.Tiempo Sagitta.Map.Tiempo.LevinMaquinas
open Sagitta.Map.Informacion.BuscarPolinomial (enP_iff_kt)

/-! ## 1. La vuelta de `Kt` -/

section Vuelta

variable {α : Type} {enc : α ↪ List Bool} {V : α × List Bool → Bool}

variable (enc V) in
/-- **Programas cortos y rápidos**: hay un `c` tal que toda instancia de `A`, de largo `n`, la resuelve una máquina
de cslib de número `i ≤ c · log₂ (n+2) + c` en `t ≤ (n+2)^c` pasos. -/
def ProgramasCortos (A : Set α) : Prop :=
  ∃ c, ∀ a ∈ A, ∃ i t, ResuelveMT enc V a i t ∧
    i ≤ c * Nat.log 2 ((enc a).length + 2) + c ∧ t ≤ ((enc a).length + 2) ^ c

/-- `⌈log₂ ((n+2)^c)⌉ ≤ c · (log₂ (n+2) + 1)`. -/
theorem clog_pow_le (n c : ℕ) : Nat.clog 2 ((n + 2) ^ c) ≤ c * (Nat.log 2 (n + 2) + 1) := by
  apply Nat.clog_le_of_le_pow
  calc (n + 2) ^ c ≤ (2 ^ (Nat.log 2 (n + 2) + 1)) ^ c :=
        Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self one_lt_two _).le c
    _ = 2 ^ (c * (Nat.log 2 (n + 2) + 1)) := by rw [← pow_mul, mul_comm]

/-- **Programas cortos ⇒ `ktMT` logarítmica**, con constante `4c`. -/
theorem cortos_implica_kt {A : Set α} (h : ProgramasCortos enc V A) : KtMTLog enc V A := by
  obtain ⟨c, hc⟩ := h
  refine ⟨4 * c, fun a ha => ?_⟩
  obtain ⟨i, t, hres, hi, ht⟩ := hc a ha
  refine ⟨⟨i, t, hres⟩, (ktMT_le hres).trans ?_⟩
  have hL : 1 ≤ Nat.log 2 ((enc a).length + 2) := KtSAT.uno_le_log _
  have h1 : Nat.clog 2 t ≤ Nat.clog 2 (((enc a).length + 2) ^ c) := Nat.clog_mono_right 2 ht
  have h2 := clog_pow_le (enc a).length c
  set L := Nat.log 2 ((enc a).length + 2)
  have hcL : c ≤ c * L := Nat.le_mul_of_pos_right c hL
  have e1 : c * (L + 1) = c * L + c := by ring
  have e2 : 4 * c * L = 4 * (c * L) := by ring
  omega

/-- **`ktMT` logarítmica ⇒ programas cortos**, con la misma constante. -/
theorem kt_implica_cortos {A : Set α} (h : KtMTLog enc V A) : ProgramasCortos enc V A := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun a ha => ?_⟩
  obtain ⟨hres, hk⟩ := hc a ha
  obtain ⟨i, t, hit, he⟩ := ktMT_alcanzado hres
  refine ⟨i, t, hit, by omega, ?_⟩
  have hct : Nat.clog 2 t ≤ c * Nat.log 2 ((enc a).length + 2) := by omega
  exact (Nat.le_pow_clog one_lt_two t).trans (KtSAT.pow_le_de_kt hct)

theorem cortos_iff_kt {A : Set α} : ProgramasCortos enc V A ↔ KtMTLog enc V A :=
  ⟨cortos_implica_kt, kt_implica_cortos⟩

/-- **La vuelta (costo contable).** Si toda instancia de `A` la resuelve un programa corto (`i ≤ c log n + c`) y
rápido (`t ≤ (n+2)^c`), la búsqueda de Levin `buscarMT` —fija, que no conoce esos programas— halla una salida
aceptada con costo polinomial: la cota de la universal de cslib y el verificador `tV`, intento por intento. -/
theorem cortos_implica_levin_pol {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV) {A : Set α}
    (h : ProgramasCortos enc V A) : BusquedaUniversalPol enc V tV A :=
  (busqueda_iff_kt htV htVm).2 (cortos_implica_kt h)

/-- **La vuelta, en pasos simulados.** Con programas cortos y rápidos, la búsqueda de Levin halla en una ronda
`T ≤ i + ⌈log₂ t⌉` y los pasos que reparte entre las máquinas (`Levin.costoHasta T`) son menos de
`8 · 2^c · (n+2)^(2c)`: un polinomio en `n` cuyo grado y constante dependen solo de `c`. -/
theorem cortos_implica_pasos {A : Set α} (h : ProgramasCortos enc V A) :
    ∃ c, ∀ a ∈ A, ∃ T y, buscarMT enc V a T = some y ∧ V (a, y) = true ∧
      Levin.costoHasta T < 8 * 2 ^ c * ((enc a).length + 2) ^ (2 * c) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun a ha => ?_⟩
  obtain ⟨i, t, hres, hi, ht⟩ := hc a ha
  obtain ⟨T, y, hy, hV, -, hcost⟩ := levinMT_pasos hres
  refine ⟨T, y, hy, hV, hcost.trans_le ?_⟩
  set n := (enc a).length
  have h2i : 2 ^ i ≤ 2 ^ c * (n + 2) ^ c := by
    calc 2 ^ i ≤ 2 ^ (c * Nat.log 2 (n + 2) + c) := Nat.pow_le_pow_right (by norm_num) hi
      _ = 2 ^ c * 2 ^ (c * Nat.log 2 (n + 2)) := by rw [pow_add, mul_comm]
      _ ≤ 2 ^ c * (n + 2) ^ c := Nat.mul_le_mul_left _ (KtSAT.pow_le_de_kt le_rfl)
  calc 8 * 2 ^ i * t ≤ 8 * (2 ^ c * (n + 2) ^ c) * (n + 2) ^ c :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 8 h2i) ht
    _ = 8 * 2 ^ c * (n + 2) ^ (2 * c) := by ring

/-- **La equivalencia junta.** Con un verificador cobrado polinomialmente:
(i) búsqueda en P (cslib) ⇒ programas cortos y rápidos;
(ii) programas cortos y rápidos ⇔ `ktMT` logarítmica;
(iii) `ktMT` logarítmica ⇔ la búsqueda de Levin es polinomial (costo contable).
La flecha «búsqueda de Levin polinomial ⇒ búsqueda en P» la da `levin_circulo`, con el verificador en P. -/
theorem levin_equivalencias {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV) {A : Set α} :
    (BusquedaEnP enc V A → ProgramasCortos enc V A) ∧
    (ProgramasCortos enc V A ↔ KtMTLog enc V A) ∧
    (KtMTLog enc V A ↔ BusquedaUniversalPol enc V tV A) :=
  ⟨fun h => kt_implica_cortos (enP_implica_kt h), cortos_iff_kt, (busqueda_iff_kt htV htVm).symm⟩

open Turing Turing.MultiTapeTM Cslib.Complexity in
/-- **El círculo cerrado.** Con el verificador en P (y cobrado con un `tV` polinomial): búsqueda en P ⇔ programas
cortos y rápidos ⇔ `ktMT` logarítmica ⇔ búsqueda de Levin polinomial. La flecha que faltaba, de `ktMT` a P, es
`BuscarPolinomial.kt_implica_enP`: `buscarMT` hasta la ronda `c · log₂ (n+2)` es polinomial en cslib. -/
theorem levin_circulo {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    {A : Set α} :
    (BusquedaEnP enc V A ↔ ProgramasCortos enc V A) ∧
    (ProgramasCortos enc V A ↔ KtMTLog enc V A) ∧
    (KtMTLog enc V A ↔ BusquedaUniversalPol enc V tV A) :=
  ⟨(enP_iff_kt hV).trans cortos_iff_kt.symm, cortos_iff_kt, (busqueda_iff_kt htV htVm).symm⟩

open Turing Turing.MultiTapeTM Cslib.Complexity in
/-- **Programas cortos y rápidos ⇒ búsqueda en P**, con el verificador en P. -/
theorem cortos_implica_enP
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    {A : Set α} (h : ProgramasCortos enc V A) : BusquedaEnP enc V A :=
  (enP_iff_kt hV).2 (cortos_implica_kt h)

end Vuelta

open Turing Turing.MultiTapeTM Cslib.Complexity in
/-- **SAT: el círculo, sin hipótesis.** La búsqueda de SAT está en P ⇔ las satisfacibles tienen programas cortos y
rápidos ⇔ su `ktMT` es `O(log n)`. -/
theorem sat_circulo :
    (BusquedaEnP encCNF SAT.verifier SAT ↔ ProgramasCortos encCNF SAT.verifier SAT) ∧
    (ProgramasCortos encCNF SAT.verifier SAT ↔ KtMTLog encCNF SAT.verifier SAT) :=
  ⟨(enP_iff_kt SAT.computableInPolyTime_verifier).trans cortos_iff_kt.symm, cortos_iff_kt⟩

/-! ## 2. El canal de tiempo -/

section Canal

/-- **La capacidad del canal de tiempo.** Si cada mensaje de `n` bits se manda como una espera `f m ≤ T` y el
receptor lo distingue (la codificación es inyectiva), entonces `2ⁿ ≤ T + 1`. -/
theorem capacidad_canal_tiempo {n T : ℕ} (f : Fin (2 ^ n) → ℕ) (hf : Function.Injective f)
    (hT : ∀ m, f m ≤ T) : 2 ^ n ≤ T + 1 := by
  let g : Fin (2 ^ n) → Fin (T + 1) := fun m => ⟨f m, Nat.lt_succ_of_le (hT m)⟩
  have hg : Function.Injective g := fun a b hab => hf (congrArg Fin.val hab)
  simpa using Fintype.card_le_of_injective g hg

/-- **En bits**: una espera acotada por `T` lleva a lo sumo `log₂ (T+1)` bits. -/
theorem capacidad_canal_tiempo_log {n T : ℕ} (f : Fin (2 ^ n) → ℕ) (hf : Function.Injective f)
    (hT : ∀ m, f m ≤ T) : n ≤ Nat.log 2 (T + 1) :=
  Nat.le_log_of_pow_le one_lt_two (capacidad_canal_tiempo f hf hT)

/-- **Control: la cota se alcanza.** Con `T = 2ⁿ − 1`, mandar el mensaje `m` como la espera `m` (la identidad) es
inyectivo, cabe en `T`, y `2ⁿ = T + 1`. -/
theorem control_canal_identidad (n : ℕ) :
    Function.Injective (fun m : Fin (2 ^ n) => (m : ℕ)) ∧ (∀ m : Fin (2 ^ n), (m : ℕ) ≤ 2 ^ n - 1) ∧
      2 ^ n = (2 ^ n - 1) + 1 := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  exact ⟨Fin.val_injective, fun m => by have := m.isLt; omega, by omega⟩

end Canal

/-! ## 3. La fuerza bruta es ese canal -/

section FuerzaBruta

/-- El verificador sobre `Fin (2ⁿ)`, extendido a `ℕ` (fuera del rango, falso). -/
def verifN {n : ℕ} (V : Fin (2 ^ n) → Bool) (k : ℕ) : Bool := if h : k < 2 ^ n then V ⟨k, h⟩ else false

/-- La búsqueda en orden con combustible `f`, desde el candidato `w`: prueba `w, w+1, …` y devuelve el **paso** en
que paró (el número de candidatos probados contando desde `0`). Solo devuelve un número: el tiempo. -/
def pasos (P : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, w => w
  | f + 1, w => if P w then w + 1 else pasos P f (w + 1)

/-- La búsqueda para justo después del primer testigo `m` a partir de `w`. -/
theorem pasos_eq {P : ℕ → Bool} {m : ℕ} (hm : P m = true) :
    ∀ f w, (∀ k, w ≤ k → k < m → P k = false) → w ≤ m → m < w + f → pasos P f w = m + 1 := by
  intro f
  induction f with
  | zero => intro w _ hw h; omega
  | succ f ih =>
    intro w hpre hw hf
    unfold pasos
    by_cases hP : P w = true
    · simp only [hP, ↓reduceIte]
      rcases Nat.lt_or_ge w m with hlt | hge
      · rw [hpre w le_rfl hlt] at hP; exact absurd hP (by simp)
      · omega
    · simp only [Bool.not_eq_true] at hP
      simp only [hP, Bool.false_eq_true, ↓reduceIte]
      have hne : w ≠ m := fun he => by rw [he, hm] at hP; exact absurd hP (by simp)
      exact ih (w + 1) (fun k hk hkm => hpre k (by omega) hkm) (by omega) (by omega)

/-- **El tiempo de la fuerza bruta** sobre `Fin (2ⁿ)`: el paso en que para la búsqueda en orden. -/
def tiempoBusqueda {n : ℕ} (V : Fin (2 ^ n) → Bool) : ℕ := pasos (verifN V) (2 ^ n) 0

/-- **El decodificador.** Solo recibe `n` y el tiempo `t`: no ve al verificador ni a la fórmula. -/
def decodificar (n t : ℕ) : Fin (2 ^ n) := ⟨(t - 1) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

theorem existe_verifN {n : ℕ} {V : Fin (2 ^ n) → Bool} (h : ∃ w, V w = true) : ∃ k, verifN V k = true := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by simp [verifN, w.isLt, hw]⟩

theorem lt_de_verifN {n : ℕ} {V : Fin (2 ^ n) → Bool} {k : ℕ} (h : verifN V k = true) : k < 2 ^ n := by
  unfold verifN at h
  split_ifs at h with hk
  exact hk

/-- **El tiempo es el primer testigo más uno** (`Nat.find`). -/
theorem tiempoBusqueda_eq {n : ℕ} {V : Fin (2 ^ n) → Bool} (h : ∃ w, V w = true) :
    tiempoBusqueda V = Nat.find (existe_verifN h) + 1 := by
  have hm := Nat.find_spec (existe_verifN h)
  have hlt := lt_de_verifN hm
  refine pasos_eq hm (2 ^ n) 0 (fun k _ hk => ?_) (Nat.zero_le _) (by omega)
  exact Bool.eq_false_iff.2 (Nat.find_min (existe_verifN h) hk)

/-- **La fuerza bruta es el canal de tiempo.** Si `V` tiene testigo, la búsqueda en orden para en
`t = (primer testigo) + 1 ≤ 2ⁿ`, y `decodificar n t` —que no mira nada más que `t`— es un testigo, el primero. -/
theorem fuerza_bruta_es_canal {n : ℕ} (V : Fin (2 ^ n) → Bool) (h : ∃ w, V w = true) :
    tiempoBusqueda V = (decodificar n (tiempoBusqueda V) : ℕ) + 1 ∧ 1 ≤ tiempoBusqueda V ∧
      tiempoBusqueda V ≤ 2 ^ n ∧ V (decodificar n (tiempoBusqueda V)) = true ∧
      ∀ w, V w = true → decodificar n (tiempoBusqueda V) ≤ w := by
  have hm := Nat.find_spec (existe_verifN h)
  have hlt := lt_de_verifN hm
  have ht := tiempoBusqueda_eq h
  have hdec : (decodificar n (tiempoBusqueda V) : ℕ) = Nat.find (existe_verifN h) := by
    simp only [decodificar, ht, Nat.add_sub_cancel]
    exact Nat.mod_eq_of_lt hlt
  refine ⟨by rw [hdec, ht], by omega, by omega, ?_, fun w hw => ?_⟩
  · have : decodificar n (tiempoBusqueda V) = ⟨Nat.find (existe_verifN h), hlt⟩ := Fin.ext hdec
    rw [this]
    have hm' := hm
    unfold verifN at hm'
    split_ifs at hm' with hh
    exact hm'
  · change (decodificar n (tiempoBusqueda V) : ℕ) ≤ w
    rw [hdec]
    exact Nat.find_min' _ (by simp [verifN, w.isLt, hw])

/-- **Mismo tiempo, mismo testigo.** Dos verificadores con testigo cuyas búsquedas paran a la misma hora tienen el
mismo primer testigo: todo lo que el receptor sabe está en `t`. -/
theorem mismo_tiempo_mismo_testigo {n : ℕ} {V V' : Fin (2 ^ n) → Bool} (h : ∃ w, V w = true)
    (h' : ∃ w, V' w = true) (ht : tiempoBusqueda V = tiempoBusqueda V') :
    Nat.find (existe_verifN h) = Nat.find (existe_verifN h') := by
  have := (tiempoBusqueda_eq h).symm.trans (ht.trans (tiempoBusqueda_eq h'))
  omega

/-- **La fuerza bruta codifica.** El mensaje `w` se manda como el tiempo de la búsqueda con el verificador
«`x = w`»: es `w + 1`, inyectivo y `≤ 2ⁿ`. Es una codificación del § 2 con `T = 2ⁿ`, y por eso la búsqueda en orden
no puede pararse antes, en el peor caso, que en `2ⁿ`: tiene que recorrer todo el canal. -/
theorem busqueda_codifica (n : ℕ) :
    Function.Injective (fun w : Fin (2 ^ n) => tiempoBusqueda (fun x => decide (x = w))) ∧
      ∀ w : Fin (2 ^ n), tiempoBusqueda (fun x => decide (x = w)) = (w : ℕ) + 1 := by
  have hval : ∀ w : Fin (2 ^ n), tiempoBusqueda (fun x => decide (x = w)) = (w : ℕ) + 1 := by
    intro w
    obtain ⟨e, -, -, hV, hmin⟩ := fuerza_bruta_es_canal (fun x => decide (x = w)) ⟨w, by simp⟩
    have hw : decodificar n (tiempoBusqueda (fun x => decide (x = w))) = w := by simpa using hV
    rw [e, hw]
  refine ⟨fun a b hab => ?_, hval⟩
  have := (hval a).symm.trans (hab.trans (hval b))
  exact Fin.ext (by simpa using this)

end FuerzaBruta

/-! ## 4. La filtración plantada -/

section Plantada

/-- La escondida `h` satisface la cláusula de signos `s` si algún literal coincide. -/
def satisface (h s : Fin 3 → Bool) : Bool := decide (∃ j, s j = h j)

/-- Las cláusulas (vectores de signos) que la escondida satisface. -/
def plantadas (h : Fin 3 → Bool) : Finset (Fin 3 → Bool) := Finset.univ.filter (fun s => satisface h s = true)

/-- De las 8 cláusulas sobre tres variables, la escondida satisface 7. -/
theorem card_plantadas (h : Fin 3 → Bool) : (plantadas h).card = 7 := by
  revert h; decide

/-- **La filtración.** Entre las 7 cláusulas que la escondida satisface, el literal `j` coincide con la escondida en
exactamente 4. -/
theorem coincide_cuatro (h : Fin 3 → Bool) (j : Fin 3) :
    ((plantadas h).filter (fun s => s j = h j)).card = 4 := by
  revert h j; decide

/-- Y no coincide en 3. -/
theorem no_coincide_tres (h : Fin 3 → Bool) (j : Fin 3) :
    ((plantadas h).filter (fun s => ¬ s j = h j)).card = 3 := by
  revert h j; decide

/-- **La probabilidad es `4/7 > 1/2`.** -/
theorem prob_cuatro_septimos (h : Fin 3 → Bool) (j : Fin 3) :
    (((plantadas h).filter (fun s => s j = h j)).card : ℚ) / (plantadas h).card = 4 / 7 ∧ (4 : ℚ) / 7 > 1 / 2 := by
  rw [coincide_cuatro, card_plantadas]
  norm_num

/-- El voto del literal `j`: `+1` si su signo coincide con la escondida, `−1` si no. -/
def voto (h : Fin 3 → Bool) (j : Fin 3) (s : Fin 3 → Bool) : ℤ := if s j = h j then 1 else -1

/-- **Una cláusula plantada vota `4 − 3 = 1`** a favor de la escondida, sumado sobre las 7. -/
theorem suma_voto (h : Fin 3 → Bool) (j : Fin 3) : ∑ s ∈ plantadas h, voto h j s = 1 := by
  revert h j; decide

/-- Suma sobre todas las `k`-tuplas de una función de una sola coordenada. -/
theorem suma_coordenada {β : Type} [Fintype β] {k : ℕ} (g : β → ℤ) (i : Fin k) :
    ∑ c : Fin k → β, g (c i) = (Fintype.card β : ℤ) ^ (k - 1) * ∑ b, g b := by
  have e : ∀ c : Fin k → β, g (c i) = ∏ j, (if j = i then g (c j) else 1) := by
    intro c
    rw [Finset.prod_ite_eq']; simp
  simp_rw [e]
  rw [← Fintype.prod_sum (fun j b => if j = i then g b else 1)]
  have e2 : ∀ j : Fin k, (∑ b, if j = i then g b else (1 : ℤ)) =
      if j = i then ∑ b, g b else (Fintype.card β : ℤ) := by
    intro j; split_ifs <;> simp
  simp_rw [e2]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_eq', Finset.filter_ne']
  simp only [Finset.mem_univ, ite_true, Finset.card_singleton, pow_one, Finset.card_erase_of_mem,
    Finset.card_univ, Fintype.card_fin]
  ring

/-- **La esperanza del voto.** Si una variable aparece en `k` cláusulas plantadas, cada una elegida uniforme entre
las 7 que satisface la escondida (todas sobre la misma tripleta de variables, con la variable en la posición `j`), la
suma de los votos sobre los `7^k` casos es `k · 7^(k−1)`: en promedio, `k/7` a favor. -/
theorem esperanza_voto (h : Fin 3 → Bool) (j : Fin 3) (k : ℕ) :
    ∑ c : Fin k → plantadas h, ∑ i, voto h j (c i) = k * 7 ^ (k - 1) := by
  rw [Finset.sum_comm]
  have hcard : Fintype.card (plantadas h) = 7 := by rw [Fintype.card_coe, card_plantadas]
  have h1 : ∑ b : plantadas h, voto h j b = 1 := by
    rw [Finset.sum_coe_sort (plantadas h) (voto h j)]; exact suma_voto h j
  simp_rw [suma_coordenada (fun b : plantadas h => voto h j b), hcard, h1]
  simp

/-- La esperanza, como número racional: `k/7`. -/
theorem esperanza_voto_racional (h : Fin 3 → Bool) (j : Fin 3) (k : ℕ) :
    ((∑ c : Fin k → plantadas h, ∑ i, voto h j (c i) : ℤ) : ℚ) / 7 ^ k = k / 7 := by
  rw [esperanza_voto]
  rcases k with _ | k
  · simp
  · push_cast
    rw [pow_succ]
    field_simp

end Plantada

/-! ## 5. En característica 2, el permanente es el determinante -/

section Permanente

/-- **`det = perm` en característica 2.** El signo de toda permutación es `±1`, y `−1 = 1`. -/
theorem det_eq_permanent {R : Type*} [CommRing R] [CharP R 2] {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m R) : M.det = M.permanent := by
  rw [Matrix.det_apply, Matrix.permanent]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
  · rw [hs, Units.neg_smul, one_smul, CharTwo.neg_eq]

/-- Sobre `ZMod 2`. -/
theorem det_eq_permanent_zmod2 {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m (ZMod 2)) :
    M.det = M.permanent := det_eq_permanent M

/-- **Control: en característica 0 no.** Sobre `ℤ`, la matriz de unos `2 × 2` tiene determinante 0 y permanente 2. -/
theorem control_det_ne_permanent_int :
    (Matrix.of fun _ _ => (1 : ℤ) : Matrix (Fin 2) (Fin 2) ℤ).det = 0 ∧
      (Matrix.of fun _ _ => (1 : ℤ) : Matrix (Fin 2) (Fin 2) ℤ).permanent = 2 := by
  constructor
  · rw [Matrix.det_fin_two]; simp
  · decide

end Permanente

end Sagitta.Map.Informacion.Tiempo
