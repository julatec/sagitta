import Sagitta.Map.KtSAT
import Sagitta.Map.Levin
import Sagitta.Map.RondasAcotadas
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.ResourceBound
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Levin en tiempo de máquina

`KtSAT` probó, sobre el presupuesto de `evaln`, que buscar una solución de SAT en el universo cerrado cuesta del orden
de `2^{kt}` y que «SAT es fácil en el modelo» equivale a «`kt` logarítmica». `RondasAcotadas` mostró que ese presupuesto
no es tiempo honesto (`evaln_no_acotado`) y que los pasos de una máquina multicinta de cslib sí lo son
(`mt_es_acotada`). Este archivo reenuncia aquello **sobre los pasos de las máquinas de cslib**.

## Qué se prueba, y sobre qué medida

* **Las máquinas numeradas** (§ 1–2). La máquina número `i` es la descripción de cslib (`Universal.Desc`) que el
  decodificador de cslib saca de la palabra número `i` (codificación de Mathlib de `List Bool`); toda descripción
  tiene número (`maquina_indiceDe`). Correrla `t` pasos es correr la **universal de cslib** con reloj `t`
  (`correrMT`); el reloj solo agrega (`correrMT_mono`) y una `MultiTapeTM` binaria de cslib corre por su número
  (`correrMT_de_maquina`, vía `universal_desc`). Lo que se cuenta son pasos de máquinas de cslib, que son rondas
  acotadas por `mt_es_acotada`.
* **La búsqueda universal** (§ 3): en la ronda `T`, cada máquina `i ≤ T` corre `2^(T-i)` pasos y su salida pasa por
  el verificador. Es correcta (`buscarMT_acepta`), halla en la ronda `i + ⌈log₂ t⌉` si la máquina `i` resuelve en `t`
  pasos (`buscarMT_halla`) y, en pasos simulados, cuesta menos de `8 · 2ⁱ · t` (`levinMT_pasos`).
* **La contabilidad, aparte** (§ 4). Cada intento se cobra con la cota de la universal de cslib,
  `(I+1)^4 · (s+1)^2` (`cotaU`, que es literalmente la de `computableInO_universal_polynomialBound`), más un
  verificador `tV` sobre el par (instancia, salida). `levinMT`: costo total
  `≤ 16 · ancho^4 · 4ⁱ · (2t)² + (T+1)² · tV (2n + 1 + 2ⁱ · 2t)`, con `ancho` lineal en `n` y en el tamaño de las
  máquinas en juego, que crece polinomialmente (`tamHasta_pol`). **El factor de la máquina es `4ⁱ`, no `2ⁱ`**: el
  sobrecosto de la universal es cuadrático en el reloj, y en la ronda `T` la máquina `0` corre `2^T` pasos.
* **La consecuencia para P** (§ 5, `busqueda_universal_pol`, y para SAT `sat_busqueda_universal_pol`): si alguna
  máquina de cslib calcula la búsqueda en tiempo polinomial, la búsqueda universal —fija, la misma para cualquiera
  que resuelva— es polinomial; la máquina solo aporta constantes.
* **La `ktMT`** (§ 6): `ktMT a = min (i + ⌈log₂ t⌉)` sobre las máquinas de cslib que resuelven `a` en `t` pasos.
  (a) `ktMT_le`; (b) `costo_le_ktMT`. La equivalencia `busqueda_iff_kt` (y `sat_busqueda_iff_kt`): la búsqueda
  universal es polinomial si y solo si `ktMT` es `O(log n)`, **las dos direcciones incondicionales**. Además
  `enP_implica_kt`: búsqueda en P implica `ktMT` logarítmica.

## La lectura

Con tiempo de máquina, el universo cerrado del proyecto **es la búsqueda universal de Levin**. Por eso, si P = NP
para la búsqueda, ya se conoce un algoritmo polinomial: este, que no depende de cuál sea la máquina rápida. Es un
hecho clásico (Levin, 1973), reenunciado sobre las máquinas de cslib.

## Lo que NO se prueba

* **La búsqueda no se construyó como una máquina de cslib.** El costo es contable: la suma de las cotas de la
  universal y del verificador, intento por intento. No se prueba que exista una `MultiTapeTM` que ejecute
  `buscarMT` dentro de un polinomio de ese costo (falta componer, en cslib, el bucle de rondas, la universal con
  reloj binario y el verificador). Por eso la vuelta «`ktMT` logarítmica ⇒ búsqueda en P» queda **condicional** a
  esa implementación (`kt_implica_enP_condicional`, con la hipótesis `hImpl` explícita).
* **Relativiza en el verificador.** `tV` se toma como dado (para SAT, `verificador_sat` muestra que el de cslib tiene
  un reloj polinomial); nada aquí mira dentro del verificador.
* **Nada sobre P contra NP.** Esto **reformula**, no decide: traduce «la búsqueda de SAT está en P» a «la `ktMT` de
  las satisfacibles es logarítmica», sin decir cuál de las dos cosas pasa.
* El número de una máquina es el código de Mathlib de su palabra: la constante `4ⁱ` es enorme, aunque no dependa de
  la entrada.
-/

namespace Sagitta.Map.Tiempo.LevinMaquinas

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.Complexity

/-! ## 1. Las máquinas numeradas -/

/-- La palabra número `i`: la de código `i` en la codificación de Mathlib de `List Bool`, o la vacía si `i` no es
código de ninguna. -/
def palabra (i : ℕ) : List Bool := (Encodable.decode₂ (List Bool) i).getD []

theorem palabra_encode (w : List Bool) : palabra (Encodable.encode w) = w := by
  simp [palabra]

theorem length_palabra_le (i : ℕ) : (palabra i).length ≤ i := by
  unfold palabra
  cases h : Encodable.decode₂ (List Bool) i with
  | none => simp
  | some w =>
    have := Encodable.mem_decode₂.1 h
    simpa [← this] using Encodable.length_le_encode w

/-- **La máquina número `i`**: la descripción de cslib que el decodificador de cslib saca de la palabra número `i`.
Toda palabra decodifica a alguna descripción, así que toda `i` es una máquina. -/
def maquina (i : ℕ) : Desc := decodeDesc (palabra i)

/-- El número de una descripción. -/
def indiceDe (d : Desc) : ℕ := Encodable.encode (eDesc d)

/-- **Toda descripción tiene número.** -/
theorem maquina_indiceDe (d : Desc) : maquina (indiceDe d) = d := by
  rw [maquina, indiceDe, palabra_encode, decodeDesc_eDesc]

/-! ## 2. Correr la máquina `i` con reloj, por la universal de cslib -/

/-- Correr la máquina `i` sobre la palabra `x` durante `t` pasos con la función universal de cslib: si paró, su
salida, leída como bits; si no, nada. -/
def correrMT (i : ℕ) (x : List Bool) (t : ℕ) : Option (List Bool) :=
  if (universal (maquina i, x.map eBit, t)).2 then
    some ((universal (maquina i, x.map eBit, t)).1.map (· != 0))
  else none

/-- Un paso de la simulación sobre una configuración parada no hace nada. -/
theorem stepOut_parado (d : Desc) (x : List ℕ) (c : SCfg × List ℕ) (h : c.1.state = none) :
    stepOut d x c = c := by
  obtain ⟨⟨s, p, w⟩, o⟩ := c
  simp only at h
  subst h
  simp [stepOut, Universal.step]

/-- Una vez parada, la simulación se queda quieta. -/
theorem iterate_parado (d : Desc) (x : List ℕ) (c : SCfg × List ℕ) (h : c.1.state = none) (n : ℕ) :
    (stepOut d x)^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, stepOut_parado d x c h]

/-- **La simulación, parada, no cambia con más pasos.** -/
theorem simulate_mono {d : Desc} {x : List ℕ} {t t' : ℕ} {o : List ℕ} (h : simulate d x t = (o, true))
    (ht : t ≤ t') : simulate d x t' = (o, true) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  unfold simulate at h ⊢
  simp only [Prod.mk.injEq] at h
  rw [add_comm, Function.iterate_add_apply,
    iterate_parado d x _ (Option.isNone_iff_eq_none.1 h.2)]
  simp [h.1, h.2]

/-- **Con más reloj, la misma respuesta.** -/
theorem correrMT_mono {i t t' : ℕ} {x y : List Bool} (h : correrMT i x t = some y) (ht : t ≤ t') :
    correrMT i x t' = some y := by
  unfold correrMT at h ⊢
  split_ifs at h with hs
  have hu : simulate (maquina i) (x.map eBit) t = ((universal (maquina i, x.map eBit, t)).1, true) := by
    rw [← hs]; rfl
  have hu' := simulate_mono hu ht
  have : universal (maquina i, x.map eBit, t') = ((universal (maquina i, x.map eBit, t)).1, true) := hu'
  rw [this]
  simpa using h

/-- Con reloj cero no para nadie: la configuración inicial tiene estado. -/
theorem correrMT_cero (i : ℕ) (x : List Bool) : correrMT i x 0 = none := by
  simp [correrMT, universal, simulate, init]

/-- Cada paso emite a lo sumo un símbolo. -/
theorem length_salida_le (d : Desc) (x : List ℕ) (t : ℕ) : (simulate d x t).1.length ≤ t := by
  have h : ∀ (n : ℕ) (c : SCfg × List ℕ), ((stepOut d x)^[n] c).2.length ≤ c.2.length + n := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [Function.iterate_succ_apply']
      have h1 := ih c
      have h2 : (stepOut d x ((stepOut d x)^[n] c)).2.length ≤ ((stepOut d x)^[n] c).2.length + 1 := by
        simp only [stepOut, List.length_append]
        have : ((step d x ((stepOut d x)^[n] c).1).2.toList).length ≤ 1 := by
          cases (step d x ((stepOut d x)^[n] c).1).2 <;> simp
        omega
      omega
  simpa [simulate] using h t (init d, [])

/-- **La respuesta mide a lo sumo el reloj.** -/
theorem length_correrMT_le {i t : ℕ} {x y : List Bool} (h : correrMT i x t = some y) : y.length ≤ t := by
  unfold correrMT at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  subst h
  rw [List.length_map]
  exact length_salida_le (maquina i) (x.map eBit) t

theorem eBit_ne_zero (b : Bool) : (eBit b != 0) = b := by cases b <;> rfl

/-- Los bits pasados a símbolos y de vuelta. -/
theorem map_eBit_ne_zero (y : List Bool) : (y.map eBit).map (· != 0) = y := by
  induction y with
  | nil => rfl
  | cons b y ih => rw [List.map_cons, List.map_cons, ih, eBit_ne_zero]

/-- **Una máquina de cslib corre por su número.** Si una `MultiTapeTM` binaria, de estados finitos, para sobre `x`
a los `t` pasos con salida `y`, entonces `correrMT` de su número da `y` con reloj `t`. -/
theorem correrMT_de_maquina {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S)
    {x : List Bool} {t : ℕ} (hh : (tm.runFrom (tm.initCfg x) t).Halted) :
    correrMT (indiceDe (desc eS eBit tm)) x t = some (tm.runFrom (tm.initCfg x) t).output := by
  unfold correrMT
  rw [maquina_indiceDe, universal_desc]
  have : (tm.runFrom (tm.initCfg x) t).state.isNone = true := Option.isNone_iff_eq_none.2 hh
  simp only [this, ↓reduceIte, map_eBit_ne_zero]


/-! ## 3. La búsqueda por rondas -/

section Busqueda

variable {α : Type} (enc : α ↪ List Bool) (V : α × List Bool → Bool)

/-- En la ronda `T`, la máquina `i` corre `2^(T-i)` pasos; su salida se conserva solo si el verificador la acepta. -/
def intentoMT (a : α) (T i : ℕ) : Option (List Bool) :=
  (correrMT i (enc a) (2 ^ (T - i))).filter (fun y => V (a, y))

/-- La ronda `T`: las máquinas `0, …, T`, en orden; la primera respuesta aceptada. -/
def rondaMT (a : α) (T : ℕ) : Option (List Bool) :=
  (List.range (T + 1)).findSome? (intentoMT enc V a T)

/-- **La búsqueda universal**, hasta la ronda `T`: la primera ronda que entrega algo. No depende de ninguna máquina
en particular: solo del verificador. -/
def buscarMT (a : α) (T : ℕ) : Option (List Bool) :=
  (List.range (T + 1)).findSome? (rondaMT enc V a)

/-- La máquina `i` resuelve `a` con reloj `t`: para en `t` pasos y el verificador acepta su salida. -/
def ResuelveMT (a : α) (i t : ℕ) : Prop := ∃ y, correrMT i (enc a) t = some y ∧ V (a, y) = true

variable {enc V}

theorem intentoMT_acepta {a : α} {T i : ℕ} {y : List Bool} (h : intentoMT enc V a T i = some y) :
    V (a, y) = true := (Option.filter_eq_some_iff.1 h).2

/-- **De dónde sale la respuesta**: de una máquina `i ≤ T' ≤ T` que paró en `2^(T'-i)` pasos con salida aceptada. -/
theorem buscarMT_origen {a : α} {T : ℕ} {y : List Bool} (h : buscarMT enc V a T = some y) :
    ∃ T' i, T' ≤ T ∧ i ≤ T' ∧ correrMT i (enc a) (2 ^ (T' - i)) = some y ∧ V (a, y) = true := by
  obtain ⟨T', hT', ht⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨i, hi, hi'⟩ := List.exists_of_findSome?_eq_some ht
  obtain ⟨hc, hv⟩ := Option.filter_eq_some_iff.1 hi'
  exact ⟨T', i, Nat.lt_succ_iff.1 (List.mem_range.1 hT'), Nat.lt_succ_iff.1 (List.mem_range.1 hi), hc, hv⟩

/-- **Corrección.** Todo lo que la búsqueda entrega lo acepta el verificador. -/
theorem buscarMT_acepta {a : α} {T : ℕ} {y : List Bool} (h : buscarMT enc V a T = some y) :
    V (a, y) = true := (buscarMT_origen h).choose_spec.choose_spec.2.2.2

/-- **Completitud, con cota de rondas.** Si la máquina `i` resuelve `a` en `t` pasos, la búsqueda entrega algo en
cuanto llega a la ronda `i + ⌈log₂ t⌉`. -/
theorem buscarMT_halla {a : α} {i t T : ℕ} (h : ResuelveMT enc V a i t) (hT : i + Nat.clog 2 t ≤ T) :
    ∃ y', buscarMT enc V a T = some y' := by
  obtain ⟨y, hy, hV⟩ := h
  have hint : intentoMT enc V a (i + Nat.clog 2 t) i = some y := by
    unfold intentoMT
    rw [Nat.add_sub_cancel_left, correrMT_mono hy (Nat.le_pow_clog one_lt_two t)]
    simp [hV]
  have hr : (rondaMT enc V a (i + Nat.clog 2 t)).isSome := by
    unfold rondaMT
    rw [List.findSome?_isSome_iff]
    exact ⟨i, List.mem_range.2 (by omega), by simp [hint]⟩
  have hb : (buscarMT enc V a T).isSome := by
    unfold buscarMT
    rw [List.findSome?_isSome_iff]
    exact ⟨i + Nat.clog 2 t, List.mem_range.2 (by omega), hr⟩
  exact Option.isSome_iff_exists.1 hb

/-- **Halla, no decide.** Si ninguna máquina resuelve `a` con ningún reloj, la búsqueda no entrega nada. -/
theorem buscarMT_nada {a : α} (h : ∀ i t, ¬ ResuelveMT enc V a i t) (T : ℕ) :
    buscarMT enc V a T = none := by
  cases hb : buscarMT enc V a T with
  | none => rfl
  | some y =>
    obtain ⟨T', i, -, -, hc, hv⟩ := buscarMT_origen hb
    exact absurd ⟨y, hc, hv⟩ (h i _)

/-- Resolver necesita al menos un paso. -/
theorem ResuelveMT.uno_le {a : α} {i t : ℕ} (h : ResuelveMT enc V a i t) : 1 ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · obtain ⟨y, hy, -⟩ := h
    rw [correrMT_cero] at hy
    exact absurd hy (by simp)
  · exact ht

/-- **Levin en pasos simulados.** Los pasos que la búsqueda le reparte a las máquinas hasta la ronda en que halla
son exactamente los presupuestos de `Sagitta.Map.Levin.costoHasta`, y son menos de `8 · 2ⁱ · t`. -/
theorem levinMT_pasos {a : α} {i t : ℕ} (h : ResuelveMT enc V a i t) :
    ∃ T y, buscarMT enc V a T = some y ∧ V (a, y) = true ∧ T ≤ i + Nat.clog 2 t ∧
      Levin.costoHasta T < 8 * 2 ^ i * t := by
  have ht := h.uno_le
  obtain ⟨y, hy⟩ := buscarMT_halla h le_rfl
  refine ⟨i + Nat.clog 2 t, y, hy, buscarMT_acepta hy, le_rfl, ?_⟩
  have h1 := Levin.costoHasta_lt (i + Nat.clog 2 t)
  have h2 : 2 ^ (i + Nat.clog 2 t + 2) = 4 * 2 ^ i * 2 ^ Nat.clog 2 t := by
    rw [pow_add, pow_add]; ring
  have h3 : 4 * 2 ^ i * 2 ^ Nat.clog 2 t < 4 * 2 ^ i * (2 * t) :=
    Nat.mul_lt_mul_of_pos_left (Levin.pow_clog_lt ht) (by positivity)
  have h4 : 4 * 2 ^ i * (2 * t) = 8 * 2 ^ i * t := by ring
  omega

end Busqueda


/-! ## 4. El costo, con la cota de la universal de cslib -/

/-- **La cota de tiempo de la universal de cslib** para correr la descripción `d` sobre `x` durante `s` pasos:
`(I + 1)^4 · (s + 1)^2`, con `I` el largo de la entrada codificada de la universal. Es literalmente la función de
`computableInO_universal_polynomialBound` (`cotaU_es_de_cslib`). -/
def cotaU (d : Desc) (x : List Bool) (s : ℕ) : ℕ := ((eIn (d, x.map eBit, s)).length + 1) ^ 4 * (s + 1) ^ 2

/-- **`cotaU` es la cota de cslib**: la universal corre en tiempo `O(cotaU)` (constante y máquina de cslib). -/
theorem cotaU_es_de_cslib :
    ComputableInO universal eIn eOut (fun i => ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2)
      (fun i => ((eIn i).length + 1) ^ 2 * (i.2.2 + 1)) ∧
    ∀ d x s, cotaU d x s = (fun i : Desc × List ℕ × ℕ => ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2)
      (d, x.map eBit, s) :=
  ⟨computableInO_universal_polynomialBound, fun _ _ _ => rfl⟩

/-- El tamaño de la mayor máquina en juego hasta la ronda `T`. -/
def tamHasta (T : ℕ) : ℕ := (Finset.range (T + 1)).sup fun j => (eDesc (maquina j)).length

theorem tam_le_tamHasta {i T : ℕ} (h : i ≤ T) : (eDesc (maquina i)).length ≤ tamHasta T :=
  Finset.le_sup (f := fun j => (eDesc (maquina j)).length) (Finset.mem_range.2 (Nat.lt_succ_of_le h))

theorem tamHasta_mono : Monotone tamHasta := fun _ _ h =>
  Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ h))

/-- **Las máquinas en juego crecen polinomialmente**: el decodificador de cslib es de grado fijo y la palabra número
`j` mide a lo sumo `j`. -/
theorem tamHasta_pol : tamHasta ∈ Pol := by
  obtain ⟨d, e, hdeg⟩ := exists_computableInDegree_decodeDesc
  obtain ⟨c, hc⟩ := hdeg.2
  refine ⟨c, e, fun T => Finset.sup_le fun j hj => ?_⟩
  have hj' : j ≤ T := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have h1 : (eDesc (decodeDesc (palabra j))).length ≤ c * ((palabra j).length + 1) ^ e := hc (palabra j)
  calc (eDesc (maquina j)).length ≤ c * ((palabra j).length + 1) ^ e := h1
    _ ≤ c * (T + 1) ^ e :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := length_palabra_le j; omega) _)

section Costo

variable {α : Type} (enc : α ↪ List Bool) (V : α × List Bool → Bool)

/-- El costo de un intento: la universal, con la cota de cslib, más el verificador `tV`, cobrado sobre el largo
máximo del par (instancia, salida); la salida mide a lo sumo el reloj (`largo_par_le`). -/
def costoIntento (tV : ℕ → ℕ) (a : α) (T i : ℕ) : ℕ :=
  cotaU (maquina i) (enc a) (2 ^ (T - i)) + tV (2 * (enc a).length + 1 + 2 ^ (T - i))

/-- El costo de la ronda `T`. -/
def costoRondaMT (tV : ℕ → ℕ) (a : α) (T : ℕ) : ℕ := ∑ i ∈ Finset.range (T + 1), costoIntento enc tV a T i

/-- **El costo de la búsqueda hasta la ronda `T`.** -/
def costoHastaMT (tV : ℕ → ℕ) (a : α) (T : ℕ) : ℕ := ∑ T' ∈ Finset.range (T + 1), costoRondaMT enc tV a T'

/-- El ancho de las entradas de la universal hasta la ronda `T`. -/
def anchoMT (a : α) (T : ℕ) : ℕ := 2 * tamHasta T + 6 * (enc a).length + T + 5

variable {enc V}

/-- **El cobro del verificador alcanza**: el par que se verifica mide a lo sumo lo que se cobra. -/
theorem largo_par_le {a : α} {T i : ℕ} {y : List Bool} (h : intentoMT enc V a T i = some y) :
    (encPair enc encBits (a, y)).length ≤ 2 * (enc a).length + 1 + 2 ^ (T - i) := by
  have := length_correrMT_le (Option.filter_eq_some_iff.1 h).1
  rw [length_encPair]
  exact Nat.add_le_add_left this _

theorem cuatro_pow (m : ℕ) : (2 ^ m) ^ 2 = 4 ^ m := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- Un intento de la ronda `T' ≤ T` cuesta a lo sumo `ancho^4 · 4 · 4^(T'-i)` en la universal. -/
theorem cotaU_le {a : α} {i T' T : ℕ} (hi : i ≤ T') (hT : T' ≤ T) :
    cotaU (maquina i) (enc a) (2 ^ (T' - i)) ≤ anchoMT enc a T ^ 4 * (4 * 4 ^ (T' - i)) := by
  unfold cotaU
  have h1 := tam_le_tamHasta (le_trans hi hT)
  have h2 := length_encList_map_eBit_le (enc a)
  have h3 : (encNat (2 ^ (T' - i))).length ≤ T' - i + 1 := length_encNat_le_of_le_two_pow le_rfl
  have hlen : (eIn (maquina i, (enc a).map eBit, 2 ^ (T' - i))).length + 1 ≤ anchoMT enc a T := by
    simp only [eIn, length_encPair, anchoMT]
    omega
  have hs : (2 ^ (T' - i) + 1) ^ 2 ≤ 4 * 4 ^ (T' - i) := by
    have hp : 1 ≤ 2 ^ (T' - i) := Nat.one_le_two_pow
    calc (2 ^ (T' - i) + 1) ^ 2 ≤ (2 * 2 ^ (T' - i)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * 4 ^ (T' - i) := by rw [mul_pow, cuatro_pow]; norm_num
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hlen 4) hs

/-- `3 · (4^T + 4^(T-1) + … + 1) + 1 = 4^(T+1)`. -/
theorem suma_cuatro (T : ℕ) : 3 * ∑ i ∈ Finset.range (T + 1), 4 ^ (T - i) + 1 = 4 ^ (T + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h : ∑ i ∈ Finset.range (T + 1 + 1), 4 ^ (T + 1 - i) =
        4 * ∑ i ∈ Finset.range (T + 1), 4 ^ (T - i) + 1 := by
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have : T + 1 - i = (T - i) + 1 := by have := Finset.mem_range.1 hi; omega
      rw [this, pow_succ']
    rw [h, pow_succ' 4 (T + 1)]
    omega

/-- `3 · (1 + 4 + … + 4^T) + 1 = 4^(T+1)`. -/
theorem suma_geom_cuatro (T : ℕ) : 3 * ∑ T' ∈ Finset.range (T + 1), 4 ^ T' + 1 = 4 ^ (T + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, pow_succ' 4 (T + 1)]
    omega

/-- **El costo de la búsqueda hasta la ronda `T`**: a lo sumo `16 · ancho^4 · 4^T` en la universal más
`(T+1)²` verificaciones de pares de largo a lo sumo `2n + 1 + 2^T`. -/
theorem costoHastaMT_le {tV : ℕ → ℕ} (htV : Monotone tV) (a : α) (T : ℕ) :
    costoHastaMT enc tV a T ≤
      16 * anchoMT enc a T ^ 4 * 4 ^ T + (T + 1) ^ 2 * tV (2 * (enc a).length + 1 + 2 ^ T) := by
  set W := anchoMT enc a T
  set v := tV (2 * (enc a).length + 1 + 2 ^ T)
  have hint : ∀ T' ∈ Finset.range (T + 1), ∀ i ∈ Finset.range (T' + 1),
      costoIntento enc tV a T' i ≤ W ^ 4 * 4 * 4 ^ (T' - i) + v := by
    intro T' hT' i hi
    have hT'' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hT')
    have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 : cotaU (maquina i) (enc a) (2 ^ (T' - i)) ≤ W ^ 4 * (4 * 4 ^ (T' - i)) := cotaU_le hi' hT''
    have h2 : tV (2 * (enc a).length + 1 + 2 ^ (T' - i)) ≤ v :=
      htV (Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (by omega)) _)
    unfold costoIntento
    have : W ^ 4 * (4 * 4 ^ (T' - i)) = W ^ 4 * 4 * 4 ^ (T' - i) := by ring
    omega
  have hronda : ∀ T' ∈ Finset.range (T + 1),
      costoRondaMT enc tV a T' ≤ W ^ 4 * 4 * (2 * 4 ^ T') + (T + 1) * v := by
    intro T' hT'
    have hT'' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hT')
    unfold costoRondaMT
    calc ∑ i ∈ Finset.range (T' + 1), costoIntento enc tV a T' i
        ≤ ∑ i ∈ Finset.range (T' + 1), (W ^ 4 * 4 * 4 ^ (T' - i) + v) := Finset.sum_le_sum (hint T' hT')
      _ = W ^ 4 * 4 * ∑ i ∈ Finset.range (T' + 1), 4 ^ (T' - i) + (T' + 1) * v := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
      _ ≤ W ^ 4 * 4 * (2 * 4 ^ T') + (T + 1) * v := by
        have := suma_cuatro T'
        have h4 : 4 ^ (T' + 1) = 4 * 4 ^ T' := pow_succ' 4 T'
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ (by omega)
        · exact Nat.mul_le_mul_right _ (by omega)
  unfold costoHastaMT
  calc ∑ T' ∈ Finset.range (T + 1), costoRondaMT enc tV a T'
      ≤ ∑ T' ∈ Finset.range (T + 1), (W ^ 4 * 4 * (2 * 4 ^ T') + (T + 1) * v) := Finset.sum_le_sum hronda
    _ = W ^ 4 * 8 * ∑ T' ∈ Finset.range (T + 1), 4 ^ T' + (T + 1) * ((T + 1) * v) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
        smul_eq_mul]
      ring
    _ ≤ 16 * W ^ 4 * 4 ^ T + (T + 1) ^ 2 * v := by
      have := suma_geom_cuatro T
      have h4 : 4 ^ (T + 1) = 4 * 4 ^ T := pow_succ' 4 T
      have hs : ∑ T' ∈ Finset.range (T + 1), 4 ^ T' ≤ 2 * 4 ^ T := by omega
      have e1 : W ^ 4 * 8 * (2 * 4 ^ T) = 16 * W ^ 4 * 4 ^ T := by ring
      have e2 : (T + 1) * ((T + 1) * v) = (T + 1) ^ 2 * v := by ring
      rw [← e1, e2]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hs) _

/-- **Levin en tiempo de máquina (meta 2).** Si la máquina `i` resuelve `a` en `t` pasos, la búsqueda universal
halla una respuesta aceptada en una ronda `T ≤ i + ⌈log₂ t⌉`, y su costo total, con la cota de la universal de cslib
para cada intento y `tV` para cada verificación, es a lo sumo
`16 · ancho^4 · 4ⁱ · (2t)² + (T+1)² · tV (2n + 1 + 2ⁱ · 2t)`.
El factor de la máquina es `4ⁱ = (2ⁱ)²` y no `2ⁱ`: el sobrecosto de la universal es cuadrático en el reloj. -/
theorem levinMT {tV : ℕ → ℕ} (htV : Monotone tV) {a : α} {i t : ℕ} (h : ResuelveMT enc V a i t) :
    ∃ T y, buscarMT enc V a T = some y ∧ V (a, y) = true ∧ T ≤ i + Nat.clog 2 t ∧
      costoHastaMT enc tV a T ≤
        16 * anchoMT enc a T ^ 4 * (4 ^ i * (2 * t) ^ 2) +
          (T + 1) ^ 2 * tV (2 * (enc a).length + 1 + 2 ^ i * (2 * t)) := by
  have ht := h.uno_le
  obtain ⟨y, hy⟩ := buscarMT_halla h le_rfl
  refine ⟨i + Nat.clog 2 t, y, hy, buscarMT_acepta hy, le_rfl, ?_⟩
  refine le_trans (costoHastaMT_le htV a _) (Nat.add_le_add ?_ ?_)
  · apply Nat.mul_le_mul_left
    rw [pow_add, ← cuatro_pow (Nat.clog 2 t)]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Levin.pow_clog_lt ht).le 2)
  · apply Nat.mul_le_mul_left
    apply htV
    rw [pow_add]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Levin.pow_clog_lt ht).le) _

end Costo


/-! ## 5. La consecuencia para P -/

theorem pol_pow' {f : ℕ → ℕ} (hf : f ∈ Pol) (k : ℕ) : (fun n => f n ^ k) ∈ Pol := by
  induction k with
  | zero => simpa using pol_const 1
  | succ k ih => simpa [pow_succ] using pol_mul ih hf

theorem clog_le_dos (m : ℕ) : Nat.clog 2 m ≤ 2 * m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 := Levin.pow_clog_lt hm
    have h2 : Nat.clog 2 m < 2 ^ Nat.clog 2 m := Nat.lt_two_pow_self
    omega

/-- Lo que una máquina de cslib calcula en `t` pasos está parado, con esa salida, en todo reloj `t' ≥ t`. -/
theorem parado_de_computes {k : ℕ} {S : Type} {tm : MultiTapeTM k Bool S} {x y : List Bool} {t s t' : ℕ}
    (h : tm.ComputesInTimeAndSpace x y t s) (ht : t ≤ t') :
    (tm.runFrom (tm.initCfg x) t').Halted ∧ (tm.runFrom (tm.initCfg x) t').output = y := by
  obtain ⟨p, hhead, hhalt, hout, hlen, -⟩ := computesInTimeAndSpace_iff_exists_runPath.1 h
  have hr : tm.runFrom (tm.initCfg x) p.length = p.last := by rw [← hhead, runPath_last_eq_runFrom]
  have hh : (tm.runFrom (tm.initCfg x) p.length).Halted := hr ▸ hhalt
  rw [runFrom_eq_of_halt tm _ (hlen.trans ht) hh, hr]
  exact ⟨hhalt, hout⟩

section Consecuencia

variable {α : Type} (enc : α ↪ List Bool) (V : α × List Bool → Bool)

/-- **La búsqueda está en P (cslib)**: una función calculable en tiempo polinomial por una máquina de cslib da, para
toda instancia de `A`, una salida que el verificador acepta. -/
def BusquedaEnP (A : Set α) : Prop :=
  ∃ f : α → List Bool, ComputableInPolyTime f enc encBits ∧ ∀ a ∈ A, V (a, f a) = true

/-- **La búsqueda universal es polinomial**: hay un polinomio `p` tal que, para toda instancia de `A`, la búsqueda
fija `buscarMT` halla una salida aceptada con costo contable (`costoHastaMT`) a lo sumo `p n`. -/
def BusquedaUniversalPol (tV : ℕ → ℕ) (A : Set α) : Prop :=
  ∃ p ∈ Pol, ∀ a ∈ A, ∃ T y, buscarMT enc V a T = some y ∧ V (a, y) = true ∧
    costoHastaMT enc tV a T ≤ p (enc a).length

variable {enc V}

/-- **La máquina de P tiene número.** Si la búsqueda está en P, hay una máquina `i` y un reloj polinomial monótono
`tt` con los que `i` resuelve toda instancia de `A`. -/
theorem maquina_de_enP {A : Set α} (h : BusquedaEnP enc V A) :
    ∃ i, ∃ tt ∈ Pol, Monotone tt ∧ ∀ a ∈ A, ResuelveMT enc V a i (tt (enc a).length) := by
  obtain ⟨f, ⟨t, s, ht, -, k, S, hfin, tm, htm⟩, hA⟩ := h
  obtain ⟨c, d, hc⟩ := Cslib.polynomiallyBounded_iff_le.1 ht
  have := Fintype.ofFinite S
  let eS : S ↪ ℕ := (Fintype.equivFin S).toEmbedding.trans Fin.valEmbedding
  refine ⟨indiceDe (desc eS eBit tm), fun n => c * (n + 1) ^ d, ⟨c, d, fun _ => le_rfl⟩,
    fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _), fun a ha => ?_⟩
  obtain ⟨hh, ho⟩ := parado_de_computes (htm a) (hc _)
  exact ⟨f a, by rw [correrMT_de_maquina eS tm hh, ho]; rfl, hA a ha⟩

/-- **La consecuencia para P (meta 3).** Si la búsqueda está en P (cslib) y el verificador se cobra con un
`tV` polinomial, la búsqueda universal —fija, la misma para cualquier máquina que resuelva— es polinomial. La
máquina que resuelve solo aporta constantes: su número `i` (el factor `4ⁱ`) y el grado de su reloj. -/
theorem busqueda_universal_pol {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV) {A : Set α}
    (h : BusquedaEnP enc V A) : BusquedaUniversalPol enc V tV A := by
  obtain ⟨i, tt, htt, httm, hres⟩ := maquina_de_enP h
  have hR : (fun n => i + 2 * tt n) ∈ Pol := pol_add (pol_const i) (pol_mul (pol_const 2) htt)
  have hTam : (fun n => tamHasta (i + 2 * tt n)) ∈ Pol := pol_comp tamHasta_pol hR
  have hW : (fun n => 2 * tamHasta (i + 2 * tt n) + 6 * n + (i + 2 * tt n) + 5) ∈ Pol :=
    pol_add (pol_add (pol_add (pol_mul (pol_const 2) hTam) (pol_mul (pol_const 6) pol_id)) hR) (pol_const 5)
  have hX : (fun n => 4 ^ i * (2 * tt n) ^ 2) ∈ Pol :=
    pol_mul (pol_const _) (pol_pow' (pol_mul (pol_const 2) htt) 2)
  have hY : (fun n => 2 * n + 1 + 2 ^ i * (2 * tt n)) ∈ Pol :=
    pol_add (pol_add (pol_mul (pol_const 2) pol_id) (pol_const 1))
      (pol_mul (pol_const _) (pol_mul (pol_const 2) htt))
  refine ⟨fun n => 16 * (2 * tamHasta (i + 2 * tt n) + 6 * n + (i + 2 * tt n) + 5) ^ 4 *
      (4 ^ i * (2 * tt n) ^ 2) + (i + 2 * tt n + 1) ^ 2 * tV (2 * n + 1 + 2 ^ i * (2 * tt n)), ?_, ?_⟩
  · exact pol_add (pol_mul (pol_mul (pol_const 16) (pol_pow' hW 4)) hX)
      (pol_mul (pol_pow' (pol_add hR (pol_const 1)) 2) (pol_comp htV hY))
  · intro a ha
    obtain ⟨T, y, hy, hV, hT, hc⟩ := levinMT htVm (hres a ha)
    refine ⟨T, y, hy, hV, hc.trans ?_⟩
    have hT' : T ≤ i + 2 * tt (enc a).length := hT.trans (by have := clog_le_dos (tt (enc a).length); omega)
    have hA : anchoMT enc a T ≤ 2 * tamHasta (i + 2 * tt (enc a).length) + 6 * (enc a).length +
        (i + 2 * tt (enc a).length) + 5 := by
      have := tamHasta_mono hT'
      unfold anchoMT; omega
    exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 4)) le_rfl)
      (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) le_rfl)

/-! ## 6. La `kt` de máquinas -/

variable (enc V) in
/-- Alguna máquina resuelve `a` con algún reloj. -/
def ResolubleMT (a : α) : Prop := ∃ i t, ResuelveMT enc V a i t

variable (enc V) in
/-- **La `kt` de máquinas**: el menor `i + ⌈log₂ t⌉` sobre las máquinas `i` de cslib que resuelven `a` en `t`
pasos (`0` si ninguna). -/
noncomputable def ktMT (a : α) : ℕ := sInf {k | ∃ i t, ResuelveMT enc V a i t ∧ k = i + Nat.clog 2 t}

/-- **(a)** Toda máquina que resuelve acota la `kt`. -/
theorem ktMT_le {a : α} {i t : ℕ} (h : ResuelveMT enc V a i t) : ktMT enc V a ≤ i + Nat.clog 2 t :=
  Nat.sInf_le ⟨i, t, h, rfl⟩

theorem ktMT_alcanzado {a : α} (h : ResolubleMT enc V a) :
    ∃ i t, ResuelveMT enc V a i t ∧ ktMT enc V a = i + Nat.clog 2 t := by
  obtain ⟨i, t, hit⟩ := h
  obtain ⟨j, u, hju, he⟩ := Nat.sInf_mem (s := {k | ∃ i t, ResuelveMT enc V a i t ∧ k = i + Nat.clog 2 t})
    ⟨_, i, t, hit, rfl⟩
  exact ⟨j, u, hju, he⟩

/-- **(b)** La búsqueda halla en la ronda `ktMT` y cuesta a lo sumo `16 · ancho^4 · 4^{ktMT}` en la universal más
`(ktMT+1)²` verificaciones de largo `≤ 2n + 1 + 2^{ktMT}`. -/
theorem costo_le_ktMT {tV : ℕ → ℕ} (htV : Monotone tV) {a : α} (h : ResolubleMT enc V a) :
    ∃ y, buscarMT enc V a (ktMT enc V a) = some y ∧ V (a, y) = true ∧
      costoHastaMT enc tV a (ktMT enc V a) ≤ 16 * anchoMT enc a (ktMT enc V a) ^ 4 * 4 ^ ktMT enc V a +
        (ktMT enc V a + 1) ^ 2 * tV (2 * (enc a).length + 1 + 2 ^ ktMT enc V a) := by
  obtain ⟨i, t, hit, he⟩ := ktMT_alcanzado h
  obtain ⟨y, hy⟩ := buscarMT_halla hit he.ge
  exact ⟨y, hy, buscarMT_acepta hy, costoHastaMT_le htV a _⟩

/-- La búsqueda hasta la ronda `T` cuesta al menos `2^T`: la máquina `0` corre `2^T` pasos en la última ronda. -/
theorem pow_le_costoHastaMT (tV : ℕ → ℕ) (a : α) (T : ℕ) : 2 ^ T ≤ costoHastaMT enc tV a T := by
  have h1 : costoIntento enc tV a T 0 ≤ costoRondaMT enc tV a T :=
    Finset.single_le_sum (f := fun i => costoIntento enc tV a T i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.succ_pos T))
  have h2 : costoRondaMT enc tV a T ≤ costoHastaMT enc tV a T :=
    Finset.single_le_sum (f := fun T' => costoRondaMT enc tV a T') (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_self T))
  have h3 : 2 ^ T ≤ costoIntento enc tV a T 0 := by
    unfold costoIntento cotaU
    rw [Nat.sub_zero]
    set X := (eIn (maquina 0, (enc a).map eBit, 2 ^ T)).length + 1
    have hX : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hs : 2 ^ T ≤ (2 ^ T + 1) ^ 2 := by nlinarith
    calc 2 ^ T ≤ (2 ^ T + 1) ^ 2 := hs
      _ ≤ X ^ 4 * (2 ^ T + 1) ^ 2 := Nat.le_mul_of_pos_left _ hX
      _ ≤ _ := Nat.le_add_right _ _
  omega

variable (enc V) in
/-- **`ktMT` logarítmica en `A`**: toda instancia es resoluble y su `ktMT` es `O(log n)`. -/
def KtMTLog (A : Set α) : Prop :=
  ∃ c, ∀ a ∈ A, ResolubleMT enc V a ∧ ktMT enc V a ≤ c * Nat.log 2 ((enc a).length + 2)

/-- **La equivalencia (meta 4).** Con un verificador cobrado polinomialmente, la búsqueda universal es polinomial
en `A` si y solo si la `ktMT` es logarítmica en `A`. Las dos direcciones son incondicionales: la de ida porque la
respuesta de la búsqueda la produjo una máquina con reloj `2^(T'-i)` y el costo ya pagó `2^T`; la de vuelta por
`costo_le_ktMT` y `tamHasta_pol`. -/
theorem busqueda_iff_kt {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV) {A : Set α} :
    BusquedaUniversalPol enc V tV A ↔ KtMTLog enc V A := by
  constructor
  · rintro ⟨p, ⟨C, d, hCd⟩, hp⟩
    refine ⟨Nat.log 2 C + 2 * d + 3, fun a ha => ?_⟩
    obtain ⟨T, y, hy, -, hc⟩ := hp a ha
    obtain ⟨T', i, hT', hi, hcorr, hv⟩ := buscarMT_origen hy
    have hres : ResuelveMT enc V a i (2 ^ (T' - i)) := ⟨y, hcorr, hv⟩
    refine ⟨⟨i, _, hres⟩, KtSAT.kt_le_de_costo (m := costoHastaMT enc tV a T) ?_ ?_⟩
    · have hk := ktMT_le hres
      rw [Nat.clog_pow 2 _ one_lt_two] at hk
      have hl : T ≤ Nat.log 2 (costoHastaMT enc tV a T) := by
        calc T = Nat.log 2 (2 ^ T) := (Nat.log_pow one_lt_two T).symm
          _ ≤ _ := Nat.log_mono_right (pow_le_costoHastaMT tV a T)
      omega
    · exact hc.trans ((hCd _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)))
  · rintro ⟨c, hc⟩
    have hM : (fun n => (n + 2) ^ c) ∈ Pol := ⟨2 ^ c, c, fun n => by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) c⟩
    have hTam : (fun n => tamHasta ((n + 2) ^ c)) ∈ Pol := pol_comp tamHasta_pol hM
    have hW : (fun n => 2 * tamHasta ((n + 2) ^ c) + 6 * n + (n + 2) ^ c + 5) ∈ Pol :=
      pol_add (pol_add (pol_add (pol_mul (pol_const 2) hTam) (pol_mul (pol_const 6) pol_id)) hM) (pol_const 5)
    have hY : (fun n => 2 * n + 1 + (n + 2) ^ c) ∈ Pol :=
      pol_add (pol_add (pol_mul (pol_const 2) pol_id) (pol_const 1)) hM
    refine ⟨fun n => 16 * (2 * tamHasta ((n + 2) ^ c) + 6 * n + (n + 2) ^ c + 5) ^ 4 * ((n + 2) ^ c) ^ 2 +
        ((n + 2) ^ c + 1) ^ 2 * tV (2 * n + 1 + (n + 2) ^ c), ?_, fun a ha => ?_⟩
    · exact pol_add (pol_mul (pol_mul (pol_const 16) (pol_pow' hW 4)) (pol_pow' hM 2))
        (pol_mul (pol_pow' (pol_add hM (pol_const 1)) 2) (pol_comp htV hY))
    · obtain ⟨hres, hk⟩ := hc a ha
      obtain ⟨y, hy, hV, hcost⟩ := costo_le_ktMT htVm (tV := tV) hres
      refine ⟨_, y, hy, hV, hcost.trans ?_⟩
      set k := ktMT enc V a
      set n := (enc a).length
      have h2k : 2 ^ k ≤ (n + 2) ^ c := KtSAT.pow_le_de_kt hk
      have hk2 : k ≤ (n + 2) ^ c := (Nat.lt_two_pow_self).le.trans h2k
      have h4k : 4 ^ k ≤ ((n + 2) ^ c) ^ 2 := by rw [← cuatro_pow]; exact Nat.pow_le_pow_left h2k 2
      have hA : anchoMT enc a k ≤ 2 * tamHasta ((n + 2) ^ c) + 6 * n + (n + 2) ^ c + 5 := by
        have := tamHasta_mono hk2
        unfold anchoMT; omega
      exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 4)) h4k)
        (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (htVm (by omega)))

/-- **Si la búsqueda está en P, la `ktMT` es logarítmica.** Incondicional (con `tV = 0`: esta dirección no usa el
costo del verificador). -/
theorem enP_implica_kt {A : Set α} (h : BusquedaEnP enc V A) : KtMTLog enc V A :=
  (busqueda_iff_kt (tV := fun _ => 0) (pol_const 0) (fun _ _ _ => le_rfl)).1
    (busqueda_universal_pol (pol_const 0) (fun _ _ _ => le_rfl) h)

/-- **La vuelta a P, condicional.** Si la búsqueda universal polinomial (contable) se implementa como una máquina
de cslib polinomial (`hImpl`, que aquí NO se prueba), `ktMT` logarítmica da la búsqueda en P. -/
theorem kt_implica_enP_condicional {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV) {A : Set α}
    (hImpl : BusquedaUniversalPol enc V tV A → BusquedaEnP enc V A) (h : KtMTLog enc V A) :
    BusquedaEnP enc V A :=
  hImpl ((busqueda_iff_kt htV htVm).2 h)

end Consecuencia

/-! ## 7. SAT -/

/-- **El verificador de SAT de cslib tiene un reloj polinomial monótono**: es el `tV` que se cobra. -/
theorem verificador_sat : ∃ tV ∈ Pol, Monotone tV ∧ ∃ s : ℕ → ℕ,
    ComputableInTimeAndSpaceOfLength SAT.verifier (encPair encCNF encBits) encBool tV s := by
  obtain ⟨t, s, ht, -, h⟩ := SAT.computableInPolyTime_verifier
  obtain ⟨c, d, hc⟩ := Cslib.polynomiallyBounded_iff_le.1 ht
  exact ⟨fun n => c * (n + 1) ^ d, ⟨c, d, fun _ => le_rfl⟩,
    fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _), s,
    h.mono (fun _ => hc _) (fun _ => le_rfl)⟩

/-- **SAT: si la búsqueda está en P, la búsqueda universal es polinomial.** -/
theorem sat_busqueda_universal_pol {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV)
    (h : BusquedaEnP encCNF SAT.verifier SAT) : BusquedaUniversalPol encCNF SAT.verifier tV SAT :=
  busqueda_universal_pol htV htVm h

/-- **SAT: la búsqueda universal es polinomial si y solo si la `ktMT` de las fórmulas satisfacibles es
`O(log n)`.** -/
theorem sat_busqueda_iff_kt {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV) :
    BusquedaUniversalPol encCNF SAT.verifier tV SAT ↔ KtMTLog encCNF SAT.verifier SAT :=
  busqueda_iff_kt htV htVm

/-- **SAT: si la búsqueda está en P, la `ktMT` de las satisfacibles es logarítmica.** -/
theorem sat_enP_implica_kt (h : BusquedaEnP encCNF SAT.verifier SAT) : KtMTLog encCNF SAT.verifier SAT :=
  enP_implica_kt h


/-! ## 8. Controles -/

/-- **Control: polinomio de polinomio.** Si el largo de la entrada de la universal es `q n` y el reloj `p n`, ambos
polinomiales, la cota de cslib `(q n + 1)^4 · (p n + 1)^2` sigue siendo polinomial (por `pol_comp`). -/
theorem control_pol_comp {p q : ℕ → ℕ} (hp : p ∈ Pol) (hq : q ∈ Pol) :
    (fun n => (q n + 1) ^ 4 * (p n + 1) ^ 2) ∈ Pol := by
  have h4 : (fun m => (m + 1) ^ 4) ∈ Pol := pol_pow' (pol_add pol_id (pol_const 1)) 4
  have h2 : (fun m => (m + 1) ^ 2) ∈ Pol := pol_pow' (pol_add pol_id (pol_const 1)) 2
  exact pol_mul (pol_comp (f := fun m => (m + 1) ^ 4) h4 hq) (pol_comp (f := fun m => (m + 1) ^ 2) h2 hp)

/-- La descripción vacía de cslib: sin cintas de trabajo y sin transiciones; para en el primer paso, sin salida. -/
def vacia : Desc := ⟨0, 0, []⟩

/-- **Control: una máquina concreta corre.** La descripción vacía, por su número, para en un paso con salida vacía. -/
theorem correrMT_vacia (x : List Bool) : correrMT (indiceDe vacia) x 1 = some [] := by
  unfold correrMT
  rw [maquina_indiceDe]
  rfl

/-- **Control: un caso fácil.** Con el verificador «la salida es vacía», la búsqueda halla en la ronda
`indiceDe vacia`, y la `ktMT` de toda instancia es a lo sumo ese número. -/
theorem control_trivial {α : Type} (enc : α ↪ List Bool) (a : α) :
    (∃ y, buscarMT enc (fun p => p.2.isEmpty) a (indiceDe vacia) = some y) ∧
      ktMT enc (fun p => p.2.isEmpty) a ≤ indiceDe vacia := by
  have h : ResuelveMT enc (fun p => p.2.isEmpty) a (indiceDe vacia) 1 := ⟨[], correrMT_vacia _, rfl⟩
  exact ⟨buscarMT_halla h (by simp), by simpa using ktMT_le h⟩

end Sagitta.Map.Tiempo.LevinMaquinas
