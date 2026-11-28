import Sagitta.Map.LevinMaquinas
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Unpair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.CourseOfValues
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# `buscarMT` en tiempo polinomial: la vuelta cerrada

`LevinMaquinas` probó que la búsqueda de Levin `buscarMT` es polinomial con un **costo contable** (la suma de las cotas
de la universal de cslib y del verificador) y dejó la vuelta «`ktMT` logarítmica ⇒ búsqueda en P» condicional a una
hipótesis `hImpl`: que `buscarMT` se implemente como una máquina de cslib polinomial. Este archivo la descarga. No
construye ninguna máquina a mano: escribe `buscarMT` como una función de listas y saca su polinomialidad de
`ComputableInPolyTime` por composición, con las herramientas de cslib-frontier.

## Las piezas

* **La palabra número `i`** (§ 2). La máquina `i` es `decodeDesc (palabra i)` y `palabra i` es el decodificador de
  Mathlib (`Encodable.decode₂`), que es una recursión por valores anteriores sobre `Nat.unpair`. `pasoDec` es un paso
  de esa recursión sobre la tabla de los valores previos; `pasoDec_val`: la tabla da exactamente `decode`;
  `encode_de_decode`: lo decodificado se vuelve a codificar en el mismo número, así que `decode₂ = decode`
  (`palabra_eq`). **`palabra_poly`**: `palabra` es polinomial en `i` escrito en unario
  (`ComputableInPolyTime.courseOfValuesVal`, con la cota `|palabra i| ≤ i`).
* **La simulación universal con reloj** ya la da cslib: `computableInPolyTime_universal`, con el número de pasos en
  unario. Polinomial en el reloj, no en su logaritmo: por eso importa que el reloj sea polinomial.
* **El tope del reloj** (§ 3). En la ronda `T'` la máquina `i` corre `2^(T'-i)` pasos; como función de `(a, T', i)`
  arbitrarios eso es exponencial, así que `intentoCap` topa el reloj en `reloj c a = (n+2)^c`
  (`binary_min_unary`: `2^k` en binario, el mínimo en unario). Hasta la ronda `largo c a = c · log₂ (n+2)` el tope no
  muerde (`2^largo ≤ (n+2)^c`), y **`buscarCap_eq`**: la búsqueda topada *es* `buscarMT a (largo c a)`.
* **Los bucles** son `findSome?` sobre `List.range`, reescritos como `map` + `find?` (`findSome?_eq_find?`), que cslib
  sabe componer (`mapWithInput`, `findWithInput`, `optionGetDWithInput`).
* **`buscarMT_poly`**: con el verificador en P, `a ↦ (buscarMT a (c · log₂ (n+2))).getD []` es una función de cslib en
  tiempo polinomial, para cada `c`.

## La vuelta (§ 4)

* **`kt_implica_enP`**: `ktMT` logarítmica ⇒ búsqueda en P. La única hipótesis es que el verificador esté en P
  (`ComputableInPolyTime V (encPair enc encBits) encBool`), que es lo que hace de `A` un problema de búsqueda de NP;
  ya no hay hipótesis de implementación.
* **`enP_iff_kt`**: búsqueda en P ⇔ `ktMT` logarítmica, y **`enP_iff_levin`**: ⇔ búsqueda de Levin polinomial (costo
  contable). **`levin_pol_implica_enP`** es exactamente la `hImpl` de `kt_implica_enP_condicional`, probada.
* **`sat_enP_iff_kt`**, sin hipótesis: la búsqueda de SAT está en P si y solo si la `ktMT` de las fórmulas
  satisfacibles es `O(log n)` (el verificador de cslib ya es polinomial).

## Lo que NO se prueba

* **El verificador en P no se puede quitar.** Sin él, `ktMT` logarítmica no da búsqueda en P: con `V (a, y)` «`y` es
  el bit `g a`» y `g` no computable, dos máquinas constantes resuelven todo con `ktMT` acotada y ninguna función
  computable acierta siempre. Ese contraejemplo no está formalizado aquí; se dice para que la hipótesis `hV` no se lea
  como una hipótesis de implementación.
* **Nada sobre P contra NP.** Se cierra una equivalencia entre dos formulaciones; no se decide cuál vale.
* Los polinomios no se calculan: salen de la composición de certificados de cslib y su grado depende de `c` y de la
  universal (que es `O(I^4 · s^2)` en el largo de la entrada y el reloj).
-/

namespace Sagitta.Map.Informacion.BuscarPolinomial

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.Complexity
open Sagitta.Map.Tiempo Sagitta.Map.Tiempo.LevinMaquinas

/-! ## 1. El tope: rondas y reloj -/

section Tope

variable {α : Type} (enc : α ↪ List Bool)

/-- La última ronda: `c · log₂ (n+2)`, con `n` el largo de la instancia. -/
def largo (c : ℕ) (a : α) : ℕ := c * Nat.log 2 ((enc a).length + 2)

/-- El tope del reloj: `(n+2)^c ≥ 2^largo`. -/
def reloj (c : ℕ) (a : α) : ℕ := ((enc a).length + 2) ^ c

variable {enc}

theorem largo_poly (c : ℕ) : ComputableInPolyTime (largo enc c) enc encUnary := by
  unfold largo
  have h := ComputableInPolyTime.encoding_length enc
  fun_prop

theorem reloj_poly (c : ℕ) : ComputableInPolyTime (reloj enc c) enc encUnary := by
  unfold reloj
  have h := ComputableInPolyTime.encoding_length enc
  fun_prop

end Tope

/-! ## 2. La palabra número `i`, en tiempo polinomial en `i` -/

section Palabra

open Encodable

/-- Un paso del decodificador de Mathlib para `List Bool`, sobre la tabla de los valores anteriores: el valor `v+1`
es `b :: l` con `b` el bit `(unpair v).1` y `l` el valor `(unpair v).2`, que ya está en la tabla. -/
def pasoDec (tbl : List (Option (List Bool))) : Option (List Bool) :=
  if tbl.length = 0 then some [] else
    if (tbl.length - 1).unpair.1 ≤ 1 then
      (tbl.getD (tbl.length - 1).unpair.2 none).elim none
        (fun l => some (decide ((tbl.length - 1).unpair.1 = 1) :: l))
    else none

theorem decode_bool_cases (m : ℕ) :
    (decode m : Option Bool) = if m ≤ 1 then some (decide (m = 1)) else none := by
  rcases m with _ | _ | m
  · simp [Encodable.decode_zero]
  · simp [Encodable.decode_one]
  · rw [Encodable.decode_ge_two _ (by omega)]; simp

/-- **El decodificador por tabla es el de Mathlib.** -/
theorem pasoDec_val (n : ℕ) : List.courseOfValuesVal pasoDec n = decode (α := List Bool) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have e : List.courseOfValuesVal pasoDec n = pasoDec (List.courseOfValues pasoDec n) := rfl
    rw [e, pasoDec, List.length_courseOfValues]
    rcases n with _ | v
    · simp
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Encodable.decode_list_succ]
      have hlt : v.unpair.2 < v + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le v)
      rw [List.getD_courseOfValues _ _ hlt, ih _ hlt, decode_bool_cases]
      split_ifs <;> cases decode (α := List Bool) v.unpair.2 <;> rfl

/-- Lo que el decodificador de Mathlib entrega para `List Bool` se vuelve a codificar en el mismo número. -/
theorem encode_de_decode : ∀ (n : ℕ) (l : List Bool), decode (α := List Bool) n = some l → encode l = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l h
    rcases n with _ | v
    · rw [Encodable.decode_list_zero, Option.some.injEq] at h; subst h; rfl
    · rw [Encodable.decode_list_succ] at h
      have hlt : v.unpair.2 < v + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le v)
      cases h1 : (decode v.unpair.1 : Option Bool) with
      | none => rw [h1] at h; cases h
      | some b =>
        cases h2 : decode (α := List Bool) v.unpair.2 with
        | none => rw [h1, h2] at h; cases h
        | some l' =>
          simp only [h1, h2, Option.map_eq_map, Option.map_some, Option.seq_some, Option.some.injEq] at h
          subst h
          have hb : encode b = v.unpair.1 := by
            rw [decode_bool_cases] at h1
            split_ifs at h1 with hle
            · simp only [Option.some.injEq] at h1; subst h1
              rcases Nat.lt_or_ge v.unpair.1 1 with h0 | h0
              · have : v.unpair.1 = 0 := by omega
                rw [this]; rfl
              · have : v.unpair.1 = 1 := by omega
                rw [this]; rfl
          change Nat.succ (Nat.pair (encode b) (encode l')) = v + 1
          rw [hb, ih _ hlt l' h2, Nat.pair_unpair]

theorem palabra_eq (i : ℕ) : palabra i = (List.courseOfValuesVal pasoDec i).getD [] := by
  rw [pasoDec_val, palabra]
  congr 1
  cases h : decode (α := List Bool) i with
  | none => simp [Encodable.decode₂, h]
  | some l => exact Encodable.decode₂_eq_some.2 (encode_de_decode i l h)

theorem pasoDec_poly :
    ComputableInPolyTime pasoDec (encList (encOption encBits)) (encOption encBits) := by
  unfold pasoDec
  have hu := ComputableInPolyTime.unary_unpair
  fun_prop

theorem palabra_poly : ComputableInPolyTime palabra encUnary encBits := by
  have hV : ComputableInPolyTime (List.courseOfValuesVal pasoDec) encUnary (encOption encBits) := by
    refine ComputableInPolyTime.courseOfValuesVal pasoDec_poly (elemBound := fun n => n + 1)
      (Cslib.PolynomiallyBounded.of_forall_le 1 1 fun n => by simp) fun n i hi => ?_
    rw [pasoDec_val]
    cases h : decode (α := List Bool) i with
    | none => simp
    | some l =>
      have := encode_de_decode i l h
      have hl := Encodable.length_le_encode l
      simp only [encOption_some, encBits_apply, List.length_cons]
      omega
  have hG := ComputableInPolyTime.optionGetDWithInput hV
    (ComputableInPolyTime.const (encIn := encUnary) (encOut := encBits) [])
  have e : palabra = fun i => (List.courseOfValuesVal pasoDec i).getD [] := funext palabra_eq
  rw [e]
  exact hG

end Palabra

/-! ## 3. `buscarMT` misma, en tiempo polinomial -/

section BuscarMT

/-- `findSome?` como `map` + `find?`: la forma que cslib sabe calcular. -/
theorem findSome?_eq_find? {β γ : Type} (f : β → Option γ) (l : List β) :
    l.findSome? f = ((l.map f).find? (·.isSome)).getD none := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.findSome?_cons, List.map_cons, List.find?_cons]
    cases h : f b with
    | none => simpa using ih
    | some y => rfl

theorem findSome?_congr {β γ : Type} {f g : β → Option γ} {l : List β} (h : ∀ b ∈ l, f b = g b) :
    l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h b List.mem_cons_self,
      ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')]

variable {α : Type} (enc : α ↪ List Bool) (V : α × List Bool → Bool)

/-- El intento de la máquina `i` en la ronda `T'`, con el reloj topado en `reloj c a` (el tope no muerde mientras
`T' ≤ largo c a`, que es donde se usa). -/
def intentoCap (c : ℕ) (a : α) (T' i : ℕ) : Option (List Bool) :=
  if (universal (decodeDesc (palabra i), (enc a).map eBit, min (reloj enc c a) (2 ^ (T' - i)))).2 &&
      V (a, (universal (decodeDesc (palabra i), (enc a).map eBit,
        min (reloj enc c a) (2 ^ (T' - i)))).1.map (· != 0)) then
    some ((universal (decodeDesc (palabra i), (enc a).map eBit,
      min (reloj enc c a) (2 ^ (T' - i)))).1.map (· != 0))
  else none

/-- La ronda `T'` con el reloj topado. -/
def rondaCap (c : ℕ) (a : α) (T' : ℕ) : Option (List Bool) :=
  (List.range (T' + 1)).findSome? (intentoCap enc V c a T')

/-- La búsqueda con el reloj topado, hasta la ronda `largo c a`. -/
def buscarCap (c : ℕ) (a : α) : Option (List Bool) :=
  (List.range (largo enc c a + 1)).findSome? (rondaCap enc V c a)

variable {enc V}

theorem intentoCap_eq {c : ℕ} {a : α} {T' i : ℕ} (hT : T' ≤ largo enc c a) :
    intentoCap enc V c a T' i = intentoMT enc V a T' i := by
  have hmin : min (reloj enc c a) (2 ^ (T' - i)) = 2 ^ (T' - i) := by
    refine min_eq_right ?_
    calc 2 ^ (T' - i) ≤ 2 ^ largo enc c a := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ reloj enc c a := KtSAT.pow_le_de_kt le_rfl
  unfold intentoCap intentoMT correrMT maquina
  rw [hmin]
  by_cases hs : (universal (decodeDesc (palabra i), (enc a).map eBit, 2 ^ (T' - i))).2 = true
  · simp only [hs, Bool.true_and, ↓reduceIte]
    cases hv : V (a, (universal (decodeDesc (palabra i), (enc a).map eBit, 2 ^ (T' - i))).1.map (· != 0)) <;>
      simp [Option.filter, hv]
  · simp [hs]

/-- **Con el reloj topado es la misma búsqueda**: `buscarCap c a = buscarMT a (largo c a)`. -/
theorem buscarCap_eq (c : ℕ) (a : α) : buscarCap enc V c a = buscarMT enc V a (largo enc c a) := by
  unfold buscarCap buscarMT
  refine findSome?_congr fun T' hT' => ?_
  unfold rondaCap rondaMT
  refine findSome?_congr fun i _ => intentoCap_eq ?_
  exact Nat.lt_succ_iff.1 (List.mem_range.1 hT')

theorem intentoCap_poly (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (c : ℕ) :
    ComputableInPolyTime (fun p : (α × ℕ) × ℕ => intentoCap enc V c p.1.1 p.1.2 p.2)
      (encPair (encPair enc encUnary) encUnary) (encOption encBits) := by
  unfold intentoCap
  have hK := reloj_poly (enc := enc) c
  have hP := palabra_poly
  have h2 := ComputableInPolyTime.binary_two_pow
  have hm := ComputableInPolyTime.binary_min_unary
  have hx : ComputableInPolyTime (fun a : α => enc a) enc encBits := ComputableInPolyTime.of_eq fun _ => rfl
  fun_prop

theorem rondaCap_poly (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (c : ℕ) :
    ComputableInPolyTime (fun p : α × ℕ => rondaCap enc V c p.1 p.2) (encPair enc encUnary)
      (encOption encBits) := by
  have e : (fun p : α × ℕ => rondaCap enc V c p.1 p.2) = fun p =>
      (((List.range (p.2 + 1)).map (fun i => intentoCap enc V c p.1 p.2 i)).find? (·.isSome)).getD none := by
    funext p; exact findSome?_eq_find? _ _
  rw [e]
  have hR : ComputableInPolyTime (fun p : α × ℕ => List.range (p.2 + 1)) (encPair enc encUnary)
      (encList encUnary) := by
    have := ComputableInPolyTime.range
    fun_prop
  have hM := ComputableInPolyTime.mapWithInput (f := fun (p : α × ℕ) i => intentoCap enc V c p.1 p.2 i) hR
    (intentoCap_poly hV c)
  have hT : ComputableInPolyTime (fun q : (α × ℕ) × Option (List Bool) => q.2.isSome)
      (encPair (encPair enc encUnary) (encOption encBits)) encBool :=
    ComputableInPolyTime.optionIsSome (ComputableInPolyTime.snd _ _)
  have hF := ComputableInPolyTime.findWithInput
    (list := fun p : α × ℕ => (List.range (p.2 + 1)).map (fun i => intentoCap enc V c p.1 p.2 i))
    (test := fun (_ : α × ℕ) (o : Option (List Bool)) => o.isSome) hM hT
  exact ComputableInPolyTime.optionGetDWithInput hF
    (ComputableInPolyTime.const (encIn := encPair enc encUnary) (encOut := encOption encBits) none)

theorem buscarCap_poly (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (c : ℕ) :
    ComputableInPolyTime (buscarCap enc V c) enc (encOption encBits) := by
  have e : buscarCap enc V c = fun a =>
      (((List.range (largo enc c a + 1)).map (rondaCap enc V c a)).find? (·.isSome)).getD none := by
    funext a; exact findSome?_eq_find? _ _
  rw [e]
  have hL := largo_poly (enc := enc) c
  have hR : ComputableInPolyTime (fun a => List.range (largo enc c a + 1)) enc (encList encUnary) := by
    have := ComputableInPolyTime.range
    fun_prop
  have hM := ComputableInPolyTime.mapWithInput (f := fun a T' => rondaCap enc V c a T') hR (rondaCap_poly hV c)
  have hT : ComputableInPolyTime (fun q : α × Option (List Bool) => q.2.isSome)
      (encPair enc (encOption encBits)) encBool :=
    ComputableInPolyTime.optionIsSome (ComputableInPolyTime.snd _ _)
  have hF := ComputableInPolyTime.findWithInput
    (list := fun a => (List.range (largo enc c a + 1)).map (rondaCap enc V c a))
    (test := fun (_ : α) (o : Option (List Bool)) => o.isSome) hM hT
  exact ComputableInPolyTime.optionGetDWithInput hF
    (ComputableInPolyTime.const (encIn := enc) (encOut := encOption encBits) none)

/-- **`buscarMT` es polinomial.** Con el verificador en P, la búsqueda de Levin de `LevinMaquinas` hasta la ronda
`c · log₂ (n+2)` es una función de cslib en tiempo polinomial (la respuesta, o `[]` si no halló). -/
theorem buscarMT_poly (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (c : ℕ) :
    ComputableInPolyTime (fun a => (buscarMT enc V a (largo enc c a)).getD []) enc encBits := by
  have e : (fun a => (buscarMT enc V a (largo enc c a)).getD []) = fun a => (buscarCap enc V c a).getD [] := by
    funext a; rw [buscarCap_eq]
  rw [e]
  exact ComputableInPolyTime.optionGetDWithInput (buscarCap_poly hV c)
    (ComputableInPolyTime.const (encIn := enc) (encOut := encBits) [])

/-- Con `ktMT a ≤ c · log₂ (n+2)`, `buscarMT` halla en la ronda `largo c a`. -/
theorem buscarMT_largo {c : ℕ} {a : α} (hres : ResolubleMT enc V a)
    (hk : ktMT enc V a ≤ c * Nat.log 2 ((enc a).length + 2)) :
    V (a, (buscarMT enc V a (largo enc c a)).getD []) = true := by
  obtain ⟨i, t, hit, he⟩ := ktMT_alcanzado hres
  obtain ⟨y, hy⟩ := buscarMT_halla hit (show i + Nat.clog 2 t ≤ largo enc c a by unfold largo; omega)
  rw [hy, Option.getD_some]
  exact buscarMT_acepta hy

end BuscarMT

/-! ## 4. La vuelta -/

section Vuelta

variable {α : Type} {enc : α ↪ List Bool} {V : α × List Bool → Bool}

/-- **`ktMT` logarítmica ⇒ búsqueda en P**, sin hipótesis de implementación. Con el verificador en P, la función
`a ↦ (buscarMT a (c · log₂ (n+2))).getD []` —la búsqueda de Levin de `LevinMaquinas`, fija— es de cslib en tiempo
polinomial (`buscarMT_poly`) y, si `ktMT a ≤ c · log₂ (n+2)`, su respuesta la acepta el verificador
(`buscarMT_largo`). -/
theorem kt_implica_enP (hV : ComputableInPolyTime V (encPair enc encBits) encBool) {A : Set α}
    (h : KtMTLog enc V A) : BusquedaEnP enc V A := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun a => (buscarMT enc V a (largo enc c a)).getD [], buscarMT_poly hV c,
    fun a ha => buscarMT_largo (hc a ha).1 (hc a ha).2⟩

/-- **Búsqueda en P ⇔ `ktMT` logarítmica**, con el verificador en P. -/
theorem enP_iff_kt (hV : ComputableInPolyTime V (encPair enc encBits) encBool) {A : Set α} :
    BusquedaEnP enc V A ↔ KtMTLog enc V A :=
  ⟨enP_implica_kt, kt_implica_enP hV⟩

/-- **La `hImpl` de `kt_implica_enP_condicional`, probada**: con el verificador en P, la búsqueda de Levin
polinomial (costo contable) da la búsqueda en P. -/
theorem levin_pol_implica_enP {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) {A : Set α} :
    BusquedaUniversalPol enc V tV A → BusquedaEnP enc V A :=
  fun h => kt_implica_enP hV ((busqueda_iff_kt htV htVm).1 h)

/-- **Búsqueda en P ⇔ búsqueda de Levin polinomial** (costo contable), con el verificador en P. -/
theorem enP_iff_levin {tV : ℕ → ℕ} (htV : tV ∈ Pol) (htVm : Monotone tV)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) {A : Set α} :
    BusquedaEnP enc V A ↔ BusquedaUniversalPol enc V tV A :=
  (enP_iff_kt hV).trans (busqueda_iff_kt htV htVm).symm

/-- **SAT, sin hipótesis**: la búsqueda de SAT está en P si y solo si la `ktMT` de las fórmulas satisfacibles es
`O(log n)`. El verificador de cslib ya es polinomial (`SAT.computableInPolyTime_verifier`). -/
theorem sat_enP_iff_kt :
    BusquedaEnP encCNF SAT.verifier SAT ↔ KtMTLog encCNF SAT.verifier SAT :=
  enP_iff_kt SAT.computableInPolyTime_verifier

end Vuelta

end Sagitta.Map.Informacion.BuscarPolinomial
