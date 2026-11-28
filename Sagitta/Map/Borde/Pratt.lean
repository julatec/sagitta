import Sagitta.Map.Borde.FactorizacionS12
import Sagitta.Map.IndiceRapido
import Sagitta.Map.SigmaFagin.Palabras
import Mathlib.NumberTheory.LucasPrimality
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# Los certificados de Pratt, y la primera hipótesis de `FactorizacionS12` demostrada

`Sagitta/Map/Borde/FactorizacionS12.lean` (24 nov 2026) prueba `s12_no_demuestra_factor` con dos hipótesis: (1) hay una
`φ ∈ Σᵇ₁` cuyo gráfico en ℕ es `Nat.minFac`; (2) `Nat.minFac` no es polinomial. Desde el 25 nov `Σᵇ₁ = NP` está
demostrado (`SigmaFagin.sigmaIgualNP`, `Sagitta/Map/SigmaFagin/Palabras.lean`), así que (1) sale de poner el gráfico de
`minFac` en la NP de `Clases.lean` (máquinas de Turing de Mathlib, verificador polinomial y certificados de largo
polinomial). El certificado es la factorización con certificados de primalidad de Pratt (1975). Aquí se hace eso, y
queda solo la hipótesis (2), que es una conjetura.

## Lo que se prueba

**Los certificados de Pratt.** Un certificado aplanado es una lista de entradas `(p, a, [q₁, …, q_k])`; la entrada
está bien (`entradaOK`) si `p ≥ 2`, `∏ qᵢ = p − 1`, `a^(p−1) ≡ 1`, y cada `qᵢ` tiene su propia entrada y cumple
`a^((p−1)/qᵢ) ≢ 1 (mod p)`. La recursión del árbol de Pratt queda en «cada `qᵢ` tiene entrada en la lista», y la
buena fundación la da `qᵢ < p`.

* `primo_de_prattOK` (corrección): todo `p` con entrada en un certificado correcto es primo. Es el criterio de Lucas
  de Mathlib (`lucas_primality`) con inducción fuerte sobre `p`.
* `existe_certificado` (completitud): todo primo tiene un certificado, con `2 · 2^|C| ≤ p²` (a lo sumo `2 log₂ p − 1`
  entradas, la cuenta de Pratt: el factor 2 de `p − 1` es una hoja barata) y entradas con `a < p' ≤ p` y la lista de
  factores de `p' − 1`. La raíz primitiva viene de `reverse_lucas_primality` (las unidades de `ZMod p` son cíclicas).
* `prattOK_poly`: revisar un certificado es polinomial (cslib-frontier: `powMod` por cuadrados, producto de una lista,
  pertenencia).
* **`primos_NP`** (Pratt 1975): los primos están en NP, con certificados de `O(|p|²)` bits, la cota de Pratt: a lo
  sumo `2|p|` entradas de `11 B` bits cada una (`largo_entradas`, con `B = |p| + 1`), porque los largos de los `qᵢ`
  suman a lo sumo `|p − 1| + k` (`suma_size_le`: `|a| + |b| ≤ |ab| + 1`). En total, `63 (|w| + 2)²` bits.

**El gráfico de `minFac` en NP.** La cadena `w` es el número `numeroDe w ≥ 1` de `SigmaNP.lean`, y `numeroDe w − 1`
es el par `⟨n, m⟩` de Mathlib (`Nat.pair`; `parDe`, que es polinomial porque `Nat.unpair` usa la raíz cuadrada
entera). El certificado es `(L, C)`: la factorización de `n` y un certificado de Pratt para sus factores.

* `minFac_de_revisaGrafo` (corrección): si `∏ L = n`, `m ∈ L`, todo `q ∈ L` cumple `m ≤ q` y es primo por `C`,
  entonces `m = minFac n`. Los casos `n = 0` (`minFac 0 = 2`) y `n = 1` (`minFac 1 = 1`) se revisan aparte.
* `certificado_grafo` (completitud con cota): siempre hay un certificado de a lo sumo `63 (|n| + 1)²` bits.
* `verificador_poly` y **`grafoMinFac_NP`**: el gráfico de `minFac` está en NP. Sin hipótesis.

**La fórmula y el corolario.**

* `formulaPar ψ` = `∃ z ≤ (x + y)² + x + y + 1, z = ⟨x, y⟩ + 1 ∧ ψ(z)`: pasa de una fórmula de una variable (lo que
  da `SigmaIgualNP`, sobre `numeroDe w`) a una de dos. Es `Σᵇ₁` si `ψ` lo es (`formulaPar_sigma`), y `numeroDe` es
  sobre `[1, ∞)` (`numeroDe_sobre`).
* **`existe_formula_minFac`**: hay una `φ ∈ Σᵇ₁` con `φ(n, m) ↔ m = minFac n` para todo `n, m` (el gráfico exacto,
  no solo `φ(n, minFac n)`).
* **`s12_no_demuestra_factor_sin_formula`**: si `minFac` no es polinomial, esa `φ` tiene `∀x ∃!y φ(x, y)` verdadero
  en ℕ y S¹₂ no lo deriva. Es `s12_no_demuestra_factor` de `FactorizacionS12` sin su hipótesis (1).

## Lo que NO se prueba

* Que factorizar sea difícil (la hipótesis (2)). Sigue siendo una conjetura; Shor la tumba en el modelo cuántico.
* `FactorizacionS12.lean`, `LimiteBlanco.lean` y `SigmaNP.lean` siguen diciendo en su encabezado que `SigmaIgualNP`
  está abierto (son de otras sesiones; no se editan aquí). Este archivo es lo que cierra la pieza (1) de
  `FactorizacionS12`.

No es nuevo: la corrección y completitud son las de Pratt (1975, «Every prime has a succinct certificate», SIAM J.
Comput. 4(3), 214–220, doi:10.1137/0204018) y el corolario es la lectura clásica del teorema de testigos de Buss sobre
la factorización. Lo propio es tenerlo sobre las máquinas de Turing de Mathlib y la S¹₂ de Sagitta, sin hipótesis
abiertas salvo la dureza de factorizar.
-/

namespace Sagitta.Map.Acotada.Pratt

open Turing.MultiTapeTM

/-! ## El certificado y su revisión -/

/-- Una entrada del certificado: `(p, a, [q₁, …, q_k])`, con `a` un testigo de Lucas y los `qᵢ` los factores primos
de `p − 1`, con repetición. -/
abbrev Entrada := ℕ × ℕ × List ℕ

/-- **La revisión de una entrada**, dentro del certificado `C`: `p ≥ 2`, el producto de los `qᵢ` es `p − 1`,
`a^(p−1) ≡ 1 (mod p)`, y cada `qᵢ` tiene su propia entrada en `C` y cumple `a^((p−1)/qᵢ) ≢ 1 (mod p)`. -/
def entradaOK (C : List Entrada) (e : Entrada) : Bool :=
  decide (2 ≤ e.1) && decide (e.2.2.prod = e.1 - 1) && decide (powMod e.1 e.2.1 (e.1 - 1) = 1) &&
    e.2.2.all (fun q => decide (q ∈ C.map Prod.fst) && decide (powMod e.1 e.2.1 ((e.1 - 1) / q) ≠ 1))

/-- **Un certificado de Pratt** (aplanado): una lista de entradas, cada una correcta dentro de la lista. -/
def prattOK (C : List Entrada) : Bool := C.all (entradaOK C)

/-- Módulo `p ≥ 2`, `x^k mod p = 1` es `x^k = 1` en `ZMod p`. -/
theorem powMod_eq_uno_iff {p x k : ℕ} (hp : 2 ≤ p) : powMod p x k = 1 ↔ (x : ZMod p) ^ k = 1 := by
  rw [powMod_of_ne_zero (by omega), ← Nat.cast_pow, ← Nat.cast_one (R := ZMod p),
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (show 1 < p by omega)]

theorem entradaOK_iff (C : List Entrada) (p a : ℕ) (fs : List ℕ) :
    entradaOK C (p, a, fs) = true ↔ 2 ≤ p ∧ fs.prod = p - 1 ∧ powMod p a (p - 1) = 1 ∧
      ∀ q ∈ fs, q ∈ C.map Prod.fst ∧ powMod p a ((p - 1) / q) ≠ 1 := by
  simp [entradaOK, and_assoc]

theorem prattOK_iff (C : List Entrada) : prattOK C = true ↔ ∀ e ∈ C, entradaOK C e = true := by
  simp [prattOK]

/-- **Corrección (Lucas)**: todo `p` con entrada en un certificado de Pratt correcto es primo. -/
theorem primo_de_prattOK {C : List Entrada} (hC : prattOK C = true) :
    ∀ p, p ∈ C.map Prod.fst → p.Prime := by
  rw [prattOK_iff] at hC
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    obtain ⟨⟨p', a, fs⟩, he, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h2, hprod, ha, hfs⟩ := (entradaOK_iff C p' a fs).1 (hC _ he)
    have hprimos : ∀ q ∈ fs, q.Prime := by
      intro q hq
      have hdvd : q ∣ p' - 1 := hprod ▸ List.dvd_prod hq
      have hle : q ≤ p' - 1 := Nat.le_of_dvd (by omega) hdvd
      exact ih q (by simp only; omega) (hfs q hq).1
    refine lucas_primality p' (a : ZMod p') ((powMod_eq_uno_iff h2).1 ha) ?_
    intro q hq hdvd
    rw [← hprod] at hdvd
    obtain ⟨q', hq', hqq'⟩ := (Prime.dvd_prod_iff hq.prime).1 hdvd
    have : q = q' := (Nat.prime_dvd_prime_iff_eq hq (hprimos q' hq')).1 hqq'
    subst this
    rw [hprod] at hdvd
    intro h1
    exact (hfs q hq').2 ((powMod_eq_uno_iff h2).2 h1)

/-! ## Completitud: todo primo tiene certificado -/

theorem entradaOK_mono {C D : List Entrada} (hCD : ∀ x ∈ C, x ∈ D) {e : Entrada}
    (h : entradaOK C e = true) : entradaOK D e = true := by
  obtain ⟨p, a, fs⟩ := e
  rw [entradaOK_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun q hq => ⟨?_, (h4 q hq).2⟩⟩
  obtain ⟨x, hx, hxq⟩ := List.mem_map.1 (h4 q hq).1
  exact List.mem_map.2 ⟨x, hCD x hx, hxq⟩

theorem prattOK_append {C D : List Entrada} (hC : prattOK C = true) (hD : prattOK D = true) :
    prattOK (C ++ D) = true := by
  rw [prattOK_iff] at *
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact entradaOK_mono (fun x hx => List.mem_append_left _ hx) (hC e he)
  · exact entradaOK_mono (fun x hx => List.mem_append_right _ hx) (hD e he)

/-- Lo que se le pide al certificado de un primo `p`: correcto, con entrada para `p`, con `2·2^|C| ≤ p²` (Pratt:
a lo sumo `2 log₂ p − 1` entradas) y con entradas de la forma `(p', a, factores de p' − 1)`, `a < p' ≤ p`. -/
def Buen (p : ℕ) (C : List Entrada) : Prop :=
  prattOK C = true ∧ p ∈ C.map Prod.fst ∧ 2 * 2 ^ C.length ≤ p ^ 2 ∧
    ∀ e ∈ C, e.1 ≤ p ∧ e.2.1 < e.1 ∧ e.2.2 = (e.1 - 1).primeFactorsList

/-- Lo mismo para una lista de primos: un certificado para todos, con `2^k · 2^|C| ≤ ∏ q²`. -/
theorem certificado_lista (B : ℕ) (hB : ∀ q, q.Prime → q ≤ B → ∃ C, Buen q C) :
    ∀ l : List ℕ, (∀ q ∈ l, q.Prime ∧ q ≤ B) → ∃ C : List Entrada, prattOK C = true ∧
      (∀ q ∈ l, q ∈ C.map Prod.fst) ∧ 2 ^ l.length * 2 ^ C.length ≤ (l.map (· ^ 2)).prod ∧
      ∀ e ∈ C, e.1 ≤ B ∧ e.2.1 < e.1 ∧ e.2.2 = (e.1 - 1).primeFactorsList
  | [], _ => ⟨[], rfl, by simp, by simp, by simp⟩
  | q :: l, h => by
    obtain ⟨Cq, hok, hmem, hlen, hent⟩ := hB q (h q (by simp)).1 (h q (by simp)).2
    obtain ⟨Cl, hok', hmem', hlen', hent'⟩ := certificado_lista B hB l (fun x hx => h x (by simp [hx]))
    refine ⟨Cq ++ Cl, prattOK_append hok hok', ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hmem
        exact List.mem_map.2 ⟨y, List.mem_append_left _ hy, hyx⟩
      · obtain ⟨y, hy, hyx⟩ := List.mem_map.1 (hmem' x hx)
        exact List.mem_map.2 ⟨y, List.mem_append_right _ hy, hyx⟩
    · simp only [List.length_cons, List.length_append, List.map_cons, List.prod_cons, pow_add, pow_succ]
      calc 2 ^ l.length * 2 * (2 ^ Cq.length * 2 ^ Cl.length)
          = (2 * 2 ^ Cq.length) * (2 ^ l.length * 2 ^ Cl.length) := by ring
        _ ≤ q ^ 2 * (l.map (· ^ 2)).prod := Nat.mul_le_mul hlen hlen'
    · intro e he
      rcases List.mem_append.1 he with he | he
      · obtain ⟨h1, h2, h3⟩ := hent e he
        exact ⟨h1.trans (h q (by simp)).2, h2, h3⟩
      · exact hent' e he

/-- El producto de los cuadrados es el cuadrado del producto. -/
theorem prod_map_cuadrado (l : List ℕ) : (l.map (· ^ 2)).prod = l.prod ^ 2 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_pow]

/-- Si `n ≥ 2` tiene a lo sumo un factor primo (con repetición), `n` es primo. -/
theorem primo_de_largo_le_uno {n : ℕ} (hn : 2 ≤ n) (h : n.primeFactorsList.length ≤ 1) : n.Prime := by
  have hprod := Nat.prod_primeFactorsList (show n ≠ 0 by omega)
  match hl : n.primeFactorsList, h with
  | [], _ => rw [hl] at hprod; simp at hprod; omega
  | [q], _ =>
    rw [hl, List.prod_singleton] at hprod
    exact hprod ▸ Nat.prime_of_mem_primeFactorsList (by rw [hl]; exact List.mem_singleton_self q)

/-- **Completitud (Pratt 1975)**: todo primo tiene un certificado, con a lo sumo `2 log₂ p − 1` entradas. -/
theorem existe_certificado : ∀ p : ℕ, p.Prime → ∃ C, Buen p C := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    have h2 := hp.two_le
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, ha, hd⟩ := reverse_lucas_primality p hp
    set fs := (p - 1).primeFactorsList with hfs
    have hprod : fs.prod = p - 1 := Nat.prod_primeFactorsList (by omega)
    have hfsP : ∀ q ∈ fs, q.Prime ∧ q ≤ p - 1 := fun q hq =>
      ⟨Nat.prime_of_mem_primeFactorsList hq, Nat.le_of_mem_primeFactorsList hq⟩
    obtain ⟨C₀, hok, hmem, hlen, hent⟩ := certificado_lista (p - 1)
      (fun q hq hqB => ih q (by omega) hq) fs hfsP
    have hval : ((a.val : ℕ) : ZMod p) = a := ZMod.natCast_zmod_val a
    refine ⟨(p, a.val, fs) :: C₀, ?_, by simp, ?_, ?_⟩
    · rw [prattOK_iff]
      have hentrada : entradaOK ((p, a.val, fs) :: C₀) (p, a.val, fs) = true := by
        rw [entradaOK_iff]
        refine ⟨h2, hprod, (powMod_eq_uno_iff h2).2 (by rw [hval]; exact ha), fun q hq => ⟨?_, ?_⟩⟩
        · obtain ⟨y, hy, hyq⟩ := List.mem_map.1 (hmem q hq)
          exact List.mem_map.2 ⟨y, List.mem_cons_of_mem _ hy, hyq⟩
        · rw [Ne, powMod_eq_uno_iff h2, hval]
          exact hd q (hfsP q hq).1 (Nat.dvd_of_mem_primeFactorsList hq)
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hentrada
      · exact entradaOK_mono (fun x hx => List.mem_cons_of_mem _ hx) ((prattOK_iff C₀).1 hok e he)
    · -- `2 · 2^(1 + |C₀|) ≤ p²`: con `k = |fs|`, `2^k · 2^|C₀| ≤ (p − 1)²`.
      rw [prod_map_cuadrado, hprod] at hlen
      simp only [List.length_cons, pow_succ]
      rcases Nat.lt_or_ge fs.length 2 with hk | hk
      · -- `p − 1` es 1 o primo: `p = 2` o `p = 3`.
        rcases Nat.lt_or_ge p 4 with hp4 | hp4
        · interval_cases p
          · -- p = 2: no hay factores, `C₀ = []`.
            have : fs = [] := by rw [hfs]; simp
            rw [this] at hlen
            simp at hlen
            have : C₀.length = 0 := by
              by_contra hc; have : 2 ≤ 2 ^ C₀.length := Nat.le_self_pow hc 2; omega
            simp [this]
          · have : fs = [2] := by rw [hfs]; exact Nat.primeFactorsList_prime Nat.prime_two
            rw [this] at hlen
            simp at hlen
            have : C₀.length ≤ 1 := by
              by_contra hc
              have : 2 ^ 2 ≤ 2 ^ C₀.length := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
            have : 2 ^ C₀.length ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
            omega
        · exfalso
          have hpm1 : (p - 1).Prime := primo_de_largo_le_uno (by omega) (by rw [← hfs]; omega)
          rcases hp.eq_two_or_odd' with rfl | hodd
          · omega
          · have heven : Even (p - 1) := by
              rcases hodd with ⟨r, hr⟩; exact ⟨r, by omega⟩
            have := (hpm1.even_iff).1 heven
            omega
      · have h4 : 4 ≤ 2 ^ fs.length := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ fs.length := Nat.pow_le_pow_right (by norm_num) hk
        have : (p - 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
        nlinarith
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨le_rfl, ZMod.val_lt a, rfl⟩
      · obtain ⟨h1, h2', h3⟩ := hent e he
        exact ⟨by omega, h2', h3⟩

/-! ## La revisión es polinomial -/

/-- La codificación de una entrada: `p`, `a` en binario y la lista de los `qᵢ` en binario. -/
abbrev encEntrada : Entrada ↪ List Bool := encPair encNat (encPair encNat (encList encNat))

/-- La codificación de un certificado de Pratt. -/
abbrev encPratt : List Entrada ↪ List Bool := encList encEntrada

theorem entradaOK_poly : ComputableInPolyTime (fun x : List Entrada × Entrada => entradaOK x.1 x.2)
    (encPair encPratt encEntrada) encBool := by
  unfold entradaOK
  have hp : ComputableInPolyTime (fun x : List Entrada × Entrada => x.2.1) (encPair encPratt encEntrada) encNat := by
    fun_prop
  have ha : ComputableInPolyTime (fun x : List Entrada × Entrada => x.2.2.1) (encPair encPratt encEntrada) encNat := by
    fun_prop
  have hfs : ComputableInPolyTime (fun x : List Entrada × Entrada => x.2.2.2) (encPair encPratt encEntrada)
      (encList encNat) := by
    fun_prop
  have hprod := ComputableInPolyTime.binary_prod.comp hfs
  have hpm1 := ComputableInPolyTime.binary_sub' hp (ComputableInPolyTime.const 1)
  have hpow := computableInPolyTime_powMod hp ha hpm1
  have hfst : ComputableInPolyTime (fun x : List Entrada × Entrada => x.1.map Prod.fst)
      (encPair encPratt encEntrada) (encList encNat) := by
    fun_prop
  have hinner : ComputableInPolyTime (fun y : (List Entrada × Entrada) × ℕ =>
      decide (y.2 ∈ y.1.1.map Prod.fst) && decide (powMod y.1.2.1 y.1.2.2.1 ((y.1.2.1 - 1) / y.2) ≠ 1))
      (encPair (encPair encPratt encEntrada) encNat) encBool := by
    have hq : ComputableInPolyTime (fun y : (List Entrada × Entrada) × ℕ => y.2)
        (encPair (encPair encPratt encEntrada) encNat) encNat := by fun_prop
    have hmem := ComputableInPolyTime.decide_mem (hfst.comp (ComputableInPolyTime.fst _ _)) hq
    have hexp := ComputableInPolyTime.binary_div' (hpm1.comp (ComputableInPolyTime.fst _ _)) hq
    have hpow' := computableInPolyTime_powMod (hp.comp (ComputableInPolyTime.fst _ _))
      (ha.comp (ComputableInPolyTime.fst _ _)) hexp
    fun_prop
  have hall := ComputableInPolyTime.allWithInput (test := fun (x : List Entrada × Entrada) (q : ℕ) =>
    decide (q ∈ x.1.map Prod.fst) && decide (powMod x.2.1 x.2.2.1 ((x.2.1 - 1) / q) ≠ 1)) hfs hinner
  fun_prop

theorem prattOK_poly : ComputableInPolyTime prattOK encPratt encBool := by
  unfold prattOK
  exact ComputableInPolyTime.allWithInput (test := entradaOK) ComputableInPolyTime.id' entradaOK_poly

/-! ## El gráfico de `Nat.minFac` en NP -/

/-- El par de una entrada: la cadena `w` es el número `numeroDe w ≥ 1`, y `numeroDe w − 1` es el par `(n, m)` de
Mathlib (`Nat.pair`). -/
def parDe (w : List Bool) : ℕ × ℕ := Nat.unpair (ofBits (w ++ [true]) - 1)

theorem unpair_poly : ComputableInPolyTime Nat.unpair encNat (encPair encNat encNat) := by
  unfold Nat.unpair
  have hs := ComputableInPolyTime.binary_sqrt
  fun_prop

theorem parDe_poly : ComputableInPolyTime parDe encBits (encPair encNat encNat) := by
  unfold parDe
  have h1 : ComputableInPolyTime (fun w : List Bool => w ++ [true]) encBits encBits := by fun_prop
  have h2 := ComputableInPolyTime.bitsToNat.comp h1
  exact unpair_poly.comp (ComputableInPolyTime.binary_sub' h2 (ComputableInPolyTime.const 1))

/-- El certificado del gráfico: la factorización de `n` y un certificado de Pratt para sus factores. -/
abbrev encCertificado : List ℕ × List Entrada ↪ List Bool := encPair (encList encNat) encPratt

/-- El decodificador (total) del certificado. -/
def decodificador : Decoder encCertificado :=
  Decoder.pair (Decoder.list Decoder.nat)
    (Decoder.list (Decoder.pair Decoder.nat (Decoder.pair Decoder.nat (Decoder.list Decoder.nat))))

/-- **La revisión del gráfico** `m = minFac n`. Para `n ≥ 2`, el certificado `(L, C)` sirve si `∏ L = n`, `m ∈ L`,
todo `q ∈ L` cumple `m ≤ q` y tiene entrada en `C`, y `C` es un certificado de Pratt correcto. -/
def revisaGrafo (n m : ℕ) (c : List ℕ × List Entrada) : Bool :=
  if n = 0 then decide (m = 2) else if n = 1 then decide (m = 1) else
    decide (c.1.prod = n) && decide (m ∈ c.1) &&
      c.1.all (fun q => decide (m ≤ q) && decide (q ∈ c.2.map Prod.fst)) && prattOK c.2

/-- **El verificador**: decodifica el par y el certificado, y revisa. -/
def verificador (x : List Bool × List Bool) : Bool :=
  revisaGrafo (parDe x.1).1 (parDe x.1).2 (decodificador.decode x.2)

theorem revisaGrafo_poly : ComputableInPolyTime (fun x : (ℕ × ℕ) × (List ℕ × List Entrada) =>
    revisaGrafo x.1.1 x.1.2 x.2) (encPair (encPair encNat encNat) encCertificado) encBool := by
  unfold revisaGrafo
  have hL : ComputableInPolyTime (fun x : (ℕ × ℕ) × (List ℕ × List Entrada) => x.2.1)
      (encPair (encPair encNat encNat) encCertificado) (encList encNat) := by fun_prop
  have hC : ComputableInPolyTime (fun x : (ℕ × ℕ) × (List ℕ × List Entrada) => x.2.2)
      (encPair (encPair encNat encNat) encCertificado) encPratt := by fun_prop
  have hprod := ComputableInPolyTime.binary_prod.comp hL
  have hok := prattOK_poly.comp hC
  have hinner : ComputableInPolyTime (fun y : ((ℕ × ℕ) × (List ℕ × List Entrada)) × ℕ =>
      decide (y.1.1.2 ≤ y.2) && decide (y.2 ∈ y.1.2.2.map Prod.fst))
      (encPair (encPair (encPair encNat encNat) encCertificado) encNat) encBool := by
    have hmap : ComputableInPolyTime (fun y : ((ℕ × ℕ) × (List ℕ × List Entrada)) × ℕ => y.1.2.2.map Prod.fst)
        (encPair (encPair (encPair encNat encNat) encCertificado) encNat) (encList encNat) := by fun_prop
    have hq : ComputableInPolyTime (fun y : ((ℕ × ℕ) × (List ℕ × List Entrada)) × ℕ => y.2)
        (encPair (encPair (encPair encNat encNat) encCertificado) encNat) encNat := by fun_prop
    have hmem := ComputableInPolyTime.decide_mem hmap hq
    have hm' : ComputableInPolyTime (fun y : ((ℕ × ℕ) × (List ℕ × List Entrada)) × ℕ => y.1.1.2)
        (encPair (encPair (encPair encNat encNat) encCertificado) encNat) encNat := by fun_prop
    exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.binary_le' hm' hq) hmem
  have hall := ComputableInPolyTime.allWithInput
    (test := fun (x : (ℕ × ℕ) × (List ℕ × List Entrada)) (q : ℕ) =>
      decide (x.1.2 ≤ q) && decide (q ∈ x.2.2.map Prod.fst)) hL hinner
  have hn : ComputableInPolyTime (fun x : (ℕ × ℕ) × (List ℕ × List Entrada) => x.1.1)
      (encPair (encPair encNat encNat) encCertificado) encNat := by fun_prop
  have hm : ComputableInPolyTime (fun x : (ℕ × ℕ) × (List ℕ × List Entrada) => x.1.2)
      (encPair (encPair encNat encNat) encCertificado) encNat := by fun_prop
  have c0 := ComputableInPolyTime.decide_eq' hn (ComputableInPolyTime.const 0)
  have c1 := ComputableInPolyTime.decide_eq' hn (ComputableInPolyTime.const 1)
  have y0 := ComputableInPolyTime.decide_eq' hm (ComputableInPolyTime.const 2)
  have y1 := ComputableInPolyTime.decide_eq' hm (ComputableInPolyTime.const 1)
  have b1 := ComputableInPolyTime.decide_eq' hprod hn
  have b2 := ComputableInPolyTime.decide_mem hL hm
  have resto := ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.bool_and' b1 b2) hall) hok
  exact ComputableInPolyTime.ite_decide c0 y0 (ComputableInPolyTime.ite_decide c1 y1 resto)

theorem verificador_poly : ComputableInPolyTime verificador (encPair encBits encBits) encBool := by
  unfold verificador
  have h1 := parDe_poly.comp (ComputableInPolyTime.fst encBits encBits)
  have h2 := decodificador.computableInPolyTime.comp (ComputableInPolyTime.snd encBits encBits)
  exact revisaGrafo_poly.comp (h1.prod h2)

/-! ### Corrección y completitud del verificador -/

/-- **Corrección**: si la revisión acepta, `m = minFac n`. -/
theorem minFac_de_revisaGrafo {n m : ℕ} {c : List ℕ × List Entrada} (h : revisaGrafo n m c = true) :
    m = Nat.minFac n := by
  unfold revisaGrafo at h
  split_ifs at h with h0 h1
  · subst h0; simpa using h
  · subst h1; simpa using h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hprod, hm⟩, hall⟩, hok⟩ := h
    have hprimos : ∀ q ∈ c.1, q.Prime := fun q hq => primo_de_prattOK hok q (hall q hq).2
    have hmP := hprimos m hm
    have hdvd : m ∣ n := hprod ▸ List.dvd_prod hm
    have hle : Nat.minFac n ≤ m := Nat.minFac_le_of_dvd hmP.two_le hdvd
    have hmin : (Nat.minFac n).Prime := Nat.minFac_prime h1
    obtain ⟨q, hq, hdq⟩ := (Prime.dvd_prod_iff hmin.prime).1 (by rw [hprod]; exact Nat.minFac_dvd n)
    have : Nat.minFac n = q := (Nat.prime_dvd_prime_iff_eq hmin (hprimos q hq)).1 hdq
    have := (hall q hq).1
    omega

/-- Una lista de números `≥ 2` tiene a lo sumo `log₂` de su producto elementos. -/
theorem dos_pow_largo_le_prod : ∀ l : List ℕ, (∀ q ∈ l, 2 ≤ q) → 2 ^ l.length ≤ l.prod
  | [], _ => by simp
  | q :: l, h => by
    simp only [List.length_cons, List.prod_cons, pow_succ]
    have := dos_pow_largo_le_prod l (fun x hx => h x (by simp [hx]))
    have hq := h q (by simp)
    calc 2 ^ l.length * 2 ≤ l.prod * q := Nat.mul_le_mul this hq
      _ = q * l.prod := by ring

/-- El largo de una lista codificada con elementos de a lo sumo `K` bits. -/
theorem largo_encList_le {α : Type} (enc : α ↪ List Bool) (K : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (enc a).length ≤ K) → (encList enc l).length ≤ l.length * (2 * K + 1)
  | [], _ => by simp
  | a :: l, h => by
    have ih := largo_encList_le enc K l (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    rw [encList_cons, List.length_append, length_frame, List.length_cons]
    nlinarith

theorem largo_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

/-- El largo de un producto: `|a| + |b| ≤ |a·b| + 1`. -/
theorem size_mul_ge {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : a.size + b.size ≤ (a * b).size + 1 := by
  have sa := Nat.size_pos.2 ha
  have sb := Nat.size_pos.2 hb
  have h1 : 2 ^ (a.size - 1) ≤ a := Nat.lt_size.1 (by omega)
  have h2 : 2 ^ (b.size - 1) ≤ b := Nat.lt_size.1 (by omega)
  have h3 : 2 ^ (a.size - 1 + (b.size - 1)) ≤ a * b := by rw [pow_add]; exact Nat.mul_le_mul h1 h2
  have := Nat.lt_size.2 h3
  omega

/-- **La cuenta fina de Pratt**: los largos de los factores suman a lo sumo el largo del producto más su número. -/
theorem suma_size_le : ∀ l : List ℕ, (∀ q ∈ l, 1 ≤ q) → (l.map Nat.size).sum ≤ l.prod.size + l.length
  | [], _ => by simp
  | q :: l, h => by
    have ih := suma_size_le l (fun x hx => h x (by simp [hx]))
    have hq := h q (by simp)
    have hl : 1 ≤ l.prod := List.prod_pos (fun x hx => h x (by simp [hx]))
    have := size_mul_ge hq hl
    simp only [List.map_cons, List.sum_cons, List.prod_cons, List.length_cons]
    omega

theorem largo_encList_nat (l : List ℕ) : (encList encNat l).length = 2 * (l.map Nat.size).sum + l.length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih, largo_encNat]; ring

/-- **El tamaño de una entrada**: si `p ≤ n < 2^(B−1)`, `a < p` y la lista es la de los factores de `p − 1`, la entrada
ocupa a lo sumo `11 B` bits: lineal en `|n|`, como en Pratt. -/
theorem largo_entradas {n B : ℕ} (hB1 : 1 ≤ B) (hnB : n < 2 ^ (B - 1)) {C : List Entrada}
    (hent : ∀ e ∈ C, e.1 ≤ n ∧ e.2.1 < e.1 ∧ e.2.2 = (e.1 - 1).primeFactorsList) :
    ∀ e ∈ C, (encEntrada e).length ≤ 11 * B := by
  have hsize : ∀ x ≤ n, x.size ≤ B := fun x hx => by
    have := Nat.size_le_size hx
    have : n.size ≤ B - 1 := Nat.size_le.2 hnB
    omega
  intro e he
  obtain ⟨h1, h2, h3⟩ := hent e he
  obtain ⟨p, a, fs⟩ := e
  simp only at h1 h2 h3
  have hfs2 : ∀ q ∈ fs, 2 ≤ q := fun q hq => by
    rw [h3] at hq; exact (Nat.prime_of_mem_primeFactorsList hq).two_le
  have hfsn : ∀ q ∈ fs, q ≤ n := fun q hq => by
    rw [h3] at hq; have := Nat.le_of_mem_primeFactorsList hq; omega
  have hfslen : fs.length ≤ B := by
    have h4 := dos_pow_largo_le_prod fs hfs2
    have h5 : fs.prod ≤ n := by
      by_cases h0 : p - 1 = 0
      · rw [h3, h0]; simp; omega
      · rw [h3, Nat.prod_primeFactorsList h0]; omega
    have h6 : 2 ^ fs.length < 2 ^ (B - 1) := by omega
    have := Nat.pow_lt_pow_iff_right (a := 2) (by norm_num) |>.1 h6
    omega
  have hsum := suma_size_le fs (fun q hq => by have := hfs2 q hq; omega)
  have hprodB : fs.prod.size ≤ B := by
    apply hsize
    by_cases h0 : p - 1 = 0
    · rw [h3, h0]; simp; omega
    · rw [h3, Nat.prod_primeFactorsList h0]; omega
  have hpB := hsize p h1
  have haB := hsize a (by omega)
  simp only [encEntrada, length_encPair, largo_encNat, largo_encList_nat]
  omega

/-- **Completitud, con la cota**: si `m = minFac n`, hay un certificado de a lo sumo `63 (|n| + 1)²` bits. -/
theorem certificado_grafo (n : ℕ) : ∃ c : List ℕ × List Entrada, revisaGrafo n (Nat.minFac n) c = true ∧
    (encCertificado c).length ≤ 63 * (n.size + 1) ^ 2 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · refine ⟨([], []), ?_, by simp; have := Nat.one_le_pow 2 (n.size + 1) (by omega); omega⟩
    interval_cases n <;> simp [revisaGrafo]
  set B := n.size + 1 with hBdef
  have hB1 : 1 ≤ B := by omega
  have hnB : n < 2 ^ (B - 1) := by rw [hBdef, Nat.add_sub_cancel]; exact Nat.lt_size_self n
  set L := n.primeFactorsList with hL
  have hLP : ∀ q ∈ L, q.Prime ∧ q ≤ n := fun q hq =>
    ⟨Nat.prime_of_mem_primeFactorsList hq, Nat.le_of_mem_primeFactorsList hq⟩
  obtain ⟨C, hok, hmem, hlen, hent⟩ := certificado_lista n (fun q hq _ => existe_certificado q hq) L hLP
  have hprod : L.prod = n := Nat.prod_primeFactorsList (by omega)
  rw [prod_map_cuadrado, hprod] at hlen
  -- `|L| + |C| < 2B`.
  have hLC : L.length + C.length ≤ 2 * B := by
    have h1 : 2 ^ (L.length + C.length) ≤ n ^ 2 := by rw [pow_add]; exact hlen
    have h2 : n ^ 2 < (2 ^ (B - 1)) ^ 2 := Nat.pow_lt_pow_left hnB (by norm_num)
    rw [← pow_mul] at h2
    have := Nat.pow_lt_pow_iff_right (a := 2) (by norm_num) |>.1 (lt_of_le_of_lt h1 h2)
    omega
  have hsize : ∀ x ≤ n, x.size ≤ B := fun x hx => by
    have := Nat.size_le_size hx; omega
  refine ⟨(L, C), ?_, ?_⟩
  · unfold revisaGrafo
    have h0 : ¬ n = 0 := by omega
    have h1 : ¬ n = 1 := by omega
    simp only [h0, h1, ↓reduceIte]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨hprod, ?_⟩, fun q hq => ⟨?_, hmem q hq⟩⟩, hok⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [hL, Nat.primeFactorsList_add_two]; simp
    · exact Nat.minFac_le_of_dvd (hLP q hq).1.two_le (Nat.dvd_of_mem_primeFactorsList hq)
  · -- Las cuentas.
    have hsumL := suma_size_le L (fun q hq => (hLP q hq).1.one_lt.le)
    rw [hprod] at hsumL
    have hEnt := largo_entradas hB1 hnB hent
    have hCenc := largo_encList_le encEntrada (11 * B) C hEnt
    have hm := Nat.mul_le_mul_right (2 * (11 * B) + 1) hLC
    have hnB' : n.size ≤ B := hsize n le_rfl
    simp only [encCertificado, length_encPair, largo_encList_nat]
    nlinarith

/-! ### El gráfico está en NP -/

/-- `numeroDe w` es el número cuyos bits (del menos significativo) son `w` seguido de un 1. -/
theorem numeroDe_eq_ofBits (w : List Bool) : numeroDe w = ofBits (w ++ [true]) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [numeroDe_cons, ih]
    change _ = Nat.bit b (ofBits (w ++ [true]))
    cases b <;> simp [Nat.bit]

theorem numeroDe_lt (w : List Bool) : numeroDe w < 2 ^ (w.length + 1) := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [pow_succ] at ih ⊢ <;> omega

theorem parDe_eq (w : List Bool) : parDe w = Nat.unpair (numeroDe w - 1) := by
  rw [parDe, numeroDe_eq_ofBits]

/-- **El gráfico de `Nat.minFac`** como problema de cadenas: `w` es un caso «sí» si `numeroDe w − 1` es el par
`⟨n, m⟩` (de Mathlib) con `m = minFac n`. -/
def grafoMinFac : Problema := fun w => decide ((parDe w).2 = Nat.minFac (parDe w).1)

/-- El tope de los certificados: `63 (|w| + 2)²` bits. -/
noncomputable def tope : Polynomial ℕ := 63 * (Polynomial.X + 2) ^ 2

theorem size_parDe_le (w : List Bool) : (parDe w).1.size ≤ w.length + 1 := by
  rw [Nat.size_le, parDe_eq]
  have h1 := Nat.unpair_left_le (numeroDe w - 1)
  have h2 := numeroDe_lt w
  omega

/-- **El gráfico de `Nat.minFac` está en NP** (la NP de `Clases.lean`): el certificado es la factorización de `n`
con un certificado de Pratt para cada factor, y se revisa en tiempo polinomial. Sin hipótesis. -/
theorem grafoMinFac_NP : grafoMinFac ∈ NP := by
  refine ⟨tope, verificador, Tiempo.IndiceRapido.esPolinomial_de_cslib verificador_poly, fun w => ?_⟩
  simp only [grafoMinFac, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨c, hc, hlen⟩ := certificado_grafo (parDe w).1
    refine ⟨encCertificado c, ?_, ?_⟩
    · have hs := size_parDe_le w
      have : 63 * ((parDe w).1.size + 1) ^ 2 ≤ 63 * (w.length + 2) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      simp only [tope, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega
    · simp only [verificador, decodificador.decode_enc]
      rw [h]; exact hc
  · rintro ⟨y, _, hy⟩
    exact minFac_de_revisaGrafo hy

/-! ### Pratt (1975): los primos están en NP -/

/-- El decodificador de un certificado de Pratt. -/
def decodificadorPratt : Decoder encPratt :=
  Decoder.list (Decoder.pair Decoder.nat (Decoder.pair Decoder.nat (Decoder.list Decoder.nat)))

/-- **El verificador de Pratt**: el número de la entrada tiene entrada en un certificado correcto. -/
def verificadorPrimo (x : List Bool × List Bool) : Bool :=
  decide (ofBits (x.1 ++ [true]) - 1 ∈ (decodificadorPratt.decode x.2).map Prod.fst) &&
    prattOK (decodificadorPratt.decode x.2)

theorem verificadorPrimo_poly : ComputableInPolyTime verificadorPrimo (encPair encBits encBits) encBool := by
  unfold verificadorPrimo
  have hw : ComputableInPolyTime (fun x : List Bool × List Bool => x.1 ++ [true]) (encPair encBits encBits)
      encBits := by fun_prop
  have hp := ComputableInPolyTime.binary_sub' (ComputableInPolyTime.bitsToNat.comp hw) (ComputableInPolyTime.const 1)
  have hC := decodificadorPratt.computableInPolyTime.comp (ComputableInPolyTime.snd encBits encBits)
  have hmap : ComputableInPolyTime (fun x : List Bool × List Bool => (decodificadorPratt.decode x.2).map Prod.fst)
      (encPair encBits encBits) (encList encNat) := by fun_prop
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.decide_mem hmap hp) (prattOK_poly.comp hC)

/-- **PRIMES como problema de cadenas**: `w` es un caso «sí» si `numeroDe w − 1` es primo. -/
def primos : Problema := fun w => decide (numeroDe w - 1).Prime

theorem cuenta_cuadratica {B : ℕ} (hB : 1 ≤ B) : 2 * B * (2 * (11 * B) + 1) ≤ 63 * B ^ 2 := by
  nlinarith

/-- **Pratt (1975): todo primo tiene un certificado sucinto**, y los primos están en NP (la de `Clases.lean`). El
certificado tiene a lo sumo `2 log₂ p − 1` entradas (`Buen`) de `O(|p|)` bits cada una (`largo_entradas`): `O(|p|²)`
bits, como en Pratt. -/
theorem primos_NP : primos ∈ NP := by
  refine ⟨tope, verificadorPrimo, Tiempo.IndiceRapido.esPolinomial_de_cslib verificadorPrimo_poly, fun w => ?_⟩
  simp only [primos, decide_eq_true_eq, verificadorPrimo, Bool.and_eq_true, ← numeroDe_eq_ofBits]
  constructor
  · intro hp
    obtain ⟨C, hok, hmem, hlen, hent⟩ := existe_certificado _ hp
    refine ⟨encPratt C, ?_, ?_⟩
    · set n := numeroDe w - 1
      set B := w.length + 2
      have hnB : n < 2 ^ (B - 1) := by
        have := numeroDe_lt w
        rw [show B - 1 = w.length + 1 by omega]
        omega
      have hent' : ∀ e ∈ C, e.1 ≤ n ∧ e.2.1 < e.1 ∧ e.2.2 = (e.1 - 1).primeFactorsList := hent
      have hE := largo_entradas (by omega) hnB hent'
      have hCl : C.length ≤ 2 * B := by
        have h1 : 2 * 2 ^ C.length < 2 * 2 ^ (2 * (B - 1)) := by
          calc 2 * 2 ^ C.length ≤ n ^ 2 := hlen
            _ < (2 ^ (B - 1)) ^ 2 := Nat.pow_lt_pow_left hnB (by norm_num)
            _ = 2 ^ (2 * (B - 1)) := by rw [← pow_mul, mul_comm]
            _ ≤ 2 * 2 ^ (2 * (B - 1)) := by omega
        have := Nat.pow_lt_pow_iff_right (a := 2) (by norm_num) |>.1 (by omega : 2 ^ C.length < 2 ^ (2 * (B - 1)))
        omega
      have hCenc := largo_encList_le encEntrada (11 * B) C hE
      simp only [tope, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      have hB1 : 1 ≤ B := Nat.le_add_left 1 (w.length + 1)
      have h3a := Nat.mul_le_mul_right (2 * (11 * B) + 1) hCl
      have h3b := cuenta_cuadratica hB1
      have h3 := h3a.trans h3b
      change (encList encEntrada C).length ≤ 63 * ((w.length : ℕ) + 2) ^ 2
      exact hCenc.trans h3
    · simp only [decodificadorPratt.decode_enc]
      exact ⟨hmem, hok⟩
  · rintro ⟨y, _, hmem, hok⟩
    exact primo_de_prattOK hok _ hmem

/-! ## De NP a una fórmula `Σᵇ₁` con gráfico `minFac` -/

section Formula

open FirstOrder FirstOrder.Language

/-- Todo número `z ≥ 1` es `numeroDe w` para alguna cadena `w`. -/
theorem numeroDe_sobre : ∀ z : ℕ, 1 ≤ z → ∃ w, numeroDe w = z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hz
    rcases Nat.lt_or_ge z 2 with h | h
    · exact ⟨[], by simp; omega⟩
    · obtain ⟨w, hw⟩ := ih (z / 2) (by omega) (by omega)
      refine ⟨decide (z % 2 = 1) :: w, ?_⟩
      rw [numeroDe_cons, hw]
      rcases Nat.mod_two_eq_zero_or_one z with h2 | h2 <;> simp [h2] <;> omega

/-- Las variables: `x` (libre 0), `y` (libre 1) y `z` (la ligada). -/
def vX : L.Term (Fin 2 ⊕ Fin 1) := Term.var (Sum.inl 0)
def vY : L.Term (Fin 2 ⊕ Fin 1) := Term.var (Sum.inl 1)
def vZ : L.Term (Fin 2 ⊕ Fin 1) := Term.var (Sum.inr 0)

/-- **`z = ⟨x, y⟩ + 1`**, con el par de Mathlib: `⟨x, y⟩ = y² + x` si `x < y`, y `x² + x + y` si no. Sin
cuantificadores. -/
def codigoPar : L.BoundedFormula (Fin 2) 1 :=
  (leF (tSc vX) vY ⊓ BoundedFormula.equal vZ (tSc (tMs (tPr vY vY) vX))) ⊔
    (leF vY vX ⊓ BoundedFormula.equal vZ (tSc (tMs (tMs (tPr vX vX) vX) vY)))

/-- La cota del código: `(x + y)² + x + y + 1`. -/
def cotaPar : L.Term (Fin 2 ⊕ Fin 0) :=
  tSc (tMs (tMs (tPr (tMs (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1)))
    (tMs (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1)))) (Term.var (Sum.inl 0))) (Term.var (Sum.inl 1)))

/-- **La fórmula de dos variables**: `∃ z ≤ (x + y)² + x + y + 1, z = ⟨x, y⟩ + 1 ∧ ψ(z)`. -/
def formulaPar (ψ : L.Formula (Fin 1)) : L.Formula (Fin 2) :=
  existeAcotado cotaPar (codigoPar ⊓ BoundedFormula.relabel (fun _ : Fin 1 => (Sum.inr 0 : Fin 2 ⊕ Fin 1)) ψ)

theorem formulaPar_sigma {ψ : L.Formula (Fin 1)} (hψ : EsSigma1 ψ) : EsSigma1 (formulaPar ψ) :=
  .existe _ (.y (.o (.y (.aguda (.rel _ _)) (.aguda (.igual _ _))) (.y (.aguda (.rel _ _)) (.aguda (.igual _ _))))
    (Arranque.EsSigma1.relabel _ hψ))

theorem realize_codigoPar (x y z : ℕ) (xs : Fin 0 → ℕ) :
    codigoPar.Realize ![x, y] (Fin.snoc xs z) ↔ z = Nat.pair x y + 1 := by
  simp only [codigoPar, BoundedFormula.realize_sup, BoundedFormula.realize_inf, Parikh.realize_leF]
  change (x + 1 ≤ y ∧ z = y * y + x + 1) ∨ (y ≤ x ∧ z = x * x + x + y + 1) ↔ _
  rw [Nat.pair]
  split_ifs with h <;> omega

theorem realize_cotaPar (x y : ℕ) (xs : Fin 0 → ℕ) :
    cotaPar.realize (Sum.elim ![x, y] xs) = (x + y) * (x + y) + x + y + 1 := rfl

theorem pair_lt_cota (x y : ℕ) : Nat.pair x y + 1 ≤ (x + y) * (x + y) + x + y + 1 := by
  rw [Nat.pair]; split_ifs <;> nlinarith

/-- `ψ(z)` dentro del cuantificador. -/
theorem realize_relabel_z (ψ : L.Formula (Fin 1)) (v : Fin 2 → ℕ) (xs : Fin 1 → ℕ) :
    (BoundedFormula.relabel (fun _ : Fin 1 => (Sum.inr 0 : Fin 2 ⊕ Fin 1)) ψ).Realize v xs ↔ ψ.Realize ![xs 0] := by
  rw [BoundedFormula.realize_relabel, Formula.Realize]
  have e1 : (Sum.elim v (xs ∘ Fin.castAdd 0) ∘ fun _ : Fin 1 => (Sum.inr 0 : Fin 2 ⊕ Fin 1)) = ![xs 0] := by
    funext i; fin_cases i; rfl
  rw [e1]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- **Lo que dice la fórmula**: `formulaPar ψ (x, y)` vale si y solo si `ψ` vale en `⟨x, y⟩ + 1`. -/
theorem realize_formulaPar (ψ : L.Formula (Fin 1)) (x y : ℕ) :
    (formulaPar ψ).Realize ![x, y] ↔ ψ.Realize ![Nat.pair x y + 1] := by
  rw [formulaPar, Formula.Realize, Parikh.realize_existe, realize_cotaPar]
  simp only [BoundedFormula.realize_inf, realize_relabel_z]
  constructor
  · rintro ⟨z, _, hc, hψ⟩
    rw [realize_codigoPar] at hc
    subst hc
    exact hψ
  · intro hψ
    exact ⟨Nat.pair x y + 1, (le_nat _ _).2 (pair_lt_cota x y), (realize_codigoPar x y _ _).2 rfl, hψ⟩

/-- **El gráfico de `minFac` se escribe con una fórmula `Σᵇ₁`** (sin hipótesis): `Σᵇ₁ = NP` (Wrathall–Stockmeyer,
`SigmaFagin.sigmaIgualNP`) aplicado a `grafoMinFac_NP`, y el par de Mathlib para pasar de una variable a dos. -/
theorem existe_formula_minFac :
    ∃ φ : L.Formula (Fin 2), EsSigma1 φ ∧ ∀ n m : ℕ, φ.Realize ![n, m] ↔ m = Nat.minFac n := by
  obtain ⟨ψ, hψ, hdef⟩ := (SigmaFagin.sigmaIgualNP grafoMinFac).1 grafoMinFac_NP
  refine ⟨formulaPar ψ, formulaPar_sigma hψ, fun n m => ?_⟩
  rw [realize_formulaPar]
  obtain ⟨w, hw⟩ := numeroDe_sobre (Nat.pair n m + 1) (by omega)
  rw [← hw, ← hdef w]
  simp only [grafoMinFac, decide_eq_true_eq, parDe_eq, hw, Nat.add_sub_cancel, Nat.unpair_pair]

end Formula

/-! ## El corolario: la hipótesis (1) de `FactorizacionS12` ya no hace falta -/

open FactorizacionS12 in
/-- **Si encontrar el menor factor primo no es polinomial, hay una fórmula `Σᵇ₁` cuyo gráfico en ℕ es exactamente
`Nat.minFac`, con `∀x ∃!y φ(x, y)` verdadero en ℕ, que S¹₂ no deriva.** Es `s12_no_demuestra_factor` con su primera
hipótesis demostrada (`existe_formula_minFac`): solo queda la conjetura de que factorizar es difícil. -/
theorem s12_no_demuestra_factor_sin_formula (hdura : ¬ EsPolinomial Nat.minFac) :
    ∃ φ : L.Formula (Fin 2), EsSigma1 φ ∧ (∀ n m : ℕ, φ.Realize ![n, m] ↔ m = Nat.minFac n) ∧
      (∀ n : ℕ, ∃! m : ℕ, φ.Realize ![n, m]) ∧ ¬ DerivaS12 (cierre (existeUnico φ)) := by
  obtain ⟨φ, hφ, hgraf⟩ := existe_formula_minFac
  exact ⟨φ, hφ, hgraf, existeUnico_verdadero hgraf,
    s12_no_demuestra_factor hdura hφ fun n => (hgraf n _).2 rfl⟩

/- Mutantes probados (25 nov 2026, fuera del repositorio; cada uno es una copia del archivo con un cambio):

* `primo_de_prattOK`: quitar de `entradaOK` la condición `a^((p−1)/q) ≢ 1` (y de `entradaOK_iff`). La prueba se rompe
  donde la usa, y con el revisor mutado `prattOK [(9, 1, [2, 2, 2]), (2, 1, [])] = true` pasa por `decide`: el
  mutante certifica que 9 es primo. Es la condición que hace al criterio de Lucas un criterio.
* `minFac_de_revisaGrafo`: quitar `m ≤ q` de `revisaGrafo`. La corrección se rompe (acepta `n = 6, m = 3` con
  `L = [2, 3]`).
* `existe_certificado`: pedir `4 · 2^|C| ≤ p²` en vez de `2 · 2^|C| ≤ p²`. Falla en `p = 2` (un certificado de una
  entrada da 8 > 4) y en el paso inductivo: la cota de Pratt es justa en las hojas.
* `grafoMinFac_NP` y `primos_NP`: un tope lineal `63 (X + 2)` en vez de cuadrático. Las cuentas de largo no cierran:
  la cota `O(|p|²)` de Pratt no se puede bajar a lineal con este certificado.
* `existe_formula_minFac`: codificar `z = ⟨x, y⟩` sin el `+ 1`. Se rompe `realize_codigoPar` (mutante débil, de
  forma); el `+ 1` importa porque `numeroDe` nunca vale 0. -/

end Sagitta.Map.Acotada.Pratt
