import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Data.Nat.Digits.Lemmas
import Sagitta.Map.Goodstein
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime

/-!
# El laboratorio de Goodstein: el ordinal que baja, la terminación y el lenguaje

La propuesta de José (25 nov 2026): traer la fuerza ordinal al mundo finito con sucesiones que obliguen a subir
ordinales (ver las notas del proyecto) y la demo en Go de
`ejemplos/laboratorio-goodstein/`. Aquí va en Lean, sobre Mathlib y cslib-frontier. Mathlib no tiene Goodstein ni
base hereditaria; sí tiene `ONote` (la forma normal de Cantor debajo de `ε₀`, `Mathlib/SetTheory/Ordinal/Notation.lean`),
que se usa para mostrar los ordinales, y la buena fundación de `Ordinal`, que es la que hace el trabajo.

## Lo que se prueba

* **La base hereditaria** (`subir`, `aONote`, `ord`): `n = b^e·d + r` con `e = log_b n`, `1 ≤ d < b`, `r < b^e`;
  `subir b n` cambia `b` por `b + 1` en toda la escritura, y `aONote b n` la cambia por `ω` (una `ONote` computable;
  `ord b n` es su valor en `Ordinal`). La sucesión `gs m`: en el paso `k` la base sube de `k + 2` a `k + 3` y se resta 1.
  Los `#eval` del final dan `G(3) = 3, 3, 3, 2, 1, 0` con ordinales `ω + 1, ω, 3, 2, 1, 0`, y `G(4) = 4, 26, 41, 60, 83`
  con ordinales `ω^ω, ω²·2 + ω·2 + 2, …`, los mismos de la demo.
* **El ordinal baja** (`ordinal_baja`): mientras el término no sea 0, `ord (k+3) (gs m (k+1)) < ord (k+2) (gs m k)`.
  Sale de dos hechos: `ord b` es estrictamente creciente en `n` (`ord_strictMono`, por la cota de la cola
  `cola_acotada`), y subir la base no cambia el ordinal (`ord_subir`). Restar 1 lo baja.
* **Goodstein termina** (`goodstein_termina`): para todo `m` hay `k` con `gs m k = 0`, por inducción bien fundada
  sobre `Ordinal`. Con `goodstein_eq_gs` (la sucesión de `Sagitta/Map/Goodstein.lean`, escrita con `Nat.digits` y
  combustible, es la misma) queda demostrado el `TeoremaGoodstein` de ese archivo (`teoremaGoodstein`).
* **Las longitudes marcadas** (`Marcada`, `marca`): se corren `G(1), G(2), …` una detrás de otra; cada paso global
  cuesta los bits del término más uno, y un reloj (`reloj`) suma esos costos. Una longitud está marcada si el reloj
  vale eso justo cuando una sucesión llega a 0. Es una construcción al estilo de Hartmanis (1985) y de
  Kurtz, O'Donnell y Royer (1987), con el reloj en costo y no en pasos de Goodstein: con pasos de Goodstein la marca
  no sería polinomial, porque desde `G(5)` un solo paso escribe números de millones de bits. Las primeras marcas son
  `3, 12, 27` (los fines de `G(1)`, `G(2)`, `G(3)`).
* **Las marcas no se acaban si y solo si vale Goodstein** (`marcadas_infinitas_iff`); la equivalencia es elemental
  y la fuerza está toda de un lado. Con `goodstein_termina`, `marcadas_infinitas`.
* **El lenguaje** `satGoodstein = {φ | marca |encCNF φ| ∧ φ ∈ SAT}`: en las longitudes marcadas es SAT
  (`satGoodstein_en_marcada`), en las demás es vacío (`satGoodstein_fuera`). En general, SAT restringido a un
  conjunto de longitudes que se decide en tiempo polinomial está en la NP de cslib-frontier (`satEn_NP`, con el
  verificador de `SAT.mem_NP` y la prueba de longitud delante, `IsVerifier.guard`); así `satGoodstein_NP` da
  `satGoodstein ∈ NP encCNF` **bajo la hipótesis** `LongitudesPolinomiales marca`.

## Lo que no

* **Que `marca` sea polinomial no está probado.** La función `marca` de aquí es extensionalmente la correcta pero su
  cálculo es ingenuo (recalcula todo, y calcula términos enormes aunque el reloj ya se haya pasado). Una máquina que
  simule con el reloj y aborte en cuanto un término nuevo supere `n` bits decide la marca en tiempo polinomial en `n`;
  escribirla en el modelo de cslib (cintas, `ComputableInPolyTime` de `subir` con corte) es el trabajo que falta, y
  es caro. Por eso `L ∈ NP` queda condicionado a `LongitudesPolinomiales marca`, enunciado con precisión.
* **Cuánto pide la prueba.** La terminación usa solo la buena fundación de `Ordinal.{0}`, y los ordinales que aparecen
  son `ONote`, todos debajo de `ε₀`: bastaría la buena fundación de `ε₀`, que es la fuerza de PA más un poco
  (Gentzen). Lean está muy por encima: su teoría de tipos con universos tiene la fuerza de ZFC con una sucesión
  numerable de inaccesibles (Carneiro, 2019; Werner, 1997). Aquí la terminación de Goodstein es una inducción de
  diez líneas.

## La trampa

La fuerza viene del dispositivo, no de SAT. Lo que no se puede demostrar en PA es «las marcas no se acaban», que es
el teorema de Goodstein (`marcadas_infinitas_iff`) vestido de complejidad; SAT solo pone el disfraz. Probar en Lean
que PA no demuestra la terminación pediría formalizar PA, su demostrabilidad y el teorema de Kirby y Paris (1982),
y queda fuera de este archivo: aquí solo se ve que la prueba de la terminación usa un ordinal, no que lo necesite.
-/

open Ordinal ONote

namespace Sagitta.Map.Borde.Goodstein

/-! ## La base hereditaria -/

theorem pow_log_pos (b n : ℕ) : 0 < b ^ Nat.log b n := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [Nat.log_zero_left]
  · exact Nat.pow_pos hb

theorem resto_lt (b : ℕ) {n : ℕ} (h : n ≠ 0) : n % b ^ Nat.log b n < n :=
  lt_of_lt_of_le (Nat.mod_lt _ (pow_log_pos b n)) (Nat.pow_log_le_self b h)

/-- Cambia la base `b` por `b + 1` en la escritura hereditaria de `n`: si `n = b^e·d + r` con `e = log_b n`,
`1 ≤ d < b` y `r < b^e`, el resultado es `(b+1)^(subir e)·d + subir r`. -/
def subir (b : ℕ) (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 else
    (b + 1) ^ subir b (Nat.log b n) * (n / b ^ Nat.log b n) + subir b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b ‹_›
  · exact resto_lt b ‹_›

/-- La forma normal de Cantor de `n` en base `b`, con la base cambiada por `ω`, como notación de Mathlib. -/
def aONote (b : ℕ) (n : ℕ) : ONote :=
  if _h : n = 0 then 0 else
    oadd (aONote b (Nat.log b n)) (n / b ^ Nat.log b n).toPNat' (aONote b (n % b ^ Nat.log b n))
termination_by n
decreasing_by
  · exact Nat.log_lt_self b ‹_›
  · exact resto_lt b ‹_›

/-- El ordinal de `n` en base `b`: la base hereditaria con `b` cambiada por `ω`. -/
noncomputable def ord (b n : ℕ) : Ordinal.{0} := (aONote b n).repr

/-- La sucesión de Goodstein: en el paso `k` la base sube de `k + 2` a `k + 3` y se resta 1. -/
def gs (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => subir (k + 2) (gs m k) - 1

/-! ## Lo que se desenrolla -/

theorem digito_pos (b : ℕ) {n : ℕ} (h : n ≠ 0) : 0 < n / b ^ Nat.log b n :=
  Nat.div_pos (Nat.pow_log_le_self b h) (pow_log_pos b n)

theorem digito_lt {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : n / b ^ Nat.log b n < b := by
  rw [Nat.div_lt_iff_lt_mul (pow_log_pos b n), mul_comm, ← pow_succ]
  exact Nat.lt_pow_succ_log_self hb n

theorem subir_cero (b : ℕ) : subir b 0 = 0 := by rw [subir]; simp

theorem subir_eq (b : ℕ) {n : ℕ} (h : n ≠ 0) : subir b n =
    (b + 1) ^ subir b (Nat.log b n) * (n / b ^ Nat.log b n) + subir b (n % b ^ Nat.log b n) := by
  rw [subir]; simp [h]

theorem ord_cero (b : ℕ) : ord b 0 = 0 := by
  rw [ord, aONote]; simp

theorem ord_eq (b : ℕ) {n : ℕ} (h : n ≠ 0) : ord b n =
    ω ^ ord b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) + ord b (n % b ^ Nat.log b n) := by
  rw [ord, aONote]
  simp only [h, ↓reduceDIte]
  show ω ^ _ * _ + _ = _
  have hd : (((n / b ^ Nat.log b n).toPNat' : ℕ) : Ordinal) = ((n / b ^ Nat.log b n : ℕ) : Ordinal) := by
    simp [Nat.toPNat'_coe, digito_pos b h]
  rw [← hd]
  rfl

/-! ## Aritmética de ordinales que hace falta -/

theorem cola_lt {a c x : Ordinal} {d : ℕ} (hx : x < ω ^ a) (hac : a < c) : ω ^ a * d + x < ω ^ c :=
  calc ω ^ a * d + x < ω ^ a * d + ω ^ a := (add_lt_add_iff_left _).2 hx
    _ = ω ^ a * ((d + 1 : ℕ) : Ordinal) := by rw [Nat.cast_succ, mul_add_one]
    _ < ω ^ a * ω := mul_lt_mul_of_pos_left (natCast_lt_omega0 _) (opow_pos _ omega0_pos)
    _ = ω ^ (a + 1) := (opow_add_one _ _).symm
    _ ≤ ω ^ c := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hac)

theorem cabeza_le {a x : Ordinal} {d : ℕ} (hd : 1 ≤ d) : ω ^ a ≤ ω ^ a * d + x :=
  (Ordinal.le_mul_left _ (by exact_mod_cast hd)).trans le_self_add

theorem ord_pos (b : ℕ) {n : ℕ} (h : n ≠ 0) : 0 < ord b n := by
  rw [ord_eq b h]
  exact lt_of_lt_of_le (opow_pos _ omega0_pos) (cabeza_le (digito_pos b h))

/-! ## El ordinal es estrictamente creciente en `n` -/

/-- La cota de la cola: si `ord` es creciente hasta `k`, todo `r < b^k` tiene ordinal `< ω^(ord k)`. -/
theorem cola_acotada {b : ℕ} : ∀ k : ℕ, (∀ a c, a < c → c ≤ k → ord b a < ord b c) →
    ∀ r, r < b ^ k → ord b r < ω ^ ord b k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hmono r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [ord_cero]; exact opow_pos _ omega0_pos
    have hr0' : r ≠ 0 := hr0.ne'
    have he : Nat.log b r < k := Nat.log_lt_of_lt_pow hr0' hr
    rw [ord_eq b hr0']
    refine cola_lt ?_ (hmono _ _ he le_rfl)
    exact ih _ he (fun a c hac hc => hmono a c hac (hc.trans he.le)) _
      (Nat.mod_lt _ (pow_log_pos b r))

/-- **El ordinal de la base hereditaria es estrictamente creciente** en `n`, para `b ≥ 2`. -/
theorem ord_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (ord b) := by
  have key : ∀ m, ∀ n < m, ord b n < ord b m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hnm
      have hm : m ≠ 0 := (Nat.zero_le n).trans_lt hnm |>.ne'
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [ord_cero]; exact ord_pos b hm
      have hn : n ≠ 0 := hn0.ne'
      set e := Nat.log b m with he
      have hem : e < m := Nat.log_lt_self b hm
      have hmono : ∀ a c, a < c → c ≤ e → ord b a < ord b c :=
        fun a c hac hc => ih c (lt_of_le_of_lt hc hem) a hac
      have hcola := cola_acotada e hmono
      have hle : Nat.log b n ≤ e := Nat.log_mono_right hnm.le
      have hcabeza : ω ^ ord b e ≤ ord b m := by
        rw [ord_eq b hm]; exact cabeza_le (digito_pos b hm)
      rcases hle.lt_or_eq with hlt | heq
      · -- el exponente de `n` es menor: `n < b^e`
        have hnb : n < b ^ e :=
          lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by omega) n) (Nat.pow_le_pow_right (by omega) hlt)
        exact lt_of_lt_of_le (hcola n hnb) hcabeza
      · -- el mismo exponente: se compara el dígito y después la cola
        have hdle : n / b ^ e ≤ m / b ^ e := Nat.div_le_div_right hnm.le
        rw [ord_eq b hn, ord_eq b hm, heq]
        rcases hdle.lt_or_eq with hd | hd
        · calc ω ^ ord b e * ((n / b ^ e : ℕ) : Ordinal) + ord b (n % b ^ e)
              < ω ^ ord b e * ((n / b ^ e + 1 : ℕ) : Ordinal) := by
                rw [Nat.cast_succ, mul_add_one]
                exact (add_lt_add_iff_left _).2 (hcola _ (Nat.mod_lt _ (by rw [he]; exact pow_log_pos b m)))
            _ ≤ ω ^ ord b e * ((m / b ^ e : ℕ) : Ordinal) :=
                mul_le_mul_right (by exact_mod_cast hd) _
            _ ≤ _ := le_self_add
        · rw [hd, ← he]
          refine (add_lt_add_iff_left _).2 ?_
          have hb0 : 0 < b ^ e := by rw [he]; exact pow_log_pos b m
          have hrr : n % b ^ e < m % b ^ e := by
            have h1 := Nat.div_add_mod n (b ^ e)
            have h2 := Nat.div_add_mod m (b ^ e)
            rw [hd] at h1
            omega
          exact ih _ (lt_of_lt_of_le (Nat.mod_lt _ hb0) (by rw [he]; exact Nat.pow_log_le_self b hm)) _ hrr
  exact fun n m h => key m n h

theorem ord_inj {b : ℕ} (hb : 2 ≤ b) {n m : ℕ} : ord b n = ord b m ↔ n = m := (ord_strictMono hb).injective.eq_iff

theorem ord_eq_cero_iff {b : ℕ} (hb : 2 ≤ b) {n : ℕ} : ord b n = 0 ↔ n = 0 := by
  rw [← ord_cero b, ord_inj hb]

/-- La cota al revés: si el ordinal de `x` queda debajo de `ω^(ord K)`, entonces `x < b^K`. -/
theorem lt_pow_de_ord {b : ℕ} (hb : 2 ≤ b) {x K : ℕ} (h : ord b x < ω ^ ord b K) : x < b ^ K := by
  by_contra hx
  push Not at hx
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (Nat.pow_pos (by omega)) hx).ne'
  have hK : K ≤ Nat.log b x := Nat.le_log_of_pow_le (by omega) hx
  have h1 : ω ^ ord b K ≤ ω ^ ord b (Nat.log b x) :=
    opow_le_opow_right omega0_pos ((ord_strictMono hb).monotone hK)
  have h2 : ω ^ ord b (Nat.log b x) ≤ ord b x := by
    rw [ord_eq b hx0]; exact cabeza_le (digito_pos b hx0)
  exact absurd h (not_lt.2 (h1.trans h2))

/-- La forma normal se lee de cualquier escritura `c^E·d + R` con `1 ≤ d < c` y `R < c^E`. -/
theorem ord_desc {c E d R : ℕ} (hc : 2 ≤ c) (hd1 : 1 ≤ d) (hd : d < c) (hR : R < c ^ E) :
    ord c (c ^ E * d + R) = ω ^ ord c E * d + ord c R := by
  have hpos : 0 < c ^ E := Nat.pow_pos (by omega)
  have hx : c ^ E * d + R ≠ 0 := by positivity
  have hlog : Nat.log c (c ^ E * d + R) = E := by
    rw [Nat.log_eq_iff (Or.inr ⟨by omega, hx⟩)]
    constructor
    · exact le_add_right (Nat.le_mul_of_pos_right _ hd1)
    · calc c ^ E * d + R < c ^ E * d + c ^ E := by omega
        _ = c ^ E * (d + 1) := by ring
        _ ≤ c ^ E * c := Nat.mul_le_mul_left _ hd
        _ = c ^ (E + 1) := (pow_succ _ _).symm
  have hdiv : (c ^ E * d + R) / c ^ E = d := by
    rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hR, add_zero]
  have hmod : (c ^ E * d + R) % c ^ E = R := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hR]
  rw [ord_eq c hx, hlog, hdiv, hmod]

/-! ## Cambiar la base no cambia el ordinal -/

/-- **Subir la base conserva el ordinal**: `ord (b+1) (subir b n) = ord b n`. -/
theorem ord_subir {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : ord (b + 1) (subir b n) = ord b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [subir_cero, ord_cero, ord_cero]
    have hn : n ≠ 0 := hn0.ne'
    have he := ih _ (Nat.log_lt_self b hn)
    have hr := ih _ (resto_lt b hn)
    have hcola : subir b (n % b ^ Nat.log b n) < (b + 1) ^ subir b (Nat.log b n) := by
      apply lt_pow_de_ord (by omega)
      rw [hr, he]
      exact cola_acotada _ (fun a c hac _ => ord_strictMono hb hac) _
        (Nat.mod_lt _ (pow_log_pos b n))
    rw [subir_eq b hn, ord_desc (by omega) (digito_pos b hn) (by have := digito_lt hb n; omega) hcola,
      he, hr, ord_eq b hn]

/-- `subir` es estrictamente creciente: sale de que conserva el ordinal y el ordinal lo es. -/
theorem subir_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (subir b) := by
  intro n m h
  have := ord_strictMono hb h
  rw [← ord_subir hb n, ← ord_subir hb m] at this
  exact (ord_strictMono (b := b + 1) (by omega)).lt_iff_lt.1 this

theorem subir_ne_cero {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (h : n ≠ 0) : subir b n ≠ 0 := by
  intro h0
  have := ord_subir hb n
  rw [h0, ord_cero] at this
  exact (ord_pos b h).ne' this.symm

/-! ## El ordinal baja a lo largo de la sucesión -/

/-- El ordinal del término `k`: la base `k + 2` cambiada por `ω`. -/
noncomputable def ordinalDe (m k : ℕ) : Ordinal.{0} := ord (k + 2) (gs m k)

/-- **El ordinal baja en cada paso** mientras el término no sea 0. -/
theorem ordinal_baja {m k : ℕ} (h : gs m k ≠ 0) : ordinalDe m (k + 1) < ordinalDe m k := by
  have hb : 2 ≤ k + 2 := by omega
  have hs := subir_ne_cero hb h
  show ord (k + 2 + 1) (subir (k + 2) (gs m k) - 1) < ord (k + 2) (gs m k)
  rw [← ord_subir hb (gs m k)]
  exact ord_strictMono (by omega) (Nat.sub_lt (Nat.pos_of_ne_zero hs) one_pos)

/-- El término sube (o se queda) mientras el ordinal baja: la base nueva no achica nada. -/
theorem gs_cero_estable {m k : ℕ} (h : gs m k = 0) : gs m (k + 1) = 0 := by
  show subir (k + 2) (gs m k) - 1 = 0
  rw [h, subir_cero]

/-- **Teorema de Goodstein**: toda sucesión llega a 0. Por la buena fundación de los ordinales. -/
theorem goodstein_termina (m : ℕ) : ∃ k, gs m k = 0 := by
  suffices H : ∀ α : Ordinal.{0}, ∀ k, ordinalDe m k = α → ∃ K, gs m K = 0 from H _ 0 rfl
  intro α
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro k hk
    by_cases h : gs m k = 0
    · exact ⟨k, h⟩
    · exact ih _ (hk ▸ ordinal_baja h) (k + 1) rfl

/-! ## La relación con `Sagitta/Map/Goodstein.lean`

Esa definición (de otra sesión) escribe `n` con `Nat.digits` y suma dígito por dígito, con combustible. Aquí se
prueba que coincide con `subir` para `b ≥ 2`, así que su `TeoremaGoodstein` queda demostrado. -/

section Relacion

variable {b : ℕ}

/-- La suma de `subeBaseAux`: cada dígito `dᵢ` en la posición `i` (a partir de `k`) aporta `dᵢ·(b+1)^(f i)`. -/
def sumaDig (b : ℕ) (f : ℕ → ℕ) (l : List ℕ) (k : ℕ) : ℕ :=
  ((l.zipIdx k).map fun di => di.1 * (b + 1) ^ f di.2).sum

theorem foldl_suma (g : ℕ × ℕ → ℕ) : ∀ (l : List (ℕ × ℕ)) (acc : ℕ),
    l.foldl (fun acc di => acc + g di) acc = acc + (l.map g).sum
  | [], acc => by simp
  | x :: l, acc => by simp [foldl_suma g l, Nat.add_assoc]

theorem sumaDig_cons (f : ℕ → ℕ) (a : ℕ) (l : List ℕ) (k : ℕ) :
    sumaDig b f (a :: l) k = a * (b + 1) ^ f k + sumaDig b f l (k + 1) := by
  simp [sumaDig]

/-- La recursión por el dígito de abajo. -/
theorem sumaDig_digits (hb : 2 ≤ b) (f : ℕ → ℕ) (n k : ℕ) :
    sumaDig b f (Nat.digits b n) k = n % b * (b + 1) ^ f k + sumaDig b f (Nat.digits b (n / b)) (k + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sumaDig]
  · rw [Nat.digits_def' (by omega) hn, sumaDig_cons]

/-- La recursión por el dígito de arriba: `b^e·d + r` con `d < b` y `r < b^e`. -/
theorem sumaDig_cabeza (hb : 2 ≤ b) (f : ℕ → ℕ) {d : ℕ} (hd : d < b) :
    ∀ e k r, r < b ^ e → sumaDig b f (Nat.digits b (b ^ e * d + r)) k =
      d * (b + 1) ^ f (k + e) + sumaDig b f (Nat.digits b r) k
  | 0, k, r, hr => by
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    rw [sumaDig_digits hb, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.mod_eq_of_lt hd,
      Nat.div_eq_of_lt hd, Nat.add_zero]
    simp [sumaDig]
  | e + 1, k, r, hr => by
    have hb0 : 0 < b := by omega
    have hrb : r / b < b ^ e := by
      rw [Nat.div_lt_iff_lt_mul hb0, ← pow_succ]; exact hr
    have hn : b ^ (e + 1) * d + r = b * (b ^ e * d) + r := by ring
    rw [sumaDig_digits hb, hn, Nat.mul_add_mod, Nat.mul_add_div hb0, sumaDig_cabeza hb f hd e (k + 1) _ hrb,
      sumaDig_digits hb f r k]
    rw [show k + 1 + e = k + (e + 1) by omega]
    ring

/-- `subir` es la suma dígito por dígito de sí misma. -/
theorem subir_eq_sumaDig (hb : 2 ≤ b) (n : ℕ) : subir b n = sumaDig b (subir b) (Nat.digits b n) 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [subir_cero, sumaDig]
    have hn : n ≠ 0 := hn0.ne'
    have hsplit : n = b ^ Nat.log b n * (n / b ^ Nat.log b n) + n % b ^ Nat.log b n :=
      (Nat.div_add_mod n _).symm
    conv_rhs => rw [hsplit]
    rw [sumaDig_cabeza hb _ (digito_lt hb n) _ 0 _ (Nat.mod_lt _ (pow_log_pos b n)),
      ← ih _ (resto_lt b hn), subir_eq b hn, Nat.zero_add, Nat.mul_comm]

theorem sumaDig_congr {f g : ℕ → ℕ} {l : List ℕ} (h : ∀ i < l.length, f i = g i) :
    sumaDig b f l 0 = sumaDig b g l 0 := by
  unfold sumaDig
  congr 1
  refine List.map_congr_left fun di hdi => ?_
  rw [h di.2 (List.mem_zipIdx' hdi).1]

/-- Con combustible suficiente, `subeBaseAux` es `subir`. -/
theorem subeBaseAux_eq (hb : 2 ≤ b) : ∀ n c, n ≤ c → subeBaseAux b c n = subir b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · cases c <;> simp [subeBaseAux, subir_cero]
    obtain ⟨comb, rfl⟩ : ∃ comb, c = comb + 1 := ⟨c - 1, by omega⟩
    have hlen : (Nat.digits b n).length = Nat.log b n + 1 := Nat.length_digits b n (by omega) hn0.ne'
    have hlog : Nat.log b n < n := Nat.log_lt_self b hn0.ne'
    rw [subeBaseAux, foldl_suma, Nat.zero_add, subir_eq_sumaDig hb n]
    exact sumaDig_congr fun i hi => ih i (by omega) comb (by omega)

theorem subeBase_eq (hb : 2 ≤ b) (n : ℕ) : subeBase b n = subir b n := subeBaseAux_eq hb n n le_rfl

/-- La sucesión de `Sagitta/Map/Goodstein.lean` es la de aquí. -/
theorem goodstein_eq_gs (m : ℕ) : ∀ k, goodstein m k = gs m k
  | 0 => rfl
  | k + 1 => by
    show subeBase (k + 2) (goodstein m k) - 1 = subir (k + 2) (gs m k) - 1
    rw [goodstein_eq_gs m k, subeBase_eq (by omega)]

/-- **El `TeoremaGoodstein` de `Sagitta/Map/Goodstein.lean`, demostrado.** -/
theorem teoremaGoodstein : TeoremaGoodstein := fun m => by
  obtain ⟨k, hk⟩ := goodstein_termina m
  exact ⟨k, by rw [goodstein_eq_gs]; exact hk⟩

end Relacion

/-! ## Las longitudes marcadas

Se corren `G(1), G(2), …` una detrás de otra. El estado global es el par `(j, k)`: se está en el paso `k` de
`G(j)`. Cada paso global cuesta lo que mide el término en bits, más uno, y el reloj suma esos costos. Una longitud
`n` está **marcada** si el reloj vale `n` justo en un paso donde una sucesión llega a 0. -/

/-- Un paso de la corrida global: si `G(j)` llegó a 0 se pasa a `G(j+1)`; si no, se da un paso de `G(j)`. -/
def pasoGlobal (s : ℕ × ℕ) : ℕ × ℕ := if gs s.1 s.2 = 0 then (s.1 + 1, 0) else (s.1, s.2 + 1)

/-- El estado de la corrida global en el paso `t`, desde `G(1)`. -/
def estado (t : ℕ) : ℕ × ℕ := pasoGlobal^[t] (1, 0)

/-- El término de Goodstein que se tiene en el paso global `t`. -/
def termino (t : ℕ) : ℕ := gs (estado t).1 (estado t).2

/-- Lo que cuesta el paso global `t`: los bits del término, más uno. -/
def peso (t : ℕ) : ℕ := Nat.size (termino t) + 1

/-- El reloj: lo gastado hasta el paso `t` inclusive. -/
def reloj (t : ℕ) : ℕ := ∑ s ∈ Finset.range (t + 1), peso s

/-- Una longitud está marcada si el reloj pasa por ella en un paso donde una sucesión termina. -/
def Marcada (n : ℕ) : Prop := ∃ t, reloj t = n ∧ termino t = 0

/-- La marca, como función booleana: basta mirar los pasos `t < n`, porque el reloj gasta al menos uno por paso. -/
def marca (n : ℕ) : Bool := (List.range n).any fun t => reloj t == n && termino t == 0

theorem estado_succ (t : ℕ) : estado (t + 1) = pasoGlobal (estado t) :=
  Function.iterate_succ_apply' _ _ _

theorem lt_reloj (t : ℕ) : t < reloj t := by
  unfold reloj
  calc t < t + 1 := Nat.lt_succ_self t
    _ = ∑ _s ∈ Finset.range (t + 1), 1 := by simp
    _ ≤ ∑ s ∈ Finset.range (t + 1), peso s := Finset.sum_le_sum fun s _ => Nat.le_add_left 1 _

theorem reloj_strictMono : StrictMono reloj := by
  refine strictMono_nat_of_lt_succ fun t => ?_
  unfold reloj
  rw [Finset.sum_range_succ _ (t + 1)]
  exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

theorem marca_iff (n : ℕ) : marca n = true ↔ Marcada n := by
  simp only [marca, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨t, -, h1, h2⟩; exact ⟨t, h1, h2⟩
  · rintro ⟨t, h1, h2⟩; exact ⟨t, h1 ▸ lt_reloj t, h1, h2⟩

theorem gs_cero_desde {m K : ℕ} (h : gs m K = 0) : ∀ i, gs m (K + i) = 0
  | 0 => h
  | i + 1 => gs_cero_estable (gs_cero_desde h i)

/-- Mientras `G(j)` no llega a 0, la corrida global avanza dentro de `G(j)`. -/
theorem estado_avanza {t j k : ℕ} (h : estado t = (j, k)) :
    ∀ i, (∀ i' < i, gs j (k + i') ≠ 0) → estado (t + i) = (j, k + i)
  | 0, _ => h
  | i + 1, hi => by
    rw [← Nat.add_assoc, estado_succ, estado_avanza h i (fun i' hi' => hi i' (by omega)), pasoGlobal]
    simp [hi i (by omega)]
    omega

/-- Si toda sucesión termina, después de cualquier paso global hay uno donde una sucesión termina. -/
theorem existe_fin_de (hG : ∀ m, ∃ k, gs m k = 0) (t : ℕ) : ∃ t' ≥ t, termino t' = 0 := by
  obtain ⟨⟨j, k⟩, h⟩ : ∃ s, estado t = s := ⟨_, rfl⟩
  have hex : ∃ i, gs j (k + i) = 0 := by
    obtain ⟨K, hK⟩ := hG j
    refine ⟨K, ?_⟩
    have := gs_cero_desde hK k
    rwa [Nat.add_comm] at this
  classical
  refine ⟨t + Nat.find hex, by omega, ?_⟩
  have ha := estado_avanza h (Nat.find hex) (fun i' hi' => Nat.find_min hex hi')
  unfold termino
  rw [ha]
  exact Nat.find_spec hex

/-- Los pasos globales donde una sucesión termina. -/
def finales : Set ℕ := {t | termino t = 0}

theorem marcadas_eq : {n | Marcada n} = reloj '' finales := by
  ext n; simp only [Set.mem_ofPred_eq, Set.mem_image, Marcada, finales]
  exact ⟨fun ⟨t, h1, h2⟩ => ⟨t, h2, h1⟩, fun ⟨t, h2, h1⟩ => ⟨t, h1, h2⟩⟩

/-- La sucesión que corre en el paso `t` es la `1 +` cuántas terminaron antes. -/
theorem estado_fst (t : ℕ) :
    (estado t).1 = 1 + ((Finset.range t).filter fun s => termino s = 0).card := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [estado_succ, Finset.range_add_one, Finset.filter_insert]
    unfold pasoGlobal
    by_cases h : termino t = 0
    · have h' : gs (estado t).1 (estado t).2 = 0 := h
      simp only [h', ite_true, h]
      rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · have h' : gs (estado t).1 (estado t).2 ≠ 0 := h
      simp only [h', ite_false, h]
      exact ih

/-- Toda sucesión que ya quedó atrás en la corrida global terminó. -/
theorem atras_termina (t : ℕ) : ∀ j, j < (estado t).1 → ∃ K, gs j K = 0 := by
  induction t with
  | zero => intro j hj; exact ⟨0, by simp [estado] at hj; subst hj; rfl⟩
  | succ t ih =>
    intro j hj
    rw [estado_succ] at hj
    unfold pasoGlobal at hj
    split_ifs at hj with h
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih j hj
      · exact ⟨_, h⟩
    · exact ih j hj

/-- **Las marcas no se acaban si y solo si vale Goodstein** (para la `gs` de aquí). La equivalencia misma es
elemental; la fuerza está toda en el lado derecho. -/
theorem marcadas_infinitas_iff : {n | Marcada n}.Infinite ↔ ∀ m, ∃ k, gs m k = 0 := by
  constructor
  · intro hinf m
    have hZ : finales.Infinite := fun hfin => hinf (marcadas_eq ▸ hfin.image reloj)
    obtain ⟨S, hS, hcard⟩ := hZ.exists_subset_card_eq m
    classical
    let t := S.sup id + 1
    have hsub : S ⊆ (Finset.range t).filter fun s => termino s = 0 := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hs), hS hs⟩
    have hle := Finset.card_le_card hsub
    exact atras_termina t m (by rw [estado_fst]; omega)
  · intro hG
    refine Set.infinite_of_forall_exists_gt fun a => ?_
    obtain ⟨t, ht, h0⟩ := existe_fin_de hG a
    exact ⟨reloj t, ⟨t, rfl, h0⟩, lt_of_le_of_lt ht (lt_reloj t)⟩

/-- **Las marcas no se acaban.** Es el teorema de Goodstein vestido de complejidad: la fuerza viene de aquí. -/
theorem marcadas_infinitas : {n | Marcada n}.Infinite :=
  marcadas_infinitas_iff.2 goodstein_termina

/-! ## El lenguaje: SAT en las longitudes de Goodstein -/

section Lenguaje

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- **SAT en un conjunto de longitudes** dado por una prueba booleana `c`: las CNF satisfacibles cuya codificación
tiene una longitud que pasa la prueba. -/
def satEn (c : ℕ → Bool) : Set (CNF ℕ) := {φ | c (encCNF φ).length = true ∧ φ ∈ SAT}

/-- **SAT en las longitudes de Goodstein.** -/
def satGoodstein : Set (CNF ℕ) := satEn marca

/-- Que la prueba de longitudes sea polinomial: leer la entrada y decidir si su longitud pasa, en tiempo polinomial
en esa longitud. -/
def LongitudesPolinomiales (c : ℕ → Bool) : Prop :=
  ComputableInPolyTime (fun φ : CNF ℕ => c (encCNF φ).length) encCNF encBool

/-- **SAT en cualquier conjunto de longitudes polinomialmente decidible está en NP.** El verificador es el de SAT
de cslib-frontier, con la prueba de longitud delante (`IsVerifier.guard`). -/
theorem satEn_NP {c : ℕ → Bool} (hc : LongitudesPolinomiales c) : satEn c ∈ NP encCNF := by
  obtain ⟨p, V, hV, hVer⟩ := SAT.mem_NP
  refine ⟨p, fun x => (fun φ : CNF ℕ => c (encCNF φ).length) x.1 && V x, ?_, hVer.guard⟩
  exact ComputableInPolyTime.bool_and' (hc.comp (ComputableInPolyTime.fst _ _)) hV

/-- **`L ∈ NP`**, condicionado a que la marca sea polinomial en la longitud. Es lo que falta probar en el modelo de
máquinas de cslib: ver `MarcaPolinomial`. -/
theorem satGoodstein_NP (h : LongitudesPolinomiales marca) : satGoodstein ∈ NP encCNF :=
  satEn_NP h

/-- En las longitudes marcadas, `L` es SAT. -/
theorem satGoodstein_en_marcada {φ : CNF ℕ} (h : Marcada (encCNF φ).length) :
    φ ∈ satGoodstein ↔ φ ∈ SAT := by
  simp only [satGoodstein, satEn, Set.mem_ofPred_eq, (marca_iff _).2 h, true_and]

/-- En las demás longitudes, `L` es vacío. -/
theorem satGoodstein_fuera {φ : CNF ℕ} (h : ¬ Marcada (encCNF φ).length) : φ ∉ satGoodstein := by
  simp only [satGoodstein, satEn, Set.mem_ofPred_eq, not_and]
  intro hm
  exact absurd ((marca_iff _).1 hm) h

end Lenguaje

/-! ## Los ejemplos, por cálculo

`G(3)` completo, con su ordinal en cada paso (`ω^…` es la notación de Mathlib): el número no baja al principio,
el ordinal sí. `G(4)` en sus primeros pasos sube (`4, 26, 41, 60, 83`) y el ordinal baja desde `ω^ω`. -/

-- `G(3)`: `[3, 3, 3, 2, 1, 0]`.
#eval (List.range 6).map (gs 3)
-- Sus ordinales.
#eval (List.range 6).map fun k => ONote.toString (aONote (k + 2) (gs 3 k))
#eval (List.range 5).map (gs 4)
#eval (List.range 5).map fun k => ONote.toString (aONote (k + 2) (gs 4 k))
-- La corrida global en sus primeros pasos: `((j, k), término, reloj)`.
#eval (List.range 12).map fun t => (estado t, termino t, reloj t)
-- Las primeras longitudes marcadas: los fines de `G(1)`, `G(2)` y `G(3)`. `G(4)` dura del orden de `3·2^402653211`
-- pasos, así que la cuarta marca está más allá de todo cálculo.
#eval (List.range 40).filter fun n => marca n

#guard (List.range 6).map (gs 3) = [3, 3, 3, 2, 1, 0]
#guard (List.range 5).map (gs 4) = (List.range 5).map (goodstein 4)
#guard (List.range 40).filter (fun n => marca n) = [3, 12, 27]

end Sagitta.Map.Borde.Goodstein
