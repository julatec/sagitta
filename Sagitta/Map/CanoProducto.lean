import Sagitta.Map.PlanoCaja
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# El caño y el producto: la caja estática sin el factor `2^s`, cuando cada corrida lee solo su subárbol

Sobre `PlanoCaja` (la caja estática, `cota_caja_estatica`), con las mismas definiciones: `Responde`, `Lee`,
`hayDebajo`, `fijarCaja`.

## La pregunta

`PlanoCaja` probó `(M − s) · L ≤ 2^s · M · t` para `M` subárboles de `L` hojas, una caja de `s` bits que no conoce la
consulta y una corrida de a lo sumo `t` lecturas (de la caja o de las hojas). José conjeturó la forma producto
`s ≥ M · (1 − t/L)`: «el caño se achica y la demora crece en proporción».

## Lo que se decidió antes de probar (fuera de Lean)

Se buscó un contraejemplo a la forma producto con un resolvedor SAT (CaDiCaL, el que trae la cadena de Lean) sobre casos
chicos: la caja como función arbitraria de `f`, las corridas como árboles completos de profundidad `t` sobre los bits de
la caja y las hojas, con lecturas cruzadas permitidas. **No hay contraejemplo**: en todos los casos probados con `s < M`
la profundidad mínima es exactamente `t = L`, más fuerte que la conjetura:
`(M, L, s) = (2, 2, 1), (2, 3, 1), (2, 4, 1), (2, 5, 1), (3, 2, 2), (3, 3, 1), (3, 3, 2), (3, 4, 2), (4, 2, 3), (4, 3, 3)`
dan insatisfacible con `t = L − 1`. Eso es evidencia, **no está verificado en Lean**, y los casos son chicos (con `L` chico
leer un bit de la caja pesa tanto como una hoja).

Lo que sí mostró el SAT: si leer la caja fuera **gratis** (la corrida conoce el contenido entero y solo paga hojas), las
lecturas cruzadas ayudan de verdad. Con `M = 2`, `L = 3` y **tres** contenidos de caja, dos lecturas de hojas alcanzan, y
una corrida usa una hoja del **otro** subárbol como dato («en este contenido, si `b₁ = 0`, hay hoja buena en `b` si y
solo si `a₂ = 1`»). Las clases de la caja no son productos, como había dicho el autor anterior. Por eso aquí la forma
producto se prueba **en el modelo restringido**.

## Qué se prueba

* **El modelo restringido** (`Propia`): la corrida de la consulta `q` lee bits de la caja y hojas **de su propio
  subárbol** `q`, nunca de otro. La caja sigue siendo cualquier función de `f` y no conoce `q`; las lecturas de la caja
  se cuentan como en `PlanoCaja`.
* **La cota, sin el factor `2^s`** (`cota_propia`), en ℕ:

      (2L − t)^M ≤ 2^s · L^M        (con `L − t` truncado: `(L − t + L)^M`)

  o sea `s ≥ M · log₂(2 − t/L)`. La prueba es un conteo con pesos: se miran solo las funciones con a lo sumo un `1` por
  subárbol (`entrada`), con peso `L − t` el subárbol vacío y `1` cada posición del `1`. El peso total es `(2L − t)^M`. Con
  el contenido `c` de la caja fijo, la corrida restringida es un árbol sobre su subárbol solo, así que la clase de `c`
  cabe en un **producto** de conjuntos buenos por subárbol (`clase_en_producto`), y cada conjunto bueno pesa a lo sumo
  `L` (`peso_buenas_le`): si contiene al vacío, la corrida con `f = 0` deja sin leer `L − t` posiciones y ninguna de
  ellas puede estar. Sumando sobre los `2^s` contenidos sale la cota.
* **La forma producto, como corolario** (`forma_producto`, en ℝ, y `forma_producto_nat`, `M · (L − t) ≤ s · L`, en ℕ):
  porque `log₂(2 − x) ≥ 1 − x` en `[0, 1]` (concavidad del logaritmo, `log_uno_mas_ge`). Es decir: **la conjetura de José
  vale en el modelo restringido, y con margen**: `log₂(2 − t/L)` está por encima de `1 − t/L` salvo en los extremos.
* **Mejora a `cota_caja_estatica` para `0 < s ≤ M`** (en `s = 0` coinciden; para `s > M` las dos son vacías). Ojo: la vieja
  vale en el modelo general y la nueva solo en el restringido. Cuenta a mano, no formalizada en general:
  despejando `t`, la nueva da `t ≥ L · (2 − 2^(s/M))` y la vieja `t ≥ L · (1 − s/M) / 2^s`, y
  `2 − 2^(s/M) ≥ 1 − s/M ≥ (1 − s/M)/2^s`.
  Control concreto (`medio_mejora`): con `M = 4`, `L = 16`, `t = 8`, la cota nueva obliga `s ≥ 3`; la de `PlanoCaja`
  no excluye `s = 1` (`medio_plano_no_excluye`); la forma producto da `s ≥ 2`.

## Controles

* Los dos extremos de `PlanoCaja` son corridas propias (`guardar_los_or_propia`, `no_guardar_nada_propia`), así que la
  hipótesis no es vacía.
* **`s = 0` obliga `t ≥ L`** (`propia_sin_caja`), y `no_guardar_nada` lo alcanza: ahí la cota vale con **igualdad**
  (`no_guardar_nada_iguala`).
* **`t = 1` obliga `s ≥ M`** en el control concreto `M = 3`, `L = 16` (`una_lectura_propia`), alcanzado por
  `guardar_los_or`. En general `t = 1` da `s ≥ M · log₂(2 − 1/L)`, o sea `s ≥ M` cuando `L` es grande frente a `M`; `guardar_los_or` alcanza `s = M`.

## Lo que NO se prueba

* **El modelo general, con lecturas cruzadas.** La cota `(2L − t)^M ≤ 2^s · L^M` queda sin probar cuando una corrida puede
  leer hojas de otros subárboles: la prueba usa que la clase de cada contenido de caja es un producto, y con lecturas
  cruzadas no lo es. El SAT no encontró contraejemplo, ni a esta cota ni a la forma producto, pero es evidencia chica.
  En el modelo general sigue valiendo solo `cota_caja_estatica`, con el factor `2^s`.
* **Que la cota sea justa en el medio.** Con la caja gratis (no el modelo de aquí) un código de cubrimiento sobre las
  posiciones que no lee cada corrida da `s ≈ M · log₂(L/(L−1))` con `t = L − 1`, del mismo orden que la cota; con la
  caja contada habría que pagar la lectura de esos bits. No se construye ni se prueba nada de eso.
* Sigue siendo caja negra (relativiza) y no uniforme (la caja es un consejo); no toca P contra NP.
* Contexto, **de memoria y sin verificar** salvo lo marcado: estructuras de datos sucintas y sistemáticas en el modelo de
  sondeo de bits; A. Gál y P. B. Miltersen, «The cell probe complexity of succinct data structures», *Theoretical
  Computer Science* 379(3):405–417, 2007 (verificado, doi 10.1016/j.tcs.2007.02.047); M. Pătrașcu, «Succincter»
  (FOCS 2008, de memoria). Nada de eso se usa.
-/

namespace Sagitta.Map.Tiempo.CanoProducto

open Pregunta
open Sagitta.Map.Tiempo.PlanoCaja

section Propia

variable {ι η : Type}

/-- **Corrida propia**: la corrida de la consulta `q` solo lee hojas del subárbol `q` (y bits de la caja). -/
def Propia {β : Type} (R : ι → Pregunta (β ⊕ (ι × η))) : Prop :=
  ∀ q g p, Sum.inr p ∈ vistos (R q) g → p.1 = q

/-- **Con la caja fija, una corrida propia solo depende de su subárbol.** -/
theorem corre_propia {s : ℕ} {R : ι → Pregunta (Fin s ⊕ (ι × η))} (hP : Propia R) (c : Fin s → Bool) (q : ι)
    {f f' : ι × η → Bool} (h : ∀ y, f (q, y) = f' (q, y)) :
    corre (fijarCaja c (R q)) f = corre (fijarCaja c (R q)) f' := by
  rw [corre_fijarCaja, corre_fijarCaja]
  apply corre_congr
  rintro (j | ⟨a, y⟩) hi
  · rfl
  · have ha : a = q := hP q _ _ hi
    subst ha
    simpa using h y

/-- **La entrada de una elección**: a lo sumo un `1` por subárbol; `φ q = some y` pone el `1` en `(q, y)`, `none` deja
el subárbol vacío. -/
def entrada [DecidableEq η] (φ : ι → Option η) : ι × η → Bool := fun i => decide (φ i.1 = some i.2)

/-- **La entrada de un solo subárbol**: el subárbol `q` con `o`, todo lo demás en `0`. -/
def enBloque [DecidableEq ι] [DecidableEq η] (q : ι) (o : Option η) : ι × η → Bool :=
  fun i => decide (i.1 = q ∧ o = some i.2)

theorem hayDebajo_entrada [Fintype η] [DecidableEq η] (φ : ι → Option η) (q : ι) :
    hayDebajo (entrada φ) q = (φ q).isSome := by
  unfold hayDebajo entrada
  cases h : φ q <;> simp [h]

/-- **El pesoHueco** de lo que hay en un subárbol: `L − t` si está vacío, `1` por cada posición del `1`. -/
def pesoHueco (L t : ℕ) : Option η → ℕ
  | none => L - t
  | some _ => 1

/-- **Los contenidos buenos de un subárbol** para el árbol `P`: aquellos con los que `P` responde bien. -/
noncomputable def buenas [Fintype η] [DecidableEq ι] [DecidableEq η] (P : Pregunta (ι × η)) (q : ι) :
    Finset (Option η) :=
  Finset.univ.filter fun o => corre P (enBloque q o) = o.isSome

/-- **Un subárbol bueno pesa a lo sumo `L`.** Si el árbol (de a lo sumo `t` lecturas) responde bien con el subárbol
vacío, con `f = 0` deja sin leer las posiciones que no mira, y con el `1` en una de ellas respondería mal: solo caben
las que mira, a lo sumo `t`. -/
theorem peso_buenas_le [Fintype η] [DecidableEq ι] [DecidableEq η] (P : Pregunta (ι × η)) (q : ι) {t : ℕ}
    (hP : costo P (fun _ => false) ≤ t) :
    ∑ o ∈ buenas P q, pesoHueco (Fintype.card η) t o ≤ Fintype.card η := by
  classical
  let K : Finset η := Finset.univ.filter fun y => corre P (enBloque q (some y)) = true
  have hK : K.card ≤ Fintype.card η := by
    simpa using Finset.card_le_univ K
  have hsum : ∑ o ∈ buenas P q, pesoHueco (Fintype.card η) t o =
      (if corre P (enBloque q none) = false then Fintype.card η - t else 0) + K.card := by
    rw [buenas, Finset.sum_filter, Fintype.sum_option]
    congr 1
    · simp [pesoHueco]
      rfl
  rw [hsum]
  split
  · rename_i h0
    have h0' : corre P (fun _ => false) = false := by
      have : enBloque (η := η) q none = fun _ => false := by
        funext i; simp [enBloque]
      rwa [this] at h0
    have hsub : K.image (fun y => (q, y)) ⊆ (vistos P (fun _ => false)).toFinset := by
      intro i hi
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hi
      rw [List.mem_toFinset]
      by_contra hv
      have hy' : corre P (enBloque q (some y)) = true := (Finset.mem_filter.1 hy).2
      have e := corre_congr P (fun _ => false) (enBloque q (some y)) fun i hi => by
        have hne : i ≠ (q, y) := fun e => hv (e ▸ hi)
        symm
        unfold enBloque
        rw [decide_eq_false_iff_not]
        rintro ⟨h1, h2⟩
        apply hne
        rw [Option.some.injEq] at h2
        exact Prod.ext h1 h2.symm
      rw [h0', hy'] at e
      exact Bool.false_ne_true e
    have hc := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)] at hc
    have : K.card ≤ t := hc.trans hP
    omega
  · omega

variable [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η]

omit [Fintype ι] in
/-- **La clase de un contenido de caja cabe en un producto.** Si la caja vale `c` en la entrada de `φ`, cada `φ q` es un
contenido bueno para la corrida `q` con la caja fija en `c`. -/
theorem clase_en_producto {s : ℕ} {caja : (ι × η → Bool) → (Fin s → Bool)} {R : ι → Pregunta (Fin s ⊕ (ι × η))}
    (hR : Responde caja R) (hP : Propia R) {c : Fin s → Bool} {φ : ι → Option η} (hc : caja (entrada φ) = c) (q : ι) :
    φ q ∈ buenas (fijarCaja c (R q)) q := by
  unfold buenas
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hloc : corre (fijarCaja c (R q)) (enBloque q (φ q)) = corre (fijarCaja c (R q)) (entrada φ) :=
    corre_propia hP c q fun y => by simp [enBloque, entrada]
  rw [hloc, corre_fijarCaja, ← hc, hR, hayDebajo_entrada]

omit [DecidableEq ι] [DecidableEq η] in
/-- **La cota de la caja estática con corridas propias**, sin el factor `2^s`:

`(L − t + L)^M ≤ 2^s · L^M`,

con `M = |ι|` subárboles de `L = |η|` hojas, una caja de `s` bits que es cualquier función de `f` y no conoce la
consulta, y corridas de a lo sumo `t` lecturas (de la caja o de su subárbol). -/
theorem cota_propia {s t : ℕ} (caja : (ι × η → Bool) → (Fin s → Bool)) (R : ι → Pregunta (Fin s ⊕ (ι × η)))
    (hR : Responde caja R) (ht : Lee R t) (hP : Propia R) :
    (Fintype.card η - t + Fintype.card η) ^ Fintype.card ι ≤ 2 ^ s * Fintype.card η ^ Fintype.card ι := by
  classical
  set L := Fintype.card η
  let W : (ι → Option η) → ℕ := fun φ => ∏ q, pesoHueco L t (φ q)
  have htot : ∑ φ : ι → Option η, W φ = (L - t + L) ^ Fintype.card ι := by
    have h1 : ∑ φ : ι → Option η, W φ = ∏ _q : ι, ∑ o : Option η, pesoHueco L t o :=
      (Fintype.prod_sum fun (_ : ι) (o : Option η) => pesoHueco L t o).symm
    rw [h1, Finset.prod_const, Finset.card_univ, Fintype.sum_option]
    simp [pesoHueco, L]
  have hfib : ∀ c : Fin s → Bool,
      ∑ φ ∈ Finset.univ.filter (fun φ : ι → Option η => caja (entrada φ) = c), W φ ≤ L ^ Fintype.card ι := by
    intro c
    calc _ ≤ ∑ φ ∈ Fintype.piFinset (fun q => buenas (fijarCaja c (R q)) q), W φ := by
          apply Finset.sum_le_sum_of_subset
          intro φ hφ
          rw [Fintype.mem_piFinset]
          exact fun q => clase_en_producto hR hP (Finset.mem_filter.1 hφ).2 q
      _ = ∏ q, ∑ o ∈ buenas (fijarCaja c (R q)) q, pesoHueco L t o :=
          (Finset.prod_univ_sum (fun q => buenas (fijarCaja c (R q)) q) fun _ o => pesoHueco L t o).symm
      _ ≤ ∏ _q : ι, L := Finset.prod_le_prod fun q _ =>
          peso_buenas_le _ q ((costo_fijarCaja_le c _ (R q)).trans (ht q _))
      _ = L ^ Fintype.card ι := by simp
  calc (L - t + L) ^ Fintype.card ι = ∑ φ : ι → Option η, W φ := htot.symm
    _ = ∑ c : Fin s → Bool, ∑ φ ∈ Finset.univ.filter (fun φ : ι → Option η => caja (entrada φ) = c), W φ :=
        (Finset.sum_fiberwise Finset.univ (fun φ => caja (entrada φ)) W).symm
    _ ≤ ∑ _c : Fin s → Bool, L ^ Fintype.card ι := Finset.sum_le_sum fun c _ => hfib c
    _ = 2 ^ s * L ^ Fintype.card ι := by simp

/-! ## La forma producto, como corolario -/

/-- **`log(1 + x) ≥ x · log 2` en `[0, 1]`**: concavidad del logaritmo entre `1` y `2`. Equivale a `log₂(2 − y) ≥ 1 − y`. -/
theorem log_uno_mas_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * Real.log 2 ≤ Real.log (1 + x) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (one_pos : (0 : ℝ) < 1))
    (Set.mem_Ioi.2 (two_pos : (0 : ℝ) < 2)) (sub_nonneg.2 h1) h0 (sub_add_cancel 1 x)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hc
  have e : (1 - x) + x * 2 = 1 + x := by ring
  rwa [e] at hc

omit [DecidableEq ι] [DecidableEq η] in
/-- **La forma producto en el modelo restringido**: `s ≥ M · (1 − t/L)`. La conjetura de José, con corridas propias. -/
theorem forma_producto {s t : ℕ} (caja : (ι × η → Bool) → (Fin s → Bool)) (R : ι → Pregunta (Fin s ⊕ (ι × η)))
    (hR : Responde caja R) (ht : Lee R t) (hP : Propia R) (htL : t ≤ Fintype.card η) (hL : 0 < Fintype.card η) :
    (Fintype.card ι : ℝ) * (1 - t / Fintype.card η) ≤ s := by
  have h := cota_propia caja R hR ht hP
  set L := Fintype.card η
  set M := Fintype.card ι
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hcast : ((L - t + L : ℕ) : ℝ) = 2 * L - t := by
    rw [Nat.cast_add, Nat.cast_sub htL]; ring
  have hR' : ((2 * L - t : ℝ)) ^ M ≤ 2 ^ s * (L : ℝ) ^ M := by
    rw [← hcast]; exact_mod_cast h
  set x : ℝ := 1 - t / L with hx
  have htLr : (t : ℝ) ≤ L := by exact_mod_cast htL
  have hx0 : 0 ≤ x := by rw [hx, sub_nonneg, div_le_one hLr]; exact htLr
  have hx1 : x ≤ 1 := by
    rw [hx]; have : (0 : ℝ) ≤ t / L := div_nonneg (Nat.cast_nonneg _) hLr.le
    linarith
  have hbase : (2 * L - t : ℝ) = (1 + x) * L := by
    rw [hx]; field_simp; ring
  rw [hbase, mul_pow] at hR'
  have hLM : (0 : ℝ) < (L : ℝ) ^ M := pow_pos hLr M
  have hpow : (1 + x) ^ M ≤ (2 : ℝ) ^ s := le_of_mul_le_mul_right hR' hLM
  have hlog := Real.log_le_log (pow_pos (by linarith) M) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmx := log_uno_mas_ge hx0 hx1
  have : (M : ℝ) * x * Real.log 2 ≤ s * Real.log 2 := by
    calc (M : ℝ) * x * Real.log 2 = M * (x * Real.log 2) := by ring
      _ ≤ M * Real.log (1 + x) := mul_le_mul_of_nonneg_left hmx (Nat.cast_nonneg _)
      _ ≤ s * Real.log 2 := hlog
  exact le_of_mul_le_mul_right this hl2

omit [DecidableEq ι] [DecidableEq η] in
/-- **La forma producto en ℕ**: `M · (L − t) ≤ s · L`. -/
theorem forma_producto_nat {s t : ℕ} (caja : (ι × η → Bool) → (Fin s → Bool)) (R : ι → Pregunta (Fin s ⊕ (ι × η)))
    (hR : Responde caja R) (ht : Lee R t) (hP : Propia R) :
    Fintype.card ι * (Fintype.card η - t) ≤ s * Fintype.card η := by
  rcases Nat.lt_or_ge (Fintype.card η) t with htL | htL
  · rw [Nat.sub_eq_zero_of_le htL.le, mul_zero]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos (Fintype.card η) with hL | hL
  · rw [hL]; simp
  have h := forma_producto caja R hR ht hP htL hL
  have hLr : (0 : ℝ) < Fintype.card η := by exact_mod_cast hL
  have h' : (Fintype.card ι : ℝ) * ((Fintype.card η : ℝ) - t) ≤ s * Fintype.card η := by
    have e : (Fintype.card ι : ℝ) * ((Fintype.card η : ℝ) - t) =
        (Fintype.card ι : ℝ) * (1 - t / Fintype.card η) * Fintype.card η := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h hLr.le
  rw [← Nat.cast_sub htL] at h'
  exact_mod_cast h'

/-! ## Controles -/

omit [Fintype η] [DecidableEq ι] [DecidableEq η] in
/-- **`guardar_los_or` es propia**: no lee ninguna hoja. -/
theorem guardar_los_or_propia : Propia (leerOr (ι := ι) (η := η)) := by
  intro q g p hp
  simp [leerOr, vistos] at hp

theorem vistos_barrer_sub {α : Type} (f : α → Bool) : ∀ (l : List α), ∀ i ∈ vistos (barrer l) f, i ∈ l
  | [] => by simp [barrer, vistos]
  | j :: l => by
    intro i hi
    simp only [barrer, vistos, List.mem_cons] at hi ⊢
    rcases hi with h | h
    · exact Or.inl h
    · right
      cases hf : f j
      · rw [hf] at h
        exact vistos_barrer_sub f l i (by simpa using h)
      · rw [hf] at h
        simp [vistos] at h

omit [Fintype ι] [DecidableEq ι] [DecidableEq η] in
/-- **`no_guardar_nada` es propia**: barre solo su subárbol. -/
theorem no_guardar_nada_propia : Propia (barrerDebajo (ι := ι) (η := η)) := by
  intro q g p hp
  have := vistos_barrer_sub g _ _ hp
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at this
  obtain ⟨y, hy⟩ := this
  cases hy
  rfl

omit [DecidableEq ι] [DecidableEq η] in
/-- **Sin caja, `t ≥ L`**, desde la cota nueva (con al menos un subárbol). -/
theorem propia_sin_caja {t : ℕ} (caja : (ι × η → Bool) → (Fin 0 → Bool)) (R : ι → Pregunta (Fin 0 ⊕ (ι × η)))
    (hR : Responde caja R) (ht : Lee R t) (hP : Propia R) (hM : 0 < Fintype.card ι) : Fintype.card η ≤ t := by
  have h := cota_propia caja R hR ht hP
  rw [pow_zero, one_mul] at h
  have := (Nat.pow_le_pow_iff_left (Nat.pos_iff_ne_zero.1 hM)).1 h
  omega

omit [DecidableEq ι] [DecidableEq η] in
/-- **`no_guardar_nada` alcanza la cota con igualdad**: `s = 0`, `t = L`. -/
theorem no_guardar_nada_iguala :
    (Fintype.card η - Fintype.card η + Fintype.card η) ^ Fintype.card ι =
      2 ^ 0 * Fintype.card η ^ Fintype.card ι := by
  simp

omit [DecidableEq ι] [DecidableEq η] in
/-- **La hipótesis no es vacía**: los dos extremos cumplen todo lo que pide `cota_propia`. -/
theorem hipotesis_no_vacia :
    (Responde (cajaOr (ι := ι) (η := η)) leerOr ∧ Lee (leerOr (ι := ι) (η := η)) 1 ∧ Propia (leerOr (ι := ι) (η := η))) ∧
      (Responde (fun _ _ => false) (barrerDebajo (ι := ι) (η := η)) ∧
        Lee (barrerDebajo (ι := ι) (η := η)) (Fintype.card η) ∧ Propia (barrerDebajo (ι := ι) (η := η))) :=
  ⟨⟨guardar_los_or.1, guardar_los_or.2, guardar_los_or_propia⟩,
    ⟨no_guardar_nada.1, no_guardar_nada.2, no_guardar_nada_propia⟩⟩

end Propia

/-- **Con una lectura, la caja tiene que guardarlo todo** (`M = 3`, `L = 16`, `t = 1`): la cota nueva obliga `s ≥ 3 = M`,
y `guardar_los_or` lo alcanza. -/
theorem una_lectura_propia {s : ℕ} (caja : (Fin 3 × Fin 16 → Bool) → (Fin s → Bool))
    (R : Fin 3 → Pregunta (Fin s ⊕ (Fin 3 × Fin 16))) (hR : Responde caja R) (ht : Lee R 1) (hP : Propia R) :
    3 ≤ s := by
  have h := cota_propia caja R hR ht hP
  simp only [Fintype.card_fin] at h
  by_contra hs
  have : 2 ^ s ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ s * 16 ^ 3 ≤ 2 ^ 2 * 16 ^ 3 := Nat.mul_le_mul_right _ this
  norm_num at h this
  omega

/-- **En el medio la cota nueva mejora a `PlanoCaja`** (`M = 4`, `L = 16`, `t = 8`): obliga `s ≥ 3`. La forma producto
pediría `s ≥ 2`. -/
theorem medio_mejora {s : ℕ} (caja : (Fin 4 × Fin 16 → Bool) → (Fin s → Bool))
    (R : Fin 4 → Pregunta (Fin s ⊕ (Fin 4 × Fin 16))) (hR : Responde caja R) (ht : Lee R 8) (hP : Propia R) :
    3 ≤ s := by
  have h := cota_propia caja R hR ht hP
  simp only [Fintype.card_fin] at h
  by_contra hs
  have : 2 ^ s ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ s * 16 ^ 4 ≤ 2 ^ 2 * 16 ^ 4 := Nat.mul_le_mul_right _ this
  norm_num at h this
  omega

/-- **Con los mismos números, `cota_caja_estatica` no excluye `s = 1`**: `(4 − 1) · 16 ≤ 2^1 · 4 · 8`. -/
theorem medio_plano_no_excluye : (4 - 1) * 16 ≤ 2 ^ 1 * 4 * 8 := by norm_num

end Sagitta.Map.Tiempo.CanoProducto
