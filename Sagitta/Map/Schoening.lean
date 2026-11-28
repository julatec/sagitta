import Sagitta.Map.AzarEnElArbol
import Mathlib.InformationTheory.Hamming

/-!
# La caminata de Schöning, contada

La caminata de Schöning para `k`-SAT, sin medidas: la base es determinista y la probabilidad es contar.

## El modelo

* **Una asignación** es una función `α : Fin n → Bool`. La leemos como lista (`List.ofFn α`) para reusar `satisface` y
  `solCNF` de `ArbolElecciones`.
* **La distancia** es la de Hamming (`hammingDist` de Mathlib): en cuántas variables difieren.
* **Un paso** (`pasoCaminata`) recibe una elección `j : Fin k`. Toma la **primera** cláusula falsa y voltea la variable
  de su literal número `j`. Si no hay cláusula falsa, o la cláusula tiene menos de `j + 1` literales, no hace nada.
* **Una caminata de `t` pasos** (`caminata`) es una función de la sucesión de elecciones `e : Fin t → Fin k`. Nada es
  al azar: el azar es elegir `e` entre las `k^t` sucesiones.
* **Los aciertos** (`aciertos`) son las sucesiones con las que la caminata termina en una solución. La **proporción**
  (`proporcion`) es `aciertos / k^t`.

## Lo que se prueba

* **El lema fácil** (`aciertos_ge`, `lema_facil`): si `β` es solución y `α` está a distancia `r ≤ t` de `β`, al menos
  `k^(t−r)` sucesiones de largo `t` aciertan. La proporción es `≥ k^(−r)`. La clave (`existe_buen_paso`): en la
  primera cláusula falsa bajo `α` hay un literal verdadero bajo `β`, y voltear su variable baja la distancia en 1.
  Con `t = r` basta una sucesión (`existe_sucesion`).
* **La composición** (`composicion`, Teorema 2 de la fuente): si desde cada `α` la proporción es `≥ q^dist(α, β)`,
  arrancar con `α` uniforme da éxito `≥ ((1+q)/2)^n`. Sale de `Σ_α q^dist(α, β) = (1 + q)^n` (`suma_pow_hamming`),
  que es la suma binomial: hay `C(n, r)` asignaciones a distancia `r` (`card_distancia`, `suma_por_distancias`).
* **El costo con reinicios** (`tiempo_schoening`): con éxito `≥ ((1+q)/2)^n` por intento de `t` pasos, el costo
  esperado (la geométrica de `CostoError`) es `≤ t · (2/(1+q))^n`.
  - Con el lema fácil, `q = 1/k` y `t = n` (`tiempo_facil`); para `k = 3`, `≤ n · (3/2)^n` (`tiempo_facil_tres`).
* **El lema fino para `k = 3`, probado** (`lema_fino_tres`): a distancia `r` de una solución, `t ≥ 3r` pasos aciertan
  con probabilidad `≥ 2^(−r) / (2r + 1)`. Se cuenta en tres escalones, sin medidas ni acoplamiento:
  - la caminata real acierta al menos tantas veces como una pesimista (`caminosA`), donde la elección buena baja y las
    otras dos suben (`caminosA_le_aciertos`; un paso cualquiera sube a lo sumo 1, `dist_paso_le`);
  - la pesimista cuenta al menos las sucesiones con `2r` bajadas y `r` subidas en cualquier orden, `C(3r, r) · 2^r`
    (`caminosLibres`, `choose_le_caminosLibres`, `caminosA_tres_ge`): terminar en `≤ 0` obliga a pasar por `0`;
  - la cota del binomial sin Stirling: `27^r ≤ (2r + 1) · 4^r · C(3r, r)` (`choose_tres_ge`), por inducción sobre el
    cociente de dos términos seguidos.
  Compuesto: éxito `≥ (3/4)^n / (2n + 1)` (`exito_fino_tres`) y costo esperado `≤ 3n · (2n + 1) · (4/3)^n`
  (`tiempo_fino_tres_probado`), sin más hipótesis que una solución `β` y cláusulas de a lo sumo 3 literales.

## Lo que queda como hipótesis

El lema fino para `k` general no se prueba: `caminosA` y la comparación sirven para cualquier `k`, pero la cota del
binomial está hecha solo para `k = 3`.

**Sobre el factor polinomial.** Moser y Scheder enuncian el lema (su Lema 1) como `≥ (k−1)^(−r)`, con el factor
polinomial escondido en su notación `O*`. Tomado al pie de la letra, sin ese factor, es **falso**: una revisión
adversarial encontró una fórmula de 3-SAT con 8 variables y `α` a distancia 1 donde la proporción con `24` pasos es
`≈ 0,4968 < 1/2`, verificado en Lean en `SchoeningContraejemplo.lean` (`schoening_sin_factor_falso`). Por eso aquí no se toma como hipótesis: lo que se
prueba es la versión con el factor `1/(2r + 1)`. En este modelo una cláusula corta desperdicia las elecciones que no tienen literal; la cuenta las
trata como elecciones malas, así que la cota vale igual. La forma de contar (la caminata pesimista que domina a la real,
y la cuenta de caminos) es la de la tesis de D. Scheder (ETH 2011, §3.1, Lemas 3.2–3.3), sin su acoplamiento
probabilístico; la cota del binomial no es la de su Lema 3.4, que no se prueba ahí.

## Fuente

R. A. Moser y D. Scheder, «A Full Derandomization of Schoening's k-SAT Algorithm», arXiv 1008.4067. Lema 1 (citado) y
Teorema 2 (la suma binomial). La cota `k^(−t)` del paso correcto es la del párrafo sobre la caminata. La prueba del lema
fino sigue la forma de contar de D. Scheder, «Algorithms and Extremal Properties of SAT and CSP», tesis doctoral, ETH
Zürich 2011, §3.1 (Lemas 3.2 y 3.3), sin su acoplamiento probabilístico.
-/

namespace Sagitta.Map
namespace Tiempo

variable {n k : ℕ}

/-! ## El modelo -/

/-- La primera cláusula falsa bajo `α`, si hay. -/
def primeraFalsa (F : List Clausula) (α : Fin n → Bool) : Option Clausula :=
  F.find? fun c => !satisface (List.ofFn α) c

/-- Voltear la variable `i`. Si no existe, no hace nada. -/
def voltear (α : Fin n → Bool) (i : ℕ) : Fin n → Bool :=
  if h : i < n then Function.update α ⟨i, h⟩ (!α ⟨i, h⟩) else α

/-- **Un paso de la caminata**: en la primera cláusula falsa, voltear la variable del literal número `j`. -/
def pasoCaminata (F : List Clausula) (α : Fin n → Bool) (j : Fin k) : Fin n → Bool :=
  match primeraFalsa F α with
  | none => α
  | some c => match c[j.val]? with
    | none => α
    | some l => voltear α l.1

/-- **Una caminata de `t` pasos**, guiada por la sucesión de elecciones `e`. -/
def caminata (F : List Clausula) : (t : ℕ) → (Fin t → Fin k) → (Fin n → Bool) → Fin n → Bool
  | 0, _, α => α
  | t + 1, e, α => caminata F t (Fin.tail e) (pasoCaminata F α (e 0))

/-- **Los aciertos**: cuántas sucesiones de `t` elecciones llevan de `α` a una solución. -/
def aciertos (F : List Clausula) (k t : ℕ) (α : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun e : Fin t → Fin k => solCNF F (List.ofFn (caminata F t e α)) = true).card

/-- **La proporción de aciertos**, sobre las `k^t` sucesiones. Es la probabilidad, contada. -/
noncomputable def proporcion (F : List Clausula) (k t : ℕ) (α : Fin n → Bool) : ℝ :=
  aciertos F k t α / (k : ℝ) ^ t

/-! ## Una solución no se mueve -/

/-- Si `α` es solución, no hay cláusula falsa. -/
theorem primeraFalsa_sol {F : List Clausula} {α : Fin n → Bool} (h : solCNF F (List.ofFn α) = true) :
    primeraFalsa F α = none := by
  unfold primeraFalsa
  rw [List.find?_eq_none]
  intro c hc
  unfold solCNF at h
  rw [List.all_eq_true] at h
  simp [h c hc]

/-- Si `α` es solución, un paso no cambia nada. -/
theorem paso_sol {F : List Clausula} {α : Fin n → Bool} (h : solCNF F (List.ofFn α) = true) (j : Fin k) :
    pasoCaminata F α j = α := by
  unfold pasoCaminata
  rw [primeraFalsa_sol h]

/-- Desde una solución, la caminata se queda quieta. -/
theorem caminata_sol {F : List Clausula} :
    ∀ (t : ℕ) (e : Fin t → Fin k) (α : Fin n → Bool), solCNF F (List.ofFn α) = true → caminata F t e α = α
  | 0, _, _, _ => rfl
  | t + 1, e, α, h => by
    simp only [caminata]
    rw [paso_sol h]
    exact caminata_sol t _ α h

/-! ## Un buen paso acerca -/

/-- Poner en `i` el valor de `β`, donde difería, baja la distancia en 1. -/
theorem hamming_acercar (α β : Fin n → Bool) (i : Fin n) (h : α i ≠ β i) :
    hammingDist (Function.update α i (β i)) β + 1 = hammingDist α β := by
  unfold hammingDist
  have e : (Finset.univ.filter fun j => α j ≠ β j) =
      insert i (Finset.univ.filter fun j => Function.update α i (β i) j ≠ β j) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj]
  rw [e, Finset.card_insert_of_notMem (by simp)]

/-- **La clave**: si `α` no es solución y `β` sí, alguna elección baja la distancia a `β` en 1. En la primera cláusula
falsa bajo `α`, algún literal es verdadero bajo `β`; voltear su variable la pone como en `β`. -/
theorem existe_buen_paso {F : List Clausula} (hw : ∀ c ∈ F, c.length ≤ k) {α β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) (hα : solCNF F (List.ofFn α) = false) :
    ∃ j : Fin k, hammingDist (pasoCaminata F α j) β + 1 = hammingDist α β := by
  obtain ⟨c, hc⟩ : ∃ c, primeraFalsa F α = some c := by
    cases h : primeraFalsa F α with
    | some c => exact ⟨c, rfl⟩
    | none =>
      exfalso
      unfold primeraFalsa at h
      rw [List.find?_eq_none] at h
      have : solCNF F (List.ofFn α) = true :=
        List.all_eq_true.2 fun c hc => by simpa using h c hc
      rw [this] at hα
      exact Bool.noConfusion hα
  have hcF : c ∈ F := List.mem_of_find?_eq_some hc
  have hcf : satisface (List.ofFn α) c = false := by simpa using List.find?_some hc
  have hcβ : satisface (List.ofFn β) c = true := List.all_eq_true.1 hβ c hcF
  obtain ⟨⟨i, s⟩, hl, hlβ⟩ := List.any_eq_true.1 hcβ
  have hlα := List.any_eq_false.1 hcf _ hl
  simp only [beq_iff_eq, List.getElem?_ofFn] at hlβ hlα
  by_cases hi : i < n
  swap
  · simp [hi] at hlβ
  simp only [hi, dite_true, Option.some.injEq] at hlβ hlα
  obtain ⟨j, hj, hcj⟩ := List.mem_iff_getElem.1 hl
  refine ⟨⟨j, lt_of_lt_of_le hj (hw c hcF)⟩, ?_⟩
  have hpaso : pasoCaminata F α ⟨j, lt_of_lt_of_le hj (hw c hcF)⟩ =
      Function.update α ⟨i, hi⟩ (β ⟨i, hi⟩) := by
    unfold pasoCaminata
    rw [hc]
    simp only [List.getElem?_eq_getElem hj, hcj]
    unfold voltear
    simp only [hi, ↓reduceDIte]
    rw [hlβ]
    congr 1
    cases s <;> cases h : α ⟨i, hi⟩ <;> simp_all
  rw [hpaso]
  exact hamming_acercar α β _ (by rw [hlβ]; exact hlα)

/-! ## El lema fácil, contando -/

/-- No hay más aciertos que sucesiones. -/
theorem aciertos_le (F : List Clausula) (k t : ℕ) (α : Fin n → Bool) : aciertos F k t α ≤ k ^ t := by
  unfold aciertos
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Desde una solución aciertan todas las sucesiones. -/
theorem aciertos_todos {F : List Clausula} {t : ℕ} {α : Fin n → Bool} (h : solCNF F (List.ofFn α) = true) :
    aciertos F k t α = k ^ t := by
  unfold aciertos
  rw [Finset.filter_true_of_mem fun e _ => by rw [caminata_sol t e α h]; exact h]
  simp

/-- **El lema fácil**: a distancia `r ≤ t` de una solución, aciertan al menos `k^(t−r)` de las `k^t` sucesiones. Las
que empiezan con los `r` buenos pasos aciertan, sigan como sigan. -/
theorem aciertos_ge {F : List Clausula} (hk : 0 < k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) :
    ∀ (t : ℕ) (α : Fin n → Bool), hammingDist α β ≤ t → k ^ (t - hammingDist α β) ≤ aciertos F k t α := by
  intro t
  induction t with
  | zero =>
    intro α hd
    have : α = β := hammingDist_eq_zero.1 (by omega)
    subst this
    rw [aciertos_todos hβ]
    simp
  | succ t ih =>
    intro α hd
    by_cases hα : solCNF F (List.ofFn α) = true
    · rw [aciertos_todos hα]
      exact Nat.pow_le_pow_right hk (Nat.sub_le _ _)
    · obtain ⟨j, hj⟩ := existe_buen_paso hw hβ (by simpa using hα)
      have h1 := ih (pasoCaminata F α j) (by omega)
      let g : (Fin t → Fin k) ↪ (Fin (t + 1) → Fin k) :=
        ⟨fun a => (Fin.cons j a : Fin (t + 1) → Fin k), fun a b h => Fin.cons_right_injective (α := fun _ => Fin k) j h⟩
      calc k ^ (t + 1 - hammingDist α β) = k ^ (t - hammingDist (pasoCaminata F α j) β) := by
            congr 1; omega
        _ ≤ aciertos F k t (pasoCaminata F α j) := h1
        _ = ((Finset.univ.filter fun e : Fin t → Fin k =>
              solCNF F (List.ofFn (caminata F t e (pasoCaminata F α j))) = true).map g).card :=
            (Finset.card_map _).symm
        _ ≤ aciertos F k (t + 1) α := by
            apply Finset.card_le_card
            intro e he
            rw [Finset.mem_map] at he
            obtain ⟨a, ha, rfl⟩ := he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            have hg : g a = Fin.cons j a := rfl
            rw [hg]
            simpa [caminata, Fin.tail_cons, Fin.cons_zero] using ha

/-- Con exactamente `r` elecciones hay al menos una sucesión que acierta. -/
theorem existe_sucesion {F : List Clausula} (hk : 0 < k) (hw : ∀ c ∈ F, c.length ≤ k) {α β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) : 0 < aciertos F k (hammingDist α β) α := by
  have := aciertos_ge hk hw hβ (hammingDist α β) α le_rfl
  simp at this
  omega

/-- **El lema fácil, como proporción**: la caminata de `t ≥ r` pasos acierta con probabilidad `≥ k^(−r)`. -/
theorem lema_facil {F : List Clausula} (hk : 0 < k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) {t : ℕ} {α : Fin n → Bool} (hd : hammingDist α β ≤ t) :
    (1 / (k : ℝ)) ^ hammingDist α β ≤ proporcion F k t α := by
  have h := aciertos_ge hk hw hβ t α hd
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  unfold proporcion
  rw [le_div_iff₀ (by positivity)]
  have e : (k : ℝ) ^ t = (k : ℝ) ^ (t - hammingDist α β) * (k : ℝ) ^ hammingDist α β := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  calc (1 / (k : ℝ)) ^ hammingDist α β * (k : ℝ) ^ t = (k : ℝ) ^ (t - hammingDist α β) := by
        rw [e, div_pow, one_pow]; field_simp
    _ ≤ aciertos F k t α := by exact_mod_cast h

/-! ## La composición: la suma binomial -/

/-- **La suma sobre todas las asignaciones**: `Σ_α q^dist(α, β) = (1 + q)^n`. Cada variable aporta `1` si coincide y
`q` si difiere. -/
theorem suma_pow_hamming (β : Fin n → Bool) (q : ℝ) :
    ∑ α : Fin n → Bool, q ^ hammingDist α β = (1 + q) ^ n := by
  have h1 : ∀ α : Fin n → Bool, q ^ hammingDist α β = ∏ i, q ^ (if α i ≠ β i then 1 else 0) := by
    intro α
    rw [Finset.prod_pow_eq_pow_sum]
    unfold hammingDist
    rw [Finset.card_filter]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (b : Bool) => q ^ (if b ≠ β i then 1 else 0))]
  have h2 : ∀ i, ∑ b : Bool, q ^ (if b ≠ β i then 1 else 0) = 1 + q := by
    intro i
    rw [Fintype.sum_bool]
    cases β i <;> simp [add_comm]
  rw [Finset.prod_congr rfl fun i _ => h2 i]
  simp

/-- **Hay `C(n, r)` asignaciones a distancia `r`**: cada una es el conjunto de variables donde difiere de `β`. -/
theorem card_distancia (β : Fin n → Bool) (r : ℕ) :
    (Finset.univ.filter fun α : Fin n → Bool => hammingDist α β = r).card = n.choose r := by
  rw [show n.choose r = (Finset.powersetCard r (Finset.univ : Finset (Fin n))).card by simp]
  refine Finset.card_bij' (fun α _ => Finset.univ.filter fun i => α i ≠ β i)
    (fun S _ => fun i => if i ∈ S then !β i else β i) ?_ ?_ ?_ ?_
  · intro α hα
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
    simpa [Finset.mem_powersetCard, hammingDist] using hα
  · intro S hS
    simp only [Finset.mem_powersetCard] at hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold hammingDist
    rw [← hS.2]
    congr 1
    ext i
    by_cases h : i ∈ S <;> simp [h]
  · intro α _
    funext i
    by_cases h : α i = β i
    · simp [h]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases ha : α i <;> cases hb : β i <;> simp_all
  · intro S _
    ext i
    by_cases h : i ∈ S <;> simp [h]

/-- **La misma suma, por distancias**: `Σ_α q^dist(α, β) = Σ_r C(n, r) q^r`. Con `add_pow` es `(1 + q)^n`. -/
theorem suma_por_distancias (β : Fin n → Bool) (q : ℝ) :
    ∑ α : Fin n → Bool, q ^ hammingDist α β = ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * q ^ r := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (n + 1))
    (g := fun α : Fin n → Bool => hammingDist α β)
    (fun α _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hammingDist_le_card_fintype.trans (by simp))))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => q ^ r) (fun α hα => by
    simp only [Finset.mem_filter] at hα; rw [hα.2]), Finset.sum_const, card_distancia, nsmul_eq_mul]

/-- La suma binomial de la fuente. -/
theorem suma_binomial (q : ℝ) : ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * q ^ r = (1 + q) ^ n := by
  rw [add_comm 1 q, add_pow]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [mul_comm]

/-- **La composición de Schöning** (Teorema 2 de la fuente): si desde cada `α` el éxito es `≥ q^dist(α, β)`, el
éxito promedio sobre las `2^n` asignaciones de partida es `≥ ((1 + q)/2)^n`. -/
theorem composicion (f : (Fin n → Bool) → ℝ) (β : Fin n → Bool) (q : ℝ) (h : ∀ α, q ^ hammingDist α β ≤ f α) :
    ((1 + q) / 2) ^ n ≤ (∑ α, f α) / 2 ^ n := by
  rw [div_pow, ← suma_pow_hamming β q]
  gcongr with α
  exact h α

/-! ## El éxito de un intento -/

/-- **El éxito de un intento**: arrancar con `α` uniforme y caminar `t` pasos con elecciones uniformes. Es la
proporción de pares `(α, e)` que aciertan. -/
noncomputable def exitoSchoening (F : List Clausula) (n k t : ℕ) : ℝ :=
  (∑ α : Fin n → Bool, proporcion F k t α) / 2 ^ n

/-- La proporción no es negativa. -/
theorem proporcion_nonneg (F : List Clausula) (k t : ℕ) (α : Fin n → Bool) : 0 ≤ proporcion F k t α := by
  unfold proporcion; positivity

/-- La proporción es a lo sumo 1. -/
theorem proporcion_le_one (F : List Clausula) (k t : ℕ) (α : Fin n → Bool) : proporcion F k t α ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast aciertos_le F k t α) (by positivity)

/-- El éxito de un intento no es negativo. -/
theorem exitoSchoening_nonneg (F : List Clausula) (n k t : ℕ) : 0 ≤ exitoSchoening F n k t := by
  unfold exitoSchoening
  exact div_nonneg (Finset.sum_nonneg fun α _ => proporcion_nonneg F k t α) (by positivity)

/-- El éxito de un intento es a lo sumo 1. -/
theorem exitoSchoening_le_one (F : List Clausula) (n k t : ℕ) : exitoSchoening F n k t ≤ 1 := by
  unfold exitoSchoening
  refine div_le_one_of_le₀ ?_ (by positivity)
  calc ∑ α : Fin n → Bool, proporcion F k t α ≤ ∑ _α : Fin n → Bool, (1 : ℝ) :=
        Finset.sum_le_sum fun α _ => proporcion_le_one F k t α
    _ = 2 ^ n := by simp

/-- El éxito, como número en `[0, 1]`, para la geométrica de `CostoError`. -/
noncomputable def exitoU (F : List Clausula) (n k t : ℕ) : unitInterval :=
  ⟨exitoSchoening F n k t, exitoSchoening_nonneg F n k t, exitoSchoening_le_one F n k t⟩

/-- **Con el lema fácil**: `t = n` pasos alcanzan, y el éxito es `≥ ((1 + 1/k)/2)^n`. -/
theorem exito_facil {F : List Clausula} (hk : 0 < k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) : ((1 + 1 / (k : ℝ)) / 2) ^ n ≤ exitoSchoening F n k n :=
  composicion _ β _ fun _ => lema_facil hk hw hβ (hammingDist_le_card_fintype.trans (by simp))

/-- Para `3`-SAT: éxito `≥ (2/3)^n`. -/
theorem exito_facil_tres {F : List Clausula} (hw : ∀ c ∈ F, c.length ≤ 3) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) : (2 / 3 : ℝ) ^ n ≤ exitoSchoening F n 3 n := by
  have := exito_facil (k := 3) (by norm_num) hw hβ
  norm_num at this ⊢
  exact this

/-! ## El costo con reinicios -/

/-- **El costo de reiniciar**: si desde cada `α` el éxito de `t` pasos es `≥ q^dist(α, β)`, el número esperado de
pasos hasta acertar, reiniciando con `α` uniforme cada vez que falla, es `≤ t · (2/(1+q))^n`. -/
theorem tiempo_schoening {F : List Clausula} {t : ℕ} {q : ℝ} (hq : 0 ≤ q) (β : Fin n → Bool)
    (h : ∀ α, q ^ hammingDist α β ≤ proporcion F k t α) :
    ∫ x, costo t x ∂tramos 1 (exitoU F n k t) ≤ t * (2 / (1 + q)) ^ n := by
  have hlow : ((1 + q) / 2) ^ n ≤ exitoSchoening F n k t := composicion _ β q h
  have hpos : 0 < ((1 + q) / 2) ^ n := by positivity
  have hne : exitoU F n k t ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    simp only [exitoU, Set.Icc.coe_zero] at this
    linarith
  rw [costo_esperado t 1 hne]
  simp only [exitoU, Nat.cast_one, mul_one]
  calc (t : ℝ) / exitoSchoening F n k t ≤ t / ((1 + q) / 2) ^ n :=
        div_le_div_of_nonneg_left (by positivity) hpos hlow
    _ = t * (2 / (1 + q)) ^ n := by
        rw [div_pow, div_pow]; field_simp

/-- **Schöning con el lema fácil**: costo esperado `≤ n · (2/(1 + 1/k))^n`. -/
theorem tiempo_facil {F : List Clausula} (hk : 0 < k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) :
    ∫ x, costo n x ∂tramos 1 (exitoU F n k n) ≤ n * (2 / (1 + 1 / (k : ℝ))) ^ n :=
  tiempo_schoening (by positivity) β fun _ => lema_facil hk hw hβ (hammingDist_le_card_fintype.trans (by simp))

/-- **Para `3`-SAT**: `≤ n · (3/2)^n`. -/
theorem tiempo_facil_tres {F : List Clausula} (hw : ∀ c ∈ F, c.length ≤ 3) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) :
    ∫ x, costo n x ∂tramos 1 (exitoU F n 3 n) ≤ n * (3 / 2 : ℝ) ^ n := by
  have := tiempo_facil (k := 3) (by norm_num) hw hβ
  norm_num at this ⊢
  exact this

/-! ## El lema fino para `k = 3`, contando

La caminata real se compara con una caminata pesimista, sin fórmula. En cada paso hay una elección buena (baja la
distancia en 1, `existe_buen_paso`) y `k − 1` malas, que la suben a lo sumo en 1 (`dist_paso_le`). La caminata pesimista
trata toda elección mala como una subida, y se queda en `0` una vez que llega. -/

/-- **La caminata pesimista, contada**: cuántas de las `k^t` sucesiones llevan de la distancia `d` a `0` en a lo sumo
`t` pasos, si en cada paso una elección baja y las otras `k − 1` suben. En `0` cuentan todas. -/
def caminosA (k : ℕ) : ℕ → ℕ → ℕ
  | t, 0 => k ^ t
  | 0, _ + 1 => 0
  | t + 1, d + 1 => caminosA k t d + (k - 1) * caminosA k t (d + 2)

/-- La caminata pesimista no tiene más caminos buenos que sucesiones. -/
theorem caminosA_le (hk : 0 < k) : ∀ (t d : ℕ), caminosA k t d ≤ k ^ t
  | t, 0 => by simp [caminosA]
  | 0, _ + 1 => by simp [caminosA]
  | t + 1, d + 1 => by
    simp only [caminosA]
    have h1 := caminosA_le hk t d
    have h2 := caminosA_le hk t (d + 2)
    calc caminosA k t d + (k - 1) * caminosA k t (d + 2) ≤ k ^ t + (k - 1) * k ^ t := by gcongr
      _ = k ^ (t + 1) := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- Más lejos, menos caminos. -/
theorem caminosA_succ_le (hk : 0 < k) : ∀ (t d : ℕ), caminosA k t (d + 1) ≤ caminosA k t d
  | 0, _ => by simp [caminosA]
  | t + 1, 0 => caminosA_le hk (t + 1) 1
  | t + 1, d + 1 => by
    simp only [caminosA]
    have h1 := caminosA_succ_le hk t d
    have h2 := caminosA_succ_le hk t (d + 2)
    gcongr

/-- Más lejos, menos caminos buenos. -/
theorem caminosA_anti (hk : 0 < k) (t : ℕ) {d d' : ℕ} (h : d ≤ d') : caminosA k t d' ≤ caminosA k t d :=
  antitone_nat_of_succ_le (caminosA_succ_le hk t) h

/-- Un paso más multiplica los caminos por `k`, por lo menos. -/
theorem caminosA_mul_le : ∀ (t d : ℕ), k * caminosA k t d ≤ caminosA k (t + 1) d
  | t, 0 => by simp [caminosA, pow_succ, mul_comm]
  | 0, _ + 1 => by simp [caminosA]
  | t + 1, d + 1 => by
    have h1 := caminosA_mul_le t d
    have h2 := caminosA_mul_le t (d + 2)
    change k * (caminosA k t d + (k - 1) * caminosA k t (d + 2)) ≤
      caminosA k (t + 1) d + (k - 1) * caminosA k (t + 1) (d + 2)
    calc k * (caminosA k t d + (k - 1) * caminosA k t (d + 2))
        = k * caminosA k t d + (k - 1) * (k * caminosA k t (d + 2)) := by ring
      _ ≤ caminosA k (t + 1) d + (k - 1) * caminosA k (t + 1) (d + 2) := by gcongr

/-- Pasos de más no quitan caminos buenos: cada uno se completa de `k^m` maneras. -/
theorem caminosA_add (t d : ℕ) : ∀ m : ℕ, k ^ m * caminosA k t d ≤ caminosA k (t + m) d
  | 0 => by simp
  | m + 1 => by
    calc k ^ (m + 1) * caminosA k t d = k * (k ^ m * caminosA k t d) := by ring
      _ ≤ k * caminosA k (t + m) d := by gcongr; exact caminosA_add t d m
      _ ≤ caminosA k (t + m + 1) d := caminosA_mul_le _ _

/-- **Un paso cualquiera** cambia la distancia en a lo sumo 1. -/
theorem dist_paso_le (F : List Clausula) (α β : Fin n → Bool) (j : Fin k) :
    hammingDist (pasoCaminata F α j) β ≤ hammingDist α β + 1 := by
  have hv : ∀ i : ℕ, hammingDist (voltear α i) α ≤ 1 := by
    intro i
    unfold voltear
    split_ifs with h
    · unfold hammingDist
      calc (Finset.univ.filter fun x => Function.update α ⟨i, h⟩ (!α ⟨i, h⟩) x ≠ α x).card
          ≤ ({⟨i, h⟩} : Finset (Fin n)).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            by_contra hxi
            simp only [Finset.mem_singleton] at hxi
            exact hx (Function.update_of_ne hxi _ _)
        _ = 1 := by simp
    · simp
  have hp : hammingDist (pasoCaminata F α j) α ≤ 1 := by
    unfold pasoCaminata
    split
    · simp
    · split
      · simp
      · exact hv _
  calc hammingDist (pasoCaminata F α j) β ≤ hammingDist (pasoCaminata F α j) α + hammingDist α β :=
        hammingDist_triangle _ _ _
    _ ≤ hammingDist α β + 1 := by omega

/-- **Los aciertos de `t + 1` pasos** se reparten según la primera elección. -/
theorem aciertos_succ (F : List Clausula) (k t : ℕ) (α : Fin n → Bool) :
    aciertos F k (t + 1) α = ∑ j : Fin k, aciertos F k t (pasoCaminata F α j) := by
  unfold aciertos
  simp only [Finset.card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (t + 1) => Fin k) _ _ (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  simp [Fin.consEquiv, caminata, Fin.tail_cons, Fin.cons_zero]

/-- **La comparación**: la caminata real acierta por lo menos tantas veces como la pesimista. -/
theorem caminosA_le_aciertos {F : List Clausula} (hk : 0 < k) (hw : ∀ c ∈ F, c.length ≤ k) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) :
    ∀ (t : ℕ) (α : Fin n → Bool), caminosA k t (hammingDist α β) ≤ aciertos F k t α := by
  intro t
  induction t with
  | zero =>
    intro α
    by_cases hα : solCNF F (List.ofFn α) = true
    · rw [aciertos_todos hα]; exact caminosA_le hk 0 _
    · have hd : hammingDist α β ≠ 0 := fun h => hα (by rw [hammingDist_eq_zero.1 h]; exact hβ)
      obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd
      rw [hd']; simp [caminosA]
  | succ t ih =>
    intro α
    by_cases hα : solCNF F (List.ofFn α) = true
    · rw [aciertos_todos hα]; exact caminosA_le hk _ _
    · obtain ⟨g, hg⟩ := existe_buen_paso hw hβ (by simpa using hα)
      rw [← hg, aciertos_succ, ← Finset.add_sum_erase _ _ (Finset.mem_univ g)]
      simp only [caminosA]
      apply Nat.add_le_add (ih _)
      calc (k - 1) * caminosA k t (hammingDist (pasoCaminata F α g) β + 2)
          = ∑ _j ∈ Finset.univ.erase g, caminosA k t (hammingDist (pasoCaminata F α g) β + 2) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ g), Finset.card_univ,
              Fintype.card_fin, smul_eq_mul]
        _ ≤ ∑ j ∈ Finset.univ.erase g, aciertos F k t (pasoCaminata F α j) := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine le_trans (caminosA_anti hk t ?_) (ih _)
            have := dist_paso_le F α β j
            omega

/-- **La caminata libre, contada**: sin quedarse en `0` y con la distancia en `ℤ`, cuántas sucesiones terminan en `≤ 0`
después de `t` pasos (una elección baja, `k − 1` suben). -/
def caminosLibres (k : ℕ) : ℕ → ℤ → ℕ
  | 0, d => if d ≤ 0 then 1 else 0
  | t + 1, d => caminosLibres k t (d - 1) + (k - 1) * caminosLibres k t (d + 1)

/-- La caminata libre no tiene más caminos que sucesiones. -/
theorem caminosLibres_le (hk : 0 < k) : ∀ (t : ℕ) (d : ℤ), caminosLibres k t d ≤ k ^ t
  | 0, d => by unfold caminosLibres; split_ifs <;> simp
  | t + 1, d => by
    simp only [caminosLibres]
    have h1 := caminosLibres_le hk t (d - 1)
    have h2 := caminosLibres_le hk t (d + 1)
    calc caminosLibres k t (d - 1) + (k - 1) * caminosLibres k t (d + 1) ≤ k ^ t + (k - 1) * k ^ t := by gcongr
      _ = k ^ (t + 1) := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- La libre que termina en `≤ 0` pasó por `0`: la pesimista la cuenta. -/
theorem caminosLibres_le_caminosA (hk : 0 < k) : ∀ (t d : ℕ), caminosLibres k t d ≤ caminosA k t d
  | t, 0 => by simpa [caminosA] using caminosLibres_le hk t 0
  | 0, d + 1 => by simp [caminosLibres, caminosA]
  | t + 1, d + 1 => by
    simp only [caminosLibres, caminosA]
    have h1 := caminosLibres_le_caminosA hk t d
    have h2 := caminosLibres_le_caminosA hk t (d + 2)
    have e1 : ((d + 1 : ℕ) : ℤ) - 1 = (d : ℕ) := by push_cast; ring
    have e2 : ((d + 1 : ℕ) : ℤ) + 1 = ((d + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2]
    gcongr

/-- **Contar las palabras**: con `g` pasos buenos y `b` malos, en cualquier orden, y `d + b ≤ g`, la libre termina en
`≤ 0`. Hay `C(g + b, g) · (k − 1)^b` de esas sucesiones. -/
theorem choose_le_caminosLibres :
    ∀ (t g b : ℕ) (d : ℤ), g + b = t → d + b ≤ g → t.choose g * (k - 1) ^ b ≤ caminosLibres k t d
  | 0, g, b, d, h, hd => by
    obtain ⟨rfl, rfl⟩ : g = 0 ∧ b = 0 := by omega
    simp only [Nat.choose_self, pow_zero, mul_one, caminosLibres]
    split_ifs with h' <;> [rfl; (push_cast at hd; omega)]
  | t + 1, 0, b, d, h, hd => by
    obtain rfl : b = t + 1 := by omega
    have := choose_le_caminosLibres t 0 t (d + 1) (by omega) (by push_cast at hd ⊢; omega)
    simp only [Nat.choose_zero_right, one_mul] at this ⊢
    simp only [caminosLibres]
    calc (k - 1) ^ (t + 1) = (k - 1) * (k - 1) ^ t := by ring
      _ ≤ (k - 1) * caminosLibres k t (d + 1) := by gcongr
      _ ≤ _ := Nat.le_add_left _ _
  | t + 1, g + 1, 0, d, h, hd => by
    have hg : g = t := by omega
    rw [hg]
    have := choose_le_caminosLibres t t 0 (d - 1) (by omega) (by push_cast at hd ⊢; omega)
    simp only [Nat.choose_self, pow_zero, mul_one] at this ⊢
    simp only [caminosLibres]
    exact le_trans this (Nat.le_add_right _ _)
  | t + 1, g + 1, b + 1, d, h, hd => by
    have h1 := choose_le_caminosLibres t g (b + 1) (d - 1) (by omega) (by push_cast at hd ⊢; omega)
    have h2 := choose_le_caminosLibres t (g + 1) b (d + 1) (by omega) (by push_cast at hd ⊢; omega)
    simp only [caminosLibres]
    rw [Nat.choose_succ_succ']
    calc (t.choose g + t.choose (g + 1)) * (k - 1) ^ (b + 1)
        = t.choose g * (k - 1) ^ (b + 1) + (k - 1) * (t.choose (g + 1) * (k - 1) ^ b) := by ring
      _ ≤ _ := by gcongr

/-- **La cota del binomial**, sin Stirling: `27^r ≤ (2r + 1) · 4^r · C(3r, r)`. El cociente entre dos términos
seguidos de `(2r + 1) · C(3r, r) · 4^r / 27^r` es `≥ 1`. -/
theorem choose_tres_ge : ∀ r : ℕ, 27 ^ r ≤ (2 * r + 1) * 4 ^ r * (3 * r).choose r
  | 0 => by simp
  | r + 1 => by
    have ih := choose_tres_ge r
    rw [show 3 * (r + 1) = 3 * r + 3 by ring]
    set x := (3 * r).choose r
    set y := (3 * r + 3).choose (r + 1)
    have a : y * (r + 1) = (3 * r + 3).choose r * (2 * r + 3) := by
      have := Nat.choose_succ_right_eq (3 * r + 3) r
      change (3 * r + 3).choose (r + 1) * (r + 1) = _
      rw [this]; congr 1; omega
    have b : (3 * r + 2).choose r * (3 * r + 3) = (3 * r + 3).choose r * (2 * r + 3) := by
      have := Nat.choose_mul_succ_eq (3 * r + 2) r
      rw [this]; congr 1; omega
    have c : (3 * r + 1).choose r * (3 * r + 2) = (3 * r + 2).choose r * (2 * r + 2) := by
      have := Nat.choose_mul_succ_eq (3 * r + 1) r
      rw [this]; congr 1; omega
    have d : x * (3 * r + 1) = (3 * r + 1).choose r * (2 * r + 1) := by
      have := Nat.choose_mul_succ_eq (3 * r) r
      rw [this]; congr 1; omega
    have P : y * ((r + 1) * (2 * r + 2) * (2 * r + 1)) = x * ((3 * r + 1) * (3 * r + 2) * (3 * r + 3)) := by
      calc y * ((r + 1) * (2 * r + 2) * (2 * r + 1)) = (y * (r + 1)) * (2 * r + 2) * (2 * r + 1) := by ring
        _ = ((3 * r + 2).choose r * (3 * r + 3)) * (2 * r + 2) * (2 * r + 1) := by rw [a, b]
        _ = ((3 * r + 2).choose r * (2 * r + 2)) * (3 * r + 3) * (2 * r + 1) := by ring
        _ = ((3 * r + 1).choose r * (2 * r + 1)) * (3 * r + 2) * (3 * r + 3) := by rw [← c]; ring
        _ = x * ((3 * r + 1) * (3 * r + 2) * (3 * r + 3)) := by rw [← d]; ring
    have hM : 0 < (r + 1) * (2 * r + 2) * (2 * r + 1) := by positivity
    have poly : 27 * (2 * r + 1) * ((r + 1) * (2 * r + 2) * (2 * r + 1)) ≤
        (2 * (r + 1) + 1) * 4 * ((3 * r + 1) * (3 * r + 2) * (3 * r + 3)) := by
      ring_nf; nlinarith [sq_nonneg r, pow_two_nonneg r]
    refine Nat.le_of_mul_le_mul_right ?_ hM
    calc 27 ^ (r + 1) * ((r + 1) * (2 * r + 2) * (2 * r + 1))
        = 27 * 27 ^ r * ((r + 1) * (2 * r + 2) * (2 * r + 1)) := by ring
      _ ≤ 27 * ((2 * r + 1) * 4 ^ r * x) * ((r + 1) * (2 * r + 2) * (2 * r + 1)) := by gcongr
      _ = (27 * (2 * r + 1) * ((r + 1) * (2 * r + 2) * (2 * r + 1))) * (4 ^ r * x) := by ring
      _ ≤ ((2 * (r + 1) + 1) * 4 * ((3 * r + 1) * (3 * r + 2) * (3 * r + 3))) * (4 ^ r * x) := by gcongr
      _ = (2 * (r + 1) + 1) * 4 ^ (r + 1) * y * ((r + 1) * (2 * r + 2) * (2 * r + 1)) := by
          rw [mul_assoc _ y, P]; ring

/-- **La caminata pesimista para `k = 3`**: desde `r`, en `3r` pasos, al menos `C(3r, r) · 2^r` sucesiones llegan a `0`
(las de `2r` bajadas y `r` subidas, en cualquier orden). -/
theorem caminosA_tres_ge (r : ℕ) : (3 * r).choose r * 2 ^ r ≤ caminosA 3 (3 * r) r := by
  have h := choose_le_caminosLibres (k := 3) (3 * r) (2 * r) r (r : ℤ) (by ring) (by push_cast; omega)
  have e : (3 * r).choose (2 * r) = (3 * r).choose r := by
    rw [show 3 * r = 2 * r + r by ring, Nat.choose_symm_add]
  rw [e] at h
  exact le_trans h (caminosLibres_le_caminosA (by norm_num) _ _)

/-- **El lema fino para `3`-SAT**, con un factor polinomial explícito (Moser–Scheder lo enuncian sin él, escondido en su
`O*`; sin el factor es falso): a distancia `r` de una solución, la
caminata de `t ≥ 3r` pasos acierta con probabilidad `≥ 2^(−r) / (2r + 1)`. Vale con cláusulas de a lo sumo 3
literales: una elección sin literal cuenta como mala. -/
theorem lema_fino_tres {F : List Clausula} (hw : ∀ c ∈ F, c.length ≤ 3) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) {t : ℕ} {α : Fin n → Bool} (hd : 3 * hammingDist α β ≤ t) :
    (1 / 2 : ℝ) ^ hammingDist α β / (2 * hammingDist α β + 1) ≤ proporcion F 3 t α := by
  set r := hammingDist α β
  have h1 : 3 ^ (t - 3 * r) * ((3 * r).choose r * 2 ^ r) ≤ aciertos F 3 t α := by
    calc 3 ^ (t - 3 * r) * ((3 * r).choose r * 2 ^ r) ≤ 3 ^ (t - 3 * r) * caminosA 3 (3 * r) r := by
          gcongr; exact caminosA_tres_ge r
      _ ≤ caminosA 3 (3 * r + (t - 3 * r)) r := caminosA_add _ _ _
      _ = caminosA 3 t r := by congr 1; omega
      _ ≤ aciertos F 3 t α := caminosA_le_aciertos (by norm_num) hw hβ t α
  have h2 := choose_tres_ge r
  have h1' : (3 : ℝ) ^ (t - 3 * r) * ((3 * r).choose r * 2 ^ r) ≤ aciertos F 3 t α := by exact_mod_cast h1
  have h2' : (27 : ℝ) ^ r ≤ (2 * r + 1) * 4 ^ r * (3 * r).choose r := by exact_mod_cast h2
  have et : (3 : ℝ) ^ t = 3 ^ (t - 3 * r) * 27 ^ r := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
  unfold proporcion
  rw [Nat.cast_ofNat, le_div_iff₀ (by positivity), et]
  have hA : (0 : ℝ) < 3 ^ (t - 3 * r) := by positivity
  have hr : (0 : ℝ) < 2 * r + 1 := by positivity
  calc (1 / 2 : ℝ) ^ r / (2 * r + 1) * (3 ^ (t - 3 * r) * 27 ^ r)
      ≤ (1 / 2 : ℝ) ^ r / (2 * r + 1) * (3 ^ (t - 3 * r) * ((2 * r + 1) * 4 ^ r * (3 * r).choose r)) := by
        gcongr
    _ = 3 ^ (t - 3 * r) * ((3 * r).choose r * 2 ^ r) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_pow, one_pow]
        field_simp
        ring
    _ ≤ aciertos F 3 t α := h1'

/-- **El éxito de un intento con el lema fino**: `3n` pasos, éxito `≥ (3/4)^n / (2n + 1)`. -/
theorem exito_fino_tres {F : List Clausula} (hw : ∀ c ∈ F, c.length ≤ 3) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) :
    (3 / 4 : ℝ) ^ n / (2 * n + 1) ≤ exitoSchoening F n 3 (3 * n) := by
  have hn : (0 : ℝ) < 2 * n + 1 := by positivity
  have h := composicion (fun α => (2 * n + 1 : ℝ) * proporcion F 3 (3 * n) α) β (1 / 2) fun α => by
    have hd : hammingDist α β ≤ n := hammingDist_le_card_fintype.trans (by simp)
    have hdr : ((hammingDist α β : ℕ) : ℝ) ≤ n := by exact_mod_cast hd
    have := lema_fino_tres hw hβ (t := 3 * n) (α := α) (by omega)
    have hr : (0 : ℝ) < 2 * hammingDist α β + 1 := by positivity
    calc (1 / 2 : ℝ) ^ hammingDist α β = (2 * n + 1) * ((1 / 2) ^ hammingDist α β / (2 * n + 1)) := by
          field_simp
      _ ≤ (2 * n + 1) * ((1 / 2) ^ hammingDist α β / (2 * hammingDist α β + 1)) := by
          gcongr
      _ ≤ _ := by gcongr
  rw [← Finset.mul_sum, mul_div_assoc] at h
  unfold exitoSchoening
  rw [div_le_iff₀ hn]
  norm_num at h ⊢
  linarith

/-- **Schöning para `3`-SAT, probado**: costo esperado `≤ 3n · (2n + 1) · (4/3)^n`. Es el `(4/3)^n · poli(n)` de la
literatura, sin hipótesis más que la solución `β`. -/
theorem tiempo_fino_tres_probado {F : List Clausula} (hw : ∀ c ∈ F, c.length ≤ 3) {β : Fin n → Bool}
    (hβ : solCNF F (List.ofFn β) = true) :
    ∫ x, costo (3 * n) x ∂tramos 1 (exitoU F n 3 (3 * n)) ≤ (3 * n : ℕ) * (2 * n + 1) * (4 / 3 : ℝ) ^ n := by
  have hlow := exito_fino_tres hw hβ
  have hpos : 0 < (3 / 4 : ℝ) ^ n / (2 * n + 1) := by positivity
  have hne : exitoU F n 3 (3 * n) ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    simp only [exitoU, Set.Icc.coe_zero] at this
    linarith
  rw [costo_esperado (3 * n) 1 hne]
  simp only [exitoU, Nat.cast_one, mul_one]
  calc ((3 * n : ℕ) : ℝ) / exitoSchoening F n 3 (3 * n) ≤ (3 * n : ℕ) / ((3 / 4 : ℝ) ^ n / (2 * n + 1)) :=
        div_le_div_of_nonneg_left (by positivity) hpos hlow
    _ = (3 * n : ℕ) * (2 * n + 1) * (4 / 3 : ℝ) ^ n := by
        rw [div_div_eq_mul_div, div_pow, show (4 / 3 : ℝ) ^ n = 4 ^ n / 3 ^ n by rw [div_pow]]
        field_simp

/-! ## Controles -/

/-- Tres cláusulas en dos variables: la única solución es `x₀ = x₁ = true`. -/
def tresDos : List Clausula := [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)]]

/-- La solución, y que el punto de partida no lo es. -/
example : solCNF tresDos (List.ofFn fun _ : Fin 2 => true) = true ∧
    solCNF tresDos (List.ofFn fun _ : Fin 2 => false) = false := by decide

/-- Distancia 2 entre todo `false` y todo `true`. -/
example : hammingDist (fun _ : Fin 2 => false) (fun _ : Fin 2 => true) = 2 := by decide

/-- Un paso: la primera cláusula falsa es la primera; el literal `0` voltea `x₀`. -/
example : pasoCaminata tresDos (fun _ : Fin 2 => false) (0 : Fin 2) = ![true, false] := by decide

/-- Desde todo `false`, con 2 pasos de 2 elecciones, alguna de las 4 sucesiones acierta. -/
example : 0 < aciertos tresDos 2 2 (fun _ : Fin 2 => false) := by decide

/-- Desde la solución aciertan las 4. -/
example : aciertos tresDos 2 2 (fun _ : Fin 2 => true) = 4 := by decide

/-- Una fórmula sin solución: nadie acierta. -/
example : aciertos [[(0, true)], [(0, false)]] 1 3 (fun _ : Fin 1 => false) = 0 := by decide

/-- Hay `C(3, 2) = 3` asignaciones a distancia 2 de todo `true`. -/
example : (Finset.univ.filter fun α : Fin 3 → Bool => hammingDist α (fun _ => true) = 2).card = 3 := by decide

/-- La pesimista desde `1` en 3 pasos: `9 + 2 · 1 = 11` de las 27 sucesiones. -/
example : caminosA 3 3 1 = 11 := by decide

/-- La libre desde `1` en 3 pasos: `C(3, 2) · 2 + C(3, 3) = 7`, menos que la pesimista. -/
example : caminosLibres 3 3 1 = 7 := by decide

/-- La cota del binomial con `r = 3`: `27^3 = 19683 ≤ 7 · 64 · 84`. -/
example : 27 ^ 3 ≤ (2 * 3 + 1) * 4 ^ 3 * (3 * 3).choose 3 := by decide

/-- En el ejemplo, desde distancia 1 con 3 pasos de 3 elecciones, aciertan al menos `C(3, 1) · 2 = 6` de 27. -/
example : 6 ≤ aciertos tresDos 3 3 ![true, false] := by decide

end Tiempo
end Sagitta.Map
