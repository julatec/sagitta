import Sagitta.Map.ConservacionTrabajo
import Sagitta.Map.AlgoritmosACotas

/-!
# La conservación del trabajo, contra el azar (el principio minimax de Yao)

En `ConservacionTrabajo.lean` la conservación vale para algoritmos deterministas: llenar una tabla y después consultarla
cuesta, sumado, al menos `|α|` preguntas para decidir «¿hay una opción buena?» en caja negra. Aquí se le da azar al
algoritmo y se ve que no esquiva la cuenta.

## El modelo

* **Un algoritmo aleatorio** es una familia de deterministas indexada por semillas: `A : ι → Pregunta α` y un conjunto
  finito no vacío de semillas `S : Finset ι`, con la semilla uniforme sobre `S`. La esperanza sobre la semilla es el
  promedio finito `prom S x = (∑ r ∈ S, x r) / |S|`, en `ℚ`. No hay teoría de la medida.
* **Una distribución sobre entradas** es un tipo finito `κ`, entradas `ent : κ → α → Bool` y pesos `w : κ → ℚ` no
  negativos que suman `1`.
* **Errar** es responder distinto de un objetivo `obj : (α → Bool) → Bool`; aquí casi siempre `existe f`, «¿hay una
  opción buena?». El indicador del error, `errQ`, vale `0` o `1`.

## Qué se prueba

1. **Yao, la dirección fácil** (`yao_facil`, `yao_peor_entrada`, `yao_error`). Para toda distribución sobre entradas y
   todo algoritmo aleatorio hay una semilla cuyo determinista cuesta, en promedio bajo la distribución, a lo sumo el
   costo esperado del aleatorio en su peor entrada. Con error: si el aleatorio erra con probabilidad `≤ ε` en toda
   entrada, hay un determinista de su soporte que erra con probabilidad `≤ ε` bajo la distribución. Es una sola cuenta
   (`yao_abstracto`): el promedio sobre semillas del promedio sobre entradas es el promedio sobre entradas del promedio
   sobre semillas (`prom_pesado`), y algo está por debajo de su promedio.
2. **Las Vegas** (`las_vegas`, `las_vegas_prom`). Si el aleatorio no erra nunca (probabilidad de error `0` en toda
   entrada), **cada** semilla decide, y cada una pregunta las `|α|` opciones en la entrada nula. El azar sin error no
   ahorra ni una pregunta, con ninguna semilla.
3. **Monte Carlo** (`error_mu`, `monte_carlo`, `monte_carlo_existe`). Con `μ = ½ nula + ½ indicador uniforme`
   (`muYao`), todo determinista que pregunta `q` veces en la nula erra con probabilidad al menos `½ (1 − q/|α|)` bajo
   `μ`. Conclusión: si el aleatorio erra con probabilidad `≤ ε` en toda entrada, su costo **esperado en la nula** es al
   menos `(1 − 2ε)|α|`:
   `prom S (fun r => costo (A r) nula) ≥ (1 − 2ε) |α|`, y por eso alguna semilla pregunta al menos eso.
   La forma que salió es sobre la esperanza (no solo sobre una semilla): se promedia la cota determinista sobre las
   semillas, que es lineal en `q`.
4. **La conservación con azar** (`trabajo_se_conserva_azar`). Llenado aleatorio `L r` más consulta aleatoria `Q r`,
   con error `≤ ε` en toda entrada: el promedio sobre semillas de `(preguntas del llenado) + (preguntas de la consulta)`
   en la nula es al menos `(1 − 2ε)|α|`.
5. **Los controles de que la cota es justa o casi.**
   * El muestreador (`muestreador`), que pregunta `q` puntos elegidos al azar (un subconjunto uniforme de tamaño `q`) y
     responde «sí» si vio un `1`, erra con probabilidad a lo sumo `1 − q/|α|` en toda entrada
     (`muestreador_error_le`) y exactamente `1 − q/|α|` en cada indicador (`muestreador_error_indicador`), que es su
     peor caso; pregunta `q` veces en la nula (`muestreador_costo_nula`). Con `ε = 1 − q/|α|` la cota de la meta 3 da
     `2q − |α| ≤ q`: el muestreador está a un factor 2 **en el error**, no en el costo.
   * Ese factor se cierra mezclando: con `α = Fin 3`, `ε = 1/4`, la mezcla `mezcla3` («sí» a ciegas con una semilla de
     cuatro, y los tres pares de opciones con las otras tres) erra a lo sumo `1/4` en toda entrada y su costo esperado en
     la nula es `3/2 = (1 − 2·¼)·3` (`mezcla3_justa`). **La cota de la meta 3 se alcanza exactamente.**
   * Y no se puede mejorar a `(1 − ε)|α|` (`no_vale_uno_menos_eps`): la misma mezcla la refuta.

## La lectura

El trabajo se conserva también contra el azar. Un algoritmo aleatorio es un promedio de deterministas; cada uno paga en
la entrada nula lo que no pregunta con errores en los indicadores, y el promedio hereda la cuenta. Lo único que compra el
azar es convertir preguntas en probabilidad de error, con la cota lineal `(1 − 2ε)|α|`: para equivocarse poco hay que
preguntar casi todo, y sin equivocarse (Las Vegas) hay que preguntar todo con cada semilla.

## Lo que NO se prueba

* Que la cota `(1 − 2ε)|α|` sea justa en general: se alcanza exactamente solo en el caso probado `|α| = 3`, `ε = 1/4`
  (`mezcla3_justa`). La mezcla general (decir «sí» a ciegas con probabilidad `ε` y muestrear el resto) la alcanzaría
  salvo redondeo, pero no está formalizada.
* Es **caja negra** y **relativiza**: el oráculo `f : α → Bool` solo se conoce preguntando. Por Baker, Gill y Solovay
  (1975), un argumento así no dice nada de una fórmula dada por su texto. Lo que agrega este archivo es solo que el azar
  no esquiva la conservación en ese modelo.
* No se prueba la otra dirección de Yao (el minimax con igualdad, que requiere el teorema de von Neumann o dualidad
  lineal); solo la desigualdad fácil, que es la que da cotas inferiores.
* El modelo de azar es una familia finita de semillas equiprobables. Pesos racionales arbitrarios sobre semillas se
  reducen a eso repitiendo semillas, pero no se formaliza; no hay azar infinito ni algoritmos que no terminan.
* La cota de la meta 3 es sobre el costo en la nula (el caso difícil), no sobre el costo en toda entrada; en las otras
  entradas un algoritmo puede parar antes.
* Fuente, de memoria y sin verificar: A. C. Yao, «Probabilistic computations: toward a unified measure of complexity»,
  FOCS 1977.
-/

namespace Sagitta.Map.Tiempo.ConservacionDual

open Sagitta.Map.Tiempo
open Sagitta.Map.Tiempo.ConservacionTrabajo
open Sagitta.Map.Tiempo.AlgoritmosACotas
open Pregunta Llenado

/-! ## Promedios finitos -/

/-- **El promedio** de `x` sobre el conjunto finito de semillas `S`: la esperanza con la semilla uniforme. -/
def prom {ι : Type} (S : Finset ι) (x : ι → ℚ) : ℚ := (∑ r ∈ S, x r) / S.card

theorem prom_mul_card {ι : Type} {S : Finset ι} (hS : S.Nonempty) (x : ι → ℚ) :
    prom S x * S.card = ∑ r ∈ S, x r := by
  have : (S.card : ℚ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  rw [prom, div_mul_cancel₀ _ this]

/-- **Lo que está por debajo de su promedio**: en un conjunto no vacío, algún valor es a lo sumo el promedio. -/
theorem existe_bajo_prom {ι : Type} {S : Finset ι} (hS : S.Nonempty) (x : ι → ℚ) : ∃ r ∈ S, x r ≤ prom S x := by
  apply Finset.exists_le_of_sum_le hS
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm, prom_mul_card hS]

/-- **Promediar sobre semillas y sobre entradas conmuta**: el promedio sobre semillas del costo pesado por `w` es el
promedio pesado del costo esperado de cada entrada. -/
theorem prom_pesado {ι κ : Type} [Fintype κ] (S : Finset ι) (w : κ → ℚ) (c : ι → κ → ℚ) :
    prom S (fun r => ∑ k, w k * c r k) = ∑ k, w k * prom S (fun r => c r k) := by
  simp only [prom, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => ?_
  ring

/-! ## 1. Yao, la dirección fácil -/

/-- **Yao en abstracto.** `c r k` es el costo (o el error) de la semilla `r` en la entrada `k`. Si el costo esperado
sobre semillas es `≤ M` en toda entrada, hay una semilla cuyo costo esperado bajo los pesos `w` es `≤ M`. -/
theorem yao_abstracto {ι κ : Type} [Fintype κ] {S : Finset ι} (hS : S.Nonempty) (w : κ → ℚ)
    (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (c : ι → κ → ℚ) (M : ℚ)
    (hM : ∀ k, prom S (fun r => c r k) ≤ M) : ∃ r ∈ S, ∑ k, w k * c r k ≤ M := by
  obtain ⟨r, hr, hle⟩ := existe_bajo_prom hS (fun r => ∑ k, w k * c r k)
  refine ⟨r, hr, hle.trans ?_⟩
  rw [prom_pesado]
  calc ∑ k, w k * prom S (fun r => c r k) ≤ ∑ k, w k * M :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hM k) (hw k)
    _ = M := by rw [← Finset.sum_mul, hw1, one_mul]

variable {α : Type}

/-- **Yao, costo.** Si el algoritmo aleatorio `A` (semillas en `S`) tiene costo esperado `≤ M` en toda entrada, alguna
de sus semillas, como determinista, tiene costo esperado `≤ M` bajo la distribución `(ent, w)`. -/
theorem yao_facil {ι κ : Type} [Fintype κ] {S : Finset ι} (hS : S.Nonempty) (A : ι → Pregunta α)
    (ent : κ → α → Bool) (w : κ → ℚ) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (M : ℚ)
    (hM : ∀ f, prom S (fun r => (costo (A r) f : ℚ)) ≤ M) :
    ∃ r ∈ S, ∑ k, w k * (costo (A r) (ent k) : ℚ) ≤ M :=
  yao_abstracto hS w hw hw1 (fun r k => (costo (A r) (ent k) : ℚ)) M fun k => hM (ent k)

/-- **Yao en la forma del enunciado**: el costo esperado en la peor entrada (el máximo, sobre todas las entradas
`k : κ`, incluidas las de peso 0, del costo esperado sobre semillas) es al menos el mínimo, sobre las semillas, del costo esperado bajo `w`. -/
theorem yao_peor_entrada {ι κ : Type} [Fintype κ] [Nonempty κ] {S : Finset ι} (hS : S.Nonempty)
    (A : ι → Pregunta α) (ent : κ → α → Bool) (w : κ → ℚ) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) :
    S.inf' hS (fun r => ∑ k, w k * (costo (A r) (ent k) : ℚ)) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun k => prom S (fun r => (costo (A r) (ent k) : ℚ))) := by
  obtain ⟨r, hr, hle⟩ := yao_abstracto hS w hw hw1 (fun r k => (costo (A r) (ent k) : ℚ))
    (Finset.univ.sup' Finset.univ_nonempty (fun k => prom S (fun r => (costo (A r) (ent k) : ℚ))))
    fun k => Finset.le_sup' (fun k => prom S (fun r => (costo (A r) (ent k) : ℚ))) (Finset.mem_univ k)
  exact (Finset.inf'_le _ hr).trans hle

/-- **El indicador del error**: `1` si `t` responde distinto de `obj f`, `0` si acierta. -/
def errQ (obj : (α → Bool) → Bool) (t : Pregunta α) (f : α → Bool) : ℚ := if corre t f = obj f then 0 else 1

theorem errQ_nonneg (obj : (α → Bool) → Bool) (t : Pregunta α) (f : α → Bool) : 0 ≤ errQ obj t f := by
  unfold errQ; split <;> norm_num

/-- **Yao, error.** Si el aleatorio erra con probabilidad `≤ ε` en toda entrada, hay un determinista de su soporte que
erra con probabilidad `≤ ε` bajo la distribución. -/
theorem yao_error {ι κ : Type} [Fintype κ] {S : Finset ι} (hS : S.Nonempty) (A : ι → Pregunta α)
    (obj : (α → Bool) → Bool) (ent : κ → α → Bool) (w : κ → ℚ) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (ε : ℚ)
    (hε : ∀ f, prom S (fun r => errQ obj (A r) f) ≤ ε) :
    ∃ r ∈ S, ∑ k, w k * errQ obj (A r) (ent k) ≤ ε :=
  yao_abstracto hS w hw hw1 (fun r k => errQ obj (A r) (ent k)) ε fun k => hε (ent k)

/-! ## 2. Las Vegas: sin error, cada semilla pregunta todo -/

/-- **¿Hay una opción buena?**, como booleano. -/
def existe [Fintype α] (f : α → Bool) : Bool := decide (∃ i, f i = true)

theorem existe_eq_true [Fintype α] (f : α → Bool) : existe f = true ↔ ∃ i, f i = true := by simp [existe]

/-- Acertar siempre `existe` es `DecideExiste`. -/
theorem decideExiste_de [Fintype α] {t : Pregunta α} (h : ∀ f, corre t f = existe f) : DecideExiste t :=
  fun f => by rw [h f, existe_eq_true]

/-- **Error de probabilidad cero en toda entrada es acertar con cada semilla.** -/
theorem sin_error_cada_semilla {ι : Type} {S : Finset ι} (hS : S.Nonempty) (A : ι → Pregunta α)
    (obj : (α → Bool) → Bool) (h0 : ∀ f, prom S (fun r => errQ obj (A r) f) = 0) :
    ∀ r ∈ S, ∀ f, corre (A r) f = obj f := by
  intro r hr f
  have hc : (S.card : ℚ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hs : ∑ r ∈ S, errQ obj (A r) f = 0 := by
    have := h0 f; rw [prom, div_eq_zero_iff] at this; exact this.resolve_right hc
  have := (Finset.sum_eq_zero_iff_of_nonneg fun r _ => errQ_nonneg obj (A r) f).1 hs r hr
  unfold errQ at this
  split at this
  · assumption
  · norm_num at this

/-- **Las Vegas.** Todo aleatorio que no erra nunca pregunta, con **cada** semilla, las `|α|` opciones en la nula. -/
theorem las_vegas [Fintype α] [DecidableEq α] {ι : Type} {S : Finset ι} (hS : S.Nonempty) (A : ι → Pregunta α)
    (h0 : ∀ f, prom S (fun r => errQ existe (A r) f) = 0) :
    ∀ r ∈ S, Fintype.card α ≤ costo (A r) nula := fun r hr =>
  costo_adversario (A r) (decideExiste_de (sin_error_cada_semilla hS A existe h0 r hr))

/-- **Y en promedio**: el costo esperado en la nula es al menos `|α|`. -/
theorem las_vegas_prom [Fintype α] [DecidableEq α] {ι : Type} {S : Finset ι} (hS : S.Nonempty)
    (A : ι → Pregunta α) (h0 : ∀ f, prom S (fun r => errQ existe (A r) f) = 0) :
    (Fintype.card α : ℚ) ≤ prom S (fun r => (costo (A r) nula : ℚ)) := by
  obtain ⟨r, hr, hle⟩ := existe_bajo_prom hS (fun r => (costo (A r) nula : ℚ))
  refine le_trans ?_ hle
  exact_mod_cast las_vegas hS A h0 r hr

/-! ## 3. Monte Carlo: `μ = ½ nula + ½ indicador uniforme` -/

/-- **Las entradas de `μ`**: `none` es la nula, `some x` el indicador de `x`. -/
def entYao [DecidableEq α] : Option α → α → Bool
  | none => nula
  | some x => indicador x

/-- **Los pesos de `μ`**: `½` a la nula, `1/(2|α|)` a cada indicador. -/
def muYao [Fintype α] : Option α → ℚ
  | none => 1 / 2
  | some _ => 1 / (2 * Fintype.card α)

theorem muYao_nonneg [Fintype α] : ∀ k, 0 ≤ (muYao : Option α → ℚ) k
  | none => by norm_num [muYao]
  | some _ => by simp only [muYao]; positivity

theorem muYao_suma [Fintype α] [Nonempty α] : ∑ k, (muYao : Option α → ℚ) k = 1 := by
  rw [Fintype.sum_option]
  simp only [muYao, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

/-- **El determinista erra mucho bajo `μ` si pregunta poco.** Si `t` pregunta `q` veces en la nula, su probabilidad de
error bajo `μ` es al menos `½ (1 − q/|α|)`: o dice «sí» en la nula (y erra la mitad del peso), o deja `|α| − q` opciones
sin mirar y en cada indicador de esas dice «no». -/
theorem error_mu [Fintype α] [DecidableEq α] [Nonempty α] (t : Pregunta α) :
    1 / 2 * (1 - (costo t nula : ℚ) / Fintype.card α) ≤ ∑ k, muYao k * errQ existe t (entYao k) := by
  have hn : (0 : ℚ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [Fintype.sum_option]
  simp only [muYao, entYao]
  have hnul : existe (nula : α → Bool) = false := by simp [existe, nula]
  have hind : ∀ x : α, existe (indicador x) = true := fun x => (existe_eq_true _).2 ⟨x, by simp [indicador]⟩
  have hsum0 : 0 ≤ ∑ x : α, 1 / (2 * (Fintype.card α : ℚ)) * errQ existe t (indicador x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (by positivity) (errQ_nonneg _ _ _)
  have hq : (0 : ℚ) ≤ (costo t nula : ℚ) / Fintype.card α := by positivity
  cases hc : corre t nula
  · -- dice «no» en la nula: erra en cada indicador que no miró
    have he0 : errQ existe t nula = 0 := by simp [errQ, hc, hnul]
    rw [he0, mul_zero, zero_add, ← Finset.mul_sum]
    -- los no vistos son al menos |α| − q
    set V := (vistos t nula).toFinset
    have hV : (V.card : ℚ) ≤ costo t nula := by exact_mod_cast List.toFinset_card_le _
    have hlow : ((Finset.univ.filter fun x => x ∉ V).card : ℚ) ≤ ∑ x : α, errQ existe t (indicador x) := by
      rw [← Finset.sum_boole]
      refine Finset.sum_le_sum fun x _ => ?_
      split
      · rename_i hx
        have hcx : corre t (indicador x) = false := by
          rw [← hc]; symm
          exact corre_congr t _ _ fun j hj => by
            have : j ≠ x := fun e => hx (List.mem_toFinset.2 (e ▸ hj))
            simp [nula, indicador, this]
        simp [errQ, hcx, hind x]
      · exact errQ_nonneg _ _ _
    have hcard : (Fintype.card α : ℚ) ≤ (Finset.univ.filter fun x => x ∉ V).card + V.card := by
      have : (Finset.univ : Finset α) ⊆ (Finset.univ.filter fun x => x ∉ V) ∪ V := by
        intro x _; by_cases hx : x ∈ V <;> simp [hx]
      have := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
      rw [Finset.card_univ] at this
      exact_mod_cast this
    have hE : (Fintype.card α : ℚ) - costo t nula ≤ ∑ x : α, errQ existe t (indicador x) := by linarith
    calc (1 : ℚ) / 2 * (1 - (costo t nula : ℚ) / Fintype.card α)
        = 1 / (2 * Fintype.card α) * ((Fintype.card α : ℚ) - costo t nula) := by field_simp
      _ ≤ 1 / (2 * Fintype.card α) * ∑ x : α, errQ existe t (indicador x) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
  · -- dice «sí» en la nula: erra la mitad del peso
    have he1 : errQ existe t nula = 1 := by simp [errQ, hc, hnul]
    rw [he1]
    nlinarith

/-- **Monte Carlo.** Si el aleatorio `A` erra con probabilidad `≤ ε` en toda entrada, su costo esperado en la nula es
al menos `(1 − 2ε)|α|`. -/
theorem monte_carlo [Fintype α] [DecidableEq α] [Nonempty α] {ι : Type} {S : Finset ι} (hS : S.Nonempty)
    (A : ι → Pregunta α) (ε : ℚ) (hε : ∀ f, prom S (fun r => errQ existe (A r) f) ≤ ε) :
    (1 - 2 * ε) * Fintype.card α ≤ prom S (fun r => (costo (A r) nula : ℚ)) := by
  have hn : (0 : ℚ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hcS : (0 : ℚ) < S.card := by exact_mod_cast hS.card_pos
  -- el promedio sobre semillas del error bajo μ es ≤ ε
  have hmu : prom S (fun r => ∑ k, muYao k * errQ existe (A r) (entYao k)) ≤ ε := by
    rw [prom_pesado]
    calc ∑ k, muYao k * prom S (fun r => errQ existe (A r) (entYao k)) ≤ ∑ k, (muYao : Option α → ℚ) k * ε :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hε _) (muYao_nonneg k)
      _ = ε := by rw [← Finset.sum_mul, muYao_suma, one_mul]
  -- y es al menos el promedio de ½(1 − q_r/|α|)
  set P := prom S (fun r => (costo (A r) nula : ℚ)) with hP
  set n : ℚ := (Fintype.card α : ℚ)
  set c : ℚ := (S.card : ℚ)
  have hlow : ∑ r ∈ S, 1 / 2 * (1 - (costo (A r) nula : ℚ) / n) ≤
      ∑ r ∈ S, ∑ k, muYao k * errQ existe (A r) (entYao k) :=
    Finset.sum_le_sum fun r _ => error_mu (A r)
  have hsplit : ∑ r ∈ S, 1 / 2 * (1 - (costo (A r) nula : ℚ) / n) = 1 / 2 * c - P * c / (2 * n) := by
    have ht : ∀ r, (1 : ℚ) / 2 * (1 - (costo (A r) nula : ℚ) / n) = 1 / 2 - 1 / (2 * n) * costo (A r) nula :=
      fun r => by field_simp
    simp_rw [ht]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hP, prom_mul_card hS]
    ring
  rw [hsplit, ← prom_mul_card hS] at hlow
  have hA := mul_le_mul_of_nonneg_right hmu hcS.le
  have h1 : c * (1 / 2 - P / (2 * n)) ≤ c * ε := by
    have : c * (1 / 2 - P / (2 * n)) = 1 / 2 * c - P * c / (2 * n) := by ring
    rw [this]; linarith
  have h2 : 1 / 2 - ε ≤ P / (2 * n) := by
    have := le_of_mul_le_mul_left h1 hcS; linarith
  rw [le_div_iff₀ (by positivity)] at h2
  linarith

/-- **Alguna semilla pregunta al menos `(1 − 2ε)|α|`** en la nula. -/
theorem monte_carlo_existe [Fintype α] [DecidableEq α] [Nonempty α] {ι : Type} {S : Finset ι} (hS : S.Nonempty)
    (A : ι → Pregunta α) (ε : ℚ) (hε : ∀ f, prom S (fun r => errQ existe (A r) f) ≤ ε) :
    ∃ r ∈ S, (1 - 2 * ε) * Fintype.card α ≤ (costo (A r) nula : ℚ) := by
  by_contra h
  push Not at h
  have hlt : prom S (fun r => (costo (A r) nula : ℚ)) < (1 - 2 * ε) * Fintype.card α := by
    have hs : ∑ r ∈ S, (costo (A r) nula : ℚ) < ∑ r ∈ S, (1 - 2 * ε) * (Fintype.card α : ℚ) :=
      Finset.sum_lt_sum_of_nonempty hS h
    rw [Finset.sum_const, nsmul_eq_mul, ← prom_mul_card hS] at hs
    have hcS : (0 : ℚ) < S.card := by exact_mod_cast hS.card_pos
    nlinarith
  exact absurd (monte_carlo hS A ε hε) (not_le.2 hlt)

/-! ## 4. La conservación con azar -/

/-- **El trabajo se conserva contra el azar.** Llenado aleatorio y consulta aleatoria (las dos pueden depender de la
semilla), con error `≤ ε` en toda entrada: el promedio sobre semillas de lo preguntado al llenar más lo preguntado al
consultar, en la nula, es al menos `(1 − 2ε)|α|`. -/
theorem trabajo_se_conserva_azar [Fintype α] [DecidableEq α] [Nonempty α] {ι τ : Type} {S : Finset ι}
    (hS : S.Nonempty) (L : ι → Llenado α τ) (Q : ι → τ → Pregunta α) (ε : ℚ)
    (hε : ∀ f, prom S (fun r => errQ existe (encadenar (L r) (Q r)) f) ≤ ε) :
    (1 - 2 * ε) * Fintype.card α ≤
      prom S (fun r => ((costoLl (L r) nula + costo (Q r (tablaDe (L r) nula)) nula : ℕ) : ℚ)) := by
  have := monte_carlo hS (fun r => encadenar (L r) (Q r)) ε hε
  simpa only [costo_encadenar] using this

/-- **Con `ε = 0` se recupera la conservación determinista** (para cada semilla). -/
theorem trabajo_se_conserva_sin_error [Fintype α] [DecidableEq α] {ι τ : Type} {S : Finset ι}
    (hS : S.Nonempty) (L : ι → Llenado α τ) (Q : ι → τ → Pregunta α)
    (h0 : ∀ f, prom S (fun r => errQ existe (encadenar (L r) (Q r)) f) = 0) :
    ∀ r ∈ S, Fintype.card α ≤ costoLl (L r) nula + costo (Q r (tablaDe (L r) nula)) nula := fun r hr =>
  trabajo_se_conserva (L r) (Q r) (decideExiste_de (sin_error_cada_semilla hS _ existe h0 r hr))

/-! ## 5. Los controles -/

/-! ### El muestreador -/

/-- **El muestreador**: con la semilla `s` (un subconjunto de opciones), pregunta las de `s` y dice «sí» si vio un `1`. -/
noncomputable def muestreador (s : Finset α) : Pregunta α := barrer s.toList

/-- Sus semillas: los subconjuntos de tamaño `q`, uniformes. -/
def semillasQ [Fintype α] (q : ℕ) : Finset (Finset α) := Finset.powersetCard q Finset.univ

theorem semillasQ_nonempty [Fintype α] {q : ℕ} (hq : q ≤ Fintype.card α) : (semillasQ (α := α) q).Nonempty :=
  Finset.powersetCard_nonempty.2 (by simpa using hq)

theorem corre_muestreador (s : Finset α) (f : α → Bool) :
    corre (muestreador s) f = true ↔ ∃ i ∈ s, f i = true := by
  simp [muestreador, corre_barrer]

/-- **Pregunta `q` veces en la nula** (y a lo sumo `q` en cualquier entrada). -/
theorem muestreador_costo_nula [Fintype α] {q : ℕ} {s : Finset α} (hs : s ∈ semillasQ q) :
    costo (muestreador s) nula = q ∧ ∀ f, costo (muestreador s) f ≤ q := by
  classical
  have hc : s.card = q := (Finset.mem_powersetCard.1 hs).2
  have hle : ∀ f, costo (muestreador s) f ≤ q := fun f => by
    simpa [muestreador, hc] using costo_barrer f s.toList
  refine ⟨le_antisymm (hle _) ?_, hle⟩
  -- en la nula barre la lista entera
  have : ∀ l : List α, costo (barrer l) nula = l.length := by
    intro l; induction l with
    | nil => rfl
    | cons i l ih => simpa [costo, barrer, vistos, nula] using ih
  simp [muestreador, this, hc]

/-- Los subconjuntos de tamaño `q` que no tocan `x` son los de `α ∖ {x}`. -/
theorem filtro_sin_x [Fintype α] [DecidableEq α] (q : ℕ) (x : α) :
    (semillasQ q).filter (fun s => x ∉ s) = Finset.powersetCard q (Finset.univ.erase x) := by
  ext s
  simp [semillasQ, Finset.mem_powersetCard, Finset.subset_erase, and_comm]

/-- **El error en un indicador** es la fracción de semillas que no lo tocan. -/
theorem muestreador_error_indicador [Fintype α] [DecidableEq α] [Nonempty α] {q : ℕ} (hq : q ≤ Fintype.card α) (x : α) :
    prom (semillasQ q) (fun s => errQ existe (muestreador s) (indicador x)) =
      1 - (q : ℚ) / Fintype.card α := by
  have hind : existe (indicador x) = true := (existe_eq_true _).2 ⟨x, by simp [indicador]⟩
  have herr : ∀ s : Finset α, errQ existe (muestreador s) (indicador x) = if x ∉ s then 1 else 0 := by
    intro s
    by_cases hx : x ∈ s
    · have : corre (muestreador s) (indicador x) = true := (corre_muestreador s _).2 ⟨x, hx, by simp [indicador]⟩
      simp [errQ, this, hind, hx]
    · have : corre (muestreador s) (indicador x) = false := by
        cases h : corre (muestreador s) (indicador x)
        · rfl
        · obtain ⟨i, hi, hfi⟩ := (corre_muestreador s _).1 h
          simp [indicador] at hfi; exact absurd (hfi ▸ hi) hx
      simp [errQ, this, hind, hx]
  simp only [prom, herr]
  rw [Finset.sum_boole, filtro_sin_x, Finset.card_powersetCard, semillasQ, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card α = m + 1 := Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  rw [hm, Nat.add_sub_cancel]
  have hid := Nat.choose_mul_succ_eq m q
  have hpos : 0 < (m + 1).choose q := Nat.choose_pos (by omega)
  have hqm : q ≤ m + 1 := by omega
  have hidQ : ((m.choose q : ℕ) : ℚ) * (m + 1) = ((m + 1).choose q : ℚ) * ((m + 1 : ℚ) - q) := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hid
    push_cast [Nat.cast_sub hqm] at this
    exact this
  have h1 : ((m + 1).choose q : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have h2 : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast at h2 ⊢
  field_simp
  linarith [hidQ]

/-- **Y ese es el peor caso**: en toda entrada el muestreador erra con probabilidad a lo sumo `1 − q/|α|`. Si no hay
`1`, nunca erra; si hay un `1` en `x`, solo erra cuando la semilla no toca `x`. -/
theorem muestreador_error_le [Fintype α] [DecidableEq α] {q : ℕ} (hq : q ≤ Fintype.card α) (f : α → Bool) :
    prom (semillasQ q) (fun s => errQ existe (muestreador s) f) ≤ 1 - (q : ℚ) / Fintype.card α := by
  by_cases hf : ∃ x, f x = true
  · obtain ⟨x, hx⟩ := hf
    have : Nonempty α := ⟨x⟩
    rw [← muestreador_error_indicador hq x]
    unfold prom
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases hxs : x ∈ s
    · have : corre (muestreador s) f = existe f := by
        rw [(corre_muestreador s f).2 ⟨x, hxs, hx⟩, eq_comm, existe_eq_true]; exact ⟨x, hx⟩
      simp only [errQ, this, ite_true]; exact errQ_nonneg _ _ _
    · have : corre (muestreador s) (indicador x) = false := by
        cases h : corre (muestreador s) (indicador x)
        · rfl
        · obtain ⟨i, hi, hfi⟩ := (corre_muestreador s _).1 h
          simp [indicador] at hfi; exact absurd (hfi ▸ hi) hxs
      have hind : existe (indicador x) = true := (existe_eq_true _).2 ⟨x, by simp [indicador]⟩
      simp only [errQ, this, hind]
      split <;> norm_num
  · have hfalse : existe f = false := by
      cases h : existe f
      · rfl
      · exact absurd ((existe_eq_true f).1 h) hf
    have : ∀ s : Finset α, errQ existe (muestreador s) f = 0 := by
      intro s
      have : corre (muestreador s) f = false := by
        cases h : corre (muestreador s) f
        · rfl
        · obtain ⟨i, -, hi⟩ := (corre_muestreador s f).1 h; exact absurd ⟨i, hi⟩ hf
      simp [errQ, this, hfalse]
    simp only [prom, this, Finset.sum_const_zero, zero_div, sub_nonneg]
    rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
    · simp [h0]
    · rw [div_le_one (by exact_mod_cast hpos)]; exact_mod_cast hq

/-- **La cota de la meta 3 aplicada al muestreador** no se contradice: con `ε = 1 − q/|α|` da `2q − |α| ≤ q`. -/
theorem muestreador_respeta_cota [Fintype α] [DecidableEq α] [Nonempty α] {q : ℕ} (hq : q ≤ Fintype.card α) :
    (1 - 2 * (1 - (q : ℚ) / Fintype.card α)) * Fintype.card α ≤
      prom (semillasQ (α := α) q) (fun s => (costo (muestreador s) nula : ℚ)) :=
  monte_carlo (semillasQ_nonempty hq) _ _ (muestreador_error_le hq)

/-! ### La cota exacta: una mezcla con `|α| = 3`, `ε = 1/4` -/

/-- **La mezcla**: con la semilla `0` dice «sí» sin preguntar; con las otras tres barre uno de los tres pares. -/
def mezcla3 : Fin 4 → Pregunta (Fin 3)
  | 0 => .resp true
  | 1 => barrer [0, 1]
  | 2 => barrer [0, 2]
  | 3 => barrer [1, 2]

theorem mezcla3_errores : ∀ f : Fin 3 → Bool,
    (Finset.univ.filter fun r => corre (mezcla3 r) f ≠ existe f).card ≤ 1 := by decide

theorem mezcla3_costos : ∑ r, costo (mezcla3 r) nula = 6 := by decide

theorem prom_errQ_card {ι : Type} [Fintype ι] (A : ι → Pregunta α) (obj : (α → Bool) → Bool) (f : α → Bool) :
    prom Finset.univ (fun r => errQ obj (A r) f) =
      ((Finset.univ.filter fun r => corre (A r) f ≠ obj f).card : ℚ) / Fintype.card ι := by
  unfold prom errQ
  rw [Finset.card_univ]
  congr 1
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : corre (A r) f = obj f <;> simp [h]

/-- **La cota `(1 − 2ε)|α|` se alcanza exactamente**: la mezcla erra a lo sumo `1/4` en toda entrada y su costo
esperado en la nula es `3/2 = (1 − 2·¼)·3`. -/
theorem mezcla3_justa :
    (∀ f, prom Finset.univ (fun r => errQ existe (mezcla3 r) f) ≤ 1 / 4) ∧
      prom Finset.univ (fun r => (costo (mezcla3 r) nula : ℚ)) = (1 - 2 * (1 / 4)) * Fintype.card (Fin 3) := by
  refine ⟨fun f => ?_, ?_⟩
  · rw [prom_errQ_card]
    have := mezcla3_errores f
    simp only [Fintype.card_fin]
    have : ((Finset.univ.filter fun r => corre (mezcla3 r) f ≠ existe f).card : ℚ) ≤ 1 := by exact_mod_cast this
    linarith
  · unfold prom
    rw [← Nat.cast_sum, mezcla3_costos]
    simp
    norm_num

/-- **La cota de la meta 3 no se mejora a `(1 − ε)|α|`**: la mezcla, con error `1/4`, cuesta `3/2 < (1 − ¼)·3`. -/
theorem no_vale_uno_menos_eps :
    ¬ ∀ (ι : Type) (S : Finset ι), S.Nonempty → ∀ (A : ι → Pregunta (Fin 3)) (ε : ℚ),
      (∀ f, prom S (fun r => errQ existe (A r) f) ≤ ε) →
        (1 - ε) * Fintype.card (Fin 3) ≤ prom S (fun r => (costo (A r) nula : ℚ)) := by
  intro h
  have := h (Fin 4) Finset.univ Finset.univ_nonempty mezcla3 (1 / 4) mezcla3_justa.1
  rw [mezcla3_justa.2] at this
  norm_num at this

/-- **Control: la hipótesis de Monte Carlo no es vacía.** El barrido determinista (una sola semilla) erra `0` y cuesta
`|α|`; la cota con `ε = 0` es justa. -/
theorem barrer_una_semilla [Fintype α] [DecidableEq α] :
    (∀ f, prom ({()} : Finset Unit) (fun _ => errQ existe (barrer (Finset.univ : Finset α).toList) f) = 0) ∧
      prom ({()} : Finset Unit) (fun _ => (costo (barrer (Finset.univ : Finset α).toList) nula : ℚ)) =
        Fintype.card α := by
  have hd := (barrer_alcanza (α := α))
  refine ⟨fun f => ?_, ?_⟩
  · have : corre (barrer (Finset.univ : Finset α).toList) f = existe f := by
      cases h : existe f
      · cases h' : corre (barrer (Finset.univ : Finset α).toList) f
        · rfl
        · exact absurd ((existe_eq_true f).2 ((hd.1 f).1 h')) (by simp [h])
      · exact (hd.1 f).2 ((existe_eq_true f).1 h)
    simp [prom, errQ, this]
  · have h1 := hd.2 nula
    have h2 := costo_adversario _ hd.1
    simp only [prom, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, div_one]
    exact_mod_cast le_antisymm h1 h2

end Sagitta.Map.Tiempo.ConservacionDual
