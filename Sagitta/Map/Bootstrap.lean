import Sagitta.Map.KtSAT
import Sagitta.Map.IntercambioAlternancias
import Sagitta.Map.BlumExiste
import Mathlib.Computability.Halting

/-!
# Cuatro bootstraps: construir, certificar, anidar, mejorar

## La pregunta

José preguntó (24 nov 2026): «¿quién dice que construir el resolvedor no es resolver el mismo problema?». Y después:
«suena a un bootstrap por contradicción». La respuesta que se formaliza aquí es que hay **dos** bootstraps distintos, y
que la diferencia entre ellos es exactamente la diferencia entre *construir* y *certificar*:

* **Construir el resolvedor, implícitamente, es resolver, y es consistente.** La búsqueda de Levin no sabe de antemano
  qué programa resuelve SAT: lo construye mientras resuelve, en la misma corrida. El costo de «construir» (el factor
  `2^i` de escribir el programa `i` que imita) queda adentro de la ejecución de un único programa `L`, como cota de
  `costoLevin` contra todo proceso correcto (`construir_es_resolver`). Suponer el resolvedor y usarlo para construirse
  no lleva a contradicción: el resolvedor existe (`bootstrap_construye_consistente`).
* **Certificar el resolvedor es más difícil, y su bootstrap sí es contradictorio.** Si un programa pudiera decidir, dado
  un código `c`, «`c` resuelve la búsqueda de SAT», el programa que se consulta a sí mismo y hace lo contrario lleva al
  absurdo (`no_hay_certificador`, por Rice de Mathlib; `no_hay_certificador_diagonal`, la diagonal escrita a mano con el
  teorema de recursión `fixed_point₂`).

## La tabla de los cuatro bootstraps

| bootstrap | qué se supone | resultado | teorema |
|---|---|---|---|
| **construir** | hay un resolvedor; usarlo para construirse | consistente: Levin construye y resuelve en la misma corrida | `construir_es_resolver`, `bootstrap_construye_consistente` |
| **certificar** | hay un programa que decide «`c` resuelve SAT» | contradicción (Rice, la diagonal) | `no_hay_certificador`, `no_hay_certificador_diagonal` |
| **anidar** | usar el supuesto `SupuestoSAT` `k` veces | exponente `b · c^k`; contradicción **solo** con las reglas de memoria chica y `c < √2` | `anidar_k_veces`, `anidar_fijo_no_contradice`, `anidar_con_memoria_contradice` |
| **mejorar** | mejorar el resolvedor con el resolvedor | en general sin punto fijo óptimo (Blum); en la búsqueda de SAT, punto fijo: Levin, salvo constante | `mejorar_sin_punto_fijo`, `busqueda_tiene_punto_fijo` |

## La propiedad semántica

`ResuelveBusquedaSAT c` es `ResuelveSAT (eval c)`, con
`ResuelveSAT f := ∀ F, Satisfacible F → ∃ y ∈ f (encode F), vSAT (encode F) y = true`: sobre la codificación de toda
fórmula satisfacible, la función parcial termina y entrega una asignación que `vSAT` acepta. Es **semántica** porque
está definida a través de `eval c` y nada más: dos códigos con la misma `eval` la cumplen o no a la vez
(`resuelve_extensional`). Eso es justo lo que pide `ComputablePred.rice`: un conjunto `C` de funciones parciales y la
pregunta `eval c ∈ C`. No se pide nada en las fórmulas insatisfacibles (ni que el programa no termine, ni qué
entrega): la propiedad es la de **búsqueda**, no la de decisión.

## Controles

* La propiedad no es trivial: el código de Levin la cumple y el que nunca termina no (`resuelve_no_trivial`).
* Para **un solo código fijo** sí hay certificador (una constante, `certificador_de_un_codigo`): lo imposible es el
  certificador **uniforme**.
* Una propiedad **sintáctica** (`c = L`, del código y no de la función) sí es decidible (`sintactica_decidible`), y no
  es extensional (`sintactica_no_extensional`): por eso Rice no la alcanza.
* Los mutantes refutados aquí mismo: «el bootstrap que construye da contradicción» (`mutante_construir_contradice`),
  «anidar sin las reglas contradice» (`mutante_anidar_sin_reglas`), «anidar con `c ≥ √2` y `k` arbitrario contradice»
  (`mutante_anidar_k_no_acotado`). El mutante «hay certificador» es la negación de `no_hay_certificador`.

## Lo que NO se prueba

* **Que P ≠ NP.** Ninguno de estos bootstraps lo da. El que da contradicción **no supone P = NP**: supone un
  *certificador* (decidir, dado un código, si resuelve SAT), y eso es imposible por computabilidad, sea cual sea la
  complejidad de SAT. Que el certificador no exista no dice nada de cuánto cuesta resolver.
* **Las medidas son las del proyecto**: rondas de la búsqueda (`costoLevin`) y presupuesto de `evaln` (`costo`, el de
  Blum), no tiempo de máquina. Y el punto fijo de la búsqueda es en rondas: no se probó que `costo L` (los pasos del
  propio programa de Levin) esté acotado por un múltiplo del de otro programa (ver `levin_es_programa`).
* **Rice es sobre computabilidad, no sobre complejidad.** `no_hay_certificador` vale igual para cualquier propiedad
  semántica no trivial; no usa nada de SAT salvo que hay una fórmula satisfacible y un programa que la resuelve.
* La anidación es la del juego (`IntercambioAlternancias.lean`): las reglas son hipótesis, no teoremas sobre máquinas.
* **Nada sobre P contra NP.**
-/

open Cslib Cslib.Logic.PL
open Nat.Partrec Nat.Partrec.Code
namespace Sagitta.Map.Tiempo.Bootstrap
open UniversoCerrado TerceraCuenta Sagitta.Map.Levin KtSAT AceleracionBlum CorteRacional

/-! ## 0. La propiedad semántica -/

/-- **Una función parcial resuelve la búsqueda de SAT**: sobre la codificación de toda fórmula satisfacible termina y
entrega una asignación que `vSAT` acepta. Es una propiedad de la función, no de un código. -/
def ResuelveSAT (f : ℕ →. ℕ) : Prop :=
  ∀ F : List Clausula, Satisfacible F → ∃ y ∈ f (Encodable.encode F), vSAT (Encodable.encode F) y = true

/-- **El código `c` resuelve la búsqueda de SAT**: su función `eval c` lo hace. -/
def ResuelveBusquedaSAT (c : Code) : Prop := ResuelveSAT (eval c)

/-- **Es semántica**: depende solo de `eval c`. -/
theorem resuelve_extensional {c d : Code} (h : eval c = eval d) :
    ResuelveBusquedaSAT c ↔ ResuelveBusquedaSAT d := by
  unfold ResuelveBusquedaSAT; rw [h]

/-- Hay alguna fórmula satisfacible. -/
theorem hay_satisfacible : ∃ F : List Clausula, Satisfacible F := by
  obtain ⟨F, hF, -⟩ := kt_no_acotado 0
  exact ⟨F, hF⟩

/-! ## 1. El bootstrap que construye: consistente -/

/-- **Construir el resolvedor (implícitamente) es resolver.** Hay un único código `L`, el mismo para todas las
fórmulas, que:
* resuelve la búsqueda de SAT y nunca entrega basura;
* para toda fórmula satisfacible `F` y **todo** proceso cerrado `(i, k)` que la resuelve, gasta en rondas menos que
  `8 · 2^i · k`: el `2^i` de construir (escribir) el programa `i` ya está pagado adentro de la corrida de `L`;
* lo mismo contra todo **código** `c` que entregue en `F` una asignación aceptada: menos que
  `8 · 2^(código de c) · costo c`.

`L` no sabe de antemano cuál `i` o cuál `c` sirve: los construye mientras resuelve. -/
theorem construir_es_resolver : ∃ L : Code, ResuelveBusquedaSAT L ∧
    (∀ x y, y ∈ eval L x → vSAT x y = true) ∧
    (∀ F, Satisfacible F → ∀ p : Proceso, Correcto (uSAT F) p →
      costoLevin vSAT (Encodable.encode F) < 8 * 2 ^ p.i * p.k) ∧
    (∀ F, Satisfacible F → ∀ (c : Code) (y : ℕ), y ∈ eval c (Encodable.encode F) →
      vSAT (Encodable.encode F) y = true →
      costoLevin vSAT (Encodable.encode F) < 8 * 2 ^ encodeCode c * costo c (Encodable.encode F)) := by
  obtain ⟨L, hL1, hL2⟩ := levin_es_programa_sat
  refine ⟨L, fun F hF => ?_, hL1, fun F _ p hp => ?_, fun F _ c y hy hV => ?_⟩
  · obtain ⟨hd, -⟩ := hL2 F hF
    exact ⟨_, Part.get_mem hd, hL1 _ _ (Part.get_mem hd)⟩
  · have := levin_contra_proceso hp
    simp only [Proceso.costoTotal] at this
    rw [mul_assoc]; exact this
  · have hp : Correcto (uSAT F) ⟨encodeCode c, costo c (Encodable.encode F)⟩ := ⟨y, correr_de_eval hy, hV⟩
    have := levin_contra_proceso hp
    simp only [Proceso.costoTotal] at this
    rw [mul_assoc]; exact this

/-- **El bootstrap que construye es consistente**: el supuesto «hay un resolvedor» no solo no se refuta, es verdad. -/
theorem bootstrap_construye_consistente : ∃ c : Code, ResuelveBusquedaSAT c := by
  obtain ⟨L, h, -⟩ := construir_es_resolver
  exact ⟨L, h⟩

/-! ## 2. El bootstrap que certifica: contradicción (Rice) -/

/-- El código que nunca termina. -/
theorem hay_codigo_vacio : ∃ c : Code, eval c = fun _ => Part.none :=
  exists_code.1 Nat.Partrec.none

/-- El que nunca termina no resuelve. -/
theorem vacio_no_resuelve {c : Code} (h : eval c = fun _ => Part.none) : ¬ ResuelveBusquedaSAT c := by
  intro hr
  obtain ⟨F, hF⟩ := hay_satisfacible
  obtain ⟨y, hy, -⟩ := hr F hF
  rw [h] at hy
  exact Part.notMem_none y hy

/-- **Control: la propiedad no es trivial**: hay códigos de los dos lados. -/
theorem resuelve_no_trivial : (∃ c, ResuelveBusquedaSAT c) ∧ ∃ c, ¬ ResuelveBusquedaSAT c := by
  obtain ⟨c, hc⟩ := hay_codigo_vacio
  exact ⟨bootstrap_construye_consistente, c, vacio_no_resuelve hc⟩

/-- **No hay certificador.** Ningún programa decide, dado un código `c`, si `c` resuelve la búsqueda de SAT. Es
`ComputablePred.rice` con `C = {f | ResuelveSAT f}`: si el certificador existiera, como el código de Levin está en `C`,
también estaría la función que nunca termina. -/
theorem no_hay_certificador : ¬ ComputablePred ResuelveBusquedaSAT := by
  intro h
  obtain ⟨L, hL, -⟩ := construir_es_resolver
  obtain ⟨c0, hc0⟩ := hay_codigo_vacio
  have hf : Nat.Partrec (eval L) := Partrec.nat_iff.1 (eval_part.comp (Computable.const L) Computable.id)
  have hmem := ComputablePred.rice {f | ResuelveSAT f} h hf Nat.Partrec.none hL
  have : ResuelveBusquedaSAT c0 := by
    show ResuelveSAT (eval c0)
    rw [hc0]; exact hmem
  exact vacio_no_resuelve hc0 this

/-- **El bootstrap por contradicción, escrito a mano.** Si `d` fuera un certificador computable, el teorema de recursión
(`fixed_point₂`) da un código `e` que se consulta a sí mismo: «si `d` dice que resuelvo, no termino nunca; si dice que
no, corro Levin». Si `d e = true`, `e` no termina y no resuelve; si `d e = false`, `e` es Levin y resuelve. Las dos
ramas contradicen a `d`. -/
theorem no_hay_certificador_diagonal :
    ¬ ∃ d : Code → Bool, Computable d ∧ ∀ c, d c = true ↔ ResuelveBusquedaSAT c := by
  rintro ⟨d, hd, hdc⟩
  obtain ⟨L, hL, -⟩ := construir_es_resolver
  have hf : Nat.Partrec (eval L) := Partrec.nat_iff.1 (eval_part.comp (Computable.const L) Computable.id)
  have hP : Partrec₂ fun (c : Code) (x : ℕ) => cond (d c) (Part.none : Part ℕ) (eval L x) :=
    (Partrec.cond (hd.comp Computable.fst) ((Partrec.nat_iff.2 Nat.Partrec.none).comp Computable.snd).to₂
      ((Partrec.nat_iff.2 hf).comp Computable.snd).to₂).to₂
  obtain ⟨e, he⟩ := fixed_point₂ hP
  cases hde : d e with
  | true =>
    have hr := (hdc e).1 hde
    have hev : eval e = fun _ => Part.none := by rw [he]; funext x; simp [hde]
    exact vacio_no_resuelve hev hr
  | false =>
    have hev : eval e = eval L := by rw [he]; funext x; simp [hde]
    have hr : ResuelveBusquedaSAT e := (resuelve_extensional hev).2 hL
    have := (hdc e).2 hr
    rw [hde] at this; exact Bool.false_ne_true this

/-- **Control: para un solo código fijo sí hay certificador** (una constante). Lo imposible es el uniforme. -/
theorem certificador_de_un_codigo (c0 : Code) :
    ∃ d : Code → Bool, Computable d ∧ (d c0 = true ↔ ResuelveBusquedaSAT c0) := by
  classical
  exact ⟨fun _ => decide (ResuelveBusquedaSAT c0), Computable.const _, by simp⟩

/-- **Control: una propiedad sintáctica sí es decidible**: «`c` es exactamente el código `c0`». -/
theorem sintactica_decidible (c0 : Code) : ComputablePred fun c : Code => c = c0 := by
  classical
  exact ComputablePred.computable_iff.2 ⟨fun c => decide (c = c0),
    (Primrec.eq.comp Primrec.id (Primrec.const c0)).decide.to_comp, by funext c; simp⟩

/-- **Y no es extensional**: `comp c0 id` hace lo mismo que `c0` y es otro código. Por eso Rice no la alcanza. -/
theorem sintactica_no_extensional (c0 : Code) :
    eval (Code.comp c0 Code.id) = eval c0 ∧ Code.comp c0 Code.id ≠ c0 := by
  refine ⟨?_, fun h => ?_⟩
  · funext n; simp only [eval, eval_id]; exact Part.bind_some n (eval c0)
  · have := (encode_lt_comp c0 Code.id).1
    rw [h] at this
    exact lt_irrefl _ this

/-! ## 3. La anidación, en el medio -/

open IntercambioAlternancias

/-- **Anidar el supuesto `k` veces**: Σ_{k+1}-TIME(n^b) ⊆ NTIME(n^{b · c^k}). Con `k` fijo, el exponente es un número
finito. Es `quitar_iterado`. -/
theorem anidar_k_veces {M : MundoClases} (R : ReglasLV M) {c : ℝ} (hc : 1 ≤ c) (hs : SupuestoSAT M c) (k : ℕ)
    {b : ℝ} (hb : 1 ≤ b) : M.Sigma (k + 1) b ⊆ M.NTIME (b * c ^ k) :=
  quitar_iterado R hc hs k b hb

/-- **Anidar un número fijo de veces no contradice.** Con `c ≥ √2` hay un mundo que cumple todas las reglas de memoria
chica, el supuesto con `c`, y en el que anidar `k` veces, para todo `k`, deja el exponente en `b · c^k`: ninguna
anidación llega a la contradicción. -/
theorem anidar_fijo_no_contradice {c : ℝ} (hc : √2 ≤ c) :
    ∃ M : MundoClases, ReglasLV M ∧ SupuestoSAT M c ∧
      ∀ k : ℕ, ∀ b : ℝ, 1 ≤ b → M.Sigma (k + 1) b ⊆ M.NTIME (b * c ^ k) := by
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hc0 : 0 ≤ c := h0.trans hc
  have hcc : 2 ≤ c * c := by nlinarith
  have hc1 : 1 ≤ c := by nlinarith
  have R := modeloUmbral_reglas hc0 hcc
  have hs := modeloUmbral_supuesto hc0
  exact ⟨_, R, hs, fun k b hb => quitar_iterado R hc1 hs k b hb⟩

/-- **Anidar con memoria chica y `c < √2` contradice**: en todo mundo con las reglas de Lipton–Viglas. -/
theorem anidar_con_memoria_contradice {c : ℝ} (hc : c < √2) :
    ∀ M : MundoClases, ReglasLV M → SupuestoSAT M c → False :=
  (umbral_lipton_viglas c).2 hc

/-- **Mutante refutado: sin las reglas, anidar no contradice**, ni con `c = 1`: el supuesto solo se cumple en un mundo. -/
theorem mutante_anidar_sin_reglas : ¬ ∀ M : MundoClases, SupuestoSAT M 1 → False :=
  fun h => h _ (modeloUmbral_supuesto (c := 1) (by norm_num))

/-- **Mutante refutado: con `c ≥ √2`, anidar cualquier número de veces no contradice**: no hay `k` que, con las reglas
y el supuesto, dé `False` en todo mundo. -/
theorem mutante_anidar_k_no_acotado {c : ℝ} (hc : √2 ≤ c) :
    ¬ ∀ M : MundoClases, ReglasLV M → SupuestoSAT M c → False := by
  intro h
  obtain ⟨M, R, hs, -⟩ := anidar_fijo_no_contradice hc
  exact h M R hs

/-! ## 4. El bootstrap que mejora: sin punto fijo en general, con punto fijo en la búsqueda -/

/-- **Mejorar el resolvedor con el resolvedor no tiene punto fijo, en general (Blum).** Hay una función computable de
valores `0, 1` sin programa óptimo ni siquiera salvo constante. -/
theorem mejorar_sin_punto_fijo : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧
    ¬ ∃ i, Computa i f ∧ ∀ j, Computa j f → EsO (costo i) (costo j) :=
  BlumExiste.existe_sin_optimo

/-- **En la búsqueda de SAT el bootstrap que mejora sí tiene punto fijo: Levin, salvo constante.** Hay un código `L`
que resuelve, y contra todo código `c` que resuelve, en toda fórmula satisfacible, las rondas de `L` quedan debajo de
`8 · 2^(código de c) · costo c`: la constante depende de `c` y no de la fórmula. La medida es la de rondas
(`costoLevin`), no los pasos del propio `L`. -/
theorem busqueda_tiene_punto_fijo : ∃ L : Code, ResuelveBusquedaSAT L ∧
    ∀ c, ResuelveBusquedaSAT c → ∀ F, Satisfacible F →
      costoLevin vSAT (Encodable.encode F) < (8 * 2 ^ encodeCode c) * costo c (Encodable.encode F) := by
  obtain ⟨L, hL, -, -, h⟩ := construir_es_resolver
  refine ⟨L, hL, fun c hc F hF => ?_⟩
  obtain ⟨y, hy, hV⟩ := hc F hF
  exact h F hF c y hy hV

/-! ## 5. Mutantes refutados -/

/-- **Mutante refutado: «el bootstrap que construye da contradicción»** es falso. -/
theorem mutante_construir_contradice : ¬ ((∃ c : Code, ResuelveBusquedaSAT c) → False) :=
  fun h => h bootstrap_construye_consistente

/-- **Mutante refutado: «no hay certificador ni para un código fijo»** es falso. -/
theorem mutante_sin_certificador_fijo :
    ¬ ∀ c0 : Code, ¬ ∃ d : Code → Bool, Computable d ∧ (d c0 = true ↔ ResuelveBusquedaSAT c0) :=
  fun h => h Code.zero (certificador_de_un_codigo Code.zero)

/-- **Mutante refutado: «la propiedad sintáctica tampoco es decidible»** es falso. -/
theorem mutante_sintactica_indecidible (c0 : Code) : ¬ ¬ ComputablePred fun c : Code => c = c0 :=
  fun h => h (sintactica_decidible c0)

/-! ## 6. Los cuatro, en un enunciado -/

/-- **Los cuatro bootstraps lado a lado.** Construir es consistente; certificar es contradictorio; anidar contradice
con memoria chica y `c < √2`, y no con `c ≥ √2`; mejorar no tiene punto fijo en general pero en la búsqueda de SAT
sí (Levin, en rondas). -/
theorem cuatro_bootstraps :
    (∃ c : Code, ResuelveBusquedaSAT c) ∧
    ¬ ComputablePred ResuelveBusquedaSAT ∧
    (∀ c : ℝ, (∀ M : MundoClases, ReglasLV M → SupuestoSAT M c → False) ↔ c < √2) ∧
    (∃ f : ℕ → ℕ, Computable f ∧ ¬ ∃ i, Computa i f ∧ ∀ j, Computa j f → EsO (costo i) (costo j)) ∧
    (∃ L : Code, ResuelveBusquedaSAT L ∧ ∀ c, ResuelveBusquedaSAT c → ∀ F, Satisfacible F →
      costoLevin vSAT (Encodable.encode F) < (8 * 2 ^ encodeCode c) * costo c (Encodable.encode F)) := by
  obtain ⟨f, -, hf, hno⟩ := mejorar_sin_punto_fijo
  exact ⟨bootstrap_construye_consistente, no_hay_certificador, umbral_lipton_viglas, ⟨f, hf, hno⟩,
    busqueda_tiene_punto_fijo⟩

end Sagitta.Map.Tiempo.Bootstrap
