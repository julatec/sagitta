import Sagitta.Map.CurvaMemoriaDemora
import Sagitta.Map.BusquedaPolinomial
import Sagitta.Map.AlfabetoFinito

/-!
# El índice rápido: la parte B de la dificultad es P ≠ NP

Sobre `CurvaMemoriaDemora`, `BusquedaPolinomial` y `AlfabetoFinito`.

## La lectura

Un detector que poda el árbol de certificados tiene que hacer dos cosas:

* **A, distinguir**: guardar lo bastante del prefijo para separar los futuros que importan. Lo mide la curva
  memoria–demora: al menos `log₂` del mayor engañador.
* **B, saber rápido**: decidir, en tiempo polinomial, a cuál de esos futuros le toca morir.

Aquí se prueba que A nunca es el obstáculo y que B, para todo NP, es la pregunta P vs NP.

## Lo que se prueba

* **A no alcanza** (`curva_le_lineal`, `curva_bits_lineal`): todo engañador, para cualquier `sol`, `N` y `d`, mide a
  lo sumo `2^(N+1)`. La curva nunca pide más de `N + 1` bits. La prueba: si el engañador tiene dos elementos,
  `distinguibles_largo` les pone largo `≤ N`, y `rellenar` los mete sin choques en las cadenas de largo `N + 1`.
* **La memoria lineal alcanza** (`memoriaPrefijo`, `memoriaPrefijo_perfecto`, `card_prefijoAcotado`): el detector
  cuyo estado es el prefijo mismo, con alarma «está muerto», es sano y tiene demora 0 en todo árbol, con a lo sumo
  `2^(N+1)` estados. Su alarma no es computable: es un control de memoria, no de tiempo. Da la misma cota por otro
  camino (`curva_le_lineal'`).
* **El índice rápido** (`EsIndiceRapido V p det`): `det` es polinomial (cslib-frontier) y responde exactamente «el
  prefijo `q` del certificado de `x` está muerto», para `|q| ≤ p(|x|)`. Es sano y tiene demora 0
  (`indice_sano_demora0`).
* **B ⇒ P** (`indice_rapido_implica_P`): con un índice rápido, `L ∈ P`. Es `busqueda_en_P` con demora 0.
* **P ⇒ B** (`P_implica_indice_rapido`): si NP ⊆ P, todo verificador polinomial tiene índice rápido. El problema de
  extensión («`q` se extiende a un certificado de `x`», `problemaExt`) está en NP sin hipótesis
  (`problemaExt_en_NP`, `problemaExt_iff`); con NP ⊆ P está en P, y negarlo da el índice (`indiceExt`). El par
  `(x, q)` va como `frame x ++ q`, y el verificador lo separa con `unframe` y `dropFrame`.
* **La equivalencia** (`indice_iff_NP_sub_P`, `indice_iff_PIgualNP`, `falta_indice_iff_PDistintoNP`): todo problema
  de NP tiene índice rápido si y solo si P = NP. Que a alguno le falte es P ≠ NP. La forma fuerte
  (`NP_sub_P_iff_todo_verificador`): con NP ⊆ P, *toda* presentación tiene índice.

## Los controles

* La hipótesis de la parte A se cumple: hay engañadores de todo tamaño (`unica (k + 1)`), y el de `control_d0` cabe.
* El detector que guarda el prefijo dispara en `[false]` y no en `[]`, en `unica 2`.
* `detEco` de `BusquedaPolinomial` es un índice rápido para `verifEco` (`eco_indice`), y el teorema da «tiene un
  `1`» ∈ P. El detector que nunca dispara no es índice: la definición tiene dientes.
* El problema de extensión responde bien en `x = [true]`.

## Lo que no se prueba

* **Nada sobre P vs NP.** La equivalencia traduce una pregunta abierta en otra; no la acerca. `P_implica_indice_rapido`
  tiene una hipótesis abierta (NP ⊆ P) y no hay control de que se cumpla: lo que sí se controla es lo incondicional
  (`problemaExt_en_NP`, `problemaExt_iff`).
* **El índice es de demora 0.** No se prueba la equivalencia para demora logarítmica: B ⇒ P vale con demora
  `O(log n)` (es `busqueda_en_P`), pero la recíproca aquí da demora 0, que es más fuerte.
* **La parte A cuenta estados, no tiempo.** `N + 1` bits alcanzan, pero llenar esos bits (la alarma) puede costar
  cualquier cosa; por eso la memoria lineal no dice nada de P.
* **No uniformidad**: la parte A es para cada `sol` y `N` por separado, como en `CurvaMemoriaDemora`.
-/

namespace Sagitta.Map.Tiempo.IndiceRapido

open List
open Sagitta.Map.Tiempo.BombeoDetector
open Sagitta.Map.Tiempo.CurvaMemoriaDemora
open Sagitta.Map.AlfabetoFinito
open Turing.MultiTapeTM

/-! ## Parte A: la memoria nunca pide más de `N + 1` bits -/

/-- **Rellenar un prefijo**: `p`, un `true` y ceros hasta largo `N + 1`. -/
def rellenar (N : ℕ) (p : List Bool) : List Bool := p ++ true :: replicate (N - p.length) false

/-- Con `|p| ≤ N`, el relleno mide `N + 1`. -/
theorem length_rellenar {N : ℕ} {p : List Bool} (h : p.length ≤ N) : (rellenar N p).length = N + 1 := by
  simp [rellenar]; omega

/-- Ceros, un uno y una cola: la cola se recupera. -/
theorem ceros_uno_inj : ∀ {a b : ℕ} {u v : List Bool},
    replicate a false ++ true :: u = replicate b false ++ true :: v → u = v
  | 0, 0, _, _, h => by simpa using h
  | _ + 1, 0, _, _, h => by simp [replicate_succ] at h
  | 0, _ + 1, _, _, h => by simp [replicate_succ] at h
  | a + 1, b + 1, _, _, h => ceros_uno_inj (a := a) (b := b) (by simpa [replicate_succ] using h)

/-- **Rellenar es inyectivo**: el último `true` marca dónde termina el prefijo. -/
theorem rellenar_inj {N : ℕ} {p p' : List Bool} (h : rellenar N p = rellenar N p') : p = p' := by
  have h2 := congrArg List.reverse h
  simp only [rellenar, reverse_append, reverse_cons, reverse_replicate, append_assoc, singleton_append] at h2
  exact reverse_injective (ceros_uno_inj h2)

/-- Las cadenas de largo `n`, como `Finset`. -/
noncomputable def cadenasDe (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (List.Vector Bool n)).image List.Vector.toList

theorem mem_cadenasDe {n : ℕ} {l : List Bool} (h : l.length = n) : l ∈ cadenasDe n :=
  Finset.mem_image.2 ⟨⟨l, h⟩, Finset.mem_univ _, rfl⟩

/-- Hay a lo sumo `2^n` cadenas de largo `n`. -/
theorem card_cadenasDe_le (n : ℕ) : (cadenasDe n).card ≤ 2 ^ n := by
  refine Finset.card_image_le.trans ?_
  simp [card_vector]

/-- **La parte A no alcanza: todo engañador mide a lo sumo `2^(N+1)`.** Si tiene dos elementos o más, cada uno
tiene pareja, y `distinguibles_largo` le pone largo `≤ N`. Vale para todo `sol`, `N` y `d`. -/
theorem curva_le_lineal (sol : List Bool → Bool) (N d : ℕ) {F : Finset (List Bool)}
    (hF : Enganador sol N d F) : F.card ≤ 2 ^ (N + 1) := by
  by_cases h1 : F.card ≤ 1
  · exact h1.trans Nat.one_le_two_pow
  have hlen : ∀ p ∈ F, p.length ≤ N := by
    intro p hp
    obtain ⟨p', hp', hne⟩ := Finset.exists_mem_ne (by omega : 1 < F.card) p
    have := (distinguibles_largo (hF p hp p' hp' (Ne.symm hne))).1
    omega
  calc F.card ≤ (cadenasDe (N + 1)).card :=
        Finset.card_le_card_of_injOn (rellenar N) (fun p hp => mem_cadenasDe (length_rellenar (hlen p hp)))
          (fun _ _ _ _ h => rellenar_inj h)
    _ ≤ 2 ^ (N + 1) := card_cadenasDe_le _

/-- **En bits**: la cota de la curva nunca pide más de `N + 1` bits. -/
theorem curva_bits_lineal (sol : List Bool → Bool) (N d : ℕ) {F : Finset (List Bool)}
    (hF : Enganador sol N d F) : Nat.clog 2 F.card ≤ N + 1 :=
  Nat.clog_le_of_le_pow (curva_le_lineal sol N d hF)

/-! ### Control: la memoria lineal alcanza para distinguir -/

/-- Prefijos de largo a lo sumo `N`: el estado del detector que guarda todo. -/
abbrev PrefijoAcotado (N : ℕ) := {l : List Bool // l.length ≤ N}

/-- El relleno, como vector de largo `N + 1`. -/
def rellenarV (N : ℕ) (s : PrefijoAcotado N) : List.Vector Bool (N + 1) := ⟨rellenar N s.1, length_rellenar s.2⟩

theorem rellenarV_inj (N : ℕ) : Function.Injective (rellenarV N) :=
  fun _ _ h => Subtype.ext (rellenar_inj (congrArg Subtype.val h))

noncomputable instance (N : ℕ) : Fintype (PrefijoAcotado N) := Fintype.ofInjective _ (rellenarV_inj N)

/-- Los estados caben en `N + 1` bits. -/
theorem card_prefijoAcotado (N : ℕ) : Fintype.card (PrefijoAcotado N) ≤ 2 ^ (N + 1) := by
  have := Fintype.card_le_of_injective _ (rellenarV_inj N)
  simpa [card_vector] using this

/-- **El detector que guarda el prefijo**: el estado es el prefijo (cortado en `N`), y la alarma es «está muerto».
La alarma no es computable; aquí solo se cuenta memoria. -/
noncomputable def memoriaPrefijo (sol : List Bool → Bool) (N : ℕ) : Memoria (PrefijoAcotado N) where
  inicio := ⟨[], by simp⟩
  paso s b := if h : s.1.length < N then ⟨s.1 ++ [b], by simp; omega⟩ else s
  alarma s := by classical exact decide (¬ Vivo sol (N - s.1.length) s.1)

/-- El estado es el prefijo cortado en `N`. -/
theorem estado_memoriaPrefijo (sol : List Bool → Bool) (N : ℕ) (p : List Bool) :
    ((memoriaPrefijo sol N).estado p).1 = p.take N := by
  induction p using List.reverseRecOn with
  | nil => simp [Memoria.estado, memoriaPrefijo]
  | append_singleton p b ih =>
    rw [Memoria.estado_append]
    simp only [foldl_cons, foldl_nil]
    change (if h : _ then _ else _ : PrefijoAcotado N).1 = _
    split_ifs with h
    · simp only [ih] at h ⊢
      have hp : p.length < N := by
        by_contra hc; simp [List.length_take] at h; omega
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp; omega)]
    · simp only [ih] at h ⊢
      have hp : N ≤ p.length := by
        by_contra hc; simp [List.length_take] at h; omega
      rw [List.take_append_of_le_length hp]

/-- **El detector que guarda el prefijo es sano y tiene demora 0**, en todo árbol. -/
theorem memoriaPrefijo_perfecto (sol : List Bool → Bool) (N : ℕ) :
    SanoN sol (memoriaPrefijo sol N).det N ∧ DemoraN sol (memoriaPrefijo sol N).det N 0 := by
  classical
  refine oraculo_perfecto fun p hp => ?_
  have he := estado_memoriaPrefijo sol N p
  rw [List.take_of_length_le hp] at he
  change decide (¬ Vivo sol (N - ((memoriaPrefijo sol N).estado p).1.length)
    ((memoriaPrefijo sol N).estado p).1) = true ↔ _
  rw [he, decide_eq_true_eq]

/-- El detector que guarda el prefijo responde «muerto» exactamente en los prefijos muertos. -/
theorem memoriaPrefijo_det (sol : List Bool → Bool) (N : ℕ) {p : List Bool} (hp : p.length ≤ N) :
    (memoriaPrefijo sol N).det p = true ↔ ¬ Vivo sol (N - p.length) p := by
  classical
  have he := estado_memoriaPrefijo sol N p
  rw [List.take_of_length_le hp] at he
  change decide (¬ Vivo sol (N - ((memoriaPrefijo sol N).estado p).1.length)
    ((memoriaPrefijo sol N).estado p).1) = true ↔ _
  rw [he, decide_eq_true_eq]

/-- **La misma cota, por otro camino**: `curva_memoria_demora` con el detector que guarda el prefijo. -/
theorem curva_le_lineal' (sol : List Bool → Bool) (N d : ℕ) {F : Finset (List Bool)}
    (hF : Enganador sol N d F) : F.card ≤ 2 ^ (N + 1) :=
  (curva_memoria_demora (memoriaPrefijo sol N) (memoriaPrefijo_perfecto sol N).1
    (memoriaPrefijo_perfecto sol N).2 (enganador_mono (Nat.zero_le d) hF)).trans (card_prefijoAcotado N)

/-! ## Parte B: el índice rápido -/

/-- **Un índice rápido** para el verificador `V` con tope `p`: un detector polinomial (en cslib-frontier) que responde
exactamente «el prefijo `q` del certificado de `x` está muerto», para `|q| ≤ p(|x|)`. -/
def EsIndiceRapido (V : List Bool × List Bool → Bool) (p : Polynomial ℕ)
    (det : List Bool × List Bool → Bool) : Prop :=
  ComputableInPolyTime det (encPair encBits encBits) encBool ∧
    ∀ x q : List Bool, q.length ≤ p.eval x.length →
      (det (x, q) = true ↔ ¬ Vivo (solCert V x) (p.eval x.length - q.length) q)

/-- **Un índice rápido es sano y tiene demora 0**, en el árbol de certificados de cada `x`. -/
theorem indice_sano_demora0 {V : List Bool × List Bool → Bool} {p : Polynomial ℕ}
    {det : List Bool × List Bool → Bool} (h : EsIndiceRapido V p det) (x : List Bool) :
    SanoN (solCert V x) (fun q => det (x, q)) (p.eval x.length) ∧
      DemoraN (solCert V x) (fun q => det (x, q)) (p.eval x.length) 0 :=
  oraculo_perfecto fun q hq => h.2 x q hq

/-- Un verificador polinomial en el sentido de `Clases.lean` lo es en el de cslib-frontier. -/
theorem verificador_cslib {V : List Bool × List Bool → Bool} (hV : EsPolinomial V) :
    ComputableInPolyTime V (encPair encBits encBits) encBool := by
  have := esPolinomial_iff.mp hV
  rwa [incrustar_par, incrustar_bool] at this

/-- Y al revés. -/
theorem esPolinomial_de_cslib {V : List Bool × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair encBits encBits) encBool) : EsPolinomial V := by
  rw [esPolinomial_iff, incrustar_par, incrustar_bool]
  exact hV

/-- **Con un índice rápido, `L ∈ P`.** Es `busqueda_en_P` con demora 0. -/
theorem indice_rapido_implica_P {L : Problema} {p : Polynomial ℕ} {V det : List Bool × List Bool → Bool}
    (hL : ∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true)
    (hV : EsPolinomial V) (hdet : EsIndiceRapido V p det) : L ∈ P :=
  busqueda_en_P (d := fun _ => 0) (a := 0) (b := 0) hL (verificador_cslib hV) hdet.1 (fun _ => by simp)
    (fun x => (indice_sano_demora0 hdet x).1) (fun x => (indice_sano_demora0 hdet x).2)

/-! ## La recíproca: con NP ⊆ P, todo verificador tiene índice rápido -/

/-- Si una hoja ya es solución, también lo es toda extensión suya: los prefijos se conservan. -/
theorem solCert_append {V : List Bool × List Bool → Bool} {x w : List Bool} (s : List Bool)
    (h : solCert V x w = true) : solCert V x (w ++ s) = true := by
  simp only [solCert, List.any_eq_true, List.mem_range] at h ⊢
  obtain ⟨j, hj, hv⟩ := h
  exact ⟨j, by simp; omega, by rw [List.take_append_of_le_length (by omega)]; exact hv⟩

/-- Un polinomio con coeficientes naturales es monótono. -/
theorem eval_mono_nat (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- **El verificador del problema de extensión.** La entrada `z = frame x ++ q` codifica el par `(x, q)`; el
certificado `y` sirve si `|q ++ y| ≤ p(|x|)` y `q ++ y` tiene un certificado de `x` como prefijo. -/
def verifExt (V : List Bool × List Bool → Bool) (p : Polynomial ℕ) (zy : List Bool × List Bool) : Bool :=
  decide ((dropFrame zy.1 ++ zy.2).length ≤ p.eval (unframe zy.1).length) &&
    solCert V (unframe zy.1) (dropFrame zy.1 ++ zy.2)

/-- **El problema de extensión**: «el prefijo `q` se extiende a un certificado de `x`», con `z = frame x ++ q`. -/
noncomputable def problemaExt (V : List Bool × List Bool → Bool) (p : Polynomial ℕ) : Problema := fun z => by
  classical
  exact decide (∃ y : List Bool, y.length ≤ p.eval z.length ∧ verifExt V p (z, y) = true)

/-- Lo que lee el verificador de extensión: el largo de `q ++ y`. -/
theorem largoExt_polinomial : ComputableInPolyTime (fun zy : List Bool × List Bool => (dropFrame zy.1 ++ zy.2).length)
    (encPair encBits encBits) encUnary := by fun_prop

/-- El tope `p(|x|)`. -/
theorem topeExt_polinomial (p : Polynomial ℕ) : ComputableInPolyTime
    (fun zy : List Bool × List Bool => p.eval (unframe zy.1).length) (encPair encBits encBits) encUnary := by
  fun_prop

/-- La cadena `q ++ y`. -/
theorem colaExt_polinomial : ComputableInPolyTime (fun zy : List Bool × List Bool => dropFrame zy.1 ++ zy.2)
    (encPair encBits encBits) encBits := by fun_prop

/-- La cadena `x`. -/
theorem cabezaExt_polinomial : ComputableInPolyTime (fun zy : List Bool × List Bool => unframe zy.1)
    (encPair encBits encBits) encBits := by fun_prop

/-- El verificador del problema de extensión es polinomial si `V` lo es. -/
theorem verifExt_polinomial {V : List Bool × List Bool → Bool} (hV : EsPolinomial V) (p : Polynomial ℕ) :
    ComputableInPolyTime (verifExt V p) (encPair encBits encBits) encBool := by
  have h2 : ComputableInPolyTime
      (fun zy : List Bool × List Bool => decide ((dropFrame zy.1 ++ zy.2).length ≤ p.eval (unframe zy.1).length))
      (encPair encBits encBits) encBool :=
    ComputableInPolyTime.unary_le.comp (largoExt_polinomial.prod (topeExt_polinomial p))
  have h3 : ComputableInPolyTime
      (fun zy : List Bool × List Bool => solCert V (unframe zy.1) (dropFrame zy.1 ++ zy.2))
      (encPair encBits encBits) encBool :=
    (solCert_polinomial (verificador_cslib hV)).comp (cabezaExt_polinomial.prod colaExt_polinomial)
  exact ComputableInPolyTime.bool_and' h2 h3

/-- **El problema de extensión está en NP**, sin hipótesis abiertas. -/
theorem problemaExt_en_NP {V : List Bool × List Bool → Bool} (hV : EsPolinomial V) (p : Polynomial ℕ) :
    problemaExt V p ∈ NP := by
  classical
  refine ⟨p, verifExt V p, esPolinomial_de_cslib (verifExt_polinomial hV p), fun z => ?_⟩
  simp [problemaExt]

/-- **Lo que responde el problema de extensión**: en `frame x ++ q`, con `|q| ≤ p(|x|)`, dice si `q` está vivo. -/
theorem problemaExt_iff {V : List Bool × List Bool → Bool} {p : Polynomial ℕ} {x q : List Bool}
    (hq : q.length ≤ p.eval x.length) :
    problemaExt V p (frame x ++ q) = true ↔ Vivo (solCert V x) (p.eval x.length - q.length) q := by
  classical
  simp only [problemaExt, verifExt, unframe_frame_append, dropFrame_frame_append, decide_eq_true_eq,
    Bool.and_eq_true]
  constructor
  · rintro ⟨y, -, hl, hs⟩
    refine ⟨y ++ replicate (p.eval x.length - q.length - y.length) false, ?_, ?_⟩
    · simp only [length_append, length_replicate] at hl ⊢; omega
    · rw [← List.append_assoc]; exact solCert_append _ hs
  · rintro ⟨r, hr, hs⟩
    refine ⟨r, ?_, by simp only [length_append]; omega, hs⟩
    calc r.length ≤ p.eval x.length := by omega
      _ ≤ p.eval (frame x ++ q).length :=
        eval_mono_nat p (by simp only [length_append, length_frame]; omega)

/-- **El índice que da el problema de extensión**: `q` está muerto si no se extiende. -/
noncomputable def indiceExt (V : List Bool × List Bool → Bool) (p : Polynomial ℕ)
    (xq : List Bool × List Bool) : Bool :=
  !problemaExt V p (frame xq.1 ++ xq.2)

/-- **Si NP ⊆ P, todo verificador polinomial tiene índice rápido.** El problema de extensión está en NP, luego en P,
y negarlo da el índice. -/
theorem P_implica_indice_rapido (hNP : VerificarImplicaResolver) {V : List Bool × List Bool → Bool}
    (hV : EsPolinomial V) (p : Polynomial ℕ) : EsIndiceRapido V p (indiceExt V p) := by
  have hE := computable_of_mem_P (hNP _ (problemaExt_en_NP hV p))
  refine ⟨?_, fun x q hq => ?_⟩
  · have hf : ComputableInPolyTime (fun xq : List Bool × List Bool => frame xq.1 ++ xq.2)
        (encPair encBits encBits) encBits := by fun_prop
    exact ComputableInPolyTime.bool_not.comp (hE.comp hf)
  · simp only [indiceExt, Bool.not_eq_true', ← problemaExt_iff hq]
    simp

/-! ## La equivalencia -/

/-- **Todo problema de NP tiene un índice rápido**, para alguna presentación con verificador polinomial. -/
def TodoNPTieneIndice : Prop :=
  ∀ L ∈ NP, ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool), EsPolinomial V ∧
    (∀ x, L x = true ↔ ∃ y : List Bool, y.length ≤ p.eval x.length ∧ V (x, y) = true) ∧
    ∃ det, EsIndiceRapido V p det

/-- **La parte B es NP ⊆ P**: todo problema de NP tiene índice rápido si y solo si NP ⊆ P. -/
theorem indice_iff_NP_sub_P : TodoNPTieneIndice ↔ VerificarImplicaResolver := by
  constructor
  · intro h L hL
    obtain ⟨p, V, hV, hLV, det, hdet⟩ := h L hL
    exact indice_rapido_implica_P hLV hV hdet
  · intro h L hL
    obtain ⟨p, V, hV, hLV⟩ := hL
    exact ⟨p, V, hV, hLV, _, P_implica_indice_rapido h hV p⟩

/-- **La forma con `PIgualNP`**: todo problema de NP tiene índice rápido si y solo si P = NP. Negando: que a algún
problema de NP le falte índice rápido es P ≠ NP. -/
theorem indice_iff_PIgualNP : TodoNPTieneIndice ↔ PIgualNP :=
  indice_iff_NP_sub_P.trans pIgualNP_iff_verificarImplicaResolver'.symm

/-- **Sin índice rápido en alguna parte es P ≠ NP.** -/
theorem falta_indice_iff_PDistintoNP : ¬ TodoNPTieneIndice ↔ PDistintoNP :=
  not_congr indice_iff_PIgualNP

/-- **La forma fuerte**: con NP ⊆ P, *toda* presentación de *todo* problema de NP tiene índice rápido. -/
theorem NP_sub_P_iff_todo_verificador :
    VerificarImplicaResolver ↔
      ∀ (V : List Bool × List Bool → Bool) (p : Polynomial ℕ), EsPolinomial V → ∃ det, EsIndiceRapido V p det := by
  constructor
  · exact fun h V p hV => ⟨_, P_implica_indice_rapido h hV p⟩
  · intro h L hL
    obtain ⟨p, V, hV, hLV⟩ := hL
    obtain ⟨det, hdet⟩ := h V p hV
    exact indice_rapido_implica_P hLV hV hdet

/-! ## Controles -/

/-- El relleno de `[true]` hasta largo 4. -/
example : rellenar 3 [true] = [true, true, false, false] := by decide

/-- Dos prefijos distintos dan rellenos distintos, aun con el mismo largo final. -/
example : rellenar 2 [true] ≠ rellenar 2 [true, false] := by decide

/-- **La hipótesis de `curva_le_lineal` se cumple**: el engañador de `control_d0` (`unica 2`, `N = 4`) tiene 4
elementos, y la cota da 32. -/
example : [[], [true], [true, true], [false]].toFinset.card ≤ 2 ^ (4 + 1) :=
  curva_le_lineal (unica 2) 4 0 control_d0

/-- **La hipótesis de `curva_le_lineal` no es vacía**: hay engañadores de todo tamaño (el de `unica (k + 1)`). -/
example (k : ℕ) : ∃ (sol : List Bool → Bool) (N : ℕ) (F : Finset (List Bool)), Enganador sol N 0 F ∧ k ≤ F.card :=
  ⟨unica (k + 1), 2 * (k + 1), _, enganador_unica (by omega), by rw [card_enganadorUnica]; omega⟩

/-- **El detector que guarda el prefijo dispara donde debe**: en `unica 2`, `[false]` está muerto y `[]` no. -/
example : (memoriaPrefijo (unica 2) 4).det [false] = true ∧ (memoriaPrefijo (unica 2) 4).det [] = false := by
  constructor
  · rw [memoriaPrefijo_det _ _ (by decide), ← vivoB_iff]; decide
  · have h := memoriaPrefijo_det (unica 2) 4 (p := []) (by decide)
    rw [← vivoB_iff] at h
    cases hd : (memoriaPrefijo (unica 2) 4).det [] with
    | false => rfl
    | true => exact absurd (h.1 hd) (by decide)

/-- **Las hipótesis de `indice_rapido_implica_P` se cumplen**: `detEco` de `BusquedaPolinomial` es un índice rápido
para `verifEco` («`x` tiene un `1`»), con tope `X`. -/
theorem eco_indice : EsIndiceRapido verifEco Polynomial.X detEco := by
  refine ⟨detEco_polinomial, fun x q hq => ?_⟩
  simp only [Polynomial.eval_X] at hq ⊢
  rw [vivo_eco hq]
  simp only [detEco, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, not_and_or, Bool.not_eq_true]

/-- Y el teorema da lo que debe: «tener un `1`» está en P, ahora por el índice. -/
example : (fun x : List Bool => x.any id) ∈ P :=
  indice_rapido_implica_P eco_L (esPolinomial_de_cslib verifEco_polinomial) eco_indice

/-- **La definición tiene dientes**: el detector que nunca dispara no es un índice rápido para `verifEco`. -/
example : ¬ EsIndiceRapido verifEco Polynomial.X (fun _ => false) := by
  rintro ⟨-, h⟩
  have h1 := h [false] [] (by simp)
  rw [Polynomial.eval_X, vivo_eco (by simp)] at h1
  revert h1; decide

/-- **El problema de extensión responde lo que debe**: con `x = [true]`, el prefijo vacío se extiende al certificado
y `[false]` no. -/
example : problemaExt verifEco Polynomial.X (frame [true] ++ []) = true ∧
    problemaExt verifEco Polynomial.X (frame [true] ++ [false]) = false := by
  constructor
  · rw [problemaExt_iff (by simp), Polynomial.eval_X, vivo_eco (by simp)]; decide
  · have h := problemaExt_iff (V := verifEco) (p := Polynomial.X) (x := [true]) (q := [false]) (by simp)
    rw [Polynomial.eval_X, vivo_eco (by simp)] at h
    cases he : problemaExt verifEco Polynomial.X (frame [true] ++ [false]) with
    | false => rfl
    | true => exact absurd (h.1 he) (by decide)

end Sagitta.Map.Tiempo.IndiceRapido
