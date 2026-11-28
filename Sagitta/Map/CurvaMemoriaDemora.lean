import Sagitta.Map.BombeoDetector

/-!
# La curva memoria–demora

Sobre `BombeoDetector` y `DemoraEfectiva`. Un detector de memoria finita (`Memoria σ`) lee el prefijo una vez, bit a
bit, y solo guarda su estado. Aquí se prueba cuánta memoria necesita para ser sano y tener demora `d`, en cualquier
árbol de elecciones `sol` con horizonte `N`.

## Lo que se prueba

* **Prefijos distinguibles** (`Distinguibles sol N d p p'`): hay un sufijo común `w` que deja a uno vivo y al otro
  muerto, y la demora cabe en los dos (`|p ++ w| + d ≤ N`, `|p' ++ w| + d ≤ N`). No se pide `|p| = |p'|`: con largos
  distintos hay más pares distinguibles, así que el teorema es más fuerte. La familia `trueⁱ` de `cota_inferior` usa
  justamente largos distintos.
* **El lema del estado** (`no_distinguibles_de_estado`): en un detector sano con demora `d`, dos prefijos en el mismo
  estado no son distinguibles. Es `bombeo_memoria` aplicado a `p ++ w` y `p' ++ w`.
* **La curva** (`curva_memoria_demora`): si `F` es un conjunto engañador (`Enganador`: prefijos distinguibles de a
  pares), todo detector sano con demora `d` tiene al menos `|F|` estados. Es un palomar: `estado` es inyectiva en `F`.
  En bits (`curva_bits`, `curva_clog`): con `card σ ≤ 2^b`, `|F| ≤ 2^b` y `⌈log₂ |F|⌉ ≤ b`.
* **La monotonía** (`distinguibles_mono`, `enganador_mono`): un engañador para `d'` lo es para todo `d ≤ d'`. Más
  demora pide menos memoria.
* **El caso de `unica m`** (`enganador_unica`): para `d < m`, `{[false], true⁰, …, trueᵐ}` es engañador, de tamaño
  `m + 2`. De ahí sale `cota_inferior_fina`: con `m + 1` estados o menos, la demora es al menos `m`. Es
  `cota_inferior` de `BombeoDetector` (que pedía `m` estados) con un estado más (`cota_inferior_desde_curva`).
* **La cota se alcanza** (`contadorFino`, `curva_exacta_unica`): el contador de `BombeoDetector` con dos estados
  fundidos tiene `m + 2` estados, es sano y tiene demora 0. Para `unica m` con demora 0, la memoria mínima es
  exactamente `m + 2` estados. Esto responde lo que `BombeoDetector` dejaba abierto: con `m + 1` estados la demora
  es al menos `m`; con `m + 2` ya es 0.

## La lectura

«Lo que no distinguís lo pagás en demora.» La memoria mínima para demora `d`, en bits, es al menos `log₂` del mayor
conjunto engañador para `d`. La curva baja con `d`: en `unica 2` (`N = 4`) el mayor engañador mide 4 con `d = 0`,
2 con `d = 2` y 1 con `d = 4` (controles al final).

## La conexión (de memoria, sin verificar)

* Es el argumento de **Myhill–Nerode** (Myhill 1957, Nerode 1958): un autómata necesita un estado por cada clase de
  prefijos que algún sufijo separa. Aquí el sufijo tiene que dejar espacio para la demora, y por eso las clases
  dependen de `d`.
* Es el método del **conjunto engañador** (*fooling set*) de la complejidad de comunicación (Yao 1979; el libro de
  Kushilevitz y Nisan, 1997): un protocolo de una vuelta, en el que el detector le pasa su estado al futuro, necesita
  tantos mensajes distintos como elementos tiene el engañador.

## Lo que NO se prueba

* El teorema es sobre detectores que leen el prefijo **una vez**, de izquierda a derecha, con memoria finita. No
  cubre detectores que vuelven a leer el prefijo ni detectores con memoria que crece con la entrada.
* El **costo de llenar la memoria**: el teorema cuenta estados, no dice cuánto cuesta calcular la transición ni el
  contenido de la tabla. Un detector con pocos estados y una transición carísima cumple la cota.
* La **no uniformidad**: para cada `sol` y `N` se cuenta un detector aparte. Nada aquí relaciona detectores de
  tamaños distintos.
* El **régimen polinomial**: contra `2^poli` estados el palomar no fuerza nada, como en `BombeoDetector`.
* Una cota superior general: no se construye, para `d` cualquiera, un detector con tantos estados como el mayor
  engañador. La relación «mismo futuro a demora `d`» (no distinguibles) no es transitiva, ni siquiera con `d = 0`,
  por el horizonte: un prefijo largo no se distingue de nadie porque el sufijo no cabe (`no_transitiva`). Sus
  «clases» no son un cociente, y Myhill–Nerode no se copia tal cual.
  Solo se muestra la igualdad en el ejemplo `unica m` con `d = 0`.

## Referencias (datos bibliográficos verificados; el contenido, de memoria)

Los compromisos tiempo–memoria para SAT, el régimen al que esto no llega:

* L. Fortnow, R. Lipton, D. van Melkebeek y A. Viglas, «Time-space lower bounds for satisfiability», *Journal of the
  ACM* 52(6), 2005.
* R. Williams, «Alternation-trading proofs, linear programming, and lower bounds», *ACM Transactions on Computation
  Theory* 5(2), 2013.
* S. Buss y R. Williams, «Limits on alternation-trading proofs for time-space lower bounds», *CCC 2012*.
-/

namespace Sagitta.Map.Tiempo.CurvaMemoriaDemora

open List
open Sagitta.Map.Tiempo.BombeoDetector

/-! ## Prefijos distinguibles -/

/-- **Dos prefijos distinguibles a demora `d`.** Un sufijo común `w` deja a uno vivo y al otro muerto, y en los dos
la demora cabe en el horizonte. Los largos de `p` y `p'` pueden ser distintos. -/
def Distinguibles (sol : List Bool → Bool) (N d : ℕ) (p p' : List Bool) : Prop :=
  ∃ w : List Bool, (p ++ w).length + d ≤ N ∧ (p' ++ w).length + d ≤ N ∧
    ((¬ Vivo sol (N - (p ++ w).length) (p ++ w) ∧ Vivo sol (N - (p' ++ w).length) (p' ++ w)) ∨
      (Vivo sol (N - (p ++ w).length) (p ++ w) ∧ ¬ Vivo sol (N - (p' ++ w).length) (p' ++ w)))

variable {sol : List Bool → Bool} {N d : ℕ}

/-- Distinguir es simétrico. -/
theorem distinguibles_symm {p p' : List Bool} (h : Distinguibles sol N d p p') : Distinguibles sol N d p' p := by
  obtain ⟨w, h1, h2, h | h⟩ := h
  · exact ⟨w, h2, h1, .inr ⟨h.2, h.1⟩⟩
  · exact ⟨w, h2, h1, .inl ⟨h.2, h.1⟩⟩

/-- Nadie se distingue de sí mismo. -/
theorem distinguibles_irrefl (p : List Bool) : ¬ Distinguibles sol N d p p := by
  rintro ⟨w, -, -, h | h⟩
  · exact h.1 h.2
  · exact h.2 h.1

/-- Los dos prefijos dejan espacio para la demora. -/
theorem distinguibles_largo {p p' : List Bool} (h : Distinguibles sol N d p p') :
    p.length + d ≤ N ∧ p'.length + d ≤ N := by
  obtain ⟨w, h1, h2, -⟩ := h
  simp only [length_append] at h1 h2
  omega

/-- **Monotonía.** Lo que se distingue a demora `d'` se distingue a toda demora menor. -/
theorem distinguibles_mono {d' : ℕ} (hdd : d ≤ d') {p p' : List Bool} (h : Distinguibles sol N d' p p') :
    Distinguibles sol N d p p' := by
  obtain ⟨w, h1, h2, h⟩ := h
  exact ⟨w, by omega, by omega, h⟩

/-! ## El lema del estado -/

/-- **Mismo estado, no distinguibles.** En un detector sano con demora `d`, dos prefijos en el mismo estado no se
distinguen a demora `d`. Si `w` los separara, el bombeo daría `N < max |p ++ w| |p' ++ w| + d`, y la demora no cabría. -/
theorem no_distinguibles_de_estado {σ : Type*} (M : Memoria σ) (hs : SanoN sol M.det N)
    (hd : DemoraN sol M.det N d) {p p' : List Bool} (h : M.estado p = M.estado p') :
    ¬ Distinguibles sol N d p p' := by
  rintro ⟨w, h1, h2, hx | hx⟩
  · have := bombeo_memoria M hs hd h hx.1 hx.2
    rcases le_total (p ++ w).length (p' ++ w).length with hl | hl
    · rw [max_eq_right hl] at this; omega
    · rw [max_eq_left hl] at this; omega
  · have := bombeo_memoria M hs hd h.symm hx.2 hx.1
    rcases le_total (p' ++ w).length (p ++ w).length with hl | hl
    · rw [max_eq_right hl] at this; omega
    · rw [max_eq_left hl] at this; omega

/-! ## La curva -/

/-- **Un conjunto engañador a demora `d`**: prefijos distinguibles de a pares. -/
def Enganador (sol : List Bool → Bool) (N d : ℕ) (F : Finset (List Bool)) : Prop :=
  ∀ p ∈ F, ∀ p' ∈ F, p ≠ p' → Distinguibles sol N d p p'

/-- **Monotonía de los engañadores.** Un engañador para `d'` lo es para todo `d ≤ d'`. -/
theorem enganador_mono {d' : ℕ} (hdd : d ≤ d') {F : Finset (List Bool)} (hF : Enganador sol N d' F) :
    Enganador sol N d F :=
  fun p hp p' hp' hne => distinguibles_mono hdd (hF p hp p' hp' hne)

/-- **La curva memoria–demora.** Todo detector sano con demora `d` tiene al menos tantos estados como cualquier
engañador para `d`. Por palomar: `estado` es inyectiva en el engañador. -/
theorem curva_memoria_demora {σ : Type*} [Fintype σ] (M : Memoria σ) (hs : SanoN sol M.det N)
    (hd : DemoraN sol M.det N d) {F : Finset (List Bool)} (hF : Enganador sol N d F) :
    F.card ≤ Fintype.card σ := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn M.estado (fun _ _ => by simp) ?_
  intro p hp p' hp' he
  by_contra hne
  exact no_distinguibles_de_estado M hs hd he (hF p hp p' hp' hne)

/-- **La curva en bits.** Con `b` bits de memoria (`card σ ≤ 2^b`), el engañador tiene a lo sumo `2^b` elementos. -/
theorem curva_bits {σ : Type*} [Fintype σ] (M : Memoria σ) {b : ℕ} (hb : Fintype.card σ ≤ 2 ^ b)
    (hs : SanoN sol M.det N) (hd : DemoraN sol M.det N d) {F : Finset (List Bool)} (hF : Enganador sol N d F) :
    F.card ≤ 2 ^ b :=
  (curva_memoria_demora M hs hd hF).trans hb

/-- **La curva en `log₂`.** Hacen falta al menos `⌈log₂ |F|⌉` bits. -/
theorem curva_clog {σ : Type*} [Fintype σ] (M : Memoria σ) {b : ℕ} (hb : Fintype.card σ ≤ 2 ^ b)
    (hs : SanoN sol M.det N) (hd : DemoraN sol M.det N d) {F : Finset (List Bool)} (hF : Enganador sol N d F) :
    Nat.clog 2 F.card ≤ b :=
  Nat.clog_le_of_le_pow (curva_bits M hb hs hd hF)

/-- **Con demora `N` no se distingue nada**: el engañador tiene a lo sumo un elemento. La curva llega a 1. -/
theorem enganador_demora_total {F : Finset (List Bool)} (hF : Enganador sol N N F) : F.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp p' hp'
  by_contra hne
  obtain ⟨h1, h2⟩ := distinguibles_largo (hF p hp p' hp' hne)
  rw [List.eq_nil_of_length_eq_zero (by omega : p.length = 0),
    List.eq_nil_of_length_eq_zero (by omega : p'.length = 0)] at hne
  exact hne rfl

/-! ## El caso de `unica m` -/

/-- `trueⁱ` y `trueʲ` (`i < j ≤ m`) se distinguen a demora `d < m`, con `w = true^(m−j) ++ [false]`. -/
theorem unos_distinguibles {m d i j : ℕ} (hd : d < m) (hij : i < j) (hjm : j ≤ m) :
    Distinguibles (unica m) (2 * m) d (replicate i true) (replicate j true) := by
  set w := replicate (m - j) true ++ [false] with hw
  have hx : replicate i true ++ w = replicate (i + (m - j)) true ++ false :: [] := by
    rw [hw, ← List.append_assoc, ← List.replicate_add]
  have hy : replicate j true ++ w = replicate m true ++ [false] := by
    rw [hw, ← List.append_assoc, ← List.replicate_add, Nat.add_sub_cancel' hjm]
  have hlx : (replicate i true ++ w).length = i + (m - j) + 1 := by rw [hx]; simp
  have hly : (replicate j true ++ w).length = m + 1 := by rw [hy]; simp
  have hmuerto : ¬ Vivo (unica m) (2 * m - (replicate i true ++ w).length) (replicate i true ++ w) := by
    rw [vivo_iff (by omega), hx]; exact muerto_cero (by omega) []
  have hvivo : Vivo (unica m) (2 * m - (replicate j true ++ w).length) (replicate j true ++ w) := by
    rw [vivo_iff (by omega), hy]
    refine ⟨replicate (m - 1) false, ?_⟩
    rw [objetivo, List.append_assoc]; congr 1
    rw [List.singleton_append, ← List.replicate_succ]; congr 1; omega
  exact ⟨w, by omega, by omega, .inl ⟨hmuerto, hvivo⟩⟩

/-- `[false]` (muerto) y `trueⁱ` (`i ≤ m`, vivo) se distinguen a demora `d < m`, con `w = []`. -/
theorem cero_distinguible {m d i : ℕ} (hd : d < m) (him : i ≤ m) :
    Distinguibles (unica m) (2 * m) d [false] (replicate i true) := by
  refine ⟨[], by simp; omega, by simp; omega, .inl ⟨?_, ?_⟩⟩
  · rw [List.append_nil, vivo_iff (by simp; omega)]
    exact muerto_cero (k := 0) (by omega) []
  · rw [List.append_nil, vivo_iff (by simp; omega)]
    exact ⟨replicate (m - i) true ++ replicate m false, by
      rw [objetivo, ← List.append_assoc, ← replicate_add, Nat.add_sub_cancel' him]⟩

/-- Los prefijos `true⁰ … trueᵐ`. -/
def unosHasta (m : ℕ) : Finset (List Bool) := (Finset.range (m + 1)).image fun i => replicate i true

/-- **El engañador de `unica m`**: `[false]` y los `m + 1` prefijos `trueⁱ`. -/
def enganadorUnica (m : ℕ) : Finset (List Bool) := insert [false] (unosHasta m)

theorem card_unosHasta (m : ℕ) : (unosHasta m).card = m + 1 := by
  rw [unosHasta, Finset.card_image_of_injective _ (List.replicate_left_injective true), Finset.card_range]

theorem card_enganadorUnica (m : ℕ) : (enganadorUnica m).card = m + 2 := by
  rw [enganadorUnica, Finset.card_insert_of_notMem, card_unosHasta]
  simp only [unosHasta, Finset.mem_image, Finset.mem_range, not_exists, not_and]
  intro i _ h
  have := congrArg List.head? h
  cases i <;> simp [List.replicate_succ] at this

/-- **El engañador de `unica m` funciona** a toda demora `d < m`. -/
theorem enganador_unica {m d : ℕ} (hd : d < m) : Enganador (unica m) (2 * m) d (enganadorUnica m) := by
  have unos : ∀ i j, i ≤ m → j ≤ m → i ≠ j →
      Distinguibles (unica m) (2 * m) d (replicate i true) (replicate j true) := by
    intro i j hi hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact unos_distinguibles hd h hj
    · exact distinguibles_symm (unos_distinguibles hd h hi)
  intro p hp p' hp' hne
  simp only [enganadorUnica, unosHasta, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hp hp'
  rcases hp with rfl | ⟨i, hi, rfl⟩ <;> rcases hp' with rfl | ⟨j, hj, rfl⟩
  · exact absurd rfl hne
  · exact cero_distinguible hd (by omega)
  · exact distinguibles_symm (cero_distinguible hd (by omega))
  · exact unos i j (by omega) (by omega) (fun h => hne (by rw [h]))

/-- **La cota inferior, afinada desde la curva.** Con `m + 1` estados o menos, un detector sano en `unica m`
tiene demora al menos `m`. -/
theorem cota_inferior_fina {σ : Type*} [Fintype σ] (M : Memoria σ) {m d : ℕ} (hcard : Fintype.card σ ≤ m + 1)
    (hs : SanoN (unica m) M.det (2 * m)) (hd : DemoraN (unica m) M.det (2 * m) d) : m ≤ d := by
  by_contra h
  have := curva_memoria_demora M hs hd (enganador_unica (show d < m by omega))
  rw [card_enganadorUnica] at this
  omega

/-- **`cota_inferior` de `BombeoDetector`, recuperada desde la curva.** -/
theorem cota_inferior_desde_curva {σ : Type*} [Fintype σ] (M : Memoria σ) {m d : ℕ}
    (hcard : Fintype.card σ ≤ m) (hs : SanoN (unica m) M.det (2 * m))
    (hd : DemoraN (unica m) M.det (2 * m) d) : m ≤ d :=
  cota_inferior_fina M (by omega) hs hd

/-! ## La cota se alcanza: un contador con `m + 2` estados

`contadorUnos` de `BombeoDetector` tiene `m + 3` estados. Dos sobran: «van `m` unos» y «ya en los ceros» tienen las
mismas transiciones (un cero sigue, un uno mata). Fundirlos da `m + 2` estados, el tamaño del engañador. -/

/-- La transición del contador fino: `none` es muerto, `some k` es «van `k` unos» (con `k = m`, también los ceros). -/
def pasoF (m : ℕ) : Option (Fin (m + 1)) → Bool → Option (Fin (m + 1))
  | none, _ => none
  | some k, true => if h : k.val < m then some ⟨k.val + 1, by omega⟩ else none
  | some k, false => if k.val = m then some k else none

/-- **El contador fino**: `m + 2` estados. -/
def contadorFino (m : ℕ) : Memoria (Option (Fin (m + 1))) := ⟨some 0, pasoF m, fun s => s.isNone⟩

/-- Fundir los dos estados equivalentes del contador. -/
def fundir (m : ℕ) : EstadoC m → Option (Fin (m + 1))
  | none => none
  | some none => some (Fin.last m)
  | some (some k) => some k

theorem fundir_paso (m : ℕ) (s : EstadoC m) (b : Bool) : fundir m (pasoC m s b) = pasoF m (fundir m s) b := by
  rcases s with _ | _ | k
  · cases b <;> rfl
  · cases b <;> simp [pasoC, pasoF, fundir]
  · cases b
    · simp only [pasoC, pasoF, fundir]
      split_ifs with h
      · simp [Fin.ext_iff, h]
      · rfl
    · simp only [pasoC, pasoF, fundir]
      split_ifs <;> rfl

theorem fundir_estado (m : ℕ) (p : List Bool) :
    fundir m ((contadorUnos m).estado p) = (contadorFino m).estado p := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p b ih =>
    simp only [Memoria.estado_append, foldl_cons, foldl_nil]
    rw [← ih]
    exact fundir_paso m _ b

theorem fino_det (m : ℕ) : (contadorFino m).det = (contadorUnos m).det := by
  funext p
  change ((contadorFino m).estado p).isNone = ((contadorUnos m).estado p).isNone
  rw [← fundir_estado]
  rcases (contadorUnos m).estado p with _ | _ | _ <;> rfl

theorem card_fino (m : ℕ) : Fintype.card (Option (Fin (m + 1))) = m + 2 := by simp

/-- **La curva es exacta en `unica m` con demora 0.** El contador fino tiene `m + 2` estados, es sano y tiene
demora 0; y todo detector sano con demora 0 tiene al menos `m + 2` estados. -/
theorem curva_exacta_unica {m : ℕ} (hm : 1 ≤ m) :
    (Fintype.card (Option (Fin (m + 1))) = m + 2 ∧ SanoN (unica m) (contadorFino m).det (2 * m) ∧
      DemoraN (unica m) (contadorFino m).det (2 * m) 0) ∧
    ∀ {σ : Type} [Fintype σ] (M : Memoria σ), SanoN (unica m) M.det (2 * m) →
      DemoraN (unica m) M.det (2 * m) 0 → m + 2 ≤ Fintype.card σ := by
  refine ⟨⟨card_fino m, ?_, ?_⟩, fun M hs hd => ?_⟩
  · rw [fino_det]; exact contador_sano m
  · rw [fino_det]; exact contador_demora m
  · have := curva_memoria_demora M hs hd (enganador_unica (show 0 < m by omega))
    rwa [card_enganadorUnica] at this

/-! ## Control: la curva baja, por enumeración

En `unica 2` (`N = 4`): con `d = 0` el mayor engañador mide 4 (cota de `curva_exacta_unica`, alcanzada); con
`d = 2` mide 2 (hay uno de 2, y no hay tres prefijos distinguibles de a pares); con `d = 4` mide 1. -/

/-- Todas las listas de largo a lo sumo `k`. -/
def listasHasta (k : ℕ) : List (List Bool) := (List.range (k + 1)).flatMap listasDe

theorem mem_listasHasta {k : ℕ} {q : List Bool} : q ∈ listasHasta k ↔ q.length ≤ k := by
  simp only [listasHasta, List.mem_flatMap, List.mem_range, mem_listasDe]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨q.length, by omega, rfl⟩

/-- `Distinguibles` como booleano, por enumeración de los sufijos. -/
def distB (sol : List Bool → Bool) (N d : ℕ) (p p' : List Bool) : Bool :=
  (listasHasta N).any fun w => decide ((p ++ w).length + d ≤ N) && decide ((p' ++ w).length + d ≤ N) &&
    (vivoB sol (N - (p ++ w).length) (p ++ w) != vivoB sol (N - (p' ++ w).length) (p' ++ w))

theorem bne_iff_casos (a b : Bool) : (a != b) = true ↔ (¬ a = true ∧ b = true) ∨ (a = true ∧ ¬ b = true) := by
  cases a <;> cases b <;> decide

theorem distB_iff (sol : List Bool → Bool) (N d : ℕ) (p p' : List Bool) :
    distB sol N d p p' = true ↔ Distinguibles sol N d p p' := by
  simp only [distB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_casos, vivoB_iff,
    mem_listasHasta, Distinguibles]
  constructor
  · rintro ⟨w, -, ⟨h1, h2⟩, h⟩; exact ⟨w, h1, h2, h⟩
  · rintro ⟨w, h1, h2, h⟩
    exact ⟨w, by simp only [length_append] at h1; omega, ⟨h1, h2⟩, h⟩

/-- Un engañador escrito como lista, comprobado por enumeración. -/
theorem enganador_de_lista {sol : List Bool → Bool} {N d : ℕ} (l : List (List Bool))
    (h : l.all (fun p => l.all fun p' => p == p' || distB sol N d p p') = true) :
    Enganador sol N d l.toFinset := by
  intro p hp p' hp' hne
  simp only [List.all_eq_true] at h
  have := h p (List.mem_toFinset.1 hp) p' (List.mem_toFinset.1 hp')
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  exact (distB_iff _ _ _ _ _).1 (this.resolve_left hne)

/-- Si no hay tres prefijos (de largo `≤ N − d`) distinguibles de a pares, todo engañador mide a lo sumo 2. -/
theorem sin_trios {sol : List Bool → Bool} {N d : ℕ}
    (h : (listasHasta (N - d)).all (fun a => (listasHasta (N - d)).all fun b => (listasHasta (N - d)).all fun c =>
      !(a != b && a != c && b != c && distB sol N d a b && distB sol N d a c && distB sol N d b c)) = true)
    {F : Finset (List Bool)} (hF : Enganador sol N d F) : F.card ≤ 2 := by
  by_contra hc
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := (Finset.two_lt_card (s := F)).1 (by omega)
  have dab := hF a ha b hb hab
  have dac := hF a ha c hc' hac
  have dbc := hF b hb c hc' hbc
  have la := (distinguibles_largo dab).1
  have lb := (distinguibles_largo dab).2
  have lc := (distinguibles_largo dac).2
  simp only [List.all_eq_true] at h
  have := h a (mem_listasHasta.2 (by omega)) b (mem_listasHasta.2 (by omega)) c (mem_listasHasta.2 (by omega))
  rw [← distB_iff] at dab dac dbc
  simp [dab, dac, dbc, hab, hac, hbc] at this

/-- **Control, `d = 0`**: `{[], [true], [true, true], [false]}` es engañador en `unica 2`, comprobado por enumeración
(sin usar `enganador_unica`). -/
theorem control_d0 : Enganador (unica 2) 4 0 [[], [true], [true, true], [false]].toFinset :=
  enganador_de_lista _ (by decide)

/-- **Control, `d = 0`, exacto**: el mayor engañador mide 4. La cota superior sale de la curva con el contador fino;
la inferior, de `control_d0`. -/
theorem control_d0_exacto :
    [[], [true], [true, true], [false]].toFinset.card = 4 ∧
    ∀ F, Enganador (unica 2) 4 0 F → F.card ≤ 4 := by
  refine ⟨by decide, fun F hF => ?_⟩
  have h := curva_memoria_demora (contadorFino 2) (curva_exacta_unica (m := 2) (by omega)).1.2.1
    (curva_exacta_unica (m := 2) (by omega)).1.2.2 hF
  rwa [card_fino] at h

/-- **Control, `d = 2`**: hay un engañador de 2 (`[]` vivo, `[false]` muerto) y ninguno de 3. -/
theorem control_d2 :
    Enganador (unica 2) 4 2 [[], [false]].toFinset ∧ ∀ F, Enganador (unica 2) 4 2 F → F.card ≤ 2 :=
  ⟨enganador_de_lista _ (by decide), fun _ hF => sin_trios (by decide +kernel) hF⟩

/-- **Control, `d = 4`**: con demora igual al horizonte, a lo sumo 1. La curva baja de 4 a 2 a 1. -/
theorem control_d4 : ∀ F, Enganador (unica 2) 4 4 F → F.card ≤ 1 :=
  fun _ hF => enganador_demora_total hF

/-- **Control: los vivos `[]`, `[true]`, `[true, true]` se separan con `d = 0` y se confunden con `d = 2`.** Es lo que
baja la curva: con más demora, el sufijo que los separaba ya no cabe. -/
example : distB (unica 2) 4 0 [] [true] = true ∧ distB (unica 2) 4 2 [] [true] = false ∧
    distB (unica 2) 4 2 [] [true, true] = false ∧ distB (unica 2) 4 2 [true] [true, true] = false := by decide

/-- **Control: «no distinguibles» no es transitiva**, ni con `d = 0`. En `unica 2`, `[]` y `[true]` se distinguen,
pero ninguno de los dos se distingue de `[true, true, false, false]`: es una hoja, y no cabe sufijo que la separe.
Por eso no se construye aquí un detector canónico con una clase por estado. -/
theorem no_transitiva :
    Distinguibles (unica 2) 4 0 [] [true] ∧ ¬ Distinguibles (unica 2) 4 0 [] [true, true, false, false] ∧
      ¬ Distinguibles (unica 2) 4 0 [true, true, false, false] [true] := by
  simp only [← distB_iff]; decide

end Sagitta.Map.Tiempo.CurvaMemoriaDemora
