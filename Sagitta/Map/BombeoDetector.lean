import Sagitta.Map.DemoraEfectiva
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Option

/-!
# Bombeo del detector: memoria contra demora

Sobre `ArbolElecciones` y `DemoraEfectiva`. Un detector de **memoria finita** es un autómata: un estado inicial, una
transición por bit y una alarma por estado (`Memoria`). Se trabaja con `SanoN` y `DemoraN`, con horizonte `N`; la
`Demora` global es vacía en fórmulas con solución (`demora_global_degenera`).

## Lo que se prueba

* **Mismo estado, mismo veredicto** (`Memoria.det_ext`): dos prefijos en el mismo estado dan la misma alarma en
  toda extensión común.
* **El bombeo con demora** (`bombeo_demora`, `bombeo_memoria`). Si `x` está muerto, `y` está vivo y el detector no
  distingue sus extensiones, entonces `N < max |x| |y| + d`. Con memoria finita: `r` y `s` en el mismo estado,
  `r ++ w` muerto y `s ++ w` vivo. El detector tendría que marcar las extensiones de largo `d` de `r ++ w`; son
  las mismas que las de `s ++ w`, y una de ellas va camino a la solución.
* **La familia** (`objetivo`, `unica`): `N = 2m` y la única solución es `trueᵐ ++ falseᵐ` (`una_solucion`). Estar
  vivo es ser prefijo del objetivo (`vivo_iff`).
* **La cota inferior** (`cota_inferior`): con a lo sumo `m` estados, sano y con demora `d`, vale `d ≥ m`. Por
  palomar, `trueⁱ` y `trueʲ` (`i < j ≤ m`) comparten estado; con `w = true^(m−j) ++ [false]` se aplica el bombeo.
  En bits (`cota_bits`): si `card σ ≤ 2^b ≤ m`, la demora es al menos `m`.
* **El umbral** (`contadorUnos`, `umbral_memoria`): un contador con `m + 3` estados es sano y tiene demora 0
  (`contador_sano`, `contador_demora`). Así el umbral está en `log₂ m` bits, más una constante: con
  `⌈log₂ (m + 3)⌉` bits alcanza la demora 0; con `⌊log₂ m⌋` bits la demora ya es al menos `m`, la mitad de la profundidad.

## Controles

* `una_solucion`: la familia tiene exactamente una solución de largo `2m`, y la raíz está viva.
* `contador_sano`, `contador_demora`: las hipótesis de lo positivo se cumplen.
* `miope_control`: para `m ≥ 3`, el detector `miope (m − 3)` tiene `m` estados, es sano y tiene demora `m + 2`.
  Cumple las hipótesis de `cota_inferior`, así que la cota no es vacía, y queda a 2 de lo alcanzable.
* Los `example` del final: el palomar en `m = 3`, por `decide`. `miope 0` pone `true¹` y `true²` en el mismo estado;
  `true² false` está muerto, `true³ false` vivo, y por eso `miope 0` no tiene demora 2.

## La conexión (referencias de memoria, sin verificar)

* Es el **lema de bombeo** de los autómatas finitos (Rabin y Scott, 1959) y el teorema de **Myhill–Nerode** (Myhill
  1957, Nerode 1958), leídos como «memoria del detector contra demora». Myhill–Nerode cuenta las clases de prefijos
  que hay que distinguir; aquí, para demora 0, hay que distinguir los `m + 1` prefijos `trueᵏ`. Con menos estados
  dos se confunden, y la diferencia solo se puede pagar con demora.
* Mathlib tiene `DFA.pumping_lemma`; no se usó, porque aquí lo que importa es el palomar sobre los estados y el
  veredicto en las extensiones, no el bombeo de un lenguaje regular.

## Lo que NO se prueba

* Que esto escale a máquinas polinomiales. Una máquina con espacio polinomial tiene `2^poli` configuraciones, y en
  una familia con `N` variables el palomar solo fuerza repeticiones si los estados son menos que los prefijos que hay
  que distinguir. Contra `2^poli` estados no fuerza nada: el argumento es de memoria **acotada por constante o por
  `log`**, no de tiempo.
* Que la cota sea exacta: con `m` estados la demora está entre `m` (`cota_inferior`) y `m + 2` (`miope_control`).
  Tampoco se sabe aquí qué pasa con `m + 1` o `m + 2` estados.
* El orden de las variables es fijo, como en `ArbolElecciones`.
-/

namespace Sagitta.Map.Tiempo.BombeoDetector

open List

/-! ## Detectores de memoria finita -/

/-- **Un detector de memoria finita.** Un autómata: estado inicial, transición por bit y una alarma por estado. -/
structure Memoria (σ : Type*) where
  /-- El estado antes de leer nada. -/
  inicio : σ
  /-- La transición: un bit más. -/
  paso : σ → Bool → σ
  /-- La alarma: `true` es «muerto». -/
  alarma : σ → Bool

namespace Memoria

variable {σ : Type*} (M : Memoria σ)

/-- El estado después de leer el prefijo `p`. -/
def estado (p : List Bool) : σ := p.foldl M.paso M.inicio

/-- El detector: la alarma del estado al que llega `p`. -/
def det (p : List Bool) : Bool := M.alarma (M.estado p)

theorem estado_append (p q : List Bool) : M.estado (p ++ q) = q.foldl M.paso (M.estado p) := by
  simp [estado, List.foldl_append]

/-- **Mismo estado, mismo futuro.** Dos prefijos en el mismo estado siguen en el mismo estado tras cualquier
extensión común. -/
theorem estado_ext {p p' : List Bool} (h : M.estado p = M.estado p') (q : List Bool) :
    M.estado (p ++ q) = M.estado (p' ++ q) := by
  rw [estado_append, estado_append, h]

/-- **Mismo estado, mismo veredicto** en toda extensión común. -/
theorem det_ext {p p' : List Bool} (h : M.estado p = M.estado p') (q : List Bool) :
    M.det (p ++ q) = M.det (p' ++ q) := by
  simp only [det, M.estado_ext h q]

end Memoria

/-! ## El bombeo con demora -/

/-- **El bombeo con demora, forma general.** Si `x` está muerto, `y` está vivo y el detector no distingue sus
extensiones, entonces la demora no cabe: `N < max |x| |y| + d`. El detector tendría que marcar las extensiones de
largo `d` de `x`; son las mismas que las de `y`, y una de ellas va camino a una solución. -/
theorem bombeo_demora {sol det : List Bool → Bool} {N d : ℕ} (hs : SanoN sol det N) (hd : DemoraN sol det N d)
    {x y : List Bool} (hxy : ∀ q, det (x ++ q) = det (y ++ q))
    (hx : ¬ Vivo sol (N - x.length) x) (hy : Vivo sol (N - y.length) y) :
    N < max x.length y.length + d := by
  by_contra hlt
  have h1 : x.length + d ≤ N := by omega
  have h2 : y.length + d ≤ N := by omega
  obtain ⟨c, hc, hsol⟩ := hy
  have hq : (c.take d).length = d := by simp; omega
  have hdet : det (y ++ c.take d) = true := by rw [← hxy]; exact hd x h1 hx _ hq
  refine hs (y ++ c.take d) (by simp; omega) hdet ⟨c.drop d, by simp; omega, ?_⟩
  rwa [List.append_assoc, List.take_append_drop]

/-- **El bombeo con memoria finita.** `r` y `s` llegan al mismo estado; `w` deja muerto a `r ++ w` y vivo a
`s ++ w`. Entonces `N < max |r ++ w| |s ++ w| + d`. -/
theorem bombeo_memoria {σ : Type*} (M : Memoria σ) {sol : List Bool → Bool} {N d : ℕ}
    (hs : SanoN sol M.det N) (hd : DemoraN sol M.det N d) {r s w : List Bool} (hrs : M.estado r = M.estado s)
    (hr : ¬ Vivo sol (N - (r ++ w).length) (r ++ w)) (hsv : Vivo sol (N - (s ++ w).length) (s ++ w)) :
    N < max (r ++ w).length (s ++ w).length + d :=
  bombeo_demora hs hd (fun q => M.det_ext (M.estado_ext hrs w) q) hr hsv

/-! ## La familia: una sola solución, `trueᵐ ++ falseᵐ` -/

/-- La única solución de largo `2m`: `m` unos y después `m` ceros. -/
def objetivo (m : ℕ) : List Bool := replicate m true ++ replicate m false

/-- La familia: `p` es solución si y solo si es `objetivo m`. -/
def unica (m : ℕ) (p : List Bool) : Bool := decide (p = objetivo m)

theorem objetivo_length (m : ℕ) : (objetivo m).length = 2 * m := by simp [objetivo]; omega

theorem objetivo_menor {m k : ℕ} (hk : k < m) : (objetivo m)[k]? = some true := by
  rw [objetivo, List.getElem?_append_left (by simpa using hk)]
  simp [hk]

theorem objetivo_mayor {m k : ℕ} (hk : m ≤ k) : (objetivo m)[k]? ≠ some true := by
  rw [objetivo, List.getElem?_append_right (by simpa using hk)]
  simp [List.getElem?_replicate]

/-- **Vivo es ser prefijo** del objetivo (con largo a lo sumo `2m`). -/
theorem vivo_iff {m : ℕ} {p : List Bool} (hp : p.length ≤ 2 * m) :
    Vivo (unica m) (2 * m - p.length) p ↔ p <+: objetivo m := by
  constructor
  · rintro ⟨q, _, h⟩
    exact ⟨q, by simpa [unica] using h⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_, by simp [unica, ht]⟩
    have := congrArg List.length ht
    simp [objetivo_length] at this
    omega

/-- Un prefijo que difiere del objetivo en una posición está muerto. -/
theorem no_prefijo {p t : List Bool} {k : ℕ} {b : Bool} (hp : p[k]? = some b) (ht : t[k]? ≠ some b) :
    ¬ p <+: t := by
  rintro ⟨u, rfl⟩
  obtain ⟨hk, _⟩ := List.getElem?_eq_some_iff.1 hp
  exact ht (by rw [List.getElem?_append_left hk]; exact hp)

/-- Muerto por un cero antes de tiempo: `trueᵏ ++ false :: r` con `k < m`. -/
theorem muerto_cero {m k : ℕ} (hk : k < m) (r : List Bool) :
    ¬ (replicate k true ++ false :: r) <+: objetivo m :=
  no_prefijo (k := k) (b := false) (by simp)
    (by rw [objetivo_menor hk]; simp)

/-- Muerto por un uno de más: la posición `j ≥ m` trae un uno. -/
theorem muerto_uno {m j : ℕ} (hj : m ≤ j) {p : List Bool} (hp : p[j]? = some true) : ¬ p <+: objetivo m :=
  no_prefijo hp (objetivo_mayor hj)

/-- **Control: la familia tiene exactamente una solución de largo `2m`**, y la raíz está viva. -/
theorem una_solucion (m : ℕ) :
    (∃! p : List Bool, p.length = 2 * m ∧ unica m p = true) ∧ Vivo (unica m) (2 * m) [] := by
  refine ⟨⟨objetivo m, ⟨objetivo_length m, by simp [unica]⟩, fun p ⟨_, h⟩ => by simpa [unica] using h⟩,
    objetivo m, objetivo_length m, by simp [unica]⟩

/-! ## La cota inferior -/

/-- **Cota inferior por palomar.** Un detector con a lo sumo `m` estados, sano y con demora `d` en la familia,
tiene `d ≥ m`. Entre `true⁰ … trueᵐ` hay dos, `trueⁱ` y `trueʲ` con `i < j ≤ m`, en el mismo estado. Con
`w = true^(m−j) ++ [false]`, `trueʲ ++ w = trueᵐ false` está vivo y `trueⁱ ++ w` está muerto. -/
theorem cota_inferior {σ : Type*} [Fintype σ] (M : Memoria σ) {m d : ℕ} (hcard : Fintype.card σ ≤ m)
    (hs : SanoN (unica m) M.det (2 * m)) (hd : DemoraN (unica m) M.det (2 * m) d) : m ≤ d := by
  have hlt : Fintype.card σ < Fintype.card (Fin (m + 1)) := by simp; omega
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (m + 1) => M.estado (replicate k true)) hlt
  -- Ordenar: `i < j ≤ m`.
  obtain ⟨i, j, hij, hjm, hst⟩ : ∃ i j : ℕ, i < j ∧ j ≤ m ∧
      M.estado (replicate i true) = M.estado (replicate j true) := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
    · exact ⟨a, b, h, by omega, heq⟩
    · exact ⟨b, a, h, by omega, heq.symm⟩
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
  have := bombeo_memoria M hs hd hst hmuerto hvivo
  rw [hlx, hly] at this
  omega

/-- **Con `b` bits de memoria**: si `card σ ≤ 2^b` y `2^b ≤ m`, la demora es al menos `m`. -/
theorem cota_bits {σ : Type*} [Fintype σ] (M : Memoria σ) {m d b : ℕ} (hb : Fintype.card σ ≤ 2 ^ b)
    (hbm : 2 ^ b ≤ m) (hs : SanoN (unica m) M.det (2 * m)) (hd : DemoraN (unica m) M.det (2 * m) d) : m ≤ d :=
  cota_inferior M (hb.trans hbm) hs hd

/-! ## Una forma normal de las listas -/

/-- Toda lista es `bⁿ`, o `bᵏ` seguido de `!b` y un resto. -/
theorem forma (b : Bool) : ∀ p : List Bool, p = replicate p.length b ∨ ∃ k r, p = replicate k b ++ (!b) :: r
  | [] => Or.inl rfl
  | a :: p => by
    by_cases ha : a = b
    · subst ha
      rcases forma a p with h | ⟨k, r, h⟩
      · left; rw [List.length_cons, replicate_succ, ← h]
      · right; exact ⟨k + 1, r, by rw [h, replicate_succ, List.cons_append]⟩
    · right; exact ⟨0, p, by cases a <;> cases b <;> simp_all⟩

/-! ## El umbral: un contador con `m + 3` estados y demora 0 -/

/-- Estados del contador: `none` es muerto, `some none` es «ya en los ceros», `some (some k)` es «van `k` unos». -/
abbrev EstadoC (m : ℕ) := Option (Option (Fin (m + 1)))

/-- La transición del contador. Un cero antes de `m` unos, o un uno de más, matan. -/
def pasoC (m : ℕ) : EstadoC m → Bool → EstadoC m
  | none, _ => none
  | some none, true => none
  | some none, false => some none
  | some (some k), true => if h : k.val < m then some (some ⟨k.val + 1, by omega⟩) else none
  | some (some k), false => if k.val = m then some none else none

/-- **El detector contador**: cuenta los unos hasta `m` y después solo acepta ceros. -/
def contadorUnos (m : ℕ) : Memoria (EstadoC m) := ⟨some (some 0), pasoC m, fun s => s.isNone⟩

/-- El contador tiene `m + 3` estados: `⌈log₂ (m + 3)⌉` bits. -/
theorem card_contador (m : ℕ) : Fintype.card (EstadoC m) = m + 3 := by simp

theorem contador_det (m : ℕ) (p : List Bool) :
    (contadorUnos m).det p = ((contadorUnos m).estado p).isNone := rfl

theorem pasoC_muerto (m : ℕ) : ∀ q : List Bool, q.foldl (pasoC m) none = none
  | [] => rfl
  | _ :: q => pasoC_muerto m q

theorem contador_muerto_ext {m : ℕ} {p : List Bool} (h : (contadorUnos m).estado p = none) (q : List Bool) :
    (contadorUnos m).estado (p ++ q) = none := by
  rw [Memoria.estado_append, h]; exact pasoC_muerto m q

theorem contador_unos {m : ℕ} : ∀ k (hk : k ≤ m),
    (contadorUnos m).estado (replicate k true) = some (some ⟨k, by omega⟩)
  | 0, _ => rfl
  | k + 1, hk => by
    rw [replicate_succ', Memoria.estado_append, contador_unos k (by omega)]
    simp [contadorUnos, pasoC, show k < m by omega]

theorem contador_unos_de_mas {m n : ℕ} (hn : m < n) : (contadorUnos m).estado (replicate n true) = none := by
  have : replicate n true = replicate m true ++ true :: replicate (n - m - 1) true := by
    rw [← replicate_succ, ← replicate_add]; congr 1; omega
  rw [this, ← List.singleton_append, ← List.append_assoc]
  apply contador_muerto_ext
  rw [Memoria.estado_append, contador_unos m le_rfl]
  simp [contadorUnos, pasoC]

theorem contador_ceros {m : ℕ} : ∀ j, (contadorUnos m).estado (replicate m true ++ replicate (j + 1) false) = some none
  | 0 => by
    rw [Memoria.estado_append, contador_unos m le_rfl]; simp [contadorUnos, pasoC]
  | j + 1 => by
    rw [replicate_succ', ← List.append_assoc, Memoria.estado_append, contador_ceros j]
    simp [contadorUnos, pasoC]

/-- **El contador dice muerto exactamente en los prefijos muertos** (de largo a lo sumo `2m`). -/
theorem contador_det_iff {m : ℕ} {p : List Bool} (hp : p.length ≤ 2 * m) :
    (contadorUnos m).det p = true ↔ ¬ p <+: objetivo m := by
  rcases forma true p with h | ⟨k, r, rfl⟩
  · generalize hn : p.length = n at h
    subst h
    simp only [length_replicate] at hp
    by_cases hnm : n ≤ m
    · have hpre : replicate n true <+: objetivo m := ⟨replicate (m - n) true ++ replicate m false, by
        rw [objetivo, ← List.append_assoc, ← replicate_add, Nat.add_sub_cancel' hnm]⟩
      simp [contador_det, contador_unos n hnm, hpre]
    · have hm : ¬ replicate n true <+: objetivo m :=
        muerto_uno (j := m) le_rfl (by simp [List.getElem?_replicate]; omega)
      simp [contador_det, contador_unos_de_mas (show m < n by omega), hm]
  · simp only [Bool.not_true] at hp ⊢
    rcases lt_trichotomy k m with hk | rfl | hk
    · have hst : (contadorUnos m).estado (replicate k true ++ false :: r) = none := by
        rw [← List.singleton_append, ← List.append_assoc]
        apply contador_muerto_ext
        rw [Memoria.estado_append, contador_unos k hk.le]
        simp [contadorUnos, pasoC, hk.ne]
      simp [contador_det, hst, muerto_cero hk r]
    · rcases forma false r with hr | ⟨j, r', rfl⟩
      · generalize hj : r.length = j at hr
        subst hr
        simp only [length_append, length_cons, length_replicate] at hp
        have hpre : replicate k true ++ false :: replicate j false <+: objetivo k :=
          ⟨replicate (k - j - 1) false, by
            rw [objetivo, List.append_assoc, ← replicate_succ, ← replicate_add]; congr 2; omega⟩
        have hst := contador_ceros (m := k) j
        rw [replicate_succ] at hst
        simp [contador_det, hst, hpre]
      · simp only [Bool.not_false] at hp ⊢
        have hq : replicate k true ++ false :: (replicate j false ++ true :: r') =
            (replicate k true ++ false :: replicate j false) ++ true :: r' := by simp
        have hq2 : replicate k true ++ false :: (replicate j false ++ true :: r') =
            (replicate k true ++ false :: replicate j false) ++ [true] ++ r' := by simp
        have hm : ¬ (replicate k true ++ false :: (replicate j false ++ true :: r')) <+: objetivo k := by
          rw [hq]
          exact muerto_uno (j := k + 1 + j) (by omega)
            (by rw [List.getElem?_append_right (by simp; omega)]; simp [show k + 1 + j - (k + (j + 1)) = 0 by omega])
        have hst : (contadorUnos k).estado (replicate k true ++ false :: (replicate j false ++ true :: r')) =
            none := by
          rw [hq2]
          apply contador_muerto_ext
          have h0 := contador_ceros (m := k) j
          rw [replicate_succ] at h0
          rw [Memoria.estado_append, h0]
          simp [contadorUnos, pasoC]
        simp [contador_det, hst, hm]
    · have hm : ¬ (replicate k true ++ false :: r) <+: objetivo m :=
        muerto_uno (j := m) le_rfl (by rw [List.getElem?_append_left (by simpa using hk)]; simp [hk])
      have hst : (contadorUnos m).estado (replicate k true ++ false :: r) = none :=
        contador_muerto_ext (contador_unos_de_mas hk) _
      simp [contador_det, hst, hm]

/-- **El contador es sano** en la familia. -/
theorem contador_sano (m : ℕ) : SanoN (unica m) (contadorUnos m).det (2 * m) := fun p hp hdet => by
  rw [vivo_iff hp]; exact (contador_det_iff hp).1 hdet

/-- **El contador tiene demora 0**: ve cada prefijo muerto en el momento. -/
theorem contador_demora (m : ℕ) : DemoraN (unica m) (contadorUnos m).det (2 * m) 0 := by
  intro p hp hm q hq
  rw [List.eq_nil_of_length_eq_zero hq, List.append_nil]
  rw [vivo_iff (by omega)] at hm
  exact (contador_det_iff (by omega)).2 hm

/-- **El umbral.** Con `m + 3` estados alcanza la demora 0; con `m` estados o menos la demora es al menos `m`. -/
theorem umbral_memoria (m : ℕ) :
    (Fintype.card (EstadoC m) = m + 3 ∧ SanoN (unica m) (contadorUnos m).det (2 * m) ∧
      DemoraN (unica m) (contadorUnos m).det (2 * m) 0) ∧
    ∀ {σ : Type} [Fintype σ] (M : Memoria σ) (d : ℕ), Fintype.card σ ≤ m →
      SanoN (unica m) M.det (2 * m) → DemoraN (unica m) M.det (2 * m) d → m ≤ d :=
  ⟨⟨card_contador m, contador_sano m, contador_demora m⟩, fun M _ hc hs hd => cota_inferior M hc hs hd⟩

/-! ## Control: un detector miope con `m` estados y demora `m + 2`

La cota `d ≥ m` no es vacía y casi es exacta. `miope c` cuenta los primeros `c` unos, mata con un cero antes de
eso y después se queda ciego. Tiene `c + 3` estados; con `c = m − 3` son `m`, y su demora es `m + 2`. -/

/-- La transición del miope: `none` es muerto, `some none` es ciego, `some (some k)` es «van `k` unos». -/
def pasoMiope (c : ℕ) : Option (Option (Fin (c + 1))) → Bool → Option (Option (Fin (c + 1)))
  | none, _ => none
  | some none, _ => some none
  | some (some k), true => if h : k.val < c then some (some ⟨k.val + 1, by omega⟩) else some none
  | some (some _), false => none

/-- **El detector miope**: mira solo los primeros `c + 1` bits. -/
def miope (c : ℕ) : Memoria (Option (Option (Fin (c + 1)))) := ⟨some (some 0), pasoMiope c, fun s => s.isNone⟩

theorem miope_det (c : ℕ) (p : List Bool) : (miope c).det p = ((miope c).estado p).isNone := rfl

theorem pasoMiope_muerto (c : ℕ) : ∀ q : List Bool, q.foldl (pasoMiope c) none = none
  | [] => rfl
  | _ :: q => pasoMiope_muerto c q

theorem miope_unos {c : ℕ} : ∀ k, (miope c).estado (replicate k true) ≠ none
  | 0 => by simp [Memoria.estado, miope]
  | k + 1 => by
    rw [replicate_succ', Memoria.estado_append]
    have ih := miope_unos (c := c) k
    revert ih
    generalize (miope c).estado (replicate k true) = s
    rcases s with _ | _ | ⟨k, hk⟩
    · simp
    · simp [miope, pasoMiope]
    · intro _; simp only [miope, pasoMiope, foldl_cons, foldl_nil]; split_ifs <;> simp

theorem miope_unos_le {c : ℕ} : ∀ k (hk : k ≤ c), (miope c).estado (replicate k true) = some (some ⟨k, by omega⟩)
  | 0, _ => rfl
  | k + 1, hk => by
    rw [replicate_succ', Memoria.estado_append, miope_unos_le k (by omega)]
    simp [miope, pasoMiope, show k < c by omega]

/-- El miope es sano y tiene demora `2m − c − 1`, para `c < m`. -/
theorem miope_sano_demora {m c : ℕ} (hc : c < m) :
    SanoN (unica m) (miope c).det (2 * m) ∧ DemoraN (unica m) (miope c).det (2 * m) (2 * m - c - 1) := by
  constructor
  · intro p hp hdet
    rw [vivo_iff hp]
    rcases forma true p with h | ⟨k, r, rfl⟩
    · rw [h, miope_det] at hdet
      exact absurd (Option.isNone_iff_eq_none.1 hdet) (miope_unos _)
    · by_cases hk : k < m
      · exact muerto_cero hk r
      · exfalso
        have hk' : c < k := by omega
        have hs : (miope c).estado (replicate k true) = some none := by
          have := miope_unos_le c le_rfl
          rw [show k = c + 1 + (k - c - 1) by omega, replicate_add, replicate_succ', Memoria.estado_append,
            Memoria.estado_append, this]
          simp only [miope, pasoMiope, foldl_cons, foldl_nil, lt_irrefl, dite_false]
          generalize k - c - 1 = n
          induction n with
          | zero => rfl
          | succ n ih => rw [replicate_succ', foldl_append, ih]; rfl
        rw [miope_det, Memoria.estado_append, hs] at hdet
        have : ∀ q : List Bool, q.foldl (miope c).paso (some none) = some none := by
          intro q; induction q with
          | nil => rfl
          | cons b q ih => cases b <;> exact ih
        simp [this] at hdet
  · intro p hp hm q _
    rw [vivo_iff (by omega)] at hm
    rcases forma true p with h | ⟨k, r, rfl⟩
    · exfalso; apply hm
      rw [h]
      exact ⟨replicate (m - p.length) true ++ replicate m false, by
        rw [objetivo, ← List.append_assoc, ← replicate_add, Nat.add_sub_cancel' (by omega)]⟩
    · simp only [length_append, length_replicate, length_cons] at hp
      rw [miope_det, Memoria.estado_append, Memoria.estado_append, miope_unos_le k (by omega)]
      simp only [Bool.not_true, foldl_cons, miope, pasoMiope]
      rw [pasoMiope_muerto, pasoMiope_muerto]; rfl

/-- **Control: la cota inferior no es vacía.** Para `m ≥ 3`, `miope (m − 3)` tiene `m` estados, es sano y tiene
demora `m + 2`: cumple las hipótesis de `cota_inferior`, y la cota `m` queda a 2 de lo que se alcanza. -/
theorem miope_control {m : ℕ} (hm : 3 ≤ m) :
    Fintype.card (Option (Option (Fin (m - 3 + 1)))) = m ∧ SanoN (unica m) (miope (m - 3)).det (2 * m) ∧
      DemoraN (unica m) (miope (m - 3)).det (2 * m) (m + 2) := by
  obtain ⟨hs, hd⟩ := miope_sano_demora (m := m) (c := m - 3) (by omega)
  refine ⟨by simp; omega, hs, ?_⟩
  rwa [show 2 * m - (m - 3) - 1 = m + 2 by omega] at hd

/-! ## Control concreto: el palomar en `m = 3` -/

/-- Todas las listas de largo `k`. -/
def listasDe : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (listasDe k).flatMap fun q => [false :: q, true :: q]

theorem mem_listasDe : ∀ {k : ℕ} {q : List Bool}, q ∈ listasDe k ↔ q.length = k
  | 0, q => by cases q <;> simp [listasDe]
  | k + 1, [] => by simp [listasDe]
  | k + 1, b :: q => by
    simp only [listasDe, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, length_cons,
      Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨r, hr, h | h⟩ <;> (cases h; exact mem_listasDe.1 hr)
    · intro h; exact ⟨q, mem_listasDe.2 h, by cases b <;> simp⟩

/-- `Vivo` como booleano, por enumeración. -/
def vivoB (sol : List Bool → Bool) (k : ℕ) (p : List Bool) : Bool := (listasDe k).any fun q => sol (p ++ q)

theorem vivoB_iff (sol : List Bool → Bool) (k : ℕ) (p : List Bool) : vivoB sol k p = true ↔ Vivo sol k p := by
  simp [vivoB, Vivo, mem_listasDe]

/-- **El palomar, concreto.** En `m = 3`, `miope 0` tiene 3 estados. `true¹` y `true²` caen en el mismo (ciego). Con
`w = [true, false]`, `true² false` está muerto, `true³ false` está vivo, y el detector no los distingue. -/
example : (miope 0).estado [true] = (miope 0).estado [true, true] ∧
    vivoB (unica 3) 3 [true, true, false] = false ∧ vivoB (unica 3) 2 [true, true, true, false] = true ∧
    (miope 0).det [true, true, false, false, false] = false := by decide

/-- Por eso `miope 0` no tiene demora 2 en `m = 3`: el prefijo muerto `true² false` sigue sin alarma dos bits después. -/
example : ¬ DemoraN (unica 3) (miope 0).det 6 2 := by
  intro h
  have hm : ¬ Vivo (unica 3) (6 - [true, true, false].length) [true, true, false] := by
    rw [← vivoB_iff]; decide
  have := h [true, true, false] (by decide) hm [false, false] rfl
  revert this; decide

/-- Y el contador, en cambio, separa los cuatro: `true⁰ … true³` llegan a estados distintos. -/
example : [0, 1, 2, 3].map (fun k => (contadorUnos 3).estado (replicate k true)) =
    [some (some 0), some (some 1), some (some 2), some (some 3)] := by decide

end Sagitta.Map.Tiempo.BombeoDetector
