import Sagitta.Map.AlgoritmoEstandar

/-!
# El destino del descenso exhaustivo, por búsqueda de prefijos

La otra dirección de `np_por_destino`: si se pueden contestar en tiempo polinomial las preguntas de NP, el destino del
descenso exhaustivo se halla en tiempo polinomial. Este archivo trae la búsqueda y la prueba de que da **exactamente**
el destino; `OtraDireccion.lean` la arma con máquinas.

**Una sola pregunta.** `pregunta (x, (k, p))`: ¿hay una cadena `r` del largo de `k` tal que `V` acepta `r ++ p`? Es
una pregunta de NP: el certificado es `r`.

**El orden.** El destino es el primer certificado en el orden del descenso (por largo y, dentro de cada largo, con el
último bit como el más significativo), o la última cadena permitida si no hay ninguno. La búsqueda va en dos fases:

1. `largoMin`: recorre los largos de `|vara|` hasta `0` y se queda con el menor que tiene certificado;
2. `buscarBits`: con ese largo, decide los bits de atrás hacia adelante; pone `false` si algún certificado del largo
   termina en `false :: p`, y `true` si no.

Si no hay certificados, todas las preguntas dan no: la primera fase deja la vara y la segunda escribe solo unos, que es
justo el destino en ese caso.

La idea es la de la búsqueda por prefijos (Papadimitriou, §10.3; en Lean, `prefixSearchRun` de cslib-frontier, que
halla *alguna* solución). Aquí hace falta la *primera* en un orden fijo, y por eso el largo va primero y los bits del
más significativo al menos.
-/

namespace Sagitta.Map
namespace BusquedaPrefijos

open Enumera
open Comparar (val)

variable (V : List Bool × List Bool → Bool)

/-- Lo que contesta la pregunta de NP: hay un `r` del largo de `k` con `V (x, r ++ p)`. -/
def Pregunta (x k p : List Bool) : Prop := ∃ r : List Bool, r.length = k.length ∧ V (x, r ++ p) = true

/-- Una función que contesta bien la pregunta. -/
def Contesta (preg : List Bool × (List Bool × List Bool) → Bool) : Prop :=
  ∀ x k p, preg (x, (k, p)) = true ↔ Pregunta V x k p

variable (preg : List Bool × (List Bool × List Bool) → Bool) (x : List Bool)

/-- **Fase 1, el largo mínimo.** Recorre `T`, `T.tail`, …, `[]`; cada vez que hay un certificado de ese largo, se
queda con él. -/
def largoMin : List Bool → List Bool → List Bool
  | [], best => if preg (x, ([], [])) then [] else best
  | b :: T, best => largoMin T (if preg (x, (b :: T, [])) then b :: T else best)

/-- **Fase 2, los bits.** Con `L` por recorrer y el final `p` ya decidido, decide el bit que va antes de `p`. -/
def buscarBits : List Bool → List Bool → List Bool
  | [], p => p
  | _ :: L, p => buscarBits L ((!preg (x, (L, false :: p))) :: p)

/-- **La búsqueda entera**, con la vara `tope`. -/
def destinoBusqueda (tope : List Bool → List Bool) (x : List Bool) : List Bool :=
  buscarBits preg x (largoMin preg x (tope x) (tope x)) []

/-! ### Control: la búsqueda contra el descenso, en ejemplos

Con una pregunta contestada a fuerza bruta (probar todas las cadenas del largo), la búsqueda en dos fases da lo mismo
que recorrer el descenso. El caso de dos certificados del mismo largo prueba el orden: `[0, 1]` va antes que `[1, 1]`;
el certificado más largo `[0, 0, 0]` no cuenta. -/

/-- Todas las cadenas de largo `n`. -/
def cadenas : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (cadenas n).flatMap fun r => [false :: r, true :: r]

/-- La pregunta, contestada probando todas las cadenas. -/
def pregFuerza (V : List Bool × List Bool → Bool) (q : List Bool × (List Bool × List Bool)) : Bool :=
  (cadenas q.2.1.length).any fun r => V (q.1, r ++ q.2.2)

#guard
  let V : List Bool × List Bool → Bool := fun q =>
    q.2 == [true, true] || q.2 == [false, true] || q.2 == [false, false, false]
  let tope : List Bool → List Bool := fun _ => [true, true, true]
  destinoBusqueda (pregFuerza V) tope [] == [false, true] &&
    (exhaustivo V (fun y => (tope y).length)).destino [] == [false, true]

#guard
  let V : List Bool × List Bool → Bool := fun _ => false
  let tope : List Bool → List Bool := fun _ => [true, false, true]
  destinoBusqueda (pregFuerza V) tope [] == [true, true, true] &&
    (exhaustivo V (fun y => (tope y).length)).destino [] == [true, true, true]

/-! ## Fase 1 -/

/-- Hay un certificado de largo `n`. -/
def HayDeLargo (n : ℕ) : Prop := ∃ r : List Bool, r.length = n ∧ V (x, r) = true

variable {V preg x}

theorem pregunta_nil_iff (h : Contesta V preg) (k : List Bool) :
    preg (x, (k, [])) = true ↔ HayDeLargo V x k.length := by
  rw [h]; simp [Pregunta, HayDeLargo]

/-- Lo que deja la fase 1: si hay un certificado de largo a lo sumo `|T|`, un largo con certificado y ninguno más
corto; si no, lo que tenía. -/
theorem largoMin_spec (h : Contesta V preg) :
    ∀ (T best : List Bool),
      ((∀ n ≤ T.length, ¬ HayDeLargo V x n) → largoMin preg x T best = best) ∧
      ((∃ n ≤ T.length, HayDeLargo V x n) →
        HayDeLargo V x (largoMin preg x T best).length ∧
        ∀ n < (largoMin preg x T best).length, ¬ HayDeLargo V x n)
  | [], best => by
    have hq := pregunta_nil_iff (x := x) h []
    simp only [List.length_nil] at hq
    refine ⟨fun hno => ?_, fun ⟨n, hn, hhay⟩ => ?_⟩
    · have : preg (x, ([], [])) = false := by
        cases hp : preg (x, ([], [])) with
        | false => rfl
        | true => exact absurd (hq.mp hp) (hno 0 le_rfl)
      simp [largoMin, this]
    · have hn0 : n = 0 := by simpa using hn
      subst hn0
      have : preg (x, ([], [])) = true := hq.mpr hhay
      simp only [largoMin, this, ↓reduceIte, List.length_nil]
      exact ⟨hhay, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  | b :: T, best => by
    obtain ⟨ih1, ih2⟩ := largoMin_spec h T (if preg (x, (b :: T, [])) then b :: T else best)
    have hq := pregunta_nil_iff (x := x) h (b :: T)
    simp only [largoMin]
    by_cases hT : ∃ n ≤ T.length, HayDeLargo V x n
    · refine ⟨fun hno => ?_, fun _ => ih2 hT⟩
      obtain ⟨n, hn, hhay⟩ := hT
      exact absurd hhay (hno n (by simp; omega))
    · push Not at hT
      rw [ih1 hT]
      by_cases hp : preg (x, (b :: T, [])) = true
      · simp only [hp, ↓reduceIte]
        refine ⟨fun hno => absurd (hq.mp hp) (hno _ le_rfl), fun _ => ⟨hq.mp hp, fun n hn => ?_⟩⟩
        exact hT n (by simp at hn; omega)
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun _ => by trivial, fun ⟨n, hn, hhay⟩ => ?_⟩
        rcases Nat.lt_or_ge n (b :: T).length with hlt | hge
        · exact absurd hhay (hT n (by simp at hlt; omega))
        · have : n = (b :: T).length := by omega
          subst this
          exact absurd (hq.mpr hhay) hp

/-! ## Fase 2 -/

theorem val_lt_pot : ∀ l : List Bool, val l < 2 ^ l.length := by
  intro l
  have := val_map_not l
  omega

/-- Partir una cadena no vacía en lo que va antes del último bit y el último bit. -/
theorem partir_ultimo {r : List Bool} {n : ℕ} (hr : r.length = n + 1) : ∃ r' c, r = r' ++ [c] ∧ r'.length = n := by
  rcases List.eq_nil_or_concat r with h | ⟨r', c, h⟩
  · subst h; simp at hr
  · subst h; exact ⟨r', c, by simp [List.concat_eq_append], by simpa using hr⟩

/-- Lo que deja la fase 2 desde `(L, p)`: una cadena `r ++ p` con `r` del largo de `L`. Si hay certificados de esa
forma, es uno, el de menor valor; si no, `r` son puros unos. -/
theorem buscarBits_spec (h : Contesta V preg) :
    ∀ (L p : List Bool),
      (∃ r, r.length = L.length ∧ buscarBits preg x L p = r ++ p) ∧
      (Pregunta V x L p → V (x, buscarBits preg x L p) = true ∧
        ∀ r', r'.length = L.length → V (x, r' ++ p) = true → val (buscarBits preg x L p) ≤ val (r' ++ p)) ∧
      (¬ Pregunta V x L p → buscarBits preg x L p = List.replicate L.length true ++ p)
  | [], p => by
    refine ⟨⟨[], rfl, rfl⟩, fun ⟨r, hr, hV⟩ => ?_, fun _ => rfl⟩
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using hr)
    subst this
    refine ⟨by simpa [buscarBits] using hV, fun r' hr' _ => ?_⟩
    have : r' = [] := List.eq_nil_of_length_eq_zero (by simpa using hr')
    subst this
    simp [buscarBits]
  | a :: L, p => by
    simp only [buscarBits, List.length_cons]
    set b := !preg (x, (L, false :: p)) with hb
    obtain ⟨⟨r, hr, hrr⟩, ha, hn⟩ := buscarBits_spec h L (b :: p)
    have hforma : ∃ r, r.length = L.length + 1 ∧ buscarBits preg x L (b :: p) = r ++ p :=
      ⟨r ++ [b], by simp [hr], by rw [hrr]; simp⟩
    -- Todo certificado `r'' ++ p` con `|r''| = |L| + 1` termina en `false :: p` o en `true :: p`.
    have hpartir : ∀ r'', r''.length = L.length + 1 → ∃ r' c, r'' ++ p = r' ++ c :: p ∧ r'.length = L.length := by
      intro r'' hr''
      obtain ⟨r', c, rfl, hl⟩ := partir_ultimo hr''
      exact ⟨r', c, by simp, hl⟩
    by_cases hq : preg (x, (L, false :: p)) = true
    · -- Hay un certificado que termina en `false :: p`: el bit es `false`.
      have hbf : b = false := by simp [hb, hq]
      have hP : Pregunta V x L (false :: p) := (h x L (false :: p)).mp hq
      rw [hbf] at ha hrr ⊢
      obtain ⟨hV, hmin⟩ := ha hP
      refine ⟨by rw [hbf] at hforma; exact hforma, fun _ => ⟨hV, fun r'' hr'' hV'' => ?_⟩, fun hno => ?_⟩
      · obtain ⟨r', c, heq, hl⟩ := hpartir r'' hr''
        rw [heq] at hV'' ⊢
        cases c with
        | false => exact hmin r' hl hV''
        | true =>
          -- Lo que termina en `false :: p` vale menos que lo que termina en `true :: p`.
          rw [hrr, val_append, val_append, hr, hl]
          have := val_lt_pot r
          rw [hr] at this
          simp only [val, Bool.false_eq_true, ↓reduceIte]
          nlinarith [Nat.one_le_two_pow (n := L.length)]
      · obtain ⟨r0, hr0, hV0⟩ := hP
        exact absurd ⟨r0 ++ [false], by simp [hr0], by simpa using hV0⟩ hno
    · -- Ningún certificado termina en `false :: p`: el bit es `true`.
      have hbt : b = true := by simp [hb, hq]
      have hnoF : ¬ Pregunta V x L (false :: p) := fun hP => hq ((h x L (false :: p)).mpr hP)
      rw [hbt] at ha hn hrr ⊢
      refine ⟨by rw [hbt] at hforma; exact hforma, fun hP => ?_, fun hno => ?_⟩
      · obtain ⟨r0, hr0, hV0⟩ := hP
        obtain ⟨r', c, heq, hl⟩ := hpartir r0 hr0
        rw [heq] at hV0
        cases c with
        | false => exact absurd ⟨r', hl, hV0⟩ hnoF
        | true =>
          obtain ⟨hV, hmin⟩ := ha ⟨r', hl, hV0⟩
          refine ⟨hV, fun r'' hr'' hV'' => ?_⟩
          obtain ⟨s', d, heq', hl'⟩ := hpartir r'' hr''
          rw [heq'] at hV'' ⊢
          cases d with
          | false => exact absurd ⟨s', hl', hV''⟩ hnoF
          | true => exact hmin s' hl' hV''
      · have hnoT : ¬ Pregunta V x L (true :: p) := by
          rintro ⟨r0, hr0, hV0⟩
          exact hno ⟨r0 ++ [true], by simp [hr0], by simpa using hV0⟩
        rw [hn hnoT, List.replicate_succ']
        simp

/-! ## El destino -/

/-- **Cómo reconocer el destino**: una cadena de largo permitido que detiene al descenso, sin certificados antes que
ella en la lista. -/
theorem destino_de_primera {M : List Bool → ℕ} {s : List Bool} (hs : s.length ≤ M x)
    (hpara : V (x, s) = true ∨ M x < (sig s).length)
    (hantes : ∀ u, num u < num s → V (x, u) = false) :
    (exhaustivo V M).destino x = s := by
  have hlargo : ∀ j ≤ num s, (sig^[j] ([] : List Bool)).length ≤ M x := by
    intro j hj
    have : num (sig^[j] ([] : List Bool)) ≤ num s := by rw [num_iter]; exact hj
    exact le_trans (length_le_of_num_le this) hs
  have hruta : ∀ j ≤ num s, (exhaustivo V M).ruta x j = sig^[j] [] := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [DescensoInstancia.ruta_succ, ih (by omega)]
      show (if V (x, sig^[j] []) = true ∨ M x < (sig (sig^[j] [])).length then _ else _) = _
      have hno : V (x, sig^[j] []) = false := hantes _ (by rw [num_iter]; omega)
      have hl := hlargo (j + 1) hj
      rw [Function.iterate_succ_apply'] at hl
      rw [ite_eq_right (by simp [hno]; omega), Function.iterate_succ_apply']
  have hfin : (exhaustivo V M).ruta x (num s) = s := by rw [hruta _ le_rfl, sig_iter_num]
  rw [← hfin]
  apply DescensoInstancia.destino_eq
  · rw [hfin, exhaustivo_esOptimo_iff]; exact hpara
  · intro j hj
    rw [hruta j hj.le, exhaustivo_esOptimo_iff]
    have hno : V (x, sig^[j] []) = false := hantes _ (by rw [num_iter]; exact hj)
    have hl := hlargo (j + 1) hj
    rw [Function.iterate_succ_apply'] at hl
    simp only [hno, Bool.false_eq_true, false_or, not_lt]
    exact hl

/-- **La búsqueda da el destino.** Si `preg` contesta bien la pregunta de NP, la búsqueda en dos fases da exactamente el
destino del descenso exhaustivo con la vara `tope`. -/
theorem destinoBusqueda_eq (h : Contesta V preg) (tope : List Bool → List Bool) :
    destinoBusqueda preg tope x = (exhaustivo V (fun y => (tope y).length)).destino x := by
  set T := tope x
  set R := largoMin preg x T T with hR
  obtain ⟨h1, h2⟩ := largoMin_spec (x := x) h T T
  rw [← hR] at h1 h2
  obtain ⟨⟨r, hr, hrr⟩, ha, hn⟩ := buscarBits_spec (x := x) h R []
  have hdest : destinoBusqueda preg tope x = buscarBits preg x R [] := rfl
  rw [hdest]
  symm
  by_cases hay : ∃ n ≤ T.length, HayDeLargo V x n
  · -- Hay certificados: el de menor valor entre los del largo mínimo.
    obtain ⟨hR1, hR2⟩ := h2 hay
    have hP : Pregunta V x R [] := by
      obtain ⟨c, hc, hV⟩ := hR1; exact ⟨c, hc, by simpa using hV⟩
    obtain ⟨hV, hmin⟩ := ha hP
    have hlen : (buscarBits preg x R []).length = R.length := by rw [hrr]; simp [hr]
    have hRT : R.length ≤ T.length := by
      obtain ⟨n, hn, hhay⟩ := hay
      by_contra hc
      exact hR2 n (by omega) hhay
    apply destino_de_primera (by rw [hlen]; exact hRT) (Or.inl hV)
    intro u hu
    by_contra hVu
    have hVu : V (x, u) = true := by simpa using hVu
    have hul : u.length ≤ R.length := hlen ▸ length_le_of_num_le hu.le
    rcases Nat.lt_or_ge u.length R.length with hlt | hge
    · exact hR2 _ hlt ⟨u, rfl, hVu⟩
    · have hue : u.length = R.length := by omega
      have := hmin u hue (by simpa using hVu)
      have e1 := num_eq_val u
      have e2 := num_eq_val (buscarBits preg x R [])
      rw [hue, ← hlen] at e1
      simp only [List.append_nil] at this
      omega
  · -- No hay: la primera fase deja la vara y la segunda escribe unos.
    push Not at hay
    have hRT : R = T := h1 hay
    have hnoP : ¬ Pregunta V x R [] := by
      rintro ⟨c, hc, hV⟩
      exact hay c.length (by rw [hc, hRT]) ⟨c, rfl, by simpa using hV⟩
    rw [hn hnoP, hRT, List.append_nil]
    have hnum : num (List.replicate T.length true) + 1 = 2 ^ (T.length + 1) - 1 := by
      have e := num_eq_val (List.replicate T.length true)
      have u := val_unos T.length
      simp only [List.length_replicate] at e
      rw [pow_succ]; omega
    apply destino_de_primera (by simp [T])
    · right
      have hs := num_sig (List.replicate T.length true)
      have c := num_cotas (sig (List.replicate T.length true))
      by_contra hc
      push Not at hc
      have hc : (sig (List.replicate T.length true)).length ≤ T.length := hc
      have : 2 ^ ((sig (List.replicate T.length true)).length + 1) ≤ 2 ^ (T.length + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 1 ≤ 2 ^ (T.length + 1) := Nat.one_le_two_pow
      omega
    · intro u hu
      have hul : u.length ≤ T.length := by
        have := length_le_of_num_le hu.le; simpa using this
      cases hVu : V (x, u) with
      | false => rfl
      | true => exact absurd ⟨u, rfl, hVu⟩ (hay u.length hul)

end BusquedaPrefijos
end Sagitta.Map
