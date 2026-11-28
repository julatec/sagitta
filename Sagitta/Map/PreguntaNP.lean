import Sagitta.Map.Bloques
import Sagitta.Map.BusquedaPrefijos
import Sagitta.Map.Bucle

/-!
# La pregunta de NP y los dos bucles de la búsqueda

Las piezas de `OtraDireccion.lean`:

1. **La pregunta como lenguaje.** `Pregunta V x k p` habla de tres cadenas; NP habla de lenguajes de una cadena. La
   pregunta se codifica como el par `(x, (k, p))`, que es `delimita x ++ delimita k ++ p`, y se lee con `leeTotal`
   (que no falla nunca: una cadena mal formada se lee como vacía). El lenguaje está en NP, con `r` de certificado.
2. **Los pasos de los dos bucles**, como funciones de tiempo polinomial si la pregunta lo es: `paso1` (el largo mínimo)
   y `paso2` (los bits).
3. **Qué dejan los bucles**: lo mismo que `largoMin` y `buscarBits`; cuándo paran, y que sus estados no crecen.
-/

namespace Sagitta.Map
namespace PreguntaNP

open Bloques BusquedaPrefijos Bucle

/-! ## Abreviaturas del cierre -/

theorem pc {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] {f : α → β} {g : β → γ}
    (hf : EsPolinomial f) (hg : EsPolinomial g) : EsPolinomial (fun a => g (f a)) :=
  Componer.esPolinomial_comp f g hf hg

theorem pp {α β γ : Type} [CodBits α] [CodBits β] [CodBits γ] {f : α → β} {g : α → γ}
    (hf : EsPolinomial f) (hg : EsPolinomial g) : EsPolinomial (fun a => (f a, g a)) :=
  Primero.esPolinomial_pares f g hf hg

theorem p1 {α β : Type} [CodBits α] [CodBits β] : EsPolinomial (fun q : α × β => q.1) :=
  Basicas.esPolinomial_fst

theorem p2 {α β : Type} [CodBits α] [CodBits β] : EsPolinomial (fun q : α × β => q.2) :=
  ExhaustivoTiempo.esPolinomial_snd

/-- Comparar si dos cadenas tienen el mismo largo: ninguna es más corta que la otra. -/
theorem esPolinomial_igualLargo :
    EsPolinomial (fun q : List Bool × List Bool => decide (q.1.length = q.2.length)) := by
  have h1 := ExhaustivoTiempo.esPolinomial_menor
  have h2 : EsPolinomial (fun q : List Bool × List Bool => decide (q.2.length < q.1.length)) :=
    pc (Pares.esPolinomial_swap (α := List Bool) (β := List Bool)) h1
  have h := pc (pp (pc h1 Basicas.esPolinomial_no) (pc h2 Basicas.esPolinomial_no)) Basicas.esPolinomial_y
  have e : (fun q : List Bool × List Bool => decide (q.1.length = q.2.length)) =
      fun q => (!decide (q.1.length < q.2.length)) && !decide (q.2.length < q.1.length) := by
    funext q
    rcases Nat.lt_trichotomy q.1.length q.2.length with hlt | heq | hgt
    · simp [hlt, Nat.ne_of_lt hlt, Nat.lt_asymm hlt]
    · simp [heq]
    · simp [hgt, Nat.ne_of_gt hgt, Nat.lt_asymm hgt]
  rw [e]; exact h

/-! ## 1. La pregunta como lenguaje -/

theorem length_delimita : ∀ u : List Bool, (CodBits.delimita u).length = 2 * u.length + 1
  | [] => rfl
  | b :: u => by simp [CodBits.delimita, length_delimita u]; ring

theorem leeTotal_largo (z : List Bool) :
    (leeTotal z).1.length ≤ z.length ∧ (leeTotal z).2.length ≤ z.length := by
  unfold leeTotal
  cases h : CodBits.lee z with
  | none => simp
  | some q =>
    obtain ⟨u, w⟩ := q
    have e := delimita_de_lee z h
    have := length_delimita u
    have hz : z.length = (CodBits.delimita u).length + w.length := by rw [← e, List.length_append]
    simp only [Option.getD_some]
    omega

/-- Las tres cadenas de una pregunta codificada. -/
def partes (z : List Bool) : List Bool × (List Bool × List Bool) :=
  ((leeTotal z).1, leeTotal (leeTotal z).2)

theorem partes_cod (x k p : List Bool) : partes (CodBits.cod (x, (k, p))) = (x, (k, p)) := by
  show partes (CodBits.delimita x ++ (CodBits.delimita k ++ p)) = _
  simp [partes, cod_leeTotal_delimita]

theorem partes_largo (z : List Bool) : (partes z).2.1.length ≤ z.length := by
  have h1 := (leeTotal_largo z).2
  have h2 := (leeTotal_largo (leeTotal z).2).1
  simp only [partes]; omega

theorem esPolinomial_partes : EsPolinomial partes :=
  pp (pc esPolinomial_leeTotal p1) (pc (pc esPolinomial_leeTotal p2) esPolinomial_leeTotal)

variable (V : List Bool × List Bool → Bool)

/-- **El verificador de la pregunta**: `r` es certificado de `z` si tiene el largo de `k` y `V` acepta `r ++ p`. -/
def verifica (q : List Bool × List Bool) : Bool :=
  decide (q.2.length = (partes q.1).2.1.length) && V ((partes q.1).1, q.2 ++ (partes q.1).2.2)

open Classical in
/-- **La pregunta, como lenguaje** de una cadena. -/
noncomputable def lenguaje : Problema := fun z =>
  decide (Pregunta V (partes z).1 (partes z).2.1 (partes z).2.2)

theorem esPolinomial_verifica (hV : EsPolinomial V) : EsPolinomial (verifica V) := by
  have hP : EsPolinomial (fun q : List Bool × List Bool => partes q.1) := pc p1 esPolinomial_partes
  have hx : EsPolinomial (fun q : List Bool × List Bool => (partes q.1).1) := pc hP p1
  have hk : EsPolinomial (fun q : List Bool × List Bool => (partes q.1).2.1) := pc (pc hP p2) p1
  have hp : EsPolinomial (fun q : List Bool × List Bool => (partes q.1).2.2) := pc (pc hP p2) p2
  have hA : EsPolinomial (fun q : List Bool × List Bool => decide (q.2.length = (partes q.1).2.1.length)) :=
    pc (pp p2 hk) esPolinomial_igualLargo
  have hcat : EsPolinomial (fun q : List Bool × List Bool => q.2 ++ (partes q.1).2.2) :=
    pc (pp p2 hp) Vara.esPolinomial_concat
  have hB : EsPolinomial (fun q : List Bool × List Bool => V ((partes q.1).1, q.2 ++ (partes q.1).2.2)) :=
    pc (pp hx hcat) hV
  exact pc (f := fun q : List Bool × List Bool =>
      (decide (q.2.length = (partes q.1).2.1.length), V ((partes q.1).1, q.2 ++ (partes q.1).2.2)))
    (g := fun b : Bool × Bool => b.1 && b.2) (pp hA hB) Basicas.esPolinomial_y

open Classical in
/-- **La pregunta está en NP**, con `r` de certificado. -/
theorem lenguaje_en_NP (hV : EsPolinomial V) : lenguaje V ∈ NP := by
  refine ⟨Polynomial.X, verifica V, esPolinomial_verifica V hV, fun z => ?_⟩
  show decide (Pregunta V (partes z).1 (partes z).2.1 (partes z).2.2) = true ↔ _
  rw [decide_eq_true_iff]
  simp only [Pregunta, Polynomial.eval_X, verifica, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, hVr⟩
    exact ⟨r, by rw [hr]; exact partes_largo z, by simp [hr], hVr⟩
  · rintro ⟨r, -, hr, hVr⟩
    exact ⟨r, by simpa using hr, hVr⟩

/-- La función que contesta la pregunta, si NP ⊆ P. -/
noncomputable def preg (t : List Bool × (List Bool × List Bool)) : Bool := lenguaje V (CodBits.cod t)

open Classical in
theorem contesta : Contesta V (preg V) := by
  intro x k p
  simp [preg, lenguaje, partes_cod]

theorem esPolinomial_preg (hNP : VerificarImplicaResolver) (hV : EsPolinomial V) : EsPolinomial (preg V) :=
  have h : EsPolinomial (lenguaje V) := hNP _ (lenguaje_en_NP V hV)
  pc (f := fun t : List Bool × (List Bool × List Bool) => CodBits.cod t) Bloques.esPolinomial_cod h

/-! ## 2. Los pasos -/

variable (pr : List Bool × (List Bool × List Bool) → Bool)

/-- El estado: la instancia, lo que falta recorrer y lo que se lleva. -/
abbrev Estado := List Bool × (List Bool × List Bool)

/-- **Paso de la fase 1**: pregunta por el largo de `T`; si hay certificado, se queda con `T`; y sigue con `T.tail`
mientras `T` no sea vacía. -/
def paso1 (s : Estado) : Bool × Estado :=
  (decide (([] : List Bool).length < s.2.1.length),
    (s.1, (s.2.1.tail, if pr (s.1, (s.2.1, ([] : List Bool))) then s.2.1 else s.2.2)))

/-- **Paso de la fase 2**: decide el bit que va antes de `p`, mientras quede `L` por recorrer. -/
def paso2 (s : Estado) : Bool × Estado :=
  (decide (([] : List Bool).length < s.2.1.length),
    (s.1, (s.2.1.tail,
      if decide (([] : List Bool).length < s.2.1.length) then
        (if pr (s.1, (s.2.1.tail, false :: s.2.2)) then false :: s.2.2 else true :: s.2.2)
      else s.2.2)))

theorem esPolinomial_paso1 (hpr : EsPolinomial pr) : EsPolinomial (paso1 pr) := by
  have hx : EsPolinomial (fun s : Estado => s.1) := p1
  have hT : EsPolinomial (fun s : Estado => s.2.1) := pc p2 p1
  have hb : EsPolinomial (fun s : Estado => s.2.2) := pc p2 p2
  have hv : EsPolinomial (fun _ : Estado => ([] : List Bool)) := ExhaustivoTiempo.esPolinomial_vacia
  have hflag := pc (pp hv hT) ExhaustivoTiempo.esPolinomial_menor
  have hq := pc (pp hx (pp hT hv)) hpr
  have hbest := pc (pp hq (pp hT hb)) ExhaustivoTiempo.esPolinomial_si
  exact pp hflag (pp hx (pp (pc hT esPolinomial_cola) hbest))

theorem esPolinomial_paso2 (hpr : EsPolinomial pr) : EsPolinomial (paso2 pr) := by
  have hx : EsPolinomial (fun s : Estado => s.1) := p1
  have hL : EsPolinomial (fun s : Estado => s.2.1) := pc p2 p1
  have hp : EsPolinomial (fun s : Estado => s.2.2) := pc p2 p2
  have hv : EsPolinomial (fun _ : Estado => ([] : List Bool)) := ExhaustivoTiempo.esPolinomial_vacia
  have hflag := pc (pp hv hL) ExhaustivoTiempo.esPolinomial_menor
  have hcola := pc hL esPolinomial_cola
  have hq := pc (pp hx (pp hcola (pc hp esPolinomial_ponerFalso))) hpr
  have hbit := pc (pp hq (pp (pc hp esPolinomial_ponerFalso) (pc hp Vara.esPolinomial_poner)))
    ExhaustivoTiempo.esPolinomial_si
  have hnuevo := pc (pp hflag (pp hbit hp)) ExhaustivoTiempo.esPolinomial_si
  exact pp hflag (pp hx (pp hcola hnuevo))

/-! ## 3. Qué dejan los bucles -/

variable {pr}

theorem mientras_paso1 (x : List Bool) :
    ∀ (T b : List Bool) (n : ℕ), T.length < n →
      mientras (paso1 pr) n (x, (T, b)) = (x, ([], largoMin pr x T b))
  | [], b, n, hn => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp [mientras_succ, paso1, largoMin]
  | c :: T, b, n, hn => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [mientras_succ]
    simp only [paso1, List.length_nil, List.length_cons, Nat.zero_lt_succ, decide_true, ↓reduceIte,
      List.tail_cons]
    rw [mientras_paso1 x T _ n (by simp at hn; omega)]
    rfl

theorem mientras_paso2 (x : List Bool) :
    ∀ (L p : List Bool) (n : ℕ), L.length < n →
      mientras (paso2 pr) n (x, (L, p)) = (x, ([], buscarBits pr x L p))
  | [], p, n, hn => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp [mientras_succ, paso2, buscarBits]
  | c :: L, p, n, hn => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    have ih := fun p => mientras_paso2 x L p n (by simp at hn; omega)
    cases hq : pr (x, (L, false :: p)) <;> simp [mientras_succ, paso2, buscarBits, hq, ih]

/-- Los estados de la fase 1: `T` va perdiendo su primer bit, y lo que se lleva no pasa de `T` ni de lo inicial. -/
theorem iter_paso1 (x : List Bool) :
    ∀ (k : ℕ) (T b : List Bool), ∃ b', (sigue (paso1 pr))^[k] (x, (T, b)) = (x, (T.drop k, b')) ∧
      b'.length ≤ max b.length T.length
  | 0, T, b => ⟨b, rfl, le_max_left _ _⟩
  | k + 1, T, b => by
    rw [Function.iterate_succ_apply]
    set b1 := if pr (x, (T, ([] : List Bool))) then T else b
    have hs : sigue (paso1 pr) (x, (T, b)) = (x, (T.tail, b1)) := rfl
    have hb1 : b1.length ≤ max b.length T.length := by
      simp only [b1]; split_ifs <;> omega
    obtain ⟨b', he, hb'⟩ := iter_paso1 x k T.tail b1
    refine ⟨b', by rw [hs, he, List.drop_tail], ?_⟩
    have : T.tail.length ≤ T.length := by simp
    omega

theorem iter_paso2 (x : List Bool) :
    ∀ (k : ℕ) (L p : List Bool), ∃ p', (sigue (paso2 pr))^[k] (x, (L, p)) = (x, (L.drop k, p')) ∧
      p'.length + (L.drop k).length ≤ p.length + L.length
  | 0, L, p => ⟨p, rfl, by simp⟩
  | k + 1, L, p => by
    rw [Function.iterate_succ_apply]
    obtain ⟨p1, hs, hp1⟩ : ∃ p1, sigue (paso2 pr) (x, (L, p)) = (x, (L.tail, p1)) ∧
        p1.length + L.tail.length ≤ p.length + L.length := by
      cases L with
      | nil => exact ⟨p, by simp [sigue, paso2], by simp⟩
      | cons c L =>
        refine ⟨if pr (x, (L, false :: p)) then false :: p else true :: p, by cases hq : pr (x, (L, false :: p)) <;> simp [sigue, paso2, hq], ?_⟩
        split_ifs <;> simp only [List.length_cons, List.tail_cons] <;> omega
    obtain ⟨p', he, hp'⟩ := iter_paso2 x k L.tail p1
    refine ⟨p', by rw [hs, he, List.drop_tail], ?_⟩
    rw [List.drop_tail] at hp'
    omega

theorem largo_cod (s : Estado) :
    (CodBits.cod s).length = 2 * s.1.length + 2 * s.2.1.length + 2 + s.2.2.length := by
  show (CodBits.delimita s.1 ++ (CodBits.delimita s.2.1 ++ s.2.2)).length = _
  simp [length_delimita]; ring

/-- La fase 1 para a lo sumo en `|T| + 1` pasos. -/
theorem para_paso1 (s : Estado) : Para (paso1 pr) ((CodBits.cod s).length + 1) s := by
  obtain ⟨x, T, b⟩ := s
  obtain ⟨b', he, -⟩ := iter_paso1 (pr := pr) x T.length T b
  refine ⟨T.length, by rw [largo_cod]; simp; omega, ?_⟩
  rw [he]; simp [paso1]

theorem para_paso2 (s : Estado) : Para (paso2 pr) ((CodBits.cod s).length + 1) s := by
  obtain ⟨x, L, p⟩ := s
  obtain ⟨p', he, -⟩ := iter_paso2 (pr := pr) x L.length L p
  refine ⟨L.length, by rw [largo_cod]; simp; omega, ?_⟩
  rw [he]; simp [paso2]

theorem largo_paso1 (s : Estado) (k : ℕ) :
    (CodBits.cod ((sigue (paso1 pr))^[k] s)).length ≤ 2 * (CodBits.cod s).length := by
  obtain ⟨x, T, b⟩ := s
  obtain ⟨b', he, hb'⟩ := iter_paso1 (pr := pr) x k T b
  rw [he, largo_cod, largo_cod]
  simp only [List.length_drop]
  omega

theorem largo_paso2 (s : Estado) (k : ℕ) :
    (CodBits.cod ((sigue (paso2 pr))^[k] s)).length ≤ (CodBits.cod s).length := by
  obtain ⟨x, L, p⟩ := s
  obtain ⟨p', he, hp'⟩ := iter_paso2 (pr := pr) x k L p
  rw [he, largo_cod, largo_cod]
  simp only [List.length_drop] at hp' ⊢
  omega

end PreguntaNP
end Sagitta.Map
