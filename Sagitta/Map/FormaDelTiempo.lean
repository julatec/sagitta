import Sagitta.Map.Clases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Data.Nat.Size

/-!
# La forma del tiempo

Una máquina **determinista** tiene un paso que es una función, `f : C → C`. Su tiempo tiene la forma de una **línea**:
la órbita `c, f c, f (f c), …`. Una **no determinista** tiene un paso que es una relación, `R : C → Set C`: desde cada
configuración salen varias. Su tiempo tiene la forma de un **árbol**, y cada rama es un futuro posible. Es la
distinción entre la lógica temporal lineal (Pnueli, 1977) y la ramificada (Clarke y Emerson, 1982).

Este archivo lo escribe y prueba lo que la forma dice:

1. **El frente.** Lo alcanzable en `t` pasos es el `t`-ésimo iterado de `levantar R : Set C → Set C`
   (`frente_eq_iterate`). Es la construcción de subconjuntos de Rabin y Scott: el árbol sobre `C` se vuelve una línea
   sobre `Set C`. Se cambia forma de tiempo por tamaño de estado. Si el paso es una función, cada frente es un punto
   (`frente_determinista`) y hay una sola corrida (`corrida_determinista`).
2. **Las corridas como espacio.** Con `C` discreto, las corridas son un **cerrado** de `ℕ → C` con la topología
   producto (`isClosed_corrida`). Si de cada configuración salen finitas, son un **compacto** (`isCompact_corrida`).
   «Acepta alguna vez» es un **abierto** (`isOpen_alguna_vez`) y «nunca sale de `S`» es un **cerrado**
   (`isClosed_siempre`): la vivacidad y la seguridad de Alpern y Schneider (1985).
3. **König es compacidad** (`konig`): si el árbol tiene ramas de todo largo finito, tiene una infinita.
4. **Lo angélico y lo demoníaco.** «Alguna rama acepta» es que algún frente toque la aceptación (`angelica_iff`): la
   lectura de NP. «Toda rama acepta» tiene, por compacidad, **un tiempo común** (`demoniaca_acotada`): si toda corrida
   acepta alguna vez, todas aceptan antes de un mismo `T`. Es la lectura de coNP, y el tiempo uniforme sale de la
   topología, no de un contador.
5. **El largo de la línea en la aritmética acotada.** Bajar por mitades (PIND, S¹₂) llega a 0 en exactamente `|x|`
   pasos (`llega_por_mitades`); bajar de uno en uno (IND, T¹₂), en `x` (`llega_de_uno_en_uno`). Los dos tiempos son
   líneas; lo que cambia es el largo, y con él la clase: polinomial contra búsqueda local.
6. **La proyección.** NP es la proyección de P (un «existe» acotado), como los analíticos son la proyección de los
   cerrados (la analogía es de Sipser, 1984). El análogo del teorema de separación de Lusin queda enunciado y **abierto**
   (`SeparacionDeLusinNP`).
-/

open Set Topology

namespace Sagitta.Map
namespace Tiempo

variable {C : Type*}

/-! ## 1. Pasos, frentes y la construcción de subconjuntos -/

/-- **Un paso no determinista**: de cada configuración, el conjunto de las siguientes. -/
abbrev Paso (C : Type*) := C → Set C

/-- **El paso determinista** de una función: una sola siguiente. -/
def determinista (f : C → C) : Paso C := fun c => {f c}

/-- **Levantar** el paso a conjuntos: de un conjunto de configuraciones, todas sus siguientes. Es determinista. -/
def levantar (R : Paso C) (S : Set C) : Set C := ⋃ c ∈ S, R c

/-- `Alcanza R t c d`: hay un camino de `t` pasos de `c` a `d`. -/
inductive Alcanza (R : Paso C) : ℕ → C → C → Prop
  | cero (c : C) : Alcanza R 0 c c
  | paso {t : ℕ} {c d e : C} : Alcanza R t c d → e ∈ R d → Alcanza R (t + 1) c e

/-- **El frente** a tiempo `t`: lo alcanzable en exactamente `t` pasos. -/
def frente (R : Paso C) (t : ℕ) (c : C) : Set C := {d | Alcanza R t c d}

/-- **El frente es el iterado del levantamiento**: el árbol sobre `C` es una línea sobre `Set C`. -/
theorem frente_eq_iterate (R : Paso C) (t : ℕ) (c : C) : frente R t c = (levantar R)^[t] {c} := by
  induction t with
  | zero =>
    ext d
    simp only [frente, mem_ofPred_eq, Function.iterate_zero, id_eq, mem_singleton_iff]
    constructor
    · rintro ⟨⟩; rfl
    · rintro rfl; exact .cero d
  | succ t ih =>
    rw [Function.iterate_succ_apply', ← ih]
    ext e
    simp only [frente, levantar, mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro (_ | ⟨h, he⟩); exact ⟨_, h, he⟩
    · rintro ⟨d, h, he⟩; exact .paso h he

/-- **En lo determinista, el frente es un punto**: el árbol es una línea. -/
theorem frente_determinista (f : C → C) (t : ℕ) (c : C) : frente (determinista f) t c = {f^[t] c} := by
  rw [frente_eq_iterate]
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp [levantar, determinista]

/-- Con ramaje finito, cada frente es finito. -/
theorem frente_finito {R : Paso C} (h : ∀ c, (R c).Finite) (t : ℕ) (c : C) : (frente R t c).Finite := by
  rw [frente_eq_iterate]
  induction t with
  | zero => exact finite_singleton c
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ih.biUnion fun d _ => h d

/-! ## 2. Las corridas como espacio -/

/-- **Las corridas** desde `c`: sucesiones infinitas que empiezan en `c` y en cada paso van a una siguiente. -/
def Corrida (R : Paso C) (c : C) : Set (ℕ → C) := {s | s 0 = c ∧ ∀ n, s (n + 1) ∈ R (s n)}

/-- **Una sola corrida determinista**: la órbita. -/
theorem corrida_determinista (f : C → C) (c : C) :
    Corrida (determinista f) c = {fun n => f^[n] c} := by
  ext s
  simp only [Corrida, determinista, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h0, hs⟩
    funext n
    induction n with
    | zero => exact h0
    | succ n ih => rw [hs n, ih, Function.iterate_succ_apply']
  · rintro rfl
    exact ⟨rfl, fun n => Function.iterate_succ_apply' f n c⟩

/-- Cada corrida pasa, a tiempo `n`, por el frente `n`. -/
theorem corrida_en_frente {R : Paso C} {c : C} {s : ℕ → C} (h0 : s 0 = c) (t : ℕ)
    (hs : ∀ n < t, s (n + 1) ∈ R (s n)) : ∀ n ≤ t, s n ∈ frente R n c := by
  intro n hn
  induction n with
  | zero => rw [h0]; exact .cero c
  | succ n ih => exact .paso (ih (by omega)) (hs n (by omega))

/-- Un camino de `t` pasos se escribe como sucesión, quieta después de `t`. -/
theorem Alcanza.camino {R : Paso C} {t : ℕ} {c d : C} (h : Alcanza R t c d) :
    ∃ s : ℕ → C, s 0 = c ∧ (∀ n < t, s (n + 1) ∈ R (s n)) ∧ ∀ n ≥ t, s n = d := by
  induction h with
  | cero c => exact ⟨fun _ => c, rfl, fun n hn => absurd hn (Nat.not_lt_zero n), fun _ _ => rfl⟩
  | @paso t c d e _ he ih =>
    obtain ⟨s, h0, hs, hfin⟩ := ih
    refine ⟨fun n => if n ≤ t then s n else e, by simp [h0], fun n hn => ?_, fun n hn => ?_⟩
    · by_cases hnt : n + 1 ≤ t
      · simp only [hnt, show n ≤ t by omega, ite_true]; exact hs n (by omega)
      · have : n = t := by omega
        subst this
        simp only [hnt, le_refl, ite_true, ite_false]
        rw [hfin n le_rfl]; exact he
    · simp only [show ¬ n ≤ t by omega, ite_false]

variable [TopologicalSpace C] [DiscreteTopology C]

theorem isClosed_eval (n : ℕ) (S : Set C) : IsClosed {s : ℕ → C | s n ∈ S} := by
  have hf : Continuous (fun s : ℕ → C => s n) := continuous_apply n
  exact (isClosed_discrete S).preimage hf

theorem isClosed_inicio (c : C) : IsClosed {s : ℕ → C | s 0 = c} := by
  simpa using isClosed_eval 0 ({c} : Set C)

theorem isClosed_paso (R : Paso C) (n : ℕ) : IsClosed {s : ℕ → C | s (n + 1) ∈ R (s n)} := by
  have hf : Continuous (fun s : ℕ → C => (s n, s (n + 1))) :=
    (continuous_apply n).prodMk (continuous_apply (n + 1))
  exact (isClosed_discrete {p : C × C | p.2 ∈ R p.1}).preimage hf

/-- **Las corridas son un cerrado** del espacio de sucesiones. -/
theorem isClosed_corrida (R : Paso C) (c : C) : IsClosed (Corrida R c) := by
  have h0 := isClosed_inicio c
  have hpaso := isClosed_paso R
  have : Corrida R c = {s | s 0 = c} ∩ ⋂ n, {s : ℕ → C | s (n + 1) ∈ R (s n)} := by
    ext s; simp [Corrida]
  rw [this]
  exact h0.inter (isClosed_iInter hpaso)

/-- **Con ramaje finito, las corridas son un compacto**: viven en el producto de los frentes, que son finitos. -/
theorem isCompact_corrida {R : Paso C} (h : ∀ c, (R c).Finite) (c : C) : IsCompact (Corrida R c) := by
  refine (isCompact_univ_pi fun n => (frente_finito h n c).isCompact).of_isClosed_subset
    (isClosed_corrida R c) ?_
  rintro s ⟨h0, hs⟩ n -
  exact corrida_en_frente h0 n (fun m _ => hs m) n le_rfl

/-- **Aceptar alguna vez es un abierto**: se ve en un prefijo finito (vivacidad). -/
theorem isOpen_alguna_vez (A : Set C) : IsOpen {s : ℕ → C | ∃ n, s n ∈ A} := by
  have : {s : ℕ → C | ∃ n, s n ∈ A} = ⋃ n, (fun s : ℕ → C => s n) ⁻¹' A := by ext s; simp
  rw [this]
  exact isOpen_iUnion fun n => (isOpen_discrete A).preimage (continuous_apply n)

/-- **No salir nunca de `S` es un cerrado**: si se sale, se ve en un prefijo finito (seguridad). -/
theorem isClosed_siempre (S : Set C) : IsClosed {s : ℕ → C | ∀ n, s n ∈ S} := by
  have : {s : ℕ → C | ∀ n, s n ∈ S} = ⋂ n, (fun s : ℕ → C => s n) ⁻¹' S := by ext s; simp
  rw [this]
  exact isClosed_iInter fun n => (isClosed_discrete S).preimage (continuous_apply n)

/-! ## 3. König es compacidad -/

/-- **El lema de König** (1927), como compacidad: si de cada configuración salen finitas y hay caminos de todo largo
desde `c`, hay una corrida infinita. -/
theorem konig {R : Paso C} (h : ∀ c, (R c).Finite) (c : C) (hne : ∀ t, (frente R t c).Nonempty) :
    (Corrida R c).Nonempty := by
  -- La caja: a tiempo `n`, algo de algún frente anterior. Es compacta.
  let caja : Set (ℕ → C) := Set.pi univ fun n => ⋃ k ∈ Finset.range (n + 1), frente R k c
  have hcaja : IsCompact caja := isCompact_univ_pi fun n =>
    ((Finset.range (n + 1)).finite_toSet.biUnion fun k _ => frente_finito h k c).isCompact
  -- Los prefijos correctos de largo `t`; cerrados.
  let Q : ℕ → Set (ℕ → C) := fun t =>
    {s | s 0 = c} ∩ ⋂ n ∈ Finset.range t, {s : ℕ → C | s (n + 1) ∈ R (s n)}
  have hQ : ∀ t, IsClosed (Q t) := fun t =>
    (isClosed_inicio c).inter (isClosed_biInter fun n _ => isClosed_paso R n)
  let P : ℕ → Set (ℕ → C) := fun t => caja ∩ Q t
  have hcerr : ∀ t, IsClosed (P t) := fun t =>
    (isClosed_set_pi fun n _ => isClosed_discrete _).inter (hQ t)
  have hdec : ∀ t, P (t + 1) ⊆ P t := by
    rintro t s ⟨hc, h0, hs⟩
    refine ⟨hc, h0, ?_⟩
    simp only [mem_iInter, Finset.mem_range] at hs ⊢
    exact fun n hn => hs n (by omega)
  have hnoe : ∀ t, (P t).Nonempty := by
    intro t
    obtain ⟨d, hd⟩ := hne t
    obtain ⟨s, h0, hs, hfin⟩ := Alcanza.camino hd
    refine ⟨s, fun n _ => ?_, h0, ?_⟩
    · simp only [mem_iUnion, Finset.mem_range, exists_prop]
      by_cases hn : n ≤ t
      · exact ⟨n, by omega, corrida_en_frente h0 t hs n hn⟩
      · exact ⟨t, by omega, by rw [hfin n (by omega)]; exact hd⟩
    · simp only [mem_iInter, Finset.mem_range]; exact hs
  obtain ⟨s, hs⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed P hdec hnoe
    (hcaja.inter_right (hQ 0)) hcerr
  simp only [mem_iInter] at hs
  refine ⟨s, (hs 0).2.1, fun n => ?_⟩
  have := (hs (n + 1)).2.2
  simp only [mem_iInter, Finset.mem_range] at this
  exact this n (by omega)

/-! ## 4. Lo angélico y lo demoníaco -/

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- **Lo angélico es el frente** (la lectura de NP): si el paso es total, alguna corrida acepta alguna vez si y solo
si algún frente toca la aceptación. -/
theorem angelica_iff {R : Paso C} (htot : ∀ c, (R c).Nonempty) (c : C) (A : Set C) :
    (∃ s ∈ Corrida R c, ∃ n, s n ∈ A) ↔ ∃ t, (frente R t c ∩ A).Nonempty := by
  constructor
  · rintro ⟨s, ⟨h0, hs⟩, n, hn⟩
    exact ⟨n, s n, corrida_en_frente h0 n (fun m _ => hs m) n le_rfl, hn⟩
  · rintro ⟨t, d, hd, hA⟩
    obtain ⟨s, h0, hs, hfin⟩ := Alcanza.camino hd
    -- Después de `t`, se sigue cualquier siguiente.
    let g : C → C := fun c => (htot c).some
    let s' : ℕ → C := fun n => if n ≤ t then s n else g^[n - t] d
    refine ⟨s', ⟨by simp [s', h0], fun n => ?_⟩, t, by simp [s', hfin t le_rfl, hA]⟩
    by_cases hnt : n + 1 ≤ t
    · simp only [s', hnt, show n ≤ t by omega, ite_true]; exact hs n (by omega)
    · simp only [s', hnt, ite_false]
      have hk : n + 1 - t = (n - t) + 1 := by omega
      rw [hk, Function.iterate_succ_apply']
      by_cases hn : n ≤ t
      · have : n = t := by omega
        subst this
        simp only [le_refl, ite_true, Nat.sub_self, Function.iterate_zero, id_eq, hfin n le_rfl]
        exact (htot d).some_mem
      · simp only [hn, ite_false]; exact (htot _).some_mem

/-- **Lo demoníaco tiene un tiempo común** (la lectura de coNP): con ramaje finito, si toda corrida acepta alguna
vez, hay un `T` antes del cual aceptan todas. Es compacidad: los abiertos «acepta a tiempo `n`» cubren el compacto
de las corridas, y un subcubrimiento finito da el tope. -/
theorem demoniaca_acotada {R : Paso C} (h : ∀ c, (R c).Finite) (c : C) (A : Set C)
    (hA : ∀ s ∈ Corrida R c, ∃ n, s n ∈ A) : ∃ T, ∀ s ∈ Corrida R c, ∃ n ≤ T, s n ∈ A := by
  obtain ⟨F, hF⟩ := (isCompact_corrida h c).elim_finite_subcover (fun n => (fun s : ℕ → C => s n) ⁻¹' A)
    (fun n => (isOpen_discrete A).preimage (continuous_apply n))
    (fun s hs => by obtain ⟨n, hn⟩ := hA s hs; exact mem_iUnion.2 ⟨n, hn⟩)
  refine ⟨F.sup id, fun s hs => ?_⟩
  obtain ⟨n, hn, hsn⟩ := mem_iUnion₂.1 (hF hs)
  exact ⟨n, Finset.le_sup (f := id) hn, hsn⟩

/-! ## 5. El largo de la línea: PIND contra IND -/

theorem iterate_mitad (x k : ℕ) : (fun y => y / 2)^[k] x = x / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, Nat.div_div_eq_div_mul, pow_succ]

/-- **Por mitades, la línea mide `|x|`** (PIND, S¹₂): `x` llega a 0 en `k` mitades si y solo si `|x| ≤ k`. -/
theorem llega_por_mitades (x k : ℕ) : (fun y => y / 2)^[k] x = 0 ↔ Nat.size x ≤ k := by
  rw [iterate_mitad, Nat.size_le]
  constructor
  · intro h
    by_contra hc
    have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.pow_pos (n := k) (by norm_num : 0 < 2))
    omega
  · exact Nat.div_eq_of_lt

theorem iterate_pred (x k : ℕ) : (fun y => y - 1)^[k] x = x - k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih]; omega

/-- **De uno en uno, la línea mide `x`** (IND, T¹₂): `x` llega a 0 en `k` pasos si y solo si `x ≤ k`. -/
theorem llega_de_uno_en_uno (x k : ℕ) : (fun y => y - 1)^[k] x = 0 ↔ x ≤ k := by
  rw [iterate_pred]; omega

/-! ## 6. La proyección: NP como analítico -/

/-- **El análogo del teorema de separación de Lusin**: dos problemas de NP disjuntos se separan con uno de P. Para
los conjuntos analíticos (proyecciones de cerrados) el teorema de Lusin dice que dos disjuntos se separan con un
Borel (Kechris, *Classical Descriptive Set Theory*, 1995, teorema 14.7). Sipser (1984) propuso la analogía entre NP y
los analíticos; leer P como Borel y esta separación como su análogo es una extensión nuestra. Aquí es la pregunta de los
**pares NP disjuntos**: Grollmann y Selman (1988) muestran que si P ≠ UP hay pares que P no separa, así que se espera
falsa. **Abierta.** -/
def SeparacionDeLusinNP : Prop :=
  ∀ A ∈ NP, ∀ B ∈ NP, (∀ x, ¬ (A x = true ∧ B x = true)) →
    ∃ S ∈ P, (∀ x, A x = true → S x = true) ∧ (∀ x, B x = true → S x = false)

end Tiempo
end Sagitta.Map
