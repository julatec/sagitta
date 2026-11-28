import Sagitta.Map.AceleracionBlum

/-!
# La aceleración de Blum: existen funciones sin programa óptimo

`AceleracionBlum.lean` probó la mitad condicional: *si* una función tiene aceleración, no tiene programa óptimo y su
piso es una escalera sin último peldaño. Este archivo prueba la otra mitad, la **existencia**, en la medida de Blum
de verdad sobre los códigos de Mathlib (`pasos`, el menor `k` con `evaln k c n ≠ none`).

## Qué se prueba (incondicional)

* `blum`: para toda `r : ℕ → ℕ → ℕ` computable hay una `f` computable, de valores `0` y `1`, con
  `TieneAceleracion r f`: todo programa de `f` tiene otro, también de `f`, con `r(n, costo nuevo) ≤ costo viejo`
  para casi todo `n`. **No queda condicionado a ninguna hipótesis H**: lo único cuantitativo que la prueba necesita
  sale de los dos axiomas de Blum que ya estaban probados (`pasos_lt_top_iff` y que `pasos ≤ K` sea decidible).
* `existe_sin_optimo`: hay una función computable de valores `0`/`1` sin programa óptimo, ni salvo una constante.
* `existe_escalera_sin_piso`: su piso es una escalera infinita, cada peldaño despreciable frente al anterior, y
  debajo de ella cualquier cota se puede subir.
* `blum_no_es_cero` (control): la `f` construida no es la constante `0`, que sí tiene programa óptimo.

## La prueba

Una diagonal con cancelación (la de Blum, en la forma de Hartmanis–Hopcroft y de Young), con el teorema de recursión
de Mathlib (`fixed_point₂`) y s-m-n (`Code.curry`). El programa `e` sabe su propio índice; `prog e w k` es su
«nivel `w`» con datos `k = (s, C, t)`.

1. **La prueba de `i` en la etapa `m`** corre `i` con `r(m, M)` pasos, donde `M = cotaN e (i+1) m` es el menor
   combustible con el que terminan *todos* los programas de nivel `i + 1` con datos `k ≤ m`. En cada etapa se cancela
   al menor `i` no cancelado que pasa la prueba y se hace lo contrario de lo que dice. Si un programa `i` calcula `f`,
   deja de pasar la prueba desde algún punto (`no_pasa`, por un conteo: cada vez que pasa se cancela alguien `≤ i`),
   así que cuesta más que `r(m, M)`.
2. **Cada nivel calcula `f` exactamente** con los datos justos (`nivel_exacto`): `s` es una etapa después de la cual
   los `i < u` ya no compiten, `C` los cancelados hasta ahí, `t` la tabla de `f` antes de `s`. El programa de nivel
   `i + 1` con esos datos `k*` cuesta, para `m ≥ k*`, a lo sumo `M`. De ahí la aceleración, con `r` monótona; para
   `r` cualquiera se usa su envolvente monótona (`rmon`).
3. **Por qué no hizo falta analizar `evaln`.** La nota de `AceleracionBlum.lean` decía que faltaba acotar los pasos
   del programa que simula la cancelación, constructor por constructor. No hace falta: el costo de los niveles no se
   acota desde la sintaxis, se **mide** (`cotaN`, una búsqueda no acotada sobre el predicado primitivo recursivo
   `evaln K c m ≠ none`), y el máximo sobre los datos `k ≤ m` cubre a la vez a todos los programas con datos
   pegados a mano. Es el truco de siempre de la teoría abstracta de Blum («máximo sobre los índices chicos»), y por
   eso el teorema vale en toda medida de Blum. La «propiedad H» que la prueba usa es `cotaN_dom` + `cotaN_spec`, y
   está probada.
4. **La totalidad** (`total`) es una inducción en la etapa y, dentro de la etapa, hacia abajo en el nivel: el nivel
   `w` en la etapa `m` solo consulta etapas anteriores o niveles mayores en la misma etapa.

## La lectura

Hay problemas cuyo piso es una escalera sin último peldaño: para la `f` de Blum, cada algoritmo admite otro mucho
más rápido en casi todas las entradas, y ninguno es el mejor. «El costo del mejor algoritmo» no siempre es un número
(ni una función): puede caer en un hueco del orden de Landau.

## Lo que NO se prueba

* **Que SAT, o cualquier problema natural, tenga aceleración.** La `f` de Blum es artificial, hecha por
  diagonalización. Y hay un contraste conocido (de memoria): la **búsqueda universal de Levin** (1973) da, para los
  problemas de búsqueda de NP, un algoritmo óptimo salvo una constante multiplicativa (y un término aditivo por
  verificar la solución), así que la escalera de Blum **no puede pasar en la búsqueda de una asignación que satisfaga
  una fórmula**. Sí podría pasar, que se sepa, en **decidir que no hay solución** (el lado coNP), donde Levin no da nada.
* **Nada sobre P contra NP.** Que un problema no tenga mejor algoritmo no dice si los de NP tienen uno polinomial.
* Que la aceleración valga para `r` no computable: es falso (ver las notas del proyecto).

## Fuentes

* M. Blum, «A machine-independent theory of the complexity of recursive functions», *J. ACM* 14(2):322–336, 1967,
  doi:10.1145/321386.321395 (verificada).
* De memoria: J. Hartmanis y J. E. Hopcroft, «An overview of the theory of computational complexity», *J. ACM*, 1971;
  P. Young, «Easy constructions in complexity theory: gap and speed-up theorems», *Proc. AMS*, 1973; L. A. Levin,
  «Universal sequential search problems», *Problemy Peredachi Informatsii*, 1973. La prueba de aquí es propia; no
  sigue ninguna de ellas línea por línea.
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map
namespace Tiempo
namespace BlumExiste

open AceleracionBlum

/-! ## 1. La combinatoria de la cancelación, sin computabilidad

Todo lo de esta sección vale para una tabla de pruebas cualquiera `O : ℕ → ℕ → Option ℕ`: `O i m = some y` dice que el
programa `i` «pasa la prueba» en la etapa `m` y que su valor ahí es `y`. -/

section Combinatoria

variable (O : ℕ → ℕ → Option ℕ)

theorem hay_candidato (v m : ℕ) (st : List ℕ) :
    ∃ i, m < i ∨ (v ≤ i ∧ i ∉ st ∧ (O i m).isSome = true) :=
  ⟨m + 1, Or.inl (Nat.lt_succ_self m)⟩

/-- **El elegido de la etapa `m`**: el menor `i ∈ [v, m]`, todavía no cancelado (fuera de `st`), que pasa la prueba;
`m + 1` o más si no hay. -/
def elegido (v m : ℕ) (st : List ℕ) : ℕ := Nat.find (hay_candidato O v m st)

/-- Una etapa: si hay elegido, se cancela (entra a la lista). -/
def pasoC (v s j : ℕ) (st : List ℕ) : List ℕ :=
  if elegido O v (s + j) st ≤ s + j then elegido O v (s + j) st :: st else st

/-- **Los cancelados al empezar la etapa `s + j`** de la construcción de nivel `v` que arranca en la etapa `s` con los
cancelados `C`. -/
def estadoC (v s : ℕ) (C : List ℕ) : ℕ → List ℕ
  | 0 => C
  | j + 1 => pasoC O v s j (estadoC v s C j)

/-- La salida de la etapa `m` con elegido `c`: lo contrario de lo que dice `c` (en `{0, 1}`), o `0` si no hay. -/
def salidaEn (m c : ℕ) : ℕ := if c ≤ m then (if O c m = some 0 then 1 else 0) else 0

/-- **La salida de la construcción de nivel `v` con datos `p = (s, C, t)`**: antes de la etapa `s`, la tabla `t`; desde
ahí, la cancelación que arranca con `C`. -/
def salidaC (v : ℕ) (p : ℕ × List ℕ × List ℕ) (m : ℕ) : ℕ :=
  if m < p.1 then p.2.2.getD m 0 else salidaEn O m (elegido O v m (estadoC O v p.1 p.2.1 (m - p.1)))

/-- Los cancelados de la construcción principal (nivel `0`, desde la etapa `0`, sin nadie cancelado). -/
def S0 (m : ℕ) : List ℕ := estadoC O 0 0 [] m

/-- **La función diagonal de Blum**, la de la construcción principal. -/
def fB (m : ℕ) : ℕ := salidaC O 0 (0, [], []) m

theorem fB_eq (m : ℕ) : fB O m = salidaEn O m (elegido O 0 m (S0 O m)) := by
  simp [fB, salidaC, S0]

theorem salidaEn_le (m c : ℕ) : salidaEn O m c ≤ 1 := by
  unfold salidaEn; split_ifs <;> omega

theorem fB_le (m : ℕ) : fB O m ≤ 1 := by rw [fB_eq]; exact salidaEn_le O _ _

variable {O}

theorem elegido_spec (v m : ℕ) (st : List ℕ) :
    m < elegido O v m st ∨ (v ≤ elegido O v m st ∧ elegido O v m st ∉ st ∧
      (O (elegido O v m st) m).isSome = true) :=
  Nat.find_spec (hay_candidato O v m st)

/-- Si el elegido cae en `[0, m]`, es un candidato de verdad. -/
theorem elegido_de_verdad {v m : ℕ} {st : List ℕ} (h : elegido O v m st ≤ m) :
    v ≤ elegido O v m st ∧ elegido O v m st ∉ st ∧ (O (elegido O v m st) m).isSome = true := by
  rcases elegido_spec (O := O) v m st with h' | h'
  · omega
  · exact h'

/-- El elegido no pasa de ningún candidato. -/
theorem elegido_le {v m i : ℕ} {st : List ℕ} (hv : v ≤ i) (hi : i ∉ st) (hp : (O i m).isSome = true) :
    elegido O v m st ≤ i :=
  Nat.find_min' _ (Or.inr ⟨hv, hi, hp⟩)

theorem mem_pasoC {v s j : ℕ} {st : List ℕ} {x : ℕ} (h : x ∈ st) : x ∈ pasoC O v s j st := by
  unfold pasoC; split_ifs <;> simp [h]

theorem mem_estadoC_mono {v s : ℕ} {C : List ℕ} {x j j' : ℕ} (hj : j ≤ j') (h : x ∈ estadoC O v s C j) :
    x ∈ estadoC O v s C j' := by
  induction hj with
  | refl => exact h
  | step _ ih => exact mem_pasoC ih

/-- **De dónde sale un cancelado**: de `C`, o lo eligió alguna etapa anterior. -/
theorem mem_estadoC {v s : ℕ} {C : List ℕ} {x : ℕ} :
    ∀ {j}, x ∈ estadoC O v s C j → x ∈ C ∨ ∃ j' < j, elegido O v (s + j') (estadoC O v s C j') = x ∧
      x ≤ s + j'
  | 0, h => Or.inl h
  | j + 1, h => by
    simp only [estadoC, pasoC] at h
    split_ifs at h with hc
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨j, Nat.lt_succ_self j, rfl, hc⟩
      · rcases mem_estadoC h with h | ⟨j', hj', h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨j', by omega, h1, h2⟩
    · rcases mem_estadoC h with h | ⟨j', hj', h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨j', by omega, h1, h2⟩

/-- Cuántos de `0, …, i` están cancelados en la construcción principal al empezar la etapa `m`. -/
def cuenta (O : ℕ → ℕ → Option ℕ) (i m : ℕ) : ℕ := ((Finset.range (i + 1)).filter fun c => c ∈ S0 O m).card

theorem cuenta_le (i m : ℕ) : cuenta O i m ≤ i + 1 :=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le

theorem cuenta_mono (i : ℕ) {m m' : ℕ} (h : m ≤ m') : cuenta O i m ≤ cuenta O i m' := by
  unfold cuenta
  refine Finset.card_le_card fun c hc => ?_
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, mem_estadoC_mono h hc.2⟩

theorem S0_succ (m : ℕ) : S0 O (m + 1) = pasoC O 0 0 m (S0 O m) := rfl

/-- **Si `i` pasa la prueba sin estar cancelado, la cuenta sube.** -/
theorem cuenta_sube {i m : ℕ} (hm : i ≤ m) (hi : i ∉ S0 O m) (hp : (O i m).isSome = true) :
    cuenta O i m + 1 ≤ cuenta O i (m + 1) := by
  have hc : elegido O 0 m (S0 O m) ≤ i := elegido_le (Nat.zero_le _) hi hp
  have hcm : elegido O 0 m (S0 O m) ≤ m := hc.trans hm
  have hnot := (elegido_de_verdad hcm).2.1
  have hnew : S0 O (m + 1) = elegido O 0 m (S0 O m) :: S0 O m := by
    rw [S0_succ]; simp only [pasoC, zero_add, hcm, ite_true]
  unfold cuenta
  rw [hnew]
  have : (Finset.range (i + 1)).filter (fun c => c ∈ elegido O 0 m (S0 O m) :: S0 O m) =
      insert (elegido O 0 m (S0 O m)) ((Finset.range (i + 1)).filter fun c => c ∈ S0 O m) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_cons, Finset.mem_insert]
    constructor
    · rintro ⟨h1, rfl | h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨by omega, Or.inl rfl⟩
      · exact ⟨h1, Or.inr h2⟩
  rw [this, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter, not_and]
  exact fun _ => hnot

/-- **La clave**: para cada `i`, desde alguna etapa en adelante `i` está cancelado o no pasa la prueba. Cada vez que
`i` pasa sin estar cancelado se cancela alguien `≤ i`, y eso solo puede pasar `i + 1` veces. -/
theorem clave (i : ℕ) : CasiTodo fun m => i ∈ S0 O m ∨ (O i m).isSome = false := by
  by_contra hno
  simp only [CasiTodo, not_exists, not_forall, not_or, Bool.not_eq_false, exists_prop] at hno
  -- `i` no queda nunca cancelado: si lo estuviera en `m₀`, lo estaría desde ahí.
  have nunca : ∀ m, i ∉ S0 O m := fun m hm => by
    obtain ⟨m', hm', hno', _⟩ := hno m
    exact hno' (mem_estadoC_mono hm' hm)
  have sube : ∀ n, ∃ m, n ≤ cuenta O i m := by
    intro n
    induction n with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨m', hm', -, hp⟩ := hno (max m i)
      refine ⟨m' + 1, ?_⟩
      have a := cuenta_sube (le_of_max_le_right hm') (nunca m') hp
      have b := cuenta_mono (O := O) i (le_of_max_le_left hm')
      omega
  obtain ⟨m, hm⟩ := sube (i + 2)
  have := cuenta_le (O := O) i m
  omega

/-- **La cota inferior, combinatoria**: si las respuestas de `i` en la tabla coinciden con `fB`, desde algún punto `i`
no pasa la prueba. -/
theorem no_pasa {i : ℕ} (hi : ∀ m y, O i m = some y → y = fB O m) :
    CasiTodo fun m => (O i m).isSome = false := by
  obtain ⟨N, hN⟩ := clave (O := O) i
  refine ⟨N, fun m hm => ?_⟩
  rcases hN m hm with h | h
  · exfalso
    rcases mem_estadoC h with h | ⟨m₁, -, he, hle⟩
    · simp at h
    · simp only [zero_add] at he hle
      change elegido O 0 m₁ (S0 O m₁) = i at he
      have hv := (elegido_de_verdad (he ▸ hle : elegido O 0 m₁ (S0 O m₁) ≤ m₁)).2.2
      rw [he] at hv
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hv
      have h1 := hi m₁ y hy
      rw [fB_eq, he, salidaEn, hy] at h1
      simp only [hle, ite_true] at h1
      by_cases hy0 : y = 0
      · subst hy0; simp at h1
      · simp [hy0] at h1
  · exact h

/-- Si los `i < u` ya no compiten, el elegido de nivel `u` es el de nivel `0`. -/
theorem elegido_nivel {u m : ℕ} {st : List ℕ} (h : ∀ i < u, i ∈ st ∨ (O i m).isSome = false) :
    elegido O u m st = elegido O 0 m st := by
  apply le_antisymm
  · rcases elegido_spec 0 m st with h0 | ⟨-, h1, h2⟩
    · exact Nat.find_min' _ (Or.inl h0)
    · by_cases hu : u ≤ elegido O 0 m st
      · exact elegido_le hu h1 h2
      · rcases h (elegido O 0 m st) (by omega) with h3 | h3
        · exact absurd h3 h1
        · rw [h2] at h3; exact absurd h3 (by decide)
  · rcases elegido_spec u m st with h0 | ⟨-, h1, h2⟩
    · exact Nat.find_min' _ (Or.inl h0)
    · exact elegido_le (Nat.zero_le _) h1 h2

theorem casiTodo_lt {P : ℕ → ℕ → Prop} : ∀ u, (∀ i < u, CasiTodo (P i)) → CasiTodo fun m => ∀ i < u, P i m
  | 0, _ => ⟨0, fun _ _ i hi => absurd hi (Nat.not_lt_zero _)⟩
  | u + 1, h => by
    obtain ⟨N₁, h₁⟩ := casiTodo_lt u fun i hi => h i (by omega)
    obtain ⟨N₂, h₂⟩ := h u (by omega)
    refine ⟨max N₁ N₂, fun m hm i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact h₁ m (le_of_max_le_left hm) i hi
    · exact h₂ m (le_of_max_le_right hm)

/-- **Cada nivel, con los datos justos, calcula exactamente `fB`**: para todo `u` hay `p = (s, C, t)` con
`salidaC O u p = fB O`. -/
theorem nivel_exacto (u : ℕ) : ∃ p : ℕ × List ℕ × List ℕ, ∀ m, salidaC O u p m = fB O m := by
  obtain ⟨N, hN⟩ := casiTodo_lt (P := fun i m => i ∈ S0 O m ∨ (O i m).isSome = false) u
    fun i _ => clave i
  refine ⟨(N, S0 O N, (List.range N).map (fB O)), fun m => ?_⟩
  have hest : ∀ j, estadoC O u N (S0 O N) j = S0 O (N + j) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [estadoC, ih, ← add_assoc, S0_succ]
      simp only [pasoC, zero_add]
      rw [elegido_nivel (hN (N + j) (by omega))]
  unfold salidaC
  split_ifs with hm
  · simp [hm]
  · simp only at hm
    rw [hest, show N + (m - N) = m by omega, elegido_nivel (hN m (by omega)), fB_eq]

end Combinatoria

/-! ## 2. La construcción, como función parcial recursiva -/

section Construccion

/-- **El programa de nivel `w` con datos `k`**: `e` con el primer argumento fijo (s-m-n, `Code.curry`). -/
def prog (e : Code) (w k : ℕ) : Code := curry e (Nat.pair w k)
/-- `K` pasos alcanzan para todos los programas de nivel `w` con datos `k ≤ m`, en la entrada `m`. -/
def alcanza (e : Code) (w m K : ℕ) : Bool :=
  (List.range (m + 1)).all fun k => (evaln K (prog e w k) m).isSome
/-- **La cota de la etapa `m` para el nivel `w`**: el menor combustible que alcanza para todos los programas de
nivel `w` con datos `k ≤ m`. Es el truco que evita analizar `evaln`: el costo de un programa compuesto no se acota
desde la sintaxis, se **mide**, y se toma el máximo sobre los índices chicos. -/
def cotaN (e : Code) (w m : ℕ) : Part ℕ := Nat.rfind fun K => Part.some (alcanza e w m K)

theorem primrec_alcanza : Primrec fun q : Code × ℕ × ℕ × ℕ => alcanza q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hm : Primrec fun q : Code × ℕ × ℕ × ℕ => q.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec fun q : Code × ℕ × ℕ × ℕ => List.range (q.2.2.1 + 1) :=
    Primrec.list_range.comp (Primrec.nat_add.comp hm (Primrec.const 1))
  have hc : Primrec fun p : (Code × ℕ × ℕ × ℕ) × ℕ => prog p.1.1 p.1.2.1 p.2 :=
    Primrec₂.comp Code.primrec₂_curry (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have he : Primrec fun p : (Code × ℕ × ℕ × ℕ) × ℕ =>
      evaln p.1.2.2.2 (prog p.1.1 p.1.2.1 p.2) p.1.2.2.1 :=
    primrec_evaln.comp (((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair hc).pair
      (hm.comp Primrec.fst))
  exact Primrec.list_all hl (Primrec.option_isSome.comp he).to₂

theorem partrec_cotaN : Partrec fun q : Code × ℕ × ℕ => cotaN q.1 q.2.1 q.2.2 := by
  have hg : Primrec fun p : (Code × ℕ × ℕ) × ℕ => (p.1.1, p.1.2.1, p.1.2.2, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have h : Primrec₂ fun (q : Code × ℕ × ℕ) (K : ℕ) => alcanza q.1 q.2.1 q.2.2 K :=
    primrec_alcanza.comp hg
  exact Partrec.rfind (Computable₂.partrec₂ h.to_comp)

/-- Un `bif` con una rama total y otra parcial es parcial recursivo. -/
theorem partrec_cond {α σ : Type*} [Primcodable α] [Primcodable σ] {c : α → Bool} {f : α → σ} {g : α →. σ}
    (hc : Computable c) (hf : Computable f) (hg : Partrec g) :
    Partrec fun a => bif c a then Part.some (f a) else g a := by
  have := Partrec.optionCasesOn_right (o := fun a => bif c a then (none : Option Unit) else some ())
    (f := f) (g := fun a (_ : Unit) => g a)
    (Computable.cond hc (Computable.const none) (Computable.const (some ()))) hf
    (hg.comp Computable.fst).to₂
  refine this.of_eq fun a => ?_
  cases c a <;> rfl

variable (r : ℕ → ℕ → ℕ)

/-- **La prueba de `i` en la etapa `m`**: correr `i` con `r(m, cota del nivel i + 1)` pasos. -/
def pruebaP (e : Code) (i m : ℕ) : Part (Option ℕ) :=
  (cotaN e (i + 1) m).map fun K => evaln (r m K) (Denumerable.ofNat Code i) m

/-- El predicado que busca al elegido; solo corre la prueba de los candidatos de verdad. -/
def predP (e : Code) (v m : ℕ) (st : List ℕ) (i : ℕ) : Part Bool :=
  bif (decide (m < i) || decide (i < v) || st.any fun a => decide (a = i)) then Part.some (decide (m < i))
  else (pruebaP r e i m).map Option.isSome

/-- El elegido, como búsqueda no acotada. -/
def elegidoP (e : Code) (v m : ℕ) (st : List ℕ) : Part ℕ := Nat.rfind (predP r e v m st)

/-- Una etapa de la cancelación, parcial. -/
def pasoP (e : Code) (v s j : ℕ) (st : List ℕ) : Part (List ℕ) :=
  (elegidoP r e v (s + j) st).map fun c => if c ≤ s + j then c :: st else st

/-- Los cancelados, por recursión primitiva parcial sobre las etapas. -/
def estadoP (e : Code) (v s : ℕ) (C : List ℕ) (j : ℕ) : Part (List ℕ) :=
  Nat.rec (motive := fun _ => Part (List ℕ)) (Part.some C) (fun y IH => IH.bind fun st => pasoP r e v s y st) j

/-- La salida con elegido `c`, parcial. -/
def salidaP (e : Code) (m c : ℕ) : Part ℕ :=
  bif decide (m < c) then Part.some 0 else (pruebaP r e c m).map fun o => if o = some 0 then 1 else 0

/-- Los datos `(s, C, t)` que van en la entrada. -/
def datos (x : ℕ) : ℕ × List ℕ × List ℕ := Denumerable.ofNat _ x.unpair.1.unpair.2

/-- **La construcción entera**: la entrada es `⟨⟨nivel, datos⟩, m⟩` y `e` es el índice de sí misma (lo pone el
teorema de recursión). -/
def F (e : Code) (x : ℕ) : Part ℕ :=
  bif decide (x.unpair.2 < (datos x).1) then Part.some ((datos x).2.2.getD x.unpair.2 0)
  else (estadoP r e x.unpair.1.unpair.1 (datos x).1 (datos x).2.1 (x.unpair.2 - (datos x).1)).bind fun st =>
    (elegidoP r e x.unpair.1.unpair.1 x.unpair.2 st).bind fun c => salidaP r e x.unpair.2 c

variable {r}

theorem partrec_pruebaP (hr : Computable₂ r) : Partrec fun q : Code × ℕ × ℕ => pruebaP r q.1 q.2.1 q.2.2 := by
  have h1 : Computable fun q : Code × ℕ × ℕ => (q.1, q.2.1 + 1, q.2.2) :=
    (Primrec.fst.pair ((Primrec.succ.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd))).to_comp
  have h2 := partrec_cotaN.comp h1
  have hrr : Computable fun p : (Code × ℕ × ℕ) × ℕ => r p.1.2.2 p.2 :=
    hr.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd
  have h3 : Computable fun p : (Code × ℕ × ℕ) × ℕ =>
      ((r p.1.2.2 p.2, Denumerable.ofNat Code p.1.2.1), p.1.2.2) :=
    (hrr.pair ((Computable.ofNat Code).comp (Computable.fst.comp (Computable.snd.comp Computable.fst)))).pair
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have h4 := primrec_evaln.to_comp.comp h3
  exact (Partrec.map (g := fun (q : Code × ℕ × ℕ) (K : ℕ) => evaln (r q.2.2 K) (Denumerable.ofNat Code q.2.1) q.2.2)
    h2 h4).of_eq fun _ => rfl

theorem partrec_predP (hr : Computable₂ r) :
    Partrec fun q : (Code × ℕ × ℕ × List ℕ) × ℕ => predP r q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2 := by
  have hm : Primrec fun q : (Code × ℕ × ℕ × List ℕ) × ℕ => q.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hv : Primrec fun q : (Code × ℕ × ℕ × List ℕ) × ℕ => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hst : Primrec fun q : (Code × ℕ × ℕ × List ℕ) × ℕ => q.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hlt := Primrec.nat_lt.decide.comp hm Primrec.snd
  have hany := Primrec.list_any (p := fun (q : (Code × ℕ × ℕ × List ℕ) × ℕ) (a : ℕ) => decide (a = q.2)) hst
    (Primrec.eq.decide.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  have hc := Primrec.or.comp (Primrec.or.comp hlt (Primrec.nat_lt.decide.comp Primrec.snd hv)) hany
  have hp := (partrec_pruebaP hr).comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair hm)).to_comp
  have hmap := Partrec.map (g := fun (_ : (Code × ℕ × ℕ × List ℕ) × ℕ) (o : Option ℕ) => o.isSome) hp
    (Primrec.option_isSome.comp Primrec.snd).to_comp
  exact (partrec_cond hc.to_comp hlt.to_comp hmap).of_eq fun _ => rfl

theorem partrec_elegidoP (hr : Computable₂ r) :
    Partrec fun q : Code × ℕ × ℕ × List ℕ => elegidoP r q.1 q.2.1 q.2.2.1 q.2.2.2 :=
  Partrec.rfind (p := fun (q : Code × ℕ × ℕ × List ℕ) (i : ℕ) => predP r q.1 q.2.1 q.2.2.1 q.2.2.2 i)
    (partrec_predP hr)

theorem partrec_pasoP (hr : Computable₂ r) :
    Partrec fun q : (Code × ℕ × ℕ) × ℕ × List ℕ => pasoP r q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2 := by
  have hsj : Primrec fun q : (Code × ℕ × ℕ) × ℕ × List ℕ => q.1.2.2 + q.2.1 :=
    Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  have h1 := (partrec_elegidoP hr).comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp
      (Primrec.snd.comp Primrec.fst)).pair (hsj.pair (Primrec.snd.comp Primrec.snd)))).to_comp
  have h2 := Primrec.ite (c := fun p : ((Code × ℕ × ℕ) × ℕ × List ℕ) × ℕ => p.2 ≤ p.1.1.2.2 + p.1.2.1)
      (Primrec.nat_le.comp Primrec.snd (hsj.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (Partrec.map (g := fun (q : (Code × ℕ × ℕ) × ℕ × List ℕ) (c : ℕ) =>
      if c ≤ q.1.2.2 + q.2.1 then c :: q.2.2 else q.2.2) h1 h2.to_comp).of_eq fun _ => rfl

theorem partrec_estadoP (hr : Computable₂ r) :
    Partrec fun q : (Code × ℕ × ℕ) × List ℕ × ℕ => estadoP r q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2 := by
  have hg : Primrec fun p : ((Code × ℕ × ℕ) × List ℕ × ℕ) × ℕ × List ℕ => (p.1.1, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  have hh := (partrec_pasoP hr).comp hg.to_comp
  exact (Partrec.nat_rec (f := fun q : (Code × ℕ × ℕ) × List ℕ × ℕ => q.2.2)
    (g := fun q => Part.some q.2.1)
    (h := fun (q : (Code × ℕ × ℕ) × List ℕ × ℕ) (p : ℕ × List ℕ) => pasoP r q.1.1 q.1.2.1 q.1.2.2 p.1 p.2)
    (Primrec.snd.comp Primrec.snd).to_comp (Primrec.fst.comp Primrec.snd).to_comp.partrec hh).of_eq
    fun _ => rfl

theorem partrec_salidaP (hr : Computable₂ r) :
    Partrec fun q : Code × ℕ × ℕ => salidaP r q.1 q.2.1 q.2.2 := by
  have hlt := Primrec.nat_lt.decide.comp (Primrec.fst.comp (Primrec.snd (α := Code) (β := ℕ × ℕ)))
    (Primrec.snd.comp Primrec.snd)
  have hp := (partrec_pruebaP hr).comp (Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair
      (Primrec.fst.comp (Primrec.snd (α := Code) (β := ℕ × ℕ))))).to_comp
  have hi := Primrec.ite (c := fun p : (Code × ℕ × ℕ) × Option ℕ => p.2 = some 0)
    (Primrec.eq.comp Primrec.snd (Primrec.const (some 0))) (Primrec.const 1) (Primrec.const 0)
  have hmap := Partrec.map (g := fun (_ : Code × ℕ × ℕ) (o : Option ℕ) => if o = some 0 then 1 else 0)
    hp hi.to_comp
  exact (partrec_cond hlt.to_comp (Computable.const 0) hmap).of_eq fun _ => rfl

theorem primrec_datos : Primrec datos :=
  (Primrec.ofNat _).comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))

/-- **La construcción es parcial recursiva** en `(e, x)`: es lo que pide el teorema de recursión. -/
theorem partrec_F (hr : Computable₂ r) : Partrec₂ (F r) := by
  have hm : Primrec fun q : Code × ℕ => q.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hv : Primrec fun q : Code × ℕ => q.2.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
  have hd : Primrec fun q : Code × ℕ => datos q.2 := primrec_datos.comp Primrec.snd
  have hc := Primrec.nat_lt.decide.comp hm (Primrec.fst.comp hd)
  have ht := (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp hd)) hm
  have he := (partrec_estadoP hr).comp ((Primrec.fst.pair (hv.pair (Primrec.fst.comp hd))).pair
      ((Primrec.fst.comp (Primrec.snd.comp hd)).pair (Primrec.nat_sub.comp hm (Primrec.fst.comp hd)))).to_comp
  have hgs : Primrec fun p : ((Code × ℕ) × List ℕ) × ℕ => (p.1.1.1, p.1.1.2.unpair.2, p.2) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((hm.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)
  have hs := (partrec_salidaP hr).comp hgs.to_comp
  have hge : Primrec fun p : (Code × ℕ) × List ℕ => (p.1.1, p.1.2.unpair.1.unpair.1, p.1.2.unpair.2, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair ((hv.comp Primrec.fst).pair ((hm.comp Primrec.fst).pair Primrec.snd))
  have hel0 := (partrec_elegidoP hr).comp hge.to_comp
  have hel := Partrec.bind (g := fun (q : (Code × ℕ) × List ℕ) (c : ℕ) => salidaP r q.1.1 q.1.2.unpair.2 c) hel0 hs
  have hb := Partrec.bind (g := fun (q : Code × ℕ) (st : List ℕ) =>
      (elegidoP r q.1 q.2.unpair.1.unpair.1 q.2.unpair.2 st).bind fun c => salidaP r q.1 q.2.unpair.2 c) he hel
  exact (partrec_cond hc.to_comp ht.to_comp hb).of_eq fun _ => rfl

end Construccion

/-! ## 3. Lo que calcula la construcción: totalidad y valores -/

section Semantica

variable {r : ℕ → ℕ → ℕ} {e : Code}

theorem cota_comun {P : ℕ → ℕ → Prop} (hP : ∀ k K K', K ≤ K' → P k K → P k K') :
    ∀ n, (∀ k < n, ∃ K, P k K) → ∃ K, ∀ k < n, P k K
  | 0, _ => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, h => by
    obtain ⟨K₁, h₁⟩ := cota_comun hP n fun k hk => h k (by omega)
    obtain ⟨K₂, h₂⟩ := h n (by omega)
    refine ⟨max K₁ K₂, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact hP _ _ _ (le_max_left _ _) (h₁ k hk)
    · exact hP _ _ _ (le_max_right _ _) h₂

/-- **La cota existe si los programas medidos terminan.** Es la «propiedad H» que la prueba necesita, y sale de los
dos axiomas de Blum: terminar es tener `pasos` finitos, y `pasos ≤ K` es decidible. -/
theorem cotaN_dom {w m : ℕ} (h : ∀ k ≤ m, (eval (prog e w k) m).Dom) : (cotaN e w m).Dom := by
  obtain ⟨K, hK⟩ := cota_comun (P := fun k K => (evaln K (prog e w k) m).isSome = true)
    (fun _ _ _ hle h => isSome_mono hle h) (m + 1)
    (fun k hk => (dom_iff_exists _ _).1 (h k (by omega)))
  refine Nat.rfind_dom.2 ⟨K, Part.mem_some_iff.2 ?_, fun _ => trivial⟩
  symm
  simp only [alcanza, List.all_eq_true, List.mem_range]
  exact fun k hk => hK k hk

/-- **Lo que garantiza la cota**: con `K` pasos terminan todos los programas de nivel `w` con datos `k ≤ m`. -/
theorem cotaN_spec {w m K : ℕ} (h : K ∈ cotaN e w m) : ∀ k ≤ m, (evaln K (prog e w k) m).isSome = true := by
  have h2 : alcanza e w m K = true := (Part.mem_some_iff.1 (Nat.rfind_spec h)).symm
  simp only [alcanza, List.all_eq_true, List.mem_range] at h2
  exact fun k hk => h2 k (by omega)

variable (r e) in
open Classical in
/-- La tabla de pruebas, como función total (vale `none` donde la prueba no termina). -/
noncomputable def Ot (i m : ℕ) : Option ℕ :=
  if h : (pruebaP r e i m).Dom then (pruebaP r e i m).get h else none

theorem pruebaP_eq {i m : ℕ} (h : (pruebaP r e i m).Dom) : pruebaP r e i m = Part.some (Ot r e i m) := by
  simp [Ot, h]

theorem Ot_spec {i m : ℕ} (hc : (cotaN e (i + 1) m).Dom) :
    ∃ K ∈ cotaN e (i + 1) m, Ot r e i m = evaln (r m K) (Denumerable.ofNat Code i) m := by
  obtain ⟨K, hK⟩ := Part.dom_iff_mem.1 hc
  refine ⟨K, hK, ?_⟩
  have h1 : pruebaP r e i m = Part.some (evaln (r m K) (Denumerable.ofNat Code i) m) := by
    rw [pruebaP, Part.eq_some_iff.2 hK, Part.map_some]
  have h2 := pruebaP_eq (r := r) (e := e) (i := i) (m := m) (by rw [h1]; trivial)
  rw [h1] at h2
  exact (Part.some_injective h2).symm

theorem predP_eq {v m : ℕ} {st : List ℕ} (hD : ∀ i, v ≤ i → i ≤ m → (cotaN e (i + 1) m).Dom) (i : ℕ) :
    predP r e v m st i = Part.some (decide (m < i ∨ (v ≤ i ∧ i ∉ st ∧ (Ot r e i m).isSome = true))) := by
  have hg : (decide (m < i) || decide (i < v) || st.any fun a => decide (a = i)) =
      decide (m < i ∨ i < v ∨ i ∈ st) := by
    have hany : (st.any fun a => decide (a = i)) = decide (i ∈ st) := by
      rw [Bool.eq_iff_iff]; simp [List.any_eq_true]
    rw [hany]; simp [Bool.or_assoc]
  rw [predP, hg]
  by_cases hc : m < i ∨ i < v ∨ i ∈ st
  · rw [decide_eq_true hc, Bool.cond_true]
    refine congrArg Part.some (decide_eq_decide.2 ⟨fun h => Or.inl h, fun h => h.elim id ?_⟩)
    rintro ⟨h4, h5, -⟩
    rcases hc with h | h | h
    · exact h
    · exact absurd h4 (by omega)
    · exact absurd h h5
  · rw [decide_eq_false hc, Bool.cond_false]
    simp only [not_or, not_lt] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    rw [pruebaP_eq (hD i h2 h1), Part.map_some]
    simp [h2, h3, show ¬ m < i by omega]

theorem elegidoP_eq {v m : ℕ} {st : List ℕ} (hD : ∀ i, v ≤ i → i ≤ m → (cotaN e (i + 1) m).Dom) :
    elegidoP r e v m st = Part.some (elegido (Ot r e) v m st) := by
  have : predP r e v m st = fun i =>
      Part.some (decide (m < i ∨ (v ≤ i ∧ i ∉ st ∧ (Ot r e i m).isSome = true))) :=
    funext fun i => predP_eq hD i
  rw [elegidoP, this]
  refine Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨?_, fun hj => ?_⟩)
  · exact Part.mem_some_iff.2 (by rw [eq_comm, decide_eq_true_iff]; exact Nat.find_spec (hay_candidato (Ot r e) v m st))
  · exact Part.mem_some_iff.2 (by rw [eq_comm, decide_eq_false_iff_not]; exact Nat.find_min (hay_candidato (Ot r e) v m st) hj)

theorem estadoP_eq {v s : ℕ} {C : List ℕ} :
    ∀ {j}, (∀ j' < j, ∀ i, v ≤ i → i ≤ s + j' → (cotaN e (i + 1) (s + j')).Dom) →
      estadoP r e v s C j = Part.some (estadoC (Ot r e) v s C j)
  | 0, _ => rfl
  | j + 1, hD => by
    change (estadoP r e v s C j).bind (fun st => pasoP r e v s j st) = _
    rw [estadoP_eq fun j' hj' => hD j' (by omega), Part.bind_some, pasoP,
      elegidoP_eq (hD j (by omega)), Part.map_some]
    rfl

theorem salidaP_eq {m c : ℕ} (h : c ≤ m → (cotaN e (c + 1) m).Dom) :
    salidaP r e m c = Part.some (salidaEn (Ot r e) m c) := by
  by_cases hc : m < c
  · simp [salidaP, salidaEn, hc, show ¬ c ≤ m by omega]
  · have hcm : c ≤ m := by omega
    rw [salidaP, decide_eq_false hc, Bool.cond_false, pruebaP_eq (h hcm), Part.map_some]
    simp [salidaEn, hcm]

theorem F_eq {v k m : ℕ} (hD : ∀ m' ≤ m, ∀ i, v ≤ i → i ≤ m' → (cotaN e (i + 1) m').Dom) :
    F r e (Nat.pair (Nat.pair v k) m) = Part.some (salidaC (Ot r e) v (Denumerable.ofNat _ k) m) := by
  simp only [F, datos, Nat.unpair_pair]
  generalize Denumerable.ofNat (ℕ × List ℕ × List ℕ) k = p
  by_cases hm : m < p.1
  · simp [hm, salidaC]
  · rw [decide_eq_false hm, Bool.cond_false,
      estadoP_eq (fun j' hj' i hv hi => hD (p.1 + j') (by omega) i hv hi), Part.bind_some,
      elegidoP_eq (hD m le_rfl), Part.bind_some,
      salidaP_eq (fun hc => hD m le_rfl _ (elegido_de_verdad hc).1 hc)]
    simp [salidaC, hm]

theorem eval_prog (he : eval e = F r e) (w k m : ℕ) :
    eval (prog e w k) m = F r e (Nat.pair (Nat.pair w k) m) := by
  rw [prog, eval_curry, he]

/-- **La construcción es total**: todo programa de todo nivel, con cualesquiera datos, termina en toda entrada. Por
inducción en la etapa `m` y, dentro de una etapa, hacia abajo en el nivel: el nivel `w` en la etapa `m` solo consulta
etapas anteriores o niveles `> w` en la misma etapa. -/
theorem total (he : eval e = F r e) : ∀ m w k, (eval (prog e w k) m).Dom := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    suffices key : ∀ d w, m + 1 - w ≤ d → ∀ k, (eval (prog e w k) m).Dom from
      fun w k => key _ w le_rfl k
    intro d
    induction d with
    | zero =>
      intro w hw k
      rw [eval_prog he, F_eq fun m' hm' i hi hi' => absurd hi (by omega)]
      trivial
    | succ d ih =>
      intro w hw k
      rw [eval_prog he, F_eq ?_]
      · trivial
      intro m' hm' i hi hi'
      refine cotaN_dom fun k' _ => ?_
      rcases Nat.lt_or_eq_of_le hm' with h | rfl
      · exact ihm m' h _ _
      · exact ih (i + 1) (by omega) k'

end Semantica

/-! ## 4. El teorema de Blum -/

section Teorema

variable {r : ℕ → ℕ → ℕ} {e : Code}

theorem eval_prog_eq (he : eval e = F r e) (w k m : ℕ) :
    eval (prog e w k) m = Part.some (salidaC (Ot r e) w (Denumerable.ofNat _ k) m) := by
  rw [eval_prog he]
  exact F_eq fun m' _ i _ _ => cotaN_dom fun k' _ => total he m' (i + 1) k'

theorem computa_nivel (he : eval e = F r e) (w : ℕ) (p : ℕ × List ℕ × List ℕ)
    (hp : ∀ m, salidaC (Ot r e) w p m = fB (Ot r e) m) :
    Computa (prog e w (Encodable.encode p)) (fB (Ot r e)) := fun m => by
  rw [eval_prog_eq he, Denumerable.ofNat_encode, hp]

/-- La tabla dice la verdad: si la prueba de `i` termina con `y`, `i` vale `y`. -/
theorem Ot_sano (he : eval e = F r e) {i m y : ℕ} (h : Ot r e i m = some y) :
    y ∈ eval (Denumerable.ofNat Code i) m := by
  obtain ⟨K, -, hK⟩ := Ot_spec (r := r) (cotaN_dom fun k _ => total he m (i + 1) k)
  rw [hK] at h
  exact evaln_sound h

/-- **La aceleración de la función construida**, con `r` monótona en su segundo argumento. -/
theorem acelera (he : eval e = F r e) (hmono : ∀ n, Monotone (r n)) : TieneAceleracion r (fB (Ot r e)) := by
  refine ⟨⟨_, computa_nivel he 0 (0, [], []) fun _ => rfl⟩, fun i hi => ?_⟩
  have hsano : ∀ m y, Ot r e (Encodable.encode i) m = some y → y = fB (Ot r e) m := fun m y h => by
    have := Ot_sano he h
    rw [Denumerable.ofNat_encode, hi m] at this
    exact Part.mem_some_iff.1 this
  obtain ⟨N, hN⟩ := no_pasa hsano
  obtain ⟨p, hp⟩ := nivel_exacto (O := Ot r e) (Encodable.encode i + 1)
  have hj := computa_nivel he _ p hp
  refine ⟨_, hj, max N (Encodable.encode p), fun m hm => ?_⟩
  obtain ⟨K, hK, hOt⟩ := Ot_spec (r := r) (cotaN_dom fun k _ => total he m (Encodable.encode i + 1) k)
  have h1 : costo (prog e (Encodable.encode i + 1) (Encodable.encode p)) m ≤ K :=
    (costo_le_iff hj m K).2 (cotaN_spec hK _ (le_of_max_le_right hm))
  have h2 : ¬ costo i m ≤ r m K := by
    rw [costo_le_iff hi]
    have : (Ot r e (Encodable.encode i) m).isSome = false := hN m (le_of_max_le_left hm)
    rw [hOt, Denumerable.ofNat_encode] at this
    rw [this]
    simp
  exact (hmono m h1).trans (by omega)

theorem computable_de_computa {c : Code} {f : ℕ → ℕ} (h : Computa c f) : Computable f :=
  (eval_part.comp (Computable.const c) Computable.id).of_eq fun n => h n

/-- **Blum con `r` monótona.** -/
theorem blum_monotona (hr : Computable₂ r) (hmono : ∀ n, Monotone (r n)) :
    ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧ TieneAceleracion r f := by
  obtain ⟨e, he⟩ := fixed_point₂ (partrec_F hr)
  exact ⟨fB (Ot r e), fB_le _, computable_de_computa (computa_nivel he 0 (0, [], []) fun _ => rfl),
    acelera he hmono⟩

variable (r) in
/-- La envolvente monótona de `r`: `máx_{y ≤ x} r(n, y)`. -/
def rmon (n x : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (r n 0) (fun y acc => max acc (r n (y + 1))) x

theorem le_rmon (n x : ℕ) : r n x ≤ rmon r n x := by
  cases x with
  | zero => exact le_rfl
  | succ x => exact le_max_right _ _

theorem rmon_mono (n : ℕ) : Monotone (rmon r n) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

theorem computable_rmon (hr : Computable₂ r) : Computable₂ (rmon r) := by
  have hg : Computable fun p : ℕ × ℕ => r p.1 0 := hr.comp Computable.fst (Computable.const 0)
  have hm1 : Computable fun q : (ℕ × ℕ) × ℕ × ℕ => q.2.2 := Computable.snd.comp Computable.snd
  have hm2 : Computable fun q : (ℕ × ℕ) × ℕ × ℕ => r q.1.1 (q.2.1 + 1) :=
    hr.comp (Computable.fst.comp Computable.fst) (Computable.succ.comp (Computable.fst.comp Computable.snd))
  have hh := Computable₂.comp Primrec.nat_max.to_comp hm1 hm2
  exact (Computable.nat_rec (f := fun p : ℕ × ℕ => p.2) (g := fun p => r p.1 0)
    (h := fun (p : ℕ × ℕ) (q : ℕ × ℕ) => max q.2 (r p.1 (q.1 + 1))) Computable.snd hg hh).of_eq
    fun _ => rfl

/-- Pedir más aceleración es pedir más: si `r ≤ r'`, la de `r'` da la de `r`. -/
theorem acelera_antitona {r' : ℕ → ℕ → ℕ} {f : ℕ → ℕ} (hle : ∀ n x, r n x ≤ r' n x)
    (h : TieneAceleracion r' f) : TieneAceleracion r f := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨j, hj, N, hN⟩ := h.2 i hi
  exact ⟨j, hj, N, fun n hn => (hle _ _).trans (hN n hn)⟩

/-- **El teorema de aceleración de Blum, incondicional, en la medida `pasos` de Mathlib**: para toda `r` computable
hay una función computable, de valores `0` y `1`, tal que todo programa que la calcula tiene otro que también la
calcula con `r(n, costo nuevo) ≤ costo viejo` para casi todo `n`. -/
theorem blum (hr : Computable₂ r) : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧ TieneAceleracion r f := by
  obtain ⟨f, h1, h2, h3⟩ := blum_monotona (computable_rmon hr) rmon_mono
  exact ⟨f, h1, h2, acelera_antitona le_rmon h3⟩

/-! ## 5. Las consecuencias y los controles -/

theorem computable_lineal : Computable₂ fun n x : ℕ => (n + 1) * x :=
  (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to_comp

/-- **Hay funciones computables sin programa óptimo**, ni siquiera salvo una constante. -/
theorem existe_sin_optimo : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧
    ¬ ∃ i, Computa i f ∧ ∀ j, Computa j f → EsO (costo i) (costo j) := by
  obtain ⟨f, h1, h2, h3⟩ := blum computable_lineal
  exact ⟨f, h1, h2, sin_optimo (fun _ _ => le_rfl) h3⟩

/-- **Y su piso es una escalera sin último peldaño**: una sucesión de programas de `f`, cada uno despreciable frente
al anterior, y debajo de todos ninguna cota que no se pueda subir. -/
theorem existe_escalera_sin_piso : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧
    ∃ s : ℕ → Code, (∀ k, Computa (s k) f) ∧ (∀ k, costo (s (k + 1)) ∈ o (costo (s k))) ∧
      ∀ g, (∀ k, g ∈ o (costo (s k))) → ∃ h, g ∈ o h ∧ ∀ k, h ∈ o (costo (s k)) := by
  obtain ⟨f, h1, h2, h3⟩ := blum computable_lineal
  exact ⟨f, h1, h2, escalera_sin_piso (fun _ _ => le_rfl) h3⟩

/-- **Control**: la función construida no es la constante `0`, que sí tiene programa óptimo
(`cero_sin_aceleracion`). -/
theorem blum_no_es_cero : ∃ f : ℕ → ℕ, (∀ n, f n ≤ 1) ∧ Computable f ∧
    TieneAceleracion (fun n x => (n + 1) * x) f ∧ f ≠ fun _ => 0 := by
  obtain ⟨f, h1, h2, h3⟩ := blum computable_lineal
  refine ⟨f, h1, h2, h3, fun hf => ?_⟩
  subst hf
  exact cero_sin_aceleracion (fun n x _ hx => by nlinarith) h3

end Teorema

end BlumExiste
end Tiempo
end Sagitta.Map
