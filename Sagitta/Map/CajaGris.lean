import Sagitta.Map.DetectorResolucion

/-!
# La caja gris: resolución con memoria acotada

El proyecto probó en caja negra que el trabajo se conserva (`ConservacionTrabajo.lean`): llenar una tabla más decidir con
ella cuesta al menos `|α|`. En `PlanoCaja.lean` la memoria es el caño que traslada trabajo del llenado a la demora. Aquí
se pasa a la **caja gris**: un modelo que **ve la fórmula**, pero solo opera con reglas fijas. Es resolución con
memoria acotada, en la presentación configuracional de Alekhnovich, Ben-Sasson, Razborov y Wigderson («Space complexity
in propositional calculus», STOC 2000, doi 10.1145/335305.335347) y de Esteban y Torán (de memoria, sin verificar:
«Space bounds for resolution», Information and Computation, 2001).

## El modelo

Una refutación es una sucesión de configuraciones (`Finset Clausula`) que arranca vacía y termina con la cláusula
vacía. Cada jugada (`Jugada`, `Avanza`) carga un axioma de `F`, agrega la resolvente de dos cláusulas que **están** en la
configuración (`Clause.resolvent` de cslib, sin debilitamiento), o borra una. `Recorre F s M ms M'` es una corrida en la
que toda configuración tiene a lo sumo `s` cláusulas. El **largo** (`largoDe`) cuenta cargas y resoluciones, no
borrados; `RefutaEn F s L` dice que hay una refutación en espacio `s` y largo `≤ L`, y `largoMinimo F s : ℕ∞` es el
mínimo (`⊤` si no hay). Hay un verificador (`verifica`) que se evalúa con `decide`.

Nota: cslib-frontier sí trae el modelo configuracional (`CslibFrontier/Logics/Propositional/Resolution/Space.lean`,
`CNF.RefutableInSpace`), pero sin largo, y su `.olean` no está compilado en esta copia (tampoco el de
`Cslib.Foundations.Semantics.LTS.Basic`, que importa). Por eso el modelo está aquí, con las mismas tres jugadas y la
misma `Clause.resolvent`, más el largo.

## Lo que se prueba

1. **Sanidad** (`refutacion_sana`): si hay una refutación configuracional, en el espacio que sea, la fórmula no tiene
   solución. Controles: `contra3` se refuta en espacio 3 y largo 3 (`refutaEn_contra3`); una fórmula con solución no
   tiene ninguna (`sin_refutacion_con_solucion`). Completitud: `refutaEn_de_insat`.
2. **La conservación en caja gris.**
   * Toda refutación se ejecuta sin borrar nada, con el mismo largo `L` y espacio `≤ L` (`refutaEn_sin_borrar`,
     sobre `Recorre.sin_borrar`).
   * Bajar el espacio nunca baja el largo mínimo: `largoMinimo F` es antítona (`largoMinimo_antitona`).
   * El extremo se alcanza: con espacio `≥ L` se consigue el largo `L` de cualquier espacio (`largoMinimo_tope`), y con
     espacio libre el largo mínimo es el tamaño mínimo de resolución (`refutaEn_iff_tamano`). Por eso toda cota de
     tamaño vale en todo espacio (`tamano_le_largoMinimo`); en el palomar, `2^(n/24) ≤ largoMinimo` para todo `s`, con
     la cota de Haken de cslib-frontier (`palomar_largoMinimo`).
3. **Cotas de espacio y un compromiso real, mirando la fórmula.**
   * **Cota de espacio** (`espacio_ge`, `espacio_ge_ancho`): si todo axioma tiene al menos `w` variables, toda
     refutación usa espacio `≥ w + 1`. La prueba mira el **paso crítico** (`Recorre.critico`): resolver y borrar no
     quitan soluciones, así que alguna carga de un axioma `A` vuelve insatisfacible una configuración `N`
     satisfacible. Voltear cada variable de `A` en un modelo de `N` satisface `A` y falsea una cláusula de `N`,
     distinta para cada variable (`cuenta_critico`). La versión con `X` y `τ` deja fuera una parte de la fórmula que
     se satisface fijando sus variables.
   * **Familia paramétrica**: las `2^n` cláusulas de ancho `n` (`formulaCompleta n`) piden espacio `≥ n + 1`
     (`espacio_formulaCompleta`); con menos, `largoMinimo = ⊤`, y con más hay refutación (`formulaCompleta_extremos`).
   * **El compromiso** (`compromiso`, `pegada_largoMinimo_ge`). La fórmula `formulaPegada k` es la completa con 3
     variables junto a una cadena de implicaciones de `k + 2` cláusulas, con variables disjuntas. Con `k ≥ 14`:

         largoMinimo (formulaPegada k) 5 ≤ 15 < k + 2 ≤ largoMinimo (formulaPegada k) 3 ≤ 2k + 3

     Con espacio 5 la completa se refuta en 15 pasos (`refutaEn_completa3`, por `decide`). Con espacio `≤ 3` no se
     puede (pide `≥ 4`), así que toda refutación carga **cada** eje de la cadena (`pegada_carga_ejes`) y paga al menos
     `k + 2` (`pegada_largo_ge`). La cadena se baja en espacio 3 con largo `2k + 3` (`refutaEn_pegada_3`), así que los
     dos largos son finitos.
4. **Controles y mutantes.** Abajo, en la sección «Controles».

## La lectura en el plano de José

La memoria es el **espacio de cláusulas**, la demora es el **largo**. Lo que se borra y hace falta otra vez se vuelve a
derivar, y eso es largo. La recta se ve en las dos mitades de la meta 2: con memoria de sobra no hay que borrar nada y
el largo es el tamaño de resolución; quitar memoria solo puede subir el largo. La memoria traslada trabajo, no lo crea:
el piso de tamaño (Haken en el palomar) vale en todo espacio. El compromiso de la meta 3 es el más chico que se dejó
probar: la memoria elige **cuál** refutación cabe, y la que cabe en poco espacio es más larga.

## Lo que NO se prueba

* Es **un sistema de pruebas**, resolución, un peldaño de la escalera de sistemas de pruebas, no máquinas
  arbitrarias. Las cotas valen para quien solo resuelve, carga y borra.
* El compromiso es de **juguete**: dos subfórmulas independientes pegadas, una corta pero espaciosa y otra angosta pero
  larga, y el refutador elige cuál refutar. No es el compromiso en que **toda** refutación de una sola familia paga, ni
  superpolinomial: eso es Ben-Sasson y Nordström («Short proofs may be spacious», FOCS 2008, doi
  10.1109/FOCS.2008.42) y Beame, Beck e Impagliazzo («Time-space tradeoffs in resolution», STOC 2012, doi
  10.1145/2213977.2213999; SIAM J. Comput. 45(4), 2016, doi 10.1137/130914085), con fórmulas de piedras sustituidas.
  Ninguno de esos teoremas está formalizado aquí.
* La cota de espacio `w + 1` es la más simple (ancho de los axiomas). Es justa en `[[]]` (`cota_ancho_justa`), pero no
  en la completa: con 3 variables da `≥ 4` y la refutación concreta usa 5. No se calculó el espacio exacto de
  `formulaCompleta n`, ni las cotas de Atserias–Dalmau o de Esteban–Torán, ni las de piedras.
* No se calcularon largos mínimos exactos: `15` y `2k + 3` son cotas superiores; `k + 2` es inferior.
* El largo cuenta jugadas, no tiempo de máquina; la configuración cuenta cláusulas, no bits.
* Llevar esto a **caja abierta completa** (cualquier algoritmo que mira la fórmula, sin reglas fijas) equivale a una
  cota inferior para SAT, o sea a P ≠ NP. Lo que hay aquí no se acerca a eso.
-/

open Cslib Cslib.Logic.PL

namespace Sagitta.Map.Tiempo.CajaGris

/-! ## El modelo -/

/-- Una jugada de una refutación configuracional. -/
inductive Jugada where
  /-- Cargar un axioma. -/
  | carga (c : Clausula)
  /-- Agregar la resolvente de `c₁` y `c₂` sobre `v`. -/
  | resuelve (c₁ c₂ : Clausula) (v : ℕ)
  /-- Borrar una cláusula. -/
  | borra (c : Clausula)
  deriving DecidableEq

/-- El efecto de una jugada sobre la configuración. -/
inductive Avanza (F : List Clausula) : Finset Clausula → Jugada → Finset Clausula → Prop
  | carga {M : Finset Clausula} {c : Clausula} (hc : c ∈ F) : Avanza F M (.carga c) (insert c M)
  | resuelve {M : Finset Clausula} {c₁ c₂ : Clausula} (v : ℕ) (h₁ : c₁ ∈ M) (h₂ : c₂ ∈ M)
      (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) :
      Avanza F M (.resuelve c₁ c₂ v) (insert (Clause.resolvent c₁ c₂ v) M)
  | borra {M : Finset Clausula} (c : Clausula) : Avanza F M (.borra c) (M.erase c)

/-- Una corrida en espacio `s`. -/
inductive Recorre (F : List Clausula) (s : ℕ) : Finset Clausula → List Jugada → Finset Clausula → Prop
  | fin {M : Finset Clausula} : Recorre F s M [] M
  | paso {M M₁ M₂ : Finset Clausula} {m : Jugada} {ms : List Jugada} (h : Avanza F M m M₁)
      (hs : M₁.card ≤ s) (r : Recorre F s M₁ ms M₂) : Recorre F s M (m :: ms) M₂

/-- El **largo**: cargas y resoluciones. Los borrados no cuentan. -/
def largoDe : List Jugada → ℕ
  | [] => 0
  | .borra _ :: ms => largoDe ms
  | .carga _ :: ms => largoDe ms + 1
  | .resuelve _ _ _ :: ms => largoDe ms + 1

/-- `F` tiene una refutación configuracional en espacio `s` y largo a lo sumo `L`. -/
def RefutaEn (F : List Clausula) (s L : ℕ) : Prop :=
  ∃ (ms : List Jugada) (M : Finset Clausula), Recorre F s ∅ ms M ∧ [] ∈ M ∧ largoDe ms ≤ L

/-- El **largo mínimo** de una refutación en espacio `s` (`⊤` si no hay ninguna). -/
noncomputable def largoMinimo (F : List Clausula) (s : ℕ) : ℕ∞ := ⨅ (L : ℕ) (_ : RefutaEn F s L), (L : ℕ∞)

/-! ## Verificador -/

/-- Aplicar una jugada, si es legal. -/
def aplica (F : List Clausula) (M : Finset Clausula) : Jugada → Option (Finset Clausula)
  | .carga c => if c ∈ F then some (insert c M) else none
  | .resuelve c₁ c₂ v =>
      if c₁ ∈ M ∧ c₂ ∈ M ∧ (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ then
        some (insert (Clause.resolvent c₁ c₂ v) M) else none
  | .borra c => some (M.erase c)

/-- Correr una lista de jugadas en espacio `s`. -/
def corre (F : List Clausula) (s : ℕ) : Finset Clausula → List Jugada → Option (Finset Clausula)
  | M, [] => some M
  | M, m :: ms => match aplica F M m with
    | some M₁ => if M₁.card ≤ s then corre F s M₁ ms else none
    | none => none

/-- El verificador: la corrida es legal en espacio `s` y termina con la cláusula vacía. -/
def verifica (F : List Clausula) (s : ℕ) (ms : List Jugada) : Bool :=
  match corre F s ∅ ms with
  | some M => decide ([] ∈ M)
  | none => false

theorem avanza_de_aplica {F : List Clausula} {M M₁ : Finset Clausula} {m : Jugada}
    (h : aplica F M m = some M₁) : Avanza F M m M₁ := by
  cases m with
  | carga c =>
    simp only [aplica] at h
    split at h
    · cases h; exact .carga ‹_›
    · cases h
  | resuelve c₁ c₂ v =>
    simp only [aplica] at h
    split at h
    · cases h; obtain ⟨a, b, c, d⟩ := ‹_ ∧ _›; exact .resuelve v a b c d
    · cases h
  | borra c => simp only [aplica, Option.some.injEq] at h; subst h; exact .borra c

theorem recorre_de_corre {F : List Clausula} {s : ℕ} :
    ∀ {M M' : Finset Clausula} {ms : List Jugada}, corre F s M ms = some M' → Recorre F s M ms M'
  | M, M', [], h => by simp only [corre, Option.some.injEq] at h; subst h; exact .fin
  | M, M', m :: ms, h => by
    simp only [corre] at h
    split at h
    · rename_i M₁ hM₁
      split at h
      · exact .paso (avanza_de_aplica hM₁) ‹_› (recorre_de_corre h)
      · cases h
    · cases h

theorem refutaEn_de_verifica {F : List Clausula} {s : ℕ} {ms : List Jugada} (h : verifica F s ms = true) :
    RefutaEn F s (largoDe ms) := by
  unfold verifica at h
  split at h
  · exact ⟨ms, _, recorre_de_corre ‹_›, by simpa using h, le_rfl⟩
  · cases h

/-! ## Propiedades básicas de las corridas -/

theorem Recorre.mono {F : List Clausula} {s t : ℕ} (hst : s ≤ t) {M M' : Finset Clausula} {ms : List Jugada}
    (r : Recorre F s M ms M') : Recorre F t M ms M' := by
  induction r with
  | fin => exact .fin
  | paso h hs _ ih => exact .paso h (hs.trans hst) ih

theorem Recorre.append {F : List Clausula} {s : ℕ} {M₁ M₂ M₃ : Finset Clausula} {ms ms' : List Jugada}
    (r : Recorre F s M₁ ms M₂) (r' : Recorre F s M₂ ms' M₃) : Recorre F s M₁ (ms ++ ms') M₃ := by
  induction r with
  | fin => exact r'
  | paso h hs _ ih => exact .paso h hs (ih r')

theorem largoDe_append (ms ms' : List Jugada) : largoDe (ms ++ ms') = largoDe ms + largoDe ms' := by
  induction ms with
  | nil => simp [largoDe]
  | cons m ms ih => cases m <;> simp [largoDe, ih] <;> omega

theorem RefutaEn.mono {F : List Clausula} {s t L L' : ℕ} (h : RefutaEn F s L) (hst : s ≤ t) (hL : L ≤ L') :
    RefutaEn F t L' :=
  let ⟨ms, M, r, hM, hl⟩ := h
  ⟨ms, M, r.mono hst, hM, hl.trans hL⟩

/-- Una corrida de `F` que solo carga cláusulas que cumplen `p` es una corrida de `F.filter p`. -/
theorem Recorre.filtra {F : List Clausula} {s : ℕ} {p : Clausula → Bool} {M M' : Finset Clausula}
    {ms : List Jugada} (r : Recorre F s M ms M') (hp : ∀ c, Jugada.carga c ∈ ms → p c = true) :
    Recorre (F.filter p) s M ms M' := by
  induction r with
  | fin => exact .fin
  | @paso M M₁ M₂ m ms h hs _ ih =>
    refine .paso ?_ hs (ih fun c hc => hp c (List.mem_cons_of_mem _ hc))
    cases h with
    | carga hc => exact .carga (List.mem_filter.2 ⟨hc, hp _ List.mem_cons_self⟩)
    | resuelve v h₁ h₂ hv₁ hv₂ => exact .resuelve v h₁ h₂ hv₁ hv₂
    | borra c => exact .borra c

theorem Recorre.formula_mono {F G : List Clausula} (hFG : ∀ c ∈ F, c ∈ G) {s : ℕ} {M M' : Finset Clausula}
    {ms : List Jugada} (r : Recorre F s M ms M') : Recorre G s M ms M' := by
  induction r with
  | fin => exact .fin
  | paso h hs _ ih =>
    refine .paso ?_ hs ih
    cases h with
    | carga hc => exact .carga (hFG _ hc)
    | resuelve v h₁ h₂ hv₁ hv₂ => exact .resuelve v h₁ h₂ hv₁ hv₂
    | borra c => exact .borra c

/-! ## Meta 1: la sanidad -/

/-- Toda configuración alcanzable se deriva por resolución de `F`. -/
theorem Recorre.deriva {F : List Clausula} {s : ℕ} {M M' : Finset Clausula} {ms : List Jugada}
    (r : Recorre F s M ms M') (hM : ∀ c ∈ M, CNF.Derives (F : CNF ℕ) c) : ∀ c ∈ M', CNF.Derives (F : CNF ℕ) c := by
  induction r with
  | fin => exact hM
  | paso h _ _ ih =>
    refine ih fun c hc => ?_
    cases h with
    | carga hc' =>
      rcases Finset.mem_insert.1 hc with rfl | hc
      exacts [.mem hc', hM c hc]
    | resuelve v h₁ h₂ hv₁ hv₂ =>
      rcases Finset.mem_insert.1 hc with rfl | hc
      exacts [.resolvent v (hM _ h₁) (hM _ h₂) hv₁ hv₂, hM c hc]
    | borra _ => exact hM c (Finset.mem_of_mem_erase hc)

/-- **Sanidad.** Si `F` tiene una refutación configuracional, en el espacio que sea, `F` no tiene solución. -/
theorem refutacion_sana {F : List Clausula} {s L : ℕ} (h : RefutaEn F s L) : ¬ CNF.Satisfiable (F : CNF ℕ) := by
  obtain ⟨ms, M, r, hM, -⟩ := h
  exact CNF.Derives.not_satisfiable (r.deriva (by simp) [] hM)

/-! ## Meta 2: la conservación en caja gris -/

/-- Las jugadas sin los borrados. -/
def sinBorrar : List Jugada → List Jugada
  | [] => []
  | .borra _ :: ms => sinBorrar ms
  | .carga c :: ms => .carga c :: sinBorrar ms
  | .resuelve c₁ c₂ v :: ms => .resuelve c₁ c₂ v :: sinBorrar ms

theorem largoDe_sinBorrar (ms : List Jugada) : largoDe (sinBorrar ms) = largoDe ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => cases m <;> simp [sinBorrar, largoDe, ih]

/-- **Correr sin borrar.** Si una corrida va de `M` a `M'`, la misma sin borrados va de cualquier `N ⊇ M` a un
`N' ⊇ M'`, y cada configuración tiene a lo sumo `|N| + largo` cláusulas. -/
theorem Recorre.sin_borrar {F : List Clausula} {s : ℕ} {M M' : Finset Clausula} {ms : List Jugada}
    (r : Recorre F s M ms M') :
    ∀ (N : Finset Clausula) (t : ℕ), M ⊆ N → N.card + largoDe ms ≤ t →
      ∃ N', Recorre F t N (sinBorrar ms) N' ∧ M' ⊆ N' := by
  induction r with
  | fin => exact fun N _ hMN _ => ⟨N, .fin, hMN⟩
  | @paso M M₁ M₂ m ms h hs _ ih =>
    intro N t hMN ht
    cases h with
    | @carga c hc =>
      have hc1 : (insert c N).card ≤ N.card + 1 := Finset.card_insert_le _ _
      obtain ⟨N', r', h'⟩ := ih (insert c N) t (Finset.insert_subset_insert _ hMN)
        (by simp only [largoDe] at ht; omega)
      exact ⟨N', .paso (.carga hc) (by simp only [largoDe] at ht; omega) r', h'⟩
    | @resuelve c₁ c₂ v h₁ h₂ hv₁ hv₂ =>
      have hc1 : (insert (Clause.resolvent c₁ c₂ v) N).card ≤ N.card + 1 := Finset.card_insert_le _ _
      obtain ⟨N', r', h'⟩ := ih (insert _ N) t (Finset.insert_subset_insert _ hMN)
        (by simp only [largoDe] at ht; omega)
      exact ⟨N', .paso (.resuelve v (hMN h₁) (hMN h₂) hv₁ hv₂) (by simp only [largoDe] at ht; omega) r', h'⟩
    | borra c =>
      exact ih N t ((Finset.erase_subset _ _).trans hMN) (by simpa only [largoDe] using ht)

/-- **La conservación, primera mitad.** Toda refutación de largo `L`, en el espacio que sea, se ejecuta sin borrar
nada: el mismo largo y espacio a lo sumo `L`. -/
theorem refutaEn_sin_borrar {F : List Clausula} {s L : ℕ} (h : RefutaEn F s L) : RefutaEn F L L := by
  obtain ⟨ms, M, r, hM, hl⟩ := h
  obtain ⟨N', r', h'⟩ := r.sin_borrar ∅ (largoDe ms) (by simp) (by simp)
  exact ⟨sinBorrar ms, N', r'.mono hl, h' hM, by rw [largoDe_sinBorrar]; exact hl⟩

/-- **La conservación, segunda mitad.** Bajar el espacio nunca baja el largo mínimo: `largoMinimo F` es antítona. -/
theorem largoMinimo_antitona (F : List Clausula) : Antitone (largoMinimo F) := by
  intro s t hst
  exact le_iInf₂ fun L hL => iInf₂_le L (hL.mono hst le_rfl)

theorem largoMinimo_le {F : List Clausula} {s L : ℕ} (h : RefutaEn F s L) : largoMinimo F s ≤ L :=
  iInf₂_le L h

theorem le_largoMinimo {F : List Clausula} {s : ℕ} {B : ℕ} (h : ∀ L, RefutaEn F s L → B ≤ L) :
    (B : ℕ∞) ≤ largoMinimo F s :=
  le_iInf₂ fun L hL => by exact_mod_cast h L hL

/-- **El extremo de la recta se alcanza.** Lo que se refuta con largo `L` en algún espacio se refuta con largo `L` en
todo espacio `t ≥ L`. -/
theorem largoMinimo_tope {F : List Clausula} {s L : ℕ} (h : RefutaEn F s L) {t : ℕ} (ht : L ≤ t) :
    largoMinimo F t ≤ L :=
  largoMinimo_le ((refutaEn_sin_borrar h).mono ht le_rfl)

/-! ### Con espacio ilimitado es resolución: el largo es el tamaño -/

/-- De una corrida sale una prueba por resolución con una línea por carga o resolución. -/
theorem Recorre.prueba {F : List Clausula} {s : ℕ} {M M' : Finset Clausula} {ms : List Jugada}
    (r : Recorre F s M ms M') :
    ∀ ls : List Clausula, CNF.IsProof (F : CNF ℕ) ls → (∀ c ∈ M, c ∈ ls) →
      ∃ ls', CNF.IsProof (F : CNF ℕ) ls' ∧ (∀ c ∈ M', c ∈ ls') ∧ ls'.length ≤ ls.length + largoDe ms := by
  induction r with
  | fin => exact fun ls h hM => ⟨ls, h, hM, by simp [largoDe]⟩
  | paso h _ _ ih =>
    intro ls hp hM
    cases h with
    | @carga c hc =>
      obtain ⟨ls', h', hM', hl⟩ := ih (c :: ls) (.mem hp hc) fun d hd => by
        rcases Finset.mem_insert.1 hd with rfl | hd
        exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hM d hd)]
      exact ⟨ls', h', hM', by simp only [largoDe, List.length_cons] at hl ⊢; omega⟩
    | @resuelve c₁ c₂ v h₁ h₂ hv₁ hv₂ =>
      obtain ⟨ls', h', hM', hl⟩ := ih (_ :: ls) (.resolvent v hp (hM _ h₁) (hM _ h₂) hv₁ hv₂) fun d hd => by
        rcases Finset.mem_insert.1 hd with rfl | hd
        exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hM d hd)]
      exact ⟨ls', h', hM', by simp only [largoDe, List.length_cons] at hl ⊢; omega⟩
    | borra c =>
      obtain ⟨ls', h', hM', hl⟩ := ih ls hp fun d hd => hM d (Finset.mem_of_mem_erase hd)
      exact ⟨ls', h', hM', by simpa only [largoDe] using hl⟩

/-- Reproducir una prueba por resolución, línea por línea, sin borrar. -/
theorem recorre_de_prueba {F : List Clausula} {ls : List Clausula} (h : CNF.IsProof (F : CNF ℕ) ls) :
    ∃ ms, Recorre F ls.length ∅ ms ls.toFinset ∧ largoDe ms = ls.length := by
  induction h with
  | nil => exact ⟨[], .fin, rfl⟩
  | @mem ls c _ hc ih =>
    obtain ⟨ms, r, hl⟩ := ih
    refine ⟨ms ++ [.carga c], (r.mono (Nat.le_succ _)).append (.paso ?_ ?_ .fin), ?_⟩
    · rw [List.toFinset_cons]; exact .carga hc
    · exact List.toFinset_card_le _
    · simp [largoDe_append, largoDe, hl]
  | @resolvent ls c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨ms, r, hl⟩ := ih
    refine ⟨ms ++ [.resuelve c₁ c₂ v], (r.mono (Nat.le_succ _)).append (.paso ?_ ?_ .fin), ?_⟩
    · rw [List.toFinset_cons]; exact .resuelve v (List.mem_toFinset.2 h₁) (List.mem_toFinset.2 h₂) hv₁ hv₂
    · exact List.toFinset_card_le _
    · simp [largoDe_append, largoDe, hl]

/-- **Con espacio ilimitado, el largo mínimo es el tamaño mínimo de resolución**: hay una refutación configuracional de
largo `L` en algún espacio si y solo si hay una refutación por resolución de a lo sumo `L` líneas. -/
theorem refutaEn_iff_tamano {F : List Clausula} {L : ℕ} :
    (∃ s, RefutaEn F s L) ↔ CNF.RefutableInSize (F : CNF ℕ) L := by
  constructor
  · rintro ⟨s, ms, M, r, hM, hl⟩
    obtain ⟨ls, h, hM', hlen⟩ := r.prueba [] .nil (by simp)
    exact ⟨ls, h, hM' _ hM, by simp at hlen; omega⟩
  · rintro ⟨ls, h, hnil, hlen⟩
    obtain ⟨ms, r, hl⟩ := recorre_de_prueba h
    exact ⟨ls.length, ms, _, r, List.mem_toFinset.2 hnil, by omega⟩

/-- **Toda cota inferior de tamaño es cota inferior del largo, en todo espacio**: la memoria no crea trabajo. -/
theorem tamano_le_largoMinimo {F : List Clausula} {B : ℕ}
    (h : ∀ L, CNF.RefutableInSize (F : CNF ℕ) L → B ≤ L) (s : ℕ) : (B : ℕ∞) ≤ largoMinimo F s :=
  le_largoMinimo fun L hL => h L (refutaEn_iff_tamano.1 ⟨s, hL⟩)

/-- **Completitud**: toda fórmula sin solución tiene una refutación configuracional, en espacio igual a su largo. -/
theorem refutaEn_de_insat {F : List Clausula} (h : ¬ CNF.Satisfiable (F : CNF ℕ)) : ∃ L, RefutaEn F L L := by
  obtain ⟨L, hL⟩ := CNF.exists_refutableInSize_iff_not_satisfiable.2 h
  obtain ⟨s, hs⟩ := refutaEn_iff_tamano.2 hL
  exact ⟨L, refutaEn_sin_borrar hs⟩

/-! ## Meta 3: cotas de espacio y un compromiso -/

/-- El número de variables distintas de una cláusula. -/
def numVars (c : Clausula) : ℕ := (c.map Prod.fst).toFinset.card

/-- La configuración `M` se satisface con una asignación que coincide con `τ` en las variables de `X`. -/
def SatFuera (X : ℕ → Prop) (τ : ℕ → Bool) (M : Finset Clausula) : Prop :=
  ∃ α : ℕ → Bool, (∀ x, X x → α x = τ x) ∧ ∀ c ∈ M, Clause.eval α c = true

/-- **El paso crítico.** Si una corrida va de una configuración satisfacible (fuera de `X`) a una que no lo es, en
algún momento carga un axioma `A` sobre una configuración `N` satisfacible y la vuelve insatisfacible. Resolver y borrar
no quitan soluciones. -/
theorem Recorre.critico {F : List Clausula} {s : ℕ} {X : ℕ → Prop} {τ : ℕ → Bool} {M M' : Finset Clausula}
    {ms : List Jugada} (r : Recorre F s M ms M') (hM : SatFuera X τ M) (hM' : ¬ SatFuera X τ M') :
    ∃ A ∈ F, ∃ N : Finset Clausula, SatFuera X τ N ∧ ¬ SatFuera X τ (insert A N) ∧ (insert A N).card ≤ s := by
  induction r with
  | fin => exact absurd hM hM'
  | @paso M M₁ M₂ m ms h hs _ ih =>
    by_cases h₁ : SatFuera X τ M₁
    · exact ih h₁ hM'
    · cases h with
      | @carga c hc => exact ⟨c, hc, M, hM, h₁, hs⟩
      | @resuelve c₁ c₂ v hc₁ hc₂ _ _ =>
        obtain ⟨α, hα, hαM⟩ := hM
        refine absurd ⟨α, hα, fun c hc => ?_⟩ h₁
        rcases Finset.mem_insert.1 hc with rfl | hc
        exacts [Clause.eval_resolvent v (hαM _ hc₁) (hαM _ hc₂), hαM c hc]
      | borra c =>
        obtain ⟨α, hα, hαM⟩ := hM
        exact absurd ⟨α, hα, fun d hd => hαM d (Finset.mem_of_mem_erase hd)⟩ h₁

/-- **La cuenta del paso crítico.** Si `N` es satisfacible fuera de `X` y al cargar `A`, cuyas variables están fuera
de `X`, deja de serlo, entonces `N` tiene al menos tantas cláusulas como variables tiene `A`: voltear cada variable de
`A` en un modelo de `N` satisface `A`, así que falsea una cláusula de `N`, y cláusulas distintas para variables
distintas. -/
theorem cuenta_critico {X : ℕ → Prop} {τ : ℕ → Bool} {N : Finset Clausula} {A : Clausula}
    (hN : SatFuera X τ N) (hA : ¬ SatFuera X τ (insert A N)) (hX : ∀ l ∈ A, ¬ X l.1) :
    numVars A + 1 ≤ (insert A N).card := by
  classical
  obtain ⟨α, hα, hαN⟩ := hN
  have hαA : Clause.eval α A = false := by
    by_contra h
    refine hA ⟨α, hα, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    exacts [by simpa using h, hαN c hc]
  have hlit : ∀ l ∈ A, α l.1 ≠ l.2 := by
    intro l hl he
    have := clause_falsa_iff.mp hαA l hl
    simp [Literal.eval, he] at this
  -- voltear la variable `i`
  set β : ℕ → ℕ → Bool := fun i => Function.update α i (!α i) with hβ
  have hβA : ∀ i ∈ (A.map Prod.fst).toFinset, Clause.eval (β i) A = true := by
    intro i hi
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hi)
    rw [Clause.eval_eq_true_iff]
    refine ⟨l, hl, ?_⟩
    have := hlit l hl
    simp only [hβ, Function.update_self]
    cases h : α l.1 <;> cases h' : l.2 <;> simp_all
  have hβX : ∀ i ∈ (A.map Prod.fst).toFinset, ∀ x, X x → β i x = τ x := by
    intro i hi x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hi)
    have hne : x ≠ l.1 := fun h => hX l hl (h ▸ hx)
    simp only [hβ, Function.update_of_ne hne]; exact hα x hx
  have hcae : ∀ i ∈ (A.map Prod.fst).toFinset, ∃ C ∈ N, Clause.eval (β i) C = false := by
    intro i hi
    by_contra h
    push Not at h
    refine hA ⟨β i, hβX i hi, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact hβA i hi
    · cases hh : Clause.eval (β i) c
      · exact absurd hh (h c hc)
      · rfl
  choose! g hgN hgf using hcae
  have hinj : Set.InjOn g ((A.map Prod.fst).toFinset : Set ℕ) := by
    intro i hi j hj hij
    have hC := hαN _ (hgN i hi)
    rw [Clause.eval_eq_true_iff] at hC
    obtain ⟨l, hl, hle⟩ := hC
    have key : ∀ k ∈ (A.map Prod.fst).toFinset, g k = g i → l.1 = k := by
      intro k hk hgk
      by_contra hne
      have hf := clause_falsa_iff.mp (hgf k hk) l (hgk ▸ hl)
      simp only [hβ, Literal.eval, Function.update_of_ne hne] at hf
      simp [hle] at hf
    exact (key i hi rfl).symm.trans (key j hj hij.symm)
  have hcard : (A.map Prod.fst).toFinset.card ≤ N.card :=
    Finset.card_le_card_of_injOn g (fun i hi => hgN i hi) hinj
  have hAN : A ∉ N := fun h => by simp [hαN A h] at hαA
  rw [Finset.card_insert_of_notMem hAN]
  unfold numVars; omega

/-- **Cota inferior de espacio.** Si cada axioma de `F` o se cumple en toda asignación que coincide con `τ` en `X`, o
tiene al menos `w` variables, todas fuera de `X`, entonces toda refutación de `F` usa espacio al menos `w + 1`. -/
theorem espacio_ge {F : List Clausula} {s L : ℕ} (h : RefutaEn F s L) (X : ℕ → Prop) (τ : ℕ → Bool) (w : ℕ)
    (hF : ∀ A ∈ F, (∀ α : ℕ → Bool, (∀ x, X x → α x = τ x) → Clause.eval α A = true) ∨
      (w ≤ numVars A ∧ ∀ l ∈ A, ¬ X l.1)) : w + 1 ≤ s := by
  obtain ⟨ms, M, r, hM, -⟩ := h
  have h0 : SatFuera X τ ∅ := ⟨τ, fun _ _ => rfl, by simp⟩
  have h1 : ¬ SatFuera X τ M := fun ⟨α, _, hα⟩ => by simpa using hα [] hM
  obtain ⟨A, hA, N, hN, hAN, hs⟩ := r.critico h0 h1
  rcases hF A hA with hsat | ⟨hw, hX⟩
  · obtain ⟨α, hα, hαN⟩ := hN
    refine absurd ⟨α, hα, fun c hc => ?_⟩ hAN
    rcases Finset.mem_insert.1 hc with rfl | hc
    exacts [hsat α hα, hαN c hc]
  · have := cuenta_critico hN hAN hX
    omega

/-- **Espacio al menos el ancho mínimo más uno.** Si todo axioma tiene al menos `w` variables, toda refutación usa
espacio `≥ w + 1`. -/
theorem espacio_ge_ancho {F : List Clausula} {s L w : ℕ} (h : RefutaEn F s L) (hw : ∀ A ∈ F, w ≤ numVars A) :
    w + 1 ≤ s :=
  espacio_ge h (fun _ => False) (fun _ => false) w fun A hA => Or.inr ⟨hw A hA, fun _ _ h => h⟩

/-! ### La familia completa: todas las cláusulas de ancho `n` -/

/-- Las `2^n` cláusulas con las variables `0, …, n−1`, una vez cada una, con todos los signos. -/
def formulaCompleta : ℕ → List Clausula
  | 0 => [[]]
  | n + 1 => (formulaCompleta n).flatMap fun c => [(n, true) :: c, (n, false) :: c]

theorem vars_formulaCompleta : ∀ (n : ℕ), ∀ c ∈ formulaCompleta n, (c.map Prod.fst).toFinset = Finset.range n
  | 0, c, hc => by simp only [formulaCompleta, List.mem_singleton] at hc; subst hc; rfl
  | n + 1, c, hc => by
    simp only [formulaCompleta, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain ⟨d, hd, rfl | rfl⟩ := hc <;>
      simp [vars_formulaCompleta n d hd, Finset.range_add_one]

theorem numVars_formulaCompleta {n : ℕ} {c : Clausula} (hc : c ∈ formulaCompleta n) : numVars c = n := by
  simp [numVars, vars_formulaCompleta n c hc]

theorem formulaCompleta_insat (n : ℕ) : ¬ CNF.Satisfiable (formulaCompleta n : CNF ℕ) := by
  rintro ⟨σ, hσ⟩
  have : ∀ n, ∃ c ∈ formulaCompleta n, Clause.eval σ c = false := by
    intro n
    induction n with
    | zero => exact ⟨[], by simp [formulaCompleta], rfl⟩
    | succ n ih =>
      obtain ⟨c, hc, hf⟩ := ih
      refine ⟨(n, !σ n) :: c, ?_, ?_⟩
      · simp only [formulaCompleta, List.mem_flatMap]
        exact ⟨c, hc, by cases σ n <;> simp⟩
      · simp [hf, Literal.eval]
  obtain ⟨c, hc, hf⟩ := this n
  rw [CNF.eval_eq_true_iff] at hσ
  rw [hσ c hc] at hf
  exact absurd hf (by simp)

/-- **La cota de espacio en la familia completa**: refutar las `2^n` cláusulas de ancho `n` pide espacio `≥ n + 1`. -/
theorem espacio_formulaCompleta {n s L : ℕ} (h : RefutaEn (formulaCompleta n) s L) : n + 1 ≤ s :=
  espacio_ge_ancho h fun _ hA => (numVars_formulaCompleta hA).ge

/-- **La cota no es vacía**: la familia completa sí tiene refutaciones, y con menos espacio el largo mínimo es `⊤`. -/
theorem formulaCompleta_extremos (n : ℕ) :
    (∀ s ≤ n, largoMinimo (formulaCompleta n) s = ⊤) ∧ ∃ L, largoMinimo (formulaCompleta n) L ≤ L := by
  refine ⟨fun s hs => ?_, ?_⟩
  · refine eq_top_iff.2 (le_iInf₂ fun L hL => ?_)
    have := espacio_formulaCompleta hL
    omega
  · obtain ⟨L, hL⟩ := refutaEn_de_insat (formulaCompleta_insat n)
    exact ⟨L, largoMinimo_le hL⟩

/-! ### Una refutación concreta de la fórmula completa con tres variables -/

/-- La cláusula `[(2, b₂), (1, b₁), (0, b₀)]` de `formulaCompleta 3`. -/
def kc (b₂ b₁ b₀ : Bool) : Clausula := [(2, b₂), (1, b₁), (0, b₀)]

/-- Resolver sobre `0` las dos cláusulas que comparten `b₂, b₁`. -/
def ec (b₂ b₁ : Bool) : Clausula := Clause.resolvent (kc b₂ b₁ true) (kc b₂ b₁ false) 0

/-- Resolver sobre `1` las dos `ec` que comparten `b₂`. -/
def dc (b₂ : Bool) : Clausula := Clause.resolvent (ec b₂ true) (ec b₂ false) 1

/-- Derivar `ec b₂ b₁`: cargar sus dos axiomas, resolver sobre `0` y borrar los axiomas. -/
def bloqueE (b₂ b₁ : Bool) : List Jugada :=
  [.carga (kc b₂ b₁ true), .carga (kc b₂ b₁ false), .resuelve (kc b₂ b₁ true) (kc b₂ b₁ false) 0,
    .borra (kc b₂ b₁ true), .borra (kc b₂ b₁ false)]

/-- Derivar `dc b₂`: las dos `ec`, resolver sobre `1` y borrarlas. -/
def bloqueD (b₂ : Bool) : List Jugada :=
  bloqueE b₂ true ++ bloqueE b₂ false ++
    [.resuelve (ec b₂ true) (ec b₂ false) 1, .borra (ec b₂ true), .borra (ec b₂ false)]

/-- La refutación en árbol de `formulaCompleta 3`, en orden de Strahler: 8 cargas y 7 resoluciones. -/
def refCompleta3 : List Jugada := bloqueD true ++ bloqueD false ++ [.resuelve (dc true) (dc false) 2]

theorem verifica_refCompleta3 : verifica (formulaCompleta 3) 5 refCompleta3 = true := by decide

theorem largoDe_refCompleta3 : largoDe refCompleta3 = 15 := by decide

/-- La fórmula completa con tres variables se refuta en espacio 5 con largo 15. -/
theorem refutaEn_completa3 : RefutaEn (formulaCompleta 3) 5 15 :=
  largoDe_refCompleta3 ▸ refutaEn_de_verifica verifica_refCompleta3

/-! ### La cadena: angosta pero larga -/

/-- El eje `j` de la cadena de implicaciones `a₀, a₀ → a₁, …, a_{k−1} → a_k, ¬a_k`, con `a_i` la variable `o + i`. -/
def ejeCadena (o k j : ℕ) : Clausula :=
  if j = 0 then [(o, true)] else if j ≤ k then [(o + (j - 1), false), (o + j, true)] else [(o + k, false)]

/-- La cadena: `k + 2` cláusulas de ancho a lo sumo 2. -/
def formulaCadena (o k : ℕ) : List Clausula := (List.range (k + 2)).map (ejeCadena o k)

theorem ejeCadena_inj {o k i j : ℕ} (hi : i < k + 2) (hj : j < k + 2) (h : ejeCadena o k i = ejeCadena o k j) :
    i = j := by
  unfold ejeCadena at h
  split_ifs at h <;> simp_all
  omega

/-- Sin el eje `j`, la cadena se cumple con `a_i` verdadera si y solo si `i < j`, y eso solo mira variables `≥ o`. -/
theorem ejeCadena_sat {o k i j : ℕ} (hi : i < k + 2) (hj : j < k + 2) (hij : i ≠ j) (α : ℕ → Bool)
    (hα : ∀ x, o ≤ x → α x = decide (x < o + j)) : Clause.eval α (ejeCadena o k i) = true := by
  unfold ejeCadena
  split_ifs with h0 h1
  · subst h0
    simp [Literal.eval, hα o le_rfl]; omega
  · rw [Clause.eval_eq_true_iff]
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact ⟨(o + i, true), by simp, by simp [hα (o + i) (by omega)]; omega⟩
    · exact ⟨(o + (i - 1), false), by simp, by simp [hα (o + (i - 1)) (by omega)]; omega⟩
  · simp [Literal.eval, hα (o + k) (by omega)]; omega

theorem vars_ejeCadena {o k j : ℕ} : ∀ l ∈ ejeCadena o k j, o ≤ l.1 := by
  intro l hl
  unfold ejeCadena at hl
  split_ifs at hl
  · simp only [List.mem_singleton] at hl; subst hl; simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp
  · simp only [List.mem_singleton] at hl; subst hl; simp

/-! ### La fórmula pegada: corta pero espaciosa, o angosta pero larga -/

/-- `formulaCompleta 3` (variables `0, 1, 2`) junto a la cadena de largo `k` (variables `3, …, k + 3`). -/
def formulaPegada (k : ℕ) : List Clausula := formulaCompleta 3 ++ formulaCadena 3 k

/-- **Con espacio a lo sumo 3, toda refutación de la fórmula pegada carga cada eje de la cadena.** Si no cargara el
eje `j`, sería una refutación de la completa junto a una cadena satisfacible, y eso pide espacio `≥ 4`
(`espacio_ge` con `X` las variables de la cadena y `τ` la solución de la cadena sin su eje `j`). -/
theorem pegada_carga_ejes {k s : ℕ} (hs : s ≤ 3) {ms : List Jugada} {M : Finset Clausula}
    (r : Recorre (formulaPegada k) s ∅ ms M) (hM : [] ∈ M) {j : ℕ} (hj : j < k + 2) :
    Jugada.carga (ejeCadena 3 k j) ∈ ms := by
  by_contra hno
  have r' := r.filtra (p := fun c => decide (c ≠ ejeCadena 3 k j)) fun c hc => by
    simp only [decide_eq_true_eq]; rintro rfl; exact hno hc
  have := espacio_ge ⟨ms, M, r', hM, le_rfl⟩ (fun x => 3 ≤ x) (fun x => decide (x < 3 + j)) 3 fun A hA => by
    simp only [formulaPegada, List.mem_filter, List.mem_append, decide_eq_true_eq] at hA
    obtain ⟨hA | hA, hne⟩ := hA
    · refine Or.inr ⟨(numVars_formulaCompleta hA).ge, fun l hl => ?_⟩
      have : l.1 ∈ Finset.range 3 := by
        rw [← vars_formulaCompleta 3 A hA]; exact List.mem_toFinset.2 (List.mem_map_of_mem hl)
      simp at this; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hA
      refine Or.inl fun α hα => ejeCadena_sat (List.mem_range.1 hi) hj (fun h => hne (h ▸ rfl)) α hα
  omega

/-- El largo de una lista de jugadas es al menos el número de cláusulas distintas que carga. -/
theorem card_le_largoDe {S : Finset Clausula} : ∀ {ms : List Jugada}, (∀ c ∈ S, Jugada.carga c ∈ ms) →
    S.card ≤ largoDe ms
  | [], h => by
    rcases S.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
    · simp
    · simpa using h c hc
  | m :: ms, h => by
    cases m with
    | carga c =>
      have := card_le_largoDe (S := S.erase c) (ms := ms) fun d hd => by
        rcases List.mem_cons.1 (h d (Finset.mem_of_mem_erase hd)) with he | he
        · exact absurd (Jugada.carga.inj he) (Finset.ne_of_mem_erase hd)
        · exact he
      have := Finset.pred_card_le_card_erase (s := S) (a := c)
      simp only [largoDe]; omega
    | resuelve c₁ c₂ v =>
      have := card_le_largoDe (S := S) (ms := ms) fun d hd => by
        rcases List.mem_cons.1 (h d hd) with he | he
        · cases he
        · exact he
      simp only [largoDe]; omega
    | borra c =>
      have := card_le_largoDe (S := S) (ms := ms) fun d hd => by
        rcases List.mem_cons.1 (h d hd) with he | he
        · cases he
        · exact he
      simpa only [largoDe] using this

/-- **Con espacio a lo sumo 3, el largo es al menos `k + 2`.** -/
theorem pegada_largo_ge {k s L : ℕ} (hs : s ≤ 3) (h : RefutaEn (formulaPegada k) s L) : k + 2 ≤ L := by
  obtain ⟨ms, M, r, hM, hl⟩ := h
  have hcard : ((Finset.range (k + 2)).image (ejeCadena 3 k)).card = k + 2 := by
    rw [Finset.card_image_of_injOn fun i hi j hj hij =>
      ejeCadena_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij]
    simp
  have := card_le_largoDe (S := (Finset.range (k + 2)).image (ejeCadena 3 k)) (ms := ms) fun c hc => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
    exact pegada_carga_ejes hs r hM (Finset.mem_range.1 hj)
  omega

/-! ### La bajada por la cadena en espacio 3 -/

/-- De `¬a_{i+1}` a `¬a_i`: cargar `a_i → a_{i+1}`, resolver, borrar las dos de antes. -/
def bloqueCadena (o i : ℕ) : List Jugada :=
  [.carga [(o + i, false), (o + (i + 1), true)],
    .resuelve [(o + i, false), (o + (i + 1), true)] [(o + (i + 1), false)] (o + (i + 1)),
    .borra [(o + i, false), (o + (i + 1), true)], .borra [(o + (i + 1), false)]]

/-- De `¬a_j` a `¬a₀`. -/
def bajada (o : ℕ) : ℕ → List Jugada
  | 0 => []
  | j + 1 => bloqueCadena o j ++ bajada o j

theorem largoDe_bajada (o j : ℕ) : largoDe (bajada o j) = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [bajada, ih, bloqueCadena, largoDe]; omega

theorem recorre_bloque {F : List Clausula} {o i : ℕ} (hP : [(o + i, false), (o + (i + 1), true)] ∈ F) :
    Recorre F 3 {[(o + (i + 1), false)]} (bloqueCadena o i) {[(o + i, false)]} := by
  have hres : Clause.resolvent [(o + i, false), (o + (i + 1), true)] [(o + (i + 1), false)] (o + (i + 1)) =
      [(o + i, false)] := by
    simp [Clause.resolvent]
  refine .paso (.carga hP) (Finset.card_insert_le _ _ |>.trans (by simp)) ?_
  refine .paso (.resuelve (o + (i + 1)) (by simp) (by simp) (by simp) (by simp)) ?_ ?_
  · exact (Finset.card_insert_le _ _).trans (by simp)
  rw [hres]
  refine .paso (.borra _) (Finset.card_erase_le.trans ((Finset.card_insert_le _ _).trans (by simp))) ?_
  have e : Finset.erase (Finset.erase (insert [(o + i, false)] (insert [(o + i, false), (o + (i + 1), true)]
      ({[(o + (i + 1), false)]} : Finset Clausula))) [(o + i, false), (o + (i + 1), true)])
      [(o + (i + 1), false)] = {[(o + i, false)]} := by
    ext c; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, rfl | rfl | rfl⟩ <;> simp_all
    · rintro rfl; simp
  refine .paso (.borra _) (by rw [e]; simp) ?_
  rw [e]; exact .fin

theorem recorre_bajada {F : List Clausula} {o k : ℕ}
    (hP : ∀ i < k, [(o + i, false), (o + (i + 1), true)] ∈ F) :
    ∀ j ≤ k, Recorre F 3 {[(o + j, false)]} (bajada o j) {[(o, false)]}
  | 0, _ => by simpa [bajada] using (Recorre.fin : Recorre F 3 {[(o, false)]} [] _)
  | j + 1, hj => (recorre_bloque (hP j (by omega))).append (recorre_bajada hP j (by omega))

/-- La refutación de la cadena: cargar `¬a_k`, bajar hasta `¬a₀`, cargar `a₀` y resolver. -/
def refCadena (o k : ℕ) : List Jugada :=
  .carga [(o + k, false)] :: bajada o k ++ [.carga [(o, true)], .resuelve [(o, true)] [(o, false)] o]

theorem refutaEn_cadena {F : List Clausula} {o k : ℕ} (hP : ∀ i < k, [(o + i, false), (o + (i + 1), true)] ∈ F)
    (hQ : [(o + k, false)] ∈ F) (hA : [(o, true)] ∈ F) : RefutaEn F 3 (2 * k + 3) := by
  have hres : Clause.resolvent [(o, true)] [(o, false)] o = [] := by simp [Clause.resolvent]
  refine ⟨refCadena o k, insert (Clause.resolvent [(o, true)] [(o, false)] o)
    (insert [(o, true)] ({[(o, false)]} : Finset Clausula)), ?_, ?_, ?_⟩
  · refine .paso (.carga hQ) (by simp) ?_
    have : insert [(o + k, false)] (∅ : Finset Clausula) = {[(o + k, false)]} := by simp
    rw [this]
    refine (recorre_bajada hP k le_rfl).append ?_
    refine .paso (.carga hA) ((Finset.card_insert_le _ _).trans (by simp)) ?_
    refine .paso (.resuelve o (by simp) (by simp) (by simp) (by simp)) ?_ .fin
    exact (Finset.card_insert_le _ _).trans (by simp)
  · simp [hres]
  · simp [refCadena, largoDe_append, largoDe_bajada, largoDe]

theorem ejes_en_pegada (k : ℕ) :
    (∀ i < k, [(3 + i, false), (3 + (i + 1), true)] ∈ formulaPegada k) ∧ [(3 + k, false)] ∈ formulaPegada k ∧
      [(3, true)] ∈ formulaPegada k := by
  refine ⟨fun i hi => ?_, ?_, ?_⟩ <;> simp only [formulaPegada, formulaCadena, List.mem_append, List.mem_map,
    List.mem_range]
  · refine Or.inr ⟨i + 1, by omega, ?_⟩; simp [ejeCadena]; omega
  · refine Or.inr ⟨k + 1, by omega, ?_⟩; simp [ejeCadena]
  · exact Or.inr ⟨0, by omega, by simp [ejeCadena]⟩

theorem refutaEn_pegada_3 (k : ℕ) : RefutaEn (formulaPegada k) 3 (2 * k + 3) :=
  refutaEn_cadena (ejes_en_pegada k).1 (ejes_en_pegada k).2.1 (ejes_en_pegada k).2.2

theorem refutaEn_pegada_5 (k : ℕ) : RefutaEn (formulaPegada k) 5 15 := by
  obtain ⟨ms, M, r, hM, hl⟩ := refutaEn_completa3
  exact ⟨ms, M, r.formula_mono fun c hc => List.mem_append_left _ hc, hM, hl⟩

/-- **El compromiso.** En la fórmula pegada con `k ≥ 14`: con espacio 5 basta largo 15; con espacio 3 (o menos) el
largo mínimo es al menos `k + 2 > 15`, y es finito (a lo sumo `2k + 3`). Menos espacio obliga a más largo. -/
theorem compromiso (k : ℕ) (hk : 14 ≤ k) :
    largoMinimo (formulaPegada k) 5 ≤ 15 ∧ 15 < largoMinimo (formulaPegada k) 3 ∧
      largoMinimo (formulaPegada k) 3 ≤ (2 * k + 3 : ℕ) := by
  refine ⟨largoMinimo_le (refutaEn_pegada_5 k), ?_, largoMinimo_le (refutaEn_pegada_3 k)⟩
  have : ((k + 2 : ℕ) : ℕ∞) ≤ largoMinimo (formulaPegada k) 3 := le_largoMinimo fun L hL => pegada_largo_ge le_rfl hL
  refine lt_of_lt_of_le ?_ this
  exact_mod_cast (show 15 < k + 2 by omega)

/-- **La forma general de la cota**: con espacio `s ≤ 3`, el largo mínimo es al menos `k + 2`. -/
theorem pegada_largoMinimo_ge (k : ℕ) {s : ℕ} (hs : s ≤ 3) : ((k + 2 : ℕ) : ℕ∞) ≤ largoMinimo (formulaPegada k) s :=
  le_largoMinimo fun _ hL => pegada_largo_ge hs hL

/-! ## El piso de Haken: la memoria no baja el tamaño -/

/-- **En el palomar, el largo mínimo es al menos `2^(n/24)` en todo espacio**: la cota de Haken de cslib-frontier
(`CNF.two_pow_le_of_refutableInSize_pigeonhole`) vía `tamano_le_largoMinimo`. Ningún espacio, por grande que sea, la
baja. -/
theorem palomar_largoMinimo (n s : ℕ) : ((2 ^ (n / 24) : ℕ) : ℕ∞) ≤ largoMinimo (formulaPal n) s :=
  tamano_le_largoMinimo (fun _ hL => CNF.two_pow_le_of_refutableInSize_pigeonhole (hL.of_relabel (ordenPal_inj n))) s

/-! ## Controles -/

/-- Control de la meta 1: `contra3` (`x₃ ∧ ¬x₃`) tiene una refutación concreta, en espacio 3 y largo 3. -/
theorem refutaEn_contra3 : RefutaEn contra3 3 3 :=
  refutaEn_de_verifica (ms := [.carga [(3, true)], .carga [(3, false)], .resuelve [(3, true)] [(3, false)] 3])
    (by decide)

/-- Control de la meta 1: una fórmula con solución no tiene ninguna refutación, en ningún espacio. -/
theorem sin_refutacion_con_solucion (s L : ℕ) : ¬ RefutaEn [[(0, true)]] s L := fun h =>
  refutacion_sana h ⟨fun _ => true, by decide⟩

/-- Control de la refutación concreta: la misma lista de jugadas **no** cabe en espacio 4 (el verificador mira el
espacio de verdad). -/
theorem refCompleta3_no_cabe_en_4 : verifica (formulaCompleta 3) 4 refCompleta3 = false := by decide

/-- Control de la cota de espacio en la completa: con 3 variables pide espacio `≥ 4`, y hay una en espacio 5. -/
theorem completa3_espacio : (∀ s L, RefutaEn (formulaCompleta 3) s L → 4 ≤ s) ∧ RefutaEn (formulaCompleta 3) 5 15 :=
  ⟨fun _ _ h => espacio_formulaCompleta h, refutaEn_completa3⟩

/-- **La cota `w + 1` es justa**: `[[]]` (ancho 0) se refuta en espacio 1. Mutante refutado: la cota `w + 2` es falsa. -/
theorem cota_ancho_justa : RefutaEn [[]] 1 1 ∧
    ¬ ∀ (F : List Clausula) (s L w : ℕ), RefutaEn F s L → (∀ A ∈ F, w ≤ numVars A) → w + 2 ≤ s := by
  have h : RefutaEn [[]] 1 1 := refutaEn_de_verifica (ms := [.carga []]) (by decide)
  exact ⟨h, fun hm => absurd (hm [[]] 1 1 0 h (fun _ _ => Nat.zero_le _)) (by omega)⟩

/-- Mutante refutado: correr sin borrar **no** cabe en espacio `L − 1`. `[[]]` se refuta con largo 1, y en espacio 0
no hay refutación. -/
theorem sin_borrar_no_menos : RefutaEn [[]] 1 1 ∧ ¬ RefutaEn [[]] 0 1 := by
  refine ⟨cota_ancho_justa.1, fun h => ?_⟩
  have := espacio_ge_ancho (w := 0) h (fun _ _ => Nat.zero_le _)
  omega

/-- **Los extremos del compromiso se alcanzan con `k = 14`**: espacio 5 y largo a lo sumo 15; espacio 3 y largo entre 16
y 31. -/
theorem compromiso_14 :
    largoMinimo (formulaPegada 14) 5 ≤ 15 ∧ 16 ≤ largoMinimo (formulaPegada 14) 3 ∧
      largoMinimo (formulaPegada 14) 3 ≤ 31 :=
  ⟨(compromiso 14 le_rfl).1, by exact_mod_cast pegada_largoMinimo_ge 14 le_rfl, (compromiso 14 le_rfl).2.2⟩

/-- Mutante refutado: el largo mínimo **no** es monótono creciente en el espacio (la recta baja, no sube). -/
theorem largoMinimo_no_monotona : ¬ Monotone (largoMinimo (formulaPegada 14)) := by
  intro hm
  have h1 := hm (show 3 ≤ 5 by omega)
  have ⟨h5, h3, _⟩ := compromiso_14
  have : (16 : ℕ∞) ≤ 15 := h3.trans (h1.trans h5)
  exact absurd this (by norm_num)

/- Mutantes, en copias fuera del repositorio (`cajagris/m*.lean`); todos rompen la compilación.
1. Resolver con una cláusula que no está en la configuración (sin `h₁` en `Avanza.resuelve`): rompe la sanidad y lo
   que se apoya en ella. **Probado falso** (`falsos.lean`, `m1_falso`): «refuta» la fórmula satisfacible `¬x₀`.
2. No contar las cargas en `largoDe`: rompe `Recorre.sin_borrar`, `Recorre.prueba`, `card_le_largoDe` y el compromiso.
   **Probado falso** (`m2_falso`): la refutación de la cadena con `k = 14` mide 15 < 16 en espacio 3.
3. Quitar el tope de espacio de `Recorre.paso`: rompe `Recorre.mono`, `Recorre.critico` y la cota de espacio.
   **Probado falso** (`m3_falso`): la completa con 3 variables «se refuta» en espacio 0.
4. Cargar cualquier cláusula (sin `c ∈ F`): rompe la sanidad. **Probado falso** (`m4_falso`): se carga la vacía.
5. Cota `w + 2` en `espacio_ge`: la prueba no cierra (`omega`). **Probado falso** aquí mismo: `cota_ancho_justa`.
6. Correr sin borrar en espacio `L − 1`: rompe `refutaEn_sin_borrar` y lo que la usa. **Probado falso** aquí mismo:
   `sin_borrar_no_menos`.
Además, `largoMinimo_no_monotona` refuta el enunciado invertido de la meta 2.
-/

end Sagitta.Map.Tiempo.CajaGris
