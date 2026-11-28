import Sagitta.Map.UniversoCerrado
import Sagitta.Map.CajaGris

/-!
# La tercera cuenta: justificar el «no»

En el universo cerrado (`UniversoCerrado.lean`) la búsqueda de Levin funciona porque el verificador `V` revisa cada
«sí»: un proceso que entrega una respuesta la entrega con su certificado, y `V` lo chequea. Un «no hay solución» no se
puede revisar con el verificador de NP: no hay certificado del que `V` diga «sí». En un universo cerrado, el «no» hay
que **justificarlo** con una prueba construida adentro, que el universo chequea. Esa es la **tercera cuenta**, la de
justificar, además de la de escribir el programa (`2^i`) y la de correrlo (`k`). Su precio es el largo de la prueba: es
complejidad de pruebas, NP contra coNP.

## La definición

* `Veredicto`: lo que un proceso entrega. `si σ` trae una asignación (la lista de valores de las variables `0, 1, …`);
  `no s ms` trae una refutación configuracional de `CajaGris.lean` (las jugadas `ms`, en espacio `s`). El espacio `s`
  es la memoria del refutador y la elige el proceso: **cualquier memoria**.
* `aceptaJ F v`: el universo chequea el veredicto. El «sí», evaluando la fórmula en la asignación (el verificador de
  NP); el «no», con `CajaGris.verifica` (la corrida es legal en espacio `s` y termina con la cláusula vacía). Las dos
  revisiones son `Bool` y se evalúan con `decide`.
* `precioJ F v`: lo que cuesta revisar la justificación. Para el «sí», los literales que lee la evaluación
  (`leerFormula`, a lo sumo el tamaño de la fórmula); para el «no», el largo de la refutación (`largoDe`: cargas y
  resoluciones).
* `terceraCuenta F : ℕ∞`: el mínimo precio de un veredicto aceptado. Es **la tercera cuenta**.
* Con procesos: `CorrectoJ F p v` dice que el programa `p.i` de la máquina universal, con presupuesto `p.k`, sobre la
  fórmula codificada, entrega el veredicto `v` codificado, y que el universo lo acepta. `costoJ F p v = 2^i · k +
  precio`: escribir por correr, **más justificar**. `costoCerradoJ F` es el mínimo.

## Lo que se prueba

1. **La cuenta es la de resolución.** Sin solución, `terceraCuenta F = ⨅ s, largoMinimo F s`
   (`terceraCuenta_eq_largo`): la tercera cuenta es el largo mínimo de una refutación, en la mejor memoria. Todo
   proceso correcto la paga (`terceraCuenta_le_costoJ`, `terceraCuenta_le_cerrado`), y el universo es completo: toda
   fórmula sin solución tiene un proceso que la justifica (`hay_proceso`, `verifica_de_refutaEn`).
2. **La cota real: el «no» del palomar es obligatorio y caro.** Responder «no» a la fórmula del palomar con `n + 1`
   palomas y `n` nidos cuesta al menos `2^(n/24)`, con cualquier memoria (`no_palomar_cuesta`,
   `terceraCuenta_palomar`, `palomar_cerrado`): todo veredicto aceptado es un «no» (el «sí» es imposible), y toda
   refutación aceptada, en el espacio que sea, mide al menos `2^(n/24)` (Haken, por `palomar_largoMinimo` de
   `CajaGris.lean`, que viene de cslib-frontier). Y no se paga una vez: se paga **en cada instancia**, porque el precio
   de la justificación se suma por instancia y no se esconde en la constante `2^i` del programa.
3. **Controles.**
   * (a) **La cuenta no es siempre cara** (`terceraCuenta_contra3`): `x₃ ∧ ¬x₃` no tiene solución y su tercera cuenta es
     exactamente `3`. La cota inferior es justa: toda refutación carga los dos axiomas (si no, refutaría una fórmula con
     solución) y resuelve al menos una vez (sin resolver no aparece la vacía).
   * (b) **La asimetría sí/no** (`precio_si_le`, `terceraCuenta_si_le`, `asimetria`): justificar un «sí» cuesta a lo
     sumo el tamaño de la fórmula (verificar el certificado, barato); justificar el «no» del palomar le gana a todo
     polinomio en el tamaño de la fórmula (`tamanoFormula (formulaPal n) ≤ (n + 2)^4`, `tamano_palomar_le`).
   * (c) **Sin la exigencia de justificar la cuenta baja a `0`** (`oraculo_rompe`, gemelo de `tabla_rompe`): con un
     oráculo que dice «no» gratis, el costo del «no» del palomar es `0` en toda instancia y la cota `1 ≤ costo` es
     falsa. Y ese «no» no está chequeado: el oráculo se lo dice también a una fórmula con solución, donde el universo
     cerrado no acepta ningún «no» (`oraculo_miente`).

## La lectura en el lenguaje del proyecto

Las tres memorias de José son el **resolvedor** (el programa, que se paga con `2^i`), la **cita** (lo que corre, que se
paga con `k`) y el **verificador** (lo que el universo revisa), y se comunican por el tiempo. En el universo cerrado de
`UniversoCerrado.lean` el verificador revisa gratis el «sí», y por eso Levin alcanza el costo cerrado salvo `8`. Aquí el
verificador también tiene que revisar el «no», y para eso hace falta que alguien escriba la prueba adentro: **el precio
del «no» se paga en la cuenta de justificar**. Con resolución, en el palomar, ese precio es exponencial. «El precio se
paga sí o sí; lo abierto es si una vez o en cada instancia»: el de justificar el «no» del palomar se paga en cada instancia y crece como `2^(n/24)`. (Que escribir el resolvedor
se pague una vez es lectura: en este modelo el costo cerrado se minimiza instancia por instancia y no hay un proceso
uniforme; la cota del palomar viene solo del sumando del precio, por definición de `costoJ`.)

Si en lugar de resolución se admitiera **cualquier** sistema de pruebas chequeable en tiempo polinomial, que toda fórmula
sin solución tenga una justificación de largo polinomial es exactamente `NP = coNP` (Cook y Reckhow, 1979, de memoria).
Que la tercera cuenta sea superpolinomial para todo sistema de pruebas es `NP ≠ coNP`: abierto.

## Lo que NO se prueba

* Es **resolución**, un peldaño de la escalera de sistemas de pruebas. Para Frege, Frege
  extendido y más allá no se conocen cotas superpolinomiales: nada aquí dice nada de ellos. Un universo que aceptara
  pruebas de Frege tendría su propia tercera cuenta, sin cota conocida.
* El precio del «no» es el **largo** (cargas y resoluciones), no el tiempo de máquina ni los bits de la prueba. El del
  «sí» son los literales leídos, no los pasos de una máquina. El presupuesto `k` de `correr` no se relaciona con el
  tamaño del veredicto que el programa escribe (`evaln` puede entregar un número enorme en pocas rondas); por eso el
  largo de la justificación **se suma aparte** en `costoJ`, y esa es una decisión del modelo, no un teorema.
* La cota de Haken es inferior; no se calculó el largo mínimo exacto del palomar ni se probó una cota superior cercana
  (la refutación existe, `palomar_cerrado` usa la completitud, pero no se midió).
* Nada sobre `NP` contra `coNP` ni sobre `P` contra `NP`.

## Fuentes, de memoria

S. A. Cook y R. A. Reckhow, «The relative efficiency of propositional proof systems», *Journal of Symbolic Logic*
44(1), 1979. A. Haken, «The intractability of resolution», *Theoretical Computer Science* 39, 1985 (la cota viene
formalizada en cslib-frontier, `CNF.two_pow_le_of_refutableInSize_pigeonhole`). No los leí en esta sesión.
-/

open Cslib Cslib.Logic.PL
open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map.Tiempo.TerceraCuenta

open CajaGris UniversoCerrado Sagitta.Map.Levin

/-! ## 1. El universo cerrado con justificación -/

/-- Las jugadas como suma, para codificarlas. -/
def jugadaEquivTercera : Jugada ≃ Clausula ⊕ (Clausula × Clausula × ℕ) ⊕ Clausula where
  toFun
    | .carga c => .inl c
    | .resuelve a b v => .inr (.inl (a, b, v))
    | .borra c => .inr (.inr c)
  invFun
    | .inl c => .carga c
    | .inr (.inl (a, b, v)) => .resuelve a b v
    | .inr (.inr c) => .borra c
  left_inv m := by cases m <;> rfl
  right_inv s := by rcases s with c | ⟨a, b, v⟩ | c <;> rfl

instance encodableJugadaTercera : Encodable Jugada := Encodable.ofEquiv _ jugadaEquivTercera

/-- **Un veredicto**, con su justificación: `si σ` trae la asignación (`σ[v]` es el valor de la variable `v`, falso
fuera de la lista); `no s ms` trae una refutación configuracional en espacio `s`. -/
inductive Veredicto where
  /-- «Hay solución», con el certificado. -/
  | si (σ : List Bool)
  /-- «No hay solución», con la refutación y la memoria `s` en que corre. -/
  | no (s : ℕ) (ms : List Jugada)

/-- Los veredictos como suma, para codificarlos. -/
def veredictoEquiv : Veredicto ≃ List Bool ⊕ (ℕ × List Jugada) where
  toFun
    | .si σ => .inl σ
    | .no s ms => .inr (s, ms)
  invFun
    | .inl σ => .si σ
    | .inr (s, ms) => .no s ms
  left_inv v := by cases v <;> rfl
  right_inv s := by rcases s with σ | ⟨s, ms⟩ <;> rfl

instance encodableVeredicto : Encodable Veredicto := Encodable.ofEquiv _ veredictoEquiv

/-- La asignación que da una lista: la variable `v` vale `σ[v]`, y falso fuera de la lista. -/
def asigDeLista (σ : List Bool) : ℕ → Bool := fun v => σ.getD v false

/-- **El universo chequea el veredicto.** El «sí», evaluando la fórmula en la asignación; el «no», con el verificador
de refutaciones de `CajaGris.lean`. -/
def aceptaJ (F : List Clausula) : Veredicto → Bool
  | .si σ => CNF.eval (asigDeLista σ) (F : CNF ℕ)
  | .no s ms => verifica F s ms

/-- Los literales que lee la evaluación de una cláusula: hasta el primero verdadero. -/
def leerClausula (σ : ℕ → Bool) : Clausula → ℕ
  | [] => 0
  | l :: c => if Literal.eval σ l then 1 else leerClausula σ c + 1

/-- Los literales que lee la evaluación de una fórmula: cláusula por cláusula, hasta la primera falsa. -/
def leerFormula (σ : ℕ → Bool) : List Clausula → ℕ
  | [] => 0
  | c :: F => leerClausula σ c + if Clause.eval σ c then leerFormula σ F else 0

/-- El tamaño de una fórmula: el número de literales. -/
def tamanoFormula (F : List Clausula) : ℕ := (F.map List.length).sum

/-- **El precio de revisar la justificación.** El «sí»: los literales que lee la evaluación. El «no»: el largo de la
refutación (cargas y resoluciones). -/
def precioJ (F : List Clausula) : Veredicto → ℕ
  | .si σ => leerFormula (asigDeLista σ) F
  | .no _ ms => largoDe ms

/-- **La tercera cuenta**: el mínimo precio de un veredicto que el universo acepta (`⊤` si no hay ninguno). -/
noncomputable def terceraCuenta (F : List Clausula) : ℕ∞ :=
  ⨅ (v : Veredicto) (_ : aceptaJ F v = true), (precioJ F v : ℕ∞)

theorem terceraCuenta_le {F : List Clausula} {v : Veredicto} (h : aceptaJ F v = true) :
    terceraCuenta F ≤ precioJ F v :=
  iInf₂_le v h

theorem le_terceraCuenta {F : List Clausula} {B : ℕ} (h : ∀ v, aceptaJ F v = true → B ≤ precioJ F v) :
    (B : ℕ∞) ≤ terceraCuenta F :=
  le_iInf₂ fun v hv => by exact_mod_cast h v hv

/-! ### Sanidad: el universo no acepta un veredicto falso -/

theorem si_sano {F : List Clausula} {σ : List Bool} (h : aceptaJ F (.si σ) = true) :
    CNF.Satisfiable (F : CNF ℕ) :=
  ⟨asigDeLista σ, h⟩

theorem no_sano {F : List Clausula} {s : ℕ} {ms : List Jugada} (h : aceptaJ F (.no s ms) = true) :
    ¬ CNF.Satisfiable (F : CNF ℕ) :=
  refutacion_sana (refutaEn_de_verifica h)

/-! ### Completitud del verificador de refutaciones -/

theorem aplica_de_avanza {F : List Clausula} {M M₁ : Finset Clausula} {m : Jugada} (h : Avanza F M m M₁) :
    aplica F M m = some M₁ := by
  cases h with
  | carga hc => simp [aplica, hc]
  | resuelve v h₁ h₂ hv₁ hv₂ => simp [aplica, h₁, h₂, hv₁, hv₂]
  | borra c => rfl

theorem corre_de_recorre {F : List Clausula} {s : ℕ} {M M' : Finset Clausula} {ms : List Jugada}
    (r : Recorre F s M ms M') : corre F s M ms = some M' := by
  induction r with
  | fin => rfl
  | paso h hs _ ih => simp [corre, aplica_de_avanza h, hs, ih]

/-- **El verificador es completo**: toda refutación configuracional se escribe como una lista de jugadas que
`verifica` acepta, con el mismo largo. -/
theorem verifica_de_refutaEn {F : List Clausula} {s L : ℕ} (h : RefutaEn F s L) :
    ∃ ms, verifica F s ms = true ∧ largoDe ms ≤ L := by
  obtain ⟨ms, M, r, hM, hl⟩ := h
  exact ⟨ms, by simp [verifica, corre_de_recorre r, hM], hl⟩

/-! ### La tercera cuenta del «no» es el largo mínimo de resolución -/

/-- **Sin solución, la tercera cuenta es el largo mínimo de una refutación, en la mejor memoria.** -/
theorem terceraCuenta_eq_largo {F : List Clausula} (hF : ¬ CNF.Satisfiable (F : CNF ℕ)) :
    terceraCuenta F = ⨅ s, largoMinimo F s := by
  apply le_antisymm
  · refine le_iInf fun s => le_iInf₂ fun L hL => ?_
    obtain ⟨ms, hv, hl⟩ := verifica_de_refutaEn hL
    exact (terceraCuenta_le (v := .no s ms) hv).trans (by exact_mod_cast hl)
  · refine le_iInf₂ fun v hv => ?_
    cases v with
    | si σ => exact absurd (si_sano hv) hF
    | no s ms => exact (iInf_le _ s).trans (largoMinimo_le (refutaEn_de_verifica hv))

/-! ### Procesos cerrados que justifican -/

/-- **Un proceso cerrado con justificación es correcto** si el programa `p.i`, con presupuesto `p.k`, sobre la fórmula
codificada, entrega el veredicto `v` codificado, y el universo acepta `v`. -/
def CorrectoJ (F : List Clausula) (p : Proceso) (v : Veredicto) : Prop :=
  correr p.i p.k (Encodable.encode F) = some (Encodable.encode v) ∧ aceptaJ F v = true

/-- **El costo con justificación**: escribir por correr, **más** justificar. -/
def costoJ (F : List Clausula) (p : Proceso) (v : Veredicto) : ℕ := p.costoTotal + precioJ F v

/-- **El costo cerrado con justificación**: el mínimo sobre los procesos correctos (`0` si no hay ninguno). -/
noncomputable def costoCerradoJ (F : List Clausula) : ℕ :=
  sInf {c | ∃ p v, CorrectoJ F p v ∧ c = costoJ F p v}

/-- **Lo aceptable se puede entregar**: si el universo acepta `v`, algún proceso cerrado lo entrega (el programa
constante, por `correr_universal`). -/
theorem hay_proceso {F : List Clausula} {v : Veredicto} (h : aceptaJ F v = true) : ∃ p, CorrectoJ F p v := by
  obtain ⟨i, hi⟩ := correr_universal (f := fun _ => Part.some (Encodable.encode v))
    (Partrec.nat_iff.1 (Computable.const (Encodable.encode v) : Computable fun _ : ℕ => Encodable.encode v))
  obtain ⟨k, hk⟩ := (hi (Encodable.encode F) (Encodable.encode v)).1 (Part.mem_some _)
  exact ⟨⟨i, k⟩, hk, h⟩

theorem costoCerradoJ_le {F : List Clausula} {p : Proceso} {v : Veredicto} (h : CorrectoJ F p v) :
    costoCerradoJ F ≤ costoJ F p v :=
  Nat.sInf_le ⟨p, v, h, rfl⟩

theorem costoCerradoJ_alcanzado {F : List Clausula} (h : ∃ p v, CorrectoJ F p v) :
    ∃ p v, CorrectoJ F p v ∧ costoCerradoJ F = costoJ F p v := by
  obtain ⟨p, v, hp⟩ := h
  have hne : {c | ∃ p v, CorrectoJ F p v ∧ c = costoJ F p v}.Nonempty := ⟨_, p, v, hp, rfl⟩
  obtain ⟨q, w, hq, he⟩ := Nat.sInf_mem hne
  exact ⟨q, w, hq, he⟩

/-- **Todo proceso correcto paga la tercera cuenta.** -/
theorem terceraCuenta_le_costoJ {F : List Clausula} {p : Proceso} {v : Veredicto} (h : CorrectoJ F p v) :
    terceraCuenta F ≤ costoJ F p v :=
  (terceraCuenta_le h.2).trans (by exact_mod_cast Nat.le_add_left _ _)

/-- **El costo cerrado con justificación paga la tercera cuenta**, y paga además leer la entrada. -/
theorem terceraCuenta_le_cerrado {F : List Clausula} (h : ∃ p v, CorrectoJ F p v) :
    terceraCuenta F ≤ costoCerradoJ F ∧ Encodable.encode F < costoCerradoJ F := by
  obtain ⟨p, v, hp, he⟩ := costoCerradoJ_alcanzado h
  rw [he]
  refine ⟨terceraCuenta_le_costoJ hp, ?_⟩
  have h1 : Encodable.encode F < p.k := evaln_bound hp.1
  have h2 := k_le_costoTotal p
  unfold costoJ; omega

/-! ## 2. La cota real: el «no» del palomar -/

theorem palomar_insat (n : ℕ) : ¬ CNF.Satisfiable (formulaPal n : CNF ℕ) := by
  have h := (CNF.satisfiable_relabel (ordenPal_inj n) (CNF.pigeonhole (n + 1) n)).not.2
    (CNF.not_satisfiable_pigeonhole (by omega))
  exact h

/-- **Toda refutación aceptada del palomar, en cualquier memoria, mide al menos `2^(n/24)`.** -/
theorem no_palomar_cuesta {n s : ℕ} {ms : List Jugada} (h : verifica (formulaPal n) s ms = true) :
    2 ^ (n / 24) ≤ largoDe ms := by
  have h1 := palomar_largoMinimo n s
  have h2 := largoMinimo_le (refutaEn_de_verifica h)
  exact_mod_cast h1.trans h2

/-- **En el palomar, todo veredicto aceptado es un «no» y cuesta al menos `2^(n/24)`.** -/
theorem palomar_veredicto {n : ℕ} {v : Veredicto} (h : aceptaJ (formulaPal n) v = true) :
    (∃ s ms, v = .no s ms) ∧ 2 ^ (n / 24) ≤ precioJ (formulaPal n) v := by
  cases v with
  | si σ => exact absurd (si_sano h) (palomar_insat n)
  | no s ms => exact ⟨⟨s, ms, rfl⟩, no_palomar_cuesta h⟩

/-- **La tercera cuenta del palomar es al menos `2^(n/24)`.** -/
theorem terceraCuenta_palomar (n : ℕ) : ((2 ^ (n / 24) : ℕ) : ℕ∞) ≤ terceraCuenta (formulaPal n) :=
  le_terceraCuenta fun _ hv => (palomar_veredicto hv).2

/-- **La cota real, con procesos.** En el universo cerrado con justificación:
* todo proceso que resuelve el palomar responde «no», con cualquier memoria `s`, y paga al menos `2^(n/24)`;
* hay procesos que lo resuelven (completitud), así que el costo cerrado con justificación es finito y es al menos
  `2^(n/24)`.

Es la cuenta «obligatoria» en este peldaño: no hay forma de responder sin pagarla. -/
theorem palomar_cerrado (n : ℕ) :
    (∀ p v, CorrectoJ (formulaPal n) p v → (∃ s ms, v = .no s ms) ∧ 2 ^ (n / 24) ≤ costoJ (formulaPal n) p v) ∧
      (∃ p v, CorrectoJ (formulaPal n) p v) ∧ 2 ^ (n / 24) ≤ costoCerradoJ (formulaPal n) := by
  have hall : ∀ p v, CorrectoJ (formulaPal n) p v →
      (∃ s ms, v = .no s ms) ∧ 2 ^ (n / 24) ≤ costoJ (formulaPal n) p v := fun p v hp => by
    obtain ⟨h1, h2⟩ := palomar_veredicto hp.2
    exact ⟨h1, h2.trans (Nat.le_add_left _ _)⟩
  have hex : ∃ p v, CorrectoJ (formulaPal n) p v := by
    obtain ⟨L, hL⟩ := refutaEn_de_insat (palomar_insat n)
    obtain ⟨ms, hv, -⟩ := verifica_de_refutaEn hL
    obtain ⟨p, hp⟩ := hay_proceso (v := .no L ms) hv
    exact ⟨p, _, hp⟩
  refine ⟨hall, hex, ?_⟩
  obtain ⟨p, v, hp, he⟩ := costoCerradoJ_alcanzado hex
  rw [he]; exact (hall p v hp).2

/-! ## 3. Controles -/

/-! ### (a) La cuenta no es siempre cara: `x₃ ∧ ¬x₃` cuesta exactamente `3` -/

/-- Una jugada que no es un borrado. -/
def cuentaEnLargo : Jugada → Bool
  | .borra _ => false
  | _ => true

theorem largoDe_eq_length (ms : List Jugada) : largoDe ms = (ms.filter cuentaEnLargo).length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => cases m <;> simp [largoDe, cuentaEnLargo, ih, List.filter_cons]

/-- Sin resolver, una corrida solo tiene lo que tenía y axiomas. -/
theorem recorre_sin_resolver {F : List Clausula} {s : ℕ} {M M' : Finset Clausula} {ms : List Jugada}
    (r : Recorre F s M ms M') : (∀ c₁ c₂ v, Jugada.resuelve c₁ c₂ v ∉ ms) → ∀ c ∈ M', c ∈ M ∨ c ∈ F := by
  induction r with
  | fin => exact fun _ c hc => Or.inl hc
  | @paso M M₁ M₂ m ms hav hs _ ih =>
    intro h c hc
    rcases ih (fun c₁ c₂ v hm => h c₁ c₂ v (List.mem_cons_of_mem _ hm)) c hc with h1 | h1
    · cases hav with
      | carga hc' =>
        rcases Finset.mem_insert.1 h1 with rfl | h1
        exacts [Or.inr hc', Or.inl h1]
      | resuelve v _ _ _ _ => exact absurd List.mem_cons_self (h _ _ v)
      | borra _ => exact Or.inl (Finset.mem_of_mem_erase h1)
    · exact Or.inr h1

theorem contra3_carga {s : ℕ} {ms : List Jugada} {M : Finset Clausula} (r : Recorre contra3 s ∅ ms M)
    (hM : [] ∈ M) {c : Clausula} (hc : c ∈ contra3) : Jugada.carga c ∈ ms := by
  by_contra hno
  have r' := r.filtra (p := fun d => decide (d ≠ c)) fun d hd => by
    simp only [decide_eq_true_eq]; rintro rfl; exact hno hd
  refine refutacion_sana ⟨ms, M, r', hM, le_rfl⟩ ?_
  simp only [contra3, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨fun _ => false, by decide⟩
  · exact ⟨fun _ => true, by decide⟩

/-- **Toda refutación de `x₃ ∧ ¬x₃` mide al menos `3`**: carga los dos axiomas y resuelve al menos una vez. -/
theorem contra3_largo_ge {s : ℕ} {ms : List Jugada} (h : verifica contra3 s ms = true) : 3 ≤ largoDe ms := by
  have hv := h
  unfold verifica at hv
  split at hv
  · rename_i M hM
    have r := recorre_de_corre hM
    have h0 : ([] : Clausula) ∈ M := by simpa using hv
    have ha := contra3_carga r h0 (c := [(3, true)]) (by simp [contra3])
    have hb := contra3_carga r h0 (c := [(3, false)]) (by simp [contra3])
    have hr : ∃ c₁ c₂ v, Jugada.resuelve c₁ c₂ v ∈ ms := by
      by_contra hno
      push Not at hno
      rcases recorre_sin_resolver r hno [] h0 with h1 | h1
      · simp at h1
      · simp [contra3] at h1
    obtain ⟨c₁, c₂, v, hr⟩ := hr
    have hsub : [Jugada.carga [(3, true)], Jugada.carga [(3, false)], Jugada.resuelve c₁ c₂ v] ⊆
        ms.filter cuentaEnLargo := by
      intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> simp [List.mem_filter, cuentaEnLargo, *]
    have hnd : [Jugada.carga [(3, true)], Jugada.carga [(3, false)], Jugada.resuelve c₁ c₂ v].Nodup := by
      simp
    have := (hnd.subperm hsub).length_le
    rw [largoDe_eq_length]
    simpa using this
  · cases hv

/-- La refutación de tres jugadas de `x₃ ∧ ¬x₃`. -/
def refContra3 : List Jugada := [.carga [(3, true)], .carga [(3, false)], .resuelve [(3, true)] [(3, false)] 3]

theorem verifica_refContra3 : verifica contra3 3 refContra3 = true := by decide

/-- **Control (a): la cuenta no es siempre cara.** `x₃ ∧ ¬x₃` no tiene solución, su tercera cuenta es exactamente `3`
(la cota inferior se alcanza), y hay un proceso cerrado que la justifica. -/
theorem terceraCuenta_contra3 : terceraCuenta contra3 = 3 ∧ ∃ p, CorrectoJ contra3 p (.no 3 refContra3) := by
  refine ⟨le_antisymm ?_ ?_, hay_proceso verifica_refContra3⟩
  · exact (terceraCuenta_le (F := contra3) (v := .no 3 refContra3) verifica_refContra3).trans (by decide)
  · refine le_terceraCuenta fun v hv => ?_
    cases v with
    | si σ =>
      exact absurd (si_sano hv) (refutacion_sana (refutaEn_de_verifica verifica_refContra3))
    | no s ms => exact contra3_largo_ge hv

/-! ### (b) La asimetría sí/no -/

theorem leerClausula_le (σ : ℕ → Bool) (c : Clausula) : leerClausula σ c ≤ c.length := by
  induction c with
  | nil => rfl
  | cons l c ih => simp only [leerClausula, List.length_cons]; split_ifs <;> omega

theorem leerFormula_le (σ : ℕ → Bool) (F : List Clausula) : leerFormula σ F ≤ tamanoFormula F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    simp only [leerFormula, tamanoFormula, List.map_cons, List.sum_cons] at ih ⊢
    have := leerClausula_le σ c
    split_ifs <;> omega

/-- **El «sí» es barato**: el precio de revisar una asignación es a lo sumo el tamaño de la fórmula. -/
theorem precio_si_le (F : List Clausula) (σ : List Bool) : precioJ F (.si σ) ≤ tamanoFormula F :=
  leerFormula_le _ F

/-- **La tercera cuenta de una fórmula con solución (escrita como lista) es a lo sumo su tamaño.** -/
theorem terceraCuenta_si_le {F : List Clausula} {σ : List Bool} (h : aceptaJ F (.si σ) = true) :
    terceraCuenta F ≤ tamanoFormula F :=
  (terceraCuenta_le h).trans (by exact_mod_cast precio_si_le F σ)

theorem tamano_le_ancho {F : List Clausula} {w : ℕ} (h : ∀ c ∈ F, c.length ≤ w) :
    tamanoFormula F ≤ F.length * w := by
  unfold tamanoFormula
  have := List.sum_le_length_nsmul (F.map List.length) w (by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact h c hc)
  simpa using this

theorem largo_pigeonhole_le (n : ℕ) :
    (CNF.pigeonhole (n + 1) n).length ≤ (n + 1) + n * ((n + 1) * (n + 1)) := by
  simp only [CNF.pigeonhole, List.length_append, List.length_map, List.length_finRange, List.length_flatMap]
  have h1 : ∀ j : Fin n, ((List.finRange (n + 1)).map fun i =>
      (((List.finRange (n + 1)).filter (i < ·)).map fun i' => CNF.holeClause i i' j).length).sum ≤
        (n + 1) * (n + 1) := by
    intro j
    have := List.sum_le_length_nsmul ((List.finRange (n + 1)).map fun i =>
      (((List.finRange (n + 1)).filter (i < ·)).map fun i' => CNF.holeClause i i' j).length) (n + 1) (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        simpa using (List.length_filter_le _ _).trans (by simp))
    simpa using this
  have h2 := List.sum_le_length_nsmul ((List.finRange n).map fun j => ((List.finRange (n + 1)).map fun i =>
      (((List.finRange (n + 1)).filter (i < ·)).map fun i' => CNF.holeClause i i' j).length).sum)
      ((n + 1) * (n + 1)) (by
        intro x hx
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
        exact h1 j)
  simp only [List.length_map, List.length_finRange, smul_eq_mul] at h2
  omega

theorem ancho_pigeonhole_le (n : ℕ) : ∀ c ∈ CNF.pigeonhole (n + 1) n, c.length ≤ n + 2 := by
  intro c hc
  rcases CNF.mem_pigeonhole.1 hc with ⟨i, rfl⟩ | ⟨i, i', j, -, rfl⟩
  · simp [CNF.pigeonClause]
  · simp [CNF.holeClause]

/-- **El tamaño del palomar es polinomial**: a lo sumo `(n + 2)^4` literales. -/
theorem tamano_palomar_le (n : ℕ) : tamanoFormula (formulaPal n) ≤ (n + 2) ^ 4 := by
  have hw : ∀ c ∈ formulaPal n, c.length ≤ n + 2 := by
    intro c hc
    simp only [formulaPal, CNF.relabel, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    simpa [Clause.relabel] using ancho_pigeonhole_le n d hd
  have h1 := tamano_le_ancho hw
  have h2 : (formulaPal n).length ≤ (n + 1) + n * ((n + 1) * (n + 1)) := by
    simpa [formulaPal, CNF.relabel] using largo_pigeonhole_le n
  have h3 : (n + 1) + n * ((n + 1) * (n + 1)) ≤ (n + 2) ^ 3 := by ring_nf; nlinarith
  calc tamanoFormula (formulaPal n) ≤ (formulaPal n).length * (n + 2) := h1
    _ ≤ (n + 2) ^ 3 * (n + 2) := Nat.mul_le_mul_right _ (h2.trans h3)
    _ = (n + 2) ^ 4 := by ring

/-- **La asimetría sí/no.** Justificar un «sí» cuesta a lo sumo el tamaño de la fórmula. Justificar el «no» del
palomar le gana a todo polinomio en el tamaño: para todos `C` y `m` hay un `n` en que **todo** veredicto aceptado de
`formulaPal n` cuesta más que `C · (tamaño + 1)^m`. -/
theorem asimetria (C m : ℕ) :
    (∀ F σ, precioJ F (.si σ) ≤ tamanoFormula F) ∧
      ∃ n, ∀ v, aceptaJ (formulaPal n) v = true → C * (tamanoFormula (formulaPal n) + 1) ^ m < precioJ (formulaPal n) v := by
  refine ⟨precio_si_le, ?_⟩
  obtain ⟨n, hn⟩ := pow_dos_gana (C * 32 ^ m) (4 * m)
  refine ⟨n, fun v hv => lt_of_lt_of_le ?_ (palomar_veredicto hv).2⟩
  have ht : tamanoFormula (formulaPal n) + 1 ≤ 32 * (n + 1) ^ 4 := by
    have := tamano_palomar_le n
    have h2 : (n + 2) ^ 4 ≤ 16 * (n + 1) ^ 4 := by
      calc (n + 2) ^ 4 ≤ (2 * (n + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        _ = 16 * (n + 1) ^ 4 := by ring
    have h3 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  calc C * (tamanoFormula (formulaPal n) + 1) ^ m ≤ C * (32 * (n + 1) ^ 4) ^ m :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht m)
    _ = C * 32 ^ m * (n + 1) ^ (4 * m) := by rw [mul_pow, ← pow_mul]; ring
    _ < 2 ^ (n / 24) := hn

/-- Un ejemplo concreto del «sí» barato: `x₀` se justifica con la asignación `[true]` leyendo un literal. -/
theorem si_x0 : aceptaJ [[(0, true)]] (.si [true]) = true ∧ precioJ [[(0, true)]] (.si [true]) = 1 ∧
    terceraCuenta [[(0, true)]] ≤ 1 :=
  ⟨by decide, by decide, (terceraCuenta_le (v := .si [true]) (by decide)).trans (by decide)⟩

/-! ### (c) Sin exigir la justificación, la cuenta baja a `0` -/

/-- **El universo abierto con un oráculo del «no»**: si el oráculo `o` dice «no» sobre `F`, el «no» sale gratis, sin
refutación; si no, queda la tercera cuenta. -/
noncomputable def cuentaAbierta (o : List Clausula → Bool) (F : List Clausula) : ℕ∞ :=
  if o F then 0 else terceraCuenta F

/-- **El control de la cerradura** (gemelo de `tabla_rompe`). En el universo cerrado la tercera cuenta del palomar es al
menos `2^(n/24)` (y por lo tanto al menos `1`) en toda instancia; con el oráculo que dice «no» gratis es `0` en toda
instancia, y la cota `1 ≤ costo` es **falsa** en el universo abierto. -/
theorem oraculo_rompe :
    (∀ n, ((2 ^ (n / 24) : ℕ) : ℕ∞) ≤ terceraCuenta (formulaPal n)) ∧ (∀ n, 1 ≤ terceraCuenta (formulaPal n)) ∧
      (∀ n, cuentaAbierta (fun _ => true) (formulaPal n) = 0) ∧
      ¬ ∀ n, 1 ≤ cuentaAbierta (fun _ => true) (formulaPal n) := by
  have ha : ∀ n, cuentaAbierta (fun _ => true) (formulaPal n) = 0 := fun n => by simp [cuentaAbierta]
  refine ⟨terceraCuenta_palomar, fun n => le_trans ?_ (terceraCuenta_palomar n), ha, fun h => ?_⟩
  · exact_mod_cast Nat.one_le_two_pow
  · have := h 0
    rw [ha] at this
    exact absurd this (by norm_num)

/-- **El «no» gratis no está chequeado.** El mismo oráculo se lo dice a `x₀`, que tiene solución: su cuenta abierta es
`0`, pero en el universo cerrado ningún «no» de `x₀` es aceptado. -/
theorem oraculo_miente :
    cuentaAbierta (fun _ => true) [[(0, true)]] = 0 ∧ CNF.Satisfiable ([[(0, true)]] : CNF ℕ) ∧
      ∀ s ms, aceptaJ [[(0, true)]] (.no s ms) = false := by
  have hs : CNF.Satisfiable ([[(0, true)]] : CNF ℕ) := ⟨fun _ => true, by decide⟩
  refine ⟨by simp [cuentaAbierta], hs, fun s ms => ?_⟩
  cases h : aceptaJ [[(0, true)]] (.no s ms)
  · rfl
  · exact absurd hs (no_sano h)

/- Mutantes, en copias fuera del repositorio (`terceracuenta/m*.lean`); todos rompen la compilación.
1. El «no» no se chequea (`aceptaJ (.no _ _) = true`): rompe la sanidad y la cota del palomar. **Probado falso**
   (`m1_falso`): la tercera cuenta del palomar con `n = 0` queda en `0 < 1 = 2^0`.
2. El largo de la refutación no se cobra (`precioJ (.no _ _) = 0`): rompe `no_palomar`, la cota y el control (a).
   **Probado falso** (`m2_falso`): de nuevo la tercera cuenta del palomar baja a `0`.
3. Cota `2^(n/24 + 1)` en `no_palomar_cuesta`: la prueba no cierra. **Probado falso** (`falsos.lean`, `m3_falso`): con
   `n = 0` la refutación `[carga []]` mide `1 < 2`.
4. `terceraCuenta_eq_largo` sin pedir que no haya solución: la prueba no cierra. **Probado falso** (`m4_falso`): en `x₀`
   la tercera cuenta es `≤ 1` y el largo mínimo es `⊤`.
5. `terceraCuenta contra3 = 2`: `decide` refuta `3 ≤ 2`. **Probado falso** (`m5_falso`), por `terceraCuenta_contra3`.
6. `precio_si_le` estricto (`<`): la prueba no cierra. **Probado falso** (`m6_falso`): en `x₀` el «sí» lee `1 = tamaño`.
-/

end Sagitta.Map.Tiempo.TerceraCuenta
