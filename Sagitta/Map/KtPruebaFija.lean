import Sagitta.Map.KtSAT
import Sagitta.Map.KolmogorovTiempo
import Sagitta.Map.HuevoGallina

/-!
# Un teorema fijo: su prueba se paga una vez

La idea es de José (24 nov 2026). La fórmula «existe una prueba de `T` de largo `≤ n`» tiene por soluciones las pruebas
de `T`. Si `T` tiene una prueba `π` de largo `L`, un programa que trae `π` escrita resuelve la fórmula para **todo**
`n ≥ L`. Por eso su `kt` (`UniversoCerrado.kt`) es una constante, lo que mide ese programa, más lo que cuesta leer la
fórmula. La dificultad de un teorema fijo la pagó una sola vez quien encontró la prueba.

## Qué se prueba

1. **Meta 1, el universo de una familia con solución fija** (`SolucionFija`, `correcto_fijo`, `resoluble_familia`).
   Una familia de entradas `x n` con una misma solución `y₀` que `V` acepta para todo `n ≥ L`. No hace falta que `V`
   sea primitivo recursivo. El proceso es `(indiceFijo y₀, x + 1)`: `indiceFijo y₀` es el índice de
   `KolmogorovTiempo.arbol y₀`, un `Code` que no lee su entrada y escribe `y₀`; corre sobre `x` con presupuesto `x + 1`
   (`evaln_arbol_entrada`, la versión de `evaln_arbol` con entrada).
2. **Meta 2, la forma exacta de la cota** (`kt_con_solucion`, `kt_familia_fija`, `exceso_acotado`,
   `costo_familia_fija`): para todo `n ≥ L`,
   `log₂ (x n) ≤ kt ⟨V, x n⟩ ≤ i₀ + ⌈log₂ (x n + K)⌉`, con `i₀ = indiceFijo y₀` y `K = 1`.
   `i₀` depende solo de `y₀`, y `K` de nada. En costos: costo cerrado `≤ 2^i₀ · (x n + 1)` y Levin `< 8 · 2^i₀ · (x n + 1)`.
   El piso `log₂ (x n)` es la lectura (`KtSAT.log_x_le_kt`); el techo es la misma lectura más la constante `i₀`.
   **La prueba fija se paga una vez, `i₀`; lo demás es leer la fórmula.**
3. **Meta 3, el teorema fijo** (`SistemaPruebas`, `vPrueba`, `uPrueba`, `primrec_vPrueba`, `prueba_es_fija`,
   `teorema_fijo`). Un sistema de pruebas **modelado** por un verificador `verifica T π` y un largo `largo π`; la
   entrada es `pair T n`. Si `π` prueba `T` y `n ≥ largo π`:
   `log₂ (pair T n) ≤ kt ≤ i₀ + ⌈log₂ (pair T n + 1)⌉ ≤ i₀ + 2 ⌈log₂ (max T n + 1)⌉`, con `i₀ = indiceFijo π`.
   Si el sistema es primitivo recursivo, `vPrueba` también (vale `levin_es_programa`).
   **Con SAT** (`formulaFija`, `vSAT_formulaFija`, `formulaFija_es_fija`, `teorema_fijo_sat`): `φ_n = φ ∧ ¬v_n` dice «la
   asignación fija `σ` cabe en `n`»; para `n ≥ |σ|`, `φ_n` es satisfacible y
   `ktSAT φ_n ≤ indiceFijo (encode σ) + ⌈log₂ (encode φ_n + 1)⌉`. Aquí `σ` hace de prueba y `φ` de teorema.
4. **Meta 4, el contraste** (`informacion_crece`, `contraste`, `contraste_caja_negra`).
   * **En el universo cerrado**: la familia `uEscondida m` (verificador «¿es `m`?», el `igual m` de `LeyTresMemorias`)
     tiene la entrada **fija** `0`, así que la lectura no cambia. Aun así, para todo `C` hay un `m < (C+1)(2^C+1) + 1`
     con `kt > C`: los procesos con `i + ⌈log₂ k⌉ ≤ C` son a lo sumo `(C+1)(2^C+1)` y cada uno entrega una sola
     respuesta. Por lo tanto **no** hay `i₀, K` con `kt U ≤ i₀ + ⌈log₂ (U.x + K)⌉` para todo universo resoluble: la cota
     de la meta 2 necesita la solución fija.
   * **En caja negra** (`HuevoGallina`): el creador constante (una sola solución escondida, con cualquier azar `r` y
     trabajo `W`) se resuelve en `t = 0`; el creador identidad (`2^r` soluciones) obliga a `2^r ≤ t + 1`.
   Con solución fija, `kt` es constante más lectura; con información que crece, el precio por instancia crece.
5. **Mutantes refutados y controles** (`mutante_sin_lectura`, `mutante_sin_aceptar`, `control_vacio`,
   `control_negativa`). Quitar la lectura de la cota es **falso** (la lectura de `φ_n` crece con `n`); quitar la
   hipótesis de que `V` acepta `y₀` hace falso «resoluble». La desigualdad de `kt` sola sobrevive, pero vacía: sin
   solución `kt = 0` por la convención `sInf ∅` (`control_vacio`); por eso los teoremas concluyen también `Resoluble`.
   La familia fácil de `KtSAT` (`negativa_facil`) es el caso `φ = []`, `σ = []`.

## La lectura

* **Un teorema fijo no hace difícil a SAT.** La familia «`T` tiene prueba de largo `≤ n`», con `T` fijo, cuesta en `kt`
  lo que cuesta leerla más una constante: el descubrimiento de la prueba se pagó una vez, en `i₀`, y después se copia.
  Es la amortización de `LeyInformacion.lean` (`total_amortizado`, `alguien_pago`) vista desde el universo cerrado: la
  información de `π` la pagó alguien, una vez (`i₀ ≥ 0` no desaparece), y por instancia ya no informa nada
  (`LeyInformacion.una_vez_no_informa_nada`).
* **La dificultad necesita familias de teoremas cuyas pruebas crezcan sin cota.** Si la información de la solución
  crece con la instancia, el precio por instancia crece (`informacion_crece`, `contraste_caja_negra`). Para que SAT sea
  difícil en el universo cerrado (`KtSAT.facil_iff_kt`) hace falta que el exceso `kt − lectura` no esté acotado por
  `O(log)`; con solución fija está acotado por la constante `i₀` (`exceso_acotado`).
* **`i₀` puede ser grande.** Es el índice de `arbol π` en la numeración de Mathlib (`encodeCode`, que anida
  `Nat.pair`); aquí no se acotó. Que sea constante no quiere decir que sea chico: dice que no depende de `n`.

## Lo que NO se prueba

* **No hay un sistema de pruebas concreto.** `SistemaPruebas` es una interfaz (un verificador y un largo); no se
  formaliza ninguna lógica, ni que `vPrueba` capture la demostrabilidad de nadie. El ejemplo con SAT es un modelo: la
  asignación hace de prueba.
* **Las medidas son las de `evaln`**, no tiempo de máquina: `kt` es `i + ⌈log₂ k⌉` con `k` el presupuesto de `evaln`, y
  el verificador se evalúa gratis (relativiza). La versión con máquinas es `LevinMaquinas.lean`; aquí no se usa.
* **El contraste en el universo cerrado es para verificadores que cambian** (`vEscondida m`). Para una familia con un
  solo `V` fijo y sin solución fija no se probó ni que la cota falle ni que valga.
* **Nada sobre `P` contra `NP`.**
-/

open Cslib Cslib.Logic.PL
open Nat.Partrec Nat.Partrec.Code
namespace Sagitta.Map.Tiempo.KtPruebaFija
open UniversoCerrado Sagitta.Map.Levin KtSAT AceleracionBlum CorteRacional TerceraCuenta

/-! ## 1. El programa que trae la solución escrita -/

/-- El árbol de `y` corre con presupuesto `k + 1` sobre toda entrada `x ≤ k`. -/
theorem evaln_arbol_entrada (y : ℕ) {x k : ℕ} (hx : x ≤ k) :
    evaln (k + 1) (KolmogorovTiempo.arbol y) x = some y := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    rcases y with _ | _ | n
    · simp [KolmogorovTiempo.arbol, evaln, hx]
    · simp [KolmogorovTiempo.arbol, evaln, hx]
    · rw [KolmogorovTiempo.arbol]
      have ha := ih _ (Nat.unpair_lt (by omega))
      have hb := ih _ (KolmogorovTiempo.unpair_right_lt (by omega))
      simp [evaln, ha, hb, hx, Seq.seq, Nat.pair_unpair]

/-- **El índice del programa que trae `y₀` escrito**: `encodeCode (arbol y₀)`. No lee su entrada. -/
def indiceFijo (y₀ : ℕ) : ℕ := encodeCode (KolmogorovTiempo.arbol y₀)

/-- Correr `indiceFijo y₀` con presupuesto `x + 1` sobre `x` entrega `y₀`. -/
theorem correr_fijo (y₀ x : ℕ) : correr (indiceFijo y₀) (x + 1) x = some y₀ := by
  have hc : ofNatCode (encodeCode (KolmogorovTiempo.arbol y₀)) = KolmogorovTiempo.arbol y₀ :=
    Denumerable.ofNat_encode (KolmogorovTiempo.arbol y₀)
  unfold correr indiceFijo
  rw [hc]
  exact evaln_arbol_entrada y₀ le_rfl

/-! ## 2. Meta 1 y 2: una familia con solución fija -/

/-- **Una familia con solución fija**: la entrada `x n` cambia con `n`, pero desde `n = L` una misma `y₀` es aceptada
por `V` en todas. No se pide que `V` sea primitivo recursivo: la cota vale para cualquier verificador. -/
def SolucionFija (V : ℕ → ℕ → Bool) (x : ℕ → ℕ) (y₀ L : ℕ) : Prop := ∀ n, L ≤ n → V (x n) y₀ = true

/-- **Si `V` acepta `y₀` en `x`, el proceso `(indiceFijo y₀, x + 1)` es correcto.** -/
theorem correcto_fijo {V : ℕ → ℕ → Bool} {x y₀ : ℕ} (h : V x y₀ = true) :
    Correcto ⟨V, x⟩ ⟨indiceFijo y₀, x + 1⟩ :=
  ⟨y₀, correr_fijo y₀ x, h⟩

/-- **La cota de un universo con la solución en la mano**: si `V x y₀`, el universo es resoluble,
`log₂ x ≤ kt ≤ indiceFijo y₀ + ⌈log₂ (x + 1)⌉`, el costo cerrado es `≤ 2^(indiceFijo y₀) · (x + 1)` y la búsqueda de
Levin cuesta menos que `8` veces eso. -/
theorem kt_con_solucion {V : ℕ → ℕ → Bool} {x y₀ : ℕ} (h : V x y₀ = true) :
    Resoluble ⟨V, x⟩ ∧ Nat.log 2 x ≤ kt ⟨V, x⟩ ∧ kt ⟨V, x⟩ ≤ indiceFijo y₀ + Nat.clog 2 (x + 1) ∧
      costoCerrado ⟨V, x⟩ ≤ 2 ^ indiceFijo y₀ * (x + 1) ∧
      costoLevin V x < 8 * (2 ^ indiceFijo y₀ * (x + 1)) := by
  have hc := correcto_fijo h
  exact ⟨⟨_, hc⟩, log_x_le_kt (U := ⟨V, x⟩) ⟨_, hc⟩, kt_le hc, costoCerrado_le hc, levin_contra_proceso hc⟩

/-- **Meta 1: con solución fija, toda la familia es resoluble** desde `L`. -/
theorem resoluble_familia {V : ℕ → ℕ → Bool} {x : ℕ → ℕ} {y₀ L : ℕ} (h : SolucionFija V x y₀ L) :
    ∀ n, L ≤ n → Resoluble ⟨V, x n⟩ :=
  fun n hn => (kt_con_solucion (h n hn)).1

/-- **Meta 2: la `kt` de la familia es una constante más la lectura.** Con `i₀ = indiceFijo y₀` y `K = 1`, que
dependen solo de `y₀` (`K` ni siquiera de eso), para todo `n ≥ L`:
`log₂ (x n) ≤ kt ⟨V, x n⟩ ≤ i₀ + ⌈log₂ (x n + K)⌉`. La prueba fija se paga una vez, `i₀`; lo demás es leer. -/
theorem kt_familia_fija {V : ℕ → ℕ → Bool} {x : ℕ → ℕ} {y₀ L : ℕ} (h : SolucionFija V x y₀ L) :
    ∃ i₀ K : ℕ, i₀ = indiceFijo y₀ ∧ K = 1 ∧ ∀ n, L ≤ n →
      Nat.log 2 (x n) ≤ kt ⟨V, x n⟩ ∧ kt ⟨V, x n⟩ ≤ i₀ + Nat.clog 2 (x n + K) :=
  ⟨_, _, rfl, rfl, fun n hn => ⟨(kt_con_solucion (h n hn)).2.1, (kt_con_solucion (h n hn)).2.2.1⟩⟩

/-- **El exceso sobre la lectura es acotado.** Con solución fija, `kt − ⌈log₂ (x n + 1)⌉ ≤ i₀` para todo `n ≥ L`: el
«exceso» que en `KtSAT` es la profundidad de la solución no crece en la familia. -/
theorem exceso_acotado {V : ℕ → ℕ → Bool} {x : ℕ → ℕ} {y₀ L : ℕ} (h : SolucionFija V x y₀ L) :
    ∀ n, L ≤ n → kt ⟨V, x n⟩ - Nat.clog 2 (x n + 1) ≤ indiceFijo y₀ := by
  intro n hn
  have := (kt_con_solucion (h n hn)).2.2.1
  omega

/-- **En costos**: con solución fija, el costo cerrado es `O(x n)` y Levin también, con la constante `2^i₀` que paga
la prueba una vez. -/
theorem costo_familia_fija {V : ℕ → ℕ → Bool} {x : ℕ → ℕ} {y₀ L : ℕ} (h : SolucionFija V x y₀ L) :
    ∀ n, L ≤ n → costoCerrado ⟨V, x n⟩ ≤ 2 ^ indiceFijo y₀ * (x n + 1) ∧
      costoLevin V (x n) < 8 * (2 ^ indiceFijo y₀ * (x n + 1)) :=
  fun n hn => (kt_con_solucion (h n hn)).2.2.2

/-! ## 3. Meta 3: el teorema fijo -/

/-- **Un sistema de pruebas, modelado**: un verificador `verifica T π` («`π` es una prueba de `T`») y un largo
`largo π`. No es un sistema formal concreto: es la interfaz que necesita la cuenta. -/
structure SistemaPruebas where
  /-- `verifica T π = true` si `π` es una prueba de `T`. -/
  verifica : ℕ → ℕ → Bool
  /-- El largo de la prueba. -/
  largo : ℕ → ℕ

/-- **La fórmula «existe una prueba de `T` de largo `≤ n`»** como verificador: la entrada codifica `(T, n)` con
`Nat.pair`; la solución es la prueba. -/
def vPrueba (S : SistemaPruebas) (x π : ℕ) : Bool :=
  S.verifica (Nat.unpair x).1 π && decide (S.largo π ≤ (Nat.unpair x).2)

/-- **El universo del teorema `T` con cota `n`**: `⟨vPrueba S, pair T n⟩`. -/
def uPrueba (S : SistemaPruebas) (T n : ℕ) : Universo := ⟨vPrueba S, Nat.pair T n⟩

/-- **Si el sistema es primitivo recursivo, `vPrueba` también**: vale todo `UniversoCerrado.lean`, incluida la búsqueda
de Levin como programa. -/
theorem primrec_vPrueba {S : SistemaPruebas} (hv : Primrec₂ S.verifica) (hl : Primrec S.largo) :
    Primrec₂ (vPrueba S) := by
  have h1 : Primrec fun q : ℕ × ℕ => S.verifica (Nat.unpair q.1).1 q.2 :=
    hv.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd
  have h2 : Primrec fun q : ℕ × ℕ => decide (S.largo q.2 ≤ (Nat.unpair q.1).2) :=
    (Primrec.nat_le.comp (hl.comp Primrec.snd) (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).decide
  exact (Primrec.and.comp h1 h2).to₂

/-- **El teorema fijo es una familia con solución fija**: si `π` prueba `T`, la familia `n ↦ pair T n` tiene la
solución fija `π` desde `n = largo π`. -/
theorem prueba_es_fija {S : SistemaPruebas} {T π : ℕ} (hπ : S.verifica T π = true) :
    SolucionFija (vPrueba S) (Nat.pair T) π (S.largo π) := by
  intro n hn
  simp [vPrueba, Nat.unpair_pair, hπ, hn]

/-- `⌈log₂ (a²)⌉ ≤ 2 ⌈log₂ a⌉`. -/
theorem clog_sq_le (a : ℕ) : Nat.clog 2 (a ^ 2) ≤ 2 * Nat.clog 2 a := by
  apply Nat.clog_le_of_le_pow
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two a) 2

/-- **Meta 3: el teorema fijo.** Si `π` es una prueba de `T`, para todo `n ≥ largo π`, «existe una prueba de `T` de
largo `≤ n`» es resoluble y su `kt` es `log₂ (pair T n) ≤ kt ≤ i₀ + ⌈log₂ (pair T n + 1)⌉`, con `i₀ = indiceFijo π`;
y como `pair T n < (max T n + 1)²`, `kt ≤ i₀ + 2 ⌈log₂ (max T n + 1)⌉`. Para `n ≥ T` la lectura es `2 ⌈log₂ (n + 1)⌉`:
**el teorema ya no cuesta nada por instancia**; quien encontró `π` lo pagó una vez. -/
theorem teorema_fijo {S : SistemaPruebas} {T π : ℕ} (hπ : S.verifica T π = true) (n : ℕ) (hn : S.largo π ≤ n) :
    Resoluble (uPrueba S T n) ∧ Nat.log 2 (Nat.pair T n) ≤ kt (uPrueba S T n) ∧
      kt (uPrueba S T n) ≤ indiceFijo π + Nat.clog 2 (Nat.pair T n + 1) ∧
      kt (uPrueba S T n) ≤ indiceFijo π + 2 * Nat.clog 2 (max T n + 1) := by
  have h := kt_con_solucion (prueba_es_fija hπ n hn)
  refine ⟨h.1, h.2.1, h.2.2.1, le_trans h.2.2.1 (Nat.add_le_add_left ?_ _)⟩
  calc Nat.clog 2 (Nat.pair T n + 1) ≤ Nat.clog 2 ((max T n + 1) ^ 2) :=
        Nat.clog_mono_right _ (Nat.pair_lt_max_add_one_sq T n)
    _ ≤ 2 * Nat.clog 2 (max T n + 1) := clog_sq_le _

/-! ### El mismo caso, con SAT

Para no depender de un sistema de pruebas modelado: `φ` es una fórmula y `σ` una asignación fija que la satisface
(«la prueba»); `φ_n = φ ∧ ¬v_n` dice «`σ` cabe en `n`»: si `|σ| ≤ n`, la variable `n` es falsa en `asigDeLista σ`.
La familia `n ↦ φ_n` tiene la solución fija `σ`. -/

/-- **La fórmula del teorema fijo con cota `n`**: `φ ++ [[(n, false)]]`. -/
def formulaFija (φ : List Clausula) (n : ℕ) : List Clausula := φ ++ [[(n, false)]]

/-- `σ` satisface `φ_n` si satisface `φ` y cabe en `n`. -/
theorem vSAT_formulaFija {φ : List Clausula} {σ : List Bool}
    (hσ : CNF.eval (asigDeLista σ) (φ : CNF ℕ) = true) {n : ℕ} (hn : σ.length ≤ n) :
    vSAT (Encodable.encode (formulaFija φ n)) (Encodable.encode σ) = true := by
  rw [vSAT_encode]
  have hv : asigDeLista σ n = false := by
    simp [asigDeLista, List.getD_eq_getElem?_getD, List.getElem?_eq_none hn]
  simp only [CNF.eval, List.all_eq_true] at hσ ⊢
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hσ c hc
  · simp only [List.mem_singleton] at hc
    subst hc
    simp [Clause.eval, Literal.eval, hv]

/-- **La familia SAT del teorema fijo tiene solución fija**: `encode σ`, desde `n = |σ|`. -/
theorem formulaFija_es_fija {φ : List Clausula} {σ : List Bool}
    (hσ : CNF.eval (asigDeLista σ) (φ : CNF ℕ) = true) :
    SolucionFija vSAT (fun n => Encodable.encode (formulaFija φ n)) (Encodable.encode σ) σ.length :=
  fun _ hn => vSAT_formulaFija hσ hn

/-- **Meta 3 con SAT.** Para `n ≥ |σ|`, `φ_n` es satisfacible y
`log₂ (encode φ_n) ≤ ktSAT φ_n ≤ indiceFijo (encode σ) + ⌈log₂ (encode φ_n + 1)⌉`. -/
theorem teorema_fijo_sat {φ : List Clausula} {σ : List Bool}
    (hσ : CNF.eval (asigDeLista σ) (φ : CNF ℕ) = true) (n : ℕ) (hn : σ.length ≤ n) :
    Satisfacible (formulaFija φ n) ∧
      Nat.log 2 (Encodable.encode (formulaFija φ n)) ≤ ktSAT (formulaFija φ n) ∧
      ktSAT (formulaFija φ n) ≤
        indiceFijo (Encodable.encode σ) + Nat.clog 2 (Encodable.encode (formulaFija φ n) + 1) := by
  have h := kt_con_solucion (vSAT_formulaFija hσ hn)
  exact ⟨(resoluble_iff _).1 h.1, h.2.1, h.2.2.1⟩

/-- La codificación de `φ_n` es al menos `n`: la lectura de `φ_n` crece con `n`. -/
theorem le_encode_formulaFija (φ : List Clausula) (n : ℕ) : n ≤ Encodable.encode (formulaFija φ n) := by
  unfold formulaFija
  induction φ with
  | nil => exact le_encode_unitaria n false
  | cons c φ ih =>
    rw [List.cons_append, Encodable.encode_list_cons]
    exact le_trans ih (le_trans (Nat.right_le_pair _ _) (Nat.le_succ _))

/-! ## 4. Meta 4: el contraste. Si la información crece, el precio por instancia crece -/

/-- **El verificador de la solución escondida** `m`, en el universo cerrado: la única respuesta aceptada es `m`. Es
`igual m` de `LeyTresMemorias`, como función de `ℕ`. -/
def vEscondida (m : ℕ) : ℕ → ℕ → Bool := fun _ y => decide (y = m)

/-- El universo de la solución escondida `m`, con la entrada fija `0`: **la lectura no cambia**, lo único que cambia
de un universo a otro es la información `m`. -/
def uEscondida (m : ℕ) : Universo := ⟨vEscondida m, 0⟩

/-- Cada universo de la familia es resoluble (el programa que trae `m` escrito). -/
theorem uEscondida_resoluble (m : ℕ) : Resoluble (uEscondida m) :=
  ⟨_, correcto_fijo (V := vEscondida m) (x := 0) (y₀ := m) (by simp [vEscondida])⟩

/-- **Con información que crece, `kt` no está acotada, aunque la lectura sea fija.** Para todo `C`, entre los
primeros `(C+1)(2^C+1) + 1` universos `uEscondida m` hay uno con `kt > C`: los procesos con `i + ⌈log₂ k⌉ ≤ C` son
a lo sumo `(C+1)(2^C+1)` y cada uno entrega una sola respuesta sobre la entrada `0`. Es el conteo de `HuevoGallina`
dentro del universo cerrado. -/
theorem informacion_crece (C : ℕ) : ∃ m, m < (C + 1) * (2 ^ C + 1) + 1 ∧ C < kt (uEscondida m) := by
  classical
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  have hp : ∀ m, ∃ p : Proceso, Correcto (uEscondida m) p ∧ kt (uEscondida m) = p.i + Nat.clog 2 p.k :=
    fun m => kt_alcanzado (uEscondida_resoluble m)
  choose f hf hfe using hp
  let g : ℕ → ℕ × ℕ := fun m => ((f m).i, (f m).k)
  have hmaps : Set.MapsTo g (Finset.range ((C + 1) * (2 ^ C + 1) + 1) : Set ℕ)
      ((Finset.range (C + 1) ×ˢ Finset.range (2 ^ C + 1) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro m hm
    have hm' : m < (C + 1) * (2 ^ C + 1) + 1 := Finset.mem_range.1 hm
    have hk := hno m hm'
    rw [hfe m] at hk
    have hk2 : (f m).k ≤ 2 ^ C := (Nat.clog_le_iff_le_pow one_lt_two).1 (by omega)
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, g]
    omega
  have hinj : Set.InjOn g (Finset.range ((C + 1) * (2 ^ C + 1) + 1) : Set ℕ) := by
    intro a _ b _ hab
    simp only [g, Prod.mk.injEq] at hab
    obtain ⟨ya, hya, hVa⟩ := hf a
    obtain ⟨yb, hyb, hVb⟩ := hf b
    have hya' : ya = a := by simpa [uEscondida, vEscondida] using hVa
    have hyb' : yb = b := by simpa [uEscondida, vEscondida] using hVb
    have : correr (f a).i (f a).k 0 = correr (f b).i (f b).k 0 := by rw [hab.1, hab.2]
    simp only [uEscondida] at hya hyb
    rw [hya, hyb, Option.some.injEq] at this
    omega
  have := Finset.card_le_card_of_injOn g hmaps hinj
  simp only [Finset.card_range, Finset.card_product] at this
  omega

/-- **Meta 4, el contraste en el universo cerrado.**
* Con solución fija (`SolucionFija V x y₀ L`), `kt ⟨V, x n⟩ ≤ i₀ + ⌈log₂ (x n + 1)⌉`: una constante más la lectura.
* Con información que crece (`uEscondida m`, entrada fija `0`, lectura constante), `kt` no está acotada.
Por eso la cota de la meta 2 **no** vale sin la solución fija: no hay `i₀, K` uniformes para toda familia resoluble. -/
theorem contraste :
    (∀ (V : ℕ → ℕ → Bool) (x : ℕ → ℕ) (y₀ L : ℕ), SolucionFija V x y₀ L →
      ∀ n, L ≤ n → kt ⟨V, x n⟩ ≤ indiceFijo y₀ + Nat.clog 2 (x n + 1)) ∧
    (∀ m, Resoluble (uEscondida m)) ∧ (∀ C, ∃ m, C < kt (uEscondida m)) ∧
    ¬ ∃ i₀ K : ℕ, ∀ U : Universo, Resoluble U → kt U ≤ i₀ + Nat.clog 2 (U.x + K) := by
  refine ⟨fun V x y₀ L h n hn => (kt_con_solucion (h n hn)).2.2.1, uEscondida_resoluble,
    fun C => (informacion_crece C).imp fun _ h => h.2, ?_⟩
  rintro ⟨i₀, K, h⟩
  obtain ⟨m, -, hm⟩ := informacion_crece (i₀ + Nat.clog 2 K)
  have := h (uEscondida m) (uEscondida_resoluble m)
  simp only [uEscondida, zero_add] at this
  exact absurd hm (not_lt.2 this)

/-- **El contraste en caja negra** (`HuevoGallina`): el creador constante (una sola solución escondida, con cualquier
cantidad `r` de azar y trabajo `W`) se resuelve sin cita en `t = 0`; el creador identidad, con `2^r` soluciones
escondidas, obliga a todo resolvedor sin cita a `2^r ≤ t + 1`. Solución fija: precio constante; información que crece:
precio que crece. -/
theorem contraste_caja_negra (r W : ℕ) :
    HuevoGallina.ResuelveFamilia (HuevoGallina.constante r W).g
        (fun _ : Unit => LeyTresMemorias.ArbolV.hoja ()) 0 ∧
      ∀ (A : Unit → LeyTresMemorias.ArbolV (Fin (2 ^ r)) Bool (Fin (2 ^ r))) (t : ℕ),
        HuevoGallina.ResuelveFamilia (HuevoGallina.identidad r).g A t → 2 ^ r ≤ t + 1 :=
  ⟨(HuevoGallina.informacion_no_trabajo r W).2.2.2, HuevoGallina.resolver_caro r⟩

/-! ## 5. Mutantes refutados y controles -/

/-- **Mutante 1, refutado: sin la lectura.** No hay `i₀` con `ktSAT φ_n ≤ i₀` para toda `n ≥ |σ|`: la lectura
`log₂ (encode φ_n) ≥ log₂ n` crece (`log_x_le_kt`). La lectura no se puede quitar de la cota. -/
theorem mutante_sin_lectura {φ : List Clausula} {σ : List Bool}
    (hσ : CNF.eval (asigDeLista σ) (φ : CNF ℕ) = true) :
    ¬ ∃ i₀, ∀ n, σ.length ≤ n → ktSAT (formulaFija φ n) ≤ i₀ := by
  rintro ⟨i₀, h⟩
  have hn : σ.length ≤ 2 ^ (i₀ + 1) + σ.length := Nat.le_add_left _ _
  have h1 := h _ hn
  have h2 := (teorema_fijo_sat hσ _ hn).2.1
  have h3 : i₀ + 1 ≤ Nat.log 2 (Encodable.encode (formulaFija φ (2 ^ (i₀ + 1) + σ.length))) :=
    Nat.le_log_of_pow_le one_lt_two
      (le_trans (Nat.le_add_right _ _) (le_encode_formulaFija φ _))
  omega

/-- **Mutante 3, refutado: sin que `V` acepte `y₀`.** Si se quita la hipótesis `V x y₀ = true`, «resoluble» es falso:
con `V ≡ false` ningún universo es resoluble. (La desigualdad `kt ≤ …` sola sobrevive, pero vacía: `kt = 0` por
convención, `sInf ∅`.) -/
theorem mutante_sin_aceptar :
    ¬ ∀ (V : ℕ → ℕ → Bool) (x y₀ : ℕ), Resoluble ⟨V, x⟩ ∧ kt ⟨V, x⟩ ≤ indiceFijo y₀ + Nat.clog 2 (x + 1) := by
  intro h
  obtain ⟨p, y, -, hV⟩ := (h (fun _ _ => false) 0 0).1
  exact absurd hV (by simp)

/-- **Control: la convención de `sInf ∅`.** Sin solución, `kt = 0`; la cota de `kt` se cumple vacía. Por eso los
teoremas piden la solución y concluyen también `Resoluble`. -/
theorem control_vacio (x : ℕ) : ¬ Resoluble ⟨fun _ _ => false, x⟩ ∧ kt ⟨fun _ _ => false, x⟩ = 0 := by
  have hno : ¬ Resoluble ⟨fun _ _ => false, x⟩ := fun ⟨_, _, _, hV⟩ => absurd hV (by simp)
  refine ⟨hno, ?_⟩
  unfold kt
  have : {c | ∃ p, Correcto ⟨fun _ _ => false, x⟩ p ∧ c = p.i + Nat.clog 2 p.k} = ∅ :=
    Set.eq_empty_of_forall_notMem fun c ⟨p, hp, _⟩ => hno ⟨p, hp⟩
  rw [this, Nat.sInf_empty]

/-- **Control: la familia fácil de `KtSAT` es el caso `σ = []`.** Con `φ = []` y `σ = []`, `φ_n = [[(n, false)]]` y
la cota es `kt ≤ indiceFijo 0 + ⌈log₂ (encode φ_n + 1)⌉`, la misma forma que `negativa_facil` (que usa el programa `0`
en vez de `arbol 0`). -/
theorem control_negativa (n : ℕ) :
    ktSAT (formulaFija [] n) ≤ indiceFijo 0 + Nat.clog 2 (Encodable.encode (formulaFija [] n) + 1) ∧
      ktSAT (formulaFija [] n) ≤ Nat.clog 2 (Encodable.encode (formulaFija [] n) + 1) := by
  refine ⟨(teorema_fijo_sat (σ := []) rfl n (Nat.zero_le _)).2.2, ?_⟩
  exact (negativa_facil (negativa_unitaria n)).2.2.1

end Sagitta.Map.Tiempo.KtPruebaFija
