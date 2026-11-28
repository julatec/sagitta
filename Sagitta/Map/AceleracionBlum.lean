import Sagitta.Map.LandauDenso
import Mathlib.Computability.PartrecCode

/-!
# La aceleración de Blum: el piso de un problema puede no ser un punto

`LandauDenso.lean` probó que el orden de Landau `o` («despreciable frente a») es denso y que una familia creciente no
tiene cota mínima (`sin_supremo`). Este archivo es el gemelo del lado de los algoritmos: el **teorema de aceleración de
Blum** dice que hay problemas sin algoritmo óptimo, porque todo algoritmo admite otro mucho más rápido en casi todas
las entradas.

## Qué se prueba

1. **Una medida de Blum de verdad, sobre los códigos de Mathlib** (`Nat.Partrec.Code`). El costo `pasos c n : ℕ∞` es
   el menor `k` con `evaln k c n ≠ none` (`⊤` si no hay). Cumple los dos axiomas de Blum:
   * es finito exactamente cuando `eval c n` está definido (`pasos_lt_top_iff`);
   * «`pasos c n ≤ k`» equivale a `(evaln k c n).isSome` (`pasos_le_iff`), así que es decidible (la instancia) y
     además **primitivo recursivo** en `(k, c, n)` (`primrec_pasos_le`), por `primrec_evaln` de Mathlib.
   De yapa: `n < pasos c n` siempre (`pasos_gt`), porque `evaln` exige que la entrada quepa en la cota.
2. **Lo que la aceleración obliga, en esta medida.** `TieneAceleracion r f` es el enunciado de Blum para `f`: `f` es
   computable (hay un código que la calcula) y para todo código `i` que la calcula hay otro `j` que también, con
   `r(n, costo j n) ≤ costo i n` para casi todo `n`. Si `r(n, x) ≥ (n+1)·x`:
   * cada programa tiene otro con costo **despreciable** frente al suyo (`acelera_o`);
   * **ningún programa es óptimo**, ni siquiera salvo una constante (`sin_optimo`);
   * hay una **escalera infinita** de programas, cada uno despreciable frente al anterior (`escalera_de_aceleracion`),
     y debajo de ella no hay un último piso: cualquier cota inferior se puede subir sin dejar de ser cota
     (`escalera_sin_piso`).
3. **El espejo de `sin_supremo`** (`sin_infimo`): si `g` es despreciable frente a toda una familia numerable, hay `h`
   estrictamente entre `g` y la familia. La prueba es la misma diagonal, con mínimos en vez de sumas.
4. **Un modelo de juguete** (`escalon`): una familia abstracta de «algoritmos» con costos `ℕ → ℕ`, construida con la
   media geométrica de `LandauDenso.lean`, donde la escalera existe de verdad (`juguete_baja`, `juguete_sin_optimo`,
   `juguete_sin_piso`). **Es un modelo de juguete, no el teorema de Blum**: los costos no salen de ningún programa.
5. **Controles.** La función constante `0` tiene un programa **exactamente óptimo** (`Code.zero`, con costo `n + 1`,
   `costo_cero` y `cero_optimo`), así que no tiene aceleración (`cero_sin_aceleracion`): la aceleración no vale
   siempre. Y la cláusula «hay un programa que computa `f`» no es decorativa: sin ella, el enunciado se cumple en vacío
   para una función diagonal que ningún código calcula (`nadie_computa_diagonal`, `clausula_vacia_en_diagonal`).

## La lectura

El «piso» de un problema, el costo del mejor algoritmo, puede no ser un punto. Si `f` tiene aceleración, los costos de
sus programas forman una **escalera sin último peldaño**: cada uno se puede bajar a algo despreciable frente a él. Y la
escalera tampoco converge a nada: cualquier función debajo de todos los peldaños tiene otra más arriba que sigue debajo
de todos. Es lo mismo que `sin_supremo` en Landau, visto desde abajo: el orden es denso y tiene huecos, y el piso de un
problema puede caer en uno.

## Lo que NO se prueba

* **La existencia de una `f` con aceleración no está en este archivo**: está en `BlumExiste.lean` (`blum`), probada sin
  hipótesis en la medida de Mathlib. Aquí se prueba qué obliga la aceleración *si* la hay, y la escalera del modelo de
  juguete. (Esta nota decía antes que la existencia pedía una cota del costo de `evaln` que no estaba en Mathlib;
  `BlumExiste.lean` la evitó midiendo ese costo con `Nat.rfind` en vez de acotarlo desde la sintaxis.)
* **Que SAT, o cualquier problema natural, tenga aceleración.** No se sabe. Las funciones de Blum son artificiales,
  construidas por diagonalización.
* **Nada sobre P contra NP.** La aceleración dice que un problema puede no tener un mejor algoritmo; no dice nada sobre
  si los problemas de NP tienen alguno polinomial.

## Fuente, de memoria

M. Blum, «A machine-independent theory of the complexity of recursive functions», *J. ACM*, 1967. No la leí en esta
sesión; las pruebas de aquí son propias.
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map
namespace Tiempo
namespace AceleracionBlum

/-! ## 1. La medida de Blum sobre `Nat.Partrec.Code` -/

/-- Si `c` termina en `k` pasos, termina en cualquier cota mayor. -/
theorem isSome_mono {k k' : ℕ} {c : Code} {n : ℕ} (hk : k ≤ k') (h : (evaln k c n).isSome) :
    (evaln k' c n).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  exact Option.isSome_iff_exists.2 ⟨x, evaln_mono hk hx⟩

/-- `eval c n` está definido exactamente cuando alguna evaluación acotada termina. -/
theorem dom_iff_exists (c : Code) (n : ℕ) : (eval c n).Dom ↔ ∃ k, (evaln k c n).isSome := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := evaln_complete.1 (Part.get_mem h)
    exact ⟨k, Option.isSome_iff_exists.2 ⟨_, hk⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
    exact Part.dom_iff_mem.2 ⟨x, evaln_sound hx⟩

open Classical in
/-- **El costo de Blum**: el menor `k` con `evaln k c n ≠ none`, o `⊤` si `c` no termina en `n`. -/
noncomputable def pasos (c : Code) (n : ℕ) : ℕ∞ :=
  if h : ∃ k, (evaln k c n).isSome then (Nat.find h : ℕ∞) else ⊤

/-- **Primer axioma de Blum**: el costo es finito exactamente cuando el programa está definido. -/
theorem pasos_lt_top_iff (c : Code) (n : ℕ) : pasos c n < ⊤ ↔ (eval c n).Dom := by
  rw [dom_iff_exists]
  unfold pasos
  split_ifs with h
  · simp only [ENat.natCast_lt_top, true_iff]; exact h
  · simp only [lt_self_iff_false, false_iff]; exact h

/-- **Segundo axioma de Blum, la forma**: `pasos c n ≤ k` es «la evaluación acotada por `k` termina». -/
theorem pasos_le_iff (c : Code) (n k : ℕ) : pasos c n ≤ k ↔ (evaln k c n).isSome := by
  unfold pasos
  split_ifs with h
  · rw [ENat.natCast_le_natCast]
    exact ⟨fun hle => isSome_mono hle (Nat.find_spec h), fun hk => Nat.find_min' h hk⟩
  · simp only [top_le_iff, ENat.natCast_ne_top, false_iff]
    exact fun hk => h ⟨k, hk⟩

/-- **Segundo axioma de Blum, decidible.** -/
instance (c : Code) (n k : ℕ) : Decidable (pasos c n ≤ k) :=
  decidable_of_iff _ (pasos_le_iff c n k).symm

/-- **Segundo axioma de Blum, computable**: `pasos c n ≤ k` es un predicado primitivo recursivo en `((k, c), n)`. -/
theorem primrec_pasos_le : PrimrecPred fun p : (ℕ × Code) × ℕ => pasos p.1.2 p.2 ≤ p.1.1 := by
  refine ⟨fun p => inferInstance, ?_⟩
  refine (Primrec.option_isSome.comp primrec_evaln).of_eq fun p => ?_
  cases hb : (evaln p.1.1 p.1.2 p.2).isSome <;> simp [hb, pasos_le_iff]

/-- **Ningún programa cuesta menos que leer la entrada**: `evaln k c n` exige `n < k`. -/
theorem pasos_gt (c : Code) (n : ℕ) : (n : ℕ∞) < pasos c n := by
  refine lt_of_not_ge fun hle => ?_
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((pasos_le_iff c n n).1 hle)
  exact lt_irrefl n (evaln_bound hx)

/-! ## Programas totales y su costo en `ℕ` -/

/-- **`c` computa la función total `f`.** -/
def Computa (c : Code) (f : ℕ → ℕ) : Prop := ∀ n, eval c n = Part.some (f n)

/-- El costo en `ℕ`; para un programa total es `pasos` (`pasos_costo`). -/
noncomputable def costo (c : Code) (n : ℕ) : ℕ := (pasos c n).toNat

theorem pasos_costo {c : Code} {f : ℕ → ℕ} (h : Computa c f) (n : ℕ) : pasos c n = costo c n := by
  have hd : (eval c n).Dom := by rw [h n]; trivial
  exact (ENat.natCast_toNat (ne_of_lt ((pasos_lt_top_iff c n).2 hd))).symm

theorem costo_le_iff {c : Code} {f : ℕ → ℕ} (h : Computa c f) (n k : ℕ) :
    costo c n ≤ k ↔ (evaln k c n).isSome := by
  rw [← pasos_le_iff, pasos_costo h, ENat.natCast_le_natCast]

theorem costo_gt {c : Code} {f : ℕ → ℕ} (h : Computa c f) (n : ℕ) : n < costo c n := by
  have := pasos_gt c n
  rw [pasos_costo h] at this
  exact_mod_cast this

/-! ## 2. Lo que obliga la aceleración -/

/-- «Para casi todo `n`»: desde algún punto. -/
def CasiTodo (P : ℕ → Prop) : Prop := ∃ N, ∀ n ≥ N, P n

/-- **El enunciado de Blum para `f`**: `f` es computable, y todo programa de `f` tiene otro, también de `f`, con
`r(n, costo j n) ≤ costo i n` para casi todo `n`. -/
def TieneAceleracion (r : ℕ → ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  (∃ i, Computa i f) ∧
    ∀ i, Computa i f → ∃ j, Computa j f ∧ CasiTodo fun n => r n (costo j n) ≤ costo i n

/-- **Lo despreciable y lo acotado no se juntan**: si `f ∈ o g` y `g = O(f)`, `f` es `0` desde algún punto. -/
theorem o_y_O {f g : ℕ → ℕ} (h1 : f ∈ o g) (h2 : EsO g f) : ∃ N, ∀ n ≥ N, f n = 0 := by
  obtain ⟨C, N₁, h2⟩ := h2
  obtain ⟨N₂, h1⟩ := h1 (C + 1)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have a := h1 n (le_of_max_le_right hn)
  have b := h2 n (le_of_max_le_left hn)
  rw [add_mul, one_mul] at a
  omega

/-- **Con `r(n, x) ≥ (n+1)·x`, cada programa tiene otro despreciable frente a él.** -/
theorem acelera_o {r : ℕ → ℕ → ℕ} {f : ℕ → ℕ} (hr : ∀ n x, (n + 1) * x ≤ r n x)
    (h : TieneAceleracion r f) {i : Code} (hi : Computa i f) :
    ∃ j, Computa j f ∧ costo j ∈ o (costo i) := by
  obtain ⟨j, hj, N, hN⟩ := h.2 i hi
  refine ⟨j, hj, fun c => ⟨max N c, fun n hn => ?_⟩⟩
  calc c * costo j n ≤ (n + 1) * costo j n :=
        Nat.mul_le_mul_right _ (by have := le_of_max_le_right hn; omega)
    _ ≤ r n (costo j n) := hr _ _
    _ ≤ costo i n := hN n (le_of_max_le_left hn)

/-- **Ningún programa es óptimo**, ni siquiera salvo una constante: no hay `i` con `costo i = O(costo j)` para todo
programa `j` de `f`. -/
theorem sin_optimo {r : ℕ → ℕ → ℕ} {f : ℕ → ℕ} (hr : ∀ n x, (n + 1) * x ≤ r n x)
    (h : TieneAceleracion r f) : ¬ ∃ i, Computa i f ∧ ∀ j, Computa j f → EsO (costo i) (costo j) := by
  rintro ⟨i, hi, hopt⟩
  obtain ⟨j, hj, ho⟩ := acelera_o hr h hi
  obtain ⟨N, hN⟩ := o_y_O ho (hopt j hj)
  have a := costo_gt hj N
  have b := hN N le_rfl
  omega

/-- **La escalera**: una sucesión infinita de programas de `f`, cada uno despreciable frente al anterior. -/
theorem escalera_de_aceleracion {r : ℕ → ℕ → ℕ} {f : ℕ → ℕ} (hr : ∀ n x, (n + 1) * x ≤ r n x)
    (h : TieneAceleracion r f) :
    ∃ s : ℕ → Code, (∀ k, Computa (s k) f) ∧ ∀ k, costo (s (k + 1)) ∈ o (costo (s k)) := by
  obtain ⟨i₀, hi₀⟩ := h.1
  have paso : ∀ i : {c // Computa c f}, ∃ j : {c // Computa c f}, costo j.1 ∈ o (costo i.1) := fun i =>
    let ⟨j, hj, ho⟩ := acelera_o hr h i.2
    ⟨⟨j, hj⟩, ho⟩
  choose F hF using paso
  let s : ℕ → {c // Computa c f} := fun k => F^[k] ⟨i₀, hi₀⟩
  refine ⟨fun k => (s k).1, fun k => (s k).2, fun k => ?_⟩
  simp only [s, Function.iterate_succ_apply']
  exact hF _

/-! ## 3. El espejo de `sin_supremo` -/

/-- El mínimo de los primeros `k + 1` miembros de la familia. -/
def minimo (t : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => t 0 n
  | k + 1, n => min (minimo t k n) (t (k + 1) n)

theorem minimo_le (t : ℕ → ℕ → ℕ) {j k : ℕ} (h : j ≤ k) (n : ℕ) : minimo t k n ≤ t j n := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact le_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · exact (min_le_left _ _).trans (ih (by omega))
    · obtain rfl : j = k + 1 := by omega
      exact min_le_right _ _

theorem o_minimo (t : ℕ → ℕ → ℕ) {g : ℕ → ℕ} (hg : ∀ k, g ∈ o (t k)) (k : ℕ) : g ∈ o (minimo t k) := by
  induction k with
  | zero => exact hg 0
  | succ k ih =>
    intro c
    obtain ⟨N₁, h₁⟩ := ih c
    obtain ⟨N₂, h₂⟩ := hg (k + 1) c
    exact ⟨max N₁ N₂, fun n hn => le_min (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))⟩

/-- **Sin ínfimo**: si `g` es despreciable frente a toda la familia, hay `h` estrictamente entre `g` y la familia.
Vale para **cualquier** familia numerable; es el espejo de `sin_supremo`, con la misma diagonal. -/
theorem sin_infimo (t : ℕ → ℕ → ℕ) {g : ℕ → ℕ} (hg : ∀ k, g ∈ o (t k)) :
    ∃ h, g ∈ o h ∧ ∀ k, h ∈ o (t k) := by
  classical
  have hN : ∀ k, ∃ N, ∀ n ≥ N, (k + 1) * (k + 1) * g n ≤ minimo t k n :=
    fun k => o_minimo t hg k ((k + 1) * (k + 1))
  choose N hN using hN
  let P : ℕ → ℕ → Prop := fun n k => ∀ j ≤ k, N j ≤ n
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  have hκP : ∀ n, N 0 ≤ n → P n (κ n) := fun n hn =>
    Nat.findGreatest_spec (P := P n) (Nat.zero_le n) (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact hn)
  have hκ : ∀ c, ∃ M, ∀ n ≥ M, c ≤ κ n := fun c => by
    refine ⟨c + ∑ j ∈ Finset.range (c + 1), N j, fun n hn => ?_⟩
    refine Nat.le_findGreatest (P := P n) (by omega) (fun j hj => ?_)
    have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (show j < c + 1 by omega))
    omega
  let H : ℕ → ℕ := fun n => minimo t (κ n) n / (κ n + 1)
  refine ⟨H, fun c => ?_, fun k c => ?_⟩
  · -- `g` es despreciable frente a `H`: `c · g · (κ+1) ≤ (κ+1)² · g ≤ mínimo` cuando `κ n ≥ c`.
    obtain ⟨M, hM⟩ := hκ c
    refine ⟨max M (N 0), fun n hn => ?_⟩
    have hc := hM n (le_of_max_le_left hn)
    have hP := hκP n (le_of_max_le_right hn)
    have hb := hN (κ n) n (hP (κ n) le_rfl)
    change c * g n ≤ minimo t (κ n) n / (κ n + 1)
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc c * g n * (κ n + 1) ≤ (κ n + 1) * (κ n + 1) * g n := by
          have : c * g n ≤ (κ n + 1) * g n := Nat.mul_le_mul_right _ (by omega)
          calc c * g n * (κ n + 1) ≤ (κ n + 1) * g n * (κ n + 1) := Nat.mul_le_mul_right _ this
            _ = (κ n + 1) * (κ n + 1) * g n := by ring
      _ ≤ minimo t (κ n) n := hb
  · -- `H` es despreciable frente a `t k`: cuando `κ n ≥ k, c`.
    obtain ⟨M, hM⟩ := hκ (k + c)
    refine ⟨M, fun n hn => ?_⟩
    have hk := hM n hn
    calc c * H n ≤ (κ n + 1) * (minimo t (κ n) n / (κ n + 1)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ minimo t (κ n) n := Nat.mul_div_le _ _
      _ ≤ t k n := minimo_le t (by omega) n

/-- **La escalera de una función con aceleración no tiene piso**: cualquier `g` despreciable frente a todos los
peldaños tiene otra `h`, más arriba, que sigue despreciable frente a todos. -/
theorem escalera_sin_piso {r : ℕ → ℕ → ℕ} {f : ℕ → ℕ} (hr : ∀ n x, (n + 1) * x ≤ r n x)
    (h : TieneAceleracion r f) :
    ∃ s : ℕ → Code, (∀ k, Computa (s k) f) ∧ (∀ k, costo (s (k + 1)) ∈ o (costo (s k))) ∧
      ∀ g, (∀ k, g ∈ o (costo (s k))) → ∃ h, g ∈ o h ∧ ∀ k, h ∈ o (costo (s k)) := by
  obtain ⟨s, hs, ho⟩ := escalera_de_aceleracion hr h
  exact ⟨s, hs, ho, fun g hg => sin_infimo _ hg⟩

/-- La cota inferior trivial, `n + 1`, está debajo de toda escalera: la hipótesis de `escalera_sin_piso` no es
vacía. -/
theorem lineal_bajo_escalera {f : ℕ → ℕ} {s : ℕ → Code} (hs : ∀ k, Computa (s k) f)
    (ho : ∀ k, costo (s (k + 1)) ∈ o (costo (s k))) (k : ℕ) : (fun n => n + 1) ∈ o (costo (s k)) :=
  o_abajo (ho k) fun n => costo_gt (hs (k + 1)) n

/-! ## 4. El modelo de juguete -/

/-- El piso del juguete. -/
def pisoJ (n : ℕ) : ℕ := n + 1

/-- El techo del juguete. -/
def techoJ (n : ℕ) : ℕ := (n + 1) * 2 ^ n

/-- **Los costos de los «algoritmos» del juguete**: se empieza en el techo y cada peldaño es la media geométrica entre
el piso y el peldaño anterior. Es un modelo de juguete: los algoritmos son los índices `k`, no programas. -/
def escalon : ℕ → ℕ → ℕ
  | 0 => techoJ
  | k + 1 => media pisoJ (escalon k)

theorem piso_o_techo : pisoJ ∈ o techoJ := fun c => by
  refine ⟨c, fun n hn => ?_⟩
  have : c ≤ 2 ^ n := (Nat.lt_two_pow_self.trans_le' hn).le
  calc c * pisoJ n ≤ 2 ^ n * (n + 1) := Nat.mul_le_mul_right _ this
    _ = techoJ n := by rw [techoJ, mul_comm]

theorem piso_o_escalon (k : ℕ) : pisoJ ∈ o (escalon k) := by
  induction k with
  | zero => exact piso_o_techo
  | succ k ih => exact (media_entre ih).1

/-- **Cada peldaño del juguete es despreciable frente al anterior.** -/
theorem juguete_baja (k : ℕ) : escalon (k + 1) ∈ o (escalon k) := (media_entre (piso_o_escalon k)).2

/-- **En el juguete no hay algoritmo óptimo**: ningún peldaño es `O` de todos los demás. -/
theorem juguete_sin_optimo : ¬ ∃ k, ∀ j, EsO (escalon k) (escalon j) := by
  rintro ⟨k, hk⟩
  obtain ⟨N, hN⟩ := o_y_O (juguete_baja k) (hk (k + 1))
  obtain ⟨M, hM⟩ := piso_o_escalon (k + 1) 1
  have a := hN (max N M) (le_max_left _ _)
  have b := hM (max N M) (le_max_right _ _)
  simp only [pisoJ, one_mul] at b
  omega

/-- **Y en el juguete el piso no es un punto**: debajo de la escalera, cualquier cota se puede subir. -/
theorem juguete_sin_piso {g : ℕ → ℕ} (hg : ∀ k, g ∈ o (escalon k)) :
    ∃ h, g ∈ o h ∧ ∀ k, h ∈ o (escalon k) :=
  sin_infimo escalon hg

/-! ## 5. Controles -/

/-- **El problema trivial tiene programa**: `Code.zero` computa la constante `0`. -/
theorem computa_cero : Computa Code.zero (fun _ => 0) := fun n => by simp [eval]; rfl

theorem evaln_cero (n : ℕ) : evaln (n + 1) Code.zero n = some 0 := by simp [evaln]

/-- **El costo exacto de `Code.zero`** es `n + 1`, el mínimo posible (`costo_gt`). -/
theorem costo_cero (n : ℕ) : costo Code.zero n = n + 1 := by
  have h1 : costo Code.zero n ≤ n + 1 :=
    (costo_le_iff computa_cero n (n + 1)).2 (by rw [evaln_cero]; rfl)
  have h2 := costo_gt computa_cero n
  omega

/-- **La constante tiene un programa óptimo**, no solo casi óptimo: `Code.zero` cuesta a lo sumo lo que cualquier otro
programa de la constante, en cada entrada. -/
theorem cero_optimo {j : Code} (hj : Computa j (fun _ => 0)) (n : ℕ) : costo Code.zero n ≤ costo j n := by
  rw [costo_cero]; exact costo_gt hj n

/-- **La aceleración no vale siempre**: con cualquier `r` que agrande estrictamente, la constante no la tiene. -/
theorem cero_sin_aceleracion {r : ℕ → ℕ → ℕ} (hr : ∀ n x, 0 < n → n < x → x < r n x) :
    ¬ TieneAceleracion r (fun _ => 0) := by
  rintro ⟨_, h⟩
  obtain ⟨j, hj, N, hN⟩ := h Code.zero computa_cero
  have a : r (N + 1) (costo j (N + 1)) ≤ costo Code.zero (N + 1) := hN (N + 1) (by omega)
  rw [costo_cero] at a
  have b := costo_gt hj (N + 1)
  have c := hr (N + 1) (costo j (N + 1)) (by omega) b
  omega

/-- La `r` de los teoremas de arriba, `(n+1)·x`, cumple la hipótesis de `cero_sin_aceleracion`. -/
example : ∀ n x, 0 < n → n < x → x < (n + 1) * x := fun n x hn hx => by nlinarith

open Classical in
/-- **Una función que ningún código calcula**: la diagonal contra `eval`. -/
noncomputable def diagonal (n : ℕ) : ℕ :=
  if eval (Denumerable.ofNat Code n) n = Part.some 0 then 1 else 0

theorem nadie_computa_diagonal (c : Code) : ¬ Computa c diagonal := by
  intro h
  have e := h (Encodable.encode c)
  simp only [diagonal, Denumerable.ofNat_encode] at e
  split_ifs at e with h0 <;> rw [Denumerable.ofNat_encode] at h0
  · rw [h0] at e
    exact absurd (Part.some_injective e) (by decide)
  · exact h0 e

/-- **La cláusula de existencia no es decorativa**: sin ella, la segunda mitad del enunciado de Blum se cumple en vacío
para `diagonal`, con cualquier `r`. -/
theorem clausula_vacia_en_diagonal (r : ℕ → ℕ → ℕ) :
    ∀ i, Computa i diagonal → ∃ j, Computa j diagonal ∧ CasiTodo fun n => r n (costo j n) ≤ costo i n :=
  fun i hi => absurd hi (nadie_computa_diagonal i)

/-- Con ella, `diagonal` no tiene aceleración. -/
theorem diagonal_sin_aceleracion (r : ℕ → ℕ → ℕ) : ¬ TieneAceleracion r diagonal :=
  fun ⟨⟨i, hi⟩, _⟩ => nadie_computa_diagonal i hi

end AceleracionBlum
end Tiempo
end Sagitta.Map
