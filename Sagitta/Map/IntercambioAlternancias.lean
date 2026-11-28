import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# El intercambio de alternancias: anidar el algoritmo supuesto, como juego de exponentes

La idea de José: **suponé** que hay un algoritmo rápido para SAT, usalo **anidado** dentro de sí mismo y mirá si la
composición choca contra algo que se sabe. En la literatura eso es el método de intercambio de alternancias
(*alternation trading*): Lipton–Viglas (SAT ∉ DTISP(n^{√2−ε}, n^{o(1)})), Fortnow–van Melkebeek (exponente φ ≈ 1,618)
y Williams (2cos(π/7) ≈ 1,8019); Buss y Williams mostraron que el método no pasa de ese último número.

## Qué se prueba

El **juego abstracto, condicionado a las reglas.** Las clases son familias de conjuntos indexadas por exponentes
reales (`MundoClases`): `DTISP a` es DTISP(n^a, n^{o(1)}), `Sigma k a` es Σ_k-TIME(n^a), `Pi k a` es Π_k-TIME(n^a),
`NTIME a = Sigma 1 a` y `coNTIME a = Pi 1 a`. No hay máquinas: las reglas del método son **hipótesis explícitas**
(`ReglasLV`), y el supuesto sobre SAT es `SupuestoSAT M c`: NTIME(n) ⊆ DTISP(n^c, n^{o(1)}).

1. **Lipton–Viglas** (`lipton_viglas_juego`): con `c < √2`, las reglas y el supuesto se contradicen. La cadena es
   NTIME(n²) ⊆ DTISP(n^{2c}) (supuesto rellenado) ⊆ Π₂(n^{c+ε}) (acelerar, sobre el complemento) ⊆ coNTIME(n^{(c+ε)c})
   (quitar una alternancia con el supuesto), y la jerarquía prohíbe NTIME(n²) ⊆ coNTIME(n^{a'}) con `a' < 2`.
   Cada nivel que se quita compone el supuesto una vez y multiplica el exponente por `c` (`quitar_iterado`).
2. **El umbral √2 es exacto para estas reglas** (`umbral_lipton_viglas`): con `c ≥ √2` hay un **modelo**
   (`modeloUmbral`), una asignación de costos a lenguajes que cumple **todas** las reglas y el supuesto. Como el modelo
   las cumple todas, ninguna prueba que use solo estas reglas, en cualquier orden y con cualquier cantidad de pasos y
   de niveles `k`, llega a una contradicción. Lo que cubre: exactamente las reglas de `ReglasLV`.
3. **Fortnow–van Melkebeek, φ** (`fortnow_van_melkebeek_juego`, `umbral_fortnow_van_melkebeek`): con una regla de
   aceleración más fina, que lleva la cuenta del **largo de la entrada** de cada fase (`ReglasFvM`), el umbral sube a
   la razón áurea, y también es exacto (modelo `modeloFvM` con `c ≥ φ`). La prueba es la de anidar **recursivamente**:
   si DTISP(n^a) ⊆ NTIME(n^{d·a}), entonces DTISP(n^a) ⊆ NTIME(n^{f(d)·a}) con `f(d) = c·d/(1+d)` (`fvm_paso`); la
   sucesión `d₀ = 1`, `d_{k+1} = f(d_k)` baja hacia `c − 1` (`fvmSucesion_cerca`) y la contradicción llega cuando
   `c·d_k < 1`, que pasa en algún `k` si y solo si `c(c − 1) < 1`, o sea `c < φ`.
4. **Los números** (`orden_de_los_umbrales`): √2 < φ < 2cos(π/7) < 2.

## La lectura, en el lenguaje del proyecto

* **Es la idea de José de anidar el algoritmo supuesto.** El supuesto se usa dos veces por vuelta: una para pasar de
  no determinista a determinista con poca memoria (`rellenar`), y otra para **quitar una alternancia** (`quitar`):
  la parte «para todo» de un Σ₂ es un coNTIME, y el supuesto la vuelve determinista. Por eso cada nivel **compone** el
  supuesto y **multiplica** el exponente por `c`. La contradicción aparece si lo que se gana al acelerar (dividir el
  exponente entre 2) paga lo que cuestan las dos composiciones (multiplicar por `c²`): `c²/2 < 1`.
* **Acelerar exige memoria chica.** Acelerar (`acelerar`) es adivinar √t configuraciones intermedias y que el
  adversario escoja un tramo para verificar. Adivinar una configuración cuesta **su largo**: es la escala logarítmica
  (`EscalaLog.codificar_log`: escribir uno de `m` casos cuesta `⌈log m⌉` símbolos), y con memoria `s` hay `2^s`
  configuraciones, o sea que adivinar una cuesta `s`. Con `s = n^{o(1)}` adivinar √t de ellas cuesta `√t · n^{o(1)}`,
  y la aceleración se gana; con memoria `n^b` cuesta `√t · n^b`, y la ganancia se esfuma cuando `n^b` se come el
  ahorro. Es el mismo umbral del bombeo: una configuración es barata de escribir solo mientras la memoria es chica.
* **Por eso el método se detiene con memoria polinomial.** Con memoria `n^b`, `b > 0` fijo, acelerar un cómputo de
  tiempo `n^a` cuesta `n^{a/2 + b}`: la ganancia se acaba cuando `b ≥ a/2`, y con memoria lineal (`b = 1`) ningún
  algoritmo de tiempo `n^c` con `c ≤ 2` se deja acelerar, que es justo el rango donde viven los umbrales √2 y φ.
  En el juego, eso es que la regla está enunciada solo para `DTISP`, no para `DTIME`: si se la enuncia para tiempo
  determinista sin cota de memoria, la prueba abstracta pasa igual (el juego no ve la memoria; es el mutante M4, ver
  las notas del proyecto) y daría NTIME(n) ⊄ DTIME(n^{1,41}), que nadie sabe probar. El juego no distingue; distingue la regla, y
  la regla es una hipótesis.

## Lo que NO se prueba

* **Las reglas sobre máquinas reales.** `acelerar`, `quitar`, `rellenar`, la jerarquía y las reglas finas de
  `ReglasFvM` son hipótesis. cslib-frontier tiene versiones parciales sobre máquinas (`Cslib.Complexity.TISP`,
  `TISP_subset_SigmaTwoTIME`, `SigmaTwoTIME_subset_NTIME`), con una aceleración más débil que la de libro
  (`√t · s` en vez de `√(t·s)`) y solo para Σ₂ con exponentes naturales; ver el mapa al final.
* **Que SAT no esté en DTISP(n^{√2−ε}, n^{o(1)}).** Para eso falta además la reducción casi lineal de NTIME(n) a SAT
  (Cook–Levin con `n · polylog n`) y las reglas sobre máquinas.
* **Nada con memoria polinomial.** Ver arriba.
* **Nada sobre P contra NP.** Los dos umbrales son para algoritmos con memoria `n^{o(1)}`; un algoritmo de tiempo
  `n^{1000}` con memoria `n` no lo toca nada de aquí.
* **El techo de Buss–Williams** (el método no pasa de 2cos(π/7) ≈ 1,8019) **no** está enunciado como teorema: haría
  falta formalizar el sistema de pruebas de Williams (sucesiones de expresiones de clases con cuantificadores, sus
  largos de entrada y la programación lineal). Aquí solo se prueba que los dos umbrales exactos de este archivo, √2 y
  φ, quedan por debajo de ese techo (`orden_de_los_umbrales`), como debe ser.

## Fuentes

* L. Fortnow, R. Lipton, D. van Melkebeek y A. Viglas, «Time-space lower bounds for satisfiability», *J. ACM*
  52(6):835–865, 2005, doi:10.1145/1101821.1101822 (`fortnow2005time`).
* R. Williams, «Alternation-trading proofs, linear programming, and lower bounds», *ACM TOCT* 5(2):1–49, 2013,
  doi:10.1145/2493246.2493249 (`williams2013alternation`).
* S. R. Buss y R. Williams, «Limits on alternation-trading proofs for time-space lower bounds», CCC 2012, 181–191,
  doi:10.1109/CCC.2012.30 (`buss2012limits`).
* R. Lipton y A. Viglas, «On the complexity of SAT», FOCS 1999.

Los datos bibliográficos son los de las publicaciones citadas; el contenido de las pruebas, de memoria: las reglas y
las dos recurrencias se reconstruyeron aquí y se comprobaron en Lean como aritmética de exponentes.
-/

namespace Sagitta.Map.Tiempo.IntercambioAlternancias

open Real

/-! ## 1. Las clases como familias indexadas por exponentes -/

/-- **Un mundo de clases.** Un tipo de lenguajes, el complemento y cuatro familias indexadas por exponentes reales:
`DTISP a` es DTISP(n^a, n^{o(1)}), `Sigma k a` es Σ_k-TIME(n^a) y `Pi k a` es Π_k-TIME(n^a). No dice nada de
máquinas: lo que valga entre las clases lo dicen las reglas. -/
structure MundoClases where
  /-- Los lenguajes. -/
  Leng : Type
  /-- El complemento. -/
  co : Leng → Leng
  /-- DTISP(n^a, n^{o(1)}): tiempo determinista `n^a` con memoria `n^{o(1)}`. -/
  DTISP : ℝ → Set Leng
  /-- Σ_k-TIME(n^a). -/
  Sigma : ℕ → ℝ → Set Leng
  /-- Π_k-TIME(n^a). -/
  Pi : ℕ → ℝ → Set Leng

namespace MundoClases

variable (M : MundoClases)

/-- NTIME(n^a) = Σ₁-TIME(n^a). -/
def NTIME (a : ℝ) : Set M.Leng := M.Sigma 1 a

/-- coNTIME(n^a) = Π₁-TIME(n^a). -/
def coNTIME (a : ℝ) : Set M.Leng := M.Pi 1 a

end MundoClases

/-- **El supuesto sobre SAT**, en la forma que usa el método: NTIME(n) ⊆ DTISP(n^c, n^{o(1)}). Con la reducción casi
lineal de Cook–Levin, eso es lo que da un algoritmo para SAT de tiempo `n^c` y memoria `n^{o(1)}`. -/
def SupuestoSAT (M : MundoClases) (c : ℝ) : Prop := M.NTIME 1 ⊆ M.DTISP c

/-- **Las reglas de Lipton–Viglas, como hipótesis.**

* `pi_iff`, `co_co`, `dtisp_co`: Π_k es el complemento de Σ_k; DTISP es cerrada bajo complemento.
* `dtisp_mono`, `sigma_mono`: más tiempo no estorba.
* `dtisp_ntime`, `sube`: lo determinista es no determinista; un cuantificador más no estorba.
* `acelerar`: DTISP(n^a, n^{o(1)}) ⊆ Σ₂-TIME(n^{a/2+ε}) para `a ≥ 2` y todo `ε > 0` (adivinar los puntos medios;
  el `ε` paga las `n^{o(1)}` de cada configuración y `a ≥ 2` que el Σ₂ alcance a leer la entrada).
* `rellenar`: el supuesto con relleno, NTIME(n) ⊆ DTISP(n^c) implica NTIME(n^a) ⊆ DTISP(n^{ac}) para `a ≥ 1`.
* `quitar`: con el supuesto, Σ_k-TIME(n^b) ⊆ Σ_{k−1}-TIME(n^{bc}) para `k ≥ 2` y `b ≥ 1` (la última fase
  «para todo» es un coNTIME sobre una entrada de largo `n^b`, y el supuesto la vuelve determinista).
* `jerarquia`: NTIME(n^a) ⊄ coNTIME(n^{a'}) para `1 ≤ a` y `a' < a`. -/
structure ReglasLV (M : MundoClases) : Prop where
  pi_iff : ∀ k a L, L ∈ M.Pi k a ↔ M.co L ∈ M.Sigma k a
  co_co : ∀ L, M.co (M.co L) = L
  dtisp_co : ∀ a L, L ∈ M.DTISP a → M.co L ∈ M.DTISP a
  dtisp_mono : ∀ a b, a ≤ b → M.DTISP a ⊆ M.DTISP b
  sigma_mono : ∀ k a b, a ≤ b → M.Sigma k a ⊆ M.Sigma k b
  dtisp_ntime : ∀ a, M.DTISP a ⊆ M.NTIME a
  sube : ∀ k a, 1 ≤ k → M.Sigma k a ⊆ M.Sigma (k + 1) a ∩ M.Pi (k + 1) a
  acelerar : ∀ a ε, 2 ≤ a → 0 < ε → M.DTISP a ⊆ M.Sigma 2 (a / 2 + ε)
  rellenar : ∀ c, SupuestoSAT M c → ∀ a, 1 ≤ a → M.NTIME a ⊆ M.DTISP (a * c)
  quitar : ∀ c, SupuestoSAT M c → ∀ k b, 2 ≤ k → 1 ≤ b → M.Sigma k b ⊆ M.Sigma (k - 1) (b * c)
  jerarquia : ∀ a a', 1 ≤ a → a' < a → ¬ M.NTIME a ⊆ M.coNTIME a'

variable {M : MundoClases}

/-- Un algoritmo más lento sigue siendo un algoritmo: el supuesto es monótono en `c`. -/
theorem supuestoSAT_mono (R : ReglasLV M) {c c' : ℝ} (h : c ≤ c') (hs : SupuestoSAT M c) :
    SupuestoSAT M c' :=
  hs.trans (R.dtisp_mono _ _ h)

/-- Lo determinista con poca memoria está en coNTIME, porque DTISP es cerrada bajo complemento. -/
theorem dtisp_en_coNTIME_de (R : ReglasLV M) {e e' : ℝ} (h : M.DTISP e ⊆ M.NTIME e') :
    M.DTISP e ⊆ M.coNTIME e' :=
  fun L hL => (R.pi_iff 1 e' L).2 (h (R.dtisp_co _ _ hL))

/-- **Anidar: cada nivel multiplica el exponente por `c`.** Con el supuesto, Σ_{k+1}-TIME(n^b) ⊆ NTIME(n^{b·c^k}):
quitar `k` alternancias es componer el supuesto `k` veces. -/
theorem quitar_iterado (R : ReglasLV M) {c : ℝ} (hc : 1 ≤ c) (hs : SupuestoSAT M c) :
    ∀ k : ℕ, ∀ b : ℝ, 1 ≤ b → M.Sigma (k + 1) b ⊆ M.NTIME (b * c ^ k) := by
  intro k
  induction k with
  | zero => intro b _; simp [MundoClases.NTIME]
  | succ k ih =>
    intro b hb
    have h1 : M.Sigma (k + 1 + 1) b ⊆ M.Sigma (k + 1) (b * c) := by
      have := R.quitar c hs (k + 2) b (by omega) hb
      simpa using this
    have h2 := ih (b * c) (by nlinarith)
    refine h1.trans (h2.trans ?_)
    rw [show b * c * c ^ k = b * c ^ (k + 1) by ring]

/-! ## 2. Lipton–Viglas: con `c < √2` hay contradicción -/

/-- **Una vuelta del juego.** Con el supuesto y `c ≥ 1`: NTIME(n²) ⊆ coNTIME(n^{(c+ε)c}). Supuesto rellenado,
complemento, acelerar, quitar una alternancia. -/
theorem ntime_en_coNTIME_LV (R : ReglasLV M) {c : ℝ} (hc : 1 ≤ c) (hs : SupuestoSAT M c) {ε : ℝ}
    (hε : 0 < ε) : M.NTIME 2 ⊆ M.coNTIME ((c + ε) * c) := by
  intro L hL
  have h1 : L ∈ M.DTISP (2 * c) := R.rellenar c hs 2 (by norm_num) hL
  have h2 : M.co L ∈ M.DTISP (2 * c) := R.dtisp_co _ _ h1
  have h3 : M.co L ∈ M.Sigma 2 (2 * c / 2 + ε) := R.acelerar _ _ (by linarith) hε h2
  have h3' : M.co L ∈ M.Sigma 2 (c + ε) := by
    rwa [show 2 * c / 2 + ε = c + ε by ring] at h3
  have h4 : M.co L ∈ M.Sigma (2 - 1) ((c + ε) * c) := R.quitar c hs 2 _ le_rfl (by linarith) h3'
  exact (R.pi_iff 1 _ L).2 h4

/-- **Lipton–Viglas, en el juego.** Si `c < √2`, las reglas y el supuesto NTIME(n) ⊆ DTISP(n^c, n^{o(1)}) se
contradicen. -/
theorem lipton_viglas_juego (R : ReglasLV M) {c : ℝ} (hc : c < √2) (hs : SupuestoSAT M c) : False := by
  set c₁ := max c 1 with hc₁
  have hs1 : SupuestoSAT M c₁ := supuestoSAT_mono R (le_max_left _ _) hs
  have h1 : 1 ≤ c₁ := le_max_right _ _
  have hraiz : (1 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hlt : c₁ < √2 := max_lt hc hraiz
  have hsq : c₁ * c₁ < 2 := by
    have := (Real.lt_sqrt (by linarith)).1 hlt
    nlinarith
  set ε := (2 - c₁ * c₁) / (2 * c₁) with hε_def
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  have hεc : ε * c₁ = (2 - c₁ * c₁) / 2 := by
    rw [hε_def]; field_simp
  have hfin : (c₁ + ε) * c₁ < 2 := by
    have : (c₁ + ε) * c₁ = c₁ * c₁ + ε * c₁ := by ring
    rw [this, hεc]; linarith
  exact R.jerarquia 2 _ (by norm_num) hfin (ntime_en_coNTIME_LV R h1 hs1 hε)

/-! ## 3. El umbral es real: un modelo de las reglas con `c ≥ √2` -/

/-- El costo Σ_k de un lenguaje de costo no determinista `x` en el modelo: `x` en los niveles 0 y 1; en los niveles
`≥ 2`, lo mejor entre no usar la alternancia (`x`) y acelerar su versión determinista (`c·x/2`). -/
noncomputable def costoSigmaModelo (c : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | 1, x => x
  | _ + 2, x => min x (c * x / 2)

/-- **El modelo.** Los lenguajes son números `x > 0` (su exponente no determinista); el complemento es la identidad
(cada lenguaje cuesta lo mismo que su complemento); DTISP cuesta `c·x` (el supuesto, justo), y Σ_k cuesta
`costoSigmaModelo`. Es la asignación de exponentes en la que el supuesto se cumple con igualdad y acelerar se usa
todo lo posible. -/
def modeloUmbral (c : ℝ) : MundoClases where
  Leng := {x : ℝ // 0 < x}
  co := id
  DTISP a := {ℓ | c * ℓ.1 ≤ a}
  Sigma k a := {ℓ | costoSigmaModelo c k ℓ.1 ≤ a}
  Pi k a := {ℓ | costoSigmaModelo c k ℓ.1 ≤ a}

/-- En el modelo, el supuesto con `c'` obliga `c ≤ c'` (se mira en el lenguaje de costo 1). -/
theorem modeloUmbral_supuesto_le {c c' : ℝ} (hs : SupuestoSAT (modeloUmbral c) c') : c ≤ c' := by
  have h := hs (show (⟨1, one_pos⟩ : (modeloUmbral c).Leng) ∈ (modeloUmbral c).NTIME 1 from
    show costoSigmaModelo c 1 1 ≤ 1 from le_refl _)
  have h' : c * 1 ≤ c' := h
  linarith

/-- El modelo cumple el supuesto con su propio `c`. -/
theorem modeloUmbral_supuesto {c : ℝ} (hc : 0 ≤ c) : SupuestoSAT (modeloUmbral c) c := by
  intro ℓ (hℓ : ℓ.1 ≤ 1)
  show c * ℓ.1 ≤ c
  nlinarith

/-- **El modelo cumple todas las reglas cuando `c² ≥ 2`.** El único paso donde entra `c² ≥ 2` es `quitar` del nivel
2 al 1: si el costo Σ₂ vino de acelerar (`c·x/2 ≤ b`), entonces `x ≤ 2b/c ≤ b·c`. -/
theorem modeloUmbral_reglas {c : ℝ} (hc0 : 0 ≤ c) (hc : 2 ≤ c * c) : ReglasLV (modeloUmbral c) := by
  have hc1 : 1 ≤ c := by nlinarith
  refine
    { pi_iff := fun _ _ _ => Iff.rfl
      co_co := fun _ => rfl
      dtisp_co := fun _ _ h => h
      dtisp_mono := ?_
      sigma_mono := ?_
      dtisp_ntime := ?_
      sube := ?_
      acelerar := ?_
      rellenar := ?_
      quitar := ?_
      jerarquia := ?_ }
  · intro a b hab ℓ (hℓ : c * ℓ.1 ≤ a)
    exact (show c * ℓ.1 ≤ b by linarith)
  · intro k a b hab ℓ (hℓ : costoSigmaModelo c k ℓ.1 ≤ a)
    exact (show costoSigmaModelo c k ℓ.1 ≤ b by linarith)
  · intro a ℓ (hℓ : c * ℓ.1 ≤ a)
    have hpos := ℓ.2
    exact (show ℓ.1 ≤ a by nlinarith)
  · intro k a hk ℓ (hℓ : costoSigmaModelo c k ℓ.1 ≤ a)
    have h : costoSigmaModelo c (k + 1) ℓ.1 ≤ a := by
      match k, hk with
      | 1, _ => exact (min_le_left _ _).trans hℓ
      | m + 2, _ => exact hℓ
    exact ⟨h, h⟩
  · intro a ε ha hε ℓ (hℓ : c * ℓ.1 ≤ a)
    show min ℓ.1 (c * ℓ.1 / 2) ≤ a / 2 + ε
    have := min_le_right ℓ.1 (c * ℓ.1 / 2)
    linarith
  · intro c' hs a ha ℓ (hℓ : costoSigmaModelo c 1 ℓ.1 ≤ a)
    have hcc := modeloUmbral_supuesto_le hs
    have hℓ' : ℓ.1 ≤ a := hℓ
    have hpos := ℓ.2
    show c * ℓ.1 ≤ a * c'
    nlinarith
  · intro c' hs k b hk hb ℓ (hℓ : costoSigmaModelo c k ℓ.1 ≤ b)
    have hcc := modeloUmbral_supuesto_le hs
    have hpos := ℓ.2
    show costoSigmaModelo c (k - 1) ℓ.1 ≤ b * c'
    match k, hk with
    | 2, _ =>
      show ℓ.1 ≤ b * c'
      have hℓ' : min ℓ.1 (c * ℓ.1 / 2) ≤ b := hℓ
      rcases min_le_iff.1 hℓ' with h | h
      · nlinarith
      · -- `c·x ≤ 2b`, así que `2x ≤ c²x ≤ 2bc`
        have h2 : c * (c * ℓ.1) ≤ c * (2 * b) := mul_le_mul_of_nonneg_left (by linarith) hc0
        nlinarith
    | m + 3, _ =>
      show min ℓ.1 (c * ℓ.1 / 2) ≤ b * c'
      have hℓ' : min ℓ.1 (c * ℓ.1 / 2) ≤ b := hℓ
      nlinarith
  · intro a a' ha ha' h
    have hm := h (show (⟨a, by linarith⟩ : (modeloUmbral c).Leng) ∈ (modeloUmbral c).NTIME a from
      show costoSigmaModelo c 1 a ≤ a from le_refl _)
    have : a ≤ a' := hm
    linarith

/-- **El umbral de Lipton–Viglas es exacto para estas reglas.** Las reglas de `ReglasLV` y el supuesto con `c` se
contradicen en todo mundo **si y solo si** `c < √2`. La dirección «solo si» la da `modeloUmbral`: con `c ≥ √2`
ninguna combinación de las reglas, en cualquier orden y número de pasos, llega a la contradicción. -/
theorem umbral_lipton_viglas (c : ℝ) :
    (∀ M : MundoClases, ReglasLV M → SupuestoSAT M c → False) ↔ c < √2 := by
  constructor
  · intro h
    by_contra hc
    have hc := not_lt.1 hc
    have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
    have hc0 : 0 ≤ c := h0.trans hc
    have hcc : 2 ≤ c * c := by nlinarith
    exact h _ (modeloUmbral_reglas hc0 hcc) (modeloUmbral_supuesto hc0)
  · intro hc M R hs
    exact lipton_viglas_juego R hc hs

/-! ## 4. Fortnow–van Melkebeek: la aceleración fina y la razón áurea -/

open scoped goldenRatio

/-- **Las reglas finas de Fortnow–van Melkebeek, como hipótesis.** Llevan la cuenta del largo de la entrada de cada
fase. `EA x e` es ∃^{n^x} ∀^{log n} DTISP(n^e), donde la fase determinista lee la entrada y **dos** configuraciones
(largo `n + n^{o(1)}`); `EC x e` es lo mismo con un coNTIME(n^e) adentro; `ED x e` es ∃^{n^x} DTIME(n^e).

* `acelerar_fino`: DTISP(n^a) ⊆ ∃^{n^{x+η}} ∀^{log n} DTISP(n^{a−x}) (`n^x` tramos de `n^{a−x}` pasos).
* `interior`: si DTISP(n^e) ⊆ coNTIME(n^{e'}), se puede cambiar la fase de adentro (`e ≥ 1`).
* `quitar_fino`: con el supuesto, ∀^{log n} coNTIME(n^e) sobre una entrada de largo `n^x` se vuelve determinista
  de tiempo `n^{c·max(x,e)}`.
* `cerrar`: ∃^{n^x} DTIME(n^e) ⊆ NTIME(n^{max(x,e)}). -/
structure ReglasFvM (M : MundoClases) (EA EC ED : ℝ → ℝ → Set M.Leng) : Prop where
  acelerar_fino : ∀ a x η, 0 ≤ x → x ≤ a → 0 < η → M.DTISP a ⊆ EA (x + η) (a - x)
  interior : ∀ x e e', 1 ≤ e → M.DTISP e ⊆ M.coNTIME e' → EA x e ⊆ EC x e'
  quitar_fino : ∀ c, SupuestoSAT M c → ∀ x e, 0 ≤ x → 1 ≤ e → EC x e ⊆ ED x (c * max x e)
  cerrar : ∀ x e, ED x e ⊆ M.NTIME (max x e)

/-- «DTISP(n^a) ⊆ NTIME(n^{(d+ε)a}) para todo `ε > 0` y todo `a` grande»: lo que se sabe en cada vuelta. -/
def CotaDTISP (M : MundoClases) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ A : ℝ, ∀ a ≥ A, M.DTISP a ⊆ M.NTIME ((d + ε) * a)

/-- La vuelta cero: `d = 1`, lo determinista es no determinista. -/
theorem cotaDTISP_uno (R : ReglasLV M) : CotaDTISP M 1 := by
  intro ε hε
  refine ⟨0, fun a ha => (R.dtisp_ntime a).trans (R.sigma_mono 1 _ _ ?_)⟩
  nlinarith

/-- **Una vuelta de Fortnow–van Melkebeek: anidar el supuesto adentro de la aceleración.** Si
DTISP(n^a) ⊆ NTIME(n^{d·a}), entonces DTISP(n^a) ⊆ NTIME(n^{f(d)·a}) con `f(d) = c·d/(1+d)`. Se acelera en `n^x`
tramos, la fase de adentro (tiempo `n^{a−x}`) se pasa a coNTIME(n^{d(a−x)}) con lo que ya se sabe, el supuesto quita
la alternancia y se elige `x = d(a − x)` para equilibrar. -/
theorem fvm_paso (R : ReglasLV M) {EA EC ED : ℝ → ℝ → Set M.Leng} (F : ReglasFvM M EA EC ED) {c : ℝ}
    (hc : 1 ≤ c) (hs : SupuestoSAT M c) {d : ℝ} (hd : 0 ≤ d) (hS : CotaDTISP M d) :
    CotaDTISP M (c * d / (1 + d)) := by
  intro ε hε
  set δ := ε / (2 * c) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hcδ : c * δ = ε / 2 := by rw [hδ]; field_simp
  obtain ⟨A, hA⟩ := hS δ hδ0
  set d' := d + δ with hd'
  have hd'0 : 0 < d' := by linarith
  refine ⟨(1 + d') * max (max A 1) (1 / d'), fun a ha L hL => ?_⟩
  set t := a / (1 + d') with ht
  have h1d : 0 < 1 + d' := by linarith
  have hat : a = (1 + d') * t := by rw [ht]; field_simp
  have htmax : max (max A 1) (1 / d') ≤ t := by
    rw [ht, le_div_iff₀ h1d]; linarith
  have htA : A ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans htmax)
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans htmax)
  have htd : 1 / d' ≤ t := (le_max_right _ _).trans htmax
  have hx1 : 1 ≤ d' * t := by
    have := mul_le_mul_of_nonneg_left htd hd'0.le
    rwa [mul_one_div_cancel hd'0.ne'] at this
  set x := d' * t with hx
  set η := δ with hη
  have ha1 : 1 ≤ a := by rw [hat]; nlinarith
  have hax : a - x = t := by rw [hat, hx]; ring
  -- acelerar
  have h1 : L ∈ EA (x + η) (a - x) := F.acelerar_fino a x η (by linarith) (by linarith) hδ0 hL
  rw [hax] at h1
  -- la fase de adentro, con lo que ya se sabe
  have hin : M.DTISP t ⊆ M.coNTIME x := dtisp_en_coNTIME_de R (by simpa [hx, hd'] using hA t htA)
  have h2 : L ∈ EC (x + η) x := F.interior _ _ _ ht1 hin h1
  -- quitar la alternancia con el supuesto
  have h3 : L ∈ ED (x + η) (c * max (x + η) x) := F.quitar_fino c hs _ _ (by linarith) hx1 h2
  have h4 : L ∈ M.NTIME (max (x + η) (c * max (x + η) x)) := F.cerrar _ _ h3
  refine R.sigma_mono 1 _ _ ?_ h4
  -- la cuenta de exponentes
  have hm1 : max (x + η) x = x + η := max_eq_left (by linarith)
  rw [hm1]
  have hm2 : max (x + η) (c * (x + η)) = c * (x + η) := max_eq_right (by nlinarith)
  rw [hm2]
  have h1d0 : 0 < 1 + d := by linarith
  have key : c * d' ≤ (c * d / (1 + d) + ε / 2) * (1 + d') := by
    have e1 : c * d / (1 + d) * (1 + d) = c * d := by field_simp
    have e2 : c * d' * (1 + d) ≤ (c * d / (1 + d) + ε / 2) * (1 + d') * (1 + d) := by
      have : (c * d / (1 + d) + ε / 2) * (1 + d') * (1 + d) =
          c * d * (1 + d') + ε / 2 * (1 + d') * (1 + d) := by
        rw [add_mul, add_mul, mul_comm (c * d / (1 + d)) (1 + d'), mul_assoc, e1]; ring
      rw [this]
      have hδd : c * d' * (1 + d) = c * d * (1 + d') + c * δ := by rw [hd']; ring
      rw [hδd, hcδ]
      have h11 : 1 ≤ (1 + d') * (1 + d) := by nlinarith
      have := mul_le_mul_of_nonneg_left h11 (show 0 ≤ ε / 2 by linarith)
      nlinarith
    exact le_of_mul_le_mul_right e2 h1d0
  have hct : c * x ≤ (c * d / (1 + d) + ε / 2) * a := by
    rw [hx, hat]
    have ht0 : 0 ≤ t := by linarith
    nlinarith [mul_le_mul_of_nonneg_right key ht0]
  have hcη : c * η ≤ ε / 2 * a := by rw [hη, hcδ]; nlinarith
  nlinarith

/-- La sucesión de exponentes de Fortnow–van Melkebeek: `d₀ = 1`, `d_{k+1} = c·d_k/(1+d_k)`. -/
noncomputable def fvmSucesion (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => c * fvmSucesion c k / (1 + fvmSucesion c k)

/-- Cada término de la sucesión es una cota válida. -/
theorem cotaDTISP_fvmSucesion (R : ReglasLV M) {EA EC ED : ℝ → ℝ → Set M.Leng} (F : ReglasFvM M EA EC ED)
    {c : ℝ} (hc : 1 ≤ c) (hs : SupuestoSAT M c) :
    ∀ k, 0 ≤ fvmSucesion c k ∧ CotaDTISP M (fvmSucesion c k) := by
  intro k
  induction k with
  | zero => exact ⟨by simp [fvmSucesion], cotaDTISP_uno R⟩
  | succ k ih =>
    refine ⟨?_, fvm_paso R F hc hs ih.1 ih.2⟩
    show 0 ≤ c * fvmSucesion c k / (1 + fvmSucesion c k)
    have := ih.1
    positivity

/-- **La sucesión baja hacia `c − 1`, geométricamente.** Con `1 < c ≤ 2`:
`c − 1 ≤ d_k ≤ (c − 1) + (2 − c)/c^k`. -/
theorem fvmSucesion_cerca {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) (k : ℕ) :
    c - 1 ≤ fvmSucesion c k ∧ fvmSucesion c k - (c - 1) ≤ (2 - c) / c ^ k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show c - 1 ≤ 1
      linarith
    · show (1 : ℝ) - (c - 1) ≤ (2 - c) / c ^ 0
      rw [pow_zero, div_one]; linarith
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    set s := fvmSucesion c k with hs
    have hpos : 0 < 1 + s := by linarith
    have hrec : fvmSucesion c (k + 1) - (c - 1) = (s - (c - 1)) / (1 + s) := by
      show c * s / (1 + s) - (c - 1) = (s - (c - 1)) / (1 + s)
      field_simp; ring
    have hnn : 0 ≤ s - (c - 1) := by linarith
    refine ⟨?_, ?_⟩
    · have : 0 ≤ (s - (c - 1)) / (1 + s) := div_nonneg hnn hpos.le
      linarith
    · rw [hrec]
      have hcs : c ≤ 1 + s := by linarith
      have hck : 0 < c ^ k := pow_pos (by linarith) k
      calc (s - (c - 1)) / (1 + s) ≤ (s - (c - 1)) / c := div_le_div_of_nonneg_left hnn (by linarith) hcs
        _ ≤ (2 - c) / c ^ k / c := div_le_div_of_nonneg_right h2 (by linarith)
        _ = (2 - c) / c ^ (k + 1) := by rw [pow_succ, div_div]

/-- **El cierre**: una cota `d` con `c·d < 1` da la contradicción. NTIME(n^b) ⊆ DTISP(n^{bc}) ⊆ coNTIME(n^{(d+ε)bc})
y `(d+ε)c < 1`. -/
theorem fvm_cierre (R : ReglasLV M) {c : ℝ} (hc : 1 ≤ c) (hs : SupuestoSAT M c) {d : ℝ}
    (hS : CotaDTISP M d) (hcd : c * d < 1) : False := by
  set ε := (1 - c * d) / (2 * c) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hcε : c * ε = (1 - c * d) / 2 := by rw [hε]; field_simp
  obtain ⟨A, hA⟩ := hS ε hε0
  set b := max A 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hbA : A ≤ b * c := by
    have : A ≤ b := le_max_left _ _
    nlinarith
  have hsub : M.NTIME b ⊆ M.coNTIME ((d + ε) * (b * c)) := fun L hL =>
    dtisp_en_coNTIME_de R (hA (b * c) hbA) (R.rellenar c hs b hb1 hL)
  have hlt : (d + ε) * (b * c) < b := by
    have : (d + ε) * (b * c) = b * (c * d + c * ε) := by ring
    rw [this, hcε]
    have : c * d + (1 - c * d) / 2 < 1 := by linarith
    nlinarith
  exact R.jerarquia b _ hb1 hlt hsub

/-- **Fortnow–van Melkebeek, en el juego.** Si `c < φ`, las reglas de Lipton–Viglas, las reglas finas y el supuesto
se contradicen. -/
theorem fortnow_van_melkebeek_juego (R : ReglasLV M) {EA EC ED : ℝ → ℝ → Set M.Leng}
    (F : ReglasFvM M EA EC ED) {c : ℝ} (hc : c < φ) (hs : SupuestoSAT M c) : False := by
  have hφ := Real.goldenRatio_sq
  have hφ32 : (3 : ℝ) / 2 < φ := by
    have h5 : (2 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    show (3 : ℝ) / 2 < (1 + √5) / 2
    linarith
  set c₁ := max c (3 / 2) with hc₁
  have hs1 : SupuestoSAT M c₁ := supuestoSAT_mono R (le_max_left _ _) hs
  have h32 : 3 / 2 ≤ c₁ := le_max_right _ _
  have hlt : c₁ < φ := max_lt hc hφ32
  have hφ2 := Real.goldenRatio_lt_two
  have hc1 : 1 < c₁ := by linarith
  have hc2 : c₁ ≤ 2 := by linarith
  -- `c₁(c₁ − 1) < 1`, o sea `c₁ − 1 < 1/c₁`
  have hcuad : c₁ * c₁ < c₁ + 1 := by nlinarith
  set γ := 1 - c₁ * (c₁ - 1) with hγ
  have hγ0 : 0 < γ := by rw [hγ]; nlinarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((2 - c₁) * c₁ / γ) hc1
  obtain ⟨hlo, hhi⟩ := fvmSucesion_cerca hc1 hc2 k
  obtain ⟨hnn, hS⟩ := cotaDTISP_fvmSucesion R F hc1.le hs1 k
  refine fvm_cierre R hc1.le hs1 hS ?_
  have hck : 0 < c₁ ^ k := pow_pos (by linarith) k
  have hdiv : (2 - c₁) / c₁ ^ k * c₁ < γ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hck]
    rw [div_lt_iff₀ hγ0] at hk
    linarith
  have h3 : c₁ * (fvmSucesion c₁ k - (c₁ - 1)) < γ := by
    have := mul_le_mul_of_nonneg_left hhi (show 0 ≤ c₁ by linarith)
    linarith
  rw [hγ] at h3
  nlinarith

/-- **El modelo para las reglas finas, con `c ≥ φ`.** El mismo `modeloUmbral c` y, para las clases nuevas, los
costos `max(c·x, e)`, `c·max(x, e)` y `max(x, e)`. El paso donde entra `c ≥ φ` es `acelerar_fino`: si un lenguaje
de costo `ℓ ≤ a/c` no cabe en el tramo (`ℓ > a − x`), entonces `x > a − a/c` y `c·x ≥ ℓ` exactamente cuando
`c(c − 1) ≥ 1`. -/
def modeloFvM (c : ℝ) : (ℝ → ℝ → Set (modeloUmbral c).Leng) × (ℝ → ℝ → Set (modeloUmbral c).Leng) ×
    (ℝ → ℝ → Set (modeloUmbral c).Leng) :=
  (fun x e => {ℓ | ℓ.1 ≤ max (c * x) e},
   fun x e => {ℓ | ℓ.1 ≤ c * max x e},
   fun x e => {ℓ | ℓ.1 ≤ max x e})

theorem modeloFvM_reglas {c : ℝ} (hc : φ ≤ c) :
    ReglasFvM (modeloUmbral c) (modeloFvM c).1 (modeloFvM c).2.1 (modeloFvM c).2.2 := by
  have hφ := Real.goldenRatio_sq
  have hφ1 := Real.one_lt_goldenRatio
  have hc1 : 1 < c := by linarith
  have hcc : c + 1 ≤ c * c := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a x η hx hxa hη ℓ (hℓ : c * ℓ.1 ≤ a)
    show ℓ.1 ≤ max (c * (x + η)) (a - x)
    by_cases h : ℓ.1 ≤ a - x
    · exact le_max_of_le_right h
    · have h := not_le.1 h
      apply le_max_of_le_left
      have hpos := ℓ.2
      -- `c·a ≥ c²·ℓ ≥ (c+1)·ℓ`, así que `c(a − ℓ) ≥ ℓ`, y `x > a − ℓ`
      have h1 : (c + 1) * ℓ.1 ≤ c * a := by nlinarith
      nlinarith
  · intro x e e' he hin ℓ (hℓ : ℓ.1 ≤ max (c * x) e)
    show ℓ.1 ≤ c * max x e'
    have hpe : 0 < e / c := div_pos (by linarith) (by linarith)
    have hmem := hin (show (⟨e / c, hpe⟩ : (modeloUmbral c).Leng) ∈ (modeloUmbral c).DTISP e from
      show c * (e / c) ≤ e by rw [mul_div_cancel₀ _ (by linarith)])
    have he' : e / c ≤ e' := hmem
    have hce : e ≤ c * e' := by
      have := mul_le_mul_of_nonneg_left he' (show 0 ≤ c by linarith)
      rwa [mul_div_cancel₀ _ (by linarith)] at this
    rcases le_max_iff.1 hℓ with h | h
    · have := mul_le_mul_of_nonneg_left (le_max_left x e') (show 0 ≤ c by linarith)
      linarith
    · have := mul_le_mul_of_nonneg_left (le_max_right x e') (show 0 ≤ c by linarith)
      linarith
  · intro c' hs x e hx he ℓ (hℓ : ℓ.1 ≤ c * max x e)
    have hcc' := modeloUmbral_supuesto_le hs
    show ℓ.1 ≤ max x (c' * max x e)
    have hm : 1 ≤ max x e := le_max_of_le_right he
    apply le_max_of_le_right
    nlinarith
  · intro x e ℓ (hℓ : ℓ.1 ≤ max x e)
    exact hℓ

/-- **El umbral de Fortnow–van Melkebeek es exacto para estas reglas**: hay contradicción en todo mundo que cumpla
`ReglasLV` y `ReglasFvM` si y solo si `c < φ`. -/
theorem umbral_fortnow_van_melkebeek (c : ℝ) :
    (∀ (M : MundoClases) (EA EC ED : ℝ → ℝ → Set M.Leng),
      ReglasLV M → ReglasFvM M EA EC ED → SupuestoSAT M c → False) ↔ c < φ := by
  constructor
  · intro h
    by_contra hc
    have hc := not_lt.1 hc
    have hφ := Real.goldenRatio_sq
    have hφ1 := Real.one_lt_goldenRatio
    have hc0 : 0 ≤ c := by linarith
    have hcc : 2 ≤ c * c := by nlinarith
    exact h _ _ _ _ (modeloUmbral_reglas hc0 hcc) (modeloFvM_reglas hc) (modeloUmbral_supuesto hc0)
  · intro hc M EA EC ED R F hs
    exact fortnow_van_melkebeek_juego R F hc hs

/-! ## 5. Los números: √2 < φ < 2cos(π/7) < 2 -/

/-- **El orden de los umbrales.** Lipton–Viglas (√2), Fortnow–van Melkebeek (φ) y el techo de Buss–Williams
(2cos(π/7) ≈ 1,8019) están en ese orden, y todos por debajo de 2. Es solo aritmética: **no** es el teorema de
Buss–Williams, que no se enuncia aquí. -/
theorem orden_de_los_umbrales : √2 < φ ∧ φ < 2 * Real.cos (π / 7) ∧ 2 * Real.cos (π / 7) < 2 := by
  have hπ0 := Real.pi_pos
  have hπ := Real.pi_lt_d2
  have hφ : φ < 1.62 := by
    have h5 : √5 < 2.24 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    show (1 + √5) / 2 < 1.62
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h5 : (2 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    show √2 < (1 + √5) / 2
    linarith
  · have hcos := Real.one_sub_sq_div_two_le_cos (x := π / 7)
    have hsq : (π / 7) ^ 2 < 0.2025 := by
      have : π / 7 < 0.45 := by linarith
      have h0 : 0 < π / 7 := by positivity
      nlinarith
    linarith
  · have habs : |π / 7| ≤ π := by
      rw [abs_of_pos (by positivity)]; linarith
    have hcos := Real.cos_le_one_sub_mul_cos_sq habs
    have hpos : 0 < 2 / π ^ 2 * (π / 7) ^ 2 := by positivity
    linarith

/-! ## 6. Controles -/

/-- **Control: las reglas solas no son contradictorias.** Sin el supuesto sobre SAT hay un mundo que las cumple todas
(también las finas). -/
theorem control_reglas_consistentes :
    ∃ M : MundoClases, ∃ EA EC ED : ℝ → ℝ → Set M.Leng, ReglasLV M ∧ ReglasFvM M EA EC ED := by
  have hφ2 := Real.goldenRatio_lt_two
  exact ⟨modeloUmbral 2, _, _, _, modeloUmbral_reglas (by norm_num) (by norm_num),
    modeloFvM_reglas hφ2.le⟩

/-- **Control: `c = 1` da la contradicción** (un SAT lineal con memoria `n^{o(1)}`). -/
theorem control_c_uno (M : MundoClases) (R : ReglasLV M) (hs : SupuestoSAT M 1) : False :=
  lipton_viglas_juego R (by rw [Real.lt_sqrt (by norm_num)]; norm_num) hs

/-- **Control: `c = 2` no la da**, ni con las reglas finas: el modelo cumple todo con el supuesto. -/
theorem control_c_dos :
    ∃ M : MundoClases, ∃ EA EC ED : ℝ → ℝ → Set M.Leng,
      ReglasLV M ∧ ReglasFvM M EA EC ED ∧ SupuestoSAT M 2 := by
  have hφ2 := Real.goldenRatio_lt_two
  exact ⟨modeloUmbral 2, _, _, _, modeloUmbral_reglas (by norm_num) (by norm_num),
    modeloFvM_reglas hφ2.le, modeloUmbral_supuesto (by norm_num)⟩

/-- **Control: `c = 3/2` separa los dos esquemas.** Las reglas de Lipton–Viglas no alcanzan (hay modelo), las finas
sí (contradicción). -/
theorem control_tres_medios :
    (∃ M : MundoClases, ReglasLV M ∧ SupuestoSAT M (3 / 2)) ∧
      (∀ (M : MundoClases) (EA EC ED : ℝ → ℝ → Set M.Leng),
        ReglasLV M → ReglasFvM M EA EC ED → SupuestoSAT M (3 / 2) → False) := by
  refine ⟨⟨modeloUmbral (3 / 2), modeloUmbral_reglas (by norm_num) (by norm_num),
    modeloUmbral_supuesto (by norm_num)⟩, ?_⟩
  refine (umbral_fortnow_van_melkebeek (3 / 2)).2 ?_
  have h5 : (2 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  show (3 : ℝ) / 2 < (1 + √5) / 2
  linarith

/-! ## 7. Mapa de cslib-frontier: qué hay para que el juego deje de ser abstracto

Explorado con `find` y `grep` en `.lake/packages/cslib-frontier` (24 nov 2026).

* **Tiempo y memoria simultáneos: sí.** `Cslib.Complexity.TISP enc t s`
  (`Computability/Complexity/Classes/TimeSpace/Basic.lean`), con monotonía, cierre bajo complemento
  (`compl_mem_TISP`) y `TISP ⊆ DTIME`, `TISP ⊆ DSPACE`. Las cotas son funciones `ℕ → ℕ` concretas: no hay
  `n^{o(1)}` como clase, hay que elegir una (por ejemplo `log² n`).
* **Alternancia: solo Σ₂ con tiempo fino.** `SigmaTwoTIME enc t` (`Classes/Time/SigmaTwo.lean`), en forma de
  verificador. Hay jerarquía polinomial `SigmaP k` (`Classes/PH.lean`) y máquinas alternantes `ATIME`/`ASPACE`
  (`Classes/Alternation.lean`), pero la propia librería dice que no hay puente entre `SigmaTwoTIME` y las máquinas
  alternantes, y **no hay Σ_k-TIME(t) para `k ≥ 3`**. Tampoco hay coNTIME(t) con nombre ni Π₂-TIME.
* **Acelerar sobre máquinas: sí, más débil.** `TISP_subset_SigmaTwoTIME` (`TimeSpace/Speedup.lean`, la de Kannan en
  la forma de FLvMV, Lema 3.1): TISP(t, s) ⊆ Σ₂TIME(√t · (s + n log² n + log² t)), con el factor `s` en vez de `√s`
  (la librería lo declara abierto) y un término `n log² n` de leer la entrada. Para `s = polylog` y `t = n^a` da
  Σ₂(n^{a/2 + 1 + o(1)}): el `+1` se diluye tomando `a` grande, así que no estorba a Lipton–Viglas. No revisé si
  estorba a la versión fina de Fortnow–van Melkebeek, que necesita llevar la cuenta de la entrada de cada fase.
* **Quitar una alternancia: sí, solo de Σ₂ a NTIME.** `SigmaTwoTIME_subset_NTIME` y su forma polinomial
  `SigmaTwoTIME_succ_pow_subset_NTIME_succ_pow` (`TimeSpace/Slowdown.lean`): si NTIME(n) ⊆ DTIME(t') con
  `t'(m)^q = O(m^p)`, entonces Σ₂TIME(n^a) ⊆ NTIME(n^b) cuando `a·p ≤ b·q`. Exponentes naturales con razón racional.
* **Lo que falta** para un Lipton–Viglas sobre máquinas: el relleno del supuesto hacia `TISP` (NTIME(n) ⊆ TISP(n^c, s)
  ⇒ NTIME(n^a) ⊆ TISP(n^{ac}, s')), que no encontré (`TISP` no aparece fuera de esos dos archivos); la jerarquía
  NTIME(n^a) ⊄ coNTIME(n^{a'}) con `a' < a` (hay `NTIME_succ_pow_ssubset_NTIME_succ_pow`, NTIME contra NTIME con
  exponentes naturales, no contra coNTIME); la reducción casi lineal de NTIME(n) a SAT (no la encontré); y el ensamble.
  Para Fortnow–van Melkebeek falta además Σ_k con el largo de entrada de cada fase. No intenté nada de esto aquí: no
  cabe en este archivo.
-/

end Sagitta.Map.Tiempo.IntercambioAlternancias
