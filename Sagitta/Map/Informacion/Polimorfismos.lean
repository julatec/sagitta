import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation

/-!
# Los polimorfismos de Schaefer

Es el paso de Lean de «Misma estructura, misma complejidad» (ver las notas del proyecto). Un **polimorfismo** de una
relación `R ⊆ Bool^r` es una operación `f : Bool^k → Bool` que, aplicada coordenada a coordenada a `k` tuplas de `R`,
da otra tupla de `R`: una receta para fabricar una solución nueva con `k` soluciones viejas. Con `k = 1` y `f`
biyectiva es un automorfismo, así que los polimorfismos generalizan la simetría.

La lectura, en una línea: **simetría generalizada ⇒ fácil; sin simetría ⇒ difícil**. Es un teorema para los CSP
(Schaefer 1978 en el caso booleano; Bulatov y Zhuk en general, 2017), no para todo NP. **Aquí solo se formaliza el
lado de los polimorfismos, no la dicotomía**: ni los algoritmos que salen de cada polimorfismo, ni la
NP-completitud de 3-SAT, ni la conexión de Galois.

## Lo que se prueba

1. **La definición** (§ 1). `Preserva f R`: para toda elección `t : Fin k → Fin r → Bool` de `k` tuplas de `R`
   (la tupla `i` es `t i`), la tupla `c ↦ f (i ↦ t i c)` está en `R`. `Polimorfismo Γ f`: `f` preserva todas las
   relaciones de `Γ`, un conjunto de relaciones de aridades cualesquiera. Las proyecciones son polimorfismos de
   todo (`proy_polimorfismo`). Las cláusulas son `clausula σ` (`∃ c, x c = σ c`: el literal `c` es positivo si
   `σ c = true`).
2. **2-SAT tiene la mayoría** (§ 2). La mayoría de tres pares booleanos es siempre uno de los tres
   (`maj_elige`, por `decide`), así que `maj` preserva **toda** relación binaria (`maj_preserva_binaria`), en
   particular las cuatro cláusulas de dos literales (`maj_polimorfismo_dosSAT`, y una por una con `decide`).
3. **XOR-SAT tiene Maltsev** (§ 3). `paridad (a ⊕ b ⊕ c) = paridad a ⊕ paridad b ⊕ paridad c`
   (`paridad_xor3`), así que `x ⊕ y ⊕ z` preserva toda ecuación `x₁ ⊕ ⋯ ⊕ x_r = b`, de cualquier largo
   (`maltsev_preserva_paridad`), y con ellas `x ⊕ y = 0, 1` y `x ⊕ y ⊕ z = 0, 1` (`maltsev_polimorfismo_xorSAT`).
4. **Horn tiene el AND** (§ 4). `x ∧ y` preserva toda cláusula con a lo sumo un literal positivo, de cualquier
   largo (`y_preserva_horn`), en particular las de hasta 3 literales (`y_polimorfismo_horn`).
5. **3-SAT no tiene nada** (§ 5). Si `f` preserva las ocho cláusulas de 3 literales, en cualquier elección de
   tres entradas coincide con una proyección (`filas`). Con las entradas unitarias se halla una coordenada `j` con
   `f (e j) = 1`, y eso obliga a `f = proy j` (`de_unitario`). Así, toda operación de aridad `1 ≤ k ≤ 3` que
   preserve las cláusulas de 3-SAT es una proyección (`tresSAT_solo_proyecciones`), con las binarias y las ternarias
   como casos (`tresSAT_binarias`, `tresSAT_ternarias`). Es un argumento, no `decide` sobre las 256 ternarias, y
   no depende de cuál `f` sea.
6. **Los automorfismos** (§ 6). Una operación unaria `g` aplicada en cada coordenada es polimorfismo de `R` si
   manda `R` en `R` (`unaria_preserva_iff`); si además `g` es biyectiva, manda `R` **sobre** `R`
   (`automorfismo`). La negación de todas las coordenadas a la vez **no** es polimorfismo de ninguna cláusula
   (`negacion_no_preserva`): manda la tupla `σ`, que cumple `clausula σ`, en `¬σ`, que no la cumple. Pero el
   conjunto de las ocho es cerrado bajo ella: `clausula σ (¬x) ↔ clausula (¬σ) x` (`clausula_neg`), así que la
   negación **permuta** las relaciones de 3-SAT (`tresSAT_cerrado_neg`). Es una simetría del molde, no de cada
   relación: mueve soluciones de una instancia a soluciones de la instancia con los signos cambiados, y no fabrica
   soluciones de la misma. Por eso no da algoritmo (`negacion_no_polimorfismo_tresSAT`).

## Antecedentes (de memoria)

Schaefer (1978), la dicotomía booleana; Jeavons, Cohen y Gyssens (1997–1998), la lectura por polimorfismos;
Bulatov (2017) y Zhuk (2017–2020), la dicotomía de los CSP finitos.
-/

namespace Sagitta.Map.Informacion.Polimorfismos

/-! ## 1. La definición -/

/-- Una relación booleana de aridad `r`. -/
abbrev Relacion (r : ℕ) := (Fin r → Bool) → Prop

/-- `f` de aridad `k` preserva `R`: se toman `k` tuplas de `R` (la `i`-ésima es `t i`), se aplica `f` en cada
coordenada `c`, y la tupla que sale está en `R`. -/
def Preserva {k r : ℕ} (f : (Fin k → Bool) → Bool) (R : Relacion r) : Prop :=
  ∀ t : Fin k → Fin r → Bool, (∀ i, R (t i)) → R (fun c => f (fun i => t i c))

/-- Un conjunto de relaciones de aridades cualesquiera (un «molde»). -/
abbrev Relaciones := Set (Σ r : ℕ, Relacion r)

/-- `f` es polimorfismo de `Γ` si preserva todas sus relaciones. -/
def Polimorfismo {k : ℕ} (Γ : Relaciones) (f : (Fin k → Bool) → Bool) : Prop :=
  ∀ R ∈ Γ, Preserva f R.2

/-- La proyección sobre la coordenada `j`. -/
def proy {k : ℕ} (j : Fin k) : (Fin k → Bool) → Bool := fun x => x j

/-- Las proyecciones preservan todo: devuelven la tupla `j`, que ya estaba en `R`. -/
theorem proy_preserva {k r : ℕ} (j : Fin k) (R : Relacion r) : Preserva (proy j) R :=
  fun _ ht => ht j

theorem proy_polimorfismo {k : ℕ} (Γ : Relaciones) (j : Fin k) : Polimorfismo Γ (proy j) :=
  fun R _ => proy_preserva j R.2

/-- La cláusula con signos `σ`: algún literal se cumple (`x c = σ c`; positivo si `σ c = true`). -/
def clausula {r : ℕ} (σ : Fin r → Bool) : Relacion r := fun x => ∃ c, x c = σ c

instance {r : ℕ} (σ : Fin r → Bool) (x : Fin r → Bool) : Decidable (clausula σ x) := by
  unfold clausula; infer_instance

/-- La negación de todas las coordenadas. -/
def neg {r : ℕ} (x : Fin r → Bool) : Fin r → Bool := fun c => !x c

/-- Una cláusula excluye una sola tupla: la de los signos opuestos. -/
theorem clausula_iff_ne {r : ℕ} (σ x : Fin r → Bool) : clausula σ x ↔ x ≠ neg σ := by
  unfold clausula neg
  constructor
  · rintro ⟨c, hc⟩ h
    have := congrFun h c
    cases hσ : σ c <;> simp_all
  · intro h
    by_contra hn
    push Not at hn
    exact h (funext fun c => by
      have := hn c
      cases hx : x c <;> cases hσ : σ c <;> simp_all)

/-! ## 2. 2-SAT tiene la mayoría -/

/-- La mayoría de tres. -/
def maj : (Fin 3 → Bool) → Bool := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

/-- La mayoría de tres pares booleanos, coordenada a coordenada, es uno de los tres pares (palomar: cada coordenada
la ganan al menos dos, y dos pares de entre tres se cruzan). -/
theorem maj_elige : ∀ t : Fin 3 → Fin 2 → Bool, ∃ i, ∀ c, maj (fun i => t i c) = t i c := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide

/-- Por eso la mayoría preserva **toda** relación binaria (las dieciséis). -/
theorem maj_preserva_binaria (R : Relacion 2) : Preserva maj R := by
  intro t ht
  obtain ⟨i, hi⟩ := maj_elige t
  have : (fun c => maj (fun i => t i c)) = t i := funext hi
  rw [this]; exact ht i

/-- Las cuatro cláusulas de dos literales. -/
def dosSAT : Relaciones := {R | ∃ σ : Fin 2 → Bool, R = ⟨2, clausula σ⟩}

theorem maj_polimorfismo_dosSAT : Polimorfismo dosSAT maj := by
  rintro R ⟨σ, rfl⟩
  exact maj_preserva_binaria _

/-- Las cuatro, una por una, por `decide`: `x ∨ y`, `x ∨ ¬y`, `¬x ∨ y`, `¬x ∨ ¬y`. -/
theorem maj_preserva_cuatro :
    Preserva maj (clausula ![true, true]) ∧ Preserva maj (clausula ![true, false]) ∧
    Preserva maj (clausula ![false, true]) ∧ Preserva maj (clausula ![false, false]) := by
  unfold Preserva
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide

/-! ## 3. XOR-SAT tiene Maltsev -/

/-- La paridad de una tupla: `x₀ ⊕ x₁ ⊕ ⋯`. -/
def paridad : {r : ℕ} → (Fin r → Bool) → Bool
  | 0, _ => false
  | _ + 1, x => xor (x 0) (paridad (Fin.tail x))

/-- La operación de Maltsev `x ⊕ y ⊕ z`. -/
def maltsev : (Fin 3 → Bool) → Bool := fun x => xor (xor (x 0) (x 1)) (x 2)

/-- La paridad conmuta con `⊕` coordenada a coordenada. -/
theorem paridad_xor3 {r : ℕ} (a b d : Fin r → Bool) :
    paridad (fun c => xor (xor (a c) (b c)) (d c)) = xor (xor (paridad a) (paridad b)) (paridad d) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [paridad]
    rw [show Fin.tail (fun c => xor (xor (a c) (b c)) (d c)) =
        fun c => xor (xor (Fin.tail a c) (Fin.tail b c)) (Fin.tail d c) from rfl, ih]
    generalize a 0 = a0; generalize b 0 = b0; generalize d 0 = d0
    generalize paridad (Fin.tail a) = pa
    generalize paridad (Fin.tail b) = pb
    generalize paridad (Fin.tail d) = pd
    revert a0 b0 d0 pa pb pd; decide

/-- La ecuación afín `x₁ ⊕ ⋯ ⊕ x_r = b`. -/
def ecuacion (r : ℕ) (b : Bool) : Relacion r := fun x => paridad x = b

/-- Maltsev preserva toda ecuación afín, de cualquier largo: `b ⊕ b ⊕ b = b`. -/
theorem maltsev_preserva_paridad (r : ℕ) (b : Bool) : Preserva maltsev (ecuacion r b) := by
  intro t ht
  unfold ecuacion maltsev at *
  rw [paridad_xor3, ht 0, ht 1, ht 2]
  cases b <;> rfl

/-- XOR-SAT con ecuaciones de dos y tres variables. -/
def xorSAT : Relaciones := {R | ∃ r b, (r = 2 ∨ r = 3) ∧ R = ⟨r, ecuacion r b⟩}

theorem maltsev_polimorfismo_xorSAT : Polimorfismo xorSAT maltsev := by
  rintro R ⟨r, b, -, rfl⟩
  exact maltsev_preserva_paridad r b

/-- Las de dos variables por `decide`: `x ⊕ y = 0` y `x ⊕ y = 1`. -/
theorem maltsev_preserva_dos :
    Preserva maltsev (ecuacion 2 false) ∧ Preserva maltsev (ecuacion 2 true) := by
  unfold Preserva ecuacion
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide

/-! ## 4. Horn tiene el AND -/

/-- El AND de dos. -/
def y : (Fin 2 → Bool) → Bool := fun x => x 0 && x 1

/-- A lo sumo un literal positivo. -/
def EsHorn {r : ℕ} (σ : Fin r → Bool) : Prop := ∀ c d, σ c = true → σ d = true → c = d

/-- El AND preserva toda cláusula de Horn, de cualquier largo. Si una de las dos soluciones cumple un literal
negativo, el AND también lo cumple; si las dos cumplen uno positivo, es el mismo (hay uno solo) y el AND lo cumple. -/
theorem y_preserva_horn {r : ℕ} (σ : Fin r → Bool) (hσ : EsHorn σ) : Preserva y (clausula σ) := by
  intro t ht
  obtain ⟨c, hc⟩ := ht 0
  obtain ⟨d, hd⟩ := ht 1
  cases hσc : σ c
  · exact ⟨c, by simp [y, hc, hσc]⟩
  · cases hσd : σ d
    · exact ⟨d, by simp [y, hd, hσd]⟩
    · obtain rfl := hσ c d hσc hσd
      exact ⟨c, by simp [y, hc, hd, hσc]⟩

/-- Las cláusulas de Horn de uno a tres literales. -/
def horn : Relaciones :=
  {R | ∃ r σ, 1 ≤ r ∧ r ≤ 3 ∧ EsHorn (r := r) σ ∧ R = ⟨r, clausula σ⟩}

theorem y_polimorfismo_horn : Polimorfismo horn y := by
  rintro R ⟨r, σ, -, -, hσ, rfl⟩
  exact y_preserva_horn σ hσ

/-! ## 5. 3-SAT no tiene nada -/

/-- Las ocho cláusulas de tres literales. -/
def tresSAT : Relaciones := {R | ∃ σ : Fin 3 → Bool, R = ⟨3, clausula σ⟩}

/-- Si `f` preserva todas las cláusulas de aridad `r`, en cualquier elección de `r` entradas (`fila c` es la entrada
de la coordenada `c`) coincide con una proyección. Si no, la tupla `c ↦ ¬ f (fila c)` sería distinta de toda
columna, así que todas las columnas cumplen la cláusula de signos `c ↦ ¬ f (fila c)`, y `f` daría justo la tupla
excluida. -/
theorem filas {k r : ℕ} (f : (Fin k → Bool) → Bool) (hf : ∀ σ : Fin r → Bool, Preserva f (clausula σ))
    (fila : Fin r → Fin k → Bool) : ∃ j, ∀ c, f (fila c) = fila c j := by
  by_contra h
  push Not at h
  obtain ⟨c, hc⟩ := hf (fun c => !f (fila c)) (fun i c => fila c i) (fun i => by
    obtain ⟨c, hc⟩ := h i
    exact ⟨c, by cases hx : fila c i <;> cases hy : f (fila c) <;> simp_all⟩)
  cases hy : f (fila c) <;> simp_all

/-- La entrada unitaria: `1` en la coordenada `j`, `0` en las demás. -/
def e {k : ℕ} (j : Fin k) : Fin k → Bool := fun i => decide (i = j)

/-- Si `f` preserva las cláusulas de 3-SAT y vale `1` en `e j`, es la proyección `j`: con las filas `x, e j, e j`,
la proyección que coincide tiene que valer `1` en `e j`, y esa es solo la `j`. -/
theorem de_unitario {k : ℕ} (f : (Fin k → Bool) → Bool) (hf : ∀ σ : Fin 3 → Bool, Preserva f (clausula σ))
    (j : Fin k) (hj : f (e j) = true) : f = proy j := by
  funext x
  obtain ⟨j', hj'⟩ := filas f hf ![x, e j, e j]
  have h1 : f (e j) = e j j' := hj' 1
  rw [hj] at h1
  have : j' = j := of_decide_eq_true h1.symm
  subst this
  exact hj' 0

/-- Toda operación de aridad `1 ≤ k ≤ 3` que preserve las ocho cláusulas de 3 literales es una proyección. -/
theorem tresSAT_solo_proyecciones {k : ℕ} (hk0 : 0 < k) (hk : k ≤ 3) (f : (Fin k → Bool) → Bool)
    (hf : Polimorfismo tresSAT f) : ∃ j, f = proy j := by
  have hf' : ∀ σ : Fin 3 → Bool, Preserva f (clausula σ) := fun σ => hf _ ⟨σ, rfl⟩
  -- Las filas unitarias `e 0, …, e (k-1)` (repitiendo la última).
  obtain ⟨j, hj⟩ := filas f hf' (fun c => e (⟨min c.val (k - 1), by omega⟩ : Fin k))
  refine ⟨j, de_unitario f hf' j ?_⟩
  have := hj ⟨j.val, by omega⟩
  have hmin : (⟨min j.val (k - 1), by omega⟩ : Fin k) = j := by
    ext; simp only; omega
  simp only [hmin] at this
  rw [this]; simp [e]

/-- Y al revés: las proyecciones sí. Así, `Pol(3-SAT)` en aridad `1 ≤ k ≤ 3` son exactamente las proyecciones. -/
theorem tresSAT_pol_iff {k : ℕ} (hk0 : 0 < k) (hk : k ≤ 3) (f : (Fin k → Bool) → Bool) :
    Polimorfismo tresSAT f ↔ ∃ j, f = proy j :=
  ⟨tresSAT_solo_proyecciones hk0 hk f, by rintro ⟨j, rfl⟩; exact proy_polimorfismo _ j⟩

theorem tresSAT_binarias (f : (Fin 2 → Bool) → Bool) (hf : Polimorfismo tresSAT f) : ∃ j, f = proy j :=
  tresSAT_solo_proyecciones (by decide) (by decide) f hf

theorem tresSAT_ternarias (f : (Fin 3 → Bool) → Bool) (hf : Polimorfismo tresSAT f) : ∃ j, f = proy j :=
  tresSAT_solo_proyecciones (by decide) le_rfl f hf

/-- En particular, ninguno de los tres de arriba sirve para 3-SAT. -/
theorem maj_no_tresSAT : ¬ Polimorfismo tresSAT maj := by
  intro h
  obtain ⟨j, hj⟩ := tresSAT_ternarias maj h
  have h1 := congrFun hj (e (j + 1))
  have h2 := congrFun hj (fun i => !e (j + 1) i)
  revert h1 h2; revert j; decide

theorem maltsev_no_tresSAT : ¬ Polimorfismo tresSAT maltsev := by
  intro h
  obtain ⟨j, hj⟩ := tresSAT_ternarias maltsev h
  have h1 := congrFun hj (fun i => !e j i)
  revert h1; revert j; decide

theorem y_no_tresSAT : ¬ Polimorfismo tresSAT y := by
  intro h
  obtain ⟨j, hj⟩ := tresSAT_binarias y h
  have h1 := congrFun hj (e j)
  revert h1; revert j; decide

/-! ## 6. Los automorfismos son los polimorfismos unarios biyectivos -/

/-- La operación unaria que aplica `g` (a la única entrada). -/
def unaria (g : Bool → Bool) : (Fin 1 → Bool) → Bool := fun x => g (x 0)

/-- Un polimorfismo unario es una función que manda `R` en `R`, aplicada en cada coordenada. -/
theorem unaria_preserva_iff {r : ℕ} (g : Bool → Bool) (R : Relacion r) :
    Preserva (unaria g) R ↔ ∀ x, R x → R (g ∘ x) := by
  constructor
  · intro h x hx
    exact h (fun _ => x) (fun _ => hx)
  · intro h t ht
    exact h (t 0) (ht 0)

/-- Si además `g` es biyectiva, manda `R` **sobre** `R`: es un automorfismo (en un dominio finito, una inyección de
`R` en `R` es biyección). -/
theorem automorfismo {r : ℕ} (g : Bool → Bool) (hg : Function.Bijective g) (R : Relacion r)
    (h : Preserva (unaria g) R) : ∀ x, R (g ∘ x) ↔ R x := by
  rw [unaria_preserva_iff] at h
  let φ : {x // R x} → {x // R x} := fun x => ⟨g ∘ x.1, h x.1 x.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    funext c
    exact hg.1 (congrFun (congrArg Subtype.val hab) c)
  have hsur := (Finite.injective_iff_surjective.mp hinj)
  intro x
  refine ⟨fun hx => ?_, h x⟩
  obtain ⟨⟨z, hz⟩, hzx⟩ := hsur ⟨g ∘ x, hx⟩
  have : z = x := by
    funext c
    exact hg.1 (congrFun (congrArg Subtype.val hzx) c)
  exact this ▸ hz

/-- La negación de todas las coordenadas, como operación unaria. -/
def negacion : (Fin 1 → Bool) → Bool := unaria (fun b => !b)

/-- No es polimorfismo de ninguna cláusula: `σ` cumple `clausula σ` y `¬σ` no. -/
theorem negacion_no_preserva {r : ℕ} [NeZero r] (σ : Fin r → Bool) : ¬ Preserva negacion (clausula σ) := by
  intro h
  obtain ⟨c, hc⟩ := h (fun _ => σ) (fun _ => ⟨0, rfl⟩)
  cases hs : σ c <;> simp_all [negacion, unaria]

theorem negacion_no_polimorfismo_tresSAT : ¬ Polimorfismo tresSAT negacion :=
  fun h => negacion_no_preserva (fun _ : Fin 3 => true) (h _ ⟨_, rfl⟩)

/-- Pero el conjunto de las cláusulas es cerrado bajo ella: negar la tupla es cambiar los signos de la cláusula. -/
theorem clausula_neg {r : ℕ} (σ x : Fin r → Bool) : clausula σ (neg x) ↔ clausula (neg σ) x := by
  unfold clausula neg
  constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c, by cases hx : x c <;> cases hs : σ c <;> simp_all⟩

/-- La negación permuta las ocho relaciones de 3-SAT: `clausula σ ∘ neg = clausula (neg σ)`. -/
theorem tresSAT_cerrado_neg (σ : Fin 3 → Bool) :
    (⟨3, fun x => clausula σ (neg x)⟩ : Σ r : ℕ, Relacion r) ∈ tresSAT :=
  ⟨neg σ, by simp only [Sigma.mk.injEq, heq_eq_eq, true_and]; funext x; exact propext (clausula_neg σ x)⟩

/-- Y es biyectiva sobre los signos, así que es una permutación de las ocho, sin puntos fijos: ninguna cláusula
es su propia negada. -/
theorem neg_sin_puntos_fijos (σ : Fin 3 → Bool) : neg σ ≠ σ := by
  intro h
  have := congrFun h 0
  cases hs : σ 0 <;> simp_all [neg]

end Sagitta.Map.Informacion.Polimorfismos
