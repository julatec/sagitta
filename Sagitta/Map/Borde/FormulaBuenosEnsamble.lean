import Sagitta.Map.Borde.FormulaBuenos
import Sagitta.Map.Borde.ParikhT12

/-!
# FormulaBuenos, el ensamble

`FormulaBuenos.lean` dejó las piezas: tres fórmulas `Σᵇ₁` con gráfico exacto (la forma de un código de circuito, su
evaluación y SAT enmarcado, por `Σᵇ₁ = NP`) y `Buenos satMarco c k` reescrito con cuantificadores acotados
(`buenos_iff_acotado`, `buenos_iff_codigos`). Aquí se arma la fórmula acotada de dos variables

  `|x| ≤ |y| ∧ ∃ C ≤ T(y) [ φF(C, y) ∧ ∀ z ≤ 4y+1 ( |z| = S|y| → (φE(C, z) → φS(z)) ∧ (φS(z) → φE(C, z)) ) ]`

y se prueba que define `Buenos satMarco c k` en ℕ (`formulaBuenos`). Con eso cae la hipótesis de
`OscilacionParikh.s12_oscila_de_formula`: si SAT oscila en circuitos, hay un enunciado `∀ x ∃ y φ` con `φ` acotada,
verdadero en ℕ, que S¹₂ no deriva (`s12_oscila_sin_hipotesis`), y lo mismo con T¹₂ (`t12_oscila_sin_hipotesis`).

## La cota del `∃ C`

Es la única cuenta nueva. Un circuito bueno tiene un código con `|C| ≤ cotaCodigo c k y = 18·(|y| + c(|y|+1)^k + 1)²`
(`buenos_iff_acotado`), así que basta un término de Buss `T(y) ≥ 2^cotaCodigo`. Con `w = 2y + 1` (`|w| = |y| + 1`),
`s₀ = w`, `s_{j+1} = s_j # w` tiene `|s_j| ≥ (|y|+1)^(j+1)`; con el numeral `D_N` (`|D_N| = N`), `T = s_{2k+1} # D_N`
vale `2^(|s_{2k+1}|·N) ≥ 2^((|y|+1)^(2k+2)·N)`, y con `N = 18(c+1)²` eso pasa a `2^cotaCodigo`, porque
`|y| + c(|y|+1)^k + 1 ≤ (c+1)(|y|+1)^(k+1)`.

## Lo que no

* No se prueba que SAT oscile ni que no oscile: el resultado sigue condicionado a `Oscila (sucNat satMarco)`.
* La fórmula no es la del artículo ni la más económica: es `Σᵇ₃` en forma (un `∃` acotado, un `∀` acotado, y dentro
  una `Σᵇ₁` y su negación), y Parikh vale para toda fórmula acotada, así que el nivel no importa aquí.
* Las piezas vienen de `Σᵇ₁ = NP` como existencia, no como fórmulas escritas; la fórmula final tampoco se imprime.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map.Borde.FormulaBuenos

open Sagitta.Map Sagitta.Map.Acotada
open Sagitta.Map.Borde.OscilacionParikh (EsAcotada Define FormulaBuenos Buenos s12_oscila_de_formula
  no_sobre_iff_verdadero existeY)
open Sagitta.Map.Borde.Tricotomia (Oscila)

/-! ## 1. Los términos de la cota -/

section Terminos

variable {β : Type}

/-- `2t + 1`, escrito `S(t + t)`: `|2t + 1| = |t| + 1`. -/
def tW (t : L.Term β) : L.Term β := tSc (tMs t t)

/-- `s₀ = w`, `s_{j+1} = s_j # w`, con `w = 2t + 1`. -/
def tPot (t : L.Term β) : ℕ → L.Term β
  | 0 => tW t
  | j + 1 => tSm (tPot t j) (tW t)

/-- El numeral `D_j = 2^j − 1`: `D₀ = 0`, `D_{j+1} = S(D_j + D_j)`. Tiene `j` bits. -/
def tNum : ℕ → L.Term β
  | 0 => tC
  | j + 1 => tSc (tMs (tNum j) (tNum j))

/-- **La cota del `∃ C`**: `s_{2k+1} # D_{18(c+1)²}`. -/
def tCota (c k : ℕ) (t : L.Term β) : L.Term β := tSm (tPot t (2 * k + 1)) (tNum (18 * (c + 1) ^ 2))

/-- **`4t + 1`**, la cota del `∀ z`. -/
def tCuatro (t : L.Term β) : L.Term β := tSc (tMs (tMs t t) (tMs t t))

theorem size_dosMasUno (a : ℕ) : Nat.size (a + a + 1) = Nat.size a + 1 := by
  have h := Nat.size_bit (b := true) (n := a) (by rw [Nat.bit_val]; simp)
  rw [Nat.bit_val] at h
  simpa [two_mul] using h

variable (v : β → ℕ)

theorem size_tW (t : L.Term β) : Nat.size ((tW t).realize v) = Nat.size (t.realize v) + 1 := by
  simp only [tW, SigmaFagin.rn_tSc, SigmaFagin.rn_tMs]; exact size_dosMasUno _

theorem size_tNum (j : ℕ) : Nat.size ((tNum j : L.Term β).realize v) = j := by
  induction j with
  | zero => simp [tNum]
  | succ j ih =>
    simp only [tNum, SigmaFagin.rn_tSc, SigmaFagin.rn_tMs]
    rw [size_dosMasUno, ih]

theorem size_tPot (t : L.Term β) (j : ℕ) :
    (Nat.size (t.realize v) + 1) ^ (j + 1) ≤ Nat.size ((tPot t j).realize v) := by
  induction j with
  | zero => simp [tPot, size_tW]
  | succ j ih =>
    simp only [tPot, SigmaFagin.rn_tSm, OscilacionParikh.size_dos_pow, size_tW]
    rw [pow_succ]
    have := Nat.mul_le_mul_right (Nat.size (t.realize v) + 1) ih
    omega

/-- `|y| + c(|y|+1)^k + 1 ≤ (c+1)(|y|+1)^(k+1)`. -/
theorem base_le (c k m : ℕ) : m + c * (m + 1) ^ k + 1 ≤ (c + 1) * (m + 1) ^ (k + 1) := by
  have h1 : m + 1 ≤ (m + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have h2 : (m + 1) ^ k ≤ (m + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 := Nat.mul_le_mul_left c h2
  rw [add_mul, one_mul]; omega

/-- `cotaCodigo c k y ≤ (|y|+1)^(2k+2) · 18(c+1)²`. -/
theorem cotaCodigo_le (c k y : ℕ) :
    cotaCodigo c k y ≤ (Nat.size y + 1) ^ (2 * k + 1 + 1) * (18 * (c + 1) ^ 2) := by
  unfold cotaCodigo
  have h := Nat.pow_le_pow_left (base_le c k (Nat.size y)) 2
  have e : ((c + 1) * (Nat.size y + 1) ^ (k + 1)) ^ 2 = (c + 1) ^ 2 * (Nat.size y + 1) ^ (2 * k + 1 + 1) := by
    rw [mul_pow, ← pow_mul]; congr 2; ring
  rw [e] at h
  calc 18 * (Nat.size y + c * (Nat.size y + 1) ^ k + 1) ^ 2
      ≤ 18 * ((c + 1) ^ 2 * (Nat.size y + 1) ^ (2 * k + 1 + 1)) := Nat.mul_le_mul_left 18 h
    _ = _ := by ring

/-- **La cota del `∃ C` alcanza**: si `|C| ≤ cotaCodigo c k y`, `C ≤ T(y)`. -/
theorem le_tCota (c k : ℕ) (t : L.Term β) (C : ℕ) (hC : Nat.size C ≤ cotaCodigo c k (t.realize v)) :
    C ≤ (tCota c k t).realize v := by
  simp only [tCota, SigmaFagin.rn_tSm, size_tNum]
  have h1 := Nat.lt_size_self C
  have h2 := cotaCodigo_le c k (t.realize v)
  have h3 := Nat.mul_le_mul_right (18 * (c + 1) ^ 2) (size_tPot v t (2 * k + 1))
  have h4 : 2 ^ Nat.size C ≤ 2 ^ (Nat.size ((tPot t (2 * k + 1)).realize v) * (18 * (c + 1) ^ 2)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- `tPot t j` solo depende del valor de `t`. -/
theorem rn_tPot (t : L.Term β) (j : ℕ) :
    (tPot t j).realize v = (tPot (Term.var () : L.Term Unit) j).realize fun _ => t.realize v := by
  induction j with
  | zero => simp [tPot, tW]
  | succ j ih => simp only [tPot, SigmaFagin.rn_tSm, ih, tW, SigmaFagin.rn_tSc, SigmaFagin.rn_tMs, Term.realize_var]

/-- **El valor de la cota**, como función de `y`. -/
def cotaT (c k y : ℕ) : ℕ := (tCota c k (Term.var () : L.Term Unit)).realize fun _ => y

theorem rn_tCota (c k : ℕ) (t : L.Term β) : (tCota c k t).realize v = cotaT c k (t.realize v) := by
  simp only [cotaT, tCota, SigmaFagin.rn_tSm, size_tNum]
  rw [rn_tPot]

/-- **La cota alcanza**, en números: `|C| ≤ cotaCodigo c k y` da `C ≤ cotaT c k y`. -/
theorem le_cotaT (c k y C : ℕ) (hC : Nat.size C ≤ cotaCodigo c k y) : C ≤ cotaT c k y :=
  le_tCota (fun _ => y) c k (Term.var ()) C hC

theorem rn_tCuatro (t : L.Term β) : (tCuatro t).realize v = 4 * t.realize v + 1 := by
  simp only [tCuatro, SigmaFagin.rn_tSc, SigmaFagin.rn_tMs]; ring

end Terminos

/-! ## 2. La fórmula -/

section Formula

/-- `x`, `y`, libres; `C` y `z`, ligadas. -/
def vx0 : L.Term (Fin 2 ⊕ Fin 0) := Term.var (Sum.inl 0)
def vy0 : L.Term (Fin 2 ⊕ Fin 0) := Term.var (Sum.inl 1)
def vy1 : L.Term (Fin 2 ⊕ Fin 1) := Term.var (Sum.inl 1)
def vy2 : L.Term (Fin 2 ⊕ Fin 2) := Term.var (Sum.inl 1)
def vz2 : L.Term (Fin 2 ⊕ Fin 2) := Term.var (Sum.inr 1)

/-- Dónde van las variables de `φF(C, y)` bajo el `∃ C`. -/
def gF : Fin 2 → Fin 2 ⊕ Fin 1 := ![Sum.inr 0, Sum.inl 1]
/-- Dónde van las de `φE(C, z)` bajo el `∀ z`. -/
def gE : Fin 2 → Fin 2 ⊕ Fin 2 := ![Sum.inr 0, Sum.inr 1]
/-- Dónde va la de `φS(z)` bajo el `∀ z`. -/
def gS : Fin 1 → Fin 2 ⊕ Fin 2 := fun _ => Sum.inr 1

/-- **La fórmula de los largos buenos**, con las piezas `φF` (forma), `φE` (evaluación) y `φS` (SAT enmarcado):
`|x| ≤ |y| ∧ ∃ C ≤ T(y) [φF(C, y) ∧ ∀ z ≤ 4y+1 (|z| = S|y| → (φE(C, z) ↔ φS(z)))]`. -/
def formulaB (c k : ℕ) (φF φE : L.Formula (Fin 2)) (φS : L.Formula (Fin 1)) : L.Formula (Fin 2) :=
  leF (tLong vx0) (tLong vy0) ⊓
    existeAcotado (tCota c k vy0)
      (BoundedFormula.relabel gF φF ⊓
        paraTodoAcotado (tCuatro vy1)
          ((BoundedFormula.equal (tLong vz2) (tSc (tLong vy2))).imp
            (((BoundedFormula.relabel gE φE).imp (BoundedFormula.relabel gS φS)) ⊓
              ((BoundedFormula.relabel gS φS).imp (BoundedFormula.relabel gE φE)))))

theorem esAcotada_formulaB (c k : ℕ) {φF φE : L.Formula (Fin 2)} {φS : L.Formula (Fin 1)}
    (hF : EsSigma1 φF) (hE : EsSigma1 φE) (hS : EsSigma1 φS) : EsAcotada (formulaB c k φF φE φS) := by
  have hF' := esAcotada_de_sigma (Arranque.EsSigma1.relabel gF hF)
  have hE' := esAcotada_de_sigma (Arranque.EsSigma1.relabel gE hE)
  have hS' := esAcotada_de_sigma (Arranque.EsSigma1.relabel gS hS)
  exact .inf (.rel _ _) (.existe _ (.inf hF' (.todo _ (.imp (.igual _ _) (.inf (.imp hE' hS') (.imp hS' hE'))))))

theorem snoc1 (d : Fin 0 → ℕ) (C : ℕ) : (Fin.snoc d C : Fin 1 → ℕ) = ![C] := by
  funext i; fin_cases i; rfl

theorem snoc2 (C z : ℕ) : (Fin.snoc (![C] : Fin 1 → ℕ) z : Fin 2 → ℕ) = ![C, z] := by
  funext i; fin_cases i <;> rfl

/-- Leer una fórmula reetiquetada hacia `Fin 2 ⊕ Fin n`. -/
theorem realize_relabel_formula {γ : Type} {n : ℕ} (φ : L.Formula γ) (g : γ → Fin 2 ⊕ Fin n) (v : Fin 2 → ℕ)
    (xs : Fin n → ℕ) : (BoundedFormula.relabel g φ).Realize v xs ↔ φ.Realize (Sum.elim v xs ∘ g) := by
  rw [BoundedFormula.realize_relabel, Formula.Realize]
  exact iff_of_eq (congrArg₂ _ rfl (Subsingleton.elim _ _))

/-- **Lo que dice la fórmula**, con piezas de gráfico exacto. -/
theorem realize_formulaB (c k : ℕ) {φF φE : L.Formula (Fin 2)} {φS : L.Formula (Fin 1)}
    (dF : ∀ C y : ℕ, φF.Realize ![C, y] ↔ formaCodB c k C y = true)
    (dE : ∀ C z : ℕ, φE.Realize ![C, z] ↔ evalCodB true C z = true)
    (dS : ∀ z : ℕ, 1 ≤ z → (φS.Realize ![z] ↔ Tiempo.Relleno.satMarco (palabraNum z) = true)) (x y : ℕ) :
    (formulaB c k φF φE φS).Realize ![x, y] ↔ Nat.size x ≤ Nat.size y ∧
      ∃ C ≤ cotaT c k y, formaCodB c k C y = true ∧
        ∀ z ≤ 4 * y + 1, Nat.size z = Nat.size y + 1 →
          (evalCodB true C z = true ↔ Tiempo.Relleno.satMarco (palabraNum z) = true) := by
  rw [formulaB, Formula.Realize, BoundedFormula.realize_inf, Parikh.realize_leF, Parikh.realize_existe]
  simp only [Arranque.realize_tLong, long_nat, le_nat, rn_tCota, vx0, vy0, Term.realize_var, Sum.elim_inl,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  refine and_congr_right fun _ => exists_congr fun C => and_congr_right fun _ => ?_
  rw [BoundedFormula.realize_inf, Parikh.realize_paraTodo, realize_relabel_formula, snoc1]
  have eF : (Sum.elim ![x, y] ![C] ∘ gF : Fin 2 → ℕ) = ![C, y] := by funext i; fin_cases i <;> rfl
  rw [eF, dF]
  refine and_congr_right fun _ => ?_
  rw [rn_tCuatro]
  refine forall_congr' fun z => ?_
  simp only [le_nat]
  refine forall_congr' fun _ => ?_
  rw [snoc2, BoundedFormula.realize_imp, BoundedFormula.realize_inf, BoundedFormula.realize_imp,
    BoundedFormula.realize_imp, realize_relabel_formula, realize_relabel_formula]
  have eE : (Sum.elim ![x, y] ![C, z] ∘ gE : Fin 2 → ℕ) = ![C, z] := by funext i; fin_cases i <;> rfl
  have eS : (Sum.elim ![x, y] ![C, z] ∘ gS : Fin 1 → ℕ) = ![z] := by funext i; fin_cases i; rfl
  rw [eE, eS, dE]
  change (Nat.size z = Nat.size y + 1 → _) ↔ _
  refine forall_congr' fun hz => ?_
  have h1 : 1 ≤ z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · rw [h, Nat.size_zero] at hz; omega
    · exact h
  rw [dS z h1]
  constructor
  · rintro ⟨a, b⟩; exact ⟨a, b⟩
  · rintro ⟨a, b⟩; exact ⟨a, b⟩

/-- **La fórmula define `Buenos satMarco c k`.** La ida usa `buenos_iff_acotado` (el `C` bueno tiene código corto, y
`le_tCota` lo pone bajo `T(y)`); la vuelta, `buenos_iff_codigos` (el `∀ z` sin cota sale de `le_de_size`). -/
theorem define_formulaB (c k : ℕ) {φF φE : L.Formula (Fin 2)} {φS : L.Formula (Fin 1)}
    (dF : ∀ C y : ℕ, φF.Realize ![C, y] ↔ formaCodB c k C y = true)
    (dE : ∀ C z : ℕ, φE.Realize ![C, z] ↔ evalCodB true C z = true)
    (dS : ∀ z : ℕ, 1 ≤ z → (φS.Realize ![z] ↔ Tiempo.Relleno.satMarco (palabraNum z) = true)) :
    Define (formulaB c k φF φE φS) (Buenos Tiempo.Relleno.satMarco c k) := by
  intro x y
  rw [realize_formulaB c k dF dE dS]
  constructor
  · rintro ⟨hxy, C, -, hF, hE⟩
    exact (buenos_iff_codigos c k x y).2 ⟨hxy, C, hF, fun z hz => hE z (le_de_size y z hz) hz⟩
  · intro hB
    obtain ⟨hxy, C, hC, hF, hE⟩ := (buenos_iff_acotado c k x y).1 hB
    exact ⟨hxy, C, le_cotaT c k y C hC, hF, hE⟩

/-- **`FormulaBuenos`, sin hipótesis**: para todo `c`, `k` hay una fórmula acotada del lenguaje de Buss que define en
ℕ los largos buenos de SAT enmarcado para `c·(m+1)^k`. -/
theorem formulaBuenos (c k : ℕ) : FormulaBuenos c k := by
  obtain ⟨φE, hE, dE⟩ := existe_formula_eval true
  obtain ⟨φF, hF, dF⟩ := existe_formula_forma c k
  obtain ⟨φS, hS, dS⟩ := existe_formula_sat
  exact ⟨formulaB c k φF φE φS, esAcotada_formulaB c k hF hE hS, define_formulaB c k dF dE dS⟩

end Formula

/-! ## 3. Los corolarios, sin la hipótesis de la fórmula -/

/-- **Con S¹₂, sin hipótesis sobre la fórmula.** Si SAT enmarcado oscila en circuitos, hay una fórmula acotada `φ`
con `∀ x ∃ y φ(x, y)` verdadero en ℕ que S¹₂ no deriva. Ya no puede ser vacío: `formulaBuenos` da la fórmula. -/
theorem s12_oscila_sin_hipotesis (hO : Oscila (Tiempo.Finitud.sucNat Tiempo.Relleno.satMarco)) :
    ∃ φ : L.Formula (Fin 2), EsAcotada φ ∧ (∀ x : ℕ, ∃ y : ℕ, φ.Realize ![x, y]) ∧
      ¬ DerivaS12 (cierre (existeY φ)) :=
  s12_oscila_de_formula hO formulaBuenos

/-- **Con T¹₂.** Si SAT enmarcado oscila, hay una fórmula acotada `φ` con `∀ x ∃ y φ` verdadero en ℕ que T¹₂ no
demuestra (por modelos, `DemuestraExisteT12`). -/
theorem t12_oscila_sin_hipotesis (hO : Oscila (Tiempo.Finitud.sucNat Tiempo.Relleno.satMarco)) :
    ∃ φ : L.Formula (Fin 2), EsAcotada φ ∧ (∀ x : ℕ, ∃ y : ℕ, φ.Realize ![x, y]) ∧
      ¬ ParikhT12.DemuestraExisteT12 φ := by
  obtain ⟨c, k, hv⟩ := (no_sobre_iff_verdadero Tiempo.Relleno.satMarco).1 hO.2
  obtain ⟨φ, hφ, hdef⟩ := formulaBuenos c k
  refine ⟨φ, hφ, fun x => ?_, ParikhT12.t12_no_demuestra_oscila hO c k hφ hdef⟩
  obtain ⟨y, hy⟩ := hv x
  exact ⟨y, (hdef x y).2 hy⟩

/- Mutantes probados (25 nov 2026, fuera del repositorio; cada uno es una copia del archivo con un cambio, compilada con
`lake env lean`; los contraejemplos se evaluaron en Lean aparte):

* `define_formulaB` (la guarda del `∀ z`): `|z| = |y|` en vez de `|z| = S|y|`. La lectura no compila (el `change` de
  `realize_formulaB`), y lo que define es otra cosa: `z` recorre palabras de `|y| − 1` bits, la evaluación de un
  circuito de `|y|` entradas en ellas da siempre falso (`evalCodB` pide el largo exacto), y la fórmula pasa a pedir que
  SAT enmarcado rechace todas las palabras de largo `|y| − 1`.
* `le_cotaT` (la cota del `∃ C`): `T = s_k # D_N` en vez de `s_{2k+1} # D_N`. `omega` no cierra en `le_tCota`, y la
  cuenta es falsa: con `c = k = 0` e `y = 1`, `cotaCodigo = 72` y la cota mutada da `2·18 = 36`.
* `formulaBuenos` (y con ella los dos corolarios): quitar `|x| ≤ |y|`. `esAcotada_formulaB` y la lectura dejan de
  tipar, y la fórmula mutada no puede definir `Buenos`: no depende de `x`, pero con `c = sucNat satMarco 0`,
  `Buenos c 0 0 0` vale y `Buenos c 0 2 0` no (`|2| = 2 > 0`). -/

end Sagitta.Map.Borde.FormulaBuenos
