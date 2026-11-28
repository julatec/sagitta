import Sagitta.Map.CajaGris
import CslibFrontier.Algorithms.Lean.DPLL.RefutationSize
import CslibFrontier.Logics.Propositional.CuttingPlanes.Separation
import CslibFrontier.Logics.Propositional.CuttingPlanes.Resolution
import CslibFrontier.Logics.Propositional.Resolution.TseitinExpander
import CslibFrontier.Logics.Propositional.ParitySystem.Tseitin
import CslibFrontier.Logics.Propositional.Algebraic.Nullstellensatz.Tseitin
import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.TseitinExpander
import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.Pigeonhole
import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.TseitinExpander

/-!
# La escalera gris: de la caja negra a la blanca, peldaño por peldaño

La idea de José (24 nov 2026): en el cubo ya había caja negra (solo pregunta, `CuboCostos.lean`) y caja gris (ve la
fórmula pero opera con reglas fijas, `CajaGris.lean`). Falta la blanca, que no es un peldaño más sino el **límite** de la
escalera de grises (`LimiteBlanco.lean`). Aquí se suben peldaños grises con lo que cslib-frontier ya prueba, y se dice en
cada uno si la **conservación** (el costo no baja de un piso, en cada instancia) se sabe o no.

Los `.olean` de cslib-frontier que hacen falta (DPLL, planos de corte, Tseitin, Nullstellensatz, cálculo polinomial,
expansores) no estaban compilados en esta copia; se compilaron uno por uno con `lake build <módulo>` el 25 nov 2026, sin
compilar cslib-frontier entero.

## Lo que se prueba

1. **En abstracto** (§1). Un peldaño es `Peldano ι := ι → ℕ → Prop` (la instancia `i` tiene prueba de tamaño `≤ s`).
   `Conserva R c` (piso), `Corto R a` (techo) y `Simula Q P f` (sobrecosto). `piso_por_simulacion`: el piso **baja** de un
   peldaño fuerte a uno débil. `separa`: si `P` es corto y `Q` conserva, toda simulación de `P` por `Q` paga
   `c i ≤ f i (a i)`. `piso_le_techo`: piso y techo no se cruzan.
2. **Cuatro peldaños sobre el palomar** `PHP^{n+1}_n` (§2): `arbol`, `resolucion`, `conMemoria m` (de `CajaGris.lean`) y
   `planos`. Probado: `conserva_arbol` (`(n/2+1)^(n/2)`, Beyersdorff–Galesi–Lauria), `conserva_resolucion` (`2^(n/24)`,
   Haken), `conserva_arbol_haken` (el piso de Haken baja al árbol por `resolucion_simula_arbol`),
   `conserva_conMemoria` (el mismo piso en todo espacio, por `palomar_largoMinimo`), `planos_simula_resolucion`,
   `corto_planos` (techo `(n+1)(n+2)²`, Cook–Coullard–Turán), `no_conserva_planos` (en planos de corte el palomar **no**
   conserva `2^(n/24)`) y `separa_resolucion_planos`.
3. **DPLL, la caja gris que busca** (§3). `dpll_busca`: `solve` de cslib-frontier devuelve un modelo verdadero o un
   certificado LRAT aceptado. `dpll_paga_palomar`: para **todo** `n`, su certificado sobre `formulaPal n` tiene entre
   `(n/2+1)^(n/2)` y `2^N` pasos. Se paga en cada instancia, no solo en infinitas. Es la salida, no el tiempo.
4. **Tseitin: la fórmula como grafo** (§4). `Cadena P k S b`: eliminación gaussiana como cadena de `k` sumas de
   ecuaciones; `Cadena.sana`, `Cadena.refuta`, `Cadena.derives` (es una derivación de `ParitySystem.Derives` sin límite
   de ancho). `cadena_tseitin`: con carga impar, `|V|` sumas dan `0 = 1` (cada arista está en dos vértices; la prueba
   usa `vacio_de_paridad_nula`). `carga_impar`: en un grafo conexo, sin modelo es carga impar. `tseitin_separa`: para la
   **misma** familia de expansores (`exists_expander_tseitinFormula`), Gauss refuta en `n` sumas y Nullstellensatz en
   característica 2 en grado `120`, mientras que cálculo polinomial con `2 ≠ 0` pide grado `≥ n / 36000`, y resolución
   ancho `≥ n / 18000` y tamaño `≥ exp (n / (960 · 36000²))`.
5. **El cubo algebraico** (§5). `AlcanzablePC F e y`: refutación de cálculo polinomial con grado `≤ e` y tamaño `≤ 2^y`;
   `alcanzablePC_mono`, `AlcanzablePC.grado`. `LeyGradoTamano K c` es la ley de Impagliazzo–Pudlák–Sgall (1999) como
   **proposición abierta** (no está en cslib-frontier). `cubo_algebraico_tseitin`: en Tseitin sobre expansores el eje del
   grado está probado (`n ≤ 36000 e` en todo punto) y, **si** vale la ley, el tamaño cumple
   `(n/36000 − 120)² ≤ c · 120 n · (log s + 1)`.
6. **Suma de cuadrados** (§6). `palomar_sos_contra_resolucion`: el palomar se refuta en grado 2 (Positivstellensatz)
   mientras resolución pide `2^(n/24)`. `paridad_dificil_sos`: la paridad sobre expansores pide grado `≥ n / 18000`
   (Grigoriev, por el lema de Schoenebeck, como está en cslib-frontier).

## Lo que NO se prueba

* Ningún tiempo de máquina: las cotas de DPLL son del certificado que devuelve, no de sus pasos.
* La separación de árbol contra resolución general (otra familia; Ben-Sasson, Impagliazzo y Wigderson, de memoria) no
  está en cslib-frontier y no se hizo. Sobre el palomar los dos peldaños tienen pisos exponenciales.
* La ley grado–tamaño queda abierta como `def`. IPS (Grochow–Pitassi) no está en cslib-frontier. En §6 el sistema de
  paridad difícil para suma de cuadrados lo da cslib-frontier sin nombrar el grafo, así que no se pone lado a lado con
  la cadena de Gauss sobre **la misma** instancia (eso sí se hace en §4 para resolución y cálculo polinomial).
* Nada arriba de planos de corte y cálculo polinomial: Frege y los circuitos generales no tienen cotas.
-/

namespace Sagitta.Map.Borde.EscaleraGris

open Sagitta.Map.Tiempo Sagitta.Map.Tiempo.CajaGris

open Cslib Cslib.Logic.PL Cslib.Logic.PL.CNF

/-! ## 1. Peldaños, cotas y simulaciones, en abstracto -/

/-- Un **peldaño** de la escalera gris sobre una familia de instancias `ι`: `R i s` dice que la instancia `i` tiene una
prueba de tamaño `≤ s` con las reglas fijas del peldaño. -/
abbrev Peldano (ι : Type*) := ι → ℕ → Prop

variable {ι : Type*}

/-- **La conservación en un peldaño**, con piso `c`: toda prueba de la instancia `i` cuesta al menos `c i`. -/
def Conserva (R : Peldano ι) (c : ι → ℕ) : Prop := ∀ i s, R i s → c i ≤ s

/-- **El peldaño es corto** en la familia, con techo `a`: cada instancia tiene una prueba de tamaño `≤ a i`. -/
def Corto (R : Peldano ι) (a : ι → ℕ) : Prop := ∀ i, R i (a i)

/-- `Q` **simula** a `P` con sobrecosto `f`: una prueba de tamaño `s` en `P` se vuelve una de tamaño `f i s` en `Q`. -/
def Simula (Q P : Peldano ι) (f : ι → ℕ → ℕ) : Prop := ∀ i s, P i s → Q i (f i s)

/-- **El piso baja por la simulación**: si `Q` simula a `P` y en `Q` se conserva `c`, una prueba de tamaño `s` en `P`
cumple `c i ≤ f i s`. Las cotas inferiores bajan de un peldaño fuerte a uno débil, nunca al revés. -/
theorem piso_por_simulacion {Q P : Peldano ι} {f : ι → ℕ → ℕ} {c : ι → ℕ} (hs : Simula Q P f) (hQ : Conserva Q c)
    {i : ι} {s : ℕ} (h : P i s) : c i ≤ f i s :=
  hQ i _ (hs i s h)

/-- **La separación de dos peldaños**: si `P` es corto con techo `a` y `Q` conserva `c`, toda simulación de `P` por `Q`
paga `c i ≤ f i (a i)`. Es la forma de `two_pow_le_of_forall_refutableInSize_pigeonhole` de cslib-frontier, en
abstracto. -/
theorem separa {Q P : Peldano ι} {f : ι → ℕ → ℕ} {a c : ι → ℕ} (hP : Corto P a) (hQ : Conserva Q c)
    (hs : Simula Q P f) (i : ι) : c i ≤ f i (a i) :=
  piso_por_simulacion hs hQ (hP i)

/-- Un peldaño que conserva `c` y es corto con `a` obliga a `c ≤ a`: el piso y el techo no se cruzan. -/
theorem piso_le_techo {R : Peldano ι} {a c : ι → ℕ} (hc : Conserva R c) (ha : Corto R a) (i : ι) : c i ≤ a i :=
  hc i _ (ha i)

/-! ## 2. Cuatro peldaños sobre el palomar `PHP^{n+1}_n` -/

/-- Resolución en árbol (cslib-frontier, `CNF.Derivation`): una derivación de la cláusula vacía con a lo sumo `s` nodos. -/
def arbol : Peldano ℕ := fun n s => ∃ d : (pigeonhole (n + 1) n).Derivation [], d.size ≤ s

/-- Resolución general (cslib-frontier, `CNF.RefutableInSize`): una refutación con a lo sumo `s` líneas. -/
def resolucion : Peldano ℕ := fun n s => (pigeonhole (n + 1) n).RefutableInSize s

/-- Planos de corte (cslib-frontier, `CuttingPlanes.RefutableInSize`) sobre las desigualdades del palomar. -/
def planos : Peldano ℕ := fun n s => CuttingPlanes.RefutableInSize (pigeonhole (n + 1) n).toIneqs s

/-- Resolución con memoria acotada a `m` cláusulas (`CajaGris.lean`): una refutación configuracional de largo `≤ s`. -/
def conMemoria (m : ℕ) : Peldano ℕ := fun n s => RefutaEn (formulaPal n) m s

/-- El árbol se vuelve resolución general sin sobrecosto: un nodo es una línea. -/
theorem resolucion_simula_arbol : Simula resolucion arbol (fun _ s => s) := by
  rintro n s ⟨d, hd⟩
  obtain ⟨ls, hp, hnil, hlen⟩ := d.refutableInSize
  exact ⟨ls, hp, hnil, hlen.trans hd⟩

/-- Planos de corte simulan resolución con sobrecosto lineal en las líneas (`CNF.RefutableInSize.cuttingPlanes`). -/
theorem planos_simula_resolucion :
    Simula planos resolucion (fun n s => (8 * (pigeonhole (n + 1) n).vars.toFinset.card + 1) * s) :=
  fun _ _ h => CNF.RefutableInSize.cuttingPlanes h

/-- **Haken en resolución general** (`two_pow_le_of_refutableInSize_pigeonhole`): el piso `2^(n/24)`. -/
theorem conserva_resolucion : Conserva resolucion (fun n => 2 ^ (n / 24)) :=
  fun _ _ h => two_pow_le_of_refutableInSize_pigeonhole h

/-- **Beyersdorff–Galesi–Lauria en árbol** (`Derivation.pow_half_le_size_pigeonhole`): el piso `(n/2+1)^(n/2)`. -/
theorem conserva_arbol : Conserva arbol (fun n => (n / 2 + 1) ^ (n / 2)) := by
  rintro n s ⟨d, hd⟩
  exact (d.pow_half_le_size_pigeonhole (Nat.lt_succ_self n)).trans hd

/-- El árbol también hereda el piso de Haken, por la simulación: el piso baja. -/
theorem conserva_arbol_haken : Conserva arbol (fun n => 2 ^ (n / 24)) :=
  fun _ _ h => piso_por_simulacion resolucion_simula_arbol conserva_resolucion h

/-- **Con memoria acotada, el mismo piso** en todo espacio `m` (`palomar_largoMinimo` de `CajaGris.lean`). -/
theorem conserva_conMemoria (m : ℕ) : Conserva (conMemoria m) (fun n => 2 ^ (n / 24)) := by
  intro n s h
  have h1 := palomar_largoMinimo n m
  have h2 := largoMinimo_le h
  exact_mod_cast h1.trans h2

/-- **En planos de corte el palomar es corto** (Cook–Coullard–Turán, `refutableInSize_pigeonhole_succ`): techo
`(n+1)(n+2)²`. -/
theorem corto_planos : Corto planos (fun n => (n + 1) * (n + 2) ^ 2) :=
  fun n => CuttingPlanes.refutableInSize_pigeonhole_succ n

/-- **La conservación del palomar se rompe en planos de corte**: ningún piso exponencial vale ahí. Con `n = 24k`, el
techo es polinomial y el piso pedido sería `2^k`. -/
theorem no_conserva_planos : ¬ Conserva planos (fun n => 2 ^ (n / 24)) := by
  intro h
  have key : ∀ k, 2 ^ k ≤ (24 * k + 1) * (24 * k + 2) ^ 2 := fun k => by
    have := piso_le_techo h corto_planos (24 * k)
    simpa [show 24 * k / 24 = k by omega] using this
  have h9 := key 30
  norm_num at h9

/-- **La separación árbol / planos y resolución / planos**, por `separa`: cualquier simulación de planos de corte por
resolución paga `2^(n/24) ≤ f n ((n+1)(n+2)²)`. -/
theorem separa_resolucion_planos {f : ℕ → ℕ → ℕ} (hs : Simula resolucion planos f) (n : ℕ) :
    2 ^ (n / 24) ≤ f n ((n + 1) * (n + 2) ^ 2) :=
  separa corto_planos conserva_resolucion hs n

/-! ## 3. DPLL: la caja gris que busca -/

open Cslib.Algorithms.Lean.DPLL in
/-- **DPLL busca**: devuelve un modelo verdadero si la fórmula es satisfacible, y un certificado que el verificador
LRAT acepta si no lo es (`solve_sat`, `solve_unsat`, `isSat_solve_iff`). -/
theorem dpll_busca (φ : CNF ℕ) :
    (∃ σ, solve φ = .sat σ ∧ φ.eval σ = true) ∨
      (¬ φ.Satisfiable ∧ ∃ cert, solve φ = .unsat cert ∧ φ.checkLRAT cert = true) := by
  cases hs : solve φ with
  | sat σ => exact Or.inl ⟨σ, rfl, solve_sat hs⟩
  | unsat cert =>
    refine Or.inr ⟨fun hsat => ?_, cert, rfl, solve_unsat hs⟩
    have := (isSat_solve_iff φ).2 hsat
    rw [hs] at this
    exact Bool.false_ne_true this

open Cslib.Algorithms.Lean.DPLL in
/-- **DPLL paga en cada instancia del palomar**: para **todo** `n` (no solo para infinitos), la salida de DPLL sobre
`formulaPal n` (el palomar numerado de `CajaGris.lean`) es un certificado con al menos `(n/2+1)^(n/2)` pasos y a lo sumo
`2^N`, con `N` el número de variables. Es una cota de la salida, no del tiempo: el tiempo es al menos lo que se escribe,
pero cslib-frontier no tiene un modelo de costo para `solve`. -/
theorem dpll_paga_palomar (n : ℕ) :
    ∃ cert, solve (formulaPal n) = .unsat cert ∧ (n / 2 + 1) ^ (n / 2) ≤ cert.size ∧
      cert.size ≤ 2 ^ (CNF.vars (formulaPal n)).toFinset.card := by
  obtain ⟨cert, hs, hle⟩ := pow_half_le_size_solve_pigeonhole (ordenPal_inj n) (Nat.lt_succ_self n)
  exact ⟨cert, hs, hle, size_le_of_solve_eq_unsat hs⟩

/-! ## 4. Tseitin: la fórmula como grafo, y dos peldaños que se separan -/

section Tseitin

open Finset

/-- **Eliminación gaussiana como cadena**: `Cadena P k S b` dice que la ecuación `⊕_{i ∈ S} xᵢ = b` se obtiene sumando
`k` ecuaciones de `P`, una tras otra, a partir de `0 = 0`. Es el peldaño algebraico más simple sobre ecuaciones de
paridad: ve la fórmula como un sistema lineal módulo 2. -/
inductive Cadena {σ : Type*} [DecidableEq σ] (P : ParitySystem σ) : ℕ → Finset σ → Bool → Prop
  | cero : Cadena P 0 ∅ false
  | suma {k : ℕ} {S : Finset σ} {b : Bool} {e : ParityEquation σ} :
      Cadena P k S b → e ∈ P → Cadena P (k + 1) (symmDiff e.vars S) (e.rhs ^^ b)

variable {σ : Type*} [DecidableEq σ] {P : ParitySystem σ}

/-- **La cadena es sana**: lo que deriva lo cumple todo modelo del sistema. -/
theorem Cadena.sana {k : ℕ} {S : Finset σ} {b : Bool} (h : Cadena P k S b) {a : σ → Bool} (ha : P.Holds a) :
    parityOn S a = b := by
  induction h with
  | cero => exact parityOn_empty a
  | suma _ he ih => rw [parityOn_symmDiff, ih, ha _ he]

/-- Una cadena que llega a `0 = 1` refuta: el sistema no tiene modelo. -/
theorem Cadena.refuta {k : ℕ} (h : Cadena P k ∅ true) (a : σ → Bool) : ¬ P.Holds a := fun ha => by
  have := h.sana ha
  rw [parityOn_empty] at this
  exact Bool.false_ne_true this

/-- **La cadena es una derivación de cslib-frontier** (`ParitySystem.Derives`) con ancho igual al número de
variables: la eliminación gaussiana no tiene límite de ancho. -/
theorem Cadena.derives [Fintype σ] {k : ℕ} {S : Finset σ} {b : Bool} (h : Cadena P k S b) :
    P.Derives (Fintype.card σ) S b := by
  induction h with
  | cero => exact .empty
  | @suma k S b e _ he ih =>
    exact .symmDiff (.mem (by simpa using he) (card_le_univ _)) ih (card_le_univ _)

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- La suma de las ecuaciones de los vértices de una lista. -/
def sumaVars (ends : E → Sym2 V) : List V → Finset E
  | [] => ∅
  | v :: L => symmDiff (Multigraph.incidence ends v) (sumaVars ends L)

/-- El lado derecho de esa suma. -/
def sumaCargas (χ : V → Bool) : List V → Bool
  | [] => false
  | v :: L => χ v ^^ sumaCargas χ L

theorem cadena_lista (ends : E → Sym2 V) (χ : V → Bool) (L : List V) :
    Cadena (ParitySystem.tseitin ends χ) L.length (sumaVars ends L) (sumaCargas χ L) := by
  induction L with
  | nil => exact .cero
  | cons v L ih => exact .suma (e := ⟨Multigraph.incidence ends v, χ v⟩) ih (ParitySystem.incidence_mem_tseitin v)

omit [Fintype V] in
theorem parityOn_sumaVars (ends : E → Sym2 V) (L : List V) (a : E → Bool) :
    parityOn (sumaVars ends L) a = sumaCargas (fun v => parityOn (Multigraph.incidence ends v) a) L := by
  induction L with
  | nil => simp [sumaVars, sumaCargas]
  | cons v L ih => simp [sumaVars, sumaCargas, parityOn_symmDiff, ih]

omit [DecidableEq V] in
theorem sumaCargas_toList (x : V → Bool) : sumaCargas x (univ : Finset V).toList = parityOn univ x := by
  classical
  suffices h : ∀ L : List V, L.Nodup → sumaCargas x L = parityOn L.toFinset x by
    simpa using h _ (Finset.nodup_toList _)
  intro L hL
  induction L with
  | nil => simp [sumaCargas]
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    rw [List.toFinset_cons, parityOn_insert (by simpa using hL.1), sumaCargas, ih hL.2]

omit [Fintype E] [DecidableEq E] in
/-- Un conjunto cuya paridad es `0` bajo toda asignación es vacío. -/
theorem vacio_de_paridad_nula {S : Finset E} (h : ∀ a : E → Bool, parityOn S a = false) : S = ∅ := by
  classical
  by_contra hne
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have h1 := h (fun j => decide (j = e))
  rw [parityOn_eq_xor_erase he] at h1
  have h2 : parityOn (S.erase e) (fun j => decide (j = e)) = false := by
    rw [parityOn_congr (y := fun _ => false) (fun j hj => by simp [Finset.ne_of_mem_erase hj])]
    rw [parityOn_eq_sum]
    exact Finset.sum_eq_zero fun _ _ => rfl
  simp [h2] at h1

/-- **Gauss refuta Tseitin en `|V|` sumas**: con carga total impar, sumar las ecuaciones de todos los vértices da
`0 = 1`, porque cada arista aparece en dos vértices. No hace falta que el grafo sea conexo ni expansor. -/
theorem cadena_tseitin {ends : E → Sym2 V} {χ : V → Bool} (h : parityOn univ χ = true) :
    Cadena (ParitySystem.tseitin ends χ) (Fintype.card V) ∅ true := by
  have hc := cadena_lista ends χ (univ : Finset V).toList
  rw [Finset.length_toList, sumaCargas_toList, h] at hc
  have hS : sumaVars ends (univ : Finset V).toList = ∅ := vacio_de_paridad_nula fun a => by
    rw [parityOn_sumaVars, sumaCargas_toList]
    exact Tseitin.parityOn_univ_parityOn_incidence_eq_false a
  rwa [hS] at hc

/-- Sobre un grafo conexo, la fórmula de Tseitin sin modelo tiene carga total impar. -/
theorem carga_impar {ends : E → Sym2 V} {χ : V → Bool} (hG : (Multigraph.toSimpleGraph ends).Connected)
    (h : ¬ (CNF.tseitinFormula ends χ).Satisfiable) : parityOn univ χ = true := by
  by_contra hχ
  rw [Bool.not_eq_true] at hχ
  obtain ⟨a, ha⟩ := (ParitySystem.exists_holds_tseitin_iff hG).2 hχ
  exact h ⟨a, (ParitySystem.holds_tseitin_iff_eval_tseitinFormula a).1 ha⟩

end Tseitin

section Separacion

open Finset Cslib.Logic.PL.Algebraic

/-- **Tseitin sobre expansores: cuatro peldaños, una sola familia.** Para cada `n ≥ 4392000` hay un grafo de `n`
vértices y a lo sumo `120 n` aristas, de grado `≤ 120`, y una carga sin solución, tales que, para la **misma** fórmula:

1. (fácil, Gauss) el sistema de paridad se refuta sumando `n` ecuaciones (`cadena_tseitin`);
2. (fácil, Nullstellensatz en característica 2) hay refutación de grado `≤ 120`, sobre cualquier anillo conmutativo de
   característica 2 (`ns_refutableInDegree_tseitinFormula_of_charP_two`);
3. (difícil, cálculo polinomial con `2 ≠ 0`) toda refutación con los axiomas booleanos tiene grado `d` con
   `n ≤ 36000 d` (`minBalancedCut_le_two_mul_of_pc_refutableInDegree`);
4. (difícil, resolución) todo ancho cumple `n / 18000 ≤ w` (`minBalancedCut_le_of_refutableInWidth`) y todo tamaño
   cumple `exp (n / (960 · 36000²)) ≤ s` (`exp_le_of_refutableInSize`).

La dificultad la da el grafo (su expansión) para las reglas fijas que no ven la paridad; el álgebra en característica 2
la esquiva. -/
theorem tseitin_separa (n : ℕ) (hn : 4392000 ≤ n) :
    ∃ m ≤ 120 * n, ∃ (ends : Fin m → Sym2 (Fin n)) (χ : Fin n → Bool),
      ¬ (CNF.tseitinFormula ends χ).Satisfiable ∧
      Cadena (ParitySystem.tseitin ends χ) n ∅ true ∧
      (∀ (R : Type) [CommRing R] [CharP R 2],
        NS.RefutableInDegree ((CNF.tseitinFormula ends χ).toBoolPolys R) 120) ∧
      (∀ (K : Type) [Field K], (2 : K) ≠ 0 → ∀ d,
        PC.RefutableInDegree ((CNF.tseitinFormula ends χ).toBoolPolys K ++ boolAxioms (Fin m) K) d →
          n ≤ 36000 * d) ∧
      (∀ w, (CNF.tseitinFormula ends χ).RefutableInWidth w → (n : ℝ) / 18000 ≤ w) ∧
      (∀ s, (CNF.tseitinFormula ends χ).RefutableInSize s → Real.exp (n / (960 * 36000 ^ 2)) ≤ s) := by
  obtain ⟨m, hm, ends, χ, hdeg, hG, he, -, -, -, hunsat⟩ :=
    Tseitin.exists_expander_tseitinFormula n (by omega)
  have hχ := carga_impar hG hunsat
  refine ⟨m, hm, ends, χ, hunsat, by simpa using cadena_tseitin (ends := ends) hχ,
    fun R _ _ => CNF.ns_refutableInDegree_tseitinFormula_of_charP_two hdeg hχ, ?_, ?_, ?_⟩
  · intro K _ h2 d hd
    have h' : (Multigraph.minBalancedCut ends : ℝ) ≤ 2 * d := by
      exact_mod_cast Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree h2 hG hd
    have : (n : ℝ) ≤ 36000 * d := by linarith
    exact_mod_cast this
  · intro w hw
    have := Tseitin.minBalancedCut_le_of_refutableInWidth hG hw
    have h' : (Multigraph.minBalancedCut ends : ℝ) ≤ w := by exact_mod_cast this
    linarith
  · intro s hs
    have hn' : (4392000 : ℝ) ≤ n := by exact_mod_cast hn
    have hke : 120 + 2 ≤ Multigraph.minBalancedCut ends := by
      have : (122 : ℝ) ≤ Multigraph.minBalancedCut ends := by linarith
      exact_mod_cast this
    have hsize := Tseitin.exp_le_of_refutableInSize hG hdeg (by simpa using hm) hke hs
    refine le_trans (Real.exp_le_exp.2 ?_) hsize
    have hx : (n : ℝ) / 36000 ≤ (Multigraph.minBalancedCut ends : ℝ) - 120 - 2 := by linarith
    have hsq := pow_le_pow_left₀ (by positivity) hx 2
    have hnpos : (0 : ℝ) < n := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith

end Separacion

/-! ## 5. El cubo algebraico: grado contra tamaño, con `x² = x` forzado -/

section CuboAlgebraico

open Finset Cslib.Logic.PL.Algebraic

variable {V K : Type*} [Field K]

/-- **Un punto del cubo algebraico** para el sistema `F`: hay una refutación de cálculo polinomial con grado `≤ e` (el
eje de la memoria: cuánto se guarda en cada línea) y tamaño `≤ 2^y` (el eje del tiempo, en bits: monomios escritos).
Es la forma de `AlcanzableCubo` de `CuboCostos.lean`, con el eje de la descripción fijo (las reglas no cambian). -/
def AlcanzablePC (F : List (MvPolynomial V K)) (e y : ℕ) : Prop :=
  ∃ ls, PC.IsProof F ls ∧ 1 ∈ ls ∧ PC.degree ls ≤ e ∧ PC.size ls ≤ 2 ^ y

/-- La región es cerrada hacia arriba, como la del cubo de caja negra. -/
theorem alcanzablePC_mono {F : List (MvPolynomial V K)} {e y e' y' : ℕ} (h : AlcanzablePC F e y) (he : e ≤ e')
    (hy : y ≤ y') : AlcanzablePC F e' y' := by
  obtain ⟨ls, hp, h1, hd, hs⟩ := h
  exact ⟨ls, hp, h1, hd.trans he, hs.trans (Nat.pow_le_pow_right two_pos hy)⟩

/-- Un punto del cubo da una refutación de grado `≤ e`: el eje del grado es una cara. -/
theorem AlcanzablePC.grado {F : List (MvPolynomial V K)} {e y : ℕ} (h : AlcanzablePC F e y) :
    PC.RefutableInDegree F e := by
  obtain ⟨ls, hp, h1, hd, -⟩ := h
  exact ⟨ls, hp, h1, hd⟩

/-- **La ley grado–tamaño, como proposición abierta.** Es el teorema de Impagliazzo, Pudlák y Sgall (1999), citado de
memoria: si los axiomas tienen grado `≤ k` e incluyen `xᵢ² − xᵢ`, una refutación de tamaño `s` da otra de grado `e` con
`(e − k)² ≤ c · m · (log s + 1)`, con `m` el número de variables. Aquí **no se prueba**: cslib-frontier no lo tiene.
Es la forma algebraica de la ley `m ≤ x + min y (e − 1)` del cubo: un grado alto obliga a un tamaño alto. -/
def LeyGradoTamano (K : Type*) [Field K] (c : ℕ) : Prop :=
  ∀ (m k s : ℕ) (F : List (MvPolynomial (Fin m) K)), (∀ f ∈ F, f.totalDegree ≤ k) →
    (∀ f ∈ boolAxioms (Fin m) K, f ∈ F) → PC.RefutableInSize F s →
      ∃ e, PC.RefutableInDegree F e ∧ (e - k) ^ 2 ≤ c * m * (Nat.log 2 s + 1)

/-- **El cubo algebraico de Tseitin.** Para la familia de expansores de `tseitin_separa`, con `n ≥ 4392000`, sobre
todo cuerpo con `2 ≠ 0`:

1. (probado) el eje del grado: todo punto `(e, y)` del cubo cumple `n ≤ 36000 e`;
2. (condicional) si vale la ley grado–tamaño con constante `c`, todo tamaño `s` de refutación cumple
   `(n / 36000 − 120)² ≤ c · 120 n · (log s + 1)`: el piso del grado se vuelve piso del tamaño, `log s = Ω(n)`. -/
theorem cubo_algebraico_tseitin (n : ℕ) (hn : 4392000 ≤ n) :
    ∃ m ≤ 120 * n, ∃ (ends : Fin m → Sym2 (Fin n)) (χ : Fin n → Bool),
      ¬ (CNF.tseitinFormula ends χ).Satisfiable ∧
      ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
        (∀ e y, AlcanzablePC ((CNF.tseitinFormula ends χ).toBoolPolys K ++ boolAxioms (Fin m) K) e y →
          n ≤ 36000 * e) ∧
        (∀ c, LeyGradoTamano K c → ∀ s,
          PC.RefutableInSize ((CNF.tseitinFormula ends χ).toBoolPolys K ++ boolAxioms (Fin m) K) s →
            (n / 36000 - 120) ^ 2 ≤ c * (120 * n) * (Nat.log 2 s + 1)) := by
  obtain ⟨m, hm, ends, χ, hdeg, hG, he, -, hlen, -, hunsat⟩ :=
    Tseitin.exists_expander_tseitinFormula n (by omega)
  have hpiso : ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ∀ d,
      PC.RefutableInDegree ((CNF.tseitinFormula ends χ).toBoolPolys K ++ boolAxioms (Fin m) K) d →
        n ≤ 36000 * d := by
    intro K _ h2 d hd
    have h' : (Multigraph.minBalancedCut ends : ℝ) ≤ 2 * d := by
      exact_mod_cast Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree h2 hG hd
    have : (n : ℝ) ≤ 36000 * d := by linarith
    exact_mod_cast this
  refine ⟨m, hm, ends, χ, hunsat, fun K _ h2 => ⟨fun e y h => hpiso K h2 e h.grado, ?_⟩⟩
  intro c hc s hs
  have hk : ∀ f ∈ (CNF.tseitinFormula ends χ).toBoolPolys K ++ boolAxioms (Fin m) K, f.totalDegree ≤ 120 := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨cl, hcl, rfl⟩ := List.mem_map.1 hf
      exact (Clause.totalDegree_toBoolPoly_le cl).trans (hlen cl hcl)
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hf
      exact (totalDegree_boolAxiom_le i).trans (by norm_num)
  obtain ⟨e, he', hle⟩ := hc m 120 s _ hk (fun f hf => List.mem_append_right _ hf) hs
  have h1 : n / 36000 ≤ e := by have := hpiso K h2 e he'; omega
  have h2' : (n / 36000 - 120) ^ 2 ≤ (e - 120) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : c * m * (Nat.log 2 s + 1) ≤ c * (120 * n) * (Nat.log 2 s + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)
  omega

end CuboAlgebraico

/-! ## 6. Suma de cuadrados: el palomar es fácil y la paridad difícil -/

section SumaDeCuadrados

open Finset Cslib.Logic.PL.SOS.Psatz

/-- **El palomar, en dos peldaños que no se parecen**: suma de cuadrados (Positivstellensatz) lo refuta en grado 2
sobre todo anillo ordenado (`refutableInDegree_two_pigeonhole`), y resolución pide `2^(n/24)` líneas (Haken). -/
theorem palomar_sos_contra_resolucion (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (n : ℕ) :
    RefutableInDegree (cnfIneqs (pigeonhole (n + 1) n) : Set (MvPolynomial (Fin (n + 1) × Fin n) R))
        (booleanAxioms (Fin (n + 1) × Fin n) R) 2 ∧
      Conserva resolucion (fun n => 2 ^ (n / 24)) :=
  ⟨refutableInDegree_two_pigeonhole (Nat.lt_succ_self n), conserva_resolucion⟩

/-- **La paridad sobre expansores es difícil para suma de cuadrados** (Grigoriev 2001, vía el lema de Schoenebeck;
`ParitySystem.exists_forall_sos_refutableInDegree_le` de cslib-frontier): grado `≥ n / 18000`. Es el mismo sistema
que Gauss refuta en `n` sumas (`cadena_tseitin`); aquí cslib-frontier lo da sin nombrar el grafo, así que la
cadena se construye aparte. -/
theorem paridad_dificil_sos :
    ∀ n ≥ 2, ∃ m ≤ 120 * n, ∃ P : ParitySystem (Fin m),
      P.length = n ∧ (∀ e ∈ P, #e.vars ≤ 120) ∧ (∀ a, ¬ P.Holds a) ∧
      ∀ (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (d : ℕ),
        Cslib.Logic.PL.SOS.RefutableInDegree (P.toPolys R) d → n ≤ 18000 * d :=
  fun n hn => ParitySystem.exists_forall_sos_refutableInDegree_le n hn

end SumaDeCuadrados

/-! ## Controles -/

section Controles

open Finset

/-- Control de §2: en `n = 24 · 30` el piso `2^30` supera al techo de planos de corte; es el punto que usa
`no_conserva_planos`. -/
example : (2 : ℕ) ^ 30 > (24 * 30 + 1) * (24 * 30 + 2) ^ 2 := by norm_num

/-- Control de §3: DPLL sobre el palomar con 4 palomares y 3 hoyos: certificado de al menos `3^2 = 9` pasos. -/
example : ∃ cert, Cslib.Algorithms.Lean.DPLL.solve (formulaPal 4) = .unsat cert ∧ 9 ≤ cert.size := by
  obtain ⟨cert, h, h1, -⟩ := dpll_paga_palomar 4
  exact ⟨cert, h, by simpa using h1⟩

/-- Control de §4: una cadena **no** llega a `0 = 1` en un sistema con modelo (la ecuación `x₀ = 1`). -/
example (k : ℕ) : ¬ Cadena ([⟨{0}, true⟩] : ParitySystem (Fin 1)) k ∅ true := fun h =>
  h.refuta (fun _ => true) (by intro e he; rw [List.mem_singleton] at he; subst he; simp [parityOn])

/-- Control de §4: el triángulo con carga en un solo vértice se refuta con 3 sumas. -/
example : Cadena (ParitySystem.tseitin (fun e : Fin 3 => (s(e, e + 1) : Sym2 (Fin 3)))
    (fun v => decide (v = 0))) 3 ∅ true := by
  have := cadena_tseitin (ends := fun e : Fin 3 => (s(e, e + 1) : Sym2 (Fin 3))) (χ := fun v => decide (v = 0))
    (by simp [parityOn, filter_eq'])
  simpa using this

/-- Control de §5: el sistema `[1]` está en el cubo algebraico en `(0, 0)`: una línea, grado 0, un monomio. -/
example : AlcanzablePC ([1] : List (MvPolynomial (Fin 1) ℚ)) 0 0 :=
  ⟨[1], .mem .nil (by simp), by simp, by simp [PC.degree], by simp [PC.size]⟩

/- Mutantes (probados en /tmp/claude-noche/MutEsc*.lean, 25 nov 2026; todos fallan, como debe ser):
   * MutEsc1: `cadena_tseitin` con la hipótesis `parityOn univ χ = false`: el `rwa` final no cierra (la carga par no da `0 = 1`).
   * MutEsc2: `no_conserva_planos` con `key 10` en vez de `key 30`: `norm_num` no cierra (`2^10 ≤ 241 · 242²` es cierto).
   * MutEsc3: `vacio_de_paridad_nula` con `∃ a` en vez de `∀ a`: la prueba no encuentra la asignación indicadora. -/

end Controles

end Sagitta.Map.Borde.EscaleraGris
