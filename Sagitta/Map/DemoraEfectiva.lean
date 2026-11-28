import Sagitta.Map.ArbolElecciones
import Mathlib.Data.Nat.Log

/-!
# La demora efectiva: mirar hacia abajo cuesta lo mismo que tardar

Sobre el modelo de `ArbolElecciones` (la vuelta atrás `buscar`, el detector `det`, la demora). Un detector con demora
`d` que cuesta `t` por llamada se puede cambiar por uno con demora `d − h` que mira `h` niveles hacia abajo, a un costo
de a lo sumo `2^(h+1)` llamadas por evaluación. Lo que no cambia con ese intercambio es la **demora efectiva**
`d + log₂ t` (sube a lo sumo en 1), no la demora sola.

## Por qué hace falta un horizonte

`Demora` de `ArbolElecciones` es global: vale para todo `k` y todo `p` muerto. Para una fórmula CNF eso es casi siempre
falso, porque un prefijo corto está «muerto con 0 variables por fijar» (`solCNF` de un prefijo parcial es `false`) y
`Demora` le pide entonces al detector que dispare debajo de él. El control `demora_global_degenera` lo muestra con
`todoTrue4`: `detCNF` no tiene `Demora d` para ningún `d`, así que `costo_vivo` no se le aplica a esa fórmula. Por eso
aquí se trabaja con un número fijo `N` de variables:

* `SanoN sol det N`: si `det` dice muerto en un prefijo de largo `≤ N`, ninguna completación a largo `N` es solución.
  Es más débil que `Sano` (`sano_sanoN`).
* `DemoraN sol det N d`: todo prefijo muerto (respecto de las `N − |p|` variables que faltan) es detectado en todas sus
  extensiones de largo `d`, **siempre que quepan** (`|p| + d ≤ N`). Cerca de las hojas no se pide nada: allí el subárbol
  entero ya cuesta menos que `2^(d+1)`. Es más débil que `Demora` (`demora_demoraN`).

## Lo que se prueba

* **La vuelta atrás con horizonte** (`buscar_correctoN`, `costo_vivoN`, `costo_muertoN`, `nodos_le`): con `SanoN` y
  `DemoraN d`, desde un nodo con `k` variables por fijar se visitan a lo sumo `k · 2^(d+1) + 1` nodos si está vivo y
  `2^(d+1) − 1` si está muerto; en todo caso `(k + 1) · 2^(d+1)`.
* **El intercambio** (`anticipa`): `anticipa sol det N h p` declara muerto a `p` si `det` lo dice, o si `p` no es hoja y
  sus dos hijos están anticipados con `h − 1`, o si `p` es hoja (largo `≥ N`) y no es solución.
  - `anticipa_sano`: si `det` es `SanoN`, `anticipa … h` también.
  - `anticipa_demora`: si `det` tiene `DemoraN d` y `h ≤ d`, `anticipa … h` tiene `DemoraN (d − h)`. En particular
    `anticipa … d` tiene demora 0 (`anticipa_perfecto`).
  - `llamadas_cota`: evaluar `anticipa … h p` con corto circuito hace a lo sumo `2^(h+1) − 1` llamadas a `det` o a
    `sol` (`llamadas` cuenta esas llamadas; en las hojas `sol` cuenta como una llamada más).
  - `demora_mono`: al revés, una demora menor siempre sirve como una mayor.
* **El costo con costo por llamada** (`peso`, `peso_le`, `peso_uno`, `llamadas_busqueda`): `peso c` suma el costo
  `c p` de cada nodo que visita la vuelta atrás; con `c ≤ C`, el peso es a lo sumo `nodos · C`, y con `c = 1` es
  `nodos`. Buscar con `anticipa … d` hace a lo sumo `(2k + 1) · 2^(d+1)` evaluaciones de `det` o de `sol` dentro de `anticipa`
  (`busqueda_anticipada`); no se cuenta el `sol` que evalúa `buscar` en sus propias hojas.
* **La demora efectiva** (`demoraEfectiva d t = d + log₂ t`): `costo_demora_efectiva` acota `nodos · t` por
  `(k + 1) · 2^(demoraEfectiva d t + 2)`, y `demoraEfectiva_anticipa` dice que anticipar `h` niveles con
  `h ≤ d` deja `demoraEfectiva (d − h) (2^(h+1) · t) = demoraEfectiva d t + 1`.
* **Demora efectiva logarítmica, búsqueda polinomial** (`busqueda_polinomial`, `anticipar_polinomial`): para una
  familia indexada por `n` con `N n + 1 ≤ A·(n+1)^a`, detectores sanos con `2^(d n) · t n` polinomial dan una búsqueda
  de costo `nodos · t` polinomial; y anticipar `d n` niveles da un detector de demora 0 que cuesta, en llamadas al
  detector base, a lo sumo `2^(d n + 1)`. Un detector de demora 0 es un oráculo de `¬ Vivo` (`oraculo_perfecto`).
  Las cotas con `t` solo dicen algo si `t n ≥ 1`; con `t n = 0` se cumplen sin contenido.
* **No hay una equivalencia con `t` libre** (`oraculo_siempre`): el oráculo clásico de `¬ Vivo` es sano y tiene
  demora 0 para toda familia, así que «existen detectores de demora 0 y costo polinomial», con el costo como etiqueta,
  vale siempre. Una versión con contenido tiene que medir el costo de verdad: en llamadas a un detector base (como
  aquí) o en tiempo de máquina (`Clases.lean`, no hecho).

## Lo que NO se prueba, y lo que es trivial

* Esto es la **autorreducibilidad de SAT vista como demora**: decidir si un prefijo está vivo (demora 0) y encontrar
  una solución son lo mismo salvo un factor lineal, y tardar `d` niveles en ver un error es lo mismo que mirar `d`
  niveles hacia abajo a un costo `2^d`. Nada de esto dice cuánto cuesta construir un detector.
* `t` es un número que se le asigna al detector, no un tiempo medido: «costo polinomial» aquí no es «tiempo polinomial
  en una máquina de Turing». Conectar con P exige las máquinas de `Clases.lean`, y acá no se hace. La parte con
  contenido son `anticipa_sano`, `anticipa_demora` y `llamadas_cota`, que dicen que la etiqueta `2^(d+1) · t` del
  detector anticipado está justificada.
* El orden de las variables es fijo y no hay aprendizaje, como en `ArbolElecciones`.
-/

namespace Sagitta.Map
namespace Tiempo

variable (sol det : List Bool → Bool) (N : ℕ)

/-! ## Sano y demora con horizonte -/

/-- **Sano con horizonte `N`**: si `det` dice muerto en un prefijo de largo `≤ N`, ninguna completación a largo `N`
es solución. -/
def SanoN : Prop := ∀ p : List Bool, p.length ≤ N → det p = true → ¬ Vivo sol (N - p.length) p

/-- **Demora `d` con horizonte `N`**: todo prefijo muerto se detecta en todas sus extensiones de largo `d`, cuando
caben dentro de las `N` variables. -/
def DemoraN (d : ℕ) : Prop :=
  ∀ p : List Bool, p.length + d ≤ N → ¬ Vivo sol (N - p.length) p →
    ∀ q : List Bool, q.length = d → det (p ++ q) = true

theorem sano_sanoN {sol det} (hs : Sano sol det) : SanoN sol det N := fun _ _ hd => sano_muerto hs hd

theorem demora_demoraN {sol det} {d : ℕ} (hd : Demora sol det d) : DemoraN sol det N d :=
  fun p _ hm q hq => hd _ p hm q hq

/-- Una extensión de un prefijo muerto está muerta. -/
theorem muerto_ext {sol} {N : ℕ} {p q : List Bool} (hm : ¬ Vivo sol (N - p.length) p)
    (hl : p.length + q.length ≤ N) : ¬ Vivo sol (N - (p ++ q).length) (p ++ q) := by
  rintro ⟨r, hr, hs⟩
  refine hm ⟨q ++ r, ?_, by simpa using hs⟩
  simp only [List.length_append] at hr ⊢
  omega

/-- **Al revés: una demora menor sirve como una mayor.** -/
theorem demora_mono {sol det} {N d : ℕ} (hd : DemoraN sol det N d) (e : ℕ) : DemoraN sol det N (e + d) := by
  intro p hpl hm q hq
  have hq1 : (q.take e).length = e := by simp [hq]
  have hq2 : (q.drop e).length = d := by simp [hq]
  have hm' := muerto_ext (q := q.take e) hm (by omega)
  have := hd (p ++ q.take e) (by simp; omega) hm' (q.drop e) hq2
  simpa using this

/-! ## La vuelta atrás con horizonte -/

/-- **La vuelta atrás es correcta con un detector sano con horizonte.** -/
theorem buscar_correctoN {sol det} {N : ℕ} (hs : SanoN sol det N) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = N → ((buscar sol det k p).1 = true ↔ Vivo sol k p)
  | 0, p, hk => by
    rw [vivo_cero]
    by_cases hd : det p = true
    · simp only [buscar, hd, ite_true, Bool.false_eq_true, false_iff]
      have := hs p (by omega) hd
      rw [show N - p.length = 0 by omega, vivo_cero] at this
      exact this
    · simp [buscar, hd]
  | k + 1, p, hk => by
    rw [vivo_succ]
    by_cases hd : det p = true
    · simp only [buscar, hd, ite_true, Bool.false_eq_true, false_iff]
      have := hs p (by omega) hd
      rw [show N - p.length = k + 1 by omega, vivo_succ] at this
      exact this
    · have hf := buscar_correctoN hs k (p ++ [false]) (by simp; omega)
      have ht := buscar_correctoN hs k (p ++ [true]) (by simp; omega)
      by_cases ha : (buscar sol det k (p ++ [false])).1 = true
      · simp only [buscar, hd, ha, ite_true, Bool.false_eq_true, ite_false, true_iff]
        exact .inl (hf.mp ha)
      · simp only [buscar, hd, ha, Bool.false_eq_true, ite_false]
        rw [ht]
        constructor
        · exact .inr
        · rintro (h | h)
          · exact absurd (hf.mpr h) ha
          · exact h

/-- **Cota trivial**: cualquier subárbol con `k` variables por fijar cuesta a lo sumo `2^(k+1) − 1` nodos. -/
theorem nodos_cota : ∀ (k : ℕ) (p : List Bool), nodos sol det k p + 1 ≤ 2 ^ (k + 1)
  | 0, p => by unfold nodos buscar; split <;> simp
  | k + 1, p => by
    have cf := nodos_cota k (p ++ [false])
    have ct := nodos_cota k (p ++ [true])
    unfold nodos at cf ct ⊢
    have e2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    rw [e2]
    unfold buscar
    split
    · have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      simp only; omega
    · split <;> simp only <;> omega

/-- **Un nodo muerto cuesta a lo sumo `2^(d+1) − 1`**, también cerca de las hojas. -/
theorem costo_muertoN {sol det} {N d : ℕ} (hd : DemoraN sol det N d) {k : ℕ} {p : List Bool}
    (hk : p.length + k = N) (hm : ¬ Vivo sol k p) : nodos sol det k p + 1 ≤ 2 ^ (d + 1) := by
  by_cases hdk : d ≤ k
  · refine costo_detectado sol det d k p fun q hq => hd p (by omega) ?_ q hq
    rwa [show N - p.length = k by omega]
  · calc nodos sol det k p + 1 ≤ 2 ^ (k + 1) := nodos_cota sol det k p
      _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **La frontera con horizonte**: con `SanoN` y `DemoraN d`, desde un nodo vivo con `k` variables por fijar se
visitan a lo sumo `k · 2^(d+1) + 1` nodos. -/
theorem costo_vivoN {sol det} {N : ℕ} (hs : SanoN sol det N) {d : ℕ} (hd : DemoraN sol det N d) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = N → Vivo sol k p → nodos sol det k p ≤ k * 2 ^ (d + 1) + 1
  | 0, p, _, _ => by unfold nodos buscar; split <;> simp
  | k + 1, p, hk, hv => by
    have hdp : det p = false := by
      by_contra h
      have := hs p (by omega) (Bool.eq_true_of_not_eq_false h)
      rw [show N - p.length = k + 1 by omega] at this
      exact this hv
    have hf := buscar_correctoN hs k (p ++ [false]) (by simp; omega)
    have hpow : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
    unfold nodos
    by_cases hvf : Vivo sol k (p ++ [false])
    · have ha : (buscar sol det k (p ++ [false])).1 = true := hf.mpr hvf
      have ih := costo_vivoN hs hd k (p ++ [false]) (by simp; omega) hvf
      unfold nodos at ih
      simp only [buscar, hdp, ha, Bool.false_eq_true, ite_false, ite_true]
      nlinarith
    · have ha : (buscar sol det k (p ++ [false])).1 = false := by
        cases h : (buscar sol det k (p ++ [false])).1
        · rfl
        · exact absurd (hf.mp h) hvf
      have hvt : Vivo sol k (p ++ [true]) := ((vivo_succ sol k p).mp hv).resolve_left hvf
      have ih := costo_vivoN hs hd k (p ++ [true]) (by simp; omega) hvt
      have hm := costo_muertoN hd (k := k) (p := p ++ [false]) (by simp; omega) hvf
      unfold nodos at ih hm
      simp only [buscar, hdp, ha, Bool.false_eq_true, ite_false]
      nlinarith

/-- **Vivo o muerto, a lo sumo `(k + 1) · 2^(d+1)` nodos.** -/
theorem nodos_le {sol det} {N : ℕ} (hs : SanoN sol det N) {d : ℕ} (hd : DemoraN sol det N d) {k : ℕ}
    {p : List Bool} (hk : p.length + k = N) : nodos sol det k p ≤ (k + 1) * 2 ^ (d + 1) := by
  have hpow : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  by_cases hv : Vivo sol k p
  · have := costo_vivoN hs hd k p hk hv
    nlinarith
  · have := costo_muertoN hd hk hv
    nlinarith

/-! ## El intercambio: mirar `h` niveles hacia abajo -/

/-- **El detector con anticipación**: declara muerto a `p` si `det` lo dice; si no, y `p` no es hoja, si sus dos hijos
están anticipados con un nivel menos; y si `p` es hoja (largo `≥ N`), si no es solución. -/
def anticipa : ℕ → List Bool → Bool
  | 0, p => det p
  | h + 1, p => det p ||
      (if p.length < N then anticipa h (p ++ [false]) && anticipa h (p ++ [true]) else !sol p)

/-- **Anticipar conserva la sanidad.** -/
theorem anticipa_sano {sol det} {N : ℕ} (hs : SanoN sol det N) : ∀ h, SanoN sol (anticipa sol det N h) N
  | 0 => hs
  | h + 1 => by
    intro p hp ha
    unfold anticipa at ha
    rcases Bool.or_eq_true_iff.mp ha with hd | hr
    · exact hs p hp hd
    · split at hr
      · rename_i hlt
        simp only [Bool.and_eq_true] at hr
        have hb : ∀ b : Bool, anticipa sol det N h (p ++ [b]) = true → ¬ Vivo sol (N - p.length - 1) (p ++ [b]) :=
          fun b hb => by
            have := anticipa_sano hs h (p ++ [b]) (by simp; omega) hb
            simpa [Nat.sub_sub] using this
        rw [show N - p.length = (N - p.length - 1) + 1 by omega, vivo_succ]
        rintro (hv | hv)
        · exact hb false hr.1 hv
        · exact hb true hr.2 hv
      · rename_i hlt
        rw [show N - p.length = 0 by omega, vivo_cero]
        simpa using hr

/-- **Cuándo dispara la anticipación**: si toda completación de `x` a largo `N` (dentro de `h` niveles) no es solución,
y `det` dispara en todas las extensiones de largo `h` que caben, entonces `anticipa … h x`. -/
theorem anticipa_de : ∀ (h : ℕ) (x : List Bool), x.length ≤ N →
    (∀ r : List Bool, r.length ≤ h → x.length + r.length = N → sol (x ++ r) = false) →
    (∀ r : List Bool, r.length = h → x.length + h ≤ N → det (x ++ r) = true) →
    anticipa sol det N h x = true
  | 0, x, hx, _, hdet => by
    simpa [anticipa] using hdet [] rfl (by omega)
  | h + 1, x, hx, hsol, hdet => by
    unfold anticipa
    by_cases hd : det x = true
    · simp [hd]
    · split
      · rename_i hlt
        have hb : ∀ b : Bool, anticipa sol det N h (x ++ [b]) = true := fun b => by
          refine anticipa_de h (x ++ [b]) (by simp; omega) (fun r hr hl => ?_) (fun r hr hl => ?_)
          · have := hsol (b :: r) (by simp; omega) (by simp at hl ⊢; omega)
            simpa using this
          · have := hdet (b :: r) (by simp; omega) (by simp at hl ⊢; omega)
            simpa using this
        simp [hb]
      · rename_i hlt
        have := hsol [] (by simp) (by simp; omega)
        simp at this
        simp [this]

/-- **Anticipar `h` niveles baja la demora en `h`.** -/
theorem anticipa_demora {sol det} {N d : ℕ} (hd : DemoraN sol det N d) {h : ℕ} (hh : h ≤ d) :
    DemoraN sol (anticipa sol det N h) N (d - h) := by
  intro p hpl hm q hq
  refine anticipa_de sol det N h (p ++ q) (by simp; omega) (fun r _ hl => ?_) (fun r hr hl => ?_)
  · cases hs : sol (p ++ q ++ r)
    · rfl
    · exact absurd ⟨q ++ r, by simp only [List.length_append] at hl ⊢; omega, by simpa using hs⟩ hm
  · have := hd p (by simp only [List.length_append] at hl; omega) hm (q ++ r) (by simp; omega)
    simpa using this

/-- **Anticipar `d` niveles da un detector perfecto** (demora 0) y sano. -/
theorem anticipa_perfecto {sol det} {N d : ℕ} (hs : SanoN sol det N) (hd : DemoraN sol det N d) :
    SanoN sol (anticipa sol det N d) N ∧ DemoraN sol (anticipa sol det N d) N 0 := by
  refine ⟨anticipa_sano hs d, ?_⟩
  simpa using anticipa_demora hd (le_refl d)

/-! ## Cuánto cuesta anticipar -/

/-- **Las llamadas a `det` (o a `sol` en las hojas) que hace la evaluación con corto circuito de `anticipa … h p`.** -/
def llamadas : ℕ → List Bool → ℕ
  | 0, _ => 1
  | h + 1, p => if det p then 1 else
      if p.length < N then
        1 + llamadas h (p ++ [false]) +
          (if anticipa sol det N h (p ++ [false]) then llamadas h (p ++ [true]) else 0)
      else 2

/-- **Anticipar `h` niveles cuesta a lo sumo `2^(h+1) − 1` llamadas.** -/
theorem llamadas_cota : ∀ (h : ℕ) (p : List Bool), llamadas sol det N h p + 1 ≤ 2 ^ (h + 1)
  | 0, p => by simp [llamadas]
  | h + 1, p => by
    have cf := llamadas_cota h (p ++ [false])
    have ct := llamadas_cota h (p ++ [true])
    have e2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by ring
    have h2 : 2 ≤ 2 ^ (h + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [e2]
    unfold llamadas
    split
    · omega
    · split
      · split <;> omega
      · omega

/-! ## Costo por nodo -/

/-- **El peso de la vuelta atrás**: la suma de `c p` sobre los nodos que visita. -/
def peso (c : List Bool → ℕ) : ℕ → List Bool → ℕ
  | 0, p => c p
  | k + 1, p => if det p then c p else
      if (buscar sol det k (p ++ [false])).1 then c p + peso c k (p ++ [false])
      else c p + peso c k (p ++ [false]) + peso c k (p ++ [true])

/-- **Con costo `1` por nodo, el peso son los nodos.** -/
theorem peso_uno : ∀ (k : ℕ) (p : List Bool), peso sol det (fun _ => 1) k p = nodos sol det k p
  | 0, p => by unfold peso nodos buscar; split <;> rfl
  | k + 1, p => by
    have hf := peso_uno k (p ++ [false])
    have ht := peso_uno k (p ++ [true])
    unfold nodos at hf ht ⊢
    by_cases hd : det p = true
    · simp only [peso, buscar, hd, ite_true]
    · by_cases ha : (buscar sol det k (p ++ [false])).1 = true
      · simp only [peso, buscar, hd, ha, Bool.false_eq_true, ite_false, ite_true]; omega
      · simp only [peso, buscar, hd, ha, Bool.false_eq_true, ite_false]; omega

/-- **Con costo a lo sumo `C` por nodo, el peso es a lo sumo `nodos · C`.** -/
theorem peso_le (c : List Bool → ℕ) {C : ℕ} (hc : ∀ x, c x ≤ C) :
    ∀ (k : ℕ) (p : List Bool), peso sol det c k p ≤ nodos sol det k p * C
  | 0, p => by
    unfold peso nodos buscar; split <;> simpa using hc p
  | k + 1, p => by
    have hf := peso_le c hc k (p ++ [false])
    have ht := peso_le c hc k (p ++ [true])
    have hp := hc p
    unfold nodos at hf ht ⊢
    by_cases hd : det p = true
    · simp only [peso, buscar, hd, ite_true]; omega
    · by_cases ha : (buscar sol det k (p ++ [false])).1 = true
      · simp only [peso, buscar, hd, ha, Bool.false_eq_true, ite_false, ite_true]; nlinarith
      · simp only [peso, buscar, hd, ha, Bool.false_eq_true, ite_false]; nlinarith

/-- **Las llamadas a `det` de una búsqueda con anticipación** son a lo sumo `nodos · 2^(h+1)`. -/
theorem llamadas_busqueda (h k : ℕ) (p : List Bool) :
    peso sol (anticipa sol det N h) (llamadas sol det N h) k p
      ≤ nodos sol (anticipa sol det N h) k p * 2 ^ (h + 1) :=
  peso_le sol _ _ (fun x => by have := llamadas_cota sol det N h x; omega) k p

/-- **Buscar con `anticipa … d` desde un nodo vivo hace a lo sumo `(2k + 1) · 2^(d+1)` llamadas a `det`.** Es la
misma escala que `k · 2^(d+1) + 1` de buscar con `det` directo: la demora se cambió por costo por llamada. -/
theorem busqueda_anticipada {sol det} {N d : ℕ} (hs : SanoN sol det N) (hd : DemoraN sol det N d) {k : ℕ}
    {p : List Bool} (hk : p.length + k = N) (hv : Vivo sol k p) :
    peso sol (anticipa sol det N d) (llamadas sol det N d) k p ≤ (2 * k + 1) * 2 ^ (d + 1) := by
  obtain ⟨hs', hd'⟩ := anticipa_perfecto hs hd
  have h1 := costo_vivoN hs' hd' k p hk hv
  have h2 := llamadas_busqueda sol det N d k p
  have : nodos sol (anticipa sol det N d) k p ≤ 2 * k + 1 := by simpa [mul_comm] using h1
  calc _ ≤ _ := h2
    _ ≤ (2 * k + 1) * 2 ^ (d + 1) := Nat.mul_le_mul_right _ this

/-! ## La demora efectiva -/

/-- **La demora efectiva**: la demora más el logaritmo del costo por llamada. -/
def demoraEfectiva (d t : ℕ) : ℕ := d + Nat.log 2 t

theorem log_dos_pow_mul (t : ℕ) (ht : t ≠ 0) : ∀ m : ℕ, Nat.log 2 (2 ^ m * t) = m + Nat.log 2 t
  | 0 => by simp
  | m + 1 => by
    have hne : 2 ^ m * t ≠ 0 := Nat.mul_ne_zero (by positivity) ht
    rw [show 2 ^ (m + 1) * t = 2 ^ m * t * 2 by ring, Nat.log_mul_base (by norm_num) hne, log_dos_pow_mul t ht m]
    ring

/-- **La búsqueda cuesta `≤ (k + 1) · 2^(demoraEfectiva + 2)`**, contando `t` por nodo. -/
theorem costo_demora_efectiva {sol det} {N : ℕ} (hs : SanoN sol det N) {d : ℕ} (hd : DemoraN sol det N d)
    (t : ℕ) {k : ℕ} {p : List Bool} (hk : p.length + k = N) :
    nodos sol det k p * t ≤ (k + 1) * 2 ^ (demoraEfectiva d t + 2) := by
  have h1 := nodos_le hs hd hk
  have h2 : t ≤ 2 ^ (Nat.log 2 t + 1) := (Nat.lt_pow_succ_log_self (by norm_num) t).le
  have e : 2 ^ (demoraEfectiva d t + 2) = 2 ^ (d + 1) * 2 ^ (Nat.log 2 t + 1) := by
    unfold demoraEfectiva; rw [← pow_add]; ring_nf
  rw [e, ← mul_assoc]
  exact Nat.mul_le_mul h1 h2

/-- **La demora efectiva no cambia al anticipar** (salvo `+1`): mirar `h` niveles hacia abajo baja la demora en `h` y
sube el costo por llamada a `2^(h+1) · t`. -/
theorem demoraEfectiva_anticipa {d h t : ℕ} (hh : h ≤ d) (ht : t ≠ 0) :
    demoraEfectiva (d - h) (2 ^ (h + 1) * t) = demoraEfectiva d t + 1 := by
  unfold demoraEfectiva
  rw [log_dos_pow_mul t ht]
  omega

/-! ## Demora efectiva y búsqueda polinomial -/

/-- **Demora efectiva logarítmica da una búsqueda polinomial.** Si `N n + 1 ≤ A·(n+1)^a` y `2^(d n) · t n ≤
C·(n+1)^c`, la búsqueda desde la raíz cuesta `nodos · t ≤ 2·A·C·(n+1)^(a+c)`, haya o no solución. -/
theorem busqueda_polinomial (sol det : ℕ → List Bool → Bool) (N d t : ℕ → ℕ)
    (hs : ∀ n, SanoN (sol n) (det n) (N n)) (hd : ∀ n, DemoraN (sol n) (det n) (N n) (d n))
    {A a C c : ℕ} (hN : ∀ n, N n + 1 ≤ A * (n + 1) ^ a) (hc : ∀ n, 2 ^ d n * t n ≤ C * (n + 1) ^ c) (n : ℕ) :
    nodos (sol n) (det n) (N n) [] * t n ≤ 2 * A * C * (n + 1) ^ (a + c) := by
  have h1 := nodos_le (hs n) (hd n) (k := N n) (p := []) (by simp)
  calc nodos (sol n) (det n) (N n) [] * t n ≤ (N n + 1) * 2 ^ (d n + 1) * t n := Nat.mul_le_mul_right _ h1
    _ = 2 * (N n + 1) * (2 ^ d n * t n) := by ring
    _ ≤ 2 * (A * (n + 1) ^ a) * (C * (n + 1) ^ c) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (hN n)) (hc n)
    _ = 2 * A * C * (n + 1) ^ (a + c) := by ring

/-- **Anticipar da demora 0 con costo por llamada polinomial**: el detector `anticipa … (d n)` es sano, tiene demora
0, cada evaluación hace a lo sumo `2^(d n + 1)` llamadas, y con `t n` por llamada cuesta `≤ 2·C·(n+1)^c`. -/
theorem anticipar_polinomial (sol det : ℕ → List Bool → Bool) (N d t : ℕ → ℕ)
    (hs : ∀ n, SanoN (sol n) (det n) (N n)) (hd : ∀ n, DemoraN (sol n) (det n) (N n) (d n))
    {C c : ℕ} (hc : ∀ n, 2 ^ d n * t n ≤ C * (n + 1) ^ c) (n : ℕ) :
    SanoN (sol n) (anticipa (sol n) (det n) (N n) (d n)) (N n) ∧
      DemoraN (sol n) (anticipa (sol n) (det n) (N n) (d n)) (N n) 0 ∧
      (∀ p, llamadas (sol n) (det n) (N n) (d n) p * t n ≤ 2 * C * (n + 1) ^ c) := by
  obtain ⟨h1, h2⟩ := anticipa_perfecto (hs n) (hd n)
  refine ⟨h1, h2, fun p => ?_⟩
  have hl := llamadas_cota (sol n) (det n) (N n) (d n) p
  calc llamadas (sol n) (det n) (N n) (d n) p * t n ≤ 2 ^ (d n + 1) * t n := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * (2 ^ d n * t n) := by ring
    _ ≤ 2 * (C * (n + 1) ^ c) := Nat.mul_le_mul_left _ (hc n)
    _ = 2 * C * (n + 1) ^ c := by ring

/-- **Un oráculo exacto de `¬ Vivo` es sano y tiene demora 0.** No dice nada del costo de evaluarlo. -/
theorem oraculo_perfecto {sol o : List Bool → Bool} {N : ℕ}
    (ho : ∀ p : List Bool, p.length ≤ N → (o p = true ↔ ¬ Vivo sol (N - p.length) p)) :
    SanoN sol o N ∧ DemoraN sol o N 0 := by
  refine ⟨fun p hp h => (ho p hp).mp h, fun p hp hm q hq => ?_⟩
  rw [List.length_eq_zero_iff.mp hq, List.append_nil]
  exact (ho p (by omega)).mpr hm

/-- **Por qué no hay una «equivalencia» con `t` libre**: para **toda** familia hay un oráculo clásico de `¬ Vivo` que es
sano y tiene demora 0. Si el costo por llamada `t` es un número que se elige aparte, con `t = 1` cualquier familia
tiene «detectores de demora 0 y costo polinomial», y un enunciado de equivalencia sería `True ↔ True`. El contenido está
en `anticipar_polinomial`, donde el costo se cuenta en llamadas a un detector base dado. -/
theorem oraculo_siempre (sol : ℕ → List Bool → Bool) (N : ℕ → ℕ) :
    ∃ o : ℕ → List Bool → Bool, (∀ n, SanoN (sol n) (o n) (N n)) ∧ ∀ n, DemoraN (sol n) (o n) (N n) 0 := by
  classical
  refine ⟨fun n p => decide (¬ Vivo (sol n) (N n - p.length) p), fun n => (oraculo_perfecto ?_).1,
    fun n => (oraculo_perfecto ?_).2⟩ <;> intro p _ <;> simp

/-! ## Controles -/

/-- **La demora global degenera en CNF**: `detCNF todoTrue4` no tiene `Demora d` para ningún `d`, porque la raíz está
«muerta con 0 variables por fijar» y `detCNF` no dispara sobre `true, …, true`. Por eso este archivo usa `DemoraN`. -/
theorem demora_global_degenera (d : ℕ) : ¬ Demora (solCNF todoTrue4) (detCNF todoTrue4) d := by
  intro h
  have hm : ¬ Vivo (solCNF todoTrue4) 0 [] := by rw [vivo_cero]; decide
  have := h 0 [] hm (List.replicate d true) (by simp)
  revert this
  simp only [List.nil_append, detCNF, todoTrue4, falsificada, List.any_cons, List.all_cons, List.all_nil,
    List.any_nil, List.getElem?_replicate]
  split_ifs <;> simp

/-- La contradicción tarde: todas las ramas mueren, pero `detCNF` solo lo ve con las 4 variables fijadas. -/
def tarde4 : List Clausula := [[(3, true)], [(3, false)]]

/-- `detCNF` no ve nada en la raíz; anticiparlo 4 niveles sí. -/
example : detCNF tarde4 [] = false ∧ anticipa (solCNF tarde4) (detCNF tarde4) 4 4 [] = true := by decide

/-- Anticipar 3 niveles no alcanza en la raíz (la contradicción está a 4), pero sí en el hijo. -/
example : anticipa (solCNF tarde4) (detCNF tarde4) 4 3 [] = false ∧
    anticipa (solCNF tarde4) (detCNF tarde4) 4 3 [false] = true := by decide

/-- Con `detCNF`, certificar que no hay solución cuesta el árbol entero (31 nodos); con `anticipa … 4`, un nodo. -/
example : nodos (solCNF tarde4) (detCNF tarde4) 4 [] = 31 ∧
    nodos (solCNF tarde4) (anticipa (solCNF tarde4) (detCNF tarde4) 4 4) 4 [] = 1 := by decide

/-- Pero ese nodo cuesta 31 llamadas a `detCNF` (`2^5 − 1`, la cota de `llamadas_cota` es exacta aquí): se cambió
demora por costo por llamada, no se ganó nada. -/
example : llamadas (solCNF tarde4) (detCNF tarde4) 4 4 [] = 31 ∧
    peso (solCNF tarde4) (anticipa (solCNF tarde4) (detCNF tarde4) 4 4)
      (llamadas (solCNF tarde4) (detCNF tarde4) 4 4) 4 [] = 31 := by decide

/-- Con `todoTrue4`, `detCNF` ya tiene demora 0 en los hechos: anticipar no cambia los nodos (9), y la búsqueda con
anticipación de 1 nivel hace 18 llamadas en vez de 9: cada nodo del camino mira a sus dos hijos. -/
example : nodos (solCNF todoTrue4) (anticipa (solCNF todoTrue4) (detCNF todoTrue4) 4 1) 4 [] = 9 ∧
    peso (solCNF todoTrue4) (anticipa (solCNF todoTrue4) (detCNF todoTrue4) 4 1)
      (llamadas (solCNF todoTrue4) (detCNF todoTrue4) 4 1) 4 [] = 18 := by decide

/-- La demora efectiva: demora 4 a costo 1 y demora 0 a costo `2^5` valen lo mismo salvo 1. -/
example : demoraEfectiva 4 1 = 4 ∧ demoraEfectiva 0 (2 ^ 5 * 1) = 5 := by decide

/-
Mutantes probados fuera del repositorio (cada uno es una copia de este archivo con un solo cambio; todos fallan):
* `m1_hoja_sin_negar`: la hoja con `sol p` en vez de `!sol p`: fallan `anticipa_sano` (caso de la hoja) y
  `anticipa_de`. (Con `else false` el mutante no es informativo: `sol` deja de ser argumento y todo falla por tipos.)
* `m2_or_hijos`: `||` entre los hijos en vez de `&&`: fallan `anticipa_sano` y el control de `tarde4` con 3 niveles.
* `m3_cota_llamadas`: `llamadas_cota` con `2 ^ h` en vez de `2 ^ (h + 1)`: falla.
* `m4_demora_menos1`: `anticipa_demora` con `DemoraN … (d - h - 1)`: falla.
* `m5_efectiva_sin1`: `demoraEfectiva_anticipa` con `= demoraEfectiva d t` (sin el `+ 1`): falla.
* `m6_control30`, `m7_control_nodos1`: controles con números cambiados (`= 30` en vez de `= 31`, `= 1` en vez de
  `= 9`): fallan con `decide`.
-/

end Tiempo
end Sagitta.Map
