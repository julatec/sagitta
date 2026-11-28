import Sagitta.Map.KolmogorovTiempo
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Rondas acotadas: la medida en que ronda ≈ tiempo

## La idea (de José)

Aplicarle un truco al cubo: las rondas son **acotadas**, cada una corre un tiempo finito y constante. Así, al
componer corridas, lo que era polinomial sigue polinomial; y al sumarle el tiempo de construcción, el más grande
absorbe al otro.

**La condición que hace que funcione.** Cada ronda necesita **dos** topes, con la misma constante `C`:

* **trabajo**: a lo sumo `C` operaciones;
* **crecimiento de datos**: el tamaño del estado sube a lo sumo `C` (bits, celdas) por ronda.

Con los dos topes, `t` rondas cuestan a lo sumo `C · t` de trabajo y dejan un estado de tamaño a lo sumo
`tam₀ + C · t` (`trabajo_lineal`, `espacio_lineal`): **tiempo y espacio son lineales en las rondas**. Por eso, con
rondas acotadas, contar rondas es contar tiempo (salvo la constante `C`).

## Por qué esta es la medida honesta que le faltaba al proyecto

Las medidas anteriores del proyecto (`pasos`/`costo` de `AceleracionBlum.lean`, usadas en `KolmogorovTiempo.lean` y
`UniversoCerrado.lean`) son el presupuesto de `evaln` de Mathlib. Esa medida cumple el tope de trabajo en un sentido
débil, pero **no** el de crecimiento: una sola ronda de `pair` arma un número con tantos bits como sus dos argumentos
juntos, y anidando `pair` el árbol de cualquier `x` corre con presupuesto `1` (`evaln_arbol`, `costo_arbol`).
`evaln_no_acotado` lo dice como teorema: **no hay ninguna `C`** tal que la salida de `evaln r p n` tenga a lo sumo
`|n| + C · r` bits. Las rondas de `evaln` no son tiempo de máquina.

En cambio, un paso de una máquina de Turing multicinta de cslib **sí** es una ronda acotada, con `C = k + 2` para `k`
cintas de trabajo (`mt_es_acotada`, § 5): cada paso escribe a lo sumo un símbolo por cinta, mueve cada cabeza a lo
sumo una celda, mueve la de entrada a lo sumo una y emite a lo sumo un símbolo de salida.

## Qué se prueba

1. **El modelo** (§ 1): `Recorrido` (estados `s₀, s₁, …` y trabajo por ronda), `EsAcotado tam C r t`, y
   `espacio_lineal`, `trabajo_lineal`.
2. **La composición mantiene lo polinomial** (§ 2): una `Etapa` es un procedimiento de rondas acotadas. Componer dos
   (`Etapa.componer`) usa `t₁(n) + t₂(n + C·t₁(n))` rondas (`componer_rondas`, con `t₂` monótona), y eso está en
   `Pol` (`componer_pol`, sin pedir monotonía: se usa el mayorante `c·(n+1)ᵏ`). Por inducción, una cadena de una
   cantidad fija de etapas (`encadenar_pol`), en particular repetir `k` veces la misma (`repetir_pol`). Es la
   clausura que pedía José. El trabajo total y el tamaño de la salida también quedan en `Pol` (`trabajo_pol`,
   `salida_pol`).
3. **El más grande absorbe** (§ 3): `a + b ≤ 2 · max a b` y `a + b + c ≤ 3 · max a b c`. Con la medida completa
   (pedido de José), el costo es **construcción del resolvedor + construcción del verificador + ejecución**, y la
   ejecución incluye correr el verificador sobre lo que entrega el resolvedor, en rondas acotadas.
   * Con resolvedor y verificador **fijos** para todos los tamaños, las dos construcciones son constantes y la
     ejecución las absorbe: el total está en `O(ejecución)` si la ejecución es `≥ 1` (`fijos_absorbidos`).
   * Si una construcción crece, por ejemplo `2ⁿ` (una tabla por tamaño), la construcción absorbe a una ejecución
     polinomial: el total está en `Θ(2ⁿ)` y fuera de toda `O(p)` polinomial (`construccion_absorbe`,
     `verificador_a_medida`), aunque el resolvedor sea barato. Si un lugar es gratis, el trabajo se esconde ahí: al
     cobrar la construcción del verificador, no puede esconderse en él (`olvidar_verificador_subestima`).
4. **El contraejemplo** (§ 4): `evaln_no_acotado` y `evaln_crece_sin_tope`.
5. **El puente con cslib** (§ 5): el tamaño de una configuración de `MultiTapeNTM`/`MultiTapeTM` (largo de la salida
   + posición de la cabeza de entrada + un radio por cinta que contiene la cabeza y todo lo escrito) sube a lo sumo
   `k + 2` por paso (`paso_es_ronda`), y la corrida de una máquina determinista, `runFrom`, es un recorrido acotado con
   `C = k + 2` y trabajo `1` por ronda (`mt_es_acotada`, `recorridoMT_cfg`). Desde la configuración inicial, `t` pasos
   dejan un tamaño de a lo sumo `1 + (k + 2) · t` (`mt_tam_lineal`).
6. **Controles**: el contador cumple las cotas con igualdad (`contador_acotado`, `contador_exacto`); componer dos
   lineales da una lineal (`componer_lineales`). **Mutante refutado en el archivo**: sin el tope de crecimiento (con
   crecimiento multiplicativo, `tam_{i+1} ≤ 2 · tam_i`) la composición deja de ser polinomial: `duplicar_escapa`.

## La lectura

Con un resolvedor fijo, la construcción es una constante y la ejecución la absorbe (`fijos_absorbidos`; es la forma
de `cerrado_en_O` de `UniversoCerrado.lean`, ahora con la medida honesta). Para SAT el verificador también es un
programa fijo, que evalúa la fórmula en tiempo polinomial: construirlo cuesta una constante. Así, con la medida
completa, **P contra NP queda como «¿la ejecución del resolvedor puede ser polinomial?»**, limpia de la medida: no se
puede esconder trabajo ni en el presupuesto de `evaln` (que no cobra los bits), ni en la construcción del resolvedor,
ni en la del verificador.

## Lo que NO se prueba

* Que los resultados anteriores del proyecto (`UniversoCerrado.lean`, `KolmogorovTiempo.lean`, `KtSAT.lean`) valgan
  con esta medida: **no están reenunciados** en rondas acotadas. Siguen siendo enunciados sobre `evaln`.
* El puente con cslib es por el **lado de las máquinas**: un paso de máquina es una ronda acotada. No se prueba lo
  recíproco (que un procedimiento abstracto de rondas acotadas se simule con una máquina en tiempo lineal en las
  rondas), ni nada sobre `RunsInTime` más allá de que `runFrom` es un recorrido acotado. El tamaño `tamMT` cuenta
  celdas y posiciones, no bits: un símbolo de un alfabeto finito vale una constante de bits.
* **Nada sobre P contra NP.**
-/

open Nat.Partrec Nat.Partrec.Code

namespace Sagitta.Map
namespace Tiempo
namespace RondasAcotadas

open KolmogorovTiempo AceleracionBlum

/-! ## 1. El modelo de rondas acotadas -/

/-- **Un recorrido**: la sucesión de estados `s₀, s₁, …` y el trabajo `w i` de la ronda que va de `sᵢ` a `sᵢ₊₁`. -/
structure Recorrido (σ : Type*) where
  /-- el estado después de `i` rondas -/
  estado : ℕ → σ
  /-- el trabajo de la ronda `i` (de `estado i` a `estado (i+1)`) -/
  trabajo : ℕ → ℕ

variable {σ : Type*}

/-- **Rondas acotadas con constante `C`** en las primeras `t` rondas: cada una hace a lo sumo `C` de trabajo y sube
el tamaño del estado a lo sumo `C`. -/
def EsAcotado (tam : σ → ℕ) (C : ℕ) (r : Recorrido σ) (t : ℕ) : Prop :=
  ∀ i < t, r.trabajo i ≤ C ∧ tam (r.estado (i + 1)) ≤ tam (r.estado i) + C

/-- El trabajo total de las primeras `t` rondas. -/
def trabajoTotal (r : Recorrido σ) (t : ℕ) : ℕ := ∑ i ∈ Finset.range t, r.trabajo i

theorem EsAcotado.mono {tam : σ → ℕ} {C C' : ℕ} {r : Recorrido σ} {t t' : ℕ} (h : EsAcotado tam C r t)
    (hC : C ≤ C') (ht : t' ≤ t) : EsAcotado tam C' r t' := fun i hi => by
  have := h i (by omega); constructor <;> omega

/-- **El tamaño crece a lo sumo lineal**: después de `j ≤ t` rondas, `tam sⱼ ≤ tam s₀ + C · j`. -/
theorem tam_lineal {tam : σ → ℕ} {C : ℕ} {r : Recorrido σ} {t : ℕ} (h : EsAcotado tam C r t) :
    ∀ j ≤ t, tam (r.estado j) ≤ tam (r.estado 0) + C * j := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := (h j (by omega)).2
    have h2 := ih (by omega)
    rw [Nat.mul_succ]; omega

/-- **Espacio lineal en las rondas**: `tam s_t ≤ tam s₀ + C · t`. -/
theorem espacio_lineal {tam : σ → ℕ} {C : ℕ} {r : Recorrido σ} {t : ℕ} (h : EsAcotado tam C r t) :
    tam (r.estado t) ≤ tam (r.estado 0) + C * t := tam_lineal h t le_rfl

/-- **Tiempo lineal en las rondas**: el trabajo total de `t` rondas es a lo sumo `C · t`. -/
theorem trabajo_lineal {tam : σ → ℕ} {C : ℕ} {r : Recorrido σ} {t : ℕ} (h : EsAcotado tam C r t) :
    trabajoTotal r t ≤ C * t := by
  unfold trabajoTotal
  calc ∑ i ∈ Finset.range t, r.trabajo i ≤ ∑ _i ∈ Finset.range t, C :=
        Finset.sum_le_sum fun i hi => (h i (Finset.mem_range.1 hi)).1
    _ = C * t := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-! ## 2. La composición mantiene lo polinomial -/

/-- **Seguir**: las primeras `t₁` rondas de `r₁` y después las de `r₂`. -/
def Recorrido.seguir (r₁ : Recorrido σ) (t₁ : ℕ) (r₂ : Recorrido σ) : Recorrido σ where
  estado i := if i ≤ t₁ then r₁.estado i else r₂.estado (i - t₁)
  trabajo i := if i < t₁ then r₁.trabajo i else r₂.trabajo (i - t₁)

/-- **Pegar dos recorridos acotados da uno acotado**, con la mayor de las dos constantes. -/
theorem seguir_acotado {tam : σ → ℕ} {C₁ C₂ t₁ t₂ : ℕ} {r₁ r₂ : Recorrido σ} (h₁ : EsAcotado tam C₁ r₁ t₁)
    (h₂ : EsAcotado tam C₂ r₂ t₂) (hj : r₂.estado 0 = r₁.estado t₁) :
    EsAcotado tam (max C₁ C₂) (r₁.seguir t₁ r₂) (t₁ + t₂) := by
  intro i hi
  simp only [Recorrido.seguir]
  by_cases hlt : i < t₁
  · rw [ite_eq_left hlt, ite_eq_left (by omega : i ≤ t₁), ite_eq_left (by omega : i + 1 ≤ t₁)]
    obtain ⟨a, b⟩ := h₁ i hlt
    constructor <;> omega
  · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬ i + 1 ≤ t₁)]
    obtain ⟨a, b⟩ := h₂ (i - t₁) (by omega)
    rw [show i + 1 - t₁ = i - t₁ + 1 by omega]
    by_cases hi' : i ≤ t₁
    · rw [ite_eq_left hi']
      obtain rfl : i = t₁ := by omega
      rw [Nat.sub_self, hj] at b
      rw [Nat.sub_self] at a ⊢
      constructor <;> omega
    · rw [ite_eq_right hi']
      constructor <;> omega

theorem seguir_final {r₁ r₂ : Recorrido σ} {t₁ : ℕ} (t₂ : ℕ) (hj : r₂.estado 0 = r₁.estado t₁) :
    (r₁.seguir t₁ r₂).estado (t₁ + t₂) = r₂.estado t₂ := by
  simp only [Recorrido.seguir]
  by_cases h : t₁ + t₂ ≤ t₁
  · rw [ite_eq_left h]; obtain rfl : t₂ = 0 := by omega
    exact hj.symm
  · rw [ite_eq_right h, Nat.add_sub_cancel_left]

/-- **Una etapa**: un procedimiento de rondas acotadas. Para cada estado inicial `s`, un recorrido que empieza en
`s`, acotado con la constante `C` de la etapa durante sus `rondas s` rondas. -/
structure Etapa (σ : Type*) (tam : σ → ℕ) where
  /-- la constante de los dos topes -/
  C : ℕ
  /-- cuántas rondas corre sobre `s` -/
  rondas : σ → ℕ
  /-- el recorrido desde `s` -/
  recorrido : σ → Recorrido σ
  inicio : ∀ s, (recorrido s).estado 0 = s
  acotado : ∀ s, EsAcotado tam C (recorrido s) (rondas s)

variable {tam : σ → ℕ}

namespace Etapa

/-- Lo que entrega la etapa: el estado después de sus rondas. -/
def salida (P : Etapa σ tam) (s : σ) : σ := (P.recorrido s).estado (P.rondas s)

/-- La etapa **corre en `t` rondas**: sobre un estado de tamaño `n` usa a lo sumo `t n` rondas. -/
def CorreEn (P : Etapa σ tam) (t : ℕ → ℕ) : Prop := ∀ s, P.rondas s ≤ t (tam s)

theorem tam_salida (P : Etapa σ tam) (s : σ) : tam (P.salida s) ≤ tam s + P.C * P.rondas s := by
  have := espacio_lineal (P.acotado s); rwa [P.inicio] at this

/-- **Componer dos etapas**: correr `P` y alimentar su salida a `Q`. -/
def componer (P Q : Etapa σ tam) : Etapa σ tam where
  C := max P.C Q.C
  rondas s := P.rondas s + Q.rondas (P.salida s)
  recorrido s := (P.recorrido s).seguir (P.rondas s) (Q.recorrido (P.salida s))
  inicio s := by simp [Recorrido.seguir, P.inicio]
  acotado s := seguir_acotado (P.acotado s) (Q.acotado _) (Q.inicio _)

theorem componer_salida (P Q : Etapa σ tam) (s : σ) : (P.componer Q).salida s = Q.salida (P.salida s) :=
  seguir_final _ (Q.inicio _)

/-- La etapa vacía: cero rondas. -/
def nada : Etapa σ tam where
  C := 0
  rondas _ := 0
  recorrido s := ⟨fun _ => s, fun _ => 0⟩
  inicio _ := rfl
  acotado _ := fun i hi => absurd hi (Nat.not_lt_zero i)

end Etapa

open Etapa

/-- **Las rondas de la composición**: `t₁(n) + t₂(n + C₁ · t₁(n))`. La segunda etapa recibe un estado que creció a lo
sumo `C₁` por ronda de la primera. -/
theorem componer_rondas {P Q : Etapa σ tam} {t₁ t₂ : ℕ → ℕ} (h₁ : P.CorreEn t₁) (h₂ : Q.CorreEn t₂)
    (hm : Monotone t₂) : (P.componer Q).CorreEn (fun n => t₁ n + t₂ (n + P.C * t₁ n)) := by
  intro s
  change P.rondas s + Q.rondas (P.salida s) ≤ t₁ (tam s) + t₂ (tam s + P.C * t₁ (tam s))
  have a := h₁ s
  have b := h₂ (P.salida s)
  have d : tam (P.salida s) ≤ tam s + P.C * t₁ (tam s) :=
    (P.tam_salida s).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ a) _)
  have e := hm d
  omega

/-- Toda función de `Pol` tiene un mayorante monótono en `Pol`: `c · (n+1)ᵏ`. -/
theorem pol_mayorante {f : ℕ → ℕ} (hf : f ∈ Pol) : ∃ g ∈ Pol, Monotone g ∧ ∀ n, f n ≤ g n := by
  obtain ⟨c, k, h⟩ := hf
  exact ⟨fun n => c * (n + 1) ^ k, ⟨c, k, fun _ => le_rfl⟩,
    fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _), h⟩

/-- **La clausura de José**: si las dos etapas corren en un número polinomial de rondas, la composición también. -/
theorem componer_pol {P Q : Etapa σ tam} {t₁ t₂ : ℕ → ℕ} (h₁ : P.CorreEn t₁) (ht₁ : t₁ ∈ Pol)
    (h₂ : Q.CorreEn t₂) (ht₂ : t₂ ∈ Pol) : ∃ t ∈ Pol, (P.componer Q).CorreEn t := by
  obtain ⟨g, hg, hgm, hfg⟩ := pol_mayorante ht₂
  have h₂' : Q.CorreEn g := fun s => (h₂ s).trans (hfg _)
  refine ⟨_, ?_, componer_rondas h₁ h₂' hgm⟩
  exact pol_add ht₁ (pol_comp hg (pol_add pol_id (pol_mul (pol_const P.C) ht₁)))

/-- **Una cadena de etapas**, una detrás de otra. -/
def encadenar : List (Etapa σ tam) → Etapa σ tam
  | [] => Etapa.nada
  | P :: l => P.componer (encadenar l)

/-- **Una cantidad fija de etapas polinomiales compuestas es polinomial.** -/
theorem encadenar_pol : ∀ l : List (Etapa σ tam), (∀ P ∈ l, ∃ t ∈ Pol, P.CorreEn t) →
    ∃ t ∈ Pol, (encadenar l).CorreEn t
  | [], _ => ⟨fun _ => 0, pol_const 0, fun _ => le_rfl⟩
  | P :: l, h => by
    obtain ⟨t₁, ht₁, h₁⟩ := h P (List.mem_cons_self ..)
    obtain ⟨t₂, ht₂, h₂⟩ := encadenar_pol l fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)
    exact componer_pol h₁ ht₁ h₂ ht₂

/-- **Repetir `k` veces la misma etapa polinomial** (las `k` rondas del cubo, con `k` fijo) es polinomial. -/
theorem repetir_pol {P : Etapa σ tam} {t : ℕ → ℕ} (h : P.CorreEn t) (ht : t ∈ Pol) (k : ℕ) :
    ∃ t' ∈ Pol, (encadenar (List.replicate k P)).CorreEn t' :=
  encadenar_pol _ fun Q hQ => by rw [List.eq_of_mem_replicate hQ]; exact ⟨t, ht, h⟩

/-- **El trabajo total de una etapa polinomial es polinomial** en el tamaño de la entrada. -/
theorem trabajo_pol {P : Etapa σ tam} {t : ℕ → ℕ} (h : P.CorreEn t) (ht : t ∈ Pol) :
    ∃ w ∈ Pol, ∀ s, trabajoTotal (P.recorrido s) (P.rondas s) ≤ w (tam s) :=
  ⟨fun n => P.C * t n, pol_mul (pol_const _) ht, fun s =>
    (trabajo_lineal (P.acotado s)).trans (Nat.mul_le_mul_left _ (h s))⟩

/-- **El tamaño de la salida de una etapa polinomial es polinomial** en el de la entrada. -/
theorem salida_pol {P : Etapa σ tam} {t : ℕ → ℕ} (h : P.CorreEn t) (ht : t ∈ Pol) :
    ∃ m ∈ Pol, ∀ s, tam (P.salida s) ≤ m (tam s) :=
  ⟨fun n => n + P.C * t n, pol_add pol_id (pol_mul (pol_const _) ht), fun s =>
    (P.tam_salida s).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (h s)) _)⟩

/-! ## 3. El más grande absorbe -/

theorem suma_le_dos_max (a b : ℕ) : a + b ≤ 2 * max a b := by omega

theorem suma_le_tres_max (a b c : ℕ) : a + b + c ≤ 3 * max a (max b c) := by omega

/-- **Si `g ∈ O(f)`, `f + g ∈ O(f)`**: el más grande absorbe al otro. -/
theorem absorbe {f g : ℕ → ℕ} (h : EsO g f) : EsO (fun n => f n + g n) f := by
  obtain ⟨C, N, h⟩ := h
  refine ⟨C + 1, N, fun n hn => ?_⟩
  have := h n hn
  change f n + g n ≤ (C + 1) * f n
  rw [Nat.add_mul, one_mul]; omega

/-- **Resolvedor fijo**: la construcción es una constante `K` y la ejecución `t ≥ 1` la absorbe. -/
theorem resolvedor_fijo (K : ℕ) {t : ℕ → ℕ} (ht : ∀ n, 1 ≤ t n) : EsO (fun n => K + t n) t := by
  refine ⟨K + 1, 0, fun n _ => ?_⟩
  have := Nat.mul_le_mul_left K (ht n)
  change K + t n ≤ (K + 1) * t n
  rw [Nat.add_mul, one_mul]; omega

/-- **La medida completa, con todo fijo** (el caso de SAT): construir el resolvedor cuesta `Kr`, construir el
verificador `Kv`, y la ejecución `t ≥ 1` (que incluye correr el verificador) las absorbe a las dos. El total queda
debajo de tres veces el máximo de las tres partes y en `O(t)`. -/
theorem fijos_absorbidos (Kr Kv : ℕ) {t : ℕ → ℕ} (ht : ∀ n, 1 ≤ t n) :
    (∀ n, Kr + Kv + t n ≤ 3 * max Kr (max Kv (t n))) ∧ EsO (fun n => Kr + Kv + t n) t := by
  refine ⟨fun n => suma_le_tres_max _ _ _, ?_⟩
  obtain ⟨C, N, h⟩ := resolvedor_fijo (Kr + Kv) ht
  exact ⟨C, N, fun n hn => by have := h n hn; simpa [Nat.add_assoc] using this⟩

/-- **Ningún polinomio acota a `2ⁿ`.** -/
theorem dos_pow_no_O_pol {p : ℕ → ℕ} (hp : p ∈ Pol) : ¬ EsO (fun n => 2 ^ n) p := by
  rintro ⟨C, N, h⟩
  obtain ⟨c, k, hp⟩ := hp
  obtain ⟨N', hN'⟩ := pol_menor_dos_pow (C * c) k
  have h1 : 2 ^ max N N' ≤ C * p (max N N') := h (max N N') (by omega)
  have h2 := hN' (max N N') (by omega)
  have h3 : C * p (max N N') ≤ C * c * (max N N' + 1) ^ k := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (hp _)
  omega

/-- **Construcción que crece**: si construir cuesta `2ⁿ` y ejecutar es polinomial, la construcción absorbe a la
ejecución: el total está en `Θ(2ⁿ)` y fuera de `O(p)`. -/
theorem construccion_absorbe {p : ℕ → ℕ} (hp : p ∈ Pol) :
    EsO (fun n => 2 ^ n + p n) (fun n => 2 ^ n) ∧ EsO (fun n => 2 ^ n) (fun n => 2 ^ n + p n) ∧
      ¬ EsO (fun n => 2 ^ n + p n) p := by
  obtain ⟨c, k, hp'⟩ := id hp
  obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
  refine ⟨⟨2, N, fun n hn => ?_⟩, ⟨1, 0, fun n _ => by beta_reduce; omega⟩, fun h => dos_pow_no_O_pol hp ?_⟩
  · have := hp' n; have := hN n hn; beta_reduce; omega
  · obtain ⟨C, N, h⟩ := h; exact ⟨C, N, fun n hn => by have := h n hn; beta_reduce at this ⊢; omega⟩

/-- **Control: verificador a medida.** Si el resolvedor es barato (`Kr`), la ejecución polinomial, pero el
verificador se construye por tamaño con una tabla de `2ⁿ` entradas, la construcción del verificador absorbe todo: el
total está en `Θ(2ⁿ)` y fuera de toda `O(q)` polinomial. Cobrarla impide esconder trabajo en el verificador. -/
theorem verificador_a_medida (Kr : ℕ) {p : ℕ → ℕ} (hp : p ∈ Pol) :
    EsO (fun n => Kr + 2 ^ n + p n) (fun n => 2 ^ n) ∧ EsO (fun n => 2 ^ n) (fun n => Kr + 2 ^ n + p n) ∧
      ∀ q ∈ Pol, ¬ EsO (fun n => Kr + 2 ^ n + p n) q := by
  obtain ⟨c, k, hp'⟩ := id hp
  obtain ⟨N, hN⟩ := pol_menor_dos_pow c k
  refine ⟨⟨Kr + 2, N, fun n hn => ?_⟩, ⟨1, 0, fun n _ => by beta_reduce; omega⟩,
    fun q hq h => dos_pow_no_O_pol hq ?_⟩
  · have := hp' n; have := hN n hn
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have : Kr ≤ Kr * 2 ^ n := Nat.le_mul_of_pos_right _ (by omega)
    beta_reduce; rw [Nat.add_mul]; omega
  · obtain ⟨C, N, h⟩ := h; exact ⟨C, N, fun n hn => by have := h n hn; beta_reduce at this ⊢; omega⟩

/-- **Olvidar la construcción del verificador subestima.** Con resolvedor fijo `Kr`, ejecución `p ∈ Pol`, `p ≥ 1`, y
verificador de tabla `2ⁿ`: la cuenta sin el verificador está en `O(p)`, la completa no. -/
theorem olvidar_verificador_subestima (Kr : ℕ) {p : ℕ → ℕ} (hp : p ∈ Pol) (h1 : ∀ n, 1 ≤ p n) :
    EsO (fun n => Kr + p n) p ∧ ¬ EsO (fun n => Kr + 2 ^ n + p n) p :=
  ⟨resolvedor_fijo Kr h1, (verificador_a_medida Kr hp).2.2 p hp⟩

/-! ## 4. El contraejemplo: `evaln` no es de rondas acotadas -/

/-- **`evaln` no tiene tope de crecimiento**: no hay `C` tal que la salida de `evaln r p n` tenga a lo sumo
`|n| + C · r` bits. El árbol de `2^(C+1)` corre con presupuesto `1` desde `0` y su salida tiene `C + 2` bits. -/
theorem evaln_no_acotado :
    ¬ ∃ C, ∀ (p : Code) (r n x : ℕ), evaln r p n = some x → Nat.size x ≤ Nat.size n + C * r := by
  rintro ⟨C, h⟩
  have := h (arbol (2 ^ (C + 1))) 1 0 _ (evaln_arbol _)
  rw [Nat.size_pow, Nat.size_zero] at this
  omega

/-- **Con presupuesto (y costo) `1`, la salida tiene tantos bits como se quiera.** -/
theorem evaln_crece_sin_tope (B : ℕ) :
    ∃ (p : Code) (x : ℕ), evaln 1 p 0 = some x ∧ costo p 0 = 1 ∧ B < Nat.size x :=
  ⟨arbol (2 ^ B), 2 ^ B, evaln_arbol _, costo_arbol _, by rw [Nat.size_pow]; omega⟩

/-! ## 5. El puente: un paso de máquina multicinta de cslib es una ronda acotada

Las configuraciones de cslib (`Turing.Cfg`) guardan las cintas de trabajo como funciones `ℤ → Option Symbol`, sin
tamaño propio. Se les agrega un **radio por cinta** (`EstadoMT.radio`): la ventana `[-R, R]` que contiene la cabeza y
todo lo escrito (`EnVentana`). El tamaño (`tamMT`) es el largo de la salida, más la posición de la cabeza de entrada,
más los radios: cuenta celdas (cada cinta ocupa `2R + 1`), no bits. -/

section Puente

open Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Una configuración de cslib con un radio por cinta de trabajo. -/
structure EstadoMT (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- la configuración de cslib -/
  cfg : Cfg k Symbol State input
  /-- el radio de la ventana de cada cinta de trabajo -/
  radio : Fin k → ℕ

/-- **El tamaño de un estado de máquina**: salida + cabeza de entrada + radios de las cintas. -/
def tamMT (e : EstadoMT k Symbol State input) : ℕ :=
  e.cfg.output.length + e.cfg.inputPos.val + ∑ i, e.radio i

/-- **En ventana**: en cada cinta, la cabeza y toda celda no blanca están a distancia `≤ radio` del origen. -/
def EnVentana (e : EstadoMT k Symbol State input) : Prop :=
  ∀ i, (e.cfg.workTapePos i).natAbs ≤ e.radio i ∧ ∀ z, e.cfg.workTapes i z ≠ Option.none → z.natAbs ≤ e.radio i

/-- Pasar a la configuración `c'`, agrandando cada radio lo justo para que contenga la nueva cabeza. -/
def avanzar (c' : Cfg k Symbol State input) (e : EstadoMT k Symbol State input) : EstadoMT k Symbol State input :=
  ⟨c', fun i => max (e.radio i) (c'.workTapePos i).natAbs⟩

theorem natAbs_pos_aplicar (a : Action k Symbol State) (c : Cfg k Symbol State input) (i : Fin k) :
    ((a.apply c).workTapePos i).natAbs ≤ (c.workTapePos i).natAbs + 1 := by
  have h := workTapePos_apply_le a c i
  rw [abs_le] at h
  omega

/-- **Una acción sube el tamaño a lo sumo `k + 2`**: uno por la salida, uno por la cabeza de entrada, uno por cinta. -/
theorem tam_aplicar (a : Action k Symbol State) (e : EstadoMT k Symbol State input) (hv : EnVentana e) :
    tamMT (avanzar (a.apply e.cfg) e) ≤ tamMT e + (k + 2) := by
  have hout : (a.apply e.cfg).output.length ≤ e.cfg.output.length + 1 := by
    rcases ho : a.output with _ | s <;> simp [Action.apply, ho]
  have hin := val_moveInputPos_le e.cfg.inputPos a.inputTape
  have hr : ∑ i, max (e.radio i) ((a.apply e.cfg).workTapePos i).natAbs ≤ ∑ i, (e.radio i + 1) :=
    Finset.sum_le_sum fun i _ => by
      have := natAbs_pos_aplicar a e.cfg i
      have := (hv i).1
      omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hr
  unfold tamMT avanzar
  simp only [Action.apply_inputPos] at hin ⊢
  omega

/-- **Una acción conserva la ventana.** -/
theorem enVentana_aplicar (a : Action k Symbol State) (e : EstadoMT k Symbol State input) (hv : EnVentana e) :
    EnVentana (avanzar (a.apply e.cfg) e) := by
  intro i
  refine ⟨le_max_right _ _, fun z hz => ?_⟩
  have hz' : (a.apply e.cfg).workTapes i z ≠ Option.none := hz
  change z.natAbs ≤ max (e.radio i) _
  refine le_trans ?_ (le_max_left _ _)
  rcases hw : (a.workTapes i).1 with _ | s
  · have h1 : (a.apply e.cfg).workTapes i = e.cfg.workTapes i := by simp [Action.apply, hw]
    rw [h1] at hz'; exact (hv i).2 z hz'
  · have h1 : (a.apply e.cfg).workTapes i = Function.update (e.cfg.workTapes i) (e.cfg.workTapePos i) s := by
      simp [Action.apply, hw]
    rw [h1] at hz'
    by_cases hzp : z = e.cfg.workTapePos i
    · subst hzp; exact (hv i).1
    · rw [Function.update_of_ne hzp] at hz'; exact (hv i).2 z hz'

/-- Quedarse en la misma configuración no cambia nada, si ya está en ventana. -/
theorem avanzar_mismo (e : EstadoMT k Symbol State input) (hv : EnVentana e) : avanzar e.cfg e = e := by
  cases e with
  | mk c R =>
    simp only [avanzar, EstadoMT.mk.injEq, true_and]
    funext i; exact max_eq_left (hv i).1

/-- **Un paso de una `MultiTapeNTM` es una ronda acotada con `C = k + 2`**: si `c` da un paso a `c'`, el tamaño sube a
lo sumo `k + 2` y la ventana se conserva. -/
theorem paso_es_ronda (ntm : MultiTapeNTM k Symbol State) {c' : Cfg k Symbol State input}
    (e : EstadoMT k Symbol State input) (h : ntm.Step e.cfg c') (hv : EnVentana e) :
    tamMT (avanzar c' e) ≤ tamMT e + (k + 2) ∧ EnVentana (avanzar c' e) := by
  unfold MultiTapeNTM.Step at h
  split at h
  · subst h; rw [avanzar_mismo e hv]; exact ⟨by omega, hv⟩
  · obtain ⟨a, -, rfl⟩ := h
    exact ⟨tam_aplicar a e hv, enVentana_aplicar a e hv⟩

/-- Un paso de una máquina determinista, con el radio al día. -/
noncomputable def pasoMT (tm : MultiTapeTM k Symbol State) (e : EstadoMT k Symbol State input) :
    EstadoMT k Symbol State input :=
  avanzar (tm.step e.cfg) e

/-- **La corrida de una máquina determinista como recorrido**: un paso por ronda, trabajo `1` por ronda. -/
noncomputable def recorridoMT (tm : MultiTapeTM k Symbol State) (e₀ : EstadoMT k Symbol State input) :
    Recorrido (EstadoMT k Symbol State input) :=
  ⟨fun i => (pasoMT tm)^[i] e₀, fun _ => 1⟩

/-- El recorrido sigue a `runFrom` de cslib. -/
theorem recorridoMT_cfg (tm : MultiTapeTM k Symbol State) (e₀ : EstadoMT k Symbol State input) (t : ℕ) :
    ((recorridoMT tm e₀).estado t).cfg = tm.runFrom e₀.cfg t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [recorridoMT, MultiTapeTM.runFrom, Function.iterate_succ_apply'] at ih ⊢
    rw [← ih]; rfl

theorem enVentana_pasoMT (tm : MultiTapeTM k Symbol State) (e : EstadoMT k Symbol State input)
    (hv : EnVentana e) : tamMT (pasoMT tm e) ≤ tamMT e + (k + 2) ∧ EnVentana (pasoMT tm e) :=
  paso_es_ronda tm.toMultiTapeNTM e (MultiTapeTM.step_iff.2 rfl) hv

theorem enVentana_iterar (tm : MultiTapeTM k Symbol State) (e₀ : EstadoMT k Symbol State input)
    (hv : EnVentana e₀) (i : ℕ) : EnVentana ((pasoMT tm)^[i] e₀) := by
  induction i with
  | zero => exact hv
  | succ i ih => rw [Function.iterate_succ_apply']; exact (enVentana_pasoMT tm _ ih).2

/-- **El puente**: la corrida de una `MultiTapeTM` con `k` cintas de trabajo es un recorrido de rondas acotadas con
`C = k + 2`, desde cualquier estado en ventana. -/
theorem mt_es_acotada (tm : MultiTapeTM k Symbol State) (e₀ : EstadoMT k Symbol State input)
    (hv : EnVentana e₀) (t : ℕ) : EsAcotado tamMT (k + 2) (recorridoMT tm e₀) t := fun i _ => by
  refine ⟨by simp [recorridoMT], ?_⟩
  simp only [recorridoMT, Function.iterate_succ_apply']
  exact (enVentana_pasoMT tm _ (enVentana_iterar tm e₀ hv i)).1

/-- El estado inicial de cslib, con radios cero: está en ventana y mide `1`. -/
def inicialMT (tm : MultiTapeTM k Symbol State) (input : List Symbol) : EstadoMT k Symbol State input :=
  ⟨tm.initCfg input, fun _ => 0⟩

theorem enVentana_inicial (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    EnVentana (inicialMT tm input) := fun i => ⟨by simp [inicialMT], fun z hz => by simp [inicialMT] at hz⟩

/-- **Tiempo `t` da tamaño lineal**: después de `t` pasos desde la configuración inicial, salida + cabeza de entrada
+ radios (que contienen todo lo escrito) suman a lo sumo `1 + (k + 2) · t`. -/
theorem mt_tam_lineal (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    tamMT ((recorridoMT tm (inicialMT tm input)).estado t) ≤ 1 + (k + 2) * t := by
  have := espacio_lineal (mt_es_acotada tm _ (enVentana_inicial tm input) t)
  have h0 : tamMT ((recorridoMT tm (inicialMT tm input)).estado 0) = 1 := by
    simp [recorridoMT, tamMT, inicialMT]
  omega

end Puente

/-! ## 6. Controles -/

/-- **El contador**: suma `1` por ronda, con trabajo `1`. -/
def contador (n : ℕ) : Recorrido ℕ := ⟨fun i => n + i, fun _ => 1⟩

theorem contador_acotado (n t : ℕ) : EsAcotado id 1 (contador n) t := fun i _ => by
  simp only [contador, id]; omega

/-- **El contador cumple las cotas con igualdad**: tamaño `n + t` y trabajo `t`. -/
theorem contador_exacto (n t : ℕ) :
    id ((contador n).estado t) = id ((contador n).estado 0) + 1 * t ∧ trabajoTotal (contador n) t = 1 * t := by
  simp [contador, trabajoTotal]

/-- **Componer dos lineales da una lineal**: si `t₁ n = a n + b` y `t₂ m = c m + d`, la composición corre en
`A n + B` rondas. -/
theorem componer_lineales {P Q : Etapa σ tam} {a b c d : ℕ} (h₁ : P.CorreEn (fun n => a * n + b))
    (h₂ : Q.CorreEn (fun m => c * m + d)) :
    ∃ A B, (P.componer Q).CorreEn (fun n => A * n + B) := by
  have hm : Monotone (fun m => c * m + d) := fun x y h => Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _
  refine ⟨a + c + c * P.C * a, b + c * P.C * b + d, fun s => (componer_rondas h₁ h₂ hm s).trans (le_of_eq ?_)⟩
  ring

/-! ### Mutante refutado: sin tope de crecimiento -/

/-- Duplicar: el estado es un tamaño, cada ronda lo duplica con trabajo `1`; corre tantas rondas como su entrada. -/
def duplicar (s : ℕ) : Recorrido ℕ := ⟨fun i => 2 ^ i * s, fun _ => 1⟩

/-- **Sin el tope aditivo, componer escapa de `Pol`.** Duplicar cumple el tope de trabajo y un tope multiplicativo
(`tam_{i+1} ≤ 2 · tam_i`), y corre `n` rondas (polinomial) sobre una entrada de tamaño `n`. Pero alimentar su salida
a sí mismo usa `n + n · 2ⁿ` rondas, que no están en `Pol`. -/
theorem duplicar_escapa :
    (∀ s i, (duplicar s).trabajo i ≤ 1 ∧ (duplicar s).estado (i + 1) ≤ 2 * (duplicar s).estado i) ∧
      (fun n => n) ∈ Pol ∧
      (fun n => n + (duplicar n).estado n) ∉ Pol := by
  refine ⟨fun s i => ⟨le_rfl, by simp [duplicar, pow_succ]; ring_nf; rfl⟩, pol_id, fun h => ?_⟩
  apply iterada_doblar_no_pol
  obtain ⟨c, k, h⟩ := h
  refine ⟨c, k, fun n => le_trans ?_ (h n)⟩
  simp [iterada, iterate_doblar, duplicar]

end RondasAcotadas
end Tiempo
end Sagitta.Map
