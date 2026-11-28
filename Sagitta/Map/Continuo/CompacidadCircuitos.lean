import Sagitta.Map.Continuo.ClaseNoContinua
import Sagitta.Map.Circuitos

/-!
# Continuo ⇒ circuitos: la compacidad (3b)

La pregunta de José (24 nov 2026): «si aceptamos máquinas infinitamente largas con resultados infinitamente largos,
¿hay continuidad?». Una máquina que lee una descripción infinita `d : ℕ → Bool` y escribe una salida infinita es un
mapa `F : (ℕ → Bool) → (ℕ → Bool)`. Que cada bit de la salida salga en tiempo finito es que dependa de un prefijo finito
de la entrada, y eso es la continuidad (`continuo_iff_prefijo` de `ClaseNoContinua.lean`, parte (d)). Aquí se agrega
la compacidad: el prefijo se puede tomar **uniforme** en `d`.

## Lo que se prueba

* (i) **Uniforme por compacidad** (`bit_de_prefijo`): si `F` es continua, para cada `k` hay un `m` tal que todas las
  `d, d'` que coinciden en `[0, m)` dan el mismo bit `k`. La prueba cubre el espacio de Cantor (compacto) con los
  cilindros que da la continuidad en cada punto y toma un subcubrimiento finito.
* (ii) **El bit es una función booleana finita, y tiene circuito** (`bit_es_funcion`, `bit_tiene_circuito`): el bit `k`
  de la salida es `g (d 0, …, d (m−1))` para una `g : (Fin m → Bool) → Bool`, y `g` tiene un circuito en el modelo de
  `Shannon.lean` (por `toda_funcion_calculable` de `TodaFuncion.lean`, de otra sesión; solo se importa).
* (iii) **El recíproco** (`continua_de_prefijos`): una familia de funciones booleanas finitas, una por bit, define una `F`
  continua. Juntas: `continua_iff_prefijos_uniformes`.

## Lectura

Computar con descripciones infinitas y tiempo finito por bit es lo continuo (la computabilidad de tipo 2: continuo es
computable con un parámetro infinito; Weihrauch, de memoria, no leído en esta sesión). La compacidad lo vuelve una
familia de circuitos **no uniforme**, uno por bit de salida: la topología garantiza que el circuito existe; la
complejidad pregunta su tamaño, y por Shannon casi todos son enormes. Las máquinas de tiempo infinito de Hamkins y Lewis
(2000) rompen la continuidad (miran la cola entera) y deciden la parada de las máquinas normales; el principio de
continuidad de Brouwer dice lo contrario: toda función total es continua. Ninguno de los dos se formaliza aquí.

## Lo que no

* Nada sobre el tamaño de los circuitos (eso es Shannon, otro archivo). Nada de computabilidad: el `m` y la `g` se
  eligen por compacidad y elección, no se calculan.
-/

open Filter Topology Set

namespace Sagitta.Map.Continuo.Compacidad

open Sagitta.Map Sagitta.Map.Continuo Sagitta.Map.Shannon

/-- Los que coinciden con `e` en `[0, N)` forman un abierto. -/
theorem cilindro_abierto (e : ℕ → Bool) (N : ℕ) : IsOpen {d : ℕ → Bool | ∀ i < N, d i = e i} := by
  have : {d : ℕ → Bool | ∀ i < N, d i = e i} = ⋂ i ∈ Finset.range N, (fun d : ℕ → Bool => d i) ⁻¹' {e i} := by
    ext d; simp
  rw [this]
  exact isOpen_biInter_finset fun i _ => (isOpen_discrete _).preimage (continuous_apply i)

/-- **(i) El prefijo es uniforme**: por compacidad, un mismo `m` sirve para toda `d`. -/
theorem bit_de_prefijo {F : (ℕ → Bool) → (ℕ → Bool)} (hF : Continuous F) (k : ℕ) :
    ∃ m, ∀ d d' : ℕ → Bool, (∀ i < m, d i = d' i) → F d k = F d' k := by
  have hG : Continuous fun d => F d k := (continuous_apply k).comp hF
  choose N hN using (continuo_iff_prefijo _).1 hG
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun e => {d : ℕ → Bool | ∀ i < N e, d i = e i})
    (fun e => cilindro_abierto e (N e)) (fun d _ => mem_iUnion.2 ⟨d, fun _ _ => rfl⟩)
  refine ⟨t.sup N, fun d d' hdd' => ?_⟩
  obtain ⟨e, he, hde⟩ := mem_iUnion₂.1 (ht (mem_univ d))
  have hle : N e ≤ t.sup N := Finset.le_sup he
  have h1 : F d k = F e k := hN e d hde
  have h2 : F d' k = F e k := hN e d' fun i hi => (hdd' i (lt_of_lt_of_le hi hle)).symm.trans (hde i hi)
  rw [h1, h2]

/-- Una palabra de `m` bits, extendida con `false`. -/
def extender {m : ℕ} (x : Fin m → Bool) : ℕ → Bool := fun i => if h : i < m then x ⟨i, h⟩ else false

/-- **(ii) El bit `k` es una función booleana de los primeros `m` bits.** -/
theorem bit_es_funcion {F : (ℕ → Bool) → (ℕ → Bool)} (hF : Continuous F) (k : ℕ) :
    ∃ m, ∃ g : (Fin m → Bool) → Bool, ∀ d, F d k = g (fun i => d i) := by
  obtain ⟨m, hm⟩ := bit_de_prefijo hF k
  exact ⟨m, fun x => F (extender x) k, fun d => hm d _ fun i hi => by simp [extender, hi]⟩

/-- **Y tiene un circuito** en el modelo de `Shannon.lean`. -/
theorem bit_tiene_circuito {F : (ℕ → Bool) → (ℕ → Bool)} (hF : Continuous F) (k : ℕ) :
    ∃ m t, ∃ C : Circuito m t, ∀ d, F d k = calcula C (fun i => d i) := by
  obtain ⟨m, g, hg⟩ := bit_es_funcion hF k
  obtain ⟨t, C, hC⟩ := toda_funcion_calculable g
  exact ⟨m, t, C, fun d => by rw [hg d, hC]⟩

/-- **(iii) El recíproco**: una función booleana finita por bit define una `F` continua. -/
theorem continua_de_prefijos (m : ℕ → ℕ) (g : ∀ k, (Fin (m k) → Bool) → Bool) :
    Continuous fun (d : ℕ → Bool) (k : ℕ) => g k (fun i => d i) := by
  refine continuous_pi fun k => (continuo_iff_prefijo _).2 fun d => ⟨m k, fun d' hd' => ?_⟩
  congr 1
  funext i
  exact hd' i i.isLt

/-- **Continua si y solo si cada bit depende de un prefijo uniforme.** -/
theorem continua_iff_prefijos_uniformes (F : (ℕ → Bool) → (ℕ → Bool)) :
    Continuous F ↔ ∀ k, ∃ m, ∀ d d' : ℕ → Bool, (∀ i < m, d i = d' i) → F d k = F d' k := by
  refine ⟨fun hF k => bit_de_prefijo hF k, fun h => ?_⟩
  refine continuous_pi fun k => (continuo_iff_prefijo _).2 fun d => ?_
  obtain ⟨m, hm⟩ := h k
  exact ⟨m, fun d' hd' => hm d' d hd'⟩

/-! ## Controles -/

/-- Correr un bit: `F d k = d (k + 1)`. Es continua, con `m = k + 2` explícito. -/
def correr (d : ℕ → Bool) (k : ℕ) : Bool := d (k + 1)

example (k : ℕ) : ∀ d d' : ℕ → Bool, (∀ i < k + 2, d i = d' i) → correr d k = correr d' k :=
  fun _ _ h => h (k + 1) (by omega)

example : Continuous correr := (continua_iff_prefijos_uniformes correr).2 fun k =>
  ⟨k + 2, fun _ _ h => h (k + 1) (by omega)⟩

/-- Con `m = k + 1` no alcanza: `m` tiene que ver el bit `k + 1`. -/
example (k : ℕ) : ¬ ∀ d d' : ℕ → Bool, (∀ i < k + 1, d i = d' i) → correr d k = correr d' k := by
  intro h
  have := h (fun _ => false) (fun i => decide (i = k + 1)) (fun i hi => by simp; omega)
  simp [correr] at this

/-- La parada (`parar` de `ClaseNoContinua.lean`) como salida de un bit no es continua, así que no tiene prefijo
uniforme: (i) sí exige algo. -/
example : ¬ ∃ m, ∀ d d' : ℕ → Bool, (∀ i < m, d i = d' i) → parar d = parar d' := by
  rintro ⟨m, hm⟩
  have := hm (fun _ => false) (fun i => decide (i = m)) (fun i hi => by simp; omega)
  have h2 : parar (fun i => decide (i = m)) = true := by simp [parar]
  have h1 : parar (fun _ => false) = false := by simp [parar]
  rw [h1, h2] at this
  exact Bool.false_ne_true this

/- Mutante probado (25 nov 2026, en /tmp/claude-noche/MutComp.lean): en `bit_de_prefijo`, tomar `m := 0` en lugar de
`t.sup N` no compila (falta `N e ≤ 0`); y el control de `correr` con `m = k + 1` muestra que el enunciado con un `m`
más chico es falso. -/

end Sagitta.Map.Continuo.Compacidad
