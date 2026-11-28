import Sagitta.Map.ArbolElecciones
import Sagitta.Map.DemoraEfectiva
import Sagitta.Map.Landau
import Mathlib.Data.Nat.Log

/-!
# La raíz muerta como sistema de pruebas (el lado de Cook y Reckhow)

Cuando la raíz está muerta (la fórmula no tiene solución), la corrida de `buscar` no encuentra nada, pero deja un
rastro: el árbol de los nodos que visitó, con hojas donde el detector dijo «muerto» (o, al fondo, donde la asignación
completa no es solución). Ese árbol es una **refutación**: se puede revisar sin volver a buscar, re-evaluando el
detector en las hojas, y su tamaño es exactamente `nodos`.

## El modelo

* **Una traza** (`Traza`) es un árbol binario: una `hoja`, o una `rama` con el hijo `false` y el hijo `true`.
* **El verificador** (`verifica sol det k p T`, un `Bool`): en una hoja con variables por fijar (`k + 1`), pide
  `det p = true`; en una hoja del fondo (`k = 0`), pide `det p = true` o `sol p = false`; en una rama, fija la variable
  `p.length` en `false` y en `true` y revisa los dos hijos. Una rama con `k = 0` se rechaza.
* **La traza de la corrida** (`traza det k p`): la que deja `buscar` en un nodo muerto. Su tamaño (`tamano`, nodos
  del árbol) es `nodos`; sus hojas (`hojas`) son las evaluaciones que hace el verificador.

## Lo que se prueba

* **Corrección** (`verifica_correcto`): si el detector es sano y una traza verifica, el nodo está muerto
  (`¬ Vivo sol k p`). En la raíz: la fórmula no tiene solución.
* **Completitud** (`traza_verifica`): si el nodo está muerto, la traza de la corrida verifica. No hace falta que el
  detector sea sano (`buscar_vivo_traza` da que, sin solución, `buscar` nunca devuelve `true`). Con las dos,
  `refuta_iff`: hay traza que verifica si y solo si el nodo está muerto.
* **Tamaño** (`tamano_traza`): el tamaño de la traza de la corrida es `nodos sol det k p`. Con demora `d`
  (`tamano_traza_demora`), es a lo sumo `2^(d+1) − 1` — **no depende de `k`** —, y siempre
  (`tamano_traza_le`) a lo sumo `2^(k+1) − 1`. Las hojas son `(tamano + 1) / 2` (`dos_hojas`).
* **La consecuencia, uniforme** (`refutaciones_uniformes`): un solo detector `det F` para **todas** las CNF, sano en
  todas (también en las que tienen solución) con el horizonte de `DemoraEfectiva.lean` (`SanoN`), y con demora
  `d F ≤ a · log₂(tam F + 1) + b`, donde `tam F` es el tamaño de la fórmula (cláusulas más literales). Entonces toda
  traza que verifica refuta, y toda CNF sin solución tiene una traza que verifica y mide a lo sumo
  `2^(b+1) · (tam F + 1)^a`. Es un sistema de pruebas polinomialmente acotado **en el modelo**: el tamaño se cuenta en
  nodos y el costo del detector no se mide.
* **Por qué uniforme y por qué `SanoN`.** Con un detector por instancia, el detector constante «muerto» es sano en
  toda fórmula sin solución, tiene demora `0` y da trazas de una hoja: el enunciado sería gratis. Exigir que el
  mismo detector sea sano en las fórmulas con solución lo descarta (`siempre_no_sanoN`). Y la `Demora` global de
  `ArbolElecciones.lean` no sirve aquí: cubre también la raíz con `0` variables por fijar, y eso obliga a un detector
  sano a disparar en todo (lo muestra `demora_global_degenera` de `DemoraEfectiva.lean`).

## Lo que NO se prueba

* **No es el teorema de Cook y Reckhow.** Por Cook y Reckhow (1979), que exista un sistema de pruebas polinomialmente
  acotado para **todas** las fórmulas sin solución equivale a `NP = coNP`. Aquí solo va la parte del modelo:
  detector con demora logarítmica ⇒ traza corta y verificable. No se construye un `ProofSystem` de cslib ni un
  `Sistema` de `SistemaDePruebas.lean`: faltaría codificar las trazas en `List Bool` y probar que el verificador corre
  en tiempo polinomial en una máquina.
* **El costo de verificar** es `hojas T` evaluaciones del detector (o de `sol` al fondo) más el recorrido del árbol.
  Que eso sea polinomial en una máquina exige que el detector mismo lo sea; aquí el detector es una función abstracta
  y su costo no se mide. Contar nodos no es tiempo de máquina de Turing.
* **La hipótesis es fuerte.** Para la familia del palomar, con `detCNF`, `RaizMuerta.lean` ya prueba que los nodos
  crecen como `(n/2+1)^(n/2)`, así que ahí la demora no es logarítmica. Si existiera un detector uniforme, sano, de
  tiempo polinomial y con demora `O(log tam)` en todas las CNF, las trazas serían un sistema de pruebas polinomialmente
  acotado y, por Cook y Reckhow, `NP = coNP`. Esa implicación pasa por la máquina y no está formalizada aquí.
* El modelo se parte en dos: la raíz viva (`costo_vivo`, encontrar) es el lado de `P` contra `NP`; la raíz muerta
  (este archivo, refutar) es el lado de `NP` contra `coNP`. Esto es una lectura, no un teorema.
-/

namespace Sagitta.Map
namespace Tiempo

/-- **Una traza**: el árbol de una refutación. Una hoja, o una rama con el hijo `false` y el hijo `true`. -/
inductive Traza where
  | hoja : Traza
  | rama (f t : Traza) : Traza
  deriving DecidableEq, Repr

namespace Traza

/-- Los nodos del árbol (hojas y ramas). Se compara con `nodos`. -/
def tamano : Traza → ℕ
  | hoja => 1
  | rama f t => tamano f + tamano t + 1

/-- Las hojas: cuántas veces el verificador evalúa el detector (o `sol`). -/
def hojas : Traza → ℕ
  | hoja => 1
  | rama f t => hojas f + hojas t

theorem dos_hojas : ∀ T : Traza, 2 * hojas T = tamano T + 1
  | hoja => rfl
  | rama f t => by
    have := dos_hojas f; have := dos_hojas t
    simp only [hojas, tamano]; omega

theorem hojas_le_tamano (T : Traza) : hojas T ≤ tamano T := by
  have := dos_hojas T; omega

end Traza

open Traza

variable (sol det : List Bool → Bool)

/-- **El verificador.** Hoja con variables por fijar: el detector dice «muerto». Hoja del fondo: el detector dice
«muerto» o la asignación completa no es solución. Rama: los dos hijos verifican. Una rama sin variables por fijar no
verifica. -/
def verifica : ℕ → List Bool → Traza → Bool
  | 0, p, hoja => det p || !sol p
  | _ + 1, p, hoja => det p
  | 0, _, rama _ _ => false
  | k + 1, p, rama f t => verifica k (p ++ [false]) f && verifica k (p ++ [true]) t

/-- **La traza de la corrida**: lo que deja `buscar` en un nodo muerto. -/
def traza : ℕ → List Bool → Traza
  | 0, _ => hoja
  | k + 1, p => if det p then hoja else rama (traza k (p ++ [false])) (traza k (p ++ [true]))

/-! ## Corrección -/

/-- **Corrección**: con un detector sano, una traza que verifica prueba que el nodo está muerto. -/
theorem verifica_correcto {sol det} (hs : Sano sol det) :
    ∀ (T : Traza) (k : ℕ) (p : List Bool), verifica sol det k p T = true → ¬ Vivo sol k p
  | hoja, 0, p, h => by
    simp only [verifica, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact sano_muerto hs h
    · rw [vivo_cero, h]; simp
  | hoja, _ + 1, p, h => sano_muerto hs (by simpa [verifica] using h)
  | rama _ _, 0, _, h => by simp [verifica] at h
  | rama f t, k + 1, p, h => by
    simp only [verifica, Bool.and_eq_true] at h
    rw [vivo_succ]
    rintro (hv | hv)
    · exact verifica_correcto hs f k _ h.1 hv
    · exact verifica_correcto hs t k _ h.2 hv

/-! ## Completitud -/

/-- Sin detector sano: si `buscar` dice que encontró, el nodo está vivo. -/
theorem buscar_vivo_traza : ∀ (k : ℕ) (p : List Bool), (buscar sol det k p).1 = true → Vivo sol k p
  | 0, p, h => by
    rw [vivo_cero]
    unfold buscar at h
    split at h
    · simp at h
    · exact h
  | k + 1, p, h => by
    rw [vivo_succ]
    unfold buscar at h
    split at h
    · simp at h
    · split at h
      · rename_i ha
        exact .inl (buscar_vivo_traza k _ ha)
      · exact .inr (buscar_vivo_traza k _ h)

/-- **Completitud**: en un nodo muerto, la traza de la corrida verifica. No pide que el detector sea sano. -/
theorem traza_verifica : ∀ (k : ℕ) (p : List Bool), ¬ Vivo sol k p → verifica sol det k p (traza det k p) = true
  | 0, p, hm => by
    rw [vivo_cero] at hm
    simp [traza, verifica, hm]
  | k + 1, p, hm => by
    rw [vivo_succ, not_or] at hm
    by_cases hd : det p = true
    · simp [traza, verifica, hd]
    · simp only [traza, hd, Bool.false_eq_true, ite_false, verifica, Bool.and_eq_true]
      exact ⟨traza_verifica k _ hm.1, traza_verifica k _ hm.2⟩

/-- **Hay refutación si y solo si el nodo está muerto** (con detector sano). -/
theorem refuta_iff {sol det} (hs : Sano sol det) (k : ℕ) (p : List Bool) :
    (∃ T, verifica sol det k p T = true) ↔ ¬ Vivo sol k p :=
  ⟨fun ⟨T, hT⟩ => verifica_correcto hs T k p hT, fun hm => ⟨_, traza_verifica sol det k p hm⟩⟩

/-! ## Tamaño -/

/-- **El tamaño de la traza es el costo de la corrida**: en un nodo muerto, `tamano = nodos`. -/
theorem tamano_traza : ∀ (k : ℕ) (p : List Bool), ¬ Vivo sol k p → tamano (traza det k p) = nodos sol det k p
  | 0, p, _ => by
    unfold nodos buscar
    split <;> rfl
  | k + 1, p, hm => by
    rw [vivo_succ, not_or] at hm
    unfold nodos
    by_cases hd : det p = true
    · simp [traza, buscar, hd, tamano]
    · have ha : (buscar sol det k (p ++ [false])).1 = false := by
        cases h : (buscar sol det k (p ++ [false])).1
        · rfl
        · exact absurd (buscar_vivo_traza sol det k _ h) hm.1
      have hf := tamano_traza k _ hm.1
      have ht := tamano_traza k _ hm.2
      unfold nodos at hf ht
      simp only [traza, buscar, hd, ha, Bool.false_eq_true, ite_false, tamano]
      omega

/-- **Con demora `d`, la traza mide a lo sumo `2^(d+1) − 1`**, sin importar cuántas variables falten. -/
theorem tamano_traza_demora {d : ℕ} (hd : Demora sol det d) {k : ℕ} {p : List Bool} (hm : ¬ Vivo sol k p) :
    tamano (traza det k p) + 1 ≤ 2 ^ (d + 1) := by
  rw [tamano_traza sol det k p hm]
  exact costo_muerto sol det hd hm

/-- Siempre: la traza mide a lo sumo `2^(k+1) − 1` (el árbol entero). -/
theorem tamano_traza_le : ∀ (k : ℕ) (p : List Bool), tamano (traza det k p) + 1 ≤ 2 ^ (k + 1)
  | 0, _ => by simp [traza, tamano]
  | k + 1, p => by
    have hf := tamano_traza_le k (p ++ [false])
    have ht := tamano_traza_le k (p ++ [true])
    have e : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    unfold traza
    split
    · simp only [tamano]; omega
    · simp only [tamano]; omega

/-! ## La consecuencia para una familia -/

/-- `2^(a · log₂(n+1) + b + 1) ≤ 2^(b+1) · (n+1)^a`. -/
theorem dos_pow_log_le (a b n : ℕ) : 2 ^ (a * Nat.log 2 (n + 1) + b + 1) ≤ 2 ^ (b + 1) * (n + 1) ^ a := by
  have h := Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  calc 2 ^ (a * Nat.log 2 (n + 1) + b + 1) = 2 ^ (b + 1) * (2 ^ Nat.log 2 (n + 1)) ^ a := by
        rw [← pow_mul, mul_comm (Nat.log 2 (n + 1)) a, ← pow_add]; ring_nf
    _ ≤ 2 ^ (b + 1) * (n + 1) ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h a)

/-! ## Con horizonte: `SanoN` y `DemoraN` -/

/-- **Corrección con horizonte**: con un detector `SanoN`, una traza que verifica en un nodo de las `N` variables
prueba que el nodo está muerto. -/
theorem verifica_correctoN {sol det} {N : ℕ} (hs : SanoN sol det N) :
    ∀ (T : Traza) (k : ℕ) (p : List Bool), p.length + k = N → verifica sol det k p T = true → ¬ Vivo sol k p
  | hoja, 0, p, hk, h => by
    simp only [verifica, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · have := hs p (by omega) h; rwa [show N - p.length = 0 by omega] at this
    · rw [vivo_cero, h]; simp
  | hoja, k + 1, p, hk, h => by
    have := hs p (by omega) (by simpa [verifica] using h)
    rwa [show N - p.length = k + 1 by omega] at this
  | rama _ _, 0, _, _, h => by simp [verifica] at h
  | rama f t, k + 1, p, hk, h => by
    simp only [verifica, Bool.and_eq_true] at h
    rw [vivo_succ]
    rintro (hv | hv)
    · exact verifica_correctoN hs f k _ (by simp; omega) h.1 hv
    · exact verifica_correctoN hs t k _ (by simp; omega) h.2 hv

/-- **Con demora `d` y horizonte, la traza mide a lo sumo `2^(d+1) − 1`.** -/
theorem tamano_traza_demoraN {N d : ℕ} (hd : DemoraN sol det N d) {k : ℕ} {p : List Bool} (hk : p.length + k = N)
    (hm : ¬ Vivo sol k p) : tamano (traza det k p) + 1 ≤ 2 ^ (d + 1) := by
  rw [tamano_traza sol det k p hm]
  exact costo_muertoN hd hk hm

/-- **El tamaño de una CNF**: cuántas cláusulas más cuántos literales. -/
def tamCNF (F : List Clausula) : ℕ := F.length + (F.map List.length).sum

/-- **Refutaciones uniformes.** Un detector `det F` para todas las CNF, sano en todas con horizonte `N F`, con demora
`d F ≤ a · log₂(tam F + 1) + b`. Entonces (1) toda traza que verifica refuta, y (2) toda CNF sin solución tiene una
traza que verifica y mide a lo sumo `2^(b+1) · (tam F + 1)^a`. -/
theorem refutaciones_uniformes (det : List Clausula → List Bool → Bool) (N d : List Clausula → ℕ) (a b : ℕ)
    (hs : ∀ F, SanoN (solCNF F) (det F) (N F)) (hd : ∀ F, DemoraN (solCNF F) (det F) (N F) (d F))
    (hlog : ∀ F, d F ≤ a * Nat.log 2 (tamCNF F + 1) + b) :
    (∀ F (T : Traza), verifica (solCNF F) (det F) (N F) [] T = true → ¬ Vivo (solCNF F) (N F) []) ∧
    ∀ F, ¬ Vivo (solCNF F) (N F) [] →
      verifica (solCNF F) (det F) (N F) [] (traza (det F) (N F) []) = true ∧
      tamano (traza (det F) (N F) []) + 1 ≤ 2 ^ (b + 1) * (tamCNF F + 1) ^ a := by
  refine ⟨fun F T h => verifica_correctoN (hs F) T _ _ (by simp) h, fun F hm => ⟨traza_verifica _ _ _ _ hm, ?_⟩⟩
  have h1 := tamano_traza_demoraN (solCNF F) (det F) (hd F) (by simp) hm
  have h2 : 2 ^ (d F + 1) ≤ 2 ^ (a * Nat.log 2 (tamCNF F + 1) + b + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := hlog F; omega)
  exact h1.trans (h2.trans (dos_pow_log_le a b _))

/-- **El detector constante «muerto» no es uniforme**: no es sano en `x₀`, que tiene solución. Sin la uniformidad,
daría refutaciones de una hoja para toda fórmula sin solución. -/
theorem siempre_no_sanoN : ¬ SanoN (solCNF [[(0, true)]]) (fun _ => true) 1 := fun h =>
  h [] (by simp) rfl ⟨[true], rfl, by decide⟩

/-- Sin detector (`nunca`), la traza es la tabla de verdad entera: `2^(k+1) − 1` nodos. -/
theorem traza_nunca (k : ℕ) (hm : ¬ Vivo sol k []) : tamano (traza nunca k []) + 1 = 2 ^ (k + 1) := by
  rw [tamano_traza sol nunca k [] hm]
  exact sin_detector_muerto sol k [] hm

/-! ## Controles -/

/-- `x₀ ∧ ¬x₀`: sin solución, una variable. -/
def contra1 : List Clausula := [[(0, true)], [(0, false)]]

/-- **Una traza concreta que verifica**: ramificar en `x₀`, y en cada hoja una cláusula ya es falsa. -/
example : verifica (solCNF contra1) (detCNF contra1) 1 [] (.rama .hoja .hoja) = true := by decide

/-- **Es la traza de la corrida**, con tamaño 3 = `nodos`. -/
example : traza (detCNF contra1) 1 [] = .rama .hoja .hoja ∧
    nodos (solCNF contra1) (detCNF contra1) 1 [] = 3 := by decide

/-- **Una traza mala**: una hoja en la raíz no verifica (ninguna cláusula es falsa todavía). -/
example : verifica (solCNF contra1) (detCNF contra1) 1 [] .hoja = false := by decide

/-- **Otra mala**: ramificar de más (sin variables por fijar) no verifica. -/
example : verifica (solCNF contra1) (detCNF contra1) 1 [] (.rama (.rama .hoja .hoja) .hoja) = false := by decide

/-- **Con solución, la misma traza no verifica**: `x₀` sola se satisface en la rama `true`. -/
example : verifica (solCNF [[(0, true)]]) (detCNF [[(0, true)]]) 1 [] (.rama .hoja .hoja) = false := by decide

/-- **La contradicción tarde** (en `x₃`): la traza es el árbol entero, 31 nodos, y verifica. -/
example : tamano (traza (detCNF [[(3, true)], [(3, false)]]) 4 []) = 31 ∧
    verifica (solCNF [[(3, true)], [(3, false)]]) (detCNF [[(3, true)], [(3, false)]]) 4 []
      (traza (detCNF [[(3, true)], [(3, false)]]) 4 []) = true := by decide

/-- **La contradicción temprana** (en `x₀`) con 4 variables: 3 nodos, no 31. La demora corta acorta la prueba. -/
example : tamano (traza (detCNF contra1) 4 []) = 3 := by decide

/-- **Sin detector sano no hay corrección**: un detector que siempre dice «muerto» hace verificar la hoja en la raíz
para `x₀`, que sí tiene solución. -/
example : verifica (solCNF [[(0, true)]]) (fun _ => true) 1 [] .hoja = true ∧
    solCNF [[(0, true)]] [true] = true := by decide

/- Mutantes probados (fuera del repositorio; cada uno rompe la compilación):
* `verifica` en la hoja del fondo con `det p || sol p` (en vez de `!sol p`): falla `verifica_correcto` y el control
  con solución (`x₀` sola) da `true`.
* `verifica` aceptando `rama` con `k = 0` (`| 0, _, rama _ _ => true`): falla `verifica_correcto`.
* `verifica` en la rama con `||` en vez de `&&`: falla `verifica_correcto` y el control con solución.
* `traza` en `k + 1` devolviendo siempre `hoja`: falla `traza_verifica` y el control de la traza de la corrida.
* `tamano (rama f t) = tamano f + tamano t` (sin el `+ 1`): falla `tamano_traza` y `dos_hojas`.
* Quitar `hs` de `verifica_correcto`: no compila. El control de arriba (detector que siempre dice «muerto») muestra
  que sin `Sano` la corrección es falsa, no solo que la prueba la usa.
Archivos: `e5prima/rmp/m1_sol.lean`, `m2_rama0`, `m3_or`, `m4_traza`, `m5_tam`, `m6_sinhs`.
-/

end Tiempo
end Sagitta.Map
