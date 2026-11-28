import Sagitta.Map.Informacion.Profundidad
import Sagitta.Map.Continuo.MemoriaPeriodica
import Mathlib.Computability.Primrec.List

/-!
# La memoria acota la profundidad

La cota «la memoria acota la profundidad» (ver las notas del proyecto) dice: una máquina con `s` bits de memoria que se detiene lo hace antes de unos `2^s`
pasos, y si no, cicla; su salida tiene `Kt ≤ |p| + s + O(log)`, así que su profundidad es a lo sumo `s + |p| + O(log)`.
Y en el párrafo del bombeo: un ciclo gasta tiempo sin crear profundidad, `K(x yⁱ z) ≤ K(x y z) + O(log i)`. Este
archivo prueba las tres piezas.

## Lo que se prueba

1. **Parar o ciclar** (`parar_o_ciclar`): un sistema determinista `δ : σ → Option σ` sobre `σ` finito, desde cualquier
   estado, o se detiene en uno de los primeros `card σ` pasos, o no se detiene nunca y su traza es finalmente periódica
   con preperíodo más período a lo sumo `card σ + 1`. Sale de `MemoriaPeriodica` (`para_iff_acotado`,
   `finalmente_periodica` sobre `Option σ`). Con `s` bits de memoria, `card σ ≤ 2^s` y el corte es `2^s`
   (`para_antes_de_dos_pow`).
2. **La memoria acota la profundidad**, en el modelo de `Profundidad` (la `K` y la `Kt` de `KolmogorovTiempo`, códigos
   de Mathlib). Esos códigos no tienen memoria: lo que tienen es el presupuesto de `evaln`. Así que el enunciado va
   por el costo (`profundidad_por_costo`): si `p` produce `x` y su evaluación cabe en `2^s`,
   **`prof x ≤ |p| + s − 3`** (la constante es `−3`: `K x ≥ 3`). El puente con la memoria
   (`memoria_acota_profundidad`) es condicional: si un sistema de `card σ ≤ 2^s` estados se detiene y el código `p` no
   tarda más que el sistema (`Simula`), sale la misma cota. La hipótesis `Simula` es lo que falta; ver abajo.
3. **El bombeo no crea profundidad**, en la forma de la no creación (`bombeo_no_crea`): hay una constante `c` tal que
   para toda palabra `x, y, z` sobre `Bool` y todo `i`,
   `K ⟦x ++ yⁱ ++ z⟧ ≤ K ⟦(x, y, z)⟧ + K i + c`, y con la cota superior de `K` (`Kt_cota_superior`),
   `K ⟦x ++ yⁱ ++ z⟧ ≤ K ⟦(x, y, z)⟧ + 24 · log₂ i + c'` (`bombeo_no_crea_log`): el `O(log i)` con su constante.
   Es `no_creacion` aplicada al bombeo (calculable, por `Primrec.nat_iterate`) y un nodo `pair` (`K_pair_le`).
4. **Un ejemplo en `Fin 8`** (tres bits): un contador que llega a `7` y para en el paso `8 = card (Fin 8)`, justo en la
   cota, y uno que cicla con período 8; las dos ramas
   de `parar_o_ciclar`, decididas.

## Lo que NO se prueba

* **La versión con espacio de una máquina de cslib.** Faltan dos cosas. (a) El conteo de configuraciones: una máquina
  de `k` cintas con espacio `s` sobre un alfabeto `Γ` y estados `Q` tiene a lo sumo `|Q| · (s + 1)^k · |Γ|^(k s)`
  configuraciones; cslib-frontier tiene la máquina (`MultiTapeTM`) pero no una cota de espacio sobre la corrida ni el
  tipo finito de las configuraciones acotadas. Con eso, `parar_o_ciclar` da el corte `2^O(s)`. (b) La `Kt` de
  máquinas: `Ktmt` de `NoCreacion` existe, pero su largo es el índice de la descripción, y ese índice crece como una
  torre en el largo de la palabra (`dos_pow_dos_pow_le_encode`): la cota «`Ktmt ≤ índice + s`» saldría, la aditiva
  en bits no.
* **Que `Simula` valga para algún sistema y su código.** `evaln` cobra la lectura de la entrada y la profundidad de
  recursión, no los pasos de una máquina; no hay en el repositorio una compilación de un `δ` finito a un `Code` con el
  costo acotado por los pasos.
* **El `O(log n)` del corte.** `K ⟦(x, y, z)⟧` no es `K ⟦x ++ y ++ z⟧`: partir la palabra pide los dos largos, unos
  `2 log n` bits más. No se formaliza aquí.
* Nada sobre P contra NP.
-/

namespace Sagitta.Map.Informacion.MemoriaProfundidad

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval evaln evaln_mono exists_code)
open Sagitta.Map.Tiempo.KolmogorovTiempo Sagitta.Map.Tiempo.AceleracionBlum
open Sagitta.Map.Informacion.NoCreacion Sagitta.Map.Informacion.Profundidad
open Sagitta.Map.Continuo.Memoria
open Sagitta.Map.Continuo.Regreso (Para)

/-! ## 1. Parar o ciclar -/

section Ciclar

variable {σ : Type*} [Fintype σ]

/-- **Parar o ciclar.** Con memoria finita, o la traza se detiene en uno de los primeros `card σ` pasos, o no se detiene
nunca y es finalmente periódica, con preperíodo más período a lo sumo `card σ + 1`. -/
theorem parar_o_ciclar (δ : σ → Option σ) (s : σ) :
    (∃ n ≤ Fintype.card σ, traza δ s n = none) ∨
    ((∀ n, traza δ s n ≠ none) ∧
      ∃ i p, 0 < p ∧ i + p ≤ Fintype.card σ + 1 ∧ ∀ n, i ≤ n → traza δ s (n + p) = traza δ s n) := by
  by_cases h : traza δ s ∈ Para none
  · obtain ⟨n, hn, e⟩ := (para_iff_acotado δ s).1 h
    exact Or.inl ⟨n, by omega, e⟩
  · refine Or.inr ⟨fun n hn => h ⟨n, hn⟩, ?_⟩
    obtain ⟨i, p, hp, hip, hper⟩ := finalmente_periodica (paso δ) (some s)
    rw [Fintype.card_option] at hip
    exact ⟨i, p, hp, hip, fun n hn => hper n hn⟩

/-- **Con `s` bits, parar es parar antes de `2^s`.** -/
theorem para_antes_de_dos_pow (δ : σ → Option σ) (s₀ : σ) {s : ℕ} (hc : Fintype.card σ ≤ 2 ^ s)
    (hp : traza δ s₀ ∈ Para none) : ∃ n ≤ 2 ^ s, traza δ s₀ n = none := by
  obtain ⟨n, hn, e⟩ := (para_iff_acotado δ s₀).1 hp
  exact ⟨n, by omega, e⟩

end Ciclar

/-! ## 2. La memoria acota la profundidad -/

/-- **La profundidad, acotada por el costo.** Si `p` produce `x` y su evaluación cabe en `2^s`,
`prof x ≤ |p| + s − 3`. -/
theorem profundidad_por_costo {p : Code} {x s : ℕ} (hp : Produce p x) (ht : (evaln (2 ^ s) p 0).isSome) :
    prof x + 3 ≤ largo p + s := by
  have h1 := ley hp ht
  rw [Nat.log_pow (by norm_num)] at h1
  have h2 := prof_add x
  have h3 := K_ge x
  omega

/-- **El código no tarda más que el sistema**: cuando la traza de `δ` desde `s₀` se detiene en el paso `n`, la
evaluación de `p` cabe en `n`. Es la hipótesis que conecta la memoria (estados) con el costo de `evaln`. -/
def Simula {σ : Type*} (δ : σ → Option σ) (s₀ : σ) (p : Code) : Prop :=
  ∀ n, traza δ s₀ n = none → (evaln n p 0).isSome

/-- **La memoria acota la profundidad** (condicional a `Simula`). Si un sistema de a lo sumo `2^s` estados se detiene y
el código `p` que produce `x` no tarda más que él, `prof x ≤ |p| + s − 3`. -/
theorem memoria_acota_profundidad {σ : Type*} [Fintype σ] (δ : σ → Option σ) (s₀ : σ) {s : ℕ}
    (hc : Fintype.card σ ≤ 2 ^ s) (hpara : traza δ s₀ ∈ Para none) {p : Code} {x : ℕ} (hp : Produce p x)
    (hsim : Simula δ s₀ p) : prof x + 3 ≤ largo p + s := by
  obtain ⟨n, hn, e⟩ := para_antes_de_dos_pow δ s₀ hc hpara
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hsim n e)
  have : (evaln (2 ^ s) p 0).isSome :=
    Option.isSome_iff_exists.2 ⟨v, evaln_mono hn (by rw [hv]; rfl)⟩
  exact profundidad_por_costo hp this

/-! ## 3. El bombeo no crea profundidad -/

/-- **Emparejar cuesta tres bits**: el nodo `pair` y los dos árboles. -/
theorem largo_pair (p q : Code) : largo (.pair p q) = largo p + largo q + 3 := by
  simp only [largo, bits, List.length_append, List.length_cons, List.length_nil]
  omega

theorem produce_pair {p q : Code} {a b : ℕ} (hp : Produce p a) (hq : Produce q b) :
    Produce (.pair p q) (Nat.pair a b) := by
  unfold Produce at *
  simp only [Code.eval, hp, hq]
  simp [Seq.seq]

/-- `K` de un par: a lo sumo la suma más tres. -/
theorem K_pair_le (a b : ℕ) : K (Nat.pair a b) ≤ K a + K b + 3 := by
  obtain ⟨p, hp, hlp⟩ := K_spec a
  obtain ⟨q, hq, hlq⟩ := K_spec b
  have := K_le (produce_pair hp hq)
  rw [largo_pair] at this
  omega

/-- El bombeo: `x ++ y ++ ⋯ ++ y ++ z`, con `i` copias de `y`. -/
def bombear (a : ℕ × (List Bool × (List Bool × List Bool))) : List Bool :=
  (fun l => l ++ a.2.2.1)^[a.1] a.2.1 ++ a.2.2.2

theorem iterate_append_eq (y : List Bool) : ∀ (i : ℕ) (x : List Bool),
    (fun l => l ++ y)^[i] x = x ++ (List.replicate i y).flatten
  | 0, x => by simp
  | i + 1, x => by
    rw [Function.iterate_succ_apply', iterate_append_eq y i x, List.replicate_succ', List.flatten_append]
    simp

/-- El bombeo es lo que dice el nombre: `x ++ yⁱ ++ z`. -/
theorem bombear_eq (i : ℕ) (x y z : List Bool) :
    bombear (i, x, y, z) = x ++ (List.replicate i y).flatten ++ z := by
  simp [bombear, iterate_append_eq]

theorem bombear_primrec : Primrec bombear := by
  unfold bombear
  refine Primrec.list_append.comp ?_ (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.nat_iterate Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.list_append.comp₂ Primrec₂.right ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp₂ Primrec₂.left))

/-- Hay un código que lleva el número de `(i, x, y, z)` al número de `x ++ yⁱ ++ z`. -/
theorem existe_codigo_bombeo : ∃ c : Code, ∀ a, eval c (Encodable.encode a) = Part.some (Encodable.encode (bombear a)) := by
  obtain ⟨c, hc⟩ := exists_code.1 (Computable.partrec bombear_primrec.to_comp)
  refine ⟨c, fun a => ?_⟩
  rw [hc]
  simp

/-- **El bombeo no crea información**: `K ⟦x ++ yⁱ ++ z⟧ ≤ K ⟦(x, y, z)⟧ + K i + c`, con `c` fija. -/
theorem bombeo_no_crea : ∃ c, ∀ (i : ℕ) (x y z : List Bool),
    K (Encodable.encode (x ++ (List.replicate i y).flatten ++ z)) ≤ K (Encodable.encode (x, y, z)) + K i + c := by
  obtain ⟨c, hc⟩ := existe_codigo_bombeo
  refine ⟨largo c + 6, fun i x y z => ?_⟩
  have h1 := no_creacion (f := fun _ => Encodable.encode (bombear (i, x, y, z))) (hc (i, x, y, z))
  have h2 := K_pair_le i (Encodable.encode (x, y, z))
  rw [bombear_eq] at h1
  have e : Encodable.encode ((i, x, y, z) : ℕ × (List Bool × (List Bool × List Bool))) =
      Nat.pair i (Encodable.encode (x, y, z)) := by
    rw [Encodable.encode_prod_val, Encodable.encode_nat]
  rw [e] at h1
  omega

/-- **El bombeo no crea información, con el `O(log i)` a la vista**: `K ⟦x ++ yⁱ ++ z⟧ ≤ K ⟦(x, y, z)⟧ + 24 · |i| + c`,
con `|i|` el número de bits de `i`. -/
theorem bombeo_no_crea_log : ∃ c, ∀ (i : ℕ) (x y z : List Bool),
    K (Encodable.encode (x ++ (List.replicate i y).flatten ++ z)) ≤
      K (Encodable.encode (x, y, z)) + 24 * Nat.size i + c := by
  obtain ⟨c, hc⟩ := bombeo_no_crea
  refine ⟨c + 9, fun i x y z => ?_⟩
  have h1 := hc i x y z
  have h2 := Kt_cota_superior i
  have h3 := K_le_Kt i
  omega

/-! ## 4. Un ejemplo en `Fin 8` -/

section Ejemplo

/-- Un contador de tres bits que para al llegar a `7`: `0, 1, …, 7, halt`. -/
def contador8 : Fin 8 → Option (Fin 8) := fun q => if q = 7 then none else some (q + 1)

/-- Un contador de tres bits que da la vuelta y no para: período `8`. -/
def vuelta8 : Fin 8 → Option (Fin 8) := fun q => some (q + 1)

example : traza contador8 0 8 = none := by decide
example : traza contador8 0 7 = some 7 := by decide

/-- El contador cae en la rama de parar, en `8 = card (Fin 8)` pasos, justo en el borde de la cota. -/
example : ∃ n ≤ Fintype.card (Fin 8), traza contador8 0 n = none := ⟨8, by simp, by decide⟩

/-- La vuelta cae en la otra rama: no para, y su traza tiene período `8` desde el principio. -/
example : ¬ ∃ n ≤ Fintype.card (Fin 8), traza vuelta8 0 n = none := by
  simp only [Fintype.card_fin]
  decide

example : ∀ n < 8, traza vuelta8 0 (n + 8) = traza vuelta8 0 n := by decide

/-- Y como no para en los primeros `8` pasos, no para nunca (`parar_o_ciclar`). -/
example : traza vuelta8 0 ∉ Para none := by
  rw [para_iff_acotado]
  simp only [Fintype.card_fin]
  decide

/- Mutantes (en el área de trabajo de la sesión, 25 nov 2026; los cuatro fallan):
* `parar_o_ciclar` con `n < card σ`: falla en `omega` (el `halt` es un estado más de `Option σ`); y es falso, porque
  `contador8` para justo en el paso `8`.
* `profundidad_por_costo` con `prof x + 4`: falla en `omega` (la constante es `K x ≥ 3`, no más).
* `bombeo_no_crea` sin el término `K i`: falla en `omega` (el número de copias hay que escribirlo).
* `memoria_acota_profundidad` sin `Simula`: falla en `assumption` (nada liga los estados con el costo de `evaln`). -/

/-- Tres bits: `card (Fin 8) ≤ 2^3`, así que el corte de `para_antes_de_dos_pow` es `8`. -/
example : traza contador8 0 ∈ Para none → ∃ n ≤ 2 ^ 3, traza contador8 0 n = none :=
  para_antes_de_dos_pow contador8 0 (by simp)

end Ejemplo

end Sagitta.Map.Informacion.MemoriaProfundidad
