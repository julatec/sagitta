import Sagitta.Map.Conservacion
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Transfer

/-!
# Los programas de Cobham corren en tiempo polinomial (F4b)

La fase F4b del plan. Con ella se cierra la dirección difícil del
teorema de Buss, `Acotada.DefinibleEsPolinomial`: lo que S¹₂ define con una fórmula `Σᵇ₁` es de tiempo
polinomial. R5c ya dio que eso es un programa de Cobham (`definible_es_cobham`); aquí, que todo programa de
Cobham corre en una máquina de Turing en tiempo polinomial.

## De dónde sale la máquina

No se escribe ninguna máquina a mano. La biblioteca **cslib-frontier** (fijada en `99f02811`) certifica tiempo
polinomial en máquinas multicinta (`ComputableInPolyTime`) y trae:

* las operaciones de ℕ en binario (suma, resta, producto, desplazamiento, `Nat.size`, `2^k`, `min`, el
  condicional) y la táctica `polytime`, que las compone;
* las tuplas finitas `encPi` (`pi`, `pi_apply`);
* el bucle con **crecimiento acotado** (`iterateWithInput_of_bounded_growth`): iterar un paso polinomial una
  cantidad de veces dada en unario es polinomial si cada vuelta agranda el estado a lo sumo en un polinomio de la
  entrada;
* el puente con Mathlib (`computableInPolyTime_iff_tm2`): una máquina multicinta polinomial da una
  `TM2ComputableInPolyTime` de Mathlib, que es lo que mide `EsPolinomial`.

## Qué se prueba aquí

* **El puente de codificaciones** (`encodeNat_eq_bits`): el `encodeNat` de Mathlib, con que `CodBits ℕ` codifica
  los números, es `Nat.bits`, que es el `encNat` de cslib-frontier. Solo hace falta la vuelta,
  `esPolinomial_of_computable`; la ida no es inmediata, porque la `FinTM2` de Mathlib solo exige finito el
  alfabeto de la pila de entrada.
* **Cada constructor** (`cob_polinomial`). Las hojas las resuelve `polytime`; `comp` es composición con una
  tupla.
* **La recursión sobre la notación con tope**, la única pieza con contenido. Se calcula de arriba abajo: con
  `L = |x|`, se recorren los prefijos `z_j = x >>> (L - j)` (los `j` bits altos de `x`), de `z_0 = 0` a
  `z_L = x`, y en cada vuelta `r := min (H z_j r) (K z_j)`. Como `⌊z_{j+1}/2⌋ = z_j`, el invariante es
  `r = F(z_j)` (`iterar_paso`). Son `|x|` vueltas, un número que se da en unario sin salir de los polinomios. El
  **tope** `K` es lo que acota el estado: `r ≤ K(z, ȳ)` y `z ≤ x`, así que el estado crece a lo sumo en un
  polinomio de la entrada por vuelta. Sin el tope, el bucle no cumpliría la hipótesis del iterador; es el mismo
  motivo por el que Cobham lo pone.
-/

namespace Sagitta.Map
namespace Cobham

open Turing.MultiTapeTM

/-! ## El puente de codificaciones -/

/-- La codificación de Mathlib de los positivos es la lista de bits. -/
theorem encodePosNum_eq_bits (p : PosNum) : Computability.encodePosNum p = (p : ℕ).bits := by
  induction p with
  | one => simp [Computability.encodePosNum]
  | bit0 p ih =>
    rw [Computability.encodePosNum, PosNum.cast_bit0, ← two_mul,
      Nat.bit0_bits _ (PosNum.to_nat_pos p).ne', ih]
  | bit1 p ih =>
    rw [Computability.encodePosNum, PosNum.cast_bit1, ← two_mul, Nat.bit1_bits, ih]

/-- **`encodeNat` es `Nat.bits`**: los números se codifican igual en Mathlib y en cslib-frontier. -/
theorem encodeNat_eq_bits (n : ℕ) : Computability.encodeNat n = n.bits := by
  unfold Computability.encodeNat
  rcases h : (n : Num) with _ | p
  · have : n = 0 := by simpa using congrArg ((↑) : Num → ℕ) h
    simp [Computability.encodeNum, this]
  · have : n = (p : ℕ) := by simpa using congrArg ((↑) : Num → ℕ) h
    simp [Computability.encodeNum, encodePosNum_eq_bits, this]

theorem cod_nat_eq : (CodBits.toEncoding (α := ℕ)).encode = ⇑encNat := by
  funext n; exact encodeNat_eq_bits n

/-- **La vuelta del puente**: lo que cslib-frontier certifica en tiempo polinomial es `EsPolinomial`. -/
theorem esPolinomial_of_computable {f : ℕ → ℕ} (h : ComputableInPolyTime f encNat encNat) :
    EsPolinomial f := by
  unfold EsPolinomial EsPolinomialCon
  rw [cod_nat_eq]
  obtain ⟨h, -⟩ := computableInPolyTime_iff_tm2.mp h
  exact ⟨h⟩

/-! ## Tuplas: `Fin.tail` y `Fin.cons` -/

@[fun_prop]
theorem tail_polinomial {n : ℕ} (enc : ℕ ↪ List Bool) :
    ComputableInPolyTime (fun v : Fin (n + 1) → ℕ => Fin.tail v) (encPi enc) (encPi enc) :=
  ComputableInPolyTime.pi fun i => ComputableInPolyTime.pi_apply enc i.succ

@[fun_prop]
theorem cons_polinomial {n : ℕ} {α : Type} {input : α ↪ List Bool} {z : α → ℕ} {w : α → Fin n → ℕ}
    (hz : ComputableInPolyTime z input encNat) (hw : ComputableInPolyTime w input (encPi encNat)) :
    ComputableInPolyTime (fun a => (Fin.cons (z a) (w a) : Fin (n + 1) → ℕ)) input (encPi encNat) := by
  refine ComputableInPolyTime.pi fun i => ?_
  cases i using Fin.cases with
  | zero => simpa using hz
  | succ j => simpa [Function.comp_def] using (ComputableInPolyTime.pi_apply encNat j).comp hw

/-! ## La recursión sobre la notación, de arriba abajo -/

section Notacion

variable (a : ℕ) (H : ℕ → ℕ → ℕ) (K : ℕ → ℕ)

/-- El valor de la recursión en `z`, con el combustible justo. -/
def valor (z : ℕ) : ℕ := notacion a H K z z

theorem valor_cero : valor a H K 0 = a := by simp only [valor, notacion]

theorem valor_pos {z : ℕ} (hz : 0 < z) : valor a H K z = min (H z (valor a H K (z / 2))) (K z) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
  simp only [valor, notacion]
  rw [notacion_fuel a H K w ((w + 1) / 2) ((w + 1) / 2) (by omega) le_rfl]

/-- Una vuelta: pasar del prefijo de `j` bits al de `j + 1`. -/
def paso (x : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + 1, min (H (x >>> (x.size - (p.1 + 1))) p.2) (K (x >>> (x.size - (p.1 + 1)))))

theorem prefijo_mitad {x j : ℕ} (hj : j < x.size) :
    x >>> (x.size - (j + 1)) / 2 = x >>> (x.size - j) := by
  have : x.size - j = x.size - (j + 1) + 1 := by omega
  rw [this, Nat.shiftRight_succ]

theorem prefijo_pos {x j : ℕ} (hj : j < x.size) : 0 < x >>> (x.size - (j + 1)) := by
  rw [Nat.shiftRight_eq_div_pow]
  refine Nat.div_pos ?_ (Nat.pow_pos (by norm_num))
  by_contra h
  have := (Nat.size_le).mpr (lt_of_not_ge h)
  omega

/-- **El invariante del bucle**: después de `j` vueltas, el estado es `(j, F(z_j))`. -/
theorem iterar_paso (x : ℕ) : ∀ j ≤ x.size,
    (paso H K x)^[j] (0, a) = (j, valor a H K (x >>> (x.size - j)))
  | 0, _ => by
    have : x >>> x.size = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (Nat.lt_size_self x)
    simp [this, valor_cero]
  | j + 1, hj => by
    rw [Function.iterate_succ_apply', iterar_paso x j (by omega), paso]
    simp only [Prod.mk.injEq, true_and]
    rw [valor_pos a H K (prefijo_pos (by omega)), prefijo_mitad (by omega)]

theorem iterar_final (x : ℕ) : ((paso H K x)^[x.size] (0, a)).2 = notacion a H K x x := by
  rw [iterar_paso a H K x x.size le_rfl]
  simp [valor]

end Notacion

/-! ## Cada programa corre en tiempo polinomial -/

/-- El paso del bucle, como función de la entrada y el estado. -/
theorem paso_polinomial {n : ℕ} {H : (Fin (n + 2) → ℕ) → ℕ} {K : (Fin (n + 1) → ℕ) → ℕ}
    (hH : ComputableInPolyTime H (encPi encNat) encNat)
    (hK : ComputableInPolyTime K (encPi encNat) encNat) :
    ComputableInPolyTime (fun q : (Fin (n + 1) → ℕ) × (ℕ × ℕ) =>
      paso (fun x r => H (Fin.cons x (Fin.cons r (Fin.tail q.1) : Fin (n + 1) → ℕ)))
        (fun x => K (Fin.cons x (Fin.tail q.1))) (q.1 0) q.2)
      (encPair (encPi encNat) (encPair encNat encNat)) (encPair encNat encNat) := by
  have hmin : ComputableInPolyTime (fun q : (Fin (n + 1) → ℕ) × (ℕ × ℕ) =>
      min (H (Fin.cons (q.1 0 >>> ((q.1 0).size - (q.2.1 + 1)))
        (Fin.cons q.2.2 (Fin.tail q.1) : Fin (n + 1) → ℕ)))
        (K (Fin.cons (q.1 0 >>> ((q.1 0).size - (q.2.1 + 1))) (Fin.tail q.1))))
      (encPair (encPi encNat) (encPair encNat encNat)) encNat :=
    ComputableInPolyTime.binary_min' (by polytime) (by polytime)
  exact ComputableInPolyTime.pair (by polytime) hmin

/-- `|bits (j + 1)| ≤ |bits j| + 1`. -/
theorem size_succ_le (j : ℕ) : (j + 1).size ≤ j.size + 1 := by
  rw [Nat.size_le]
  have := Nat.lt_size_self j
  rw [pow_succ]
  omega

/-- **La recursión con tope** corre en tiempo polinomial si sus tres partes lo hacen. -/
theorem rn_polinomial {n : ℕ} {G : (Fin n → ℕ) → ℕ} {H : (Fin (n + 2) → ℕ) → ℕ}
    {K : (Fin (n + 1) → ℕ) → ℕ}
    (hG : ComputableInPolyTime G (encPi encNat) encNat)
    (hH : ComputableInPolyTime H (encPi encNat) encNat)
    (hK : ComputableInPolyTime K (encPi encNat) encNat) :
    ComputableInPolyTime (fun v : Fin (n + 1) → ℕ =>
      notacion (G (Fin.tail v))
        (fun x r => H (Fin.cons x (Fin.cons r (Fin.tail v) : Fin (n + 1) → ℕ)))
        (fun x => K (Fin.cons x (Fin.tail v))) (v 0) (v 0))
      (encPi encNat) encNat := by
  -- La salida de `K` mide a lo sumo un polinomio de su entrada.
  obtain ⟨d, e, hdeg⟩ := hK.exists_degree
  obtain ⟨c, hc⟩ := hdeg.2
  set step : (Fin (n + 1) → ℕ) → ℕ × ℕ → ℕ × ℕ := fun v =>
    paso (fun x r => H (Fin.cons x (Fin.cons r (Fin.tail v) : Fin (n + 1) → ℕ)))
      (fun x => K (Fin.cons x (Fin.tail v))) (v 0) with hstep
  have hloop : ComputableInPolyTime (fun v => (step v)^[(v 0).size] (0, G (Fin.tail v)))
      (encPi encNat) (encPair encNat encNat) := by
    refine ComputableInPolyTime.iterateWithInput_of_bounded_growth
      (growth := fun v => 2 + c * ((n + 1) * (2 * (encPi encNat v).length + 1) + 1) ^ e)
      (by polytime) (ComputableInPolyTime.pair
        (show ComputableInPolyTime (fun _ : Fin (n + 1) → ℕ => (0 : ℕ)) (encPi encNat) encNat by polytime)
        (show ComputableInPolyTime (fun v : Fin (n + 1) → ℕ => G (Fin.tail v)) (encPi encNat) encNat
          by polytime))
      (paso_polinomial hH hK) ⟨?_, ?_⟩
    · exact (PolyBounded.const 2).add ((PolyBounded.const c).mul
        ((((PolyBounded.const (n + 1)).mul (((PolyBounded.const 2).mul PolyBounded.self).add
          (PolyBounded.const 1))).add (PolyBounded.const 1)).pow e))
    · intro v p
      set z := v 0 >>> ((v 0).size - (p.1 + 1)) with hzdef
      have hz : z ≤ v 0 := Nat.shiftRight_le _ _
      -- La tupla con que se llama a `K` no es más larga, salvo un factor fijo, que la entrada.
      have htupla : (encPi encNat (Fin.cons z (Fin.tail v) : Fin (n + 1) → ℕ)).length ≤
          (n + 1) * (2 * (encPi encNat v).length + 1) := by
        have := length_encPi_le encNat (Fin.cons z (Fin.tail v) : Fin (n + 1) → ℕ)
          (bound := (encPi encNat v).length) (fun i => by
            cases i using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, encNat_apply, Nat.size_eq_bits_len]
              exact (Nat.size_le_size hz).trans
                (by simpa [encNat_apply, Nat.size_eq_bits_len] using length_le_encPi encNat v 0)
            | succ j => simpa [Fin.tail] using length_le_encPi encNat v j.succ)
        simpa using this
      have hK' := hc (Fin.cons z (Fin.tail v))
      have hr : (min (H (Fin.cons z (Fin.cons p.2 (Fin.tail v) : Fin (n + 1) → ℕ)))
          (K (Fin.cons z (Fin.tail v)))).size ≤ c * ((n + 1) * (2 * (encPi encNat v).length + 1) + 1) ^ e := by
        refine (Nat.size_le_size (min_le_right _ _)).trans ?_
        simp only [encNat_apply, Nat.size_eq_bits_len] at hK'
        exact hK'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have hj := size_succ_le p.1
      simp only [hstep, paso, length_encPair, encNat_apply, Nat.size_eq_bits_len]
      rw [← hzdef]
      omega
  have hfin := (ComputableInPolyTime.snd encNat encNat).comp hloop
  convert hfin using 1
  funext v
  simp only [Function.comp_apply, hstep]
  exact (iterar_final _ _ _ (v 0)).symm

/-- **F4b: todo programa de Cobham corre en tiempo polinomial.** -/
theorem cob_polinomial : ∀ {n : ℕ} (c : Cob n), ComputableInPolyTime c.eval (encPi encNat) encNat
  | _, .cero => by simp only [Cob.eval]; polytime
  | _, .proy i => by simp only [Cob.eval]; exact ComputableInPolyTime.pi_apply encNat i
  | _, .suc => by simp only [Cob.eval]; polytime
  | _, .suma => by simp only [Cob.eval]; polytime
  | _, .resta => by simp only [Cob.eval]; polytime
  | _, .prod => by simp only [Cob.eval]; polytime
  | _, .mitad => by
    have : (fun v : Fin 1 → ℕ => v 0 / 2) = fun v => v 0 >>> 1 := by
      funext v; simp [Nat.shiftRight_eq_div_pow]
    simp only [Cob.eval]; rw [this]; polytime
  | _, .largo => by
    simp only [Cob.eval]
    exact ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.pi_apply encNat 0))
  | _, .smash => by simp only [Cob.eval]; polytime
  | _, .cond => by simp only [Cob.eval]; polytime
  | _, .comp f gs => by
    have hf := cob_polinomial f
    have hgs := ComputableInPolyTime.pi fun i => cob_polinomial (gs i)
    simpa [Cob.eval, Function.comp_def] using hf.comp hgs
  | _, .rn g h k => by
    simp only [Cob.eval]
    exact rn_polinomial (cob_polinomial g) (cob_polinomial h) (cob_polinomial k)

/-! ## La dirección difícil del teorema de Buss -/

/-- `n ↦ ![n]`, de un número a la tupla de un elemento. -/
theorem uno_polinomial : ComputableInPolyTime (fun n : ℕ => ![n]) encNat (encPi encNat) :=
  ComputableInPolyTime.pi fun i => by
    rw [Fin.fin_one_eq_zero i]
    exact ComputableInPolyTime.of_eq fun _ => rfl

/-- **Buss, la dirección difícil**: lo que S¹₂ define con una fórmula `Σᵇ₁` es de tiempo polinomial. -/
theorem definibleEsPolinomial : Acotada.DefinibleEsPolinomial := by
  intro f hf
  obtain ⟨c, hc⟩ := definible_es_cobham f hf
  apply esPolinomial_of_computable
  have := (cob_polinomial c).comp uno_polinomial
  have hfun : (c.eval ∘ fun n : ℕ => ![n]) = f := funext fun n => hc n
  rwa [hfun] at this

end Cobham
end Sagitta.Map
