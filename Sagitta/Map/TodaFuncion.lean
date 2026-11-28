import Sagitta.Map.Shannon

/-!
# Toda función tiene algún circuito

En el modelo de `Shannon.lean`, toda función de `n` bits la calcula algún circuito. Con esto la sucesión de tamaños
mínimos nunca vale `⊤`.

El camino:

1. **Semántica.** El valor de la compuerta `k` es su operación aplicada a los dos cables que lee, y un cable que
   todavía no se calculó (índice `≥ n + k`) vale `false` (`cables_compuerta`).
2. **Combinar.** De un circuito para `f` y otro para `g` sale uno para `op (f x) (g x)`: primero las compuertas
   del primero, después las del segundo con sus cables corridos, y una compuerta final (`calcula_combinar`).
3. **Forma normal disyuntiva.** `f x` es la disyunción, sobre las entradas `a` donde `f a` vale `true`, de «`x` es
   igual a `a`»; y «`x` es igual a `a`» es una conjunción de literales.

No se acota aquí el tamaño (la construcción da del orden de `n · 2ⁿ` compuertas): solo que el circuito existe.
-/

namespace Sagitta.Map
namespace Shannon

variable {n s : ℕ}

/-! ## 1. Semántica de un circuito -/

/-- Lo que todavía no se calculó vale `false`. -/
theorem paso_futuro (C : Circuito n s) (x : Fin n → Bool) :
    ∀ (m : ℕ) (w : Fin (n + s)), n + m ≤ w.val → paso C x m w = false
  | 0, w, h => by simp only [paso]; rw [dite_eq_right (by omega)]
  | m + 1, w, h => by
    simp only [paso]
    split_ifs with hm
    · rw [Function.update_of_ne]
      · exact paso_futuro C x m w (by omega)
      · intro e
        have := congrArg Fin.val e
        simp only [cableDe] at this
        omega
    · exact paso_futuro C x m w (by omega)

/-- Lo que ya se calculó no cambia. -/
theorem paso_estable (C : Circuito n s) (x : Fin n → Bool) (m : ℕ) (w : Fin (n + s)) (hw : w.val < n + m) :
    ∀ j, m + j ≤ s → paso C x (m + j) w = paso C x m w
  | 0, _ => rfl
  | j + 1, h => by
    show paso C x ((m + j) + 1) w = _
    simp only [paso]
    rw [dite_eq_left (by omega), Function.update_of_ne]
    · exact paso_estable C x m w hw j (by omega)
    · intro e
      have := congrArg Fin.val e
      simp only [cableDe] at this
      omega

theorem cables_de_paso (C : Circuito n s) (x : Fin n → Bool) {m : ℕ} (hm : m ≤ s) {w : Fin (n + s)}
    (hw : w.val < n + m) : cables C x w = paso C x m w := by
  have := paso_estable C x m w hw (s - m) (by omega)
  rw [show m + (s - m) = s by omega] at this
  exact this

/-- El cable `a` visto por la compuerta `k`: su valor final si ya se calculó, `false` si no. -/
def lee (C : Circuito n s) (x : Fin n → Bool) (k : ℕ) (a : Fin (n + s)) : Bool :=
  if a.val < n + k then cables C x a else false

theorem paso_eq_lee (C : Circuito n s) (x : Fin n → Bool) {k : ℕ} (hk : k ≤ s) (a : Fin (n + s)) :
    paso C x k a = lee C x k a := by
  unfold lee
  split_ifs with h
  · exact (cables_de_paso C x hk h).symm
  · exact paso_futuro C x k a (by omega)

/-- **Las entradas.** -/
theorem cables_entrada (C : Circuito n s) (x : Fin n → Bool) (w : Fin (n + s)) (h : w.val < n) :
    cables C x w = x ⟨w.val, h⟩ := by
  rw [cables_de_paso C x (m := 0) (Nat.zero_le _) (by omega)]
  simp only [paso]
  rw [dite_eq_left h]

/-- **Las compuertas.** La compuerta `k` aplica su operación a los dos cables que lee. -/
theorem cables_compuerta (C : Circuito n s) (x : Fin n → Bool) (k : Fin s) :
    cables C x (cableDe k) = (C.1 k).1.aplica (lee C x k (C.1 k).2.1) (lee C x k (C.1 k).2.2) := by
  rw [cables_de_paso C x (m := k.val + 1) k.isLt (by simp only [cableDe]; omega)]
  simp only [paso]
  rw [dite_eq_left k.isLt]
  simp only [Fin.eta, Function.update_self]
  rw [paso_eq_lee C x k.isLt.le, paso_eq_lee C x k.isLt.le]

/-! ## 2. Combinar dos circuitos -/

section Combinar

variable {t₁ t₂ : ℕ}

/-- Un cable del primer circuito, en el combinado: el mismo índice. -/
def izq (t₂ : ℕ) (w : Fin (n + t₁)) : Fin (n + (t₁ + t₂ + 1)) := ⟨w.val, by have := w.isLt; omega⟩

/-- Un cable del segundo circuito, en el combinado: las entradas quedan, las compuertas se corren `t₁`. -/
def der (t₁ : ℕ) (w : Fin (n + t₂)) : Fin (n + (t₁ + t₂ + 1)) :=
  if w.val < n then ⟨w.val, by omega⟩ else ⟨w.val + t₁, by have := w.isLt; omega⟩

theorem der_val (w : Fin (n + t₂)) : (der t₁ w).val = if w.val < n then w.val else w.val + t₁ := by
  unfold der; split_ifs <;> rfl

/-- **El circuito combinado**: las compuertas de `C₁`, las de `C₂` corridas, y una final con `op`. -/
def combinar (op : Op) (C₁ : Circuito n t₁) (C₂ : Circuito n t₂) : Circuito n (t₁ + t₂ + 1) :=
  (fun k =>
    if h₁ : k.val < t₁ then
      ((C₁.1 ⟨k.val, h₁⟩).1, izq t₂ (C₁.1 ⟨k.val, h₁⟩).2.1, izq t₂ (C₁.1 ⟨k.val, h₁⟩).2.2)
    else if h₂ : k.val - t₁ < t₂ then
      ((C₂.1 ⟨k.val - t₁, h₂⟩).1, der t₁ (C₂.1 ⟨k.val - t₁, h₂⟩).2.1, der t₁ (C₂.1 ⟨k.val - t₁, h₂⟩).2.2)
    else (op, izq t₂ C₁.2, der t₁ C₂.2),
   ⟨n + (t₁ + t₂), by omega⟩)

variable (op : Op) (C₁ : Circuito n t₁) (C₂ : Circuito n t₂)

theorem combinar_izq (k : Fin t₁) (h : k.val < t₁ + t₂ + 1) :
    (combinar op C₁ C₂).1 ⟨k.val, h⟩ = ((C₁.1 k).1, izq t₂ (C₁.1 k).2.1, izq t₂ (C₁.1 k).2.2) := by
  simp [combinar]

theorem combinar_der (k : Fin t₂) (h : t₁ + k.val < t₁ + t₂ + 1) :
    (combinar op C₁ C₂).1 ⟨t₁ + k.val, h⟩ = ((C₂.1 k).1, der t₁ (C₂.1 k).2.1, der t₁ (C₂.1 k).2.2) := by
  simp [combinar]

theorem combinar_fin (h : t₁ + t₂ < t₁ + t₂ + 1) :
    (combinar op C₁ C₂).1 ⟨t₁ + t₂, h⟩ = (op, izq t₂ C₁.2, der t₁ C₂.2) := by
  simp [combinar]

/-- Los cables del primer circuito valen lo mismo en el combinado. -/
theorem cables_izq (x : Fin n → Bool) :
    ∀ j (w : Fin (n + t₁)), w.val < j → cables (combinar op C₁ C₂) x (izq t₂ w) = cables C₁ x w := by
  intro j
  induction j with
  | zero => intro w h; omega
  | succ j ih =>
    intro w hw
    by_cases hn : w.val < n
    · rw [cables_entrada _ x _ (by simp only [izq]; exact hn), cables_entrada _ x _ hn]
      rfl
    · let k : Fin t₁ := ⟨w.val - n, by have := w.isLt; omega⟩
      have hw' : w = cableDe k := Fin.ext (by simp only [cableDe, k]; omega)
      have hk : izq t₂ w = cableDe (⟨k.val, by have := k.isLt; omega⟩ : Fin (t₁ + t₂ + 1)) :=
        Fin.ext (by simp only [izq, cableDe, k]; omega)
      have key : ∀ a : Fin (n + t₁),
          lee (combinar op C₁ C₂) x k.val (izq t₂ a) = lee C₁ x k.val a := by
        intro a
        unfold lee
        by_cases ha : a.val < n + k.val
        · rw [ite_eq_left (by simp only [izq]; exact ha), ite_eq_left ha]
          exact ih a (by simp only [k] at ha; omega)
        · rw [ite_eq_right (by simp only [izq]; exact ha), ite_eq_right ha]
      rw [hk, cables_compuerta, combinar_izq, congrArg (cables C₁ x) hw', cables_compuerta]
      dsimp only
      rw [key, key]

/-- Los cables del segundo circuito valen lo mismo en el combinado, corridos. -/
theorem cables_der (x : Fin n → Bool) :
    ∀ j (w : Fin (n + t₂)), w.val < j → cables (combinar op C₁ C₂) x (der t₁ w) = cables C₂ x w := by
  intro j
  induction j with
  | zero => intro w h; omega
  | succ j ih =>
    intro w hw
    by_cases hn : w.val < n
    · rw [cables_entrada _ x _ (by rw [der_val, ite_eq_left hn]; exact hn), cables_entrada _ x _ hn]
      congr 1
      exact Fin.ext (by simp only [der_val, ite_eq_left hn])
    · let k : Fin t₂ := ⟨w.val - n, by have := w.isLt; omega⟩
      have hw' : w = cableDe k := Fin.ext (by simp only [cableDe, k]; omega)
      have hk : der t₁ w = cableDe (⟨t₁ + k.val, by have := k.isLt; omega⟩ : Fin (t₁ + t₂ + 1)) :=
        Fin.ext (by rw [der_val, ite_eq_right hn]; simp only [cableDe, k]; omega)
      have key : ∀ a : Fin (n + t₂),
          lee (combinar op C₁ C₂) x (t₁ + k.val) (der t₁ a) = lee C₂ x k.val a := by
        intro a
        unfold lee
        have hiff : (der t₁ a).val < n + (t₁ + k.val) ↔ a.val < n + k.val := by
          rw [der_val]; split_ifs <;> omega
        by_cases ha : a.val < n + k.val
        · rw [ite_eq_left (hiff.mpr ha), ite_eq_left ha]
          exact ih a (by simp only [k] at ha; omega)
        · rw [ite_eq_right (fun h => ha (hiff.mp h)), ite_eq_right ha]
      rw [hk, cables_compuerta, combinar_der, congrArg (cables C₂ x) hw', cables_compuerta]
      dsimp only
      rw [key, key]

/-- **Combinar calcula la operación de las dos funciones.** -/
theorem calcula_combinar :
    calcula (combinar op C₁ C₂) = fun x => op.aplica (calcula C₁ x) (calcula C₂ x) := by
  funext x
  unfold calcula
  have hs : (combinar op C₁ C₂).2 = cableDe (⟨t₁ + t₂, by omega⟩ : Fin (t₁ + t₂ + 1)) :=
    Fin.ext (by simp only [combinar, cableDe])
  rw [hs, cables_compuerta, combinar_fin]
  dsimp only
  have h1 : lee (combinar op C₁ C₂) x (t₁ + t₂) (izq t₂ C₁.2) = cables C₁ x C₁.2 := by
    unfold lee
    rw [ite_eq_left (by simp only [izq]; have := C₁.2.isLt; omega)]
    exact cables_izq op C₁ C₂ x _ C₁.2 (Nat.lt_succ_self _)
  have h2 : lee (combinar op C₁ C₂) x (t₁ + t₂) (der t₁ C₂.2) = cables C₂ x C₂.2 := by
    unfold lee
    rw [ite_eq_left (by rw [der_val]; have := C₂.2.isLt; split_ifs <;> omega)]
    exact cables_der op C₁ C₂ x _ C₂.2 (Nat.lt_succ_self _)
  rw [h1, h2]

end Combinar

/-! ## 3. Toda función -/

/-- `f` la calcula algún circuito. -/
def Calculable (f : (Fin n → Bool) → Bool) : Prop := ∃ t, ∃ C : Circuito n t, calcula C = f

/-- Un circuito de una compuerta que lee su propio cable, todavía sin calcular: vale siempre `false`. -/
def falso (n : ℕ) : Circuito n 1 := (fun _ => (Op.o, ⟨n, by omega⟩, ⟨n, by omega⟩), ⟨n, by omega⟩)

/-- Un circuito sin compuertas que devuelve la entrada `i`. -/
def proy (i : Fin n) : Circuito n 0 := (fun k => k.elim0, ⟨i.val, by omega⟩)

theorem calculable_falso : Calculable (fun _ : Fin n → Bool => false) := by
  refine ⟨1, falso n, ?_⟩
  funext x
  unfold calcula
  have : (falso n).2 = cableDe (0 : Fin 1) := Fin.ext (by simp [falso, cableDe])
  rw [this, cables_compuerta]
  simp [falso, lee, Op.aplica]

theorem calculable_proy (i : Fin n) : Calculable (fun x : Fin n → Bool => x i) := by
  refine ⟨0, proy i, ?_⟩
  funext x
  unfold calcula
  rw [cables_entrada _ _ _ (by simp only [proy]; exact i.isLt)]
  rfl

theorem calculable_op (op : Op) {f g : (Fin n → Bool) → Bool} (hf : Calculable f) (hg : Calculable g) :
    Calculable (fun x => op.aplica (f x) (g x)) := by
  obtain ⟨t₁, C₁, rfl⟩ := hf
  obtain ⟨t₂, C₂, rfl⟩ := hg
  exact ⟨_, combinar op C₁ C₂, calcula_combinar op C₁ C₂⟩

theorem calculable_no {f : (Fin n → Bool) → Bool} (hf : Calculable f) :
    Calculable (fun x => !f x) :=
  calculable_op Op.no hf hf

theorem calculable_verdadero : Calculable (fun _ : Fin n → Bool => true) :=
  calculable_no calculable_falso

/-- La conjunción de literales «`xᵢ = aᵢ`» sobre una lista de índices. -/
theorem calculable_conj (a : Fin n → Bool) :
    ∀ L : List (Fin n), Calculable (fun x => L.all (fun i => x i == a i))
  | [] => by simpa using (calculable_verdadero (n := n))
  | i :: L => by
    have hlit : Calculable (fun x : Fin n → Bool => x i == a i) := by
      cases hai : a i
      · simpa using calculable_no (calculable_proy i)
      · simpa using calculable_proy i
    have := calculable_op Op.y hlit (calculable_conj a L)
    simpa [Op.aplica] using this

/-- «`x` es igual a `a`». -/
theorem calculable_igual (a : Fin n → Bool) : Calculable (fun x => decide (x = a)) := by
  have := calculable_conj a (List.finRange n)
  convert this using 2 with x
  rw [Bool.eq_iff_iff]
  simp [funext_iff]

/-- La disyunción, sobre una lista de entradas, de «`f a` y `x` es igual a `a`». -/
theorem calculable_disy (f : (Fin n → Bool) → Bool) :
    ∀ L : List (Fin n → Bool), Calculable (fun x => L.any (fun a => f a && decide (x = a)))
  | [] => by simpa using (calculable_falso (n := n))
  | a :: L => by
    cases hfa : f a
    · simpa [hfa] using calculable_disy f L
    · have := calculable_op Op.o (calculable_igual a) (calculable_disy f L)
      simpa [hfa, Op.aplica] using this

/-- **Toda función de `n` bits la calcula algún circuito.** -/
theorem toda_funcion_calculable (f : (Fin n → Bool) → Bool) : Calculable f := by
  have := calculable_disy f (Finset.univ : Finset (Fin n → Bool)).toList
  convert this using 2 with x
  rw [Bool.eq_iff_iff]
  simp

end Shannon
end Sagitta.Map
