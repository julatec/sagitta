import Sagitta.Map.Saturacion

/-!
# La inducción por bits en el modelo saturado (R4)

Cuarto paso de la ruta por modelos.

## Qué hay

* **Herramientas en un modelo cualquiera de `TC`**: composición con `c1`, `c2`, `c3`, «y» y «o» como programas.
* **`rec_cero`, `rec_pos`**: la ecuación de la recursión sobre la notación vale en el modelo, también en elementos
  no estándar.
* **`pind_abierta_modelo`**: la inducción por bits para una fórmula sin cuantificadores vale en todo modelo de
  `TC`. Sale de `pind_abierta` de `Cobham.lean`, que es un enunciado universal.
* **`pind_iterando`**: si el paso de la inducción lo da un programa, la inducción para «existe `y ≤ t(x)` con
  `δ(x, y) = 0`» vale: se itera el programa con la recursión con tope.
* **`pind_saturado`**, el teorema de R4: en el modelo saturado de `Saturacion.lean` vale la inducción por bits
  para «existe `y ≤ t(x)` con `δ(x, y) = 0`», con parámetros cualesquiera del modelo. La saturación da el paso como
  un programa (`pedidoPaso`), y los parámetros se pasan a programas de las constantes (`sust1`, `sust2`).

## Qué no hay

* **La forma de las fórmulas de Buss.** Aquí la fórmula es «existe `y ≤ t(x)` con `δ = 0`», con `δ` un programa: la
  forma Σᵇ₁ estricta, ya sin cuantificadores pequeños (los elimina `buscar`). Que toda fórmula Σᵇ₁ del lenguaje de
  Buss equivale en el modelo a una así, y que los axiomas BASIC valen, es R5.

Convención de este archivo: la variable de la recursión va primero, `Fin.cons x w`, como en `Cob.rn`.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language

section Modelo

variable {M : Type} [LC.Structure M] [M ⊨ TC]

theorem ap_c1 {n : ℕ} (f : Cob 1) (a : Cob n) (v : Fin n → M) : ap (c1 f a) v = ap f ![ap a v] := by
  rw [c1, ap_comp]; congr 1; funext i; fin_cases i; rfl

theorem ap_c2 {n : ℕ} (f : Cob 2) (a b : Cob n) (v : Fin n → M) :
    ap (c2 f a b) v = ap f ![ap a v, ap b v] := by
  rw [c2, ap_comp]; congr 1; funext i; fin_cases i <;> rfl

/-- Componer con un primer argumento y los demás pasados tal cual. -/
theorem ap_comp_cons {n m : ℕ} (f : Cob (m + 1)) (a : Cob n) (gs : Fin m → Cob n) (v : Fin n → M) :
    ap (Cob.comp f (Fin.cons a gs)) v = ap f (Fin.cons (ap a v) fun i => ap (gs i) v) := by
  rw [ap_comp]; congr 1; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem ap_proy_succ {n : ℕ} (x : M) (w : Fin n → M) :
    (fun i : Fin n => ap (Cob.proy i.succ) (Fin.cons x w : Fin (n + 1) → M)) = w := by
  funext i; rw [ap_proy, Fin.cons_succ]

/-- La mitad en un modelo. -/
def mitadM (x : M) : M := ap Cob.mitad ![x]

/-- La resta truncada en un modelo. -/
def restaM (x y : M) : M := ap Cob.resta ![x, y]

theorem ap_yy {n : ℕ} (p q : Cob n) (v : Fin n → M) :
    ap (yy p q) v = cero0 M ↔ ap p v = cero0 M ∧ ap q v = cero0 M := by
  have h := Enunciado.transferir (M := M)
    (.yy (.entonces (.ec (yy p q) .cero) (.yy (.ec p .cero) (.ec q .cero)))
      (.entonces (.yy (.ec p .cero) (.ec q .cero)) (.ec (yy p q) .cero)))
    (fun w => by
      simp only [Enunciado.Vale, ap_nat, eval_cero]
      exact ⟨(yy_vale p q w).mp, (yy_vale p q w).mpr⟩) v
  simp only [Enunciado.Vale, ap_cero] at h
  exact ⟨h.1, h.2⟩

theorem ap_oo {n : ℕ} (p q : Cob n) (v : Fin n → M) :
    ap (oo p q) v = cero0 M ↔ ap p v = cero0 M ∨ ap q v = cero0 M := by
  have h := Enunciado.transferir (M := M)
    (.yy (.entonces (.ec (oo p q) .cero) (.oo (.ec p .cero) (.ec q .cero)))
      (.entonces (.oo (.ec p .cero) (.ec q .cero)) (.ec (oo p q) .cero)))
    (fun w => by
      simp only [Enunciado.Vale, ap_nat, eval_cero]
      exact ⟨(oo_vale p q w).mp, (oo_vale p q w).mpr⟩) v
  simp only [Enunciado.Vale, ap_cero] at h
  exact ⟨h.1, h.2⟩

/-! ## La recursión en un modelo -/

/-- El valor en `⌊x/2⌋`, como programa de `(x, w)`. -/
def enMitad {n : ℕ} (f : Cob (n + 1)) : Cob (n + 1) :=
  .comp f (Fin.cons (c1 .mitad (.proy 0)) fun i => .proy i.succ)

theorem ap_enMitad {n : ℕ} (f : Cob (n + 1)) (x : M) (w : Fin n → M) :
    ap (enMitad f) (Fin.cons x w) = ap f (Fin.cons (mitadM x) w) := by
  rw [enMitad, ap_comp_cons, ap_c1, ap_proy, Fin.cons_zero, ap_proy_succ]; rfl

/-- El paso de la recursión, como programa de `(x, w)`. -/
def pasoRec {n : ℕ} (g : Cob n) (h : Cob (n + 2)) (k : Cob (n + 1)) : Cob (n + 1) :=
  .comp h (Fin.cons (.proy 0) (Fin.cons (enMitad (.rn g h k)) fun i => .proy i.succ))

theorem ap_pasoRec {n : ℕ} (g : Cob n) (h : Cob (n + 2)) (k : Cob (n + 1)) (x : M) (w : Fin n → M) :
    ap (pasoRec g h k) (Fin.cons x w) =
      ap h (Fin.cons x (Fin.cons (ap (Cob.rn g h k) (Fin.cons (mitadM x) w)) w)) := by
  rw [pasoRec, ap_comp_cons, ap_proy, Fin.cons_zero]
  congr 1; congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero]; exact ap_enMitad _ x w
  · simp only [Fin.cons_succ, ap_proy]

/-- **La base de la recursión vale en todo modelo.** -/
theorem rec_cero {n : ℕ} (g : Cob n) (h : Cob (n + 2)) (k : Cob (n + 1)) (w : Fin n → M) :
    ap (Cob.rn g h k) (Fin.cons (cero0 M) w) = ap g w := by
  have hT := Enunciado.transferir (M := M)
    (.entonces (.ec (.proy 0) .cero) (.ec (.rn g h k) (.comp g fun i => .proy i.succ)))
    (fun v => by
      simp only [Enunciado.Vale, ap_nat, eval_proy, eval_cero]
      intro h0
      rw [← Fin.cons_self_tail v, h0]
      change _ = g.eval fun i => v i.succ
      rw [eval_rec_cero]; rfl) (Fin.cons (cero0 M) w)
  simp only [Enunciado.Vale, ap_proy, Fin.cons_zero, ap_cero, ap_comp] at hT
  exact hT trivial

/-- **El paso de la recursión vale en todo modelo**: si `x ≠ 0` y el paso no pasa del tope, la recursión da el paso. -/
theorem rec_pos {n : ℕ} (g : Cob n) (h : Cob (n + 2)) (k : Cob (n + 1)) (w : Fin n → M) (x : M)
    (hx : x ≠ cero0 M)
    (htope : restaM (ap h (Fin.cons x (Fin.cons (ap (Cob.rn g h k) (Fin.cons (mitadM x) w)) w)))
      (ap k (Fin.cons x w)) = cero0 M) :
    ap (Cob.rn g h k) (Fin.cons x w) =
      ap h (Fin.cons x (Fin.cons (ap (Cob.rn g h k) (Fin.cons (mitadM x) w)) w)) := by
  have hT := Enunciado.transferir (M := M)
    (.entonces (.no (.ec (.proy 0) .cero))
      (.entonces (.ec (c2 .resta (pasoRec g h k) k) .cero) (.ec (.rn g h k) (pasoRec g h k))))
    (fun v => by
      simp only [Enunciado.Vale, ap_nat, eval_proy, eval_cero, eval_c2, eval_resta]
      intro h0 hle
      rw [← Fin.cons_self_tail v] at hle ⊢
      have e := ap_pasoRec (M := ℕ) g h k (v 0) (Fin.tail v)
      simp only [ap_nat, mitadM, eval_mitad] at e
      rw [e] at hle ⊢
      rw [eval_rec_pos _ _ _ _ h0, min_eq_left (by omega)]) (Fin.cons x w)
  simp only [Enunciado.Vale, ap_proy, Fin.cons_zero, ap_cero, ap_c2, ap_pasoRec] at hT
  exact hT hx htope

/-! ## La inducción por bits sin cuantificadores -/

/-- **La inducción por bits para una fórmula sin cuantificadores vale en todo modelo de `TC`.** -/
theorem pind_abierta_modelo {n : ℕ} (χ : Cob (n + 1)) (w : Fin n → M)
    (h0 : ap χ (Fin.cons (cero0 M) w) = cero0 M)
    (hpaso : ∀ x, x ≠ cero0 M → ap χ (Fin.cons (mitadM x) w) = cero0 M → ap χ (Fin.cons x w) = cero0 M)
    (b : M) : ap χ (Fin.cons b w) = cero0 M := by
  let P : Cob (n + 1) := c2 .resta (primerFallo χ) uno
  let enP : Cob (n + 1) := .comp χ (Fin.cons P fun i => .proy i.succ)
  let enP2 : Cob (n + 1) := .comp χ (Fin.cons (c1 .mitad P) fun i => .proy i.succ)
  let en0 : Cob (n + 1) := .comp χ (Fin.cons .cero fun i => .proy i.succ)
  have hT := Enunciado.transferir (M := M)
    (.entonces (.no (.ec χ .cero))
      (.oo (.no (.ec en0 .cero)) (.yy (.no (.ec P .cero)) (.yy (.ec enP2 .cero) (.no (.ec enP .cero))))))
    (fun v => by
      simp only [Enunciado.Vale, ap_nat, eval_cero]
      intro hb
      rw [← Fin.cons_self_tail v] at hb
      have := pind_abierta χ (Fin.tail v) (v 0) hb
      have eP : P.eval v = (primerFallo χ).eval (Fin.cons (v 0) (Fin.tail v)) - 1 := by
        simp only [P, eval_c2, eval_resta, eval_uno, Fin.cons_self_tail]
      have eT : ∀ q : Cob (n + 1), (fun i : Fin n => (Cob.proy i.succ : Cob (n + 1)).eval v) = Fin.tail v :=
        fun _ => rfl
      simp only [en0, enP, enP2, Cob.eval]
      rw [show (fun i => (Fin.cons Cob.cero (fun i => Cob.proy i.succ) : Fin (n + 1) → Cob (n + 1)) i |>.eval v)
          = Fin.cons 0 (Fin.tail v) from funext fun i => Fin.cases rfl (fun _ => rfl) i,
        show (fun i => (Fin.cons P (fun i => Cob.proy i.succ) : Fin (n + 1) → Cob (n + 1)) i |>.eval v)
          = Fin.cons (P.eval v) (Fin.tail v) from funext fun i => Fin.cases rfl (fun _ => rfl) i,
        show (fun i => (Fin.cons (c1 .mitad P) (fun i => Cob.proy i.succ) : Fin (n + 1) → Cob (n + 1)) i
          |>.eval v) = Fin.cons (P.eval v / 2) (Fin.tail v) from
          funext fun i => Fin.cases (by simp) (fun _ => rfl) i, eP]
      rcases this with h | ⟨h1, h2, h3⟩
      · exact .inl h
      · exact .inr ⟨h1, h2, h3⟩) (Fin.cons b w)
  by_contra hb
  simp only [Enunciado.Vale, ap_cero] at hT
  rcases hT hb with h | ⟨h1, h2, h3⟩
  · apply h
    simp only [en0, ap_comp_cons, ap_cero, ap_proy_succ]
    exact h0
  · apply h3
    simp only [enP, ap_comp_cons, ap_proy_succ] at h2 ⊢
    simp only [enP2, ap_comp_cons, ap_proy_succ, ap_c1] at h2
    exact hpaso _ h1 h2

/-! ## Iterar el paso -/

/-- `D(x, y)`: `δ(x, y, w) = 0` e `y ≤ t(x, w)`. Es «`y` atestigua la fórmula en `x`». -/
def Dt {n : ℕ} (δ : Cob (n + 2)) (t : Cob (n + 1)) (w : Fin n → M) (x y : M) : Prop :=
  ap δ (Fin.cons x (Fin.cons y w)) = cero0 M ∧ restaM y (ap t (Fin.cons x w)) = cero0 M

/-- `D` como un solo programa de `(x, y, w)`. -/
def dtProg {n : ℕ} (δ : Cob (n + 2)) (t : Cob (n + 1)) : Cob (n + 2) :=
  yy δ (c2 .resta (.proy 1) (.comp t (Fin.cons (.proy 0) fun i => .proy i.succ.succ)))

theorem ap_dtProg {n : ℕ} (δ : Cob (n + 2)) (t : Cob (n + 1)) (w : Fin n → M) (x y : M) :
    ap (dtProg δ t) (Fin.cons x (Fin.cons y w)) = cero0 M ↔ Dt δ t w x y := by
  rw [dtProg, ap_yy, ap_c2, ap_proy, ap_comp_cons, ap_proy]
  have : (fun i : Fin n => ap (Cob.proy i.succ.succ) (Fin.cons x (Fin.cons y w) : Fin (n + 2) → M)) = w :=
    funext fun i => by rw [ap_proy]; rfl
  rw [this]; rfl

/-- Componer con dos primeros argumentos y los demás pasados tal cual. -/
theorem ap_comp_cons2 {n m : ℕ} (f : Cob (m + 2)) (a b : Cob n) (gs : Fin m → Cob n) (v : Fin n → M) :
    ap (Cob.comp f (Fin.cons a (Fin.cons b gs))) v =
      ap f (Fin.cons (ap a v) (Fin.cons (ap b v) fun i => ap (gs i) v)) := by
  rw [ap_comp_cons]; congr 2; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl

/-- **Si el paso lo da un programa, la inducción vale.** Con `Γ` que lleva un testigo en `⌊x/2⌋` a uno en `x`, la
recursión con tope `rn γ Γ t` da un testigo en todo `x`. El tope no estorba: `D` ya pide `y ≤ t(x)`. -/
theorem pind_iterando {n : ℕ} (δ : Cob (n + 2)) (t : Cob (n + 1)) (w : Fin n → M) (γ : Cob n)
    (Γ : Cob (n + 2)) (h0 : Dt δ t w (cero0 M) (ap γ w))
    (hΓ : ∀ x r, x ≠ cero0 M → Dt δ t w (mitadM x) r → Dt δ t w x (ap Γ (Fin.cons x (Fin.cons r w))))
    (x : M) : Dt δ t w x (ap (Cob.rn γ Γ t) (Fin.cons x w)) := by
  let χ : Cob (n + 1) := .comp (dtProg δ t) (Fin.cons (.proy 0) (Fin.cons (.rn γ Γ t) fun i => .proy i.succ))
  have hχ : ∀ z, ap χ (Fin.cons z w) = cero0 M ↔ Dt δ t w z (ap (Cob.rn γ Γ t) (Fin.cons z w)) := by
    intro z
    rw [ap_comp_cons2, ap_proy, Fin.cons_zero, ap_proy_succ, ap_dtProg]
  rw [← hχ]
  refine pind_abierta_modelo χ w ?_ ?_ x
  · rw [hχ, rec_cero]; exact h0
  · intro z hz hm
    rw [hχ] at hm ⊢
    have hD := hΓ z _ hz hm
    rw [rec_pos γ Γ t w z hz hD.2]
    exact hD

/-! ## Cambiar los parámetros -/

/-- `δ` con sus parámetros dados por programas `Q` de otros parámetros. -/
def sust2 {n m : ℕ} (δ : Cob (n + 2)) (Q : Fin n → Cob m) : Cob (m + 2) :=
  .comp δ (Fin.cons (.proy 0) (Fin.cons (.proy 1) fun i => .comp (Q i) fun j => .proy j.succ.succ))

/-- `t` con sus parámetros dados por programas `Q` de otros parámetros. -/
def sust1 {n m : ℕ} (t : Cob (n + 1)) (Q : Fin n → Cob m) : Cob (m + 1) :=
  .comp t (Fin.cons (.proy 0) fun i => .comp (Q i) fun j => .proy j.succ)

theorem dt_sust {n m : ℕ} (δ : Cob (n + 2)) (t : Cob (n + 1)) (Q : Fin n → Cob m) (u : Fin m → M) (x y : M) :
    Dt (sust2 δ Q) (sust1 t Q) u x y ↔ Dt δ t (fun i => ap (Q i) u) x y := by
  have h2 : (fun i => ap (Cob.comp (Q i) fun j => Cob.proy j.succ.succ) (Fin.cons x (Fin.cons y u) :
      Fin (m + 2) → M)) = fun i => ap (Q i) u :=
    funext fun i => by rw [ap_comp]; congr 1; funext j; rw [ap_proy]; rfl
  have h1 : (fun i => ap (Cob.comp (Q i) fun j => Cob.proy j.succ) (Fin.cons x u : Fin (m + 1) → M)) =
      fun i => ap (Q i) u :=
    funext fun i => by rw [ap_comp]; congr 1; funext j; rw [ap_proy]; rfl
  have e1 : ap (sust2 δ Q) (Fin.cons x (Fin.cons y u)) = ap δ (Fin.cons x (Fin.cons y fun i => ap (Q i) u)) := by
    rw [sust2, ap_comp_cons2, ap_proy, ap_proy, h2]; rfl
  have e2 : ap (sust1 t Q) (Fin.cons x u) = ap t (Fin.cons x fun i => ap (Q i) u) := by
    rw [sust1, ap_comp_cons, ap_proy, h1]; rfl
  simp only [Dt, e1, e2]

end Modelo

/-! ## La inducción en el modelo saturado -/

section Saturado

/-- Lugares de `(c₀, …, c_{N-1}, x, y, y')` en el formato de `Saturada`. -/
def lugC (N : ℕ) (i : Fin N) : Fin (N + 2 + 1) := Fin.castAdd 1 (Fin.castAdd 2 i)
def lugX (N : ℕ) : Fin (N + 2 + 1) := Fin.castAdd 1 (Fin.natAdd N 0)
def lugY (N : ℕ) : Fin (N + 2 + 1) := Fin.castAdd 1 (Fin.natAdd N 1)
def lugY' (N : ℕ) : Fin (N + 2 + 1) := Fin.natAdd (N + 2) 0

variable {M : Type} [LC.Structure M] [M ⊨ TC]

omit [LC.Structure M] [M ⊨ TC] in
theorem lug_vale {N : ℕ} (c : Fin N → M) (x y y' : M) :
    let v := Fin.append (Fin.append c ![x, y]) ![y']
    v (lugX N) = x ∧ v (lugY N) = y ∧ v (lugY' N) = y' ∧ ∀ i, v (lugC N i) = c i := by
  refine ⟨?_, ?_, ?_, fun i => ?_⟩ <;>
    simp only [lugX, lugY, lugY', lugC, Fin.append_left, Fin.append_right, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- **El pedido del paso**: «`x = 0`, o no hay testigo en `⌊x/2⌋` con `y`, o `y'` es testigo en `x`». -/
def pedidoPaso {N : ℕ} (δ : Cob (N + 2)) (t : Cob (N + 1)) : Cob (N + 2 + 1) :=
  oo (oo (.proy (lugX N))
      (no (.comp (dtProg δ t)
        (Fin.cons (c1 .mitad (.proy (lugX N))) (Fin.cons (.proy (lugY N)) fun i => .proy (lugC N i))))))
    (.comp (dtProg δ t) (Fin.cons (.proy (lugX N)) (Fin.cons (.proy (lugY' N)) fun i => .proy (lugC N i))))

theorem pedidoPaso_vale {N : ℕ} (δ : Cob (N + 2)) (t : Cob (N + 1)) (c : Fin N → M) (x y y' : M) :
    ap (pedidoPaso δ t) (Fin.append (Fin.append c ![x, y]) ![y']) = cero0 M ↔
      x = cero0 M ∨ ¬ Dt δ t c (mitadM x) y ∨ Dt δ t c x y' := by
  obtain ⟨hx, hy, hy', hc⟩ := lug_vale c x y y'
  have hC : (fun i => ap (Cob.proy (lugC N i)) (Fin.append (Fin.append c ![x, y]) ![y'])) = c :=
    funext fun i => by rw [ap_proy, hc]
  rw [pedidoPaso, ap_oo, ap_oo, ap_no, ap_comp_cons2, ap_comp_cons2, ap_c1, ap_proy, ap_proy, ap_proy, hx, hy,
    hy', hC, ne_eq, ap_dtProg, ap_dtProg, or_assoc]
  rfl

end Saturado

/-- **R4: en el modelo saturado vale la inducción por bits** para «existe `y ≤ t(x)` con `δ(x, y) = 0`», con
parámetros `w` cualesquiera del modelo. El paso lo da la saturación como un programa; la recursión con tope lo
itera; la inducción sin cuantificadores cierra. -/
theorem pind_saturado (R : Realizacion) (hG : Generada R) (hS : Saturada R) {n : ℕ} (δ : Cob (n + 2))
    (t : Cob (n + 1)) (w : Fin n → R.M) (h0 : ∃ y, Dt δ t w (cero0 R.M) y)
    (hpaso : ∀ x, x ≠ cero0 R.M → (∃ y, Dt δ t w (mitadM x) y) → ∃ y, Dt δ t w x y) :
    ∀ x, ∃ y, Dt δ t w x y := by
  classical
  -- Los parámetros, como programas de las primeras `N` constantes.
  choose Nw Pw hPw using fun i => hG (w i)
  let N := Finset.univ.sup Nw
  have hNw : ∀ i, Nw i ≤ N := fun i => Finset.le_sup (f := Nw) (Finset.mem_univ i)
  let Q : Fin n → Cob N := fun i => (Pw i).renombrar (Fin.castLE (hNw i))
  have hQ : (fun i => ap (Q i) (pre R.ι N)) = w := funext fun i => by rw [ap_renombrar, hPw i]; rfl
  let δ1 := sust2 δ Q
  let t1 := sust1 t Q
  have hD1 : ∀ x y, Dt δ1 t1 (pre R.ι N) x y ↔ Dt δ t w x y := fun x y => by rw [dt_sust, hQ]
  -- El paso, de la saturación.
  have hpar : ∀ xs : Fin 2 → R.M, xs = ![xs 0, xs 1] := fun xs => by funext i; fin_cases i <;> rfl
  obtain ⟨L, G, hGL⟩ := hS N 2 (pedidoPaso δ1 t1) (fun xs => by
    rw [hpar xs]
    by_cases hx : xs 0 = cero0 R.M
    · exact ⟨cero0 R.M, (pedidoPaso_vale δ1 t1 _ _ _ _).mpr (Or.inl hx)⟩
    · by_cases hd : Dt δ1 t1 (pre R.ι N) (mitadM (xs 0)) (xs 1)
      · obtain ⟨y', hy'⟩ := hpaso (xs 0) hx ⟨xs 1, (hD1 _ _).mp hd⟩
        exact ⟨y', (pedidoPaso_vale δ1 t1 _ _ _ _).mpr (Or.inr (Or.inr ((hD1 _ _).mpr hy')))⟩
      · exact ⟨cero0 R.M, (pedidoPaso_vale δ1 t1 _ _ _ _).mpr (Or.inr (Or.inl hd))⟩)
  -- La base, como programa de las constantes.
  obtain ⟨y0, hy0⟩ := h0
  obtain ⟨N0, P0, rfl⟩ := hG y0
  -- Todo sobre las primeras `N'` constantes.
  let N' := max N (max L N0)
  have hN : N ≤ N' := le_max_left _ _
  have hL : L ≤ N' := (le_max_left _ _).trans (le_max_right _ _)
  have hN0 : N0 ≤ N' := (le_max_right _ _).trans (le_max_right _ _)
  let Qc : Fin N → Cob N' := fun i => .proy (Fin.castLE hN i)
  have hQc : (fun i => ap (Qc i) (pre R.ι N')) = pre R.ι N := funext fun i => by rw [ap_proy]; rfl
  let δ2 := sust2 δ1 Qc
  let t2 := sust1 t1 Qc
  have hD2 : ∀ x y, Dt δ2 t2 (pre R.ι N') x y ↔ Dt δ1 t1 (pre R.ι N) x y := fun x y => by rw [dt_sust, hQc]
  let γ : Cob N' := P0.renombrar (Fin.castLE hN0)
  have hγ : ap γ (pre R.ι N') = ap P0 (pre R.ι N0) := by rw [ap_renombrar]; rfl
  let Γ : Cob (N' + 2) :=
    .comp G (Fin.append (fun j : Fin L => .proy (Fin.castLE hL j).succ.succ) ![.proy 0, .proy 1])
  have hΓ : ∀ x r, ap Γ (Fin.cons x (Fin.cons r (pre R.ι N'))) = ap G (Fin.append (pre R.ι L) ![x, r]) := by
    intro x r
    rw [ap_comp]; congr 1; funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, ap_proy, Fin.cons_succ]; rfl
    · fin_cases j <;> simp [Fin.append_right, ap_proy]
  intro x
  have := pind_iterando δ2 t2 (pre R.ι N') γ Γ ((hD2 _ _).mpr (hγ ▸ hy0 |> (hD1 _ _).mpr))
    (fun z r hz hm => by
      rw [hD2] at hm ⊢
      have h := (pedidoPaso_vale δ1 t1 (pre R.ι N) z r _).mp (hGL ![z, r])
      rw [hΓ]
      rcases h with h | h | h
      · exact absurd h hz
      · exact absurd hm h
      · exact h) x
  exact ⟨_, (hD1 _ _).mp ((hD2 _ _).mp this)⟩



end Cobham
end Sagitta.Map
