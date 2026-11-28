import Sagitta.Map.SigmaBuss

/-!
# Sucesiones en un número: la colección aguda (R5b, parte 3)

Para llevar «para todo `x ≤ |t|` existe `y ≤ s(x)` con `δ`» a un solo «existe», los `|t| + 1` testigos se guardan
en un número `w`, uno por dígito en base `D = 2^|S|`, con `S` una cota de todos ellos. Aquí están los programas y lo
que cumplen en ℕ.

* **`unosHasta`**: `2^min(|u|, x) - 1`, un número de largo exactamente `min(|u|, x)`. Con él se calcula `D^x` sin
  iterar `x` veces: `D^x = S # (2^x - 1)`.
* **`size_dos_pow_menos_uno`**: `|2^m - 1| = m`.
* **`digito`**: lo que cumplen los dígitos de una suma `c + g · D^m`.
-/

namespace Sagitta.Map
namespace Cobham

/-- `|2^m - 1| = m`. -/
theorem size_dos_pow_menos_uno (m : ℕ) : Nat.size (2 ^ m - 1) = m := by
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  apply le_antisymm
  · exact Nat.size_le.mpr (by omega)
  · rcases m with _ | m
    · exact Nat.zero_le _
    · by_contra h
      push Not at h
      have h1 := Nat.lt_size_self (2 ^ (m + 1) - 1)
      have h2 : 2 ^ Nat.size (2 ^ (m + 1) - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      have h3 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      have h4 : 0 < 2 ^ m := Nat.two_pow_pos m
      omega

/-- **Un número de largo dado.** Con argumentos `(u, x)`: `2^min(|u|, x) - 1`. Es una recursión sobre los bits de `u`
que agrega un `1` mientras el largo no pase de `x`. -/
def unosHasta : Cob 2 :=
  .rn .cero
    (c3 .cond (c2 .resta (c1 .largo (.proy 0)) (.proy 2))
      (c1 .suc (c2 .prod (c1 .suc (c1 .suc .cero)) (.proy 1))) (.proy 1))
    (c2 .smash (.proy 0) uno)

theorem unosHasta_eval (x : ℕ) : ∀ u : ℕ, unosHasta.eval (Fin.cons u ![x]) = 2 ^ min (Nat.size u) x - 1 := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  by_cases hu : u = 0
  · subst hu; rw [unosHasta, eval_rec_cero]; simp
  · rw [unosHasta, eval_rec_pos _ _ _ _ hu, ← unosHasta,
      ih (u / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hu) (by decide))]
    have hs : Nat.size u = Nat.size (u / 2) + 1 := Acotada.size_mitad hu
    simp only [eval_c3, eval_c2, eval_c1, eval_cond, eval_resta, eval_largo, eval_proy, eval_suc, eval_prod,
      eval_cero, eval_uno, Fin.cons_zero, Fin.cons_one]
    change min (if Nat.size u - (Fin.cons (2 ^ min (Nat.size (u / 2)) x - 1) ![x] : Fin 2 → ℕ) 1 = 0 then _ else _)
      (2 ^ (Nat.size u * Nat.size 1)) = _
    simp only [Fin.cons_one, Matrix.cons_val_zero, Nat.size_one, Nat.mul_one]
    rw [hs]
    generalize Nat.size (u / 2) = m
    have hP : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hx : m + 1 ≤ x
    · rw [min_eq_left (show m ≤ x by omega), min_eq_left hx, h2]
      simp only [show m + 1 - x = 0 by omega, ↓reduceIte]
      generalize 2 ^ m = P at hP ⊢
      omega
    · rw [min_eq_right (show x ≤ m by omega), min_eq_right (show x ≤ m + 1 by omega)]
      simp only [show m + 1 - x ≠ 0 by omega, ↓reduceIte]
      have : 2 ^ x ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega

/-- **Los dígitos** en base `D` de `c + g · D^m`, con `c < D^m` y `g < D`: el `m`-ésimo es `g`, los anteriores son
los de `c`. -/
theorem digito (D m c g x : ℕ) (hD : 0 < D) (hc : c < D ^ m) (hg : g < D) (hx : x ≤ m) :
    (c + g * D ^ m) / D ^ x % D = if x = m then g else c / D ^ x % D := by
  have hDx : 0 < D ^ x := pow_pos hD x
  split
  · rename_i h; subst h
    rw [Nat.add_mul_div_right _ _ hDx, Nat.div_eq_of_lt hc, Nat.zero_add, Nat.mod_eq_of_lt hg]
  · rename_i h
    have hlt : x < m := lt_of_le_of_ne hx h
    have e : g * D ^ m = (g * D ^ (m - x - 1) * D) * D ^ x := by
      rw [show m = (m - x - 1) + 1 + x by omega, Nat.pow_add, Nat.pow_succ]
      simp only [show m - x - 1 + 1 + x - x - 1 = m - x - 1 by omega]
      ring
    rw [e, Nat.add_mul_div_right _ _ hDx, Nat.add_mul_mod_self_right]

/-- El mínimo, como programa: `min(G, S)` con `S` sin la última variable. -/
def recorte {k : ℕ} (G : Cob (k + 1)) (S : Cob k) : Cob (k + 1) := c3 .cond (c2 .resta G (levantar S)) G (levantar S)

theorem recorte_eval {k : ℕ} (G : Cob (k + 1)) (S : Cob k) (z : Fin k → ℕ) (x : ℕ) :
    (recorte G S).eval (Fin.snoc z x) = min (G.eval (Fin.snoc z x)) (S.eval z) := by
  simp only [recorte, eval_c3, eval_c2, eval_cond, eval_resta, levantar_eval, Fin.init_snoc]
  split <;> omega

/-- **Armar la sucesión.** Recursión sobre los bits de `u` (el primer argumento), con parámetros `z`: al llegar a
largo `ℓ` se agrega `min(G(z, ℓ), S(z)) · D^ℓ`, con `D = 2^|S(z)|`. -/
def armar {k : ℕ} (G : Cob (k + 1)) (S : Cob k) : Cob (k + 1) :=
  .rn ((recorte G S).comp (Fin.snoc (fun i => .proy i) .cero))
    (c2 .suma (.proy 1)
      (c2 .prod ((recorte G S).comp (Fin.snoc (fun i => .proy i.succ.succ) (c1 .largo (.proy 0))))
        (c2 .smash (S.comp fun i => .proy i.succ.succ) (.proy 0))))
    (c2 .smash (S.comp fun i => .proy i.succ) (c1 .suc (c2 .prod (c1 .suc (c1 .suc .cero)) (.proy 0))))

theorem comp_snoc_eval {n m : ℕ} (f : Cob (m + 1)) (gs : Fin m → Cob n) (g : Cob n) (v : Fin n → ℕ) :
    (Cob.comp f (Fin.snoc gs g)).eval v = f.eval (Fin.snoc (fun i => (gs i).eval v) (g.eval v)) := by
  have := ap_comp_snoc (M := ℕ) f gs g v
  simpa only [ap_nat] using this

/-- **Lo que cumple la sucesión armada**: no pasa de `D^(|u|+1)`, y su dígito `x` es `min(G(z, x), S(z))` para todo
`x ≤ |u|`. -/
theorem armar_eval {k : ℕ} (G : Cob (k + 1)) (S : Cob k) (z : Fin k → ℕ) : ∀ u : ℕ,
    (armar G S).eval (Fin.cons u z) < (2 ^ Nat.size (S.eval z)) ^ (Nat.size u + 1) ∧
    ∀ x ≤ Nat.size u, (armar G S).eval (Fin.cons u z) / (2 ^ Nat.size (S.eval z)) ^ x % 2 ^ Nat.size (S.eval z) =
      min (G.eval (Fin.snoc z x)) (S.eval z) := by
  set D := 2 ^ Nat.size (S.eval z) with hDdef
  have hD : 0 < D := Nat.two_pow_pos _
  have hgD : ∀ x, min (G.eval (Fin.snoc z x)) (S.eval z) < D := fun x =>
    lt_of_le_of_lt (min_le_right _ _) (Nat.lt_size_self _)
  have hz : (fun i : Fin k => (Cob.proy i : Cob k).eval z) = z := rfl
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  by_cases hu : u = 0
  · subst hu
    rw [armar, eval_rec_cero, comp_snoc_eval, hz, eval_cero, recorte_eval]
    simp only [Nat.size_zero, Nat.zero_add, Nat.pow_one, Nat.le_zero, forall_eq, Nat.pow_zero, Nat.div_one]
    exact ⟨hgD 0, Nat.mod_eq_of_lt (hgD 0)⟩
  · obtain ⟨ih1, ih2⟩ := ih (u / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hu) (by decide))
    have hs : Nat.size u = Nat.size (u / 2) + 1 := Acotada.size_mitad hu
    rw [armar, eval_rec_pos _ _ _ _ hu, ← armar]
    generalize (armar G S).eval (Fin.cons (u / 2) z) = c at ih1 ih2
    have eS : ∀ (a b : ℕ), (S.comp fun i => Cob.proy i.succ.succ).eval (Fin.cons a (Fin.cons b z)) = S.eval z :=
      fun a b => rfl
    have eS1 : (S.comp fun i => Cob.proy i.succ).eval (Fin.cons u z) = S.eval z := rfl
    have eG : ((recorte G S).comp (Fin.snoc (fun i => Cob.proy i.succ.succ) (c1 .largo (.proy 0)))).eval
        (Fin.cons u (Fin.cons c z)) = min (G.eval (Fin.snoc z (Nat.size u))) (S.eval z) := by
      rw [comp_snoc_eval, ← recorte_eval]; rfl
    simp only [eval_c2, eval_suma, eval_prod, eval_proy, eS, eS1, eG, eval_c1, eval_suc, eval_cero,
      Fin.cons_zero, Fin.cons_one]
    have hsm1 : Cob.smash.eval ![S.eval z, u] = D ^ Nat.size u := by
      change 2 ^ (Nat.size (S.eval z) * Nat.size u) = _; rw [Nat.pow_mul]
    have hsm2 : Cob.smash.eval ![S.eval z, (0 + 1 + 1) * u + 1] = D ^ (Nat.size u + 1) := by
      change 2 ^ (Nat.size (S.eval z) * Nat.size ((0 + 1 + 1) * u + 1)) = _
      rw [show (0 + 1 + 1) * u + 1 = 2 * u + 1 by ring, Acotada.size_doble_mas_uno, Nat.pow_mul]
    simp only [hsm1, hsm2]
    rw [hs]
    set m := Nat.size (u / 2)
    have hlt : c + min (G.eval (Fin.snoc z (m + 1))) (S.eval z) * D ^ (m + 1) < D ^ (m + 1 + 1) := by
      have := hgD (m + 1)
      rw [Nat.pow_succ D (m + 1)]
      nlinarith
    rw [min_eq_left hlt.le]
    refine ⟨hlt, fun x hx => ?_⟩
    rw [digito D (m + 1) c _ x hD ih1 (hgD _) hx]
    split
    · rename_i h; rw [h]
    · exact ih2 x (by omega)

/-- La cota de la sucesión: `S # (2T + 1) = D^(|T|+1)`. -/
def cotaArmar {k : ℕ} (S T : Cob k) : Cob k := c2 .smash S (c1 .suc (c2 .prod (c1 .suc (c1 .suc .cero)) T))

theorem cotaArmar_eval {k : ℕ} (S T : Cob k) (z : Fin k → ℕ) :
    (cotaArmar S T).eval z = (2 ^ Nat.size (S.eval z)) ^ (Nat.size (T.eval z) + 1) := by
  simp only [cotaArmar, eval_c2, eval_c1, eval_suc, eval_prod, eval_cero]
  change 2 ^ (Nat.size (S.eval z) * Nat.size ((0 + 1 + 1) * T.eval z + 1)) = _
  rw [show (0 + 1 + 1) * T.eval z + 1 = 2 * T.eval z + 1 by ring, Acotada.size_doble_mas_uno, Nat.pow_mul]

/-- **Leer el dígito `x`** de `w` en base `D = 2^|S(z)|`, para `x ≤ |T(z)|`. Variables `(z, w, x)`. Calcula `D^x` como
`S # (2^x - 1)`, divide corriendo bits, y se queda con el resto. -/
def leer {k : ℕ} (S T : Cob k) : Cob (k + 2) :=
  c2 .resta (c2 correr (c2 .resta (c2 .smash (S.comp fun i => .proy (Fin.castSucc (Fin.castSucc i)))
      (c2 unosHasta (T.comp fun i => .proy (Fin.castSucc (Fin.castSucc i))) (.proy (Fin.last (k + 1))))) uno)
      (.proy (Fin.castSucc (Fin.last k))))
    (c2 .prod
      (c2 correr (S.comp fun i => .proy (Fin.castSucc (Fin.castSucc i)))
        (c2 correr (c2 .resta (c2 .smash (S.comp fun i => .proy (Fin.castSucc (Fin.castSucc i)))
          (c2 unosHasta (T.comp fun i => .proy (Fin.castSucc (Fin.castSucc i))) (.proy (Fin.last (k + 1))))) uno)
          (.proy (Fin.castSucc (Fin.last k)))))
      (c2 .smash (S.comp fun i => .proy (Fin.castSucc (Fin.castSucc i))) uno))

theorem leer_eval {k : ℕ} (S T : Cob k) (z : Fin k → ℕ) (w x : ℕ) (hx : x ≤ Nat.size (T.eval z)) :
    (leer S T).eval (Fin.snoc (Fin.snoc z w) x) =
      w / (2 ^ Nat.size (S.eval z)) ^ x % 2 ^ Nat.size (S.eval z) := by
  have eZ : ∀ c : Cob k, (c.comp fun i => Cob.proy (Fin.castSucc (Fin.castSucc i))).eval
      (Fin.snoc (Fin.snoc z w) x : Fin (k + 2) → ℕ) = c.eval z := fun c => by
    simp only [Cob.eval, Fin.snoc_castSucc]
  have eW : (Cob.proy (Fin.castSucc (Fin.last k)) : Cob (k + 2)).eval (Fin.snoc (Fin.snoc z w) x) = w := by
    simp only [eval_proy, Fin.snoc_castSucc, Fin.snoc_last]
  have eX : (Cob.proy (Fin.last (k + 1)) : Cob (k + 2)).eval (Fin.snoc (Fin.snoc z w) x) = x := by
    simp only [eval_proy, Fin.snoc_last]
  have eU : unosHasta.eval ![T.eval z, x] = 2 ^ x - 1 := by
    have := unosHasta_eval x (T.eval z)
    rw [min_eq_right hx] at this
    exact this
  have eSm : ∀ a b : ℕ, Cob.smash.eval ![a, b] = 2 ^ (Nat.size a * Nat.size b) := fun _ _ => rfl
  have eC : ∀ u p : ℕ, correr.eval ![u, p] = p / 2 ^ Nat.size u := fun u p => correr_eval p u
  simp only [leer, eval_c2, eZ, eW, eX, eU, eSm, eC, eval_resta, eval_prod, eval_uno, Nat.size_one, Nat.mul_one,
    size_dos_pow_menos_uno]
  rw [← Nat.pow_mul]
  generalize w / 2 ^ (Nat.size (S.eval z) * x) = Q
  generalize 2 ^ Nat.size (S.eval z) = D
  rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]

/-- **La colección en ℕ**: leer el dígito `x ≤ |T|` de la sucesión armada da `min(G(z, x), S(z))`, y la sucesión no
pasa de su cota. -/
theorem coleccion_nat {k : ℕ} (G : Cob (k + 1)) (S T : Cob k) (z : Fin k → ℕ) :
    ((armar G S).comp (Fin.cons T fun i => .proy i)).eval z ≤ (cotaArmar S T).eval z ∧
    ∀ x ≤ Nat.size (T.eval z),
      (leer S T).eval (Fin.snoc (Fin.snoc z (((armar G S).comp (Fin.cons T fun i => .proy i)).eval z)) x) =
        min (G.eval (Fin.snoc z x)) (S.eval z) := by
  have e : ((armar G S).comp (Fin.cons T fun i => .proy i)).eval z = (armar G S).eval (Fin.cons (T.eval z) z) := by
    simp only [Cob.eval]; congr 1; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  obtain ⟨h1, h2⟩ := armar_eval G S z (T.eval z)
  rw [e, cotaArmar_eval]
  exact ⟨h1.le, fun x hx => by rw [leer_eval S T z _ x hx, h2 x hx]⟩

/-! ## Parte 3b: la colección en el modelo saturado -/

/-- Leer, con `S` y `T` como valores: variables `(s, t, w, x)`. -/
def leerB : Cob 4 := leer (k := 2) (.proy 0) (.proy 1)

/-- La cota, con `S` y `T` como valores: variables `(s, t)`. -/
def cotaB : Cob 2 := cotaArmar (k := 2) (.proy 0) (.proy 1)

theorem leerB_eval (a b w x : ℕ) (hx : x ≤ Nat.size b) :
    leerB.eval ![a, b, w, x] = w / (2 ^ Nat.size a) ^ x % 2 ^ Nat.size a := by
  have e : (![a, b, w, x] : Fin 4 → ℕ) = Fin.snoc (Fin.snoc ![a, b] w) x := by
    funext i; fin_cases i <;> rfl
  rw [leerB, e, leer_eval _ _ _ _ _ hx]; rfl

theorem cotaB_eval (a b : ℕ) : cotaB.eval ![a, b] = (2 ^ Nat.size a) ^ (Nat.size b + 1) := by
  rw [cotaB, cotaArmar_eval]; rfl

section Modelo3

variable {M : Type} [LC.Structure M] [M ⊨ TC]

omit [M ⊨ TC] in
theorem ap_snoc_fun {n m : ℕ} (gs : Fin m → Cob n) (g : Cob n) (v : Fin n → M) :
    (fun i => ap (Fin.snoc (α := fun _ => Cob n) gs g i) v) = Fin.snoc (fun i => ap (gs i) v) (ap g v) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

/-- **El «para todo» pequeño como programa**: `no (buscar (no I) ≤ |T|)` da 0 justo cuando `I` da 0 en todo
`x ≤ |T|`. -/
theorem paraTodo_prog {k : ℕ} (I : Cob (k + 1)) (T : Cob k) (u : Fin k → M) :
    ap (no (c2 .resta (buscarUltima (no I) T) (c1 .largo T))) u = cero0 M ↔
      ∀ x, LeM x (ap Cob.largo ![ap T u]) → ap I (Fin.snoc u x) = cero0 M := by
  obtain ⟨h1, h2⟩ := buscarUltima_modelo (no I) T u
  rw [ap_no, ap_c2, ap_c1, ne_eq]
  change ¬ LeM _ _ ↔ _
  constructor
  · intro hB x hx
    by_contra hc
    exact hB (h2 x hx ((ap_no I _).mpr hc))
  · intro h hB
    exact (ap_no I _).mp (h1 hB) (h _ hB)

end Modelo3

/-- **La colección aguda, en el modelo saturado.** Si para todo `x ≤ |t(z)|` vale algo representable, ese «para
todo» es representable: los testigos de todos los `x` se juntan en uno solo, `w`, uno por dígito. -/
theorem rep_paraTodo (R : Realizacion) (hG : Generada R) (hS : Saturada R) {A : ℕ}
    {P : (Fin (A + 1) → R.M) → Prop} (hP : Rep R.M P) (t : Cob A) (mt : Mono t) :
    Rep R.M (fun z => ∀ x, LeM x (ap Cob.largo ![ap t z]) → P (Fin.snoc z x)) := by
  classical
  obtain ⟨δ, s, ms, h⟩ := hP
  let S : Cob A := enPunto s (c1 .largo t)
  let Zs : Fin A → Cob (A + 2) := fun i => .proy (Fin.castSucc (Fin.castSucc i))
  let W : Cob (A + 2) := .proy (Fin.castSucc (Fin.last A))
  let X : Cob (A + 2) := .proy (Fin.last (A + 1))
  let E : Cob (A + 2) := .comp leerB ![S.comp Zs, t.comp Zs, W, X]
  let I : Cob (A + 2) := yy (c2 .resta E (.comp s (Fin.snoc Zs X))) (.comp δ (Fin.snoc (Fin.snoc Zs X) E))
  have hv : ∀ (z : Fin A → R.M) (w x : R.M),
      (fun i => ap (Zs i) (Fin.snoc (Fin.snoc z w) x : Fin (A + 2) → R.M)) = z ∧
      ap W (Fin.snoc (Fin.snoc z w) x) = w ∧ ap X (Fin.snoc (Fin.snoc z w) x) = x := fun z w x => by
    refine ⟨funext fun i => ?_, ?_, ?_⟩ <;> simp [Zs, W, X, ap_proy, Fin.snoc_castSucc, Fin.snoc_last]
  have hE : ∀ (z : Fin A → R.M) (w x : R.M),
      ap E (Fin.snoc (Fin.snoc z w) x) = ap leerB ![ap S z, ap t z, w, x] := fun z w x => by
    obtain ⟨h1, h2, h3⟩ := hv z w x
    rw [ap_comp]; congr 1; funext i; fin_cases i
    · change ap (S.comp Zs) _ = _; rw [ap_comp, h1]; rfl
    · change ap (t.comp Zs) _ = _; rw [ap_comp, h1]; rfl
    · exact h2
    · exact h3
  have hI : ∀ (z : Fin A → R.M) (w x : R.M), ap I (Fin.snoc (Fin.snoc z w) x) = cero0 R.M ↔
      LeM (ap E (Fin.snoc (Fin.snoc z w) x)) (ap s (Fin.snoc z x)) ∧
        ap δ (Fin.snoc (Fin.snoc z x) (ap E (Fin.snoc (Fin.snoc z w) x))) = cero0 R.M := fun z w x => by
    obtain ⟨h1, -, h3⟩ := hv z w x
    simp only [I, ap_yy, leM_iff, ap_comp_snoc, ap_snoc_fun, h1, h3]
  let χ : Cob (A + 1) := no (c2 .resta (buscarUltima (no I) (levantar t)) (c1 .largo (levantar t)))
  have hχ : ∀ (z : Fin A → R.M) (w : R.M), ap χ (Fin.snoc z w) = cero0 R.M ↔
      ∀ x, LeM x (ap Cob.largo ![ap t z]) → ap I (Fin.snoc (Fin.snoc z w) x) = cero0 R.M := fun z w => by
    simp only [χ]; rw [paraTodo_prog, ap_levantar]
  have hSe : ∀ u : Fin A → ℕ, S.eval u = s.eval (Fin.snoc u (Nat.size (t.eval u))) := fun u => by
    have := ap_enPunto (M := ℕ) s (c1 .largo t) u
    simp only [ap_nat, eval_c1, eval_largo] at this; exact this
  have hmS : Mono S := fun v w hvw => by
    rw [hSe, hSe]
    refine ms _ _ fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact Nat.size_le_size (mt v w hvw)
    · simp only [Fin.snoc_castSucc]; exact hvw j
  have hcomp2 : ∀ {n : ℕ} (f : Cob 2) (a b : Cob n) (v : Fin n → R.M),
      ap (Cob.comp f ![a, b]) v = ap f ![ap a v, ap b v] := fun f a b v => by
    rw [ap_comp]; congr 1; funext i; fin_cases i <;> rfl
  refine ⟨χ, .comp cotaB ![S, t], fun v w hvw => ?_, fun z => ?_⟩
  · have e : ∀ u, (fun i => ((![S, t] : Fin 2 → Cob A) i).eval u) = ![S.eval u, t.eval u] := fun u => by
      funext i; fin_cases i <;> rfl
    simp only [Cob.eval]
    rw [e, e, cotaB_eval, cotaB_eval]
    calc (2 ^ Nat.size (S.eval v)) ^ (Nat.size (t.eval v) + 1)
        ≤ (2 ^ Nat.size (S.eval w)) ^ (Nat.size (t.eval v) + 1) :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (Nat.size_le_size (hmS v w hvw))) _
      _ ≤ (2 ^ Nat.size (S.eval w)) ^ (Nat.size (t.eval w) + 1) :=
          Nat.pow_le_pow_right Nat.one_le_two_pow (by have := Nat.size_le_size (mt v w hvw); omega)
  constructor
  · intro hall
    -- Los parámetros, como programas de las constantes.
    choose Nz Pz hPz using fun i => hG (z i)
    let N := Finset.univ.sup Nz
    have hNz : ∀ i, Nz i ≤ N := fun i => Finset.le_sup (f := Nz) (Finset.mem_univ i)
    let Q : Fin A → Cob N := fun i => (Pz i).renombrar (Fin.castLE (hNz i))
    have hQ : (fun i => ap (Q i) (pre R.ι N)) = z := funext fun i => by rw [ap_renombrar, hPz i]; rfl
    -- El pedido de los testigos, sobre `(c̄, x, y)`.
    let lc : Fin N → Fin (N + 1 + 1) := fun j => Fin.castAdd 1 (Fin.castAdd 1 j)
    let lx : Fin (N + 1 + 1) := Fin.castAdd 1 (Fin.natAdd N 0)
    let ly : Fin (N + 1 + 1) := Fin.natAdd (N + 1) 0
    let Zc : Fin A → Cob (N + 1 + 1) := fun i => (Q i).comp fun j => .proy (lc j)
    let θ : Cob (N + 1 + 1) := oo (no (c2 .resta (.proy lx) (c1 .largo (t.comp Zc))))
      (yy (c2 .resta (.proy ly) (s.comp (Fin.snoc Zc (.proy lx))))
        (δ.comp (Fin.snoc (Fin.snoc Zc (.proy lx)) (.proy ly))))
    have hθ : ∀ x y : R.M, ap θ (Fin.append (Fin.append (pre R.ι N) ![x]) ![y]) = cero0 R.M ↔
        ¬ LeM x (ap Cob.largo ![ap t z]) ∨
          (LeM y (ap s (Fin.snoc z x)) ∧ ap δ (Fin.snoc (Fin.snoc z x) y) = cero0 R.M) := fun x y => by
      have hZ : (fun i => ap (Zc i) (Fin.append (Fin.append (pre R.ι N) ![x]) ![y])) = z := by
        rw [← hQ]; funext i; simp only [Zc, ap_comp, ap_proy, lc, Fin.append_left]
      have hx : ap (Cob.proy lx) (Fin.append (Fin.append (pre R.ι N) ![x]) ![y]) = x := by
        simp only [lx, ap_proy, Fin.append_left, Fin.append_right, Matrix.cons_val_zero]
      have hy : ap (Cob.proy ly) (Fin.append (Fin.append (pre R.ι N) ![x]) ![y]) = y := by
        simp only [ly, ap_proy, Fin.append_right, Matrix.cons_val_zero]
      simp only [θ, ap_oo, ap_no, ap_yy, ne_eq, leM_iff, ap_c1, ap_comp, ap_snoc_fun, hZ, hx, hy]
    obtain ⟨L, G0, hG0⟩ := hS N 1 θ (fun xs => by
      rw [show xs = ![xs 0] from funext fun i => by fin_cases i; rfl]
      by_cases hx : LeM (xs 0) (ap Cob.largo ![ap t z])
      · obtain ⟨y, hy, hd⟩ := (h _).mp (hall _ hx)
        exact ⟨y, (hθ _ _).mpr (.inr ⟨hy, hd⟩)⟩
      · exact ⟨xs 0, (hθ _ _).mpr (.inl hx)⟩)
    -- Todo sobre las primeras `N'` constantes.
    let N' := max N L
    have hN : N ≤ N' := le_max_left _ _
    have hL : L ≤ N' := le_max_right _ _
    let Q' : Fin A → Cob N' := fun i => (Q i).renombrar (Fin.castLE hN)
    have hQ' : (fun i => ap (Q' i) (pre R.ι N')) = z := by
      rw [← hQ]; funext i; simp only [Q', ap_renombrar]; rfl
    let G1 : Cob (N' + 1) :=
      G0.comp (Fin.append (fun j : Fin L => .proy (Fin.castSucc (Fin.castLE hL j))) ![.proy (Fin.last N')])
    have hG1 : ∀ x : R.M, ap G1 (Fin.snoc (pre R.ι N') x) = ap G0 (Fin.append (pre R.ι L) ![x]) := fun x => by
      simp only [G1, ap_comp]; congr 1; funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · simp only [Fin.append_left, ap_proy, Fin.snoc_castSucc]; rfl
      · fin_cases j; simp [Fin.append_right, ap_proy, Fin.snoc_last]
    let S1 : Cob N' := S.comp Q'
    let T1 : Cob N' := t.comp Q'
    let code : Cob N' := (armar G1 S1).comp (Fin.cons T1 fun i => .proy i)
    have hS1 : ap S1 (pre R.ι N') = ap S z := by simp only [S1, ap_comp, hQ']
    have hT1 : ap T1 (pre R.ι N') = ap t z := by simp only [T1, ap_comp, hQ']
    -- Los hechos de ℕ, transferidos. Variables `(c̄', x)`.
    let Xl := ultima N'
    let Ql : Fin A → Cob (N' + 1) := fun i => levantar (Q' i)
    have hF := fun x => Enunciado.transferir (M := R.M)
      (.yy (.ec (c2 .resta (levantar code) (.comp cotaB ![levantar S1, levantar T1])) .cero)
        (.entonces (.ec (c2 .resta Xl (c1 .largo (levantar T1))) .cero)
          (.yy (.ec (.comp leerB ![levantar S1, levantar T1, levantar code, Xl]) (recorte G1 S1))
            (.entonces (.ec (c2 .resta G1 (s.comp (Fin.snoc Ql Xl))) .cero) (.ec (recorte G1 S1) G1)))))
      (fun v => by
        rw [← Fin.snoc_init_self v]
        generalize Fin.init v = u
        generalize v (Fin.last N') = x
        have e2 : ∀ (f : Cob 2) (a b : Cob (N' + 1)), (Cob.comp f ![a, b]).eval (Fin.snoc u x) =
            f.eval ![a.eval (Fin.snoc u x), b.eval (Fin.snoc u x)] := fun f a b => by
          simp only [Cob.eval]; congr 1; funext i; fin_cases i <;> rfl
        have e4 : ∀ (f : Cob 4) (a b c d : Cob (N' + 1)), (Cob.comp f ![a, b, c, d]).eval (Fin.snoc u x) =
            f.eval ![a.eval (Fin.snoc u x), b.eval (Fin.snoc u x), c.eval (Fin.snoc u x), d.eval (Fin.snoc u x)] :=
          fun f a b c d => by simp only [Cob.eval]; congr 1; funext i; fin_cases i <;> rfl
        have eX : Xl.eval (Fin.snoc u x) = x := by simp only [Xl, ultima, eval_proy, Fin.snoc_last]
        have eQ : (fun i => (Ql i).eval (Fin.snoc u x)) = fun i => (Q' i).eval u := by
          funext i; simp only [Ql, levantar_eval, Fin.init_snoc]
        obtain ⟨c1', c2'⟩ := coleccion_nat G1 S1 T1 u
        simp only [Enunciado.Vale, ap_nat, eval_cero, eval_c2, eval_resta, eval_c1, eval_largo, levantar_eval,
          Fin.init_snoc, e2, e4, eX, comp_snoc_eval, eQ]
        rw [cotaB_eval]
        have c1'' : code.eval u ≤ (cotaArmar S1 T1).eval u := c1'
        rw [cotaArmar_eval] at c1''
        refine ⟨by omega, fun hx => ?_⟩
        have hx' : x ≤ Nat.size (T1.eval u) := by omega
        refine ⟨?_, fun hg => ?_⟩
        · rw [leerB_eval _ _ _ _ hx', recorte_eval, ← c2' x hx', leer_eval _ _ _ _ _ hx']
        · rw [recorte_eval]
          apply min_eq_left
          have hS1e : S1.eval u = s.eval (Fin.snoc (fun i => (Q' i).eval u) (Nat.size (T1.eval u))) := hSe _
          rw [hS1e]
          refine (Nat.sub_eq_zero_iff_le.mp hg).trans (ms _ _ fun i => Fin.lastCases ?_ (fun j => ?_) i)
          · simp only [Fin.snoc_last]; exact hx'
          · simp only [Fin.snoc_castSucc]; exact le_refl _) (Fin.snoc (pre R.ι N') x)
    have ev : ∀ x : R.M, (fun i => ap (Ql i) (Fin.snoc (pre R.ι N') x)) = z := fun x => by
      rw [← hQ']; funext i; simp only [Ql, ap_levantar]
    have eX : ∀ x : R.M, ap Xl (Fin.snoc (pre R.ι N') x) = x := fun x => ap_ultima _ _
    simp only [Enunciado.Vale, ap_cero, leM_iff, ap_levantar, hcomp2, ap_comp, ap_snoc_fun, eX, ev, hS1, hT1,
      ap_c1] at hF
    refine ⟨ap code (pre R.ι N'), ?_, (hχ z _).mpr fun x hx => (hI z _ x).mpr ?_⟩
    · rw [hcomp2]
      have := (hF (ap code (pre R.ι N'))).1
      convert this using 2
    · have hθx := (hθ x _).mp (hG0 ![x])
      rcases hθx with hn | ⟨hy, hd⟩
      · exact absurd hx hn
      · rw [← hG1] at hy hd
        have h4 := (hF x).2 hx
        have hE' : ap E (Fin.snoc (Fin.snoc z (ap code (pre R.ι N'))) x) = ap G1 (Fin.snoc (pre R.ι N') x) := by
          rw [hE]
          have e1 : (![ap S z, ap t z, ap code (pre R.ι N'), x] : Fin 4 → R.M) =
              fun i => ap ((![levantar S1, levantar T1, levantar code, Xl] : Fin 4 → Cob (N' + 1)) i)
                (Fin.snoc (pre R.ι N') x) := by
            funext i; fin_cases i <;> simp [ap_levantar, hS1, hT1, eX]
          rw [e1]; exact h4.1.trans (h4.2 hy)
        rw [hE']
        exact ⟨hy, hd⟩
  · rintro ⟨w, -, hw⟩ x hx
    have := (hχ z w).mp hw x hx
    rw [hI] at this
    exact (h _).mpr ⟨_, this.1, this.2⟩

end Cobham
end Sagitta.Map
