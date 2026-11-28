import Sagitta.Map.SigmaBuss

/-!
# El teorema de KPT: el alumno y el maestro

Krajíček, Pudlák y Takeuti, «Bounded Arithmetic and the Polynomial Hierarchy», *Annals of Pure and Applied Logic* 52
(1991) 143–153.

**Reserva sobre el enunciado.** No se cotejó contra el texto de KPT ni contra el capítulo 7 de Krajíček (1995): el
enunciado sigue la versión estándar para **teorías universales** que citan Cook y Nguyen (2010), *Logical Foundations
of Proof Complexity*, la «KPT witnessing» para `∀x ∃y ∀z φ` con `φ` abierta:

> si una teoría universal `T` demuestra `∀x ∃y ∀z φ(x, y, z)` con `φ` sin cuantificadores, hay `k` y términos
> `t₁, …, t_k` tales que `T` demuestra
> `φ(x, t₁(x), z₁) ∨ φ(x, t₂(x, z₁), z₂) ∨ … ∨ φ(x, t_k(x, z₁, …, z_{k-1}), z_k)`.

Se lee como un juego: el **alumno** propone `y₁ = t₁(x)`; si no sirve, el **maestro** le da un contraejemplo `z₁`
(`φ(x, y₁, z₁)` falla); el alumno propone `y₂ = t₂(x, z₁)`, y así. En `k` rondas como mucho el alumno acierta.

## Qué teoría, y por qué

Se prueba para **`TC`** (`TeoriaCobham.lean`): todo lo universal verdadero en ℕ, en el lenguaje con un símbolo por
programa de Cobham. Es el papel de PV en este repo, y es universal, que es lo que pide la prueba: el submodelo
generado por `x` y los contraejemplos vuelve a ser modelo (`cerrar`). Ni S¹₂ ni T¹₂ son universales, así que la
prueba no se traslada. **Reserva sobre el enunciado** (revisión adversaria, 23 nov): el KPT original de 1991 ya se
enuncia para `Tⁱ₂`, con un número fijo de rondas, pero con un alumno más fuerte que polinomial (para T¹₂, funciones
`□ᵖ₂`, es decir `Pᴺᴾ`, según la versión estándar; no se cotejó el original). Lo dudoso es la forma con alumno
**polinomial** para S¹₂ o T¹₂, no la de rondas fijas. Por eso no se enuncia aquí un «KPT para S¹₂» con alumno
polinomial: un `Prop` así podría ser falso, no abierto.

* **probado**: `kpt` y su vuelta (`demuestraAEA_de_gana`, `kpt_iff`), para `TC` y `φ` dada como «un programa da 0»;
  `kpt_abierta`, para `φ` abierta, es decir una combinación booleana de ecuaciones (`Enunciado`);
* **no enunciado**: KPT para S¹₂ o T¹₂, y el colapso de la jerarquía polinomial si T¹₂ = S²₂ (ver «Qué no hay»).

## Cómo va la prueba de `kpt`

Se enumeran todos los programas, cada uno infinitas veces (`paso`). La ronda `j` del maestro es la condición
`D j`: «`φ(c₀, P_j(c₀, …, c_j), c_{j+1})` falla», con `c₀ = x` y `c_{j+1} = z_j`.

1. **Si el alumno nunca gana en ℕ**, todo conjunto finito de rondas es consistente: para `k` rondas, el alumno que
   juega `P₀, …, P_{k-1}` pierde en algún `x, z₀, …, z_{k-1}` de ℕ, y eso es un modelo. Por compacidad
   (`compacidad` de `Saturacion.lean`), todas juntas tienen un modelo.
2. **Se cierra** ese modelo (`Realizacion.cierre`): sigue cumpliendo las rondas (son universales) y todo elemento es
   un programa de las constantes. La hipótesis da un `y` para `x = c₀`; ese `y` es `P(c₀, …, c_{N-1})`, que aparece
   como `P_j` en alguna ronda `j ≥ N - 1`; la ronda `j` da un `z` contra `y`. Contradicción.

## Qué no hay

* **KPT para S¹₂ o T¹₂.** La prueba de aquí no se traslada: el modelo generado por los contraejemplos tendría que ser
  modelo de S¹₂, y la herramienta del repo para eso (`existe_saturada`, `esModeloS12_saturado`) arranca de una lista
  **finita** de condiciones, mientras que el juego necesita infinitas. Además, como se dijo arriba, no está claro que
  la forma de rondas fijas valga para S¹₂.
* **El colapso** («si T¹₂ = S²₂, la jerarquía polinomial colapsa», KPT 1991). No se enuncia: el repo no tiene S²₂
  (haría falta la clase de fórmulas `Σᵇ₂` y la inducción por bits para ella), ni la jerarquía polinomial por encima
  de `Σ₂` (`Colapso.Sigma2`), ni clases con consejo (solo `PsobrePoly`, por circuitos). Enunciarlo con piezas
  inventadas daría un `Prop` que no dice lo que dice KPT.
-/

namespace Sagitta.Map
namespace Cobham

open FirstOrder FirstOrder.Language

/-! ## El juego en ℕ -/

/-- **Lo que el alumno ve en la ronda `i`**: los contraejemplos de las rondas anteriores, `z_j` con `j < i`; el resto
se borra a `0`. Así un programa que mire más allá no gana nada. -/
def previas {k : ℕ} (zs : Fin k → ℕ) (i : Fin k) : Fin k → ℕ := fun j => if j < i then zs j else 0

/-- **El alumno gana en `k` rondas** con los programas `f₀, …, f_{k-1}`: para todo `x` y toda lista de contraejemplos
`z₀, …, z_{k-1}`, alguna ronda `i` acierta, `φ(x, f_i(x, z₀, …, z_{i-1}), z_i)`, con `φ` dada como `χ = 0`. Es la
disyunción de KPT, verdadera en ℕ. -/
def GanaAlumno (χ : Cob 3) (k : ℕ) (f : Fin k → Cob (k + 1)) : Prop :=
  ∀ (x : ℕ) (zs : Fin k → ℕ), ∃ i : Fin k, χ.eval ![x, (f i).eval (Fin.cons x (previas zs i)), zs i] = 0

/-- Sin rondas no se gana: la disyunción vacía es falsa. Control de que `GanaAlumno` no es trivial. -/
theorem no_gana_sin_rondas (χ : Cob 3) (f : Fin 0 → Cob 1) : ¬ GanaAlumno χ 0 f := fun h =>
  let ⟨i, _⟩ := h 0 Fin.elim0; i.elim0

/-- «La teoría `TC` demuestra `∀x ∃y ∀z φ(x, y, z)`», por modelos, con `φ` dada como `χ = 0`. -/
def DemuestraAEA (χ : Cob 3) : Prop :=
  ∀ (M : Type) [LC.Structure M] [M ⊨ TC], ∀ x : M, ∃ y : M, ∀ z : M, ap χ ![x, y, z] = cero0 M

/-! ## Las rondas del maestro -/

/-- Un programa de la enumeración, puesto sobre las constantes `c₀, …, c_j`; si pide más, el cero. -/
def ajustar (j : ℕ) (q : Σ N, Cob N) : Cob (j + 1) :=
  if h : q.1 ≤ j + 1 then q.2.renombrar (Fin.castLE h) else .cero

theorem ap_ajustar {M : Type} [LC.Structure M] [M ⊨ TC] (ι : ℕ → M) (j : ℕ) (q : Σ N, Cob N) (h : q.1 ≤ j + 1) :
    ap (ajustar j q) (pre ι (j + 1)) = ap q.2 (pre ι q.1) := by
  rw [ajustar, dite_eq_left h, ap_renombrar]
  rfl

/-- **La ronda `j`**: con el programa `P` de las constantes `c₀, …, c_j`, «`φ(c₀, P, c_{j+1})` falla». -/
def ronda (χ : Cob 3) (j : ℕ) (P : Cob (j + 1)) : Cond :=
  ⟨j + 2, 0, no (.comp χ ![.proy 0, P.renombrar (Fin.castLE (Nat.le_succ _)), .proy (Fin.last (j + 1))])⟩

theorem append_nada {M : Type} {n : ℕ} (u : Fin n → M) (ys : Fin 0 → M) :
    (Fin.append u ys : Fin (n + 0) → M) = u := by
  funext i; exact Fin.append_left u ys i

theorem ronda_vale {M : Type} [LC.Structure M] [M ⊨ TC] (ι : ℕ → M) (χ : Cob 3) (j : ℕ) (P : Cob (j + 1)) :
    (ronda χ j P).Vale ι ↔ ap χ ![ι 0, ap P (pre ι (j + 1)), ι (j + 1)] ≠ cero0 M := by
  rw [Cond.vale_iff]
  change (∀ ys : Fin 0 → M, ap (no _) (Fin.append (pre ι (j + 2)) ys) = cero0 M) ↔ _
  simp only [append_nada, ap_no, ap_comp]
  have e : (fun i : Fin 3 => ap (![Cob.proy 0, P.renombrar (Fin.castLE (Nat.le_succ _)),
      Cob.proy (Fin.last (j + 1))] i) (pre ι (j + 2))) = ![ι 0, ap P (pre ι (j + 1)), ι (j + 1)] := by
    funext i
    fin_cases i
    · simp [ap_proy, pre]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, ap_renombrar]
      rfl
    · simp [ap_proy, pre]
  rw [e]
  exact ⟨fun h => h Fin.elim0, fun h _ => h⟩

/-! ## El teorema -/

/-- **KPT para la teoría universal `TC`.** Si en todo modelo de `TC` vale `∀x ∃y ∀z φ(x, y, z)`, con `φ` dada como
`χ = 0`, el alumno gana en ℕ en un número finito `k` de rondas, con programas de Cobham que en la ronda `i` solo ven
`x` y los contraejemplos anteriores. -/
theorem kpt (χ : Cob 3) (h : DemuestraAEA χ) : ∃ (k : ℕ) (f : Fin k → Cob (k + 1)), GanaAlumno χ k f := by
  classical
  have : Nonempty (Σ N, Cob N) := ⟨⟨0, .cero⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Σ N, Cob N)
  let paso : (j : ℕ) → Cob (j + 1) := fun j => ajustar j (e (Nat.unpair j).1)
  let D : ℕ → Cond := fun j => ronda χ j (paso j)
  by_contra hno
  push Not at hno
  -- Cada número finito de rondas tiene modelo en ℕ.
  have hfin : ∀ n : ℕ, Consistente {C | ∃ j < n, C = D j} := by
    intro n
    let f : Fin n → Cob (n + 1) := fun i => (paso i).renombrar (Fin.castLE (Nat.succ_le_succ i.2.le))
    obtain ⟨x, zs, hxz⟩ : ∃ x zs, ∀ i : Fin n,
        χ.eval ![x, (f i).eval (Fin.cons x (previas zs i)), zs i] ≠ 0 := by
      have := hno n f
      simp only [GanaAlumno, not_forall, not_exists] at this
      exact this
    let ι : ℕ → ℕ := fun c => if c = 0 then x else if hc : c - 1 < n then zs ⟨c - 1, hc⟩ else 0
    refine ⟨{ M := ℕ, ι := ι }, ?_⟩
    rintro C ⟨j, hj, rfl⟩
    rw [ronda_vale]
    have hpre : pre ι (j + 1) = (Fin.cons x (previas zs ⟨j, hj⟩) : Fin (n + 1) → ℕ) ∘
        Fin.castLE (Nat.succ_le_succ hj.le) := by
      funext l
      refine Fin.cases ?_ (fun m => ?_) l
      · simp [pre, ι]
      · have hm : (m : ℕ) < j := m.2
        simp only [pre, ι, Function.comp_apply, Fin.val_succ, Nat.add_sub_cancel, Nat.add_one_ne_zero,
          ite_false, dite_eq_left (lt_trans hm hj)]
        rw [show (Fin.castLE (Nat.succ_le_succ hj.le) m.succ : Fin (n + 1)) =
          (⟨m, lt_trans hm hj⟩ : Fin n).succ from rfl, Fin.cons_succ]
        simp [previas, Fin.lt_def, hm]
    have h1 := hxz ⟨j, hj⟩
    simp only [f, ap_nat] at h1 ⊢
    rw [hpre]
    have e0 : ι 0 = x := by simp [ι]
    have e1 : ι (j + 1) = zs ⟨j, hj⟩ := by simp [ι, hj]
    rw [e0, e1]
    have h2 := ap_renombrar (M := ℕ) (paso j) (Fin.castLE (Nat.succ_le_succ hj.le))
      (Fin.cons x (previas zs ⟨j, hj⟩) : Fin (n + 1) → ℕ)
    simp only [ap_nat] at h2
    rw [h2] at h1
    exact h1
  -- Todas las rondas juntas, por compacidad.
  have hall : Consistente (Set.range D) := by
    refine compacidad _ fun F hF => ?_
    choose idx hidx using fun C : {C // C ∈ F} => hF C.2
    refine (hfin (Finset.univ.sup idx + 1)).mono fun C hC => ?_
    let c : {C // C ∈ F} := ⟨C, hC⟩
    exact show ∃ j < _, C = D j from ⟨idx c, Nat.lt_succ_of_le (Finset.le_sup (f := idx) (Finset.mem_univ c)),
      (hidx c).symm⟩
  obtain ⟨R0, hR0⟩ := hall
  let R := R0.cierre
  have hD : ∀ j, (D j).Vale R.ι := fun j => R0.vale_cierre (hR0 _ ⟨j, rfl⟩)
  obtain ⟨y, hy⟩ := h R.M (R.ι 0)
  obtain ⟨N, P, rfl⟩ := R0.cierre_programa y
  obtain ⟨a, ha⟩ := he ⟨N, P⟩
  have hN : N ≤ Nat.pair a N + 1 := (Nat.right_le_pair a N).trans (Nat.le_succ _)
  have hj := hD (Nat.pair a N)
  simp only [D, paso, Nat.unpair_pair, ha] at hj
  rw [ronda_vale, ap_ajustar R.ι _ ⟨N, P⟩ hN] at hj
  exact hj (hy _)

/-! ## La vuelta: si el alumno gana, `TC` demuestra `∀x ∃y ∀z φ` -/

/-- El programa de la ronda `i`, leído sobre `(x, z₀, …, z_{k-1})` con los contraejemplos de las rondas `≥ i`
borrados por el programa cero. -/
def rondaPrograma {k : ℕ} (χ : Cob 3) (f : Fin k → Cob (k + 1)) (i : Fin k) : Cob (k + 1) :=
  .comp χ ![.proy 0, .comp (f i) (Fin.cons (.proy 0) fun j => if j < i then .proy j.succ else .cero),
    .proy i.succ]

/-- La disyunción de KPT como `Enunciado` sobre `(x, z₀, …, z_{k-1})`. -/
def disyuncion {k : ℕ} (χ : Cob 3) (f : Fin k → Cob (k + 1)) : (l : ℕ) → l ≤ k → Enunciado (k + 1)
  | 0, _ => .no (.ec .cero .cero)
  | l + 1, h => .oo (disyuncion χ f l (Nat.le_of_succ_le h)) (.ec (rondaPrograma χ f ⟨l, h⟩) .cero)

theorem disyuncion_vale {M : Type} [LC.Structure M] [M ⊨ TC] {k : ℕ} (χ : Cob 3) (f : Fin k → Cob (k + 1))
    (v : Fin (k + 1) → M) : ∀ (l : ℕ) (hl : l ≤ k),
      (disyuncion χ f l hl).Vale v ↔ ∃ i : Fin k, (i : ℕ) < l ∧ ap (rondaPrograma χ f i) v = cero0 M
  | 0, _ => by simp [disyuncion, Enunciado.Vale]
  | l + 1, h => by
      simp only [disyuncion, Enunciado.Vale, disyuncion_vale χ f v l (Nat.le_of_succ_le h), ap_cero]
      constructor
      · rintro (⟨i, hi, hv⟩ | hv)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hv⟩
        · exact ⟨⟨l, h⟩, Nat.lt_succ_self l, hv⟩
      · rintro ⟨i, hi, hv⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact .inl ⟨i, hi, hv⟩
        · exact .inr (by rw [show (⟨l, h⟩ : Fin k) = i from Fin.ext hi.symm]; exact hv)

theorem ap_rondaPrograma {M : Type} [LC.Structure M] [M ⊨ TC] {k : ℕ} (χ : Cob 3) (f : Fin k → Cob (k + 1))
    (i : Fin k) (x : M) (zs : Fin k → M) :
    ap (rondaPrograma χ f i) (Fin.cons x zs) =
      ap χ ![x, ap (f i) (Fin.cons x fun j => if j < i then zs j else cero0 M), zs i] := by
  rw [rondaPrograma, ap_comp]
  congr 1
  funext t
  fin_cases t
  · simp [ap_proy]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, ap_comp]
    congr 1
    funext l
    refine Fin.cases ?_ (fun j => ?_) l
    · simp [ap_proy]
    · simp only [Fin.cons_succ]
      split_ifs <;> simp [ap_proy, ap_cero]
  · simp [ap_proy]

/-- **La vuelta de KPT.** Si el alumno gana en ℕ, en todo modelo de `TC` vale `∀x ∃y ∀z φ`: la disyunción es
universal y verdadera en ℕ, así que vale en el modelo, y se juega allí. Si ninguna respuesta del alumno sirviera, el
maestro tendría un contraejemplo en cada ronda y la disyunción fallaría. -/
theorem demuestraAEA_de_gana (χ : Cob 3) {k : ℕ} (f : Fin k → Cob (k + 1)) (hg : GanaAlumno χ k f) :
    DemuestraAEA χ := by
  classical
  intro M _ _ x
  by_contra hno
  push Not at hno
  -- La disyunción vale en `M`.
  have hdis := Enunciado.transferir (M := M) (disyuncion χ f k le_rfl) (fun v => by
    rw [disyuncion_vale χ f v k le_rfl]
    have hv : v = Fin.cons (v 0) (fun j => v j.succ) := by
      funext l; refine Fin.cases rfl (fun _ => rfl) l
    obtain ⟨i, hi⟩ := hg (v 0) (fun j => v j.succ)
    refine ⟨i, i.2, ?_⟩
    rw [hv, ap_rondaPrograma]
    simp only [ap_nat] at hi ⊢
    have e : (fun j => if j < i then v j.succ else cero0 ℕ) = previas (fun j => v j.succ) i := by
      funext j
      simp only [previas]
      split_ifs
      · rfl
      · simp [cero0, eval_cero]
    rw [e]; exact hi)
  -- El maestro contesta ronda por ronda.
  choose maestro hmaestro using hno
  let G : (Fin k → M) → Fin k → M := fun zs i => ap (f i) (Fin.cons x fun j => if j < i then zs j else cero0 M)
  have key : ∀ l ≤ k, ∃ zs : Fin k → M, ∀ i : Fin k, (i : ℕ) < l → ap χ ![x, G zs i, zs i] ≠ cero0 M := by
    intro l
    induction l with
    | zero => exact fun _ => ⟨fun _ => cero0 M, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ l ih =>
      intro hl
      obtain ⟨zs, hzs⟩ := ih (Nat.le_of_succ_le hl)
      let il : Fin k := ⟨l, hl⟩
      let zs' := Function.update zs il (maestro (G zs il))
      have hG : ∀ i : Fin k, (i : ℕ) ≤ l → G zs' i = G zs i := fun i hi => by
        simp only [G]
        congr 2
        funext j
        split_ifs with hj
        · exact Function.update_of_ne (fun e => by rw [e] at hj; exact absurd hj (by simp [Fin.lt_def, il]; omega)) _ _
        · rfl
      refine ⟨zs', fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · rw [hG i hi.le, show zs' i = zs i from Function.update_of_ne (fun e => by
          rw [e] at hi; exact absurd hi (lt_irrefl _)) _ _]
        exact hzs i hi
      · have e : i = il := Fin.ext hi
        subst e
        rw [hG il le_rfl, show zs' il = maestro (G zs il) from Function.update_self _ _ _]
        exact hmaestro _
  obtain ⟨zs, hzs⟩ := key k le_rfl
  obtain ⟨i, -, hi⟩ := (disyuncion_vale χ f _ k le_rfl).mp (hdis (Fin.cons x zs))
  rw [ap_rondaPrograma] at hi
  exact hzs i i.2 hi

/-- **KPT, las dos direcciones**: `TC` demuestra `∀x ∃y ∀z φ` si y solo si el alumno gana en un número finito de
rondas con programas de Cobham. -/
theorem kpt_iff (χ : Cob 3) : DemuestraAEA χ ↔ ∃ (k : ℕ) (f : Fin k → Cob (k + 1)), GanaAlumno χ k f :=
  ⟨kpt χ, fun ⟨_, f, hg⟩ => demuestraAEA_de_gana χ f hg⟩

/-! ## Para fórmulas abiertas -/

/-- **KPT para `φ` abierta**: una combinación booleana de ecuaciones entre programas (`Enunciado`). Si en todo modelo
de `TC` vale `∀x ∃y ∀z φ`, el alumno gana en ℕ en `k` rondas. Se pasa a programas con `programa_de_enunciado` en ℕ, y
la equivalencia se lleva a todo modelo porque es ella misma un enunciado verdadero en ℕ. -/
theorem kpt_abierta (φ : Enunciado 3)
    (h : ∀ (M : Type) [LC.Structure M] [M ⊨ TC], ∀ x : M, ∃ y : M, ∀ z : M, φ.Vale ![x, y, z]) :
    ∃ (k : ℕ) (f : Fin k → Cob (k + 1)), ∀ (x : ℕ) (zs : Fin k → ℕ), ∃ i : Fin k,
      φ.Vale ![x, (f i).eval (Fin.cons x (previas zs i)), zs i] := by
  obtain ⟨χ, hχ⟩ := programa_de_enunciado (M := ℕ) φ
  have hM : ∀ (M : Type) [LC.Structure M] [M ⊨ TC] (v : Fin 3 → M), ap χ v = cero0 M ↔ φ.Vale v := by
    intro M _ _ v
    have := Enunciado.transferir (M := M) (.yy (.entonces (.ec χ .cero) φ) (.entonces φ (.ec χ .cero)))
      (fun w => by
        simp only [Enunciado.Vale, ap_cero]
        exact ⟨(hχ w).mp, (hχ w).mpr⟩) v
    simp only [Enunciado.Vale, ap_cero] at this
    exact ⟨this.1, this.2⟩
  obtain ⟨k, f, hg⟩ := kpt χ fun M _ _ x => by
    obtain ⟨y, hy⟩ := h M x
    exact ⟨y, fun z => (hM M _).mpr (hy z)⟩
  refine ⟨k, f, fun x zs => ?_⟩
  obtain ⟨i, hi⟩ := hg x zs
  refine ⟨i, (hχ _).mp ?_⟩
  simp only [ap_nat, cero0, eval_cero]
  exact hi

/-- **Control**: la hipótesis de `kpt` se cumple. Con `φ(x, y, z) : y = x`, el alumno gana en una ronda con la
proyección `y = x`, y `kpt` lo encuentra; la vuelta lo confirma en todo modelo. -/
example : ∃ (k : ℕ) (f : Fin k → Cob (k + 1)), GanaAlumno (igual (.proy 1) (.proy 0)) k f := by
  refine kpt _ (demuestraAEA_de_gana _ (k := 1) (fun _ => .proy 0) fun x zs => ⟨0, ?_⟩)
  exact (igual_vale _ _ _).mpr rfl

end Cobham
end Sagitta.Map
