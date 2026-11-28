import Sagitta.Map.RaizMuertaFuerte
import Sagitta.Map.IntentoContradiccion
import CslibFrontier.Logics.Propositional.Resolution.Pigeonhole

/-!
# Detectores certificados por resolución general

Peldaño «aprendizaje de cláusulas» de la escalera de detectores (ver las notas del proyecto). `RaizMuertaFuerte.lean` probó la cota para
detectores certificados por árboles de decisión (`Certifica`), que es resolución en árbol. Aquí se sube a resolución
general, en DAG: una línea se puede usar muchas veces. Es lo que hace CDCL: cada cláusula que aprende sale de una
derivación por resolución.

## Lo que se prueba

* `CertificaRes F N det c`: cada vez que `det` dice «muerto» en `p`, hay una cláusula `C` falsa en toda asignación
  que sigue a `p`, con una derivación por resolución desde `F` de a lo sumo `c p` líneas (`CNF.IsProof` de
  cslib-frontier).
* **El puente** (`refuta_debajo`, `refutacion_traza`): si `F` no tiene solución, la traza de `buscar` es una
  refutación por resolución de `F`. Su tamaño es a lo sumo `peso … (costoRes det c) N []`: un `1` por nodo donde `det`
  no dijo «muerto», más `c p` por nodo donde sí. En cada rama, las cláusulas de los dos hijos se resuelven sobre la
  variable de la rama (`paso_resolucion`); si una no tiene esa variable, sirve sola.
* **La cota** (`palomar_res`): sobre el palomar con `n + 1` palomas y `n` nidos, en cualquier orden inyectivo de las
  variables, `2^(n/24) ≤ peso … (costoRes det c)`. Es la cota de Haken de cslib-frontier
  (`CNF.two_pow_le_of_refutableInSize_pigeonhole`), sin términos que restar. Con derivaciones de a lo sumo `K`
  líneas: `2^(n/24) ≤ nodos · max K 1` (`palomar_res_nodos`).
* **El corolario** (`res_sin_demora_log`): ningún detector certificado por resolución con derivaciones de tamaño
  polinomial en `N` tiene demora logarítmica sobre `formulaPal n`. Es `detCNF_sin_demora_log` para toda la clase a la
  vez. No pide que el detector sea sano: lo es por estar certificado (`certificaRes_sanoN`).
* **Casos particulares**: `detCNF` con tamaño `1` (`certificaRes_detCNF`); todo detector de `Certifica` con tamaño
  `2c` (`certificaRes_de_certifica`, vía `arbol_a_res`: un árbol de `L` hojas da `2L − 1` líneas); y por eso el
  detector con anticipación de `h` niveles (`certificaRes_anticipa`).

## Lo que no se prueba

* No se modela CDCL entero: ni heurísticas, ni reinicios, ni la base de cláusulas aprendidas que crece en la corrida.
  Solo el hecho de que cada veredicto «muerto» viene con una derivación por resolución. Si las cláusulas aprendidas se
  reusan entre nodos, `c` cuenta la derivación entera en cada uso; la cota sobre la suma sigue valiendo, pero no mide
  el costo amortizado.
* La búsqueda sigue un orden fijo de variables (cualquiera, vía `relabel f`).
* Contar líneas y nodos no es tiempo de máquina de Turing.
* Resolución tiene cotas inferiores conocidas; sistemas más fuertes (Frege) no. Un detector que se certifique en un
  sistema más fuerte queda fuera.
-/

open Cslib Cslib.Logic.PL

namespace Sagitta.Map
namespace Tiempo

/-! ## La definición -/

/-- **Detector certificado por resolución con tamaño `c`.** Cada vez que `det` dice «muerto» en un prefijo `p` de
largo `≤ N`, hay una cláusula `C` falsa en toda asignación que sigue a `p`. Y hay una derivación por resolución de `C`
desde `F` de a lo sumo `c p` líneas. Es la versión en DAG de `Certifica`. -/
def CertificaRes (F : List Clausula) (N : ℕ) (det : List Bool → Bool) (c : List Bool → ℕ) : Prop :=
  ∀ p : List Bool, p.length ≤ N → det p = true →
    ∃ (C : Clausula) (ls : List Clausula), CNF.IsProof (F : CNF ℕ) ls ∧ C ∈ ls ∧ ls.length ≤ c p ∧
      ∀ σ : ℕ → Bool, Sigue σ p → Clause.eval σ C = false

/-- El costo de cada nodo de la búsqueda: `c p` donde el detector dice «muerto», `1` en los demás. -/
def costoRes (det : List Bool → Bool) (c : List Bool → ℕ) (p : List Bool) : ℕ := if det p then c p else 1

/-! ## Un paso de resolución sobre la variable de la rama -/

/-- Si un literal es falso al fijar `v` en `b`, y no es el literal `(v, !b)`, también es falso antes de fijarlo. -/
theorem lit_falsa {σ : ℕ → Bool} {v : ℕ} {b : Bool} {l : Literal ℕ}
    (hl : Literal.eval (Function.update σ v b) l = false) (hne : l ≠ (v, !b)) : Literal.eval σ l = false := by
  obtain ⟨u, a⟩ := l
  by_cases hu : u = v
  · subst hu
    simp only [Literal.eval_mk, Function.update_self, beq_eq_false_iff_ne, ne_eq] at hl
    exact absurd (by cases a <;> cases b <;> simp_all) hne
  · simpa [Literal.eval_mk, Function.update_of_ne hu] using hl

theorem clause_falsa_iff {σ : ℕ → Bool} {C : Clausula} :
    Clause.eval σ C = false ↔ ∀ l ∈ C, Literal.eval σ l = false := by
  simp [Clause.eval, List.any_eq_false]

/-- **El paso de resolución.** `S` es un conjunto de asignaciones cerrado bajo cambiar `v`. Si `C₀` es falsa en las de
`S` con `v = false` y `C₁` en las de `S` con `v = true`, sale una cláusula falsa en todo `S`. Su derivación tiene a lo
sumo una línea más que las dos juntas. -/
theorem paso_resolucion {F : List Clausula} {S : (ℕ → Bool) → Prop} {v : ℕ}
    (hS : ∀ σ b, S σ → S (Function.update σ v b)) {C₀ C₁ : Clausula} {ls₀ ls₁ : List Clausula}
    (h₀ : CNF.IsProof (F : CNF ℕ) ls₀) (m₀ : C₀ ∈ ls₀) (f₀ : ∀ σ, S σ → σ v = false → Clause.eval σ C₀ = false)
    (h₁ : CNF.IsProof (F : CNF ℕ) ls₁) (m₁ : C₁ ∈ ls₁) (f₁ : ∀ σ, S σ → σ v = true → Clause.eval σ C₁ = false) :
    ∃ (C : Clausula) (ls : List Clausula), CNF.IsProof (F : CNF ℕ) ls ∧ C ∈ ls ∧
      ls.length ≤ ls₀.length + ls₁.length + 1 ∧ ∀ σ, S σ → Clause.eval σ C = false := by
  -- cada literal de `C₀` distinto de `(v, true)` es falso en todo `S`
  have g₀ : ∀ σ, S σ → ∀ l ∈ C₀, l ≠ (v, true) → Literal.eval σ l = false := by
    intro σ hσ l hl hne
    have := clause_falsa_iff.mp (f₀ _ (hS σ false hσ) (by simp)) l hl
    exact lit_falsa (b := false) this (by simpa using hne)
  have g₁ : ∀ σ, S σ → ∀ l ∈ C₁, l ≠ (v, false) → Literal.eval σ l = false := by
    intro σ hσ l hl hne
    have := clause_falsa_iff.mp (f₁ _ (hS σ true hσ) (by simp)) l hl
    exact lit_falsa (b := true) this (by simpa using hne)
  by_cases hv₀ : (v, true) ∈ C₀
  · by_cases hv₁ : (v, false) ∈ C₁
    · refine ⟨Clause.resolvent C₀ C₁ v, Clause.resolvent C₀ C₁ v :: (ls₀ ++ ls₁),
        .resolvent v (h₀.append h₁) (List.mem_append_left _ m₀) (List.mem_append_right _ m₁) hv₀ hv₁,
        List.mem_cons_self, by simp, fun σ hσ => clause_falsa_iff.mpr fun l hl => ?_⟩
      rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact g₀ σ hσ l hl hne
      · exact g₁ σ hσ l hl hne
    · exact ⟨C₁, ls₁, h₁, m₁, by omega, fun σ hσ => clause_falsa_iff.mpr fun l hl =>
        g₁ σ hσ l hl (fun h => hv₁ (h ▸ hl))⟩
  · exact ⟨C₀, ls₀, h₀, m₀, by omega, fun σ hσ => clause_falsa_iff.mpr fun l hl =>
      g₀ σ hσ l hl (fun h => hv₀ (h ▸ hl))⟩

/-! ## El puente: la traza de la búsqueda es una refutación -/

theorem sigue_update {σ : ℕ → Bool} {p : List Bool} (hs : Sigue σ p) (b : Bool) :
    Sigue (Function.update σ p.length b) p := fun i hi => by
  rw [Function.update_of_ne (by omega)]; exact hs i hi

theorem sigue_snoc_de {σ : ℕ → Bool} {p : List Bool} {b : Bool} (hs : Sigue σ p) (hb : σ p.length = b) :
    Sigue σ (p ++ [b]) := by
  have := sigue_snoc hs; rwa [hb] at this

/-- **El puente.** Debajo de todo nodo muerto hay una derivación por resolución de una cláusula falsa en toda
asignación que sigue al nodo. Su tamaño es a lo sumo la suma de `costoRes det c` sobre los nodos que visita la
búsqueda: `1` por nodo de rama u hoja completa, `c p` por nodo donde `det` dijo «muerto». -/
theorem refuta_debajo {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N) {det : List Bool → Bool}
    {c : List Bool → ℕ} (hcert : CertificaRes F N det c) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = N → ¬ Vivo (solCNF F) k p →
      ∃ (C : Clausula) (ls : List Clausula), CNF.IsProof (F : CNF ℕ) ls ∧ C ∈ ls ∧
        ls.length ≤ peso (solCNF F) det (costoRes det c) k p ∧ ∀ σ, Sigue σ p → Clause.eval σ C = false
  | 0, p, hl, hm => by
    by_cases hd : det p = true
    · obtain ⟨C, ls, h, hC, hle, hf⟩ := hcert p (by omega) hd
      exact ⟨C, ls, h, hC, by simpa [peso, costoRes, hd] using hle, hf⟩
    · have hsol : solCNF F p = false := by
        cases h : solCNF F p
        · rfl
        · exact absurd ((vivo_cero _ p).mpr h) hm
      obtain ⟨h1, h2⟩ := clFalsa_spec (det_de_completa hvar (by omega) hsol)
      exact ⟨clFalsa F p, [clFalsa F p], .mem .nil h1, List.mem_singleton_self _,
        by simp [peso, costoRes, hd], fun σ hs => eval_falsificada hs h2⟩
  | k + 1, p, hl, hm => by
    by_cases hd : det p = true
    · obtain ⟨C, ls, h, hC, hle, hf⟩ := hcert p (by omega) hd
      exact ⟨C, ls, h, hC, by simpa [peso, costoRes, hd] using hle, hf⟩
    · have hb : ∀ b, ¬ Vivo (solCNF F) k (p ++ [b]) := fun b h =>
        hm ((vivo_succ _ k p).mpr (by cases b <;> simp [h]))
      have ha : (buscar (solCNF F) det k (p ++ [false])).1 = false := by
        cases h : (buscar (solCNF F) det k (p ++ [false])).1
        · rfl
        · exact absurd (buscar_vivo _ _ k _ h) (hb false)
      obtain ⟨C₀, ls₀, h₀, m₀, l₀, f₀⟩ := refuta_debajo hvar hcert k (p ++ [false]) (by simp; omega) (hb false)
      obtain ⟨C₁, ls₁, h₁, m₁, l₁, f₁⟩ := refuta_debajo hvar hcert k (p ++ [true]) (by simp; omega) (hb true)
      obtain ⟨C, ls, h, hC, hle, hf⟩ := paso_resolucion (S := fun σ => Sigue σ p) (v := p.length)
        (fun σ b hs => sigue_update hs b) h₀ m₀ (fun σ hs hv => f₀ σ (sigue_snoc_de hs hv))
        h₁ m₁ (fun σ hs hv => f₁ σ (sigue_snoc_de hs hv))
      refine ⟨C, ls, h, hC, ?_, hf⟩
      simp only [peso, costoRes, hd, ha, Bool.false_eq_true, ite_false]
      omega

/-- Una cláusula falsa en toda asignación es la vacía. -/
theorem vacia_de_falsa {C : Clausula} (h : ∀ σ : ℕ → Bool, Clause.eval σ C = false) : C = [] := by
  rcases C with _ | ⟨l, C⟩
  · rfl
  · have := clause_falsa_iff.mp (h fun _ => l.2) l List.mem_cons_self
    simp [Literal.eval] at this

/-- **La traza de la búsqueda es una refutación por resolución general.** Si `F` no tiene solución y `det` está
certificado por resolución con tamaño `c`, `F` tiene una refutación de a lo sumo `peso … (costoRes det c) N []`
líneas: los nodos de la búsqueda donde `det` no dijo «muerto», más la suma de `c` donde sí lo dijo. -/
theorem refutacion_traza {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N)
    (hF : ¬ CNF.Satisfiable (F : CNF ℕ)) {det : List Bool → Bool} {c : List Bool → ℕ}
    (hcert : CertificaRes F N det c) :
    CNF.RefutableInSize (F : CNF ℕ) (peso (solCNF F) det (costoRes det c) N []) := by
  obtain ⟨C, ls, h, hC, hle, hf⟩ := refuta_debajo hvar hcert N [] (by simp) (raiz_muerta hF N)
  have : C = [] := vacia_de_falsa fun σ => hf σ (fun i hi => absurd hi (by simp))
  exact ⟨ls, h, this ▸ hC, hle⟩

/-! ## La cota de Haken -/

/-- **Cota exponencial en el palomar.** Con `n + 1` palomas, `n` nidos y cualquier orden inyectivo `f` de las
variables, la búsqueda con un detector certificado por resolución paga `2^(n/24) ≤ peso … (costoRes det c)`. Es decir,
los nodos donde `det` no dijo «muerto», más la suma de los tamaños de las derivaciones donde sí. -/
theorem palomar_res {n : ℕ} {f : Fin (n + 1) × Fin n → ℕ} (hf : Function.Injective f) {N : ℕ}
    (hN : ∀ v, f v < N) {det : List Bool → Bool} {c : List Bool → ℕ}
    (hcert : CertificaRes ((CNF.pigeonhole (n + 1) n).relabel f) N det c) :
    2 ^ (n / 24) ≤ peso (solCNF ((CNF.pigeonhole (n + 1) n).relabel f)) det (costoRes det c) N [] := by
  set F : List Clausula := (CNF.pigeonhole (n + 1) n).relabel f
  have hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N := by
    intro c hc l hl
    simp only [F, CNF.relabel, List.mem_map] at hc
    obtain ⟨c', -, rfl⟩ := hc
    simp only [Clause.relabel, List.mem_map] at hl
    obtain ⟨l', -, rfl⟩ := hl
    exact hN l'.1
  have hunsat : ¬ CNF.Satisfiable (F : CNF ℕ) := by
    rw [CNF.satisfiable_relabel hf]; exact CNF.not_satisfiable_pigeonhole (by omega)
  exact CNF.two_pow_le_of_refutableInSize_pigeonhole
    ((refutacion_traza hvar hunsat hcert).of_relabel hf)

/-- **Con derivaciones de tamaño a lo sumo `K`**: `2^(n/24) ≤ nodos · max K 1`. -/
theorem palomar_res_nodos {n : ℕ} {f : Fin (n + 1) × Fin n → ℕ} (hf : Function.Injective f) {N : ℕ}
    (hN : ∀ v, f v < N) {det : List Bool → Bool} {c : List Bool → ℕ} {K : ℕ} (hK : ∀ p, c p ≤ K)
    (hcert : CertificaRes ((CNF.pigeonhole (n + 1) n).relabel f) N det c) :
    2 ^ (n / 24) ≤ nodos (solCNF ((CNF.pigeonhole (n + 1) n).relabel f)) det N [] * max K 1 := by
  refine (palomar_res hf hN hcert).trans (peso_le _ _ _ (fun p => ?_) N [])
  unfold costoRes
  split
  · exact (hK p).trans (le_max_left _ _)
  · exact le_max_right _ _

/-! ## Un detector certificado es sano -/

/-- Una solución completa, como asignación, satisface la fórmula. -/
theorem eval_de_solCNF {F : List Clausula} {q : List Bool} (hq : solCNF F q = true) :
    CNF.eval (fun i => q.getD i false) (F : CNF ℕ) = true := by
  simp only [solCNF, List.all_eq_true] at hq
  simp only [CNF.eval, List.all_eq_true]
  intro c hc
  have := hq c hc
  simp only [satisface, List.any_eq_true, beq_iff_eq] at this
  obtain ⟨l, hl, hget⟩ := this
  simp only [Clause.eval, List.any_eq_true]
  refine ⟨l, hl, ?_⟩
  simp [Literal.eval, List.getD_eq_getElem?_getD, hget]

/-- **Un detector certificado por resolución es sano**: la cláusula derivada es consecuencia de `F` y es falsa debajo
de `p`, así que nada debajo de `p` es solución. -/
theorem certificaRes_sanoN {F : List Clausula} {N : ℕ} {det : List Bool → Bool} {c : List Bool → ℕ}
    (h : CertificaRes F N det c) : SanoN (solCNF F) det N := by
  rintro p hp hd ⟨q, -, hs⟩
  obtain ⟨C, ls, hpr, hC, -, hf⟩ := h p hp hd
  have hσ := eval_de_solCNF hs
  have hseg : Sigue (fun i => (p ++ q).getD i false) p := fun i hi => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  have := (CNF.IsProof.derives hpr hC).eval_eq_true hσ
  rw [hf _ hseg] at this
  exact Bool.false_ne_true this

/-! ## Sin demora logarítmica con derivaciones polinomiales -/

/-- **Lo exponencial le gana a lo polinomial**: para todos `C` y `m` hay un `n` con `C · (n+1)^m < 2^(n/24)`. -/
theorem pow_dos_gana_aux (C m s : ℕ) (hexp : C + (s + 5) * m ≤ 2 ^ s) :
    C * (24 * 2 ^ s + 1) ^ m < 2 ^ (24 * 2 ^ s / 24) := by
  have h24 : 24 * 2 ^ s / 24 = 2 ^ s := by omega
  rw [h24]
  have hs1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have h1 : 24 * 2 ^ s + 1 ≤ 2 ^ (s + 5) := by rw [pow_add]; omega
  have hpow : (24 * 2 ^ s + 1) ^ m ≤ 2 ^ ((s + 5) * m) :=
    calc (24 * 2 ^ s + 1) ^ m ≤ (2 ^ (s + 5)) ^ m := Nat.pow_le_pow_left h1 m
      _ = 2 ^ ((s + 5) * m) := (pow_mul 2 (s + 5) m).symm
  have hC : C < 2 ^ C := Nat.lt_two_pow_self
  have hpos : 0 < (24 * 2 ^ s + 1) ^ m := Nat.pow_pos (by omega)
  calc C * (24 * 2 ^ s + 1) ^ m < 2 ^ C * (24 * 2 ^ s + 1) ^ m := Nat.mul_lt_mul_of_pos_right hC hpos
    _ ≤ 2 ^ C * 2 ^ ((s + 5) * m) := Nat.mul_le_mul_left _ hpow
    _ = 2 ^ (C + (s + 5) * m) := (pow_add 2 C _).symm
    _ ≤ 2 ^ (2 ^ s) := Nat.pow_le_pow_right (by norm_num) hexp

/-- **Lo exponencial le gana a lo polinomial**: para todos `C` y `m` hay un `n` con `C · (n+1)^m < 2^(n/24)`. -/
theorem pow_dos_gana (C m : ℕ) : ∃ n, C * (n + 1) ^ m < 2 ^ (n / 24) := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = C + 6 * m + 5 := ⟨_, rfl⟩
  have hM : M < 2 ^ M := Nat.lt_two_pow_self
  have hsq : (M + 1) * (M + 1) ≤ 2 ^ (M + M) := by rw [pow_add]; exact Nat.mul_le_mul hM hM
  have hexp : C + (M + M + 5) * m ≤ 2 ^ (M + M) := le_trans (by subst hMdef; nlinarith) hsq
  exact ⟨_, pow_dos_gana_aux C m (M + M) hexp⟩

/-- **Ningún detector certificado por resolución con derivaciones de tamaño polinomial tiene demora logarítmica sobre
el palomar.** Para todos `a`, `b`, `e` y `K` hay un `n` tal que, con `N = n(n+1)` variables, ningún detector certificado
por resolución con derivaciones de a lo sumo `K · (N+1)^e` líneas tiene demora `a · log₂(N+1) + b` sobre
`formulaPal n`. Es `detCNF_sin_demora_log` para todos los detectores de esta clase a la vez. -/
theorem res_sin_demora_log (a b e K : ℕ) :
    ∃ n, ∀ (det : List Bool → Bool) (c : List Bool → ℕ),
      CertificaRes (formulaPal n) (n * (n + 1)) det c → (∀ p, c p ≤ K * (n * (n + 1) + 1) ^ e) →
      ¬ DemoraN (solCNF (formulaPal n)) det (n * (n + 1)) (a * Nat.log 2 (n * (n + 1) + 1) + b) := by
  obtain ⟨n, hn⟩ := pow_dos_gana (2 ^ (b + 1) * (K + 1)) (2 * (a + e + 1))
  refine ⟨n, fun det c hcert hc hd => ?_⟩
  set N := n * (n + 1) with hNdef
  have hlow := palomar_res_nodos (n := n) (ordenPal_inj n) (ordenPal_lt n) hc hcert
  have hup := nodos_le (k := N) (p := []) (certificaRes_sanoN hcert) hd (by simp)
  have hlog : 2 ^ (a * Nat.log 2 (N + 1) + b + 1) ≤ 2 ^ (b + 1) * (N + 1) ^ a := by
    rw [show a * Nat.log 2 (N + 1) + b + 1 = a * Nat.log 2 (N + 1) + (b + 1) by ring, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (dos_pow_mul_log_le a (N + 1) (by omega))
  have hX : 1 ≤ (N + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have hmax : max (K * (N + 1) ^ e) 1 ≤ (K + 1) * (N + 1) ^ e := by
    refine max_le (by nlinarith) (by nlinarith)
  have hN1 : N + 1 ≤ (n + 1) ^ 2 := by simp only [hNdef]; nlinarith
  have hbig : 2 ^ (n / 24) ≤ 2 ^ (b + 1) * (K + 1) * (n + 1) ^ (2 * (a + e + 1)) := by
    calc 2 ^ (n / 24) ≤ nodos (solCNF (formulaPal n)) det N [] * max (K * (N + 1) ^ e) 1 := hlow
      _ ≤ ((N + 1) * 2 ^ (a * Nat.log 2 (N + 1) + b + 1)) * ((K + 1) * (N + 1) ^ e) :=
          Nat.mul_le_mul (by simpa using hup) hmax
      _ ≤ ((N + 1) * (2 ^ (b + 1) * (N + 1) ^ a)) * ((K + 1) * (N + 1) ^ e) := by gcongr
      _ = 2 ^ (b + 1) * (K + 1) * (N + 1) ^ (a + e + 1) := by ring
      _ ≤ 2 ^ (b + 1) * (K + 1) * ((n + 1) ^ 2) ^ (a + e + 1) := by gcongr
      _ = 2 ^ (b + 1) * (K + 1) * (n + 1) ^ (2 * (a + e + 1)) := by rw [← pow_mul]
  exact absurd hn (not_lt.mpr hbig)

/-! ## Casos particulares: resolución en árbol es resolución -/

/-- **`detCNF` está certificado por resolución con derivaciones de tamaño `1`**: la cláusula falsa misma. -/
theorem certificaRes_detCNF (F : List Clausula) (N : ℕ) : CertificaRes F N (detCNF F) (fun _ => 1) := by
  intro p _ hd
  obtain ⟨h1, h2⟩ := clFalsa_spec hd
  exact ⟨clFalsa F p, [clFalsa F p], .mem .nil h1, List.mem_singleton_self _, le_refl _,
    fun σ hs => eval_falsificada hs h2⟩

/-- `σ` respeta la asignación parcial `ρ`. -/
def Respeta (ρ : ℕ → Option Bool) (σ : ℕ → Bool) : Prop := ∀ i b, ρ i = some b → σ i = b

theorem respeta_update {ρ : ℕ → Option Bool} {i : ℕ} (hi : ρ i = none) {σ : ℕ → Bool} (b : Bool)
    (h : Respeta ρ σ) : Respeta ρ (Function.update σ i b) := fun j b' hj => by
  have hji : j ≠ i := by rintro rfl; simp [hi] at hj
  rw [Function.update_of_ne hji]; exact h j b' hj

theorem respeta_fijar {ρ : ℕ → Option Bool} {i : ℕ} {σ : ℕ → Bool} {b : Bool} (h : Respeta ρ σ) (hb : σ i = b) :
    Respeta (Function.update ρ i (some b)) σ := fun j b' hj => by
  by_cases hji : j = i
  · subst hji; simp only [Function.update_self, Option.some.injEq] at hj; rw [hb, hj]
  · rw [Function.update_of_ne hji] at hj; exact h j b' hj

/-- **De árbol de decisión a derivación por resolución.** Un árbol de `L` hojas que, en toda asignación que respeta
`ρ`, llega a una cláusula de `F` falsa, da una derivación de a lo sumo `2L − 1` líneas de una cláusula falsa en
todas esas asignaciones. -/
theorem arbol_a_res {F : List Clausula} :
    ∀ (t : DecisionTree ℕ Clausula) (ρ : ℕ → Option Bool),
      (∀ σ, Respeta ρ σ → t.eval σ ∈ F ∧ Clause.eval σ (t.eval σ) = false) →
      ∃ (C : Clausula) (ls : List Clausula), CNF.IsProof (F : CNF ℕ) ls ∧ C ∈ ls ∧
        ls.length + 1 ≤ 2 * t.leafCount ∧ ∀ σ, Respeta ρ σ → Clause.eval σ C = false
  | .leaf C, ρ, h => by
    have h0 := h (fun i => (ρ i).getD false) (fun i b hi => by simp [hi])
    refine ⟨C, [C], .mem .nil (by simpa using h0.1), List.mem_singleton_self _,
      by simp [DecisionTree.leafCount], fun σ hσ => by simpa using (h σ hσ).2⟩
  | .node i t₀ t₁, ρ, h => by
    cases hρ : ρ i with
    | some b =>
      cases b with
      | false =>
        obtain ⟨C, ls, hp, hC, hl, hf⟩ := arbol_a_res t₀ ρ fun σ hσ => by
          have := h σ hσ; simpa [hσ i false hρ] using this
        exact ⟨C, ls, hp, hC, by simp only [DecisionTree.leafCount]; have := t₁.leafCount_pos; omega, hf⟩
      | true =>
        obtain ⟨C, ls, hp, hC, hl, hf⟩ := arbol_a_res t₁ ρ fun σ hσ => by
          have := h σ hσ; simpa [hσ i true hρ] using this
        exact ⟨C, ls, hp, hC, by simp only [DecisionTree.leafCount]; have := t₀.leafCount_pos; omega, hf⟩
    | none =>
      have hb : ∀ b, Respeta (Function.update ρ i (some b)) = fun σ => Respeta ρ σ ∧ σ i = b := by
        intro b; funext σ; apply propext; constructor
        · intro hσ
          refine ⟨fun j b' hj => ?_, hσ i b (by simp)⟩
          have hji : j ≠ i := by rintro rfl; simp [hρ] at hj
          exact hσ j b' (by rw [Function.update_of_ne hji]; exact hj)
        · rintro ⟨hσ, hi⟩; exact respeta_fijar hσ hi
      obtain ⟨C₀, ls₀, h₀, m₀, l₀, f₀⟩ := arbol_a_res t₀ (Function.update ρ i (some false)) fun σ hσ => by
        rw [hb] at hσ; have := h σ hσ.1; simpa [hσ.2] using this
      obtain ⟨C₁, ls₁, h₁, m₁, l₁, f₁⟩ := arbol_a_res t₁ (Function.update ρ i (some true)) fun σ hσ => by
        rw [hb] at hσ; have := h σ hσ.1; simpa [hσ.2] using this
      obtain ⟨C, ls, hp, hC, hl, hf⟩ := paso_resolucion (F := F) (S := Respeta ρ) (v := i)
        (fun σ b hσ => respeta_update hρ b hσ) h₀ m₀ (fun σ hσ hv => f₀ σ (respeta_fijar hσ hv))
        h₁ m₁ (fun σ hσ hv => f₁ σ (respeta_fijar hσ hv))
      exact ⟨C, ls, hp, hC, by simp only [DecisionTree.leafCount]; omega, hf⟩

/-- Seguir el prefijo `p` es respetar la asignación parcial `i ↦ p[i]?`. -/
theorem respeta_iff_sigue {σ : ℕ → Bool} {p : List Bool} : Respeta (fun i => p[i]?) σ ↔ Sigue σ p := by
  constructor
  · intro h i hi; exact h i _ (List.getElem?_eq_getElem hi)
  · intro h i b hi
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hi
    rw [h i hlt, hget]

/-- **Todo detector certificado por árboles (`Certifica`) está certificado por resolución**, con derivaciones de a lo
sumo el doble de hojas. Resolución en árbol es resolución. -/
theorem certificaRes_de_certifica {F : List Clausula} {N : ℕ} {det : List Bool → Bool} {c : List Bool → ℕ}
    (h : Certifica F N det c) : CertificaRes F N det (fun p => 2 * c p) := by
  intro p hp hd
  obtain ⟨t, ht, he⟩ := h p hp hd
  obtain ⟨C, ls, hpr, hC, hl, hf⟩ := arbol_a_res t (fun i => p[i]?) fun σ hσ => he σ (respeta_iff_sigue.mp hσ)
  exact ⟨C, ls, hpr, hC, show ls.length ≤ 2 * c p by omega, fun σ hs => hf σ (respeta_iff_sigue.mpr hs)⟩

/-- **El detector con anticipación de `h` niveles** (`anticipa`, de `DemoraEfectiva`) está certificado por resolución
con derivaciones de a lo sumo `2 · llamadas`. -/
theorem certificaRes_anticipa {F : List Clausula} {N : ℕ} (hvar : ∀ c ∈ F, ∀ l ∈ c, l.1 < N) (h : ℕ) :
    CertificaRes F N (anticipa (solCNF F) (detCNF F) N h) (fun p => 2 * llamadas (solCNF F) (detCNF F) N h p) :=
  certificaRes_de_certifica (certifica_anticipa hvar h)

/-! ## Controles -/

/-- **Control: la hipótesis se cumple.** `detCNF` sobre el palomar está certificado por resolución con tamaño `1`, y
con él `palomar_res` da `2^(n/24) ≤ nodos`. -/
theorem palomar_res_detCNF (n : ℕ) :
    2 ^ (n / 24) ≤ nodos (solCNF (formulaPal n)) (detCNF (formulaPal n)) (n * (n + 1)) [] := by
  have := palomar_res_nodos (n := n) (ordenPal_inj n) (ordenPal_lt n) (K := 1) (fun _ => le_refl 1)
    (certificaRes_detCNF (formulaPal n) (n * (n + 1)))
  simpa [formulaPal] using this

example : CertificaRes (formulaPal 3) 12 (detCNF (formulaPal 3)) (fun _ => 1) := certificaRes_detCNF _ _

/-- Una refutación de `contra3` (`x3 ∧ ¬x3`) en tres líneas. -/
theorem contra3_prueba : CNF.IsProof (contra3 : CNF ℕ) [[], [(3, true)], [(3, false)]] := by
  have h : CNF.IsProof (contra3 : CNF ℕ)
      (Clause.resolvent [(3, true)] [(3, false)] 3 :: [[(3, true)], [(3, false)]]) :=
    .resolvent 3 (.mem (.mem .nil (by simp [contra3])) (by simp [contra3])) (by simp) (by simp) (by simp) (by simp)
  have e : Clause.resolvent ([(3, true)] : Clausula) [(3, false)] 3 = [] := by decide
  rwa [e] at h

-- El detector que dispara siempre está certificado por resolución con tamaño 3 en `contra3`: la cláusula vacía, falsa
-- en todo, con su refutación. La búsqueda paga 3.
example : CertificaRes contra3 4 (fun _ => true) (fun _ => 3) := fun _ _ _ =>
  ⟨[], _, contra3_prueba, by simp, by simp, fun _ _ => rfl⟩
example : peso (solCNF contra3) (fun _ => true) (costoRes (fun _ => true) (fun _ => 3)) 4 [] = 3 := by decide

/-- **`CertificaRes` no es trivial**: en `contra3`, ningún detector que dispare en la raíz está certificado con
derivaciones de 2 líneas. En la raíz la cláusula tiene que ser la vacía, y dos líneas no la derivan. -/
theorem no_certificaRes_raiz {det : List Bool → Bool} (hd : det [] = true) :
    ¬ CertificaRes contra3 4 det (fun _ => 2) := by
  intro h
  obtain ⟨C, ls, hpr, hC, hl, hf⟩ := h [] (by simp) hd
  have hC0 : C = [] := vacia_de_falsa fun σ => hf σ (fun i hi => absurd hi (by simp))
  subst hC0
  have hne : ∀ c ∈ (contra3 : CNF ℕ), c ≠ [] := by simp [contra3]
  have huni : ∀ c ∈ (contra3 : CNF ℕ), ∀ v, ¬ ((v, true) ∈ c ∧ (v, false) ∈ c) := by simp [contra3]
  cases hpr with
  | nil => simp at hC
  | @mem ls₁ c₁ h₁ hc₁ =>
    rcases List.mem_cons.1 hC with he | hC
    · exact hne _ hc₁ he.symm
    cases h₁ with
    | nil => simp at hC
    | @mem ls₂ c₂ h₂ hc₂ =>
      simp only [List.length_cons] at hl
      have : ls₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp only [List.mem_singleton] at hC
      exact hne _ hc₂ hC.symm
    | @resolvent ls₂ d₁ d₂ v h₂ m₁ m₂ _ _ =>
      simp only [List.length_cons] at hl
      have : ls₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp at m₁
  | @resolvent ls₁ d₁ d₂ v h₁ m₁ m₂ hv₁ hv₂ =>
    simp only [List.length_cons] at hl
    cases h₁ with
    | nil => simp at m₁
    | @mem ls₂ c₂ h₂ hc₂ =>
      have : ls₂ = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hl; omega)
      subst this
      simp only [List.mem_singleton] at m₁ m₂
      subst m₁; subst m₂
      exact huni _ hc₂ v ⟨hv₁, hv₂⟩
    | @resolvent ls₂ e₁ e₂ u h₂ n₁ _ _ _ =>
      have : ls₂ = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hl; omega)
      subst this; simp at n₁

example : ¬ CertificaRes contra3 4 (fun _ => true) (fun _ => 2) := no_certificaRes_raiz rfl

/-- `contra3` no tiene refutación de una línea: la única línea sería una cláusula de `contra3`, y ninguna es vacía. -/
theorem contra3_sin_refutacion_uno : ¬ CNF.RefutableInSize (contra3 : CNF ℕ) 1 := by
  rintro ⟨ls, h, hnil, hl⟩
  cases h with
  | nil => simp at hnil
  | @mem ls₁ c₁ h₁ hc₁ =>
    simp only [List.length_cons] at hl
    have : ls₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [List.mem_singleton] at hnil
    subst hnil; simp [contra3] at hc₁
  | @resolvent ls₁ d₁ d₂ v h₁ m₁ _ _ _ =>
    simp only [List.length_cons] at hl
    have : ls₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp at m₁

-- Mutante 1, refutado: sin la condición «`C` falsa en toda asignación que sigue a `p`», el detector que dispara siempre
-- quedaría «certificado» con tamaño 1 en `contra3` (cualquier cláusula de la fórmula, sin derivar nada), su peso sería
-- 1, y `refutacion_traza` daría una refutación de una línea, que no existe. La condición hace falta.
example : (∀ p : List Bool, p.length ≤ 4 → (fun _ => true) p = true →
      ∃ (C : Clausula) (ls : List Clausula), CNF.IsProof (contra3 : CNF ℕ) ls ∧ C ∈ ls ∧ ls.length ≤ 1) ∧
    peso (solCNF contra3) (fun _ => true) (costoRes (fun _ => true) (fun _ => 1)) 4 [] = 1 ∧
    ¬ CNF.RefutableInSize (contra3 : CNF ℕ) 1 :=
  ⟨fun _ _ _ => ⟨[(3, true)], [[(3, true)]], .mem .nil (by simp [contra3]), by simp, le_refl _⟩, by decide,
    contra3_sin_refutacion_uno⟩

/- Mutantes probados fuera del repositorio (todos rompen la compilación, como debe ser):
1. Quitar de `CertificaRes` la condición de que `C` sea falsa debajo de `p`: rompen `refuta_debajo`,
   `certificaRes_sanoN` y los controles. Además queda refutado arriba con un `example`.
2. Cambiar `ls.length ≤ c p` por `ls.length ≤ c p + 1`: rompe `refuta_debajo` (el peso ya no acota).
3. Quitar el `+ 1` de la cota de `paso_resolucion`: la táctica no cierra (la línea del resolvente cuenta).
4. Poner costo `0` en vez de `1` a los nodos donde `det` no dispara (`costoRes`): rompe `refuta_debajo`.
-/

end Tiempo
end Sagitta.Map
