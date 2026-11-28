import Sagitta.Map.DetectorResolucion
import Sagitta.Map.PlanosDeCorteClique

/-!
# Detectores que razonan con desigualdades

Peldaño «planos de corte» de la escalera de detectores (ver las notas del proyecto). `DetectorResolucion.lean` probó la cota para
detectores cuyos veredictos «muerto» vienen con una derivación por resolución. Aquí los veredictos vienen con una
derivación por planos de corte: el detector suma desigualdades, las multiplica y divide redondeando.

## El problema, y la salida

Con resolución, la traza de la búsqueda es una refutación por resolución: en cada rama se resuelve sobre la variable
de la rama. Planos de corte no tiene un paso que junte las dos ramas de una variable. La traza es entonces un árbol de
decisión con hojas de planos de corte: un sistema más fuerte, cercano a *stabbing planes* y a `R(CP)`. No es una
refutación por planos de corte, y la cota de `PlanosDeCorteClique.lean` no se aplica tal cual.

La salida es leer la traza como una **refutación semántica** (Krajíček 1997, Definición 4.1; `IsSemanticRefutation`
de cslib-frontier). Las líneas son de dos clases (`Linea`): desigualdades, y «la asignación no sigue a `p`». Las reglas
(`reglas`) son todas las sanas de a lo sumo dos premisas. En una hoja, la desigualdad del certificado implica «no sigue
a `p`» (una premisa); en una rama, «no sigue a `p0`» y «no sigue a `p1`» implican «no sigue a `p`» (dos premisas);
en la raíz, «no sigue a `[]`» es el vacío.

La interpolación de Krajíček para refutaciones semánticas pide poco de cada línea: decidir si `(v, q, r)` está en
ella, y buscar una coordenada solo en las líneas iniciales de Alice. «No sigue a `p`» se decide con **dos bits**,
fije `p` las variables que fije, compartidas incluidas (`ecomplexity_fuera_le`): Alice dice si sus variables siguen a
`p` y Bob contesta. Por eso la interpolación **monótona** sí encaja: la búsqueda solo corre en las desigualdades del
clique, donde las aristas tienen coeficiente `0` o `1`. La monotonía de «no sigue a `p`» no hace falta nunca.

## Lo que se prueba

* `CertificaCP φ f N det c M`: cada vez que `det` dice «muerto» en `p`, hay una desigualdad falsa en toda asignación
  que sigue a `p` (en el orden `f` de las variables), con una derivación por planos de corte desde `φ` de a lo sumo
  `c p` líneas y coeficientes a lo sumo `M`. `CertificaSem` es lo único que la traza usa de eso.
* **El puente** (`traza_debajo`, `traza_refutacion`): si `φ` no tiene solución, la traza de `buscar` es una refutación
  semántica con a lo sumo `peso … (costoCP det c) N []` líneas: `c p + 1` donde `det` dijo «muerto», `2` en los demás
  nodos. Sus desigualdades tienen coeficientes a lo sumo `max M 1`.
* **La comunicación** (`ecomplexity_fuera_le`): dos bits por línea «no sigue». Las desigualdades cuestan
  `⌈log₂(2 M |y| + 1)⌉ + 1` (cslib-frontier, `ecomplexity_memRight_holds_le`).
* **La interpolación** (`existe_separador_traza`): sobre `Clique_{n,k} ∧ Color_{n,r}`, en cualquier orden inyectivo de
  las variables, la traza da un circuito monótono que separa los grafos con `k`-clique de los `r`-coloreables, de a lo
  sumo `(P · 2^(2t) + 1) · 2^(2t+1)` compuertas, con `P` el tamaño de la traza.
* **La cota** (`cota_traza`): con Alon–Boppana, `2^⌊⌊√⌊√n⌋⌋/2⌋ < (P + 1) · 2^(4(b+1)² + 1)` si
  `2 (max M 1 + 1) n² + 1 ≤ 2^b`. Con `M` polinomial, la traza es `2^(Ω(n^{1/4}) − O(log² n))`.
* **El corolario** (`cp_sin_demora_log`, desde `sem_sin_demora_log`): ningún detector certificado por planos de corte
  con derivaciones de tamaño y coeficientes polinomiales en `N` tiene demora logarítmica sobre clique–coloreo (la
  sucesión `n = 2^(4j)`, `k = 2^(2j) + 1`, `r = 2^(2j)`), en ningún orden de las variables. Es el análogo de
  `res_sin_demora_log`. No pide que el detector sea sano: lo es por estar certificado (`certificaSem_sanoN`).
* **Caso particular** (`certificaSem_de_res`, `res_cc_sin_demora_log`): los detectores certificados por resolución
  (`CertificaRes`) entran, con coeficientes `1` y el mismo tamaño. No hace falta simular resolución en planos de corte
  (`CNF.IsProof.cuttingPlanes` de cslib no acota coeficientes): las cláusulas entran como sus desigualdades y un paso
  de resolución es una regla sana de dos premisas.
* **Controles**: `detCNF` está certificado por planos de corte con una línea y coeficientes `1` (`certificaCP_detCNF`),
  y con él las hipótesis de `cota_traza` se cumplen a la vez en todo `j ≥ 10` (`cota_detCNF`); el detector que siempre
  dispara está certificado en `Clique_{0,1} ∧ Color_{0,0}` y `existe_separador_traza` se aplica; `DemoraN` sola se
  cumple (el detector que siempre dispara tiene demora `0`), así que el corolario dice algo sobre la conjunción.

## Qué es nuevo y qué no

* No es nuevo el método: interpolación factible para planos de corte (Krajíček 1997, Teorema 6.4; Pudlák 1997) y para
  refutaciones semánticas (Krajíček 1997, Teorema 5.1), con la cota monótona de Alon–Boppana. Tampoco lo es que
  árboles de decisión con hojas de planos de corte tengan cotas por interpolación: es el terreno de *stabbing planes*
  (Beame, Fleming, Impagliazzo, Kolokolova, Pankratov, Pitassi, Robere 2018) y de `R(CP)` (Krajíček 1998), que la
  literatura trata en el nivel de investigación: hay cotas vía interpolación con coeficientes acotados, y el caso
  general sigue abierto. (Las referencias de este párrafo no se verificaron contra las fuentes en esta pasada.)
* Lo que se hace aquí es la lectura de la traza de esta búsqueda (`buscar` de `ArbolElecciones`) como refutación
  semántica, la cota de dos bits para «no sigue a `p`» y la observación de que la interpolación monótona encaja porque
  la búsqueda de coordenadas solo corre en las líneas iniciales. Todo formalizado sobre cslib-frontier, sin `sorry`.

## Lo que no se prueba

* **Coeficientes arbitrarios.** Los coeficientes entran en la comunicación: con coeficientes de `n^{1/8}` bits la cota
  no dice nada. La versión de Pudlák (circuitos monótonos reales) para árboles con hojas de planos de corte no está.
* Las derivaciones de las hojas son independientes: si se reusan entre nodos, `c` cuenta la derivación entera en cada
  uso (como en `DetectorResolucion`).
* Las ramas son solo sobre variables, en un orden fijo (cualquiera, vía `f`). Ramificar sobre desigualdades (*stabbing
  planes* en serio) no está.
* Las constantes son malas: la cota solo dice algo para `j ≥ 10` y mucho más.
* Contar líneas y nodos no es tiempo de máquina de Turing.
-/

open Cslib Cslib.Logic.PL

namespace Sagitta.Map
namespace Tiempo
namespace DetectorPlanosDeCorte

variable {W : Type*}

/-! ## Las definiciones -/

/-- `τ`, una asignación de las variables `W`, **sigue** al prefijo `p` en el orden `f`: la variable `w` vale `p[f w]`
cuando `f w < |p|`. -/
def SigueV (f : W → ℕ) (τ : W → Bool) (p : List Bool) : Prop :=
  ∀ w (h : f w < p.length), τ w = p[f w]

/-- **Detector certificado por planos de corte.** Cada vez que `det` dice «muerto» en un prefijo `p` de largo `≤ N`,
hay una desigualdad `I` falsa en toda asignación que sigue a `p`. Y hay una derivación por planos de corte de `I`
desde las desigualdades de `φ`, de a lo sumo `c p` líneas, con coeficientes de valor absoluto a lo sumo `M`. -/
def CertificaCP [DecidableEq W] (φ : CNF W) (f : W → ℕ) (N : ℕ) (det : List Bool → Bool) (c : List Bool → ℕ)
    (M : ℕ) : Prop :=
  ∀ p : List Bool, p.length ≤ N → det p = true →
    ∃ (I : Ineq W) (ls : List (Ineq W)), CuttingPlanes.IsProof φ.toIneqs ls ∧ I ∈ ls ∧ ls.length ≤ c p ∧
      (∀ J ∈ ls, ∀ w, |J.coeff w| ≤ M) ∧ ∀ τ : W → Bool, SigueV f τ p → ¬ I.Holds τ

/-- El costo de cada nodo en la traza: `c p + 1` donde el detector dice «muerto» (la derivación y la línea «no sigue
a `p`»), `2` en los demás (la línea «no sigue a `p`» y, en una hoja, la cláusula falsa). -/
def costoCP (det : List Bool → Bool) (c : List Bool → ℕ) (p : List Bool) : ℕ := if det p then c p + 1 else 2

/-- **Las líneas de la traza.** Una desigualdad sobre `W`, o «la asignación no sigue a `p`». -/
inductive Linea (W : Type*)
  | ineq (I : Ineq W)
  | fuera (p : List Bool)

/-- Lo que dice cada línea, como conjunto de asignaciones. -/
def modelos (f : W → ℕ) : Linea W → Set (W → Bool)
  | .ineq I => {τ | I.Holds τ}
  | .fuera p => {τ | ¬ SigueV f τ p}

/-- **Las reglas de la traza**: toda regla sana de a lo sumo dos premisas. Contiene las de planos de corte, la que
pasa de una desigualdad falsa debajo de `p` a «no sigue a `p`», y la que junta las dos ramas de una variable. Es la
regla semántica de Krajíček (1997), Definición 4.1. -/
def reglas (f : W → ℕ) : Set (LineRule (Linea W)) :=
  {r | r.premises.length ≤ 2 ∧ ∀ τ, (∀ x ∈ r.premises, τ ∈ modelos f x) → τ ∈ modelos f r.concl}

/-- Una línea con coeficientes acotados por `M` (las de la forma «no sigue a `p`» no tienen coeficientes). -/
def Acotada (M : ℕ) : Linea W → Prop
  | .ineq I => ∀ w, |I.coeff w| ≤ M
  | .fuera _ => True

/-! ## Seguir un prefijo -/

theorem sigueV_nil (f : W → ℕ) (τ : W → Bool) : SigueV f τ [] := fun _ h => absurd h (by simp)

/-- Si `τ` sigue a `p`, sigue a `p ++ [b]` para algún `b`: el valor de la variable de la rama, si la hay. -/
theorem sigueV_snoc {f : W → ℕ} (hf : Function.Injective f) {τ : W → Bool} {p : List Bool}
    (h : SigueV f τ p) : ∃ b, SigueV f τ (p ++ [b]) := by
  classical
  by_cases hw : ∃ w, f w = p.length
  · obtain ⟨w₀, hw₀⟩ := hw
    refine ⟨τ w₀, fun w hl => ?_⟩
    simp only [List.length_append, List.length_singleton] at hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
    · rw [List.getElem_append_left hlt]; exact h w hlt
    · have : w = w₀ := hf (heq.trans hw₀.symm)
      subst this
      simp [heq]
  · refine ⟨false, fun w hl => ?_⟩
    simp only [List.length_append, List.length_singleton] at hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
    · rw [List.getElem_append_left hlt]; exact h w hlt
    · exact absurd ⟨w, heq⟩ hw

/-- Una asignación de `ℕ` que sigue a `p` y coincide con `τ` en la imagen de `f`. -/
theorem existe_sigue {f : W → ℕ} (hf : Function.Injective f) {τ : W → Bool} {p : List Bool}
    (h : SigueV f τ p) : ∃ σ : ℕ → Bool, Sigue σ p ∧ σ ∘ f = τ := by
  classical
  refine ⟨fun i => if hi : ∃ w, f w = i then τ hi.choose else p.getD i false, fun i hi => ?_, ?_⟩
  · by_cases he : ∃ w, f w = i
    · simp only [he, dite_true]
      have hc := he.choose_spec
      have := h he.choose (by omega)
      rw [this]; simp [hc]
    · simp [he, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · funext w
    have he : ∃ w', f w' = f w := ⟨w, rfl⟩
    simp only [Function.comp_apply, he, dite_true]
    exact congrArg τ (hf he.choose_spec)

/-! ## Las líneas de un certificado entran en la traza -/

/-- Una derivación por planos de corte es una derivación con las reglas de la traza. -/
theorem lineProof_de_cp {f : W → ℕ} {Γ : Set (Ineq W)} {ls : List (Ineq W)}
    (h : LineProof (CuttingPlanes.rules W) Γ ls) :
    LineProof (reglas f) (Linea.ineq '' Γ) (ls.map Linea.ineq) := by
  induction h with
  | nil => exact .nil
  | hyp _ hx ih => exact ih.hyp ⟨_, hx, rfl⟩
  | @step ls r _ hr hp ih =>
    refine ih.step (r := ⟨r.premises.map Linea.ineq, Linea.ineq r.concl⟩)
      ⟨by simpa using CuttingPlanes.rules_premises_length_le hr, fun τ hτ => ?_⟩ ?_
    · exact CuttingPlanes.rules_sound hr fun I hI => hτ (.ineq I) (List.mem_map_of_mem hI)
    · intro x hx
      obtain ⟨I, hI, rfl⟩ := List.mem_map.1 hx
      exact List.mem_map_of_mem (hp I hI)


/-- **Los coeficientes de una cláusula valen `-1`, `0` o `1`.** -/
theorem abs_coeff_clause_le [DecidableEq W] (d : Clause W) (w : W) : |d.toIneq.coeff w| ≤ 1 := by
  have hterm : ∀ l : Literal W, (Literal.toIneq l).coeff w =
      (if l = (w, true) then 1 else 0) - (if l = (w, false) then 1 else 0) := by
    rintro ⟨v, b⟩
    cases b <;> by_cases hv : v = w <;> simp [hv]
  rw [Clause.toIneq, Ineq.coeff_add, Ineq.coeff_sum, Finsupp.add_apply, Finset.sum_apply',
    Ineq.coeff_contra, Finsupp.zero_apply, zero_add, Finset.sum_congr rfl fun l _ => hterm l,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  split_ifs <;> simp

/-! ## Certificados semánticos: lo que la traza necesita de cada veredicto -/

/-- Achicar la cota de los coeficientes no cuesta nada. -/
theorem acotada_mono {M M' : ℕ} (h : M ≤ M') {x : Linea W} (hx : Acotada M x) : Acotada M' x := by
  cases x with
  | ineq I => exact fun w => (hx w).trans (by exact_mod_cast h)
  | fuera _ => trivial

/-- **Certificado semántico.** Cada vez que `det` dice «muerto» en `p`, hay una derivación con las reglas de la
traza, desde las desigualdades de `φ`, de la línea «no sigue a `p`», de a lo sumo `c p + 1` líneas, y con
coeficientes a lo sumo `M`. Es lo único que la traza usa de un certificado. Los de planos de corte
(`certificaSem_de_cp`) y los de resolución (`certificaSem_de_res`) lo son. -/
def CertificaSem [DecidableEq W] (φ : CNF W) (f : W → ℕ) (N : ℕ) (det : List Bool → Bool) (c : List Bool → ℕ)
    (M : ℕ) : Prop :=
  ∀ p : List Bool, p.length ≤ N → det p = true →
    ∃ ls : List (Linea W), LineProof (reglas f) (Linea.ineq '' φ.toIneqs) ls ∧ Linea.fuera p ∈ ls ∧
      ls.length ≤ c p + 1 ∧ ∀ x ∈ ls, Acotada M x

/-- **Un certificado por planos de corte es un certificado semántico**: la derivación, más la línea «no sigue a
`p`», que sale de la desigualdad falsa debajo de `p` en un paso. -/
theorem certificaSem_de_cp [DecidableEq W] {φ : CNF W} {f : W → ℕ} {N : ℕ} {det : List Bool → Bool}
    {c : List Bool → ℕ} {M : ℕ} (hcert : CertificaCP φ f N det c M) : CertificaSem φ f N det c M := by
  intro p hp hd
  obtain ⟨I, ls, h, hI, hl, hM, hfalsa⟩ := hcert p hp hd
  refine ⟨Linea.fuera p :: ls.map Linea.ineq, ?_, List.mem_cons_self, by simpa using hl, ?_⟩
  · refine (lineProof_de_cp (CuttingPlanes.isProof_iff_lineProof.1 h)).step
      (r := ⟨[Linea.ineq I], Linea.fuera p⟩) ⟨by simp, fun τ hτ hs => ?_⟩ (by simpa using hI)
    exact hfalsa τ hs (hτ (.ineq I) (by simp))
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · trivial
    · obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
      exact hM J hJ

/-! ## La traza de la búsqueda como derivación semántica -/

/-- **El puente.** Debajo de todo nodo muerto hay una derivación con las reglas de la traza de la línea «no sigue a
`p`». Sus líneas son las de los certificados, las cláusulas falsas de las hojas y una línea «no sigue» por nodo. Su
largo es a lo sumo la suma de `costoCP det c` sobre los nodos que visita la búsqueda. Todas sus desigualdades tienen
coeficientes a lo sumo `max M 1`. -/
theorem traza_debajo [DecidableEq W] {φ : CNF W} {f : W → ℕ} (hf : Function.Injective f) {N : ℕ}
    (hN : ∀ w, f w < N) {det : List Bool → Bool} {c : List Bool → ℕ} {M : ℕ}
    (hcert : CertificaSem φ f N det c M) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = N → ¬ Vivo (solCNF (φ.relabel f)) k p →
      ∃ ls : List (Linea W), LineProof (reglas f) (Linea.ineq '' φ.toIneqs) ls ∧ Linea.fuera p ∈ ls ∧
        ls.length ≤ peso (solCNF (φ.relabel f)) det (costoCP det c) k p ∧ ∀ x ∈ ls, Acotada (max M 1) x := by
  have hvar : ∀ c ∈ (φ.relabel f : List Clausula), ∀ l ∈ c, l.1 < N := by
    intro c hc l hl
    simp only [CNF.relabel, List.mem_map] at hc
    obtain ⟨c', -, rfl⟩ := hc
    simp only [Clause.relabel, List.mem_map] at hl
    obtain ⟨l', -, rfl⟩ := hl
    exact hN l'.1
  -- la hoja de un certificado
  have hoja : ∀ p : List Bool, p.length ≤ N → det p = true →
      ∃ ls : List (Linea W), LineProof (reglas f) (Linea.ineq '' φ.toIneqs) ls ∧ Linea.fuera p ∈ ls ∧
        ls.length ≤ c p + 1 ∧ ∀ x ∈ ls, Acotada (max M 1) x := by
    intro p hp hd
    obtain ⟨ls, h, hp, hl, hb⟩ := hcert p hp hd
    exact ⟨ls, h, hp, hl, fun x hx => acotada_mono (le_max_left M 1) (hb x hx)⟩
  intro k
  induction k with
  | zero =>
    intro p hl hm
    by_cases hd : det p = true
    · obtain ⟨ls, h, hp, hle, hb⟩ := hoja p (by omega) hd
      exact ⟨ls, h, hp, by simpa [peso, costoCP, hd] using hle, hb⟩
    · have hsol : solCNF (φ.relabel f) p = false := by
        cases h : solCNF (φ.relabel f) p
        · rfl
        · exact absurd ((vivo_cero _ p).mpr h) hm
      obtain ⟨h1, h2⟩ := clFalsa_spec (det_de_completa hvar (by omega) hsol)
      obtain ⟨d, hd', hdC⟩ : ∃ d ∈ φ, Clause.relabel f d = clFalsa (φ.relabel f) p := List.mem_map.1 h1
      refine ⟨[Linea.fuera p, Linea.ineq d.toIneq], ?_, by simp, by simp [peso, costoCP, hd], ?_⟩
      · refine ((LineProof.nil (R := reglas f) (Γ := Linea.ineq '' φ.toIneqs)).hyp
          (Set.mem_image_of_mem _ (CNF.toIneq_mem_toIneqs hd'))).step
          (r := ⟨[Linea.ineq d.toIneq], Linea.fuera p⟩) ⟨by simp, fun τ hτ hs => ?_⟩ (by simp)
        have hh : d.toIneq.Holds τ := hτ (.ineq d.toIneq) (by simp)
        rw [Clause.holds_toIneq_iff] at hh
        obtain ⟨σ, hσ, rfl⟩ := existe_sigue hf hs
        have := eval_falsificada hσ h2
        rw [← hdC, Clause.eval_relabel] at this
        rw [this] at hh
        exact Bool.false_ne_true hh
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · trivial
        · exact fun w => (abs_coeff_clause_le d w).trans (by exact_mod_cast le_max_right M 1)
  | succ k ih =>
    intro p hl hm
    by_cases hd : det p = true
    · obtain ⟨ls, h, hp, hle, hb⟩ := hoja p (by omega) hd
      exact ⟨ls, h, hp, by simpa [peso, costoCP, hd] using hle, hb⟩
    · have hb : ∀ b, ¬ Vivo (solCNF (φ.relabel f)) k (p ++ [b]) := fun b h =>
        hm ((vivo_succ _ k p).mpr (by cases b <;> simp [h]))
      have ha : (buscar (solCNF (φ.relabel f)) det k (p ++ [false])).1 = false := by
        cases h : (buscar (solCNF (φ.relabel f)) det k (p ++ [false])).1
        · rfl
        · exact absurd (buscar_vivo _ _ k _ h) (hb false)
      obtain ⟨ls₀, h₀, m₀, l₀, b₀⟩ := ih (p ++ [false]) (by simp; omega) (hb false)
      obtain ⟨ls₁, h₁, m₁, l₁, b₁⟩ := ih (p ++ [true]) (by simp; omega) (hb true)
      refine ⟨Linea.fuera p :: (ls₀ ++ ls₁), ?_, List.mem_cons_self, ?_, ?_⟩
      · refine (h₀.append h₁).step (r := ⟨[Linea.fuera (p ++ [false]), Linea.fuera (p ++ [true])], Linea.fuera p⟩)
          ⟨by simp, fun τ hτ hs => ?_⟩ ?_
        · obtain ⟨b, hsb⟩ := sigueV_snoc hf hs
          cases b
          · exact hτ (.fuera (p ++ [false])) (by simp) hsb
          · exact hτ (.fuera (p ++ [true])) (by simp) hsb
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact List.mem_append_left _ m₀
          · exact List.mem_append_right _ m₁
      · simp only [List.length_cons, List.length_append, peso, costoCP, hd, ha, Bool.false_eq_true, ite_false]
        omega
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · trivial
        · rcases List.mem_append.1 hx with hx | hx
          · exact b₀ x hx
          · exact b₁ x hx

/-- **La traza de la búsqueda es una refutación semántica.** Si `φ` no tiene solución y `det` está certificado por
planos de corte, las líneas de la traza, leídas desde la primera, forman una refutación semántica (Krajíček 1997,
Definición 4.1) de los conjuntos de soluciones de las desigualdades de `φ`. Tiene a lo sumo
`peso … (costoCP det c) N []` líneas, y todas sus desigualdades tienen coeficientes a lo sumo `max M 1`. -/
theorem traza_refutacion [DecidableEq W] {φ : CNF W} (hφ : ¬ φ.Satisfiable) {f : W → ℕ}
    (hf : Function.Injective f) {N : ℕ} (hN : ∀ w, f w < N) {det : List Bool → Bool} {c : List Bool → ℕ}
    {M : ℕ} (hcert : CertificaSem φ f N det c M) {init : Set (Set (W → Bool))}
    (hinit : ∀ E ∈ φ.toIneqs, {τ : W → Bool | E.Holds τ} ∈ init) :
    ∃ ls : List (Linea W), ls.length ≤ peso (solCNF (φ.relabel f)) det (costoCP det c) N [] ∧
      (∀ x ∈ ls, Acotada (max M 1) x) ∧
      IsSemanticRefutation init fun j : Fin ls.reverse.length => modelos f ls.reverse[j] := by
  have hF : ¬ CNF.Satisfiable (φ.relabel f : CNF ℕ) := by rwa [CNF.satisfiable_relabel hf]
  obtain ⟨ls, h, hp, hle, hb⟩ := traza_debajo hf hN hcert N [] (by simp) (raiz_muerta hF N)
  refine ⟨ls, hle, hb, h.toSemanticRefutation ?_ (fun r hr => hr.1) (fun r hr => hr.2) hp ?_⟩
  · rintro _ ⟨E, hE, rfl⟩
    exact hinit E hE
  · intro τ hτ
    exact hτ (sigueV_nil f τ)

/-! ## Un certificado semántico da un detector sano -/

/-- **Un detector con certificado semántico es sano.** Una solución que sigue a `p` cumple las desigualdades de `φ`,
luego toda línea de la derivación, luego «no sigue a `p`»: contradicción. -/
theorem certificaSem_sanoN [DecidableEq W] {φ : CNF W} {f : W → ℕ} {N : ℕ} {det : List Bool → Bool}
    {c : List Bool → ℕ} {M : ℕ} (hcert : CertificaSem φ f N det c M) : SanoN (solCNF (φ.relabel f)) det N := by
  rintro p hp hd ⟨q, -, hs⟩
  obtain ⟨ls, h, hpl, -, -⟩ := hcert p hp hd
  set τ : W → Bool := fun w => (p ++ q).getD (f w) false
  have hτ : CNF.eval τ φ = true := by
    have := eval_de_solCNF hs
    rwa [CNF.eval_relabel] at this
  have hall := h.holds (Sem := fun x => τ ∈ modelos f x)
    (by rintro _ ⟨E, hE, rfl⟩; exact (CNF.holds_toIneqs_iff τ φ).2 hτ E hE) (fun r hr hp => hr.2 τ hp)
  refine hall _ hpl fun w hw => ?_
  simp [τ, List.getD_eq_getElem?_getD, List.getElem?_append_left hw, List.getElem?_eq_getElem hw]

/-! ## Caso particular: resolución -/

/-- Una derivación por resolución de `φ.relabel f`, con `f` inyectiva, es la renombrada de una de `φ`. -/
theorem isProof_de_relabel [DecidableEq W] {φ : CNF W} {f : W → ℕ} (hf : Function.Injective f)
    {ls : List (Clause ℕ)} (h : (φ.relabel f).IsProof ls) :
    ∃ ls', φ.IsProof ls' ∧ ls'.map (Clause.relabel f) = ls := by
  induction h with
  | nil => exact ⟨[], .nil, rfl⟩
  | mem _ hc ih =>
    obtain ⟨ls', h', rfl⟩ := ih
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact ⟨c' :: ls', h'.mem hc', rfl⟩
  | resolvent v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨ls', h', rfl⟩ := ih
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 h₁
    obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.1 h₂
    obtain ⟨⟨u, b⟩, hu₁, hub⟩ := List.mem_map.1 hv₁
    obtain ⟨⟨u', b'⟩, hu₂, hub'⟩ := List.mem_map.1 hv₂
    simp only [Prod.map, id, Prod.mk.injEq] at hub hub'
    obtain ⟨rfl, rfl⟩ := hub
    obtain ⟨hu', rfl⟩ := hub'
    obtain rfl : u = u' := (hf hu').symm
    exact ⟨_ :: ls', h'.resolvent u hc₁ hc₂ hu₁ hu₂,
      by rw [List.map_cons, Clause.relabel_resolvent hf]⟩

/-- Una derivación por resolución, como derivación de la traza: cada cláusula pasa a su desigualdad. -/
theorem lineProof_de_res [DecidableEq W] {f : W → ℕ} {φ : CNF W} {ls : List (Clause W)} (h : φ.IsProof ls) :
    LineProof (reglas f) (Linea.ineq '' φ.toIneqs) (ls.map fun d => Linea.ineq d.toIneq) := by
  induction h with
  | nil => exact .nil
  | mem _ hc ih => exact ih.hyp ⟨_, CNF.toIneq_mem_toIneqs hc, rfl⟩
  | @resolvent ls c₁ c₂ v _ h₁ h₂ _ _ ih =>
    refine ih.step (r := ⟨[Linea.ineq c₁.toIneq, Linea.ineq c₂.toIneq], Linea.ineq (c₁.resolvent c₂ v).toIneq⟩)
      ⟨by simp, fun τ hτ => ?_⟩ ?_
    · have e₁ : c₁.toIneq.Holds τ := hτ (.ineq c₁.toIneq) (by simp)
      have e₂ : c₂.toIneq.Holds τ := hτ (.ineq c₂.toIneq) (by simp)
      rw [Clause.holds_toIneq_iff] at e₁ e₂
      exact (Clause.holds_toIneq_iff τ _).2 (Clause.eval_resolvent v e₁ e₂)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_map_of_mem (f := fun d => Linea.ineq d.toIneq) h₁
      · exact List.mem_map_of_mem (f := fun d => Linea.ineq d.toIneq) h₂

/-- **Todo detector certificado por resolución (`CertificaRes`) tiene certificado semántico**, con coeficientes `1`
y el mismo tamaño. Las cláusulas entran como sus desigualdades; un paso de resolución es una regla sana de dos
premisas. (No hace falta simular resolución en planos de corte: la traza ya es semántica.) -/
theorem certificaSem_de_res [DecidableEq W] {φ : CNF W} {f : W → ℕ} (hf : Function.Injective f) {N : ℕ}
    {det : List Bool → Bool} {c : List Bool → ℕ} (hcert : CertificaRes (φ.relabel f) N det c) :
    CertificaSem φ f N det c 1 := by
  intro p hp hd
  obtain ⟨C, ls, h, hC, hl, hfalsa⟩ := hcert p hp hd
  obtain ⟨ls', h', rfl⟩ := isProof_de_relabel hf h
  obtain ⟨d, hd', rfl⟩ := List.mem_map.1 hC
  refine ⟨Linea.fuera p :: ls'.map fun d => Linea.ineq d.toIneq, ?_, List.mem_cons_self, by simpa using hl, ?_⟩
  · refine (lineProof_de_res h').step (r := ⟨[Linea.ineq d.toIneq], Linea.fuera p⟩) ⟨by simp, fun τ hτ hs => ?_⟩
      (by simpa using ⟨d, hd', rfl⟩)
    have hh : d.toIneq.Holds τ := hτ (.ineq d.toIneq) (by simp)
    rw [Clause.holds_toIneq_iff] at hh
    obtain ⟨σ, hσ, rfl⟩ := existe_sigue hf hs
    have := hfalsa σ hσ
    rw [Clause.eval_relabel, hh] at this
    exact Bool.false_ne_true this.symm
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · trivial
    · obtain ⟨J, -, rfl⟩ := List.mem_map.1 hx
      exact abs_coeff_clause_le J

/-! ## La complejidad de comunicación de «no sigue a `p`» -/

section Comunicacion

open Cslib.Communication SemanticDerivation

variable {X Y Z : Type*}

theorem sigueV_iff_getD {f : W → ℕ} {τ : W → Bool} {p : List Bool} :
    SigueV f τ p ↔ ∀ w, f w < p.length → τ w = p.getD (f w) false := by
  refine forall_congr' fun w => ?_
  constructor
  · intro h hl; rw [h hl]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  · intro h hl; rw [h hl]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

/-- La parte de Alice: sus variables privadas siguen a `p`. -/
def OkA (f : X ⊕ (Y ⊕ Z) → ℕ) (p : List Bool) (q : Y → Bool) : Prop :=
  ∀ y, f (.inr (.inl y)) < p.length → q y = p.getD (f (.inr (.inl y))) false

/-- La parte de Bob: las compartidas y sus privadas siguen a `p`. -/
def OkB (f : X ⊕ (Y ⊕ Z) → ℕ) (p : List Bool) (v : X → Bool) (r : Z → Bool) : Prop :=
  (∀ x, f (.inl x) < p.length → v x = p.getD (f (.inl x)) false) ∧
    ∀ z, f (.inr (.inr z)) < p.length → r z = p.getD (f (.inr (.inr z))) false

/-- Seguir a `p` es que las dos partes lo sigan. -/
theorem sigueV_partes {f : X ⊕ (Y ⊕ Z) → ℕ} {p : List Bool} {v : X → Bool} {q : Y → Bool} {r : Z → Bool} :
    SigueV f (Sum.elim v (Sum.elim q r)) p ↔ OkA f p q ∧ OkB f p v r := by
  rw [sigueV_iff_getD, Sum.forall, Sum.forall]
  simp only [Sum.elim_inl, Sum.elim_inr, OkA, OkB]
  tauto

/-- **«No sigue a `p`» cuesta dos bits.** Alice manda si sus variables siguen a `p`; Bob contesta. Vale para todo
`p`, fije o no variables compartidas, porque la interpolación solo pide decidir si `(v, q, r)` está en la línea. -/
theorem ecomplexity_fuera_le (f : X ⊕ (Y ⊕ Z) → ℕ) (p : List Bool) (A : Set ((X → Bool) × (Y → Bool)))
    (B : Set ((X → Bool) × (Z → Bool))) :
    Protocol.ecomplexity (Decides (MemRight (modelos f (.fuera p)))) A B ≤ 2 := by
  classical
  refine Protocol.ecomplexity_decides_le.trans ?_
  have h := Protocol.ecomplexityFun_le_clog_card_finset_succ (X := (X → Bool) × (Y → Bool))
    (Y := (X → Bool) × (Z → Bool)) (Finset.univ : Finset Bool) (fun a => decide (OkA f p a.2))
    (fun _ => Finset.mem_univ _) (fun bA b => !(bA && decide (OkB f p b.1 b.2)))
  have hc : Nat.clog 2 (Finset.univ : Finset Bool).card = 1 := by
    rw [Finset.card_univ, Fintype.card_bool]; simpa using Nat.clog_pow 2 1 (by omega)
  rw [hc] at h
  refine le_of_eq_of_le ?_ (h.trans (by norm_num))
  congr 1
  funext a b
  simp only [MemRight, modelos, Set.mem_ofPred_eq, sigueV_partes]
  by_cases h1 : OkA f p a.2 <;> by_cases h2 : OkB f p b.1 b.2 <;> simp [h1, h2]

end Comunicacion

/-! ## Interpolación sobre clique–coloreo -/

section CliqueColoreo

open Cslib.Communication Cslib.Circuits Cslib.Circuits.Clique Cslib.BitString.Graph SemanticDerivation
open PlanosDeCorteClique

variable {n k r : ℕ}

/-- Las variables de `Clique_{n,k} ∧ Color_{n,r}`: aristas, más las del clique, más las del coloreo. -/
abbrev VarsCC (n k r : ℕ) := Fin (edgeCount n) ⊕ (Fin k × Fin n ⊕ Fin n × Fin r)

/-- Con coeficiente no negativo, una caída en la contribución de una variable compartida es un `1` de Alice y un `0`
de Bob. -/
theorem exceedsAt_de_lt {a : ℤ} (ha : 0 ≤ a) {u v : Fin m → Bool} {i : Fin m}
    (h : a * (v i).toInt < a * (u i).toInt) : ExceedsAt u v i := by
  cases hu : u i <;> cases hv : v i <;> simp_all [ExceedsAt]
  omega

/-- **Interpolación monótona de la traza.** Si `det` está certificado por planos de corte sobre
`Clique_{n,k} ∧ Color_{n,r}` (con `r < k`), en cualquier orden inyectivo `f` de las variables, hay un circuito
monótono que separa los grafos con `k`-clique de los `r`-coloreables, de a lo sumo
`(P · 2^(2t) + 1) · 2^(2t+1)` compuertas, donde `P = peso … (costoCP det c) N []` es el tamaño de la traza. `t` es
como en Krajíček 6.4, y al menos `2` por las líneas «no sigue». -/
theorem existe_separador_traza (hrk : r < k) {f : VarsCC n k r → ℕ} (hf : Function.Injective f) {N : ℕ}
    (hN : ∀ w, f w < N) {det : List Bool → Bool} {c : List Bool → ℕ} {M : ℕ}
    (hcert : CertificaSem (CNF.cliqueColoring n k r) f N det c M) {t : ℕ} (ht₁ : 2 ≤ t)
    (ht₂ : Nat.clog 2 (2 * max M 1 * (k * n) + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 (edgeCount n) * (Nat.clog 2 (2 * 1 * edgeCount n + 1) + 1) ≤ t) :
    ∃ C : Circuit Monotone.signature (edgeCount n) 1,
      C.size ≤ (peso (solCNF ((CNF.cliqueColoring n k r).relabel f)) det (costoCP det c) N [] * 2 ^ (2 * t) + 1) *
        2 ^ (2 * t + 1) ∧
      Separates k r fun x => C.eval Monotone.interpretation x 0 := by
  set 𝒜 : Set (Set (Fin (edgeCount n) ⊕ Fin k × Fin n → Bool)) :=
    (fun E => {σ | E.Holds σ}) '' (CNF.clique n k).toIneqs
  set ℬ : Set (Set (Fin (edgeCount n) ⊕ Fin n × Fin r → Bool)) :=
    (fun E => {σ | E.Holds σ}) '' (CNF.coloring n r).toIneqs
  have hinit : ∀ E ∈ (CNF.cliqueColoring n k r).toIneqs, {τ : VarsCC n k r → Bool | E.Holds τ} ∈ initSets 𝒜 ℬ := by
    intro E hE
    rw [toIneqs_cliqueColoring] at hE
    rcases hE with ⟨E', hE', rfl⟩ | ⟨E', hE', rfl⟩
    · exact Or.inl ⟨_, ⟨E', hE', rfl⟩, (CuttingPlanes.setOf_holds_relabel_inl E').symm⟩
    · exact Or.inr ⟨_, ⟨E', hE', rfl⟩, (CuttingPlanes.setOf_holds_relabel_inr E').symm⟩
  obtain ⟨ls, hle, hb, hD⟩ := traza_refutacion (CNF.not_satisfiable_cliqueColoring hrk) hf hN hcert hinit
  have hcard : Fintype.card (Fin k × Fin n) = k * n := by simp
  obtain ⟨C, hsize, hU, hV⟩ := hD.exists_monotone_circuit (t := t)
    (fun j => by
      have hx : ls.reverse[j] ∈ ls := List.mem_reverse.1 (List.getElem_mem _)
      have hbj := hb _ hx
      generalize ls.reverse[j] = x at hbj ⊢
      cases x with
      | ineq I =>
        refine (CuttingPlanes.ecomplexity_memRight_holds_le I (M := max M 1) (fun y => hbj _) _ _).trans ?_
        rw [hcard]; exact_mod_cast ht₂
      | fuera p => exact (ecomplexity_fuera_le f p _ _).trans (by exact_mod_cast ht₁))
    (fun j S hS _ => by
      obtain ⟨E, hE, rfl⟩ := hS
      refine (CuttingPlanes.ecomplexity_search_holds_le E (M₀ := 1) (fun i => ?_)
        (fun _ _ i => exceedsAt_de_lt (coeff_arista_nonneg hE i)) _ _).trans (by exact_mod_cast ht₃)
      rw [abs_of_nonneg (coeff_arista_nonneg hE i)]
      exact_mod_cast coeff_arista_le_one hE i)
  refine ⟨C, hsize.trans ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [List.length_reverse]; gcongr
  · obtain ⟨q, hq⟩ := (CNF.exists_eval_clique_iff x).2 hx
    exact hU x q (CuttingPlanes.mem_models_iff.2 ((CNF.holds_toIneqs_iff _ _).2 hq))
  · obtain ⟨z, hz⟩ := (CNF.exists_eval_coloring_iff x).2 hx
    exact hV x z (CuttingPlanes.mem_models_iff.2 ((CNF.holds_toIneqs_iff _ _).2 hz))

/-- **La cota sobre la traza.** Para `n ≥ 2^40`, `⌊√n⌋ < k ≤ ⌊√n⌋ + 2` y `r + 1 = k`, si `det` tiene certificado
semántico sobre `Clique_{n,k} ∧ Color_{n,r}` con coeficientes a lo sumo `M`, y `2 (max M 1 + 1) n² + 1 ≤ 2^b`, el
tamaño `P` de la traza cumple `2^⌊⌊√⌊√n⌋⌋/2⌋ < (P + 1) · 2^(4(b+1)² + 1)`. Con `M` polinomial en `n`,
`b = O(log n)` y `P ≥ 2^(Ω(n^{1/4}) − O(log² n))`. -/
theorem cota_traza (hn : 2 ^ 40 ≤ n) (hk : n.sqrt < k) (hk' : k ≤ n.sqrt + 2) (hr : r + 1 = k)
    {f : VarsCC n k r → ℕ} (hf : Function.Injective f) {N : ℕ} (hN : ∀ w, f w < N) {det : List Bool → Bool}
    {c : List Bool → ℕ} {M : ℕ} (hcert : CertificaSem (CNF.cliqueColoring n k r) f N det c M) {b : ℕ}
    (hb : 2 * (max M 1 + 1) * n ^ 2 + 1 ≤ 2 ^ b) :
    2 ^ (n.sqrt.sqrt / 2) <
      (peso (solCNF ((CNF.cliqueColoring n k r).relabel f)) det (costoCP det c) N [] + 1) *
        2 ^ (4 * (b + 1) ^ 2 + 1) := by
  have hkn : k ≤ n := by
    have h2 : n.sqrt + 2 ≤ n := by
      have : 2 ≤ n.sqrt := Nat.le_sqrt.2 (by omega)
      have := Nat.sqrt_le' n
      nlinarith
    omega
  obtain ⟨ht₂, ht₃⟩ := t_cabe (M := max M 1) hkn hb
  have hM1 : 1 ≤ max M 1 := le_max_right M 1
  have ht₃' : Nat.clog 2 (edgeCount n) * (Nat.clog 2 (2 * 1 * edgeCount n + 1) + 1) ≤ (b + 1) ^ 2 := by
    refine le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.clog_mono_right 2 ?_) 1)) ht₃
    have := Nat.mul_le_mul_right (edgeCount n) (Nat.mul_le_mul_left 2 hM1)
    omega
  have ht₁ : 2 ≤ (b + 1) ^ 2 := by
    rcases b with _ | b
    · have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
      simp at hb; nlinarith
    · have : 2 ≤ b + 1 + 1 := by omega
      nlinarith
  obtain ⟨C, hsize, hC⟩ := existe_separador_traza (by omega) hf hN hcert ht₁ ht₂ ht₃'
  obtain rfl : r = k - 1 := by omega
  calc 2 ^ (n.sqrt.sqrt / 2) < C.size := Monotone.two_pow_lt_size_of_separates_sqrt hn hk hk' hC
    _ ≤ _ := hsize
    _ ≤ _ := acota_tamano _ _

/-! ## Sin demora logarítmica -/

/-- El número de variables de la sucesión `n = 2^(4j)`, `k = 2^(2j) + 1`, `r = 2^(2j)`, más uno, cabe en
`2^(8j+3)`. -/
theorem card_varsCC_le (j : ℕ) :
    Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1 ≤ 2 ^ (8 * j + 3) := by
  have hcard : Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) =
      edgeCount (2 ^ (4 * j)) + ((2 ^ (2 * j) + 1) * 2 ^ (4 * j) + 2 ^ (4 * j) * 2 ^ (2 * j)) := by
    simp [VarsCC, Fintype.card_sum, Fintype.card_prod]
  have hE : edgeCount (2 ^ (4 * j)) ≤ (2 ^ (4 * j)) ^ 2 :=
    (edgeCount_eq_choose _).trans_le (Nat.choose_le_pow _ 2)
  have h4 : (2 : ℕ) ^ (4 * j) = 2 ^ (2 * j) * 2 ^ (2 * j) := by rw [← pow_add]; ring_nf
  have h8 : (2 : ℕ) ^ (8 * j + 3) = 8 * (2 ^ (2 * j) * 2 ^ (2 * j) * (2 ^ (2 * j) * 2 ^ (2 * j))) := by
    rw [show 8 * j + 3 = 2 * j + 2 * j + (2 * j + 2 * j) + 3 by ring, pow_add, pow_add, pow_add]; ring
  have hX : 1 ≤ 2 ^ (2 * j) := Nat.one_le_two_pow
  rw [hcard, h8]
  rw [h4] at hE ⊢
  generalize 2 ^ (2 * j) = X at hE hX ⊢
  have hXY : X ≤ X * X := Nat.le_mul_self X
  have h1 : 1 ≤ X * X := Nat.mul_le_mul hX hX
  generalize X * X = Y at hE hXY h1 ⊢
  have h2 : X * Y ≤ Y * Y := Nat.mul_le_mul_right Y hXY
  have h3 : Y ≤ Y * Y := Nat.le_mul_self Y
  nlinarith

/-- `2^E + 1 ≤ 2^(E+1)`. -/
theorem pow_mas_uno (E : ℕ) : 2 ^ E + 1 ≤ 2 ^ (E + 1) := by
  rw [pow_succ]; have := Nat.one_le_two_pow (n := E); omega

/-- **Ningún detector con certificado semántico, con derivaciones de tamaño y coeficientes polinomiales, tiene
demora logarítmica sobre clique–coloreo.** Para todos `a`, `b`, `e` y `K` hay un `j` tal que, con
`n = 2^(4j)`, `k = 2^(2j) + 1`, `r = 2^(2j)` y `N` el número de variables, en cualquier orden inyectivo de las
variables, ningún detector con certificado semántico de tamaño y coeficientes a lo sumo `K · (N+1)^e` tiene demora
`a · log₂(N+1) + b`. -/
theorem sem_sin_demora_log (a b e K : ℕ) :
    ∃ j, ∀ f : VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)) → ℕ, Function.Injective f →
      (∀ w, f w < Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)))) →
      ∀ (det : List Bool → Bool) (c : List Bool → ℕ) (M : ℕ),
        CertificaSem (CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) f
          (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)))) det c M →
        M ≤ K * (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) ^ e →
        (∀ p, c p ≤ K * (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) ^ e) →
        ¬ DemoraN (solCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel f)) det
          (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))))
          (a * Nat.log 2 (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) + b) := by
  have hg : PolynomiallyBounded fun j =>
      2 * (((8 * j + 3) + a * (8 * j + 3) + (b + 1) + (K + 2) + e * (8 * j + 3) + 1) +
        (4 * ((K + 2) + e * (8 * j + 3) + (8 * j) + 2 + 1) ^ 2 + 1)) + 2 := by
    fun_prop
  obtain ⟨j, hj, hj10⟩ := (hg.eventually_lt_two_pow.and (Filter.eventually_ge_atTop 10)).exists
  refine ⟨j, fun f hf hN det c M hcert hM hc hd => ?_⟩
  set N := Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) with hNdef
  set L := 8 * j + 3 with hLdef
  have hN1 : N + 1 ≤ 2 ^ L := card_varsCC_le j
  -- arriba: la búsqueda con demora logarítmica es corta
  have hup := nodos_le (k := N) (p := []) (certificaSem_sanoN hcert) hd (by simp)
  have hpeso := peso_le (solCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel f))
    det (costoCP det c) (C := K * (N + 1) ^ e + 2) (fun p => by
      unfold costoCP; split
      · have := hc p; omega
      · omega) N []
  have hNe : (N + 1) ^ e ≤ 2 ^ (e * L) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hN1 e
  have hNa : (N + 1) ^ a ≤ 2 ^ (a * L) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hN1 a
  have hlog : 2 ^ (a * Nat.log 2 (N + 1)) ≤ (N + 1) ^ a := dos_pow_mul_log_le a (N + 1) (by omega)
  have hK2 : K + 2 ≤ 2 ^ (K + 2) := Nat.lt_two_pow_self.le
  have hKe : K * (N + 1) ^ e + 2 ≤ 2 ^ (K + 2) * 2 ^ (e * L) := by
    have h1 : 1 ≤ 2 ^ (e * L) := Nat.one_le_two_pow
    calc K * (N + 1) ^ e + 2 ≤ K * 2 ^ (e * L) + 2 * 2 ^ (e * L) := by gcongr; omega
      _ = (K + 2) * 2 ^ (e * L) := by ring
      _ ≤ 2 ^ (K + 2) * 2 ^ (e * L) := by gcongr
  set P := peso (solCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel f)) det
    (costoCP det c) N [] with hPdef
  have hP : P + 1 ≤ 2 ^ (L + a * L + (b + 1) + (K + 2) + e * L + 1) := by
    refine le_trans ?_ (pow_mas_uno _)
    refine Nat.add_le_add_right ?_ 1
    calc P ≤ _ := hpeso
      _ ≤ ((N + 1) * 2 ^ (a * Nat.log 2 (N + 1) + b + 1)) * (2 ^ (K + 2) * 2 ^ (e * L)) :=
          Nat.mul_le_mul (by simpa using hup) hKe
      _ = (N + 1) * 2 ^ (a * Nat.log 2 (N + 1)) * 2 ^ (b + 1) * (2 ^ (K + 2) * 2 ^ (e * L)) := by
          rw [show a * Nat.log 2 (N + 1) + b + 1 = a * Nat.log 2 (N + 1) + (b + 1) by ring, pow_add]; ring
      _ ≤ 2 ^ L * 2 ^ (a * L) * 2 ^ (b + 1) * (2 ^ (K + 2) * 2 ^ (e * L)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN1 (hlog.trans hNa)) le_rfl) le_rfl
      _ = 2 ^ (L + a * L + (b + 1) + (K + 2) + e * L) := by simp only [pow_add]; ring
  -- abajo: la cota de interpolación
  have hb' : 2 * (max M 1 + 1) * (2 ^ (4 * j)) ^ 2 + 1 ≤ 2 ^ ((K + 2) + e * L + 8 * j + 2) := by
    have hM' : max M 1 + 1 ≤ 2 ^ (K + 2) * 2 ^ (e * L) := by
      have : max M 1 ≤ M + 1 := max_le (by omega) (by omega)
      omega
    have hn2 : (2 ^ (4 * j)) ^ 2 = 2 ^ (8 * j) := by rw [← pow_mul]; ring_nf
    have h1 : 1 ≤ 2 ^ (K + 2) * 2 ^ (e * L) * 2 ^ (8 * j) := Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [hn2]
    calc 2 * (max M 1 + 1) * 2 ^ (8 * j) + 1 ≤ 2 * (2 ^ (K + 2) * 2 ^ (e * L)) * 2 ^ (8 * j) + 1 := by gcongr
      _ ≤ 4 * (2 ^ (K + 2) * 2 ^ (e * L) * 2 ^ (8 * j)) := by nlinarith
      _ = 2 ^ ((K + 2) + e * L + 8 * j + 2) := by simp only [pow_add]; ring
  have hN40 : 2 ^ 40 ≤ 2 ^ (4 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : (2 ^ (4 * j)).sqrt = 2 ^ (2 * j) := sqrt_dos_pow_cuatro j
  have hlow := cota_traza (k := 2 ^ (2 * j) + 1) (r := 2 ^ (2 * j)) hN40 (by rw [hsq]; omega) (by rw [hsq]; omega)
    rfl hf hN hcert hb'
  rw [hsq, sqrt_dos_pow_dos] at hlow
  have hexp := exponente_lt hlow hP
  exact mitad_no_lt (by simpa [hLdef] using hj) hexp

/-- **Ningún detector certificado por planos de corte, con derivaciones de tamaño y coeficientes polinomiales, tiene
demora logarítmica sobre clique–coloreo.** Es `sem_sin_demora_log` para `CertificaCP`. -/
theorem cp_sin_demora_log (a b e K : ℕ) :
    ∃ j, ∀ f : VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)) → ℕ, Function.Injective f →
      (∀ w, f w < Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)))) →
      ∀ (det : List Bool → Bool) (c : List Bool → ℕ),
        CertificaCP (CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) f
          (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)))) det c
          (K * (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) ^ e) →
        (∀ p, c p ≤ K * (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) ^ e) →
        ¬ DemoraN (solCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel f)) det
          (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))))
          (a * Nat.log 2 (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) + b) := by
  obtain ⟨j, hj⟩ := sem_sin_demora_log a b e K
  exact ⟨j, fun f hf hN det c hcert hc => hj f hf hN det c _ (certificaSem_de_cp hcert) le_rfl hc⟩

/-- **Caso particular: resolución.** Ningún detector certificado por resolución (`CertificaRes`), con derivaciones de
tamaño polinomial, tiene demora logarítmica sobre clique–coloreo. -/
theorem res_cc_sin_demora_log (a b e K : ℕ) :
    ∃ j, ∀ f : VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)) → ℕ, Function.Injective f →
      (∀ w, f w < Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)))) →
      ∀ (det : List Bool → Bool) (c : List Bool → ℕ),
        CertificaRes ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel f)
          (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)))) det c →
        (∀ p, c p ≤ K * (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) ^ e) →
        ¬ DemoraN (solCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel f)) det
          (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))))
          (a * Nat.log 2 (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) + b) := by
  obtain ⟨j, hj⟩ := sem_sin_demora_log a b e (K + 1)
  refine ⟨j, fun f hf hN det c hcert hc => hj f hf hN det c 1 (certificaSem_de_res hf hcert) ?_ ?_⟩
  · have : 1 ≤ (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) ^ e :=
      Nat.one_le_pow _ _ (by omega)
    nlinarith
  · intro p
    exact (hc p).trans (Nat.mul_le_mul_right _ (Nat.le_succ K))

/-! ## Controles: las hipótesis se cumplen -/

/-- Un orden de las variables de clique–coloreo: el de `Fintype.equivFin`. -/
noncomputable def ordenCC (n k r : ℕ) (w : VarsCC n k r) : ℕ := (Fintype.equivFin _ w).val

theorem ordenCC_inj (n k r : ℕ) : Function.Injective (ordenCC n k r) :=
  Fin.val_injective.comp (Fintype.equivFin _).injective

theorem ordenCC_lt (n k r : ℕ) (w : VarsCC n k r) : ordenCC n k r w < Fintype.card (VarsCC n k r) :=
  (Fintype.equivFin _ w).isLt

end CliqueColoreo

/-- Una cláusula falsificada en `p`, vista en las variables `W`, es falsa en toda asignación que sigue a `p`. -/
theorem clausula_falsa {f : W → ℕ} (hf : Function.Injective f) {d : Clause W} {p : List Bool}
    (h : falsificada p (d.relabel f) = true) (τ : W → Bool) (hs : SigueV f τ p) : d.eval τ = false := by
  obtain ⟨σ, hσ, rfl⟩ := existe_sigue hf hs
  have := eval_falsificada hσ h
  rwa [Clause.eval_relabel] at this

/-- **`detCNF` está certificado por planos de corte** con derivaciones de una línea (la cláusula falsa) y
coeficientes `1`. -/
theorem certificaCP_detCNF [DecidableEq W] (φ : CNF W) {f : W → ℕ} (hf : Function.Injective f) (N : ℕ) :
    CertificaCP φ f N (detCNF (φ.relabel f)) (fun _ => 1) 1 := by
  intro p _ hd
  obtain ⟨h1, h2⟩ := clFalsa_spec hd
  obtain ⟨d, hd', hdC⟩ : ∃ d ∈ φ, Clause.relabel f d = clFalsa (φ.relabel f) p := List.mem_map.1 h1
  refine ⟨d.toIneq, [d.toIneq], CuttingPlanes.IsProof.nil.hyp (CNF.toIneq_mem_toIneqs hd'), by simp, by simp,
    by simpa using abs_coeff_clause_le d, fun τ hs hh => ?_⟩
  rw [Clause.holds_toIneq_iff, clausula_falsa hf (hdC ▸ h2) τ hs] at hh
  exact Bool.false_ne_true hh

/-- El detector que nunca dispara está certificado con cualquier tamaño: la hipótesis no pide nada si no hay
veredictos. -/
example [DecidableEq W] (φ : CNF W) (f : W → ℕ) (N : ℕ) : CertificaCP φ f N (fun _ => false) (fun _ => 0) 0 :=
  fun _ _ h => absurd h (by simp)

/-- `DemoraN` sola se cumple: el detector que siempre dispara tiene demora `0`. La que pesa en `cp_sin_demora_log` es
la conjunción con el certificado de tamaño polinomial. -/
example (sol : List Bool → Bool) (N : ℕ) : DemoraN sol (fun _ => true) N 0 := fun _ _ _ _ _ => rfl

section Controles

open Cslib.Circuits Cslib.Circuits.Clique Cslib.BitString.Graph PlanosDeCorteClique

/-- `0 ≥ 1` es una desigualdad de `Clique_{0,1} ∧ Color_{0,0}`; el detector que siempre dispara está certificado
por planos de corte con una línea y coeficientes `0`. -/
example (f : VarsCC 0 1 0 → ℕ) (N : ℕ) :
    CertificaCP (CNF.cliqueColoring 0 1 0) f N (fun _ => true) (fun _ => 1) 0 :=
  fun _ _ _ => ⟨Ineq.contra, [Ineq.contra], CuttingPlanes.IsProof.nil.hyp contra_mem_cero, by simp, by simp,
    by simp, fun τ _ => Ineq.not_holds_contra τ⟩

/-- `existe_separador_traza` se aplica a ese detector, con `t = 2`. -/
example : ∃ C : Circuit Monotone.signature (edgeCount 0) 1,
    Separates 1 0 fun x => C.eval Monotone.interpretation x 0 := by
  have hcert : CertificaCP (CNF.cliqueColoring 0 1 0) (ordenCC 0 1 0) (Fintype.card (VarsCC 0 1 0))
      (fun _ => true) (fun _ => 1) 0 :=
    fun _ _ _ => ⟨Ineq.contra, [Ineq.contra], CuttingPlanes.IsProof.nil.hyp contra_mem_cero, by simp, by simp,
      by simp, fun τ _ => Ineq.not_holds_contra τ⟩
  obtain ⟨C, -, hC⟩ := existe_separador_traza (t := 2) (by omega) (ordenCC_inj 0 1 0) (ordenCC_lt 0 1 0)
    (certificaSem_de_cp hcert) le_rfl (by simp) (by simp)
  exact ⟨C, hC⟩

/-- **Las hipótesis de `cota_traza` se cumplen a la vez**, con el detector de propagación `detCNF` (certificado con
una línea y coeficientes `1`), en cualquier `j ≥ 10`: `n = 2^(4j)`, `k = 2^(2j) + 1`, `r = 2^(2j)` y `b = 8j + 3`.
La cota que sale es `2^(2^j/2) < (P+1) · 2^(4(8j+4)²+1)`, con `P` el peso de la búsqueda. Para `j < 18` el segundo
factor ya basta y la cota no dice nada de `P`. Desde `j ≥ 18` sí: `P + 1 > 2^(2^j/2 − 4(8j+4)² − 1)`, que crece
como `2^(Ω(n^{1/4}))`. -/
theorem cota_detCNF (j : ℕ) (hj : 10 ≤ j) :
    2 ^ (2 ^ j / 2) <
      (peso (solCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel (ordenCC _ _ _)))
        (detCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel (ordenCC _ _ _)))
        (costoCP (detCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel
          (ordenCC _ _ _))) fun _ => 1)
        (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j)))) [] + 1) *
      2 ^ (4 * (8 * j + 3 + 1) ^ 2 + 1) := by
  have hN40 : 2 ^ 40 ≤ 2 ^ (4 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : (2 ^ (4 * j)).sqrt = 2 ^ (2 * j) := sqrt_dos_pow_cuatro j
  have hb : 2 * (max 1 1 + 1) * (2 ^ (4 * j)) ^ 2 + 1 ≤ 2 ^ (8 * j + 3) := by
    have : (2 ^ (4 * j)) ^ 2 = 2 ^ (8 * j) := by rw [← pow_mul]; ring_nf
    rw [this, pow_add]; have := Nat.one_le_two_pow (n := 8 * j); simp; omega
  have h := cota_traza (k := 2 ^ (2 * j) + 1) (r := 2 ^ (2 * j)) hN40 (by rw [hsq]; omega) (by rw [hsq]; omega)
    rfl (ordenCC_inj _ _ _) (ordenCC_lt _ _ _)
    (certificaSem_de_cp (certificaCP_detCNF _ (ordenCC_inj _ _ _) _)) hb
  rwa [hsq, sqrt_dos_pow_dos] at h

/-- El exponente de `cota_detCNF` no es vacío: en `j = 18`, `2^j/2` le gana a `4(8j+4)² + 1`. -/
example : 4 * (8 * 18 + 3 + 1) ^ 2 + 1 < 2 ^ 18 / 2 := by decide

/-- **Las premisas de `cp_sin_demora_log` se cumplen en el `j` que da.** Con `e = 0`, `K = 1`, el orden `ordenCC`,
el detector `detCNF` y `c = 1`, el corolario concluye: `detCNF` no tiene demora `a · log₂(N+1) + b`. -/
example (a b : ℕ) : ∃ j, ¬ DemoraN
    (solCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel (ordenCC _ _ _)))
    (detCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel (ordenCC _ _ _)))
    (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))))
    (a * Nat.log 2 (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) + 1) + b) := by
  obtain ⟨j, hj⟩ := cp_sin_demora_log a b 0 1
  refine ⟨j, hj _ (ordenCC_inj _ _ _) (ordenCC_lt _ _ _) _ (fun _ => 1) ?_ (fun _ => by simp)⟩
  simpa using certificaCP_detCNF _ (ordenCC_inj _ _ _) _

/-- Un detector certificado por resolución también entra: `detCNF` vía `CertificaRes` (`certificaRes_detCNF`). -/
example (j : ℕ) :
    CertificaSem (CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))) (ordenCC _ _ _)
      (Fintype.card (VarsCC (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))))
      (detCNF ((CNF.cliqueColoring (2 ^ (4 * j)) (2 ^ (2 * j) + 1) (2 ^ (2 * j))).relabel (ordenCC _ _ _)))
      (fun _ => 1) 1 :=
  certificaSem_de_res (ordenCC_inj _ _ _) (certificaRes_detCNF _ _)

end Controles

/- Mutantes probados (rompen la compilación, como debe ser):
1. Costo `1` en vez de `2` en los nodos donde `det` no dispara (`costoCP`): rompe `traza_debajo` (la hoja completa
   tiene dos líneas: la cláusula y «no sigue»).
2. Pedir `1 ≤ t` en vez de `2 ≤ t` en `existe_separador_traza`: rompe la cota de comunicación de «no sigue».
3. Reglas sin el tope de dos premisas (`reglas`).
4. Un bit, en vez de dos, para decidir «no sigue».
5. `M₀ = 0` en la búsqueda de la línea falsa.
6. La cota de `cota_traza` sin el `/2` del exponente.
7. Quitar la cota de `M` en `sem_sin_demora_log`.
8. `n · r` en vez de `k · n` en `ht₂` de `existe_separador_traza`.
9. `CertificaSem` sin pedir `Linea.fuera p ∈ ls`.
-/


end DetectorPlanosDeCorte
end Tiempo
end Sagitta.Map
