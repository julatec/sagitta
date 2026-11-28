import Sagitta.Map.Teoria
import Mathlib.ModelTheory.Complexity

/-!
# Un cálculo de secuentes para S¹₂, con PIND como regla

El teorema de Buss (lo `Σᵇ₁`-definible en S¹₂ es polinomial) se prueba sobre **demostraciones**: de una prueba libre de
cortes libres se extrae un algoritmo (Buss, *Bounded Arithmetic*, 1986, cap. 4; *Handbook of Proof Theory*, 1998, cap. II,
§3). Para eso hace falta un cálculo donde la inducción sea una **regla**, no un axioma: un axioma de inducción, al negarse
en el secuente, trae un `∃x` no acotado, y el lema del testigo pide que toda fórmula de la prueba sea `Σᵇ₁`. Es lo que
no trae Foundation, cuyo Hauptsatz es el de la lógica pura.

Este archivo escribe ese cálculo sobre el lenguaje `L` de `Acotada.lean` (el de Mathlib):

* **Secuentes** `Γ ⇒ Δ`: dos listas de fórmulas con variables libres en `ℕ` (`L.Formula ℕ`).
* **Iniciales**: `φ ⇒ φ`; `⇒ φ` para cada instancia **sin cuantificadores** de un axioma BASIC (Buss: los BASIC son
  abiertos); la igualdad (`⇒ t = t` y `s = t, A(s) ⇒ A(t)`).
* **Estructurales**: debilitamiento por **encaje** (`Encaja Γ Γ'`, una función entre posiciones; da también contracción
  e intercambio) y corte. Las posiciones son datos (`Pos`), no la proposición `φ ∈ Γ`: así una función puede seguir
  cada fórmula de arriba abajo, que es lo que piden el lema del testigo y los cortes anclados.
* **Lógicas**: las de `⊥`, `→` y `∀`, que son las primitivas de Mathlib (`∧`, `∨`, `¬`, `∃` se definen a partir de ellas,
  así que sus reglas se derivan).
* **PIND** (Buss 1998, §2.4): de `Γ, A(⌊a/2⌋) ⇒ A(a), Δ` sale `Γ, A(0) ⇒ A(t), Δ`, con `A` en `Σᵇ₁` y la variable
  propia `a` fuera de `Γ`, `Δ` y los parámetros.

Las derivaciones son **datos** (`Deriva Γ Δ : Type`), como en Foundation: el lema del testigo se prueba por recursión
sobre ellas. Probado aquí:

* la **corrección** (`correcta`): todo secuente derivable vale en todo modelo de S¹₂;
* las **ocurrencias ancladas** (`anclAnt`, `anclSuc`) y los **cortes libres** (`sinCortesLibres`), con la definición
  de Buss (*Handbook*, cap. I, §2.4.4.1 y §2.4.6), y que **toda ocurrencia anclada es `Σᵇ₁`** (`sigma1_de_ancl`), así
  que en una derivación libre de cortes libres **toda fórmula de corte es `Σᵇ₁`** (`formulasDeCorte_sigma1`). Para eso,
  que la sustitución no saca a una fórmula de `Σᵇ₁` ni de `Πᵇ₁` (`EsSigma1.subst`), que Mathlib no trae.

Abierto, con nombre: `EliminacionDeCortesLibres` (el teorema de Buss). Y una advertencia para el paso siguiente: el
corolario que usa el lema del testigo es más fuerte que `formulasDeCorte_sigma1` (que **toda** fórmula de la prueba sea
`Σᵇ₁`), y sale de la propiedad de la subfórmula. Con las primitivas de Mathlib no sale: `∃ x ≤ t` es `¬∀x¬(x ≤ t ∧ φ)`,
y su subfórmula `∀x¬(x ≤ t ∧ φ)` no está en ninguna clase acotada. Buss usa reglas propias para los cuantificadores
acotados; el piloto `Testigo.lean` los trae como sintaxis primitiva.
-/

open FirstOrder FirstOrder.Language

namespace Sagitta.Map
namespace Acotada

noncomputable section

/-! ## Instanciar y llenar -/

/-- `ψ[t]`: el cuerpo de un `∀` con la variable ligada cambiada por `t`. -/
def instanciar (ψ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) : L.Formula ℕ :=
  ψ.toFormula.subst (Sum.elim Term.var (fun _ => t))

/-- `A(t, p⃗)`: una fórmula con la variable 0 (la de inducción) cambiada por `t` y la `i + 1` por el parámetro `ps i`.
Es la forma de `EsModeloS12.pind`. -/
def llenar {k : ℕ} (A : L.Formula (Fin (k + 1))) (ps : Fin k → L.Term ℕ) (t : L.Term ℕ) : L.Formula ℕ :=
  A.subst (Fin.cons (α := fun _ => L.Term ℕ) t ps)

/-- `φ'` sale de `φ` cambiando los `∀` del frente por términos, uno por uno. -/
inductive EsInstancia : L.Formula ℕ → L.Formula ℕ → Prop
  | refl (φ : L.Formula ℕ) : EsInstancia φ φ
  | todo (ψ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) {φ : L.Formula ℕ} :
      EsInstancia (instanciar ψ t) φ → EsInstancia (BoundedFormula.all ψ) φ

/-! ## Contextos: posiciones como dato

El lema del testigo es una **función** que recorre la derivación y lleva testigos de arriba abajo. Para eso, cada
regla tiene que decir **dónde** fue a parar cada fórmula, no solo que está. `φ ∈ Γ` es una proposición y Lean no deja
sacar de ella un dato (la posición): fue la lección del piloto `Testigo.lean`, que por eso indexa los contextos con
tipos inductivos. Aquí la posición es un tipo inductivo, `Pos φ Γ` (`aqui`/`alla`), y el debilitamiento lleva una
función entre posiciones (`Encaja`). Con eso vienen gratis la contracción (dos posiciones a la misma) y el intercambio,
y se puede seguir cada ocurrencia de una fórmula hacia abajo, que es lo que piden los cortes anclados. -/

/-- **Una posición de `a` en la lista `l`**, como dato: la primera (`aqui`) o una de las de la cola (`alla`). -/
inductive Pos {α : Type} : α → List α → Type
  | aqui {a : α} {l : List α} : Pos a (a :: l)
  | alla {a b : α} {l : List α} : Pos a l → Pos a (b :: l)

namespace Pos

variable {α : Type} {a : α} {l : List α}

/-- El número de la posición, contando desde 0. -/
def idx : {l : List α} → Pos a l → ℕ
  | _, .aqui => 0
  | _, .alla p => p.idx + 1

theorem mem : {l : List α} → Pos a l → a ∈ l
  | _, .aqui => List.mem_cons_self
  | _, .alla p => List.mem_cons_of_mem _ p.mem

/-- En la posición `p` está `a`. -/
theorem getElem? : {l : List α} → (p : Pos a l) → l[p.idx]? = some a
  | _, .aqui => rfl
  | _, .alla p => by simp only [idx, List.getElem?_cons_succ]; exact p.getElem?

theorem existe : {l : List α} → a ∈ l → Nonempty (Pos a l)
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨.aqui⟩
    · obtain ⟨p⟩ := existe h; exact ⟨.alla p⟩

/-- De `a ∈ l`, una posición, **por elección**: sirve para escribir derivaciones, no para extraer de ellas. -/
noncomputable def deMem (h : a ∈ l) : Pos a l := Classical.choice (existe h)

end Pos

/-- **`Γ` encaja en `Γ'`**: a cada posición de `Γ`, una de `Γ'` con la misma fórmula. Es el dato del debilitamiento.
No tiene que ser inyectiva (contracción) ni monótona (intercambio). -/
abbrev Encaja {α : Type} (Γ Γ' : List α) : Type := ∀ a, Pos a Γ → Pos a Γ'

namespace Encaja

variable {α : Type} {a b : α} {Γ Γ' : List α}

def refl : Encaja Γ Γ := fun _ p => p

/-- Debilitar: agregar `b` al frente. -/
def cola : Encaja Γ (b :: Γ) := fun _ p => .alla p

/-- Dejar la cabeza en su lugar. -/
def cons (e : Encaja Γ Γ') : Encaja (b :: Γ) (b :: Γ') := fun _ p =>
  match p with
  | .aqui => .aqui
  | .alla q => .alla (e _ q)

/-- Contraer las dos primeras, que son la misma. -/
def contr : Encaja (b :: b :: Γ) (b :: Γ) := fun _ p =>
  match p with
  | .aqui => .aqui
  | .alla .aqui => .aqui
  | .alla (.alla q) => .alla q

/-- Intercambiar las dos primeras. -/
def camb : Encaja (a :: b :: Γ) (b :: a :: Γ) := fun _ p =>
  match p with
  | .aqui => .alla .aqui
  | .alla .aqui => .aqui
  | .alla (.alla q) => .alla (.alla q)

theorem sub (e : Encaja Γ Γ') : Γ ⊆ Γ' := fun _ h => (e _ (Pos.deMem h)).mem

/-- De una inclusión, un encaje, **por elección** (como `Pos.deMem`). -/
noncomputable def deSub (h : Γ ⊆ Γ') : Encaja Γ Γ' := fun _ p => Pos.deMem (h p.mem)

/-- Lo que se le asigna a cada posición de `Γ'` da algo para cada posición de `Γ`: así bajan los testigos del
antecedente por un debilitamiento, sin elegir nada. -/
def tirar {P : α → Type} (e : Encaja Γ Γ') (w : ∀ a, Pos a Γ' → P a) : ∀ a, Pos a Γ → P a :=
  fun a p => w a (e a p)

/-- Y un testigo de alguna fórmula de `Γ` lo es de una de `Γ'`: así sube el del sucedente. -/
def empujar {P : α → Type} (e : Encaja Γ Γ') : (Σ a, Pos a Γ × P a) → Σ a, Pos a Γ' × P a :=
  fun ⟨a, p, x⟩ => ⟨a, e a p, x⟩

end Encaja

/-! ## El cálculo -/

/-- **Las derivaciones de S¹₂ con PIND como regla.** `Deriva Γ Δ` es el tipo de las pruebas de `Γ ⇒ Δ`. -/
inductive Deriva : List (L.Formula ℕ) → List (L.Formula ℕ) → Type
  /-- `φ ⇒ φ`. -/
  | ax (φ : L.Formula ℕ) : Deriva [φ] [φ]
  /-- `⇒ φ`, para `φ` una instancia sin cuantificadores de un axioma BASIC. -/
  | basic {σ : L.Sentence} (hσ : σ ∈ teoriaBASIC) {φ : L.Formula ℕ}
      (hi : EsInstancia (σ.relabel Empty.elim) φ) (hq : φ.IsQF) : Deriva [] [φ]
  /-- `⇒ t = t`. -/
  | igualRefl (t : L.Term ℕ) : Deriva [] [Term.equal t t]
  /-- `s = t, A(s) ⇒ A(t)`, con `A` **atómica** (como en LKe, Buss 1998, cap. I: la sustitución en una fórmula
  cualquiera se deriva de esta). -/
  | igualSust {k : ℕ} (A : L.Formula (Fin (k + 1))) (hA : A.IsAtomic) (ps : Fin k → L.Term ℕ) (s t : L.Term ℕ) :
      Deriva [Term.equal s t, llenar A ps s] [llenar A ps t]
  /-- Debilitamiento, con contracción e intercambio: cada fórmula de arriba va a una posición de abajo. -/
  | debil {Γ Δ Γ' Δ' : List (L.Formula ℕ)} : Deriva Γ Δ → Encaja Γ Γ' → Encaja Δ Δ' → Deriva Γ' Δ'
  /-- Corte. -/
  | corte {Γ Δ : List (L.Formula ℕ)} (φ : L.Formula ℕ) :
      Deriva Γ (φ :: Δ) → Deriva (φ :: Γ) Δ → Deriva Γ Δ
  /-- `⊥ ⇒`. -/
  | falso : Deriva [BoundedFormula.falsum] []
  /-- `→` a la izquierda. -/
  | impIzq {Γ Δ : List (L.Formula ℕ)} {φ ψ : L.Formula ℕ} :
      Deriva Γ (φ :: Δ) → Deriva (ψ :: Γ) Δ → Deriva (φ.imp ψ :: Γ) Δ
  /-- `→` a la derecha. -/
  | impDer {Γ Δ : List (L.Formula ℕ)} {φ ψ : L.Formula ℕ} :
      Deriva (φ :: Γ) (ψ :: Δ) → Deriva Γ (φ.imp ψ :: Δ)
  /-- `∀` a la izquierda: vale para todos, vale para `t`. -/
  | todoIzq {Γ Δ : List (L.Formula ℕ)} (ψ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) :
      Deriva (instanciar ψ t :: Γ) Δ → Deriva (BoundedFormula.all ψ :: Γ) Δ
  /-- `∀` a la derecha, con la variable propia `a` fuera de todo lo demás. -/
  | todoDer {Γ Δ : List (L.Formula ℕ)} (ψ : L.BoundedFormula ℕ 1) (a : ℕ) (hψ : a ∉ ψ.freeVarFinset)
      (hΓ : ∀ φ ∈ Γ, a ∉ φ.freeVarFinset) (hΔ : ∀ φ ∈ Δ, a ∉ φ.freeVarFinset) :
      Deriva Γ (instanciar ψ (Term.var a) :: Δ) → Deriva Γ (BoundedFormula.all ψ :: Δ)
  /-- **PIND** para `A` en `Σᵇ₁`: de `Γ, A(⌊a/2⌋) ⇒ A(a), Δ` sale `Γ, A(0) ⇒ A(t), Δ`, con `a` fuera de `Γ`, `Δ` y
  los parámetros `ps`. -/
  | pind {Γ Δ : List (L.Formula ℕ)} {k : ℕ} (A : L.Formula (Fin (k + 1))) (hA : EsSigma1 A)
      (ps : Fin k → L.Term ℕ) (a : ℕ) (t : L.Term ℕ) (hps : ∀ i, a ∉ (ps i).varFinset)
      (hΓ : ∀ φ ∈ Γ, a ∉ φ.freeVarFinset) (hΔ : ∀ φ ∈ Δ, a ∉ φ.freeVarFinset) :
      Deriva (llenar A ps (tMt (Term.var a)) :: Γ) (llenar A ps (Term.var a) :: Δ) →
      Deriva (llenar A ps tC :: Γ) (llenar A ps t :: Δ)

/-- **Sin cortes**: la derivación no usa la regla de corte. -/
def Deriva.sinCortes : {Γ Δ : List (L.Formula ℕ)} → Deriva Γ Δ → Prop
  | _, _, .ax _ => True
  | _, _, .basic _ _ _ => True
  | _, _, .igualRefl _ => True
  | _, _, .igualSust _ _ _ _ _ => True
  | _, _, .debil d _ _ => d.sinCortes
  | _, _, .corte _ _ _ => False
  | _, _, .falso => True
  | _, _, .impIzq d e => d.sinCortes ∧ e.sinCortes
  | _, _, .impDer d => d.sinCortes
  | _, _, .todoIzq _ _ d => d.sinCortes
  | _, _, .todoDer _ _ _ _ _ d => d.sinCortes
  | _, _, .pind _ _ _ _ _ _ _ _ d => d.sinCortes

/-- **La altura** de una derivación. -/
def Deriva.altura : {Γ Δ : List (L.Formula ℕ)} → Deriva Γ Δ → ℕ
  | _, _, .ax _ => 0
  | _, _, .basic _ _ _ => 0
  | _, _, .igualRefl _ => 0
  | _, _, .igualSust _ _ _ _ _ => 0
  | _, _, .debil d _ _ => d.altura + 1
  | _, _, .corte _ d e => max d.altura e.altura + 1
  | _, _, .falso => 0
  | _, _, .impIzq d e => max d.altura e.altura + 1
  | _, _, .impDer d => d.altura + 1
  | _, _, .todoIzq _ _ d => d.altura + 1
  | _, _, .todoDer _ _ _ _ _ d => d.altura + 1
  | _, _, .pind _ _ _ _ _ _ _ _ d => d.altura + 1

/-! ## Ocurrencias ancladas y cortes libres

Buss, «An Introduction to Proof Theory» (*Handbook of Proof Theory*, 1998, cap. I): el **descendiente inmediato** de
una fórmula lateral es la misma fórmula en el mismo lugar del secuente de abajo; el de una auxiliar es la principal; las
fórmulas de corte no tienen (§1.2.3, p. 12). Un descendiente es **directo** si es la misma fórmula. Una ocurrencia está
**anclada** si es descendiente directo de una fórmula de un inicial no lógico o de una **principal de una inducción**
(`A(0)` y `A(t)` de PIND) (§2.4.4.1, p. 43, y §2.4.6, p. 46). Un corte es **anclado** si (i) la fórmula de corte no es
atómica y **al menos una** de sus dos ocurrencias arriba está anclada, o (ii) es atómica y lo están **las dos**; si no,
es **libre** (§2.4.4.1).

Aquí los iniciales no lógicos son los de BASIC y los de la igualdad (Buss pone los de la igualdad como el ejemplo de
conjunto de iniciales, p. 42). Una regla lógica nunca hace descendiente directo: su principal es más larga que sus
auxiliares (`φ → ψ` contra `φ`, `∀ψ` contra `ψ[t]`). Las ocurrencias se nombran por su número en la lista
(`Pos.idx`); el debilitamiento las lleva por su encaje, y lo que agrega no tiene antepasado. -/

/-- **La ocurrencia número `j` del antecedente está anclada.** -/
def Deriva.anclAnt : {Γ Δ : List (L.Formula ℕ)} → Deriva Γ Δ → ℕ → Prop
  | _, _, .ax _, _ => False
  | _, _, .basic _ _ _, _ => False
  | _, _, .igualRefl _, _ => False
  | _, _, .igualSust _ _ _ _ _, j => j = 0 ∨ j = 1
  | _, _, .debil (Γ := Γ) d eΓ _, j => ∃ (ψ : L.Formula ℕ) (i : Pos ψ Γ), (eΓ ψ i).idx = j ∧ d.anclAnt i.idx
  | _, _, .corte _ d e, j => d.anclAnt j ∨ e.anclAnt (j + 1)
  | _, _, .falso, _ => False
  | _, _, .impIzq _ _, 0 => False
  | _, _, .impIzq d e, j + 1 => d.anclAnt j ∨ e.anclAnt (j + 1)
  | _, _, .impDer d, j => d.anclAnt (j + 1)
  | _, _, .todoIzq _ _ _, 0 => False
  | _, _, .todoIzq _ _ d, j + 1 => d.anclAnt (j + 1)
  | _, _, .todoDer _ _ _ _ _ d, j => d.anclAnt j
  | _, _, .pind _ _ _ _ _ _ _ _ _, 0 => True
  | _, _, .pind _ _ _ _ _ _ _ _ d, j + 1 => d.anclAnt (j + 1)

/-- **La ocurrencia número `j` del sucedente está anclada.** -/
def Deriva.anclSuc : {Γ Δ : List (L.Formula ℕ)} → Deriva Γ Δ → ℕ → Prop
  | _, _, .ax _, _ => False
  | _, _, .basic _ _ _, j => j = 0
  | _, _, .igualRefl _, j => j = 0
  | _, _, .igualSust _ _ _ _ _, j => j = 0
  | _, _, .debil (Δ := Δ) d _ eΔ, j => ∃ (ψ : L.Formula ℕ) (i : Pos ψ Δ), (eΔ ψ i).idx = j ∧ d.anclSuc i.idx
  | _, _, .corte _ d e, j => d.anclSuc (j + 1) ∨ e.anclSuc j
  | _, _, .falso, _ => False
  | _, _, .impIzq d e, j => d.anclSuc (j + 1) ∨ e.anclSuc j
  | _, _, .impDer _, 0 => False
  | _, _, .impDer d, j + 1 => d.anclSuc (j + 1)
  | _, _, .todoIzq _ _ d, j => d.anclSuc j
  | _, _, .todoDer _ _ _ _ _ _, 0 => False
  | _, _, .todoDer _ _ _ _ _ d, j + 1 => d.anclSuc (j + 1)
  | _, _, .pind _ _ _ _ _ _ _ _ _, 0 => True
  | _, _, .pind _ _ _ _ _ _ _ _ d, j + 1 => d.anclSuc (j + 1)

/-- **Libre de cortes libres** (*free-cut free*, Buss §2.4.4.1): todo corte de la derivación está anclado. -/
def Deriva.sinCortesLibres : {Γ Δ : List (L.Formula ℕ)} → Deriva Γ Δ → Prop
  | _, _, .ax _ => True
  | _, _, .basic _ _ _ => True
  | _, _, .igualRefl _ => True
  | _, _, .igualSust _ _ _ _ _ => True
  | _, _, .debil d _ _ => d.sinCortesLibres
  | _, _, .corte φ d e =>
      (φ.IsAtomic → d.anclSuc 0 ∧ e.anclAnt 0) ∧ (¬ φ.IsAtomic → d.anclSuc 0 ∨ e.anclAnt 0) ∧
        d.sinCortesLibres ∧ e.sinCortesLibres
  | _, _, .falso => True
  | _, _, .impIzq d e => d.sinCortesLibres ∧ e.sinCortesLibres
  | _, _, .impDer d => d.sinCortesLibres
  | _, _, .todoIzq _ _ d => d.sinCortesLibres
  | _, _, .todoDer _ _ _ _ _ d => d.sinCortesLibres
  | _, _, .pind _ _ _ _ _ _ _ _ d => d.sinCortesLibres

/-- **Las fórmulas de corte** de la derivación, de arriba abajo. -/
def Deriva.formulasDeCorte : {Γ Δ : List (L.Formula ℕ)} → Deriva Γ Δ → List (L.Formula ℕ)
  | _, _, .ax _ => []
  | _, _, .basic _ _ _ => []
  | _, _, .igualRefl _ => []
  | _, _, .igualSust _ _ _ _ _ => []
  | _, _, .debil d _ _ => d.formulasDeCorte
  | _, _, .corte φ d e => φ :: (d.formulasDeCorte ++ e.formulasDeCorte)
  | _, _, .falso => []
  | _, _, .impIzq d e => d.formulasDeCorte ++ e.formulasDeCorte
  | _, _, .impDer d => d.formulasDeCorte
  | _, _, .todoIzq _ _ d => d.formulasDeCorte
  | _, _, .todoDer _ _ _ _ _ d => d.formulasDeCorte
  | _, _, .pind _ _ _ _ _ _ _ _ d => d.formulasDeCorte

/-- Sin cortes, no hay cortes libres. -/
theorem Deriva.sinCortesLibres_de_sinCortes {Γ Δ : List (L.Formula ℕ)} (d : Deriva Γ Δ) (h : d.sinCortes) :
    d.sinCortesLibres := by
  induction d with
  | corte => exact h.elim
  | impIzq _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | debil _ _ _ ih => exact ih h
  | impDer _ ih => exact ih h
  | todoIzq _ _ _ ih => exact ih h
  | todoDer _ _ _ _ _ _ ih => exact ih h
  | pind _ _ _ _ _ _ _ _ _ ih => exact ih h
  | _ => trivial

/-! ## Corrección -/

/-- **`Γ ⇒ Δ` vale en `M` con la asignación `v`**: si todo `Γ` es verdadero, algo de `Δ` lo es. -/
def Vale (M : Type) [L.Structure M] (v : ℕ → M) (Γ Δ : List (L.Formula ℕ)) : Prop :=
  (∀ φ ∈ Γ, φ.Realize v) → ∃ ψ ∈ Δ, ψ.Realize v

variable {M : Type} [L.Structure M]

theorem realize_instanciar (ψ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) (v : ℕ → M) :
    (instanciar ψ t).Realize v ↔ ψ.Realize v (fun _ => t.realize v) := by
  rw [instanciar, formula_realize_subst, BoundedFormula.realize_toFormula]
  apply iff_of_eq; congr 1

theorem realize_todo (ψ : L.BoundedFormula ℕ 1) (v : ℕ → M) :
    Formula.Realize (BoundedFormula.all ψ) v ↔ ∀ x : M, ψ.Realize v (fun _ => x) := by
  rw [Formula.Realize, BoundedFormula.realize_all]
  refine forall_congr' fun x => iff_of_eq ?_
  congr 1

theorem realize_llenar {k : ℕ} (A : L.Formula (Fin (k + 1))) (ps : Fin k → L.Term ℕ) (t : L.Term ℕ) (v : ℕ → M) :
    (llenar A ps t).Realize v ↔ A.Realize (Fin.cons (t.realize v) (fun i => (ps i).realize v)) :=
  realize_subst_cons A t ps v

/-- Una fórmula solo depende de sus variables libres. -/
theorem realize_congr_libres {n : ℕ} {φ : L.BoundedFormula ℕ n} {v w : ℕ → M} {xs : Fin n → M}
    (h : ∀ a ∈ φ.freeVarFinset, v a = w a) : φ.Realize v xs ↔ φ.Realize w xs := by
  rw [← BoundedFormula.realize_restrictFreeVar (f := id) (v := fun a : φ.freeVarFinset => v a) v (fun _ => rfl),
    BoundedFormula.realize_restrictFreeVar (f := id) (v := fun a : φ.freeVarFinset => v a) w (fun a => h a a.2)]

/-- Un término solo depende de sus variables. -/
theorem realize_congr_term {t : L.Term ℕ} {v w : ℕ → M} (h : ∀ a ∈ t.varFinset, v a = w a) :
    t.realize v = t.realize w := by
  rw [← Term.realize_restrictVar (f := id) (v := fun a : t.varFinset => v a) v (fun _ => rfl),
    Term.realize_restrictVar (f := id) (v := fun a : t.varFinset => v a) w (fun a => h a a.2)]

/-- Cambiar el valor de una variable que no aparece no cambia nada. -/
theorem realize_update_fresca {φ : L.Formula ℕ} {a : ℕ} (ha : a ∉ φ.freeVarFinset) (v : ℕ → M) (x : M) :
    φ.Realize (Function.update v a x) ↔ φ.Realize v :=
  realize_congr_libres fun b hb => Function.update_of_ne (by rintro rfl; exact ha hb) x v

theorem realize_term_update_fresca {t : L.Term ℕ} {a : ℕ} (ha : a ∉ t.varFinset) (v : ℕ → M) (x : M) :
    t.realize (Function.update v a x) = t.realize v :=
  realize_congr_term fun b hb => Function.update_of_ne (by rintro rfl; exact ha hb) x v

/-- Lo que se instancia de algo verdadero en todo `v` es verdadero en todo `v`. -/
theorem EsInstancia.correcta {φ φ' : L.Formula ℕ} (h : EsInstancia φ φ') :
    (∀ v : ℕ → M, φ.Realize v) → ∀ v : ℕ → M, φ'.Realize v := by
  induction h with
  | refl => exact id
  | todo ψ t _ ih =>
    intro hall
    apply ih
    intro v
    rw [realize_instanciar]
    exact (realize_todo ψ v).1 (hall v) (t.realize v)

theorem realize_tMt (t : L.Term ℕ) (v : ℕ → M) : (tMt t).realize v = mitad (t.realize v) := by
  simp only [tMt, Term.realize_functions_apply₁]; rfl

/-- **Corrección**: todo secuente derivable vale en todo modelo de S¹₂, con toda asignación. -/
theorem Deriva.correcta {Γ Δ : List (L.Formula ℕ)} (d : Deriva Γ Δ) (hM : EsModeloS12 M) (v : ℕ → M) :
    Vale M v Γ Δ := by
  induction d generalizing v with
  | ax φ => intro h; exact ⟨φ, by simp, h φ (by simp)⟩
  | @basic σ hσ φ hi _ =>
    intro _
    refine ⟨φ, List.mem_singleton_self _, ?_⟩
    have hT : M ⊨ teoriaBASIC := (modelo_basic_iff M).2 hM.basic
    have hσM : Sentence.Realize M σ := Theory.realize_sentence_of_mem (M := M) teoriaBASIC hσ
    refine hi.correcta (fun w => ?_) v
    rw [Formula.realize_relabel]
    have : (w ∘ Empty.elim : Empty → M) = default := funext fun e => e.elim
    rw [this]; exact hσM
  | igualRefl t => intro _; exact ⟨_, List.mem_singleton_self _, by simp [Formula.realize_equal]⟩
  | igualSust A _ ps s t =>
    intro h
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have hst : s.realize v = t.realize v := by
      have := h (Term.equal s t) (by simp); simpa [Formula.realize_equal] using this
    have hs := h (llenar A ps s) (by simp)
    rw [realize_llenar] at hs ⊢
    rwa [← hst]
  | debil _ eΓ eΔ ih =>
    intro h
    obtain ⟨ψ, hψ, hr⟩ := ih v (fun φ hφ => h φ (eΓ.sub hφ))
    exact ⟨ψ, eΔ.sub hψ, hr⟩
  | @corte Γ Δ φ _ _ ih1 ih2 =>
    intro h
    obtain ⟨ψ, hψ, hr⟩ := ih1 v h
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact ih2 v (fun χ hχ => by
        rcases List.mem_cons.1 hχ with rfl | hχ
        · exact hr
        · exact h χ hχ)
    · exact ⟨ψ, hψ, hr⟩
  | falso =>
    intro h
    exact absurd (h _ (List.mem_singleton_self _)) (fun h' => h')
  | @impIzq Γ Δ φ ψ _ _ ih1 ih2 =>
    intro h
    have himp : (φ.imp ψ).Realize v := h _ List.mem_cons_self
    have hΓ : ∀ χ ∈ Γ, χ.Realize v := fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)
    obtain ⟨θ, hθ, hr⟩ := ih1 v hΓ
    rcases List.mem_cons.1 hθ with rfl | hθ
    · have hψ : ψ.Realize v := by
        simp only [Formula.Realize, BoundedFormula.realize_imp] at himp hr ⊢; exact himp hr
      exact ih2 v (fun χ hχ => by
        rcases List.mem_cons.1 hχ with rfl | hχ
        · exact hψ
        · exact hΓ χ hχ)
    · exact ⟨θ, hθ, hr⟩
  | @impDer Γ Δ φ ψ _ ih =>
    intro h
    by_cases hφ : φ.Realize v
    · obtain ⟨θ, hθ, hr⟩ := ih v (fun χ hχ => by
        rcases List.mem_cons.1 hχ with rfl | hχ
        · exact hφ
        · exact h χ hχ)
      rcases List.mem_cons.1 hθ with rfl | hθ
      · refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [Formula.Realize, BoundedFormula.realize_imp] at hr ⊢; exact fun _ => hr
      · exact ⟨θ, List.mem_cons_of_mem _ hθ, hr⟩
    · refine ⟨_, List.mem_cons_self, ?_⟩
      simp only [Formula.Realize, BoundedFormula.realize_imp] at hφ ⊢; exact fun h' => absurd h' hφ
  | @todoIzq Γ Δ ψ t _ ih =>
    intro h
    apply ih v
    intro χ hχ
    rcases List.mem_cons.1 hχ with rfl | hχ
    · rw [realize_instanciar]; exact (realize_todo ψ v).1 (h _ List.mem_cons_self) _
    · exact h χ (List.mem_cons_of_mem _ hχ)
  | @todoDer Γ Δ ψ a hψ hΓ hΔ _ ih =>
    intro h
    by_cases hD : ∃ θ ∈ Δ, Formula.Realize θ v
    · obtain ⟨θ, hθ, hr⟩ := hD; exact ⟨θ, List.mem_cons_of_mem _ hθ, hr⟩
    · refine ⟨_, List.mem_cons_self, (realize_todo ψ v).2 fun x => ?_⟩
      obtain ⟨θ, hθ, hr⟩ :=
        ih (Function.update v a x) (fun χ hχ => (realize_update_fresca (hΓ χ hχ) v x).2 (h χ hχ))
      rcases List.mem_cons.1 hθ with rfl | hθ
      · rw [realize_instanciar, Term.realize_var, Function.update_self] at hr
        exact (realize_congr_libres fun b hb => Function.update_of_ne (by rintro rfl; exact hψ hb) x v).1 hr
      · exact absurd ⟨θ, hθ, (realize_update_fresca (hΔ θ hθ) v x).1 hr⟩ hD
  | @pind Γ Δ k A hA ps a t hps hΓ hΔ _ ih =>
    intro h
    by_cases hD : ∃ θ ∈ Δ, Formula.Realize θ v
    · obtain ⟨θ, hθ, hr⟩ := hD; exact ⟨θ, List.mem_cons_of_mem _ hθ, hr⟩
    · refine ⟨_, List.mem_cons_self, ?_⟩
      let w : Fin k → M := fun i => (ps i).realize v
      have h0 : A.Realize (Fin.cons cero w) := by
        have := h _ List.mem_cons_self
        rwa [realize_llenar, realize_tC] at this
      have hpaso : ∀ x : M, A.Realize (Fin.cons (mitad x) w) → A.Realize (Fin.cons x w) := by
        intro x hx
        have hps' : (fun i => (ps i).realize (Function.update v a x)) = w :=
          funext fun i => realize_term_update_fresca (hps i) v x
        have hΓ' : ∀ χ ∈ llenar A ps (tMt (Term.var a)) :: Γ, χ.Realize (Function.update v a x) := by
          intro χ hχ
          rcases List.mem_cons.1 hχ with rfl | hχ
          · rw [realize_llenar, realize_tMt, Term.realize_var, Function.update_self, hps']; exact hx
          · exact (realize_update_fresca (hΓ χ hχ) v x).2 (h χ (List.mem_cons_of_mem _ hχ))
        obtain ⟨θ, hθ, hr⟩ := ih (Function.update v a x) hΓ'
        rcases List.mem_cons.1 hθ with rfl | hθ
        · rwa [realize_llenar, Term.realize_var, Function.update_self, hps'] at hr
        · exact absurd ⟨θ, hθ, (realize_update_fresca (hΔ θ hθ) v x).1 hr⟩ hD
      rw [realize_llenar]
      exact hM.pind k A hA w h0 hpaso (t.realize v)

/-- **Lo que el cálculo prueba sin hipótesis vale en todo modelo de S¹₂**; en particular, en ℕ. -/
theorem Deriva.verdadera {φ : L.Formula ℕ} (d : Deriva [] [φ]) (hM : EsModeloS12 M) (v : ℕ → M) : φ.Realize v := by
  obtain ⟨ψ, hψ, hr⟩ := d.correcta hM v (by simp)
  rw [List.mem_singleton] at hψ
  exact hψ ▸ hr


/-! ## Lo anclado es `Σᵇ₁`

Las fórmulas de los iniciales no lógicos son sin cuantificadores, y las principales de PIND son instancias de una
`Σᵇ₁`. Para lo segundo hace falta que **sustituir términos no saque a una fórmula de su clase**, que Mathlib no trae
para las clases de `Acotada.lean`. Se prueba para cualquier mapa de términos que respete la variable recién ligada,
`sube` y `|·|`; la sustitución es uno. -/

section Mapa

variable {α β : Type}

/-- Mapear los términos de una fórmula por `G`, sin tocar los cuantificadores. -/
abbrev mapa (G : ∀ n, L.Term (α ⊕ Fin n) → L.Term (β ⊕ Fin n)) {n : ℕ} (φ : L.BoundedFormula α n) :
    L.BoundedFormula β n :=
  φ.mapTermRel (g := id) G (fun _ => id) (fun _ => id)

/-- Un mapa de términos **respeta los cuantificadores acotados**. -/
structure EsMapaAcotado (G : ∀ n, L.Term (α ⊕ Fin n) → L.Term (β ⊕ Fin n)) : Prop where
  hn : ∀ n, G (n + 1) nueva = nueva
  hs : ∀ n (t : L.Term (α ⊕ Fin n)), G (n + 1) (sube t) = sube (G n t)
  hl : ∀ n (t : L.Term (α ⊕ Fin n)), G n (tLong t) = tLong (G n t)

variable (G : ∀ n, L.Term (α ⊕ Fin n) → L.Term (β ⊕ Fin n))

theorem mapa_leF {n : ℕ} (t u : L.Term (α ⊕ Fin n)) : mapa G (leF t u) = leF (G n t) (G n u) := by
  show BoundedFormula.rel _ _ = BoundedFormula.rel _ _
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

theorem mapa_inf {n : ℕ} (φ ψ : L.BoundedFormula α n) : mapa G (φ ⊓ ψ) = mapa G φ ⊓ mapa G ψ := rfl
theorem mapa_sup {n : ℕ} (φ ψ : L.BoundedFormula α n) : mapa G (φ ⊔ ψ) = mapa G φ ⊔ mapa G ψ := rfl
theorem mapa_not {n : ℕ} (φ : L.BoundedFormula α n) : mapa G φ.not = (mapa G φ).not := rfl
theorem mapa_imp {n : ℕ} (φ ψ : L.BoundedFormula α n) : mapa G (φ.imp ψ) = (mapa G φ).imp (mapa G ψ) := rfl

variable {G}

theorem mapa_paraTodo (h : EsMapaAcotado G) {n : ℕ} (t : L.Term (α ⊕ Fin n)) (φ : L.BoundedFormula α (n + 1)) :
    mapa G (paraTodoAcotado t φ) = paraTodoAcotado (G n t) (mapa G φ) := by
  show ((mapa G (leF nueva (sube t))).imp (mapa G φ)).all = _
  rw [mapa_leF, h.hn, h.hs]; rfl

theorem mapa_existe (h : EsMapaAcotado G) {n : ℕ} (t : L.Term (α ⊕ Fin n)) (φ : L.BoundedFormula α (n + 1)) :
    mapa G (existeAcotado t φ) = existeAcotado (G n t) (mapa G φ) := by
  show (mapa G (leF nueva (sube t)) ⊓ mapa G φ).ex = _
  rw [mapa_leF, h.hn, h.hs]; rfl

theorem EsAguda.mapa (h : EsMapaAcotado G) {n : ℕ} {φ : L.BoundedFormula α n} (hφ : EsAguda φ) :
    EsAguda (mapa G φ) := by
  induction hφ with
  | falso => exact .falso
  | igual t u => exact .igual _ _
  | rel R ts => exact .rel _ _
  | imp _ _ ih1 ih2 => rw [mapa_imp]; exact .imp ih1 ih2
  | todoAgudo t _ ih => rw [mapa_paraTodo h, h.hl]; exact .todoAgudo _ ih
  | existeAgudo t _ ih => rw [mapa_existe h, h.hl]; exact .existeAgudo _ ih

mutual

theorem EsSigma1.mapa (h : EsMapaAcotado G) : ∀ {n : ℕ} {φ : L.BoundedFormula α n},
    EsSigma1 φ → EsSigma1 (mapa G φ)
  | _, _, .aguda hφ => .aguda (hφ.mapa h)
  | _, _, .existe t hφ => by rw [mapa_existe h]; exact .existe _ (EsSigma1.mapa h hφ)
  | _, _, .todoAgudo t hφ => by rw [mapa_paraTodo h, h.hl]; exact .todoAgudo _ (EsSigma1.mapa h hφ)
  | _, _, .y h1 h2 => by rw [mapa_inf]; exact .y (EsSigma1.mapa h h1) (EsSigma1.mapa h h2)
  | _, _, .o h1 h2 => by rw [mapa_sup]; exact .o (EsSigma1.mapa h h1) (EsSigma1.mapa h h2)
  | _, _, .no hφ => by rw [mapa_not]; exact .no (EsPi1.mapa h hφ)
  | _, _, .imp h1 h2 => by rw [mapa_imp]; exact .imp (EsPi1.mapa h h1) (EsSigma1.mapa h h2)

theorem EsPi1.mapa (h : EsMapaAcotado G) : ∀ {n : ℕ} {φ : L.BoundedFormula α n},
    EsPi1 φ → EsPi1 (mapa G φ)
  | _, _, .aguda hφ => .aguda (hφ.mapa h)
  | _, _, .todo t hφ => by rw [mapa_paraTodo h]; exact .todo _ (EsPi1.mapa h hφ)
  | _, _, .existeAgudo t hφ => by rw [mapa_existe h, h.hl]; exact .existeAgudo _ (EsPi1.mapa h hφ)
  | _, _, .y h1 h2 => by rw [mapa_inf]; exact .y (EsPi1.mapa h h1) (EsPi1.mapa h h2)
  | _, _, .o h1 h2 => by rw [mapa_sup]; exact .o (EsPi1.mapa h h1) (EsPi1.mapa h h2)
  | _, _, .no hφ => by rw [mapa_not]; exact .no (EsSigma1.mapa h hφ)
  | _, _, .imp h1 h2 => by rw [mapa_imp]; exact .imp (EsSigma1.mapa h h1) (EsPi1.mapa h h2)

end

/-- **La sustitución respeta los cuantificadores acotados.** -/
theorem esMapaAcotado_subst (f : α → L.Term β) :
    EsMapaAcotado (fun n (t : L.Term (α ⊕ Fin n)) => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))) where
  hn _ := rfl
  hs n t := by
    induction t with
    | var a =>
      rcases a with a | i
      · simp only [sube, Term.relabel, Sum.map_inl, id, Term.subst, Sum.elim_inl, Function.comp,
          Term.relabel_relabel]
        rfl
      · rfl
    | func g ts ih => simp only [sube, Term.relabel, Term.subst] at ih ⊢; congr 1; funext i; exact ih i
  hl _ t := by
    show Term.func _ _ = Term.func _ _
    congr 1; funext i; match i with | 0 => rfl

/-- **Sustituir en una `Σᵇ₁` da una `Σᵇ₁`.** -/
theorem EsSigma1.subst {n : ℕ} {φ : L.BoundedFormula α n} (hφ : EsSigma1 φ) (f : α → L.Term β) :
    EsSigma1 (φ.subst f) :=
  hφ.mapa (esMapaAcotado_subst f)

theorem EsAguda.de_atomica {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : EsAguda φ := by
  cases h with
  | equal => exact .igual _ _
  | rel => exact .rel _ _

/-- **Lo que no tiene cuantificadores es agudo.** -/
theorem EsAguda.de_QF {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) : EsAguda φ := by
  induction h with
  | falsum => exact .falso
  | of_isAtomic h => exact .de_atomica h
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2

end Mapa

theorem esSigma1_llenar {k : ℕ} {A : L.Formula (Fin (k + 1))} (hA : EsSigma1 A) (ps : Fin k → L.Term ℕ)
    (t : L.Term ℕ) : EsSigma1 (llenar A ps t) :=
  hA.subst _

/-- **Toda ocurrencia anclada es `Σᵇ₁`**, en el antecedente y en el sucedente. -/
theorem Deriva.sigma1_de_ancl {Γ Δ : List (L.Formula ℕ)} (d : Deriva Γ Δ) :
    (∀ j, d.anclAnt j → ∀ φ, Γ[j]? = some φ → EsSigma1 φ) ∧
      (∀ j, d.anclSuc j → ∀ φ, Δ[j]? = some φ → EsSigma1 φ) := by
  induction d with
  | ax φ => exact ⟨fun _ h => by simp [Deriva.anclAnt] at h, fun _ h => by simp [Deriva.anclSuc] at h⟩
  | @basic σ hσ φ hi hq =>
    refine ⟨fun _ h => by simp [Deriva.anclAnt] at h, fun j h ψ hψ => ?_⟩
    simp only [Deriva.anclSuc] at h; subst h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hψ; subst hψ
    exact .aguda (.de_QF hq)
  | igualRefl t =>
    refine ⟨fun _ h => by simp [Deriva.anclAnt] at h, fun j h ψ hψ => ?_⟩
    simp only [Deriva.anclSuc] at h; subst h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hψ; subst hψ
    exact .aguda (.igual _ _)
  | igualSust A hA ps s t =>
    have hA' : EsSigma1 A := .aguda (.de_atomica hA)
    refine ⟨fun j h ψ hψ => ?_, fun j h ψ hψ => ?_⟩
    · simp only [Deriva.anclAnt] at h
      rcases h with rfl | rfl
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hψ; subst hψ; exact .aguda (.igual _ _)
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hψ; subst hψ
        exact esSigma1_llenar hA' ps s
    · simp only [Deriva.anclSuc] at h; subst h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hψ; subst hψ
      exact esSigma1_llenar hA' ps t
  | debil d eΓ eΔ ih =>
    refine ⟨fun j h φ hφ => ?_, fun j h φ hφ => ?_⟩
    · obtain ⟨ψ, i, rfl, hi⟩ := h
      rw [(eΓ ψ i).getElem?, Option.some.injEq] at hφ; subst hφ
      exact ih.1 _ hi ψ i.getElem?
    · obtain ⟨ψ, i, rfl, hi⟩ := h
      rw [(eΔ ψ i).getElem?, Option.some.injEq] at hφ; subst hφ
      exact ih.2 _ hi ψ i.getElem?
  | corte φ d e ih1 ih2 =>
    refine ⟨fun j h ψ hψ => ?_, fun j h ψ hψ => ?_⟩
    · rcases h with h | h
      · exact ih1.1 j h ψ hψ
      · exact ih2.1 (j + 1) h ψ (by simpa using hψ)
    · rcases h with h | h
      · exact ih1.2 (j + 1) h ψ (by simpa using hψ)
      · exact ih2.2 j h ψ hψ
  | falso => exact ⟨fun _ h => by simp [Deriva.anclAnt] at h, fun _ h => by simp [Deriva.anclSuc] at h⟩
  | impIzq d e ih1 ih2 =>
    refine ⟨fun j h ψ hψ => ?_, fun j h ψ hψ => ?_⟩
    · rcases j with _ | j
      · simp [Deriva.anclAnt] at h
      · simp only [Deriva.anclAnt] at h
        simp only [List.getElem?_cons_succ] at hψ
        rcases h with h | h
        · exact ih1.1 j h ψ hψ
        · exact ih2.1 (j + 1) h ψ (by simpa using hψ)
    · rcases h with h | h
      · exact ih1.2 (j + 1) h ψ (by simpa using hψ)
      · exact ih2.2 j h ψ hψ
  | impDer d ih =>
    refine ⟨fun j h ψ hψ => ih.1 (j + 1) h ψ (by simpa using hψ), fun j h ψ hψ => ?_⟩
    rcases j with _ | j
    · simp [Deriva.anclSuc] at h
    · exact ih.2 (j + 1) h ψ (by simpa using hψ)
  | todoIzq ψ t d ih =>
    refine ⟨fun j h θ hθ => ?_, fun j h θ hθ => ih.2 j h θ hθ⟩
    rcases j with _ | j
    · simp [Deriva.anclAnt] at h
    · exact ih.1 (j + 1) h θ (by simpa using hθ)
  | todoDer ψ a _ _ _ d ih =>
    refine ⟨fun j h θ hθ => ih.1 j h θ hθ, fun j h θ hθ => ?_⟩
    rcases j with _ | j
    · simp [Deriva.anclSuc] at h
    · exact ih.2 (j + 1) h θ (by simpa using hθ)
  | pind A hA ps a t _ _ _ d ih =>
    refine ⟨fun j h θ hθ => ?_, fun j h θ hθ => ?_⟩
    · rcases j with _ | j
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hθ; subst hθ; exact esSigma1_llenar hA ps tC
      · exact ih.1 (j + 1) h θ (by simpa using hθ)
    · rcases j with _ | j
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hθ; subst hθ; exact esSigma1_llenar hA ps t
      · exact ih.2 (j + 1) h θ (by simpa using hθ)

/-- **En una derivación libre de cortes libres, toda fórmula de corte es `Σᵇ₁`.** Es lo que hace inofensivos a los
cortes que la eliminación de Buss deja: un corte anclado no atómico corta una fórmula que vino de un axioma o de una
inducción, y esas son `Σᵇ₁`; uno atómico es agudo de por sí. -/
theorem Deriva.formulasDeCorte_sigma1 {Γ Δ : List (L.Formula ℕ)} (d : Deriva Γ Δ) (h : d.sinCortesLibres) :
    ∀ φ ∈ d.formulasDeCorte, EsSigma1 φ := by
  induction d with
  | corte φ d e ih1 ih2 =>
    obtain ⟨_, hno, h1, h2⟩ := h
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · by_cases hat : ψ.IsAtomic
      · exact .aguda (.de_atomica hat)
      · rcases hno hat with h | h
        · exact d.sigma1_de_ancl.2 0 h ψ rfl
        · exact e.sigma1_de_ancl.1 0 h ψ rfl
    · rcases List.mem_append.1 hψ with hψ | hψ
      · exact ih1 h1 ψ hψ
      · exact ih2 h2 ψ hψ
  | impIzq d e ih1 ih2 =>
    intro ψ hψ
    rcases List.mem_append.1 hψ with hψ | hψ
    · exact ih1 h.1 ψ hψ
    · exact ih2 h.2 ψ hψ
  | debil _ _ _ ih => exact ih h
  | impDer _ ih => exact ih h
  | todoIzq _ _ _ ih => exact ih h
  | todoDer _ _ _ _ _ _ ih => exact ih h
  | pind _ _ _ _ _ _ _ _ _ ih => exact ih h
  | _ => intro _ hψ; simp [Deriva.formulasDeCorte] at hψ

/-- **Eliminación de cortes libres para S¹₂** (Buss 1998, cap. I, §2.4.6, p. 46; enunciada para PIND en la p. 45):
todo secuente derivable tiene una derivación libre de cortes libres. Es un teorema conocido; **abierto aquí**. -/
def EliminacionDeCortesLibres : Prop :=
  ∀ (Γ Δ : List (L.Formula ℕ)), Deriva Γ Δ → ∃ d : Deriva Γ Δ, d.sinCortesLibres


end

end Acotada
end Sagitta.Map
