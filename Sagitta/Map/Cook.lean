import Sagitta.Map.Clases

/-!
# El enunciado oficial: P versus NP como lo escribió Cook para el Clay

Transcripción del enunciado oficial del Clay Mathematics Institute: S. Cook, «The P versus NP Problem», en
*The Millennium Prize Problems* (Carlson, Jaffe y Wiles, eds., CMI y AMS, 2006), pp. 87–104, con la máquina de
Turing de su apéndice (pp. 101–102). Cada definición sigue el texto, en el mismo orden. Donde Lean obliga a
elegir una representación, el comentario dice cuál y por qué no cambia nada.

`Clases.lean` define P y NP de otra forma, la de formal-conjectures sobre las máquinas `TM2` de Mathlib. Al
final de este archivo están los dos puentes que harían falta para pasar de una a la otra, como proposiciones,
y se prueba que, si valen, las dos preguntas son la misma.

En Lean `Σ` es una palabra reservada; el alfabeto de entrada se llama `S`.
-/

namespace Sagitta.Map
namespace Cook

/-! ## El apéndice: la máquina de Turing -/

/-- El movimiento del cabezal: `izq` es −1 y `der` es 1. -/
inductive Mov
  | izq
  | der
  deriving DecidableEq, Repr

/-- Una máquina de Turing `⟨Σ, Γ, Q, δ⟩` con alfabeto de entrada `S`.

* `Γ` y `Q` son finitos y no vacíos; `S ⊆ Γ` va como una inyección, y el blanco `b` está en `Γ − S`.
* `Q` tiene tres estados especiales, `q₀`, `qaccept` y `qreject`.
* `δ : (Q − {qaccept, qreject}) × Γ → Q × Γ × {−1, 1}`.

Que `Q` y `Γ` sean disjuntos solo sirve para escribir una configuración como la cadena `xqy`; aquí la
configuración es una estructura con sus partes separadas, así que no hace falta. -/
structure Maquina (S : Type) where
  /-- El alfabeto de la cinta. -/
  Γ : Type
  /-- Los estados. -/
  Q : Type
  [finΓ : Fintype Γ]
  [decΓ : DecidableEq Γ]
  [finQ : Fintype Q]
  [decQ : DecidableEq Q]
  /-- `Σ ⊆ Γ`. -/
  entrada : S → Γ
  entrada_inyectiva : Function.Injective entrada
  /-- El blanco `b`. -/
  blanco : Γ
  /-- `b ∈ Γ − Σ`. -/
  blanco_fuera : ∀ s, entrada s ≠ blanco
  q₀ : Q
  qacepta : Q
  qrechaza : Q
  /-- La función de transición, definida solo fuera de los dos estados finales. -/
  δ : {q : Q // q ≠ qacepta ∧ q ≠ qrechaza} → Γ → Q × Γ × Mov

attribute [instance] Maquina.finΓ Maquina.decΓ Maquina.finQ Maquina.decQ

variable {S : Type}

/-- Una configuración `xqy` con `y` no vacía: lo que está a la izquierda del cabezal (`x`), el estado, y
`y = lee :: der`, donde `lee` es el símbolo bajo el cabezal. -/
structure Config (M : Maquina S) where
  izq : List M.Γ
  estado : M.Q
  lee : M.Γ
  der : List M.Γ

/-- Una configuración es final si su estado es `qaccept` o `qreject`. -/
def Config.esFinal {M : Maquina S} (C : Config M) : Prop :=
  C.estado = M.qacepta ∨ C.estado = M.qrechaza

/-- El paso `C → C'` del apéndice, con sus cuatro casos. Si `C = xqsy` y `δ(q, s) = (q', s', h)`:

* `h = 1` e `y` no vacía: `C' = xs'q'y`;
* `h = 1` e `y` vacía: `C' = xs'q'b`;
* `h = −1` y `x = x'a`: `C' = x'q'as'y`;
* `h = −1` y `x` vacía: `C' = q'bs'y`.

Una configuración final no tiene sucesora (`none`). -/
def paso (M : Maquina S) (C : Config M) : Option (Config M) :=
  if h : C.estado ≠ M.qacepta ∧ C.estado ≠ M.qrechaza then
    match M.δ ⟨C.estado, h⟩ C.lee with
    | (q', s', Mov.der) =>
      match C.der with
      | [] => some ⟨C.izq ++ [s'], q', M.blanco, []⟩
      | a :: y => some ⟨C.izq ++ [s'], q', a, y⟩
    | (q', s', Mov.izq) =>
      match C.izq.getLast? with
      | none => some ⟨[], q', M.blanco, s' :: C.der⟩
      | some a => some ⟨C.izq.dropLast, q', a, s' :: C.der⟩
  else none

/-- `C₀ = q₀w`, o `q₀b` si `w` es vacía. -/
def inicial (M : Maquina S) (w : List S) : Config M :=
  match w.map M.entrada with
  | [] => ⟨[], M.q₀, M.blanco, []⟩
  | s :: y => ⟨[], M.q₀, s, y⟩

/-- La computación de `M` con entrada `w`: `computacion M w i` es `Cᵢ`, o `none` si la sucesión ya terminó. -/
def computacion (M : Maquina S) (w : List S) : ℕ → Option (Config M)
  | 0 => some (inicial M w)
  | i + 1 => (computacion M w i).bind (paso M)

/-- La computación es finita y termina en `Cₜ`, una configuración final: son `t` pasos, uno menos que el
número de configuraciones. Es `t_M(w) = t`. -/
def TerminaEn (M : Maquina S) (w : List S) (t : ℕ) : Prop :=
  ∃ C, computacion M w t = some C ∧ C.esFinal

/-- `M` acepta `w` si la computación es finita y la configuración final tiene el estado `qaccept`. -/
def Acepta (M : Maquina S) (w : List S) : Prop :=
  ∃ t C, computacion M w t = some C ∧ C.estado = M.qacepta

/-! ## La sección 1: lenguajes, P y NP -/

/-- Un lenguaje sobre `Σ` es un subconjunto de `Σ*`. -/
abbrev Lenguaje (S : Type) := Set (List S)

/-- `L(M) = {w ∈ Σ* | M acepta w}`. -/
def lenguaje (M : Maquina S) : Lenguaje S := {w | Acepta M w}

/-- `M` corre en tiempo polinomial: hay `k` tal que `T_M(n) ≤ nᵏ + k` para todo `n`. Como
`T_M(n) = max {t_M(w) | w ∈ Σⁿ}` es el máximo de un conjunto finito, eso es lo mismo que pedir que cada `w`
termine en a lo sumo `|w|ᵏ + k` pasos, que es como va aquí. -/
def CorreEnTiempoPolinomial (M : Maquina S) : Prop :=
  ∃ k : ℕ, ∀ w : List S, ∃ t, t ≤ w.length ^ k + k ∧ TerminaEn M w t

/-- `P = {L | L = L(M) para alguna máquina de Turing M que corre en tiempo polinomial}`, sobre `Σ`. -/
def ClaseP (S : Type) : Set (Lenguaje S) :=
  {L | ∃ M : Maquina S, CorreEnTiempoPolinomial M ∧ L = lenguaje M}

/-- `L_R = {w#y | R(w, y)}`, sobre `Σ ∪ Σ₁ ∪ {#}`. El alfabeto va como `Option (Σ ⊕ Σ₁)`, con `none` como `#`:
la unión es disjunta. Si `Σ` y `Σ₁` comparten símbolos, eso los renombra, y renombrar el alfabeto no cambia
qué está en P. -/
def lenguajeDe {S₁ : Type} (R : List S → List S₁ → Prop) : Lenguaje (Option (S ⊕ S₁)) :=
  {u | ∃ w y, R w y ∧ u = w.map (some ∘ Sum.inl) ++ [none] ++ y.map (some ∘ Sum.inr)}

/-- `R` es de tiempo polinomial si `L_R ∈ P`. -/
def RelacionPolinomial {S₁ : Type} (R : List S → List S₁ → Prop) : Prop :=
  lenguajeDe R ∈ ClaseP (Option (S ⊕ S₁))

/-- `L ∈ NP` si hay `k ∈ ℕ` y una relación de verificación `R ⊆ Σ* × Σ₁*` de tiempo polinomial, con `Σ₁` un
alfabeto finito, tales que para todo `w`, `w ∈ L ⟺ ∃ y (|y| ≤ |w|ᵏ y R(w, y))`. -/
def ClaseNP (S : Type) : Set (Lenguaje S) :=
  {L | ∃ (S₁ : Type) (_ : Fintype S₁) (_ : DecidableEq S₁) (_ : Nonempty S₁) (k : ℕ)
      (R : List S → List S₁ → Prop), RelacionPolinomial R ∧
      ∀ w, w ∈ L ↔ ∃ y : List S₁, y.length ≤ w.length ^ k ∧ R w y}

/-- **El problema: ¿P = NP?** Para todo alfabeto finito con al menos dos símbolos. El caso de un símbolo Cook
lo deja aparte: también está abierto, y podría tener otra respuesta. -/
def PIgualNP : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S], 2 ≤ Fintype.card S → ClaseP S = ClaseNP S

/-- `P ⊆ NP`. Cook lo da por trivial: la relación `R(w, y) ⟺ w ∈ L` sirve. Probarlo aquí pide construir la
máquina que decide `L_R`, y queda como proposición. -/
def PSubNP : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S], 2 ≤ Fintype.card S → ClaseP S ⊆ ClaseNP S

/-! ## Las definiciones no son vacías

Una máquina de un paso que acepta todo y otra que rechaza todo: así P tiene al lenguaje total y al vacío. -/

/-- La máquina de un paso: desde `q₀` va a `qaccept` (si `acepta`) o a `qreject`, sin mirar la cinta. Estados
`0 = q₀`, `1 = qaccept`, `2 = qreject`; la cinta es `Option Σ`, con `none` como blanco. -/
def unPaso (S : Type) [Fintype S] [DecidableEq S] (acepta : Bool) : Maquina S where
  Γ := Option S
  Q := Fin 3
  entrada := some
  entrada_inyectiva := Option.some_injective S
  blanco := none
  blanco_fuera := fun s => Option.some_ne_none s
  q₀ := 0
  qacepta := 1
  qrechaza := 2
  δ := fun _ s => (if acepta then 1 else 2, s, Mov.der)

/-- La máquina de un paso termina en exactamente un paso, con cualquier entrada: en `qaccept` si `acepta`, en
`qreject` si no. -/
theorem unPaso_computacion (S : Type) [Fintype S] [DecidableEq S] (acepta : Bool) (w : List S) :
    ∃ C, computacion (unPaso S acepta) w 1 = some C ∧
      C.estado = if acepta then (unPaso S acepta).qacepta else (unPaso S acepta).qrechaza := by
  cases acepta <;> cases w with
  | nil => exact ⟨_, rfl, rfl⟩
  | cons s y => cases y <;> exact ⟨_, rfl, rfl⟩

theorem unPaso_polinomial (S : Type) [Fintype S] [DecidableEq S] (acepta : Bool) :
    CorreEnTiempoPolinomial (unPaso S acepta) := by
  refine ⟨1, fun w => ⟨1, by simp, ?_⟩⟩
  obtain ⟨C, hC, he⟩ := unPaso_computacion S acepta w
  refine ⟨C, hC, ?_⟩
  cases acepta
  · exact Or.inr he
  · exact Or.inl he

/-- El lenguaje total `Σ*` está en P. -/
theorem todo_en_P (S : Type) [Finite S] : (Set.univ : Lenguaje S) ∈ ClaseP S := by
  classical
  let := Fintype.ofFinite S
  refine ⟨unPaso S true, unPaso_polinomial S true, ?_⟩
  ext w
  simp only [Set.mem_univ, true_iff]
  obtain ⟨C, hC, he⟩ := unPaso_computacion S true w
  exact ⟨1, C, hC, he⟩

/-- Una computación que llega a una configuración final no sigue: después hay `none`. -/
theorem computacion_despues_de_final {M : Maquina S} {w : List S} {t : ℕ} {C : Config M}
    (h : computacion M w t = some C) (hf : C.esFinal) : computacion M w (t + 1) = none := by
  have hno : ¬(C.estado ≠ M.qacepta ∧ C.estado ≠ M.qrechaza) := by
    rintro ⟨h1, h2⟩
    rcases hf with hf | hf
    · exact h1 hf
    · exact h2 hf
  simp only [computacion, h, Option.bind_some]
  unfold paso
  simp [hno]

/-- El lenguaje vacío está en P: la máquina de un paso que va a `qreject` no acepta nada. -/
theorem vacio_en_P (S : Type) [Finite S] : (∅ : Lenguaje S) ∈ ClaseP S := by
  classical
  let := Fintype.ofFinite S
  refine ⟨unPaso S false, unPaso_polinomial S false, ?_⟩
  ext w
  simp only [Set.mem_empty_iff_false, false_iff]
  rintro ⟨t, C, hC, hacc⟩
  obtain ⟨C₁, h₁, he₁⟩ := unPaso_computacion S false w
  have hfin : C₁.esFinal := Or.inr he₁
  -- en el paso 0 está C₀, con el estado q₀; en el 1, la final, con qreject; después, nada
  match t, hC with
  | 0, hC =>
    obtain rfl : inicial _ w = C := Option.some.inj hC
    cases w <;> simp [inicial, unPaso] at hacc
  | 1, hC =>
    rw [h₁] at hC
    cases hC
    rw [he₁] at hacc
    simp [unPaso] at hacc
  | n + 2, hC =>
    have hnone : ∀ m, computacion (unPaso S false) w (m + 2) = none := by
      intro m
      induction m with
      | zero => exact computacion_despues_de_final h₁ hfin
      | succ m ih =>
        rw [show computacion (unPaso S false) w (m + 1 + 2) =
            (computacion (unPaso S false) w (m + 2)).bind (paso _) from rfl, ih]
        rfl
    rw [hnone n] at hC
    cases hC

/-! ### Dos controles del paso

`paso` tiene cuatro casos. Estas dos máquinas ejercitan los dos de borde, donde se agrega un blanco. -/

/-- Camina a la derecha hasta el primer blanco, y ahí acepta: con entrada de largo `n` termina en `n + 1` pasos.
Ejercita el caso `h = 1` con `y` vacía, `C' = xs'q'b`. -/
def caminaDerecha : Maquina Bool where
  Γ := Option Bool
  Q := Fin 3
  entrada := some
  entrada_inyectiva := Option.some_injective Bool
  blanco := none
  blanco_fuera := fun s => Option.some_ne_none s
  q₀ := 0
  qacepta := 1
  qrechaza := 2
  δ := fun _ s => match s with
    | none => (1, none, Mov.der)
    | some b => (0, some b, Mov.der)

/-- Da un paso a la izquierda desde el borde, y acepta si encuentra un blanco. Ejercita el caso `h = −1` con `x`
vacía, `C' = q'bs'y`: si el paso no agregara el blanco, leería la entrada y rechazaría. -/
def izquierdaDesdeElBorde : Maquina Bool where
  Γ := Option Bool
  Q := Fin 4
  entrada := some
  entrada_inyectiva := Option.some_injective Bool
  blanco := none
  blanco_fuera := fun s => Option.some_ne_none s
  q₀ := 0
  qacepta := 1
  qrechaza := 2
  δ := fun q s => match q.val, s with
    | 0, s => (3, s, Mov.izq)
    | _, none => (1, none, Mov.der)
    | _, some b => (2, some b, Mov.der)

/-- Los pasos en que la computación está en una configuración final, entre 0 y 9, y si acepta. -/
def finales (M : Maquina Bool) (w : List Bool) : List (ℕ × Bool) :=
  (List.range 10).filterMap fun t => (computacion M w t).bind fun C =>
    if C.estado = M.qacepta then some (t, true) else if C.estado = M.qrechaza then some (t, false) else none

#guard finales caminaDerecha [true, false, true] = [(4, true)]
#guard finales caminaDerecha [] = [(1, true)]
#guard finales izquierdaDesdeElBorde [true, true] = [(2, true)]
#guard finales izquierdaDesdeElBorde [] = [(2, true)]

/-! ## El puente con `Clases.lean`

`Clases.lean` toma los problemas como funciones `List Bool → Bool`, solo con el alfabeto binario, y las
máquinas como `TM2` de Mathlib. Hacen falta dos hechos clásicos para pasar de una versión a la otra. Ninguno
está probado aquí. -/

/-- El conjunto de cadenas que un problema de `Clases.lean` acepta. -/
def comoLenguaje (L : Problema) : Lenguaje Bool := {w | L w = true}

/-- **Puente 1, el modelo:** con el alfabeto binario, P y NP de Cook coinciden con los de `Clases.lean`. Es el
resultado de que una cinta y varias pilas se simulan con costo polinomial. -/
def CoincideConClases : Prop :=
  (∀ L : Problema, L ∈ Sagitta.Map.P ↔ comoLenguaje L ∈ ClaseP Bool) ∧
  (∀ L : Problema, L ∈ Sagitta.Map.NP ↔ comoLenguaje L ∈ ClaseNP Bool)

/-- **Puente 2, el alfabeto:** la respuesta no depende del alfabeto mientras tenga al menos dos símbolos. Cook
lo da por fácil: se codifica cada símbolo en binario. -/
def IndependienteDelAlfabeto : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S], 2 ≤ Fintype.card S →
    (ClaseP S = ClaseNP S ↔ ClaseP Bool = ClaseNP Bool)

/-- Todo lenguaje binario es el de algún problema de `Clases.lean`. -/
theorem comoLenguaje_sobre (A : Lenguaje Bool) : ∃ L : Problema, comoLenguaje L = A := by
  classical
  exact ⟨fun w => decide (w ∈ A), by ext w; simp [comoLenguaje]⟩

/-- **Con los dos puentes, la pregunta de Cook y la de `Clases.lean` son la misma.** -/
theorem pIgualNP_iff (hm : CoincideConClases) (ha : IndependienteDelAlfabeto) :
    PIgualNP ↔ Sagitta.Map.PIgualNP := by
  have hb : PIgualNP ↔ ClaseP Bool = ClaseNP Bool := by
    constructor
    · intro h
      exact h Bool (by simp)
    · intro h S _ _ hS
      exact (ha S hS).mpr h
  rw [hb]
  constructor
  · intro h
    ext L
    rw [hm.1 L, hm.2 L, h]
  · intro h
    ext A
    obtain ⟨L, rfl⟩ := comoLenguaje_sobre A
    rw [← hm.1 L, ← hm.2 L]
    unfold Sagitta.Map.PIgualNP at h
    rw [h]

end Cook
end Sagitta.Map
