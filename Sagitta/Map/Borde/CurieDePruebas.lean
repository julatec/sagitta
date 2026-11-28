import Sagitta.Map.Informacion.Simetria
import CslibFrontier.Computability.Complexity.Classes.Oracle

/-!
# El principio de Curie de las pruebas

La observación es de José (25 nov 2026): **cuando chocamos con un muro es porque implícitamente no estamos tomando una
decisión**. Las notas del proyecto, sección «Los muros como decisiones no tomadas», la lee así: un muro aparece cuando el método
es simétrico respecto de un interruptor del que depende la respuesta. Es el principio de Curie (1894) aplicado a las
pruebas: los efectos tienen por lo menos la simetría de las causas, así que una técnica invariante bajo una
transformación solo puede concluir enunciados invariantes bajo esa transformación. Si la respuesta cambia al mover el
interruptor, la técnica que no lo mira no la alcanza.

## Lo que se prueba

1. **El lema abstracto** (§ 1). Mundos `W`, una relación `R` entre mundos (las transformaciones), una técnica
   `t : W → V` que da un veredicto y un lector `d : V → Prop` que lo convierte en afirmación. La técnica **decide**
   `φ` si `d (t w) ↔ φ w` en todo mundo. Si `t` es invariante (`Invariante R t`) y decide `φ`, entonces `φ` es
   invariante (`curie`). Contrapuesto: si `φ a` y `¬ φ b` con `R a b`, la técnica no es correcta en los dos
   (`curie_dos_mundos`) y no decide `φ` (`curie_no_decide`). La versión con un grupo que actúa (`curie_accion`), y
   la que se lee al revés: una técnica correcta separa todo par que `φ` separa (`decide_separa`).
   Con la forma canónica de `Sagitta/Map/Informacion/Simetria.lean` (`EsCanonica`, que ya era el Curie de las órbitas):
   nada que se lea de la forma canónica decide un `φ` que la acción mueve (`canonica_no_decide`).
2. **Dos mundos y una técnica que relativiza** (§ 2). `Relativiza t`: el veredicto no depende del mundo (del
   oráculo). Con `A` y `B` en los que `φ` vale y no vale, ninguna técnica que relativiza decide `φ`
   (`relativiza_no_decide`).
3. **La instancia de la relativización** (§ 3), sobre las clases con oráculo de cslib-frontier
   (`Cslib.Complexity.PWithOracle`, `NPWithOracle`, la máquina con oráculo de Arora y Barak § 3.4). `PigualNP enc O`
   es `P^O = NP^O`. Baker, Gill y Solovay (1975) dan `A` con `P^A = NP^A` y `B` con `P^B ≠ NP^B`; **no se prueba
   aquí**: va como hipótesis con nombre (`BakerGillSolovay`), parámetro explícito y no axioma. Una prueba que
   relativiza de `S` es una que da `S O` para todo oráculo (`PruebaRelativizada`); como conclusión uniforme es una
   técnica constante, y por § 2 ninguna de las dos sale: ni `∀ O, P^O = NP^O` ni `∀ O, P^O ≠ NP^O`
   (`ninguna_relativizada`). Toda técnica correcta para `P^O = NP^O` separa `A` de `B` (`correcta_separa_A_B`).
4. **La otra cara: cruzar el muro** (§ 4), de juguete. Mundos `Bool × Bool`; el interruptor es la primera
   coordenada y `φ w = w.1`. Toda técnica constante falla (`constante_falla`). `w.1` toma la decisión y decide
   (`mira_decide`). `w.1 && w.2` también rompe la simetría (separa `(true, true)` de `(false, true)`), pero sigue
   ciega en el par `(true, false)`, `(false, false)` y no decide `φ` con ningún lector (`rompe_pero_no_decide`).
   Romper la simetría del método es **necesario** (§ 1) y **no suficiente**: hay que romperla en cada par que la
   respuesta separa (`decide_separa`), no en algún par.

## La tabla de muros

```
muro              técnica simétrica respecto de...          el interruptor que no mira          referencia
----------------  ----------------------------------------  ----------------------------------  ---------------------------
relativización    cambiar el oráculo (la máquina lo trata   el oráculo: A da P = NP, B da P ≠ NP Baker–Gill–Solovay 1975
                  como caja negra)
pruebas naturales la dureza «grande y constructiva» no      si hay funciones pseudoaleatorias:   Razborov–Rudich 1997
                  distingue funciones aleatorias de las     la técnica natural las rompería
                  pseudoaleatorias
algebrización     cambiar el oráculo por su extensión       el oráculo algebraico: los dos       Aaronson–Wigderson 2009
                  algebraica de bajo grado                  lados vuelven a tener mundos
```

Solo la primera fila está formalizada (§ 3), y solo en la forma «la técnica es invariante, la respuesta no»; las
otras dos son lecturas de la misma forma, con otro grupo de transformaciones.

## La honestidad

* **El lema es formal y elemental.** `curie` es una línea: si `d (t a) ↔ φ a`, `d (t b) ↔ φ b` y `t a = t b`,
  entonces `φ a ↔ φ b`. Lo que vale de él es el encuadre, no la dificultad.
* **«Decisión» es una lectura.** Que un muro sea «una decisión no tomada» es la interpretación de José de este lema;
  Lean no sabe qué es una decisión. Lo que Lean sabe es: la técnica no mira el interruptor (`Invariante`), y la
  respuesta depende de él.
* **Baker–Gill–Solovay no se prueba**; entra como hipótesis. El modelo de «prueba que relativiza» es el semántico
  (una conclusión que vale para todo oráculo), no uno sintáctico de pruebas.
* **Cruzar el muro de juguete** (§ 4) no dice nada sobre P contra NP; muestra la forma lógica: romper la simetría es
  condición necesaria y no suficiente.
* Nada sobre P contra NP.
-/

namespace Sagitta.Map.Borde.CurieDePruebas

open MulAction

/-! ## 1. El lema abstracto -/

section Abstracto

variable {W V : Type*}

/-- La técnica `t` es **invariante** bajo `R`: da el mismo veredicto en mundos relacionados. -/
def Invariante (R : W → W → Prop) (t : W → V) : Prop := ∀ a b, R a b → t a = t b

/-- La técnica `t`, leída con `d`, es **correcta** para `φ` en el mundo `w`. -/
def CorrectaEn (t : W → V) (d : V → Prop) (φ : W → Prop) (w : W) : Prop := (d (t w) ↔ φ w)

/-- La técnica **decide** `φ`: es correcta en todos los mundos. -/
def Decide (t : W → V) (d : V → Prop) (φ : W → Prop) : Prop := ∀ w, CorrectaEn t d φ w

/-- **Curie**: si la técnica es invariante bajo `R` y decide `φ`, entonces `φ` es invariante bajo `R`.
Los efectos tienen por lo menos la simetría de las causas. -/
theorem curie {R : W → W → Prop} {t : W → V} (ht : Invariante R t) {d : V → Prop} {φ : W → Prop}
    (hd : Decide t d φ) {a b : W} (hab : R a b) : φ a ↔ φ b := by
  have h1 : d (t a) ↔ φ a := hd a
  have h2 : d (t b) ↔ φ b := hd b
  rw [ht a b hab] at h1
  exact h1.symm.trans h2

/-- Dos mundos relacionados que `φ` separa: la técnica invariante no es correcta en los dos. -/
theorem curie_dos_mundos {R : W → W → Prop} {t : W → V} (ht : Invariante R t) (d : V → Prop)
    {φ : W → Prop} {a b : W} (hab : R a b) (ha : φ a) (hb : ¬ φ b) :
    ¬ (CorrectaEn t d φ a ∧ CorrectaEn t d φ b) := by
  rintro ⟨h1, h2⟩
  have : d (t a) := h1.mpr ha
  rw [ht a b hab] at this
  exact hb (h2.mp this)

/-- Y por lo tanto no decide `φ`, con ningún lector. -/
theorem curie_no_decide {R : W → W → Prop} {t : W → V} (ht : Invariante R t) (d : V → Prop)
    {φ : W → Prop} {a b : W} (hab : R a b) (ha : φ a) (hb : ¬ φ b) : ¬ Decide t d φ :=
  fun hd => curie_dos_mundos ht d hab ha hb ⟨hd a, hd b⟩

/-- Leído al revés: una técnica correcta **separa** todo par de mundos que `φ` separa. -/
theorem decide_separa {t : W → V} {d : V → Prop} {φ : W → Prop} (hd : Decide t d φ) {a b : W}
    (ha : φ a) (hb : ¬ φ b) : t a ≠ t b := by
  intro h
  exact hb ((hd b).mp (h ▸ (hd a).mpr ha))

/-- La versión con un grupo que actúa: la técnica invariante bajo `G` no decide un `φ` que algún `g` mueve. -/
theorem curie_accion {G : Type*} [Group G] [MulAction G W] {t : W → V} (ht : ∀ (g : G) w, t (g • w) = t w)
    (d : V → Prop) {φ : W → Prop} {w : W} {g : G} (h1 : φ w) (h2 : ¬ φ (g • w)) : ¬ Decide t d φ :=
  curie_no_decide (R := fun a b => ∃ g : G, g • a = b) (fun a _ ⟨g, hg⟩ => hg ▸ (ht g a).symm) d ⟨g, rfl⟩ h1 h2

/-- Con la forma canónica de `Simetria` (el Curie de las órbitas): nada que se lea de ella decide un `φ` que la
acción mueve. Ganar toda la simetría es perder todo lo que no es invariante. -/
theorem canonica_no_decide {G σ : Type*} [Group G] [MulAction G σ] {c : σ → σ}
    (hc : Sagitta.Map.Informacion.Simetria.EsCanonica G c) (d : σ → Prop) {φ : σ → Prop} {x : σ} {g : G}
    (h1 : φ x) (h2 : ¬ φ (g • x)) : ¬ Decide c d φ :=
  curie_accion (G := G) hc.invariante d h1 h2

end Abstracto

/-! ## 2. Dos mundos y una técnica que relativiza -/

section DosMundos

variable {O V : Type*}

/-- Una técnica que **relativiza**: su veredicto no depende del mundo (del oráculo). Es `Invariante` respecto de la
relación total. -/
def Relativiza (t : O → V) : Prop := ∀ A B, t A = t B

theorem relativiza_invariante {t : O → V} (ht : Relativiza t) : Invariante (fun _ _ => True) t :=
  fun a b _ => ht a b

/-- **Dos mundos**: si `φ` vale en `A` y no en `B`, ninguna técnica que relativiza decide `φ`. -/
theorem relativiza_no_decide {t : O → V} (ht : Relativiza t) (d : V → Prop) {φ : O → Prop} {A B : O}
    (hA : φ A) (hB : ¬ φ B) : ¬ Decide t d φ :=
  curie_no_decide (relativiza_invariante ht) d trivial hA hB

/-- Una conclusión uniforme («`S` vale en todo mundo») es una técnica constante que decide `S`. -/
theorem uniforme_decide {S : O → Prop} (h : ∀ o, S o) :
    Relativiza (fun _ : O => ()) ∧ Decide (fun _ : O => ()) (fun _ => True) S :=
  ⟨fun _ _ => rfl, fun o => ⟨fun _ => h o, fun _ => trivial⟩⟩

/-- Con dos mundos que `S` separa, ni `∀ o, S o` ni `∀ o, ¬ S o`. -/
theorem ninguna_uniforme {S : O → Prop} {A B : O} (hA : S A) (hB : ¬ S B) :
    ¬ (∀ o, S o) ∧ ¬ (∀ o, ¬ S o) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hr, hd⟩ := uniforme_decide h
    exact relativiza_no_decide hr _ hA hB hd
  · obtain ⟨hr, hd⟩ := uniforme_decide h
    exact relativiza_no_decide hr _ hB (not_not_intro hA) hd

end DosMundos

/-! ## 3. La instancia de la relativización -/

section Relativizacion

open Cslib.Complexity

variable {α : Type} (enc : α ↪ List Bool)

/-- `P^O = NP^O`, con las clases con oráculo de cslib-frontier, para la codificación `enc` de las instancias. -/
def PigualNP (O : Set (List Bool)) : Prop := PWithOracle O enc = NPWithOracle O enc

/-- **Baker, Gill y Solovay (1975)**, como hipótesis con nombre: hay un oráculo con `P = NP` y otro con `P ≠ NP`.
No se prueba aquí; los teoremas que la usan la reciben como parámetro. -/
structure BakerGillSolovay : Prop where
  iguales : ∃ A, PigualNP enc A
  distintas : ∃ B, ¬ PigualNP enc B

/-- Una **prueba que relativiza** de `S`: da `S O` para todo oráculo `O`. -/
def PruebaRelativizada (S : Set (List Bool) → Prop) : Prop := ∀ O, S O

/-- **El muro de la relativización**: con Baker–Gill–Solovay, ninguna de las dos conclusiones relativizadas es
verdadera, ni `∀ O, P^O = NP^O` ni `∀ O, P^O ≠ NP^O`. -/
theorem ninguna_relativizada (h : BakerGillSolovay enc) :
    ¬ PruebaRelativizada (PigualNP enc) ∧ ¬ PruebaRelativizada (fun O => ¬ PigualNP enc O) := by
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := h
  exact ninguna_uniforme hA hB

/-- Ninguna técnica que relativiza decide `P^O = NP^O`. -/
theorem relativizante_no_decide (h : BakerGillSolovay enc) {V : Type*} {t : Set (List Bool) → V}
    (ht : Relativiza t) (d : V → Prop) : ¬ Decide t d (PigualNP enc) := by
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := h
  exact relativiza_no_decide ht d hA hB

/-- Toda técnica correcta para `P^O = NP^O` separa los dos mundos de Baker–Gill–Solovay: tiene que mirar el
oráculo. -/
theorem correcta_separa_A_B {V : Type*} {t : Set (List Bool) → V} {d : V → Prop}
    (hd : Decide t d (PigualNP enc)) {A B : Set (List Bool)} (hA : PigualNP enc A) (hB : ¬ PigualNP enc B) :
    t A ≠ t B :=
  decide_separa hd hA hB

end Relativizacion

/-! ## 4. La otra cara: cruzar el muro, de juguete -/

section Juguete

/-- El enunciado de juguete: el interruptor es la primera coordenada. -/
def φj (w : Bool × Bool) : Prop := w.1 = true

/-- Toda técnica constante falla: el interruptor cambia la respuesta. -/
theorem constante_falla {V : Type*} (v : V) (d : V → Prop) : ¬ Decide (fun _ : Bool × Bool => v) d φj :=
  relativiza_no_decide (A := (true, true)) (B := (false, true)) (fun _ _ => rfl) d rfl (by simp [φj])

/-- La técnica que toma la decisión (mira el interruptor) decide. -/
theorem mira_decide : ¬ Relativiza (fun w : Bool × Bool => w.1) ∧ Decide (fun w : Bool × Bool => w.1) (· = true) φj :=
  ⟨fun h => by simpa using h (true, true) (false, true), fun _ => Iff.rfl⟩

/-- **Necesario y no suficiente**: `w.1 && w.2` rompe la simetría (separa `(true, true)` de `(false, true)`) pero
queda ciega en `(true, false)`, `(false, false)`, y no decide `φj` con ningún lector. -/
theorem rompe_pero_no_decide :
    ¬ Relativiza (fun w : Bool × Bool => w.1 && w.2) ∧
      ∀ d : Bool → Prop, ¬ Decide (fun w : Bool × Bool => w.1 && w.2) d φj := by
  refine ⟨fun h => by simpa using h (true, true) (false, true), fun d hd => ?_⟩
  exact decide_separa hd (a := (true, false)) (b := (false, false)) rfl (by simp [φj]) rfl

end Juguete

end Sagitta.Map.Borde.CurieDePruebas
