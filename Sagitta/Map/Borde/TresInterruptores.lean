import Sagitta.Map.Borde.FractalSAT
import Sagitta.Map.Borde.DicotomiaBooleana
import CslibFrontier.Computability.Complexity.Classes.NP.Witness

/-!
# Los tres interruptores: dicotomía contra intermedios

El paso «los tres interruptores» de las notas del proyecto («El fractal de SAT»). José (25 nov 2026) pidió montar formalmente
«dicotomía contra intermedios» con tres interruptores que hagan exactamente eso. Los interruptores son las tres
restricciones de Feder y Vardi (1993–1998) sobre SNP (la lógica existencial de segundo orden con la parte de primer
orden universal):

* **M**, monótono: las relaciones de la entrada solo aparecen negadas;
* **Mo**, monádico: los predicados existenciales son de un argumento;
* **D**, sin desigualdad: no se escribe `x ≠ y`.

Con los tres encendidos (MMSNP) la clase es, salvo equivalencia polinomial, la de los CSP de plantilla finita, y esos
tienen dicotomía (Bulatov y Zhuk, 2017). Con cualquiera apagado la clase captura todo NP salvo equivalencia polinomial,
y por Ladner hay intermedios si P ≠ NP.

## La tabla

`1` = restricción impuesta (interruptor encendido). Las ocho combinaciones se parten en **una** con dicotomía y
**siete** con «intermedios ⟺ P ≠ NP» (`interruptor_decide`, `card_encendido`, `card_apagado`).

| M | Mo | D | clase                                  | por qué (hipótesis con nombre)            | resultado                     |
|---|----|---|----------------------------------------|-------------------------------------------|-------------------------------|
| 1 | 1  | 1 | MMSNP                                  | `FV_encendido` (FV Teo. 5, Kun Teo. 2) + BZ | dicotomía                     |
| 1 | 1  | 0 | MMSNP con `≠`                          | `FV_conDesigualdad` (FV Teo. 1)           | intermedios ⟺ P ≠ NP          |
| 0 | 1  | 1 | SNP monádico sin `≠`                   | `FV_sinMonotonia` (FV Teo. 2)             | intermedios ⟺ P ≠ NP          |
| 1 | 0  | 1 | SNP monótono sin `≠`                   | `FV_sinMonadicidad` (FV Teo. 3)           | intermedios ⟺ P ≠ NP          |
| 0 | 0  | 1 | SNP sin `≠`                            | contiene a la de (0,1,1): `contencion`    | intermedios ⟺ P ≠ NP          |
| 0 | 1  | 0 | SNP monádico                           | contiene a la de (0,1,1)                  | intermedios ⟺ P ≠ NP          |
| 1 | 0  | 0 | SNP monótono                           | contiene a la de (1,0,1)                  | intermedios ⟺ P ≠ NP          |
| 0 | 0  | 0 | SNP                                    | contiene a cualquiera                     | intermedios ⟺ P ≠ NP          |

Y en forma de «el interruptor decide exactamente»: si P ≠ NP, el fragmento tiene dicotomía **si y solo si** los tres
están encendidos (`dicotomia_iff_encendido`); si P = NP, los ocho tienen dicotomía y ninguno intermedios
(`todos_dicotomia_de_P_eq_NP`).

## Lo que se prueba y lo que entra como hipótesis

**Probado aquí** (sin `sorry`, axiomas `propext`, `Classical.choice`, `Quot.sound`):

* el **transporte por equivalencia polinomial** (§ 1): la reducción `L ≤ₚ L'` baja «en P» y «en NP» de `L'` a `L` y
  sube «NP-difícil» de `L` a `L'`; con las dos direcciones se conservan «en P», «en NP», «NP-completo» y «ser
  intermedio» (`Equivalentes.enP_iff`, `.enNP_iff`, `.completo_iff`, `.intermedio_iff`); la dicotomía pasa de una clase
  a otra cuyos problemas le son equivalentes (`dicotomia_de_equivalentes`), y una clase que captura NP hereda los
  intermedios (`intermedios_de_captura`);
* los casos triviales: `∅` y `Σ*` nunca son NP-completos (`vacio_no_completo`, `univ_no_completo`), y con P = NP (en
  toda codificación) un `L ∈ NP` es NP-completo **exactamente** cuando no es trivial (`completo_iff_no_trivial`);
* la **lógica de los interruptores** (§ 3): (a) `encendido_dicotomia`, (b) `apagado_iff`, (c) `interruptor_decide`;
* **Ladner** no es hipótesis: viene de cslib-frontier, ya conectado en `RelojDeLadner.lean` y `FractalSAT.lean`
  (`FractalSAT.ladner`).

**Hipótesis con nombre**, parámetros explícitos y nunca axiomas (`FederVardi`, y `BZ` aparte):

* `FV_encendido`: todo problema de MMSNP es polinomialmente equivalente a un CSP de plantilla finita. **Matiz
  aleatorio.** Feder–Vardi (Teo. 5) dicen literalmente que la equivalencia es por una reducción de Karp determinista
  de MMSNP a CSP y por una reducción de **Turing aleatoria** de CSP a MMSNP. Kun (Combinatorica 33(3), 2013, Teo. 2)
  la desaleatorizó: da `L ≤ₚ CSP(T)` y `CSP(T) ≤ₚ L` deterministas. La hipótesis está en la forma de Kun, con un
  matiz no leído: un trabajo posterior dice que Kun todavía usa una prueba probabilística de que *existen* los
  expansores (la reducción es determinista; su existencia se prueba contando). Sin Kun, lo que sí sobrevive se lee en
  `dicotomia_de_reducciones`: el lado «en P» usa **solo** la dirección determinista `L ≤ₚ C`; el lado «NP-completo»
  pide la vuelta `C ≤ₚ L`, que con Feder–Vardi solos es aleatoria, y daría «NP-difícil bajo reducciones aleatorias».
* `BZ`: los CSP de plantilla finita tienen dicotomía (Bulatov, FOCS 2017; Zhuk, J. ACM 2020, Teo. 1.4).
* `FV_conDesigualdad`, `FV_sinMonotonia`, `FV_sinMonadicidad`: Feder–Vardi, Teos. 1, 2 y 3. Las tres son
  equivalencias polinomiales **deterministas** en las dos direcciones; la del Teo. 1 está completa en Barsukov–Madelaine
  (LMCS 21(4):15, 2025, § 4).
* `contencion`: apagar más interruptores agranda la clase (es sintaxis: una fórmula con más restricciones también
  cumple menos). Feder–Vardi enuncian solo las tres esquinas con un interruptor apagado; las otras cuatro salen de
  aquí.
* `enNP`: cada fragmento está en NP (SNP ⊆ ESO = NP, Fagin; Fagin es ESO = NP, no SNP = NP).

La sintaxis de SNP **no** se formaliza: cada fragmento es un parámetro (`frag s`, una clase de lenguajes sobre
`List Bool` al estilo de cslib). Formalizar Feder–Vardi y Bulatov–Zhuk es otro proyecto; lo probado es la lógica de los
interruptores y el transporte por equivalencias, más Ladner de cslib.

## El caso booleano (§ 4)

Bulatov–Zhuk restringido a plantillas booleanas es Schaefer, que `DicotomiaBooleana.lean` arma módulo `Supuestos`.
Aquí se instancia (a) **sin la hipótesis BZ**: si cada problema de la clase es equivalente a un `CSP(Γ)` booleano
finito, la clase tiene dicotomía (`booleano_dicotomia`, `encendido_dicotomia_booleano`). Lo que falta, con nombre en
`SchaeferSinSeparar`: que `CSP(Γ)` esté en NP, el lado fácil (2-SAT y afín; Horn y constantes ya están probados como
algoritmos allá), el retículo de Post, Cook–Levin para 3-SAT y NAE-3-SAT, y que la traducción por gadgets sea
polinomial. El campo `separa` (P ≠ NP) de `Supuestos` **ya no hace falta**: si P = NP, todo `CSP(Γ)` en NP está en P
y la dicotomía vale de balde; si P ≠ NP, `separa` sale de `NPComplete.P_eq_NP_of_mem_P`. Lo que no se puede dar: la
instancia sirve para clases equivalentes a CSP **booleanos**, y MMSNP no lo es (sus plantillas son de cualquier
tamaño); para MMSNP entero hace falta BZ.

## La lectura de José, y una diferencia

**«Dimensión 0 o 1» contra fractal.** En la lectura de José, la dicotomía es que el conjunto de respuestas, mirado por
lo que cuesta decidirlo, cae en dimensión 0 (P, colapsa) o en 1 (NP-completo, lo llena todo), y los intermedios de
Ladner son el fractal, lo autosimilar que queda en medio. Lo formal es más pobre y más preciso: dicotomía es
`∀ L ∈ F, L ∈ P ∨ L NP-completo`; intermedios es `∃ L ∈ F` en NP, fuera de P y no NP-completo. No hay ninguna
dimensión definida (las notas del proyecto, «Qué principio permite la dimensión fraccionaria»: no hay contraparte rigurosa de una
dimensión fraccionaria intrínseca). Lo que el teorema dice es que **tres restricciones sintácticas** deciden de qué
lado cae una clase, y que la decisión es exacta: ningún interruptor tiene grados, y ninguna combinación queda a medias.

**No son los interruptores R, A y N de las notas del proyecto.** Aquellos (relativiza, algebriza, es natural) son propiedades de
**técnicas de prueba**: clasifican argumentos, y la esquina (0,0,0) es dónde tendría que vivir una prueba de P ≠ NP.
Estos son propiedades de **clases de problemas**: clasifican fórmulas de SNP, y la esquina (1,1,1) es la única donde el
medio está prohibido. Allá el interruptor dice qué técnica podría alcanzar; aquí dice qué problema puede quedar en
medio. Los dos cubos tienen ocho esquinas y una esquina especial, y ahí termina el parecido: ningún resultado de este
archivo dice nada de técnicas.

## Antecedentes

Feder–Vardi, SIAM J. Comput. 28(1):57–104, 1998 (STOC '93); Kun, Combinatorica 33(3):335–347, 2013; Bulatov, FOCS
2017; Zhuk, J. ACM 67(5), 2020; Ladner, J. ACM 22(1), 1975; Fagin, 1974; Schaefer, STOC 1978; Barsukov–Madelaine,
LMCS 2025. Las referencias se verificaron (DOI en Crossref) en la investigación de la sesión del 25 nov 2026.
-/

namespace Sagitta.Map.Borde.TresInterruptores

open Cslib.Complexity Turing.MultiTapeTM
open Sagitta.Map.Borde.FractalSAT (Intermedio intermedio_implica_P_ne_NP ladner completo_de_P_eq_NP)

/-- Un problema de decisión, en el estilo de cslib: un lenguaje sobre `List Bool` con la codificación `encBits`. -/
abbrev Lenguaje := Set (List Bool)

/-- Una clase de problemas. -/
abbrev Clase := Set Lenguaje

/-! ## 1. El transporte por equivalencia polinomial -/

/-- `L ≤ₚ L'` (reducción de Karp polinomial de cslib). -/
abbrev Reduce (L L' : Lenguaje) : Prop := PolyTimeReducible encBits encBits L L'

/-- **Equivalencia polinomial**: reducciones de Karp deterministas en las dos direcciones. -/
def Equivalentes (L L' : Lenguaje) : Prop := Reduce L L' ∧ Reduce L' L

theorem Equivalentes.symm {L L' : Lenguaje} (h : Equivalentes L L') : Equivalentes L' L := ⟨h.2, h.1⟩

theorem Equivalentes.refl (L : Lenguaje) : Equivalentes L L :=
  ⟨PolyTimeReducible.refl encBits L, PolyTimeReducible.refl encBits L⟩

/-- La reducción baja «en P». -/
theorem enP_de_reduce {L L' : Lenguaje} (h : Reduce L L') (h' : L' ∈ Cslib.Complexity.P encBits) : L ∈ Cslib.Complexity.P encBits := h.mem_P h'

/-- La reducción baja «en NP». -/
theorem enNP_de_reduce {L L' : Lenguaje} (h : Reduce L L') (h' : L' ∈ Cslib.Complexity.NP encBits) : L ∈ Cslib.Complexity.NP encBits := h.mem_NP h'

/-- La reducción sube «NP-completo», si el de llegada está en NP. -/
theorem completo_de_reduce {L L' : Lenguaje} (h : Reduce L L') (hL : NPComplete encBits L) (h' : L' ∈ Cslib.Complexity.NP encBits) :
    NPComplete encBits L' := ⟨h', NPHard.trans hL.2 h⟩

theorem Equivalentes.enP_iff {L L' : Lenguaje} (h : Equivalentes L L') : L ∈ Cslib.Complexity.P encBits ↔ L' ∈ Cslib.Complexity.P encBits :=
  ⟨enP_de_reduce h.2, enP_de_reduce h.1⟩

theorem Equivalentes.enNP_iff {L L' : Lenguaje} (h : Equivalentes L L') : L ∈ Cslib.Complexity.NP encBits ↔ L' ∈ Cslib.Complexity.NP encBits :=
  ⟨enNP_de_reduce h.2, enNP_de_reduce h.1⟩

theorem Equivalentes.completo_iff {L L' : Lenguaje} (h : Equivalentes L L') :
    NPComplete encBits L ↔ NPComplete encBits L' :=
  ⟨fun hc => completo_de_reduce h.1 hc (enNP_de_reduce h.2 hc.1),
    fun hc => completo_de_reduce h.2 hc (enNP_de_reduce h.1 hc.1)⟩

/-- **Ser intermedio se conserva** por equivalencia polinomial. -/
theorem Equivalentes.intermedio_iff {L L' : Lenguaje} (h : Equivalentes L L') : Intermedio L ↔ Intermedio L' := by
  unfold Intermedio
  rw [h.enNP_iff, h.enP_iff, h.completo_iff]

/-! ## 2. Dicotomía e intermedios -/

/-- **Dicotomía**: todo problema de la clase está en P o es NP-completo. -/
def TieneDicotomia (F : Clase) : Prop := ∀ L ∈ F, L ∈ Cslib.Complexity.P encBits ∨ NPComplete encBits L

/-- **Intermedios**: algún problema de la clase está en NP, fuera de P y no es NP-completo. -/
def TieneIntermedios (F : Clase) : Prop := ∃ L ∈ F, L ∈ Cslib.Complexity.NP encBits ∧ L ∉ Cslib.Complexity.P encBits ∧ ¬ NPComplete encBits L

/-- Las dos cosas se excluyen. -/
theorem no_ambas {F : Clase} (hD : TieneDicotomia F) : ¬ TieneIntermedios F := by
  rintro ⟨L, hL, -, hP, hC⟩
  rcases hD L hL with h | h
  · exact hP h
  · exact hC h

/-- **La dicotomía, por reducciones de un lado cada una.** Si cada `L` de `F` tiene un `C` en una clase con dicotomía
con `L ≤ₚ C` (ida) y `C ≤ₚ L` (vuelta), `F` tiene dicotomía. El lado «en P» usa **solo la ida**: es la reducción de
Karp determinista de MMSNP a CSP de Feder–Vardi. El lado «NP-completo» usa la vuelta (para la dificultad) y la ida
(para estar en NP): con Feder–Vardi solos la vuelta es una reducción de Turing aleatoria, y con Kun es de Karp. -/
theorem dicotomia_de_reducciones {F G : Clase} (hG : TieneDicotomia G)
    (h : ∀ L ∈ F, ∃ C ∈ G, Reduce L C ∧ Reduce C L) : TieneDicotomia F := by
  intro L hL
  obtain ⟨C, hC, ida, vuelta⟩ := h L hL
  rcases hG C hC with hp | hc
  · exact Or.inl (enP_de_reduce ida hp)
  · exact Or.inr (completo_de_reduce vuelta hc (enNP_de_reduce ida hc.1))

/-- **La dicotomía se transporta** por equivalencia polinomial. -/
theorem dicotomia_de_equivalentes {F G : Clase} (hG : TieneDicotomia G)
    (h : ∀ L ∈ F, ∃ C ∈ G, Equivalentes L C) : TieneDicotomia F :=
  dicotomia_de_reducciones hG fun L hL => by
    obtain ⟨C, hC, e⟩ := h L hL
    exact ⟨C, hC, e.1, e.2⟩

/-- Una clase que **captura NP** (todo `L ∈ NP` tiene un equivalente en ella). -/
def CapturaNP (F : Clase) : Prop := ∀ L ∈ Cslib.Complexity.NP encBits, ∃ L' ∈ F, Equivalentes L L'

/-- **Los intermedios suben** a una clase que captura NP: Ladner (cslib-frontier) da uno en NP, y la equivalencia lo
lleva a la clase conservando ser intermedio. -/
theorem intermedios_de_captura {F : Clase} (hF : CapturaNP F) (h : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits) : TieneIntermedios F := by
  obtain ⟨L, hL⟩ := ladner h
  obtain ⟨L', hL', e⟩ := hF L hL.1
  exact ⟨L', hL', (e.intermedio_iff.mp hL)⟩

/-- La dirección trivial: un intermedio, en cualquier clase, ya da P ≠ NP. -/
theorem P_ne_NP_de_intermedios {F : Clase} (h : TieneIntermedios F) : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits := by
  obtain ⟨L, -, hL⟩ := h
  exact intermedio_implica_P_ne_NP hL

/-- **En una clase que captura NP, hay intermedios exactamente si P ≠ NP.** -/
theorem captura_iff {F : Clase} (hF : CapturaNP F) : TieneIntermedios F ↔ Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits :=
  ⟨P_ne_NP_de_intermedios, intermedios_de_captura hF⟩

/-- Con P = NP, cualquier clase dentro de NP tiene dicotomía, y de la manera más barata: todo está en P. -/
theorem dicotomia_de_P_eq_NP {F : Clase} (h : Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits) (hF : F ⊆ Cslib.Complexity.NP encBits) : TieneDicotomia F :=
  fun _ hL => Or.inl (h ▸ hF hL)

/-! ### Los casos triviales `∅` y `Σ*` -/

/-- `∅` nunca es NP-completo: `Σ*` está en NP y no se reduce a `∅`. -/
theorem vacio_no_completo : ¬ NPComplete encBits (∅ : Lenguaje) := by
  intro h
  obtain ⟨f, -, hf⟩ := h.2 encBits Set.univ univ_mem_NP
  exact ((hf []).mp trivial).elim

/-- `Σ*` nunca es NP-completo: `∅` está en NP y no se reduce a `Σ*`. -/
theorem univ_no_completo : ¬ NPComplete encBits (Set.univ : Lenguaje) := by
  intro h
  obtain ⟨f, -, hf⟩ := h.2 encBits ∅ empty_mem_NP
  exact (hf []).mpr trivial

/-- **Con P = NP (en toda codificación), un `L ∈ NP` es NP-completo exactamente cuando no es trivial.** Es la
dirección de `P = NP ⟹ sin intermedios` con los casos triviales cuidados: `∅` y `Σ*` están en P y no son
NP-completos; todo lo demás es NP-completo y también está en P. -/
theorem completo_iff_no_trivial
    (hPNP : ∀ {α : Type} (enc : α ↪ List Bool), Cslib.Complexity.P enc = Cslib.Complexity.NP enc) {L : Lenguaje} (hL : L ∈ Cslib.Complexity.NP encBits) :
    NPComplete encBits L ↔ L ≠ ∅ ∧ L ≠ Set.univ := by
  constructor
  · intro h
    refine ⟨fun e => vacio_no_completo (e ▸ h), fun e => univ_no_completo (e ▸ h)⟩
  · rintro ⟨h0, h1⟩
    obtain ⟨y₁, hy₁⟩ := Set.nonempty_iff_ne_empty.mpr h0
    obtain ⟨y₀, hy₀⟩ : ∃ y, y ∉ L := by
      by_contra hc
      push Not at hc
      exact h1 (Set.eq_univ_of_forall hc)
    exact completo_de_P_eq_NP hPNP hL hy₁ hy₀

/-! ## 3. Los tres interruptores -/

/-- **Los tres interruptores** de Feder y Vardi. `true` = la restricción está impuesta (encendido). -/
structure Interruptores where
  /-- M: las relaciones de la entrada solo aparecen negadas. -/
  monotono : Bool
  /-- Mo: los predicados existenciales son monádicos. -/
  monadico : Bool
  /-- D: no se escribe la desigualdad. -/
  sinDesigualdad : Bool
  deriving DecidableEq, Fintype, Repr

/-- Los tres encendidos: MMSNP. -/
def encendido : Interruptores := ⟨true, true, true⟩

/-- Las tres esquinas con un solo interruptor apagado, las de Feder–Vardi Teos. 1, 2 y 3. -/
def sinM : Interruptores := ⟨false, true, true⟩
def sinMo : Interruptores := ⟨true, false, true⟩
def sinD : Interruptores := ⟨true, true, false⟩

/-- `Impone s t`: `s` impone al menos las restricciones que impone `t`. Entonces la clase de `s` es más chica. -/
def Impone (s t : Interruptores) : Prop :=
  (t.monotono = true → s.monotono = true) ∧ (t.monadico = true → s.monadico = true) ∧
    (t.sinDesigualdad = true → s.sinDesigualdad = true)

/-- **Lo que se toma de Feder–Vardi (y de Kun), con nombre.** `frag s` es la clase de problemas de SNP con las
restricciones encendidas en `s`; `csp` es la clase de los CSP de plantilla finita. Ver el encabezado del archivo para la
fuente de cada campo y el matiz aleatorio de `FV_encendido`. -/
structure FederVardi (frag : Interruptores → Clase) (csp : Clase) : Prop where
  /-- Más restricciones, clase más chica (sintaxis). -/
  contencion : ∀ s t, Impone s t → frag s ⊆ frag t
  /-- SNP ⊆ NP (Fagin). -/
  enNP : ∀ s, frag s ⊆ Cslib.Complexity.NP encBits
  /-- FV Teo. 5, en la forma determinista de Kun (2013, Teo. 2): MMSNP ≡ CSP finito. -/
  FV_encendido : ∀ L ∈ frag encendido, ∃ C ∈ csp, Equivalentes L C
  /-- FV Teo. 2: SNP monádico sin `≠` y sin monotonía captura NP. -/
  FV_sinMonotonia : CapturaNP (frag sinM)
  /-- FV Teo. 3: SNP monótono sin `≠` y sin monadicidad captura NP. -/
  FV_sinMonadicidad : CapturaNP (frag sinMo)
  /-- FV Teo. 1: MMSNP con desigualdad captura NP. -/
  FV_conDesigualdad : CapturaNP (frag sinD)

variable {frag : Interruptores → Clase} {csp : Clase}

/-- Capturar NP sube a las clases más grandes. -/
theorem CapturaNP.mono {F G : Clase} (h : CapturaNP F) (hFG : F ⊆ G) : CapturaNP G := fun L hL => by
  obtain ⟨L', hL', e⟩ := h L hL
  exact ⟨L', hFG hL', e⟩

/-- **Con algún interruptor apagado, la clase captura NP**: está por encima de una de las tres esquinas de
Feder–Vardi. -/
theorem captura_de_apagado (H : FederVardi frag csp) {s : Interruptores} (hs : s ≠ encendido) :
    CapturaNP (frag s) := by
  obtain ⟨m, mo, d⟩ := s
  cases m
  · exact H.FV_sinMonotonia.mono (H.contencion _ _ (by simp [Impone, sinM]))
  cases mo
  · exact H.FV_sinMonadicidad.mono (H.contencion _ _ (by simp [Impone, sinMo]))
  cases d
  · exact H.FV_conDesigualdad.mono (H.contencion _ _ (by simp [Impone, sinD]))
  exact absurd rfl hs

/-- **(a) Los tres encendidos: dicotomía**, de `FV_encendido` y Bulatov–Zhuk, por transporte. -/
theorem encendido_dicotomia (H : FederVardi frag csp) (BZ : TieneDicotomia csp) : TieneDicotomia (frag encendido) :=
  dicotomia_de_equivalentes BZ H.FV_encendido

/-- **(b) Al menos uno apagado: intermedios ⟺ P ≠ NP.** (⟸) Ladner de cslib y la captura de Feder–Vardi; (⟹) un
intermedio está en NP y fuera de P. -/
theorem apagado_iff (H : FederVardi frag csp) {s : Interruptores} (hs : s ≠ encendido) :
    TieneIntermedios (frag s) ↔ Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits :=
  captura_iff (captura_de_apagado H hs)

/-- **(c) El interruptor decide**: cada combinación cae en exactamente uno de los dos lados de la tabla. -/
theorem interruptor_decide (H : FederVardi frag csp) (BZ : TieneDicotomia csp) (s : Interruptores) :
    (s = encendido ∧ TieneDicotomia (frag s)) ∨
      (s ≠ encendido ∧ (TieneIntermedios (frag s) ↔ Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits)) := by
  by_cases hs : s = encendido
  · subst hs; exact Or.inl ⟨rfl, encendido_dicotomia H BZ⟩
  · exact Or.inr ⟨hs, apagado_iff H hs⟩

/-- Ocho combinaciones. -/
theorem card_interruptores : Fintype.card Interruptores = 8 := by decide

/-- Una con dicotomía… -/
theorem card_encendido : (Finset.univ.filter fun s : Interruptores => s = encendido).card = 1 := by decide

/-- … y siete con «intermedios ⟺ P ≠ NP». -/
theorem card_apagado : (Finset.univ.filter fun s : Interruptores => s ≠ encendido).card = 7 := by decide

/-- **El interruptor decide exactamente**: si P ≠ NP, un fragmento tiene dicotomía **si y solo si** los tres
interruptores están encendidos. -/
theorem dicotomia_iff_encendido (H : FederVardi frag csp) (BZ : TieneDicotomia csp) (hPNP : Cslib.Complexity.P encBits ≠ Cslib.Complexity.NP encBits)
    (s : Interruptores) : TieneDicotomia (frag s) ↔ s = encendido := by
  constructor
  · intro hD
    by_contra hs
    exact no_ambas hD ((apagado_iff H hs).mpr hPNP)
  · rintro rfl; exact encendido_dicotomia H BZ

/-- Y si P = NP, el interruptor no decide nada: los ocho fragmentos tienen dicotomía y ninguno intermedios. -/
theorem todos_dicotomia_de_P_eq_NP (H : FederVardi frag csp) (hPNP : Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits) (s : Interruptores) :
    TieneDicotomia (frag s) ∧ ¬ TieneIntermedios (frag s) :=
  ⟨dicotomia_de_P_eq_NP hPNP (H.enNP s), fun h => P_ne_NP_de_intermedios h hPNP⟩

/-! ## 4. El caso booleano: Schaefer en lugar de Bulatov–Zhuk -/

section Booleano

open Sagitta.Map.Informacion.Polimorfismos (Relaciones Polimorfismo tresSAT)
open Sagitta.Map.Borde.DicotomiaBooleana (Supuestos TieneUnaDeLasSeis DefPP EsencialUnaria naeSAT)

/-- **Lo que falta para Schaefer, sin `P ≠ NP`.** `cspDe Γ` es `CSP(Γ)` como lenguaje (la codificación de las
instancias es un parámetro). Son los campos de `DicotomiaBooleana.Supuestos` con «en P» y «NP-completo» de cslib en
lugar de predicados opacos, **sin** `separa`, y con `enNP` (adivinar la asignación). -/
structure SchaeferSinSeparar (cspDe : Relaciones → Lenguaje) : Prop where
  enNP : ∀ Γ : Relaciones, Γ.Finite → cspDe Γ ∈ Cslib.Complexity.NP encBits
  facil : ∀ Γ : Relaciones, Γ.Finite → TieneUnaDeLasSeis Γ → cspDe Γ ∈ Cslib.Complexity.P encBits
  post : ∀ Γ : Relaciones, ¬ TieneUnaDeLasSeis Γ →
    ∀ (k : ℕ) (f : (Fin k → Bool) → Bool), Polimorfismo Γ f → EsencialUnaria f
  tres : NPComplete encBits (cspDe tresSAT)
  naeC : NPComplete encBits (cspDe naeSAT)
  reduce : ∀ Γ Δ : Relaciones, Γ.Finite → Δ.Finite → NPComplete encBits (cspDe Δ) →
    (∀ R ∈ Δ, ∃ D : DefPP Γ R.1, Function.Injective D.libre ∧ ∀ y, R.2 y ↔ D.Define y) →
      NPComplete encBits (cspDe Γ)

/-- Los CSP booleanos de plantilla finita, como clase. -/
def cspBooleanos (cspDe : Relaciones → Lenguaje) : Clase := {L | ∃ Γ : Relaciones, Γ.Finite ∧ cspDe Γ = L}

/-- **Bulatov–Zhuk en el caso booleano, de Schaefer**: los CSP booleanos finitos tienen dicotomía, sin suponer
`P ≠ NP`. Si P = NP, todo está en P; si no, `separa` sale de `NPComplete.P_eq_NP_of_mem_P` y se usa
`DicotomiaBooleana.dicotomia`. -/
theorem schaefer_da_BZ_booleano {cspDe : Relaciones → Lenguaje} (H : SchaeferSinSeparar cspDe) :
    TieneDicotomia (cspBooleanos cspDe) := by
  rintro L ⟨Γ, hΓ, rfl⟩
  by_cases hPNP : Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits
  · exact Or.inl (hPNP ▸ H.enNP Γ hΓ)
  · have S : Supuestos (fun Γ => cspDe Γ ∈ Cslib.Complexity.P encBits) (fun Γ => NPComplete encBits (cspDe Γ)) :=
      { facil := H.facil
        post := H.post
        tres := H.tres
        naeC := H.naeC
        reduce := H.reduce
        separa := fun _ hn hp => hPNP (hn.P_eq_NP_of_mem_P hp encBits) }
    rcases Sagitta.Map.Borde.DicotomiaBooleana.dicotomia S Γ hΓ with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1

/-- **(a) en el caso booleano, sin la hipótesis BZ**: una clase cuyos problemas son equivalentes a CSP booleanos
finitos tiene dicotomía, módulo solo `SchaeferSinSeparar`. -/
theorem booleano_dicotomia {cspDe : Relaciones → Lenguaje} (H : SchaeferSinSeparar cspDe) {F : Clase}
    (hF : ∀ L ∈ F, ∃ C ∈ cspBooleanos cspDe, Equivalentes L C) : TieneDicotomia F :=
  dicotomia_de_equivalentes (schaefer_da_BZ_booleano H) hF

/-- El teorema de los interruptores con plantillas booleanas: si el `csp` de Feder–Vardi son los CSP booleanos,
(a) sale sin BZ. (Para MMSNP entero no basta: sus plantillas no son booleanas.) -/
theorem encendido_dicotomia_booleano {cspDe : Relaciones → Lenguaje} (HS : SchaeferSinSeparar cspDe)
    (H : FederVardi frag (cspBooleanos cspDe)) : TieneDicotomia (frag encendido) :=
  encendido_dicotomia H (schaefer_da_BZ_booleano HS)

end Booleano

/- Mutantes probados (25 nov 2026, fuera del repositorio); los seis fallan:
1. (b) sin pedir que el interruptor esté apagado (`captura_de_apagado` para todo `s`): la esquina (1,1,1) no la cubre
   ninguna de las tres capturas de Feder–Vardi; `Impone sinD encendido` es falso y `simp` no cierra.
2. (a) con solo la ida `L ≤ₚ C` (la reducción determinista de Feder–Vardi, sin la vuelta de Kun): el lado «en P» sale,
   el lado «NP-completo» no (la dificultad no sube por la ida).
3. Ser intermedio con una sola reducción `L ≤ₚ L'`: ni «en NP» ni «no NP-completo» pasan de `L` a `L'`.
4. `dicotomia_iff_encendido` sin `P ≠ NP`: la dirección (⟹) pide el intermedio y no hay de dónde sacarlo.
5. `completo_iff_no_trivial` sin `P = NP`: lo no trivial de NP no se vuelve NP-completo.
6. La cuenta con seis combinaciones apagadas en lugar de siete: `decide` la refuta. -/

end Sagitta.Map.Borde.TresInterruptores
