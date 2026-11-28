import Sagitta.Map.PreguntaNP
import Sagitta.Map.MientrasMaquina
import Sagitta.Map.Vara

/-!
# La otra dirección: si NP ⊆ P, el destino se halla en tiempo polinomial

`Vara.np_al_algoritmo_estandar` probó que decidir un lenguaje de NP se reduce a hallar el destino de un descenso de
tiempo polinomial. Aquí va la vuelta: **si todo lenguaje de NP está en P, el destino del descenso exhaustivo se halla
en tiempo polinomial** (`destino_polinomial`). Juntas dan una equivalencia (`verificarImplicaResolver_iff`).

**Qué se sabía.** El lema 1 de Johnson, Papadimitriou y Yannakakis (1988, p. 83) da la ida para un problema de su
clase, y su lema 2 (p. 84) dice que hallar *alguna* solución de un problema de búsqueda de NP es fácil si y solo si
P = NP; cslib-frontier lo formaliza (`FNP_subset_FPSearch_iff`). Aquí hace falta la *primera* solución en un orden
fijo, que sale con la búsqueda por prefijos de manual. Lo de este repo es la formalización, sobre las máquinas
`FinTM2` de Mathlib.

**La máquina.** Dos bucles `mientras` (`MientrasMaquina.lean`) seguidos:

1. el del largo mínimo, desde `(x, (vara, vara))`;
2. el de los bits, desde `(x, (largo mínimo, []))`.

Cada paso hace una pregunta de NP (`PreguntaNP.preg`), que por hipótesis se contesta en tiempo polinomial. Que el
resultado es el destino lo prueba `BusquedaPrefijos.destinoBusqueda_eq`.
-/

namespace Sagitta.Map
namespace OtraDireccion

open PreguntaNP BusquedaPrefijos Bucle
open ExhaustivoTiempo (exhaustivoVara)

variable {pr : List Bool × (List Bool × List Bool) → Bool}

/-- El bucle de la fase 1, con combustible `n + 1`, es de tiempo polinomial. -/
theorem esPolinomial_bucle1 (hpr : EsPolinomial pr) :
    EsPolinomial (fun a : Estado => mientras (paso1 pr) ((Polynomial.X + 1).eval (CodBits.cod a).length) a) :=
  MientrasMaquina.esPolinomial_mientras (paso1 pr) (esPolinomial_paso1 pr hpr) (Polynomial.X + 1)
    (Polynomial.C 2 * Polynomial.X)
    (fun a => by simpa using para_paso1 (pr := pr) a)
    (fun a k _ => by simpa using largo_paso1 (pr := pr) a k)

/-- El bucle de la fase 2, con combustible `n + 1`, es de tiempo polinomial. -/
theorem esPolinomial_bucle2 (hpr : EsPolinomial pr) :
    EsPolinomial (fun a : Estado => mientras (paso2 pr) ((Polynomial.X + 1).eval (CodBits.cod a).length) a) :=
  MientrasMaquina.esPolinomial_mientras (paso2 pr) (esPolinomial_paso2 pr hpr) (Polynomial.X + 1) Polynomial.X
    (fun a => by simpa using para_paso2 (pr := pr) a)
    (fun a k _ => by simpa using largo_paso2 (pr := pr) a k)

/-- **La búsqueda, como composición de máquinas**: armar el estado inicial, correr la fase 1, pasar al estado de la
fase 2, correrla y quedarse con lo que se llevaba. -/
noncomputable def busqueda (pr : List Bool × (List Bool × List Bool) → Bool) (tope : List Bool → List Bool)
    (x : List Bool) : List Bool :=
  let fase1 := fun a : Estado => mientras (paso1 pr) ((Polynomial.X + 1).eval (CodBits.cod a).length) a
  let fase2 := fun a : Estado => mientras (paso2 pr) ((Polynomial.X + 1).eval (CodBits.cod a).length) a
  let s := fase1 (x, (tope x, tope x))
  (fase2 (s.1, (s.2.2, ([] : List Bool)))).2.2

theorem esPolinomial_busqueda (hpr : EsPolinomial pr) {tope : List Bool → List Bool} (htope : EsPolinomial tope) :
    EsPolinomial (busqueda pr tope) := by
  have hini : EsPolinomial (fun x : List Bool => (x, (tope x, tope x))) := pp esPolinomial_id (pp htope htope)
  have hmed : EsPolinomial (fun s : Estado => (s.1, (s.2.2, ([] : List Bool)))) :=
    pp p1 (pp (pc p2 p2) ExhaustivoTiempo.esPolinomial_vacia)
  have hfin : EsPolinomial (fun s : Estado => s.2.2) := pc p2 p2
  have H := pc (pc (pc hini (esPolinomial_bucle1 hpr)) hmed) (esPolinomial_bucle2 hpr)
  exact pc (g := fun s : Estado => s.2.2) H hfin

/-- Con combustible de sobra, la composición es la búsqueda en dos fases. -/
theorem busqueda_eq (tope : List Bool → List Bool) (x : List Bool) :
    busqueda pr tope x = destinoBusqueda pr tope x := by
  have h1 := mientras_paso1 (pr := pr) x (tope x) (tope x)
    ((Polynomial.X + 1).eval (CodBits.cod (x, (tope x, tope x))).length)
    (by simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]; rw [largo_cod]; dsimp only; omega)
  set R := largoMin pr x (tope x) (tope x)
  have h2 := mientras_paso2 (pr := pr) x R []
    ((Polynomial.X + 1).eval (CodBits.cod (x, (R, ([] : List Bool)))).length)
    (by simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]; rw [largo_cod]; simp; omega)
  simp only [busqueda]
  rw [h1]
  simp only
  rw [h2]
  rfl

/-- **La otra dirección.** Si todo lenguaje de NP está en P, el destino del descenso exhaustivo de un verificador
polinomial, con una vara polinomial, se halla en tiempo polinomial. -/
theorem destino_polinomial (hNP : VerificarImplicaResolver) {V : List Bool × List Bool → Bool}
    (hV : EsPolinomial V) {tope : List Bool → List Bool} (htope : EsPolinomial tope) :
    EsPolinomial (exhaustivoVara V tope).destino := by
  have e : (exhaustivoVara V tope).destino = busqueda (preg V) tope := by
    funext x
    rw [busqueda_eq, destinoBusqueda_eq (contesta V)]
  rw [e]
  exact esPolinomial_busqueda (esPolinomial_preg V hNP hV) htope

/-- Lo mismo, con la hipótesis P = NP. -/
theorem destino_polinomial_de_pIgualNP (h : PIgualNP) {V : List Bool × List Bool → Bool}
    (hV : EsPolinomial V) {tope : List Bool → List Bool} (htope : EsPolinomial tope) :
    EsPolinomial (exhaustivoVara V tope).destino := by
  refine destino_polinomial (fun L hL => ?_) hV htope
  unfold PIgualNP at h
  rw [h]; exact hL

/-- **Las dos direcciones juntas.** Todo lenguaje de NP está en P si y solo si el destino de todo descenso exhaustivo
polinomial se halla en tiempo polinomial. La vuelta usa `np_por_destino_polinomial`: un lenguaje de NP se decide
mirando si el verificador acepta el destino. -/
theorem verificarImplicaResolver_iff :
    VerificarImplicaResolver ↔
      ∀ (V : List Bool × List Bool → Bool) (tope : List Bool → List Bool),
        EsPolinomial V → EsPolinomial tope → EsPolinomial (exhaustivoVara V tope).destino := by
  refine ⟨fun hNP V tope hV htope => destino_polinomial hNP hV htope, fun h L hL => ?_⟩
  obtain ⟨p, W, hW, hiff⟩ := hL
  obtain ⟨tope, htope, hlargo⟩ := Vara.tieneVara p
  have hdec := (ExhaustivoTiempo.np_por_destino_polinomial hW htope hlargo hiff).2
  have hD := h W tope hW htope
  have e : L = fun x => W (x, (exhaustivoVara W tope).destino x) :=
    funext fun x => Bool.eq_iff_iff.mpr (hdec x)
  show EsPolinomial L
  rw [e]
  exact pc (pp esPolinomial_id hD) hW

end OtraDireccion
end Sagitta.Map
