import Sagitta.Map.Infinito
import Sagitta.Map.CookS12

/-!
# El relleno: SAT enmarcado no se deja hacer la trampa de los largos pares

En `Infinito.lean`, `existe_solo_en_el_limite` da un problema con un circuito de una compuerta en un largo infinito y
que aun así está fuera de P/poly. Funciona porque sus largos pares (triviales) no tienen relación con los impares
(difíciles). SAT no es así: una fórmula corta se **rellena** hasta un largo mayor sin cambiar la respuesta. Aquí se
mide cuánto obliga eso.

## Lo que se prueba

1. **Fijar entradas cuesta a lo sumo dos compuertas** (`tamMin_fijar`). Si `g` se obtiene de `f` fijando entradas
   (cada entrada de `f` es una entrada de `g` o una constante), el menor circuito de `g` tiene a lo sumo dos compuertas
   más que el de `f`. El circuito se construye en el modelo de `Shannon.lean` (`reetiquetar`): dos compuertas para las
   constantes `false` y `true`, y después las de `f` con los cables reetiquetados (`calcula_reetiquetar`).
2. **Rellenable y denso ⇒ P/poly** (`psobrePoly_de_denso`). `Rellenable L`: para todo `n ≤ m`, la rebanada de `L` en `n`
   se obtiene de la de `m` fijando entradas. Si además los **largos buenos** (donde `sucNat L m ≤ c·(m+1)^k`) son
   polinomialmente densos (desde algún `N`, todo `n` tiene uno entre `n` y `a·(n+1)^b`), `L` está en P/poly. Para un
   problema rellenable vale la equivalencia (`psobrePoly_iff_denso`), y fuera de P/poly hay infinitos **huecos**
   (`fuera_iff_huecos`): para todo polinomio y toda ventana polinomial, infinitos `n` cuya ventana no tiene ningún largo
   bueno. En el lenguaje de `Infinito.lean`, un largo infinito donde la ventana es un hueco (`fuera_iff_huecos_infinitos`).
   El problema de `existe_solo_en_el_limite` no es rellenable (`no_rellenable_soloEnElLimite`).
3. **SAT con relleno.** `satBits` no parece rellenable a todo largo exacto (una cadena que es `encCNF φ` no se alarga
   en un bit cualquiera y sigue siendo el código de una fórmula equivalente; no se prueba que sea imposible), así que se
   toma la variante enmarcada `satMarco w = satBits (unframe w)`: la
   fórmula va enmarcada con `frame` (de cslib-frontier, el mismo de `CookS12.lean`) y lo que sigue al marco se ignora.
   * `satMarco` es rellenable (`rellenable_satMarco`).
   * Las dos reducciones son identidades: `satMarco (frame w ++ u) = satBits w` (`satMarco_frame`) y
     `satBits w = satMarco (frame w)` (`satBits_eq_satMarco`).
   * `satBits` se obtiene de `satMarco` fijando entradas (`satBits_fija_satMarco`), así que si `satMarco` está en
     P/poly, `satBits` también (`satBits_de_satMarco`), y largos buenos densos para `satMarco` dan `satBits ∈ P/poly`
     (`satBits_de_denso`).
   * **La lectura** (`huecos_de_sat`, `huecos_de_sat_infinito`): si `satBits` no está en P/poly, `satMarco` tiene, para
     todo polinomio `c·(m+1)^k` y toda ventana `a·(n+1)^b`, infinitos huecos. **Para SAT, existir solo en el límite exige
     huecos enormes entre largos buenos**: más separados que cualquier polinomio.
4. **La densidad importa** (`control_densidad`, `control_en_el_infinito`). Hay un problema rellenable (`espaciado`) con
   infinitos largos buenos (su óptimo no pasa del largo) que no está en P/poly. Lee los primeros `nivel n` bits de una
   escalera de funciones difíciles de Shannon, y `nivel` solo sube cuando el nivel anterior ya cabe en el largo: los
   saltos quedan separados más que cualquier polinomio, como obliga `psobrePoly_de_denso`.

## Lo que no

* **Nada sobre de qué lado cae SAT.** Los teoremas condicionan en `satBits ∉ P/poly`, que sigue abierto (es más fuerte
  que P ≠ NP).
* **La otra dirección entre las dos versiones de SAT** (`SatMarcoDeSatBits`: `satBits ∈ P/poly ⇒ satMarco ∈ P/poly`)
  queda como `Prop` documentado. Es cierta y conocida (pide un circuito polinomial para `unframe`), pero no se construye
  aquí. Por eso la lectura habla de los huecos de `satMarco`, no de los de `satBits`.
* Los huecos dependen del polinomio y de la ventana: para cada par `(c, k)`, `(a, b)` hay infinitos. No se prueba aquí
  un solo largo infinito que sea hueco para todos los pares a la vez.
* El control usa la elección (`Classical.choose` de Shannon) y su `nivel` no es computable; no es un problema de NP.
-/

namespace Sagitta.Map
namespace Tiempo
namespace Relleno

open Shannon Finitud Infinito

/-! ## 1. Fijar entradas no agranda el circuito más que en dos compuertas -/

/-- Las entradas de `f` leídas desde las de `g`: cada una es una entrada de `g` (`inl`) o una constante (`inr`). -/
def sustituir {n m : ℕ} (σ : Fin m → Fin n ⊕ Bool) (x : Fin n → Bool) : Fin m → Bool :=
  fun i => (σ i).elim x id

/-- `g` **se obtiene de `f` fijando entradas**: cada entrada de `f` es una entrada de `g` o una constante. -/
def SeObtieneFijando {n m : ℕ} (g : (Fin n → Bool) → Bool) (f : (Fin m → Bool) → Bool) : Prop :=
  ∃ σ : Fin m → Fin n ⊕ Bool, ∀ x, g x = f (sustituir σ x)

section Reetiquetar

variable {n m t : ℕ}

/-- Adónde va a dar una entrada de `f` en el circuito nuevo: a la entrada `j` de `g`, o a uno de los dos cables
constantes (`n` vale `false`, `n + 1` vale `true`). -/
def destino (t : ℕ) : Fin n ⊕ Bool → Fin (n + (t + 2))
  | .inl j => ⟨j.val, by omega⟩
  | .inr false => ⟨n, by omega⟩
  | .inr true => ⟨n + 1, by omega⟩

theorem destino_lt (e : Fin n ⊕ Bool) : (destino t e).val < n + 2 := by
  rcases e with j | b
  · simp only [destino]; omega
  · cases b <;> simp [destino]

/-- Los cables del circuito de `f`, en el circuito nuevo: las entradas van a `destino`, la compuerta `k` a la
compuerta `k + 2` (las dos primeras son las constantes). -/
def mapa (σ : Fin m → Fin n ⊕ Bool) (w : Fin (m + t)) : Fin (n + (t + 2)) :=
  if h : w.val < m then destino t (σ ⟨w.val, h⟩) else ⟨w.val - m + n + 2, by have := w.isLt; omega⟩

theorem mapa_entrada (σ : Fin m → Fin n ⊕ Bool) (w : Fin (m + t)) (h : w.val < m) :
    mapa σ w = destino t (σ ⟨w.val, h⟩) := by
  simp [mapa, h]

theorem mapa_val_compuerta (σ : Fin m → Fin n ⊕ Bool) (w : Fin (m + t)) (h : ¬ w.val < m) :
    (mapa σ w).val = w.val - m + n + 2 := by
  simp [mapa, h]

/-- **El circuito reetiquetado**: dos compuertas constantes (`false`, `true`) y después las de `C`, leyendo por `mapa`. -/
def reetiquetar (σ : Fin m → Fin n ⊕ Bool) (C : Circuito m t) : Circuito n (t + 2) :=
  (fun k =>
    if h : k.val < 2 then
      (if k.val = 0 then Op.o else Op.no, ⟨n, by omega⟩, ⟨n, by omega⟩)
    else
      ((C.1 ⟨k.val - 2, by omega⟩).1, mapa σ (C.1 ⟨k.val - 2, by omega⟩).2.1,
        mapa σ (C.1 ⟨k.val - 2, by omega⟩).2.2),
   mapa σ C.2)

variable (σ : Fin m → Fin n ⊕ Bool) (C : Circuito m t)

theorem reetiquetar_cero :
    (reetiquetar σ C).1 ⟨0, by omega⟩ = (Op.o, ⟨n, by omega⟩, ⟨n, by omega⟩) := by
  simp [reetiquetar]

theorem reetiquetar_uno :
    (reetiquetar σ C).1 ⟨1, by omega⟩ = (Op.no, ⟨n, by omega⟩, ⟨n, by omega⟩) := by
  simp [reetiquetar]

theorem reetiquetar_comp (k : Fin t) :
    (reetiquetar σ C).1 ⟨k.val + 2, by omega⟩ = ((C.1 k).1, mapa σ (C.1 k).2.1, mapa σ (C.1 k).2.2) := by
  simp [reetiquetar]

theorem cables_falso (x : Fin n → Bool) :
    cables (reetiquetar σ C) x ⟨n, by omega⟩ = false := by
  have : (⟨n, by omega⟩ : Fin (n + (t + 2))) = cableDe (⟨0, by omega⟩ : Fin (t + 2)) :=
    Fin.ext (by simp [cableDe])
  rw [this, cables_compuerta, reetiquetar_cero]
  simp [lee, Op.aplica]

theorem cables_verdadero (x : Fin n → Bool) :
    cables (reetiquetar σ C) x ⟨n + 1, by omega⟩ = true := by
  have : (⟨n + 1, by omega⟩ : Fin (n + (t + 2))) = cableDe (⟨1, by omega⟩ : Fin (t + 2)) :=
    Fin.ext (by simp [cableDe])
  rw [this, cables_compuerta, reetiquetar_uno]
  simp only [lee, Op.aplica]
  rw [ite_eq_left (by omega), cables_falso]
  rfl

theorem cables_destino (x : Fin n → Bool) (e : Fin n ⊕ Bool) :
    cables (reetiquetar σ C) x (destino t e) = e.elim x id := by
  rcases e with j | b
  · rw [cables_entrada _ _ _ (by simp only [destino]; exact j.isLt)]
    rfl
  · cases b
    · exact cables_falso σ C x
    · exact cables_verdadero σ C x

/-- Cada cable de `C` vale lo mismo que su imagen en el circuito reetiquetado. -/
theorem cables_mapa (x : Fin n → Bool) :
    ∀ j (w : Fin (m + t)), w.val < j →
      cables (reetiquetar σ C) x (mapa σ w) = cables C (sustituir σ x) w := by
  intro j
  induction j with
  | zero => intro w h; omega
  | succ j ih =>
    intro w hw
    by_cases hm : w.val < m
    · rw [mapa_entrada σ w hm, cables_destino, cables_entrada _ _ _ hm]
      rfl
    · let k : Fin t := ⟨w.val - m, by have := w.isLt; omega⟩
      have hw' : w = cableDe k := Fin.ext (by simp only [cableDe, k]; omega)
      have hk : mapa σ w = cableDe (⟨k.val + 2, by have := k.isLt; omega⟩ : Fin (t + 2)) :=
        Fin.ext (by rw [mapa_val_compuerta σ w hm]; simp only [cableDe, k]; omega)
      have key : ∀ a : Fin (m + t),
          lee (reetiquetar σ C) x (k.val + 2) (mapa σ a) = lee C (sustituir σ x) k.val a := by
        intro a
        unfold lee
        by_cases ha : a.val < m + k.val
        · have hlt : (mapa σ a).val < n + (k.val + 2) := by
            by_cases ham : a.val < m
            · rw [mapa_entrada σ a ham]; have := destino_lt (t := t) (σ ⟨a.val, ham⟩); omega
            · rw [mapa_val_compuerta σ a ham]; omega
          rw [ite_eq_left hlt, ite_eq_left ha]
          exact ih a (by simp only [k] at ha; omega)
        · have hge : ¬ (mapa σ a).val < n + (k.val + 2) := by
            have ham : ¬ a.val < m := by omega
            rw [mapa_val_compuerta σ a ham]; omega
          rw [ite_eq_right hge, ite_eq_right ha]
      rw [hk, cables_compuerta, reetiquetar_comp, congrArg (cables C (sustituir σ x)) hw', cables_compuerta]
      dsimp only
      rw [key, key]

/-- **El reetiquetado calcula `f` con las entradas fijadas.** -/
theorem calcula_reetiquetar : calcula (reetiquetar σ C) = fun x => calcula C (sustituir σ x) := by
  funext x
  exact cables_mapa σ C x _ C.2 (Nat.lt_succ_self _)

end Reetiquetar

/-- **Fijar entradas cuesta a lo sumo dos compuertas**: si `g` se obtiene de `f` fijando entradas, su menor circuito
tiene a lo sumo dos compuertas más que el de `f` (las dos constantes). -/
theorem tamMin_fijar {n m : ℕ} {g : (Fin n → Bool) → Bool} {f : (Fin m → Bool) → Bool}
    (h : SeObtieneFijando g f) : tamMin g ≤ tamMin f + 2 := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨t, C, hC, ht⟩ := tamMin_alcanzado f
  rw [ht]
  have hg : calcula (reetiquetar σ C) = g := by
    rw [calcula_reetiquetar, hC]; funext x; exact (hσ x).symm
  exact iInf_le_of_le (t + 2) (iInf_le_of_le (reetiquetar σ C) (iInf_le_of_le hg (by push_cast; rfl)))

/-- Lo mismo, para dos problemas y la sucesión de óptimos. -/
theorem sucNat_fijar {L L' : Problema} {n m : ℕ} (h : SeObtieneFijando (rebanada L n) (rebanada L' m)) :
    sucNat L n ≤ sucNat L' m + 2 := by
  have := tamMin_fijar h
  rw [← sucesion, ← sucesion, sucesion_eq, sucesion_eq] at this
  exact_mod_cast this

/-! ## 2. Rellenable: los largos buenos densos dan P/poly -/

/-- **`L` es rellenable**: para todo `n ≤ m`, la rebanada de `L` en `n` se obtiene de la de `m` fijando entradas. Una
instancia corta se escribe, sin cambiar la respuesta, como una instancia más larga. -/
def Rellenable (L : Problema) : Prop :=
  ∀ n m, n ≤ m → SeObtieneFijando (rebanada L n) (rebanada L m)

/-- En un problema rellenable, el óptimo de un largo acota el de todos los largos menores, más dos. -/
theorem sucNat_le_de_rellenable {L : Problema} (hL : Rellenable L) {n m : ℕ} (h : n ≤ m) :
    sucNat L n ≤ sucNat L m + 2 :=
  sucNat_fijar (hL n m h)

/-- **Largos buenos densos** (desde `N`): para todo `n ≥ N` hay un largo `m` entre `n` y `a·(n+1)^b` donde el óptimo
no pasa de `c·(m+1)^k`. -/
def Denso (L : Problema) (c k a b : ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, ∃ m, n ≤ m ∧ m ≤ a * (n + 1) ^ b ∧ sucNat L m ≤ c * (m + 1) ^ k

/-- La cuenta de `psobrePoly_de_denso`: `c·(m+1)^k + 2` con `m ≤ a·(n+1)^b` es a lo sumo
`(c·(a+1)^k + 2)·(n+1)^(b·k)`. -/
theorem cota_compuesta (c k a b n m : ℕ) (hm : m ≤ a * (n + 1) ^ b) :
    c * (m + 1) ^ k + 2 ≤ (c * (a + 1) ^ k + 2) * (n + 1) ^ (b * k) := by
  have h1 : 1 ≤ (n + 1) ^ b := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (n + 1) ^ (b * k) := Nat.one_le_pow _ _ (by omega)
  have h3 : m + 1 ≤ (a + 1) * (n + 1) ^ b := by nlinarith
  have h4 : (m + 1) ^ k ≤ (a + 1) ^ k * (n + 1) ^ (b * k) := by
    calc (m + 1) ^ k ≤ ((a + 1) * (n + 1) ^ b) ^ k := Nat.pow_le_pow_left h3 k
      _ = (a + 1) ^ k * (n + 1) ^ (b * k) := by rw [mul_pow, ← pow_mul]
  calc c * (m + 1) ^ k + 2 ≤ c * ((a + 1) ^ k * (n + 1) ^ (b * k)) + 2 * (n + 1) ^ (b * k) := by
        have := Nat.mul_le_mul_left c h4; omega
    _ = (c * (a + 1) ^ k + 2) * (n + 1) ^ (b * k) := by ring

/-- **El relleno con largos buenos densos da P/poly.** Si `L` es rellenable y sus largos buenos están a distancia
polinomial, `L` tiene circuitos polinomiales: el circuito del largo `n` es el del largo bueno `m ≥ n`, con las
entradas sobrantes fijadas. -/
theorem psobrePoly_de_denso {L : Problema} (hL : Rellenable L) {c k a b : ℕ} (hD : Denso L c k a b) :
    L ∈ PsobrePoly := by
  obtain ⟨N, hN⟩ := hD
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff]
  refine pol_de_casi (c := c * (a + 1) ^ k + 2) (k := b * k) (N := N) fun n hn => ?_
  obtain ⟨m, hnm, hma, hmc⟩ := hN n hn
  calc sucNat L n ≤ sucNat L m + 2 := sucNat_le_de_rellenable hL hnm
    _ ≤ c * (m + 1) ^ k + 2 := by omega
    _ ≤ _ := cota_compuesta c k a b n m hma

/-- **Para un problema rellenable, P/poly es la densidad de los largos buenos.** -/
theorem psobrePoly_iff_denso {L : Problema} (hL : Rellenable L) :
    L ∈ PsobrePoly ↔ ∃ c k a b, Denso L c k a b := by
  constructor
  · intro h
    rw [psobrePoly_iff_grado, gradoPol_lt_top_iff] at h
    obtain ⟨c, k, hc⟩ := h
    exact ⟨c, k, 1, 1, 0, fun n _ => ⟨n, le_rfl, by simp, hc n⟩⟩
  · rintro ⟨c, k, a, b, hD⟩
    exact psobrePoly_de_denso hL hD

/-- **Un hueco** en `n`: ningún largo entre `n` y `a·(n+1)^b` es bueno para `c·(m+1)^k`. -/
def Hueco (L : Problema) (c k a b n : ℕ) : Prop :=
  ∀ m, n ≤ m → m ≤ a * (n + 1) ^ b → c * (m + 1) ^ k < sucNat L m

/-- **Fuera de P/poly, los huecos son infinitos.** Un problema rellenable está fuera de P/poly si y solo si, para todo
polinomio de calidad `c·(m+1)^k` y toda ventana `a·(n+1)^b`, hay infinitos largos `n` cuya ventana no tiene ningún
largo bueno. -/
theorem fuera_iff_huecos {L : Problema} (hL : Rellenable L) :
    L ∉ PsobrePoly ↔ ∀ c k a b, {n | Hueco L c k a b n}.Infinite := by
  constructor
  · intro hfuera c k a b hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    refine hfuera (psobrePoly_de_denso hL (c := c) (k := k) (a := a) (b := b) ⟨N + 1, fun n hn => ?_⟩)
    by_contra hno
    push Not at hno
    have : n ∈ {n | Hueco L c k a b n} := fun m h1 h2 => hno m h1 h2
    have := hN this
    omega
  · intro h hP
    rw [psobrePoly_iff_grado, gradoPol_lt_top_iff] at hP
    obtain ⟨c, k, hc⟩ := hP
    obtain ⟨n, hn⟩ := (h c k 1 1).nonempty
    have := hn n le_rfl (by simp)
    have := hc n
    omega

/-- **Lo mismo, en el lenguaje de `Infinito.lean`**: fuera de P/poly, para cada polinomio y cada ventana hay un largo
infinito donde la ventana no tiene largos buenos. -/
theorem fuera_iff_huecos_infinitos {L : Problema} (hL : Rellenable L) :
    L ∉ PsobrePoly ↔ ∀ c k a b, ∃ U : Ultrafilter ℕ, LargoInfinito U ∧
      ∀ᶠ n in (U : Filter ℕ), Hueco L c k a b n := by
  rw [fuera_iff_huecos hL]
  exact forall₄_congr fun c k a b => io_iff_largo_infinito _

/-! ### La trampa de los largos pares no se puede hacer con un problema rellenable -/

/-- **Buenos en los largos pares, rellenable ⇒ P/poly.** Todo `n` tiene un largo par en `{n, n+1}`. -/
theorem psobrePoly_de_pares {L : Problema} (hL : Rellenable L) {c k : ℕ}
    (h : ∀ j, sucNat L (2 * j) ≤ c * (2 * j + 1) ^ k) : L ∈ PsobrePoly := by
  refine psobrePoly_de_denso hL (c := c) (k := k) (a := 2) (b := 1) ⟨0, fun n _ => ?_⟩
  rw [pow_one]
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨2 * j, by omega, by omega, h j⟩
  · exact ⟨2 * (j + 1), by omega, by omega, by have := h (j + 1); omega⟩

/-- **El problema de `existe_solo_en_el_limite` no es rellenable.** Su circuito de una compuerta en los largos pares
se rellenaría hasta los impares, y entonces estaría en P/poly. -/
theorem no_rellenable_soloEnElLimite : ¬ Rellenable soloEnElLimite := fun hL =>
  existe_solo_en_el_limite.2 (psobrePoly_de_pares hL (c := 1) (k := 0) fun j =>
    by have := sucNat_par (show (2 * j) % 2 = 0 by omega); simpa using this)

/-! ## 3. SAT con relleno -/

section Sat

open Turing.MultiTapeTM CookS12

/-- Lo que sigue a un prefijo de largo par no le cambia nada a `unframe` si por sí solo desenmarca a vacío. -/
theorem unframe_append_par : ∀ (u v : List Bool), u.length % 2 = 0 → unframe v = [] →
    unframe (u ++ v) = unframe u
  | [], v, _, hv => by simpa [unframe] using hv
  | [_], _, h, _ => by simp at h
  | true :: b :: u, v, h, hv => by
    simp only [List.cons_append, unframe]
    rw [unframe_append_par u v (by simp at h; omega) hv]
  | false :: _ :: _, _, _, _ => by simp [unframe]

theorem unframe_replicate_false : ∀ k, unframe (List.replicate k false) = []
  | 0 => rfl
  | _ + 1 => rfl

theorem unframe_corto : ∀ (v : List Bool), v.length ≤ 1 → unframe v = []
  | [], _ => rfl
  | [true], _ => rfl
  | [false], _ => rfl
  | _ :: _ :: _, h => by simp at h

/-- `unframe` solo lee el prefijo de largo par. -/
theorem unframe_take_par (l : List Bool) : unframe (l.take (2 * (l.length / 2))) = unframe l := by
  conv_rhs => rw [← List.take_append_drop (2 * (l.length / 2)) l]
  refine (unframe_append_par _ _ ?_ (unframe_corto _ ?_)).symm
  · simp only [List.length_take]; rw [min_eq_left (by omega)]; omega
  · simp only [List.length_drop]; omega

/-- **SAT enmarcado con relleno**: la entrada se desenmarca (`unframe`: se lee hasta el primer marcador `false`) y lo
que se lee se le pregunta a `satBits`. Todo lo que sigue al marco se ignora. -/
noncomputable def satMarco : Problema := fun w => satBits (unframe w)

/-- **Las dos reducciones.** `satMarco` es `satBits` después de desenmarcar, y `satBits` es `satMarco` después de
enmarcar (con cualquier relleno detrás). -/
theorem satMarco_frame (w u : List Bool) : satMarco (frame w ++ u) = satBits w := by
  simp [satMarco, unframe_frame_append]

theorem satBits_eq_satMarco (w : List Bool) : satBits w = satMarco (frame w) := by
  simp [satMarco, unframe_frame]

/-- **`satMarco` es rellenable.** Una entrada de `n` bits se lleva a `m ≥ n` bits copiando su prefijo de largo par y
completando con `false`: el desenmarcado no cambia. -/
theorem rellenable_satMarco : Rellenable satMarco := by
  intro n m hnm
  let p := 2 * (n / 2)
  refine ⟨fun i => if h : i.val < p then .inl ⟨i.val, by omega⟩ else .inr false, fun x => ?_⟩
  have hlist : List.ofFn (sustituir (fun i : Fin m => if h : i.val < p then
      (.inl ⟨i.val, by omega⟩ : Fin n ⊕ Bool) else .inr false) x) =
      (List.ofFn x).take p ++ List.replicate (m - p) false := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append, List.length_take, List.length_replicate]
      rw [min_eq_left (by omega)]; omega
    · intro i h1 h2
      simp only [List.getElem_ofFn, sustituir]
      by_cases hi : i < p
      · rw [List.getElem_append_left (by simp only [List.length_take, List.length_ofFn]; omega)]
        simp [hi]
      · rw [List.getElem_append_right (by simp only [List.length_take, List.length_ofFn]; omega)]
        simp [hi]
  change satBits (unframe (List.ofFn x)) = satBits (unframe (List.ofFn _))
  rw [hlist, unframe_append_par _ _ (by simp only [List.length_take, List.length_ofFn]; omega)
    (unframe_replicate_false _)]
  have := unframe_take_par (List.ofFn x)
  rw [List.length_ofFn] at this
  rw [this]

/-- El bit `j` del marco de `w`: los impares son los bits de `w`, los pares son marcadores (`true` mientras quedan
bits, `false` al final). -/
theorem getElem_frame : ∀ (w : List Bool) (j : ℕ) (h : j < (frame w).length),
    (frame w)[j] = if j % 2 = 1 then w.getD (j / 2) false else decide (j < 2 * w.length)
  | [], 0, _ => rfl
  | [], j + 1, h => by simp [frame] at h
  | b :: w, 0, _ => by simp [frame_cons]
  | b :: w, 1, _ => by simp [frame_cons]
  | b :: w, j + 2, h => by
    have h' : j < (frame w).length := by simp only [length_frame, List.length_cons] at h ⊢; omega
    simp only [frame_cons, List.getElem_cons_succ]
    rw [getElem_frame w j h']
    have e1 : (j + 2) % 2 = j % 2 := by omega
    have e2 : (j + 2) / 2 = j / 2 + 1 := by omega
    rw [e1, e2, List.getD_cons_succ]
    congr 1

/-- **`satBits` se obtiene de `satMarco` fijando entradas**: la rebanada de `n` bits de `satBits` es la de `2n+1`
de `satMarco` con los marcadores fijados. -/
theorem satBits_fija_satMarco (n : ℕ) :
    SeObtieneFijando (rebanada satBits n) (rebanada satMarco (2 * n + 1)) := by
  refine ⟨fun j => if h : j.val % 2 = 1 then .inl ⟨j.val / 2, by omega⟩
    else .inr (decide (j.val < 2 * n)), fun x => ?_⟩
  change satBits (List.ofFn x) = satBits (unframe (List.ofFn _))
  have hlist : List.ofFn (sustituir (fun j : Fin (2 * n + 1) => if h : j.val % 2 = 1 then
      (.inl ⟨j.val / 2, by omega⟩ : Fin n ⊕ Bool) else .inr (decide (j.val < 2 * n))) x) =
      frame (List.ofFn x) := by
    apply List.ext_getElem
    · simp [length_frame]
    · intro i h1 h2
      rw [getElem_frame]
      simp only [List.getElem_ofFn, sustituir, List.length_ofFn]
      by_cases hi : i % 2 = 1
      · simp only [hi, ↓reduceIte]
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn] at h1 ⊢; omega)]
        simp
      · simp [hi]
  rw [hlist, unframe_frame]

/-- El óptimo de `satBits` en `n` bits no pasa del de `satMarco` en `2n+1`, más dos. -/
theorem sucNat_satBits_le (n : ℕ) : sucNat satBits n ≤ sucNat satMarco (2 * n + 1) + 2 :=
  sucNat_fijar (satBits_fija_satMarco n)

/-- **Si `satMarco` está en P/poly, `satBits` también.** -/
theorem satBits_de_satMarco (h : satMarco ∈ PsobrePoly) : satBits ∈ PsobrePoly := by
  rw [psobrePoly_iff_grado, gradoPol_lt_top_iff] at h ⊢
  obtain ⟨c, k, hc⟩ := h
  refine ⟨2 ^ k * c + 2, k, fun n => ?_⟩
  have h1 := sucNat_satBits_le n
  have h2 := hc (2 * n + 1)
  have h3 : (2 * n + 1 + 1) ^ k ≤ 2 ^ k * (n + 1) ^ k := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) k
  have h4 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  calc sucNat satBits n ≤ c * (2 ^ k * (n + 1) ^ k) + 2 := by
        have := Nat.mul_le_mul_left c h3; omega
    _ ≤ (2 ^ k * c + 2) * (n + 1) ^ k := by nlinarith

/-- **SAT, con relleno y largos buenos densos, está en P/poly.** -/
theorem satBits_de_denso {c k a b : ℕ} (hD : Denso satMarco c k a b) : satBits ∈ PsobrePoly :=
  satBits_de_satMarco (psobrePoly_de_denso rellenable_satMarco hD)

/-- **La lectura.** Si `satBits` no tiene circuitos polinomiales, `satMarco` tiene, para todo polinomio y toda ventana
polinomial, infinitos huecos: largos `n` tales que ningún largo entre `n` y `a·(n+1)^b` tiene un circuito de tamaño
`c·(m+1)^k`. Existir solo en el límite, para SAT, exige huecos enormes entre largos buenos. -/
theorem huecos_de_sat (h : satBits ∉ PsobrePoly) (c k a b : ℕ) :
    {n | Hueco satMarco c k a b n}.Infinite :=
  (fuera_iff_huecos rellenable_satMarco).1 (fun hm => h (satBits_de_satMarco hm)) c k a b

/-- Lo mismo con un largo infinito: para cada polinomio y cada ventana, uno donde la ventana es un hueco. -/
theorem huecos_de_sat_infinito (h : satBits ∉ PsobrePoly) (c k a b : ℕ) :
    ∃ U : Ultrafilter ℕ, LargoInfinito U ∧ ∀ᶠ n in (U : Filter ℕ), Hueco satMarco c k a b n :=
  (io_iff_largo_infinito _).1 (huecos_de_sat h c k a b)

/-- **Abierto aquí (cierto y conocido): la otra dirección.** Si `satBits` tiene circuitos polinomiales, `satMarco`
también. Pide un circuito polinomial para `unframe` (encontrar el primer marcador `false` y llevar los bits leídos a
las entradas de `satBits` del largo que corresponda) en el modelo de `Shannon.lean`. No se construye aquí; por eso
los teoremas de arriba hablan de `satMarco` y solo bajan a `satBits` en la dirección probada. -/
def SatMarcoDeSatBits : Prop := satBits ∈ PsobrePoly → satMarco ∈ PsobrePoly

end Sat

/-! ## 4. Control: sin densidad, el relleno no alcanza -/

section Control

/-- Quitar los `false` del final. -/
def recorte (y : List Bool) : List Bool := y.rdropWhile (fun b => !b)

theorem recorte_append_replicate (y : List Bool) :
    ∀ k, recorte (y ++ List.replicate k false) = recorte y
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ', ← List.append_assoc]
    unfold recorte
    rw [List.rdropWhile_concat_pos _ _ _ rfl]
    exact recorte_append_replicate y k

theorem recorte_concat_true (y : List Bool) : recorte (y ++ [true]) = y ++ [true] :=
  List.rdropWhile_concat_neg _ _ _ (by simp)

/-- **Una escalera de funciones difíciles**: si el último `true` de `y` está en la posición `p`, la función difícil
de Shannon de `p` bits sobre los bits anteriores; si no hay ninguno, `false`. No cambia al agregar `false` al final. -/
noncomputable def escalera : Problema := fun y =>
  if recorte y = [] then false else dificilEn ((recorte y).length - 1) (recorte y)

theorem escalera_append (y : List Bool) (k : ℕ) : escalera (y ++ List.replicate k false) = escalera y := by
  simp only [escalera, recorte_append_replicate]

theorem escalera_concat_true {n : ℕ} (x : Fin n → Bool) : escalera (List.ofFn x ++ [true]) = dificil n x := by
  have hr := recorte_concat_true (List.ofFn x)
  have hne : recorte (List.ofFn x ++ [true]) ≠ [] := by rw [hr]; simp
  unfold escalera
  rw [ite_eq_right hne, hr]
  rw [show (List.ofFn x ++ [true]).length - 1 = n by simp, dificilEn]
  congr 1
  funext i
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [List.getElem_append_left]

/-- **El nivel**: cuántos bits lee el problema de control en las entradas de `n` bits. Sube hasta `n + 1` solo cuando
el nivel anterior ya cabe en `n` compuertas (más dos); si no, se queda. Así los saltos quedan muy separados. -/
noncomputable def nivel : ℕ → ℕ
  | 0 => 0
  | n + 1 => if sucNat escalera (nivel n) + 2 ≤ n then n + 1 else nivel n

theorem nivel_succ (n : ℕ) :
    nivel (n + 1) = if sucNat escalera (nivel n) + 2 ≤ n then n + 1 else nivel n := rfl

theorem nivel_le : ∀ n, nivel n ≤ n
  | 0 => le_rfl
  | n + 1 => by
    rw [nivel_succ]
    have := nivel_le n
    split <;> omega

theorem nivel_mono : Monotone nivel :=
  monotone_nat_of_le_succ fun n => by
    rw [nivel_succ]
    have := nivel_le n
    split <;> omega

/-- **El problema de control**: en las entradas de `n` bits, la escalera sobre los primeros `nivel n` bits. -/
noncomputable def espaciado : Problema := fun x => escalera (x.take (nivel x.length))

theorem rebanada_espaciado {n : ℕ} (x : Fin n → Bool) :
    rebanada espaciado n x = escalera ((List.ofFn x).take (nivel n)) := by
  simp [rebanada, espaciado]

/-- **El control es rellenable**: se copian los primeros `nivel n` bits y se completa con `false`. -/
theorem rellenable_espaciado : Rellenable espaciado := by
  intro n m hnm
  have hn := nivel_le n
  have hm := nivel_le m
  have hmono := nivel_mono hnm
  let σ : Fin m → Fin n ⊕ Bool := fun i =>
    if h : i.val < nivel n then .inl ⟨i.val, by omega⟩ else .inr false
  refine ⟨σ, fun x => ?_⟩
  rw [rebanada_espaciado, rebanada_espaciado]
  have hlist : (List.ofFn (sustituir σ x)).take (nivel m) =
      (List.ofFn x).take (nivel n) ++ List.replicate (nivel m - nivel n) false := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn, List.length_append, List.length_replicate]
      rw [min_eq_left hm, min_eq_left hn]; omega
    · intro i h1 h2
      simp only [List.length_take, List.length_ofFn] at h1
      rw [List.getElem_take, List.getElem_ofFn]
      simp only [sustituir, σ]
      by_cases hi : i < nivel n
      · rw [List.getElem_append_left (by simp only [List.length_take, List.length_ofFn]; omega)]
        simp [hi]
      · rw [List.getElem_append_right (by simp only [List.length_take, List.length_ofFn]; omega)]
        simp [hi]
  rw [hlist, escalera_append]

/-- En `n` bits, el control cuesta lo que la escalera en `nivel n` bits, más dos. -/
theorem sucNat_espaciado_le (n : ℕ) : sucNat espaciado n ≤ sucNat escalera (nivel n) + 2 := by
  have hn := nivel_le n
  refine sucNat_fijar ⟨fun i => .inl ⟨i.val, by omega⟩, fun x => ?_⟩
  rw [rebanada_espaciado]
  change escalera _ = escalera _
  congr 1
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]; omega
  · intro i h1 h2
    simp [sustituir]

/-- Donde el nivel salta a `n + 1`, el control contiene la función difícil de `n` bits. -/
theorem dificil_fija_espaciado {n : ℕ} (h : nivel (n + 1) = n + 1) :
    SeObtieneFijando (dificil n) (rebanada espaciado (n + 1)) := by
  refine ⟨fun i => if hi : i.val < n then .inl ⟨i.val, hi⟩ else .inr true, fun x => ?_⟩
  rw [rebanada_espaciado, h]
  have hlist : List.ofFn (sustituir (fun i : Fin (n + 1) =>
      if hi : i.val < n then (.inl ⟨i.val, hi⟩ : Fin n ⊕ Bool) else .inr true) x) = List.ofFn x ++ [true] := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_ofFn] at h1
      rw [List.getElem_ofFn]
      by_cases hi : i < n
      · rw [List.getElem_append_left (by simp; omega)]
        simp [sustituir, hi]
      · rw [List.getElem_append_right (by simp; omega)]
        simp [sustituir, hi]
  rw [List.take_of_length_le (by simp), hlist, escalera_concat_true]

/-- **Los saltos no se acaban**: para todo `N` hay un `n ≥ N` donde el nivel cabe en `n` compuertas (y salta). -/
theorem saltos (N : ℕ) : ∃ n ≥ N, sucNat escalera (nivel n) + 2 ≤ n := by
  by_contra h
  push Not at h
  have hcte : ∀ n ≥ N, nivel n = nivel N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [nivel_succ, ite_eq_right (by have := h n hn; omega), ih]
  set n := N + sucNat escalera (nivel N) + 2
  have := h n (by omega)
  rw [hcte n (by omega)] at this
  omega

/-- **Control de la densidad.** Hay un problema rellenable con infinitos largos buenos (su circuito óptimo no pasa del
largo) que no está en P/poly. Sus largos buenos son los saltos del nivel, separados más que cualquier polinomio
(por `psobrePoly_de_denso`, no puede ser de otra forma). Sin la hipótesis de densidad, el teorema es falso. -/
theorem control_densidad :
    Rellenable espaciado ∧ {m | sucNat espaciado m ≤ 1 * (m + 1) ^ 1}.Infinite ∧ espaciado ∉ PsobrePoly := by
  refine ⟨rellenable_espaciado, ?_, ?_⟩
  · refine Set.infinite_of_forall_exists_gt fun a => ?_
    obtain ⟨n, hn, hb⟩ := saltos (a + 1)
    refine ⟨n, ?_, by omega⟩
    have := sucNat_espaciado_le n
    simp only [Set.mem_ofPred_eq, pow_one, one_mul]
    omega
  · rw [psobrePoly_iff_grado, gradoPol_lt_top_iff]
    rintro ⟨c, k, hc⟩
    obtain ⟨N, hN⟩ := pol_menor_dos_pow (8 * (c + 2) * 2 ^ k) (k + 1)
    obtain ⟨n, hn, hb⟩ := saltos (N + 5)
    have hsalto : nivel (n + 1) = n + 1 := by rw [nivel_succ, ite_eq_left hb]
    have hn5 : 5 ≤ n := by omega
    -- Abajo: la función difícil de `n` bits.
    have hdif : ((2 ^ n / (8 * n) : ℕ) : ℕ∞) < sucesion espaciado (n + 1) + 2 := by
      have h1 := tamMin_fijar (dificil_fija_espaciado hsalto)
      have h2 : ((2 ^ n / (8 * n) : ℕ) : ℕ∞) < tamMin (dificil n) := by
        simp only [dificil, hn5, ↓reduceDIte]
        exact Classical.choose_spec (existe_funcion_exponencial n hn5)
      exact h2.trans_le h1
    rw [sucesion_eq] at hdif
    have hdif' : 2 ^ n / (8 * n) < sucNat espaciado (n + 1) + 2 := by exact_mod_cast hdif
    -- Arriba: el polinomio.
    have hup := hc (n + 1)
    have h3 : (n + 1 + 1) ^ k ≤ 2 ^ k * (n + 1) ^ k := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) k
    have h4 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    have h5 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hX : c * (n + 1 + 1) ^ k + 2 ≤ (c + 2) * 2 ^ k * (n + 1) ^ k := by
      have := Nat.mul_le_mul_left c h3
      have : 1 ≤ 2 ^ k * (n + 1) ^ k := Nat.one_le_iff_ne_zero.2 (by positivity)
      nlinarith
    have hY : (c + 2) * 2 ^ k * (n + 1) ^ k * (8 * n) < 2 ^ n := by
      have := hN n (by omega)
      calc (c + 2) * 2 ^ k * (n + 1) ^ k * (8 * n) ≤ 8 * (c + 2) * 2 ^ k * (n + 1) ^ (k + 1) := by
            rw [pow_succ]
            have : n ≤ n + 1 := by omega
            have := Nat.mul_le_mul_left ((c + 2) * 2 ^ k * (n + 1) ^ k * 8) this
            nlinarith
        _ < 2 ^ n := this
    have hZ : (c + 2) * 2 ^ k * (n + 1) ^ k ≤ 2 ^ n / (8 * n) :=
      (Nat.le_div_iff_mul_le (by omega)).2 hY.le
    omega

/-- El control, en el lenguaje de `Infinito.lean`: un largo infinito donde el circuito óptimo no pasa del largo, y
aun así fuera de P/poly. Como `existe_solo_en_el_limite`, pero con un problema rellenable. -/
theorem control_en_el_infinito :
    Rellenable espaciado ∧ (∃ U : Ultrafilter ℕ, LargoInfinito U ∧
      ∀ᶠ m in (U : Filter ℕ), sucNat espaciado m ≤ 1 * (m + 1) ^ 1) ∧ espaciado ∉ PsobrePoly := by
  obtain ⟨h1, h2, h3⟩ := control_densidad
  exact ⟨h1, (io_iff_largo_infinito _).1 h2, h3⟩

end Control

end Relleno
end Tiempo
end Sagitta.Map
