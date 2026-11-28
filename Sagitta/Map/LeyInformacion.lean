import Sagitta.Map.ProfundidadLogica
import Sagitta.Map.UniversoCerrado
import Sagitta.Map.ConservacionTrabajo
import Sagitta.Map.HuevoGallina
import Sagitta.Map.DosCuentas
import Sagitta.Map.TerceraCuenta

/-!
# La ley de la información: nunca es gratis, alguien la pagó, una vez

La frase es de José (24 nov 2026): **«la información nunca es gratis, alguien paga por ella»**. Este módulo no prueba
nada nuevo salvo la amortización: junta, con un nombre cada uno, los teoremas del proyecto que dicen lo mismo desde cinco
lados, y agrega la precisión de que la información se paga **una vez** y después se copia.

## La ley, en cinco caras (alias de teoremas ya probados)

| Cara | Alias | Teorema original |
|---|---|---|
| El cálculo no crea información | `calculo_no_crea` | `ProfundidadLogica.K_no_crece` |
| Si entra gratis de afuera, el universo cerrado se rompe | `gratis_rompe_cerrado` | `UniversoCerrado.tabla_rompe` |
| Una tabla regalada rompe la conservación del trabajo | `gratis_rompe_conservacion` | `ConservacionTrabajo.tabla_gratis_rompe` |
| Quien resuelve le debe al creador su información | `se_debe_al_creador` | `HuevoGallina.paga_la_informacion` |
| Lo escrito una vez no informa nada por instancia | `una_vez_no_informa_nada` | `DosCuentas.una_vez_no_informa` |
| Justificar un «no» también cuesta | `justificar_cuesta` | `TerceraCuenta.terceraCuenta_palomar` |

## Lo nuevo: la amortización (contabilidad declarada)

Una vez pagada, la información se **copia**: una tabla de costo `T` que sirve para `M` consultas, cada una de costo `r`,
cuesta en total `T + M · r` (`total_amortizado`), nunca menos que `T` (`alguien_pago`), y su costo medio por consulta
baja hacia `r` (`medio_baja`, `medio_tiende`): el precio de la información por consulta tiende a cero, pero el total
nunca. Es la única salida legítima que se encontró: **amortizar**, no esquivar.

## La forma completa

> La información nunca es gratis: alguien la pagó, una vez. El cálculo no la crea; solo la mueve, la copia o la
> extrae.

«Extraer» es donde vive `P` contra `NP`: la fórmula de SAT ya contiene la información de su solución (nadie tiene que
volver a pagarla), pero sacarla puede costar tiempo. Eso es la profundidad (`ProfundidadLogica`), no la información.

## Lo que NO se prueba

* La amortización es contabilidad declarada: no hay un modelo de cómputo donde la tabla se escriba y se lea.
* En caja negra (`una_vez_no_informa_nada`) una tabla escrita una vez **no** ayuda a instancias con soluciones
  distintas: la amortización sirve cuando muchas consultas preguntan sobre **el mismo** dato (como en `PlanoCaja`), no
  cuando cada instancia esconde otro.
* Todo relativiza salvo lo que se diga lo contrario; nada sobre `P` contra `NP`.
-/

namespace Sagitta.Map.Tiempo.LeyInformacion

open Sagitta.Map.Tiempo

alias calculo_no_crea := ProfundidadLogica.K_no_crece
alias gratis_rompe_cerrado := UniversoCerrado.tabla_rompe
alias gratis_rompe_conservacion := ConservacionTrabajo.tabla_gratis_rompe
alias se_debe_al_creador := HuevoGallina.paga_la_informacion
alias una_vez_no_informa_nada := DosCuentas.una_vez_no_informa
alias justificar_cuesta := TerceraCuenta.terceraCuenta_palomar

/-! ## La amortización -/

/-- **El costo total**: una tabla de costo `T`, pagada una vez, más `M` consultas de costo `r`. -/
def total (T M r : ℕ) : ℕ := T + M * r

/-- **Alguien pagó**: el total nunca baja del costo de la tabla, por más consultas que la compartan. -/
theorem alguien_pago (T M r : ℕ) : T ≤ total T M r := Nat.le_add_right _ _

/-- **Sin la tabla, cada consulta paga entera**: si cada consulta tuviera que pagar `T` por su cuenta, el total sería
`M · (T + r)`; compartida, es `T + M · r`. -/
theorem total_amortizado (T M r : ℕ) (hM : 1 ≤ M) : total T M r ≤ M * (T + r) := by
  unfold total
  rw [Nat.mul_add]
  have : T ≤ M * T := Nat.le_mul_of_pos_left T hM
  omega

/-- **El costo medio baja**: `total / M ≤ r + T / M` (en ℚ). -/
theorem medio_baja (T M r : ℕ) (hM : 0 < M) :
    (total T M r : ℚ) / M = r + (T : ℚ) / M := by
  unfold total
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp
  ring

/-- **El precio por consulta de la información tiende a cero**: para todo `ε > 0` hay un `M₀` desde el cual
`T / M < ε`. El total, en cambio, nunca baja de `T` (`alguien_pago`). -/
theorem medio_tiende (T : ℕ) (ε : ℚ) (hε : 0 < ε) : ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < M → (T : ℚ) / M < ε := by
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt ((T : ℚ) / ε)
  refine ⟨M₀, fun M hM hpos => ?_⟩
  have hMq : (M₀ : ℚ) ≤ M := by exact_mod_cast hM
  have hpos' : (0 : ℚ) < M := by exact_mod_cast hpos
  rw [div_lt_iff₀ hpos']
  have := (div_lt_iff₀ hε).1 (lt_of_lt_of_le hM₀ hMq)
  linarith

/-- **Control: con una sola consulta no hay amortización**: el total es la tabla más la consulta. -/
theorem una_consulta (T r : ℕ) : total T 1 r = T + r := by simp [total]

/-- **Control: la tabla no se esfuma**: aun con infinitas consultas, el total es al menos `T`. -/
theorem no_se_esfuma (T r : ℕ) : ∀ M, T ≤ total T M r := fun M => alguien_pago T M r

end Sagitta.Map.Tiempo.LeyInformacion
