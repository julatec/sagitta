import Sagitta.Map.Jerarquia
import Sagitta.Map.Decidir

/-!
# Verificar contra resolver: en la cebolla y en Landau

Dónde caen, en la cebolla de `Jerarquia.lean`, el costo de **verificar** (te dan las elecciones: se suman) y el de
**resolver** buscando (cada elección multiplica las ramas: se componen), y qué regla los separa.

## Lo que se prueba

* **El resolvedor sale de la capa lineal**: `2ⁿ ∉ Capa 1` (`dos_pow_no_capa_uno`), y lo mismo con una elección cada
  `k` pasos, el «`1 + ε`» con `ε = 1/k`: `2^(n/k) ∉ Capa 1` (`rala_no_capa_uno`). Leer el certificado, `n/k`, sí está
  en la capa 1 (`rala_certificado_capa_uno`).
* **Pero la cebolla no separa P de Exp**: `2ⁿ ∈ Capa 2` (`dos_pow_capa_dos`) y todo `Exp ⊆ Capa 2`
  (`exp_sub_capa_dos`), igual que `Pol ⊆ Capa 2` (`pol_sub_capa_dos`). Un verificador cuadrático tampoco está en la
  capa 1 (`cuadrar_no_capa_uno`): verificar y resolver **comparten** la capa 2, la de las funciones elementales.
* **La que separa es la regla de Landau** (`cebolla_no_separa_landau_si`): `2ⁿ` está en la misma capa que los
  polinomios y aun así escapa de toda `O(K)` con `K` polinomial.

## Lo que no se prueba

Que **todo** resolvedor pague el costo compuesto. Con la elección escondida en una caja negra sí está probado
(`adversario` en `Decidir.lean`); con la elección definida por un programa corto es P ≠ NP.
-/

namespace Sagitta.Map
namespace Tiempo

/-- **Las capas son cerradas hacia abajo**: lo que queda debajo de algo de la capa, está en la capa. -/
theorem capa_abajo {k : ℕ} {f g : ℕ → ℕ} (hg : g ∈ Capa k) (h : ∀ n, f n ≤ g n) : f ∈ Capa k := by
  obtain ⟨m, hg⟩ := hg
  exact ⟨m, fun n => (h n).trans (hg n)⟩

/-! ## El resolvedor, en la capa 2 -/

/-- **`2ⁿ` está en la capa 2**: queda debajo de `F 2 (n + 1) = 2ⁿ⁺¹ (n + 1)`. -/
theorem dos_pow_capa_dos : (fun n => 2 ^ n) ∈ Capa 2 := by
  refine ⟨1, fun n => ?_⟩
  simp only [Function.iterate_one, F_dos, pow_succ]
  nlinarith [Nat.one_le_two_pow (n := n)]

/-- **Todo `Exp` está en la capa 2**: `2^K(n)` con `K` polinomial es una composición dentro de la capa. -/
theorem exp_sub_capa_dos : Exp ⊆ Capa 2 := by
  rintro f ⟨K, hK, hf⟩
  exact capa_abajo (capa_comp dos_pow_capa_dos (pol_sub_capa_dos hK)) hf

/-! ## El resolvedor, fuera de la capa 1 -/

/-- **`2ⁿ` no está en la capa 1.** Si estuviera, `2^(2n)` también (la capa 1 contiene `2n` y es cerrada por
composición), y debajo de `2^(2n)` está el cuadrado, que no está en la capa 1. -/
theorem dos_pow_no_capa_uno : (fun n => 2 ^ n) ∉ Capa 1 := by
  intro h
  have h2 : (fun n => 2 ^ F 1 n) ∈ Capa 1 := capa_comp h (F_mem_capa 1)
  refine cuadrar_no_capa_uno (capa_abajo h2 fun n => ?_)
  rw [F_uno]
  simp only [cuadrar, doblar, pow_mul]
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num, pow_two]
  have h := n.lt_two_pow_self
  calc n * n ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul h.le h.le
    _ = 4 ^ n := by rw [← mul_pow]; norm_num

/-- **Una elección cada `k` pasos** (`ε = 1/k`): `2^(n/k)` tampoco está en la capa 1. Si estuviera, componiéndolo con
`k · n`, que es lineal, saldría `2ⁿ`. -/
theorem rala_no_capa_uno (k : ℕ) (hk : 1 ≤ k) : (fun n => 2 ^ (n / k)) ∉ Capa 1 := by
  intro h
  have hlin : (fun n => k * n) ∈ Capa 1 := by
    refine capa_abajo (capa_iterate (F_mem_capa 1) k) fun n => ?_
    rw [F_uno, iterate_doblar]
    exact Nat.mul_le_mul_right _ k.lt_two_pow_self.le
  refine dos_pow_no_capa_uno (capa_abajo (capa_comp h hlin) fun n => ?_)
  simp only [Nat.mul_div_cancel_left n (by omega : 0 < k), le_refl]

/-- `2^(n/k)` sí está en la capa 2. -/
theorem rala_capa_dos (k : ℕ) : (fun n => 2 ^ (n / k)) ∈ Capa 2 :=
  capa_abajo dos_pow_capa_dos fun n => Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self n k)

/-- **Leer el certificado**, `n/k` elecciones, está en la capa 1. -/
theorem rala_certificado_capa_uno (k : ℕ) : (fun n => n / k) ∈ Capa 1 :=
  capa_abajo (capa_id 1) fun n => Nat.div_le_self n k

/-! ## La regla que sí separa -/

/-- **La cebolla no separa P de Exp; Landau sí.** `2ⁿ` está en la misma capa que todos los polinomios y aun así
escapa de toda `O(K)` con `K` polinomial. -/
theorem cebolla_no_separa_landau_si :
    (fun n => 2 ^ n) ∈ Capa 2 ∧ Pol ⊆ Capa 2 ∧ ∀ K ∈ Pol, (fun n => 2 ^ n) ∉ O K :=
  ⟨dos_pow_capa_dos, pol_sub_capa_dos, escapa_de_dos_pow fun _ => le_rfl⟩

end Tiempo
end Sagitta.Map
