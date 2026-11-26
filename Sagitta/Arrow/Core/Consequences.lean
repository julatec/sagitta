/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Sagitta.Arrow.Core.SecondLaw

/-!
# Consequences of the arrow, in any model

Every theorem here takes the arrow `(h : M.Arrow)` as an explicit hypothesis.

* `Model.not_InP_of_NPComplete`: no `NP`-complete problem is efficiently decidable.
* `Model.not_searchEasy`: some search problem cannot be solved efficiently.
* `Model.not_reduces_of_InP`: an `NP`-complete problem does not reduce to an efficiently decidable
  one.

The existence of `NP`-intermediate problems (Ladner) needs a diagonalization over machines, so it
is a theorem of the Turing-machine instance: `Sagitta.Arrow.TM.exists_intermediate`.
-/

namespace Sagitta.Arrow.Model

universe u

variable {M : Model.{u}}

/-- **With the arrow, no `NP`-complete problem is in `P`.** -/
theorem not_InP_of_NPComplete (h : M.Arrow) {B : M.Problem} (hB : M.NPComplete B) : ¬M.InP B :=
  (arrow_iff_not_InP hB).1 h

/-- **With the arrow, going back from "yes" is not always cheap.** -/
theorem not_searchEasy (h : M.Arrow) : ¬M.SearchEasy :=
  kelvin.1 h

/-- With the arrow, an `NP`-complete problem does not reduce to a problem in `P`. -/
theorem not_reduces_of_InP (h : M.Arrow) {B C : M.Problem} (hB : M.NPComplete B)
    (hC : M.InP C) : ¬M.Reduces B C :=
  fun hBC => not_InP_of_NPComplete h hB (M.InP_of_reduces hBC hC)

end Sagitta.Arrow.Model
