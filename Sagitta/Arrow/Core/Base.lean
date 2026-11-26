/-
Copyright (c) 2026 Jose-de-Jesus Ulate-Cardenas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose-de-Jesus Ulate-Cardenas
-/
import Mathlib.Logic.Function.Basic

/-!
# The abstract model

The argument of *The Computational Arrow of Time* does not depend on Turing machines. It only uses
a few closure properties of the classes `P` and `NP`: reductions compose, a polynomial-time
procedure may call a polynomial-time subroutine, every `NP` problem is the domain of a search
problem, and a search problem can be solved by asking a decision procedure about prefixes of its
solutions. This file collects those properties in the structure `Model`.

`Sagitta.Arrow.TM.tmModel` (in the `TM` layer) proves that the multi-tape Turing machines of
cslib, with polynomial-time many-one reductions and the classes `P`, `NP`, `FNP` and `FPSearch` of
cslib-frontier, form a `Model`. Every theorem stated here for an arbitrary `Model` therefore holds
for real machines.

## Main definitions

* `Model`: decision problems with a reduction preorder, the classes `P ⊆ NP`, search problems with
  the classes `FP ⊆ FNP`, and the four closure properties.
* `Model.PeqNP`, `Model.SearchEasy`, `Model.NPComplete`, `Model.Intermediate`.
-/

namespace Sagitta.Arrow

universe u

/-- **An abstract complexity model.** Decision problems (`Problem`) and search problems
(`Search`), the classes `P ⊆ NP` and `FP ⊆ FNP`, a reduction preorder, and the closure properties
that the argument uses. Nothing here mentions a machine. -/
structure Model where
  /-- Decision problems (in the Turing-machine instance: a set together with an encoding). -/
  Problem : Type u
  /-- Search problems (in the Turing-machine instance: a relation together with an encoding). -/
  Search : Type u
  /-- `Reduces A B`: `A` reduces to `B` (polynomial-time many-one, in the instance). -/
  Reduces : Problem → Problem → Prop
  reduces_refl : ∀ A, Reduces A A
  /-- **Composing** two efficient translations is an efficient translation. -/
  reduces_trans : ∀ {A B C}, Reduces A B → Reduces B C → Reduces A C
  /-- Efficiently decidable problems. -/
  InP : Problem → Prop
  /-- Problems with efficiently checkable witnesses. -/
  InNP : Problem → Prop
  P_subset_NP : ∀ {A}, InP A → InNP A
  /-- **Calling a subroutine**: if `A` reduces to `B` and `B` is efficiently decidable, so is `A`. -/
  InP_of_reduces : ∀ {A B}, Reduces A B → InP B → InP A
  /-- Search problems with efficiently checkable, polynomially short solutions. -/
  InFNP : Search → Prop
  /-- Search problems solved by an efficient procedure. -/
  InFP : Search → Prop
  /-- The decision problem of a search problem: "does this instance have a solution?" -/
  domain : Search → Problem
  domain_NP : ∀ {R}, InFNP R → InNP (domain R)
  /-- An efficient solver also decides the domain: run it and see whether it finds something. -/
  domain_P : ∀ {R}, InFP R → InP (domain R)
  /-- Every `NP` problem is the domain of an `FNP` search problem (its witnesses). -/
  exists_search : ∀ {A}, InNP A → ∃ R, InFNP R ∧ domain R = A
  /-- The prefix problem of a search problem: "does some solution of `a` begin with `u`?" -/
  prefixProblem : Search → Problem
  prefix_NP : ∀ {R}, InFNP R → InNP (prefixProblem R)
  /-- **Search through prefixes**: an efficient decider of the prefix problem, called as a
  subroutine once per bit, solves the search problem. -/
  search_of_prefix : ∀ {R}, InFNP R → InP (prefixProblem R) → InFP R

namespace Model

variable (M : Model.{u})

/-- `P = NP` in the model: every problem with efficiently checkable witnesses is efficiently
decidable. -/
def PeqNP : Prop := ∀ A, M.InNP A → M.InP A

/-- Every search problem with efficiently checkable solutions is efficiently solvable: going from
a "yes" back to its witness is cheap. -/
def SearchEasy : Prop := ∀ R, M.InFNP R → M.InFP R

/-- `B` is `NP`-complete: it is in `NP` and every `NP` problem reduces to it. -/
def NPComplete (B : M.Problem) : Prop := M.InNP B ∧ ∀ A, M.InNP A → M.Reduces A B

/-- `A` is `NP`-intermediate: in `NP`, not in `P`, and not `NP`-complete. -/
def Intermediate (A : M.Problem) : Prop := M.InNP A ∧ ¬M.InP A ∧ ¬M.NPComplete A

end Model

end Sagitta.Arrow
