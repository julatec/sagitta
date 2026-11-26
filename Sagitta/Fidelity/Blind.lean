import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Blind formalization of five statements from the literature

This file was written *blind*: its author read only the vendored definitions of cslib and
cslib-frontier (`MultiTapeTM`, `Cfg`, `step`, `runFrom`, `RunsInTime`, `ComputesInTimeAndSpace`,
`ComputableInPolyTime`, `P`, `NP`, `IsVerifier`, `PolyTimeReducible`, `NPComplete`, `SAT`,
`ThreeSAT`, `encCNF` and the encodings) and the sources cited in each docstring, and did **not**
read the statements elsewhere in this project. The point is to have an independent rendering of
each statement to compare against.

Only statements are given, as `def … : Prop`; nothing here is proved, and nothing here is assumed.

* (a) `BennettPoly`, `BennettLinear`: Bennett (1973), reversible simulation with clean tapes.
* (b) `GoldreichThm2_6`: Goldreich, `PC ⊆ PF ↔ P = NP`.
* (c) `Ladner`: Ladner (1975), NP-intermediate languages if `P ≠ NP`.
* (d) `IsingNPComplete`: the decision problem "is there a spin configuration of energy `≤ t`"
  for zero-field Ising models on arbitrary graphs with integer couplings is `NP`-complete.
* (e) `WeakETH`, `WeakETHSize`, `SH`: the Weak ETH, its size form, and the Satisfiability
  Hypothesis of Stearns and Hunt, as stated in arXiv:2611.02650.
-/

namespace Sagitta.Fidelity.Blind

open Turing Turing.MultiTapeTM Cslib Cslib.Complexity Cslib.Logic.PL

/-! ## (a) Bennett 1973 -/

/-- A deterministic machine is *reversible* when its step function is injective on running
configurations: two configurations that are both still running and have the same successor are
equal. This is the global form of Bennett's local condition that no two quadruples overlap in
range (Bennett 1973, p. 527: a deterministic machine "will be reversible if and only if" its
transition formulas "have non-overlapping ranges"), quantified over *all* configurations of every
input, reachable or not. Halted configurations are excluded because `step` fixes them. -/
def IsReversible {k : ℕ} {Symbol State : Type} (tm : MultiTapeTM k Symbol State) : Prop :=
  ∀ (input : List Symbol) (c c' : Cfg k Symbol State input),
    c.state.isSome → c'.state.isSome →
      MultiTapeTM.step (tm := tm) c = MultiTapeTM.step (tm := tm) c' → c = c'

/-- `cfg` is the initial configuration of `tm` on `input` except that the machine has halted and
the output tape holds `output`: every work tape is blank again, every work head and the input head
are back where they started. This is Bennett's final condition: the reversible machine `R`
satisfies `R : (I; B; B) → (I; B; P)`, i.e. the history tape is blank again, "restoring the
machine (except for the now-written output tape) to its original condition" (Bennett 1973,
abstract and main theorem). -/
def CleanHalt {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) (input output : List Bool)
    (cfg : Cfg k Bool State input) : Prop :=
  cfg = { tm.initCfg input with state := none, output := output }

/-- **Bennett (1973), polynomial form.** Every function computable in polynomial time (by a
multi-tape machine over `Bool` with finitely many states, in the sense of cslib's
`ComputableInPolyTime`) is computed, in polynomial time and space, by a *reversible* machine of
the same kind that halts with all of its work tapes blank and its heads back at the origin, the
output being on the (write-only) output tape.

Source: C. H. Bennett, "Logical reversibility of computation", IBM J. Res. Dev. 17(6):525–532,
1973, DOI 10.1147/rd.176.0525; read from the scan at
https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2013W/Bennett_Reversibiity.pdf (main theorem,
p. 527). Bennett states it for a standard one-tape machine `S` and a three-tape reversible `R`
(input, history, output tapes); here the source machine may have any number of work tapes, the
input tape is cslib's read-only one and the output tape cslib's append-only one, so "the input is
restored" is automatic for the contents and is asked of the head. -/
def BennettPoly : Prop :=
  ∀ {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β),
    ComputableInPolyTime f encIn encOut →
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State)
        (t s : ℕ → ℕ),
        PolynomiallyBounded t ∧ PolynomiallyBounded s ∧ IsReversible tm ∧
          ∀ a, tm.ComputesInTimeAndSpace (encIn a) (encOut (f a))
              (t (encIn a).length) (s (encIn a).length) ∧
            ∃ u, CleanHalt tm (encIn a) (encOut (f a))
              (MultiTapeTM.runFrom (tm := tm) (tm.initCfg (encIn a)) u)

/-- **Bennett (1973), quantitative form.** If a machine computes `f` within time `t` and space
`s` (per input), a reversible machine computes it with clean tapes within time `O(t)` and space
`O(s + t)`. Bennett's bound is `4ν + 4λ + 5` steps and `s`, `ν + 1`, `λ + 2` squares on the three
tapes, for a run of `ν` steps, `s` squares and an output of length `λ` (here `λ ≤ ν`, since the
output tape receives at most one symbol per step). Same source as `BennettPoly`. -/
def BennettLinear : Prop :=
  ∀ {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (f : α → β)
    {k : ℕ} {State : Type} [Finite State] (tm : MultiTapeTM k Bool State) (t s : α → ℕ),
    tm.ComputesFunInTimeAndSpace encIn encOut f t s →
      ∃ (k' : ℕ) (State' : Type) (_ : Finite State') (R : MultiTapeTM k' Bool State') (C : ℕ),
        IsReversible R ∧
          ∀ a, R.ComputesInTimeAndSpace (encIn a) (encOut (f a))
              (C * t a + C) (C * (s a + t a) + C) ∧
            ∃ u, CleanHalt R (encIn a) (encOut (f a))
              (MultiTapeTM.runFrom (tm := R) (R.initCfg (encIn a)) u)

/-! ## (b) Goldreich, Theorem 2.6 -/

/-- Binary strings encode themselves (Goldreich works over `{0,1}*`). -/
abbrev encStr : List Bool ↪ List Bool := encBits

/-- Goldreich, Definition 2.1: `R ⊆ {0,1}* × {0,1}*` is polynomially bounded when some
polynomial `p` gives `|y| ≤ p(|x|)` for every `(x, y) ∈ R`. -/
def PolyBoundedRel (R : List Bool → List Bool → Prop) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x y, R x y → y.length ≤ p.eval x.length

/-- Goldreich, Definition 2.3: `PC`, the polynomially bounded relations whose membership
`(x, y) ∈ R` is decided by a polynomial-time algorithm. -/
def PC : Set (List Bool → List Bool → Prop) :=
  {R | PolyBoundedRel R ∧ ∃ A : List Bool × List Bool → Bool,
    ComputableInPolyTime A (encPair encStr encStr) encBool ∧ ∀ x y, A (x, y) = true ↔ R x y}

/-- Goldreich, Definition 2.2: `PF`, the polynomially bounded relations whose search problem is
solved by a polynomial-time algorithm `A`: `A(x) ∈ R(x)` whenever `R(x) ≠ ∅`, and `A(x) = ⊥`
(here `none`) when `R(x) = ∅`. Membership of pairs need not be decidable. -/
def PF : Set (List Bool → List Bool → Prop) :=
  {R | PolyBoundedRel R ∧ ∃ A : List Bool → Option (List Bool),
    ComputableInPolyTime A encStr (encOption encStr) ∧
      ∀ x, ((∃ y, R x y) → ∃ y, A x = some y ∧ R x y) ∧ ((¬ ∃ y, R x y) → A x = none)}

/-- Goldreich, Definition 2.4: `P`, the sets `S ⊆ {0,1}*` decided by a polynomial-time
algorithm. -/
def PGold : Set (Set (List Bool)) :=
  {S | ∃ A : List Bool → Bool, ComputableInPolyTime A encStr encBool ∧ ∀ x, A x = true ↔ x ∈ S}

/-- Goldreich, Definition 2.5: `NP`, the sets with an efficiently verifiable proof system: a
polynomial `p` and a polynomial-time `V` with completeness (every `x ∈ S` has a `y` with
`|y| ≤ p(|x|)` and `V(x, y) = 1`) and soundness (`V(x, y) = 0` for every `x ∉ S` and every `y`).
Note `≤ p(|x|)`, not cslib's exact length. -/
def NPGold : Set (Set (List Bool)) :=
  {S | ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    ComputableInPolyTime V (encPair encStr encStr) encBool ∧
      (∀ x ∈ S, ∃ y, y.length ≤ p.eval x.length ∧ V (x, y) = true) ∧
      (∀ x ∉ S, ∀ y, V (x, y) = false)}

/-- **Goldreich, Theorem 2.6.** `PC ⊆ PF` if and only if `P = NP`.

Source: O. Goldreich, *Computational Complexity: A Conceptual Perspective*, Cambridge University
Press, 2008, DOI 10.1017/CBO9780511804106, Section 2.1.3. What was read is the author's draft of
Chapters 0–2 (Dec. 2006), `CC/r1.pdf` from https://www.wisdom.weizmann.ac.il/~oded/cc-drafts.html
(fetched through web.archive.org, the site itself refusing connections); Definitions 2.1–2.5 and
Theorem 2.6 are quoted from there. The printed 2008 edition was not read. "Polynomial-time
algorithm" is rendered as cslib's `ComputableInPolyTime` (multi-tape machine over `Bool`, finite
control); pairs `⟨x, y⟩` use cslib's framed pair encoding. -/
def GoldreichThm2_6 : Prop := PC ⊆ PF ↔ PGold = NPGold

/-! ## (c) Ladner 1975 -/

/-- Karp (polynomial-time many-one) reducibility between languages `A, B ⊆ {0,1}*`
(Arora–Barak, Definition 2.7). -/
def KarpReducible (A B : Set (List Bool)) : Prop := PolyTimeReducible encStr encStr A B

/-- `B ⊆ {0,1}*` is `NP`-complete as a language: `B ∈ NP` and every language in `NP` Karp-reduces
to `B` (Arora–Barak, Definition 2.7). Hardness is asked only of *languages*, not of problems over
every type and encoding as in cslib's `NPComplete`, so that its negation is not weakened. -/
def NPCompleteLang (B : Set (List Bool)) : Prop :=
  B ∈ NP encStr ∧ ∀ A : Set (List Bool), A ∈ NP encStr → KarpReducible A B

/-- **Ladner's theorem.** If `P ≠ NP` (for languages over `{0,1}`), some language is in `NP`,
not in `P`, and not `NP`-complete under Karp reductions.

Sources: R. E. Ladner, "On the structure of polynomial time reducibility", J. ACM
22(1):155–171, 1975, DOI 10.1145/321864.321877 — **not read** (paywalled; only the bibliographic
entry at https://projects.csail.mit.edu/jacm/References/ladner1975:155.html, whose keywords list
both Turing and many-one reducibility). The statement follows Arora and Barak, *Computational
Complexity: A Modern Approach*, Theorem 3.4 ("Suppose that P ≠ NP. Then there exists a language
L ∈ NP \ P that is not NP-complete"), read in the draft at
https://theory.cs.princeton.edu/complexity/book.pdf, with Karp reductions (Definition 2.7).
Ladner's paper proves the stronger form in which `L` is not complete even under polynomial-time
Turing reductions; that form is not stated here. -/
def Ladner : Prop :=
  P encStr ≠ NP encStr →
    ∃ L : Set (List Bool), L ∈ NP encStr ∧ L ∉ P encStr ∧ ¬ NPCompleteLang L

/-! ## (d) The Ising decision problem -/

/-- An instance: a list of weighted edges `(i, j, J_ij)` with integer couplings, on vertices
numbered by `ℕ` (an arbitrary finite graph; parallel edges add up, a self-loop contributes the
constant `-J_ii`), and an integer threshold `t`. -/
abbrev IsingInstance : Type := List (ℕ × ℕ × ℤ) × ℤ

/-- The spin `±1` of vertex `i` under the configuration `σ` (`true` is `+1`). -/
def spin (σ : ℕ → Bool) (i : ℕ) : ℤ := if σ i then 1 else -1

/-- The zero-field Ising energy `H(σ) = - Σ_{(i,j)} J_ij s_i s_j` (Lucas, eq. (3), with `h = 0`). -/
def isingEnergy (edges : List (ℕ × ℕ × ℤ)) (σ : ℕ → Bool) : ℤ :=
  -(edges.map fun e => e.2.2 * spin σ e.1 * spin σ e.2.1).sum

/-- The decision problem: some spin configuration has energy at most the threshold. -/
def IsingLE : Set IsingInstance := {I | ∃ σ : ℕ → Bool, isingEnergy I.1 σ ≤ I.2}

/-- Instances in binary: the list of edges, each `(i, j, J)` with `i`, `j` in binary and `J` in
binary sign–magnitude, then the threshold in binary sign–magnitude. -/
def encIsing : IsingInstance ↪ List Bool :=
  encPair (encList (encPair encNat (encPair encNat encIntBin))) encIntBin

/-- **The Ising decision problem is `NP`-complete** (cslib's `NPComplete`: in `NP` and every
problem in `NP`, with any encoding, reduces to it; this implies the language version).

Sources: F. Barahona, "On the computational complexity of Ising spin glass models", J. Phys. A
15(10):3241–3253, 1982, DOI 10.1088/0305-4470/15/10/028 — only the abstract was read (full text
paywalled): it shows the ground-state problem NP-hard in the planar case with a field and in the
three-dimensional case. The decision form and the Hamiltonian follow A. Lucas, "Ising formulations
of many NP problems", Front. Phys. 2:5, 2014, arXiv:1302.5843 (read: eq. (3) and §1.2, "does the
ground state of H have energy ≤ 0?"); hardness on arbitrary graphs without a field is MAX-CUT
(all `J_ij = -1`), Karp 1972. The threshold `t` is part of the instance; Lucas fixes `t = 0`. -/
def IsingNPComplete : Prop := NPComplete encIsing IsingLE

/-! ## (e) Weak ETH and SH -/

/-- The number `n` of variables of a formula whose variables are numbered `0, …, n - 1`: one more
than the largest index that occurs (unused smaller indices count, as in arXiv:2611.02650,
footnote 2). -/
def numVars (φ : CNF ℕ) : ℕ := (φ.vars.map Nat.succ).foldr max 0

/-- The inputs the hypotheses talk about (arXiv:2611.02650, footnote 2): no literal repeated
within a clause and no clause repeated. Without this, a formula on few variables could be
arbitrarily long and no machine could even read it within a bound in `n`. -/
def IsCNFInput (φ : CNF ℕ) : Prop := (∀ c ∈ φ, c.Nodup) ∧ φ.Nodup

/-- A `3CNF` input: an input in the sense of `IsCNFInput` with clauses of width at most 3. -/
def Is3CNFInput (φ : CNF ℕ) : Prop := IsCNFInput φ ∧ ∀ c ∈ φ, c.length ≤ 3

/-- The input length `L = n + m + (number of literal occurrences)` of a CNF formula
(arXiv:2611.02650, footnote 2). -/
def inputLength (φ : CNF ℕ) : ℕ := numVars φ + φ.length + φ.vars.length

/-- Some deterministic multi-tape machine over `Bool` with finitely many states decides `L` on
every formula satisfying `Dom`, from cslib's encoding `encCNF`, within `T φ` steps (space
unbounded). -/
def DecidesWithin (Dom : CNF ℕ → Prop) (L : Set (CNF ℕ)) (T : CNF ℕ → ℝ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ∀ φ, Dom φ → tm.Computes (encCNF φ) [MultiTapeTM.indicator L φ] ∧
      ∃ t : ℕ, (t : ℝ) ≤ T φ ∧ tm.RunsInTime (encCNF φ) t

/-- **Weak ETH.** For every constant `ε > 0`, 3SAT on inputs with `n` variables cannot be solved
in `O(2^{n^{1-ε}})` time.

Source: MIT Hardness Group et al., "ETH is Dead, Long Live SH", arXiv:2611.02650v2
(https://arxiv.org/abs/2611.02650, PDF read), §1, "Weak ETH", with the input conventions of
footnote 2. The paper's algorithms are word-RAM-like (`L` may count words of `L^{o(1)}` bits,
footnote 1); here the model is cslib's multi-tape machine on the bit encoding `encCNF`. On the
domain `Is3CNFInput` the encoding has length polynomial in `n` (there are at most `O(n³)` distinct
clauses), so the polynomial overhead between the two models is absorbed: `2^{n^{1-ε}} · poly(n)`
is `O(2^{n^{1-ε/2}})`. The `O` is a single constant over all inputs, which is the same thing on
this domain because only finitely many inputs have a given `n`. Deterministic algorithms: the
paper states randomized versions separately (rSH). -/
def WeakETH : Prop :=
  ∀ ε : ℝ, 0 < ε → ¬ ∃ C : ℝ,
    DecidesWithin Is3CNFInput ThreeSAT fun φ => C * 2 ^ ((numVars φ : ℝ) ^ (1 - ε))

/-- **Weak ETH, size form** (arXiv:2611.02650v2, Lemma 2.1 and Corollary 2.3 with `k = 3`): for
every constant `ε > 0`, 3SAT has no `2^{O((n+m)^{1-ε})}`-time algorithm, where `m` is the number of
clauses. The `O` is inside the exponent, as in the paper. Same conventions as `WeakETH`. -/
def WeakETHSize : Prop :=
  ∀ ε : ℝ, 0 < ε → ¬ ∃ C : ℝ,
    DecidesWithin Is3CNFInput ThreeSAT
      fun φ => 2 ^ (C * ((numVars φ + φ.length : ℕ) : ℝ) ^ (1 - ε))

/-- **SH (Stearns and Hunt, 1990)**, as stated in arXiv:2611.02650v2, §1: for every constant
`ε > 0`, CNF SAT on inputs of length `L` cannot be solved in `O(2^{L^{1-ε}})` time, with `L` the
number of variables plus clauses plus literal occurrences (footnote 2). The original,
R. E. Stearns and H. B. Hunt III, "Power indices and easier hard problems", Math. Systems Theory
23:209–225, 1990, DOI 10.1007/BF02090776, was **not read**; the paper says it is "in terms of bit length". The paper proves
SH ⟺ Weak ETH (Theorem 2.4). -/
def SH : Prop :=
  ∀ ε : ℝ, 0 < ε → ¬ ∃ C : ℝ,
    DecidesWithin IsCNFInput SAT fun φ => C * 2 ^ ((inputLength φ : ℝ) ^ (1 - ε))

/-! ## Sanity checks and axioms -/

/-- Variables `0` and `2` occur, so `n = 3` (index `1` is counted though unused). -/
example : numVars [[(0, true)], [(2, false)]] = 3 := by decide

/-- One antiferromagnetic edge (`J = -1`): opposite spins give energy `-1`. -/
example : isingEnergy [(0, 1, -1)] (fun i => decide (i = 0)) = -1 := by decide

/-- Aligned spins on the same edge give energy `+1`. -/
example : isingEnergy [(0, 1, -1)] (fun _ => true) = 1 := by decide

/-- info: 'Sagitta.Fidelity.Blind.BennettPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BennettPoly

/-- info: 'Sagitta.Fidelity.Blind.BennettLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BennettLinear

/-- info: 'Sagitta.Fidelity.Blind.GoldreichThm2_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GoldreichThm2_6

/-- info: 'Sagitta.Fidelity.Blind.Ladner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ladner

/-- info: 'Sagitta.Fidelity.Blind.IsingNPComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsingNPComplete

/-- info: 'Sagitta.Fidelity.Blind.WeakETH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WeakETH

/-- info: 'Sagitta.Fidelity.Blind.WeakETHSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WeakETHSize

/-- info: 'Sagitta.Fidelity.Blind.SH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SH

end Sagitta.Fidelity.Blind
