/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import CSP.Instance

/-!
# The main statements

The three theorems Zhuk's algorithm consumes, and the single induction they come from.
Everything in this file is **stated but not proved**: it is the target of the project, and
the point of writing it now is that the statements are what the blueprint must be checked
against and what the supporting lemmas must be aimed at.

Each `sorry` below is annotated with the blueprint label of the statement and an estimate
of what it needs.  Nothing else in `CSP` depends on this file, so the development stays
`sorry`-free below it.

## Blueprint

`ch6-main.tex`.
-/

open FirstOrder Language

universe u v w

namespace CSP

variable {L : Language.{u, v}} {V : Type w} {D : V → Type w} [∀ x, L.Structure (D x)]

/-! ### The measure

`haz:the-induction`: the main induction is on `∑_x |D⁽¹⁾_x|`, with the instance
universally quantified *inside*.  On a finite variable set with finite domains this is a
natural number and every appeal to the inductive hypothesis strictly decreases it. -/

/-- The measure of a reduction: the total number of elements it retains. -/
noncomputable def Reduction.measure [Fintype V] [∀ x, Fintype (D x)]
    (Dt : Reduction L D) : ℕ :=
  ∑ x : V, Nat.card (Dt x : Set (D x))

/-- Every strict one-step reduction at some variable decreases the measure.  This is the
uniform decrease lemma that `haz:the-induction`(b) asks for; without it, each of the four
appeals to the inductive hypothesis has to re-derive its own decrease. -/
theorem Reduction.measure_lt [Fintype V] [∀ x, Fintype (D x)]
    {Db Dt : Reduction L D} (_hle : Db ≤ Dt) (_hne : Db ≠ Dt) :
    Db.measure < Dt.measure := by
  -- Blueprint `haz:the-induction`(b).  Needs: `Nat.card` monotone under `⊆` on finite
  -- sets, strict at the variable where the inclusion is proper, and `Finset.sum_lt_sum`.
  sorry

/-! ### Auxiliary predicates used by the main statement -/

/-- An instance is **irreducible** in Zhuk's sense.  Blueprint `def:instance-linked`;
`haz:irreducible-instance` records that this is never unfolded — only its two consequences
are used. -/
def IsIrreducibleInstance (I : Instance L D) : Prop :=
  ¬ ∃ I' : Instance L D,
      (∀ C' ∈ I', ∃ C ∈ I, C'.WeakerEq C) ∧
      ¬ IsLinkedInstance I' ∧
      ¬ SolutionSetSubdirect I'

open scoped Classical in
/-- A constraint has the **parallelogram property**.  Blueprint `def:parallelogram`;
`haz:permutations` argues for the split-into-two-blocks formulation used here. -/
def Constraint.Parallelogram (C : Constraint L D) : Prop :=
  ∀ (S : Set (Fin C.arity)) (_hS : S.Nonempty) (_hS' : Sᶜ.Nonempty)
    (a b : ∀ i, D (C.scope i)),
    (fun i => if i ∈ S then a i else b i) ∈ C.rel →
    (fun i => if i ∈ S then b i else a i) ∈ C.rel →
    b ∈ C.rel → a ∈ C.rel

/-- Zhuk's `Con₁(C, i)`: the pairs of values at position `i` that share a common context
inside the constraint relation.  Blueprint `def:conone`.

`haz:conone-not-congruence`: this is reflexive and symmetric but not transitive in
general, so it is *not* a congruence without further hypotheses.  It is indexed by the
*position* `i`, not by the variable — which matters, because a scope may repeat a
variable. -/
def Constraint.conOne (C : Constraint L D) (i : Fin C.arity) :
    Set (D (C.scope i) × D (C.scope i)) :=
  {p | ∃ t ∈ C.rel, ∃ t' ∈ C.rel, (∀ j, j ≠ i → HEq (t j) (t' j)) ∧ t i = p.1 ∧ t' i = p.2}

theorem Constraint.conOne_refl (C : Constraint L D) (i : Fin C.arity)
    {a : D (C.scope i)} (h : ∃ t ∈ C.rel, t i = a) : (a, a) ∈ C.conOne i := by
  obtain ⟨t, ht, hti⟩ := h
  exact ⟨t, ht, t, ht, fun _ _ => HEq.rfl, hti, hti⟩

theorem Constraint.conOne_symm (C : Constraint L D) (i : Fin C.arity)
    {a b : D (C.scope i)} (h : (a, b) ∈ C.conOne i) : (b, a) ∈ C.conOne i := by
  obtain ⟨t, ht, t', ht', hctx, hta, htb⟩ := h
  exact ⟨t', ht', t, ht, fun j hj => (hctx j hj).symm, htb, hta⟩

/-! Two predicates of `ch4-instances.tex` are **not** defined here.

`IsConnectedInstance` (blueprint `def:connected`) requires the adjacency relation between
constraints, which is "there is a reflexive bridge between their `Con₁`s" — and `Con₁` is
a congruence only under the hypotheses of `lem:conone-basics`.  Defining it therefore
means first proving that lemma and carrying the congruence as data.

`IsExpandedCovering` (blueprint `def:expanded`) requires the coproduct-of-variable-types
design of `haz:renaming`, which is the single most consequential representation decision
still open.

Both are deliberately absent rather than stubbed: a `def … : Prop := sorry` would be a
junk constant that later proofs could silently "use".  The statement of
`main_inductive` below is correspondingly restricted to the part (1a) that the present
vocabulary can express. -/

/-! ### The main inductive claim -/

/-- **Theorem (main inductive claim).**  Blueprint `thm:main-inductive`.

This is the single induction that carries the proof.  Part (2) is proved first, from the
inductive hypothesis for part (1) at a strictly smaller reduction; part (1) then splits on
whether some domain has a nontrivial binary absorbing or central subuniverse.

Cost estimate: this is the summit.  It consumes `lem:bridge-from-instance` (the longest
proof in the source), `thm:stable-intersection`, `lem:ubiquity`, `lem:find-consistent`,
`lem:minimal-consistent`, `lem:tree-coverings`, `lem:connected`, and the construction of
`Ω` in `constr:omega`.  It should be attempted last. -/
theorem main_inductive [Fintype V] [∀ x, Fintype (D x)]
    (_I : Instance L D) (_D1 : Reduction L D)
    (_hirr : IsIrreducibleInstance _I) (_hcc : CycleConsistent _I)
    (_hone : OneConsistent _I _D1) (_hlll : _D1.Lll Reduction.top)
    (_hcrucial : Crucial _I _D1) :
    ∀ C ∈ _I, C.Parallelogram := by
  sorry

/-- **Theorem (main inductive claim), part (2).**  Blueprint `thm:main-inductive`(2).

If a further reduction of type `BA` or `C` is 1-consistent and the instance was solvable
in `D⁽¹⁾`, it is still solvable in `D⁽²⁾`.  This is the half proved first, and it is what
`thm:reductions-safe` consumes. -/
theorem main_inductive_two [Fintype V] [∀ x, Fintype (D x)]
    (_I : Instance L D) (_D1 _D2 : Reduction L D)
    (_hirr : IsIrreducibleInstance _I) (_hcc : CycleConsistent _I)
    (_hone : OneConsistent _I _D1) (_hlll : _D1.Lll Reduction.top)
    (_hone2 : OneConsistent _I _D2)
    (_hstep : ∀ x, SubBA L (_D2 x : Set (D x)) (_D1 x) ∨ SubC L (_D2 x : Set (D x)) (_D1 x))
    (_hsol : SolvableIn _I _D1) :
    SolvableIn _I _D2 := by
  sorry

/-! ### The three consumed theorems -/

/-- **Theorem (reductions are safe).**  Blueprint `thm:reductions-safe`, Informal
Claim (IC2).  If a variable's domain has a strong subset of type `BA`, `C` or `PC`, then
restricting to it preserves solvability.

This is what licenses the `ReduceDomain` step of the algorithm. -/
theorem reductions_safe [Fintype V] [∀ x, Fintype (D x)]
    (I : Instance L D) (_hcc : CycleConsistent I) (_hirr : IsIrreducibleInstance I)
    (x : V) (B : Set (D x))
    (_hB : SubBA L B Set.univ ∨ SubC L B Set.univ ∨ SubPC L B Set.univ) :
    Solvable I ↔ ∃ s, IsSolution I s ∧ s x ∈ B := by
  sorry

/-- **Theorem (PC reductions do not kill all solutions).**  Blueprint `thm:pc-safe`. -/
theorem pc_safe [Fintype V] [∀ x, Fintype (D x)]
    (I : Instance L D) (_hcc : CycleConsistent I) (_hirr : IsIrreducibleInstance I)
    (y : V) (B : Set (D y)) (_hB : SubPC L B Set.univ) (_hsol : Solvable I) :
    ∃ s, IsSolution I s ∧ s y ∈ B := by
  sorry

/-- **Theorem (ubiquity).**  Blueprint `lem:ubiquity`, Informal Claim (IC1).  Every domain
of size at least two that has been reached by strong reductions admits another one.

This is what guarantees the algorithm's outer loop makes progress, and it is the smallest
of the three claims — a good first target. -/
theorem ubiquity {A : Type w} [L.Structure A] (B : Set A) (_h : Lll L B Set.univ)
    (_hcard : 1 < Nat.card B) :
    ∃ C : Set A, SubBA L C B ∨ SubC L C B ∨ SubL L C B ∨ SubPC L C B := by
  sorry

/-- **Theorem (codimension one).**  Blueprint `thm:codim-one`, Informal Claim (IC3).

The statement here is deliberately abridged: the full hypotheses involve the minimal
linear congruences `σ_{x_i}`, the quotients `L_{x_i}`, and a homomorphism `φ` from a
product of `ℤ_q`'s.  Writing them needs the mixed-prime linear algebra of
`haz:step2-linear-algebra`, which is itself a missing Mathlib layer; see `GAPS.md`. -/
theorem codim_one : True := trivial

end CSP
