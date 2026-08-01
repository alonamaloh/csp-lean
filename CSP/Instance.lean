/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import CSP.Types

/-!
# CSP instances

Zhuk's \S3.1.  The representation choices here are the ones argued for in the blueprint
(`haz:instance-list`, `haz:renaming`):

* an instance is a **list** of constraints, not a set: proofs delete "a constraint
  `C ∈ 𝓘`", and the same relation can legitimately occur twice;
* a constraint's scope is a **tuple** `Fin k → V`, not a set of variables: repeated
  variables occur (`ζ(x, x', z)` in the main proof, and `R(x,…,x)` in the definition of an
  expanded covering);
* the variable type is a **parameter**, so that joining two instances is a coproduct of
  variable types rather than a renaming with a fresh-name supply.

## Blueprint

`ch4-instances.tex`.
-/

open FirstOrder Language

universe u v w

namespace CSP

variable {L : Language.{u, v}} {V : Type w} {D : V → Type w} [∀ x, L.Structure (D x)]

/-- A constraint: a scope (a tuple of variables, repeats allowed) together with a
subuniverse of the product of the corresponding domains. -/
structure Constraint (L : Language.{u, v}) {V : Type w} (D : V → Type w)
    [∀ x, L.Structure (D x)] where
  /-- The number of argument positions. -/
  arity : ℕ
  /-- Which variable sits at each position.  Not injective in general. -/
  scope : Fin arity → V
  /-- The constraint relation. -/
  rel : L.Substructure (∀ i : Fin arity, D (scope i))

/-- An instance is a list of constraints. -/
abbrev Instance (L : Language.{u, v}) {V : Type w} (D : V → Type w)
    [∀ x, L.Structure (D x)] := List (Constraint L D)

/-- An assignment gives every variable a value in its domain. -/
abbrev Assignment {V : Type w} (D : V → Type w) := ∀ x, D x

namespace Constraint

variable (C : Constraint L D)

/-- The tuple an assignment presents to a constraint. -/
def restrict (s : Assignment D) : ∀ i : Fin C.arity, D (C.scope i) := fun i => s (C.scope i)

/-- An assignment satisfies a constraint. -/
def Satisfies (s : Assignment D) : Prop := C.restrict s ∈ C.rel

/-- The set of variables occurring in a constraint. -/
def vars : Set V := Set.range C.scope

end Constraint

/-- An assignment is a solution of an instance if it satisfies every constraint. -/
def IsSolution (I : Instance L D) (s : Assignment D) : Prop := ∀ C ∈ I, C.Satisfies s

/-- An instance is solvable. -/
def Solvable (I : Instance L D) : Prop := ∃ s, IsSolution I s

/-! ### Reductions -/

/-- A reduction assigns a subuniverse — possibly empty — to every variable.
Blueprint `def:reduction`; `haz:empty-reduction` explains why emptiness is allowed. -/
abbrev Reduction (L : Language.{u, v}) {V : Type w} (D : V → Type w)
    [∀ x, L.Structure (D x)] := ∀ x, L.Substructure (D x)

/-- The trivial reduction. -/
def Reduction.top : Reduction L D := fun _ => ⊤

/-- A reduction is nonempty if it is nonempty at every variable. -/
def Reduction.Nonempty (Dt : Reduction L D) : Prop := ∀ x, (Dt x : Set (D x)).Nonempty

/-- An assignment lies in a reduction. -/
def Reduction.Contains (Dt : Reduction L D) (s : Assignment D) : Prop := ∀ x, s x ∈ Dt x

/-- A solution of `𝓘` inside the reduction `Dt` — Zhuk's "`𝓘^{(⊤)}` has a solution". -/
def SolvableIn (I : Instance L D) (Dt : Reduction L D) : Prop :=
  ∃ s, IsSolution I s ∧ Dt.Contains s

/-- Reductions are ordered pointwise. -/
instance : LE (Reduction L D) := ⟨fun Db Dt => ∀ x, Db x ≤ Dt x⟩

/-- `D⁽ᵇᵒᵗ⁾ ⋘ D⁽ᵗᵒᵖ⁾`: the strong-reduction relation, pointwise.  Blueprint
`def:reduction`. -/
def Reduction.Lll (Db Dt : Reduction L D) : Prop :=
  ∀ x, CSP.Lll L (Db x : Set (D x)) (Dt x : Set (D x))

/-! ### Consistency -/

/-- The projection of a constraint relation onto one argument position, inside a
reduction. -/
def Constraint.projIn (C : Constraint L D) (Dt : Reduction L D) (i : Fin C.arity) :
    Set (D (C.scope i)) :=
  {a | ∃ t ∈ C.rel, (∀ j, t j ∈ Dt (C.scope j)) ∧ t i = a}

/-- **1-consistency** of a reduction for an instance: every constraint, restricted to the
reduction, still projects onto the whole reduced domain at every position.
Blueprint `def:consistency`. -/
def OneConsistent (I : Instance L D) (Dt : Reduction L D) : Prop :=
  ∀ C ∈ I, ∀ i : Fin C.arity, C.projIn Dt i = (Dt (C.scope i) : Set (D (C.scope i)))

/-- The instance itself is 1-consistent when the trivial reduction is. -/
def Instance.OneConsistent (I : Instance L D) : Prop := CSP.OneConsistent I Reduction.top

/-! ### Linkedness

The graph Zhuk uses has vertices `Σ x, D x` and joins `(x,a)` to `(y,b)` when some
constraint's projection onto the pair contains `(a,b)`.  Following the Mathlib probe, we
take `Relation.ReflTransGen` of that relation as the definition rather than routing
through `SimpleGraph`, and keep the bridge to `SimpleGraph.Connected` for the places that
need connected components. -/

/-- One step of the link graph: some constraint of `I` relates `a` at `x` to `b` at `y`. -/
def LinkStep (I : Instance L D) : (Σ x, D x) → (Σ x, D x) → Prop := fun p q =>
  ∃ C ∈ I, ∃ (i j : Fin C.arity) (t : ∀ i : Fin C.arity, D (C.scope i)), t ∈ C.rel ∧
    ∃ hi : C.scope i = p.1, ∃ hj : C.scope j = q.1,
      hi ▸ t i = p.2 ∧ hj ▸ t j = q.2

/-- Two values of the same variable are connected by a path. -/
def Linked (I : Instance L D) (p q : Σ x, D x) : Prop :=
  Relation.ReflTransGen (LinkStep I) p q

theorem Linked.refl (I : Instance L D) (p : Σ x, D x) : Linked I p p :=
  Relation.ReflTransGen.refl

theorem Linked.trans {I : Instance L D} {p q r : Σ x, D x}
    (h₁ : Linked I p q) (h₂ : Linked I q r) : Linked I p r :=
  Relation.ReflTransGen.trans h₁ h₂

/-- **A linked instance**: every two values of every variable are connected.
Blueprint `def:instance-linked`.  Note this is a different predicate from `Linked` for a
binary relation (`haz:linked`); the two meet only in `lem:connected`(p). -/
def IsLinkedInstance (I : Instance L D) : Prop :=
  ∀ (x : V) (a b : D x), Linked I ⟨x, a⟩ ⟨x, b⟩

/-- **Cycle-consistency**: 1-consistent, and every closed path returns each value to
itself.  Blueprint `def:consistency`. -/
structure CycleConsistent (I : Instance L D) : Prop where
  one : I.OneConsistent
  /-- Every path from `x` back to `x` connects `a` only to `a`. -/
  cycle : ∀ (x : V) (a b : D x), Linked I ⟨x, a⟩ ⟨x, b⟩ → a = b

/-- Cycle-consistency and linkedness are incompatible unless every domain is a singleton
— which is why the main theorem needs both `irreducible` and `linked` instances and never
`cycle-consistent linked` ones with large domains. -/
theorem subsingleton_of_cycleConsistent_of_linked {I : Instance L D}
    (hc : CycleConsistent I) (hl : IsLinkedInstance I) (x : V) (a b : D x) : a = b :=
  hc.cycle x a b (hl x a b)

/-! ### Solution sets and subdirectness -/

/-- The solution set of `𝓘` is subdirect: every value of every variable extends to a
solution.  Blueprint `def:instance`. -/
def SolutionSetSubdirect (I : Instance L D) : Prop :=
  ∀ (x : V) (a : D x), ∃ s, IsSolution I s ∧ s x = a

/-- The relation an instance defines on a tuple of its variables.
Blueprint `def:instance-relation`. -/
def Instance.defines (I : Instance L D) {k : ℕ} (xs : Fin k → V) :
    Set (∀ i, D (xs i)) :=
  {t | ∃ s, IsSolution I s ∧ ∀ i, s (xs i) = t i}

/-! ### Weakening and cruciality -/

/-- `C₁` is weaker than or equivalent to `C₂` when every assignment satisfying `C₂`
satisfies `C₁`.  Blueprint `def:weakening`; note this is stated as a *relation*, never as
an operation producing "all weaker constraints" — see `haz:weakening`. -/
def Constraint.WeakerEq (C₁ C₂ : Constraint L D) : Prop :=
  ∀ s : Assignment D, C₂.Satisfies s → C₁.Satisfies s

/-- `𝓘'` is a weakening of `𝓘`. -/
def IsWeakening (I' I : Instance L D) : Prop :=
  ∀ C' ∈ I', ∃ C ∈ I, C'.WeakerEq C

theorem IsWeakening.refl (I : Instance L D) : IsWeakening I I :=
  fun C hC => ⟨C, hC, fun _ h => h⟩

theorem IsWeakening.solution {I' I : Instance L D} (h : IsWeakening I' I)
    {s : Assignment D} (hs : IsSolution I s) : IsSolution I' s := by
  intro C' hC'
  obtain ⟨C, hC, hle⟩ := h C' hC'
  exact hle s (hs C hC)

/-- An instance is **crucial** in a reduction: it has a constraint, has no solution there,
and weakening any single constraint restores one.  Blueprint `def:crucial`.

The "weakening" is expressed as: for each constraint there is a strictly weaker instance
obtained by replacing it, which has a solution.  Stating it with an existential over
weakenings, rather than with the literal "replace by all weaker constraints", is what
`haz:weakening` argues for. -/
structure Crucial (I : Instance L D) (Dt : Reduction L D) : Prop where
  nonempty : I ≠ []
  no_solution : ¬ SolvableIn I Dt
  weakening_solvable : ∀ C ∈ I, ∀ I' : Instance L D,
    IsWeakening I' I → (¬ ∃ C' ∈ I', C'.WeakerEq C ∧ C.WeakerEq C') → SolvableIn I' Dt

end CSP
