/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import CSP.Irreducible

/-!
# Bridges

A bridge from `σ₁` to `σ₂` is a `4`-ary relation that "sees" `σ₁` in its first two
coordinates exactly when it sees `σ₂` in its last two.  Bridges are the mechanism by
which a local failure of consistency in one variable of a CSP instance is transported to
another variable; every use of connectedness in the main proof routes through them.

The collapse `δ̃(x,y) := δ(x,x,y,y)` is the binary relation a bridge leaves behind, and the
whole theory is organised around making `δ̃` large.

## Blueprint

`def:bridge`, `def:bridge-comp`, `lem:bridge-comp`, `def:perfect-linear` of
`ch2-vocabulary.tex`.
-/

open FirstOrder Language

universe u v w₁ w₂ w₃

namespace CSP

variable {L : Language.{u, v}}
variable {M₁ : Type w₁} {M₂ : Type w₂} {M₃ : Type w₃}
variable [L.Structure M₁] [L.Structure M₂] [L.Structure M₃]

/-- Zhuk's `δ ≤ 𝐃₁² × 𝐃₂²`, carried as a set of `4`-tuples written as nested pairs so that
the product structure of `CSP.Product` applies. -/
abbrev Quad (M₁ M₂ : Type*) := (M₁ × M₁) × (M₂ × M₂)

/-- A `4`-ary relation is a subuniverse of the corresponding product. -/
def IsSub4 (S : Set (Quad M₁ M₂)) : Prop :=
  ∀ {n : ℕ} (f : L.Functions n) (x : Fin n → Quad M₁ M₂),
    (∀ i, x i ∈ S) → Structure.funMap f x ∈ S

/-- **Bridge.**  Blueprint `def:bridge`.

Condition `sees` is the content: membership forces the first pair to be `σ₁`-related
exactly when the second is `σ₂`-related. -/
structure IsBridge (σ₁ : Congruence L M₁) (σ₂ : Congruence L M₂)
    (δ : Set (Quad M₁ M₂)) : Prop where
  /-- `δ` is a subuniverse of `𝐃₁² × 𝐃₂²`. -/
  sub : IsSub4 (L := L) δ
  /-- The first two variables are stable under `σ₁`. -/
  stable_left : ∀ a b a' c, ((a, b), c) ∈ δ → σ₁ a a' → ((a', b), c) ∈ δ
  /-- ... in the second coordinate too. -/
  stable_left' : ∀ a b b' c, ((a, b), c) ∈ δ → σ₁ b b' → ((a, b'), c) ∈ δ
  /-- The last two variables are stable under `σ₂`. -/
  stable_right : ∀ c a b a', (c, (a, b)) ∈ δ → σ₂ a a' → (c, (a', b)) ∈ δ
  /-- ... in the fourth coordinate too. -/
  stable_right' : ∀ c a b b', (c, (a, b)) ∈ δ → σ₂ b b' → (c, (a, b')) ∈ δ
  /-- The projection onto the first two coordinates properly contains `σ₁`. -/
  proj_left : σ₁.rel ⊂ {p : M₁ × M₁ | ∃ q, (p, q) ∈ δ}
  /-- The projection onto the last two coordinates properly contains `σ₂`. -/
  proj_right : σ₂.rel ⊂ {q : M₂ × M₂ | ∃ p, (p, q) ∈ δ}
  /-- The defining biconditional. -/
  sees : ∀ a b c d, ((a, b), (c, d)) ∈ δ → (σ₁ a b ↔ σ₂ c d)

/-- The collapse `δ̃` of a bridge: the binary relation `δ(x,x,y,y)`. -/
def collapse (δ : Set (Quad M₁ M₂)) : Set (M₁ × M₂) :=
  {p | ((p.1, p.1), (p.2, p.2)) ∈ δ}

@[simp] theorem mem_collapse {δ : Set (Quad M₁ M₂)} {a : M₁} {b : M₂} :
    (a, b) ∈ collapse δ ↔ ((a, a), (b, b)) ∈ δ := Iff.rfl

/-- A bridge on a single algebra is *reflexive* if it contains every constant `4`-tuple. -/
def IsReflexiveBridge (δ : Set (Quad M₁ M₁)) : Prop := ∀ a : M₁, ((a, a), (a, a)) ∈ δ

theorem collapse_refl_of_isReflexiveBridge {δ : Set (Quad M₁ M₁)}
    (h : IsReflexiveBridge δ) (a : M₁) : (a, a) ∈ collapse δ := h a

/-- The trivial bridge `δ(x₁,x₂,x₃,x₄) = σ(x₁,x₃) ∧ σ(x₂,x₄)`, which witnesses that every
proper congruence is adjacent to itself (blueprint `def:connected`). -/
def trivialBridge (σ : Congruence L M₁) : Set (Quad M₁ M₁) :=
  {q | σ q.1.1 q.2.1 ∧ σ q.1.2 q.2.2}

theorem isReflexiveBridge_trivialBridge (σ : Congruence L M₁) :
    IsReflexiveBridge (trivialBridge σ) := fun a => ⟨σ.refl a, σ.refl a⟩

/-- The inverse of a bridge, obtained by swapping the two halves. -/
def invBridge (δ : Set (Quad M₁ M₂)) : Set (Quad M₂ M₁) := {q | (q.2, q.1) ∈ δ}

@[simp] theorem mem_invBridge {δ : Set (Quad M₁ M₂)} {q : Quad M₂ M₁} :
    q ∈ invBridge δ ↔ (q.2, q.1) ∈ δ := Iff.rfl

theorem collapse_invBridge (δ : Set (Quad M₁ M₂)) :
    collapse (invBridge δ) = {p : M₂ × M₁ | (p.2, p.1) ∈ collapse δ} := rfl

/-- **Composition of bridges.**  Blueprint `def:bridge-comp`. -/
def compBridge (δ₁ : Set (Quad M₁ M₂)) (δ₂ : Set (Quad M₂ M₃)) : Set (Quad M₁ M₃) :=
  {q | ∃ y : M₂ × M₂, (q.1, y) ∈ δ₁ ∧ (y, q.2) ∈ δ₂}

/-- **Bridge composition.**  Blueprint `lem:bridge-comp`; Zhuk imports this from
`[ZhukJACM, Lemma 6.3]`.  Both conclusions are used: the first in every chain of bridges,
the second — that the collapse is functorial — in `lem:perfect-from-linked`. -/
theorem isBridge_compBridge {σ₁ : Congruence L M₁} {σ₂ : Congruence L M₂}
    {σ₃ : Congruence L M₃} {δ₁ : Set (Quad M₁ M₂)} {δ₂ : Set (Quad M₂ M₃)}
    (_h₁ : IsBridge σ₁ σ₂ δ₁) (_h₂ : IsBridge σ₂ σ₃ δ₂)
    (_hi₁ : Irreducible σ₁) (_hi₂ : Irreducible σ₂) (_hi₃ : Irreducible σ₃) :
    IsBridge σ₁ σ₃ (compBridge δ₁ δ₂) := by
  sorry

theorem collapse_compBridge {δ₁ : Set (Quad M₁ M₂)} {δ₂ : Set (Quad M₂ M₃)}
    (_h₁ : ∀ q ∈ δ₁, True) :
    collapse (compBridge δ₁ δ₂) ⊆
      {p : M₁ × M₃ | ∃ b : M₂, (p.1, b) ∈ collapse δ₁ ∧ (b, p.2) ∈ collapse δ₂} := by
  sorry

/-! ### Linear and PC congruences

Following blueprint `haz:linear-def`, we take the *bridge criterion* as the definition and
leave Zhuk's per-block `ℤ_p^m` description as a structure theorem to be proved later.  The
criterion is what every consumer uses, and it is a first-order condition over finite data
rather than an existential over quotients, primes and families of isomorphisms. -/

/-- A congruence is **linear** if it is irreducible and carries a self-bridge whose
collapse is strictly larger than the congruence. -/
structure IsLinear (σ : Congruence L M₁) : Prop where
  irreducible : Irreducible σ
  bridge : ∃ δ : Set (Quad M₁ M₁), IsBridge σ σ δ ∧
    σ.rel ⊂ {p : M₁ × M₁ | (p.1, p.2) ∈ collapse δ}

/-- A **PC congruence** is an irreducible congruence that is not linear. -/
def IsPC (σ : Congruence L M₁) : Prop := Irreducible σ ∧ ¬ IsLinear σ

theorem isLinear_or_isPC {σ : Congruence L M₁} (h : Irreducible σ) :
    IsLinear σ ∨ IsPC σ := by
  by_cases hl : IsLinear σ
  · exact Or.inl hl
  · exact Or.inr ⟨h, hl⟩

theorem not_isLinear_and_isPC {σ : Congruence L M₁} : ¬ (IsLinear σ ∧ IsPC σ) :=
  fun h => h.2.2 h.1

end CSP
