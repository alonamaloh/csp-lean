/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import CSP.Congruence

/-!
# Irreducible congruences and their covers

Zhuk's `σ*` is the least binary subuniverse of `𝐀 × 𝐀` that properly contains `σ` and is
stable under `σ`.  Two traps, both recorded in the blueprint (`haz:irreducible`):

* irreducibility here is **not** meet-irreducibility in the congruence lattice — the
  competing objects are binary subuniverses stable under `σ`, which need not be
  equivalence relations;
* `σ*` need not be a congruence.  That it is one is an extra hypothesis in the definition
  of a *linear* congruence, which would be redundant otherwise.

Accordingly `cover` is produced here as data attached to a proof of irreducibility, via
`Irreducible.exists_isCover`, rather than as a standalone function.

## Blueprint

`def:irreducible`, `haz:irreducible` of `ch2-vocabulary.tex`.
-/

open FirstOrder Language

universe u v w

namespace CSP

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- The underlying set of pairs of a congruence. -/
def Congruence.rel (σ : Congruence L M) : Set (M × M) := {p | σ p.1 p.2}

@[simp] theorem Congruence.mem_rel {σ : Congruence L M} {p : M × M} :
    p ∈ σ.rel ↔ σ p.1 p.2 := Iff.rfl

theorem Congruence.rel_subset_rel {σ τ : Congruence L M} : σ.rel ⊆ τ.rel ↔ σ ≤ τ := by
  constructor
  · intro h a b hab; exact h (show (a, b) ∈ σ.rel from hab)
  · intro h p hp; exact h p.1 p.2 hp

/-- A congruence is a binary subuniverse of `𝐀 × 𝐀`. -/
theorem Congruence.rel_closed (σ : Congruence L M) {n : ℕ} (f : L.Functions n)
    (x : Fin n → M × M) (hx : ∀ i, x i ∈ σ.rel) : Structure.funMap f x ∈ σ.rel :=
  σ.funMap_rel f _ _ hx

/-- A set of pairs is a binary subuniverse if it is closed under the basic operations of
the product structure. -/
def IsSub2 (S : Set (M × M)) : Prop :=
  ∀ {n : ℕ} (f : L.Functions n) (x : Fin n → M × M), (∀ i, x i ∈ S) → Structure.funMap f x ∈ S

/-- `S ⊆ M × M` is stable under `σ` in both variables: changing either coordinate to a
`σ`-related element keeps the pair in `S`.  Blueprint `def:stable`, specialised to arity
two, which is the only case `def:irreducible` uses. -/
def Stable2 (S : Set (M × M)) (σ : Congruence L M) : Prop :=
  (∀ a b a', (a, b) ∈ S → σ a a' → (a', b) ∈ S) ∧
  (∀ a b b', (a, b) ∈ S → σ b b' → (a, b') ∈ S)

theorem isSub2_rel (σ : Congruence L M) : IsSub2 (L := L) σ.rel := fun f x hx =>
  σ.rel_closed f x hx

theorem stable2_self (σ : Congruence L M) : Stable2 σ.rel σ :=
  ⟨fun _ _ _ hab h => σ.trans (σ.symm h) hab,
   fun _ _ _ hab h => σ.trans hab h⟩

theorem isSub2_univ : IsSub2 (L := L) (Set.univ : Set (M × M)) := fun _ _ _ => trivial

theorem stable2_univ (σ : Congruence L M) : Stable2 (Set.univ : Set (M × M)) σ :=
  ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

theorem isSub2_sInter {F : Set (Set (M × M))} (h : ∀ S ∈ F, IsSub2 (L := L) S) :
    IsSub2 (L := L) (⋂₀ F) := fun f x hx S hS => h S hS f x fun i => hx i S hS

theorem stable2_sInter {F : Set (Set (M × M))} {σ : Congruence L M}
    (h : ∀ S ∈ F, Stable2 S σ) : Stable2 (⋂₀ F) σ :=
  ⟨fun _ _ _ hab hσ S hS => (h S hS).1 _ _ _ (hab S hS) hσ,
   fun _ _ _ hab hσ S hS => (h S hS).2 _ _ _ (hab S hS) hσ⟩

/-- The family of binary subuniverses that are stable under `σ` and properly contain it.
These are the objects `def:irreducible` competes against. -/
def StrictStableSubs (σ : Congruence L M) : Set (Set (M × M)) :=
  {S | IsSub2 (L := L) S ∧ Stable2 S σ ∧ σ.rel ⊂ S}

/-- **Irreducible congruence.**  `σ` is not an intersection of binary subuniverses that
are stable under `σ` and properly contain it. -/
def Irreducible (σ : Congruence L M) : Prop :=
  ∀ F : Set (Set (M × M)), (∀ S ∈ F, S ∈ StrictStableSubs σ) → ⋂₀ F ≠ σ.rel

/-- `δ` is *the cover* `σ*` of `σ`: least among the binary subuniverses stable under `σ`
that properly contain it. -/
structure IsCover (σ : Congruence L M) (δ : Set (M × M)) : Prop where
  mem : δ ∈ StrictStableSubs σ
  least : ∀ S ∈ StrictStableSubs σ, δ ⊆ S

theorem IsCover.unique {σ : Congruence L M} {δ δ' : Set (M × M)}
    (h : IsCover σ δ) (h' : IsCover σ δ') : δ = δ' :=
  Set.Subset.antisymm (h.least _ h'.mem) (h'.least _ h.mem)

/-- **Existence of `σ*`.**  For an irreducible congruence that is not the full relation,
the intersection of all strictly larger stable binary subuniverses is itself one, and is
therefore the least.  This is the step the source states by writing "the minimal `δ`", and
it is exactly where irreducibility is consumed. -/
theorem Irreducible.exists_isCover {σ : Congruence L M} (h : Irreducible σ) :
    ∃ δ, IsCover σ δ := by
  classical
  refine ⟨⋂₀ StrictStableSubs σ, ?_, ?_⟩
  · refine ⟨isSub2_sInter fun S hS => hS.1, stable2_sInter fun S hS => hS.2.1, ?_⟩
    -- the intersection contains `σ`, and by irreducibility does not equal it
    have hsub : σ.rel ⊆ ⋂₀ StrictStableSubs σ := fun p hp S hS => hS.2.2.1 hp
    refine lt_of_le_of_ne hsub ?_
    exact fun hEq => h _ (fun _ hS => hS) hEq.symm
  · exact fun S hS p hp => hp S hS

/-- The universe is always a candidate, so `StrictStableSubs` is nonempty exactly when
`σ` is proper. -/
theorem univ_mem_strictStableSubs {σ : Congruence L M} (hne : σ.rel ≠ Set.univ) :
    (Set.univ : Set (M × M)) ∈ StrictStableSubs σ :=
  ⟨isSub2_univ, stable2_univ σ, lt_of_le_of_ne (Set.subset_univ _) hne⟩

/-- An irreducible congruence is proper.  The source never says this, because it reads
`σ*` as "the minimal congruence properly above `σ`" and tacitly assumes there is one; with
the definition taken literally, `⊤` fails to be irreducible because the *empty* family of
strictly larger stable subuniverses intersects to the universe.  Recording it keeps the
degenerate case from having to be excluded by hand at every use site. -/
theorem Irreducible.rel_ne_univ {σ : Congruence L M} (h : Irreducible σ) :
    σ.rel ≠ Set.univ := by
  intro hEq
  refine h ∅ (fun S hS => absurd hS (Set.notMem_empty S)) ?_
  rw [Set.sInter_empty, hEq]

end CSP
