/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Mathlib.ModelTheory.Substructures
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Quotient
import CSP.Product

/-!
# Congruences of a first-order structure

Mathlib has `Con` for monoids and rings, and `Setoid` with its complete lattice, but no
congruence of a general `FirstOrder.Language.Structure`.  `ModelTheory/Quotients.lean`
supplies `Prestructure`, which is a `Structure` bundled with a compatible `Setoid` — the
right data, but arranged so that the setoid is a parameter of a class rather than a
first-class object one can quantify over, intersect, or order.  Zhuk's argument quantifies
over congruences constantly (`σ`, `σ*`, "the intersection of all linear congruences ..."),
so we need them bundled.

## Main definitions

* `CSP.Congruence L M` — an equivalence relation on `M` compatible with the operations.
* `CSP.Congruence.Quotient` — the quotient structure.
* the complete lattice structure on `Congruence L M`.
* `CSP.StableAt` / `CSP.Stable` — Zhuk's stability of a relation under a congruence.

## Blueprint

Definitions `def:congruence`, `def:stable` of `ch2-vocabulary.tex`.
-/

open FirstOrder Language

universe u v w

namespace CSP

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- A congruence on a structure: an equivalence relation compatible with every basic
operation.  Compare `Mathlib.ModelTheory.Quotients.Prestructure`, which carries the same
compatibility condition but as a class indexed by the setoid. -/
structure Congruence (L : Language.{u, v}) (M : Type w) [L.Structure M] extends Setoid M where
  funMap_rel : ∀ {n : ℕ} (f : L.Functions n) (x y : Fin n → M),
    (∀ i, toSetoid.r (x i) (y i)) → toSetoid.r (Structure.funMap f x) (Structure.funMap f y)

namespace Congruence

instance : CoeFun (Congruence L M) (fun _ => M → M → Prop) :=
  ⟨fun c => c.toSetoid.r⟩

@[simp] theorem coe_toSetoid (c : Congruence L M) (a b : M) : c.toSetoid.r a b ↔ c a b :=
  Iff.rfl

theorem refl (c : Congruence L M) (a : M) : c a a := c.toSetoid.refl' a
theorem symm (c : Congruence L M) {a b : M} : c a b → c b a := c.toSetoid.symm'
theorem trans (c : Congruence L M) {a b d : M} : c a b → c b d → c a d := c.toSetoid.trans'

@[ext] theorem ext {c d : Congruence L M} (h : ∀ a b, c a b ↔ d a b) : c = d := by
  cases c; cases d
  congr 1
  exact Setoid.ext h

/-- Congruences are ordered by inclusion. -/
instance : LE (Congruence L M) := ⟨fun c d => ∀ a b, c a b → d a b⟩

theorem le_def {c d : Congruence L M} : c ≤ d ↔ ∀ a b, c a b → d a b := Iff.rfl

instance : PartialOrder (Congruence L M) where
  le_refl _ _ _ h := h
  le_trans _ _ _ hcd hde a b h := hde a b (hcd a b h)
  le_antisymm c d hcd hdc := ext fun a b => ⟨hcd a b, hdc a b⟩

/-- The trivial congruence `0_A`: equality.  Zhuk writes `0_𝐀`. -/
instance : Bot (Congruence L M) :=
  ⟨{ toSetoid := ⟨Eq, eq_equivalence⟩
     funMap_rel := fun _ x y h => by
       have : x = y := funext h
       simp [this] }⟩

/-- The full congruence `A²`. -/
instance : Top (Congruence L M) :=
  ⟨{ toSetoid := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
     funMap_rel := fun _ _ _ _ => trivial }⟩

@[simp] theorem bot_apply (a b : M) : (⊥ : Congruence L M) a b ↔ a = b := Iff.rfl
@[simp] theorem top_apply (a b : M) : (⊤ : Congruence L M) a b := trivial

/-- An arbitrary intersection of congruences is a congruence.  This is what makes
"the intersection of all linear congruences such that `σ* = A²`"
(`thm:codim-one`, hypothesis (iv)) well defined. -/
def sInf (S : Set (Congruence L M)) : Congruence L M where
  toSetoid :=
    { r := fun a b => ∀ c ∈ S, c a b
      iseqv :=
        ⟨fun a c _ => c.refl a,
         fun h c hc => c.symm (h c hc),
         fun h₁ h₂ c hc => c.trans (h₁ c hc) (h₂ c hc)⟩ }
  funMap_rel f x y h c hc := c.funMap_rel f x y fun i => h i c hc

theorem sInf_le {S : Set (Congruence L M)} {c : Congruence L M} (hc : c ∈ S) :
    sInf S ≤ c := fun _ _ h => h c hc

theorem le_sInf {S : Set (Congruence L M)} {c : Congruence L M} (h : ∀ d ∈ S, c ≤ d) :
    c ≤ sInf S := fun a b hab d hd => h d hd a b hab

instance : InfSet (Congruence L M) := ⟨sInf⟩
instance : Min (Congruence L M) := ⟨fun c d => sInf {c, d}⟩

theorem inf_apply (c d : Congruence L M) (a b : M) : (c ⊓ d) a b ↔ c a b ∧ d a b := by
  constructor
  · intro h; exact ⟨h c (by simp), h d (by simp)⟩
  · rintro ⟨h₁, h₂⟩ e he
    rcases he with he | he <;> subst he <;> assumption

/-! ### The quotient structure -/

section Quotient

variable (c : Congruence L M)

/-- The quotient of `M` by a congruence, as a type. -/
abbrev Quot := _root_.Quotient c.toSetoid

instance [Nonempty M] : Nonempty c.Quot := ⟨Quotient.mk c.toSetoid (Classical.arbitrary M)⟩

/-- The canonical surjection. -/
def proj (a : M) : c.Quot := Quotient.mk c.toSetoid a

theorem proj_eq_proj {a b : M} : c.proj a = c.proj b ↔ c a b := Quotient.eq

theorem proj_surjective : Function.Surjective c.proj := Quotient.mk_surjective

/-- The quotient structure.  Function symbols act on representatives; relation symbols
are given their direct image, which is the only choice available in general and is never
used here — Zhuk's languages are algebraic. -/
instance quotStructure : L.Structure c.Quot where
  funMap {n} f x :=
    Quotient.map (fun y : Fin n → M => Structure.funMap f y)
      (fun _ _ h => c.funMap_rel f _ _ h) (Quotient.finChoice x)
  RelMap {n} r x := ∃ y : Fin n → M, (∀ i, c.proj (y i) = x i) ∧ Structure.RelMap r y

@[simp] theorem funMap_proj {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    Structure.funMap f (fun i => c.proj (x i)) = c.proj (Structure.funMap f x) := by
  change Quotient.map _ _ (Quotient.finChoice fun i => Quotient.mk c.toSetoid (x i)) = _
  rw [Quotient.finChoice_eq, Quotient.map_mk]
  rfl

/-- The quotient map is a homomorphism. -/
def projHom : M →[L] c.Quot where
  toFun := c.proj
  map_fun' f x := (c.funMap_proj f x).symm
  map_rel' _r x h := ⟨x, fun _ => rfl, h⟩

@[simp] theorem projHom_apply (a : M) : c.projHom a = c.proj a := rfl

end Quotient

end Congruence

/-! ### Stability

Zhuk's relations live inside products, and stability is stated per coordinate.  We phrase
it for a relation on a product of a family, which is the form every use needs. -/

section Stable

variable {ι : Type*} [DecidableEq ι] {A : ι → Type*}

/-- The `i`-th variable of `R` is stable under the binary relation `σ` on `A i`:
replacing the `i`-th entry of a member of `R` by anything `σ`-related to it stays in `R`.
Blueprint `def:stable`. -/
def StableAt (R : Set (∀ i, A i)) (i : ι) (σ : A i → A i → Prop) : Prop :=
  ∀ a ∈ R, ∀ b, σ (a i) b → Function.update a i b ∈ R

/-- A relation on a power is stable under `σ` if every variable is. -/
def Stable {A : Type*} (R : Set (ι → A)) (σ : A → A → Prop) : Prop :=
  ∀ i : ι, ∀ a ∈ R, ∀ b, σ (a i) b → Function.update a i b ∈ R

theorem stable_iff_forall {A : Type*} (R : Set (ι → A))
    (σ : A → A → Prop) :
    Stable R σ ↔ ∀ i : ι, StableAt (A := fun _ => A) R i σ := Iff.rfl

end Stable

end CSP
