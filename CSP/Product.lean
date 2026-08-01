/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Mathlib.ModelTheory.Substructures
import Mathlib.ModelTheory.Semantics

/-!
# Products of structures

Mathlib has no `Structure` instance on a dependent product: `ModelTheory.Ultraproducts`
goes straight to the quotient via `Prestructure` and never exposes `∀ i, M i`. The
blueprint needs plain products (Definition 1.8), so we build one here.

This is the only part of the blueprint's Part I that Mathlib does not already
supply.
-/

open FirstOrder Language

namespace CSP

section Products

variable {L : Language} {I : Type*} (M : I → Type*) [∀ i, L.Structure (M i)]

/-- The product structure: operations act coordinatewise. -/
instance piStructure : L.Structure (∀ i, M i) where
  funMap f x := fun i => Structure.funMap f (fun j => x j i)
  RelMap r x := ∀ i, Structure.RelMap r (fun j => x j i)

@[simp]
theorem funMap_pi {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ i, M i) (i : I) :
    Structure.funMap f x i = Structure.funMap f (fun j => x j i) :=
  rfl

end Products

section Preservation

variable {L : Language} {I : Type*} {M : I → Type*} [∀ i, L.Structure (M i)] {α : Type*}

/-- Terms are evaluated coordinatewise in a product. This is what the blueprint uses
under the name preservation (Lemma 1.14) once combined with `Substructure`. -/
@[simp]
theorem realize_pi (t : L.Term α) (v : α → ∀ i, M i) (i : I) :
    t.realize v i = t.realize (fun a => v a i) := by
  induction t with
  | var a => rfl
  | func f ts ih => simp [Term.realize, ih]

end Preservation

section BinaryProduct

variable {L : Language} {A B : Type*} [L.Structure A] [L.Structure B]

/-- The binary product structure, used for the relations `R ≤ A × B` of Part III. -/
instance prodStructure : L.Structure (A × B) where
  funMap f x := (Structure.funMap f fun i => (x i).1, Structure.funMap f fun i => (x i).2)
  RelMap r x := Structure.RelMap r (fun i => (x i).1) ∧ Structure.RelMap r fun i => (x i).2

@[simp]
theorem fst_funMap_prod {n : ℕ} (f : L.Functions n) (x : Fin n → A × B) :
    (Structure.funMap f x).1 = Structure.funMap f fun i => (x i).1 := rfl

@[simp]
theorem snd_funMap_prod {n : ℕ} (f : L.Functions n) (x : Fin n → A × B) :
    (Structure.funMap f x).2 = Structure.funMap f fun i => (x i).2 := rfl

/-- Terms are realized coordinatewise in a binary product. -/
@[simp]
theorem realize_prod {α : Type*} (t : L.Term α) (v : α → A × B) :
    t.realize v = (t.realize fun a => (v a).1, t.realize fun a => (v a).2) := by
  induction t with
  | var a => rfl
  | func f ts ih =>
      simp only [Term.realize, ih]
      rfl

/-- First projection of a binary product, as a homomorphism. -/
def fstHom : (A × B) →[L] A where
  toFun := Prod.fst
  map_fun' _ _ := rfl
  map_rel' _ _ h := h.1

/-- Second projection of a binary product, as a homomorphism. -/
def sndHom : (A × B) →[L] B where
  toFun := Prod.snd
  map_fun' _ _ := rfl
  map_rel' _ _ h := h.2

@[simp] theorem fstHom_apply (p : A × B) : fstHom (L := L) p = p.1 := rfl
@[simp] theorem sndHom_apply (p : A × B) : sndHom (L := L) p = p.2 := rfl

end BinaryProduct

section Snoc

variable {L : Language} {A : Type*} [L.Structure A]

/-- Appending a last coordinate commutes with the operations, because `Fin.snoc` acts
coordinatewise. Needed to see that the doubled relation of the doubling trick is a
subuniverse. -/
theorem snoc_funMap {n p : ℕ} (f : L.Functions p) (a : Fin p → (Fin n → A)) (b : Fin p → A) :
    Fin.snoc (Structure.funMap f a) (Structure.funMap f b)
      = Structure.funMap f (fun i => Fin.snoc (a i) (b i) : Fin p → (Fin (n + 1) → A)) := by
  funext r
  refine Fin.lastCases ?_ ?_ r
  · simp [funMap_pi]
  · intro r'
    simp [funMap_pi]

end Snoc

section Reindex

variable {L : Language} {M : Type*} [L.Structure M]

/-- Precomposition with a reindexing map is a homomorphism of powers. This packages
the blueprint's Lemma 1.19(c) (projection) and (e) (reindexing) in one map. -/
def reindexHom {I I' : Type*} (g : I' → I) : (I → M) →[L] (I' → M) where
  toFun x := x ∘ g
  map_fun' _ _ := rfl
  map_rel' _ _ h := fun i' => h (g i')

@[simp]
theorem reindexHom_apply {I I' : Type*} (g : I' → I) (x : I → M) :
    reindexHom (L := L) g x = x ∘ g := rfl

/-- Evaluation at one coordinate is a homomorphism from a power. -/
def evalHom {I : Type*} (i : I) : (I → M) →[L] M where
  toFun x := x i
  map_fun' _ _ := rfl
  map_rel' _ _ h := h i

@[simp]
theorem evalHom_apply {I : Type*} (i : I) (x : I → M) : evalHom (L := L) i x = x i := rfl

end Reindex

end CSP
