import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Endpoint-stable Hom subspaces

This file isolates the local categorical language used in the
Jans--Kupisch argument.  A Hom subspace is a subbimodule when it is stable
under precomposition and postcomposition by endpoint endomorphisms.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- A linear subspace of one Hom space stable under both endpoint
endomorphism rings. -/
def IsHomSubbimodule {X Y : C} (S : Submodule k (X ⟶ Y)) : Prop :=
  (∀ (a : End X) {f : X ⟶ Y}, f ∈ S → a.asHom ≫ f ∈ S) ∧
  (∀ (b : End Y) {f : X ⟶ Y}, f ∈ S → f ≫ b.asHom ∈ S)

/-- The linear span of all two-sided endpoint multiples of one morphism. -/
def twoSidedEndomorphismSpan {X Y : C} (f : X ⟶ Y) :
    Submodule k (X ⟶ Y) :=
  Submodule.span k {g | ∃ (a : End X) (b : End Y),
    g = (a.asHom ≫ f) ≫ b.asHom}

/-- A principal two-sided endomorphism span is endpoint-stable. -/
theorem isHomSubbimodule_twoSidedEndomorphismSpan
    {X Y : C} (f : X ⟶ Y) :
    IsHomSubbimodule (twoSidedEndomorphismSpan (k := k) f) := by
  constructor
  · intro a g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨c, d, rfl⟩
        apply Submodule.subset_span
        exact ⟨a.asHom ≫ c.asHom, d, by simp [Category.assoc]⟩
    | zero => simp
    | add g h _ _ hg hh =>
        simpa using
          (twoSidedEndomorphismSpan (k := k) f).add_mem hg hh
    | smul c g _ hg =>
        simpa using
          (twoSidedEndomorphismSpan (k := k) f).smul_mem c hg
  · intro b g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨a, c, rfl⟩
        apply Submodule.subset_span
        exact ⟨a, c.asHom ≫ b.asHom, by simp [Category.assoc]⟩
    | zero => simp
    | add g h _ _ hg hh =>
        simpa using
          (twoSidedEndomorphismSpan (k := k) f).add_mem hg hh
    | smul c g _ hg =>
        simpa using
          (twoSidedEndomorphismSpan (k := k) f).smul_mem c hg

/-- The generator belongs to its principal two-sided span. -/
theorem mem_twoSidedEndomorphismSpan
    {X Y : C} (f : X ⟶ Y) :
    f ∈ twoSidedEndomorphismSpan (k := k) f := by
  apply Submodule.subset_span
  exact ⟨1, 1, by simp⟩

/-- Membership in a principal two-sided span implies inclusion of principal
spans. -/
theorem twoSidedEndomorphismSpan_le_of_mem
    {X Y : C} {f g : X ⟶ Y}
    (hg : g ∈ twoSidedEndomorphismSpan (k := k) f) :
    twoSidedEndomorphismSpan (k := k) g ≤
      twoSidedEndomorphismSpan (k := k) f := by
  apply Submodule.span_le.2
  rintro h ⟨a, b, rfl⟩
  exact (isHomSubbimodule_twoSidedEndomorphismSpan (k := k) f).2 b
    ((isHomSubbimodule_twoSidedEndomorphismSpan (k := k) f).1 a hg)

/-- Every source endomorphism can be transferred across a morphism to its
target endpoint. -/
def AllowsTransit {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ a : End X, ∃ b : End Y, a.asHom ≫ f = f ≫ b.asHom

/-- Every target endomorphism can be transferred across a morphism to its
source endpoint. -/
def AllowsCotransit {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ b : End Y, ∃ a : End X, f ≫ b.asHom = a.asHom ≫ f

end MagnitudeConjecture
