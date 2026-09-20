import MagnitudeConjecture.CategoryTheory.GradedModuleHomCategory
import MagnitudeConjecture.Graded.GradedSubmodule
import Mathlib.CategoryTheory.Idempotents.Basic

/-! # Splitting homogeneous idempotents of graded modules -/

set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.Graded.FiniteGradedModule

universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- The image of a degree-zero endomorphism as a finite graded module. -/
def imageObject (X : FiniteGradedModule.{u,v} R) (f : X.module →ₗ[A] X.module)
    (hf : X.grading.Homogeneous X.grading 0 f) : FiniteGradedModule.{u,v} R where
  module := ModuleCat.of A f.range
  finite := Module.Finite.of_injective (f.range.subtype.restrictScalars k) Subtype.val_injective
  grading := X.grading.rangeGrading X.grading f hf

/-- Homogeneous idempotents split through their actual module image. -/
instance : IsIdempotentComplete
    (GradedCategory.DegreeObject (homGrading (R := R) :
      GradedCategory.HomGrading k (FiniteGradedModule.{u,v} R))) where
  idempotents_split X p hp := by
    let f : X.obj.module →ₗ[A] X.obj.module := p.val
    have hf : X.obj.grading.Homogeneous X.obj.grading 0 f := by
      have hh := p.property
      change X.obj.grading.Homogeneous X.obj.grading (X.degree - X.degree) f at hh
      simpa only [sub_self] using hh
    let Y := imageObject X.obj f hf
    let Z : GradedCategory.DegreeObject homGrading := ⟨Y, X.degree⟩
    have hff : f.comp f = f := congrArg Subtype.val hp
    let i : Z ⟶ X := ⟨f.range.subtype, by
      intro d x hx
      change x.val ∈ X.obj.grading.component (d + (X.degree - X.degree))
      change x.val ∈ X.obj.grading.component d at hx
      simpa only [sub_self, add_zero] using hx⟩
    let e : X ⟶ Z := ⟨f.rangeRestrict, by
      intro d x hx
      change f x ∈ X.obj.grading.component (d + (X.degree - X.degree))
      simpa only [sub_self, add_zero] using hf d x hx⟩
    refine ⟨Z, i, e, ?_, ?_⟩
    · apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      obtain ⟨y, hy⟩ := x.property
      change f x.val = x.val
      rw [← hy]
      exact LinearMap.congr_fun hff y
    · apply Subtype.ext
      rfl

end MagnitudeConjecture.Graded.FiniteGradedModule
