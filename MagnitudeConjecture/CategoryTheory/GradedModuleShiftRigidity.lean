import MagnitudeConjecture.CategoryTheory.GradedModuleHomCategory
import MagnitudeConjecture.Graded.ShiftRigidity

/-! # Uniqueness of shifts of actual graded modules -/

set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.Graded.FiniteGradedModule

universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- Distinct shifts of a nonzero finite-dimensional graded module are not
isomorphic by homogeneous degree-preserving maps. -/
theorem shift_eq_of_iso (X : FiniteGradedModule.{u,v} R) [Nontrivial X.module]
    (s t : ℤ)
    (e : (⟨X, s⟩ : GradedCategory.DegreeObject homGrading) ≅ ⟨X, t⟩) : s = t := by
  let f : X.module →ₗ[A] X.module := e.hom.val
  let g : X.module →ₗ[A] X.module := e.inv.val
  have hgf : g.comp f = LinearMap.id := by
    have hh := congrArg Subtype.val e.hom_inv_id
    exact hh
  have hf : Function.Injective f := by
    intro x y hxy
    have hh := congrArg g hxy
    have hx := LinearMap.congr_fun hgf x
    have hy := LinearMap.congr_fun hgf y
    change g (f x) = x at hx
    change g (f y) = y at hy
    rwa [hx, hy] at hh
  have hd : s - t = 0 := X.grading.toVectorGrading.degree_eq_zero_of_injective
    (s - t) (f.restrictScalars k) hf e.hom.property
  omega

end MagnitudeConjecture.Graded.FiniteGradedModule
