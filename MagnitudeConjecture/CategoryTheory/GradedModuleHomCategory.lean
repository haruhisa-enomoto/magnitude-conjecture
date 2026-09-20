import MagnitudeConjecture.Graded.ModuleHomGrading
import MagnitudeConjecture.CategoryTheory.GradedDegreeCategory
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # The Hom grading on actual finite-dimensional graded modules

Objects carry a grading, while the ambient morphisms are all module maps.
The degree category therefore supplies the homogeneous morphisms required by
the graded identity-splitting argument.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.Graded

universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- A finite-dimensional graded module, with its full ungraded Hom space. -/
structure FiniteGradedModule (R : VectorGrading k A) where
  module : ModuleCat.{v} A
  finite : FiniteDimensional k module
  grading : ModuleGrading (M := module) R

attribute [instance] FiniteGradedModule.finite

namespace FiniteGradedModule
variable {R : VectorGrading k A}

instance : Category (FiniteGradedModule.{u,v} R) where
  Hom X Y := X.module →ₗ[A] Y.module
  id _X := LinearMap.id
  comp f g := g.comp f
  id_comp _ := LinearMap.comp_id _
  comp_id _ := LinearMap.id_comp _
  assoc _ _ _ := rfl

instance : Preadditive (FiniteGradedModule.{u,v} R) where
  homGroup X Y := inferInstanceAs (AddCommGroup (X.module →ₗ[A] Y.module))
  add_comp X Y Z f g h := by
    change X.module →ₗ[A] Y.module at f g
    change Y.module →ₗ[A] Z.module at h
    change h.comp (f + g) = h.comp f + h.comp g
    ext x
    exact h.map_add (f x) (g x)
  comp_add X Y Z f g h := by
    change X.module →ₗ[A] Y.module at f
    change Y.module →ₗ[A] Z.module at g h
    change (g + h).comp f = g.comp f + h.comp f
    rfl

instance (X Y : FiniteGradedModule R) : Module k (X ⟶ Y) :=
  inferInstanceAs (Module k (X.module →ₗ[A] Y.module))

instance : Linear k (FiniteGradedModule.{u,v} R) where
  smul_comp X Y Z c f g := by
    change X.module →ₗ[A] Y.module at f
    change Y.module →ₗ[A] Z.module at g
    change g.comp (c • f) = c • g.comp f
    ext x
    exact g.map_smul_of_tower c (f x)
  comp_smul _ _ _ c f g := rfl

/-- Homogeneous components of actual module maps, with internal decomposition. -/
def homGrading : GradedCategory.HomGrading k (FiniteGradedModule.{u,v} R) where
  component X Y := X.grading.homComponent Y.grading
  internal X Y := X.grading.homComponent_isInternal Y.grading
  id_mem X := X.grading.id_homogeneous
  comp_mem := by
    intro X Y Z i j f g hf hg
    exact X.grading.homogeneous_comp Y.grading Z.grading hf hg

end FiniteGradedModule
end MagnitudeConjecture.Graded
