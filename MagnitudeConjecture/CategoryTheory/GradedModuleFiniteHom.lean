import MagnitudeConjecture.CategoryTheory.GradedModuleHomCategory
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite-dimensional Hom spaces of graded modules -/

set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.Graded.FiniteGradedModule

universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

instance finiteHom (X Y : FiniteGradedModule.{u,v} R) : FiniteDimensional k (X ⟶ Y) := by
  change FiniteDimensional k (X.module →ₗ[A] Y.module)
  exact Module.Finite.of_injective
    (LinearMap.restrictScalarsₗ k A X.module Y.module k) (LinearMap.restrictScalars_injective k)

instance finiteDegreeHom
    (X Y : GradedCategory.DegreeObject (homGrading (R := R) :
      GradedCategory.HomGrading k (FiniteGradedModule.{u,v} R))) :
    FiniteDimensional k (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional k (homGrading.component X.obj Y.obj (X.degree - Y.degree)))

end MagnitudeConjecture.Graded.FiniteGradedModule
