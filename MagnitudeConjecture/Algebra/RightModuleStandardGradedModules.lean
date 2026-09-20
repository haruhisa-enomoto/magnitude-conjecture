import MagnitudeConjecture.Algebra.RightModuleStandardGradedAlgebraComparison
import MagnitudeConjecture.Graded.AlgebraTransport

/-! # Graded modules over the existing standard-form algebra -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable (hfinite : S.StandardFormMeshHomFinite)

/-- Restrict the actual Hom-module action to the existing standard-form algebra. -/
def standardFormHomModuleAction (X : Mat_ S.StandardFormMeshCategory) :
    Module (S.standardFormAlgebra hfinite)ᵐᵒᵖ (⨁ S.standardGradedProjectiveFamily ⟶ X) :=
  Module.compHom _ (S.standardFormOppositeGeneratorAlgEquiv hfinite).toRingHom

/-- The transported right-module action is compatible with the original field scalars. -/
def standardFormHomModuleScalarTower (X : Mat_ S.StandardFormMeshCategory) :
    letI := S.standardFormHomModuleAction hfinite X
    IsScalarTower k (S.standardFormAlgebra hfinite)ᵐᵒᵖ
      (⨁ S.standardGradedProjectiveFamily ⟶ X) :=
  Graded.restrictedScalarTower (M := (⨁ S.standardGradedProjectiveFamily ⟶ X))
    (S.standardFormOppositeGeneratorAlgEquiv hfinite)

/-- The homogeneous components define a grading over the existing standard-form algebra. -/
def standardFormHomModuleGrading (X : Mat_ S.StandardFormMeshCategory) :
    letI := S.standardFormHomModuleAction hfinite X
    Graded.ModuleGrading (M := (⨁ S.standardGradedProjectiveFamily ⟶ X))
      (S.standardFormOppositeAlgebraGrading hfinite) :=
  (S.standardGradedGeneratorModule hfinite X).restrictAlgebra
    (S.standardFormOppositeGeneratorAlgEquiv hfinite)

include hfinite in
/-- These transported modules are finite-dimensional over the original field. -/
theorem standardFormHomModule_finite (X : Mat_ S.StandardFormMeshCategory) :
    FiniteDimensional k (⨁ S.standardGradedProjectiveFamily ⟶ X) := by
  letI : ∀ Y Z : S.StandardFormMeshCategory, FiniteDimensional k (Y ⟶ Z) := hfinite
  infer_instance

/-- Postcomposition as a map over the existing standard-form algebra. -/
def standardFormHomModuleMap {X Y : Mat_ S.StandardFormMeshCategory} (f : X ⟶ Y) :
    letI := S.standardFormHomModuleAction hfinite X
    letI := S.standardFormHomModuleAction hfinite Y
    (⨁ S.standardGradedProjectiveFamily ⟶ X) →ₗ[(S.standardFormAlgebra hfinite)ᵐᵒᵖ]
      (⨁ S.standardGradedProjectiveFamily ⟶ Y) :=
  Graded.restrictAlgebraMap (S.standardFormOppositeGeneratorAlgEquiv hfinite)
    (GradedCategory.HomGrading.generatorModuleMap S.standardGradedProjectiveFamily f)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
