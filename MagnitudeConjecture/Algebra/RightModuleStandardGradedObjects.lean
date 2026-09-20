import MagnitudeConjecture.Algebra.RightModuleStandardGradedModules
import MagnitudeConjecture.Graded.ModuleBundling

/-! # Standard-form modules as objects of the finite graded category -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable (hfinite : S.StandardFormMeshHomFinite)

/-- Bundle the transported generator module with its canonical field action. -/
def standardFormGradedObject (X : Mat_ S.StandardFormMeshCategory) :
    Graded.FiniteGradedModule (S.standardFormOppositeAlgebraGrading hfinite) := by
  letI := S.standardFormHomModuleAction hfinite X
  letI := S.standardFormHomModuleScalarTower hfinite X
  letI := S.standardFormHomModule_finite hfinite X
  exact (S.standardFormHomModuleGrading hfinite X).toBundled

/-- The graded object attached to a single mesh vertex. -/
def standardFormGradedVertex (X : S.StandardFormMeshCategory) :
    Graded.FiniteGradedModule (S.standardFormOppositeAlgebraGrading hfinite) :=
  S.standardFormGradedObject hfinite ((Mat_.embedding _).obj X)

/-- The map of bundled graded objects induced by any ambient morphism. -/
def standardFormGradedMap {X Y : Mat_ S.StandardFormMeshCategory} (f : X ⟶ Y) :
    S.standardFormGradedObject hfinite X ⟶ S.standardFormGradedObject hfinite Y :=
  S.standardFormHomModuleMap hfinite f

/-- Bundling and scalar transport preserve the degree of a represented map. -/
theorem standardFormGradedMap_homogeneous {X Y : Mat_ S.StandardFormMeshCategory}
    {d : ℤ} {f : X ⟶ Y} (hf : f ∈ (S.standardFormAdditiveHomGrading hfinite).component X Y d) :
    (S.standardFormGradedObject hfinite X).grading.Homogeneous
      (S.standardFormGradedObject hfinite Y).grading d (S.standardFormGradedMap hfinite f) := by
  letI : ∀ U V : S.StandardFormMeshCategory, FiniteDimensional k (U ⟶ V) := hfinite
  intro n x hx
  exact (S.standardFormAdditiveHomGrading hfinite).generatorHom_postcomp_mem
    S.standardGradedProjectiveFamily hx hf

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
