import MagnitudeConjecture.Algebra.RightModuleStandardGradedGenerator
import MagnitudeConjecture.Algebra.RightModuleStandardFormAlgebraSkeleton
import MagnitudeConjecture.CategoryTheory.LinearAdditiveEnvelopeLift
import MagnitudeConjecture.CategoryTheory.RepresentedHomTransport

/-! # Realization of the graded mesh generator by restricted Yoneda -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CoveringHom
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

instance standardFormRestrictedYonedaLinear :
    (S.standardFormRestrictedYonedaFunctor S.standardFormMeshHomFinite).Linear k where
  map_smul := by
    intro X Y f c
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    ext Z x
    change x ≫ (c • f) = c • (x ≫ f)
    exact Linear.comp_smul _ _ _ _ _ _

/-- Restricted Yoneda on the raw mesh additive envelope used by the grading. -/
def standardGradedRecovery : Mat_ S.StandardFormMeshCategory ⥤
    S.StandardFormProjectiveVertexModuleCategory (k := k) :=
  finiteMatrixLift (S.standardFormRestrictedYonedaFunctor S.standardFormMeshHomFinite)

instance : S.standardGradedRecovery.Additive := by
  unfold standardGradedRecovery
  infer_instance
instance : S.standardGradedRecovery.Linear k := by
  unfold standardGradedRecovery
  infer_instance
instance : S.standardGradedRecovery.Full := by
  unfold standardGradedRecovery
  infer_instance
instance : S.standardGradedRecovery.Faithful := by
  let := S.standardFormRestrictedYonedaFunctor_faithful
  unfold standardGradedRecovery
  infer_instance

/-- The realization of a singleton is its original restricted Yoneda module. -/
def standardGradedRecoverySingletonIso (X : S.StandardFormMeshCategory) :
    S.standardGradedRecovery.obj ((Mat_.embedding _).obj X) ≅
      (S.standardFormRestrictedYonedaFunctor S.standardFormMeshHomFinite).obj X :=
  biproductUniqueIso (fun _ : PUnit ↦
    (S.standardFormRestrictedYonedaFunctor S.standardFormMeshHomFinite).obj X)

/-- Each projective singleton realizes the corresponding representable. -/
def standardGradedRecoveryProjectiveIso (p : S.StandardFormProjectiveMeshCategory) :
    S.standardGradedRecovery.obj (S.standardGradedProjectiveFamily p) ≅
      finiteDimensionalLinearCoyoneda (C := S.StandardFormProjectiveMeshCategoryᵒᵖ)
        (k := k) (Opposite.op p)
        (S.standardFormFiniteRightRepresentables S.standardFormMeshHomFinite (Opposite.op p)) :=
  (S.standardGradedRecoverySingletonIso _).trans
    (S.standardFormProjectiveRestrictedYonedaIso p).symm

/-- The mesh projective sum realizes the category-algebra projective generator. -/
def standardGradedRecoveryGeneratorIso :
    S.standardGradedRecovery.obj (⨁ S.standardGradedProjectiveFamily) ≅
      finiteCategoryProjectiveGenerator
        (S.standardFormFiniteRightRepresentables S.standardFormMeshHomFinite) :=
  (S.standardGradedRecovery.mapBiproduct S.standardGradedProjectiveFamily).trans
    (biproduct.whiskerEquiv
      (Opposite.equivToOpposite (α := S.StandardFormProjectiveMeshCategory))
      (fun p ↦ (S.standardGradedRecoveryProjectiveIso p).symm))

/-- Algebra comparison induced directly by restricted Yoneda realization. -/
def standardGradedRecoveryEndEquiv :
    End (⨁ S.standardGradedProjectiveFamily) ≃ₐ[k]
      S.standardFormAlgebra S.standardFormMeshHomFinite :=
  MagnitudeConjecture.CategoryTheory.representedEndEquiv (k := k)
    S.standardGradedRecovery S.standardGradedRecoveryGeneratorIso

/-- The graded construction and restricted Yoneda have the same represented
right modules, with scalars transported by the realized algebra comparison. -/
def standardGradedRecoveryModuleEquiv (X : Mat_ S.StandardFormMeshCategory) :
    letI : Module S.StandardGradedGeneratorAlgebra
        (finiteCategoryProjectiveGenerator
          (S.standardFormFiniteRightRepresentables S.standardFormMeshHomFinite) ⟶
            S.standardGradedRecovery.obj X) :=
      Module.compHom _ (AlgEquiv.op S.standardGradedRecoveryEndEquiv).toRingHom
    (⨁ S.standardGradedProjectiveFamily ⟶ X) ≃ₗ[S.StandardGradedGeneratorAlgebra]
      (finiteCategoryProjectiveGenerator
        (S.standardFormFiniteRightRepresentables S.standardFormMeshHomFinite) ⟶
          S.standardGradedRecovery.obj X) :=
  MagnitudeConjecture.CategoryTheory.representedModuleEquiv (k := k)
    S.standardGradedRecovery S.standardGradedRecoveryGeneratorIso X

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
