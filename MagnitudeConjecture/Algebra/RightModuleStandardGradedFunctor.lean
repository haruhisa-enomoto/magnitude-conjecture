import MagnitudeConjecture.Algebra.RightModuleStandardGradedRepresentatives

/-! # Fully faithful realization by standard-form graded modules -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The graded generator realization, retaining all underlying module maps. -/
def standardFormGradedFunctor : Mat_ S.StandardFormMeshCategory ⥤
    Graded.FiniteGradedModule (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite) where
  obj := S.standardFormGradedObject S.standardFormMeshHomFinite
  map := S.standardFormGradedMap S.standardFormMeshHomFinite
  map_id X := by apply LinearMap.ext; intro x; exact Category.comp_id x
  map_comp f g := by apply LinearMap.ext; intro x; exact (Category.assoc x f g).symm

instance : S.standardFormGradedFunctor.Additive where
  map_add := by
    intro X Y f g
    apply LinearMap.ext
    intro x
    change x ≫ (f + g) = x ≫ f + x ≫ g
    exact Preadditive.comp_add _ _ _ _ _ _

instance : S.standardFormGradedFunctor.Linear k where
  map_smul := by
    intro X Y f c
    apply LinearMap.ext
    intro x
    let := S.standardFormHomModuleAction S.standardFormMeshHomFinite Y
    let := S.standardFormHomModuleScalarTower S.standardFormMeshHomFinite Y
    change x ≫ (c • f) = (algebraMap k
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ c) • (x ≫ f)
    rw [IsScalarTower.algebraMap_smul]
    exact Linear.comp_smul _ _ _ _ _ _

/-- Forgetting this realization agrees naturally with the established standard-form equivalence. -/
def standardFormGradedUnderlyingNatIso :
    S.standardFormGradedFunctor ⋙ Graded.FiniteGradedModule.underlying ≅
      S.standardGradedRecovery ⋙ S.standardFormProjectiveVertexModuleAlgebraEquivalence.functor ⋙
        forget₂ (RightModule.FinitelyGeneratedCategory
          (S.standardFormAlgebra S.standardFormMeshHomFinite))
          (RightModule.Category (S.standardFormAlgebra S.standardFormMeshHomFinite)) :=
  NatIso.ofComponents S.standardFormGradedObjectUnderlyingIso (by
    intro X Y f
    ext x
    exact (MagnitudeConjecture.CategoryTheory.representedHomEquiv_postcomp (k := k)
      S.standardGradedRecovery S.standardGradedRecoveryGeneratorIso x f))

instance : S.standardFormGradedFunctor.Full :=
  Functor.Full.of_comp_faithful_iso S.standardFormGradedUnderlyingNatIso

instance : S.standardFormGradedFunctor.Faithful :=
  Functor.Faithful.of_comp_iso S.standardFormGradedUnderlyingNatIso

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
