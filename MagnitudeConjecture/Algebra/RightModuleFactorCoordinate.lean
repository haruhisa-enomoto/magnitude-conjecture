import MagnitudeConjecture.Algebra.RightModuleGeneratedRelationsFactorLift

/-! # Primitive coordinates on arbitrary factor-category objects -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)

/-- The source-Hom space of a factor object is the e-coordinate of its
underlying finite module. -/
def primitiveFactorCoordinateEquiv {e : A} (D : PrimitiveIdempotentData e)
    (X : S.FactorCategory (S.primitiveKilledLabels D)) :
    (S.factorObject (S.primitiveKilledLabels D) (S.primitiveMultiplicityInput D).source ⟶ X)
      ≃ₗ[k] idempotentCoordinate (k := k) e X.as.obj :=
  (S.factorHomFromSelectedObjectLinearEquiv
    (S.primitiveMultiplicityInput D).noMapsFromKilled X.as).symm.trans
    ((InducedCategory.homLinearEquiv (R := k)).trans
      (S.primitiveSourceHomCoordinateEquiv D X.as.obj))

/-- The factor coordinate identification agrees with evaluation on any
chosen ambient representative of a source map. -/
theorem primitiveFactorCoordinateEquiv_map {e : A} (D : PrimitiveIdempotentData e)
    (X : S.FactorCategory (S.primitiveKilledLabels D))
    (f : S.ambientAddPoint (S.primitiveSourceLabel D) ⟶ X.as) :
    S.primitiveFactorCoordinateEquiv D X
      ((S.factorFunctor (S.primitiveKilledLabels D)).map f) =
      S.primitiveSourceHomCoordinateEquiv D X.as.obj f.hom := by
  change S.primitiveSourceHomCoordinateEquiv D X.as.obj
    ((S.factorHomFromSelectedObjectLinearEquiv
      (S.primitiveMultiplicityInput D).noMapsFromKilled X.as).symm
        ((S.factorHomFromSelectedObjectLinearEquiv
          (S.primitiveMultiplicityInput D).noMapsFromKilled X.as) f)).hom = _
  rw [LinearEquiv.symm_apply_apply]

/-- Evaluation is natural for a morphism of ambient finite modules. -/
theorem primitiveSourceHomCoordinateEquiv_comp
    {e : A} (D : PrimitiveIdempotentData e)
    {V W : FinitelyGeneratedCategory A}
    (f : S.fgObj (S.primitiveSourceLabel D) ⟶ V) (q : V ⟶ W) :
    S.primitiveSourceHomCoordinateEquiv D W (f ≫ q) =
      idempotentCoordinateMap e q (S.primitiveSourceHomCoordinateEquiv D V f) := by
  rfl

/-- Naturality of factor coordinates for a specified ambient representative
of a factor morphism. -/
theorem primitiveFactorCoordinateEquiv_comp_map
    {e : A} (D : PrimitiveIdempotentData e)
    (X Y : S.FactorCategory (S.primitiveKilledLabels D))
    (f : S.factorObject (S.primitiveKilledLabels D)
      (S.primitiveMultiplicityInput D).source ⟶ X)
    (q : X.as ⟶ Y.as) :
    S.primitiveFactorCoordinateEquiv D Y
      (f ≫ (S.factorFunctor (S.primitiveKilledLabels D)).map q) =
    idempotentCoordinateMap e q.hom (S.primitiveFactorCoordinateEquiv D X f) := by
  let F := S.factorFunctor (S.primitiveKilledLabels D)
  obtain ⟨f', rfl⟩ := F.map_surjective f
  rw [← F.map_comp f' q]
  rw [S.primitiveFactorCoordinateEquiv_map D Y,
    S.primitiveFactorCoordinateEquiv_map D X]
  exact S.primitiveSourceHomCoordinateEquiv_comp D f'.hom q.hom

/-- The new factor quotient map induces the canonical coordinate quotient. -/
theorem generatedRelationsFactorMap_coordinate
    {e : A} (D : PrimitiveIdempotentData e)
    (X : S.FactorCategory (S.primitiveKilledLabels D))
    (R : Submodule k (idempotentCoordinate (k := k) e X.as.obj))
    (f : S.factorObject (S.primitiveKilledLabels D)
      (S.primitiveMultiplicityInput D).source ⟶ X) :
    S.primitiveFactorCoordinateEquiv D (S.generatedRelationsFactorObj D X R)
      (f ≫ S.generatedRelationsFactorMap D X R) =
    idempotentCoordinateMap e (quotientFGMap X.as.obj (generatedCoordinateRelations e X.as.obj R))
      (S.primitiveFactorCoordinateEquiv D X f) :=
  S.primitiveFactorCoordinateEquiv_comp_map D X _ f _

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
