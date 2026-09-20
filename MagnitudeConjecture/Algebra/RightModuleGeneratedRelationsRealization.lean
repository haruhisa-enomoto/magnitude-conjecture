import MagnitudeConjecture.Algebra.RightModuleFactorCoordinate
import MagnitudeConjecture.Algebra.RightModuleIyamaBoundaryCover
import MagnitudeConjecture.Algebra.RightModuleIncidenceFullness
import MagnitudeConjecture.CategoryTheory.RepresentablePosetSpaceQuotient

/-! # Poset-space realization by generated relations -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable (S : FiniteIndecomposableSkeleton k A)
variable {T : Type u} [Fintype T] [PartialOrder T]

/-- A represented boundary cover realizes its target after quotienting its
underlying module by the relations generated at e. -/
theorem exists_realization_of_generated_relations
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (R : S.PrimitiveProjectivePosetData (S.primitiveMultiplicityInput D) T)
    (X : S.FactorCategory (S.primitiveKilledLabels D))
    (Y : PosetSpace.Obj k T) (c : R.representableData.obj X ⟶ Y)
    (hc : PosetSpace.BoundarySurjective c) :
    ∃ M : S.FactorCategory (S.primitiveKilledLabels D),
      Nonempty (R.representableData.obj M ≅ Y) := by
  let : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let : HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ) := CategoryTheory.hasExt_of_enoughProjectives _
  let E₀ := S.primitiveFactorCoordinateEquiv D X
  let π : idempotentCoordinate (k := k) e X.as.obj →ₗ[k] Y :=
    c.linear.comp E₀.symm.toLinearMap
  have hπ : Function.Surjective π := hc.1.comp E₀.symm.surjective
  let J := LinearMap.ker π
  let M := S.generatedRelationsFactorObj D X J
  let q := S.generatedRelationsFactorMap D X J
  let E : (R.representableData.source ⟶ M) ≃ₗ[k] Y :=
    (S.primitiveFactorCoordinateEquiv D M).trans
      (generatedRelations_coordinateEquivTarget D.idempotent
        (S.primitive_opposite_corner_scalar H D) X.as.obj π hπ)
  have hE : ∀ f : R.representableData.source ⟶ X, E (f ≫ q) = c.linear f := by
    intro f
    change generatedRelations_coordinateEquivTarget D.idempotent
      (S.primitive_opposite_corner_scalar H D) X.as.obj π hπ
      (S.primitiveFactorCoordinateEquiv D M (f ≫ q)) = c.linear f
    rw [S.generatedRelationsFactorMap_coordinate D X J f]
    rw [generatedRelations_coordinateEquivTarget_map]
    change c.linear (E₀.symm (E₀ f)) = c.linear f
    rw [E₀.symm_apply_apply]
  refine ⟨M, ⟨R.representableData.isoOfQuotientCover c hc q E hE ?_⟩⟩
  intro t f
  exact S.generatedRelationsFactorMap_hom_lift D (R.projectiveEquiv.symm (some t)) X J f

/-- Every finite poset space is realized by the generated-relations quotient
of the explicit source-and-projective presentation. -/
theorem generatedRelations_essentiallySurjective
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (R : S.PrimitiveProjectivePosetData (S.primitiveMultiplicityInput D) T)
    (Y : PosetSpace.Obj k T) :
    ∃ M : S.FactorCategory (S.primitiveKilledLabels D),
      Nonempty (R.representableData.obj M ≅ Y) :=
  S.exists_realization_of_generated_relations H D R (R.boundaryCoverObject Y) Y
    (R.representedBoundaryCoverMap H Y)
    (R.representedBoundaryCoverMap_boundarySurjective H Y)

/-- The primitive realization equivalence uses generated relations for
essential surjectivity and the existing directed-mesh fullness proof. -/
def generatedRelationsEquivalenceData
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (R : S.PrimitiveProjectivePosetData (S.primitiveMultiplicityInput D) T) :
    PosetSpace.RepresentableData.EquivalenceData R.representableData where
  full := fun f ↦ (R.representable_full H).map_surjective f
  faithful := fun _ _ h ↦ R.representable_faithful.map_injective h
  essSurj := S.generatedRelations_essentiallySurjective H D R

/-- The generated-relations equivalence on the literal primitive factor. -/
def generatedRelationsEquivalence
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (R : S.PrimitiveProjectivePosetData (S.primitiveMultiplicityInput D) T) :
    S.FactorCategory (S.primitiveKilledLabels D) ≌ PosetSpace.Obj k T :=
  (S.generatedRelationsEquivalenceData H D R).equivalence

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
