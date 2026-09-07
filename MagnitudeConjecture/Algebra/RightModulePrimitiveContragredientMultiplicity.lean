import MagnitudeConjecture.Algebra.RightModuleContragredientMultiplicity
import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.AlmostSplitEquivalence

/-!
# Primitive relative multiplicities under contragredient duality

Dualizing the minimal left almost-split map of an original primitive new
mesh gives a minimal right almost-split map in the opposite primitive
quotient.  Uniqueness identifies its middle with the middle of the
constructed opposite new mesh.  Thus relative arrow multiplicities reverse
at the same literal labels, just as ambient arrow multiplicities do.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {e : A} {D : RightModule.PrimitiveIdempotentData e}

namespace PrimitiveNewRightMeshEndpoint

/-- The relative middle multiplicity of `Y → N` agrees with the relative
middle multiplicity of the reversed dual arrow `DN → DY`. -/
theorem contragredient_relativeArrowMultiplicity_eq
    [IsAlgClosed k] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (y : S.PrimitiveQuotientLabel D) :
    let Nop := N.contragredientNewMeshEndpoint H he
    let yop : S.contragredientSkeleton.PrimitiveQuotientLabel D.opposite :=
      ⟨y.1, (S.mem_contragredient_primitiveKilledLabels_iff D y.1).2 y.2⟩
    Nop.relativeArrowMultiplicity yop = N.relativeArrowMultiplicity y := by
  dsimp only
  let Sop := S.contragredientSkeleton
  let B := S.contragredientAlignedBiduality
  let E := primitiveQuotientContragredientEquivalence (k := k) e
  let Nop := N.contragredientNewMeshEndpoint H he
  let T := N.quotientShortComplex
  let Top := Nop.quotientShortComplex
  let source := N.sourceLabel H he
  let eSource : T.X₁ ≅ S.primitiveQuotientLabelObj D source :=
    ObjectProperty.isoMk _ (N.sourceIso H he)
  let eDualLabel :
      E.functor.obj (Opposite.op (S.primitiveQuotientLabelObj D source)) ≅
        S.contragredientPrimitiveQuotientLabelObj D source :=
    S.contragredientPrimitiveQuotientLabelObjIso D source
  let eEndpoint : E.functor.obj (Opposite.op T.X₁) ≅ Top.X₃ := by
    refine (E.functor.mapIso eSource.op).symm.trans (eDualLabel.trans ?_)
    change Sop.primitiveQuotientLabelObj D.opposite _ ≅
      Sop.primitiveQuotientLabelObj D.opposite Nop.label
    exact eqToIso (congrArg (Sop.primitiveQuotientLabelObj D.opposite)
      (Subtype.ext rfl))
  let g : E.functor.obj (Opposite.op T.X₂) ⟶ Top.X₃ :=
    E.functor.map T.f.op ≫ eEndpoint.hom
  have hTf := N.quotientShortComplex_f_minimalLeftAlmostSplit H he
  have hgAS : IsRightAlmostSplit g :=
    ((MagnitudeConjecture.CategoryTheory.leftAlmostSplit_op hTf.1)
      |>.map_equivalence E).postcomp_iso eEndpoint
  have hgMin : IsRightMinimal g :=
    ((MagnitudeConjecture.CategoryTheory.leftMinimal_op hTf.2)
      |>.map_equivalence E).postcomp_iso eEndpoint
  have hTop := Nop.quotientShortComplex_g_minimalRightAlmostSplit
    (S.contragredientSkeleton_hasAcyclicNonzeroNonisomorphisms H)
    D.opposite.idempotent
  obtain ⟨eMiddle, _heMiddle⟩ :=
    exists_rightAlmostSplit_middleIso hgAS hgMin hTop.1 hTop.2
  let eMiddleAmbient :
      B.forward.categoryEquiv.functor.obj (Opposite.op N.middleModule) ≅
        Nop.middleModule :=
    (RightModule.PrimitiveQuotientProperty (MulOpposite.op e)).ι.mapIso
      eMiddle
  change Sop.indecomposableMultiplicity y.1 Nop.middleModule =
    S.indecomposableMultiplicity y.1 N.middleModule
  calc
    Sop.indecomposableMultiplicity y.1 Nop.middleModule =
        Sop.indecomposableMultiplicity y.1
          (B.forward.categoryEquiv.functor.obj
            (Opposite.op N.middleModule)) :=
      (Sop.indecomposableMultiplicity_iso_invariant y.1
        eMiddleAmbient).symm
    _ = S.indecomposableMultiplicity y.1 N.middleModule :=
      S.indecomposableMultiplicity_map_alignedAntiEquivalence
        Sop B.forward y.1 N.middleModule

/-- Strict gain in the dual relative right mesh is exactly strict gain for
the reversed original pair.  This is the numerical core of the manuscript's
negative gaining-pair construction. -/
theorem contragredient_relative_gt_ambient_iff
    [IsAlgClosed k] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (y : S.PrimitiveQuotientLabel D) :
    let Nop := N.contragredientNewMeshEndpoint H he
    let yop : S.contragredientSkeleton.PrimitiveQuotientLabel D.opposite :=
      ⟨y.1, (S.mem_contragredient_primitiveKilledLabels_iff D y.1).2 y.2⟩
    (Nop.relativeArrowMultiplicity yop >
      FiniteTauMatrix.arrowMultiplicity
        S.contragredientSkeleton.finiteTauCategoryData.toFiniteRightTauCategoryData
        yop.1 Nop.label.1) ↔
      (N.relativeArrowMultiplicity y >
        FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData
          (N.sourceLabel H he).1 y.1) := by
  dsimp only
  rw [N.contragredient_relativeArrowMultiplicity_eq H he y]
  change N.relativeArrowMultiplicity y >
      FiniteTauMatrix.arrowMultiplicity
        S.contragredientSkeleton.finiteTauCategoryData.toFiniteRightTauCategoryData
        y.1 (S.contragredientNonprojectiveLabel
          (N.sourceNoninjectiveLabel H he)).1 ↔
    N.relativeArrowMultiplicity y >
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (N.sourceNoninjectiveLabel H he).1 y.1
  rw [S.contragredient_arrowMultiplicity_eq_reverse
    (N.sourceNoninjectiveLabel H he) y.1]

end PrimitiveNewRightMeshEndpoint
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
