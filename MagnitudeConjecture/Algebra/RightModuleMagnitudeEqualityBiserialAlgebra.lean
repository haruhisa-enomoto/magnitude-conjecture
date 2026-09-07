import MagnitudeConjecture.Algebra.RightModuleMagnitudeEqualityBiserialCover
import MagnitudeConjecture.Algebra.RightModuleStandardFormLiftedOrbitAlgebra
import MagnitudeConjecture.Algebra.RightModuleStandardFormProjectiveDeckOrbit
import MagnitudeConjecture.Algebra.BiserialLeftIdealOpposite
import MagnitudeConjecture.Algebra.BiserialProjectivePresentation
import MagnitudeConjecture.Algebra.RightModulePrimitiveSpecialBiserial
import MagnitudeConjecture.Algebra.SpecialBiserialAlgebra
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraBiserial
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraOpposite

/-!
# Biserial projectives of the standard-form algebra at magnitude equality

The equality-case biserial representables on the universe-lifted strict
deck-orbit skeleton transport through the literal object-bijective orbit
reindexings to every representable of the opposite projective standard-form
mesh category.  The finite-category projective-generator equivalence then
identifies these with every canonical principal right ideal of the
manuscript's standard-form algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMagnitudeEqualityBiserialAlgebraQuiver :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormMagnitudeEqualityBiserialAlgebraArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance
    standardFormMagnitudeEqualityBiserialAlgebraFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormMagnitudeEqualityBiserialAlgebraNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

local instance standardFormMagnitudeEqualityBiserialAlgebraLeftNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  IsNoetherianRing.of_finite k _

/-- The canonical summand projectors of the standard-form category algebra,
reindexed by the indecomposable projective labels of its module skeleton. -/
def standardFormPrimitiveProjectivePresentation :
    (S.standardFormAlgebraIndecomposableSkeleton
      (k := k)).PrimitiveProjectivePresentation :=
  CoveringHom.finiteCategoryProjectiveGenerator.primitiveProjectivePresentation
    (S.standardFormFiniteRightRepresentables S.standardFormMeshHomFinite)
    ((S.standardFormProjectiveMeshCategoryIsLocallyBounded
      S.standardFormMeshHomFinite).op.localEndomorphismRings)
    (S.standardFormAlgebraIndecomposableSkeleton (k := k))
    S.standardFormProjectiveMeshCategoryOppositeSkeletal

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

/-- At magnitude equality, every canonical principal right ideal of the
literal standard-form algebra is intrinsically biserial. -/
theorem
    standardFormCanonicalRightIdeal_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (P : S.StandardFormProjectiveMeshCategoryᵒᵖ) :
    IsBiserialObject
      (RightModule.rightIdealFGObj
        (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
          (S.standardFormFiniteRightRepresentables
            S.standardFormMeshHomFinite) P)) := by
  let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
  let hP := H.finiteCovariantRepresentables
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI : IsMulTorsionFree (ProjectiveGroup S x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient
      (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveDeckOrbitFinite S x₀ hconnected
  letI : Finite (MulAction.orbitRel.Quotient
      (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
  let hLift := StandardCovering.orbitFiniteCovariantRepresentables
    (k := k) D hP
  let hSmall := standardFormOppositeProjectiveDeckOrbitFiniteRightRepresentables
    S x₀ hconnected S.standardFormMeshHomFinite
  let hTarget := S.standardFormFiniteRightRepresentables
    S.standardFormMeshHomFinite
  let eLift := D₀.uliftDeckOrbitSkeletonEquivalence (k := k)
  letI : eLift.functor.Additive := by
    change (D₀.uliftDeckOrbitSkeletonFunctor (k := k)).Additive
    infer_instance
  letI : eLift.functor.Linear k := by
    change (D₀.uliftDeckOrbitSkeletonFunctor (k := k)).Linear k
    infer_instance
  let eTarget := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    S x₀ hconnected
  letI : eTarget.functor.Additive := inferInstance
  letI : eTarget.functor.Linear k := inferInstance
  let hLiftObj := D₀.uliftDeckOrbitSkeletonFunctor_obj_bijective (k := k)
  let hTargetObj :=
    standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_bijective
      S x₀ hconnected
  obtain ⟨qSmall, rfl⟩ := hTargetObj.2 P
  obtain ⟨qLift, rfl⟩ := hLiftObj.2 qSmall
  have hqLift : IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) qLift (hLift qLift)) :=
    standardFormOppositeProjective_orbitSkeleton_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero qLift
  have hqSmall : IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) (eLift.functor.obj qLift)
          (hSmall (eLift.functor.obj qLift))) :=
    (CoveringHom.finiteDimensionalLinearCoyoneda_isBiserialObject_iff_of_equivalence
      hLift hSmall eLift hLiftObj qLift).2 hqLift
  have hqTarget : IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) (eTarget.functor.obj (eLift.functor.obj qLift))
          (hTarget (eTarget.functor.obj (eLift.functor.obj qLift)))) :=
    (CoveringHom.finiteDimensionalLinearCoyoneda_isBiserialObject_iff_of_equivalence
      hSmall hTarget eTarget hTargetObj (eLift.functor.obj qLift)).2 hqSmall
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.canonicalRightIdeal_isBiserialObject_of_covariantRepresentable
      hTarget (eTarget.functor.obj (eLift.functor.obj qLift)) hqTarget

/-- At magnitude equality, every left representable of the literal
standard-form projective mesh category is intrinsically biserial. -/
theorem
    standardFormProjectiveMesh_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (P : S.StandardFormProjectiveMeshCategory) :
    IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) P
        (S.standardFormFiniteCovariantRepresentables
          S.standardFormMeshHomFinite P)) := by
  let H := standardFormProjectiveSourceCategoryIsLocallyBounded S x₀
  let hP := H.finiteCovariantRepresentables
  let D₀ := standardFormProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI : IsMulTorsionFree (ProjectiveGroup S x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hLift := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hTarget := S.standardFormFiniteCovariantRepresentables
    S.standardFormMeshHomFinite
  let eLift := D₀.uliftDeckOrbitSkeletonEquivalence (k := k)
  letI : eLift.functor.Additive := by
    change (D₀.uliftDeckOrbitSkeletonFunctor (k := k)).Additive
    infer_instance
  letI : eLift.functor.Linear k := by
    change (D₀.uliftDeckOrbitSkeletonFunctor (k := k)).Linear k
    infer_instance
  let eTarget := standardFormProjectiveIndexedDeckOrbitEquivalence
    S x₀ hconnected
  letI : eTarget.functor.Additive := inferInstance
  letI : eTarget.functor.Linear k := inferInstance
  let hLiftObj := D₀.uliftDeckOrbitSkeletonFunctor_obj_bijective (k := k)
  let hTargetObj :=
    standardFormProjectiveIndexedDeckOrbitEquivalence_obj_bijective
      S x₀ hconnected
  letI : Finite (MulAction.orbitRel.Quotient
      (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)) :=
    Finite.of_injective eTarget.functor.obj hTargetObj.1
  letI : Finite (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)
      (ProjectiveGroup S x₀)) := by
    change Finite (MulAction.orbitRel.Quotient
      (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀))
    infer_instance
  letI : Fintype (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)
      (ProjectiveGroup S x₀)) := Fintype.ofFinite _
  let hSmall := CoveringHom.linearCoyonedaFiniteOfFullyFaithful
    (k := k) eTarget.functor hTarget
  obtain ⟨qSmall, rfl⟩ := hTargetObj.2 P
  obtain ⟨qLift, rfl⟩ := hLiftObj.2 qSmall
  have hqLift : IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) qLift (hLift qLift)) :=
    standardFormProjectiveSource_orbitSkeleton_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero qLift
  have hqSmall : IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) (eLift.functor.obj qLift)
          (hSmall (eLift.functor.obj qLift))) :=
    (CoveringHom.finiteDimensionalLinearCoyoneda_isBiserialObject_iff_of_equivalence
      hLift hSmall eLift hLiftObj qLift).2 hqLift
  exact
    (CoveringHom.finiteDimensionalLinearCoyoneda_isBiserialObject_iff_of_equivalence
      hSmall hTarget eTarget hTargetObj (eLift.functor.obj qLift)).2 hqSmall

/-- At magnitude equality, every canonical principal left ideal of the
literal standard-form algebra is intrinsically biserial. -/
theorem
    standardFormCanonicalLeftIdeal_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (P : S.StandardFormProjectiveMeshCategoryᵒᵖ) :
    IsBiserialObject
      (RightModule.leftIdealFGObj (k := k)
        (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
          (S.standardFormFiniteRightRepresentables
            S.standardFormMeshHomFinite) P)) := by
  let hC := S.standardFormFiniteCovariantRepresentables
    S.standardFormMeshHomFinite
  let hOp := S.standardFormFiniteRightRepresentables
    S.standardFormMeshHomFinite
  let B := CoveringHom.finiteCategoryProjectiveGenerator.algebra hC
  let A₀ := CoveringHom.finiteCategoryProjectiveGenerator.algebra hOp
  letI : FiniteDimensional k B :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hC
  letI : FiniteDimensional k A₀ :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hOp
  letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite k Bᵐᵒᵖ
  letI : IsNoetherianRing A₀ := IsNoetherianRing.of_finite k A₀
  letI : IsNoetherianRing A₀ᵐᵒᵖ := IsNoetherianRing.of_finite k A₀ᵐᵒᵖ
  letI : IsNoetherianRing (A₀ᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k (A₀ᵐᵒᵖ)ᵐᵒᵖ
  have hRep : IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) P.unop (hC P.unop)) :=
    standardFormProjectiveMesh_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero P.unop
  have hRightB : IsBiserialObject
      (RightModule.rightIdealFGObj
        (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
          hC P.unop)) :=
    CoveringHom.finiteCategoryProjectiveGenerator.canonicalRightIdeal_isBiserialObject_of_covariantRepresentable
      hC P.unop hRep
  let f : B ≃ₐ[k] A₀ᵐᵒᵖ :=
    CoveringHom.finiteCategoryProjectiveGenerator.categoryAlgebraOppositeEquiv
      hC hOp
  have hOppRight : IsBiserialObject
      (RightModule.rightIdealFGObj
        (MulOpposite.op
          (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
            hOp P))) := by
    have hMapped :=
      (RightModule.rightIdealFGObj_isBiserialObject_mapAlgEquiv_iff
        f
        (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
          hC P.unop)).2 hRightB
    rw [CoveringHom.finiteCategoryProjectiveGenerator.categoryAlgebraOppositeEquiv_canonicalProjector]
      at hMapped
    simpa using hMapped
  exact
    (RightModule.leftIdealFGObj_isBiserialObject_iff_oppositeRightIdeal
      (k := k)
      (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
        hOp P)).2 hOppRight

/-- Equality makes both the right and left canonical principal projectives
of the literal standard-form algebra intrinsically biserial. -/
theorem
    standardFormCanonicalPrincipalIdeals_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0) :
    (∀ P : S.StandardFormProjectiveMeshCategoryᵒᵖ,
      IsBiserialObject
        (RightModule.rightIdealFGObj
          (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
            (S.standardFormFiniteRightRepresentables
              S.standardFormMeshHomFinite) P))) ∧
    (∀ P : S.StandardFormProjectiveMeshCategoryᵒᵖ,
      IsBiserialObject
        (RightModule.leftIdealFGObj (k := k)
          (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
            (S.standardFormFiniteRightRepresentables
              S.standardFormMeshHomFinite) P))) := by
  constructor
  · exact
      standardFormCanonicalRightIdeal_isBiserialObject_of_ambientARSurplus_eq_zero
        S x₀ hconnected hzero
  · exact
      standardFormCanonicalLeftIdeal_isBiserialObject_of_ambientARSurplus_eq_zero
        S x₀ hconnected hzero

/-- At magnitude equality, the canonical complete primitive-projective
presentation of the literal standard-form algebra is biserial. -/
theorem
    standardFormPrimitiveProjectivePresentation_isBiserial_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0) :
    (S.standardFormPrimitiveProjectivePresentation
      (k := k)).IsBiserial := by
  let hP := S.standardFormFiniteRightRepresentables
    S.standardFormMeshHomFinite
  let hlocal :=
    (S.standardFormProjectiveMeshCategoryIsLocallyBounded
      S.standardFormMeshHomFinite).op.localEndomorphismRings
  let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let hskel := S.standardFormProjectiveMeshCategoryOppositeSkeletal
  change
    (∀ p : T.ProjectiveLabel,
      IsBiserialObject
        (RightModule.rightIdealFGObj
          (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
            hP
            ((CoveringHom.finiteCategoryProjectiveGenerator.canonicalSourceEquiv
              hP hlocal T hskel).symm p)))) ∧
    (∀ p : T.ProjectiveLabel,
      IsBiserialObject
        (RightModule.leftIdealFGObj (k := k)
          (CoveringHom.finiteCategoryProjectiveGenerator.canonicalProjector
            hP
            ((CoveringHom.finiteCategoryProjectiveGenerator.canonicalSourceEquiv
              hP hlocal T hskel).symm p))))
  constructor
  · intro p
    exact
      standardFormCanonicalRightIdeal_isBiserialObject_of_ambientARSurplus_eq_zero
        S x₀ hconnected hzero _
  · intro p
    exact
      standardFormCanonicalLeftIdeal_isBiserialObject_of_ambientARSurplus_eq_zero
        S x₀ hconnected hzero _

/-- At magnitude equality, the literal standard-form algebra admits the
manuscript's special-biserial bound-quiver presentation. -/
theorem
    standardFormAlgebra_admitsSpecialBiserialPresentation_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0) :
    BoundQuiver.AdmitsSpecialBiserialPresentation k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  (S.standardFormPrimitiveProjectivePresentation (k := k))
    |>.ambient_admitsSpecialBiserialPresentation_of_isBiserial
      (standardFormPrimitiveProjectivePresentation_isBiserial_of_ambientARSurplus_eq_zero
        S x₀ hconnected hzero)

/-- At magnitude equality, the standard-form algebra is special biserial in
the manuscript's Morita-invariant sense. -/
theorem standardFormAlgebra_isSpecialBiserial_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0) :
    BoundQuiver.IsSpecialBiserial k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  BoundQuiver.isSpecialBiserial_of_presentation
    (standardFormAlgebra_admitsSpecialBiserialPresentation_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero)

/-- At magnitude equality, the first radical layer of every canonical
principal right ideal of the standard-form algebra has length at most two. -/
theorem
    standardFormCanonicalRightIdeal_top_jacobson_length_le_two_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (p : (S.standardFormAlgebraIndecomposableSkeleton
      (k := k)).ProjectiveLabel) :
    Module.length
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ
      (Module.jacobson
          (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ
          (RightModule.rightIdealFGObj
            ((S.standardFormPrimitiveProjectivePresentation
              (k := k)).idempotent p)) ⧸
        Module.jacobson
          (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ
          (Module.jacobson
            (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ
            (RightModule.rightIdealFGObj
              ((S.standardFormPrimitiveProjectivePresentation
                (k := k)).idempotent p)))) ≤ 2 :=
  (standardFormPrimitiveProjectivePresentation_isBiserial_of_ambientARSurplus_eq_zero
    S x₀ hconnected hzero).rightIdeal_top_jacobson_length_le_two p

/-- At magnitude equality, the first radical layer of every canonical
principal left ideal of the standard-form algebra has length at most two. -/
theorem
    standardFormCanonicalLeftIdeal_top_jacobson_length_le_two_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (p : (S.standardFormAlgebraIndecomposableSkeleton
      (k := k)).ProjectiveLabel) :
    Module.length
      (S.standardFormAlgebra S.standardFormMeshHomFinite)
      (Module.jacobson
          (S.standardFormAlgebra S.standardFormMeshHomFinite)
          (RightModule.leftIdealFGObj (k := k)
            ((S.standardFormPrimitiveProjectivePresentation
              (k := k)).idempotent p)) ⧸
        Module.jacobson
          (S.standardFormAlgebra S.standardFormMeshHomFinite)
          (Module.jacobson
            (S.standardFormAlgebra S.standardFormMeshHomFinite)
            (RightModule.leftIdealFGObj (k := k)
              ((S.standardFormPrimitiveProjectivePresentation
                (k := k)).idempotent p)))) ≤ 2 :=
  (standardFormPrimitiveProjectivePresentation_isBiserial_of_ambientARSurplus_eq_zero
    S x₀ hconnected hzero).leftIdeal_top_jacobson_length_le_two p

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
