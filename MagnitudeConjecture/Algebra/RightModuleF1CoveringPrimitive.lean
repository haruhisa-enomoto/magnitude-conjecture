import MagnitudeConjecture.Algebra.RightModuleAlgebraEquiv
import MagnitudeConjecture.Algebra.RightModuleStandardFormLiftedOrbitAlgebra
import MagnitudeConjecture.Algebra.RightModuleStandardFormPeriodicComponent
import MagnitudeConjecture.Algebra.RightModuleStandardFormSurplus
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalDirected
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableBaseFreeness
import MagnitudeConjecture.CategoryTheory.StandardCoveringCategoryAlgebraDefs

/-!
# F1 primitive projectors in the literal standard-form algebra

The universe-lifted strict orbit algebra is identified with the standard-form
algebra.  This file transports the finite-support primitive projector across
that algebra equivalence, including the literal primitive quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace MagnitudeConjecture.StandardCovering

open MagnitudeConjecture.CoveringHom

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable {G : Type u} [Group G] [MulAction G C] [IsCancelSMul G C]

noncomputable instance orbitCategoryAlgebra_finiteDimensional
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    FiniteDimensional k (orbitCategoryAlgebra (k := k) D hP) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Category.{u} (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Category.{u} (DeckOrbitSkeleton C G) :=
    InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) :=
    Linear.inducedCategory _
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  exact finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (orbitFiniteCovariantRepresentables (k := k) D hP)

noncomputable instance orbitCategoryAlgebra_opposite_isNoetherian
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    IsNoetherianRing (orbitCategoryAlgebra (k := k) D hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

noncomputable abbrev orbitObject
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (x : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    DeckOrbitSkeleton C G := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (Quotient.mk'' x : MulAction.orbitRel.Quotient G C)

noncomputable abbrev orbitCategoryProjector
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (x : C) : orbitCategoryAlgebra (k := k) D hP := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Category.{u} (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Category.{u} (DeckOrbitSkeleton C G) :=
    InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) :=
    Linear.inducedCategory _
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  exact finiteCategoryProjectiveGenerator.canonicalProjector
    (orbitFiniteCovariantRepresentables (k := k) D hP)
    (orbitObject (k := k) D x)

theorem orbitCategoryProjectorPrimitive
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (x : C) :
    RightModule.PrimitiveIdempotentData
      (orbitCategoryProjector (k := k) D hP x) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Category.{u} (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Category.{u} (DeckOrbitSkeleton C G) :=
    InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) :=
    Linear.inducedCategory _
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hlocalDown :=
    D.orbitSkeleton_end_isLocalRing (k := k) hP hlocal hfree
  exact finiteCategoryProjectiveGenerator.canonicalProjector_primitive
    hPdown hlocalDown (orbitObject (k := k) D x)

end MagnitudeConjecture.StandardCovering

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance f1CoveringPrimitiveQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance f1CoveringPrimitiveArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance f1CoveringPrimitiveFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance f1CoveringPrimitiveNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _



namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

/-- The primitive idempotent in the literal standard-form algebra obtained
from an object in its universal projective cover. -/
noncomputable def standardFormCoveringIdempotent
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    S.standardFormAlgebra S.standardFormMeshHomFinite := by
  let H := standardFormOppositeProjectiveSourceCategoryIsAdmissible
    S x₀ hconnected
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient
      (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
  let f := standardFormOppositeProjectiveLiftedOrbitCategoryAlgebraEquiv
    S x₀ hconnected S.standardFormMeshHomFinite
  exact f (StandardCovering.orbitCategoryProjector (k := k) D hP x)

/-- The covering idempotent is primitive. -/
theorem standardFormCoveringPrimitive
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    RightModule.PrimitiveIdempotentData
      (standardFormCoveringIdempotent S x₀ hconnected x) := by
  letI : IsMulTorsionFree (ProjectiveGroup S x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  let H := standardFormOppositeProjectiveSourceCategoryIsAdmissible
    S x₀ hconnected
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let hlocal := H.locallyBounded.localEndomorphismRings
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient
      (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let P := StandardCovering.orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  let f := standardFormOppositeProjectiveLiftedOrbitCategoryAlgebraEquiv
    S x₀ hconnected S.standardFormMeshHomFinite
  change RightModule.PrimitiveIdempotentData
    (f (StandardCovering.orbitCategoryProjector (k := k) D hP x))
  exact P.mapAlgEquiv f

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
