import MagnitudeConjecture.Algebra.StringArrowCokernelAlmostSplit
import MagnitudeConjecture.Algebra.StringAlgebraSkeletonArity
import MagnitudeConjecture.Algebra.StringAlgebraSkeletonUnaryBoundary
import MagnitudeConjecture.Algebra.StringProjectiveARCount

/-!
# Numerical assembly of the Butler--Ringel correspondence

The arrow-cokernel construction gives an injective map from displayed quiver
arrows to one-middle meshes.  Literal unary boundary classification gives an
injective map in the reverse direction.  Finite cardinality therefore makes
the arrow-cokernel map surjective.  Together with the two-middle bound, this
proves `E₁ = |Q₁|` and vanishing of the Auslander--Reiten surplus.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance butlerRingelCountAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance butlerRingelCountAlgebraOppositeIsNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

noncomputable local instance butlerRingelCountFGHasFiniteBiproducts
    (P : StringPresentation k A Q) :
    HasFiniteBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

noncomputable local instance butlerRingelCountFGHasBinaryBiproducts
    (P : StringPresentation k A Q) :
    HasBinaryBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

noncomputable local instance butlerRingelCountProjectiveDecidablePred
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    DecidablePred S.finiteTauCategoryData.IsProjective :=
  Classical.decPred _

/-- The Butler--Ringel arrow-cokernel map is surjective.  Its proved
injectivity and the injective reverse choice of a unary-boundary arrow force
equality of the two finite cardinalities. -/
theorem displayedArrowOneMiddleMesh_surjective
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    Function.Surjective (P.displayedArrowOneMiddleMesh T) := by
  have hcard :
      Nat.card (FiniteTauMatrix.OneMiddleMesh T.finiteTauCategoryData) ≤
        Nat.card (DisplayedArrow Q) :=
    Nat.card_le_card_of_injective
      (P.oneMiddleMeshDisplayedArrow S T)
      (P.oneMiddleMeshDisplayedArrow_injective S T)
  exact (P.displayedArrowOneMiddleMesh_injective T).bijective_of_nat_card_le
    hcard |>.2

/-- The displayed-arrow/one-middle-mesh Butler--Ringel equivalence. -/
def displayedArrowOneMiddleMeshEquiv
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    DisplayedArrow Q ≃
      FiniteTauMatrix.OneMiddleMesh T.finiteTauCategoryData :=
  Equiv.ofBijective (P.displayedArrowOneMiddleMesh T)
    ⟨P.displayedArrowOneMiddleMesh_injective T,
      P.displayedArrowOneMiddleMesh_surjective S T⟩

/-- The converse Butler--Ringel classification gives the manuscript's count
`E₁ = |Q₁|`. -/
theorem oneMiddleMeshCount_eq_natCard_displayedArrow
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    FiniteTauMatrix.oneMiddleMeshCount T.finiteTauCategoryData =
      Nat.card (DisplayedArrow Q) :=
  FiniteTauMatrix.oneMiddleMeshCount_eq_natCard_of_equiv
    T.finiteTauCategoryData
    (P.displayedArrowOneMiddleMeshEquiv S T)

/-- The exact string-algebra numerical endpoint: literal boundary
classification and the two-middle bound force the quotient-algebra
Auslander--Reiten surplus to vanish. -/
theorem quotientCategoryAlgebra_surplus_eq_zero
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    ARCount.surplus
        (FiniteTauMatrix.arrowMultiplicity
          T.finiteTauCategoryData.toFiniteRightTauCategoryData)
        T.finiteTauCategoryData.IsProjective = 0 := by
  rw [P.surplus_eq_oneMiddleMeshCount_sub_natCard_displayedArrow T
      (fun Y hY ↦ P.rightMiddleArity_le_two_of_not_projective S T Y hY),
    P.oneMiddleMeshCount_eq_natCard_displayedArrow S T]
  omega

end StringPresentation

end MagnitudeConjecture.BoundQuiver
