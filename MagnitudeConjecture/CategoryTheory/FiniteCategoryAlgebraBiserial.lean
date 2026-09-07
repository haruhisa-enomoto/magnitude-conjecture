import MagnitudeConjecture.Algebra.BiserialInduction
import MagnitudeConjecture.CategoryTheory.BiserialObject
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation

/-!
# Biserial canonical projectives of a finite category algebra

The canonical projector attached to an object of a finite linear category is
primitive when that object's endomorphism ring is local.  The direct
coordinate-thin biserial induction therefore applies to its principal right
ideal.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom.finiteCategoryProjectiveGenerator

universe u

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]
variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

local instance finiteCategoryBiserialAlgebraFiniteDimensional :
    FiniteDimensional k (algebra hP) :=
  algebra_finiteDimensional hP

local instance finiteCategoryBiserialAlgebraOppositeIsNoetherian :
    IsNoetherianRing (algebra hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k (algebra hP)ᵐᵒᵖ

/-- If all indecomposable modules over a finite category algebra are thin in
the canonical coordinates, then every canonical principal right projective
is biserial. -/
theorem canonicalRightIdeal_isBiserial_of_allIndecomposablesCoordinateThin
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (Hthin : RightModule.AllIndecomposablesCoordinateThin (k := k)
      (canonicalProjector hP))
    (X : C) :
    IsBiserialModule (algebra hP)ᵐᵒᵖ
      (RightModule.rightIdealFGObj (canonicalProjector hP X)) := by
  exact
    (canonicalProjector_primitive hP hlocal X).rightIdeal_isBiserial_of_allIndecomposablesCoordinateThin
      (k := k) (canonicalProjector hP) (canonicalProjector_complete hP)
        Hthin

/-- Under the finite-category projective-generator equivalence, every
covariant representable is biserial when all indecomposable algebra modules
are thin in the canonical coordinates. -/
theorem representedCovariantRepresentable_isBiserial_of_allIndecomposablesCoordinateThin
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (Hthin : RightModule.AllIndecomposablesCoordinateThin (k := k)
      (canonicalProjector hP))
    (X : C) :
    IsBiserialModule (algebra hP)ᵐᵒᵖ
      ((representedFGFunctor hP).obj
        ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op X))) := by
  exact IsBiserialModule.congr
    (canonicalRightIdealLinearEquiv (k := k) hP X)
    (canonicalRightIdeal_isBiserial_of_allIndecomposablesCoordinateThin
      hP hlocal Hthin X)

/-- A canonical principal right projective is intrinsically biserial in the
finitely generated module category. -/
theorem canonicalRightIdeal_isBiserialObject_of_allIndecomposablesCoordinateThin
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (Hthin : RightModule.AllIndecomposablesCoordinateThin (k := k)
      (canonicalProjector hP))
    (X : C) :
    IsBiserialObject
      (RightModule.rightIdealFGObj (canonicalProjector hP X)) := by
  let D := canonicalProjector_primitive hP hlocal X
  apply IsBiserialModule.toFGModuleCatIsBiserialObject
  · exact canonicalRightIdeal_isBiserial_of_allIndecomposablesCoordinateThin
      hP hlocal Hthin X
  · exact D.rightIdeal_top_isSimple (k := k)

/-- The represented covariant representable is intrinsically biserial in
the finitely generated module category. -/
theorem representedCovariantRepresentable_isBiserialObject_of_allIndecomposablesCoordinateThin
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (Hthin : RightModule.AllIndecomposablesCoordinateThin (k := k)
      (canonicalProjector hP))
    (X : C) :
    IsBiserialObject
      ((representedFGFunctor hP).obj
        ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op X))) := by
  let D := canonicalProjector_primitive hP hlocal X
  let e := canonicalRightIdealLinearEquiv (k := k) hP X
  apply IsBiserialModule.toFGModuleCatIsBiserialObject
  · exact representedCovariantRepresentable_isBiserial_of_allIndecomposablesCoordinateThin
      hP hlocal Hthin X
  · exact isSimpleModule_top_congr e
      (D.rightIdeal_top_isSimple (k := k))

/-- Every covariant representable of the finite linear category is
intrinsically biserial when all indecomposable modules over its category
algebra are thin in the canonical coordinates. -/
theorem covariantRepresentable_isBiserialObject_of_allIndecomposablesCoordinateThin
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (Hthin : RightModule.AllIndecomposablesCoordinateThin (k := k)
      (canonicalProjector hP))
    (X : C) :
    IsBiserialObject
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X)) := by
  apply IsBiserialObject.of_map_equivalence (moduleEquivalence hP)
  exact
    representedCovariantRepresentable_isBiserialObject_of_allIndecomposablesCoordinateThin
      hP hlocal Hthin X

/-- Intrinsic biseriality of a covariant representable transports to its
canonical principal right ideal in the finite category algebra. -/
theorem canonicalRightIdeal_isBiserialObject_of_covariantRepresentable
    (X : C)
    (hX : IsBiserialObject
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X))) :
    IsBiserialObject
      (RightModule.rightIdealFGObj (canonicalProjector hP X)) := by
  have hrepresented := hX.map_equivalence (moduleEquivalence hP)
  exact hrepresented.congr (canonicalRightIdealIso (k := k) hP X).symm

end MagnitudeConjecture.CoveringHom.finiteCategoryProjectiveGenerator
