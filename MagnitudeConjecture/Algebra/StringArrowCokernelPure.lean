import MagnitudeConjecture.Algebra.StringAlgebraSkeletonClassification
import MagnitudeConjecture.Algebra.StringArrowCokernelAlmostSplit
import MagnitudeConjecture.Algebra.StringArrowCokernelBranch
import MagnitudeConjecture.Algebra.StringMixedSignUniserial

/-!
# Pure-string classification of arrow cokernels

Every Butler--Ringel arrow cokernel is uniserial.  Pulling its selected
algebra-skeleton representative back through the finite-category
projective-generator equivalence and then through coefficient duality shows
that its literal classified string is uniserial as well.  The mixed-sign
obstruction therefore forces that word to be purely positive or purely
negative.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance arrowPureAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance arrowPureAlgebraOppositeNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The literal string selected by a complete algebra-module skeleton for
an arrow cokernel has only one sign. -/
theorem arrowCokernelClassifiedWord_isPure
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    {x y : Q} (a : x ⟶ y) :
    let i := P.arrowCokernelSkeletonIndex T a
    let C := (P.algebraSkeletonDetectorIndex S T i).endpointWord.word
    C.IsPurePositive P.toPresentation.admissible ∨
      C.IsPureNegative P.toPresentation.admissible := by
  let i := P.arrowCokernelSkeletonIndex T a
  let C := (P.algebraSkeletonDetectorIndex S T i).endpointWord.word
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let E := finiteCategoryProjectiveGenerator.moduleEquivalence hP
  let D := finiteCoefficientDualityEquivalence
    (k := k) (C := Category P.toPresentation.relations)
  have hV : IsUniserialObject (P.arrowCokernelFGObj a) :=
    IsUniserialModule.toFGModuleCatIsUniserialObject
      (P.arrowCokernelFGObj a) (P.arrowCokernelFGObj_isUniserial a)
  have hT : IsUniserialObject (T.fgObj i) :=
    IsUniserialObject.congr hV (P.arrowCokernelSkeletonIso T a)
  let eClass := P.representedAlgebraSkeletonStringDualIso S T i
  have hRepresented : IsUniserialObject
      (E.functor.obj
        (reverseFiniteCoefficientDual (k := k)
          (C.finiteRightModule P.monomial))) := by
    apply IsUniserialObject.congr hT eClass.symm
  have hReverseDual : IsUniserialObject
      (reverseFiniteCoefficientDual (k := k)
        (C.finiteRightModule P.monomial)) :=
    IsUniserialObject.of_map_equivalence E hRepresented
  have hOpposite : IsUniserialObject
      (Opposite.op
        (reverseFiniteCoefficientDual (k := k)
          (C.finiteRightModule P.monomial))) :=
    IsUniserialObject.op hReverseDual
  have hDual : IsUniserialObject
      (D.functor.obj
        (Opposite.op
          (reverseFiniteCoefficientDual (k := k)
            (C.finiteRightModule P.monomial)))) :=
    IsUniserialObject.map_equivalence hOpposite D
  have hLiteral : IsUniserialObject
      (C.finiteRightModule P.monomial) :=
    IsUniserialObject.congr hDual
      (finiteCoefficientDualReverseIso
        (k := k) (C.finiteRightModule P.monomial))
  exact C.isPurePositive_or_isPureNegative_of_isUniserialObject
    P.toPresentation.admissible P.monomial hLiteral

end StringPresentation

end MagnitudeConjecture.BoundQuiver
