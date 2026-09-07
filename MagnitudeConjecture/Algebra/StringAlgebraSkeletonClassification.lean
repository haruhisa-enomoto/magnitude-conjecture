import MagnitudeConjecture.Algebra.StringArrowRightIdeal
import MagnitudeConjecture.Algebra.StringFiniteSkeletonClassification
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDualSkeleton

/-!
# String classification on the quotient-category algebra skeleton

The quotient-category algebra is built from covariant representables, whereas
the manuscript's literal right string modules are contravariant functors on
the quotient category.  The finite-category projective-generator equivalence
therefore first pulls an algebra-module skeleton back to covariant quotient-
category modules.  Pointwise coefficient duality then transports that
skeleton to the contravariant variance classified by literal strings.

Consequently each original algebra-skeleton object is represented by the
reverse coefficient dual of one canonically selected literal string.  This
file keeps that duality explicit; it does not identify the two variances.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CoveringHom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance algebraSkeletonClassificationFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance algebraSkeletonClassificationNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Pull the chosen quotient-category algebra skeleton back to finite
covariant modules on the quotient category. -/
def finiteCategoryModuleIndecomposableSkeleton
    (P : StringPresentation k A Q)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := Category P.toPresentation.relations) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let E := finiteCategoryProjectiveGenerator.moduleEquivalence hP
  letI : E.functor.Additive :=
    finiteCategoryProjectiveGenerator.representedFGFunctor_additive hP
  letI : E.inverse.Additive := inferInstance
  refine
    { n := T.n
      obj := fun i ↦ E.inverse.obj (T.fgObj i)
      indecomposable := ?_
      skeletal := ?_
      complete := ?_ }
  · intro i
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse (T.fgObj i)).2 (T.fgObj_indecomposable i)
  · intro i j hij
    obtain ⟨hij⟩ := hij
    apply T.fgObj_skeletal
    exact ⟨(E.counitIso.app (T.fgObj i)).symm ≪≫
      E.functor.mapIso hij ≪≫ E.counitIso.app (T.fgObj j)⟩
  · intro M hM
    have hMap : Indecomposable (E.functor.obj M) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor M).2 hM
    obtain ⟨i, ⟨hi⟩⟩ := T.fgObj_complete (E.functor.obj M) hMap
    exact ⟨i, ⟨E.unitIso.app M ≪≫ E.inverse.mapIso hi⟩⟩

/-- The counit identifies a pulled-back covariant category-module skeleton
object with the original quotient-algebra skeleton object. -/
def finiteCategoryModuleIndecomposableSkeletonObjIso
    (P : StringPresentation k A Q)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (i : Fin T.n) :
    let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
    (finiteCategoryProjectiveGenerator.moduleEquivalence hP).functor.obj
        ((P.finiteCategoryModuleIndecomposableSkeleton T).obj i) ≅
      T.fgObj i := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let E := finiteCategoryProjectiveGenerator.moduleEquivalence hP
  simpa [finiteCategoryModuleIndecomposableSkeleton] using
    E.counitIso.app (T.fgObj i)

/-- The coefficient-dual skeleton lies in the contravariant variance of the
literal right string modules. -/
noncomputable def finiteCategoryDualModuleIndecomposableSkeleton
    (P : StringPresentation k A Q)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P) :=
  (P.finiteCategoryModuleIndecomposableSkeleton T).coefficientDual

/-- The detector index canonically selected for one quotient-algebra skeleton
label after pullback and coefficient duality. -/
def algebraSkeletonDetectorIndex
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (i : Fin T.n) :
    StringWord.DetectorIndex S :=
  StringWord.DetectorIndex.detectorIndexOfFiniteSkeletonLabel
    (S := S) (P.finiteCategoryDualModuleIndecomposableSkeleton T) i

/-- Every object of the chosen quotient-algebra skeleton is the represented
image of the reverse coefficient dual of a canonically selected literal
string module. -/
noncomputable def representedAlgebraSkeletonStringDualIso
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (i : Fin T.n) :
    let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
    let L := (P.algebraSkeletonDetectorIndex S T i).endpointWord.word
      |>.finiteRightModule P.monomial
    (finiteCategoryProjectiveGenerator.representedFGFunctor hP).obj
        (reverseFiniteCoefficientDual (k := k) L) ≅
      T.fgObj i := by
  let C := Category P.toPresentation.relations
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let E := finiteCategoryProjectiveGenerator.moduleEquivalence hP
  let D := finiteCoefficientDualityEquivalence (k := k) (C := C)
  let U := P.finiteCategoryModuleIndecomposableSkeleton T
  let V := P.finiteCategoryDualModuleIndecomposableSkeleton T
  let d := P.algebraSkeletonDetectorIndex S T i
  let L := d.endpointWord.word.finiteRightModule P.monomial
  let eString : L ≅ D.functor.obj (Opposite.op (U.obj i)) := by
    simpa [L, d, algebraSkeletonDetectorIndex, V, U, D,
      finiteCategoryDualModuleIndecomposableSkeleton,
      FiniteDimensionalModuleIndecomposableSkeleton.coefficientDual]
      using StringWord.DetectorIndex.finiteSkeletonStringIso (S := S) V i
  let eDouble : D.functor.obj
        (Opposite.op (reverseFiniteCoefficientDual (k := k) L)) ≅ L :=
    finiteCoefficientDualReverseIso (k := k) L
  let eOp : Opposite.op (reverseFiniteCoefficientDual (k := k) L) ≅
      Opposite.op (U.obj i) := by
    apply D.functor.preimageIso
    exact eDouble ≪≫ eString
  let eBack : reverseFiniteCoefficientDual (k := k) L ≅ U.obj i :=
    (Iso.unop eOp).symm
  exact E.functor.mapIso eBack ≪≫
    P.finiteCategoryModuleIndecomposableSkeletonObjIso T i

end StringPresentation

end MagnitudeConjecture.BoundQuiver
