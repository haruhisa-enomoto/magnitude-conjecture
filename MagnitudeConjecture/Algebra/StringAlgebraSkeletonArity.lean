import MagnitudeConjecture.Algebra.RightModuleLeftAlmostSplit
import MagnitudeConjecture.Algebra.StringAlgebraSkeletonClassification
import MagnitudeConjecture.Algebra.StringFiniteBoundaryArity
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleRightTau
import MagnitudeConjecture.CategoryTheory.FiniteTauSurplusEquivalence

/-!
# The two-middle bound on the quotient-algebra skeleton

The literal Butler--Ringel boundary calculation lives in the contravariant
finite-module category of right string modules.  The quotient-category
algebra skeleton pulls back to covariant finite modules.  We therefore send
its chosen right almost-split map through coefficient duality, rotate the
resulting left almost-split monomorphism across its cokernel, classify that
cokernel by a literal string, and compare minimal right almost-split middle
terms.  Finally, ordinary projective-generator equivalence transports the
arity bound back to the algebra skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance algebraSkeletonArityFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance algebraSkeletonArityNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Every nonprojective quotient-algebra skeleton label has incoming
Auslander--Reiten arity at most two.  The estimate is the literal string
boundary theorem transported through coefficient duality and the finite
projective-generator equivalence. -/
theorem rightMiddleArity_le_two_of_not_projective
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    (i : Fin T.n)
    (hi : ¬ T.finiteTauCategoryData.IsProjective i) :
    FiniteTauMatrix.rightMiddleArity
        T.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2 := by
  let C := Category P.toPresentation.relations
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let E := finiteCategoryProjectiveGenerator.moduleEquivalence hP
  let U := P.finiteCategoryModuleIndecomposableSkeleton T
  let V := P.finiteCategoryDualModuleIndecomposableSkeleton T
  letI : E.functor.Additive :=
    finiteCategoryProjectiveGenerator.representedFGFunctor_additive hP
  letI : E.inverse.Additive := inferInstance
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, u, u, u} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        P.quotientCategoryAlgebra) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      P.quotientCategoryAlgebraᵐᵒᵖ
  let TU := U.toFiniteRightTauCategoryData
  let TT := T.finiteTauCategoryData.toFiniteRightTauCategoryData
  let labelEquiv : Fin T.n ≃ Fin T.n := Equiv.refl _
  let objIso (j : Fin T.n) :
      E.functor.obj (U.obj j) ≅ T.fgObj j := by
    simpa [E, hP, U] using
      P.finiteCategoryModuleIndecomposableSkeletonObjIso T j
  have hprojective :=
    FiniteTauMatrix.isProjective_equivalence_iff
      TU TT E labelEquiv objIso i
  have hlabel : labelEquiv i = i := rfl
  have hiU : ¬ TU.IsProjective i := by
    intro h
    apply hi
    exact hlabel ▸ hprojective.mp h
  have hiUobj : ¬ Projective (TU.obj i) := by
    rwa [FiniteTauMatrix.isProjective_iff_projective_obj] at hiU
  have hUarity : FiniteTauMatrix.rightMiddleArity TU i ≤ 2 := by
    let d := FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition TU i
    let m := (TU.rightMesh (TU.obj i)).g ≫
      (TU.rightTermIso (TU.obj i)).hom
    have hmAS : IsRightAlmostSplit m :=
      FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit TU i
    have hmMin : IsRightMinimal m :=
      FiniteTauMatrix.rightMesh_terminal_isRightMinimal TU i
    letI : Epi m :=
      MagnitudeConjecture.CategoryTheory.IsRightAlmostSplit.epi_of_not_projective
        m hmAS hiUobj
    let D := finiteCoefficientDualityEquivalence (k := k) (C := C)
    letI : D.functor.Additive := finiteCoefficientDualFunctor_additive
    have hYindec :
        Indecomposable (D.functor.obj (Opposite.op (TU.obj i))) := by
      apply
        (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
          D.functor (Opposite.op (TU.obj i))).2
      exact
        (MagnitudeConjecture.CategoryTheory.indecomposable_op_iff
          (TU.obj i)).2 (TU.obj_indec i)
    have hYlocal :
        IsLocalRing (End (D.functor.obj (Opposite.op (TU.obj i)))) :=
      finiteDimensionalModule_end_isLocalRing k _ hYindec
    have hIndec (j : Fin d.n) :
        Indecomposable
          (D.functor.obj (Opposite.op (d.summand j))) := by
      apply
        (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
          D.functor (Opposite.op (d.summand j))).2
      exact
        (MagnitudeConjecture.CategoryTheory.indecomposable_op_iff
          (d.summand j)).2 (d.indecomposable j)
    have hlocal (j : Fin d.n) :
        IsLocalRing
          (End (D.functor.obj (Opposite.op (d.summand j)))) :=
      finiteDimensionalModule_end_isLocalRing k _ (hIndec j)
    have hbound (Z :
        FiniteDimensionalModuleCategory.{u, u, u, u}
          (C := Cᵒᵖ) k)
        (hZindec : Indecomposable Z) (hZnonprojective : ¬ Projective Z) :
        Nonempty
          (MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
            Z 2) := by
      obtain ⟨j, ⟨eZ⟩⟩ := V.complete Z hZindec
      let W :=
        (StringWord.DetectorIndex.detectorIndexOfFiniteSkeletonLabel
          (S := S) V j).endpointWord.word
      let eW : W.finiteRightModule P.monomial ≅ Z :=
        StringWord.DetectorIndex.finiteSkeletonStringIso
            (S := S) V j ≪≫ eZ.symm
      have hWnonprojective :
          ¬ Projective (W.finiteRightModule P.monomial) := by
        intro hW
        exact hZnonprojective (Projective.of_iso eW hW)
      obtain ⟨w⟩ :=
        StringWord.Word.exists_finiteRightAlmostSplitDecompositionBound_two_of_not_projective
          P S V W hWnonprojective
      exact ⟨w.postcompIso eW⟩
    change d.n ≤ 2
    exact d.n_le_of_mapOp_cokernel_bound D hYindec hYlocal
      hIndec hlocal hmAS hmMin hbound
  have harity :
      FiniteTauMatrix.rightMiddleArity TU i =
        FiniteTauMatrix.rightMiddleArity TT i := by
    calc
      FiniteTauMatrix.rightMiddleArity TU i =
          FiniteTauMatrix.rightMiddleArity TT (labelEquiv i) :=
        FiniteTauMatrix.rightMiddleArity_eq_of_equivalence
          TU TT E labelEquiv objIso i
      _ = FiniteTauMatrix.rightMiddleArity TT i :=
        congrArg (FiniteTauMatrix.rightMiddleArity TT) hlabel
  rw [← harity]
  exact hUarity

end StringPresentation
end MagnitudeConjecture.BoundQuiver
