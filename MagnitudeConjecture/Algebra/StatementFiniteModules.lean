import MagnitudeConjecture.Statement
import MagnitudeConjecture.Algebra.RightModuleMagnitudePublic

/-!
# Connecting the independent module vocabulary to the proof library

The statement's finite family is the same data as the production skeleton.
Forgetting the finite-generation bundle identifies the Hom spaces linearly,
so the direct Hom matrix and its magnitude agree with those in the proof.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.Statement.IndecomposableFamily

universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (S : IndecomposableFamily k A)

/-- View the independently specified family as a production skeleton. -/
def toSkeleton : RightModule.FiniteIndecomposableSkeleton k A where
  n := S.size
  obj := S.obj
  obj_finite := S.finite
  obj_indecomposable := S.indecomposable
  eq_of_iso := S.distinct
  complete M hM := S.complete M hM.1 hM.2

include S in
/-- Existence of the independent family gives the production finite-type hypothesis. -/
theorem isRepresentationFinite : RightModule.IsRepresentationFinite k A := by
  refine ⟨S.size, S.obj, ?_, ?_⟩
  · intro i
    exact ⟨S.finite i, S.indecomposable i⟩
  · intro M hM
    exact S.complete M hM.1 hM.2

variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- The direct simple count is unchanged by bundling finite generation. -/
theorem simpleCount_eq : simpleCount k A S = S.toSkeleton.simpleCount := rfl

/-- The independent Hom matrix agrees with the matrix used in the proof. -/
theorem homMatrix_eq : homMatrix k A S =
    FiniteTauMatrix.rationalHomDimensionMatrix (k := k)
      S.toSkeleton.finiteTauCategoryData := by
  ext i j
  change (Module.finrank k (S.obj i ⟶ S.obj j) : ℚ) =
    (Module.finrank k (S.toSkeleton.fgObj i ⟶ S.toSkeleton.fgObj j) : ℚ)
  congr 1
  let e : (S.toSkeleton.fgObj i ⟶ S.toSkeleton.fgObj j) ≃ₗ[k]
      (S.obj i ⟶ S.obj j) := InducedCategory.homLinearEquiv
  exact e.finrank_eq.symm

/-- Equality of the matrices identifies their inverse sums. -/
theorem magnitude_eq : magnitude k A S =
    FiniteTauMatrix.categoryMagnitude (k := k) S.toSkeleton.finiteTauCategoryData := by
  unfold magnitude FiniteTauMatrix.categoryMagnitude
  rw [S.homMatrix_eq]
  rfl

variable [IsAlgClosed k]

/-- The Hom matrix in the independent statement is nonsingular. -/
theorem homMatrix_det_ne_zero : (homMatrix k A S).det ≠ 0 := by
  let T := S.toSkeleton.finiteTauCategoryData
  let : DecidablePred T.IsProjective := Classical.decPred _
  have hmono : ∀ i, Mono (T.rightMesh (T.obj i)).f := by
    intro i
    change Mono (S.toSkeleton.canonicalRightMesh (S.toSkeleton.fgObj i)).f
    rw [S.toSkeleton.canonicalRightMesh_at_label i]
    exact S.toSkeleton.labelRightMesh_f_mono i
  let D := FiniteTauMatrix.HomMeshInverseData.ofIsAlgClosed (k := k) T hmono
  rw [S.homMatrix_eq]
  exact Matrix.det_ne_zero_of_right_inverse
    (FiniteTauMatrix.rationalHomDimensionMatrix_mul_rationalMeshMatrix T D)

/-- The numerical assertion, with special biseriality still expressed by the
production predicate. Its independent presentation connection is separate. -/
theorem magnitude_inequality_and_equality :
    (simpleCount k A S : ℚ) ≤ magnitude k A S ∧
      (magnitude k A S = (simpleCount k A S : ℚ) ↔
        BoundQuiver.IsSpecialBiserial k A) := by
  rw [S.simpleCount_eq, S.magnitude_eq]
  exact S.toSkeleton.magnitudeConjecture_simpleCount

end MagnitudeConjecture.Statement.IndecomposableFamily
