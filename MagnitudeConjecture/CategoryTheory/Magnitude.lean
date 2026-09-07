import MagnitudeConjecture.CategoryTheory.HomUnitEquations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Rational magnitude of a finite Hom-finite category

For a finite chosen skeleton, the Leinster magnitude is the total sum of the
inverse of the rational Hom-dimension matrix.  The Hom--mesh inverse theorem
identifies that inverse with the integral mesh matrix, proving the frozen
manuscript's magnitude formula rather than merely its combinatorial analogue.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MagnitudeConjecture.FiniteTauMatrix

open QuotientSubmoduleEquidistribution.Iyama

universe s v u w

variable {k : Type s} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] [Linear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

variable (T : FiniteTauCategoryData C Ind)

/-- Rational Hom-dimension matrix of the chosen finite skeleton. -/
def rationalHomDimensionMatrix : Matrix Ind Ind ℚ :=
  fun X Y ↦ Module.finrank k (T.obj X ⟶ T.obj Y)

/-- The integral mesh matrix, regarded over the rationals. -/
def rationalMeshMatrix [DecidablePred T.IsProjective] : Matrix Ind Ind ℚ :=
  fun X Y ↦ meshMatrix T X Y

/-- Leinster magnitude of the chosen finite Hom-dimension matrix. -/
def categoryMagnitude : ℚ :=
  ∑ X, ∑ Y, (rationalHomDimensionMatrix (k := k) T)⁻¹ X Y

/-- The integer inverse equation remains valid after passing to rational
coefficients. -/
theorem rationalHomDimensionMatrix_mul_rationalMeshMatrix
    [DecidablePred T.IsProjective]
    (D : HomMeshInverseData (k := k) T) :
    rationalHomDimensionMatrix (k := k) T * rationalMeshMatrix T = 1 := by
  ext X Y
  have h := congrArg (fun M : Matrix Ind Ind ℤ ↦ M X Y)
    (homDimensionMatrix_mul_meshMatrix T D)
  simp only [Matrix.mul_apply, Matrix.one_apply] at h ⊢
  simp only [rationalHomDimensionMatrix, rationalMeshMatrix]
  exact_mod_cast h

/-- Hence the nonsingular inverse of the rational Hom matrix is precisely the
rationalized mesh matrix. -/
theorem rationalHomDimensionMatrix_inv_eq_rationalMeshMatrix
    [DecidablePred T.IsProjective]
    (D : HomMeshInverseData (k := k) T) :
    (rationalHomDimensionMatrix (k := k) T)⁻¹ = rationalMeshMatrix T :=
  Matrix.inv_eq_right_inv
    (rationalHomDimensionMatrix_mul_rationalMeshMatrix T D)

/-- Frozen manuscript, equations `(2.1)` and `(2.3)`: categorical magnitude is
the Auslander--Reiten Euler expression `vertices - arrows + meshes`. -/
theorem categoryMagnitude_eq_eulerMagnitude
    [DecidablePred T.IsProjective]
    (D : HomMeshInverseData (k := k) T) :
    categoryMagnitude (k := k) T =
      (MagnitudeConjecture.ARCount.eulerMagnitude
        (arrowMultiplicity T.toFiniteRightTauCategoryData) T.IsProjective : ℚ) := by
  rw [categoryMagnitude,
    rationalHomDimensionMatrix_inv_eq_rationalMeshMatrix T D]
  change (∑ X, ∑ Y, (meshMatrix T X Y : ℚ)) = _
  exact_mod_cast
    (MagnitudeConjecture.ARCount.matrixTotal_meshMatrix_eq_eulerMagnitude
      (arrowMultiplicity T.toFiniteRightTauCategoryData) T.IsProjective (tau T))

end MagnitudeConjecture.FiniteTauMatrix
