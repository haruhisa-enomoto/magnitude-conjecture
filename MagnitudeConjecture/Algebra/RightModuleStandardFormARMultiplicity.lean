import MagnitudeConjecture.Algebra.RightModuleStandardFormARDecomposition

/-!
# Arrow multiplicities for the standard-form algebra
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARMultiplicityQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARMultiplicityArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARMultiplicityFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARMultiplicityNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- On the unchanged literal labels, the standard-form algebra has exactly
the original Auslander--Reiten arrow multiplicities, including at projective
boundary targets. -/
theorem standardFormAlgebra_arrowMultiplicity_eq_original
    (x z : Fin S.n) :
    FiniteTauMatrix.arrowMultiplicity
        (S.standardFormAlgebraIndecomposableSkeleton
          (k := k)).finiteTauCategoryData.toFiniteRightTauCategoryData x z =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x z := by
  let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let sigma := T.almostSplitSkeleton
  let B := S.standardFormAlgebra S.standardFormMeshHomFinite
  letI : ∀ i : Fin T.n, Module k (sigma.obj i) :=
    fun i ↦ Module.restrictScalars k Bᵐᵒᵖ (sigma.obj i)
  letI : ∀ i : Fin T.n, IsScalarTower k Bᵐᵒᵖ (sigma.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k Bᵐᵒᵖ (sigma.obj i)
  let C := T.meshRightAlmostSplitAt z
  let R :=
    S.standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition
      (k := k) z
  calc
    FiniteTauMatrix.arrowMultiplicity
          T.finiteTauCategoryData.toFiniteRightTauCategoryData x z =
        Nat.card (T.MeshArrow z x) :=
      (T.natCard_meshArrow_eq_arrowMultiplicity z x).symm
    _ = Module.finrank k
          (sigma.irreducibleHomSpace (K := k) x z) :=
      (sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
        C x).symm
    _ = Nat.card (sigma.RightAROccurrence R x) :=
      sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
        R x
    _ = Nat.card (S.StandardFormArrow z x) :=
      Nat.card_congr
        (S.standardFormAlgebraRecoveredOccurrenceEquiv (k := k) z x)
    _ = FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData x z :=
      S.natCard_standardFormArrow z x

/-- A noncanonical arrowwise equivalence from the standard-form algebra's
reversed AR quiver to the original reversed standard-form quiver. -/
def standardFormAlgebraMeshArrowEquiv (z x : Fin S.n) :
    (S.standardFormAlgebraIndecomposableSkeleton (k := k)).MeshArrow z x ≃
      S.StandardFormArrow z x := by
  let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  letI : Fintype (T.MeshArrow z x) := T.meshArrowFintype z x
  letI : Fintype (S.StandardFormArrow z x) :=
    S.standardFormArrowFintype z x
  apply Fintype.equivOfCardEq
  simpa only [Nat.card_eq_fintype_card] using
    (T.natCard_meshArrow_eq_arrowMultiplicity z x).trans
      ((S.standardFormAlgebra_arrowMultiplicity_eq_original
        (k := k) x z).trans (S.natCard_standardFormArrow z x).symm)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
