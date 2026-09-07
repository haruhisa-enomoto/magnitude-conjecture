import MagnitudeConjecture.Algebra.RightModuleStandardFormARIdentification
import MagnitudeConjecture.CategoryTheory.FiniteTauBeta

/-!
# The nonprojective middle-term bound of the standard form

The standard-form algebra and the original representation-finite algebra
have the same `beta`: their complete indecomposable skeletons have the same
projective labels and every Auslander--Reiten arrow multiplicity agrees.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

noncomputable local instance standardFormBetaFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormBetaNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Frozen manuscript lines 2580--2583: the standard-form algebra and the
original algebra have the same maximum number of nonprojective
indecomposable middle occurrences in a right almost-split sequence. -/
theorem standardFormAlgebra_beta_eq_original :
    FiniteTauMatrix.beta (Ind := Fin S.n)
        (S.standardFormAlgebraIndecomposableSkeleton
          (k := k)).finiteTauCategoryData.toFiniteRightTauCategoryData =
      FiniteTauMatrix.beta (Ind := Fin S.n)
        S.finiteTauCategoryData.toFiniteRightTauCategoryData := by
  let B := S.standardFormAlgebra S.standardFormMeshHomFinite
  letI : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives (FGModuleCat.{u} Bᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  apply FiniteTauMatrix.beta_eq_of_projective_iff_of_arrowMultiplicity_eq
    (Ind := Fin S.n)
  · intro i
    rw [FiniteTauMatrix.isProjective_iff_projective_obj,
      FiniteTauMatrix.isProjective_iff_projective_obj]
    exact S.standardFormAlgebraSkeleton_projective_iff_original (k := k) i
  · exact S.standardFormAlgebra_arrowMultiplicity_eq_original (k := k)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
