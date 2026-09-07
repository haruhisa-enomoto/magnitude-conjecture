import MagnitudeConjecture.Algebra.RightModulePrimitiveDirectedDeletion
import MagnitudeConjecture.Algebra.RightModuleStandardFormARIdentification

/-!
# Auslander--Reiten surplus of the standard-form algebra

The literal translation-quiver identification makes the manuscript's
standard-form surplus equality pointwise: the vertex type is unchanged, the
projective predicates agree, and every arrow multiplicity agrees.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

noncomputable local instance standardFormSurplusFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormSurplusNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Frozen manuscript, equation `eq:standard-surplus`: the literal
standard-form algebra and the original representation-finite algebra have
the same Auslander--Reiten surplus. -/
theorem standardFormAlgebra_ambientARSurplus_eq_original :
    (S.standardFormAlgebraIndecomposableSkeleton (k := k)).ambientARSurplus =
      S.ambientARSurplus := by
  classical
  unfold ambientARSurplus
  congr 1
  · funext x z
    exact S.standardFormAlgebra_arrowMultiplicity_eq_original (k := k) x z
  · funext x
    exact propext
      (S.standardFormAlgebraSkeleton_projective_iff_original (k := k) x)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
