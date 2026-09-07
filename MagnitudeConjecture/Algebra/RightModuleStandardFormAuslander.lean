import MagnitudeConjecture.Algebra.RightModuleStandardFormGlobalDimension
import MagnitudeConjecture.Algebra.RightModuleStandardFormAuslanderProjective

/-!
# The Auslander category of the standard-form mesh

The global-dimension and projective-injective-resolution results for the
standard mesh are assembled here into the Auslander--Bongartz--Gabriel kernel
equivalence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormAuslanderQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormAuslanderArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The standard mesh is an Auslander category: the left Freyd category of
its projective-injective objects is equivalent to its projective objects. -/
def standardFormAuslanderBongartzGabrielEquivalence :
    CategoryTheory.Preadditive.LeftFreyd
        (CategoryTheory.ProjectiveInjectiveObject
          S.StandardFormFiniteContravariantModuleCategory) ≌
      CategoryTheory.ProjectiveObject
        S.StandardFormFiniteContravariantModuleCategory :=
  LeftFreyd.auslanderBongartzGabrielEquivalence
    (fun M ↦ S.standardFormFiniteModule_hasProjectiveDimensionLE_two M)
    S.standardFormProjective_projectiveInjectiveCopresentation_nonempty

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
