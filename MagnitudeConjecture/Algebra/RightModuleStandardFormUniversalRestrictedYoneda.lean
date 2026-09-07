import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYonedaDownstairs

/-!
# Restricted Yoneda on the universal standard-form cover

This umbrella exposes the finite-support restricted-Yoneda functor after the
pushdown, orbit-projection, and downstairs-comparison layers have been built.
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

local instance standardFormUniversalRestrictedYonedaFunctorQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalRestrictedYonedaFunctorArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- Restricted Yoneda from the universal mesh category to finite-support
modules on its lifted projective full subcategory. -/
def standardFormUniversalRestrictedYonedaFunctor
    (p : Fin S.n) :
    SourceCategory S p ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k :=
  CoveringHom.finiteSupportRestrictedLinearYonedaFunctor
    (k := k) (standardFormProjectiveProperty S p).ι
    (standardFormUniversalRestrictedYonedaFinite S p)

noncomputable instance standardFormUniversalRestrictedYonedaFunctor_additive
    (p : Fin S.n) :
    (standardFormUniversalRestrictedYonedaFunctor S p).Additive := by
  dsimp only [standardFormUniversalRestrictedYonedaFunctor]
  infer_instance

noncomputable instance standardFormUniversalRestrictedYonedaFunctor_linear
    (p : Fin S.n) :
    (standardFormUniversalRestrictedYonedaFunctor S p).Linear k := by
  dsimp only [standardFormUniversalRestrictedYonedaFunctor]
  infer_instance

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
