import MagnitudeConjecture.Algebra.RightModuleStandardFormARRecoveredKernelIso

/-!
# Object-level Auslander--Reiten translation for the standard-form algebra
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

local instance standardFormARTranslationIsoQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARTranslationIsoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARTranslationIsoFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARTranslationIsoNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The module at the original mesh translate is isomorphic to the module at
the standard-form algebra's chosen Auslander--Reiten translate. -/
def standardFormAlgebraRightTranslationIso
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
    let zT : {z : Fin T.n // ¬ Projective (T.fgObj z)} :=
      ⟨z.1, by
        rw [S.standardFormAlgebraSkeleton_projective_iff_original (k := k)]
        simpa [standardFormProjectiveSet] using z.2⟩
    T.fgObj (S.standardFormTau z) ≅ T.fgObj (T.rightTranslationLabel zT) := by
  dsimp only
  let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let zT : {z : Fin T.n // ¬ Projective (T.fgObj z)} :=
    ⟨z.1, by
      rw [S.standardFormAlgebraSkeleton_projective_iff_original (k := k)]
      simpa [standardFormProjectiveSet] using z.2⟩
  let R :=
    S.standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition
      (k := k) z.1
  let C := T.minimalRightAlmostSplitAt z.1
  let eRecovered : T.fgObj (S.standardFormTau z) ≅ kernel R.map :=
    S.standardFormAlgebraRecoveredRightMeshKernelIso (k := k) z
  let eChosen : kernel R.map ≅ kernel C.map :=
    Classical.choice (nonempty_kernelIso_of_rightAlmostSplit
      R.rightAlmostSplit R.rightMinimal C.rightAlmostSplit C.rightMinimal)
  exact eRecovered ≪≫ eChosen ≪≫ T.rightTranslationKernelIso zT

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
