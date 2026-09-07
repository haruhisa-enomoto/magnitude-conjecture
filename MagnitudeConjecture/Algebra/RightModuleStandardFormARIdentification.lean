import MagnitudeConjecture.Algebra.RightModuleStandardFormARTranslationIso

/-!
# Auslander--Reiten translation for the standard-form algebra

At a nonprojective vertex, short exactness identifies the recovered kernel
with the original mesh translate and hence identifies the chosen algebraic
Auslander--Reiten translation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARIdentificationQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARIdentificationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARIdentificationFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARIdentificationNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- At every nonprojective label, the standard-form algebra's chosen
Auslander--Reiten translation is the original mesh translation. -/
theorem standardFormAlgebra_rightTranslationLabel_eq_standardFormTau
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
    let zT : {z : Fin T.n // ¬ Projective (T.fgObj z)} :=
      ⟨z.1, by
        rw [S.standardFormAlgebraSkeleton_projective_iff_original (k := k)]
        simpa [standardFormProjectiveSet] using z.2⟩
    T.rightTranslationLabel zT = S.standardFormTau z := by
  dsimp only
  let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let zT : {z : Fin T.n // ¬ Projective (T.fgObj z)} :=
    ⟨z.1, by
      rw [S.standardFormAlgebraSkeleton_projective_iff_original (k := k)]
      simpa [standardFormProjectiveSet] using z.2⟩
  symm
  apply T.fgObj_skeletal
  exact ⟨S.standardFormAlgebraRightTranslationIso (k := k) z⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
