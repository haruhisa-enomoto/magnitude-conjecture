import MagnitudeConjecture.Algebra.RightModuleCoherentDefectDimensionShift

/-!
# Naturality of coherent-defect dimension shifting
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable [HasExt.{u} (FG (A := A))]
variable [HasExt.{u} (S.FiniteContravariantFunctor)]

/-- The specialized dimension shift commutes with postcomposition in the
restricted representable target. -/
theorem finiteContravariantDefectDimensionShiftLinearEquiv_postcomp
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    {X Y : S.IndecCategory} (a : X ⟶ Y)
    (x : Ext.{u} (S.finiteContravariantDefectSyzygy K)
      (S.finiteContravariantRepresentableOnSkeleton.obj X) 1) :
    S.finiteContravariantDefectDimensionShiftLinearEquiv hK Y
        (x.comp
          (Ext.mk₀ (S.finiteContravariantRepresentableOnSkeleton.map a))
          (add_zero 1)) =
      (S.finiteContravariantDefectDimensionShiftLinearEquiv hK X x).comp
        (Ext.mk₀ (S.finiteContravariantRepresentableOnSkeleton.map a))
        (add_zero 2) := by
  letI : Projective
      (S.finiteRestrictedContravariantRepresentable K.X₃) :=
    S.finiteRestrictedContravariantRepresentable_projective K.X₃
  letI : Projective
      (S.finiteContravariantDefectRightShortComplex K).X₂ := by
    change Projective
      (S.finiteRestrictedContravariantRepresentable K.X₃)
    infer_instance
  exact MagnitudeConjecture.ProjectiveMiddleDimensionShift.linearEquiv_postcomp
    (k := k) (S.finiteContravariantDefectRightShortComplex_shortExact hK)
    (S.finiteContravariantRepresentableOnSkeleton.map a) 0 x

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
