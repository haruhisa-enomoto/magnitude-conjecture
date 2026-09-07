import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectDimensionShift

/-! # Naturality of reverse coherent-defect dimension shifting -/

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
variable [HasExt.{u} (S.FiniteCovariantFunctor)]

/-- The reverse dimension shift commutes with postcomposition in the
restricted covariant-representable target. -/
theorem finiteCovariantDefectDimensionShiftLinearEquiv_postcomp
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    {X Y : S.IndecCategoryᵒᵖ} (a : X ⟶ Y)
    (x : Ext.{u} (S.finiteCovariantDefectSyzygy K)
      (S.finiteCovariantRepresentableOnSkeleton.obj X) 1) :
    S.finiteCovariantDefectDimensionShiftLinearEquiv hK Y
        (x.comp
          (Ext.mk₀ (S.finiteCovariantRepresentableOnSkeleton.map a))
          (add_zero 1)) =
      (S.finiteCovariantDefectDimensionShiftLinearEquiv hK X x).comp
        (Ext.mk₀ (S.finiteCovariantRepresentableOnSkeleton.map a))
        (add_zero 2) := by
  letI : Projective
      (S.finiteRestrictedCovariantRepresentable K.X₁) :=
    S.finiteRestrictedCovariantRepresentable_projective K.X₁
  letI : Projective
      (S.finiteCovariantDefectRightShortComplex K).X₂ := by
    change Projective
      (S.finiteRestrictedCovariantRepresentable K.X₁)
    infer_instance
  exact MagnitudeConjecture.ProjectiveMiddleDimensionShift.linearEquiv_postcomp
    (k := k) (S.finiteCovariantDefectRightShortComplex_shortExact hK)
    (S.finiteCovariantRepresentableOnSkeleton.map a) 0 x

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
