import MagnitudeConjecture.Algebra.RightModuleCoherentDefectSerre
import MagnitudeConjecture.Algebra.RightModuleProjectiveStableCovariantSourceUniserial

/-!
# Uniserial syzygies from coherent defect duality

This file packages the source-shaped implication in Auslander--Reiten,
Proposition 1.3(a)(iii).  Coherent duality carries a uniserial
projective-stable contravariant representable to a uniserial degree-one Ext
functor.  Its canonical quotient makes the projective-stable covariant
representable of the syzygy uniserial, and Proposition 1.1(a) then makes the
syzygy itself uniserial when it is indecomposable and nonprojective.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

variable [HasExt.{u} (RightModule.FinitelyGeneratedCategory A)]

/-- Auslander--Reiten Proposition 1.3(a)(iii), in the projective-presentation
interface needed at a projective radical boundary. -/
theorem projectivePresentation_kernel_isUniserialModule_of_stableContravariant
    {X : RightModule.FinitelyGeneratedCategory A}
    (P : MinimalProjectivePresentation X)
    (hkernel : Indecomposable (kernel P.f))
    (hkernelNonprojective : ¬ Projective (kernel P.f))
    (hstable : IsUniserialObject
      (S.finiteProjectiveStableContravariantRepresentable X)) :
    IsUniserialModule Aᵐᵒᵖ (kernel P.f).obj := by
  let K := projectiveCoverShortComplex P
  have hK : K.ShortExact := projectiveCoverShortComplex_shortExact P
  have hContravariantDefect :
      IsUniserialObject (S.finiteContravariantDefect K) :=
    (S.finiteContravariantDefect_isUniserial_iff_projectiveStable P).mpr
      hstable
  have hCovariantDefect :
      IsUniserialObject (S.finiteCovariantDefect K) :=
    (S.finiteContravariantDefect_isUniserial_iff_finiteCovariantDefect
      K hK).mp hContravariantDefect
  have hExt : IsUniserialObject (S.finiteRestrictedExtOne P) :=
    (S.finiteCovariantDefect_isUniserial_iff_restrictedExtOne P).mp
      hCovariantDefect
  have hSyzygyStable : IsUniserialObject
      (S.finiteProjectiveStableCovariantRepresentable (kernel P.f)) :=
    S.finiteProjectiveStableCovariantRepresentable_isUniserial_of_extOne
      P hExt
  exact S.isUniserialModule_of_projectiveStableCovariantRepresentable
    hkernel hkernelNonprojective hSyzygyStable

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
