import MagnitudeConjecture.Algebra.RightModuleDirectedTransport
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientFiniteSkeleton
import MagnitudeConjecture.Algebra.RightModuleBasicMorita

/-! # Directedness of primitive quotients and basic representatives -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)

/-- A primitive quotient of a directed algebra remains directed on its
literal finite indecomposable skeleton. -/
theorem primitiveQuotientFinite_hasAcyclicNonzeroNonisomorphisms
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    [IsNoetherianRing (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] :
    (S.primitiveQuotientFiniteIndecomposableSkeleton D).HasAcyclicNonzeroNonisomorphisms := by
  let E := RightModule.primitiveQuotientEquivalence (k := k) e
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  letI : E.inverse.Additive := inferInstance
  let Q := S.primitiveQuotientFiniteIndecomposableSkeleton D
  let q := S.primitiveQuotientFiniteLabelEquiv D
  apply hasAcyclicNonzeroNonisomorphisms_of_fullyFaithful S Q H (E.inverse ⋙ U)
    (fun i ↦ (q i).1)
  intro i
  exact U.mapIso ((E.inverse.mapIso (S.primitiveQuotientFiniteFGObjIso D i)).trans
    (E.unitIso.app (S.primitiveQuotientLabelObj D (q i))).symm)

/-- The canonical basic Morita representative of a directed algebra is
directed on the corresponding finite skeleton. -/
theorem moritaBasicSkeleton_hasAcyclicNonzeroNonisomorphisms
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.moritaBasicSkeleton.HasAcyclicNonzeroNonisomorphisms := by
  let E := S.basicMoritaEquivalence
  letI : E.inverse.Additive := inferInstance
  apply hasAcyclicNonzeroNonisomorphisms_of_fullyFaithful S S.moritaBasicSkeleton H
    E.inverse id
  intro i
  exact (E.inverse.mapIso (S.moritaBasicSkeletonObjIso i).symm).trans
    (E.unitIso.app (S.fgObj i)).symm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
