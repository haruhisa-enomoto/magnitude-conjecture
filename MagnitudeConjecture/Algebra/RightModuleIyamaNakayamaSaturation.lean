import MagnitudeConjecture.Algebra.RightModuleIyamaSaturatedImage
import MagnitudeConjecture.Algebra.RightModuleIyamaGlobalDimension
import MagnitudeConjecture.Algebra.RightModuleIyamaBoundaryNakayama

/-!
# Iyama saturation through finite Nakayama evaluation

For a saturated quotient of a represented projective, the boundary
representable detects every nonzero submodule.  Finite Nakayama evaluation
therefore embeds that quotient into finitely many copies of the boundary
Nakayama module.  The factor Auslander global-dimension bound then reduces
projective dimension at most one for every such quotient to the single
boundary estimate `pd (nu U) ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

namespace PrimitiveProjectivePosetData

/-- The source quotient in Iyama's saturation argument has projective
dimension at most one. -/
theorem saturatedSubobjectAmbientQuotient_projectiveDimensionLE_one
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        ((S.factorAdditiveGenerator K ⟶ X) ⧸
          R.saturatedSubobjectImage H m)) 1 := by
  let i := R.saturatedSubobjectAmbientQuotientNakayamaMap H m
  apply R.saturatedSubobjectQuotient_projectiveDimensionLE_one_of_injective
    H m i
  · exact R.saturatedSubobjectAmbientQuotientNakayamaMap_injective H m
  · exact RightModule.nakayamaEmbeddingTarget_projectiveDimensionLE_one
      (k := k) (S.factorBoundaryRepresentableFGObj K)
      (R.saturatedSubobjectAmbientQuotientFGObj H m)
      (S.factorBoundaryNakayama_hasProjectiveDimensionLE_one
        D.toPrimitiveTraceInput.toPrimitiveFactorInput H)
  · exact S.finiteModule_hasProjectiveDimensionLE_two
      D.toPrimitiveTraceInput.toPrimitiveFactorInput H

end PrimitiveProjectivePosetData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
