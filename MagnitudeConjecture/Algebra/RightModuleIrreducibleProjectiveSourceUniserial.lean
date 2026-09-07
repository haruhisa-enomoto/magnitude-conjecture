import MagnitudeConjecture.Algebra.RightModuleCoherentDefectUniserial
import MagnitudeConjecture.Algebra.RightModuleStableRepresentableSocleInduction
import MagnitudeConjecture.CategoryTheory.ShortExactKernelTransport

/-!
# Uniserial sources of irreducible maps into projectives

This file combines the stable-representable conclusion at a projective
boundary with coherent defect duality.  Under the two-arm bound, every
nonprojective indecomposable source of an irreducible morphism into an
indecomposable projective is uniserial.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

variable [HasExt.{u} (RightModule.FinitelyGeneratedCategory A)]

/-- The selected quotient of an irreducible inclusion into a projective,
with the original projective as its minimal projective cover. -/
noncomputable def irreducibleIntoProjective_selectedProjectivePresentation
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    MinimalProjectivePresentation
      (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) :=
  (S.irreducibleIntoProjective_cokernelProjectivePresentation p g hg hp).postIso
    (S.irreducibleIntoProjective_cokernelIso p g hg hp)

/-- The source of the irreducible inclusion is the syzygy of the selected
quotient. -/
noncomputable def irreducibleIntoProjective_sourceIsoSelectedSyzygy
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.fgObj u ≅ kernel
      (S.irreducibleIntoProjective_selectedProjectivePresentation
        u p g hg hp).f := by
  letI : Mono g := irreducibleIntoProjective_mono g hg hp
  let K := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  have hK : K.ShortExact := by
    exact { exact := K.exact_of_g_is_cokernel (cokernelIsCokernel g) }
  exact K.sourceIsoKernelOfShortExactCompIso hK
    (S.irreducibleIntoProjective_selectedProjectivePresentation
      u p g hg hp).f
    (S.irreducibleIntoProjective_cokernelIso p g hg hp) rfl

/-- The source-shaped conclusion of Auslander--Reiten Proposition
1.3(a)(iii) at a projective boundary. -/
theorem irreducibleIntoProjective_source_isUniserialModule
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (hu : ¬ Projective (S.fgObj u)) :
    IsUniserialModule Aᵐᵒᵖ (S.fgObj u).obj := by
  let P := S.irreducibleIntoProjective_selectedProjectivePresentation
    u p g hg hp
  let e : S.fgObj u ≅ kernel P.f :=
    S.irreducibleIntoProjective_sourceIsoSelectedSyzygy u p g hg hp
  have hkernel : Indecomposable (kernel P.f) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).mp
      (S.fgObj_indecomposable u)
  have hkernelNonprojective : ¬ Projective (kernel P.f) := by
    intro hprojective
    exact hu (Projective.of_iso e.symm hprojective)
  have hstable : IsUniserialObject
      (S.finiteProjectiveStableContravariantRepresentable
        (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))) :=
    S.irreducibleIntoProjective_stableRepresentable_isUniserial
      harity u p g hg hp
  have hsyzygy : IsUniserialModule Aᵐᵒᵖ (kernel P.f).obj :=
    S.projectivePresentation_kernel_isUniserialModule_of_stableContravariant
      P hkernel hkernelNonprojective hstable
  exact IsUniserialModule.congr (FGModuleCat.isoToLinearEquiv e.symm) hsyzygy

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
