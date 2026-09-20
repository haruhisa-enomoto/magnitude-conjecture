import MagnitudeConjecture.Algebra.RightModuleFiniteType
import MagnitudeConjecture.CategoryTheory.FiniteKernelExtBound

/-! # The finite-kernel bound for representation-finite right modules -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Infinite k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable [HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ)]

/-- Scalar endpoint endomorphisms and Ext vanishing on submodules of an
injective target bound the Hom dimension by one. -/
theorem finrank_hom_le_one_of_ext_vanishing
    (S : FiniteIndecomposableSkeleton k A)
    (Z I : FinitelyGeneratedCategory A) [Injective I]
    (hZ : ∀ a : Z ⟶ Z, ∃ c : k, a = c • 𝟙 Z)
    (hI : ∀ a : I ⟶ I, ∃ c : k, a = c • 𝟙 I)
    (hext : ∀ (U : FinitelyGeneratedCategory A) (j : U ⟶ I),
      Mono j → ∀ xi : Ext.{u} U Z 1, xi = 0) :
    Module.finrank k (Z ⟶ I) ≤ 1 :=
  FiniteKernel.finrank_hom_le_one_of_ext_vanishing S.fgObj
    (fun i ↦ (S.fgObj_indecomposable i).1)
    S.fgObj_decomposition Z I hZ hI hext

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
