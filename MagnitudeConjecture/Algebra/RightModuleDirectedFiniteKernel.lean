import MagnitudeConjecture.Algebra.RightModuleARHomVanishing
import MagnitudeConjecture.Algebra.RightModuleFiniteKernelBound
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Directed boundary Hom bounds by finite kernels -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable (S : FiniteIndecomposableSkeleton k A)

/-- The finite-kernel argument bounds maps from an AR translate to an
indecomposable injective whenever the untranslated endpoint has no such maps. -/
theorem finrank_rightTranslation_hom_injective_le_one
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (i : Fin S.n) [Injective (S.fgObj i)]
    (hHom : ∀ f : S.fgObj z.1 ⟶ S.fgObj i, f = 0) :
    Module.finrank k (S.fgObj (S.rightTranslationLabel z) ⟶ S.fgObj i) ≤ 1 := by
  letI : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
    fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  apply S.finrank_hom_le_one_of_ext_vanishing
    (S.fgObj (S.rightTranslationLabel z)) (S.fgObj i)
  · intro a
    obtain ⟨c, hc⟩ := H.endomorphism_eq_smul_id S (S.rightTranslationLabel z) a
    exact ⟨c, hc.symm⟩
  · intro a
    obtain ⟨c, hc⟩ := H.endomorphism_eq_smul_id S i a
    exact ⟨c, hc.symm⟩
  · intro U j hj xi
    letI : Mono j := hj
    letI := S.extOne_rightTranslation_subsingleton_of_mono H z (S.fgObj i) hHom U j
    exact Subsingleton.elim xi 0

/-- The injective-source case of the same boundary bound. -/
theorem finrank_injective_hom_injective_le_one
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z i : Fin S.n) [Injective (S.fgObj z)] [Injective (S.fgObj i)] :
    Module.finrank k (S.fgObj z ⟶ S.fgObj i) ≤ 1 := by
  letI : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
    fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  apply S.finrank_hom_le_one_of_ext_vanishing (S.fgObj z) (S.fgObj i)
  · intro a
    obtain ⟨c, hc⟩ := H.endomorphism_eq_smul_id S z a
    exact ⟨c, hc.symm⟩
  · intro a
    obtain ⟨c, hc⟩ := H.endomorphism_eq_smul_id S i a
    exact ⟨c, hc.symm⟩
  · intro U j hj xi
    exact Ext.eq_zero_of_injective xi

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
