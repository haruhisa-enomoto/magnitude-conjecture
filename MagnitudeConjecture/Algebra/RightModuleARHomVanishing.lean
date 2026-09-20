import MagnitudeConjecture.Algebra.RightModuleNakayamaARIdentification

/-! # AR-duality vanishing from ordinary Hom vanishing -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable [HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ)]
variable (S : FiniteIndecomposableSkeleton k A)

/-- Ordinary Hom vanishing suffices for Ext vanishing into the AR translate. -/
theorem extOne_rightTranslation_subsingleton_of_hom_zero
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (U : FinitelyGeneratedCategory A)
    (hHom : ∀ f : S.fgObj z.1 ⟶ U, f = 0) :
    Subsingleton (Ext.{u} U (S.fgObj (S.rightTranslationLabel z)) 1) := by
  obtain ⟨P⟩ := twoStepMinimalProjectivePresentation_nonempty k
    (S.fgObj z.1)
  obtain ⟨eNak⟩ := S.rightTranslationIso_nakayamaKernel H z P
  have hzero : ∀ xi : Ext.{u}
      U
      (S.fgObj (S.rightTranslationLabel z)) 1, xi = 0 := by
    intro xi
    let xi' : Ext.{u}
        U
        (P.nakayamaKernel (k := k)) 1 :=
      xi.comp (Ext.mk₀ eNak.hom) (add_zero 1)
    have hstable : ∀ a : RightModule.projectiveStableHom
        (k := k) (S.fgObj z.1)
        U, a = 0 := by
      intro a
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      have hf : f = 0 :=
        hHom f
      rw [hf]
      simp
    have hxi' : xi' = 0 := by
      apply (P.stableHomExtLinearEquiv (k := k)
        U).injective
      apply LinearMap.ext
      intro a
      rw [hstable a]
      simp
    have hrecover := congrArg
      (fun eta : Ext.{u}
          U
          (P.nakayamaKernel (k := k)) 1 ↦
        eta.comp (Ext.mk₀ eNak.inv) (add_zero 1)) hxi'
    simpa [xi', Ext.comp_assoc_of_second_deg_zero] using hrecover
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩


/-- Hom vanishing into I also holds into every subobject of I, so AR duality
provides precisely the subobject Ext vanishing used by the finite-kernel lemma. -/
theorem extOne_rightTranslation_subsingleton_of_mono
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (I : FinitelyGeneratedCategory A)
    (hHom : ∀ f : S.fgObj z.1 ⟶ I, f = 0)
    (U : FinitelyGeneratedCategory A) (j : U ⟶ I) [Mono j] :
    Subsingleton (Ext.{u} U (S.fgObj (S.rightTranslationLabel z)) 1) := by
  apply S.extOne_rightTranslation_subsingleton_of_hom_zero H z U
  intro f
  apply (cancel_mono j).mp
  simpa using hHom (f ≫ j)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
