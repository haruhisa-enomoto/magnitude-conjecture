import MagnitudeConjecture.Algebra.RightModuleFiniteType

/-! # A right-module skeleton from a complete finite family in FGModuleCat -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {ι : Type} [Fintype ι]

/-- Preserve the exact size of a complete family with no repeated isomorphism classes. -/
def ofFGFamily (F : ι → RightModule.FinitelyGeneratedCategory.{u} A)
    (hF : ∀ i, Indecomposable (F i))
    (hcomplete : ∀ X : RightModule.FinitelyGeneratedCategory.{u} A, Indecomposable X →
      ∃ i, Nonempty (X ≅ F i))
    (hskeletal : ∀ i j, Nonempty (F i ≅ F j) → i = j) :
    RightModule.FiniteIndecomposableSkeleton k A where
  n := Fintype.card ι
  obj i := (F ((Fintype.equivFin ι).symm i)).obj
  obj_finite i := RightModule.finite_over_field_of_finitelyGenerated k A _
  obj_indecomposable i := (indecomposable_iff_obj (k := k) _).mp (hF _)
  eq_of_iso {i j} h := by
    apply (Fintype.equivFin ι).symm.injective
    exact hskeletal _ _ (h.map fun e ↦
      (forget₂ (RightModule.FinitelyGeneratedCategory A) (RightModule.Category A)).preimageIso e)
  complete M hM := by
    letI : Module.Finite k M := hM.1
    let X := RightModule.finitelyGeneratedOfFiniteDimensional (k := k) A M
    have hX : Indecomposable X := (indecomposable_iff_obj (k := k) X).mpr hM.2
    obtain ⟨i, ⟨e⟩⟩ := hcomplete X hX
    refine ⟨(Fintype.equivFin ι) i, ?_⟩
    simpa only [Equiv.symm_apply_apply] using
      (show Nonempty (M ≅ (F i).obj) from
        ⟨(forget₂ (RightModule.FinitelyGeneratedCategory A) (RightModule.Category A)).mapIso e⟩)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
