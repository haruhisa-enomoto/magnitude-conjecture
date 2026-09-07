import MagnitudeConjecture.CategoryTheory.ObjectDeletionSurvivingWindows
import MagnitudeConjecture.CategoryTheory.FiniteModuleResidualSeparation
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownAdditiveControlWindow

/-!
# Uniform residual separation for object-deletion stages

The manuscript first chooses one finite module family controlling every
intermediate object-deletion stage and then uses residual finiteness once on
that family.  This file joins those two already formalized steps: the subgroup
is independent of the deletion stage, and its nonidentity shifted Homs vanish
on the entire additive closure of the common control family.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- One application of residual finiteness separates the common finite
control family selected from all realized survivor signatures.  This is the
formal conjunction of the manuscript's finite-union step and its choice of
the normal finite-index subgroup `Γ`. -/
theorem exists_uniformControlFamily_and_residuallySeparatedWindow_for_threeStepDeletionStages
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    [Group.ResiduallyFinite G]
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    (Allowed : Set C → Prop)
    (Control : Set C →
      FiniteIndecomposableModuleFamily (k := k) (C := C) → Prop)
    (exists_control : ∀ E, Allowed E → ∃ V, Control E V)
    (control_invariant :
      ∀ {E F}, Allowed E → Allowed F →
        deletionSurvivingIndices (k := k) C
            (finiteThreeStepControlFamily hlocal y) E =
          deletionSurvivingIndices (k := k) C
            (finiteThreeStepControlFamily hlocal y) F →
        ∀ {V}, Control E V ↔ Control F V)
    (control_upward :
      ∀ E, Allowed E → ∀ {V U}, Control E V →
        V.isoClosure ⊆ U.isoClosure → Control E U) :
    ∃ U : FiniteIndecomposableModuleFamily (k := k) (C := C),
      (∀ E, Allowed E → Control E U) ∧
        ∃ N : FiniteIndexNormalSubgroup G,
          (∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G) U,
            g ∉ N) ∧
            (D.restrict N).FiniteModuleWindowShiftHomOrthogonal
              (k := k) U.additiveClosure := by
  obtain ⟨U, hU⟩ :=
    exists_uniformControlFamily_for_threeStepDeletionStages (k := k) C
      hlocal y Allowed Control exists_control control_invariant control_upward
  obtain ⟨N, havoid⟩ :=
    exists_finiteIndexNormalSubgroup_avoiding_supportBadDegrees
      (G := G) U
  have hN :=
    D.restrict_finiteModuleWindowShiftHomOrthogonal_of_avoids
      (k := k) U N havoid
  refine ⟨U, hU, N, havoid, ?_⟩
  exact (D.restrict N).finiteModuleWindowShiftHomOrthogonal_additiveClosure U
    ((D.restrict N).finiteModuleWindowShiftHomOrthogonal_isoClosure U hN)

end MagnitudeConjecture.ObjectDeletion
