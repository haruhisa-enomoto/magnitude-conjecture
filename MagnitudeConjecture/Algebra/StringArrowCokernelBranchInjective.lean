import MagnitudeConjecture.Algebra.StringArrowCokernelBranchBasic

/-! # Injectivity of the surviving-branch map -/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

set_option maxHeartbeats 2000000 in
theorem otherIncomingFamilyToCokernelRadical_injective
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Function.Injective (P.otherIncomingFamilyToCokernelRadical a) := by
  classical
  intro g h hgh
  apply funext
  intro b
  let e := P.incomingArrowRangeFamilyRadicalLinearEquiv y
  have hzero :
      P.otherIncomingFamilyToCokernelRadical a (g - h) = 0 := by
    rw [map_sub, hgh, sub_self]
  have hker :
      e (P.otherIncomingFamilyInsertion (Sigma.mk x a) (g - h)) ∈
        LinearMap.ker (P.arrowCokernelRadicalLinearMap a) := by
    rw [LinearMap.mem_ker]
    exact hzero
  rw [P.arrowCokernelRadicalMap_ker a] at hker
  obtain ⟨z, hz⟩ := hker
  have hzsymm :
      e.symm (e (P.otherIncomingFamilyInsertion
        (Sigma.mk x a) (g - h))) =
        e.symm (P.arrowBranchRadicalInclusionLinearMap
          (Sigma.mk x a) z) :=
    congrArg (fun w ↦ e.symm w) hz.symm
  have hfamily :
      P.otherIncomingFamilyInsertion (Sigma.mk x a) (g - h) =
        P.incomingArrowRangeFamilySingle (Sigma.mk x a) z := by
    have hsingle :
        e.symm (P.arrowBranchRadicalInclusionLinearMap
          (Sigma.mk x a) z) =
          P.incomingArrowRangeFamilySingle (Sigma.mk x a) z :=
      P.incomingArrowRangeFamilyRadicalLinearEquiv_symm_branchInclusion
        (Sigma.mk x a) z
    exact Eq.trans (e.symm_apply_apply _).symm (Eq.trans hzsymm hsingle)
  have hb := congrFun hfamily b.1
  have hbLeft :
      P.otherIncomingFamilyInsertion (Sigma.mk x a) (g - h) b.1 =
        (g - h) b := by
    exact P.otherIncomingFamilyInsertion_apply_other
      (Sigma.mk x a) (g - h) b
  rw [hbLeft] at hb
  have hbne : b.1 ≠ Sigma.mk x a := b.2
  have hbRight :
      P.incomingArrowRangeFamilySingle (Sigma.mk x a) z b.1 = 0 := by
    unfold incomingArrowRangeFamilySingle
    exact Pi.single_eq_of_ne
      (M := fun c : DisplayedIncomingArrow y ↦
        LinearMap.range (P.representedArrowLinearMap c.2)) hbne z
  rw [hbRight] at hb
  exact sub_eq_zero.mp hb

end MagnitudeConjecture.BoundQuiver.StringPresentation
