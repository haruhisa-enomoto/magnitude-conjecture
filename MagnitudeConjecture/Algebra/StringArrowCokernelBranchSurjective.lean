import MagnitudeConjecture.Algebra.StringArrowCokernelBranchInjective
import MagnitudeConjecture.Algebra.StringArrowCokernelBranchSection

/-! # Surjectivity of the surviving-branch map -/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

set_option maxHeartbeats 2000000 in
theorem otherIncomingFamilyToCokernelRadical_surjective
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Function.Surjective (P.otherIncomingFamilyToCokernelRadical a) := by
  classical
  intro z
  let e := P.incomingArrowRangeFamilyRadicalLinearEquiv y
  let s := P.arrowCokernelRadicalSection a z
  let f := e.symm s
  let g : ∀ b : OtherIncomingArrow (Sigma.mk x a),
      LinearMap.range (P.representedArrowLinearMap b.1.2) :=
    fun b ↦ f b.1
  refine ⟨g, ?_⟩
  have hinsert :
      P.otherIncomingFamilyInsertion (Sigma.mk x a) g = f := by
    funext b
    by_cases hb : b = Sigma.mk x a
    · subst b
      have hself :
          P.otherIncomingFamilyInsertion (Sigma.mk x a) g
            (Sigma.mk x a) = 0 := by
        exact P.otherIncomingFamilyInsertion_apply_self
          (Sigma.mk x a) g
      rw [hself]
      exact (P.arrowCokernelRadicalSection_selectedCoordinate a z).symm
    · let b' : OtherIncomingArrow (Sigma.mk x a) := ⟨b, hb⟩
      have hother :
          P.otherIncomingFamilyInsertion (Sigma.mk x a) g b'.1 = g b' := by
        exact P.otherIncomingFamilyInsertion_apply_other
          (Sigma.mk x a) g b'
      exact hother
  change P.arrowCokernelRadicalLinearMap a
      (e (P.otherIncomingFamilyInsertion (Sigma.mk x a) g)) = z
  rw [hinsert]
  change P.arrowCokernelRadicalLinearMap a (e (e.symm s)) = z
  rw [e.apply_symm_apply]
  have hsection := LinearMap.congr_fun
    (P.arrowCokernelRadicalMap_section a) z
  exact hsection

end MagnitudeConjecture.BoundQuiver.StringPresentation
