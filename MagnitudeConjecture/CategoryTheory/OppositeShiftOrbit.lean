import MagnitudeConjecture.CategoryTheory.OppositeDeckShift
import MagnitudeConjecture.CategoryTheory.OrbitPushdownCorepresentable

/-!
# Opposite shift-orbit Hom spaces

For the naive shift on an opposite category, reversing a homogeneous
degree-`a` morphism produces a source-shifted morphism in the original
category.  Reindexing by negation therefore identifies an opposite
shift-orbit Hom space with the reversed original shift-orbit Hom space.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- Reversing opposite homogeneous morphisms componentwise, followed by
the source-shift decomposition, identifies the opposite orbit Hom with the
reversed original orbit Hom. -/
noncomputable def oppositeShiftOrbitHomLinearEquiv (X Y : Cᵒᵖ) :
    letI : HasShift Cᵒᵖ A :=
      hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)
    ShiftOrbitHom A X Y ≃ₗ[k] ShiftOrbitHom A Y.unop X.unop := by
  letI : HasShift Cᵒᵖ A :=
    hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)
  let e₁ : ShiftOrbitHom A X Y ≃ₗ[k]
      DirectSum A (fun a ↦ (shiftFunctor C a).obj Y.unop ⟶ X.unop) :=
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun a ↦
      oppositeHomLinearEquiv X ((shiftFunctor Cᵒᵖ a).obj Y)
  exact e₁.trans
    (shiftSourceHomDirectSumEquiv (k := k) (A := A) Y.unop X.unop)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem oppositeShiftOrbitHomLinearEquiv_shiftOrbitLof
    (X Y : Cᵒᵖ) (a : A)
    (f : letI : HasShift Cᵒᵖ A :=
        hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)
      ShiftHom X Y ((Equiv.neg A).symm a)) :
    letI : HasShift Cᵒᵖ A :=
      hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)
    oppositeShiftOrbitHomLinearEquiv (k := k) (A := A) X Y
        (shiftOrbitLof (k := k) X Y ((Equiv.neg A).symm a) f) =
      shiftOrbitLof (k := k) Y.unop X.unop a
        (shiftSourceHomLinearEquiv (k := k) Y.unop X.unop
          ((Equiv.neg A).symm a) a (neg_negEquiv_symm a) f.unop) := by
  letI : HasShift Cᵒᵖ A :=
    hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)
  classical
  unfold oppositeShiftOrbitHomLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [shiftOrbitLof_apply]
  change shiftSourceHomDirectSumEquiv (k := k) (A := A) Y.unop X.unop
      (MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv
        (fun b ↦ oppositeHomLinearEquiv X ((shiftFunctor Cᵒᵖ b).obj Y))
        (DirectSum.of (fun b ↦ ShiftHom X Y b) ((Equiv.neg A).symm a) f)) = _
  rw [MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv_of]
  change shiftSourceHomDirectSumEquiv (k := k) (A := A) Y.unop X.unop
      (directSumInclusion (k := k)
        (fun b ↦ ((shiftFunctor C b).obj Y.unop ⟶ X.unop))
          ((Equiv.neg A).symm a) f.unop) = _
  exact shiftSourceHomDirectSumEquiv_inclusion_neg
    (k := k) (A := A) Y.unop X.unop a f.unop

end MagnitudeConjecture.CoveringHom
