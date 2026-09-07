import MagnitudeConjecture.CategoryTheory.DeckShiftAction
import MagnitudeConjecture.CategoryTheory.OppositeLinear
import MagnitudeConjecture.CategoryTheory.OrbitPushdownCommShift
import Mathlib.CategoryTheory.Shift.Opposite

/-!
# Coherent deck shifts on opposite categories

A left deck action on a category acts on its opposite by the same object
permutation.  The naive opposite of the associated coherent right shift is
again a coherent deck shift for that action.  This file packages the action,
its freeness, and the compatibility of opposite functors with shifts.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]

/-- The same left object action, transported to the opposite category. -/
@[implicit_reducible]
def oppositeMulAction : MulAction G Cᵒᵖ where
  smul g X := Opposite.op (g • X.unop)
  one_smul X := congrArg Opposite.op (one_smul G X.unop)
  mul_smul g h X := congrArg Opposite.op (mul_smul g h X.unop)

omit [Category.{v} C] in
/-- A free/cancellative object action remains so on the opposite category. -/
theorem oppositeIsCancelSMul [IsCancelSMul G C] :
    letI := oppositeMulAction (C := C) (G := G)
    IsCancelSMul G Cᵒᵖ := by
  letI := oppositeMulAction (C := C) (G := G)
  exact
    { right_cancel' := by
        intro g h X hgh
        apply IsCancelSMul.right_cancel g h X.unop
        exact congrArg Opposite.unop hgh }

namespace CoherentDeckShift

/-- The naive opposite of a coherent deck shift. -/
def op (D : CoherentDeckShift C G) :
    letI := oppositeMulAction (C := C) (G := G)
    CoherentDeckShift Cᵒᵖ G := by
  letI := oppositeMulAction (C := C) (G := G)
  letI := D.hasShift
  exact
    { core := HasShift.mkShiftCoreOp C (Additive G)
      objIso := fun g X ↦ (D.objIso g X.unop).op.symm }

/-- The shift instance exported by the opposite coherent package is
Mathlib's naive opposite shift. -/
theorem op_hasShift_eq (D : CoherentDeckShift C G) :
    letI := D.hasShift
    letI := oppositeMulAction (C := C) (G := G)
    D.op.hasShift = hasShiftMk Cᵒᵖ (Additive G)
      (HasShift.mkShiftCoreOp C (Additive G)) := by
  letI := D.hasShift
  letI := oppositeMulAction (C := C) (G := G)
  rfl

section Linear

variable {k : Type uK} [Field k]
variable [Preadditive C] [CategoryTheory.Linear k C]

noncomputable instance op_core_additive
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    (a : Additive G) :
    letI := oppositeMulAction (C := C) (G := G)
    ((D.op.core.F a).Additive) := by
  letI := D.hasShift
  letI := oppositeMulAction (C := C) (G := G)
  letI : (shiftFunctor C a).Additive := by
    change (D.core.F a).Additive
    infer_instance
  dsimp only [op]
  change ((shiftFunctor C a).op.Additive)
  infer_instance

noncomputable instance op_core_linear
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Linear k]
    (a : Additive G) :
    letI := oppositeMulAction (C := C) (G := G)
    ((D.op.core.F a).Linear k) := by
  letI := D.hasShift
  letI := oppositeMulAction (C := C) (G := G)
  letI : (shiftFunctor C a).Linear k := by
    change (D.core.F a).Linear k
    infer_instance
  dsimp only [op]
  change ((shiftFunctor C a).op.Linear k)
  infer_instance

end Linear

end CoherentDeckShift

/-- The naive opposite of a trivial shift is the trivial shift on the
opposite category. -/
theorem oppositeTrivialHasShift_eq
    (E : Type u) [Category.{v} E]
    (A : Type w) [AddMonoid A] :
    letI := trivialHasShift E A
    hasShiftMk Eᵒᵖ A (HasShift.mkShiftCoreOp E A) =
      trivialHasShift Eᵒᵖ A := by
  letI := trivialHasShift E A
  rfl

/-- If a functor from a coherent deck-shift category to a trivially shifted
target commutes with shifts, then its opposite has the same property for the
opposite coherent deck shift and the trivial opposite target shift. -/
@[implicit_reducible]
noncomputable def opFunctorCommShiftToTrivial
    {E : Type u} [Category.{v} E]
    (D : CoherentDeckShift C G) (F : C ⥤ E)
    (hF :
      letI := D.hasShift
      letI := trivialHasShift E (Additive G)
      F.CommShift (Additive G)) :
    letI := oppositeMulAction (C := C) (G := G)
    let Dop := D.op
    letI := Dop.hasShift
    letI := trivialHasShift Eᵒᵖ (Additive G)
    F.op.CommShift (Additive G) := by
  letI := D.hasShift
  letI : HasShift E (Additive G) := trivialHasShift E (Additive G)
  letI : F.CommShift (Additive G) := hF
  letI := oppositeMulAction (C := C) (G := G)
  let Dop := D.op
  letI := Dop.hasShift
  letI : HasShift Eᵒᵖ (Additive G) :=
    trivialHasShift Eᵒᵖ (Additive G)
  change @Functor.CommShift Cᵒᵖ Eᵒᵖ _ _ F.op (Additive G) _
    Dop.hasShift (trivialHasShift Eᵒᵖ (Additive G))
  rw [D.op_hasShift_eq, ← oppositeTrivialHasShift_eq E (Additive G)]
  change (OppositeShift.functor (Additive G) F).CommShift (Additive G)
  infer_instance

end MagnitudeConjecture.CoveringHom
