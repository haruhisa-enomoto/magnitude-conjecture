import MagnitudeConjecture.CategoryTheory.OrbitPullupPushdownDecomposition
import MagnitudeConjecture.CategoryTheory.OrbitPushdownAdjunction

/-!
# Gabriel's pull-up/push-down decomposition

This file identifies the explicit coproduct model for pull-up of push-down
with the bundled pull-up functor and with the formal module shifts attached to
a chosen shift core.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- The explicit coproduct object is the bundled pull-up of the bundled
push-down. -/
noncomputable def linearOrbitPullupPushdownIso
    (M : LinearModuleCategory.{u, v, uK, max w uM} (C := C) k) :
    (linearOrbitPullupPushdownTranslateCofan (A := A) M).pt ≅
      (linearModuleOrbitPullup
        (k := k) (C := C) (A := A)).obj
          ((linearModuleOrbitPushdown
            (k := k) (C := C) (A := A)).obj M) :=
  ObjectProperty.isoMk _ (orbitPullupPushdownIso M.obj)

end MagnitudeConjecture.CoveringHom
