import Mathlib.Algebra.Algebra.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Linear structure on an opposite category

The opposite of a `k`-linear category is `k`-linear, with scalar action
transported through morphism reversal.
-/

set_option autoImplicit false

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- The opposite of a linear category carries the same scalar action on
Hom spaces. -/
instance oppositeLinear : CategoryTheory.Linear k Cᵒᵖ where
  homModule X Y := Equiv.module k (CategoryTheory.opEquiv X Y)
  smul_comp := by
    intro X Y Z r f g
    apply Quiver.Hom.unop_inj
    change g.unop ≫ (r • f.unop) = r • (g.unop ≫ f.unop)
    simp
  comp_smul := by
    intro X Y Z f r g
    apply Quiver.Hom.unop_inj
    change (r • g.unop) ≫ f.unop = r • (g.unop ≫ f.unop)
    simp

/-- Reversing an opposite-category morphism is a linear equivalence. -/
def oppositeHomLinearEquiv (X Y : Cᵒᵖ) :
    (X ⟶ Y) ≃ₗ[k] (Y.unop ⟶ X.unop) :=
  { CategoryTheory.opEquiv X Y with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

@[simp]
theorem opposite_unop_smul {X Y : Cᵒᵖ} (r : k) (f : X ⟶ Y) :
    (r • f).unop = r • f.unop :=
  rfl

@[simp]
theorem opposite_op_smul {X Y : C} (r : k) (f : X ⟶ Y) :
    (r • f).op = r • f.op :=
  rfl

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable [CategoryTheory.Linear k D]

/-- The opposite of a linear functor is linear for the transported linear
structures on the opposite categories. -/
instance functorOpLinear (F : C ⥤ D)
    [CategoryTheory.Functor.Linear k F] :
    CategoryTheory.Functor.Linear k F.op where
  map_smul f r := by
    apply Quiver.Hom.unop_inj
    change F.map (r • f.unop) = r • F.map f.unop
    exact F.map_smul r f.unop

/-- Turning a functor out of an opposite category around on both sides
preserves linearity. -/
instance functorRightOpLinear (F : Cᵒᵖ ⥤ D)
    [CategoryTheory.Functor.Linear k F] :
    CategoryTheory.Functor.Linear k F.rightOp where
  map_smul f r := by
    apply Quiver.Hom.unop_inj
    change F.map (r • f.op) = r • F.map f.op
    exact F.map_smul r f.op

end MagnitudeConjecture.CoveringHom
