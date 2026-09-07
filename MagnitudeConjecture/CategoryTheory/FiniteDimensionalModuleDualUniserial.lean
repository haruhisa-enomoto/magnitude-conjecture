import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDualSkeleton
import MagnitudeConjecture.CategoryTheory.UniserialObject

/-!
# Uniseriality under finite-dimensional coefficient duality

This leaf module keeps abelian and uniserial structure out of the foundational
coefficient-duality files.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.IsUniserialObject

universe v u

variable {C : Type u} [Category.{v} C]

/-- Passing back from the opposite category preserves uniseriality. -/
theorem unop [Abelian C] {X : Cᵒᵖ} (hX : IsUniserialObject X) :
    IsUniserialObject X.unop := by
  have hop : IsUniserialObject (Opposite.op X) := hX.op
  simpa using
    (IsUniserialObject.map_equivalence hop (opOpEquivalence C))

/-- An epimorphic image of a uniserial object in an abelian category is
uniserial.  Opposite-category duality realizes the target as a subobject of
the opposite of the source. -/
theorem of_epi [Abelian C] {X Y : C} (hX : IsUniserialObject X)
    (f : X ⟶ Y) [Epi f] : IsUniserialObject Y := by
  have hopX : IsUniserialObject (Opposite.op X) := hX.op
  have hopY : IsUniserialObject
      ((Subobject.mk f.op : Subobject (Opposite.op X)) : Cᵒᵖ) :=
    hopX.subobject (Subobject.mk f.op)
  have hY' := hopY.unop
  exact hY'.congr (Subobject.underlyingIso f.op).unop.symm

end MagnitudeConjecture.IsUniserialObject

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Finite C] [Category.{v} C]
  [Preadditive C] [Linear k C]

/-- Finite-dimensional coefficient duality preserves and reflects
uniseriality. -/
theorem finiteCoefficientDual_isUniserialObject_iff
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    IsUniserialObject
        ((finiteCoefficientDualFunctor (k := k) (C := C)).obj
          (Opposite.op M)) ↔
      IsUniserialObject M := by
  let D := finiteCoefficientDualityEquivalence (k := k) (C := C)
  constructor
  · intro hdual
    have hOpposite : IsUniserialObject (Opposite.op M) :=
      IsUniserialObject.of_map_equivalence D hdual
    exact IsUniserialObject.unop hOpposite
  · intro hM
    have hOpposite : IsUniserialObject (Opposite.op M) :=
      IsUniserialObject.op hM
    exact IsUniserialObject.map_equivalence hOpposite D

/-- Reverse coefficient duality preserves and reflects uniseriality. -/
theorem reverseFiniteCoefficientDual_isUniserialObject_iff
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    IsUniserialObject (reverseFiniteCoefficientDual (k := k) M) ↔
      IsUniserialObject M := by
  let D := finiteCoefficientDualityEquivalence (k := k) (C := C)
  let R := reverseFiniteCoefficientDual (k := k) M
  let e : D.functor.obj (Opposite.op R) ≅ M :=
    finiteCoefficientDualReverseIso (k := k) M
  constructor
  · intro hR
    have hOpposite : IsUniserialObject (Opposite.op R) :=
      IsUniserialObject.op hR
    have hDual : IsUniserialObject (D.functor.obj (Opposite.op R)) :=
      IsUniserialObject.map_equivalence hOpposite D
    exact IsUniserialObject.congr hDual e
  · intro hM
    have hDual : IsUniserialObject (D.functor.obj (Opposite.op R)) :=
      IsUniserialObject.congr hM e.symm
    have hOpposite : IsUniserialObject (Opposite.op R) :=
      IsUniserialObject.of_map_equivalence D hDual
    exact IsUniserialObject.unop hOpposite

end MagnitudeConjecture.CoveringHom
