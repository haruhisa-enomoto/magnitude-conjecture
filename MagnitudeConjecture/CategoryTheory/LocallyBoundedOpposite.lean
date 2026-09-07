import MagnitudeConjecture.CategoryTheory.AdmissibleModuleCategory
import MagnitudeConjecture.CategoryTheory.OppositeLinear

/-!
# Locally bounded opposite categories

The locally bounded package used by the covering argument is self-dual.  This
file records the variance change explicitly, including finite object support
and the opposite endomorphism ring.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Endomorphisms in the opposite category form the opposite endomorphism
ring. -/
def oppositeEndRingEquiv (X : C) :
    (End X)ᵐᵒᵖ ≃+* End (Opposite.op X) where
  toFun f := f.unop.op
  invFun f := MulOpposite.op f.unop
  left_inv := by intro f; cases f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; apply Quiver.Hom.unop_inj; rfl
  map_mul' := by intro f g; apply Quiver.Hom.unop_inj; rfl

/-- A noncommutative local ring remains local after reversing
multiplication. -/
theorem isLocalRing_mulOpposite
    {R : Type v} [Ring R] [IsLocalRing R] :
    IsLocalRing Rᵐᵒᵖ := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := R) (a := a.unop) (b := 1 - a.unop)
      (add_sub_cancel a.unop 1) with h | h
  · exact Or.inl (by simpa using h.op)
  · exact Or.inr (by simpa using h.op)

/-- Locally boundedness is preserved by passage to the opposite category.
The covariant-representable support on the opposite is controlled by the
dual-corepresentable support on the original category, and conversely. -/
theorem IsLocallyBounded.op
    (H : IsLocallyBounded (k := k) (C := C)) :
    IsLocallyBounded (k := k) (C := Cᵒᵖ) where
  skeletal := by
    intro X Y hXY
    obtain ⟨e⟩ := hXY
    exact congrArg Opposite.op (H.skeletal ⟨e.unop.symm⟩)
  finiteCovariantRepresentables := by
    intro X
    constructor
    · intro Y
      change FiniteDimensional k (X ⟶ Y)
      letI : FiniteDimensional k (Y.unop ⟶ X.unop) :=
        (H.finiteCovariantRepresentables Y.unop).1 X.unop
      exact FiniteDimensional.of_injective
        (oppositeHomLinearEquiv (k := k) (C := C) X Y).toLinearMap
        (oppositeHomLinearEquiv (k := k) (C := C) X Y).injective
    · let T : Set C :=
        {Y | Nontrivial (Module.Dual k (Y ⟶ X.unop))}
      have hT : T.Finite :=
        (H.finiteDualCorepresentables X.unop).2
      have hpre : (Opposite.unop ⁻¹' T).Finite :=
        hT.preimage (Set.injOn_of_injective Opposite.unop_injective)
      refine hpre.subset ?_
      intro Y hY
      change Nontrivial (X ⟶ Y) at hY
      change Nontrivial (Module.Dual k (Y.unop ⟶ X.unop))
      exact (Module.nontrivial_dual_iff k).mpr
        ((oppositeHomLinearEquiv (k := k) (C := C) X Y).toEquiv
          |>.nontrivial_congr.mp hY)
  finiteDualCorepresentables := by
    intro X
    constructor
    · intro Y
      change FiniteDimensional k (Module.Dual k (Y ⟶ X))
      letI : FiniteDimensional k (X.unop ⟶ Y.unop) :=
        (H.finiteCovariantRepresentables X.unop).1 Y.unop
      letI : FiniteDimensional k (Y ⟶ X) :=
        FiniteDimensional.of_injective
          (oppositeHomLinearEquiv (k := k) (C := C) Y X).toLinearMap
          (oppositeHomLinearEquiv (k := k) (C := C) Y X).injective
      infer_instance
    · let T : Set C := {Y | Nontrivial (X.unop ⟶ Y)}
      have hT : T.Finite :=
        (H.finiteCovariantRepresentables X.unop).2
      have hpre : (Opposite.unop ⁻¹' T).Finite :=
        hT.preimage (Set.injOn_of_injective Opposite.unop_injective)
      refine hpre.subset ?_
      intro Y hY
      change Nontrivial (Module.Dual k (Y ⟶ X)) at hY
      change Nontrivial (X.unop ⟶ Y.unop)
      exact (oppositeHomLinearEquiv (k := k) (C := C) Y X).toEquiv
        |>.nontrivial_congr.mp
        ((Module.nontrivial_dual_iff k).mp hY)
  localEndomorphismRings := by
    intro X
    letI : IsLocalRing (End X.unop) :=
      H.localEndomorphismRings X.unop
    letI : IsLocalRing (End X.unop)ᵐᵒᵖ :=
      isLocalRing_mulOpposite
    exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (oppositeEndRingEquiv X.unop)

end MagnitudeConjecture.CoveringHom
