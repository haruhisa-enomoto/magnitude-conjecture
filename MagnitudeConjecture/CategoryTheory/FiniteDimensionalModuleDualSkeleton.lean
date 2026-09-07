import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDuality
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteType

/-!
# Finite indecomposable skeletons under coefficient duality

Pointwise coefficient duality transports a duplicate-free complete skeleton
of finite modules over a linear category to one over the opposite category.
The labels are unchanged, while the anti-equivalence reverses morphisms.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- The reverse pointwise coefficient dual, bundled as a finite module over
the original category. -/
noncomputable def reverseFiniteCoefficientDual
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  ⟨reverseCoefficientDualModule (k := k) M.obj,
    reverseCoefficientDualModule_isFiniteDimensionalModule (k := k) M⟩

/-- Dualizing the reverse coefficient dual recovers the original finite
module. -/
noncomputable def finiteCoefficientDualReverseIso
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    (finiteCoefficientDualFunctor (k := k) (C := C)).obj
        (Opposite.op (reverseFiniteCoefficientDual (k := k) M)) ≅ M := by
  exact ObjectProperty.isoMk _
    (coefficientReverseDoubleDualLinearIso (k := k) M)

/-- The reverse coefficient dual is injective exactly when the original
finite module is projective.  The reversal is forced by the intervening
opposite category; coefficient duality is an anti-equivalence. -/
theorem reverseFiniteCoefficientDual_injective_iff_projective
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    Injective (reverseFiniteCoefficientDual (k := k) M) ↔ Projective M := by
  let E := finiteCoefficientDualityEquivalence (k := k) (C := C)
  let R := reverseFiniteCoefficientDual (k := k) M
  let e : E.functor.obj (Opposite.op R) ≅ M :=
    finiteCoefficientDualReverseIso (k := k) M
  constructor
  · intro hR
    have hop : Projective (Opposite.op R) :=
      Injective.injective_iff_projective_op.mp hR
    have hmap : Projective (E.functor.obj (Opposite.op R)) :=
      (E.map_projective_iff (Opposite.op R)).2 hop
    exact Projective.of_iso e hmap
  · intro hM
    have hmap : Projective (E.functor.obj (Opposite.op R)) :=
      Projective.of_iso e.symm hM
    have hop : Projective (Opposite.op R) :=
      (E.map_projective_iff (Opposite.op R)).1 hmap
    exact Injective.injective_iff_projective_op.mpr hop

/-- Dually, the reverse coefficient dual is projective exactly when the
original finite module is injective. -/
theorem reverseFiniteCoefficientDual_projective_iff_injective
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    Projective (reverseFiniteCoefficientDual (k := k) M) ↔ Injective M := by
  let E := finiteCoefficientDualityEquivalence (k := k) (C := C)
  let R := reverseFiniteCoefficientDual (k := k) M
  let e : E.functor.obj (Opposite.op R) ≅ M :=
    finiteCoefficientDualReverseIso (k := k) M
  constructor
  · intro hR
    have hop : Injective (Opposite.op R) :=
      Injective.projective_iff_injective_op.mp hR
    have hmap : Injective (E.functor.obj (Opposite.op R)) :=
      (E.map_injective_iff (Opposite.op R)).2 hop
    exact Injective.of_iso e hmap
  · intro hM
    have hmap : Injective (E.functor.obj (Opposite.op R)) :=
      Injective.of_iso e.symm hM
    have hop : Injective (Opposite.op R) :=
      (E.map_injective_iff (Opposite.op R)).1 hmap
    exact Injective.projective_iff_injective_op.mpr hop

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- Transport a finite complete indecomposable skeleton through pointwise
coefficient duality.  This is an anti-equivalence, so the target is the
finite-module category over `Cᵒᵖ`. -/
noncomputable def coefficientDual
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C)) :
    FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := Cᵒᵖ) := by
  let E := finiteCoefficientDualityEquivalence (k := k) (C := C)
  letI : E.functor.Additive := finiteCoefficientDualFunctor_additive
  letI : E.inverse.Additive := inferInstance
  refine
    { n := S.n
      obj := fun i ↦ E.functor.obj (Opposite.op (S.obj i))
      indecomposable := ?_
      skeletal := ?_
      complete := ?_ }
  · intro i
    exact (finiteCoefficientDualFunctor_indec_iff (S.obj i)).2
      (S.indecomposable i)
  · intro i j hij
    obtain ⟨hij⟩ := hij
    let eop : Opposite.op (S.obj i) ≅ Opposite.op (S.obj j) :=
      E.functor.preimageIso hij
    exact (S.skeletal ⟨Iso.unop eop⟩).symm
  · intro M hM
    have hpreOp : Indecomposable (E.inverse.obj M) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse M).2 hM
    have hpre : Indecomposable (E.inverse.obj M).unop := by
      simpa only [Opposite.op_unop] using
        (MagnitudeConjecture.CategoryTheory.indecomposable_op_iff
          (E.inverse.obj M).unop).mp hpreOp
    obtain ⟨i, ⟨hi⟩⟩ := S.complete (E.inverse.obj M).unop hpre
    let eop : E.inverse.obj M ≅ Opposite.op (S.obj i) := by
      simpa only [Opposite.op_unop] using Iso.op hi.symm
    exact ⟨i, ⟨(E.counitIso.app M).symm ≪≫ E.functor.mapIso eop⟩⟩

end MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton
