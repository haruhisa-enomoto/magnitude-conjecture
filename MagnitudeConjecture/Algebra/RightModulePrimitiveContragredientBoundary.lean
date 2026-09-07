import MagnitudeConjecture.Algebra.RightModulePrimitiveBoundary
import MagnitudeConjecture.Algebra.RightModuleContragredientMultiplicity
import MagnitudeConjecture.Algebra.RightModulePrimitiveContragredientSign
import MagnitudeConjecture.CategoryTheory.OppositeLinear

/-!
# Primitive boundary data under contragredient duality

The primitive multiplicity at a label is unchanged after passing to the
label-aligned contragredient skeleton.  Projective and injective boundary
bounds exchange, while the translation-difference bound is invariant under
reversing the difference and replacing right translation by inverse right
translation.  Consequently the boundary package on the opposite side is
constructed from the original coordinate estimate rather than supplied as
an independent hypothesis.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : PrimitiveIdempotentData e)

/-- Passing to the opposite category is a linear equivalence on each Hom
space. -/
private def homOpLinearEquiv (i j : Fin S.n) :
    (S.fgObj i ⟶ S.fgObj j) ≃ₗ[k]
      (Opposite.op (S.fgObj j) ⟶ Opposite.op (S.fgObj i)) where
  toFun := Quiver.Hom.op
  invFun := Quiver.Hom.unop
  left_inv := Quiver.Hom.unop_op
  right_inv := Quiver.Hom.op_unop
  map_add' f g := by apply Quiver.Hom.unop_inj; rfl
  map_smul' r f := by
    exact MagnitudeConjecture.CoveringHom.opposite_op_smul r f

/-- The concrete contragredient functor acts linearly on a Hom space. -/
private def contragredientMapLinearMap (i j : Fin S.n) :
    (Opposite.op (S.fgObj j) ⟶ Opposite.op (S.fgObj i)) →ₗ[k]
      ((Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.obj
          (Opposite.op (S.fgObj j)) ⟶
        (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.obj
          (Opposite.op (S.fgObj i))) where
  toFun := (Contragredient.dualFunctor k Aᵐᵒᵖ).map
  map_add' f g := by
    letI : Module k (S.fgObj i) :=
      Module.restrictScalars k Aᵐᵒᵖ (S.fgObj i)
    letI : IsScalarTower k Aᵐᵒᵖ (S.fgObj i) :=
      IsScalarTower.restrictScalars k Aᵐᵒᵖ (S.fgObj i)
    letI : Module k (S.fgObj j) :=
      Module.restrictScalars k Aᵐᵒᵖ (S.fgObj j)
    letI : IsScalarTower k Aᵐᵒᵖ (S.fgObj j) :=
      IsScalarTower.restrictScalars k Aᵐᵒᵖ (S.fgObj j)
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual k (S.fgObj j) at phi
    apply LinearMap.ext
    intro x
    change phi ((f + g).unop x) = phi (f.unop x) + phi (g.unop x)
    rw [show (f + g).unop = f.unop + g.unop by rfl]
    change phi (f.unop x + g.unop x) =
      phi (f.unop x) + phi (g.unop x)
    exact phi.map_add (f.unop x) (g.unop x)
  map_smul' r f := by
    letI : Module k (S.fgObj i) :=
      Module.restrictScalars k Aᵐᵒᵖ (S.fgObj i)
    letI : IsScalarTower k Aᵐᵒᵖ (S.fgObj i) :=
      IsScalarTower.restrictScalars k Aᵐᵒᵖ (S.fgObj i)
    letI : Module k (S.fgObj j) :=
      Module.restrictScalars k Aᵐᵒᵖ (S.fgObj j)
    letI : IsScalarTower k Aᵐᵒᵖ (S.fgObj j) :=
      IsScalarTower.restrictScalars k Aᵐᵒᵖ (S.fgObj j)
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual k (S.fgObj j) at phi
    apply LinearMap.ext
    intro x
    dsimp [Contragredient.dualFunctor, Contragredient.dualMap]
    change phi ((algebraMap k Aᵐᵒᵖ r) • f.unop x) =
      phi (f.unop ((algebraMap k (Aᵐᵒᵖ)ᵐᵒᵖ r).unop • x))
    rw [show (algebraMap k (Aᵐᵒᵖ)ᵐᵒᵖ r).unop =
      algebraMap k Aᵐᵒᵖ r by rfl]
    apply congrArg phi
    exact (f.unop.hom.hom.map_smul (algebraMap k Aᵐᵒᵖ r) x).symm

/-- Contragredient duality reverses Hom spaces between aligned skeleton
objects. -/
def contragredientHomLinearEquiv (i j : Fin S.n) :
    (S.fgObj i ⟶ S.fgObj j) ≃ₗ[k]
      (S.contragredientSkeleton.fgObj j ⟶
        S.contragredientSkeleton.fgObj i) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let B := S.contragredientAlignedBiduality
  let F := Contragredient.dualityEquivalence k Aᵐᵒᵖ
  exact
    (S.homOpLinearEquiv i j).trans
      ((LinearEquiv.ofBijective
          (S.contragredientMapLinearMap i j)
          ⟨F.functor.map_injective, F.functor.map_surjective⟩).trans
        (CategoryTheory.Linear.homCongr k
          (B.forward.objIso j) (B.forward.objIso i)))

/-- Primitive multiplicity is unchanged at the same literal finite label
under contragredient duality. -/
theorem contragredient_primitiveMultiplicity_eq (x : Fin S.n) :
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    S.contragredientSkeleton.primitiveMultiplicity D.opposite x =
      S.primitiveMultiplicity D x := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Sop := S.contragredientSkeleton
  calc
    Sop.primitiveMultiplicity D.opposite x =
        Module.finrank k
          (Sop.fgObj (Sop.primitiveSourceLabel D.opposite) ⟶
            Sop.fgObj x) :=
      Sop.primitiveMultiplicity_eq_sourceHom D.opposite x
    _ = Module.finrank k
        (Sop.fgObj (S.primitiveSinkLabel D) ⟶ Sop.fgObj x) := by
      rw [S.contragredient_primitiveSinkLabel_eq_primitiveSourceLabel D]
    _ = Module.finrank k
        (S.fgObj x ⟶ S.fgObj (S.primitiveSinkLabel D)) :=
      (S.contragredientHomLinearEquiv x
        (S.primitiveSinkLabel D)).finrank_eq.symm
    _ = S.primitiveMultiplicity D x :=
      (S.primitiveMultiplicity_eq_sinkHom D x).symm

/-- The original coordinate estimate canonically supplies its opposite-side
counterpart. -/
theorem MultiplicityCoordinateEstimate.contragredient
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D)) :
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    S.contragredientSkeleton.MultiplicityCoordinateEstimate
      (S.contragredientSkeleton.primitiveMultiplicityInput D.opposite) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Sop := S.contragredientSkeleton
  let B := S.contragredientAlignedBiduality
  refine {
    projective_le_one := ?_
    injective_le_one := ?_
    translation_difference_le_one := ?_ }
  · intro x hx
    change Sop.primitiveMultiplicity D.opposite x ≤ 1
    rw [S.contragredient_primitiveMultiplicity_eq D x]
    exact E.injective_le_one x
      ((B.forward.injective_iff_projective_image
        S.almostSplitSkeleton S.contragredientAlmostSplitSkeleton x).2 hx)
  · intro x hx
    change Sop.primitiveMultiplicity D.opposite x ≤ 1
    rw [S.contragredient_primitiveMultiplicity_eq D x]
    exact E.projective_le_one x
      ((B.backward.injective_iff_projective_image
        S.contragredientAlmostSplitSkeleton S.almostSplitSkeleton x).1 hx)
  · intro q
    let x : {i : Fin S.n // ¬ Injective (S.fgObj i)} := ⟨q.1, by
      intro hx
      apply q.2
      exact (B.forward.injective_iff_projective_image
        S.almostSplitSkeleton S.contragredientAlmostSplitSkeleton q.1).1 hx⟩
    let z : {i : Fin S.n // ¬ Projective (S.fgObj i)} :=
      (S.rightTranslationEquiv).symm x
    have hq : q = S.contragredientNonprojectiveLabel x :=
      Subtype.ext rfl
    have htranslateOp : Sop.rightTranslationLabel q = z.1 := by
      rw [hq]
      exact S.contragredient_rightTranslationLabel_eq_inverse x
    have htranslate : S.rightTranslationLabel z = x.1 :=
      congrArg Subtype.val (S.rightTranslationEquiv.apply_symm_apply x)
    have hbound := E.translation_difference_le_one z
    change abs ((Sop.primitiveMultiplicity D.opposite q.1 : ℤ) -
      (Sop.primitiveMultiplicity D.opposite
        (Sop.rightTranslationLabel q) : ℤ)) ≤ 1
    change abs ((S.primitiveMultiplicity D z.1 : ℤ) -
      (S.primitiveMultiplicity D (S.rightTranslationLabel z) : ℤ)) ≤ 1
      at hbound
    rw [S.contragredient_primitiveMultiplicity_eq D q.1,
      S.contragredient_primitiveMultiplicity_eq D
        (Sop.rightTranslationLabel q), htranslateOp]
    change abs ((S.primitiveMultiplicity D x.1 : ℤ) -
      (S.primitiveMultiplicity D z.1 : ℤ)) ≤ 1
    rw [htranslate] at hbound
    simpa [abs_sub_comm] using hbound

/-- Directed primitive boundary data on the contragredient side is derived
from the original directedness and coordinate estimate. -/
theorem PrimitiveDirectedBoundaryData.contragredient
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D)) :
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    S.contragredientSkeleton.PrimitiveDirectedBoundaryData
      (S.contragredientSkeleton.primitiveMultiplicityInput D.opposite) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact PrimitiveDirectedBoundaryData.ofCoordinateEstimate
    S.contragredientSkeleton
    (S.contragredientSkeleton.primitiveMultiplicityInput D.opposite)
    (S.contragredientSkeleton_hasAcyclicNonzeroNonisomorphisms H)
    (E.contragredient S D)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
