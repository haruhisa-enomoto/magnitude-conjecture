import MagnitudeConjecture.Algebra.StringExtension

/-!
# One-letter extension maps for string modules

The coordinate maps for one-letter string extensions already form morphisms
of quiver representations.  This file transports them through the free
linear path realization and the monomial relation quotient, producing actual
morphisms of right modules over the bound-quiver category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- In the opposite-module realization, a negative one-letter inclusion has
the reversed natural-transformation direction. -/
def appendFreeRightModuleAuxInclusionNegative
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath)) :
    (append R C (negativeArrow a) h).freeRightModuleAux ⟶
      C.freeRightModuleAux :=
  LinearPathCategory.liftNatTrans
    (fun x ↦ Opposite.op
      (ModuleCat.of k ((append R C (negativeArrow a) h).Space x)))
    (fun x ↦ Opposite.op (ModuleCat.of k (C.Space x)))
    (fun b ↦ (ModuleCat.ofHom
      ((append R C (negativeArrow a) h).arrowLinearMap b)).op)
    (fun b ↦ (ModuleCat.ofHom (C.arrowLinearMap b)).op)
    (fun x ↦ (ModuleCat.ofHom
      (appendSpaceInclusion C (negativeArrow a) h (x := x))).op)
    (fun {x y} b ↦ by
      rw [← op_comp, ← op_comp]
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change (append R C (negativeArrow a) h).arrowLinearMap b
          (appendSpaceInclusion C (negativeArrow a) h v) =
        appendSpaceInclusion C (negativeArrow a) h
          (C.arrowLinearMap b v)
      exact (appendSpaceInclusion_arrowLinearMap_negative C a h b v).symm)

/-- In the opposite-module realization, a positive one-letter projection has
the reversed natural-transformation direction. -/
def appendFreeRightModuleAuxProjectionPositive
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath)) :
    C.freeRightModuleAux ⟶
      (append R C (positiveArrow a) h).freeRightModuleAux :=
  LinearPathCategory.liftNatTrans
    (fun x ↦ Opposite.op (ModuleCat.of k (C.Space x)))
    (fun x ↦ Opposite.op
      (ModuleCat.of k ((append R C (positiveArrow a) h).Space x)))
    (fun b ↦ (ModuleCat.ofHom (C.arrowLinearMap b)).op)
    (fun b ↦ (ModuleCat.ofHom
      ((append R C (positiveArrow a) h).arrowLinearMap b)).op)
    (fun x ↦ (ModuleCat.ofHom
      (appendSpaceProjection C (positiveArrow a) h (x := x))).op)
    (fun {x y} b ↦ by
      rw [← op_comp, ← op_comp]
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change C.arrowLinearMap b
          (appendSpaceProjection C (positiveArrow a) h v) =
        appendSpaceProjection C (positiveArrow a) h
          ((append R C (positiveArrow a) h).arrowLinearMap b v)
      exact (appendSpaceProjection_arrowLinearMap_positive C a h b v).symm)

/-- The negative-extension transformation descends through the monomial
relation quotient. -/
def appendQuotientRightModuleAuxInclusionNegative
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (hmono : IsMonomial R) :
    (append R C (negativeArrow a) h).quotientRightModuleAux hmono ⟶
      C.quotientRightModuleAux hmono :=
  HomIdeal.quotientLiftNatTrans
    (k := k)
    (I := LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (F := (append R C (negativeArrow a) h).freeRightModuleAux)
    ((append R C (negativeArrow a) h).relationIdeal_isKilledBy hmono)
    (C.relationIdeal_isKilledBy hmono)
    (appendFreeRightModuleAuxInclusionNegative C a h)

/-- The positive-extension transformation descends through the monomial
relation quotient. -/
def appendQuotientRightModuleAuxProjectionPositive
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (hmono : IsMonomial R) :
    C.quotientRightModuleAux hmono ⟶
      (append R C (positiveArrow a) h).quotientRightModuleAux hmono :=
  HomIdeal.quotientLiftNatTrans
    (k := k)
    (I := LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (F := C.freeRightModuleAux)
    (C.relationIdeal_isKilledBy hmono)
    ((append R C (positiveArrow a) h).relationIdeal_isKilledBy hmono)
    (appendFreeRightModuleAuxProjectionPositive C a h)

/-- The canonical negative-extension inclusion as a morphism of right modules
over the bound-quiver category. -/
def appendRightModuleInclusionNegative
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (hmono : IsMonomial R) :
    C.rightModule hmono ⟶
      (append R C (negativeArrow a) h).rightModule hmono where
  app X :=
    ((appendQuotientRightModuleAuxInclusionNegative C a h hmono).app
      X.unop).unop
  naturality {X Y} f := by
    apply Quiver.Hom.op_inj
    exact
      ((appendQuotientRightModuleAuxInclusionNegative C a h hmono).naturality
        f.unop).symm

/-- The canonical positive-extension projection as a morphism of right
modules over the bound-quiver category. -/
def appendRightModuleProjectionPositive
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (hmono : IsMonomial R) :
    (append R C (positiveArrow a) h).rightModule hmono ⟶
      C.rightModule hmono where
  app X :=
    ((appendQuotientRightModuleAuxProjectionPositive C a h hmono).app
      X.unop).unop
  naturality {X Y} f := by
    apply Quiver.Hom.op_inj
    exact
      ((appendQuotientRightModuleAuxProjectionPositive C a h hmono).naturality
        f.unop).symm

@[simp]
theorem appendRightModuleInclusionNegative_app_obj
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (hmono : IsMonomial R) (x : Q) :
    (appendRightModuleInclusionNegative C a h hmono).app
        (Opposite.op (obj R x)) =
      ModuleCat.ofHom
        (appendSpaceInclusion C (negativeArrow a) h (x := x)) :=
  rfl

@[simp]
theorem appendRightModuleProjectionPositive_app_obj
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (hmono : IsMonomial R) (x : Q) :
    (appendRightModuleProjectionPositive C a h hmono).app
        (Opposite.op (obj R x)) =
      ModuleCat.ofHom
        (appendSpaceProjection C (positiveArrow a) h (x := x)) :=
  rfl

/-- The negative one-letter map is a submodule inclusion. -/
instance appendRightModuleInclusionNegative_mono
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (hmono : IsMonomial R) :
    Mono (appendRightModuleInclusionNegative C a h hmono) := by
  haveI hmonoApp (X : (Category R)ᵒᵖ) :
      Mono ((appendRightModuleInclusionNegative C a h hmono).app X) := by
    rw [ModuleCat.mono_iff_injective]
    exact appendSpaceInclusion_injective C (negativeArrow a) h
  exact NatTrans.mono_of_mono_app _

/-- The positive one-letter map is a quotient projection. -/
instance appendRightModuleProjectionPositive_epi
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (hmono : IsMonomial R) :
    Epi (appendRightModuleProjectionPositive C a h hmono) := by
  haveI hepiApp (X : (Category R)ᵒᵖ) :
      Epi ((appendRightModuleProjectionPositive C a h hmono).app X) := by
    rw [ModuleCat.epi_iff_surjective]
    exact appendSpaceProjection_surjective C (positiveArrow a) h
  exact NatTrans.epi_of_epi_app _

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
