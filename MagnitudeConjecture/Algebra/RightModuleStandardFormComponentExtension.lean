import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentAlgebra
import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleExtension
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Extension by zero from a standard-form component

The opposite projective category of one augmented-walk component is identified
with the object-deletion quotient obtained by removing every other component
from the global opposite projective category.  Cross-component Hom vanishing
makes the deletion ideal zero on surviving objects.  Existing object-deletion
machinery therefore gives a fully faithful additive extension by zero from
component modules to global projective modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance componentExtensionQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance componentExtensionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- Projective vertices outside a fixed walk component. -/
def standardFormProjectiveComplement
    (c : S.StandardFormWalkComponent) :
    Set S.StandardFormProjectiveMeshCategory :=
  {p | S.standardFormWalkComponentClass p.1 ≠ c}

/-- The ambient projective full subcategory surviving deletion of all other
walk components. -/
abbrev StandardFormComponentSurvivingProjectiveCategory
    (c : S.StandardFormWalkComponent) :=
  ObjectDeletion.SurvivingCategory S.StandardFormProjectiveMeshCategory
    (S.standardFormProjectiveComplement c)

/-- A component projective category identifies with the surviving full
subcategory of the global projective category. -/
def standardFormComponentProjectiveToSurviving
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentProjectiveMeshCategory (k := k) c ⥤
      S.StandardFormComponentSurvivingProjectiveCategory c where
  obj p := ⟨⟨p.1.1, p.2⟩, by
    change ¬S.standardFormWalkComponentClass p.1.1 ≠ c
    exact fun h ↦ h p.1.2⟩
  map f := ObjectProperty.homMk (InducedCategory.homMk f.hom.hom)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance standardFormComponentProjectiveToSurviving_full
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToSurviving (k := k) c).Full where
  map_surjective f :=
    ⟨InducedCategory.homMk (InducedCategory.homMk f.hom.hom), by ext; rfl⟩

instance standardFormComponentProjectiveToSurviving_faithful
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToSurviving (k := k) c).Faithful where
  map_injective := by
    intro X Y f g h
    apply InducedCategory.hom_ext
    apply InducedCategory.hom_ext
    exact congrArg (fun q ↦ q.hom.hom) h

instance standardFormComponentProjectiveToSurviving_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToSurviving (k := k) c).Additive := by
  exact { map_add := by intros; ext; rfl }

instance standardFormComponentProjectiveToSurviving_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToSurviving (k := k) c).Linear k := by
  exact { map_smul := by intros; ext; rfl }

instance standardFormComponentProjectiveToSurviving_essSurj
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToSurviving (k := k) c).EssSurj where
  mem_essImage Y := by
    have hY : S.standardFormWalkComponentClass Y.obj.1 = c := by
      have hnot := Y.property
      change ¬S.standardFormWalkComponentClass Y.obj.1 ≠ c at hnot
      exact not_ne_iff.mp hnot
    let X : S.StandardFormComponentProjectiveMeshCategory (k := k) c :=
      ⟨⟨Y.obj.1, hY⟩, Y.obj.2⟩
    refine ⟨X, ⟨eqToIso ?_⟩⟩
    apply ObjectProperty.FullSubcategory.ext
    apply Subtype.ext
    rfl

instance standardFormComponentProjectiveToSurviving_isEquivalence
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToSurviving (k := k) c).IsEquivalence where

/-- Equivalence between the intrinsic component projective category and the
same objects as a global surviving full subcategory. -/
def standardFormComponentProjectiveSurvivingEquivalence
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentProjectiveMeshCategory (k := k) c ≌
      S.StandardFormComponentSurvivingProjectiveCategory c :=
  (S.standardFormComponentProjectiveToSurviving (k := k) c).asEquivalence

instance standardFormComponentProjectiveSurvivingEquivalence_functor_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveSurvivingEquivalence
      (k := k) c).functor.Additive := by
  change (S.standardFormComponentProjectiveToSurviving (k := k) c).Additive
  infer_instance

instance standardFormComponentProjectiveSurvivingEquivalence_functor_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveSurvivingEquivalence
      (k := k) c).functor.Linear k := by
  change (S.standardFormComponentProjectiveToSurviving (k := k) c).Linear k
  infer_instance

/-- Opposite projective vertices outside a fixed walk component. -/
def standardFormOppositeProjectiveComplement
    (c : S.StandardFormWalkComponent) :
    Set S.StandardFormProjectiveMeshCategoryᵒᵖ :=
  {p | S.standardFormWalkComponentClass p.unop.1 ≠ c}

/-- The object property selecting one projective walk component. -/
abbrev standardFormComponentProjectiveSurvivingProperty
    (c : S.StandardFormWalkComponent) :
    ObjectProperty S.StandardFormProjectiveMeshCategory :=
  ObjectDeletion.IsSurviving S.StandardFormProjectiveMeshCategory
    (S.standardFormProjectiveComplement c)

/-- The surviving component inside the opposite global projective category. -/
abbrev StandardFormComponentSurvivingOppositeProjectiveCategory
    (c : S.StandardFormWalkComponent) :=
  ObjectDeletion.SurvivingCategory S.StandardFormProjectiveMeshCategoryᵒᵖ
    (S.standardFormOppositeProjectiveComplement c)

instance standardFormComponentProjectiveSurvivingEquivalence_op_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveSurvivingEquivalence
      (k := k) c).functor.op.Linear k := by
  constructor
  intro X Y f r
  apply Quiver.Hom.unop_inj
  change (S.standardFormComponentProjectiveSurvivingEquivalence
    (k := k) c).functor.map (r • f.unop) =
      r • (S.standardFormComponentProjectiveSurvivingEquivalence
        (k := k) c).functor.map f.unop
  exact (S.standardFormComponentProjectiveSurvivingEquivalence
    (k := k) c).functor.map_smul r f.unop

instance standardFormComponentProjectiveSurvivingOpEquivalence_inverse_additive
    (c : S.StandardFormWalkComponent) :
    ((S.standardFormComponentProjectiveSurvivingProperty c).opEquivalence
      ).inverse.Additive := by
  exact { map_add := by intros; rfl }

instance standardFormComponentProjectiveSurvivingOpEquivalence_inverse_linear
    (c : S.StandardFormWalkComponent) :
    ((S.standardFormComponentProjectiveSurvivingProperty c).opEquivalence
      ).inverse.Linear k := by
  exact { map_smul := by intros; rfl }

/-- Taking opposites in the intrinsic component category agrees with taking
the surviving full subcategory inside the opposite global category. -/
def standardFormComponentOppositeProjectiveSurvivingEquivalence
    (c : S.StandardFormWalkComponent) :
    (S.StandardFormComponentProjectiveMeshCategory (k := k) c)ᵒᵖ ≌
      S.StandardFormComponentSurvivingOppositeProjectiveCategory c := by
  exact (S.standardFormComponentProjectiveSurvivingEquivalence
    (k := k) c).op |>.trans
      ((S.standardFormComponentProjectiveSurvivingProperty c).opEquivalence).symm

instance standardFormComponentOppositeProjectiveSurvivingEquivalence_functor_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveSurvivingEquivalence
      (k := k) c).functor.Additive := by
  exact { map_add := by intros; ext; rfl }

instance standardFormComponentOppositeProjectiveSurvivingEquivalence_functor_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveSurvivingEquivalence
      (k := k) c).functor.Linear k := by
  exact { map_smul := by intros; ext; rfl }

/-- At component objects, the ideal generated by all other opposite
projective components is zero. -/
private theorem standardFormOppositeProjectiveComplement_ideal_hom_eq_zero
    (c : S.StandardFormWalkComponent)
    {X Y : S.StandardFormComponentSurvivingOppositeProjectiveCategory c}
    (f : X.obj ⟶ Y.obj)
    (hf : f ∈ (ObjectDeletion.ideal (k := k)
      S.StandardFormProjectiveMeshCategoryᵒᵖ
      (S.standardFormOppositeProjectiveComplement c)).hom X.obj Y.obj) :
    f = 0 := by
  change f ∈ HomIdeal.generatedHomSubmodule k
    (ObjectDeletion.endomorphismRelations
      S.StandardFormProjectiveMeshCategoryᵒᵖ
      (S.standardFormOppositeProjectiveComplement c)) X.obj Y.obj at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨U, V, r, hr, a, b, rfl⟩
      rcases hr with ⟨rfl, hU⟩
      have hXc : S.standardFormWalkComponentClass X.obj.unop.1 = c := by
        have hnot := X.property
        change ¬S.standardFormWalkComponentClass X.obj.unop.1 ≠ c at hnot
        exact not_ne_iff.mp hnot
      have hUc : S.standardFormWalkComponentClass U.unop.1 ≠ c := by
        exact hU
      have hclass : S.standardFormWalkComponentClass U.unop.1 ≠
          S.standardFormWalkComponentClass X.obj.unop.1 := by
        intro h
        exact hUc (h.trans hXc)
      have haUnop : a.unop = 0 := by
        apply InducedCategory.hom_ext
        exact S.standardForm_meshHom_eq_zero_of_walkComponentClass_ne
          hclass a.unop.hom
      have ha : a = 0 := by
        apply Quiver.Hom.unop_inj
        simpa using haUnop
      simp [ha]
  | zero => rfl
  | add f g _ _ hf hg => simp [hf, hg]
  | smul r f _ hf => simp [hf]

/-- Quotient deletion of all other opposite projective components. -/
abbrev StandardFormComponentOppositeProjectiveDeletionCategory
    (c : S.StandardFormWalkComponent) :=
  ObjectDeletion.DeletionCategory (k := k)
    S.StandardFormProjectiveMeshCategoryᵒᵖ
    (S.standardFormOppositeProjectiveComplement c)

noncomputable instance standardFormComponentOppositeProjectiveDeletionCategoryFinite
    (c : S.StandardFormWalkComponent) :
    Finite (S.StandardFormComponentOppositeProjectiveDeletionCategory
      (k := k) c) := by
  apply Finite.of_injective
    (f := fun X : S.StandardFormComponentOppositeProjectiveDeletionCategory
      (k := k) c ↦ X.obj.as)
  intro X Y h
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Quotient.ext
  exact h

/-- The surviving-to-deletion functor for one opposite projective component. -/
abbrev standardFormComponentOppositeProjectiveDeletionFunctor
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentSurvivingOppositeProjectiveCategory c ⥤
      S.StandardFormComponentOppositeProjectiveDeletionCategory (k := k) c :=
  ObjectDeletion.functor (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
    (S.standardFormOppositeProjectiveComplement c)

instance standardFormComponentOppositeProjectiveDeletionFunctor_faithful
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveDeletionFunctor
      (k := k) c).Faithful where
  map_injective := by
    intro X Y f g hfg
    apply sub_eq_zero.mp
    apply ObjectProperty.hom_ext
    apply S.standardFormOppositeProjectiveComplement_ideal_hom_eq_zero
      (k := k) c
    apply (ObjectDeletion.functor_map_eq_zero_iff
      (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
      (S.standardFormOppositeProjectiveComplement c) (f - g)).1
    rw [Functor.map_sub, hfg, sub_self]

instance standardFormComponentOppositeProjectiveDeletionFunctor_essSurj
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveDeletionFunctor
      (k := k) c).EssSurj where
  mem_essImage Y := by
    let X : S.StandardFormComponentSurvivingOppositeProjectiveCategory c :=
      ⟨Y.obj.as, Y.property⟩
    refine ⟨X, ⟨eqToIso ?_⟩⟩
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    rfl

instance standardFormComponentOppositeProjectiveDeletionFunctor_isEquivalence
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveDeletionFunctor
      (k := k) c).IsEquivalence where

/-- The surviving component and its object-deletion quotient are equivalent
because every factorization through another component is zero. -/
def standardFormComponentOppositeProjectiveDeletionEquivalence
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentSurvivingOppositeProjectiveCategory c ≌
      S.StandardFormComponentOppositeProjectiveDeletionCategory (k := k) c :=
  (S.standardFormComponentOppositeProjectiveDeletionFunctor
    (k := k) c).asEquivalence

instance standardFormComponentOppositeProjectiveDeletionEquivalence_functor_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveDeletionEquivalence
      (k := k) c).functor.Additive := by
  change (S.standardFormComponentOppositeProjectiveDeletionFunctor
    (k := k) c).Additive
  infer_instance

instance standardFormComponentOppositeProjectiveDeletionEquivalence_functor_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveDeletionEquivalence
      (k := k) c).functor.Linear k := by
  change (S.standardFormComponentOppositeProjectiveDeletionFunctor
    (k := k) c).Linear k
  infer_instance

/-- The intrinsic opposite component projective category is equivalent to
the deletion of all other objects from the global opposite projective
category. -/
def standardFormComponentOppositeProjectiveToDeletionEquivalence
    (c : S.StandardFormWalkComponent) :
    (S.StandardFormComponentProjectiveMeshCategory (k := k) c)ᵒᵖ ≌
      S.StandardFormComponentOppositeProjectiveDeletionCategory (k := k) c :=
  (S.standardFormComponentOppositeProjectiveSurvivingEquivalence
    (k := k) c).trans
      (S.standardFormComponentOppositeProjectiveDeletionEquivalence
        (k := k) c)

instance standardFormComponentOppositeProjectiveToDeletionEquivalence_functor_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveToDeletionEquivalence
      (k := k) c).functor.Additive := by
  let F := (S.standardFormComponentOppositeProjectiveSurvivingEquivalence
    (k := k) c).functor
  let G := (S.standardFormComponentOppositeProjectiveDeletionEquivalence
    (k := k) c).functor
  change (F ⋙ G).Additive
  infer_instance

instance standardFormComponentOppositeProjectiveToDeletionEquivalence_functor_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentOppositeProjectiveToDeletionEquivalence
      (k := k) c).functor.Linear k := by
  let F := (S.standardFormComponentOppositeProjectiveSurvivingEquivalence
    (k := k) c).functor
  let G := (S.standardFormComponentOppositeProjectiveDeletionEquivalence
    (k := k) c).functor
  change (F ⋙ G).Linear k
  infer_instance

/-- Transport between finite modules on the deletion model and finite
modules on the intrinsic opposite component category. -/
def standardFormComponentDeletionModuleEquivalence
    (c : S.StandardFormWalkComponent) :
    CoveringHom.FiniteDimensionalModuleCategory
        (C := S.StandardFormComponentOppositeProjectiveDeletionCategory
          (k := k) c) k ≌
      CoveringHom.FiniteDimensionalModuleCategory
        (C := (S.StandardFormComponentProjectiveMeshCategory
          (k := k) c)ᵒᵖ) k :=
  CoveringHom.finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k)
    (S.standardFormComponentOppositeProjectiveToDeletionEquivalence
      (k := k) c)

instance standardFormComponentDeletionModuleEquivalence_functor_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentDeletionModuleEquivalence
      (k := k) c).functor.Additive := by
  change (CoveringHom.finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k)
    (S.standardFormComponentOppositeProjectiveToDeletionEquivalence
      (k := k) c)).functor.Additive
  infer_instance

instance standardFormComponentDeletionModuleEquivalence_inverse_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentDeletionModuleEquivalence
      (k := k) c).inverse.Additive :=
  (S.standardFormComponentDeletionModuleEquivalence
    (k := k) c).inverse_additive

/-- Extend a finite module on one component by zero to the global opposite
projective category. -/
def standardFormComponentModuleExtensionByZero
    (c : S.StandardFormWalkComponent) :
    CoveringHom.FiniteDimensionalModuleCategory
        (C := (S.StandardFormComponentProjectiveMeshCategory
          (k := k) c)ᵒᵖ) k ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k :=
  (S.standardFormComponentDeletionModuleEquivalence (k := k) c).inverse ⋙
    ObjectDeletion.finiteDimensionalModuleExtensionByZero
      (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
      (S.standardFormOppositeProjectiveComplement c)

instance standardFormComponentModuleExtensionByZero_full
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentModuleExtensionByZero (k := k) c).Full := by
  dsimp only [standardFormComponentModuleExtensionByZero]
  infer_instance

instance standardFormComponentModuleExtensionByZero_faithful
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentModuleExtensionByZero (k := k) c).Faithful := by
  dsimp only [standardFormComponentModuleExtensionByZero]
  infer_instance

instance standardFormComponentModuleExtensionByZero_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentModuleExtensionByZero (k := k) c).Additive := by
  dsimp only [standardFormComponentModuleExtensionByZero]
  infer_instance

/-- Extension by zero from a component preserves indecomposability. -/
theorem standardFormComponentModuleExtensionByZero_indec
    (c : S.StandardFormWalkComponent)
    (M : CoveringHom.FiniteDimensionalModuleCategory
      (C := (S.StandardFormComponentProjectiveMeshCategory
        (k := k) c)ᵒᵖ) k)
    (hM : Indecomposable M) :
    Indecomposable
      ((S.standardFormComponentModuleExtensionByZero (k := k) c).obj M) := by
  let E := S.standardFormComponentDeletionModuleEquivalence (k := k) c
  let N := E.inverse.obj M
  have hN : Indecomposable N :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse M).2 hM
  exact ObjectDeletion.finiteDimensionalModuleExtensionByZero_indec
    (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
    (S.standardFormOppositeProjectiveComplement c) N hN

/-- The extension of a component module is zero at every projective vertex
outside that component. -/
theorem standardFormComponentModuleExtensionByZero_obj_isZero_of_class_ne
    (c : S.StandardFormWalkComponent)
    (M : CoveringHom.FiniteDimensionalModuleCategory
      (C := (S.StandardFormComponentProjectiveMeshCategory
        (k := k) c)ᵒᵖ) k)
    (P : S.StandardFormProjectiveMeshCategoryᵒᵖ)
    (hP : S.standardFormWalkComponentClass P.unop.1 ≠ c) :
    IsZero (((S.standardFormComponentModuleExtensionByZero
      (k := k) c).obj M).obj.obj.obj P) := by
  let E := S.standardFormComponentDeletionModuleEquivalence (k := k) c
  let N := E.inverse.obj M
  change IsZero
    ((ObjectDeletion.moduleExtensionByZero
      (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
      (S.standardFormOppositeProjectiveComplement c) N.obj.obj).obj P)
  exact ObjectDeletion.moduleExtensionByZero_obj_isZero_of_mem
    (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
    (S.standardFormOppositeProjectiveComplement c) N.obj.obj hP

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
