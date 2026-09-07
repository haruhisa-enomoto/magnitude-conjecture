import MagnitudeConjecture.CategoryTheory.AdmissibleModuleCategory
import MagnitudeConjecture.CategoryTheory.ObjectDeletionQuotient
import Mathlib.CategoryTheory.Skeletal

/-!
# Convex full subcategories and object deletion

If no morphism between surviving objects factors nontrivially through a
deleted object, the deletion ideal vanishes on surviving Hom spaces.  The
canonical full functor from the surviving full subcategory to the deletion
quotient is then an equivalence.  Convexity for nonzero nonisomorphisms gives
this factorization condition in a skeletal category.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.ObjectDeletion

universe u v w

variable {k : Type w} [Ring k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- The literal full subcategory on a set of ambient objects. -/
abbrev FullSubcategoryOn (U : Set C) :=
  ObjectProperty.FullSubcategory (fun X : C ↦ X ∈ U)

/-- The identity-on-underlying-objects functor from the literal full
subcategory on `U` to the surviving subcategory for deletion by `Uᶜ`. -/
def fullSubcategoryOnToSurvivingComplFunctor (U : Set C) :
    FullSubcategoryOn C U ⥤ SurvivingCategory C Uᶜ where
  obj X := ⟨X.obj, by simpa [IsSurviving] using X.property⟩
  map f := ObjectProperty.homMk f.hom

instance fullSubcategoryOnToSurvivingComplFunctor_full (U : Set C) :
    (fullSubcategoryOnToSurvivingComplFunctor C U).Full where
  map_surjective f := ⟨ObjectProperty.homMk f.hom, by
    apply ObjectProperty.hom_ext
    rfl⟩

instance fullSubcategoryOnToSurvivingComplFunctor_faithful (U : Set C) :
    (fullSubcategoryOnToSurvivingComplFunctor C U).Faithful where
  map_injective {X Y} f g h := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun q ↦ q.hom) h

instance fullSubcategoryOnToSurvivingComplFunctor_essSurj (U : Set C) :
    (fullSubcategoryOnToSurvivingComplFunctor C U).EssSurj where
  mem_essImage Y := by
    let X : FullSubcategoryOn C U :=
      ⟨Y.obj, by simpa [IsSurviving] using Y.property⟩
    exact ⟨X, ⟨ObjectProperty.isoMk _ (Iso.refl _)⟩⟩

/-- The literal full subcategory on `U` is the surviving subcategory for
deletion by the complement of `U`. -/
noncomputable def fullSubcategoryOnSurvivingComplEquivalence (U : Set C) :
    FullSubcategoryOn C U ≌ SurvivingCategory C Uᶜ := by
  letI : (fullSubcategoryOnToSurvivingComplFunctor C U).IsEquivalence := {}
  exact (fullSubcategoryOnToSurvivingComplFunctor C U).asEquivalence

noncomputable instance fullSubcategoryOnSurvivingComplEquivalence_functor_additive
    (U : Set C) :
    (fullSubcategoryOnSurvivingComplEquivalence C U).functor.Additive := by
  change (fullSubcategoryOnToSurvivingComplFunctor C U).Additive
  constructor
  intro X Y f g
  apply ObjectProperty.hom_ext
  rfl

noncomputable instance fullSubcategoryOnSurvivingComplEquivalence_functor_linear
    (U : Set C) :
    (fullSubcategoryOnSurvivingComplEquivalence C U).functor.Linear k := by
  change (fullSubcategoryOnToSurvivingComplFunctor C U).Linear k
  constructor
  intro X Y f r
  apply ObjectProperty.hom_ext
  rfl

/-- No morphism between surviving objects factors nontrivially through one
deleted object. -/
def NoDeletedFactorization (S : Set C) : Prop :=
  ∀ {X Y Z : C}, X ∉ S → Y ∉ S → Z ∈ S →
    ∀ (a : X ⟶ Z) (b : Z ⟶ Y), a ≫ b = 0

/-- Under the no-factorization condition, every member of the deletion ideal
between surviving objects is zero. -/
theorem eq_zero_of_mem_ideal_of_noDeletedFactorization
    {S : Set C} (hS : NoDeletedFactorization C S)
    {X Y : C} (hX : X ∉ S) (hY : Y ∉ S)
    {f : X ⟶ Y} (hf : f ∈ (ideal (k := k) C S).hom X Y) :
    f = 0 := by
  change f ∈ HomIdeal.generatedHomSubmodule k
    (endomorphismRelations C S) X Y at hf
  induction hf using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨A, B, r, hr, a, b, rfl⟩
      rcases hr with ⟨hAB, hA⟩
      subst B
      have hzero := hS hX hY hA (a ≫ r) b
      simpa only [Category.assoc] using hzero
  | zero => rfl
  | add p q hp hq ihp ihq => simp [ihp, ihq]
  | smul c q hq ihq => simp [ihq]

/-- The surviving-to-deletion functor is faithful when deleted objects cannot
carry a nonzero factorization between survivors. -/
theorem functor_faithful_of_noDeletedFactorization
    (S : Set C) (hS : NoDeletedFactorization C S) :
    (functor (k := k) C S).Faithful where
  map_injective {X Y} f g hfg := by
    have hzero : (functor (k := k) C S).map (f - g) = 0 := by
      rw [(functor (k := k) C S).map_sub, hfg, sub_self]
    have hideal := (functor_map_eq_zero_iff (k := k) C S (f - g)).1 hzero
    apply ObjectProperty.hom_ext
    exact sub_eq_zero.mp
      (eq_zero_of_mem_ideal_of_noDeletedFactorization
        (k := k) C hS X.property Y.property hideal)

/-- Every deletion-quotient object is represented by the corresponding
surviving ambient object. -/
theorem functor_essSurj (S : Set C) :
    (functor (k := k) C S).EssSurj where
  mem_essImage Y := by
    refine ⟨⟨Y.obj.as, Y.property⟩, ⟨ObjectProperty.isoMk _ (eqToIso ?_)⟩⟩
    apply CategoryTheory.Quotient.ext
    rfl

/-- Under no deleted factorization, the retained full subcategory is
equivalent to the deletion quotient. -/
noncomputable def survivingDeletionEquivalence
    (S : Set C) (hS : NoDeletedFactorization C S) :
    SurvivingCategory C S ≌ DeletionCategory (k := k) C S := by
  letI : (functor (k := k) C S).Faithful :=
    functor_faithful_of_noDeletedFactorization (k := k) C S hS
  letI : (functor (k := k) C S).EssSurj := functor_essSurj (k := k) C S
  letI : (functor (k := k) C S).IsEquivalence := {}
  exact (functor (k := k) C S).asEquivalence

noncomputable instance survivingDeletionEquivalence_functor_additive
    (S : Set C) (hS : NoDeletedFactorization C S) :
    (survivingDeletionEquivalence (k := k) C S hS).functor.Additive := by
  change (functor (k := k) C S).Additive
  infer_instance

noncomputable instance survivingDeletionEquivalence_functor_linear
    (S : Set C) (hS : NoDeletedFactorization C S) :
    (survivingDeletionEquivalence (k := k) C S hS).functor.Linear k := by
  change (functor (k := k) C S).Linear k
  infer_instance

/-- In a skeletal category, convexity of the retained object set forbids a
nonzero factorization between retained objects through an object outside the
set. -/
theorem noDeletedFactorization_compl_of_isConvexObjectSet
    (hC : Skeletal C) (U : Set C)
    (hU : CoveringHom.IsConvexObjectSet
      (C := C) U) :
    NoDeletedFactorization C Uᶜ := by
  intro X Y Z hX hY hZ a b
  rw [Set.mem_compl_iff, not_not] at hX hY
  rw [Set.mem_compl_iff] at hZ
  by_contra hab
  have ha : a ≠ 0 := by
    intro ha
    apply hab
    simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    apply hab
    simp [hb]
  have haNotIso : ¬ IsIso a := by
    intro haIso
    letI : IsIso a := haIso
    apply hZ
    exact (hC ⟨asIso a⟩) ▸ hX
  have hbNotIso : ¬ IsIso b := by
    intro hbIso
    letI : IsIso b := hbIso
    apply hZ
    exact (hC ⟨asIso b⟩).symm ▸ hY
  apply hZ
  exact hU hX hY
    (Relation.ReflTransGen.single ⟨a, ha, haNotIso⟩)
    (Relation.ReflTransGen.single ⟨b, hb, hbNotIso⟩)

/-- A convex retained full subcategory of a skeletal linear category is
canonically equivalent to deletion by its complement. -/
noncomputable def convexSurvivingDeletionEquivalence
    (hC : Skeletal C) (U : Set C)
    (hU : CoveringHom.IsConvexObjectSet (C := C) U) :
    SurvivingCategory C Uᶜ ≌ DeletionCategory (k := k) C Uᶜ :=
  survivingDeletionEquivalence (k := k) C Uᶜ
    (noDeletedFactorization_compl_of_isConvexObjectSet C hC U hU)

noncomputable instance convexSurvivingDeletionEquivalence_functor_additive
    (hC : Skeletal C) (U : Set C)
    (hU : CoveringHom.IsConvexObjectSet (C := C) U) :
    (convexSurvivingDeletionEquivalence
      (k := k) C hC U hU).functor.Additive := by
  change (survivingDeletionEquivalence (k := k) C Uᶜ
    (noDeletedFactorization_compl_of_isConvexObjectSet C hC U hU)).functor.Additive
  infer_instance

noncomputable instance convexSurvivingDeletionEquivalence_functor_linear
    (hC : Skeletal C) (U : Set C)
    (hU : CoveringHom.IsConvexObjectSet (C := C) U) :
    (convexSurvivingDeletionEquivalence
      (k := k) C hC U hU).functor.Linear k := by
  change (survivingDeletionEquivalence (k := k) C Uᶜ
    (noDeletedFactorization_compl_of_isConvexObjectSet C hC U hU)).functor.Linear k
  infer_instance

/-- The manuscript's finite convex full subcategory is linearly equivalent
to the literal deletion quotient by the complementary objects. -/
noncomputable def convexFullSubcategoryDeletionEquivalence
    (hC : Skeletal C) (U : Set C)
    (hU : CoveringHom.IsConvexObjectSet (C := C) U) :
    FullSubcategoryOn C U ≌ DeletionCategory (k := k) C Uᶜ :=
  (fullSubcategoryOnSurvivingComplEquivalence C U).trans
    (convexSurvivingDeletionEquivalence (k := k) C hC U hU)

noncomputable instance convexFullSubcategoryDeletionEquivalence_functor_additive
    (hC : Skeletal C) (U : Set C)
    (hU : CoveringHom.IsConvexObjectSet (C := C) U) :
    (convexFullSubcategoryDeletionEquivalence
      (k := k) C hC U hU).functor.Additive := by
  change ((fullSubcategoryOnSurvivingComplEquivalence C U).functor ⋙
    (convexSurvivingDeletionEquivalence (k := k) C hC U hU).functor).Additive
  infer_instance

noncomputable instance convexFullSubcategoryDeletionEquivalence_functor_linear
    (hC : Skeletal C) (U : Set C)
    (hU : CoveringHom.IsConvexObjectSet (C := C) U) :
    (convexFullSubcategoryDeletionEquivalence
      (k := k) C hC U hU).functor.Linear k := by
  change ((fullSubcategoryOnSurvivingComplEquivalence C U).functor ⋙
    (convexSurvivingDeletionEquivalence (k := k) C hC U hU).functor).Linear k
  infer_instance

end MagnitudeConjecture.ObjectDeletion
