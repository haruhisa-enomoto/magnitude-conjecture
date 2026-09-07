import MagnitudeConjecture.CategoryTheory.LinearCovering
import MagnitudeConjecture.LinearAlgebra.DirectSumFubini
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Restricting linear coverings to full subcategories

A linear covering restricts to the inverse image of any full subcategory of
its target.  Its fibres and all Hom summands are unchanged, up to the bundled
full-subcategory wrappers.
-/

set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace MagnitudeConjecture.LinearCovering

universe u v₁ v₂ w₁ w₂

variable {k : Type u} [Field k]
variable {C : Type v₁} [Category.{w₁} C] [Preadditive C]
variable {D : Type v₂} [Category.{w₂} D] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k]

/-- The inverse-image object property of a target property under a functor. -/
def pullbackProperty (Q : ObjectProperty D) : ObjectProperty C :=
  fun X ↦ Q (F.obj X)

/-- Restriction of a functor to the inverse image of a full subcategory. -/
@[reducible]
def fullSubcategoryRestriction (Q : ObjectProperty D) :
    (pullbackProperty F Q).FullSubcategory ⥤ Q.FullSubcategory where
  obj X := ⟨F.obj X.obj, X.property⟩
  map f := ObjectProperty.homMk (F.map f.hom)
  map_id X := by
    apply InducedCategory.hom_ext
    exact F.map_id X.obj
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact F.map_comp f.hom g.hom

instance fullSubcategoryRestriction_additive (Q : ObjectProperty D) :
    (fullSubcategoryRestriction F Q).Additive where
  map_add := by
    intro X Y f g
    apply InducedCategory.hom_ext
    change F.map (f.hom + g.hom) = F.map f.hom + F.map g.hom
    simp

instance fullSubcategoryRestriction_linear (Q : ObjectProperty D) :
    (fullSubcategoryRestriction F Q).Linear k where
  map_smul f r := by
    apply InducedCategory.hom_ext
    change F.map (r • f.hom) = r • F.map f.hom
    simp

/-- The underlying ambient morphism of a morphism in a full subcategory. -/
noncomputable def fullSubcategoryHomLinearEquiv
    {E : Type*} [Category E] [Preadditive E] [CategoryTheory.Linear k E]
    (P : ObjectProperty E) (X Y : P.FullSubcategory) :
    (X ⟶ Y) ≃ₗ[k] (X.obj ⟶ Y.obj) :=
  InducedCategory.homLinearEquiv

@[simp]
theorem fullSubcategoryHomLinearEquiv_apply
    {E : Type*} [Category E] [Preadditive E] [CategoryTheory.Linear k E]
    (P : ObjectProperty E) (X Y : P.FullSubcategory) (f : X ⟶ Y) :
    fullSubcategoryHomLinearEquiv (k := k) P X Y f = f.hom :=
  rfl

/-- Fibres of the restricted functor are the same as the original fibres. -/
noncomputable def fullSubcategoryRestrictionFiberEquiv
    (Q : ObjectProperty D) (Y : Q.FullSubcategory) :
    Fiber (fullSubcategoryRestriction F Q) Y ≃ Fiber F Y.obj where
  toFun Z := ⟨Z.1.obj, congrArg ObjectProperty.FullSubcategory.obj Z.2⟩
  invFun Z :=
    ⟨⟨Z.1, Eq.ndrec Y.property Z.2.symm⟩, by
      apply ObjectProperty.FullSubcategory.ext
      exact Z.2⟩
  left_inv Z := by
    apply Subtype.ext
    apply ObjectProperty.FullSubcategory.ext
    rfl
  right_inv Z := by
    apply Subtype.ext
    rfl

/-- Reindex a fixed-source direct sum from the restricted fibre to the
ambient fibre, removing the source and target full-subcategory wrappers. -/
noncomputable def fullSubcategoryTargetFiberHomLinearEquiv
    (Q : ObjectProperty D)
    (X : (pullbackProperty F Q).FullSubcategory)
    (Y : Q.FullSubcategory) :
    DirectSum (Fiber (fullSubcategoryRestriction F Q) Y)
        (fun Z ↦ X ⟶ Z.1) ≃ₗ[k]
      DirectSum (Fiber F Y.obj) (fun Z ↦ X.obj ⟶ Z.1) := by
  let e := fullSubcategoryRestrictionFiberEquiv F Q Y
  let M : Fiber F Y.obj → Type _ :=
    fun Z ↦ X.obj ⟶ Z.1
  let removeWrapper : ∀ Z, (X ⟶ (e.symm Z).1) ≃ₗ[k] M Z :=
    fun Z ↦ by
      let U := (e.symm Z).1
      let unwrap : (X ⟶ U) ≃ₗ[k] (X.obj ⟶ U.obj) :=
        InducedCategory.homLinearEquiv
      let hU : U.obj = Z.1 := by rfl
      exact unwrap.trans (LinearEquiv.cast (R := k)
        (M := fun V : C ↦ X.obj ⟶ V) hU)
  exact (DirectSum.lequivCongrLeft k e).trans
    (MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv removeWrapper)

omit [Preadditive D] [CategoryTheory.Linear k D]
  [F.Additive] [F.Linear k] in
@[simp]
theorem fullSubcategoryTargetFiberHomLinearEquiv_targetFiberLof
    (Q : ObjectProperty D)
    (X : (pullbackProperty F Q).FullSubcategory)
    (Y : Q.FullSubcategory)
    (Z : Fiber (fullSubcategoryRestriction F Q) Y)
    (f : X ⟶ Z.1) :
    fullSubcategoryTargetFiberHomLinearEquiv (k := k) F Q X Y
        (targetFiberLof (k := k) (fullSubcategoryRestriction F Q) X Y Z f) =
      targetFiberLof (k := k) F X.obj Y.obj
        (fullSubcategoryRestrictionFiberEquiv F Q Y Z)
        (InducedCategory.homLinearEquiv (R := k) f) := by
  classical
  let e := fullSubcategoryRestrictionFiberEquiv F Q Y
  let M : Fiber F Y.obj → Type _ := fun W ↦ X.obj ⟶ W.1
  let removeWrapper : ∀ W, (X ⟶ (e.symm W).1) ≃ₗ[k] M W :=
    fun W ↦ by
      let U := (e.symm W).1
      let unwrap : (X ⟶ U) ≃ₗ[k] (X.obj ⟶ U.obj) :=
        InducedCategory.homLinearEquiv
      let hU : U.obj = W.1 := by rfl
      exact unwrap.trans (LinearEquiv.cast (R := k)
        (M := fun V : C ↦ X.obj ⟶ V) hU)
  change fullSubcategoryTargetFiberHomLinearEquiv (k := k) F Q X Y
      (DirectSum.of (fun W ↦ X ⟶ W.1) Z f) =
    DirectSum.of M (e Z) (InducedCategory.homLinearEquiv (R := k) f)
  unfold fullSubcategoryTargetFiberHomLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  change MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv removeWrapper
      ((DirectSum.lequivCongrLeft k e)
        (DirectSum.of (fun W ↦ X ⟶ W.1) Z f)) =
    DirectSum.of M (e Z) f.hom
  let h : Z = e.symm (e Z) := (e.symm_apply_apply Z).symm
  let f' : X ⟶ (e.symm (e Z)).1 :=
    cast (congrArg (fun W ↦ X ⟶ W.1) h) f
  have hreindex := DirectSum.lequivCongrLeft_lof
    (M := fun W ↦ X ⟶ W.1) (e := e) (i := Z) (k := e Z)
    k h f f' rfl
  rw [← DirectSum.lof_eq_of k _ (fun W ↦ X ⟶ W.1) Z f,
    hreindex, DirectSum.lof_eq_of,
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv_of]
  apply congrArg (DirectSum.of M (e Z))
  dsimp only [removeWrapper, LinearEquiv.trans_apply,
    InducedCategory.homLinearEquiv_apply]
  cases h
  rfl

/-- Reindex a fixed-target direct sum from the restricted fibre to the
ambient fibre, removing the source and target full-subcategory wrappers. -/
noncomputable def fullSubcategorySourceFiberHomLinearEquiv
    (Q : ObjectProperty D)
    (X : Q.FullSubcategory)
    (Y : (pullbackProperty F Q).FullSubcategory) :
    DirectSum (Fiber (fullSubcategoryRestriction F Q) X)
        (fun Z ↦ Z.1 ⟶ Y) ≃ₗ[k]
      DirectSum (Fiber F X.obj) (fun Z ↦ Z.1 ⟶ Y.obj) := by
  let e := fullSubcategoryRestrictionFiberEquiv F Q X
  let M : Fiber F X.obj → Type _ :=
    fun Z ↦ Z.1 ⟶ Y.obj
  let removeWrapper : ∀ Z, ((e.symm Z).1 ⟶ Y) ≃ₗ[k] M Z :=
    fun Z ↦ by
      let U := (e.symm Z).1
      let unwrap : (U ⟶ Y) ≃ₗ[k] (U.obj ⟶ Y.obj) :=
        InducedCategory.homLinearEquiv
      let hU : U.obj = Z.1 := by rfl
      exact unwrap.trans (LinearEquiv.cast (R := k)
        (M := fun V : C ↦ V ⟶ Y.obj) hU)
  exact (DirectSum.lequivCongrLeft k e).trans
    (MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv removeWrapper)

omit [Preadditive D] [CategoryTheory.Linear k D]
  [F.Additive] [F.Linear k] in
@[simp]
theorem fullSubcategorySourceFiberHomLinearEquiv_sourceFiberLof
    (Q : ObjectProperty D)
    (X : Q.FullSubcategory)
    (Y : (pullbackProperty F Q).FullSubcategory)
    (Z : Fiber (fullSubcategoryRestriction F Q) X)
    (f : Z.1 ⟶ Y) :
    fullSubcategorySourceFiberHomLinearEquiv (k := k) F Q X Y
        (sourceFiberLof (k := k) (fullSubcategoryRestriction F Q) X Y Z f) =
      sourceFiberLof (k := k) F X.obj Y.obj
        (fullSubcategoryRestrictionFiberEquiv F Q X Z)
        (InducedCategory.homLinearEquiv (R := k) f) := by
  classical
  let e := fullSubcategoryRestrictionFiberEquiv F Q X
  let M : Fiber F X.obj → Type _ := fun W ↦ W.1 ⟶ Y.obj
  let removeWrapper : ∀ W, ((e.symm W).1 ⟶ Y) ≃ₗ[k] M W :=
    fun W ↦ by
      let U := (e.symm W).1
      let unwrap : (U ⟶ Y) ≃ₗ[k] (U.obj ⟶ Y.obj) :=
        InducedCategory.homLinearEquiv
      let hU : U.obj = W.1 := by rfl
      exact unwrap.trans (LinearEquiv.cast (R := k)
        (M := fun V : C ↦ V ⟶ Y.obj) hU)
  change fullSubcategorySourceFiberHomLinearEquiv (k := k) F Q X Y
      (DirectSum.of (fun W ↦ W.1 ⟶ Y) Z f) =
    DirectSum.of M (e Z) (InducedCategory.homLinearEquiv (R := k) f)
  unfold fullSubcategorySourceFiberHomLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  change MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv removeWrapper
      ((DirectSum.lequivCongrLeft k e)
        (DirectSum.of (fun W ↦ W.1 ⟶ Y) Z f)) =
    DirectSum.of M (e Z) (InducedCategory.homLinearEquiv (R := k) f)
  let h : Z = e.symm (e Z) := (e.symm_apply_apply Z).symm
  let f' : (e.symm (e Z)).1 ⟶ Y :=
    cast (congrArg (fun W ↦ W.1 ⟶ Y) h) f
  have hreindex := DirectSum.lequivCongrLeft_lof
    (M := fun W ↦ W.1 ⟶ Y) (e := e) (i := Z) (k := e Z)
    k h f f' rfl
  rw [← DirectSum.lof_eq_of k _ (fun W ↦ W.1 ⟶ Y) Z f,
    hreindex, DirectSum.lof_eq_of,
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv_of]
  apply congrArg (DirectSum.of M (e Z))
  dsimp only [removeWrapper, LinearEquiv.trans_apply,
    InducedCategory.homLinearEquiv_apply]
  cases h
  rfl

/-- The target-fibre map of the restricted functor is the ambient
target-fibre map after removing the full-subcategory wrappers. -/
theorem fullSubcategoryTargetFiberHomMap_commutes
    (Q : ObjectProperty D)
    (X : (pullbackProperty F Q).FullSubcategory)
    (Y : Q.FullSubcategory)
    (a : DirectSum (Fiber (fullSubcategoryRestriction F Q) Y)
      (fun Z ↦ X ⟶ Z.1)) :
    fullSubcategoryHomLinearEquiv (k := k) Q
      ((fullSubcategoryRestriction F Q).obj X) Y
        (targetFiberHomMap (k := k) (fullSubcategoryRestriction F Q) X Y a) =
      targetFiberHomMap (k := k) F X.obj Y.obj
        (fullSubcategoryTargetFiberHomLinearEquiv (k := k) F Q X Y a) := by
  classical
  induction a using DirectSum.induction_on with
  | zero => rfl
  | of Z f =>
      rw [← DirectSum.lof_eq_of k _ (fun W ↦ X ⟶ W.1) Z f]
      change fullSubcategoryHomLinearEquiv (k := k) Q
          ((fullSubcategoryRestriction F Q).obj X) Y
          (targetFiberHomMap (k := k) (fullSubcategoryRestriction F Q) X Y
            (targetFiberLof (k := k) (fullSubcategoryRestriction F Q)
              X Y Z f)) =
        targetFiberHomMap (k := k) F X.obj Y.obj
          (fullSubcategoryTargetFiberHomLinearEquiv (k := k) F Q X Y
            (targetFiberLof (k := k) (fullSubcategoryRestriction F Q)
              X Y Z f))
      rw [targetFiberHomMap_lof,
        fullSubcategoryTargetFiberHomLinearEquiv_targetFiberLof,
        targetFiberHomMap_lof]
      change
        (((fullSubcategoryRestriction F Q).map f ≫
          eqToHom Z.2).hom) =
        F.map f.hom ≫
          eqToHom (congrArg ObjectProperty.FullSubcategory.obj Z.2)
      rw [ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.eqToHom_hom]
      rfl
  | add a b ha hb =>
      simp only [map_add, ha, hb]

/-- The source-fibre map of the restricted functor is the ambient
source-fibre map after removing the full-subcategory wrappers. -/
theorem fullSubcategorySourceFiberHomMap_commutes
    (Q : ObjectProperty D)
    (X : Q.FullSubcategory)
    (Y : (pullbackProperty F Q).FullSubcategory)
    (a : DirectSum (Fiber (fullSubcategoryRestriction F Q) X)
      (fun Z ↦ Z.1 ⟶ Y)) :
    fullSubcategoryHomLinearEquiv (k := k) Q X
      ((fullSubcategoryRestriction F Q).obj Y)
        (sourceFiberHomMap (k := k) (fullSubcategoryRestriction F Q) X Y a) =
      sourceFiberHomMap (k := k) F X.obj Y.obj
        (fullSubcategorySourceFiberHomLinearEquiv (k := k) F Q X Y a) := by
  classical
  induction a using DirectSum.induction_on with
  | zero => rfl
  | of Z f =>
      rw [← DirectSum.lof_eq_of k _ (fun W ↦ W.1 ⟶ Y) Z f]
      change fullSubcategoryHomLinearEquiv (k := k) Q X
          ((fullSubcategoryRestriction F Q).obj Y)
          (sourceFiberHomMap (k := k) (fullSubcategoryRestriction F Q) X Y
            (sourceFiberLof (k := k) (fullSubcategoryRestriction F Q)
              X Y Z f)) =
        sourceFiberHomMap (k := k) F X.obj Y.obj
          (fullSubcategorySourceFiberHomLinearEquiv (k := k) F Q X Y
            (sourceFiberLof (k := k) (fullSubcategoryRestriction F Q)
              X Y Z f))
      rw [sourceFiberHomMap_lof,
        fullSubcategorySourceFiberHomLinearEquiv_sourceFiberLof,
        sourceFiberHomMap_lof]
      change
        ((eqToHom Z.2.symm ≫
          (fullSubcategoryRestriction F Q).map f).hom) =
        eqToHom
            (congrArg ObjectProperty.FullSubcategory.obj Z.2).symm ≫
          F.map f.hom
      rw [ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.eqToHom_hom]
      rfl
  | add a b ha hb =>
      simp only [map_add, ha, hb]

/-- A linear covering restricts to the inverse image of every full
subcategory of its target. -/
theorem fullSubcategoryRestriction_isCovering
    (hF : IsCovering (k := k) F) (Q : ObjectProperty D) :
    IsCovering (k := k) (fullSubcategoryRestriction F Q) where
  target_bijective X Y := by
    let eDom := fullSubcategoryTargetFiberHomLinearEquiv
      (k := k) F Q X Y
    let eCod := fullSubcategoryHomLinearEquiv (k := k) Q
      ((fullSubcategoryRestriction F Q).obj X) Y
    let hAmbient := hF.target_bijective X.obj Y.obj
    constructor
    · intro a b hab
      apply eDom.injective
      apply hAmbient.1
      rw [← fullSubcategoryTargetFiberHomMap_commutes
        (k := k) F Q X Y a,
        ← fullSubcategoryTargetFiberHomMap_commutes
          (k := k) F Q X Y b,
        hab]
    · intro y
      obtain ⟨b, hb⟩ := hAmbient.2 (eCod y)
      obtain ⟨a, ha⟩ := eDom.surjective b
      refine ⟨a, eCod.injective ?_⟩
      rw [fullSubcategoryTargetFiberHomMap_commutes
        (k := k) F Q X Y a, ha, hb]
  source_bijective X Y := by
    let eDom := fullSubcategorySourceFiberHomLinearEquiv
      (k := k) F Q X Y
    let eCod := fullSubcategoryHomLinearEquiv (k := k) Q X
      ((fullSubcategoryRestriction F Q).obj Y)
    let hAmbient := hF.source_bijective X.obj Y.obj
    constructor
    · intro a b hab
      apply eDom.injective
      apply hAmbient.1
      rw [← fullSubcategorySourceFiberHomMap_commutes
        (k := k) F Q X Y a,
        ← fullSubcategorySourceFiberHomMap_commutes
          (k := k) F Q X Y b,
        hab]
    · intro y
      obtain ⟨b, hb⟩ := hAmbient.2 (eCod y)
      obtain ⟨a, ha⟩ := eDom.surjective b
      refine ⟨a, eCod.injective ?_⟩
      rw [fullSubcategorySourceFiberHomMap_commutes
        (k := k) F Q X Y a, ha, hb]

end MagnitudeConjecture.LinearCovering
