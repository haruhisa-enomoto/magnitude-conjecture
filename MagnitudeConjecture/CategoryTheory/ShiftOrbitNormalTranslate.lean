import MagnitudeConjecture.CategoryTheory.ShiftOrbitSubgroupFunctor
import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso

/-!
# Ambient translations of normal-subgroup orbit categories

For a normal subgroup `N ≤ G`, conjugation by an ambient deck translation
preserves the `N`-graded morphisms in the shift-orbit category.  This file
constructs the resulting additive endofunctor for each `g : G`.

The construction embeds `N`-graded morphisms faithfully into the full
`G`-orbit category, conjugates by the canonical object-shift isomorphisms,
and projects back to subgroup degrees.  Normality is used exactly to prove
that every conjugated homogeneous degree remains in `N`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]

private theorem shiftOrbitCategory_comp_eq
    {A : Type*} [AddMonoid A] [HasShift C A]
    [∀ a : A, (shiftFunctor C a).Additive]
    {X Y Z : C} (f : ShiftOrbitHom A X Y)
    (g : ShiftOrbitHom A Y Z) :
    (show (show ShiftOrbitCategory C A from X) ⟶
        (show ShiftOrbitCategory C A from Z) from
      (show (show ShiftOrbitCategory C A from X) ⟶
          (show ShiftOrbitCategory C A from Y) from f) ≫
        (show (show ShiftOrbitCategory C A from Y) ⟶
          (show ShiftOrbitCategory C A from Z) from g)) =
      shiftOrbitCompHom f g := rfl

private theorem shiftOrbitCategory_id_eq
    {A : Type*} [AddMonoid A] [HasShift C A]
    [∀ a : A, (shiftFunctor C a).Additive]
    (X : C) :
    (𝟙 (show ShiftOrbitCategory C A from X)) = shiftOrbitId X := rfl

private def ambientShiftHomToSubgroup
    (N : Subgroup G) (X Y : C) (a : Additive G)
    (h : a.toMul ∈ N) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftHom X Y a →+
      ShiftHom X Y (Additive.ofMul (⟨a.toMul, h⟩ : N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  let n : N := ⟨a.toMul, h⟩
  have ha : Additive.ofMul (n : G) = a := by
    apply Additive.ext
    rfl
  let e : D.core.F (Additive.ofMul (n : G)) ≅ D.core.F a := eqToIso (by rw [ha])
  exact
    { toFun := fun f ↦ f ≫ e.inv.app Y
      map_zero' := by simp
      map_add' := by intro f g; simp }

noncomputable def shiftOrbitSubgroupProjection
    (N : Subgroup G) (X Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive G) X Y →+
      ShiftOrbitHom (Additive N) X Y := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  classical
  letI : DecidableEq (Additive G) := Classical.decEq _
  letI : DecidableEq (Additive N) := Classical.decEq _
  exact DirectSum.toAddMonoid fun a ↦
    if h : a.toMul ∈ N then
      (shiftOrbitOf X Y (Additive.ofMul (⟨a.toMul, h⟩ : N))).comp
        (D.ambientShiftHomToSubgroup N X Y a h)
    else 0

set_option linter.unusedSectionVars false in
@[simp]
theorem shiftOrbitSubgroupProjection_of_mem
    (N : Subgroup G) (X Y : C) (a : Additive G)
    (h : a.toMul ∈ N) (f :
      letI := D.hasShift
      letI := D.additiveShift
      ShiftHom X Y a) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupProjection N X Y (shiftOrbitOf X Y a f) =
      shiftOrbitOf X Y (Additive.ofMul (⟨a.toMul, h⟩ : N))
        (D.ambientShiftHomToSubgroup N X Y a h f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : DecidableEq (Additive G) := Classical.decEq _
  letI : DecidableEq (Additive N) := Classical.decEq _
  unfold shiftOrbitSubgroupProjection shiftOrbitOf
  rw [DirectSum.toAddMonoid_of]
  simp only [dif_pos h]
  rfl

theorem shiftOrbitSubgroupProjection_map
    (N : Subgroup G) (X Y : C)
    (f : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupProjection N X Y
        (D.shiftOrbitSubgroupMap N X Y f) = f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : DecidableEq (Additive G) := Classical.decEq _
  letI : DecidableEq (Additive N) := Classical.decEq _
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    change D.shiftOrbitSubgroupProjection N X Y
        (D.shiftOrbitSubgroupMap N X Y
          (shiftOrbitOf (C := C) (A := Additive N) X Y a fa)) =
      shiftOrbitOf (C := C) (A := Additive N) X Y a fa
    rw [D.shiftOrbitSubgroupMap_of,
      D.shiftOrbitSubgroupProjection_of_mem]
    apply DFinsupp.single_eq_of_sigma_eq
    apply Sigma.ext
    · apply Additive.ext
      rfl
    · simp [ambientShiftHomToSubgroup]
      change fa ≫ 𝟙 _ = fa
      simp
  · intro f₁ f₂ hf₁ hf₂
    simpa only [map_add] using congrArg₂ (.+.) hf₁ hf₂

theorem shiftOrbitSubgroupMap_projection_of_mem
    (N : Subgroup G) (X Y : C) (a : Additive G)
    (h : a.toMul ∈ N) (f :
      letI := D.hasShift
      letI := D.additiveShift
      ShiftHom X Y a) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N X Y
        (D.shiftOrbitSubgroupProjection N X Y
          (shiftOrbitOf X Y a f)) =
      shiftOrbitOf X Y a f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : DecidableEq (Additive G) := Classical.decEq _
  letI : DecidableEq (Additive N) := Classical.decEq _
  rw [D.shiftOrbitSubgroupProjection_of_mem N X Y a h,
    D.shiftOrbitSubgroupMap_of]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext
  · apply Additive.ext
    rfl
  · simp [ambientShiftHomToSubgroup]
    change (f ≫ 𝟙 ((D.core.F a).obj Y)) = f
    exact Category.comp_id f

theorem shiftOrbitSubgroupMap_injective (N : Subgroup G) (X Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    Function.Injective (D.shiftOrbitSubgroupMap N X Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  intro f g h
  apply_fun D.shiftOrbitSubgroupProjection N X Y at h
  simpa only [D.shiftOrbitSubgroupProjection_map] using h

/-- Ambient conjugation of an `N`-orbit morphism by the canonical
identifications with a fixed `g`-shift. -/
noncomputable def shiftOrbitAmbientConjugate
    (N : Subgroup G) (g : G) {X Y : C}
    (f : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive G)
      ((shiftFunctor C (Additive.ofMul g)).obj X)
      ((shiftFunctor C (Additive.ofMul g)).obj Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g)).inv ≫
    D.shiftOrbitSubgroupMap N X Y f ≫
    (ShiftOrbitCategory.objectShiftIso Y (Additive.ofMul g)).hom

@[simp]
theorem shiftOrbitAmbientConjugate_zero
    (N : Subgroup G) (g : G) (X Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitAmbientConjugate N g
      (0 : ShiftOrbitHom (Additive N) X Y) = 0 := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  simp [shiftOrbitAmbientConjugate]

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitAmbientConjugate_add
    (N : Subgroup G) (g : G) {X Y : C}
    (f h : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitAmbientConjugate N g (f + h) =
      D.shiftOrbitAmbientConjugate N g f +
        D.shiftOrbitAmbientConjugate N g h := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitAmbientConjugate
  simp_rw [shiftOrbitCategory_comp_eq]
  rw [map_add, map_add]
  exact (shiftOrbitCompHom
    (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g)).inv).map_add _ _

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitAmbientConjugate_homogeneous_supported
    (N : Subgroup G) [N.Normal] (g : G) (X Y : C)
    (a : Additive N) (f :
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftHom X Y a) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitSubgroupProjection N _ _
          (D.shiftOrbitAmbientConjugate N g
            (shiftOrbitOf X Y a f))) =
      D.shiftOrbitAmbientConjugate N g
        (shiftOrbitOf X Y a f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  rw [shiftOrbitAmbientConjugate]
  simp only [ShiftOrbitCategory.objectShiftIso]
  simp_rw [shiftOrbitCategory_comp_eq]
  unfold shiftOrbitFromShift shiftOrbitToShift
  rw [D.shiftOrbitSubgroupMap_of,
    shiftOrbitCompHom_of_of, shiftOrbitCompHom_of_of]
  apply D.shiftOrbitSubgroupMap_projection_of_mem
  simpa [mul_assoc] using
    ‹N.Normal›.conj_mem a.toMul a.toMul.property g⁻¹

theorem shiftOrbitAmbientConjugate_supported
    (N : Subgroup G) [N.Normal] (g : G) {X Y : C}
    (f : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitSubgroupProjection N _ _
          (D.shiftOrbitAmbientConjugate N g f)) =
      D.shiftOrbitAmbientConjugate N g f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : DecidableEq (Additive N) := Classical.decEq _
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    exact D.shiftOrbitAmbientConjugate_homogeneous_supported N g X Y a fa
  · intro f₁ f₂ hf₁ hf₂
    rw [D.shiftOrbitAmbientConjugate_add,
      map_add, map_add, hf₁, hf₂]

/-- Translation of an `N`-orbit morphism by an ambient group element.  It is
the subgroup-degree projection of its canonical conjugate in the full
`G`-orbit category. -/
noncomputable def shiftOrbitNormalTranslateMap
    (N : Subgroup G) [N.Normal] (g : G) {X Y : C}
    (f : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive N)
      ((shiftFunctor C (Additive.ofMul g)).obj X)
      ((shiftFunctor C (Additive.ofMul g)).obj Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact D.shiftOrbitSubgroupProjection N _ _
    (D.shiftOrbitAmbientConjugate N g f)

theorem shiftOrbitSubgroupMap_normalTranslateMap
    (N : Subgroup G) [N.Normal] (g : G) {X Y : C}
    (f : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitNormalTranslateMap N g f) =
      D.shiftOrbitAmbientConjugate N g f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact D.shiftOrbitAmbientConjugate_supported N g f

@[simp]
theorem shiftOrbitNormalTranslateMap_add
    (N : Subgroup G) [N.Normal] (g : G) {X Y : C}
    (f h : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitNormalTranslateMap N g (f + h) =
      D.shiftOrbitNormalTranslateMap N g f +
        D.shiftOrbitNormalTranslateMap N g h := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitNormalTranslateMap
  rw [D.shiftOrbitAmbientConjugate_add, map_add]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed ambient translation functor on the nonskeletal `N`-shift-orbit
category. -/
noncomputable def shiftOrbitNormalTranslateFunctor
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitCategory C (Additive N) ⥤
      ShiftOrbitCategory C (Additive N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact
    { obj := fun X ↦
        (shiftFunctor C (Additive.ofMul g)).obj (show C from X)
      map := fun {X Y} f ↦ D.shiftOrbitNormalTranslateMap N g f
      map_id := by
        intro X
        apply D.shiftOrbitSubgroupMap_injective N _ _
        simp_rw [shiftOrbitCategory_id_eq]
        rw [D.shiftOrbitSubgroupMap_normalTranslateMap,
          D.shiftOrbitSubgroupMap_id]
        unfold shiftOrbitAmbientConjugate
        rw [D.shiftOrbitSubgroupMap_id]
        simp_rw [shiftOrbitCategory_comp_eq]
        let u := ShiftOrbitCategory.objectShiftIso
          (show C from X) (Additive.ofMul g)
        rw [shiftOrbitComp_id_left]
        have hu := u.inv_hom_id
        change shiftOrbitCompHom u.inv u.hom =
          shiftOrbitId ((shiftFunctor C (Additive.ofMul g)).obj
            (show C from X)) at hu
        exact hu
      map_comp := by
        intro X Y Z f h
        apply D.shiftOrbitSubgroupMap_injective N _ _
        simp_rw [shiftOrbitCategory_comp_eq]
        rw [D.shiftOrbitSubgroupMap_normalTranslateMap,
          D.shiftOrbitSubgroupMap_comp,
          D.shiftOrbitSubgroupMap_normalTranslateMap,
          D.shiftOrbitSubgroupMap_normalTranslateMap]
        unfold shiftOrbitAmbientConjugate
        rw [D.shiftOrbitSubgroupMap_comp]
        let uX := ShiftOrbitCategory.objectShiftIso
          (show C from X) (Additive.ofMul g)
        let uY := ShiftOrbitCategory.objectShiftIso
          (show C from Y) (Additive.ofMul g)
        let uZ := ShiftOrbitCategory.objectShiftIso
          (show C from Z) (Additive.ofMul g)
        have hcat :
            uX.inv ≫
                (D.shiftOrbitSubgroupMap N _ _ f ≫
                  D.shiftOrbitSubgroupMap N _ _ h) ≫ uZ.hom =
              (uX.inv ≫ D.shiftOrbitSubgroupMap N _ _ f ≫ uY.hom) ≫
                (uY.inv ≫ D.shiftOrbitSubgroupMap N _ _ h ≫ uZ.hom) := by
          simp
        simpa only [uX, uY, uZ, shiftOrbitCategory_comp_eq] using hcat }

instance shiftOrbitNormalTranslateFunctor_additive
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateFunctor N g).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  constructor
  intro X Y f h
  exact D.shiftOrbitNormalTranslateMap_add N g f h

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
