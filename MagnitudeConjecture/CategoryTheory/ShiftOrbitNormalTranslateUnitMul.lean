import MagnitudeConjecture.CategoryTheory.DeckOrbitNormalTranslateCoset

/-!
# Unit and multiplication for normal-orbit translations

Ambient normal-orbit translation by the identity is naturally isomorphic to
the identity functor, and translation by a product is naturally isomorphic to
the composite translations.  The components are projected canonical paths in
the full orbit category.  Their degrees multiply to the identity, so they lie
in every normal subgroup orbit category.
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

noncomputable def shiftOrbitNormalTranslateUnitHom (N : Subgroup G) [N.Normal]
    (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive N)
      ((shiftFunctor C (Additive.ofMul (1 : G))).obj X) X := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact D.shiftOrbitSubgroupProjection N _ _
    (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul (1 : G))).inv

noncomputable def shiftOrbitNormalTranslateUnitInv (N : Subgroup G) [N.Normal]
    (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive N) X
      ((shiftFunctor C (Additive.ofMul (1 : G))).obj X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact D.shiftOrbitSubgroupProjection N _ _
    (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul (1 : G))).hom

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitSubgroupMap_normalTranslateUnitHom
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N _ _ (D.shiftOrbitNormalTranslateUnitHom N X) =
      (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul (1 : G))).inv := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitNormalTranslateUnitHom
  simp only [ShiftOrbitCategory.objectShiftIso, shiftOrbitFromShift]
  apply D.shiftOrbitSubgroupMap_projection_of_mem
  simp

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitSubgroupMap_normalTranslateUnitInv
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N _ _ (D.shiftOrbitNormalTranslateUnitInv N X) =
      (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul (1 : G))).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitNormalTranslateUnitInv
  simp only [ShiftOrbitCategory.objectShiftIso, shiftOrbitToShift]
  apply D.shiftOrbitSubgroupMap_projection_of_mem
  simp

set_option backward.isDefEq.respectTransparency false in
noncomputable def shiftOrbitNormalTranslateUnitIso (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitNormalTranslateFunctor N 1 ≅
      𝟭 (ShiftOrbitCategory C (Additive N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  refine NatIso.ofComponents (fun X ↦
    { hom := D.shiftOrbitNormalTranslateUnitHom N (show C from X)
      inv := D.shiftOrbitNormalTranslateUnitInv N (show C from X)
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  · apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom (D.shiftOrbitNormalTranslateUnitHom N (show C from X))
          (D.shiftOrbitNormalTranslateUnitInv N (show C from X))) =
      D.shiftOrbitSubgroupMap N _ _ (shiftOrbitId _)
    rw [D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateUnitHom,
      D.shiftOrbitSubgroupMap_normalTranslateUnitInv,
      D.shiftOrbitSubgroupMap_id]
    let u := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul (1 : G))
    exact u.inv_hom_id
  · apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom (D.shiftOrbitNormalTranslateUnitInv N (show C from X))
          (D.shiftOrbitNormalTranslateUnitHom N (show C from X))) =
      D.shiftOrbitSubgroupMap N _ _ (shiftOrbitId _)
    rw [D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateUnitInv,
      D.shiftOrbitSubgroupMap_normalTranslateUnitHom,
      D.shiftOrbitSubgroupMap_id]
    let u := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul (1 : G))
    exact u.hom_inv_id
  · intro X Y f
    apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom (D.shiftOrbitNormalTranslateMap N 1 f)
          (D.shiftOrbitNormalTranslateUnitHom N (show C from Y))) =
      D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom (D.shiftOrbitNormalTranslateUnitHom N (show C from X)) f)
    rw [D.shiftOrbitSubgroupMap_comp, D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateMap]
    have hX := D.shiftOrbitSubgroupMap_normalTranslateUnitHom N (show C from X)
    have hY := D.shiftOrbitSubgroupMap_normalTranslateUnitHom N (show C from Y)
    rw [hX, hY]
    unfold shiftOrbitAmbientConjugate
    let uX := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul (1 : G))
    let uY := ShiftOrbitCategory.objectShiftIso
      (show C from Y) (Additive.ofMul (1 : G))
    let ef := D.shiftOrbitSubgroupMap N (show C from X) (show C from Y) f
    have hcat : (uX.inv ≫ ef ≫ uY.hom) ≫ uY.inv = uX.inv ≫ ef := by
      simp
    exact hcat

@[simp]
theorem shiftOrbitNormalTranslateUnitIso_hom_app
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateUnitIso N).hom.app X =
      D.shiftOrbitNormalTranslateUnitHom N X := rfl

@[simp]
theorem shiftOrbitNormalTranslateUnitIso_inv_app
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateUnitIso N).inv.app X =
      D.shiftOrbitNormalTranslateUnitInv N X := rfl

noncomputable def shiftOrbitNormalTranslateMulHom
    (N : Subgroup G) [N.Normal] (g h : G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive N)
      ((shiftFunctor C (Additive.ofMul (g * h))).obj X)
      ((shiftFunctor C (Additive.ofMul h)).obj
        ((shiftFunctor C (Additive.ofMul g)).obj X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  let ugh := ShiftOrbitCategory.objectShiftIso X (Additive.ofMul (g * h))
  let ug := ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g)
  let uh := ShiftOrbitCategory.objectShiftIso
    ((shiftFunctor C (Additive.ofMul g)).obj X) (Additive.ofMul h)
  exact D.shiftOrbitSubgroupProjection N _ _
    ((ugh.inv ≫ ug.hom) ≫ uh.hom)

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitSubgroupMap_normalTranslateMulHom
    (N : Subgroup G) [N.Normal] (g h : G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitNormalTranslateMulHom N g h X) =
      ((ShiftOrbitCategory.objectShiftIso X
          (Additive.ofMul (g * h))).inv ≫
        (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g)).hom) ≫
        (ShiftOrbitCategory.objectShiftIso
          ((shiftFunctor C (Additive.ofMul g)).obj X)
          (Additive.ofMul h)).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitNormalTranslateMulHom
  dsimp only
  simp only [ShiftOrbitCategory.objectShiftIso]
  change D.shiftOrbitSubgroupMap N _ _
      (D.shiftOrbitSubgroupProjection N _ _
        (shiftOrbitCompHom
          (shiftOrbitCompHom
            (shiftOrbitFromShift X (Additive.ofMul (g * h)))
            (shiftOrbitToShift X (Additive.ofMul g)))
          (shiftOrbitToShift
            ((shiftFunctor C (Additive.ofMul g)).obj X)
            (Additive.ofMul h)))) =
    shiftOrbitCompHom
      (shiftOrbitCompHom
        (shiftOrbitFromShift X (Additive.ofMul (g * h)))
        (shiftOrbitToShift X (Additive.ofMul g)))
      (shiftOrbitToShift ((shiftFunctor C (Additive.ofMul g)).obj X)
        (Additive.ofMul h))
  simp only [shiftOrbitFromShift, shiftOrbitToShift]
  rw [shiftOrbitCompHom_of_of, shiftOrbitCompHom_of_of]
  apply D.shiftOrbitSubgroupMap_projection_of_mem
  simp

noncomputable def shiftOrbitNormalTranslateMulInv
    (N : Subgroup G) [N.Normal] (g h : G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive N)
      ((shiftFunctor C (Additive.ofMul h)).obj
        ((shiftFunctor C (Additive.ofMul g)).obj X))
      ((shiftFunctor C (Additive.ofMul (g * h))).obj X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  let ugh := ShiftOrbitCategory.objectShiftIso X (Additive.ofMul (g * h))
  let ug := ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g)
  let uh := ShiftOrbitCategory.objectShiftIso
    ((shiftFunctor C (Additive.ofMul g)).obj X) (Additive.ofMul h)
  exact D.shiftOrbitSubgroupProjection N _ _
    ((uh.inv ≫ ug.inv) ≫ ugh.hom)

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitSubgroupMap_normalTranslateMulInv
    (N : Subgroup G) [N.Normal] (g h : G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitNormalTranslateMulInv N g h X) =
      ((ShiftOrbitCategory.objectShiftIso
          ((shiftFunctor C (Additive.ofMul g)).obj X)
          (Additive.ofMul h)).inv ≫
        (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g)).inv) ≫
        (ShiftOrbitCategory.objectShiftIso X
          (Additive.ofMul (g * h))).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitNormalTranslateMulInv
  dsimp only
  simp only [ShiftOrbitCategory.objectShiftIso]
  change D.shiftOrbitSubgroupMap N _ _
      (D.shiftOrbitSubgroupProjection N _ _
        (shiftOrbitCompHom
          (shiftOrbitCompHom
            (shiftOrbitFromShift
              ((shiftFunctor C (Additive.ofMul g)).obj X)
              (Additive.ofMul h))
            (shiftOrbitFromShift X (Additive.ofMul g)))
          (shiftOrbitToShift X (Additive.ofMul (g * h))))) =
    shiftOrbitCompHom
      (shiftOrbitCompHom
        (shiftOrbitFromShift ((shiftFunctor C (Additive.ofMul g)).obj X)
          (Additive.ofMul h))
        (shiftOrbitFromShift X (Additive.ofMul g)))
      (shiftOrbitToShift X (Additive.ofMul (g * h)))
  simp only [shiftOrbitFromShift, shiftOrbitToShift]
  rw [shiftOrbitCompHom_of_of, shiftOrbitCompHom_of_of]
  apply D.shiftOrbitSubgroupMap_projection_of_mem
  simp

set_option backward.isDefEq.respectTransparency false in
noncomputable def shiftOrbitNormalTranslateMulIso
    (N : Subgroup G) [N.Normal] (g h : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitNormalTranslateFunctor N (g * h) ≅
      D.shiftOrbitNormalTranslateFunctor N g ⋙
        D.shiftOrbitNormalTranslateFunctor N h := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  refine NatIso.ofComponents (fun X ↦
    { hom := D.shiftOrbitNormalTranslateMulHom N g h (show C from X)
      inv := D.shiftOrbitNormalTranslateMulInv N g h (show C from X)
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  · apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (D.shiftOrbitNormalTranslateMulHom N g h (show C from X))
          (D.shiftOrbitNormalTranslateMulInv N g h (show C from X))) =
      D.shiftOrbitSubgroupMap N _ _ (shiftOrbitId _)
    rw [D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateMulHom,
      D.shiftOrbitSubgroupMap_normalTranslateMulInv,
      D.shiftOrbitSubgroupMap_id]
    let ugh := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul (g * h))
    let ug := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g)
    let uh := ShiftOrbitCategory.objectShiftIso
      ((shiftFunctor C (Additive.ofMul g)).obj (show C from X))
      (Additive.ofMul h)
    have hcat : ((ugh.inv ≫ ug.hom) ≫ uh.hom) ≫
        ((uh.inv ≫ ug.inv) ≫ ugh.hom) = 𝟙 _ := by
      simp
    exact hcat

  · apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (D.shiftOrbitNormalTranslateMulInv N g h (show C from X))
          (D.shiftOrbitNormalTranslateMulHom N g h (show C from X))) =
      D.shiftOrbitSubgroupMap N _ _ (shiftOrbitId _)
    rw [D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateMulInv,
      D.shiftOrbitSubgroupMap_normalTranslateMulHom,
      D.shiftOrbitSubgroupMap_id]
    let ugh := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul (g * h))
    let ug := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g)
    let uh := ShiftOrbitCategory.objectShiftIso
      ((shiftFunctor C (Additive.ofMul g)).obj (show C from X))
      (Additive.ofMul h)
    have hcat : ((uh.inv ≫ ug.inv) ≫ ugh.hom) ≫
        ((ugh.inv ≫ ug.hom) ≫ uh.hom) = 𝟙 _ := by
      simp
    exact hcat
  · intro X Y f
    apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom (D.shiftOrbitNormalTranslateMap N (g * h) f)
          (D.shiftOrbitNormalTranslateMulHom N g h (show C from Y))) =
      D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (D.shiftOrbitNormalTranslateMulHom N g h (show C from X))
          (D.shiftOrbitNormalTranslateMap N h
            (D.shiftOrbitNormalTranslateMap N g f)))
    rw [D.shiftOrbitSubgroupMap_comp, D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateMap,
      D.shiftOrbitSubgroupMap_normalTranslateMap,
      D.shiftOrbitSubgroupMap_normalTranslateMulHom,
      D.shiftOrbitSubgroupMap_normalTranslateMulHom]
    unfold shiftOrbitAmbientConjugate
    rw [D.shiftOrbitSubgroupMap_normalTranslateMap]
    unfold shiftOrbitAmbientConjugate
    let ughX := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul (g * h))
    let ughY := ShiftOrbitCategory.objectShiftIso
      (show C from Y) (Additive.ofMul (g * h))
    let ugX := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g)
    let ugY := ShiftOrbitCategory.objectShiftIso
      (show C from Y) (Additive.ofMul g)
    let uhX := ShiftOrbitCategory.objectShiftIso
      ((shiftFunctor C (Additive.ofMul g)).obj (show C from X))
      (Additive.ofMul h)
    let uhY := ShiftOrbitCategory.objectShiftIso
      ((shiftFunctor C (Additive.ofMul g)).obj (show C from Y))
      (Additive.ofMul h)
    let ef := D.shiftOrbitSubgroupMap N (show C from X) (show C from Y) f
    have hcat :
        (ughX.inv ≫ ef ≫ ughY.hom) ≫
            ((ughY.inv ≫ ugY.hom) ≫ uhY.hom) =
          ((ughX.inv ≫ ugX.hom) ≫ uhX.hom) ≫
            (uhX.inv ≫ (ugX.inv ≫ ef ≫ ugY.hom) ≫ uhY.hom) := by
      simp
    exact hcat

@[simp]
theorem shiftOrbitNormalTranslateMulIso_hom_app
    (N : Subgroup G) [N.Normal] (g h : G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateMulIso N g h).hom.app X =
      D.shiftOrbitNormalTranslateMulHom N g h X := rfl

@[simp]
theorem shiftOrbitNormalTranslateMulIso_inv_app
    (N : Subgroup G) [N.Normal] (g h : G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateMulIso N g h).inv.app X =
      D.shiftOrbitNormalTranslateMulInv N g h X := rfl

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
