import MagnitudeConjecture.CategoryTheory.ShiftOrbitNormalTranslateUnitMul

/-!
# Coherent ambient shifts on a normal-subgroup orbit category

For a normal subgroup `N ≤ G`, the ambient translations of the `N`-shift-orbit
category form a coherent shift indexed by `Additive G`.  The unit and product
constraints are the canonical projected paths constructed in
`ShiftOrbitNormalTranslateUnitMul`.

The coherence proof is checked after applying the faithful inclusion into the
full `G`-orbit category.  There it reduces to cancellation of canonical
object-shift isomorphisms and the equality transports for the group unit and
associativity laws.
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

set_option backward.isDefEq.respectTransparency false in
private theorem shiftOrbitNormalTranslate_zero_add_hom_app
    (N : Subgroup G) [N.Normal] (n : Additive G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateMulIso N
        (0 : Additive G).toMul n.toMul).hom.app
          (show ShiftOrbitCategory C (Additive N) from X) =
      eqToHom (by simp) ≫
        (D.shiftOrbitNormalTranslateFunctor N n.toMul).map
          ((D.shiftOrbitNormalTranslateUnitIso N).inv.app
            (show ShiftOrbitCategory C (Additive N) from X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  induction n using Additive.rec with
  | ofMul g =>
    simp only [toMul_zero, toMul_ofMul]
    apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitNormalTranslateMulHom N 1 g X) =
      D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (eqToHom (by rw [one_mul]) :
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul (1 * g))).obj X) ⟶
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul g)).obj X))
          (D.shiftOrbitNormalTranslateMap N g
            (D.shiftOrbitNormalTranslateUnitInv N X)))
    rw [D.shiftOrbitSubgroupMap_normalTranslateMulHom,
      D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateMap]
    unfold shiftOrbitAmbientConjugate
    rw [D.shiftOrbitSubgroupMap_normalTranslateUnitInv]
    change _ = (D.shiftOrbitSubgroupFunctor N).map (eqToHom _) ≫ _
    rw [eqToHom_map]
    simp
    simp only [← Category.assoc]
    rw [cancel_mono, cancel_mono]
    simpa using dcongr_arg
      (fun a : Additive G ↦ (ShiftOrbitCategory.objectShiftIso X a).inv)
      (zero_add (Additive.ofMul g))

set_option backward.isDefEq.respectTransparency false in
private theorem shiftOrbitNormalTranslate_add_zero_hom_app
    (N : Subgroup G) [N.Normal] (n : Additive G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateMulIso N
        n.toMul (0 : Additive G).toMul).hom.app
          (show ShiftOrbitCategory C (Additive N) from X) =
      eqToHom (by simp) ≫
        (D.shiftOrbitNormalTranslateUnitIso N).inv.app
          ((D.shiftOrbitNormalTranslateFunctor N n.toMul).obj
            (show ShiftOrbitCategory C (Additive N) from X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  induction n using Additive.rec with
  | ofMul g =>
    simp only [toMul_zero, toMul_ofMul]
    apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitNormalTranslateMulHom N g 1 X) =
      D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (eqToHom (by rw [mul_one]) :
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul (g * 1))).obj X) ⟶
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul g)).obj X))
          (D.shiftOrbitNormalTranslateUnitInv N
            ((shiftFunctor C (Additive.ofMul g)).obj X)))
    rw [D.shiftOrbitSubgroupMap_normalTranslateMulHom,
      D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateUnitInv]
    change _ = (D.shiftOrbitSubgroupFunctor N).map (eqToHom _) ≫ _
    rw [eqToHom_map]
    simp
    simp only [← Category.assoc]
    rw [cancel_mono]
    rw [dcongr_arg
      (fun a : Additive G ↦ (ShiftOrbitCategory.objectShiftIso X a).inv)
      (add_zero (Additive.ofMul g))]
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem shiftOrbitNormalTranslate_assoc_hom_app
    (N : Subgroup G) [N.Normal]
    (m₁ m₂ m₃ : Additive G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateMulIso N
        (m₁ + m₂).toMul m₃.toMul).hom.app
          (show ShiftOrbitCategory C (Additive N) from X) ≫
      (D.shiftOrbitNormalTranslateFunctor N m₃.toMul).map
        ((D.shiftOrbitNormalTranslateMulIso N
          m₁.toMul m₂.toMul).hom.app
            (show ShiftOrbitCategory C (Additive N) from X)) =
      eqToHom (by simp [mul_assoc]) ≫
        (D.shiftOrbitNormalTranslateMulIso N
          m₁.toMul (m₂ + m₃).toMul).hom.app
            (show ShiftOrbitCategory C (Additive N) from X) ≫
          (D.shiftOrbitNormalTranslateMulIso N
            m₂.toMul m₃.toMul).hom.app
              ((D.shiftOrbitNormalTranslateFunctor N m₁.toMul).obj
                (show ShiftOrbitCategory C (Additive N) from X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  induction m₁ using Additive.rec with
  | ofMul g =>
    induction m₂ using Additive.rec with
    | ofMul h =>
      induction m₃ using Additive.rec with
      | ofMul k =>
        simp only [toMul_add, toMul_ofMul]
        apply D.shiftOrbitSubgroupMap_injective N _ _
        dsimp only [shiftOrbitNormalTranslateFunctor, Functor.comp_obj]
        simp only [D.shiftOrbitNormalTranslateMulIso_hom_app]
        simp_rw [shiftOrbitCategory_comp_eq]
        rw [D.shiftOrbitSubgroupMap_comp,
          D.shiftOrbitSubgroupMap_normalTranslateMulHom,
          D.shiftOrbitSubgroupMap_normalTranslateMap]
        unfold shiftOrbitAmbientConjugate
        dsimp only [Functor.comp]
        rw [D.shiftOrbitSubgroupMap_normalTranslateMulHom,
          D.shiftOrbitSubgroupMap_comp,
          D.shiftOrbitSubgroupMap_comp,
          D.shiftOrbitSubgroupMap_normalTranslateMulHom,
          D.shiftOrbitSubgroupMap_normalTranslateMulHom]
        change _ = (D.shiftOrbitSubgroupFunctor N).map (eqToHom _) ≫ _
        rw [eqToHom_map]
        simp_rw [← shiftOrbitCategory_comp_eq]
        simp
        simp only [← Category.assoc]
        rw [cancel_mono, cancel_mono, cancel_mono]
        simpa using dcongr_arg
          (fun a : Additive G ↦ (ShiftOrbitCategory.objectShiftIso X a).inv)
          (add_assoc (Additive.ofMul g) (Additive.ofMul h)
            (Additive.ofMul k))

set_option backward.isDefEq.respectTransparency false in
/-- The coherent `G`-indexed ambient translation core on the `N`-orbit
category.  Elements of `N` are not yet quotiented from the index here. -/
noncomputable def shiftOrbitNormalTranslateCore
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftMkCore (ShiftOrbitCategory C (Additive N)) (Additive G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact
    { F := fun a ↦ D.shiftOrbitNormalTranslateFunctor N a.toMul
      zero := D.shiftOrbitNormalTranslateUnitIso N
      add := fun a b ↦ D.shiftOrbitNormalTranslateMulIso N a.toMul b.toMul
      assoc_hom_app := by
        intro m₁ m₂ m₃ X
        exact D.shiftOrbitNormalTranslate_assoc_hom_app N
          m₁ m₂ m₃ (show C from X)
      zero_add_hom_app := by
        intro n X
        exact D.shiftOrbitNormalTranslate_zero_add_hom_app N
          n (show C from X)
      add_zero_hom_app := by
        intro n X
        exact D.shiftOrbitNormalTranslate_add_zero_hom_app N
          n (show C from X) }

/-- The `G`-indexed ambient translation shift on the `N`-orbit category. -/
@[implicit_reducible]
noncomputable def shiftOrbitNormalTranslateHasShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    HasShift (ShiftOrbitCategory C (Additive N)) (Additive G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact hasShiftMk _ _ (D.shiftOrbitNormalTranslateCore N)

/-- Every ambient translation in the constructed shift is additive. -/
theorem shiftOrbitNormalTranslateAdditiveShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := D.shiftOrbitNormalTranslateHasShift N
    ∀ a : Additive G,
      (shiftFunctor (ShiftOrbitCategory C (Additive N)) a).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := D.shiftOrbitNormalTranslateHasShift N
  intro a
  change (D.shiftOrbitNormalTranslateFunctor N a.toMul).Additive
  infer_instance

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
