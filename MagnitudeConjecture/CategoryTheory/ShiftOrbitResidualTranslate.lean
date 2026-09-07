import MagnitudeConjecture.CategoryTheory.ShiftOrbitNormalTranslateShift

/-!
# Residual quotient translations of a normal-subgroup orbit category

Let `N ◁ G`.  A chosen representative of each coset in `G / N` determines
an ambient translation functor of the `N`-shift-orbit category.  This file
constructs the residual unit and product isomorphisms.  They combine the
canonical coset-comparison isomorphisms with the coherent unit and product
isomorphisms for fixed ambient translations.
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

/-- The representative of a quotient-group element used by the residual
translation construction. -/
noncomputable def normalQuotientRepresentative
    (N : Subgroup G) (q : G ⧸ N) : G :=
  Quotient.out q

@[simp]
theorem normalQuotientRepresentative_mk
    (N : Subgroup G) (q : G ⧸ N) :
    ((normalQuotientRepresentative N q : G) : G ⧸ N) = q :=
  Quotient.out_eq' q

theorem normalQuotientRepresentative_one_eq
    (N : Subgroup G) [N.Normal] :
    ((normalQuotientRepresentative N (1 : G ⧸ N) : G) : G ⧸ N) =
      ((1 : G) : G ⧸ N) := by
  simp

theorem normalQuotientRepresentative_mul_eq
    (N : Subgroup G) [N.Normal] (q r : G ⧸ N) :
    ((normalQuotientRepresentative N (q * r) : G) : G ⧸ N) =
      ((normalQuotientRepresentative N q *
        normalQuotientRepresentative N r : G) : G ⧸ N) := by
  simp

/-- The residual translation at the identity coset is isomorphic to the
identity functor. -/
noncomputable def shiftOrbitResidualUnitIso
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitNormalTranslateFunctor N
        (normalQuotientRepresentative N (1 : G ⧸ N)) ≅
      𝟭 (ShiftOrbitCategory C (Additive N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact (D.shiftOrbitNormalTranslateIsoOfQuotientEq N _ _
    (normalQuotientRepresentative_one_eq N)).trans
    (D.shiftOrbitNormalTranslateUnitIso N)

/-- The residual translation at a product coset is isomorphic to the
composite residual translations at its two factors. -/
noncomputable def shiftOrbitResidualAddIso
    (N : Subgroup G) [N.Normal] (q r : G ⧸ N) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitNormalTranslateFunctor N
        (normalQuotientRepresentative N (q * r)) ≅
      D.shiftOrbitNormalTranslateFunctor N
          (normalQuotientRepresentative N q) ⋙
        D.shiftOrbitNormalTranslateFunctor N
          (normalQuotientRepresentative N r) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact (D.shiftOrbitNormalTranslateIsoOfQuotientEq N _ _
    (normalQuotientRepresentative_mul_eq N q r)).trans
    (D.shiftOrbitNormalTranslateMulIso N _ _)

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitSubgroupMap_residualUnitHom
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N (1 : G ⧸ N)))).obj X) X
        ((D.shiftOrbitResidualUnitIso N).hom.app
          (show ShiftOrbitCategory C (Additive N) from X)) =
      (ShiftOrbitCategory.objectShiftIso X
        (Additive.ofMul
          (normalQuotientRepresentative N (1 : G ⧸ N)))).inv := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitResidualUnitIso
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change D.shiftOrbitSubgroupMap N _ _
      (shiftOrbitCompHom
        (D.shiftOrbitNormalTranslateComparisonMap N
          (normalQuotientRepresentative N (1 : G ⧸ N)) 1
          (normalQuotientRepresentative_one_eq N) X)
        (D.shiftOrbitNormalTranslateUnitHom N X)) = _
  rw [D.shiftOrbitSubgroupMap_comp,
    D.shiftOrbitSubgroupMap_normalTranslateComparisonMap,
    D.shiftOrbitSubgroupMap_normalTranslateUnitHom]
  simp_rw [← shiftOrbitCategory_comp_eq]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitSubgroupMap_residualUnitInv
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N X
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N (1 : G ⧸ N)))).obj X)
        ((D.shiftOrbitResidualUnitIso N).inv.app
          (show ShiftOrbitCategory C (Additive N) from X)) =
      (ShiftOrbitCategory.objectShiftIso X
        (Additive.ofMul
          (normalQuotientRepresentative N (1 : G ⧸ N)))).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitResidualUnitIso
  simp only [Iso.trans_inv, NatTrans.comp_app]
  change D.shiftOrbitSubgroupMap N _ _
      (shiftOrbitCompHom
        (D.shiftOrbitNormalTranslateUnitInv N X)
        (D.shiftOrbitNormalTranslateComparisonMap N 1
          (normalQuotientRepresentative N (1 : G ⧸ N))
          (normalQuotientRepresentative_one_eq N).symm X)) = _
  rw [D.shiftOrbitSubgroupMap_comp,
    D.shiftOrbitSubgroupMap_normalTranslateUnitInv,
    D.shiftOrbitSubgroupMap_normalTranslateComparisonMap]
  simp_rw [← shiftOrbitCategory_comp_eq]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitSubgroupMap_residualAddHom
    (N : Subgroup G) [N.Normal] (q r : G ⧸ N) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N (q * r)))).obj X)
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N r))).obj
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q))).obj X))
        ((D.shiftOrbitResidualAddIso N q r).hom.app
          (show ShiftOrbitCategory C (Additive N) from X)) =
      ((ShiftOrbitCategory.objectShiftIso X
          (Additive.ofMul
            (normalQuotientRepresentative N (q * r)))).inv ≫
        (ShiftOrbitCategory.objectShiftIso X
          (Additive.ofMul
            (normalQuotientRepresentative N q))).hom) ≫
        (ShiftOrbitCategory.objectShiftIso
          ((shiftFunctor C (Additive.ofMul
            (normalQuotientRepresentative N q))).obj X)
          (Additive.ofMul
            (normalQuotientRepresentative N r))).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitResidualAddIso
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change D.shiftOrbitSubgroupMap N _ _
      (shiftOrbitCompHom
        (D.shiftOrbitNormalTranslateComparisonMap N
          (normalQuotientRepresentative N (q * r))
          (normalQuotientRepresentative N q *
            normalQuotientRepresentative N r)
          (normalQuotientRepresentative_mul_eq N q r) X)
        (D.shiftOrbitNormalTranslateMulHom N
          (normalQuotientRepresentative N q)
          (normalQuotientRepresentative N r) X)) = _
  rw [D.shiftOrbitSubgroupMap_comp,
    D.shiftOrbitSubgroupMap_normalTranslateComparisonMap,
    D.shiftOrbitSubgroupMap_normalTranslateMulHom]
  simp_rw [← shiftOrbitCategory_comp_eq]
  simp

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
