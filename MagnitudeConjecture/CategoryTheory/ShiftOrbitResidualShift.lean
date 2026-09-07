import MagnitudeConjecture.CategoryTheory.ShiftOrbitResidualTranslate

/-!
# The residual quotient-group shift

For `N ◁ G`, the chosen `G / N`-representative translations of the
`N`-shift-orbit category satisfy the two unit laws and associativity.  They
therefore define a coherent shift indexed by `Additive (G / N)`.

The proofs use the canonical-path formulas from
`ShiftOrbitResidualTranslate`.  Faithful inclusion into the full `G`-orbit
category reduces every coherence equation to cancellation of object-shift
isomorphisms and dependent congruence along a quotient-group law.
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
private theorem shiftOrbitResidual_zero_add_hom_app
    (N : Subgroup G) [N.Normal]
    (n : Additive (G ⧸ N)) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitResidualAddIso N
        (0 : Additive (G ⧸ N)).toMul n.toMul).hom.app
          (show ShiftOrbitCategory C (Additive N) from X) =
      eqToHom (by simp) ≫
        (D.shiftOrbitNormalTranslateFunctor N
          (normalQuotientRepresentative N n.toMul)).map
            ((D.shiftOrbitResidualUnitIso N).inv.app
              (show ShiftOrbitCategory C (Additive N) from X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  induction n using Additive.rec with
  | ofMul q =>
    simp only [toMul_zero, toMul_ofMul]
    apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        ((D.shiftOrbitResidualAddIso N 1 q).hom.app
          (show ShiftOrbitCategory C (Additive N) from X)) =
      D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (eqToHom (by rw [one_mul]) :
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N (1 * q)))).obj X) ⟶
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q))).obj X))
          (D.shiftOrbitNormalTranslateMap N
            (normalQuotientRepresentative N q)
            ((D.shiftOrbitResidualUnitIso N).inv.app
              (show ShiftOrbitCategory C (Additive N) from X))))
    dsimp only [shiftOrbitNormalTranslateFunctor, Functor.comp_obj]
    dsimp only [Functor.comp]
    rw [D.shiftOrbitSubgroupMap_residualAddHom,
      D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateMap]
    unfold shiftOrbitAmbientConjugate
    dsimp only [shiftOrbitNormalTranslateFunctor, Functor.comp_obj]
    rw [D.shiftOrbitSubgroupMap_residualUnitInv]
    change _ = (D.shiftOrbitSubgroupFunctor N).map (eqToHom _) ≫ _
    rw [eqToHom_map]
    simp
    simp only [← Category.assoc]
    rw [cancel_mono, cancel_mono]
    simpa using dcongr_arg
      (fun a : Additive (G ⧸ N) ↦
        (ShiftOrbitCategory.objectShiftIso X
          (Additive.ofMul
            (normalQuotientRepresentative N a.toMul))).inv)
      (zero_add (Additive.ofMul q))

set_option backward.isDefEq.respectTransparency false in
private theorem shiftOrbitResidual_add_zero_hom_app
    (N : Subgroup G) [N.Normal]
    (n : Additive (G ⧸ N)) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitResidualAddIso N
        n.toMul (0 : Additive (G ⧸ N)).toMul).hom.app
          (show ShiftOrbitCategory C (Additive N) from X) =
      eqToHom (by simp) ≫
        (D.shiftOrbitResidualUnitIso N).inv.app
          ((D.shiftOrbitNormalTranslateFunctor N
            (normalQuotientRepresentative N n.toMul)).obj
              (show ShiftOrbitCategory C (Additive N) from X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  induction n using Additive.rec with
  | ofMul q =>
    simp only [toMul_zero, toMul_ofMul]
    apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        ((D.shiftOrbitResidualAddIso N q 1).hom.app
          (show ShiftOrbitCategory C (Additive N) from X)) =
      D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (eqToHom (by rw [mul_one]) :
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N (q * 1)))).obj X) ⟶
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q))).obj X))
          ((D.shiftOrbitResidualUnitIso N).inv.app
            (show ShiftOrbitCategory C (Additive N) from
              (shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q))).obj X)))
    dsimp only [shiftOrbitNormalTranslateFunctor, Functor.comp_obj]
    dsimp only [Functor.comp]
    rw [D.shiftOrbitSubgroupMap_residualAddHom,
      D.shiftOrbitSubgroupMap_comp]
    dsimp only [shiftOrbitNormalTranslateFunctor, Functor.comp_obj]
    rw [D.shiftOrbitSubgroupMap_residualUnitInv]
    change _ = (D.shiftOrbitSubgroupFunctor N).map (eqToHom _) ≫ _
    rw [eqToHom_map]
    simp
    simp only [← Category.assoc]
    rw [cancel_mono]
    rw [dcongr_arg
      (fun a : G ⧸ N ↦
        (ShiftOrbitCategory.objectShiftIso X
          (Additive.ofMul
            (normalQuotientRepresentative N a))).inv)
      (mul_one q)]
    simp

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem shiftOrbitResidual_assoc_hom_app
    (N : Subgroup G) [N.Normal]
    (m₁ m₂ m₃ : Additive (G ⧸ N)) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitResidualAddIso N
        (m₁ + m₂).toMul m₃.toMul).hom.app
          (show ShiftOrbitCategory C (Additive N) from X) ≫
      (D.shiftOrbitNormalTranslateFunctor N
        (normalQuotientRepresentative N m₃.toMul)).map
          ((D.shiftOrbitResidualAddIso N m₁.toMul m₂.toMul).hom.app
            (show ShiftOrbitCategory C (Additive N) from X)) =
      eqToHom (by simp [mul_assoc]) ≫
        (D.shiftOrbitResidualAddIso N
          m₁.toMul (m₂ + m₃).toMul).hom.app
            (show ShiftOrbitCategory C (Additive N) from X) ≫
          (D.shiftOrbitResidualAddIso N m₂.toMul m₃.toMul).hom.app
            ((D.shiftOrbitNormalTranslateFunctor N
              (normalQuotientRepresentative N m₁.toMul)).obj
                (show ShiftOrbitCategory C (Additive N) from X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  induction m₁ using Additive.rec with
  | ofMul q =>
    induction m₂ using Additive.rec with
    | ofMul r =>
      induction m₃ using Additive.rec with
      | ofMul s =>
        simp only [toMul_add, toMul_ofMul]
        apply D.shiftOrbitSubgroupMap_injective N _ _
        dsimp only [shiftOrbitNormalTranslateFunctor, Functor.comp_obj]
        dsimp only [Functor.comp]
        simp_rw [shiftOrbitCategory_comp_eq]
        rw [D.shiftOrbitSubgroupMap_comp]
        rw [D.shiftOrbitSubgroupMap_residualAddHom N (q * r) s X]
        rw [D.shiftOrbitSubgroupMap_normalTranslateMap]
        unfold shiftOrbitAmbientConjugate
        dsimp only [Functor.comp]
        rw [D.shiftOrbitSubgroupMap_residualAddHom N q r X]
        rw [D.shiftOrbitSubgroupMap_comp,
          D.shiftOrbitSubgroupMap_comp]
        rw [D.shiftOrbitSubgroupMap_residualAddHom N q (r * s) X]
        rw [D.shiftOrbitSubgroupMap_residualAddHom N r s
          ((shiftFunctor C (Additive.ofMul
            (normalQuotientRepresentative N q))).obj X)]
        change _ = (D.shiftOrbitSubgroupFunctor N).map (eqToHom _) ≫ _
        rw [eqToHom_map]
        simp_rw [← shiftOrbitCategory_comp_eq]
        simp
        simp only [← Category.assoc]
        rw [cancel_mono, cancel_mono, cancel_mono]
        simpa using dcongr_arg
          (fun a : G ⧸ N ↦
            (ShiftOrbitCategory.objectShiftIso X
              (Additive.ofMul
                (normalQuotientRepresentative N a))).inv)
          (mul_assoc q r s)

set_option backward.isDefEq.respectTransparency false in
/-- The coherent residual `G / N`-indexed translation core on the
`N`-shift-orbit category. -/
noncomputable def shiftOrbitResidualCore
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftMkCore (ShiftOrbitCategory C (Additive N))
      (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact
    { F := fun a ↦ D.shiftOrbitNormalTranslateFunctor N
        (normalQuotientRepresentative N a.toMul)
      zero := D.shiftOrbitResidualUnitIso N
      add := fun a b ↦ D.shiftOrbitResidualAddIso N a.toMul b.toMul
      assoc_hom_app := by
        intro m₁ m₂ m₃ X
        exact D.shiftOrbitResidual_assoc_hom_app N
          m₁ m₂ m₃ (show C from X)
      zero_add_hom_app := by
        intro n X
        exact D.shiftOrbitResidual_zero_add_hom_app N
          n (show C from X)
      add_zero_hom_app := by
        intro n X
        exact D.shiftOrbitResidual_add_zero_hom_app N
          n (show C from X) }

/-- The residual `G / N` shift on the `N`-shift-orbit category. -/
@[implicit_reducible]
noncomputable def shiftOrbitResidualHasShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    HasShift (ShiftOrbitCategory C (Additive N))
      (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact hasShiftMk _ _ (D.shiftOrbitResidualCore N)

/-- Every functor in the residual quotient shift is additive. -/
theorem shiftOrbitResidualAdditiveShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := D.shiftOrbitResidualHasShift N
    ∀ a : Additive (G ⧸ N),
      (shiftFunctor (ShiftOrbitCategory C (Additive N)) a).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := D.shiftOrbitResidualHasShift N
  intro a
  change (D.shiftOrbitNormalTranslateFunctor N
    (normalQuotientRepresentative N a.toMul)).Additive
  infer_instance

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
