import MagnitudeConjecture.CategoryTheory.DeckOrbitNormalTranslateLinear
import MagnitudeConjecture.CategoryTheory.OrbitPushdownDescent
import MagnitudeConjecture.CategoryTheory.ShiftOrbitResidualShift

/-!
# Residual descent of the subgroup orbit functor

For a normal subgroup `N ◁ G`, extension by zero from the `N`-shift-orbit
category to the `G`-shift-orbit category commutes coherently with the residual
`G / N` shift when the target is trivially shifted.  It therefore descends
through the residual shift-orbit category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK

variable {k : Type uK} [CommSemiring k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The map of the subgroup orbit functor is literally extension by zero in
deck degree. -/
theorem shiftOrbitSubgroupFunctor_map_eq
    (N : Subgroup G)
    {X Y : letI := D.hasShift
      letI := D.additiveShift
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitCategory C (Additive N)}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      X ⟶ Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitSubgroupFunctor N).map f =
      D.shiftOrbitSubgroupMap N (show C from X) (show C from Y) f := by
  rfl

/-- Extension by zero is a linear functor between the subgroup and ambient
shift-orbit categories. -/
instance shiftOrbitSubgroupFunctor_linear (N : Subgroup G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    (D.shiftOrbitSubgroupFunctor N).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  constructor
  intro X Y f r
  exact D.shiftOrbitSubgroupMap_smul N r f

/-- The subgroup inclusion commutes with a fixed residual quotient shift when
the ambient orbit category is given the trivial quotient shift. -/
noncomputable def shiftOrbitSubgroupResidualCommShiftIso
    (N : Subgroup G) [N.Normal] (a : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := trivialHasShift
      (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
    shiftFunctor (ShiftOrbitCategory C (Additive N)) a ⋙
        D.shiftOrbitSubgroupFunctor N ≅
      D.shiftOrbitSubgroupFunctor N ⋙
        shiftFunctor (ShiftOrbitCategory C (Additive G)) a := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := trivialHasShift
    (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
  let g := normalQuotientRepresentative N a.toMul
  refine NatIso.ofComponents
    (fun X ↦ (ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g)).symm) (naturality := ?_)
  intro X Y f
  change D.shiftOrbitSubgroupMap N _ _
      (D.shiftOrbitNormalTranslateMap N g f) ≫
        (ShiftOrbitCategory.objectShiftIso
          (show C from Y) (Additive.ofMul g)).inv =
    (ShiftOrbitCategory.objectShiftIso
        (show C from X) (Additive.ofMul g)).inv ≫
      D.shiftOrbitSubgroupMap N _ _ f
  rw [D.shiftOrbitSubgroupMap_normalTranslateMap]
  simp [shiftOrbitAmbientConjugate, Category.assoc]

/-- The residual commutation isomorphisms satisfy the zero and addition
coherence laws. -/
@[implicit_reducible]
noncomputable def shiftOrbitSubgroupResidualCommShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := trivialHasShift
      (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
    (D.shiftOrbitSubgroupFunctor N).CommShift (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := trivialHasShift
    (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
  refine
    { commShiftIso := D.shiftOrbitSubgroupResidualCommShiftIso N
      commShiftIso_zero := ?_
      commShiftIso_add := ?_ }
  · apply Iso.ext
    apply NatTrans.ext
    funext X
    have hunit := D.shiftOrbitSubgroupMap_residualUnitHom N
      (show C from X)
    simp only [Functor.CommShift.isoZero_hom_app]
    rw [(D.shiftOrbitResidualCore N).shiftFunctorZero_eq,
      (trivialShiftMkCore
        (ShiftOrbitCategory C (Additive G))
        (Additive (G ⧸ N))).shiftFunctorZero_eq]
    dsimp [shiftOrbitSubgroupResidualCommShiftIso,
      shiftOrbitResidualCore, trivialShiftMkCore]
    simp only [shiftOrbitResidualCore, ShiftMkCore.shiftFunctor_eq,
      Iso.refl_inv, NatTrans.id_app]
    rw [D.shiftOrbitSubgroupFunctor_map_eq]
    erw [Category.comp_id]
    exact hunit.symm
  · intro a b
    apply Iso.ext
    apply NatTrans.ext
    funext X
    have hadd := D.shiftOrbitSubgroupMap_residualAddHom N
      a.toMul b.toMul (show C from X)
    simp only [Functor.CommShift.isoAdd_hom_app]
    rw [(D.shiftOrbitResidualCore N).shiftFunctorAdd_eq,
      (trivialShiftMkCore
        (ShiftOrbitCategory C (Additive G))
        (Additive (G ⧸ N))).shiftFunctorAdd_eq]
    dsimp [shiftOrbitSubgroupResidualCommShiftIso,
      shiftOrbitResidualCore, trivialShiftMkCore]
    simp only [trivialShiftMkCore, ShiftMkCore.shiftFunctor_eq,
      shiftOrbitResidualCore, Functor.id_map,
      Functor.rightUnitor_hom_app]
    rw [D.shiftOrbitSubgroupFunctor_map_eq]
    erw [Category.comp_id]
    simp only [toMul_add]
    dsimp only [shiftOrbitNormalTranslateFunctor, Functor.comp_obj]
    erw [hadd]
    let eab := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul
        (normalQuotientRepresentative N (a.toMul * b.toMul)))
    let ea := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul
        (normalQuotientRepresentative N a.toMul))
    let eb := ShiftOrbitCategory.objectShiftIso
      ((shiftFunctor C (Additive.ofMul
        (normalQuotientRepresentative N a.toMul))).obj (show C from X))
      (Additive.ofMul (normalQuotientRepresentative N b.toMul))
    change eab.inv = ((eab.inv ≫ ea.hom) ≫ eb.hom) ≫ eb.inv ≫ ea.inv
    simp

/-- Every nonskeletal residual shift functor is linear. -/
theorem shiftOrbitResidualLinearShift (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    ∀ a : Additive (G ⧸ N),
      (shiftFunctor (ShiftOrbitCategory C (Additive N)) a).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  intro a
  change (D.shiftOrbitNormalTranslateFunctor N
    (normalQuotientRepresentative N a.toMul)).Linear k
  infer_instance

/-- Extension by zero descends through the residual quotient shift-orbit
category to the ambient `G`-shift-orbit category. -/
noncomputable def shiftOrbitResidualFlattenFunctor
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    ShiftOrbitCategory (ShiftOrbitCategory C (Additive N))
        (Additive (G ⧸ N)) ⥤
      ShiftOrbitCategory C (Additive G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := trivialHasShift
    (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
  letI := D.shiftOrbitSubgroupResidualCommShift N
  exact shiftOrbitDescendedFunctor (k := k)
    (A := Additive (G ⧸ N)) (D.shiftOrbitSubgroupFunctor N)

instance shiftOrbitResidualFlattenFunctor_additive
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    (D.shiftOrbitResidualFlattenFunctor (k := k) N).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := trivialHasShift
    (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
  letI := D.shiftOrbitSubgroupResidualCommShift N
  change (shiftOrbitDescendedFunctor (k := k)
    (A := Additive (G ⧸ N)) (D.shiftOrbitSubgroupFunctor N)).Additive
  infer_instance

instance shiftOrbitResidualFlattenFunctor_linear
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    (D.shiftOrbitResidualFlattenFunctor (k := k) N).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := trivialHasShift
    (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
  letI := D.shiftOrbitSubgroupResidualCommShift N
  change (shiftOrbitDescendedFunctor (k := k)
    (A := Additive (G ⧸ N)) (D.shiftOrbitSubgroupFunctor N)).Linear k
  infer_instance

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
