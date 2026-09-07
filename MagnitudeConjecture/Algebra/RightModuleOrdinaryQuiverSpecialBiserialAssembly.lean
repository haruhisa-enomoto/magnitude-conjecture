import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiverLiftedPresentation
import MagnitudeConjecture.Algebra.RightModuleOppositeProjectivePresentation

/-!
# Assembling a special-biserial ordinary-quiver presentation

For an explicit system of ordinary-arrow representatives, the two
continuation conditions can be checked before passing to the exact-kernel
quotient: a two-arrow path survives precisely when the corresponding
composite of selected-projective morphisms is nonzero.  Together with the
incoming and outgoing degree bounds supplied by a biserial primitive
projective presentation, these concrete conditions assemble the literal
special-biserial presentation used in the frozen manuscript.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace OrdinaryArrowRepresentatives

/-- At most one displayed arrow can follow any fixed ordinary arrow with
nonzero composite of the selected representatives. -/
def HasRightContinuationBound (D : S.OrdinaryArrowRepresentatives) : Prop :=
  ∀ {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y),
    Nat.card
      {b : Quiver.Star y // D.hom b.2 ≫ D.hom a ≠ 0} ≤ 1

/-- At most one displayed arrow can precede any fixed ordinary arrow with
nonzero composite of the selected representatives. -/
def HasLeftContinuationBound (D : S.OrdinaryArrowRepresentatives) : Prop :=
  ∀ {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y),
    Nat.card
      {c : Quiver.Costar x // D.hom a ≫ D.hom c.2 ≠ 0} ≤ 1

/-- A right two-arrow path in the lifted exact-kernel quotient is nonzero
exactly when the corresponding representative composite is nonzero. -/
theorem lifted_arrowMap_comp_right_ne_zero_iff
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.OrdinaryLiftedVertex} (a : x ⟶ y)
    (b : Quiver.Star y) :
    BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) b.2 ≫
          BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a ≠ 0 ↔
        D.hom b.2 ≫ D.hom a ≠ 0 := by
  let F := S.ordinaryLiftedQuiverQuotientRealization D
  apply not_congr
  constructor
  · intro hzero
    have hmap := congrArg F.map hzero
    rw [F.map_comp, F.map_zero] at hmap
    have hhom := congrArg InducedCategory.Hom.hom hmap
    change
      (F.map (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) b.2) ≫
          F.map (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a)).hom = 0
        at hhom
    rw [InducedCategory.comp_hom,
      S.ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom,
      S.ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom] at hhom
    exact hhom
  · intro hzero
    apply F.zero_of_map_zero
    rw [F.map_comp]
    apply InducedCategory.hom_ext
    change
      (F.map (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) b.2) ≫
          F.map (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a)).hom = 0
    rw [InducedCategory.comp_hom,
      S.ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom,
      S.ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom]
    exact hzero

/-- A left two-arrow path in the lifted exact-kernel quotient is nonzero
exactly when the corresponding representative composite is nonzero. -/
theorem lifted_arrowMap_comp_left_ne_zero_iff
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.OrdinaryLiftedVertex} (a : x ⟶ y)
    (c : Quiver.Costar x) :
    BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a ≫
          BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) c.2 ≠ 0 ↔
        D.hom a ≫ D.hom c.2 ≠ 0 := by
  let F := S.ordinaryLiftedQuiverQuotientRealization D
  apply not_congr
  constructor
  · intro hzero
    have hmap := congrArg F.map hzero
    rw [F.map_comp, F.map_zero] at hmap
    have hhom := congrArg InducedCategory.Hom.hom hmap
    change
      (F.map (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a) ≫
          F.map (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) c.2)).hom = 0
        at hhom
    rw [InducedCategory.comp_hom,
      S.ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom,
      S.ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom] at hhom
    exact hhom
  · intro hzero
    apply F.zero_of_map_zero
    rw [F.map_comp]
    apply InducedCategory.hom_ext
    change
      (F.map (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a) ≫
          F.map (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) c.2)).hom = 0
    rw [InducedCategory.comp_hom,
      S.ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom,
      S.ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom]
    exact hzero

/-- The concrete right-continuation bound descends unchanged through the
universe lift and exact-kernel quotient. -/
theorem lifted_continuation_right_le_one
    (D : S.OrdinaryArrowRepresentatives)
    (hD : D.HasRightContinuationBound)
    {x y : S.OrdinaryLiftedVertex} (a : x ⟶ y) :
    Nat.card
      {b : Quiver.Star y //
        BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) b.2 ≫
            BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a ≠ 0} ≤ 1 := by
  let e := Equiv.subtypeEquiv (S.ordinaryLiftedStarEquiv y)
    (p := fun b ↦
      BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) b.2 ≫
          BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a ≠ 0)
    (q := fun b ↦ D.hom b.2 ≫ D.hom a ≠ 0)
    (fun b ↦ by
      simpa [ordinaryLiftedStarEquiv] using
        D.lifted_arrowMap_comp_right_ne_zero_iff a b)
  rw [Nat.card_congr e]
  exact hD a

/-- The concrete left-continuation bound descends unchanged through the
universe lift and exact-kernel quotient. -/
theorem lifted_continuation_left_le_one
    (D : S.OrdinaryArrowRepresentatives)
    (hD : D.HasLeftContinuationBound)
    {x y : S.OrdinaryLiftedVertex} (a : x ⟶ y) :
    Nat.card
      {c : Quiver.Costar x //
        BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a ≫
            BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) c.2 ≠ 0} ≤ 1 := by
  let e := Equiv.subtypeEquiv (S.ordinaryLiftedCostarEquiv x)
    (p := fun c ↦
      BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a ≫
          BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) c.2 ≠ 0)
    (q := fun c ↦ D.hom a ≫ D.hom c.2 ≠ 0)
    (fun c ↦ by
      simpa [ordinaryLiftedCostarEquiv] using
        D.lifted_arrowMap_comp_left_ne_zero_iff a c)
  rw [Nat.card_congr e]
  exact hD a

variable [IsNoetherianRing A] [IsAlgClosed k]

/-- Biserial primitive projectives and adapted ordinary-arrow representatives
assemble the literal special-biserial presentation of the chosen basic
algebra. -/
noncomputable def liftedSpecialBiserialPresentation
    (P : S.PrimitiveProjectivePresentation) (hP : P.IsBiserial)
    (D : S.OrdinaryArrowRepresentatives)
    (hRight : D.HasRightContinuationBound)
    (hLeft : D.HasLeftContinuationBound) :
    BoundQuiver.SpecialBiserialPresentation
      k S.basicAlgebra S.OrdinaryLiftedVertex := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact
    { toPresentation := S.ordinaryLiftedPresentation D
      arrows_starting_le_two := by
        intro x
        rw [Nat.card_congr (S.ordinaryLiftedStarEquiv x)]
        exact
          S.ordinaryStar_card_le_two_of_primitiveProjectivePresentation_isBiserial
            P hP x.down
      arrows_ending_le_two := by
        intro x
        rw [Nat.card_congr (S.ordinaryLiftedCostarEquiv x)]
        exact P.ordinaryCostar_card_le_two_of_isBiserial hP x.down
      continuation_right_le_one := D.lifted_continuation_right_le_one hRight
      continuation_left_le_one := D.lifted_continuation_left_le_one hLeft }

end OrdinaryArrowRepresentatives

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
