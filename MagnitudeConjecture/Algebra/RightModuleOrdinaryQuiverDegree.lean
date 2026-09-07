import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiverUniverseLift
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Degrees in the ordinary projective quiver

The total numbers of arrows starting and ending at a selected projective are
the sums of the dimensions of the corresponding internal projective-radical
quotients.  Universe lifting the vertex set preserves both stars literally up
to an explicit equivalence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance ordinaryDegreeQuiver : Quiver S.ProjectiveLabel :=
  S.ordinaryQuiver

local instance ordinaryDegreeArrowFintype (x y : S.ProjectiveLabel) :
    Fintype (x ⟶ y) :=
  S.ordinaryArrowFintype x y

/-- The number of ordinary-quiver arrows starting at `x` is the sum of the
dimensions of the internal projective irreducible spaces with first label
`x`. -/
theorem ordinaryStar_card_eq_sum_finrank (x : S.ProjectiveLabel) :
    Nat.card (Quiver.Star x) =
      ∑ y : S.ProjectiveLabel,
        Module.finrank k (S.projectiveIrreducibleHomSpace x y) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro y _
  change Fintype.card
      (ULift.{u} (Fin (Module.finrank k
        (S.projectiveIrreducibleHomSpace x y)))) = _
  rw [Fintype.card_ulift, Fintype.card_fin]

/-- The number of ordinary-quiver arrows ending at `x` is the sum of the
dimensions of the internal projective irreducible spaces with second label
`x`. -/
theorem ordinaryCostar_card_eq_sum_finrank (x : S.ProjectiveLabel) :
    Nat.card (Quiver.Costar x) =
      ∑ y : S.ProjectiveLabel,
        Module.finrank k (S.projectiveIrreducibleHomSpace y x) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro y _
  change Fintype.card
      (ULift.{u} (Fin (Module.finrank k
        (S.projectiveIrreducibleHomSpace y x)))) = _
  rw [Fintype.card_ulift, Fintype.card_fin]

/-- Forgetting the universe lift gives the same ordinary-quiver star. -/
def ordinaryLiftedStarEquiv (x : S.OrdinaryLiftedVertex) :
    Quiver.Star x ≃ Quiver.Star x.down where
  toFun a := ⟨a.1.down, a.2⟩
  invFun a := ⟨ULift.up a.1, a.2⟩
  left_inv := by
    rintro ⟨⟨y⟩, a⟩
    rfl
  right_inv := by
    rintro ⟨y, a⟩
    rfl

/-- Forgetting the universe lift gives the same ordinary-quiver costar. -/
def ordinaryLiftedCostarEquiv (x : S.OrdinaryLiftedVertex) :
    Quiver.Costar x ≃ Quiver.Costar x.down where
  toFun a := ⟨a.1.down, a.2⟩
  invFun a := ⟨ULift.up a.1, a.2⟩
  left_inv := by
    rintro ⟨⟨y⟩, a⟩
    rfl
  right_inv := by
    rintro ⟨y, a⟩
    rfl

/-- The lifted ordinary-quiver outgoing degree has the same dimension-sum
formula as the original quiver. -/
theorem ordinaryLiftedStar_card_eq_sum_finrank
    (x : S.OrdinaryLiftedVertex) :
    Nat.card (Quiver.Star x) =
      ∑ y : S.ProjectiveLabel,
        Module.finrank k
          (S.projectiveIrreducibleHomSpace x.down y) := by
  rw [Nat.card_congr (S.ordinaryLiftedStarEquiv x)]
  exact S.ordinaryStar_card_eq_sum_finrank x.down

/-- The lifted ordinary-quiver incoming degree has the same dimension-sum
formula as the original quiver. -/
theorem ordinaryLiftedCostar_card_eq_sum_finrank
    (x : S.OrdinaryLiftedVertex) :
    Nat.card (Quiver.Costar x) =
      ∑ y : S.ProjectiveLabel,
        Module.finrank k
          (S.projectiveIrreducibleHomSpace y x.down) := by
  rw [Nat.card_congr (S.ordinaryLiftedCostarEquiv x)]
  exact S.ordinaryCostar_card_eq_sum_finrank x.down

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
