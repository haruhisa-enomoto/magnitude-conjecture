import MagnitudeConjecture.Algebra.StringProjectivePathBasis
import MagnitudeConjecture.Algebra.StringArrowRightIdealAction
import MagnitudeConjecture.LinearAlgebra.PiExplicitBasis

/-!
# Incoming-arrow sum data in represented string projectives

Nontrivial surviving paths split according to their final displayed arrow.
This file identifies the corresponding internal sum with the radical of the
represented canonical projective.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- Nontrivial surviving paths ending at a fixed vertex. -/
abbrev PositiveVertexPath (P : StringPresentation k A Q) (y : Q) :=
  {p : P.VertexPath y // p.2.1.length ≠ 0}

/-- Concatenating a left continuation with its displayed final arrow gives
the corresponding nontrivial surviving path. -/
def incomingContinuationToPositiveVertexPath
    (P : StringPresentation k A Q) (y : Q) :
    (Σ a : DisplayedIncomingArrow y,
      P.toSpecialBiserialPresentation.LeftContinuationPath a.2) →
      P.PositiveVertexPath y := by
  rintro ⟨⟨x, a⟩, ⟨⟨z, p⟩, hp⟩⟩
  refine ⟨⟨z, ⟨p.cons a, ?_⟩⟩, by simp⟩
  simpa only [← Quiver.Path.comp_toPath_eq_cons, ← pathMap_comp,
    arrowMap] using hp

/-- The final arrow of a nontrivial path and its preceding segment recover
the unique incoming-arrow continuation index. -/
def positiveVertexPathToIncomingContinuation
    (P : StringPresentation k A Q) (y : Q) :
    P.PositiveVertexPath y →
      (Σ a : DisplayedIncomingArrow y,
        P.toSpecialBiserialPresentation.LeftContinuationPath a.2) := by
  rintro ⟨⟨z, ⟨p, hp⟩⟩, hlen⟩
  cases p with
  | nil => exact (hlen rfl).elim
  | @cons x _ q a =>
      refine ⟨⟨x, a⟩, ⟨⟨z, q⟩, ?_⟩⟩
      simpa only [← Quiver.Path.comp_toPath_eq_cons, ← pathMap_comp,
        arrowMap] using hp

/-- Partitioning a nontrivial surviving path by its final displayed arrow
is a bijection. -/
def incomingContinuationEquivPositiveVertexPath
    (P : StringPresentation k A Q) (y : Q) :
    (Σ a : DisplayedIncomingArrow y,
      P.toSpecialBiserialPresentation.LeftContinuationPath a.2) ≃
      P.PositiveVertexPath y where
  toFun := P.incomingContinuationToPositiveVertexPath y
  invFun := P.positiveVertexPathToIncomingContinuation y
  left_inv := by
    rintro ⟨⟨x, a⟩, ⟨⟨z, p⟩, hp⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨z, ⟨p, hp⟩⟩, hlen⟩
    cases p with
    | nil => exact (hlen rfl).elim
    | cons q a => rfl

/-- Sum the represented arrow ranges ending at `y` inside the represented
canonical projective at `y`. -/
def incomingArrowRangeSumLinearMap
    (P : StringPresentation k A Q) (y : Q) :
    (∀ a : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap a.2)) →ₗ[
        P.quotientCategoryAlgebraᵐᵒᵖ]
      P.representedVertexModule y where
  toFun g := ∑ a, (g a).1
  map_add' g h := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' r g := by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower,
      RingHom.id_apply, Finset.smul_sum]

/-- The coefficient-field version of the incoming-arrow range sum. -/
def incomingArrowRangeSumKLinearMap
    (P : StringPresentation k A Q) (y : Q) :
    (∀ a : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap a.2)) →ₗ[k]
      P.representedVertexModule y :=
  (P.incomingArrowRangeSumLinearMap y).restrictScalars k

/-- The continuation basis in each incoming-arrow coordinate, packaged as a
named dependent family so coordinatewise basis operations need not unfold its
representation-theoretic construction. -/
def incomingArrowModuleBasisFamily
    (P : StringPresentation k A Q) (y : Q)
    (a : DisplayedIncomingArrow y) :
    Module.Basis
      (P.toSpecialBiserialPresentation.LeftContinuationPath a.2) k
      (LinearMap.range (P.representedArrowLinearMap a.2)) :=
  P.representedArrowModuleBasis a.2

/-- The product of the continuation bases is the coefficient-field basis of
the family of incoming represented-arrow ranges. -/
def incomingArrowRangeBasis
    (P : StringPresentation k A Q) (y : Q) :
    Module.Basis
      (Σ a : DisplayedIncomingArrow y,
        P.toSpecialBiserialPresentation.LeftContinuationPath a.2) k
      (∀ a : DisplayedIncomingArrow y,
        LinearMap.range (P.representedArrowLinearMap a.2)) :=
  MagnitudeConjecture.piExplicitBasis
    (P.incomingArrowModuleBasisFamily y)

end StringPresentation

end MagnitudeConjecture.BoundQuiver
