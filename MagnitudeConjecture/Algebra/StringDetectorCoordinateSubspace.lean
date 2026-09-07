import MagnitudeConjecture.Algebra.StringDetectorSelfPath

/-!
# Coordinate subspaces in literal string modules

The displayed arrow maps of a literal string module are partial injections on
the position basis.  Consequently images and preimages of coordinate
subspaces are again coordinate subspaces.  This file propagates that fact
through the Butler--Ringel boundary filters and detector operations.

The resulting closure under individual coordinate parts is the linear-algebra
bridge from detector vectors to the word-position occurrence calculation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

namespace Word

/-- A subspace of a position space is coordinate when it contains every
individual coordinate part of each of its elements. -/
def IsCoordinateSubspace (D : Word R) {x : Q}
    (U : Submodule k (D.Space x)) : Prop :=
  ∀ v, v ∈ U → ∀ i : D.PositionAt x,
    Finsupp.single i (v i) ∈ U

/-- A vector belongs to a subspace once all of its individual coordinate
parts do. -/
theorem mem_of_all_coordinateParts_mem (D : Word R) {x : Q}
    (U : Submodule k (D.Space x)) (v : D.Space x)
    (hparts : ∀ i : D.PositionAt x, Finsupp.single i (v i) ∈ U) :
    v ∈ U := by
  rw [← Finsupp.sum_single v]
  exact Submodule.sum_mem U fun i _ ↦ hparts i

theorem isCoordinateSubspace_bot (D : Word R) (x : Q) :
    D.IsCoordinateSubspace (⊥ : Submodule k (D.Space x)) := by
  intro v hv i
  rw [Submodule.mem_bot] at hv
  subst v
  simp

theorem isCoordinateSubspace_top (D : Word R) (x : Q) :
    D.IsCoordinateSubspace (⊤ : Submodule k (D.Space x)) := by
  intro _ _ _
  trivial

theorem IsCoordinateSubspace.inf (D : Word R) {x : Q}
    {U V : Submodule k (D.Space x)}
    (hU : D.IsCoordinateSubspace U) (hV : D.IsCoordinateSubspace V) :
    D.IsCoordinateSubspace (U ⊓ V) := by
  intro v hv i
  exact ⟨hU v hv.1 i, hV v hv.2 i⟩

theorem IsCoordinateSubspace.sup (D : Word R) {x : Q}
    {U V : Submodule k (D.Space x)}
    (hU : D.IsCoordinateSubspace U) (hV : D.IsCoordinateSubspace V) :
    D.IsCoordinateSubspace (U ⊔ V) := by
  intro v hv i
  rcases Submodule.mem_sup.mp hv with ⟨w, hw, z, hz, hwz⟩
  rw [← hwz, Finsupp.add_apply, Finsupp.single_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (hU w hw i))
    (Submodule.mem_sup_right (hV z hz i))

/-- Direct image under a displayed arrow preserves coordinate subspaces. -/
theorem IsCoordinateSubspace.map_arrowLinearMap (D : Word R)
    {x y : Q} {U : Submodule k (D.Space x)}
    (hU : D.IsCoordinateSubspace U) (a : x ⟶ y) :
    D.IsCoordinateSubspace (U.map (D.arrowLinearMap a)) := by
  classical
  intro v hv j
  rcases hv with ⟨w, hw, rfl⟩
  by_cases hj : ∃ i : D.PositionAt x, D.ArrowStep a i j
  · let i := Classical.choose hj
    have hij : D.ArrowStep a i j := Classical.choose_spec hj
    refine ⟨Finsupp.single i (w i), hU w hw i, ?_⟩
    rw [D.arrowLinearMap_single,
      D.arrowOnBasis_eq_single_of_step a i j hij,
      D.arrowLinearMap_apply_of_step a w i j hij]
    exact Finsupp.smul_single_one j (w i)
  · rw [D.arrowLinearMap_apply_eq_zero_of_not_exists_source a w j hj]
    simp

/-- Preimage under a displayed arrow preserves coordinate subspaces. -/
theorem IsCoordinateSubspace.comap_arrowLinearMap (D : Word R)
    {x y : Q} {U : Submodule k (D.Space y)}
    (hU : D.IsCoordinateSubspace U) (a : x ⟶ y) :
    D.IsCoordinateSubspace (U.comap (D.arrowLinearMap a)) := by
  classical
  intro v hv i
  change D.arrowLinearMap a v ∈ U at hv
  change D.arrowLinearMap a (Finsupp.single i (v i)) ∈ U
  by_cases hi : ∃ j : D.PositionAt y, D.ArrowStep a i j
  · let j := Classical.choose hi
    have hij : D.ArrowStep a i j := Classical.choose_spec hi
    have hpart := hU (D.arrowLinearMap a v) hv j
    rw [D.arrowLinearMap_apply_of_step a v i j hij] at hpart
    rw [D.arrowLinearMap_single,
      D.arrowOnBasis_eq_single_of_step a i j hij]
    simpa only [Finsupp.smul_single_one] using hpart
  · rw [D.arrowLinearMap_single,
      D.arrowOnBasis_eq_zero_of_not_exists a i hi, smul_zero]
    exact U.zero_mem

/-- Taking an individual coordinate part commutes with membership after
transport across one signed arrow in a literal string module. -/
theorem signedArrowSubspace_coordinatePart (D : Word R)
    (hmono : IsMonomial R) {x y : Q} (e : SignedArrow x y)
    {U : Submodule k (D.Space x)} (hU : D.IsCoordinateSubspace U)
    (v : D.Space y)
    (hv : v ∈ signedArrowSubspace (D.rightModule hmono) e U)
    (j : D.PositionAt y) :
    Finsupp.single j (v j) ∈
      signedArrowSubspace (D.rightModule hmono) e U := by
  cases e with
  | inl a =>
      simp only [signedArrowSubspace] at hv ⊢
      rw [D.moduleArrowMap_rightModule hmono a] at hv ⊢
      exact (hU.map_arrowLinearMap D a) v hv j
  | inr a =>
      simp only [signedArrowSubspace] at hv ⊢
      rw [D.moduleArrowMap_rightModule hmono a] at hv ⊢
      exact (hU.comap_arrowLinearMap D a) v hv j

/-- Taking an individual coordinate part commutes with membership after
transport along a signed path in a literal string module. -/
theorem signedPathSubspace_coordinatePart (D : Word R)
    (hmono : IsMonomial R) :
    ∀ {x y : Q} (p : SignedPath x y) {U : Submodule k (D.Space x)},
      D.IsCoordinateSubspace U →
        ∀ (v : D.Space y),
          v ∈ signedPathSubspace (D.rightModule hmono) p U →
            ∀ j : D.PositionAt y,
              Finsupp.single j (v j) ∈
                signedPathSubspace (D.rightModule hmono) p U := by
  intro x y p
  induction hlength : p.length using Nat.strong_induction_on generalizing x y with
  | h n ih =>
      cases p with
      | nil =>
          intro U hU v hv j
          rw [signedPathSubspace_nil] at hv ⊢
          exact hU v hv j
      | @cons y z p e =>
          change Q at y
          intro U hU v hv j
          rw [signedPathSubspace_cons] at hv ⊢
          apply D.signedArrowSubspace_coordinatePart hmono e
            (hU := by
              intro w hw i
              apply ih p.length
              · simp only [Quiver.Path.length_cons] at hlength
                omega
              · rfl
              · exact hU
              · exact hw
              )
            v hv j

end Word

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}
variable {u₀ : Q} {t : Bool}

namespace EndpointWord

/-- Every lower boundary filter is coordinate in a literal string module. -/
theorem lowerBoundarySubspace_isCoordinate_rightModule
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t) :
    D.IsCoordinateSubspace
      (lowerBoundarySubspace (D.rightModule P.monomial) C) := by
  classical
  by_cases hinc : Nonempty C.IncomingExtension
  · simp only [lowerBoundarySubspace, hinc, dite_true]
    rw [D.moduleArrowMap_rightModule P.monomial]
    exact (D.isCoordinateSubspace_top _).map_arrowLinearMap D _
  · simp only [lowerBoundarySubspace, hinc, dite_false]
    exact D.isCoordinateSubspace_bot _

/-- Every upper boundary filter is coordinate in a literal string module. -/
theorem upperBoundarySubspace_isCoordinate_rightModule
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t) :
    D.IsCoordinateSubspace
      (upperBoundarySubspace (D.rightModule P.monomial) C) := by
  classical
  by_cases hout : Nonempty C.OutgoingInverseExtension
  · simp only [upperBoundarySubspace, hout, dite_true]
    rw [D.moduleArrowMap_rightModule P.monomial]
    exact (D.isCoordinateSubspace_bot _).comap_arrowLinearMap D _
  · simp only [upperBoundarySubspace, hout, dite_false]
    exact D.isCoordinateSubspace_top _

/-- Every lower word subspace is coordinate in a literal string module. -/
theorem lowerSubspace_isCoordinate_rightModule
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t) :
    D.IsCoordinateSubspace (lowerSubspace (D.rightModule P.monomial) C) := by
  intro v hv i
  exact D.signedPathSubspace_coordinatePart P.monomial C.path
    (C.lowerBoundarySubspace_isCoordinate_rightModule D) v hv i

/-- Every upper word subspace is coordinate in a literal string module. -/
theorem upperSubspace_isCoordinate_rightModule
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t) :
    D.IsCoordinateSubspace (upperSubspace (D.rightModule P.monomial) C) := by
  intro v hv i
  exact D.signedPathSubspace_coordinatePart P.monomial C.path
    (C.upperBoundarySubspace_isCoordinate_rightModule D) v hv i

/-- The detector numerator is coordinate on every literal string module. -/
theorem detectorNumerator_isCoordinate_rightModule
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t) :
    D.IsCoordinateSubspace
      (detectorNumerator (D.rightModule P.monomial) C) := by
  exact (C.oppositeVertex.upperSubspace_isCoordinate_rightModule D).inf D
    (C.upperSubspace_isCoordinate_rightModule D)

/-- The detector denominator is coordinate on every literal string module. -/
theorem detectorDenominator_isCoordinate_rightModule
    (D : Word P.toPresentation.relations) (C : EndpointWord S u₀ t) :
    D.IsCoordinateSubspace
      (detectorDenominator (D.rightModule P.monomial) C) := by
  apply Word.IsCoordinateSubspace.sup D
  · exact (C.oppositeVertex.upperSubspace_isCoordinate_rightModule D).inf D
      (C.lowerSubspace_isCoordinate_rightModule D)
  · exact (C.oppositeVertex.lowerSubspace_isCoordinate_rightModule D).inf D
      (C.upperSubspace_isCoordinate_rightModule D)

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
