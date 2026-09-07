import MagnitudeConjecture.Algebra.RightModulePosetPositiveGrading
import MagnitudeConjecture.Algebra.RightModulePrimitiveDirectCount
import MagnitudeConjecture.Algebra.RightModuleSchurianBoundary

/-!
# The representation-theoretic correction in primitive directed deletion

This file combines the two nonnegative terms in the live manuscript's
directed-deletion theorem.  All three quantities are the literal categorical
ones attached to a primitive quotient:

* the intrinsic Euler excess of the strict tau-factor;
* the total increase of intrinsic irreducible-arrow multiplicities; and
* the number of new quotient meshes.

The direct vertex--arrow--mesh count identifies this correction with the
difference of the ambient and primitive-quotient Auslander--Reiten surpluses;
factor positivity and arrow-gain dominance then give monotonicity and the
equality rigidity statement used downstream.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : RightModule.PrimitiveIdempotentData e)

/-- Total irreducible-arrow multiplicity of the literal primitive quotient.
-/
def primitiveQuotientArrowCount : ℕ := by
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Fintype (S.PrimitiveQuotientLabel D) := Fintype.ofFinite _
  exact ∑ source : S.PrimitiveQuotientLabel D,
    ∑ target : S.PrimitiveQuotientLabel D,
      S.primitiveQuotientIrreducibleArrowMultiplicity D source target

/-- The ambient Auslander--Reiten surplus, using the official finite-tau
arrow multiplicities and the categorical projective predicate. -/
def ambientARSurplus : ℤ :=
  @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
    (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData)
    (fun x ↦ Projective (S.fgObj x)) (Classical.decPred _)

/-- The literal primitive quotient's Auslander--Reiten surplus, using its
intrinsic irreducible-arrow dimensions and categorical projectives. -/
def primitiveQuotientARSurplus : ℤ := by
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Fintype (S.PrimitiveQuotientLabel D) := Fintype.ofFinite _
  exact @MagnitudeConjecture.ARCount.surplus
    (S.PrimitiveQuotientLabel D) inferInstance
    (S.primitiveQuotientIrreducibleArrowMultiplicity D)
    (fun x ↦ Projective (S.primitiveQuotientLabelObj D x))
    (Classical.decPred _)

/-- The ambient translation-quiver surplus, expressed through the literal
ambient vertex, projective, and arrow-occurrence counts. -/
def ambientTranslationQuiverSurplus : ℤ :=
  MagnitudeConjecture.DirectedDeletion.translationQuiverSurplus
    (Nat.card (Fin S.n))
    (Nat.card {x : Fin S.n // Projective (S.fgObj x)})
    (Nat.card S.AmbientArrowOccurrence)

/-- The literal primitive quotient's translation-quiver surplus. -/
def primitiveQuotientTranslationQuiverSurplus : ℤ :=
  MagnitudeConjecture.DirectedDeletion.translationQuiverSurplus
    (Nat.card (S.PrimitiveQuotientLabel D))
    (Nat.card {x : S.PrimitiveQuotientLabel D //
      Projective (S.primitiveQuotientLabelObj D x)})
    (S.primitiveQuotientArrowCount D)

omit [IsAlgClosed k] in
/-- The official ambient Auslander--Reiten surplus agrees with its literal
translation-quiver cardinality expression. -/
theorem ambientARSurplus_eq_ambientTranslationQuiverSurplus :
    S.ambientARSurplus = S.ambientTranslationQuiverSurplus := by
  classical
  rw [ambientARSurplus,
    MagnitudeConjecture.DirectedDeletion.surplus_eq_translationQuiverSurplus,
    ambientTranslationQuiverSurplus,
    S.ambientArrowCount_eq_card_ambientArrowOccurrence]
  have hprojectives :
      MagnitudeConjecture.ARCount.projectiveCount
          (fun x : Fin S.n ↦ Projective (S.fgObj x)) =
        (Nat.card {x : Fin S.n // Projective (S.fgObj x)} : ℤ) := by
    rw [MagnitudeConjecture.ARCount.projectiveCount,
      Nat.card_eq_fintype_card]
  rw [hprojectives]
  simp only [MagnitudeConjecture.ARCount.vertexCount,
    Nat.card_eq_fintype_card]

omit [IsAlgClosed k] in
/-- The intrinsic primitive-quotient Auslander--Reiten surplus agrees with
its literal translation-quiver cardinality expression. -/
theorem primitiveQuotientARSurplus_eq_primitiveQuotientTranslationQuiverSurplus :
    S.primitiveQuotientARSurplus D =
      S.primitiveQuotientTranslationQuiverSurplus D := by
  classical
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Fintype (S.PrimitiveQuotientLabel D) := Fintype.ofFinite _
  rw [primitiveQuotientARSurplus,
    MagnitudeConjecture.DirectedDeletion.surplus_eq_translationQuiverSurplus,
    primitiveQuotientTranslationQuiverSurplus]
  have hvertices :
      MagnitudeConjecture.ARCount.vertexCount
          (ι := S.PrimitiveQuotientLabel D) =
        (Nat.card (S.PrimitiveQuotientLabel D) : ℤ) := by
    simp only [MagnitudeConjecture.ARCount.vertexCount,
      Nat.card_eq_fintype_card]
  have hprojectives :
      MagnitudeConjecture.ARCount.projectiveCount
          (fun x : S.PrimitiveQuotientLabel D ↦
            Projective (S.primitiveQuotientLabelObj D x)) =
        (Nat.card {x : S.PrimitiveQuotientLabel D //
          Projective (S.primitiveQuotientLabelObj D x)} : ℤ) := by
    simp only [MagnitudeConjecture.ARCount.projectiveCount,
      Nat.card_eq_fintype_card]
  have harrows :
      MagnitudeConjecture.ARCount.arrowCount
          (S.primitiveQuotientIrreducibleArrowMultiplicity D) =
        (S.primitiveQuotientArrowCount D : ℤ) := by
    unfold MagnitudeConjecture.ARCount.arrowCount
      primitiveQuotientArrowCount
    norm_cast
  rw [hvertices, hprojectives, harrows]

/-- The live manuscript's actual correction
`epsilon(Q) + c - r` for a primitive deletion. -/
def primitiveDirectedDeletionCost : ℤ :=
  MagnitudeConjecture.DirectedDeletion.deletionCost
    (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
      (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)))
    (S.primitiveTotalArrowGain D : ℤ)
    (Nat.card (S.PrimitiveNewRightMeshEndpoint D) : ℤ)

omit [IsAlgClosed k] in
/-- The manuscript's count
`epsilon(Q) = 2 q - a_H - p - 1`, written with the literal vertex, arrow,
and tau-projective counts of the strict primitive factor. -/
theorem primitiveFactorIntrinsicEulerExcess_eq :
    MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
        (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
          (S.factorFiniteTauCategoryData
            (S.primitiveKilledLabels D))) =
      2 * MagnitudeConjecture.ARCount.vertexCount
          (ι := S.SurvivingLabel (S.primitiveKilledLabels D)) -
        MagnitudeConjecture.ARCount.arrowCount
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            (S.factorFiniteTauCategoryData
              (S.primitiveKilledLabels D)).toFiniteRightTauCategoryData) -
        MagnitudeConjecture.ARCount.projectiveCount
          (S.factorFiniteTauCategoryData
            (S.primitiveKilledLabels D)).IsProjective - 1 := by
  classical
  let T := S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)
  have hpartition :=
    MagnitudeConjecture.ARCount.vertexCount_eq_projectiveCount_add_meshCount
      T.IsProjective
  dsimp only [T] at hpartition
  rw [MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess,
    MagnitudeConjecture.FiniteTauMatrix.meshMatrix,
    MagnitudeConjecture.ARCount.matrixTotal_meshMatrix_eq_eulerMagnitude,
    MagnitudeConjecture.ARCount.eulerMagnitude]
  change _ =
    2 * MagnitudeConjecture.ARCount.vertexCount
        (ι := S.SurvivingLabel (S.primitiveKilledLabels D)) -
      _ - _ - 1
  omega

/-- The quotient arrow count is the ambient internal count plus the total
gain `c`. -/
theorem primitiveQuotientArrowCount_eq_internal_add_gain
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.primitiveQuotientArrowCount D =
      Nat.card (S.PrimitiveKilledInternalArrow D) +
        S.primitiveTotalArrowGain D := by
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  unfold primitiveQuotientArrowCount
  rw [S.sum_primitiveQuotientIrreducibleArrowMultiplicity_eq_ambient_add_gain
    D, ← S.card_primitiveKilledInternalArrow_eq_sum_ambientMultiplicity
      D H]

omit [IsAlgClosed k] in
/-- The strict factor's intrinsic excess in the literal direct-count
variables `q`, `a_H`, and `p`. -/
theorem primitiveFactorIntrinsicEulerExcess_eq_directCount :
    MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
        (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
          (S.factorFiniteTauCategoryData
            (S.primitiveKilledLabels D))) =
      2 * (Nat.card
          (S.SurvivingLabel (S.primitiveKilledLabels D)) : ℤ) -
        (Nat.card (S.PrimitiveSurvivingInternalArrow D) : ℤ) -
        (Nat.card
          (S.FactorProjectiveLabel
            (S.primitiveKilledLabels D)) : ℤ) - 1 := by
  classical
  rw [S.primitiveFactorIntrinsicEulerExcess_eq D,
    S.factorArrowCount_eq_card_primitiveSurvivingInternalArrow D]
  simp only [MagnitudeConjecture.ARCount.vertexCount,
    MagnitudeConjecture.ARCount.projectiveCount,
    Nat.card_eq_fintype_card]

/-- The live manuscript's exact identity
`sigma(A) - sigma(A/AeA) = epsilon(Q) + c - r`, for the literal ambient and
primitive-quotient translation-quiver counts. -/
theorem ambientTranslationQuiverSurplus_sub_primitiveQuotientTranslationQuiverSurplus_eq_cost
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput (P.primitive p))) :
    S.ambientTranslationQuiverSurplus -
        S.primitiveQuotientTranslationQuiverSurplus (P.primitive p) =
      S.primitiveDirectedDeletionCost (P.primitive p) := by
  let D := P.primitive p
  have hverticesNat := S.card_ambientVertex_eq_quotient_add_factor D
  have hsimplesNat :=
    P.card_ambientProjective_eq_primitiveQuotientProjective_add_one H p
  have hambientArrowsNat :=
    S.card_ambientArrowOccurrence_eq_internal_add_crossing D
  have hquotientArrowsNat :=
    S.primitiveQuotientArrowCount_eq_internal_add_gain D H
  have hfactor := S.primitiveFactorIntrinsicEulerExcess_eq_directCount D
  have hnewMeshes :=
    S.card_primitiveNewRightMeshEndpoint_eq_crossing_sub_projectiveRemainder
      P p H E
  have hvertices :
      (Nat.card (Fin S.n) : ℤ) =
        Nat.card (S.PrimitiveQuotientLabel D) +
          Nat.card (S.SurvivingLabel (S.primitiveKilledLabels D)) := by
    exact_mod_cast hverticesNat
  have hsimples :
      (Nat.card {x : Fin S.n // Projective (S.fgObj x)} : ℤ) =
        Nat.card {x : S.PrimitiveQuotientLabel D //
          Projective (S.primitiveQuotientLabelObj D x)} + 1 := by
    exact_mod_cast hsimplesNat
  have hambientArrows :
      (Nat.card S.AmbientArrowOccurrence : ℤ) =
        Nat.card (S.PrimitiveKilledInternalArrow D) +
          Nat.card (S.PrimitiveSurvivingInternalArrow D) +
            Nat.card (S.PrimitiveCrossingArrow D) := by
    exact_mod_cast hambientArrowsNat
  have hquotientArrows :
      (S.primitiveQuotientArrowCount D : ℤ) =
        Nat.card (S.PrimitiveKilledInternalArrow D) +
          S.primitiveTotalArrowGain D := by
    exact_mod_cast hquotientArrowsNat
  simpa only [ambientTranslationQuiverSurplus,
    primitiveQuotientTranslationQuiverSurplus,
    primitiveDirectedDeletionCost] using
    MagnitudeConjecture.DirectedDeletion.translationQuiverSurplus_difference_eq_deletionCost
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData
          (S.primitiveKilledLabels D)))
      (Nat.card (Fin S.n))
      (Nat.card {x : Fin S.n // Projective (S.fgObj x)})
      (Nat.card S.AmbientArrowOccurrence)
      (Nat.card (S.PrimitiveQuotientLabel D))
      (Nat.card {x : S.PrimitiveQuotientLabel D //
        Projective (S.primitiveQuotientLabelObj D x)})
      (S.primitiveQuotientArrowCount D)
      (Nat.card (S.SurvivingLabel (S.primitiveKilledLabels D)))
      (Nat.card (S.PrimitiveKilledInternalArrow D))
      (Nat.card (S.PrimitiveSurvivingInternalArrow D))
      (Nat.card (S.PrimitiveCrossingArrow D))
      (Nat.card
        (S.FactorProjectiveLabel (S.primitiveKilledLabels D)))
      (S.primitiveTotalArrowGain D)
      (Nat.card (S.PrimitiveNewRightMeshEndpoint D))
      hvertices hsimples hambientArrows hquotientArrows hfactor hnewMeshes

/-- The structural direct-deletion identity once the multiplicity-coordinate
estimate has been supplied. -/
private theorem ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost_ofCoordinateEstimate
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput (P.primitive p))) :
    S.ambientARSurplus -
        S.primitiveQuotientARSurplus (P.primitive p) =
      S.primitiveDirectedDeletionCost (P.primitive p) := by
  rw [S.ambientARSurplus_eq_ambientTranslationQuiverSurplus,
    S.primitiveQuotientARSurplus_eq_primitiveQuotientTranslationQuiverSurplus]
  exact
    S.ambientTranslationQuiverSurplus_sub_primitiveQuotientTranslationQuiverSurplus_eq_cost
      P p H E

/-- Nonnegativity of the primitive-deletion correction from constructed
coordinate and boundary data. -/
private theorem primitiveDirectedDeletionCost_nonnegative_ofBoundaryData
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    0 ≤ S.primitiveDirectedDeletionCost D := by
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hFactor := B.standardFactorIntrinsicEulerExcess_nonnegative
  have hGainNat :=
    S.card_primitiveNewRightMeshEndpoint_le_primitiveTotalArrowGain
      D H he E B
  have hGain :
      (Nat.card (S.PrimitiveNewRightMeshEndpoint D) : ℤ) ≤
        (S.primitiveTotalArrowGain D : ℤ) := by
    exact_mod_cast hGainNat
  simp only [primitiveDirectedDeletionCost,
    MagnitudeConjecture.DirectedDeletion.deletionCost]
  omega

/-- Structural monotonicity from constructed coordinate and boundary data. -/
private theorem primitiveQuotientARSurplus_le_ambientARSurplus_ofBoundaryData
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput (P.primitive p)))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput (P.primitive p))) :
    S.primitiveQuotientARSurplus (P.primitive p) ≤
      S.ambientARSurplus := by
  have hcost := primitiveDirectedDeletionCost_nonnegative_ofBoundaryData
    (S := S)
    (P.primitive p) H (P.primitive p).idempotent E B
  rw [← ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost_ofCoordinateEstimate
    (S := S)
    P p H E] at hcost
  omega

/-- Structural equality decomposition from constructed coordinate and
boundary data. -/
private theorem primitiveDirectedDeletionCost_eq_zero_iff_ofBoundaryData
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    S.primitiveDirectedDeletionCost D = 0 ↔
      MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
          (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
            (S.factorFiniteTauCategoryData
              (S.primitiveKilledLabels D))) = 0 ∧
        S.primitiveTotalArrowGain D =
          Nat.card (S.PrimitiveNewRightMeshEndpoint D) := by
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hFactor := B.standardFactorIntrinsicEulerExcess_nonnegative
  have hGainNat :=
    S.card_primitiveNewRightMeshEndpoint_le_primitiveTotalArrowGain
      D H he E B
  have hGain :
      (Nat.card (S.PrimitiveNewRightMeshEndpoint D) : ℤ) ≤
        (S.primitiveTotalArrowGain D : ℤ) := by
    exact_mod_cast hGainNat
  rw [primitiveDirectedDeletionCost,
    MagnitudeConjecture.DirectedDeletion.equality_iff_zero_factorExcess_and_equal_correction
      _ _ _ hFactor hGain]
  constructor
  · rintro ⟨hzero, heq⟩
    exact ⟨hzero, by exact_mod_cast heq⟩
  · rintro ⟨hzero, heq⟩
    exact ⟨hzero, by exact_mod_cast heq⟩

/-- Structural equality characterization from constructed coordinate and
boundary data. -/
private theorem ambientARSurplus_eq_primitiveQuotientARSurplus_iff_ofBoundaryData
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput (P.primitive p)))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput (P.primitive p))) :
    S.ambientARSurplus =
        S.primitiveQuotientARSurplus (P.primitive p) ↔
      MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
          (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
            (S.factorFiniteTauCategoryData
              (S.primitiveKilledLabels (P.primitive p)))) = 0 ∧
        S.primitiveTotalArrowGain (P.primitive p) =
          Nat.card
            (S.PrimitiveNewRightMeshEndpoint (P.primitive p)) := by
  rw [← sub_eq_zero,
    ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost_ofCoordinateEstimate
      (S := S) P p H E,
    primitiveDirectedDeletionCost_eq_zero_iff_ofBoundaryData (S := S)
      (P.primitive p) H (P.primitive p).idempotent E B]

/-- Structural equality rigidity from constructed coordinate and boundary
data. -/
private theorem primitiveMultiplicity_eq_one_of_primitiveDirectedDeletionCost_eq_zero_ofBoundaryData
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (hzero : S.primitiveDirectedDeletionCost D = 0)
    (X : S.SurvivingLabel (S.primitiveKilledLabels D)) :
    S.primitiveMultiplicity D X.1 = 1 := by
  have hFactorZero :=
    (primitiveDirectedDeletionCost_eq_zero_iff_ofBoundaryData
      (S := S) D H he E B).mp hzero |>.1
  let R := B.schurRealizationFamily
  calc
    S.primitiveMultiplicity D X.1 =
        Module.finrank k (R.obj X) :=
      R.multiplicity_eq_finrank X
    _ = 1 :=
      B.standardFactorSchur_finrank_eq_one_of_intrinsicEulerExcess_eq_zero
        hFactorZero (R.obj X) (R.schur X)

/-- Structural ambient-equality rigidity from constructed coordinate and
boundary data. -/
private theorem primitiveMultiplicity_eq_one_of_ambientARSurplus_eq_primitiveQuotientARSurplus_ofBoundaryData
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput (P.primitive p)))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput (P.primitive p)))
    (hEquality : S.ambientARSurplus =
      S.primitiveQuotientARSurplus (P.primitive p))
    (X : S.SurvivingLabel
      (S.primitiveKilledLabels (P.primitive p))) :
    S.primitiveMultiplicity (P.primitive p) X.1 = 1 := by
  apply
    primitiveMultiplicity_eq_one_of_primitiveDirectedDeletionCost_eq_zero_ofBoundaryData
      (S := S)
    (P.primitive p) H (P.primitive p).idempotent E B
  rw [← ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost_ofCoordinateEstimate
    (S := S)
    P p H E, hEquality, sub_self]

/-- The manuscript's direct-deletion identity
`sigma(A) - sigma(A/AeA) = epsilon(Q) + c - r` for a
representation-directed algebra.  The coordinate estimate is constructed
from the literal middle-support quotient. -/
theorem ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.ambientARSurplus -
        S.primitiveQuotientARSurplus (P.primitive p) =
      S.primitiveDirectedDeletionCost (P.primitive p) :=
  ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost_ofCoordinateEstimate
    (S := S) P p H
      (P.multiplicityCoordinateEstimate hA H (P.primitive p))

/-- The actual primitive-deletion correction is nonnegative for a
representation-directed algebra.  The coordinate and boundary packages are
constructed from the manuscript's hypotheses. -/
theorem primitiveDirectedDeletionCost_nonnegative
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    0 ≤ S.primitiveDirectedDeletionCost D :=
  primitiveDirectedDeletionCost_nonnegative_ofBoundaryData (S := S)
    D H D.idempotent
      (P.multiplicityCoordinateEstimate hA H D)
      (P.primitiveDirectedBoundaryData hA H D)

/-- Primitive directed deletion cannot increase the quotient
Auslander--Reiten surplus.  This is the manuscript-facing local monotonicity
theorem: no coordinate or boundary package is an external hypothesis. -/
theorem primitiveQuotientARSurplus_le_ambientARSurplus
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.primitiveQuotientARSurplus (P.primitive p) ≤
      S.ambientARSurplus :=
  primitiveQuotientARSurplus_le_ambientARSurplus_ofBoundaryData (S := S)
    P p H
      (P.multiplicityCoordinateEstimate hA H (P.primitive p))
      (P.primitiveDirectedBoundaryData hA H (P.primitive p))

/-- Equality in the actual correction separates into vanishing factor excess
and equality between total arrow gain and the number of new meshes. -/
theorem primitiveDirectedDeletionCost_eq_zero_iff
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.primitiveDirectedDeletionCost D = 0 ↔
      MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
          (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
            (S.factorFiniteTauCategoryData
              (S.primitiveKilledLabels D))) = 0 ∧
        S.primitiveTotalArrowGain D =
          Nat.card (S.PrimitiveNewRightMeshEndpoint D) :=
  primitiveDirectedDeletionCost_eq_zero_iff_ofBoundaryData (S := S)
    D H D.idempotent
      (P.multiplicityCoordinateEstimate hA H D)
      (P.primitiveDirectedBoundaryData hA H D)

/-- Equality of the ambient and quotient Auslander--Reiten surpluses is
equivalent to simultaneous vanishing of the factor excess and of the
new-arrow/new-mesh discrepancy. -/
theorem ambientARSurplus_eq_primitiveQuotientARSurplus_iff
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.ambientARSurplus =
        S.primitiveQuotientARSurplus (P.primitive p) ↔
      MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
          (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
            (S.factorFiniteTauCategoryData
              (S.primitiveKilledLabels (P.primitive p)))) = 0 ∧
        S.primitiveTotalArrowGain (P.primitive p) =
          Nat.card
            (S.PrimitiveNewRightMeshEndpoint (P.primitive p)) :=
  ambientARSurplus_eq_primitiveQuotientARSurplus_iff_ofBoundaryData (S := S)
    P p H
      (P.multiplicityCoordinateEstimate hA H (P.primitive p))
      (P.primitiveDirectedBoundaryData hA H (P.primitive p))

/-- Equality in the actual correction forces every object of the strict
primitive factor to have deleted-simple multiplicity one. -/
theorem primitiveMultiplicity_eq_one_of_primitiveDirectedDeletionCost_eq_zero
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hzero : S.primitiveDirectedDeletionCost D = 0)
    (X : S.SurvivingLabel (S.primitiveKilledLabels D)) :
    S.primitiveMultiplicity D X.1 = 1 :=
  primitiveMultiplicity_eq_one_of_primitiveDirectedDeletionCost_eq_zero_ofBoundaryData
    (S := S) D H D.idempotent
      (P.multiplicityCoordinateEstimate hA H D)
      (P.primitiveDirectedBoundaryData hA H D) hzero X

/-- Equality of the ambient and primitive-quotient Auslander--Reiten
surpluses forces every object in the strict primitive factor to have
deleted-simple multiplicity one. -/
theorem primitiveMultiplicity_eq_one_of_ambientARSurplus_eq_primitiveQuotientARSurplus
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hEquality : S.ambientARSurplus =
      S.primitiveQuotientARSurplus (P.primitive p))
    (X : S.SurvivingLabel
      (S.primitiveKilledLabels (P.primitive p))) :
    S.primitiveMultiplicity (P.primitive p) X.1 = 1 :=
  primitiveMultiplicity_eq_one_of_ambientARSurplus_eq_primitiveQuotientARSurplus_ofBoundaryData
    (S := S) P p H
      (P.multiplicityCoordinateEstimate hA H (P.primitive p))
      (P.primitiveDirectedBoundaryData hA H (P.primitive p)) hEquality X

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
