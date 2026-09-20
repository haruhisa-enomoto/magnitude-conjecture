import MagnitudeConjecture.Algebra.RightModuleDirectAntichain
import MagnitudeConjecture.Combinatorics.FiniteWidthTwo

/-! # Zero excess implies one-dimensional Schur poset spaces -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A} {e : A} {D : PrimitiveIdempotentData e}
namespace PrimitiveDirectedBoundaryData

/-- The two-square argument rules out three pairwise incomparable elements. -/
theorem directPoset_no_threeAntichain
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (hz : DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) = 0)
    (a b c : B.ProjectivePoset) : ¬ PosetSpace.IsThreeAntichain a b c := by
  classical
  intro h
  have hF : ∀ x ∈ ({a, b, c} : Finset B.ProjectivePoset),
      ∀ y ∈ ({a, b, c} : Finset B.ProjectivePoset), x ≤ y → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · exact (h.not_ab hxy).elim
    · exact (h.not_ac hxy).elim
    · exact (h.not_ba hxy).elim
    · rfl
    · exact (h.not_bc hxy).elim
    · exact (h.not_ca hxy).elim
    · exact (h.not_cb hxy).elim
    · rfl
  have hcard := B.directAntichain_card_le_two hz {a, b, c} hF
  simpa [h.ne_ab, h.ne_ac, h.ne_bc] using hcard

/-- The sharp direct height, two upper-set squares, and a basis adapted to
two filtrations imply that every Schur poset space is one-dimensional. -/
theorem directSchur_finrank_eq_one_of_excess_zero
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (hz : DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) = 0)
    (X : PosetSpace.Obj k B.ProjectivePoset)
    (hX : PosetSpace.IsSchur k B.ProjectivePoset X) : Module.finrank k X = 1 :=
  PosetSpace.finrank_eq_one_of_isSchur_of_no_threeAntichain X hX
    (B.directPoset_no_threeAntichain hz)

/-- Zero intrinsic excess forces multiplicity one for every actual surviving
indecomposable, using the generated-relations realization. -/
theorem directMultiplicity_eq_one_of_excess_zero
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (hz : DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) = 0)
    (x : S.SurvivingLabel (S.primitiveKilledLabels D)) :
    S.primitiveMultiplicity D x.1 = 1 := by
  let R := B.projectivePosetData
  have hschur := (S.generatedRelationsEquivalenceData B.acyclic D R).obj_isSchur
    (R.exists_source_hom_ne_zero x)
    (fun g ↦ by
      obtain ⟨a, ha⟩ := B.acyclic.factorObject_endomorphism_eq_smul_id
        S (S.primitiveKilledLabels D) x g
      exact ⟨a, ha.symm⟩)
  calc
    S.primitiveMultiplicity D x.1 =
        Module.finrank k (R.representableData.obj (S.factorObject _ x)) :=
      (R.finrank_obj_factorObject x).symm
    _ = 1 := B.directSchur_finrank_eq_one_of_excess_zero hz _ hschur

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
