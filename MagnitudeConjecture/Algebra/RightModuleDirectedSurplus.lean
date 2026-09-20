import MagnitudeConjecture.Algebra.RightModuleDirectedQuotient

/-! # Nonnegative surplus by directed primitive deletion -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- A representation-directed algebra has nonnegative AR surplus. The proof
uses primitive deletion and induction on the number of indecomposables. -/
theorem ambientARSurplus_nonnegative_of_directed
    (S : FiniteIndecomposableSkeleton k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms) : 0 ≤ S.ambientARSurplus := by
  classical
  revert H
  induction hn : S.n using Nat.strong_induction_on generalizing A S with
  | h n ih =>
    intro H
    by_cases hz : S.n = 0
    · haveI : IsEmpty (Fin S.n) := ⟨fun i ↦ by have hi := i.isLt; omega⟩
      simp [ambientARSurplus, ARCount.surplus, ARCount.eulerMagnitude,
        ARCount.vertexCount, ARCount.arrowCount, ARCount.meshCount, ARCount.projectiveCount]
    · let T := S.moritaBasicSkeleton
      have HT : T.HasAcyclicNonzeroNonisomorphisms :=
        S.moritaBasicSkeleton_hasAcyclicNonzeroNonisomorphisms H
      let P := S.moritaBasicPrimitiveProjectivePresentation
      have hT : RightModule.IsRepresentationFinite k S.moritaBasicAlgebra :=
        ⟨T.n, T.obj, fun i ↦ ⟨T.obj_finite i, T.obj_indecomposable i⟩, T.complete⟩
      obtain ⟨p, _, _⟩ := T.exists_projectiveLabel_hom_ne_zero
        ⟨0, by change 0 < S.n; omega⟩
      let D := P.primitive p
      letI : IsNoetherianRing (RightModule.primitiveQuotientAlgebra (P.idempotent p))ᵐᵒᵖ :=
        IsNoetherianRing.of_finite k _
      let Q := T.primitiveQuotientFiniteIndecomposableSkeleton D
      have hQlt : Q.n < n := by
        rw [← hn]
        change Nat.card (T.PrimitiveQuotientLabel D) < T.n
        simpa only [Nat.card_fin] using
          (Finite.card_subtype_lt (T.primitiveSource_not_mem_primitiveKilledLabels D))
      have HQ : Q.HasAcyclicNonzeroNonisomorphisms :=
        T.primitiveQuotientFinite_hasAcyclicNonzeroNonisomorphisms HT D
      have hQ : 0 ≤ Q.ambientARSurplus := ih Q.n hQlt Q rfl HQ
      have hle : Q.ambientARSurplus ≤ T.ambientARSurplus := by
        rw [T.primitiveQuotientFinite_ambientARSurplus_eq D HT]
        exact T.primitiveQuotientARSurplus_le_ambientARSurplus P p hT HT
      rw [← S.ambientARSurplus_moritaBasicSkeleton]
      exact hQ.trans hle

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
