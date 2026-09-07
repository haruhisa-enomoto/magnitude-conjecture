import MagnitudeConjecture.Algebra.RightModuleIyamaEssentialSurjectivity

/-!
# The primitive poset-space equivalence

The concrete restricted Yoneda functor is faithful and full, and Iyama
saturation proves that its image is closed under subobjects.  The distinguished
sink represents full-support envelopes, so the functor is essentially
surjective and hence an equivalence.  No realization hypothesis remains.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

namespace PrimitiveProjectivePosetData

/-- Fullness, faithfulness, and the saturated-image realization assemble the
literal equivalence data for restricted Yoneda. -/
theorem equivalenceData [IsAlgClosed k]
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1) :
    PosetSpace.RepresentableData.EquivalenceData R.representableData where
  full := fun f ↦ R.representable_full H |>.map_surjective f
  faithful := fun _ _ h ↦ R.representable_faithful.map_injective h
  essSurj := R.representable_essentiallySurjective H hsink

/-- The literal primitive factor is equivalent to the category of finite
`T`-spaces. -/
def equivalence [IsAlgClosed k]
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1) :
    S.FactorCategory K ≌ PosetSpace.Obj k T :=
  (R.equivalenceData H hsink).equivalence

/-- Every selected indecomposable becomes a Schur `T`-space and its total
dimension is its primitive multiplicity. -/
def schurRealizationFamily [IsAlgClosed k]
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1) :
    PosetSpace.SchurRealizationFamily k T (S.SurvivingLabel K) where
  obj := fun x ↦ R.representableData.obj (S.factorObject K x)
  schur := fun x ↦
    (R.equivalenceData H hsink).obj_isSchur
      (R.exists_source_hom_ne_zero x)
      (fun g ↦ by
        obtain ⟨a, ha⟩ := H.factorObject_endomorphism_eq_smul_id S K x g
        exact ⟨a, ha.symm⟩)
  multiplicity := fun x ↦ D.multiplicity x.1
  multiplicity_eq_finrank := fun x ↦
    (R.finrank_obj_factorObject x).symm

end PrimitiveProjectivePosetData

namespace PrimitiveDirectedBoundaryData

/-- The canonical primitive representable functor is unconditionally the
literal poset-space equivalence. -/
def posetSpaceEquivalence [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData D) :
    S.FactorCategory K ≌ PosetSpace.Obj k B.ProjectivePoset :=
  B.projectivePosetData.equivalence B.acyclic
    (B.injective_multiplicity_eq_one D.sinkInjectiveLabel)

/-- Canonical Schur realization family for the primitive factor; its
multiplicity function is definitionally the manuscript's `d_X`. -/
def schurRealizationFamily [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData D) :
    PosetSpace.SchurRealizationFamily
      k B.ProjectivePoset (S.SurvivingLabel K) :=
  B.projectivePosetData.schurRealizationFamily B.acyclic
    (B.injective_multiplicity_eq_one D.sinkInjectiveLabel)

end PrimitiveDirectedBoundaryData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
