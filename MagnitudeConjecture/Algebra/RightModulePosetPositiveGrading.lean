import MagnitudeConjecture.Algebra.RightModuleTranslationExcess
import MagnitudeConjecture.CategoryTheory.SchurIndecomposable

/-!
# Positive grading transported to Schur poset spaces

The primitive factor is equivalent to the category of finite poset spaces.
Every Schur poset space pulls back to a nonzero object with only scalar
endomorphisms, hence to one selected indecomposable factor label.  Transporting
the concrete standard-factor level along this label gives the positive grading
needed for the realization-length bound.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

namespace PrimitiveDirectedBoundaryData

/-- A Schur poset space pulls back along the primitive equivalence to one
selected indecomposable factor object. -/
theorem exists_standardFactorLabelIso_of_isSchur
    (B : S.PrimitiveDirectedBoundaryData D)
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    ∃ x : S.SurvivingLabel K,
      Nonempty
        ((B.posetSpaceEquivalence.inverse.obj X) ≅ S.factorObject K x) := by
  let E := B.posetSpaceEquivalence
  let Z := E.inverse.obj X
  let eX : E.functor.obj Z ≅ X := by
    simpa [Z] using E.counitIso.app X
  letI : E.functor.Linear k := by
    change B.projectivePosetData.representableData.functor.Linear k
    infer_instance
  have hZ : ¬ IsZero Z := by
    intro hzero
    have hEZ : IsZero (E.functor.obj Z) := E.functor.map_isZero hzero
    have hXzero : IsZero X := hEZ.of_iso eX.symm
    obtain ⟨x, hx⟩ := hX.1
    apply hx
    have hid : (𝟙 X : X ⟶ X) = 0 :=
      (IsZero.iff_id_eq_zero X).1 hXzero
    have happ := congrArg (fun f : X ⟶ X ↦ f.linear x) hid
    simpa using happ
  have hscalar : ∀ f : Z ⟶ Z, ∃ c : k, c • 𝟙 Z = f := by
    intro f
    let q : X ⟶ X :=
      eX.inv ≫ E.functor.map f ≫ eX.hom
    obtain ⟨c, hc⟩ := hX.2 q
    have hq : q = c • 𝟙 X := by
      apply MagnitudeConjecture.PosetSpace.Hom.ext
      exact hc
    have hmap : E.functor.map f = c • 𝟙 (E.functor.obj Z) := by
      calc
        E.functor.map f =
            eX.hom ≫ q ≫ eX.inv := by
          dsimp only [q]
          simp
        _ = eX.hom ≫ (c • 𝟙 X) ≫ eX.inv := by rw [hq]
        _ = c • 𝟙 (E.functor.obj Z) := by simp
    refine ⟨c, E.functor.map_injective ?_⟩
    simpa using hmap.symm
  have hindecomposable : Indecomposable Z :=
    MagnitudeConjecture.CategoryTheory.indecomposable_of_endomorphism_eq_smul_id
      Z hZ hscalar
  exact (S.factorFiniteTauCategoryData K).obj_complete Z hindecomposable

/-- The selected factor label representing a Schur poset space. -/
def standardFactorSchurLabel
    (B : S.PrimitiveDirectedBoundaryData D)
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    S.SurvivingLabel K :=
  Classical.choose (B.exists_standardFactorLabelIso_of_isSchur X hX)

/-- The pullback of a Schur poset space is isomorphic to its selected factor
label. -/
def standardFactorSchurIso
    (B : S.PrimitiveDirectedBoundaryData D)
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    B.posetSpaceEquivalence.inverse.obj X ≅
      S.factorObject K (B.standardFactorSchurLabel X hX) :=
  Classical.choice
    (Classical.choose_spec (B.exists_standardFactorLabelIso_of_isSchur X hX))

/-- The concrete factor level transported to a Schur poset space.  Its value
away from the Schur locus is irrelevant to the positive-grading interface. -/
def standardFactorSchurLevel
    (B : S.PrimitiveDirectedBoundaryData D)
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset) : ℕ := by
  classical
  exact
    if hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X then
      B.standardFactorLevel (B.standardFactorSchurLabel X hX)
    else 0

@[simp]
theorem standardFactorSchurLevel_of_isSchur
    (B : S.PrimitiveDirectedBoundaryData D)
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    B.standardFactorSchurLevel X =
      B.standardFactorLevel (B.standardFactorSchurLabel X hX) := by
  classical
  rw [standardFactorSchurLevel, dif_pos hX]

/-- The concrete standard-factor grading transports across the completed
poset-space equivalence to a positive grading on every Schur poset space. -/
def standardFactorSchurPositiveGrading
    (B : S.PrimitiveDirectedBoundaryData D) :
    MagnitudeConjecture.PosetSpace.PositiveGrading
      (MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
      (MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset)
      B.standardFactorLength where
  level := B.standardFactorSchurLevel
  level_le X hX := by
    rw [B.standardFactorSchurLevel_of_isSchur X hX]
    exact B.standardFactorLevel_le_length _
  lt_of_nonzero_not_isIso {X Y} f hX hY hf hniso := by
    let E := B.posetSpaceEquivalence
    letI : E.functor.Linear k := by
      change B.projectivePosetData.representableData.functor.Linear k
      infer_instance
    letI : E.inverse.Linear k := E.inverseLinear k
    let eX := B.standardFactorSchurIso X hX
    let eY := B.standardFactorSchurIso Y hY
    let g :
        S.factorObject K (B.standardFactorSchurLabel X hX) ⟶
          S.factorObject K (B.standardFactorSchurLabel Y hY) :=
      eX.inv ≫ E.inverse.map f ≫ eY.hom
    have hg : g ≠ 0 := by
      intro hzero
      have hmapzero : E.inverse.map f = 0 := by
        calc
          E.inverse.map f = eX.hom ≫ g ≫ eY.inv := by
            dsimp only [g]
            simp
          _ = 0 := by rw [hzero]; simp
      apply hf
      apply E.inverse.map_injective
      simpa using hmapzero
    have hgniso : ¬ IsIso g := by
      intro hgiso
      letI : IsIso g := hgiso
      have hmapiso : IsIso (E.inverse.map f) := by
        rw [show E.inverse.map f = eX.hom ≫ g ≫ eY.inv by
          dsimp only [g]
          simp]
        infer_instance
      letI : IsIso (E.inverse.map f) := hmapiso
      exact hniso (isIso_of_reflects_iso f E.inverse)
    have hlt :=
      (S.standardFactorSkeletonHomGrading B.acyclic K).objLevel_lt_of_nonzero_not_isIso
          B.projectivePosetData B.acyclic
            (B.injective_multiplicity_eq_one D.sinkInjectiveLabel)
              g hg hgniso
    change B.standardFactorSchurLevel X < B.standardFactorSchurLevel Y
    rw [B.standardFactorSchurLevel_of_isSchur X hX,
      B.standardFactorSchurLevel_of_isSchur Y hY]
    exact hlt

/-- The projective-poset realization gives the manuscript's lower bound on
the length of the concrete factor grading. -/
theorem standardFactorRealization_length_bound
    (B : S.PrimitiveDirectedBoundaryData D) :
    MagnitudeConjecture.ARCount.projectiveCount
          (S.factorFiniteTauCategoryData K).IsProjective - 1 ≤
      (B.standardFactorLength : ℤ) := by
  have hcard : Fintype.card B.ProjectivePoset ≤ B.standardFactorLength :=
    MagnitudeConjecture.PosetSpace.card_le_of_schurPositiveGrading
      k B.ProjectivePoset B.standardFactorSchurPositiveGrading
  have hcardZ : (Fintype.card B.ProjectivePoset : ℤ) ≤
      (B.standardFactorLength : ℤ) := by
    exact_mod_cast hcard
  rw [B.standardFactorProjectiveCount_eq_projectivePoset_card_add_one]
  omega

/-- The concrete translation recurrence and completed poset-space grading
prove nonnegativity of the intrinsic Euler excess of the primitive factor. -/
theorem standardFactorIntrinsicEulerExcess_nonnegative
    (B : S.PrimitiveDirectedBoundaryData D) :
    0 ≤ MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData K)) := by
  apply
    MagnitudeConjecture.GradedTreeExcess.matrixIntrinsicEulerExcess_nonnegative_of_translationRecurrence_and_posetSpace
        (k := k) (T := B.ProjectivePoset)
        (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
          (S.factorFiniteTauCategoryData K))
        B.standardFactorVertexCount B.standardFactorArrowCount
        B.standardFactorInjectiveCount B.standardFactorProjectiveCount
        (MagnitudeConjecture.ARCount.projectiveCount
          (S.factorFiniteTauCategoryData K).IsProjective)
  · exact B.standardFactorProjectiveCount_eq_projectivePoset_card_add_one
  · exact B.standardFactorSchurPositiveGrading
  · exact B.standardFactorVertexCount_zero
  · exact B.standardFactorVertexCount_length
  · exact B.standardFactorArrowCount_zero
  · exact fun j hj ↦ B.standardFactorArrowCount_add_one j hj
  · exact fun j _hj ↦ B.standardFactorVertexCount_add_two j
  · exact B.standardFactorMeshEulerTotal

/-- Vanishing intrinsic factor excess is exactly sharpness of the concrete
grading-length bound. -/
theorem standardFactorIntrinsicEulerExcess_eq_zero_iff
    (B : S.PrimitiveDirectedBoundaryData D) :
    MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
        (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
          (S.factorFiniteTauCategoryData K)) = 0 ↔
      (B.standardFactorLength : ℤ) =
        MagnitudeConjecture.ARCount.projectiveCount
            (S.factorFiniteTauCategoryData K).IsProjective - 1 := by
  apply
    MagnitudeConjecture.GradedTreeExcess.matrixIntrinsicEulerExcess_eq_zero_iff_of_translationRecurrence
        (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
          (S.factorFiniteTauCategoryData K))
        B.standardFactorVertexCount B.standardFactorArrowCount
        B.standardFactorInjectiveCount B.standardFactorProjectiveCount
        (MagnitudeConjecture.ARCount.projectiveCount
          (S.factorFiniteTauCategoryData K).IsProjective)
  · exact B.standardFactorVertexCount_zero
  · exact B.standardFactorVertexCount_length
  · exact B.standardFactorArrowCount_zero
  · exact fun j hj ↦ B.standardFactorArrowCount_add_one j hj
  · exact fun j _hj ↦ B.standardFactorVertexCount_add_two j
  · exact B.standardFactorMeshEulerTotal

/-- Equality in the intrinsic factor estimate forces every Schur object in
the completed poset-space realization to be one-dimensional. -/
theorem standardFactorSchur_finrank_eq_one_of_intrinsicEulerExcess_eq_zero
    (B : S.PrimitiveDirectedBoundaryData D)
    (hzero : MagnitudeConjecture.DirectedDeletion.intrinsicEulerExcess
        (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
          (S.factorFiniteTauCategoryData K)) = 0)
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    Module.finrank k X = 1 := by
  apply
    MagnitudeConjecture.GradedTreeExcess.finrank_eq_one_of_matrixIntrinsicEulerExcess_eq_zero_of_translationRecurrence_and_posetSpace
        (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
          (S.factorFiniteTauCategoryData K))
        B.standardFactorVertexCount B.standardFactorArrowCount
        B.standardFactorInjectiveCount B.standardFactorProjectiveCount
        (MagnitudeConjecture.ARCount.projectiveCount
          (S.factorFiniteTauCategoryData K).IsProjective)
        B.standardFactorProjectiveCount_eq_projectivePoset_card_add_one
        B.standardFactorSchurPositiveGrading
        B.standardFactorVertexCount_zero
        B.standardFactorVertexCount_length
        B.standardFactorArrowCount_zero
        (fun j hj ↦ B.standardFactorArrowCount_add_one j hj)
        (fun j _hj ↦ B.standardFactorVertexCount_add_two j)
        B.standardFactorMeshEulerTotal hzero X hX

end PrimitiveDirectedBoundaryData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
