import MagnitudeConjecture.Algebra.RightModuleGeneratedRelationsRealization
import MagnitudeConjecture.Algebra.RightModuleDirectHeightHom
import MagnitudeConjecture.Algebra.RightModuleDirectHeightSink
import MagnitudeConjecture.CategoryTheory.SchurIndecomposable

/-! # The direct height grading on Schur poset spaces -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : FiniteIndecomposableSkeleton k A} {e : A} {D : PrimitiveIdempotentData e}
namespace PrimitiveDirectedBoundaryData

/-- The generated-relations equivalence for the canonical projective poset. -/
def directPosetSpaceEquivalence
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D)) :=
  S.generatedRelationsEquivalence B.acyclic D B.projectivePosetData

/-- A Schur poset space pulls back along the primitive equivalence to one
selected indecomposable factor object. -/
theorem exists_directFactorLabelIso_of_isSchur
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    ∃ x : S.SurvivingLabel (S.primitiveKilledLabels D),
      Nonempty
        ((B.directPosetSpaceEquivalence.inverse.obj X) ≅ S.factorObject (S.primitiveKilledLabels D) x) := by
  let E := B.directPosetSpaceEquivalence
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
  exact (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)).obj_complete Z hindecomposable

/-- The selected factor label representing a Schur poset space. -/
def directFactorSchurLabel
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    S.SurvivingLabel (S.primitiveKilledLabels D) :=
  Classical.choose (B.exists_directFactorLabelIso_of_isSchur X hX)

/-- The pullback of a Schur poset space is isomorphic to its selected factor
label. -/
def directFactorSchurIso
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    B.directPosetSpaceEquivalence.inverse.obj X ≅
      S.factorObject (S.primitiveKilledLabels D) (B.directFactorSchurLabel X hX) :=
  Classical.choice
    (Classical.choose_spec (B.exists_directFactorLabelIso_of_isSchur X hX))

/-- The direct factor height transported to a Schur poset space.  Its value
away from the Schur locus is irrelevant to the positive-grading interface. -/
def directFactorSchurLevel
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset) : ℕ := by
  classical
  exact
    if hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X then
      B.directFactorHeight (B.directFactorSchurLabel X hX)
    else 0

@[simp]
theorem directFactorSchurLevel_of_isSchur
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (X : MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
    (hX : MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset X) :
    B.directFactorSchurLevel X =
      B.directFactorHeight (B.directFactorSchurLabel X hX) := by
  classical
  rw [directFactorSchurLevel, dif_pos hX]

/-- The direct factor grading transports across the completed
poset-space equivalence to a positive grading on every Schur poset space. -/
def directFactorSchurPositiveGrading
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D)) :
    MagnitudeConjecture.PosetSpace.PositiveGrading
      (MagnitudeConjecture.PosetSpace.Obj k B.ProjectivePoset)
      (MagnitudeConjecture.PosetSpace.IsSchur k B.ProjectivePoset)
      (B.directFactorHeight (S.primitiveMultiplicityInput D).sink) where
  level := B.directFactorSchurLevel
  level_le X hX := by
    rw [B.directFactorSchurLevel_of_isSchur X hX]
    exact B.directFactorHeight_le_sink _
  lt_of_nonzero_not_isIso {X Y} f hX hY hf hniso := by
    let E := B.directPosetSpaceEquivalence
    letI : E.functor.Linear k := by
      change B.projectivePosetData.representableData.functor.Linear k
      infer_instance
    letI : E.inverse.Linear k := E.inverseLinear k
    let eX := B.directFactorSchurIso X hX
    let eY := B.directFactorSchurIso Y hY
    let g :
        S.factorObject (S.primitiveKilledLabels D) (B.directFactorSchurLabel X hX) ⟶
          S.factorObject (S.primitiveKilledLabels D) (B.directFactorSchurLabel Y hY) :=
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
    have hlt := B.directFactorHeight_lt_of_hom g hg hgniso
    change B.directFactorSchurLevel X < B.directFactorSchurLevel Y
    rw [B.directFactorSchurLevel_of_isSchur X hX,
      B.directFactorSchurLevel_of_isSchur Y hY]
    exact hlt


end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
