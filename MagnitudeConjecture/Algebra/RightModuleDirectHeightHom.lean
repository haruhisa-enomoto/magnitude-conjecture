import MagnitudeConjecture.Algebra.RightModuleDirectFactorHeight
import MagnitudeConjecture.CategoryTheory.FiniteTauHomPredecessor

/-! # Direct heights increase along nonzero nonisomorphisms -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

/-- Induction through incoming meshes makes the directly constructed height
strictly increase on every nonzero nonisomorphism. -/
theorem PrimitiveDirectedBoundaryData.directFactorHeight_lt_of_hom
    (B : S.PrimitiveDirectedBoundaryData D)
    {X Y : S.SurvivingLabel K}
    (f : S.factorObject K X ⟶ S.factorObject K Y) (hf : f ≠ 0) (hn : ¬ IsIso f) :
    B.directFactorHeight X < B.directFactorHeight Y := by
  classical
  suffices hall : ∀ Y X : S.SurvivingLabel K,
      ∀ f : S.factorObject K X ⟶ S.factorObject K Y,
      f ≠ 0 → ¬ IsIso f → B.directFactorHeight X < B.directFactorHeight Y from
    hall Y X f hf hn
  intro Y
  induction Y using (measure B.directHeightRank).wf.induction with
  | h Y ih =>
    intro X f hf hn
    let T := (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData
    obtain ⟨i, g, hg⟩ := MagnitudeConjecture.FiniteTauMatrix.exists_nonzero_hom_rightMiddle
      T f hf hn
    let Z := MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel T Y i
    have ha : directFactorArrow Z Y := directFactorArrow_rightMiddleLabel Y i
    have hstep : B.directFactorHeight Y = B.directFactorHeight Z + 1 :=
      B.directFactorHeight_arrow Z Y ha
    by_cases hx : X = Z
    · rw [hx, hstep]
      omega
    · have hgn : ¬ IsIso g := by
        intro hgiso
        letI : IsIso g := hgiso
        let eg := asIso g
        exact hx (S.factorObject_skeletal K ⟨eg⟩)
      have hzrank : B.directHeightRank Z < B.directHeightRank Y :=
        B.directHeightRank_lt_of_arrow Z Y ha
      have hi := ih Z hzrank X g hg hgn
      omega

/-- A nonzero map between distinct selected factor objects increases height. -/
theorem PrimitiveDirectedBoundaryData.directFactorHeight_lt_of_ne
    (B : S.PrimitiveDirectedBoundaryData D)
    {X Y : S.SurvivingLabel K} (hXY : X ≠ Y)
    (f : S.factorObject K X ⟶ S.factorObject K Y) (hf : f ≠ 0) :
    B.directFactorHeight X < B.directFactorHeight Y := by
  apply B.directFactorHeight_lt_of_hom f hf
  intro h
  let := h
  exact hXY (S.factorObject_skeletal K ⟨asIso f⟩)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
