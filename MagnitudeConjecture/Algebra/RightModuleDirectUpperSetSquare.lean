import MagnitudeConjecture.Algebra.RightModuleDirectUpperSetHeight
import MagnitudeConjecture.Algebra.RightModuleDirectSchurMaps
import MagnitudeConjecture.Algebra.RightModuleDirectHeightSquare
import MagnitudeConjecture.Combinatorics.PosetSpaceLineSupport

/-! # Upper-set squares in a zero-excess primitive factor -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A} {e : A} {D : PrimitiveIdempotentData e}
namespace PrimitiveDirectedBoundaryData
variable (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))

/-- Selected factor label of an upper-set line. -/
def directLineLabel (U : Finset B.ProjectivePoset)
    (hU : IsUpperSet (U : Set B.ProjectivePoset)) :=
  B.directFactorSchurLabel (PosetSpace.line k B.ProjectivePoset (U : Set _) hU)
    (PosetSpace.line_isSchur k B.ProjectivePoset _ hU)

/-- Distinct upper sets give distinct selected labels. -/
theorem directLineLabel_ne {U V : Finset B.ProjectivePoset}
    (hU : IsUpperSet (U : Set B.ProjectivePoset))
    (hV : IsUpperSet (V : Set B.ProjectivePoset)) (hne : U ≠ V) :
    B.directLineLabel U hU ≠ B.directLineLabel V hV := by
  apply B.directFactorSchurLabel_ne_of_not_iso
  rintro ⟨i⟩
  exact hne (Finset.coe_injective (PosetSpace.line_support_eq_of_iso i))

/-- A diamond of upper sets whose edges add one element determines an AR
translate when the primitive factor has zero excess. -/
theorem directUpperSet_square_tauPlus
    (hz : DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) = 0)
    (U V W Y : Finset B.ProjectivePoset)
    (hU : IsUpperSet (U : Set B.ProjectivePoset))
    (hV : IsUpperSet (V : Set B.ProjectivePoset))
    (hW : IsUpperSet (W : Set B.ProjectivePoset))
    (hY : IsUpperSet (Y : Set B.ProjectivePoset))
    (hUV : U ⊆ V) (hVY : V ⊆ Y) (hUW : U ⊆ W) (hWY : W ⊆ Y)
    (hVW : V ≠ W) (hcV : V.card = U.card + 1)
    (hcW : W.card = U.card + 1) (hcY : Y.card = V.card + 1) :
    ∃ hn : ¬ (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)).IsProjective
        (B.directLineLabel Y hY),
      (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)).tauPlus
        ⟨B.directLineLabel Y hY, hn⟩ = B.directLineLabel U hU := by
  let sU := PosetSpace.line_isSchur k B.ProjectivePoset (U : Set _) hU
  let sV := PosetSpace.line_isSchur k B.ProjectivePoset (V : Set _) hV
  let sW := PosetSpace.line_isSchur k B.ProjectivePoset (W : Set _) hW
  let sY := PosetSpace.line_isSchur k B.ProjectivePoset (Y : Set _) hY
  let a := PosetSpace.lineHom k B.ProjectivePoset (hU := hU) (hV := hV) hUV
  let b := PosetSpace.lineHom k B.ProjectivePoset (hU := hV) (hV := hY) hVY
  let c := PosetSpace.lineHom k B.ProjectivePoset (hU := hU) (hV := hW) hUW
  let d := PosetSpace.lineHom k B.ProjectivePoset (hU := hW) (hV := hY) hWY
  have hs : a ≫ b = c ≫ d := by apply PosetSpace.Hom.ext; rfl
  have hheight (Z : Finset B.ProjectivePoset)
      (hZ : IsUpperSet (Z : Set B.ProjectivePoset)) :
      B.directFactorHeight (B.directLineLabel Z hZ) = Z.card :=
    B.directHeight_lineLabel_eq_card_of_excess_zero hz Z hZ
  apply B.directHeight_square_tauPlus (B.directLineLabel_ne hV hW hVW)
    (by change B.directFactorHeight (B.directLineLabel V hV) =
          B.directFactorHeight (B.directLineLabel U hU) + 1
        rw [hheight V hV, hheight U hU]; exact hcV)
    (by change B.directFactorHeight (B.directLineLabel W hW) =
          B.directFactorHeight (B.directLineLabel U hU) + 1
        rw [hheight W hW, hheight U hU]; exact hcW)
    (by change B.directFactorHeight (B.directLineLabel Y hY) =
          B.directFactorHeight (B.directLineLabel V hV) + 1
        rw [hheight Y hY, hheight V hV]; exact hcY)
    (B.directFactorSchurMap sU sV a) (B.directFactorSchurMap sV sY b)
    (B.directFactorSchurMap sU sW c) (B.directFactorSchurMap sW sY d)
    (B.directFactorSchurMap_ne_zero sU sV a (PosetSpace.lineHom_ne_zero k _ hUV))
    (B.directFactorSchurMap_ne_zero sV sY b (PosetSpace.lineHom_ne_zero k _ hVY))
    (B.directFactorSchurMap_ne_zero sW sY d (PosetSpace.lineHom_ne_zero k _ hWY))
  exact (B.directFactorSchurMap_comp sU sV sY a b).symm.trans
    ((congrArg (B.directFactorSchurMap sU sY) hs).trans
      (B.directFactorSchurMap_comp sU sW sY c d))

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
