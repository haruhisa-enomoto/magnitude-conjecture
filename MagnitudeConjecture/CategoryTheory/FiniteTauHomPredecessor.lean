import MagnitudeConjecture.CategoryTheory.FiniteTauAlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix

/-! # Nonzero maps factor through a nonzero incoming component -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.Iyama
namespace MagnitudeConjecture.FiniteTauMatrix
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- A nonzero nonisomorphism between selected indecomposables has a nonzero
map to some occurrence in the target's incoming mesh. -/
theorem exists_nonzero_hom_rightMiddle
    (T : FiniteRightTauCategoryData C Ind) {X Y : Ind}
    (f : T.obj X ⟶ T.obj Y) (hf : f ≠ 0) (hn : ¬ IsIso f) :
    ∃ i : Fin (rightMiddleArity T Y),
      ∃ g : T.obj X ⟶ T.obj (rightMiddleLabel T Y i), g ≠ 0 := by
  classical
  have hsplit : ¬ IsSplitEpi f := by
    intro h
    let := h
    exact hn (MagnitudeConjecture.CategoryTheory.isIso_of_isSplitEpi_from_indecomposable
      (T.obj_indec X) f (T.obj_indec Y).1)
  obtain ⟨g, hg⟩ := (rightMesh_terminal_isRightAlmostSplit T Y).factors f hsplit
  let e := Classical.choice (rightMiddleIso T Y)
  have hcomponent : ∃ i, g ≫ e.hom ≫
      biproduct.π (fun j ↦ T.obj (rightMiddleLabel T Y j)) i ≠ 0 := by
    by_contra! h
    have hz : g ≫ e.hom = 0 := by
      apply biproduct.hom_ext
      intro i
      simpa [Category.assoc] using h i
    have hgzero : g = 0 := by
      apply (cancel_mono e.hom).1
      simpa using hz
    apply hf
    rw [← hg, hgzero, zero_comp]
  obtain ⟨i, hi⟩ := hcomponent
  exact ⟨i, g ≫ e.hom ≫ biproduct.π _ i, hi⟩

end MagnitudeConjecture.FiniteTauMatrix
