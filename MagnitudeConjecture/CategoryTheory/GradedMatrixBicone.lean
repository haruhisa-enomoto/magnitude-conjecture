import MagnitudeConjecture.CategoryTheory.GradedAdditiveEnvelope
import MagnitudeConjecture.CategoryTheory.GradedBicone

/-! # Homogeneous direct-sum coordinates for finite matrix objects -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C]
variable (G : HomGrading k C) [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- The matrix object with its singleton summand injections and projections. -/
def matrixBicone (M : Mat_ C) : Bicone (fun i ↦ (Mat_.embedding C).obj (M.X i)) where
  pt := M
  π i := M.isoBiproductEmbedding.hom ≫ biproduct.π (fun j ↦ (Mat_.embedding C).obj (M.X j)) i
  ι i := biproduct.ι (fun j ↦ (Mat_.embedding C).obj (M.X j)) i ≫ M.isoBiproductEmbedding.inv
  ι_π i j := by
    classical
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact biproduct.ι_π _ i j

theorem matrixBicone_total (M : Mat_ C) :
    ∑ i, (matrixBicone M).π i ≫ (matrixBicone M).ι i = 𝟙 M := by
  let e := M.isoBiproductEmbedding
  let V := fun j ↦ (Mat_.embedding C).obj (M.X j)
  change ∑ i, (e.hom ≫ biproduct.π V i) ≫ (biproduct.ι V i ≫ e.inv) = 𝟙 M
  calc
    _ = e.hom ≫ (∑ i, biproduct.π V i ≫ biproduct.ι V i) ≫ e.inv := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = 𝟙 M := (congrArg (fun f ↦ e.hom ≫ f ≫ e.inv) (biproduct.total (f := V))).trans
      (by
        have hi : (𝟙 (⨁ V)) ≫ e.inv = e.inv := Category.id_comp _
        exact (congrArg (fun f ↦ e.hom ≫ f) hi).trans e.hom_inv_id)

/-- The singleton projections have degree zero. -/
theorem matrixBicone_π_homogeneous (M : Mat_ C) (i : M.ι) :
    (matrixBicone M).π i ∈ G.additiveEnvelope.component M ((Mat_.embedding C).obj (M.X i)) 0 := by
  classical
  intro a ha b hb
  change ((M.isoBiproductEmbedding.hom ≫ biproduct.π (fun j ↦ (Mat_.embedding C).obj (M.X j)) i) a b) ∈ G.component _ _ 0
  simp only [Mat_.isoBiproductEmbedding_hom, biproduct.lift_π]
  split_ifs with h
  · subst a
    exact G.id_mem _
  · exact (G.component _ _ _).zero_mem

/-- The singleton injections have degree zero. -/
theorem matrixBicone_ι_homogeneous (M : Mat_ C) (i : M.ι) :
    (matrixBicone M).ι i ∈ G.additiveEnvelope.component ((Mat_.embedding C).obj (M.X i)) M 0 := by
  classical
  intro a ha b hb
  change ((biproduct.ι (fun j ↦ (Mat_.embedding C).obj (M.X j)) i ≫ M.isoBiproductEmbedding.inv) a b) ∈ G.component _ _ 0
  simp only [Mat_.isoBiproductEmbedding_inv, biproduct.ι_desc]
  split_ifs with h
  · subst b
    exact G.id_mem _
  · exact (G.component _ _ _).zero_mem

end MagnitudeConjecture.GradedCategory.HomGrading
