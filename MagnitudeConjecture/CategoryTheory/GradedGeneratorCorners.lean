import MagnitudeConjecture.CategoryTheory.GradedGeneratorIdempotents
import MagnitudeConjecture.Graded.ProjectiveCorners

/-! # Homogeneous corners of a projective-generator algebra -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
variable {ι : Type} [Fintype ι] (P : ι → C)
variable (G : HomGrading k C) [∀ i X, FiniteDimensional k (P i ⟶ X)]

/-- A corner of the opposite generator algebra is the corresponding Hom
space between summands, with the same homogeneous degree. -/
def generatorCornerEquiv (i j : ι) (d : ℤ) :
    Graded.cornerComponent (G.generatorAlgebraGrading P)
      (generatorIdempotent P i) (generatorIdempotent P j) d ≃ₗ[k]
        G.component (P i) (P j) d where
  toFun a := ⟨biproduct.ι P i ≫ a.val.unop.asHom ≫ biproduct.π P j,
    a.property.1 i (Set.mem_univ i) j (Set.mem_univ j)⟩
  invFun f := ⟨MulOpposite.op (End.of (biproduct.π P i ≫ f.val ≫ biproduct.ι P j)), by
    classical
    refine ⟨?_, ?_, ?_⟩
    · intro p hp q hq
      change biproduct.ι P p ≫ (biproduct.π P i ≫ f.val ≫ biproduct.ι P j) ≫
        biproduct.π P q ∈ G.component (P p) (P q) d
      by_cases hpi : p = i
      · subst p
        by_cases hjq : j = q
        · subst q
          simpa using f.property
        · simp [Category.assoc, hjq]
      · simp [← Category.assoc, hpi]
    · apply MulOpposite.unop_injective
      change End.of ((biproduct.π P i ≫ biproduct.ι P i) ≫
        (biproduct.π P i ≫ f.val ≫ biproduct.ι P j)) = _
      simp [Category.assoc]
    · apply MulOpposite.unop_injective
      change End.of ((biproduct.π P i ≫ f.val ≫ biproduct.ι P j) ≫
        (biproduct.π P j ≫ biproduct.ι P j)) = _
      simp [Category.assoc]⟩
  left_inv a := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply End.ext
    have hi := congrArg (fun b : (End (⨁ P))ᵐᵒᵖ ↦ b.unop.asHom) a.property.2.1
    have hj := congrArg (fun b : (End (⨁ P))ᵐᵒᵖ ↦ b.unop.asHom) a.property.2.2
    change (biproduct.π P i ≫ biproduct.ι P i) ≫ a.val.unop.asHom =
      a.val.unop.asHom at hi
    change a.val.unop.asHom ≫ (biproduct.π P j ≫ biproduct.ι P j) =
      a.val.unop.asHom at hj
    change biproduct.π P i ≫ (biproduct.ι P i ≫ a.val.unop.asHom ≫ biproduct.π P j) ≫
      biproduct.ι P j = a.val.unop.asHom
    calc
      _ = ((biproduct.π P i ≫ biproduct.ι P i) ≫ a.val.unop.asHom) ≫
          (biproduct.π P j ≫ biproduct.ι P j) := by simp only [Category.assoc]
      _ = a.val.unop.asHom := by rw [hi, hj]
  right_inv f := by
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Subtype.ext
    change biproduct.ι P i ≫ (a.val.unop.asHom + b.val.unop.asHom) ≫ biproduct.π P j = _
    simp
  map_smul' c a := by
    apply Subtype.ext
    change biproduct.ι P i ≫ (c • a.val.unop.asHom) ≫ biproduct.π P j = _
    simp

end MagnitudeConjecture.GradedCategory.HomGrading
