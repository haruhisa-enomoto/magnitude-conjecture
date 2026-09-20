import MagnitudeConjecture.CategoryTheory.GradedAdditiveEnvelope

/-! # Homogeneous maps between singleton additive-envelope objects -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C]
variable (G : HomGrading k C) [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- The additive embedding preserves each homogeneous Hom space exactly. -/
def additiveEmbeddingComponentEquiv (X Y : C) (d : ℤ) :
    G.additiveEnvelope.component ((Mat_.embedding C).obj X)
      ((Mat_.embedding C).obj Y) d ≃ₗ[k] G.component X Y d where
  toFun f := ⟨f.val PUnit.unit PUnit.unit,
    f.property PUnit.unit (Set.mem_univ _) PUnit.unit (Set.mem_univ _)⟩
  invFun f := ⟨fun _ _ ↦ f.val, fun _ _ _ _ ↦ f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext i j
    cases i
    cases j
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end MagnitudeConjecture.GradedCategory.HomGrading
