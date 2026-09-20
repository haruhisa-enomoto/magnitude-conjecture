import MagnitudeConjecture.CategoryTheory.GradedDegreeCategory

/-! # Simultaneous translation of graded shift labels -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] (G : HomGrading k C)

/-- Translate all shift labels by the same integer. -/
def shiftFunctor (s : ℤ) : DegreeObject G ⥤ DegreeObject G where
  obj X := ⟨X.obj, X.degree + s⟩
  map f := ⟨f.val, by simpa only [add_sub_add_right_eq_sub] using f.property⟩
  map_id X := rfl
  map_comp f g := rfl

instance (s : ℤ) : (G.shiftFunctor s).Full where
  map_surjective f := ⟨⟨f.val, by simpa only [shiftFunctor, add_sub_add_right_eq_sub] using f.property⟩, rfl⟩
instance (s : ℤ) : (G.shiftFunctor s).Faithful where
  map_injective h := by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
instance (s : ℤ) : (G.shiftFunctor s).Additive where
  map_add := by intros; rfl
instance (s : ℤ) : (G.shiftFunctor s).Linear k where
  map_smul := by intros; rfl

end MagnitudeConjecture.GradedCategory.HomGrading
