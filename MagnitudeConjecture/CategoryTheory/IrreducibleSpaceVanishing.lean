import MagnitudeConjecture.CategoryTheory.CategoricalIrreducibleSpace

/-! # Vanishing of intrinsic irreducible quotients -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.CategoricalIrreducible
universe u v w
variable (k : Type u) [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C]

/-- If every morphism lies in the radical square, the irreducible quotient vanishes. -/
theorem finrank_eq_zero_of_radicalSquare_eq_top (X Y : C)
    (h : radicalSquare k X Y = ⊤) : Module.finrank k (Space k X Y) = 0 := by
  have hd : denominator k X Y = ⊤ := by
    simp only [denominator, h, Submodule.comap_top]
  letI : Subsingleton (Space k X Y) := by
    change Subsingleton (radical k X Y ⧸ denominator k X Y)
    rw [hd]
    infer_instance
  exact Module.finrank_zero_of_subsingleton

end MagnitudeConjecture.CategoricalIrreducible
