import MagnitudeConjecture.CategoryTheory.GradedHomComponents
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Biproduct decompositions with homogeneous degree-zero structure maps -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w z
variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)
variable {ι : Type z} [Fintype ι] {V : ι → C} (b : Bicone V)
variable (hπ : ∀ i, b.π i ∈ G.component b.pt (V i) 0)
variable (hι : ∀ i, b.ι i ∈ G.component (V i) b.pt 0)

/-- A degree-zero direct-sum diagram lifts with any common external shift. -/
def shiftedBicone (t : ℤ) : Bicone (fun i ↦ (⟨V i, t⟩ : DegreeObject G)) where
  pt := ⟨b.pt, t⟩
  π i := ⟨b.π i, by simpa using hπ i⟩
  ι i := ⟨b.ι i, by simpa using hι i⟩
  ι_π i j := by
    classical
    by_cases h : i = j
    · subst j
      simp only [dite_true]
      apply Subtype.ext
      change b.ι i ≫ b.π i = 𝟙 (V i)
      simpa using b.ι_π i i
    · simp only [dif_neg h]
      apply Subtype.ext
      change b.ι i ≫ b.π j = 0
      simpa [h] using b.ι_π i j

/-- The lifted diagram is still a biproduct: its total identity is unchanged. -/
def shiftedBiconeIsBilimit (t : ℤ)
    (htotal : ∑ i, b.π i ≫ b.ι i = 𝟙 b.pt) :
    (G.shiftedBicone b hπ hι t).IsBilimit := by
  apply isBilimitOfTotal
  apply G.forget.map_injective
  simp only [Functor.map_sum, Functor.map_comp, Functor.map_id]
  exact htotal

end MagnitudeConjecture.GradedCategory.HomGrading
