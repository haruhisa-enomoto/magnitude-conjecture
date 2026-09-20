import MagnitudeConjecture.CategoryTheory.GradedDegreeCategory
import MagnitudeConjecture.Graded.FinitePiGrading
import Mathlib.CategoryTheory.Preadditive.Mat

/-! # Extending the mesh Hom grading to finite direct sums

The original grading is supplied only on the indecomposable category. Its
additive envelope supplies the finite biproducts needed for the generator.
-/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.GradedCategory
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C]

instance matHomModule (X Y : Mat_ C) : Module k (X ⟶ Y) :=
  inferInstanceAs (Module k (∀ i j, X.X i ⟶ Y.X j))

instance matLinear : Linear k (Mat_ C) where
  smul_comp X Y Z c f g := by
    apply Mat_.hom_ext
    intro i j
    change (∑ l, (c • f i l) ≫ g l j) = c • ∑ l, f i l ≫ g l j
    simp [Finset.smul_sum]
  comp_smul X Y Z f c g := by
    apply Mat_.hom_ext
    intro i j
    change (∑ l, f i l ≫ (c • g l j)) = c • ∑ l, f i l ≫ g l j
    simp [Finset.smul_sum]

variable (G : HomGrading k C) [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

instance matFiniteHom (X Y : Mat_ C) : FiniteDimensional k (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional k (∀ i j, X.X i ⟶ Y.X j))

/-- Extend a Hom grading componentwise to the additive envelope. -/
def HomGrading.additiveEnvelope : HomGrading k (Mat_ C) where
  component X Y := (Graded.VectorGrading.finitePi fun i ↦
    Graded.VectorGrading.finitePi fun j ↦
      { component := G.component (X.X i) (Y.X j), internal := G.internal _ _ }).component
  internal X Y := (Graded.VectorGrading.finitePi fun i ↦
    Graded.VectorGrading.finitePi fun j ↦
      { component := G.component (X.X i) (Y.X j), internal := G.internal _ _ }).internal
  id_mem X := by
    classical
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      exact (Mat_.id_apply_self X i).symm ▸ G.id_mem (X.X i)
    · rw [Mat_.id_apply_of_ne X i j hij]
      exact (G.component _ _ _).zero_mem
  comp_mem := by
    intro X Y Z d n f g hf hg i hi j hj
    apply Submodule.sum_mem
    intro l hl
    exact G.comp_mem (hf i hi l (Set.mem_univ l)) (hg l (Set.mem_univ l) j hj)

end MagnitudeConjecture.GradedCategory
