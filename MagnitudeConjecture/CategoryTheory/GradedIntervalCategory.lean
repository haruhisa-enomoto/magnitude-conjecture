import MagnitudeConjecture.CategoryTheory.GradedDegreeCategory
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite intervals in a graded category

The interval category has objects `(X,r)` for `0 ≤ r ≤ m` and morphisms
the degree `r-s` part of `Hom(X,Y)`. When `C` is the category of projectives
of the standard form, this is the finite category defining the manuscript's
interval algebra. Here we construct the category and its Hom coordinates;
the equivalence of its modules with supported graded modules is separate.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)

/-- Include the finite range of degree coordinates in all integer shifts. -/
def intervalObject (m : ℕ) (X : C × Fin (m + 1)) : DegreeObject G :=
  ⟨X.1, X.2.val⟩

/-- The full category on objects with degrees from zero to `m`. -/
abbrev Interval (m : ℕ) :=
  InducedCategory (DegreeObject G) (G.intervalObject m)

instance (m : ℕ) [Fintype C] : Fintype (G.Interval m) :=
  inferInstanceAs (Fintype (C × Fin (m + 1)))

theorem card_interval (m : ℕ) [Fintype C] :
    Fintype.card (G.Interval m) = (m + 1) * Fintype.card C := by
  change Fintype.card (C × Fin (m + 1)) = _
  simp [Nat.mul_comm]

/-- Include the interval as a full subcategory of the degree category. -/
def intervalInclusion (m : ℕ) : G.Interval m ⥤ DegreeObject G :=
  inducedFunctor (G.intervalObject m)

instance (m : ℕ) : (G.intervalInclusion m).Full :=
  inferInstanceAs ((inducedFunctor (G.intervalObject m)).Full)

instance (m : ℕ) : (G.intervalInclusion m).Faithful :=
  inferInstanceAs ((inducedFunctor (G.intervalObject m)).Faithful)

/-- The defining Hom-coordinate equivalence of the finite interval. -/
def intervalHomEquiv (m : ℕ) (X Y : G.Interval m) :
    (X ⟶ Y) ≃ₗ[k] G.component X.1 Y.1 ((X.2.val : ℤ) - Y.2.val) :=
  InducedCategory.homLinearEquiv

instance (m : ℕ) (X Y : G.Interval m)
    [FiniteDimensional k (X.1 ⟶ Y.1)] : FiniteDimensional k (X ⟶ Y) :=
  Module.Finite.equiv (G.intervalHomEquiv m X Y).symm

/-- The Hom coordinate of an interval identity is the original identity. -/
theorem intervalHomEquiv_id (m : ℕ) (X : G.Interval m) :
    (G.intervalHomEquiv m X X (𝟙 X)).val = 𝟙 X.1 := rfl

/-- Composition in the interval is the original homogeneous composition. -/
theorem intervalHomEquiv_comp (m : ℕ) {X Y Z : G.Interval m}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (G.intervalHomEquiv m X Z (f ≫ g)).val =
      (G.intervalHomEquiv m X Y f).val ≫ (G.intervalHomEquiv m Y Z g).val := rfl

/-- A nonzero interval morphism decreases degree by at most the common
Hom-degree bound. This also controls every factor in a nonzero composite. -/
theorem interval_degree_bounds_of_ne_zero (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) {X Y : G.Interval m} (f : X ⟶ Y) (hf : f ≠ 0) :
    Y.2.val ≤ X.2.val ∧ X.2.val ≤ Y.2.val + h := by
  have hf' : f.hom ≠ 0 := by
    intro hz
    exact hf (InducedCategory.hom_ext hz)
  have hb := G.degree_bounds_of_ne_zero h hbound f.hom hf'
  change (Y.2.val : ℤ) ≤ X.2.val ∧ (X.2.val : ℤ) ≤ Y.2.val + h at hb
  omega

end MagnitudeConjecture.GradedCategory.HomGrading
