import MagnitudeConjecture.CategoryTheory.GradedDegreeCategory

/-!
# Homogeneous components of maps

An internal Hom grading gives finite homogeneous decompositions of every map.
Taking degree zero of a composite pairs opposite degrees. This is the
identity decomposition used to classify graded indecomposables as shifts.
-/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)

/-- The finite homogeneous decomposition of a map. -/
def decomposeHom (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] DirectSum ℤ (fun d ↦ G.component X Y d) := by
  letI := (G.internal X Y).chooseDecomposition
  exact DirectSum.decomposeLinearEquiv (G.component X Y)

/-- Projection onto degree `d`, viewed as an ambient map. -/
def part (X Y : C) (d : ℤ) : (X ⟶ Y) →ₗ[k] (X ⟶ Y) :=
  (G.component X Y d).subtype.comp
    ((DirectSum.component k ℤ (fun i ↦ G.component X Y i) d).comp
      (G.decomposeHom X Y).toLinearMap)

theorem part_mem {X Y : C} (d : ℤ) (f : X ⟶ Y) :
    G.part X Y d f ∈ G.component X Y d :=
  ((G.decomposeHom X Y f) d).property

theorem part_of_mem {X Y : C} {d : ℤ} {f : X ⟶ Y}
    (hf : f ∈ G.component X Y d) : G.part X Y d f = f := by
  letI := (G.internal X Y).chooseDecomposition
  exact DirectSum.decompose_of_mem_same (G.component X Y) hf

theorem part_of_mem_ne {X Y : C} {d e : ℤ} {f : X ⟶ Y}
    (hf : f ∈ G.component X Y d) (hde : d ≠ e) : G.part X Y e f = 0 := by
  letI := (G.internal X Y).chooseDecomposition
  exact DirectSum.decompose_of_mem_ne (G.component X Y) hf hde

theorem sum_parts {X Y : C} (f : X ⟶ Y) :
    ∑ d ∈ (G.decomposeHom X Y f).support, G.part X Y d f = f := by
  classical
  letI := (G.internal X Y).chooseDecomposition
  exact DirectSum.sum_support_decompose (G.component X Y) f

/-- With the first factor homogeneous of degree `d`, only degree `-d` of
the second factor contributes to degree zero of their composite. -/
theorem part_zero_comp_homogeneous {X Y Z : C} {d : ℤ} (f : X ⟶ Y)
    (hf : f ∈ G.component X Y d) (g : Y ⟶ Z) :
    G.part X Z 0 (f ≫ g) = f ≫ G.part Y Z (-d) g := by
  letI := (G.internal Y Z).chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component Y Z)
    (motive := fun g ↦ G.part X Z 0 (f ≫ g) = f ≫ G.part Y Z (-d) g)
  · simp
  · intro e g
    by_cases he : e = -d
    · subst e
      rw [G.part_of_mem g.property]
      apply G.part_of_mem
      simpa using G.comp_mem hf g.property
    · rw [G.part_of_mem_ne g.property he, Limits.comp_zero]
      exact G.part_of_mem_ne (G.comp_mem hf g.property) (by omega)
  · intro g g' hg hg'
    simp only [Preadditive.comp_add, map_add, hg, hg']

/-- Degree-zero convolution has a finite sum indexed only by the support of
the first factor. -/
theorem part_zero_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G.part X Z 0 (f ≫ g) =
      ∑ d ∈ (G.decomposeHom X Y f).support,
        G.part X Y d f ≫ G.part Y Z (-d) g := by
  classical
  calc
    _ = G.part X Z 0 ((∑ d ∈ (G.decomposeHom X Y f).support,
        G.part X Y d f) ≫ g) := by rw [G.sum_parts f]
    _ = _ := by
      rw [Preadditive.sum_comp, map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      exact G.part_zero_comp_homogeneous _ (G.part_mem d f) g

/-- Taking degree zero preserves the identity map. -/
theorem part_zero_id (X : C) : G.part X X 0 (𝟙 X) = 𝟙 X :=
  G.part_of_mem (G.id_mem X)

end MagnitudeConjecture.GradedCategory.HomGrading
