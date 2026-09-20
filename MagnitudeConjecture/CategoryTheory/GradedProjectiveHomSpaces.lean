import MagnitudeConjecture.CategoryTheory.GradedDegreeCategory
import MagnitudeConjecture.Graded.FinitePiGrading

/-! # Graded Hom coordinates from a finite projective family

The construction applies to any finite family; at the standard-form
application the family consists of the indecomposable projectives.
-/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v w z
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C]
variable (G : HomGrading k C) {ι : Type z} [Fintype ι] (P : ι → C)
variable [∀ i X, FiniteDimensional k (P i ⟶ X)]

/-- The homogeneous coordinates of `Hom(⊕ᵢ Pᵢ, X)`. -/
def projectiveHomGrading (X : C) : Graded.VectorGrading k (∀ i, P i ⟶ X) :=
  Graded.VectorGrading.finitePi fun i ↦
    { component := G.component (P i) X, internal := G.internal (P i) X }

/-- Postcomposition on the Hom coordinates. -/
def projectiveHomMap {X Y : C} (f : X ⟶ Y) :
    (∀ i, P i ⟶ X) →ₗ[k] (∀ i, P i ⟶ Y) where
  toFun x i := x i ≫ f
  map_add' x y := by funext i; exact Preadditive.add_comp _ _ _ _ _ _
  map_smul' c x := by funext i; exact Linear.smul_comp _ _ _ _ _ _

/-- Homogeneous postcomposition has the same degree as the original morphism. -/
theorem projectiveHomMap_mem {X Y : C} {d n : ℤ} {f : X ⟶ Y}
    (hf : f ∈ G.component X Y d) {x : ∀ i, P i ⟶ X}
    (hx : x ∈ (G.projectiveHomGrading P X).component n) :
    projectiveHomMap (k := k) P f x ∈ (G.projectiveHomGrading P Y).component (n + d) := by
  intro i hi
  exact G.comp_mem (hx i hi) hf

/-- The homogeneous matrix coordinates of the endomorphisms of the projective sum. -/
def projectiveMatrixGrading : Graded.VectorGrading k (∀ i j, P i ⟶ P j) :=
  Graded.VectorGrading.finitePi fun i ↦ Graded.VectorGrading.finitePi fun j ↦
    { component := G.component (P i) (P j), internal := G.internal (P i) (P j) }

/-- Precomposition by a homogeneous matrix shifts the degree of Hom coordinates.
This is the right module action used in the manuscript. -/
theorem projectiveMatrixAction_mem {X : C} {d n : ℤ}
    {a : ∀ i j, P i ⟶ P j} {x : ∀ i, P i ⟶ X}
    (ha : a ∈ (G.projectiveMatrixGrading P).component d)
    (hx : x ∈ (G.projectiveHomGrading P X).component n) :
    (fun i ↦ ∑ j, a i j ≫ x j) ∈ (G.projectiveHomGrading P X).component (d + n) := by
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact G.comp_mem (ha i hi j (Set.mem_univ j)) (hx j (Set.mem_univ j))

end MagnitudeConjecture.GradedCategory.HomGrading
