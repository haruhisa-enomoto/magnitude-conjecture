import MagnitudeConjecture.CategoryTheory.GradedProjectiveHomSpaces
import MagnitudeConjecture.Graded.EquivTransport
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Grading actual morphisms from the projective sum -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C]
variable {ι : Type} [Fintype ι] (P : ι → C) [HasFiniteBiproducts C]

/-- The finite biproduct universal property as a linear coordinate equivalence. -/
def generatorHomEquiv (X : C) : (⨁ P ⟶ X) ≃ₗ[k] (∀ i, P i ⟶ X) where
  toFun f i := biproduct.ι P i ≫ f
  invFun f := biproduct.desc f
  left_inv f := by apply biproduct.hom_ext'; intro i; simp
  right_inv f := by funext i; simp
  map_add' f g := by funext i; simp
  map_smul' c f := by funext i; simp

/-- Endomorphisms of the finite sum in matrix coordinates. -/
def generatorMatrixEquiv : (⨁ P ⟶ ⨁ P) ≃ₗ[k] (∀ i j, P i ⟶ P j) where
  toFun f i j := biproduct.ι P i ≫ f ≫ biproduct.π P j
  invFun a := biproduct.desc fun i ↦ biproduct.lift (a i)
  left_inv f := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp
  right_inv a := by funext i j; simp
  map_add' f g := by funext i j; simp
  map_smul' c f := by funext i j; simp

variable (G : HomGrading k C) [∀ i X, FiniteDimensional k (P i ⟶ X)]

/-- The internal grading on actual maps from the projective sum. -/
def generatorHomGrading (X : C) : Graded.VectorGrading k (⨁ P ⟶ X) :=
  (G.projectiveHomGrading P X).comap (generatorHomEquiv P X)

/-- The internal grading on actual endomorphisms of the projective sum. -/
def generatorEndGrading : Graded.VectorGrading k (⨁ P ⟶ ⨁ P) :=
  (G.projectiveMatrixGrading P).comap (generatorMatrixEquiv P)

/-- Postcomposition respects the grading on the actual generator Hom space. -/
theorem generatorHom_postcomp_mem {X Y : C} {n d : ℤ} {f : ⨁ P ⟶ X} {g : X ⟶ Y}
    (hf : f ∈ (G.generatorHomGrading P X).component n)
    (hg : g ∈ G.component X Y d) :
    f ≫ g ∈ (G.generatorHomGrading P Y).component (n + d) := by
  intro i hi
  have hh := G.comp_mem (hf i hi) hg
  change (biproduct.ι P i ≫ f) ≫ g ∈ G.component (P i) Y (n+d) at hh
  change biproduct.ι P i ≫ (f ≫ g) ∈ G.component (P i) Y (n+d)
  simpa only [Category.assoc] using hh

/-- Precomposition respects the grading on actual generator Hom spaces. -/
theorem generatorHom_precomp_mem {X : C} {d n : ℤ} {a : ⨁ P ⟶ ⨁ P} {f : ⨁ P ⟶ X}
    (ha : a ∈ (G.generatorEndGrading P).component d)
    (hf : f ∈ (G.generatorHomGrading P X).component n) :
    a ≫ f ∈ (G.generatorHomGrading P X).component (d + n) := by
  intro i hi
  change biproduct.ι P i ≫ (a ≫ f) ∈ G.component (P i) X (d + n)
  have heq : biproduct.ι P i ≫ (a ≫ f) =
      ∑ j, (biproduct.ι P i ≫ a ≫ biproduct.π P j) ≫ (biproduct.ι P j ≫ f) := by
    calc
      _ = (biproduct.ι P i ≫ a) ≫ (∑ j, biproduct.π P j ≫ biproduct.ι P j) ≫ f := by
        rw [biproduct.total (f := P)]; simp
      _ = _ := by simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  rw [heq]
  apply Submodule.sum_mem
  intro j hj
  have hh := G.comp_mem (ha i hi j (Set.mem_univ j)) (hf j (Set.mem_univ j))
  change (biproduct.ι P i ≫ a ≫ biproduct.π P j) ≫ (biproduct.ι P j ≫ f) ∈
    G.component (P i) X (d+n) at hh
  exact hh

/-- Composition adds degrees in the actual generator endomorphism space. -/
theorem generatorEnd_comp_mem {d n : ℤ} {a b : ⨁ P ⟶ ⨁ P}
    (ha : a ∈ (G.generatorEndGrading P).component d)
    (hb : b ∈ (G.generatorEndGrading P).component n) :
    a ≫ b ∈ (G.generatorEndGrading P).component (d + n) := by
  intro i hi j hj
  have hcol : b ≫ biproduct.π P j ∈ (G.generatorHomGrading P (P j)).component n := by
    intro l hl
    exact hb l hl j hj
  have hh := G.generatorHom_precomp_mem P ha hcol i hi
  change biproduct.ι P i ≫ (a ≫ (b ≫ biproduct.π P j)) ∈
    G.component (P i) (P j) (d+n) at hh
  change biproduct.ι P i ≫ (a ≫ b) ≫ biproduct.π P j ∈
    G.component (P i) (P j) (d+n)
  simpa only [Category.assoc] using hh

/-- The generator identity is homogeneous of degree zero. -/
theorem generatorEnd_id_mem :
    𝟙 (⨁ P) ∈ (G.generatorEndGrading P).component 0 := by
  classical
  intro i hi j hj
  change biproduct.ι P i ≫ 𝟙 (⨁ P) ≫ biproduct.π P j ∈ G.component (P i) (P j) 0
  by_cases hij : i = j
  · subst j
    simpa using G.id_mem (P i)
  · simp [biproduct.ι_π, hij]

end MagnitudeConjecture.GradedCategory.HomGrading
