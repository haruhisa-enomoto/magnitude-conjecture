import MagnitudeConjecture.CategoryTheory.GradedGeneratorHom
import MagnitudeConjecture.Graded.ModuleMapComponents
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Linear.Basic

/-! # The graded right modules represented by the projective generator -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
variable {ι : Type} [Fintype ι] (P : ι → C)

/-- Coordinates for the opposite endomorphism ring acting by precomposition. -/
def generatorOppositeEquiv : (End (⨁ P))ᵐᵒᵖ ≃ₗ[k] (⨁ P ⟶ ⨁ P) where
  toFun a := a.unop.asHom
  invFun f := MulOpposite.op (End.of f)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance generatorScalarTower (X : C) : IsScalarTower k (End (⨁ P))ᵐᵒᵖ (⨁ P ⟶ X) where
  smul_assoc c a f := by
    change (c • a.unop.asHom) ≫ f = c • (a.unop.asHom ≫ f)
    exact Linear.smul_comp _ _ _ _ _ _

variable (G : HomGrading k C) [∀ i X, FiniteDimensional k (P i ⟶ X)]

/-- The internal grading on the opposite generator algebra. -/
def generatorAlgebraGrading : Graded.VectorGrading k (End (⨁ P))ᵐᵒᵖ :=
  (G.generatorEndGrading P).comap (generatorOppositeEquiv P)

/-- The actual Hom module, graded compatibly with the right algebra action. -/
def generatorModuleGrading (X : C) :
    Graded.ModuleGrading (M := (⨁ P ⟶ X)) (G.generatorAlgebraGrading P) where
  toVectorGrading := G.generatorHomGrading P X
  smul_mem := by
    intro d n a f ha hf
    exact G.generatorHom_precomp_mem P ha hf

/-- Multiplication in the opposite algebra adds degrees. -/
theorem generatorAlgebra_mul_mem {d n : ℤ} {a b : (End (⨁ P))ᵐᵒᵖ}
    (ha : a ∈ (G.generatorAlgebraGrading P).component d)
    (hb : b ∈ (G.generatorAlgebraGrading P).component n) :
    a * b ∈ (G.generatorAlgebraGrading P).component (d + n) :=
  G.generatorEnd_comp_mem P ha hb

/-- The algebra unit has degree zero. -/
theorem generatorAlgebra_one_mem :
    (1 : (End (⨁ P))ᵐᵒᵖ) ∈ (G.generatorAlgebraGrading P).component 0 :=
  G.generatorEnd_id_mem P

instance generatorHomFinite (X : C) : FiniteDimensional k (⨁ P ⟶ X) :=
  Module.Finite.equiv (generatorHomEquiv (k := k) P X).symm

/-- Postcomposition is a map of the actual right modules. -/
def generatorModuleMap {X Y : C} (f : X ⟶ Y) :
    (⨁ P ⟶ X) →ₗ[(End (⨁ P))ᵐᵒᵖ] (⨁ P ⟶ Y) where
  toFun x := x ≫ f
  map_add' x y := Preadditive.add_comp _ _ _ _ _ _
  map_smul' a x := Category.assoc _ _ _

/-- The represented module map has the degree of its original morphism. -/
theorem generatorModuleMap_homogeneous {X Y : C} {d : ℤ} {f : X ⟶ Y}
    (hf : f ∈ G.component X Y d) :
    (G.generatorModuleGrading P X).Homogeneous (G.generatorModuleGrading P Y) d
      (generatorModuleMap P f) := by
  intro n x hx
  exact G.generatorHom_postcomp_mem P hx hf

end MagnitudeConjecture.GradedCategory.HomGrading
