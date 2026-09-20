import MagnitudeConjecture.CategoryTheory.GradedGeneratorModule

/-! # Complete homogeneous idempotents of the graded projective generator -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
variable {ι : Type} [Fintype ι] (P : ι → C)

/-- The opposite endomorphism projecting onto one summand of the generator. -/
def generatorIdempotent (p : ι) : (End (⨁ P))ᵐᵒᵖ :=
  MulOpposite.op (End.of (biproduct.π P p ≫ biproduct.ι P p))

theorem generatorIdempotent_idempotent (p : ι) :
    generatorIdempotent P p * generatorIdempotent P p = generatorIdempotent P p := by
  apply MulOpposite.unop_injective
  change End.of ((biproduct.π P p ≫ biproduct.ι P p) ≫
    (biproduct.π P p ≫ biproduct.ι P p)) = End.of (biproduct.π P p ≫ biproduct.ι P p)
  simp [Category.assoc]

theorem generatorIdempotent_orthogonal : Pairwise fun p q ↦
    generatorIdempotent P p * generatorIdempotent P q = 0 := by
  intro p q hpq
  apply MulOpposite.unop_injective
  change End.of ((biproduct.π P p ≫ biproduct.ι P p) ≫
    (biproduct.π P q ≫ biproduct.ι P q)) = End.of 0
  simp [Category.assoc, biproduct.ι_π, hpq]

include k in
theorem sum_generatorIdempotent : ∑ p, generatorIdempotent P p = 1 := by
  apply (generatorOppositeEquiv (k := k) P).injective
  rw [map_sum]
  change ∑ p, biproduct.π P p ≫ biproduct.ι P p = 𝟙 (⨁ P)
  exact biproduct.total

variable (G : HomGrading k C) [∀ i X, FiniteDimensional k (P i ⟶ X)]

/-- Each summand projection is homogeneous of degree zero. -/
theorem generatorIdempotent_mem_zero (p : ι) :
    generatorIdempotent P p ∈ (G.generatorAlgebraGrading P).component 0 := by
  classical
  intro i hi j hj
  change biproduct.ι P i ≫ (biproduct.π P p ≫ biproduct.ι P p) ≫ biproduct.π P j ∈
    G.component (P i) (P j) 0
  by_cases hip : i = p
  · subst i
    by_cases hpj : p = j
    · subst j
      simpa using G.id_mem (P p)
    · simp [Category.assoc, hpj]
  · simp [← Category.assoc, hip]

/-- A degree absent in every projective Hom space is absent in the generator algebra. -/
theorem generatorAlgebra_component_eq_bot (d : ℤ)
    (hd : ∀ i j, G.component (P i) (P j) d = ⊥) :
    (G.generatorAlgebraGrading P).component d = ⊥ := by
  apply bot_unique
  intro a ha
  change a = 0
  apply (generatorOppositeEquiv (k := k) P).injective
  apply (generatorMatrixEquiv (k := k) P).injective
  funext i j
  have h := ha i (Set.mem_univ i) j (Set.mem_univ j)
  change _ ∈ G.component (P i) (P j) d at h
  rw [hd, Submodule.mem_bot] at h
  change biproduct.ι P i ≫ a.unop.asHom ≫ biproduct.π P j = 0 at h
  change biproduct.ι P i ≫ a.unop.asHom ≫ biproduct.π P j =
    biproduct.ι P i ≫ (0 : ⨁ P ⟶ ⨁ P) ≫ biproduct.π P j
  simpa only [zero_comp, comp_zero] using h

end MagnitudeConjecture.GradedCategory.HomGrading
