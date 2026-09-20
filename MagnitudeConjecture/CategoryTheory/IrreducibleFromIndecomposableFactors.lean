import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleCofinite

/-! # Testing irreducibility on indecomposable intermediate factors -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasBinaryBiproducts C] [HasFiniteBiproducts C]

theorem retraction_ne_zero_of_ne_zero {X Y : C} (f : X ⟶ Y) (hf : f ≠ 0)
    [IsSplitMono f] : retraction f ≠ 0 := by
  intro hz
  apply hf
  calc
    f = (f ≫ retraction f) ≫ f := by rw [IsSplitMono.id, Category.id_comp]
    _ = 0 := by rw [hz, comp_zero, zero_comp]

theorem section_ne_zero_of_ne_zero {X Y : C} (f : X ⟶ Y) (hf : f ≠ 0)
    [IsSplitEpi f] : section_ f ≠ 0 := by
  intro hz
  apply hf
  calc
    f = f ≫ (section_ f ≫ f) := by rw [IsSplitEpi.id, Category.comp_id]
    _ = 0 := by rw [hz, zero_comp, comp_zero]

/-- With finite indecomposable decompositions, it suffices to test nonzero
two-sided interactions with indecomposable intermediate objects. -/
theorem irreducible_of_indecomposable_factors
    (decomposition : ∀ M : C, Nonempty (FiniteIndecomposableDecomposition M))
    {X Y : C} (f : X ⟶ Y) (hf : f ≠ 0)
    (hm : ¬ IsSplitMono f) (he : ¬ IsSplitEpi f)
    (hpair : ∀ M : C, Indecomposable M → ∀ a : X ⟶ M, ∀ b : M ⟶ Y,
      a ≠ 0 → b ≠ 0 → IsSplitMono a ∨ IsSplitEpi b) : IsIrreducibleMorphism f := by
  classical
  refine { not_isSplitMono := hm, not_isSplitEpi := he, factorization := ?_ }
  intro M g h hgh
  obtain ⟨d⟩ := decomposition M
  let p j := d.isoBiproduct.hom ≫ biproduct.π d.summand j
  let q j := biproduct.ι d.summand j ≫ d.isoBiproduct.inv
  let a j := g ≫ p j
  let b j := q j ≫ h
  have hs : ∑ j, a j ≫ b j = f := by
    calc
      _ = g ≫ d.isoBiproduct.hom ≫
          (∑ j, biproduct.π d.summand j ≫ biproduct.ι d.summand j) ≫ d.isoBiproduct.inv ≫ h := by
        simp only [a, b, p, q, Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
      _ = f := by rw [biproduct.total]; simpa using hgh
  have hj : ∃ j, a j ≫ b j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    rw [← hs]
    exact Finset.sum_eq_zero (fun j _ ↦ hn j)
  obtain ⟨j, hj⟩ := hj
  have ha : a j ≠ 0 := by intro hz; apply hj; simp [hz]
  have hb : b j ≠ 0 := by intro hz; apply hj; simp [hz]
  rcases hpair (d.summand j) (d.indecomposable j) (a j) (b j) ha hb with ha | hb
  · letI := ha
    exact Or.inl (IsSplitMono.mk'
      { retraction := p j ≫ retraction (a j)
        id := by simpa only [a, Category.assoc] using IsSplitMono.id (a j) })
  · letI := hb
    exact Or.inr (IsSplitEpi.mk'
      { section_ := section_ (b j) ≫ q j
        id := by simpa only [b, Category.assoc] using IsSplitEpi.id (b j) })

end MagnitudeConjecture.CategoryTheory
