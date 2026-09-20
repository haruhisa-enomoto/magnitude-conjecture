import MagnitudeConjecture.CategoryTheory.FiniteTauHeightIrreducible

/-! # Commutative squares give nonzero maps into the almost-split kernel -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.Iyama
namespace MagnitudeConjecture.CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A commutative square with distinct orthogonal middle objects produces
a nonzero map to the weak kernel of a right almost-split terminal map. -/
theorem exists_nonzero_weakKernel_map_of_square
    (S : ShortComplex C) (hS : ShortComplex.IsWeakKernel S)
    (hg : IsRightAlmostSplit S.g)
    {X V W : C} (a : X ⟶ V) (b : V ⟶ S.X₃)
    (c : X ⟶ W) (d : W ⟶ S.X₃)
    (ha : a ≠ 0) (hb : IsIrreducibleMorphism b) (hd : ¬ IsSplitEpi d)
    (hWV : ∀ f : W ⟶ V, f = 0) (hsquare : a ≫ b = c ≫ d) :
    ∃ f : X ⟶ S.X₁, f ≠ 0 := by
  obtain ⟨u, hu⟩ := hg.factors b hb.not_isSplitEpi
  obtain ⟨v, hv⟩ := hg.factors d hd
  have huSplit : IsSplitMono u := (hb.factorization u S.g hu).resolve_right hg.not_isSplitEpi
  letI : IsSplitMono u := huSplit
  let r := a ≫ u - c ≫ v
  have hr : r ≫ S.g = 0 := by
    dsimp only [r]
    rw [Preadditive.sub_comp, Category.assoc, hu, Category.assoc, hv, hsquare, sub_self]
  have hrne : r ≠ 0 := by
    intro hz
    have heq : a ≫ u = c ≫ v := sub_eq_zero.mp hz
    have h := congrArg (fun f : X ⟶ S.X₂ ↦ f ≫ retraction u) heq
    have hcross := hWV (v ≫ retraction u)
    apply ha
    simpa [Category.assoc, hcross] using h
  obtain ⟨f, hf⟩ := (ShortComplex.isWeakKernel_iff S).mp hS r hr
  refine ⟨f, ?_⟩
  intro hz
  apply hrne
  rw [← hf, hz, zero_comp]

end MagnitudeConjecture.CategoryTheory
