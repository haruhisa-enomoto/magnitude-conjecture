import MagnitudeConjecture.CategoryTheory.FiniteTauHomPredecessor
import MagnitudeConjecture.CategoryTheory.IrreducibleRadicalSquare

/-! # Adjacent-height morphisms are irreducible -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution QuotientSubmoduleEquidistribution.Iyama
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture.FiniteTauMatrix
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- A composite of radical maps cannot connect heights differing by at most one. -/
theorem radical_comp_eq_zero_of_height_gap
    (T : FiniteRightTauCategoryData C Ind) (height : Ind → ℕ)
    (hh : ∀ {x y : Ind} (f : T.obj x ⟶ T.obj y), f ≠ 0 → ¬ IsIso f → height x < height y)
    {x y : Ind} (hgap : height y ≤ height x + 1)
    {M : C} (g : T.obj x ⟶ M) (h : M ⟶ T.obj y)
    (hg : IsRadicalMorphism g) (hh' : IsRadicalMorphism h) : g ≫ h = 0 := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := T.obj_decomposition M
  let gi := fun i : Fin n ↦ g ≫ e.hom ≫ biproduct.π (fun i ↦ T.obj (a i)) i
  let hi := fun i : Fin n ↦ biproduct.ι (fun i ↦ T.obj (a i)) i ≫ e.inv ≫ h
  have hzero : ∀ i, gi i ≫ hi i = 0 := by
    intro i
    by_contra hn
    have hgi : gi i ≠ 0 := by intro hz; exact hn (by rw [hz, zero_comp])
    have hhi : hi i ≠ 0 := by intro hz; exact hn (by rw [hz, comp_zero])
    have hgr : IsRadicalMorphism (gi i) := isRadicalMorphism_postcomp _ hg
    have hhr : IsRadicalMorphism (hi i) := by
      exact isRadicalMorphism_precomp _ (isRadicalMorphism_precomp e.inv hh')
    have hgn : ¬ IsIso (gi i) := by
      intro hI
      let := hI
      exact ((T.isRadicalMorphism_iff_not_isSplitMono_from_obj (gi i)).1 hgr) inferInstance
    have hhn : ¬ IsIso (hi i) := by
      intro hI
      let := hI
      exact ((T.isRadicalMorphism_iff_not_isSplitEpi_to_obj (hi i)).1 hhr) inferInstance
    have h₁ := hh (gi i) hgi hgn
    have h₂ := hh (hi i) hhi hhn
    omega
  have hsum : g ≫ h = ∑ i, gi i ≫ hi i := by
    calc
      g ≫ h = g ≫ e.hom ≫ (𝟙 _) ≫ e.inv ≫ h := by simp
      _ = ∑ i, gi i ≫ hi i := by
        rw [← biproduct.total (f := fun i ↦ T.obj (a i))]
        simp only [gi, hi, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  rw [hsum]
  exact Finset.sum_eq_zero (fun i _ ↦ hzero i)

/-- Every nonzero map across one height step is irreducible. -/
theorem isIrreducible_of_height_eq_add_one
    (T : FiniteRightTauCategoryData C Ind) (height : Ind → ℕ)
    (hh : ∀ {x y : Ind} (f : T.obj x ⟶ T.obj y), f ≠ 0 → ¬ IsIso f → height x < height y)
    {x y : Ind} (hgap : height y = height x + 1)
    (f : T.obj x ⟶ T.obj y) (hf : f ≠ 0) : IsIrreducibleMorphism f := by
  classical
  have hn : ¬ IsIso f := by
    intro hI
    let := hI
    have hxy := T.obj_skeletal ⟨asIso f⟩
    rw [hxy] at hgap
    omega
  constructor
  · intro hI
    let := hI
    exact hn (MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
      (T.obj_indec y) f (T.obj_indec x).1)
  · intro hI
    let := hI
    exact hn (MagnitudeConjecture.CategoryTheory.isIso_of_isSplitEpi_from_indecomposable
      (T.obj_indec x) f (T.obj_indec y).1)
  · intro M g h hcomp
    by_contra! hn
    have hg := (T.isRadicalMorphism_iff_not_isSplitMono_from_obj g).2 hn.1
    have hh' := (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj h).2 hn.2
    exact hf (hcomp.symm.trans (radical_comp_eq_zero_of_height_gap T height hh
      (le_of_eq hgap) g h hg hh'))

end MagnitudeConjecture.FiniteTauMatrix
