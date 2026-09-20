import MagnitudeConjecture.CategoryTheory.FiniteTauHeightIrreducible
import QuotientSubmoduleEquidistribution.CategoryTheory.HomIdealPowers

/-! # Radical powers determined by a finite tau-category height -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution QuotientSubmoduleEquidistribution.Iyama
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture.FiniteTauMatrix
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- Recursive incoming factorization places every Hom in its height power. -/
theorem hom_mem_radical_pow_of_height_gap
    (T : FiniteRightTauCategoryData C Ind) (height : Ind → ℕ)
    (hstep : ∀ y i, height (rightMiddleLabel T y i) + 1 = height y)
    (n : ℕ) {x y : Ind} (hgap : height x + n ≤ height y)
    (f : T.obj x ⟶ T.obj y) : f ∈ (T.radical.ideal.pow n).hom (T.obj x) (T.obj y) := by
  classical
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    have hn : ¬ IsIso f := by
      intro hI
      let := hI
      have hxy := T.obj_skeletal ⟨asIso f⟩
      rw [hxy] at hgap
      omega
    have hs : ¬ IsSplitEpi f := by
      intro hI
      let := hI
      exact hn (MagnitudeConjecture.CategoryTheory.isIso_of_isSplitEpi_from_indecomposable
        (T.obj_indec x) f (T.obj_indec y).1)
    let q := (T.rightMesh (T.obj y)).g ≫ (T.rightTermIso (T.obj y)).hom
    have hq := rightMesh_terminal_isRightAlmostSplit T y
    obtain ⟨g, hg⟩ := hq.factors f hs
    let e := Classical.choice (rightMiddleIso T y)
    let V := fun i ↦ T.obj (rightMiddleLabel T y i)
    let gi := fun i ↦ g ≫ e.hom ≫ biproduct.π V i
    let hi := fun i ↦ biproduct.ι V i ≫ e.inv ≫ q
    have hqr : IsRadicalMorphism q :=
      (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj q).mpr hq.not_isSplitEpi
    have hsum : f = ∑ i, gi i ≫ hi i := by
      rw [← hg]
      calc
        g ≫ q = g ≫ e.hom ≫ (𝟙 _) ≫ e.inv ≫ q := by simp
        _ = ∑ i, gi i ≫ hi i := by
          rw [← biproduct.total (f := V)]
          simp only [gi, hi, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    rw [hsum, HomIdeal.pow_succ]
    apply sum_mem
    intro i hi'
    apply HomIdeal.comp_mem_mul
    · exact ih (by have h := hstep y i; omega) (gi i)
    · apply (T.radical.mem_ideal_iff (hi i)).mpr
      exact isRadicalMorphism_precomp _ (isRadicalMorphism_precomp _ hqr)

/-- Powers beyond the available strict height increase vanish. -/
theorem radical_pow_eq_zero_of_height_gap
    (T : FiniteRightTauCategoryData C Ind) (height : Ind → ℕ)
    (hh : ∀ {x y : Ind} (f : T.obj x ⟶ T.obj y), f ≠ 0 → ¬ IsIso f → height x < height y)
    (n : ℕ) {x y : Ind} (hgap : height y < height x + n)
    (f : T.obj x ⟶ T.obj y)
    (hf : f ∈ (T.radical.ideal.pow n).hom (T.obj x) (T.obj y)) : f = 0 := by
  classical
  induction n generalizing x y with
  | zero =>
    by_contra hne
    by_cases hI : IsIso f
    · let := hI
      have hxy := T.obj_skeletal ⟨asIso f⟩
      rw [hxy] at hgap
      omega
    · have h := hh f hne hI
      omega
  | succ n ih =>
    change f ∈ (T.radical.ideal.pow n ⋆ᵢ T.radical.ideal).hom _ _ at hf
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
      obtain ⟨M, g, h, hg, hhr, rfl⟩ := hf
      obtain ⟨r, a, ⟨e⟩⟩ := T.obj_decomposition M
      let V := fun i : Fin r ↦ T.obj (a i)
      let gi := fun i ↦ g ≫ e.hom ≫ biproduct.π V i
      let hi := fun i ↦ biproduct.ι V i ≫ e.inv ≫ h
      have hz : ∀ i, gi i ≫ hi i = 0 := by
        intro i
        by_cases hhi : hi i = 0
        · rw [hhi, comp_zero]
        have hri : IsRadicalMorphism (hi i) := by
          exact isRadicalMorphism_precomp _ (isRadicalMorphism_precomp _
            ((T.radical.mem_ideal_iff h).mp hhr))
        have hni : ¬ IsIso (hi i) := by
          intro hI
          let := hI
          exact ((T.isRadicalMorphism_iff_not_isSplitEpi_to_obj (hi i)).mp hri) inferInstance
        have hheight := hh (hi i) hhi hni
        have hgi : gi i ∈ (T.radical.ideal.pow n).hom (T.obj x) (T.obj (a i)) :=
          (T.radical.ideal.pow n).postcomp (e.hom ≫ biproduct.π V i) hg
        have hzero := ih (by omega) (gi i) hgi
        rw [hzero, zero_comp]
      have hsum : g ≫ h = ∑ i, gi i ≫ hi i := by
        calc
          g ≫ h = g ≫ e.hom ≫ (𝟙 _) ≫ e.inv ≫ h := by simp
          _ = ∑ i, gi i ≫ hi i := by
            rw [← biproduct.total (f := V)]
            simp only [gi, hi, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      rw [hsum]
      exact Finset.sum_eq_zero (fun i _ ↦ hz i)
    | zero => rfl
    | add f g _ _ hf hg => rw [hf, hg, add_zero]
    | neg f _ hf => rw [hf, neg_zero]

end MagnitudeConjecture.FiniteTauMatrix
