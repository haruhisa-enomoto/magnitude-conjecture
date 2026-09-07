import MagnitudeConjecture.CategoryTheory.AlmostSplitLocalFunctor
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition

/-!
# Almost-split morphisms from finite indecomposable cores

A finite window of indecomposable objects cannot contain every decomposable
test object for an almost-split map: an arbitrary irrelevant direct summand
may always be added.  It is enough to lift the indecomposable summands on
which the test morphism has a nonzero component.  This file packages that
finite-core argument for fully faithful additive functors.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- Every indecomposable source relevant to testing right almost-splitness at
`F.obj Y` lies in the essential image.  Decomposable test objects are handled
by retaining only their nonzero indecomposable components. -/
def IsLocallyIndecomposableRightObjectClosedAt
    [HasBinaryBiproducts D]
    (F : C ⥤ D) (Y : C) : Prop :=
  ∀ (W : D), Indecomposable W → ∀ (g : W ⟶ F.obj Y),
    g ≠ 0 → ¬ IsSplitEpi g →
      ∃ V : C, Nonempty (F.obj V ≅ W)

/-- Every indecomposable target relevant to testing left almost-splitness at
`F.obj X` lies in the essential image. -/
def IsLocallyIndecomposableLeftObjectClosedAt
    [HasBinaryBiproducts D]
    (F : C ⥤ D) (X : C) : Prop :=
  ∀ (W : D), Indecomposable W → ∀ (g : F.obj X ⟶ W),
    g ≠ 0 → ¬ IsSplitMono g →
      ∃ V : C, Nonempty (F.obj V ≅ W)

/-- Full faithfulness and a finite indecomposable-core condition preserve a
right almost-split morphism. -/
theorem rightAlmostSplit_map_of_full_faithful_of_finiteIndecomposableCore
    [HasBinaryBiproducts D] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (decomposition : ∀ W : D,
      Nonempty (CategoryTheory.FiniteIndecomposableDecomposition W))
    {X Y : C} {f : X ⟶ Y}
    (hf : IsRightAlmostSplit f)
    (hclosed : IsLocallyIndecomposableRightObjectClosedAt F Y) :
    IsRightAlmostSplit (F.map f) := by
  classical
  constructor
  · intro hsplit
    exact hf.not_isSplitEpi ((F.isSplitEpi_iff f).1 hsplit)
  · intro W g hg
    by_cases hzero : g = 0
    · exact ⟨0, by simp [hzero]⟩
    obtain ⟨d⟩ := decomposition W
    let b (j : Fin d.n) : d.summand j ⟶ F.obj Y :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv ≫ g
    let Relevant (j : Fin d.n) : Prop := b j ≠ 0
    have hbNotSplit (q : {j : Fin d.n // Relevant j}) :
        ¬ IsSplitEpi (b q.1) := by
      intro hsplit
      apply hg
      letI : IsSplitEpi (b q.1) := hsplit
      exact IsSplitEpi.mk'
        { section_ := section_ (b q.1) ≫
            biproduct.ι d.summand q.1 ≫ d.isoBiproduct.inv
          id := by
            simpa only [b, Category.assoc] using IsSplitEpi.id (b q.1) }
    choose V e using fun q : {j : Fin d.n // Relevant j} ↦
      hclosed (d.summand q.1) (d.indecomposable q.1)
        (b q.1) q.2 (hbNotSplit q)
    let g' (q : {j : Fin d.n // Relevant j}) : V q ⟶ Y :=
      F.preimage ((Classical.choice (e q)).hom ≫ b q.1)
    have hg'NotSplit (q : {j : Fin d.n // Relevant j}) :
        ¬ IsSplitEpi (g' q) := by
      intro hsplit
      apply hbNotSplit q
      letI : IsSplitEpi (g' q) := hsplit
      have heq :
          (Classical.choice (e q)).inv ≫ F.map (g' q) = b q.1 := by
        simp [g']
      rw [← heq]
      infer_instance
    choose h hh using fun q : {j : Fin d.n // Relevant j} ↦
      hf.factors (g' q) (hg'NotSplit q)
    let c (j : Fin d.n) : d.summand j ⟶ F.obj X :=
      if hj : Relevant j then
        (Classical.choice (e ⟨j, hj⟩)).inv ≫ F.map (h ⟨j, hj⟩)
      else 0
    refine ⟨d.isoBiproduct.hom ≫ biproduct.desc c, ?_⟩
    rw [Category.assoc, ← d.isoBiproduct.hom_inv_id_assoc g]
    apply (cancel_epi d.isoBiproduct.hom).2
    apply biproduct.hom_ext'
    intro j
    simp only [biproduct.ι_desc_assoc]
    by_cases hj : Relevant j
    · let q : {i : Fin d.n // Relevant i} := ⟨j, hj⟩
      change c j ≫ F.map f = b j
      simp only [c, dif_pos hj]
      rw [Category.assoc, ← F.map_comp, hh q]
      simp [g', q]
    · have hbj : b j = 0 := not_ne_iff.mp hj
      change c j ≫ F.map f = b j
      simp [c, hj, hbj]

/-- The dual finite-core condition preserves a left almost-split morphism. -/
theorem leftAlmostSplit_map_of_full_faithful_of_finiteIndecomposableCore
    [HasBinaryBiproducts D] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (decomposition : ∀ W : D,
      Nonempty (CategoryTheory.FiniteIndecomposableDecomposition W))
    {X Y : C} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit f)
    (hclosed : IsLocallyIndecomposableLeftObjectClosedAt F X) :
    IsLeftAlmostSplit (F.map f) := by
  classical
  constructor
  · intro hsplit
    exact hf.not_isSplitMono ((F.isSplitMono_iff f).1 hsplit)
  · intro W g hg
    by_cases hzero : g = 0
    · exact ⟨0, by simp [hzero]⟩
    obtain ⟨d⟩ := decomposition W
    let b (j : Fin d.n) : F.obj X ⟶ d.summand j :=
      g ≫ d.isoBiproduct.hom ≫ biproduct.π d.summand j
    let Relevant (j : Fin d.n) : Prop := b j ≠ 0
    have hbNotSplit (q : {j : Fin d.n // Relevant j}) :
        ¬ IsSplitMono (b q.1) := by
      intro hsplit
      apply hg
      letI : IsSplitMono (b q.1) := hsplit
      exact IsSplitMono.mk'
        { retraction := d.isoBiproduct.hom ≫
            biproduct.π d.summand q.1 ≫ retraction (b q.1)
          id := by
            simpa only [b, Category.assoc] using IsSplitMono.id (b q.1) }
    choose V e using fun q : {j : Fin d.n // Relevant j} ↦
      hclosed (d.summand q.1) (d.indecomposable q.1)
        (b q.1) q.2 (hbNotSplit q)
    let g' (q : {j : Fin d.n // Relevant j}) : X ⟶ V q :=
      F.preimage (b q.1 ≫ (Classical.choice (e q)).inv)
    have hg'NotSplit (q : {j : Fin d.n // Relevant j}) :
        ¬ IsSplitMono (g' q) := by
      intro hsplit
      apply hbNotSplit q
      letI : IsSplitMono (g' q) := hsplit
      have heq :
          F.map (g' q) ≫ (Classical.choice (e q)).hom = b q.1 := by
        simp [g', Category.assoc]
      rw [← heq]
      infer_instance
    choose h hh using fun q : {j : Fin d.n // Relevant j} ↦
      hf.factors (g' q) (hg'NotSplit q)
    let c (j : Fin d.n) : F.obj Y ⟶ d.summand j :=
      if hj : Relevant j then
        F.map (h ⟨j, hj⟩) ≫ (Classical.choice (e ⟨j, hj⟩)).hom
      else 0
    refine ⟨biproduct.lift c ≫ d.isoBiproduct.inv, ?_⟩
    apply (cancel_mono d.isoBiproduct.hom).1
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      biproduct.lift_π]
    by_cases hj : Relevant j
    · let q : {i : Fin d.n // Relevant i} := ⟨j, hj⟩
      change F.map f ≫ c j = b j
      simp only [c, dif_pos hj]
      rw [← Category.assoc, ← F.map_comp, hh q]
      simp [g', q, Category.assoc]
    · have hbj : b j = 0 := not_ne_iff.mp hj
      change F.map f ≫ c j = b j
      simp [c, hj, hbj]

end MagnitudeConjecture
