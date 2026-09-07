import MagnitudeConjecture.CategoryTheory.AlmostSplitEquivalence
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Almost-split morphisms under locally closed functors

For preservation of a right almost-split map, essential surjectivity is needed
only for objects carrying a nonzero nonsplit map to its endpoint.  The left
statement is dual.  These local conditions isolate the role of the first Hom
neighborhoods in the covering-control argument, while minimality of either
map is preserved by full faithfulness alone.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v u' v'

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- Every object relevant to testing right almost-splitness at `F.obj Y` lies
in the essential image.  The zero map is excluded because it factors
trivially and needs no object lift. -/
def IsLocallyRightObjectClosedAt (F : C ⥤ D) (Y : C) : Prop :=
  ∀ (W : D) (g : W ⟶ F.obj Y),
    g ≠ 0 → ¬ IsSplitEpi g →
      ∃ V : C, Nonempty (F.obj V ≅ W)

/-- Every object relevant to testing left almost-splitness at `F.obj X` lies
in the essential image. -/
def IsLocallyLeftObjectClosedAt (F : C ⥤ D) (X : C) : Prop :=
  ∀ (W : D) (g : F.obj X ⟶ W),
    g ≠ 0 → ¬ IsSplitMono g →
      ∃ V : C, Nonempty (F.obj V ≅ W)

/-- Full faithfulness and local source-object closure preserve a right
almost-split morphism. -/
theorem rightAlmostSplit_map_of_full_faithful_of_locallyRightObjectClosed
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesZeroMorphisms]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsRightAlmostSplit f)
    (hclosed : IsLocallyRightObjectClosedAt F Y) :
    IsRightAlmostSplit (F.map f) := by
  constructor
  · intro hsplit
    exact hf.not_isSplitEpi ((F.isSplitEpi_iff f).1 hsplit)
  · intro W g hg
    by_cases hzero : g = 0
    · exact ⟨0, by simp [hzero]⟩
    obtain ⟨V, ⟨e⟩⟩ := hclosed W g hzero hg
    let g' : V ⟶ Y := F.preimage (e.hom ≫ g)
    have hg' : ¬ IsSplitEpi g' := by
      intro hsplit
      apply hg
      letI : IsSplitEpi g' := hsplit
      have hgeq : e.inv ≫ F.map g' = g := by
        simp [g']
      rw [← hgeq]
      infer_instance
    obtain ⟨h', hh'⟩ := hf.factors g' hg'
    refine ⟨e.inv ≫ F.map h', ?_⟩
    rw [Category.assoc, ← F.map_comp, hh']
    simp [g']

/-- Full faithfulness and local target-object closure preserve a left
almost-split morphism. -/
theorem leftAlmostSplit_map_of_full_faithful_of_locallyLeftObjectClosed
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesZeroMorphisms]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit f)
    (hclosed : IsLocallyLeftObjectClosedAt F X) :
    IsLeftAlmostSplit (F.map f) := by
  constructor
  · intro hsplit
    exact hf.not_isSplitMono ((F.isSplitMono_iff f).1 hsplit)
  · intro W g hg
    by_cases hzero : g = 0
    · exact ⟨0, by simp [hzero]⟩
    obtain ⟨V, ⟨e⟩⟩ := hclosed W g hzero hg
    let g' : X ⟶ V := F.preimage (g ≫ e.inv)
    have hg' : ¬ IsSplitMono g' := by
      intro hsplit
      apply hg
      letI : IsSplitMono g' := hsplit
      have hgeq : F.map g' ≫ e.hom = g := by
        simp [g', Category.assoc]
      rw [← hgeq]
      infer_instance
    obtain ⟨h', hh'⟩ := hf.factors g' hg'
    refine ⟨F.map h' ≫ e.hom, ?_⟩
    rw [← Category.assoc, ← F.map_comp, hh']
    simp [g', Category.assoc]

/-- Full faithfulness reflects right almost-splitness.  This is the
restriction direction used for a full control window containing both terms
of an ambient sink map. -/
theorem rightAlmostSplit_of_map_full_faithful
    (F : Functor C D) [F.Full] [F.Faithful] [F.PreservesZeroMorphisms]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsRightAlmostSplit (F.map f)) :
    IsRightAlmostSplit f := by
  constructor
  · intro hsplit
    letI : IsSplitEpi f := hsplit
    haveI : IsSplitEpi (F.map f) := inferInstance
    exact hf.not_isSplitEpi inferInstance
  · intro W g hg
    have hmapg : ¬ IsSplitEpi (F.map g) := by
      intro hsplit
      exact hg ((F.isSplitEpi_iff g).1 hsplit)
    obtain ⟨h, hh⟩ := hf.factors (F.map g) hmapg
    refine ⟨F.preimage h, ?_⟩
    apply F.map_injective
    simpa only [F.map_comp, F.map_preimage] using hh

/-- Full faithfulness reflects left almost-splitness. -/
theorem leftAlmostSplit_of_map_full_faithful
    (F : Functor C D) [F.Full] [F.Faithful] [F.PreservesZeroMorphisms]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit (F.map f)) :
    IsLeftAlmostSplit f := by
  constructor
  · intro hsplit
    letI : IsSplitMono f := hsplit
    haveI : IsSplitMono (F.map f) := inferInstance
    exact hf.not_isSplitMono inferInstance
  · intro W g hg
    have hmapg : ¬ IsSplitMono (F.map g) := by
      intro hsplit
      exact hg ((F.isSplitMono_iff g).1 hsplit)
    obtain ⟨h, hh⟩ := hf.factors (F.map g) hmapg
    refine ⟨F.preimage h, ?_⟩
    apply F.map_injective
    simpa only [F.map_comp, F.map_preimage] using hh

omit [HasZeroMorphisms C] [HasZeroMorphisms D] in
/-- Full faithfulness preserves right minimality. -/
theorem rightMinimal_map_of_full_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsRightMinimal f) :
    IsRightMinimal (F.map f) := by
  intro e he
  let e' : X ⟶ X := F.preimage e
  have he' : e' ≫ f = f := by
    apply F.map_injective
    simpa only [e', F.map_comp, F.map_preimage] using he
  letI : IsIso e' := hf e' he'
  haveI : IsIso (F.map e') := F.map_isIso e'
  have heq : F.map e' = e := F.map_preimage e
  rw [← heq]
  infer_instance

omit [HasZeroMorphisms C] [HasZeroMorphisms D] in
/-- Full faithfulness reflects right minimality. -/
theorem rightMinimal_of_map_full_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsRightMinimal (F.map f)) :
    IsRightMinimal f := by
  intro e he
  haveI : IsIso (F.map e) := hf (F.map e) (by
    rw [← F.map_comp, he])
  exact isIso_of_reflects_iso e F

omit [HasZeroMorphisms C] [HasZeroMorphisms D] in
/-- Full faithfulness preserves left minimality. -/
theorem leftMinimal_map_of_full_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsLeftMinimal f) :
    IsLeftMinimal (F.map f) := by
  intro e he
  let e' : Y ⟶ Y := F.preimage e
  have he' : f ≫ e' = f := by
    apply F.map_injective
    simpa only [e', F.map_comp, F.map_preimage] using he
  letI : IsIso e' := hf e' he'
  haveI : IsIso (F.map e') := F.map_isIso e'
  have heq : F.map e' = e := F.map_preimage e
  rw [← heq]
  infer_instance

end MagnitudeConjecture
