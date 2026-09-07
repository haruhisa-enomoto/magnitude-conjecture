import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitUniqueness

/-!
# Almost-split morphisms under equivalence

An ordinary categorical equivalence preserves right and left almost-split
morphisms and their minimality.  The proof uses essential surjectivity to
pull an arbitrary test object back across the equivalence and full
faithfulness to reflect splittings.

This is the covariant companion of the anti-equivalence argument in
`QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitDuality`;
only the two transport lemmas required by the support-algebra passage are
included here.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]

/-- A right almost-split morphism remains right almost split after applying
an equivalence. -/
theorem IsRightAlmostSplit.map_equivalence
    {X Y : C} {f : X ⟶ Y} (hf : IsRightAlmostSplit f)
    (E : C ≌ D) :
    IsRightAlmostSplit (E.functor.map f) := by
  constructor
  · intro hs
    exact hf.not_isSplitEpi ((E.functor.isSplitEpi_iff f).mp hs)
  · intro W g hg
    let e : E.functor.obj (E.inverse.obj W) ≅ W := E.counitIso.app W
    let g' : E.functor.obj (E.inverse.obj W) ⟶ E.functor.obj Y :=
      e.hom ≫ g
    let g₀ : E.inverse.obj W ⟶ Y := E.functor.preimage g'
    have hg₀map : E.functor.map g₀ = g' := E.functor.map_preimage g'
    have hg₀ : ¬ IsSplitEpi g₀ := by
      intro hs
      apply hg
      letI : IsSplitEpi g₀ := hs
      letI : IsSplitEpi (E.functor.map g₀) := inferInstance
      haveI : IsSplitEpi g' := hg₀map ▸ inferInstance
      have hgeq : e.inv ≫ g' = g := by simp [g']
      rw [← hgeq]
      infer_instance
    obtain ⟨h₀, hh₀⟩ := hf.factors g₀ hg₀
    refine ⟨e.inv ≫ E.functor.map h₀, ?_⟩
    rw [Category.assoc, ← E.functor.map_comp, hh₀, hg₀map]
    simp [g']

/-- Right almost-splitness is reflected by a fully faithful functor. -/
theorem IsRightAlmostSplit.of_map_fully_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsRightAlmostSplit (F.map f)) :
    IsRightAlmostSplit f := by
  constructor
  · intro hs
    apply hf.not_isSplitEpi
    exact (F.isSplitEpi_iff f).mpr hs
  · intro W g hg
    have hgmap : ¬ IsSplitEpi (F.map g) := by
      intro hs
      exact hg ((F.isSplitEpi_iff g).mp hs)
    obtain ⟨h, hh⟩ := hf.factors (F.map g) hgmap
    refine ⟨F.preimage h, ?_⟩
    apply F.map_injective
    rw [F.map_comp, F.map_preimage, hh]

/-- Right almost-splitness is reflected by an equivalence. -/
theorem IsRightAlmostSplit.of_map_equivalence
    {X Y : C} {f : X ⟶ Y} (E : C ≌ D)
    (hf : IsRightAlmostSplit (E.functor.map f)) :
    IsRightAlmostSplit f :=
  hf.of_map_fully_faithful E.functor

/-- A left almost-split morphism remains left almost split after applying an
equivalence. -/
theorem IsLeftAlmostSplit.map_equivalence
    {X Y : C} {f : X ⟶ Y} (hf : IsLeftAlmostSplit f)
    (E : C ≌ D) :
    IsLeftAlmostSplit (E.functor.map f) := by
  constructor
  · intro hs
    exact hf.not_isSplitMono ((E.functor.isSplitMono_iff f).mp hs)
  · intro W g hg
    let e : E.functor.obj (E.inverse.obj W) ≅ W := E.counitIso.app W
    let g' : E.functor.obj X ⟶ E.functor.obj (E.inverse.obj W) :=
      g ≫ e.inv
    let g₀ : X ⟶ E.inverse.obj W := E.functor.preimage g'
    have hg₀map : E.functor.map g₀ = g' := E.functor.map_preimage g'
    have hg₀ : ¬ IsSplitMono g₀ := by
      intro hs
      apply hg
      letI : IsSplitMono g₀ := hs
      haveI : IsSplitMono (E.functor.map g₀) := inferInstance
      haveI : IsSplitMono g' := hg₀map ▸ inferInstance
      have hgeq : g' ≫ e.hom = g := by simp [g', Category.assoc]
      rw [← hgeq]
      infer_instance
    obtain ⟨h₀, hh₀⟩ := hf.factors g₀ hg₀
    refine ⟨E.functor.map h₀ ≫ e.hom, ?_⟩
    rw [← Category.assoc, ← E.functor.map_comp, hh₀, hg₀map]
    simp [g', Category.assoc]

/-- Left almost-splitness is reflected by a fully faithful functor. -/
theorem IsLeftAlmostSplit.of_map_fully_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit (F.map f)) :
    IsLeftAlmostSplit f := by
  constructor
  · intro hs
    apply hf.not_isSplitMono
    exact (F.isSplitMono_iff f).mpr hs
  · intro W g hg
    have hgmap : ¬ IsSplitMono (F.map g) := by
      intro hs
      exact hg ((F.isSplitMono_iff g).mp hs)
    obtain ⟨h, hh⟩ := hf.factors (F.map g) hgmap
    refine ⟨F.preimage h, ?_⟩
    apply F.map_injective
    rw [F.map_comp, F.map_preimage, hh]

/-- Left almost-splitness is reflected by an equivalence. -/
theorem IsLeftAlmostSplit.of_map_equivalence
    {X Y : C} {f : X ⟶ Y} (E : C ≌ D)
    (hf : IsLeftAlmostSplit (E.functor.map f)) :
    IsLeftAlmostSplit f :=
  hf.of_map_fully_faithful E.functor

/-- Postcomposition by an isomorphism preserves left almost-splitness. -/
theorem IsLeftAlmostSplit.postcomp_iso
    {X Y Y' : C} {f : X ⟶ Y} (hf : IsLeftAlmostSplit f)
    (e : Y ≅ Y') :
    IsLeftAlmostSplit (f ≫ e.hom) := by
  constructor
  · intro hs
    apply hf.not_isSplitMono
    letI : IsSplitMono (f ≫ e.hom) := hs
    haveI : IsSplitMono ((f ≫ e.hom) ≫ e.inv) := inferInstance
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      (inferInstance : IsSplitMono ((f ≫ e.hom) ≫ e.inv))
  · intro Z g hg
    obtain ⟨h, hh⟩ := hf.factors g hg
    exact ⟨e.inv ≫ h, by
      rw [Category.assoc, Iso.hom_inv_id_assoc, hh]⟩

/-- Right minimality is preserved after applying an equivalence. -/
theorem IsRightMinimal.map_equivalence
    {X Y : C} {f : X ⟶ Y} (hf : IsRightMinimal f)
    (E : C ≌ D) :
    IsRightMinimal (E.functor.map f) := by
  intro e he
  let e' : X ⟶ X := E.functor.preimage e
  have he' : e' ≫ f = f := by
    apply E.functor.map_injective
    simpa only [e', E.functor.map_comp, E.functor.map_preimage] using he
  letI : IsIso e' := hf e' he'
  haveI : IsIso (E.functor.map e') := E.functor.map_isIso e'
  have heq : E.functor.map e' = e := E.functor.map_preimage e
  rw [← heq]
  infer_instance

/-- Left minimality is preserved after applying an equivalence. -/
theorem IsLeftMinimal.map_equivalence
    {X Y : C} {f : X ⟶ Y} (hf : IsLeftMinimal f)
    (E : C ≌ D) :
    IsLeftMinimal (E.functor.map f) := by
  intro e he
  let e' : Y ⟶ Y := E.functor.preimage e
  have he' : f ≫ e' = f := by
    apply E.functor.map_injective
    simpa only [e', E.functor.map_comp, E.functor.map_preimage] using he
  letI : IsIso e' := hf e' he'
  haveI : IsIso (E.functor.map e') := E.functor.map_isIso e'
  have heq : E.functor.map e' = e := E.functor.map_preimage e
  rw [← heq]
  infer_instance

end QuotientSubmoduleEquidistribution
