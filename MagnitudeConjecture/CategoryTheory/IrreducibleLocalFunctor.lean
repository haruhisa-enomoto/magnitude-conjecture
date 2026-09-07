import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleCofinite
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Irreducible morphisms under locally closed functors

A fully faithful functor always reflects irreducible morphisms, but need not
preserve them: an image morphism might acquire a factorization through an
object outside the essential image.  For one fixed morphism, preservation
only requires the intermediate objects of factorizations whose two factors
are nonsplit to lie in the essential image.  This is the precise categorical
role of the manuscript's third Hom-neighborhood in the covering argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- The essential image of `F` contains every intermediate object needed to
test irreducibility of `F.map f`.  Factorizations already split on one side
need no lifting and are omitted from the condition. -/
def IsLocallyFactorizationClosedAt
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ (M : D) (g : F.obj X ⟶ M) (h : M ⟶ F.obj Y),
    g ≫ h = F.map f →
      ¬ IsSplitMono g → ¬ IsSplitEpi h →
        ∃ W : C, Nonempty (F.obj W ≅ M)

/-- Full faithfulness reflects irreducibility without any hypothesis on
objects outside the image. -/
theorem irreducible_of_map_of_full_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsIrreducibleMorphism (F.map f)) :
    IsIrreducibleMorphism f := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hsplit
    apply hf.not_isSplitMono
    exact (F.isSplitMono_iff f).2 hsplit
  · intro hsplit
    apply hf.not_isSplitEpi
    exact (F.isSplitEpi_iff f).2 hsplit
  · intro M g h hgh
    have hmap : F.map g ≫ F.map h = F.map f := by
      simp only [← F.map_comp, hgh]
    rcases hf.factorization (F.map g) (F.map h) hmap with hg | hh
    · exact Or.inl ((F.isSplitMono_iff g).1 hg)
    · exact Or.inr ((F.isSplitEpi_iff h).1 hh)

/-- A fully faithful functor preserves irreducibility at a morphism when all
new nonsplit factorizations have intermediate object in its essential image. -/
theorem irreducible_map_of_full_faithful_of_locallyFactorizationClosed
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsIrreducibleMorphism f)
    (hclosed : IsLocallyFactorizationClosedAt F f) :
    IsIrreducibleMorphism (F.map f) := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hsplit
    exact hf.not_isSplitMono ((F.isSplitMono_iff f).1 hsplit)
  · intro hsplit
    exact hf.not_isSplitEpi ((F.isSplitEpi_iff f).1 hsplit)
  · intro M g h hgh
    by_cases hg : IsSplitMono g
    · exact Or.inl hg
    by_cases hh : IsSplitEpi h
    · exact Or.inr hh
    obtain ⟨W, ⟨e⟩⟩ := hclosed M g h hgh hg hh
    let g' : X ⟶ W := F.preimage (g ≫ e.inv)
    let h' : W ⟶ Y := F.preimage (e.hom ≫ h)
    have hfactor : g' ≫ h' = f := by
      apply F.map_injective
      simp only [g', h', F.map_comp, F.map_preimage]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hgh]
    rcases hf.factorization g' h' hfactor with hg' | hh'
    · left
      letI : IsSplitMono g' := hg'
      have hgeq : F.map g' ≫ e.hom = g := by
        simp [g', Category.assoc]
      rw [← hgeq]
      infer_instance
    · right
      letI : IsSplitEpi h' := hh'
      have hheq : e.inv ≫ F.map h' = h := by
        simp [h']
      rw [← hheq]
      infer_instance

/-- Under local factorization closure, full faithfulness identifies
irreducibility on the nose. -/
theorem isIrreducibleMorphism_map_iff_of_locallyFactorizationClosed
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hclosed : IsLocallyFactorizationClosedAt F f) :
    IsIrreducibleMorphism (F.map f) ↔ IsIrreducibleMorphism f :=
  ⟨fun hf ↦
      irreducible_of_map_of_full_faithful F hf,
    fun hf ↦
      irreducible_map_of_full_faithful_of_locallyFactorizationClosed
        F hf hclosed⟩

end MagnitudeConjecture
