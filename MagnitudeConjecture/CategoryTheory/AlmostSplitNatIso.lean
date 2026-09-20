import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel

/-! # Almost-splitness and minimality under natural isomorphism -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {F G : C ⥤ D} (e : F ≅ G)

include e in
/-- Isomorphic realizations have the same right almost-split maps. -/
theorem rightAlmostSplit_map_of_natIso {X Y : C} (f : X ⟶ Y)
    (hf : IsRightAlmostSplit (G.map f)) : IsRightAlmostSplit (F.map f) := by
  rw [← NatIso.naturality_1 e.symm f]
  exact rightAlmostSplit_precomp_iso (e.app X)
    (hf.postcomp_iso (e.app Y).symm)

include e in
/-- Isomorphic realizations have the same right-minimal maps. -/
theorem rightMinimal_map_of_natIso [Preadditive D] {X Y : C} (f : X ⟶ Y)
    (hf : IsRightMinimal (G.map f)) : IsRightMinimal (F.map f) := by
  rw [← NatIso.naturality_1 e.symm f]
  exact (hf.postcomp_iso (e.app Y).symm).precomp_splitMono (e.app X).hom

end MagnitudeConjecture.CategoryTheory
