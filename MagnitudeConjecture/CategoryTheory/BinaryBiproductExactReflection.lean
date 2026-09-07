import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Reflecting exact binary-biproduct complexes

This file packages the bookkeeping needed to move an explicit exact complex
through a faithful additive inclusion.  The inclusion need not preserve the
chosen binary biproduct definitionally: its canonical `mapBiprod` isomorphism
identifies the mapped complex with the explicit target complex.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- A three-term complex whose middle object is a binary biproduct. -/
def binaryBiproductShortComplex
    {X A B Y : C}
    (fA : X ⟶ A) (fB : X ⟶ B)
    (gA : A ⟶ Y) (gB : B ⟶ Y)
    (hzero : fA ≫ gA + fB ≫ gB = 0) : ShortComplex C :=
  ShortComplex.mk (biprod.lift fA fB) (biprod.desc gA gB) (by
    rw [biprod.lift_desc]
    exact hzero)

/-- Exactness of an explicit mapped binary-biproduct complex reflects
through a faithful additive functor, even though the functor's image of the
chosen biproduct is only canonically isomorphic to the target biproduct. -/
theorem binaryBiproductShortComplex_exact_of_map
    (F : C ⥤ D) [F.Additive] [F.Faithful]
    {X A B Y : C} [PreservesBinaryBiproduct A B F]
    (fA : X ⟶ A) (fB : X ⟶ B)
    (gA : A ⟶ Y) (gB : B ⟶ Y)
    (hzero : fA ≫ gA + fB ≫ gB = 0)
    (hmap :
      (binaryBiproductShortComplex
        (F.map fA) (F.map fB) (F.map gA) (F.map gB) (by
          rw [← F.map_comp, ← F.map_comp, ← F.map_add, hzero, F.map_zero])).Exact) :
    (binaryBiproductShortComplex fA fB gA gB hzero).Exact := by
  let hzeroMap :
      F.map fA ≫ F.map gA + F.map fB ≫ F.map gB = 0 := by
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, hzero, F.map_zero]
  let e :
      (binaryBiproductShortComplex fA fB gA gB hzero).map F ≅
        binaryBiproductShortComplex
          (F.map fA) (F.map fB) (F.map gA) (F.map gB) hzeroMap := by
    refine ShortComplex.isoMk (Iso.refl (F.obj X)) (F.mapBiprod A B)
      (Iso.refl (F.obj Y)) ?_ ?_
    · simp only [binaryBiproductShortComplex, ShortComplex.map_f, Iso.refl_hom]
      exact (Category.id_comp _).trans
        (biprod.map_lift_mapBiprod F A B fA fB).symm
    · simp only [binaryBiproductShortComplex, ShortComplex.map_g, Iso.refl_hom]
      exact (biprod.mapBiprod_hom_desc F A B gA gB).trans
        (Category.comp_id _).symm
  apply F.reflects_exact_of_faithful
    (binaryBiproductShortComplex fA fB gA gB hzero)
  exact ShortComplex.exact_of_iso e.symm hmap

end MagnitudeConjecture.CategoryTheory
