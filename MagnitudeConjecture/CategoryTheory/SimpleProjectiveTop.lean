import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel

/-!
# Simple quotients of indecomposable projectives

A nonzero morphism from a projective object with local endomorphism ring to
a simple object kills every monic right almost-split subobject.  This is the
abstract form of the fact that every simple quotient of an indecomposable
projective is its top.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A nonzero map from an indecomposable projective to a simple object kills
a monic right almost-split morphism into that projective. -/
theorem rightAlmostSplit_comp_nonzero_to_simple_eq_zero
    {R P T : C} (r : R ⟶ P) [Mono r] [Projective P]
    [IsLocalRing (End P)] (hr : IsRightAlmostSplit r)
    [Simple T] (p : P ⟶ T) (hp : p ≠ 0) :
    r ≫ p = 0 := by
  by_contra hrp
  letI : Epi p := epi_of_nonzero_to_simple hp
  letI : Epi (r ≫ p) := epi_of_nonzero_to_simple hrp
  let s := Projective.factorThru p (r ≫ p)
  have he : (s ≫ r) ≫ p = p := by
    rw [Category.assoc, Projective.factorThru_comp]
  let e : End P := s ≫ r
  let e' : End P := 1 - e
  have he'p : e' ≫ p = 0 := by
    dsimp only [e', e]
    rw [End.one_def, Preadditive.sub_comp, Category.id_comp, he, sub_self]
  have hone_sub_e_not_unit : ¬ IsUnit (1 - e) := by
    intro hunit
    have hunit' : IsUnit e' := by simpa only [e'] using hunit
    letI : IsIso e' := (isUnit_iff_isIso e').1 hunit'
    apply hp
    rw [← IsIso.inv_hom_id_assoc e' p, he'p, comp_zero]
  have heunit : IsUnit e := by
    apply (IsLocalRing.isUnit_or_isUnit_of_isUnit_add
      (show IsUnit (e + (1 - e)) by rw [add_sub_cancel]; exact isUnit_one)).resolve_right
    exact hone_sub_e_not_unit
  letI : IsIso (s ≫ r) := by
    simpa only [e] using (isUnit_iff_isIso e).1 heunit
  apply hr.not_isSplitEpi
  exact IsSplitEpi.mk'
    { section_ := inv (s ≫ r) ≫ s
      id := by rw [Category.assoc, IsIso.inv_hom_id] }

end MagnitudeConjecture.CategoryTheory
