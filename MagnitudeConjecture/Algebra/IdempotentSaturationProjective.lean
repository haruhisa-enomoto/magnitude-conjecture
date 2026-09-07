import MagnitudeConjecture.Algebra.IdempotentSaturation
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# The projective-dimension exit from idempotent saturation

For a submodule `N` of a projective module `P`, projective dimension at most
one of `P/N` forces `N` to be projective.  Applied to an idempotent saturation,
this isolates the exact final homological obligation in Iyama's construction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace MagnitudeConjecture.IdempotentSaturation

universe u

variable {R V : Type u} [Ring R] [AddCommGroup V] [Module R V]

/-- Dimension shifting in the form used at the end of Iyama's saturation
argument: in a short exact sequence, projective dimension at most one of the
middle term and at most two of the right term force projective dimension at
most one of the left term. -/
theorem projectiveDimensionLE_one_of_shortExact
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact)
    (hmiddle : HasProjectiveDimensionLE S.X₂ 1)
    (hright : HasProjectiveDimensionLE S.X₃ 2) :
    HasProjectiveDimensionLE S.X₁ 1 := by
  letI : HasProjectiveDimensionLE S.X₂ 1 := hmiddle
  letI : HasProjectiveDimensionLE S.X₃ 2 := hright
  exact hS.hasProjectiveDimensionLT_X₁ 2 inferInstance inferInstance

/-- Concrete monomorphism form of the same dimension shift.  This is the
precise step used after embedding a saturated quotient into its injective
hull. -/
theorem projectiveDimensionLE_one_of_injective
    {W Z : Type u} [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    (f : W →ₗ[R] Z) (hf : Function.Injective f)
    (hZ : HasProjectiveDimensionLE (ModuleCat.of R Z) 1)
    (hcokernel : HasProjectiveDimensionLE
      (ModuleCat.of R (Z ⧸ (LinearMap.range f))) 2) :
    HasProjectiveDimensionLE (ModuleCat.of R W) 1 := by
  let S : ShortComplex (ModuleCat.{u} R) :=
    ModuleCat.shortComplexOfCompEqZero f (LinearMap.range f).mkQ (by
      ext x
      simp)
  have hS : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact LinearMap.exact_map_mkQ_range f
    · exact hf
    · exact (LinearMap.range f).mkQ_surjective
  exact projectiveDimensionLE_one_of_shortExact hS hZ hcokernel

/-- A submodule of a projective module is projective as soon as the quotient
has projective dimension at most one. -/
theorem submodule_projective_of_quotient_projectiveDimensionLE_one
    (N : Submodule R V)
    (hV : Projective (ModuleCat.of R V))
    (hquotient :
      HasProjectiveDimensionLE (ModuleCat.of R (V ⧸ N)) 1) :
    Projective (ModuleCat.of R N) := by
  let S : ShortComplex (ModuleCat.{u} R) :=
    ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by
      ext x
      simp)
  have hS : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact LinearMap.exact_subtype_mkQ N
    · exact N.injective_subtype
    · exact N.mkQ_surjective
  letI : Projective S.X₂ := by
    change Projective (ModuleCat.of R V)
    exact hV
  letI : HasProjectiveDimensionLE S.X₃ 1 := by
    change HasProjectiveDimensionLE (ModuleCat.of R (V ⧸ N)) 1
    exact hquotient
  apply projective_iff_hasProjectiveDimensionLT_one.mpr
  exact hS.hasProjectiveDimensionLT_X₁ 1 inferInstance inferInstance

/-- In particular, an idempotent saturation is projective once its quotient
in the ambient projective has projective dimension at most one. -/
theorem saturation_projective_of_quotient_projectiveDimensionLE_one
    (e : R) (L : Submodule R V)
    (hV : Projective (ModuleCat.of R V))
    (hquotient : HasProjectiveDimensionLE
      (ModuleCat.of R (V ⧸ saturation e L)) 1) :
    Projective (ModuleCat.of R (saturation e L)) :=
  submodule_projective_of_quotient_projectiveDimensionLE_one
    (saturation e L) hV hquotient

end MagnitudeConjecture.IdempotentSaturation
