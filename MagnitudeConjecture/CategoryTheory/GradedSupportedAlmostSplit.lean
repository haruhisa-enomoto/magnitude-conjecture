import MagnitudeConjecture.CategoryTheory.GradedAlmostSplitTransfer
import MagnitudeConjecture.CategoryTheory.GradedSupportedCategory
import MagnitudeConjecture.CategoryTheory.AlmostSplitLocalFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-! # Almost-split maps and nonprojectivity inside finite graded intervals -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A} {m : ℕ}

/-- The actual module underlying an interval-supported graded module. -/
def supportedUnderlying (m : ℕ) : SupportedCategory (R := R) m ⥤ ModuleCat.{u} A :=
  (intervalSupport (R := R) m).ι ⋙ shiftedUnderlying

instance (m : ℕ) : (supportedUnderlying (R := R) m).Faithful := by
  unfold supportedUnderlying
  infer_instance

/-- A homogeneous almost-split map stays almost split when both terms lie
in the interval; all degree-zero factorizations remain in this full subcategory. -/
theorem supported_rightAlmostSplit_of_underlying
    {X Y : SupportedCategory (R := R) m} (f : X ⟶ Y)
    (hf : IsRightAlmostSplit (ModuleCat.ofHom f.hom.val)) : IsRightAlmostSplit f := by
  apply MagnitudeConjecture.rightAlmostSplit_of_map_full_faithful (intervalSupport (R := R) m).ι
  apply homGrading.rightAlmostSplit_of_underlying f.hom
  exact MagnitudeConjecture.rightAlmostSplit_of_map_full_faithful (underlying (R := R)) hf

/-- An ungraded right-minimal homogeneous map is right minimal in the interval. -/
theorem supported_rightMinimal_of_underlying
    {X Y : SupportedCategory (R := R) m} (f : X ⟶ Y)
    (hf : IsRightMinimal (ModuleCat.ofHom f.hom.val)) : IsRightMinimal f := by
  apply MagnitudeConjecture.rightMinimal_of_map_full_faithful (intervalSupport (R := R) m).ι
  apply homGrading.rightMinimal_of_underlying f.hom
  exact MagnitudeConjecture.rightMinimal_of_map_full_faithful (underlying (R := R)) hf

/-- A nonsplit epimorphism of underlying modules inside the interval witnesses
nonprojectivity of its target in the interval category. -/
theorem supported_not_projective_of_underlying_nonsplit_epi
    {X Y : SupportedCategory (R := R) m} (f : X ⟶ Y)
    (hepi : Epi (ModuleCat.ofHom f.hom.val))
    (hn : ¬ IsSplitEpi (ModuleCat.ofHom f.hom.val)) : ¬ Projective Y := by
  intro hY
  letI : Projective Y := hY
  let F := supportedUnderlying (R := R) m
  letI : Epi f := F.epi_of_epi_map hepi
  letI : IsSplitEpi f := IsSplitEpi.mk'
    { section_ := Projective.factorThru (𝟙 Y) f
      id := Projective.factorThru_comp (𝟙 Y) f }
  exact hn (inferInstanceAs (IsSplitEpi (F.map f)))

end MagnitudeConjecture.Graded.FiniteGradedModule
