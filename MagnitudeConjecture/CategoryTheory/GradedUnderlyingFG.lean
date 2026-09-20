import MagnitudeConjecture.CategoryTheory.GradedSupportedAlmostSplit
import Mathlib.Algebra.Category.FGModuleCat.Basic

/-! # Finitely generated underlying modules of finite graded modules -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- Forget the grading into the finitely generated module category. -/
def underlyingFG : FiniteGradedModule.{u,u} R ⥤ FGModuleCat.{u} A where
  obj X := ⟨X.module, Module.Finite.of_restrictScalars_finite k A X.module⟩
  map f := ObjectProperty.homMk (ModuleCat.ofHom f)

instance : (underlyingFG (R := R)).Full where
  map_surjective f := ⟨f.hom.hom, rfl⟩
instance : (underlyingFG (R := R)).Faithful where
  map_injective h := congrArg (fun f ↦ f.hom.hom) h
instance : (underlyingFG (R := R)).Additive where
  map_add := by intros; rfl

/-- The graded transfer only needs almost-splitness among finitely generated
modules, which is the scope of the standard-form construction. -/
theorem rightAlmostSplit_of_underlyingFG
    {X Y : ShiftedModule.{u,u} (R := R)} (f : X ⟶ Y)
    (hf : IsRightAlmostSplit ((underlyingFG (R := R)).map f.val)) :
    IsRightAlmostSplit f := by
  apply homGrading.rightAlmostSplit_of_underlying f
  exact MagnitudeConjecture.rightAlmostSplit_of_map_full_faithful (underlyingFG (R := R)) hf

theorem rightMinimal_of_underlyingFG
    {X Y : ShiftedModule.{u,u} (R := R)} (f : X ⟶ Y)
    (hf : IsRightMinimal ((underlyingFG (R := R)).map f.val)) :
    IsRightMinimal f := by
  apply homGrading.rightMinimal_of_underlying f
  exact MagnitudeConjecture.rightMinimal_of_map_full_faithful (underlyingFG (R := R)) hf

/-- A finite-module almost-split map restricts to any interval containing its terms. -/
theorem supported_rightAlmostSplit_of_underlyingFG {m : ℕ}
    {X Y : SupportedCategory (R := R) m} (f : X ⟶ Y)
    (hf : IsRightAlmostSplit ((underlyingFG (R := R)).map f.hom.val)) :
    IsRightAlmostSplit f := by
  apply MagnitudeConjecture.rightAlmostSplit_of_map_full_faithful (intervalSupport (R := R) m).ι
  exact rightAlmostSplit_of_underlyingFG f.hom hf

theorem supported_rightMinimal_of_underlyingFG {m : ℕ}
    {X Y : SupportedCategory (R := R) m} (f : X ⟶ Y)
    (hf : IsRightMinimal ((underlyingFG (R := R)).map f.hom.val)) :
    IsRightMinimal f := by
  apply MagnitudeConjecture.rightMinimal_of_map_full_faithful (intervalSupport (R := R) m).ι
  exact rightMinimal_of_underlyingFG f.hom hf

end MagnitudeConjecture.Graded.FiniteGradedModule
