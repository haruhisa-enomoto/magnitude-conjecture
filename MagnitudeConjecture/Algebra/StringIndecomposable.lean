import MagnitudeConjecture.Algebra.StringGraphComponentNilpotence
import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleBiproducts

/-!
# Indecomposability of string modules

The endomorphism algebra of a literal string module is the direct sum of its
scalar identity direction and the nilpotent ideal spanned by proper graph
components.  It is therefore local, so every string module is
indecomposable.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The endomorphism ring of every literal string module is local. -/
theorem rightModule_end_isLocalRing
    (C : Word R) (hmono : IsMonomial R) :
    IsLocalRing (End (C.rightModule hmono)) := by
  letI : Nontrivial (End (C.rightModule hmono)) :=
    ⟨⟨1, 0, fun h ↦ C.rightModule_not_isZero hmono
      ((IsZero.iff_id_eq_zero (C.rightModule hmono)).2 h)⟩⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  obtain ⟨r, hr, hfr⟩ :=
    C.exists_eq_smul_id_add_mem_properComponentSubspace hmono f
  let rEnd : End (C.rightModule hmono) := CategoryTheory.End.of r
  have hrnil : IsNilpotent rEnd :=
    C.isNilpotent_of_mem_properMorphismCoefficientComponentSubspace
      hmono rEnd hr
  let c := C.diagonalMorphismCoefficientLinearMap hmono f
  have hfrEnd : f = c • (1 : End (C.rightModule hmono)) + rEnd := by
    change (show C.rightModule hmono ⟶ C.rightModule hmono from f) =
      c • 𝟙 (C.rightModule hmono) + r
    exact hfr
  by_cases hc : c = 0
  · right
    have hfr' : f = rEnd := by
      simpa only [hc, zero_smul, zero_add] using hfrEnd
    rw [hfr']
    exact hrnil.isUnit_one_sub
  · left
    have hu : IsUnit (c • (1 : End (C.rightModule hmono))) := by
      rw [Algebra.smul_def]
      exact (isUnit_iff_ne_zero.mpr hc).map
        (algebraMap k (End (C.rightModule hmono)))
    have hcomm : Commute rEnd (c • (1 : End (C.rightModule hmono))) := by
      rw [Algebra.smul_def]
      exact (Algebra.commutes c rEnd).symm
    rw [hfrEnd]
    simpa only [add_comm] using
      hrnil.isUnit_add_right_of_commute hu hcomm

/-- A string-module endomorphism with nonzero diagonal graph coordinate is
an isomorphism. -/
theorem isIso_of_diagonalMorphismCoefficientLinearMap_ne_zero
    (C : Word R) (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ C.rightModule hmono)
    (hf : C.diagonalMorphismCoefficientLinearMap hmono f ≠ 0) :
    IsIso f := by
  obtain ⟨r, hr, hfr⟩ :=
    C.exists_eq_smul_id_add_mem_properComponentSubspace hmono f
  let rEnd : End (C.rightModule hmono) := CategoryTheory.End.of r
  have hrnil : IsNilpotent rEnd :=
    C.isNilpotent_of_mem_properMorphismCoefficientComponentSubspace
      hmono rEnd hr
  let c := C.diagonalMorphismCoefficientLinearMap hmono f
  have hfrEnd : f = c • (1 : End (C.rightModule hmono)) + rEnd := by
    change (show C.rightModule hmono ⟶ C.rightModule hmono from f) =
      c • 𝟙 (C.rightModule hmono) + r
    exact hfr
  have hu : IsUnit (c • (1 : End (C.rightModule hmono))) := by
    rw [Algebra.smul_def]
    exact (isUnit_iff_ne_zero.mpr hf).map
      (algebraMap k (End (C.rightModule hmono)))
  have hcomm : Commute rEnd (c • (1 : End (C.rightModule hmono))) := by
    rw [Algebra.smul_def]
    exact (Algebra.commutes c rEnd).symm
  apply (CategoryTheory.isUnit_iff_isIso f).1
  rw [hfrEnd]
  simpa only [add_comm] using
    hrnil.isUnit_add_right_of_commute hu hcomm

/-- Every literal string module is indecomposable in the raw functor
category. -/
theorem rightModule_indecomposable
    (C : Word R) (hmono : IsMonomial R) :
    Indecomposable (C.rightModule hmono) := by
  letI : IsLocalRing (End (C.rightModule hmono)) :=
    C.rightModule_end_isLocalRing hmono
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _

variable [Fintype Q]

/-- Every literal string module is indecomposable in the finite-dimensional
linear-module category used by the campaign. -/
theorem finiteRightModule_indecomposable
    (C : Word R) (hmono : IsMonomial R) :
    Indecomposable (C.finiteRightModule hmono) := by
  let Jlinear :=
    (CoveringHom.IsLinearModule (C := (Category R)ᵒᵖ) k).ι
  have hraw : Indecomposable (C.rightModule hmono) :=
    C.rightModule_indecomposable hmono
  have hlinear : Indecomposable (C.rightLinearModule hmono) := by
    apply MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
      Jlinear (C.rightLinearModule hmono)
    exact hraw
  let Jfinite :=
    (CoveringHom.IsFiniteDimensionalModule (C := (Category R)ᵒᵖ) k).ι
  apply MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
    Jfinite (C.finiteRightModule hmono)
  exact hlinear

end MagnitudeConjecture.BoundQuiver.StringWord.Word
