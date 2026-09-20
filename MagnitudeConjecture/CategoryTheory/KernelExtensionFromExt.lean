import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Ext vanishing extends maps out of kernels -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace MagnitudeConjecture.FiniteKernel
universe v w t
variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{t} C]

/-- If Ext¹(U,Z) vanishes for every subobject U of I, every map ker f to Z
extends to an endomorphism of Z, for every f from Z to I. -/
theorem kernel_extension_of_ext_vanishing {Z I : C} (f : Z ⟶ I)
    (hext : ∀ (U : C) (j : U ⟶ I), Mono j → ∀ xi : Ext.{t} U Z 1, xi = 0) :
    ∀ h : kernel f ⟶ Z, ∃ a : Z ⟶ Z, kernel.ι f ≫ a = h := by
  let S : ShortComplex C := ShortComplex.mk (kernel.ι f)
    (cokernel.π (kernel.ι f)) (by simp)
  have hs : S.ShortExact := { exact := ShortComplex.exact_cokernel (kernel.ι f) }
  intro h
  have hz : hs.extClass.comp (Ext.mk₀ h) (rfl : 1 + 0 = 1) = 0 :=
    hext (Abelian.coimage f) (Abelian.factorThruCoimage f) inferInstance _
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hs Z (Ext.mk₀ h)
    (rfl : 1 + 0 = 1) hz
  refine ⟨Ext.addEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (kernel f) Z).1
  rw [← Ext.mk₀_comp_mk₀]
  simpa using ha

end MagnitudeConjecture.FiniteKernel
