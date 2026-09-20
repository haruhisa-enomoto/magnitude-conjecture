import MagnitudeConjecture.CategoryTheory.FiniteKernelBound
import MagnitudeConjecture.CategoryTheory.KernelExtensionFromExt

/-! # The finite-kernel lemma from Ext vanishing on subobjects -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace MagnitudeConjecture.FiniteKernel
universe u v w t
variable {k : Type u} [Field k] [Infinite k]
variable {C : Type v} [Category.{w} C] [Abelian C] [Linear k C] [HasExt.{t} C]
variable [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
variable {ι : Type} [Fintype ι]

/-- In a Hom-finite category with a finite additive classification, the frozen
finite-kernel hypotheses imply that Hom(Z,I) has dimension at most one. -/
theorem finrank_hom_le_one_of_ext_vanishing
    (F : ι → C) (hF : ∀ i, ¬ IsZero (F i))
    (hdec : ∀ X : C, ∃ n : ℕ, ∃ label : Fin n → ι,
      Nonempty (X ≅ ⨁ fun j ↦ F (label j)))
    (Z I : C) [Injective I]
    (hZ : ∀ a : Z ⟶ Z, ∃ c : k, a = c • 𝟙 Z)
    (hI : ∀ a : I ⟶ I, ∃ c : k, a = c • 𝟙 I)
    (hext : ∀ (U : C) (j : U ⟶ I), Mono j → ∀ xi : Ext.{t} U Z 1, xi = 0) :
    Module.finrank k (Z ⟶ I) ≤ 1 :=
  finrank_hom_le_one_of_finite_additive_family F hF hdec Z I hZ hI
    (fun f _ ↦ kernel_extension_of_ext_vanishing f hext)

end MagnitudeConjecture.FiniteKernel
