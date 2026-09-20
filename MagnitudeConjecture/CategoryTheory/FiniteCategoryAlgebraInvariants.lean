import MagnitudeConjecture.CategoryTheory.FiniteCategorySurplusInvariant
import MagnitudeConjecture.CategoryTheory.IndecomposableFamilyEquivalence
import MagnitudeConjecture.CategoryTheory.RankedFamilyEquivalence

/-! # Directedness and intrinsic surplus across an algebra-module equivalence -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CoveringHom
universe u w
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C] [Fintype C]
variable (E : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k ≌
  RightModule.FinitelyGeneratedCategory A) [E.functor.Additive]

include E in
/-- A complete strictly ranked algebra-module family makes the equivalent
finite category-module category directed. -/
theorem hasAcyclicFiniteModuleNonzeroNonisomorphisms_of_ranked_algebra_family
    {ι : Type w} (V : ι → RightModule.FinitelyGeneratedCategory A) (rank : ι → ℤ)
    (hstrict : ∀ a b (f : V a ⟶ V b), f ≠ 0 → ¬ IsIso f → rank b < rank a)
    (hcomplete : ∀ M : RightModule.FinitelyGeneratedCategory A,
      Indecomposable M → ∃ a, Nonempty (M ≅ V a)) :
    HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C) := by
  let F := inducedFunctor (fun a : ι ↦ E.inverse.obj (V a))
  apply hasAcyclicFiniteModuleNonzeroNonisomorphisms_of_ranked_realization F rank
  · intro a b h
    obtain ⟨f, hf, hi⟩ := h
    apply MagnitudeConjecture.CategoryTheory.ranked_family_of_equivalence E V rank hstrict a b f.hom
    · intro hz
      exact hf (InducedCategory.hom_ext hz)
    · intro hiso
      letI : IsIso (F.map f) := hiso
      exact hi (isIso_of_reflects_iso f F)
  · intro M hM
    obtain ⟨a, ⟨ha⟩⟩ := MagnitudeConjecture.CategoryTheory.complete_indecomposable_family_of_equivalence
      E V hcomplete M hM
    exact ⟨a, ⟨ha.symm⟩⟩

include E in
/-- The intrinsic surplus agrees with that of any complete algebra skeleton. -/
theorem finiteCategorySurplus_eq_algebra_surplus
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    finiteCategorySurplus hP hrep = S.ambientARSurplus := by
  letI := enoughProjectives_of_finiteRepresentables hP
  let T := finiteCategoryModuleIndecomposableSkeleton hrep
  exact (finiteCategorySurplus_eq_skeleton hP hrep T).trans
    (categorySkeleton_surplus_eq_ambientARSurplus_of_equivalence E T S)

end MagnitudeConjecture.CoveringHom
