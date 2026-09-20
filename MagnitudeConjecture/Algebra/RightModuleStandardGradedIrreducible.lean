import MagnitudeConjecture.Algebra.RightModuleStandardGradedHigherDegree

/-! # The irreducible maps between graded standard-form representatives -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

private theorem irreducible_ne_zero {C : Type*} [CategoryTheory.Category C] [Preadditive C] [HasZeroObject C]
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f) : f ≠ 0 := by
  intro hz
  let Z : C := 0
  rcases hf.factorization (0 : X ⟶ Z) (0 : Z ⟶ Y) (by simp [hz]) with ha | hb
  · letI := ha
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := 0
        id := by simpa only [hz, zero_comp] using IsSplitMono.id (0 : X ⟶ Z) }
  · letI := hb
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := 0
        id := by simpa only [hz, comp_zero] using IsSplitEpi.id (0 : Z ⟶ Y) }

/-- Exactly the nonzero maps of degree one are irreducible in the full graded category. -/
theorem standardFormGraded_irreducible_iff
    (X Y : S.StandardFormMeshCategory) (s t : ℤ)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩) :
    IsIrreducibleMorphism f ↔ f ≠ 0 ∧ s = t + 1 := by
  constructor
  · intro hi
    have hf := irreducible_ne_zero hi
    have hni : ¬ IsIso f := by
      intro hiso
      letI := hiso
      exact hi.not_isSplitMono inferInstance
    have hts := S.standardFormGraded_noniso_descent X Y s t f hf hni
    refine ⟨hf, ?_⟩
    by_contra h
    obtain ⟨n, hn, hs⟩ : ∃ n : ℕ, 0 < n ∧ s = t + n + 1 := by
      refine ⟨(s - t - 1).toNat, ?_, ?_⟩ <;> omega
    subst s
    exact S.standardFormGraded_higherDegree_not_irreducible X Y t n hn f hf hi
  · rintro ⟨hf, rfl⟩
    exact S.standardFormGraded_degreeOne_irreducible X Y t f hf

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
