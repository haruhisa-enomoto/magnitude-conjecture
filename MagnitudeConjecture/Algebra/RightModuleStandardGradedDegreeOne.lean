import MagnitudeConjecture.Algebra.RightModuleStandardGradedDecomposition
import MagnitudeConjecture.Algebra.RightModuleStandardGradedDirected
import MagnitudeConjecture.CategoryTheory.IrreducibleFromIndecomposableFactors

/-! # Nonzero degree-one maps are irreducible in the full graded category -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance rdGradedDegreeOneQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance rdGradedDegreeOneArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- Adjacent shifts leave no room for two noninvertible factors through an indecomposable. -/
theorem standardFormGraded_degreeOne_irreducible
    (X Y : S.StandardFormMeshCategory) (t : ℤ)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, t + 1⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩) (hf : f ≠ 0) : IsIrreducibleMorphism f := by
  apply MagnitudeConjecture.CategoryTheory.irreducible_of_indecomposable_factors
    Graded.FiniteGradedModule.finiteDecomposition f hf
  · intro hs
    letI := hs
    have hr := MagnitudeConjecture.CategoryTheory.retraction_ne_zero_of_ne_zero f hf
    have hd := S.standardFormGraded_strict_descent Y X t (t + 1) (retraction f) hr
      (Or.inr (by omega))
    omega
  · intro hs
    letI := hs
    have hr := MagnitudeConjecture.CategoryTheory.section_ne_zero_of_ne_zero f hf
    have hd := S.standardFormGraded_strict_descent Y X t (t + 1) (section_ f) hr
      (Or.inr (by omega))
    omega
  · intro M hM a b ha hb
    obtain ⟨i, r, ⟨e⟩⟩ := S.standardFormGraded_shifted_exists_iso M hM
    let Z := MeshCategory.obj (k := k) S.standardFormRightMeshData i
    let a' : (⟨S.standardFormGradedVertexFunctor.obj X, t + 1⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
        ⟨S.standardFormGradedVertexFunctor.obj Z, r⟩ := a ≫ e.hom
    let b' : (⟨S.standardFormGradedVertexFunctor.obj Z, r⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
        ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩ := e.inv ≫ b
    have ha' : a' ≠ 0 := by
      intro hz
      apply ha
      have h := congrArg (fun q ↦ q ≫ e.inv) hz
      simpa only [a', Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp] using h
    have hb' : b' ≠ 0 := by
      intro hz
      apply hb
      have h := congrArg (fun q ↦ e.hom ≫ q) hz
      simpa only [b', Iso.hom_inv_id_assoc, comp_zero] using h
    by_cases hi : IsIso a'
    · let := hi
      exact Or.inl (IsSplitMono.mk'
        { retraction := e.hom ≫ inv a'
          id := by simpa only [a', Category.assoc] using IsIso.hom_inv_id a' })
    by_cases hj : IsIso b'
    · let := hj
      exact Or.inr (IsSplitEpi.mk'
        { section_ := inv b' ≫ e.inv
          id := by simpa only [b', Category.assoc] using IsIso.inv_hom_id b' })
    have h1 := S.standardFormGraded_noniso_descent X Z (t + 1) r a' ha' hi
    have h2 := S.standardFormGraded_noniso_descent Z Y r t b' hb' hj
    omega

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
