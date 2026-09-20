import MagnitudeConjecture.Algebra.RightModuleAlgebraEquiv
import MagnitudeConjecture.Algebra.RightModuleSimpleCount

/-! # Simple-module counts under algebra equivalence -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A B : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]
  [IsNoetherianRing Bᵐᵒᵖ]

/-- Transporting the complete family along an algebra equivalence preserves
the literal number of simple-module classes. -/
theorem simpleCount_mapAlgEquiv
    (S : RightModule.FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B) :
    (S.mapAlgEquiv f).simpleCount = S.simpleCount := by
  let e : S.ProjectiveLabel ≃ (S.mapAlgEquiv f).ProjectiveLabel :=
    { toFun := fun p ↦ ⟨p.label, Projective.of_iso
        (S.mapAlgEquivObjIso f p.label)
          (((fgModuleEquivalenceOfAlgEquiv f).map_projective_iff
            (S.fgObj p.label)).2 p.projective)⟩
      invFun := fun q ↦ ⟨q.label,
        ((fgModuleEquivalenceOfAlgEquiv f).map_projective_iff
          (S.fgObj q.label)).1
            (Projective.of_iso (S.mapAlgEquivObjIso f q.label).symm
              q.projective)⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro q; cases q; rfl }
  rw [(S.mapAlgEquiv f).simpleCount_eq_card_projectiveLabel,
    S.simpleCount_eq_card_projectiveLabel]
  exact (Fintype.card_congr e).symm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
