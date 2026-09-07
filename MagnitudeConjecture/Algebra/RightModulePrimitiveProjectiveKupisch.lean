import MagnitudeConjecture.Algebra.RightModulePrimitiveProjectiveHomChain
import MagnitudeConjecture.CategoryTheory.KupischUniserial

/-!
# Kupisch uniseriality for selected projectives

The primitive-corner finite-ideal theorem gives comparability on literal
corners.  This file transports it through the fully faithful coordinate
functor to the selected-projective category and applies the generic Kupisch
classification, producing condition (K)(2) in the exact module orientation
used by the Skowroński--Waschbüsch correction.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

/-- Representation-finite primitive-corner comparability transported to the
literal selected-projective category. -/
theorem finiteIdeal_projectiveHom_homSubbimodule_comparable
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    {X Y : S.ProjectiveCategory}
    (T U : Submodule k (X ⟶ Y))
    (hT : IsHomSubbimodule T) (hU : IsHomSubbimodule U) :
    T ≤ U ∨ U ≤ T := by
  let p : P.PrimitiveCornerCategory := X
  let q : P.PrimitiveCornerCategory := Y
  let e := P.primitiveCornerHomLinearEquiv p q
  let Tc : Submodule k (p ⟶ q) := T.comap e.toLinearMap
  let Uc : Submodule k (p ⟶ q) := U.comap e.toLinearMap
  have hTc : IsHomSubbimodule Tc := by
    constructor
    · intro a f hf
      change e (a.asHom ≫ f) ∈ T
      change P.primitiveCornerToProjective.map (a.asHom ≫ f) ∈ T
      rw [P.primitiveCornerToProjective.map_comp]
      exact hT.1
        (End.of (P.primitiveCornerToProjective.map a.asHom)) hf
    · intro b f hf
      change e (f ≫ b.asHom) ∈ T
      change P.primitiveCornerToProjective.map (f ≫ b.asHom) ∈ T
      rw [P.primitiveCornerToProjective.map_comp]
      exact hT.2
        (End.of (P.primitiveCornerToProjective.map b.asHom)) hf
  have hUc : IsHomSubbimodule Uc := by
    constructor
    · intro a f hf
      change e (a.asHom ≫ f) ∈ U
      change P.primitiveCornerToProjective.map (a.asHom ≫ f) ∈ U
      rw [P.primitiveCornerToProjective.map_comp]
      exact hU.1
        (End.of (P.primitiveCornerToProjective.map a.asHom)) hf
    · intro b f hf
      change e (f ≫ b.asHom) ∈ U
      change P.primitiveCornerToProjective.map (f ≫ b.asHom) ∈ U
      rw [P.primitiveCornerToProjective.map_comp]
      exact hU.2
        (End.of (P.primitiveCornerToProjective.map b.asHom)) hf
  rcases P.finiteIdeal_homSubbimodule_comparable hA Tc Uc hTc hUc with h | h
  · exact Or.inl
      ((Submodule.comap_le_comap_iff_of_surjective e.surjective).mp h)
  · exact Or.inr
      ((Submodule.comap_le_comap_iff_of_surjective e.surjective).mp h)

/-- Representation-finiteness gives Kupisch's exact target-side or
opposite-source-side uniserial alternative on every selected-projective Hom
space. -/
theorem finiteIdeal_projectiveHom_uniserialAlternative
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (X Y : S.ProjectiveCategory) :
    IsUniserialModule (End Y) (X ⟶ Y) ∨
      IsUniserialModule (End X)ᵐᵒᵖ (X ⟶ Y) := by
  letI : ∀ Z : S.ProjectiveCategory, Module.Finite k (End Z) :=
    fun Z ↦ S.projectiveCategoryHomFinite Z Z
  apply uniserialModule_or_opposite_of_homSubbimodule_comparable
    (k := k)
  intro X Y T U hT hU
  exact P.finiteIdeal_projectiveHom_homSubbimodule_comparable
    hA T U hT hU

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
