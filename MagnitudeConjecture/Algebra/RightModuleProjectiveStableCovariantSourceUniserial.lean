import MagnitudeConjecture.Algebra.CoordinateThinModule
import MagnitudeConjecture.Algebra.RightModuleProjectiveFactorRadical
import MagnitudeConjecture.Algebra.RightModuleProjectiveStableCovariantUniserial

/-!
# Covariant stable representables detect uniserial modules

This file completes Auslander--Reiten, Proposition 1.1(a), in the finite
right-module skeleton: a nonzero indecomposable nonprojective module whose
projective-stable covariant representable is uniserial is itself uniserial.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Auslander--Reiten Proposition 1.1(a), in the exact finite-skeleton
interface used by the magnitude campaign. -/
theorem isUniserialModule_of_projectiveStableCovariantRepresentable
    {X : RightModule.FinitelyGeneratedCategory A}
    (hX : Indecomposable X) (hXnonprojective : ¬ Projective X)
    (hstable : IsUniserialObject
      (S.finiteProjectiveStableCovariantRepresentable X)) :
    IsUniserialModule Aᵐᵒᵖ X := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  by_contra hnotUniserial
  obtain ⟨n, K, L, hnextK, hnextL, hKn, hLn, hKL, hLK⟩ :=
    exists_incomparable_between_iteratedJacobson_of_not_uniserial
      (R := Aᵐᵒᵖ) (M := X) hnotUniserial
  let Y : RightModule.FinitelyGeneratedCategory A :=
    RightModule.quotientFGObj X K
  let Z : RightModule.FinitelyGeneratedCategory A :=
    RightModule.quotientFGObj X L
  let p : X ⟶ Y :=
    FGModuleCat.ofHom (RightModule.quotientFGMkQ X K)
  let q : X ⟶ Z :=
    FGModuleCat.ofHom (RightModule.quotientFGMkQ X L)
  rcases S.stableFactorization_dichotomy_of_covariantUniserial
      hstable p q with hpq | hqp
  · obtain ⟨t, ⟨hfactor⟩⟩ := hpq
    let tLinear : (X ⧸ L) →ₗ[Aᵐᵒᵖ] (X ⧸ K) := t.hom.hom
    have hrange : LinearMap.range (p - q ≫ t).hom.hom ≤
        Module.jacobson Aᵐᵒᵖ Y :=
      range_le_jacobson_of_factorsThroughProjective
        (k := k) hX hXnonprojective hfactor
    change LinearMap.range (K.mkQ - tLinear.comp L.mkQ) ≤
      Module.jacobson Aᵐᵒᵖ (X ⧸ K) at hrange
    have hnotRange := quotientMap_sub_comp_range_not_le_jacobson
      (R := Aᵐᵒᵖ) (M := X) hnextK hLn hLK tLinear
    apply hnotRange
    exact hrange
  · obtain ⟨t, ⟨hfactor⟩⟩ := hqp
    let tLinear : (X ⧸ K) →ₗ[Aᵐᵒᵖ] (X ⧸ L) := t.hom.hom
    have hrange : LinearMap.range (q - p ≫ t).hom.hom ≤
        Module.jacobson Aᵐᵒᵖ Z :=
      range_le_jacobson_of_factorsThroughProjective
        (k := k) hX hXnonprojective hfactor
    change LinearMap.range (L.mkQ - tLinear.comp K.mkQ) ≤
      Module.jacobson Aᵐᵒᵖ (X ⧸ L) at hrange
    have hnotRange := quotientMap_sub_comp_range_not_le_jacobson
      (R := Aᵐᵒᵖ) (M := X) hnextL hKn hKL tLinear
    apply hnotRange
    exact hrange

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
