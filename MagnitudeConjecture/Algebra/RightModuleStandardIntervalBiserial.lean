import MagnitudeConjecture.Algebra.RightModuleStandardIntervalThin
import MagnitudeConjecture.CategoryTheory.FiniteCategoryTwoSidedBiserial
import MagnitudeConjecture.CategoryTheory.LocallyBoundedOpposite
import MagnitudeConjecture.Algebra.SpecialBiserialAlgebra

/-! # Special-biserial interval algebras at zero ambient surplus -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance intervalBiserialBaseFinite : FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
local instance intervalBiserialFintype (m : ℕ) : Fintype (S.standardFormIntervalPrincipalCategory m) :=
  inferInstanceAs (Fintype (S.StandardFormProjectiveMeshCategory × Fin (m + 1)))
local instance intervalBiserialOpFintype (m : ℕ) : Fintype (S.standardFormIntervalPrincipalCategory m)ᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite
local instance intervalBiserialFinite (m : ℕ) : FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance intervalBiserialNoetherian (m : ℕ) : IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Finite representables in the other variance of the actual interval. -/
theorem standardFormIntervalCategory_finiteCovariantRepresentables (m : ℕ)
    (X : S.standardFormIntervalPrincipalCategory m) :
    CoveringHom.IsFiniteDimensionalModule (C := S.standardFormIntervalPrincipalCategory m) k
      (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k (Opposite.op Y ⟶ Opposite.op X) :=
      (S.standardFormIntervalCategory_finiteRepresentables m (Opposite.op Y)).1 (Opposite.op X)
    exact Module.Finite.equiv (CoveringHom.oppositeHomLinearEquiv (k := k)
      (Opposite.op Y) (Opposite.op X))
  · exact Set.toFinite _

/-- Endomorphism rings of the interval objects are local in both variances. -/
theorem standardFormIntervalCategory_end_isLocalRing (m : ℕ)
    (X : S.standardFormIntervalPrincipalCategory m) : IsLocalRing (End X) := by
  letI : IsLocalRing (End (Opposite.op X)) :=
    Graded.FiniteGradedModule.principalIntervalOp_end_isLocalRing
      (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
      S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
      S.standardFormHomogeneousCorner_diagonal m (Opposite.op X)
  letI : IsLocalRing (End X)ᵐᵒᵖ := MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (CoveringHom.oppositeEndRingEquiv X).symm
  letI : IsLocalRing ((End X)ᵐᵒᵖ)ᵐᵒᵖ := CoveringHom.isLocalRing_mulOpposite
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm (RingEquiv.opOp (End X)).symm

attribute [local irreducible] standardFormIntervalSkeleton

/-- Every interval algebra at zero ambient surplus admits the literal
special-biserial presentation obtained from its two-sided biserial projectives. -/
theorem standardFormIntervalAlgebra_admitsSpecialBiserialPresentation_of_ambient_eq_zero
    (hz : S.ambientARSurplus = 0) (m : ℕ) :
    BoundQuiver.AdmitsSpecialBiserialPresentation k (S.standardFormIntervalAlgebra m) := by
  let hC := S.standardFormIntervalCategory_finiteCovariantRepresentables m
  let hOp := S.standardFormIntervalCategory_finiteRepresentables m
  let := CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hOp
  let : IsNoetherianRing (CoveringHom.finiteCategoryProjectiveGenerator.algebra hOp)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let f : S.standardFormIntervalAlgebra m ≃ₐ[k]
      CoveringHom.finiteCategoryProjectiveGenerator.algebra hOp :=
    Graded.FiniteGradedModule.principalIntervalAlgebraRepresentableEquiv
      (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
      S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent m
  have hSpecial :=
    CoveringHom.finiteCategoryProjectiveGenerator.admitsSpecialBiserialPresentation_of_opposite_pointwiseThin hC hOp
      (S.standardFormIntervalCategory_end_isLocalRing m)
      (Graded.FiniteGradedModule.principalIntervalOp_end_isLocalRing
        (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
        S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
        S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
        S.standardFormHomogeneousCorner_diagonal m)
      (Graded.FiniteGradedModule.principalIntervalOp_skeletal
        (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
        S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
        S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
        S.standardFormHomogeneousCorner_diagonal S.standardFormOppositeAlgebra_negative
        S.standardFormHomogeneousCorner_off_diagonal m)
      (S.standardFormIntervalCategory_pointwiseThin_of_ambient_eq_zero hz m)
      ((S.standardFormIntervalSkeleton m).mapAlgEquiv f)
  obtain ⟨N⟩ := hSpecial
  exact ⟨N.mapAlgEquiv f⟩

/-- Zero ambient surplus makes every interval algebra special biserial. -/
theorem standardFormIntervalAlgebra_isSpecialBiserial_of_ambient_eq_zero
    (hz : S.ambientARSurplus = 0) (m : ℕ) :
    BoundQuiver.IsSpecialBiserial k (S.standardFormIntervalAlgebra m) :=
  BoundQuiver.isSpecialBiserial_of_presentation
    (S.standardFormIntervalAlgebra_admitsSpecialBiserialPresentation_of_ambient_eq_zero hz m)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
