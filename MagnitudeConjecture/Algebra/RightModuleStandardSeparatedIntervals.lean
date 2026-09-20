import MagnitudeConjecture.Algebra.RightModuleStandardIntervalAlgebra
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalControlHeight
import MagnitudeConjecture.CategoryTheory.GradedPrincipalSeparatedDeletion

/-! # Separated block deletion in the actual standard-form intervals -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance separatedIntervalMeshHomFinite (X Y : S.StandardFormMeshCategory) :
    FiniteDimensional k (X ⟶ Y) := S.standardFormMeshHomFinite X Y
local instance separatedIntervalBaseFinite :
    FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

/-- The common interval control height also bounds the actual standard-form
algebra grading, not just its mesh Hom spaces. -/
theorem standardFormOppositeAlgebra_above_control (d : ℤ)
    (hd : (S.standardFormIntervalControlHeight : ℤ) < d) :
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite).component d = ⊥ := by
  have hmat (X Y : Mat_ S.StandardFormMeshCategory) :
      (S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).component X Y d = ⊥ := by
    apply bot_unique
    intro f hf
    change f = 0
    apply Mat_.hom_ext
    intro i j
    have hm := hf i (Set.mem_univ i) j (Set.mem_univ j)
    change f i j ∈ S.standardFormIntegerHomGrading.component (X.X i) (Y.X j) d at hm
    rw [S.standardFormIntervalControlHeight_hom_bound _ _ d (Or.inr hd)] at hm
    exact hm
  have hgen := (S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).generatorAlgebra_component_eq_bot
    S.standardGradedProjectiveFamily d (fun i j ↦ hmat _ _)
  apply bot_unique
  intro a ha
  change a = 0
  apply (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite).injective
  rw [map_zero]
  change (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite) a ∈
    (S.standardGradedGeneratorAlgebraGrading S.standardFormMeshHomFinite).component d at ha
  change (S.standardGradedGeneratorAlgebraGrading S.standardFormMeshHomFinite).component d = ⊥ at hgen
  rw [hgen] at ha
  exact ha

/-- The principal-projective category whose matrix algebra is the actual
standard-form interval algebra. -/
abbrev standardFormIntervalPrincipalCategory (m : ℕ) :=
  Graded.FiniteGradedModule.PrincipalIntervalCategory
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero m

/-- Objects deleted between the separated blocks inside the actual interval. -/
def standardFormIntervalSeparatedDeleted (m r q : ℕ) :
    Set (S.standardFormIntervalPrincipalCategory m)ᵒᵖ :=
  Graded.FiniteGradedModule.principalIntervalSeparatedDeleted
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormIntervalControlHeight m r q

/-- In the actual finite interval, deleting the gaps imposes no relations
between retained objects. -/
theorem standardFormIntervalSeparated_noDeletedFactorization (m r q : ℕ) :
    ObjectDeletion.NoDeletedFactorization (S.standardFormIntervalPrincipalCategory m)ᵒᵖ
      (S.standardFormIntervalSeparatedDeleted m r q) :=
  Graded.FiniteGradedModule.principalIntervalSeparated_noDeletedFactorization
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
    S.standardFormOppositeAlgebra_negative S.standardFormIntervalControlHeight
    S.standardFormOppositeAlgebra_above_control m r q

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
