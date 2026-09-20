import MagnitudeConjecture.Algebra.RightModuleStandardIntervalIncoming
import MagnitudeConjecture.Algebra.RightModuleStandardGradedBiproduct

/-! # Occurrence-preserving incoming decompositions in the control interval -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance intervalDecompQuiver : Quiver (Fin S.n) := S.standardFormQuiver
local instance intervalDecompArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- Each occurrence is the shifted representative belonging to its incoming arrow. -/
def standardFormIntervalIncomingSummand (z : Fin S.n)
    (a : MeshCategory.RightMeshData.IncomingArrow z) :=
  S.standardFormIntervalIncomingTarget a.1 1 (by omega) (by omega)

/-- The matrix coordinates restrict to the control interval without identifying repeated labels. -/
def standardFormIntervalIncomingBicone (z : Fin S.n) :
    Bicone (S.standardFormIntervalIncomingSummand z) where
  pt := S.standardFormIntervalIncomingSource z 0 (by omega) (by omega)
  π i := ObjectProperty.homMk
    ((S.standardFormGradedMatrixBicone (S.standardGradedIncomingObject z) 1).π i)
  ι i := ObjectProperty.homMk
    ((S.standardFormGradedMatrixBicone (S.standardGradedIncomingObject z) 1).ι i)
  ι_π i j := by
    classical
    by_cases h : i = j
    · subst j
      simp only [dite_true]
      apply ObjectProperty.hom_ext
      change (S.standardFormGradedMatrixBicone (S.standardGradedIncomingObject z) 1).ι i ≫
        (S.standardFormGradedMatrixBicone (S.standardGradedIncomingObject z) 1).π i = 𝟙 _
      simpa only [dite_true, eqToHom_refl, if_true] using
        (S.standardFormGradedMatrixBicone (S.standardGradedIncomingObject z) 1).ι_π i i
    · simp only [dif_neg h]
      apply ObjectProperty.hom_ext
      change (S.standardFormGradedMatrixBicone (S.standardGradedIncomingObject z) 1).ι i ≫
        (S.standardFormGradedMatrixBicone (S.standardGradedIncomingObject z) 1).π j = 0
      simpa only [dif_neg h] using
        (S.standardFormGradedMatrixBicone (S.standardGradedIncomingObject z) 1).ι_π i j

/-- The literal incoming source is the direct sum indexed by incoming arrow occurrences. -/
def standardFormIntervalIncomingBicone_isBilimit (z : Fin S.n) :
    (S.standardFormIntervalIncomingBicone z).IsBilimit := by
  apply isBilimitOfTotal
  let F := (Graded.FiniteGradedModule.intervalSupport
    (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    (S.standardFormIntervalControlHeight + 2)).ι
  apply F.map_injective
  simp only [Functor.map_sum, Functor.map_comp, Functor.map_id]
  exact IsBilimit.total (S.standardFormGradedMatrixBicone_isBilimit (S.standardGradedIncomingObject z) 1)

/-- The finite interval's actual incoming source decomposition retains all multiplicities. -/
def standardFormIntervalIncomingBiproductIso (z : Fin S.n) :
    S.standardFormIntervalIncomingSource z 0 (by omega) (by omega) ≅
      ⨁ S.standardFormIntervalIncomingSummand z :=
  biproduct.uniqueUpToIso _ (S.standardFormIntervalIncomingBicone_isBilimit z)

/-- Every displayed occurrence is indecomposable in the interval. -/
theorem standardFormIntervalIncomingSummand_indecomposable (z : Fin S.n)
    (a : MeshCategory.RightMeshData.IncomingArrow z) :
    Indecomposable (S.standardFormIntervalIncomingSummand z a) := by
  apply MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
    (Graded.FiniteGradedModule.intervalSupport _).ι
  exact Graded.FiniteGradedModule.indecomposable_of_underlying
    (S.standardFormGradedFamily a.1) 1 (S.standardFormGradedFamily_indecomposable a.1)

/-- Every originally nonprojective incoming occurrence stays nonprojective in the interval. -/
theorem standardFormIntervalIncomingSummand_not_projective (z : Fin S.n)
    (a : MeshCategory.RightMeshData.IncomingArrow z) (ha : ¬ Projective (S.fgObj a.1)) :
    ¬ Projective (S.standardFormIntervalIncomingSummand z a) :=
  S.standardFormIntervalIncomingTarget_not_projective a.1 ha 1 (by omega) (by omega)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
