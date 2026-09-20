import MagnitudeConjecture.Algebra.RightModuleStandardGradedIncomingAlmostSplit

/-! # Actual almost-split maps and nonprojective targets in the control interval -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance intervalIncomingQuiver : Quiver (Fin S.n) := S.standardFormQuiver
local instance intervalIncomingArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- At a nonprojective original label the actual incoming map is epic after
forgetting its grading, in the finitely generated standard-form category. -/
theorem standardFormGradedIncomingMap_underlyingFG_epi (z : Fin S.n)
    (hz : ¬ Projective (S.fgObj z)) (t : ℤ) :
    Epi (Graded.FiniteGradedModule.underlyingFG.map (S.standardFormGradedIncomingMap z t).val) := by
  let zn : {z : Fin S.n // z ∉ S.standardFormProjectiveSet} :=
    ⟨z, by simpa [standardFormProjectiveSet] using hz⟩
  let f := S.standardFormRightMeshData.additiveIncomingMap (k := k) z
  let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence
  let G := S.standardFormAdditiveRestrictedYonedaFunctor (k := k) ⋙ E.functor
  letI : Epi ((S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).map f) :=
    (S.standardFormRecoveredRightMesh_shortExact zn).epi_g
  letI : Epi (G.map f) := E.functor.map_epi _
  let e := S.standardGradedIncomingRecoveryIso
  change Epi (((S.standardFormMeshRawFunctor (k := k)).mapMat_ ⋙
    (S.standardFormGradedFunctor ⋙ Graded.FiniteGradedModule.underlyingFG)).map f)
  rw [← NatIso.naturality_1 e.symm f]
  infer_instance

/-- The middle of the incoming map, placed in the single control interval. -/
def standardFormIntervalIncomingSource (z : Fin S.n) (t : ℤ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Graded.FiniteGradedModule.SupportedCategory
      (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      (S.standardFormIntervalControlHeight + 2) :=
  ⟨_, (S.standardFormGradedIncomingMap_supported z t ht0 ht1).1⟩

/-- The target representative at shift zero or one in the same interval. -/
def standardFormIntervalIncomingTarget (z : Fin S.n) (t : ℤ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Graded.FiniteGradedModule.SupportedCategory
      (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      (S.standardFormIntervalControlHeight + 2) :=
  ⟨_, (S.standardFormGradedIncomingMap_supported z t ht0 ht1).2⟩

/-- The literal degree-one incoming map in the finite interval. -/
def standardFormIntervalIncomingMap (z : Fin S.n) (t : ℤ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    S.standardFormIntervalIncomingSource z t ht0 ht1 ⟶
      S.standardFormIntervalIncomingTarget z t ht0 ht1 :=
  ObjectProperty.homMk (S.standardFormGradedIncomingMap z t)

theorem standardFormIntervalIncomingMap_rightAlmostSplit (z : Fin S.n) (t : ℤ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsRightAlmostSplit (S.standardFormIntervalIncomingMap z t ht0 ht1) :=
  MagnitudeConjecture.rightAlmostSplit_of_map_full_faithful
    (Graded.FiniteGradedModule.intervalSupport _).ι
    (S.standardFormGradedIncomingMap_rightAlmostSplit z t)

theorem standardFormIntervalIncomingMap_rightMinimal (z : Fin S.n) (t : ℤ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsRightMinimal (S.standardFormIntervalIncomingMap z t ht0 ht1) :=
  MagnitudeConjecture.rightMinimal_of_map_full_faithful
    (Graded.FiniteGradedModule.intervalSupport _).ι
    (S.standardFormGradedIncomingMap_rightMinimal z t)

/-- The second shift preserves nonprojectivity inside the control interval:
the shifted incoming map is an actual nonsplit epimorphism there. -/
theorem standardFormIntervalIncomingTarget_not_projective (z : Fin S.n)
    (hz : ¬ Projective (S.fgObj z)) (t : ℤ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ¬ Projective (S.standardFormIntervalIncomingTarget z t ht0 ht1) := by
  let f := S.standardFormIntervalIncomingMap z t ht0 ht1
  let F := (Graded.FiniteGradedModule.intervalSupport
    (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    (S.standardFormIntervalControlHeight + 2)).ι ⋙
      Graded.FiniteGradedModule.homGrading.forget ⋙ Graded.FiniteGradedModule.underlyingFG
  letI : Epi f := F.epi_of_epi_map (S.standardFormGradedIncomingMap_underlyingFG_epi z hz t)
  intro hP
  letI := hP
  apply (S.standardFormIntervalIncomingMap_rightAlmostSplit z t ht0 ht1).not_isSplitEpi
  exact IsSplitEpi.mk'
    { section_ := Projective.factorThru (𝟙 _) f
      id := Projective.factorThru_comp (𝟙 _) f }

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
