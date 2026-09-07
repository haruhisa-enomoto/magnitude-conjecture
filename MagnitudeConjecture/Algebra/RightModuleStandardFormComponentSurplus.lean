import MagnitudeConjecture.Algebra.RightModuleStandardFormSurplus
import MagnitudeConjecture.CategoryTheory.TranslationQuiverWalkComponent
import MagnitudeConjecture.Combinatorics.ComponentSurplus

/-!
# Component additivity for the standard-form translation quiver

The augmented-walk components of the standard-form translation quiver contain
every ordinary arrow and every translation edge.  Consequently the official
Auslander--Reiten arrow multiplicities have no cross-component entries, and
the ambient surplus is the sum of the induced component surpluses.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

noncomputable local instance standardFormComponentFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormComponentNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

local instance standardFormComponentQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormComponentArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- Components of the standard-form translation quiver, using the augmented
walks of its universal-cover construction. -/
abbrev StandardFormWalkComponent :=
  WalkComponent S.standardFormRightMeshData

/-- The augmented-walk component of one standard-form vertex. -/
abbrev standardFormWalkComponentClass (x : Fin S.n) :
    S.StandardFormWalkComponent :=
  walkComponentClass S.standardFormRightMeshData x

/-- Vertices in one augmented-walk component of the standard-form
translation quiver. -/
abbrev StandardFormWalkComponentVertex
    (c : S.StandardFormWalkComponent) :=
  WalkComponentVertex S.standardFormRightMeshData c

/-- The induced polarized right-mesh data on one standard-form walk
component. -/
abbrev standardFormComponentRightMeshData
    (c : S.StandardFormWalkComponent) :=
  walkComponentRightMeshData S.standardFormRightMeshData c

/-- Every standard-form walk component has a vertex representative. -/
theorem standardFormWalkComponentVertex_nonempty
    (c : S.StandardFormWalkComponent) :
    Nonempty (S.StandardFormWalkComponentVertex c) :=
  walkComponentVertex_nonempty S.standardFormRightMeshData c

/-- Every induced standard-form component is connected by its own augmented
walks from any chosen vertex. -/
theorem standardFormComponent_isWalkConnectedAt
    (c : S.StandardFormWalkComponent)
    (x₀ : S.StandardFormWalkComponentVertex c) :
    IsWalkConnectedAt (S.standardFormComponentRightMeshData c) x₀ :=
  walkComponent_isWalkConnectedAt S.standardFormRightMeshData c x₀

@[simp]
theorem standardFormComponent_projective_iff
    (c : S.StandardFormWalkComponent)
    (x : S.StandardFormWalkComponentVertex c) :
    x ∈ (S.standardFormComponentRightMeshData c).projective ↔
      Projective (S.fgObj x.1) :=
  Iff.rfl

noncomputable local instance standardFormWalkComponentDecidableEq :
    DecidableEq S.StandardFormWalkComponent :=
  Classical.decEq _

/-- The official AR arrow-multiplicity function restricted to one
standard-form walk component. -/
abbrev standardFormComponentArrowMultiplicity
    (c : S.StandardFormWalkComponent) :=
  ARCount.componentArrowMultiplicity
    (FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData)
    S.standardFormWalkComponentClass c

/-- The projective predicate restricted to one standard-form walk
component. -/
abbrev standardFormComponentIsProjective
    (c : S.StandardFormWalkComponent) :=
  ARCount.componentIsProjective
    (fun x : Fin S.n ↦ Projective (S.fgObj x))
    S.standardFormWalkComponentClass c

noncomputable local instance standardFormComponentProjectiveDecidablePred
    (c : S.StandardFormWalkComponent) :
    DecidablePred (S.standardFormComponentIsProjective c) :=
  Classical.decPred _

/-- The Auslander--Reiten surplus induced on one standard-form walk
component. -/
abbrev standardFormComponentSurplus
    (c : S.StandardFormWalkComponent) : ℤ :=
  ARCount.surplus (S.standardFormComponentArrowMultiplicity c)
    (S.standardFormComponentIsProjective c)

/-- Official AR arrow multiplicity vanishes between distinct standard-form
walk components. -/
theorem standardForm_arrowMultiplicity_eq_zero_of_walkComponentClass_ne
    (source target : Fin S.n)
    (h : S.standardFormWalkComponentClass source ≠
      S.standardFormWalkComponentClass target) :
    FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData source target = 0 := by
  let hEmpty : IsEmpty (target ⟶ source) :=
    isEmpty_arrow_of_walkComponentClass_ne S.standardFormRightMeshData h.symm
  rw [← S.natCard_standardFormArrow target source,
    Nat.card_eq_fintype_card]
  exact Fintype.card_eq_zero

/-- There are no standard mesh-category morphisms between vertices in
distinct augmented-walk components. -/
theorem standardForm_meshHom_eq_zero_of_walkComponentClass_ne
    {x y : Fin S.n}
    (h : S.standardFormWalkComponentClass x ≠
      S.standardFormWalkComponentClass y)
    (f : MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData y) :
    f = 0 :=
  meshCategory_hom_eq_zero_of_walkComponentClass_ne
    S.standardFormRightMeshData h f

/-- Frozen manuscript, component additivity for the original algebra's
Auslander--Reiten surplus, using the common standard-form translation
quiver. -/
theorem ambientARSurplus_eq_sum_standardFormComponentSurplus :
    S.ambientARSurplus =
      ∑ c : S.StandardFormWalkComponent,
        S.standardFormComponentSurplus c := by
  classical
  unfold ambientARSurplus standardFormComponentSurplus
  exact ARCount.surplus_eq_sum_componentSurplus
    (FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData)
    (fun x : Fin S.n ↦ Projective (S.fgObj x))
    S.standardFormWalkComponentClass
    S.standardForm_arrowMultiplicity_eq_zero_of_walkComponentClass_ne

/-- The literal standard-form algebra has the same componentwise surplus
decomposition. -/
theorem standardFormAlgebra_ambientARSurplus_eq_sum_componentSurplus :
    (S.standardFormAlgebraIndecomposableSkeleton (k := k)).ambientARSurplus =
      ∑ c : S.StandardFormWalkComponent,
        S.standardFormComponentSurplus c := by
  rw [S.standardFormAlgebra_ambientARSurplus_eq_original]
  exact S.ambientARSurplus_eq_sum_standardFormComponentSurplus

/-- Componentwise nonnegativity implies nonnegativity of the original
ambient surplus. -/
theorem ambientARSurplus_nonnegative_of_standardFormComponents_nonnegative
    (hcomponent : ∀ c : S.StandardFormWalkComponent,
      0 ≤ S.standardFormComponentSurplus c) :
    0 ≤ S.ambientARSurplus := by
  rw [S.ambientARSurplus_eq_sum_standardFormComponentSurplus]
  exact Finset.sum_nonneg fun c _ ↦ hcomponent c

/-- If all component surpluses are nonnegative and the ambient surplus
vanishes, then every standard-form component has surplus zero. -/
theorem standardFormComponentSurplus_eq_zero_of_ambientARSurplus_eq_zero
    (hcomponent : ∀ c : S.StandardFormWalkComponent,
      0 ≤ S.standardFormComponentSurplus c)
    (hzero : S.ambientARSurplus = 0)
    (c : S.StandardFormWalkComponent) :
    S.standardFormComponentSurplus c = 0 := by
  classical
  rw [S.ambientARSurplus_eq_sum_standardFormComponentSurplus] at hzero
  have hle : S.standardFormComponentSurplus c ≤
      ∑ d : S.StandardFormWalkComponent,
        S.standardFormComponentSurplus d := by
    apply Finset.single_le_sum
    · intro d hd
      exact hcomponent d
    · exact Finset.mem_univ c
  exact le_antisymm (by simpa [hzero] using hle) (hcomponent c)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
