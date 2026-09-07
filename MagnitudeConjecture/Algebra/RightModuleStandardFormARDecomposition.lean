import MagnitudeConjecture.Algebra.RightModuleStandardFormAR
import MagnitudeConjecture.Algebra.RightModuleTauAssembly
import MagnitudeConjecture.CategoryTheory.AlgebraicallyClosedOccurrenceBasis

/-!
# Recovered right almost-split decompositions for the standard-form algebra
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARDecompositionQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARDecompositionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARDecompositionFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARDecompositionNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The literal recovered incoming map, transported to the standard-form
algebra and equipped with its original incoming-arrow decomposition. -/
def standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition
    (z : Fin S.n) :
    (S.standardFormAlgebraIndecomposableSkeleton (k := k)).almostSplitSkeleton
      |>.MinimalRightAlmostSplitDecomposition z := by
  let B := S.standardFormAlgebra S.standardFormMeshHomFinite
  let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  let sigma := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let e (i : Fin S.n) : T.fgObj i ≅ E.functor.obj (sigma.obj i) :=
    pushforwardRightModuleIndecomposableSkeletonObjIso E sigma i
  let M := (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
    (S.standardFormRightMeshData.additiveIncomingObj (k := k) z)
  let f := E.functor.map
      (S.standardFormRecoveredIncomingMap (k := k) z) ≫ (e z).inv
  exact
    { middle := E.functor.obj M
      finiteLength := fgModule_isFiniteLength (k := k) (A := B) _
      map := f
      rightAlmostSplit :=
        (S.standardFormRecoveredIncomingMap_rightAlmostSplit
          (k := k) z).map_equivalence E |>.postcomp_iso (e z).symm
      rightMinimal :=
        (S.standardFormRecoveredIncomingMap_rightMinimal
          (k := k) z).map_equivalence E |>.postcomp_iso (e z).symm
      index := FintypeCat.of
        (MeshCategory.RightMeshData.IncomingArrow z)
      label := fun a ↦ a.1
      decomposition :=
        E.functor.mapBiproduct
            (fun a : MeshCategory.RightMeshData.IncomingArrow z ↦
              sigma.obj a.1) ≪≫
          biproduct.mapIso (fun a ↦ (e a.1).symm) }

/-- Occurrences of one algebra-skeleton label in the recovered minimal
right almost-split source are exactly the original reversed standard-form
arrows with those endpoints. -/
def standardFormAlgebraRecoveredOccurrenceEquiv (z x : Fin S.n) :
    (S.standardFormAlgebraIndecomposableSkeleton
        (k := k)).almostSplitSkeleton.RightAROccurrence
          (S.standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition
            (k := k) z) x ≃
      S.StandardFormArrow z x := by
  change {t : MeshCategory.RightMeshData.IncomingArrow z // t.1 = x} ≃
    S.StandardFormArrow z x
  exact
    { toFun := fun t ↦ Quiver.Hom.cast rfl t.2 t.1.2
      invFun := fun a ↦ ⟨⟨x, a⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨y, a⟩, h⟩
        change y = x at h
        subst y
        rfl
      right_inv := fun _ ↦ rfl }

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
