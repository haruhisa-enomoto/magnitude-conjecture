import MagnitudeConjecture.Algebra.RightModuleStandardFormARRecoveredTransportEndIso
import MagnitudeConjecture.Algebra.RightModuleStandardFormARRecoveredTransportSourceIso
import MagnitudeConjecture.Algebra.RightModuleStandardFormARRecoveredDecompositionMap

/-!
# Compatibility of the transported recovered standard-form right mesh
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CoveringHom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARRecoveredTransportDataQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARRecoveredTransportDataArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARRecoveredTransportDataFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARRecoveredTransportDataNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option maxHeartbeats 800000 in
/-- The transported terminal map followed by the terminal object isomorphism
is the recovered minimal right-almost-split map. -/
theorem standardFormAlgebraRecoveredRightMeshMap_comp_endIso
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    let Mmap := S.standardFormAlgebraRecoveredRightMeshMap (k := k) z
    let eEnd := S.standardFormAlgebraRecoveredRightMeshEndIso (k := k) z
    let R :=
      S.standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition
        (k := k) z.1
    Mmap.g ≫ eEnd.hom = R.map := by
  dsimp only
  let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  let sigma := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let e (i : Fin S.n) : T.fgObj i ≅ E.functor.obj (sigma.obj i) :=
    pushforwardRightModuleIndecomposableSkeletonObjIso E sigma i
  rw [S.standardFormAlgebraRecoveredRightMeshMap_g (k := k) z,
    S.standardFormAlgebraRecoveredRightMeshEndIso_hom (k := k) z,
    S.standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition_map_vertexIso
      (k := k) z.1,
    S.standardFormRecoveredIncomingMap_eq_map_additiveIncoming_comp_singletonIso
      (k := k) z.1]
  dsimp only [standardFormAlgebraIndecomposableSkeleton,
    pushforwardRightModuleIndecomposableSkeleton,
    standardFormProjectiveVertexModuleIndecomposableSkeleton]
  rw [E.functor.map_comp]
  dsimp only [standardFormAlgebraVertexIso]
  simp only [Iso.trans_hom]
  dsimp only [standardFormAlgebraMappedSingletonIso]
  simp only [Functor.mapIso_hom]
  exact (Category.assoc _ _ _).symm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
