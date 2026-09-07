import MagnitudeConjecture.Algebra.RightModuleStandardFormAlgebraSkeletonVertexIso

/-!
# The map in the recovered standard-form decomposition
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARRecoveredDecompositionMapQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARRecoveredDecompositionMapArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARRecoveredDecompositionMapFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARRecoveredDecompositionMapNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The map stored in the recovered decomposition is the transported
recovered incoming map followed by the named skeleton vertex isomorphism. -/
theorem standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition_map_vertexIso
    (z : Fin S.n) :
    (S.standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition
      (k := k) z).map =
      (S.standardFormProjectiveVertexModuleAlgebraEquivalence
        (k := k)).functor.map
          (S.standardFormRecoveredIncomingMap (k := k) z) ≫
        (S.standardFormAlgebraSkeletonVertexIso (k := k) z).hom :=
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
