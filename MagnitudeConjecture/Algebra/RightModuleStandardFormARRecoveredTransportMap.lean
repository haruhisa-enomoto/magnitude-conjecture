import MagnitudeConjecture.Algebra.RightModuleStandardFormARMultiplicity

/-!
# The transported recovered standard-form right mesh
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

local instance standardFormARRecoveredTransportMapQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARRecoveredTransportMapArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARRecoveredTransportMapFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARRecoveredTransportMapNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The recovered right mesh after transport to modules over the literal
standard-form algebra. -/
def standardFormAlgebraRecoveredRightMeshMap
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :=
  (S.standardFormRecoveredRightMesh (k := k) z).map
    (S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)).functor

/-- The terminal arrow of the transported mesh is the transported additive
incoming arrow. -/
theorem standardFormAlgebraRecoveredRightMeshMap_g
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    (S.standardFormAlgebraRecoveredRightMeshMap (k := k) z).g =
      (S.standardFormProjectiveVertexModuleAlgebraEquivalence
        (k := k)).functor.map
        ((S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).map
          (S.standardFormRightMeshData.additiveIncomingMap (k := k) z.1)) :=
  rfl

/-- The transported recovered right mesh remains short exact. -/
theorem standardFormAlgebraRecoveredRightMeshMap_shortExact
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    (S.standardFormAlgebraRecoveredRightMeshMap (k := k) z).ShortExact := by
  let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  exact (ShortExact.shortExact_map_iff E.functor).2
    (S.standardFormRecoveredRightMesh_shortExact (k := k) z)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
