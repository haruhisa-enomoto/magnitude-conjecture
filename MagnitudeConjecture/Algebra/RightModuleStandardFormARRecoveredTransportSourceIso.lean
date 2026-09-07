import MagnitudeConjecture.Algebra.RightModuleStandardFormARRecoveredTransportMap
import MagnitudeConjecture.Algebra.RightModuleStandardFormAlgebraVertexIso

/-!
# The source object of the transported recovered right mesh
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

local instance standardFormARRecoveredTransportSourceIsoQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARRecoveredTransportSourceIsoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARRecoveredTransportSourceIsoFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARRecoveredTransportSourceIsoNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option backward.isDefEq.respectTransparency false in
/-- The initial object of the transported recovered mesh is the algebra
skeleton module at the original mesh translate. -/
def standardFormAlgebraRecoveredRightMeshSourceIso
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
    (S.standardFormAlgebraRecoveredRightMeshMap (k := k) z).X₁ ≅
      T.fgObj (S.standardFormTau z) := by
  change
    (S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)).functor.obj
      ((S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
        (S.standardFormRightMeshData.additiveVertexObj
          (k := k) (S.standardFormTau z))) ≅
      (S.standardFormAlgebraIndecomposableSkeleton (k := k)).fgObj
        (S.standardFormTau z)
  exact S.standardFormAlgebraVertexIso (k := k) (S.standardFormTau z)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
