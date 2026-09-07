import MagnitudeConjecture.Algebra.RightModuleStandardFormARRecoveredTransportMap
import MagnitudeConjecture.Algebra.RightModuleStandardFormAlgebraVertexIso

/-!
# The terminal object of the transported recovered right mesh
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

local instance standardFormARRecoveredTransportEndIsoQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARRecoveredTransportEndIsoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARRecoveredTransportEndIsoFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARRecoveredTransportEndIsoNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option backward.isDefEq.respectTransparency false in
/-- The terminal object of the transported recovered mesh is the algebra
skeleton module with the same label. -/
def standardFormAlgebraRecoveredRightMeshEndIso
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
    (S.standardFormAlgebraRecoveredRightMeshMap (k := k) z).X₃ ≅
      T.fgObj z.1 := by
  change
    (S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)).functor.obj
      ((S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
        (S.standardFormRightMeshData.additiveVertexObj (k := k) z.1)) ≅
      (S.standardFormAlgebraIndecomposableSkeleton (k := k)).fgObj z.1
  exact S.standardFormAlgebraVertexIso (k := k) z.1

/-- The terminal transport isomorphism is the generic vertex isomorphism at
the terminal label. -/
theorem standardFormAlgebraRecoveredRightMeshEndIso_hom
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    (S.standardFormAlgebraRecoveredRightMeshEndIso (k := k) z).hom =
      (S.standardFormAlgebraVertexIso (k := k) z.1).hom :=
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
