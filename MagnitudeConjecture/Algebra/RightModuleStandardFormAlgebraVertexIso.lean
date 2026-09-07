import MagnitudeConjecture.Algebra.RightModuleStandardFormAlgebraMappedSingletonIso
import MagnitudeConjecture.Algebra.RightModuleStandardFormAlgebraSkeletonVertexIso

/-!
# Standard-form algebra vertex objects

This file isolates the objectwise isomorphism used when the recovered mesh is
transported to modules over the literal standard-form algebra.
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

local instance standardFormAlgebraVertexIsoQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormAlgebraVertexIsoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormAlgebraVertexIsoFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormAlgebraVertexIsoNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option backward.isDefEq.respectTransparency false in
/-- The transported additive-Yoneda image of a singleton mesh vertex is the
correspondingly labelled module in the standard-form algebra skeleton. -/
def standardFormAlgebraVertexIso (i : Fin S.n) :
    let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
    let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
    E.functor.obj
        ((S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
          (S.standardFormRightMeshData.additiveVertexObj (k := k) i)) ≅
      T.fgObj i := by
  exact S.standardFormAlgebraMappedSingletonIso (k := k) i ≪≫
    S.standardFormAlgebraSkeletonVertexIso (k := k) i

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
