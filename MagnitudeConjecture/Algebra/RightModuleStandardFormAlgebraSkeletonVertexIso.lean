import MagnitudeConjecture.Algebra.RightModuleStandardFormARMultiplicity

/-!
# Standard-form algebra skeleton vertices
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormAlgebraSkeletonVertexIsoQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormAlgebraSkeletonVertexIsoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormAlgebraSkeletonVertexIsoFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormAlgebraSkeletonVertexIsoNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option backward.isDefEq.respectTransparency false in
/-- The image of a projective-vertex skeleton object is the correspondingly
labelled object in the pushed-forward algebra skeleton. -/
def standardFormAlgebraSkeletonVertexIso (i : Fin S.n) :
    let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
    let sigma := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
      (k := k)
    let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
    E.functor.obj (sigma.obj i) ≅ T.fgObj i := by
  let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  let sigma := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  exact
    (pushforwardRightModuleIndecomposableSkeletonObjIso E sigma i).symm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
