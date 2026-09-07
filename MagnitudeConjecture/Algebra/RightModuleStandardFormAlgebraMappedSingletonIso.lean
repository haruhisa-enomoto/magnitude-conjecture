import MagnitudeConjecture.Algebra.RightModuleStandardFormARMultiplicity

/-!
# Transported standard-form singleton vertices
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

local instance standardFormAlgebraMappedSingletonIsoQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormAlgebraMappedSingletonIsoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- The algebra equivalence maps the singleton additive-Yoneda isomorphism. -/
def standardFormAlgebraMappedSingletonIso (i : Fin S.n) :
    let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
    let sigma := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
      (k := k)
    E.functor.obj
        ((S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
          (S.standardFormRightMeshData.additiveVertexObj (k := k) i)) ≅
      E.functor.obj (sigma.obj i) := by
  let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  exact E.functor.mapIso
    (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) i)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
