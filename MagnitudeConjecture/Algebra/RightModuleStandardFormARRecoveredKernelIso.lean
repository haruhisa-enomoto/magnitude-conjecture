import MagnitudeConjecture.Algebra.RightModuleStandardFormARRecoveredTransportData
import MagnitudeConjecture.CategoryTheory.ShortExactKernelTransport

/-!
# The recovered standard-form mesh source as an AR kernel
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

local instance standardFormARRecoveredKernelIsoQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARRecoveredKernelIsoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormARRecoveredKernelIsoFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormARRecoveredKernelIsoNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The original mesh-translate module is the kernel of the transported
recovered right-almost-split map. -/
def standardFormAlgebraRecoveredRightMeshKernelIso
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
    let R :=
      S.standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition
        (k := k) z.1
    T.fgObj (S.standardFormTau z) ≅ kernel R.map := by
  dsimp only
  let T := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let R :=
    S.standardFormAlgebraRecoveredMinimalRightAlmostSplitDecomposition
      (k := k) z.1
  let Mmap := S.standardFormAlgebraRecoveredRightMeshMap (k := k) z
  have hMmap : Mmap.ShortExact :=
    S.standardFormAlgebraRecoveredRightMeshMap_shortExact (k := k) z
  let eEnd : Mmap.X₃ ≅ T.fgObj z.1 :=
    S.standardFormAlgebraRecoveredRightMeshEndIso (k := k) z
  have hRmap : Mmap.g ≫ eEnd.hom = R.map :=
    S.standardFormAlgebraRecoveredRightMeshMap_comp_endIso (k := k) z
  let eKernel : Mmap.X₁ ≅ kernel R.map :=
    Mmap.sourceIsoKernelOfShortExactCompIso hMmap R.map eEnd hRmap
  let eSource : Mmap.X₁ ≅ T.fgObj (S.standardFormTau z) :=
    S.standardFormAlgebraRecoveredRightMeshSourceIso (k := k) z
  exact eSource.symm ≪≫ eKernel

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
