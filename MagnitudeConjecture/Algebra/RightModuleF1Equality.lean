import MagnitudeConjecture.Algebra.RightModuleF1Inequality

/-!
# F1 equality interfaces for the magnitude conjecture

The declarations are exposed under the frozen-route names so the public
endpoint has a stable migration seam. The finite support and deletion-order
interfaces are independent of this retained standard-form consequence; the
remaining category-level replacement is tracked by the correspondence record.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormEqualityQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormEqualityArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- Every augmented-walk component of the standard form has nonnegative
Auslander--Reiten surplus. -/
theorem standardFormComponentSurplus_nonnegative
    (c : S.StandardFormWalkComponent) :
    0 ≤ S.standardFormComponentSurplus c := by
  letI : Fintype (S.StandardFormWalkComponentVertex c) :=
    Fintype.ofFinite _
  letI : FiniteDimensional k (S.standardFormComponentAlgebra (k := k) c) :=
    S.standardFormComponentAlgebra_finiteDimensional (k := k) c
  letI : IsNoetherianRing
      (S.standardFormComponentAlgebra (k := k) c)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  rw [← S.standardFormComponentAlgebra_ambientARSurplus_eq_componentSurplus
    (k := k) c]
  exact (S.standardFormComponentAlgebraIndecomposableSkeleton
    (k := k) c).ambientARSurplus_nonnegative

/-- Equality in the ambient magnitude inequality forces equality on every
augmented-walk component. -/
theorem standardFormComponentSurplus_eq_zero
    (hzero : S.ambientARSurplus = 0)
    (c : S.StandardFormWalkComponent) :
    S.standardFormComponentSurplus c = 0 :=
  S.standardFormComponentSurplus_eq_zero_of_ambientARSurplus_eq_zero
    S.standardFormComponentSurplus_nonnegative hzero c

/-- Consequently the literal algebra recovered from every standard-form
component has zero ambient Auslander--Reiten surplus. -/
theorem standardFormComponentAlgebra_ambientARSurplus_eq_zero_of_ambientARSurplus_eq_zero
    (hzero : S.ambientARSurplus = 0)
    (c : S.StandardFormWalkComponent) :
    letI : Fintype (S.StandardFormWalkComponentVertex c) :=
      Fintype.ofFinite _
    letI : FiniteDimensional k
        (S.standardFormComponentAlgebra (k := k) c) :=
      S.standardFormComponentAlgebra_finiteDimensional (k := k) c
    letI : IsNoetherianRing
        (S.standardFormComponentAlgebra (k := k) c)ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    (S.standardFormComponentAlgebraIndecomposableSkeleton
      (k := k) c).ambientARSurplus = 0 := by
  rw [S.standardFormComponentAlgebra_ambientARSurplus_eq_componentSurplus
    (k := k) c]
  exact S.standardFormComponentSurplus_eq_zero
    hzero c

set_option maxHeartbeats 5000000 in
/-- Frozen manuscript, equality propagation through one standard-form
primitive deletion: zero ambient surplus makes every nonzero fibre of an
indecomposable finite module on the universal cover one-dimensional. -/
theorem UniversalCover.standardFormCovering_finrank_obj_eq_one_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (UniversalCover.StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    (hzero : S.ambientARSurplus = 0)
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (UniversalCover.StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) k)
    (hM : Indecomposable M)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  let P := UniversalCover.standardFormCoveringPrimitive
    S x₀ hconnected x
  let B := S.standardFormAlgebra S.standardFormMeshHomFinite
  letI : FiniteDimensional k B :=
    S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
  letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let Sstd := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let Bq := RightModule.primitiveQuotientAlgebra
    (UniversalCover.standardFormCoveringIdempotent S x₀ hconnected x)
  letI : IsNoetherianRing Bqᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let Q := Sstd.primitiveQuotientFiniteIndecomposableSkeleton P
  have hQnonnegative : 0 ≤ Q.ambientARSurplus :=
    Q.ambientARSurplus_nonnegative
  have hdeletion : Q.ambientARSurplus ≤ Sstd.ambientARSurplus :=
    UniversalCover.standardFormCoveringPrimitiveQuotient_ambientARSurplus_le
      S x₀ hconnected x
  have hstandardZero : Sstd.ambientARSurplus = 0 := by
    rw [S.standardFormAlgebra_ambientARSurplus_eq_original (k := k)]
    exact hzero
  have hQzero : Q.ambientARSurplus = 0 :=
    le_antisymm (hdeletion.trans_eq hstandardZero) hQnonnegative
  exact UniversalCover.standardFormCovering_finrank_obj_eq_one_of_ambientARSurplus_eq
    S x₀ hconnected x (hstandardZero.trans hQzero.symm) M hM hMx

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
