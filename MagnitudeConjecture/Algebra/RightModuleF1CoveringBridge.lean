import MagnitudeConjecture.Algebra.RightModuleF1CoveringPrimitive
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientAlgebraEquivInequality
import MagnitudeConjecture.CategoryTheory.F1CoveringAverage

/-!
# F1 covering bridge

The F1 algebra layer only needs the two endpoint statements attached to a
standard-form component: primitive deletion does not increase surplus, and
equality is rigid on fibres.  The category-algebra endpoint is exposed here so
the production F1 files do not depend on the superseded algebra-level
covering-average umbrella.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance f1CoveringBridgeQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance f1CoveringBridgeArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance f1CoveringBridgeFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance f1CoveringBridgeNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

set_option maxHeartbeats 20000000 in
/-- F1 primitive-deletion monotonicity for the literal standard-form
component algebra. -/
theorem standardFormCoveringPrimitiveQuotient_ambientARSurplus_le
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let P := standardFormCoveringPrimitive S x₀ hconnected x
    letI : IsNoetherianRing
        (RightModule.primitiveQuotientAlgebra
          (standardFormCoveringIdempotent S x₀ hconnected x))ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    ((S.standardFormAlgebraIndecomposableSkeleton
        (k := k)).primitiveQuotientFiniteIndecomposableSkeleton P
          ).ambientARSurplus ≤
      (S.standardFormAlgebraIndecomposableSkeleton
        (k := k)).ambientARSurplus := by
  letI : IsMulTorsionFree (ProjectiveGroup S x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  let H := standardFormOppositeProjectiveSourceCategoryIsAdmissible
    S x₀ hconnected
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient
      (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
  let f := standardFormOppositeProjectiveLiftedOrbitCategoryAlgebraEquiv
    S x₀ hconnected S.standardFormMeshHomFinite
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let hlocal := H.locallyBounded.localEndomorphismRings
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let e := StandardCovering.orbitCategoryProjector (k := k) D hP x
  let P := StandardCovering.orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra (f e))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Sstd := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let Salg := Sstd.mapAlgEquiv f.symm
  have hcover :=
    StandardCovering.primitiveQuotient_ambientARSurplus_le_ambientARSurplus_of_admissible
      (k := k) D H Salg x
  let Q := Salg.primitiveQuotientFiniteIndecomposableSkeleton P
  let Qmap := Q.mapAlgEquiv (RightModule.primitiveQuotientAlgEquiv f e)
  let Pf := P.mapAlgEquiv f
  let Qstandard := Sstd.primitiveQuotientFiniteIndecomposableSkeleton Pf
  have hleft : Qstandard.ambientARSurplus = Q.ambientARSurplus :=
    (Qstandard.ambientARSurplus_eq Qmap).trans
      (Q.ambientARSurplus_mapAlgEquiv
        (RightModule.primitiveQuotientAlgEquiv f e))
  have hright : Salg.ambientARSurplus = Sstd.ambientARSurplus :=
    Sstd.ambientARSurplus_mapAlgEquiv f.symm
  have hidem : standardFormCoveringIdempotent S x₀ hconnected x = f e := by
    rfl
  cases hidem
  let Pstd := standardFormCoveringPrimitive S x₀ hconnected x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra
        (standardFormCoveringIdempotent S x₀ hconnected x))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hprimitive : Pstd = Pf := Subsingleton.elim _ _
  have hquotient :
      (Sstd.primitiveQuotientFiniteIndecomposableSkeleton Pstd
        ).ambientARSurplus = Qstandard.ambientARSurplus := by
    rw [hprimitive]
    rfl
  calc
    (Sstd.primitiveQuotientFiniteIndecomposableSkeleton Pstd
      ).ambientARSurplus = Qstandard.ambientARSurplus := hquotient
    _ = Q.ambientARSurplus := hleft
    _ ≤ Salg.ambientARSurplus := hcover
    _ = Sstd.ambientARSurplus := hright

set_option maxHeartbeats 4000000 in
/-- F1 equality rigidity for a primitive deletion of the standard-form
component algebra. -/
theorem standardFormCovering_finrank_obj_eq_one_of_ambientARSurplus_eq
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    (hEquality :
      let P := standardFormCoveringPrimitive S x₀ hconnected x
      letI : IsNoetherianRing
          (RightModule.primitiveQuotientAlgebra
            (standardFormCoveringIdempotent S x₀ hconnected x))ᵐᵒᵖ :=
        IsNoetherianRing.of_finite k _
      (S.standardFormAlgebraIndecomposableSkeleton
          (k := k)).ambientARSurplus =
        ((S.standardFormAlgebraIndecomposableSkeleton
          (k := k)).primitiveQuotientFiniteIndecomposableSkeleton P
            ).ambientARSurplus)
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) k)
    (hM : Indecomposable M)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  letI : IsMulTorsionFree (ProjectiveGroup S x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  let H := standardFormOppositeProjectiveSourceCategoryIsAdmissible
    S x₀ hconnected
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient
      (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
  let f := standardFormOppositeProjectiveLiftedOrbitCategoryAlgebraEquiv
    S x₀ hconnected S.standardFormMeshHomFinite
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let hlocal := H.locallyBounded.localEndomorphismRings
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let e := StandardCovering.orbitCategoryProjector (k := k) D hP x
  let P := StandardCovering.orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra (f e))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Sstd := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let Salg := Sstd.mapAlgEquiv f.symm
  let Q := Salg.primitiveQuotientFiniteIndecomposableSkeleton P
  let Qmap := Q.mapAlgEquiv (RightModule.primitiveQuotientAlgEquiv f e)
  let Pf := P.mapAlgEquiv f
  let Qstandard := Sstd.primitiveQuotientFiniteIndecomposableSkeleton Pf
  have hleft : Qstandard.ambientARSurplus = Q.ambientARSurplus :=
    (Qstandard.ambientARSurplus_eq Qmap).trans
      (Q.ambientARSurplus_mapAlgEquiv
        (RightModule.primitiveQuotientAlgEquiv f e))
  have hright : Salg.ambientARSurplus = Sstd.ambientARSurplus :=
    Sstd.ambientARSurplus_mapAlgEquiv f.symm
  have hidem : standardFormCoveringIdempotent S x₀ hconnected x = f e := by
    rfl
  cases hidem
  let Pstd := standardFormCoveringPrimitive S x₀ hconnected x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra
        (standardFormCoveringIdempotent S x₀ hconnected x))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hprimitive : Pstd = Pf := Subsingleton.elim _ _
  have hquotient :
      (Sstd.primitiveQuotientFiniteIndecomposableSkeleton Pstd
        ).ambientARSurplus = Qstandard.ambientARSurplus := by
    rw [hprimitive]
    rfl
  have hCoverEquality : Salg.ambientARSurplus = Q.ambientARSurplus :=
    hright.trans (hEquality.trans (hquotient.trans hleft))
  have hUpstairs :=
    StandardCovering.finrank_obj_eq_one_of_ambientARSurplus_eq_primitiveQuotient_of_admissible
      (k := k) D H Salg x hCoverEquality M hM hMx
  exact hUpstairs

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
