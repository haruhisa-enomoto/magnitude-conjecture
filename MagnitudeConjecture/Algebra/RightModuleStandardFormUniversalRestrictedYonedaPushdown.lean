import MagnitudeConjecture.Algebra.RightModuleStandardFormCoverLocallyBounded
import MagnitudeConjecture.Algebra.RightModuleStandardFormOppositeProjectiveCover
import MagnitudeConjecture.CategoryTheory.OrbitPushdownChangeBase
import MagnitudeConjecture.CategoryTheory.OrbitPushdownRepresentable
import MagnitudeConjecture.CategoryTheory.RestrictedYoneda

/-!
# Restricted Yoneda on the universal standard-form cover

The lifted projective category is infinite, but local boundedness is exactly
the finiteness needed by restricted Yoneda: every ambient Hom space is finite
dimensional and only finitely many lifted projectives map nontrivially to a
fixed universal-mesh object.  Thus the manuscript's recovery functor exists
upstairs as a functor to finite-support modules, without imposing a finite
object set on the cover.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalRestrictedYonedaQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalRestrictedYonedaArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- Among the lifted projective vertices, only finitely many admit a nonzero
map to a fixed object of the universal mesh category. -/
theorem standardFormUniversalProjectiveIncomingSupportFinite
    (p : Fin S.n) (X : SourceCategory S p) :
    {Y : (StandardFormProjectiveSourceCategory S p)ᵒᵖ |
      Nontrivial (Y.unop.obj ⟶ X)}.Finite := by
  let T : Set (SourceCategory S p) :=
    {Y | Nontrivial (Y ⟶ X)}
  have hT : T.Finite :=
    standardFormUniversalIncomingSupportFinite S p X
  have hpre :
      ((fun Y : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ↦
        Y.unop.obj) ⁻¹' T).Finite :=
    hT.preimage (by
      intro Y _ Z _ hYZ
      apply Opposite.unop_injective
      apply ObjectProperty.FullSubcategory.ext
      exact hYZ)
  exact hpre

/-- The representable of a universal-mesh object, restricted to lifted
projective vertices, is pointwise finite dimensional and has finite support. -/
theorem standardFormUniversalRestrictedYonedaFinite
    (p : Fin S.n) (X : SourceCategory S p) :
    CoveringHom.IsFiniteDimensionalModule
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k
      (CoveringHom.restrictedLinearYonedaLinearModule
        (k := k) (standardFormProjectiveProperty S p).ι X) := by
  apply CoveringHom.restrictedLinearYoneda_isFiniteDimensional_of_finite_support
  · intro Y
    change FiniteDimensional k (Y.obj ⟶ X)
    exact S.standardFormUniversalMeshHomFinite p Y.obj X
  · exact standardFormUniversalProjectiveIncomingSupportFinite S p X

/-- The ambient opposite representable `Hom(-,X)` is itself a finite-support
module on the whole universal mesh category. -/
theorem standardFormUniversalOppositeRepresentableFinite
    (p : Fin S.n) (X : SourceCategory S p) :
    CoveringHom.IsFiniteDimensionalModule
      (C := (SourceCategory S p)ᵒᵖ) k
      (CoveringHom.linearCoyonedaLinearModule
        (k := k) (C := (SourceCategory S p)ᵒᵖ)
        (Opposite.op X)) := by
  constructor
  · intro Y
    let e := CoveringHom.oppositeHomLinearEquiv
      (k := k) (Opposite.op X) Y
    letI : FiniteDimensional k (Y.unop ⟶ X) :=
      S.standardFormUniversalMeshHomFinite p Y.unop X
    exact e.symm.finiteDimensional
  · let T : Set (SourceCategory S p) :=
      {Y | Nontrivial (Y ⟶ X)}
    have hT : T.Finite :=
      standardFormUniversalIncomingSupportFinite S p X
    have hpre : ((fun Y : (SourceCategory S p)ᵒᵖ ↦ Y.unop) ⁻¹' T).Finite :=
      hT.preimage Opposite.unop_injective.injOn
    refine hpre.subset ?_
    intro Y hY
    change Nontrivial (Opposite.op X ⟶ Y) at hY
    exact (CoveringHom.oppositeHomLinearEquiv
      (k := k) (Opposite.op X) Y).toEquiv.nontrivial_congr.mp hY

/-- Restricting the ambient opposite representable to lifted projective
vertices gives the raw restricted-Yoneda module. -/
noncomputable def standardFormUniversalRestrictedYonedaAmbientOppositeIso
    (p : Fin S.n) (X : SourceCategory S p) :
    CoveringHom.restrictedLinearYoneda
        (k := k) (standardFormProjectiveProperty S p).ι X ≅
      (standardFormProjectiveProperty S p).ι.op ⋙
        (linearCoyoneda k (SourceCategory S p)ᵒᵖ).obj
          (Opposite.op (Opposite.op X)) := by
  refine NatIso.ofComponents (fun Y ↦
    (CoveringHom.oppositeHomLinearEquiv
      (k := k) (Opposite.op X) (Opposite.op Y.unop.obj)).symm.toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  rfl

/-- Linear-module form of restriction of the ambient opposite
representable. -/
noncomputable def standardFormUniversalAmbientOppositeRepresentableRestriction
    (p : Fin S.n) (X : SourceCategory S p) :
    CoveringHom.LinearModuleCategory
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k :=
  ⟨(standardFormProjectiveProperty S p).ι.op ⋙
      (linearCoyoneda k (SourceCategory S p)ᵒᵖ).obj
        (Opposite.op (Opposite.op X)),
    inferInstance, inferInstance⟩

/-- Bundled linear-module comparison between universal restricted Yoneda and
restriction of the ambient opposite representable. -/
noncomputable def
    standardFormUniversalRestrictedYonedaAmbientOppositeLinearModuleIso
    (p : Fin S.n) (X : SourceCategory S p) :
    CoveringHom.restrictedLinearYonedaLinearModule
        (k := k) (standardFormProjectiveProperty S p).ι X ≅
      standardFormUniversalAmbientOppositeRepresentableRestriction S p X :=
  (CoveringHom.IsLinearModule
    (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k).isoMk
    (standardFormUniversalRestrictedYonedaAmbientOppositeIso S p X)

/-- The opposite lifted-projective inclusion commutes with the restricted and
ambient opposite deck shifts. -/
@[implicit_reducible]
noncomputable def
    standardFormUniversalOppositeProjectiveInclusionCommShift
    (p : Fin S.n) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    let H := standardFormProjectiveInvariantData S p
    let DProjective := standardFormProjectiveDeckShift S p
    let DOpposite := standardFormOppositeProjectiveDeckShift S p
    let DAmbientOpposite := DAmbient.op
    let J := (standardFormProjectiveProperty S p).ι
    letI := DProjective.hasShift
    letI := DAmbient.hasShift
    letI : J.CommShift (Additive G) := H.inclusionCommShift
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := DOpposite.hasShift
    letI := DAmbientOpposite.hasShift
    J.op.CommShift (Additive G) := by
  dsimp only
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let H := standardFormProjectiveInvariantData S p
  let DProjective := standardFormProjectiveDeckShift S p
  letI := DProjective.hasShift
  letI := DAmbient.hasShift
  letI : (standardFormProjectiveProperty S p).ι.CommShift
      (Additive
        (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData p)) := H.inclusionCommShift
  change (OppositeShift.functor
    (Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p))
    (standardFormProjectiveProperty S p).ι).CommShift
      (Additive
        (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData p))
  infer_instance

/-- Before choosing orbit representatives, pushdown of universal restricted
Yoneda is change of base of pushdown of the ambient opposite representable. -/
noncomputable def
    standardFormUniversalRestrictedYonedaOrbitPushdownToAmbientIso
    (p : Fin S.n) (X : SourceCategory S p) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
    let DAmbientOpposite := DAmbient.op
    let J := (standardFormProjectiveProperty S p).ι
    let F : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ⥤
        (SourceCategory S p)ᵒᵖ := J.op
    let M := (linearCoyoneda k (SourceCategory S p)ᵒᵖ).obj
      (Opposite.op (Opposite.op X))
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := DProjectiveOpposite.hasShift
    letI := DProjectiveOpposite.additiveShift
    letI := DProjectiveOpposite.linearShift (k := k)
    letI := DAmbientOpposite.hasShift
    letI := DAmbientOpposite.additiveShift
    letI := DAmbientOpposite.linearShift (k := k)
    letI : F.CommShift (Additive G) :=
      standardFormUniversalOppositeProjectiveInclusionCommShift S p
    CoveringHom.orbitPushdown (A := Additive G)
        (CoveringHom.restrictedLinearYoneda (k := k) J X) ≅
      CoveringHom.shiftOrbitMapFunctor (k := k) (A := Additive G) F ⋙
        CoveringHom.orbitPushdown (A := Additive G) M := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
  let DAmbientOpposite := DAmbient.op
  let J := (standardFormProjectiveProperty S p).ι
  let F : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ⥤
      (SourceCategory S p)ᵒᵖ := J.op
  let M := (linearCoyoneda k (SourceCategory S p)ᵒᵖ).obj
    (Opposite.op (Opposite.op X))
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := DProjectiveOpposite.hasShift
  letI := DProjectiveOpposite.additiveShift
  letI := DProjectiveOpposite.linearShift (k := k)
  letI := DAmbientOpposite.hasShift
  letI := DAmbientOpposite.additiveShift
  letI := DAmbientOpposite.linearShift (k := k)
  letI : F.CommShift (Additive G) :=
    standardFormUniversalOppositeProjectiveInclusionCommShift S p
  let Push := CoveringHom.linearModuleOrbitPushdown
    (k := k) (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ)
    (A := Additive G)
  let eRestrict :=
    standardFormUniversalRestrictedYonedaAmbientOppositeLinearModuleIso S p X
  let ePush :=
    (CoveringHom.IsLinearModule
      (C := CoveringHom.ShiftOrbitCategory
        (StandardFormProjectiveSourceCategory S p)ᵒᵖ
        (Additive G)) k).ι.mapIso (Push.mapIso eRestrict)
  exact ePush ≪≫
    CoveringHom.orbitPushdownCommShiftIso (k := k) F M

/-- Restricting the preceding comparison to one chosen representative per
projective deck orbit. -/
noncomputable def
    standardFormUniversalRestrictedYonedaOrbitSkeletonPushdownToAmbientIso
    (p : Fin S.n) (X : SourceCategory S p) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
    let DAmbientOpposite := DAmbient.op
    let J := (standardFormProjectiveProperty S p).ι
    let F : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ⥤
        (SourceCategory S p)ᵒᵖ := J.op
    let M := (linearCoyoneda k (SourceCategory S p)ᵒᵖ).obj
      (Opposite.op (Opposite.op X))
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := DProjectiveOpposite.hasShift
    letI := DProjectiveOpposite.additiveShift
    letI := DProjectiveOpposite.linearShift (k := k)
    letI := DAmbientOpposite.hasShift
    letI := DAmbientOpposite.additiveShift
    letI := DAmbientOpposite.linearShift (k := k)
    letI : F.CommShift (Additive G) :=
      standardFormUniversalOppositeProjectiveInclusionCommShift S p
    CoveringHom.orbitSkeletonPushdown (G := G)
        (CoveringHom.restrictedLinearYoneda (k := k) J X) ≅
      CoveringHom.deckOrbitRepresentativeFunctor
          (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) (G := G) ⋙
        (CoveringHom.shiftOrbitMapFunctor
            (k := k) (A := Additive G) F ⋙
          CoveringHom.orbitPushdown (A := Additive G) M) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
  let DAmbientOpposite := DAmbient.op
  let J := (standardFormProjectiveProperty S p).ι
  let F : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ⥤
      (SourceCategory S p)ᵒᵖ := J.op
  let M := (linearCoyoneda k (SourceCategory S p)ᵒᵖ).obj
    (Opposite.op (Opposite.op X))
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := DProjectiveOpposite.hasShift
  letI := DProjectiveOpposite.additiveShift
  letI := DProjectiveOpposite.linearShift (k := k)
  letI := DAmbientOpposite.hasShift
  letI := DAmbientOpposite.additiveShift
  letI := DAmbientOpposite.linearShift (k := k)
  letI : F.CommShift (Additive G) :=
    standardFormUniversalOppositeProjectiveInclusionCommShift S p
  exact Functor.isoWhiskerLeft
    (CoveringHom.deckOrbitRepresentativeFunctor
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) (G := G))
    (standardFormUniversalRestrictedYonedaOrbitPushdownToAmbientIso S p X)

/-- Skeletal pushdown of a lifted restricted representable is the ambient
opposite orbit representable, pulled back to the chosen projective orbit
representatives. -/
noncomputable def
    standardFormUniversalRestrictedYonedaOrbitSkeletonPushdownRepresentableIso
    (p : Fin S.n) (X : SourceCategory S p) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
    let DAmbientOpposite := DAmbient.op
    let J := (standardFormProjectiveProperty S p).ι
    let F : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ⥤
        (SourceCategory S p)ᵒᵖ := J.op
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := DProjectiveOpposite.hasShift
    letI := DProjectiveOpposite.additiveShift
    letI := DProjectiveOpposite.linearShift (k := k)
    letI := DAmbientOpposite.hasShift
    letI := DAmbientOpposite.additiveShift
    letI := DAmbientOpposite.linearShift (k := k)
    letI : F.CommShift (Additive G) :=
      standardFormUniversalOppositeProjectiveInclusionCommShift S p
    CoveringHom.orbitSkeletonPushdown (G := G)
        (CoveringHom.restrictedLinearYoneda (k := k) J X) ≅
      (CoveringHom.deckOrbitRepresentativeFunctor
          (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) (G := G) ⋙
        CoveringHom.shiftOrbitMapFunctor
          (k := k) (A := Additive G) F) ⋙
        (linearCoyoneda k
          (CoveringHom.ShiftOrbitCategory
            (SourceCategory S p)ᵒᵖ (Additive G))).obj
          (Opposite.op
            (show CoveringHom.ShiftOrbitCategory
                (SourceCategory S p)ᵒᵖ (Additive G) from
              Opposite.op X)) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
  let DAmbientOpposite := DAmbient.op
  let J := (standardFormProjectiveProperty S p).ι
  let F : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ⥤
      (SourceCategory S p)ᵒᵖ := J.op
  let M := (linearCoyoneda k (SourceCategory S p)ᵒᵖ).obj
    (Opposite.op (Opposite.op X))
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := DProjectiveOpposite.hasShift
  letI := DProjectiveOpposite.additiveShift
  letI := DProjectiveOpposite.linearShift (k := k)
  letI := DAmbientOpposite.hasShift
  letI := DAmbientOpposite.additiveShift
  letI := DAmbientOpposite.linearShift (k := k)
  letI : F.CommShift (Additive G) :=
    standardFormUniversalOppositeProjectiveInclusionCommShift S p
  let Rep := CoveringHom.deckOrbitRepresentativeFunctor
    (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) (G := G)
  let Map := CoveringHom.shiftOrbitMapFunctor
    (k := k) (A := Additive G) F
  let P := CoveringHom.orbitPushdown (A := Additive G) M
  let R := (linearCoyoneda k
    (CoveringHom.ShiftOrbitCategory
      (SourceCategory S p)ᵒᵖ (Additive G))).obj
        (Opposite.op
          (show CoveringHom.ShiftOrbitCategory
              (SourceCategory S p)ᵒᵖ (Additive G) from
            Opposite.op X))
  exact
    standardFormUniversalRestrictedYonedaOrbitSkeletonPushdownToAmbientIso
        S p X ≪≫
      (Functor.associator Rep Map P).symm ≪≫
      Functor.isoWhiskerLeft (Rep ⋙ Map)
        (CoveringHom.orbitPushdownLinearCoyonedaIso
          (k := k) (A := Additive G) (Opposite.op X))


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
