import MagnitudeConjecture.Algebra.RightModuleStandardFormRiedtmann
import MagnitudeConjecture.CategoryTheory.MeshSimplePresentation

/-!
# Projective simple resolutions in the standard-form mesh category

The generic mesh-simple presentation is exact at its middle term, but its
translation map need not be monic for an arbitrary translation quiver.  For
the standard form the normalized universal realization identifies the arrows
leaving a translated mesh source with a genuine left almost-split
monomorphism.  The two covering Hom equivalences therefore make the
translation map monic downstairs.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormSimpleResolutionQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormSimpleResolutionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The base outgoing categorical arrow underlying an outgoing arrow at a
universal-cover vertex. -/
def projectedOutgoingArrow
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Costar W) :
    MeshCategory.RightMeshData.OutgoingArrow W.1 :=
  ⟨d.1.1,
    (MeshCategory.RightMeshData.UniversalCover.projection
      S.standardFormRightMeshData x₀).map d.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The universal mesh projection sends an outgoing represented arrow to
its underlying outgoing represented arrow downstairs. -/
@[simp]
theorem meshProjection_map_outgoingArrowHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Costar W) :
    (meshProjection S x₀).map
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).outgoingArrowHom (k := k) d) =
      S.standardFormRightMeshData.outgoingArrowHom (k := k)
        (projectedOutgoingArrow S x₀ W d) := by
  unfold meshProjection
    MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor
    MeshCategory.RightMeshData.outgoingArrowHom
  rw [(MeshCategory.RightMeshData.UniversalCover.cover
    S.standardFormRightMeshData x₀).functorUsingSourceFintype_map_quotient_pathHom]
  rfl

@[simp]
theorem projectedOutgoingArrow_meshStarCostarEquiv
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (d : Quiver.Star W.1) :
    projectedOutgoingArrow S x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W)
        (S.standardFormUniversalMeshStarCostarEquiv x₀ W d) =
      ⟨d.1.1,
        S.standardFormRightMeshData.arrowEquiv
          (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
            S.standardFormRightMeshData x₀ W)
          d.1.1
          ((MeshCategory.RightMeshData.UniversalCover.projection
            S.standardFormRightMeshData x₀).map d.2)⟩ := by
  rfl

end UniversalCover

set_option backward.isDefEq.respectTransparency false in
/-- Every evaluated translation map in the standard-form mesh-simple
presentation is injective. -/
theorem standardFormPairedCoefficientLinearMap_injective
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n) :
    Function.Injective
      (S.standardFormRightMeshData.pairedCoefficientLinearMap
        (k := k) z x) := by
  let T := S.standardFormRightMeshData
  let W₀ := MeshCategory.RightMeshData.UniversalCover.baseVertex T z.1
  have hW₀ : W₀ ∉
      MeshCategory.RightMeshData.UniversalCover.projectiveSet T z.1 := by
    change z.1 ∉ S.standardFormProjectiveSet
    exact z.2
  let W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex T z.1 //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet T z.1} :=
    ⟨W₀, hW₀⟩
  let Wτ := MeshCategory.RightMeshData.UniversalCover.tau T z.1 W
  have hWτ : Wτ.1 = T.tau z := rfl
  let E := UniversalCover.meshHomLinearEquivFGIndecFixedTarget
    S z.1 x Wτ
  apply (injective_iff_map_eq_zero
    (T.pairedCoefficientLinearMap (k := k) z x)).mpr
  intro q hq
  have hcoeff : T.pairedCoefficient (k := k) z q = 0 := hq
  have hdown (d : Quiver.Star W.1) :
      q ≫ T.outgoingArrowHom (k := k)
        (UniversalCover.projectedOutgoingArrow S z.1 Wτ
          (S.standardFormUniversalMeshStarCostarEquiv z.1 W d)) = 0 := by
    rw [UniversalCover.projectedOutgoingArrow_meshStarCostarEquiv]
    exact congrFun hcoeff
      ⟨d.1.1,
        (MeshCategory.RightMeshData.UniversalCover.projection T z.1).map d.2⟩
  let qF := E q
  have hqF (c : Quiver.Costar Wτ) :
      qF.hom ≫ S.standardFormUniversalMappedOutgoingHom z.1 Wτ c = 0 := by
    obtain ⟨d, rfl⟩ :=
      (S.standardFormUniversalMeshStarCostarEquiv z.1 W).surjective c
    let e :=
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData T z.1).outgoingArrowHom
        (k := k) (S.standardFormUniversalMeshStarCostarEquiv z.1 W d)
    have hbase :
        q ≫ (UniversalCover.meshProjection S z.1).map e = 0 := by
      dsimp only [e]
      rw [UniversalCover.meshProjection_map_outgoingArrowHom]
      exact hdown d
    have hpost := UniversalCover.meshHomLinearEquivFGIndecFixedTarget_postcomp
      S z.1 x Wτ
        (S.standardFormUniversalMeshStarCostarEquiv z.1 W d).1
        e
        q
    have hzero := congrArg InducedCategory.Hom.hom
      (show UniversalCover.meshHomLinearEquivFGIndecFixedTarget S z.1 x
          (S.standardFormUniversalMeshStarCostarEquiv z.1 W d).1
            (q ≫ (UniversalCover.meshProjection S z.1).map e) = 0 by
        rw [hbase, map_zero])
    rw [hpost] at hzero
    change _ = 0 at hzero
    rw [InducedCategory.comp_hom,
      S.standardFormUniversalIndecMeshFunctor_map_outgoingArrowHom] at hzero
    rw [S.standardFormUniversalMappedOutgoingHom_eq_normalized]
    simpa only [qF, E, e] using hzero
  have hqFzero : qF.hom = 0 :=
    S.eq_zero_of_comp_standardFormUniversalMappedOutgoingHom_of_not_injective
      z.1 x Wτ (S.standardFormUniversal_tau_noninjective z.1 W) qF.hom hqF
  have hqFzero' : qF = 0 := by
    apply InducedCategory.hom_ext
    exact hqFzero
  apply E.injective
  change qF = E 0
  rw [hqFzero', map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The first map of the standard-form right mesh is already monic in the
finite additive hull of the raw mesh category. -/
theorem standardFormAdditiveTranslationMap_mono
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    Mono (S.standardFormRightMeshData.additiveTranslationMap
      (k := k) z) := by
  let T := S.standardFormRightMeshData
  apply Preadditive.mono_of_cancel_zero
  intro W f hf
  apply Mat_.hom_ext
  intro i j
  cases j
  let x : Fin S.n := W.X i
  let row : T.additiveVertexObj (k := k) x ⟶
      T.additiveVertexObj (k := k) (T.tau z) :=
    fun _ _ ↦ f i PUnit.unit
  have hrow : row ≫ T.additiveTranslationMap (k := k) z = 0 := by
    apply Mat_.hom_ext
    rintro ⟨⟩ a
    have hentry := congrFun (congrFun hf i) a
    change (row ≫ T.additiveTranslationMap (k := k) z)
      PUnit.unit a = 0
    change (f ≫ T.additiveTranslationMap (k := k) z) i a = 0 at hentry
    exact hentry
  have hcoeff : T.pairedCoefficient (k := k) z
      (T.additiveVertexHomLinearEquiv (k := k) x (T.tau z) row) = 0 := by
    rw [← T.additiveIncomingHomLinearEquiv_comp_translationMap
      (k := k) x z row, hrow, map_zero]
  have hrowZero : row = 0 := by
    apply (T.additiveVertexHomLinearEquiv
      (k := k) x (T.tau z)).injective
    apply S.standardFormPairedCoefficientLinearMap_injective z x
    rw [T.pairedCoefficientLinearMap_apply (k := k)]
    exact hcoeff
  have hentry := congrFun (congrFun hrowZero PUnit.unit) PUnit.unit
  exact hentry

set_option backward.isDefEq.respectTransparency false in
/-- The first differential in the standard-form mesh-simple presentation is
a monomorphism in the ambient module category. -/
theorem standardFormTranslationMap_mono
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    Mono (S.standardFormRightMeshData.translationMap (k := k) z) := by
  haveI hmonoApp
      (X : S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) :
      Mono ((S.standardFormRightMeshData.translationMap (k := k) z).app X) := by
    rw [ModuleCat.mono_iff_injective]
    exact (S.standardFormPairedCoefficientLinearMap_injective z X.unop).comp
      InducedCategory.homLinearEquiv.injective
  exact NatTrans.mono_of_mono_app _

set_option backward.isDefEq.respectTransparency false in
/-- The finite-dimensional lift of the standard-form translation map is
monic. -/
theorem standardFormTranslationMapFinite_mono
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    Mono (S.standardFormRightMeshData.translationMapFinite
      (k := k) hP z) := by
  let T := S.standardFormRightMeshData
  let J := (IsFiniteDimensionalModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let I := (IsLinearModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  haveI : Mono (I.map (J.map
      (T.translationMapFinite (k := k) hP z))) := by
    change Mono (T.translationMap (k := k) z)
    exact S.standardFormTranslationMap_mono z
  haveI : Mono (J.map (T.translationMapFinite (k := k) hP z)) :=
    I.mono_of_mono_map inferInstance
  exact J.mono_of_mono_map inferInstance

/-- At a projective boundary vertex, the incoming map is monic in the
ambient module category. -/
theorem standardFormIncomingMap_mono_of_projective
    (z : Fin S.n) (hz : z ∈ S.standardFormProjectiveSet) :
    Mono (S.standardFormRightMeshData.incomingMap (k := k) z) := by
  let T := S.standardFormRightMeshData
  haveI hmonoApp (X : (T.VertexCategory (k := k))ᵒᵖ) :
      Mono ((T.incomingMap (k := k) z).app X) := by
    rw [ModuleCat.mono_iff_injective]
    exact T.incomingMap_app_injective_of_projective (k := k) z hz X
  exact NatTrans.mono_of_mono_app _

set_option backward.isDefEq.respectTransparency false in
/-- The finite-dimensional incoming map at a projective boundary vertex is
monic. -/
theorem standardFormIncomingMapFinite_mono_of_projective
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : Fin S.n) (hz : z ∈ S.standardFormProjectiveSet) :
    Mono (S.standardFormRightMeshData.incomingMapFinite
      (k := k) hP z) := by
  let T := S.standardFormRightMeshData
  let J := (IsFiniteDimensionalModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  let I := (IsLinearModule
    (C := (T.VertexCategory (k := k))ᵒᵖ) k).ι
  haveI : Mono (I.map (J.map
      (T.incomingMapFinite (k := k) hP z))) := by
    change Mono (T.incomingMap (k := k) z)
    exact S.standardFormIncomingMap_mono_of_projective z hz
  haveI : Mono (J.map (T.incomingMapFinite (k := k) hP z)) :=
    I.mono_of_mono_map inferInstance
  exact J.mono_of_mono_map inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- At a projective boundary vertex, the finite mesh simple has projective
dimension at most one. -/
theorem standardFormProjectiveSimpleFiniteModule_hasProjectiveDimensionLE_one
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : Fin S.n) (hz : z ∈ S.standardFormProjectiveSet) :
    HasProjectiveDimensionLE
      (S.standardFormRightMeshData.simpleFiniteModule (k := k) z) 1 := by
  let T := S.standardFormRightMeshData
  let P := T.simplePositiveFiniteShortComplex (k := k) hP z
  have hPshort : P.ShortExact := by
    letI : Mono P.f := by
      change Mono (T.incomingMapFinite (k := k) hP z)
      exact S.standardFormIncomingMapFinite_mono_of_projective hP z hz
    letI : Epi P.g := by
      change Epi (T.simpleProjectionFinite (k := k) hP z)
      infer_instance
    refine { exact := ?_ }
    exact T.simplePositiveFiniteShortComplex_exact (k := k) hP z
  have hP₁ : Projective P.X₁ := by
    change Projective (T.incomingCoefficientFiniteModule (k := k) hP z)
    infer_instance
  have hP₀ : Projective P.X₂ := by
    change Projective
      (T.contravariantRepresentableFiniteModule (k := k) hP z)
    infer_instance
  letI : Projective P.X₁ := hP₁
  letI : Projective P.X₂ := hP₀
  exact hPshort.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- At a nonprojective vertex, the standard-form mesh complex is a
length-two projective resolution of the corresponding finite mesh simple. -/
theorem standardFormSimpleFiniteModule_hasProjectiveDimensionLE_two_of_nonprojective
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    HasProjectiveDimensionLE
      (S.standardFormRightMeshData.simpleFiniteModule (k := k) z.1) 2 := by
  let T := S.standardFormRightMeshData
  let P := T.simplePositiveFiniteShortComplex (k := k) hP z.1
  let R := T.simpleTranslationFiniteShortComplex (k := k) hP z
  have hRPzero : R.f ≫ P.f = 0 := by
    change R.f ≫ R.g = 0
    exact R.zero
  let RP : ShortComplex (FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
    ShortComplex.mk R.f P.f hRPzero
  let C₁ : ShortComplex (FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
    ShortComplex.mk R.f (factorThruImage P.f)
      (comp_factorThruImage_eq_zero hRPzero)
  have hR : R.Exact :=
    T.simpleTranslationFiniteShortComplex_exact (k := k) hP z
  have hRP : RP.Exact := by
    change R.Exact
    exact hR
  have hC₁ : C₁.ShortExact := by
    letI : Mono C₁.f := by
      dsimp [C₁, R]
      exact S.standardFormTranslationMapFinite_mono hP z
    letI : Epi C₁.g := by
      dsimp [C₁]
      infer_instance
    refine { exact := ?_ }
    dsimp [C₁]
    exact ShortComplex.exact_of_g_is_cokernel _ hRP.isColimitImage
  have hP₂ : Projective C₁.X₁ := by
    change Projective
      (T.contravariantRepresentableFiniteModule (k := k) hP (T.tau z))
    infer_instance
  have hP₁ : Projective C₁.X₂ := by
    change Projective (T.incomingCoefficientFiniteModule (k := k) hP z.1)
    infer_instance
  have hImage : HasProjectiveDimensionLE C₁.X₃ 1 := by
    letI : Projective C₁.X₁ := hP₂
    letI : Projective C₁.X₂ := hP₁
    exact hC₁.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance
  let C₀ : ShortComplex (FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
    ShortComplex.mk (Abelian.image.ι P.f) P.g
      (Abelian.image_ι_comp_eq_zero P.zero)
  have hPexact : P.Exact :=
    T.simplePositiveFiniteShortComplex_exact (k := k) hP z.1
  have hC₀ : C₀.ShortExact := by
    letI : Mono C₀.f := by
      dsimp [C₀]
      infer_instance
    letI : Epi C₀.g := by
      change Epi (T.simpleProjectionFinite (k := k) hP z.1)
      infer_instance
    refine { exact := ?_ }
    dsimp [C₀]
    exact ShortComplex.exact_of_f_is_kernel _ hPexact.isLimitImage
  have hP₀ : Projective C₀.X₂ := by
    change Projective
      (T.contravariantRepresentableFiniteModule (k := k) hP z.1)
    infer_instance
  letI : HasProjectiveDimensionLE C₀.X₁ 1 := by
    letI : HasProjectiveDimensionLE (image P.f) 1 := by
      change HasProjectiveDimensionLE C₁.X₃ 1
      exact hImage
    change HasProjectiveDimensionLE (Abelian.image P.f) 1
    exact hasProjectiveDimensionLT_of_iso
      (Abelian.imageIsoImage P.f).symm 2
  letI : Projective C₀.X₂ := hP₀
  exact hC₀.hasProjectiveDimensionLT_X₃ 2 inferInstance inferInstance

/-- Every standard-form finite mesh simple has projective dimension at most
two, with the projective boundary case bounded by one. -/
theorem standardFormSimpleFiniteModule_hasProjectiveDimensionLE_two
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : Fin S.n) :
    HasProjectiveDimensionLE
      (S.standardFormRightMeshData.simpleFiniteModule (k := k) z) 2 := by
  by_cases hz : z ∈ S.standardFormProjectiveSet
  · letI : HasProjectiveDimensionLE
        (S.standardFormRightMeshData.simpleFiniteModule (k := k) z) 1 :=
      S.standardFormProjectiveSimpleFiniteModule_hasProjectiveDimensionLE_one
        hP z hz
    exact hasProjectiveDimensionLT_of_ge
      (S.standardFormRightMeshData.simpleFiniteModule (k := k) z)
      2 3 (by omega)
  · exact S.standardFormSimpleFiniteModule_hasProjectiveDimensionLE_two_of_nonprojective
      hP ⟨z, hz⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
