import MagnitudeConjecture.Algebra.RightModuleStandardFormSimpleResolution
import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGenerator
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableInjectiveBoundary
import MagnitudeConjecture.CategoryTheory.MeshSimpleClassification
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.RingTheory.FiniteLength

/-!
# Global dimension of the standard-form mesh module category

The standard-form mesh simples exhaust the simple finite modules.  Their
mesh resolutions therefore give a projective-dimension bound of two for all
simple objects, and finite length propagates that bound to every finite
module.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormGlobalDimensionQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormGlobalDimensionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- Every contravariant representable of the full standard-form mesh
category is finite-dimensional. -/
theorem standardFormFiniteContravariantRepresentables :
    S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k) := by
  let T := S.standardFormRightMeshData
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k
        (MeshCategory.obj (k := k) T Y.unop ⟶
          MeshCategory.obj (k := k) T X.unop) :=
      S.standardFormMeshHomFinite
        (MeshCategory.obj (k := k) T Y.unop)
        (MeshCategory.obj (k := k) T X.unop)
    letI : FiniteDimensional k (Y.unop ⟶ X.unop) :=
      FiniteDimensional.of_injective
        InducedCategory.homLinearEquiv.toLinearMap
        InducedCategory.homLinearEquiv.injective
    exact FiniteDimensional.of_injective
      (oppositeHomLinearEquiv X Y).toLinearMap
      (oppositeHomLinearEquiv X Y).injective
  · exact Set.toFinite _

/-- Every vertex of the full standard-form mesh category has local
endomorphism ring. -/
theorem standardFormVertexCategoryEndLocal
    (X : S.standardFormRightMeshData.VertexCategory (k := k)) :
    IsLocalRing (End X) := by
  let T := S.standardFormRightMeshData
  let eLinear : End X ≃ₗ[k]
      End (MeshCategory.obj (k := k) T X) :=
    InducedCategory.homLinearEquiv
  letI : FiniteDimensional k
      (End (MeshCategory.obj (k := k) T X)) :=
    S.standardFormMeshHomFinite
      (MeshCategory.obj (k := k) T X)
      (MeshCategory.obj (k := k) T X)
  letI : FiniteDimensional k (End X) :=
    FiniteDimensional.of_injective eLinear.toLinearMap eLinear.injective
  letI : IsLocalRing
      (End (MeshCategory.obj (k := k) T X)) :=
    MeshCategory.end_isLocalRing_of_finiteDimensional T X
  let e : End X ≃+* End (MeshCategory.obj (k := k) T X) :=
    { InducedCategory.endEquiv with
      map_add' := fun _ _ ↦ rfl }
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm e.symm

/-- Local vertex endomorphism rings pass to the opposite vertex category
used for contravariant finite modules. -/
theorem standardFormOppositeVertexCategoryEndLocal
    (X : S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) :
    IsLocalRing (End X) :=
  opposite_end_isLocalRing
    (fun Y ↦ S.standardFormVertexCategoryEndLocal Y) X

set_option maxHeartbeats 800000 in
/-- Every simple object of the standard-form finite mesh-module category is
one of the vertex mesh simples. -/
theorem exists_iso_standardFormSimpleFiniteModule_of_simple
    (M : FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) k)
    [Simple M] :
    ∃ z : Fin S.n, Nonempty
      (M ≅ S.standardFormRightMeshData.simpleFiniteModule (k := k) z) := by
  let T := S.standardFormRightMeshData
  change ∃ z : Fin S.n, Nonempty
    (M ≅ T.simpleFiniteModule (k := k) z)
  have hP : T.FiniteContravariantRepresentables (k := k) := by
    change S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k)
    exact standardFormFiniteContravariantRepresentables (k := k) S
  have hlocal : ∀ X : T.VertexCategory (k := k)ᵒᵖ,
      IsLocalRing (End X) := by
    intro X
    exact standardFormOppositeVertexCategoryEndLocal (k := k) S X
  classical
  have hex : ∃ (z : Fin S.n)
      (x : M.obj.obj.obj (Opposite.op z)), x ≠ 0 := by
    by_contra h
    push Not at h
    apply CategoryTheory.id_nonzero M
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    rcases X with ⟨z⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = 0
    exact h z x
  obtain ⟨z, x, hx⟩ := hex
  let X : T.VertexCategory (k := k)ᵒᵖ := Opposite.op z
  let P := finiteDimensionalLinearCoyoneda
    (C := T.VertexCategory (k := k)ᵒᵖ) (k := k) X (hP X)
  let r := finiteDimensionalLinearCoyonedaRadicalInclusion
    (C := T.VertexCategory (k := k)ᵒᵖ) (k := k) X (hP X)
  let J := (IsFiniteDimensionalModule
    (C := T.VertexCategory (k := k)ᵒᵖ) k).ι
  let pLinear : J.obj P ⟶ J.obj M :=
    linearCoyonedaHom M.obj X x
  let p : P ⟶ M := J.preimage pLinear
  have hp : p ≠ 0 := by
    intro hzero
    apply hx
    have hmap : J.map p = pLinear := by
      dsimp only [p]
      exact J.map_preimage pLinear
    have hz := congrArg
      (fun f : P ⟶ M ↦ (J.map f).hom.app X (𝟙 X)) hzero
    rw [hmap, J.map_zero] at hz
    change (linearCoyonedaHom M.obj X x).hom.app X (𝟙 X) = 0 at hz
    rw [linearCoyonedaHom_app_id] at hz
    exact hz
  letI : Projective P :=
    finiteDimensionalLinearCoyoneda_projective X (hP X)
  letI : IsLocalRing (End P) :=
    finiteDimensionalLinearCoyoneda_end_isLocalRing hP hlocal X
  have hr : IsRightAlmostSplit r :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP hlocal X
  let eM : cokernel r ≅ M :=
    MagnitudeConjecture.CategoryTheory.cokernelIsoSimpleTarget_of_mono_rightAlmostSplit_projective
      r hr p hp
  let q := T.simpleStandardAugmentation (k := k) hP z
  have hq : q ≠ 0 := by
    intro hzero
    apply CategoryTheory.id_nonzero (T.simpleFiniteModule (k := k) z)
    apply (cancel_epi q).1
    rw [Category.comp_id, hzero, zero_comp]
  let eS : cokernel r ≅ T.simpleFiniteModule (k := k) z :=
    MagnitudeConjecture.CategoryTheory.cokernelIsoSimpleTarget_of_mono_rightAlmostSplit_projective
      r hr q hq
  exact ⟨z, ⟨eM.symm ≪≫ eS⟩⟩

set_option maxHeartbeats 800000 in
/-- Every simple object of the standard-form finite mesh-module category
has projective dimension at most two. -/
theorem standardFormSimpleObject_hasProjectiveDimensionLE_two
    (M : FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) k)
    [Simple M] :
    HasProjectiveDimensionLE M 2 := by
  let T := S.standardFormRightMeshData
  let hP := S.standardFormFiniteContravariantRepresentables
  obtain ⟨z, ⟨e⟩⟩ :=
    S.exists_iso_standardFormSimpleFiniteModule_of_simple M
  letI : HasProjectiveDimensionLE
      (T.simpleFiniteModule (k := k) z) 2 :=
    S.standardFormSimpleFiniteModule_hasProjectiveDimensionLE_two hP z
  exact hasProjectiveDimensionLT_of_iso e.symm 3

/-- Every finite-dimensional module on the standard-form mesh category has
projective dimension at most two. -/
theorem standardFormFiniteModule_hasProjectiveDimensionLE_two
    (M : FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) k) :
    HasProjectiveDimensionLE M 2 := by
  let T := S.standardFormRightMeshData
  let hP := S.standardFormFiniteContravariantRepresentables
  let E := finiteCategoryProjectiveGenerator.moduleEquivalence hP
  let R := (finiteCategoryProjectiveGenerator.algebra hP)ᵐᵒᵖ
  let N := E.functor.obj M
  letI : FiniteDimensional k
      (finiteCategoryProjectiveGenerator.algebra hP) :=
    finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : FiniteDimensional k R := by infer_instance
  letI : IsNoetherianRing R := IsNoetherianRing.of_finite k R
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  have hNfinite : IsFiniteLength R N :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨inferInstance, inferInstance⟩
  have hInvAll : ∀ (V : Type u) [AddCommGroup V] [Module R V]
      [Module.Finite R V], IsFiniteLength R V →
        HasProjectiveDimensionLE
          (E.inverse.obj (FGModuleCat.of R V)) 2 := by
    intro V _ _ hfinite hVfinite
    induction hVfinite generalizing hfinite with
    | @of_subsingleton V _ _ hsub =>
        let Vfg : FGModuleCat.{u} R := FGModuleCat.of R V
        have hzero : IsZero Vfg := by
          rw [IsZero.iff_id_eq_zero]
          apply FGModuleCat.hom_ext
          ext x
          exact Subsingleton.elim _ _
        have hzeroInv : IsZero (E.inverse.obj Vfg) :=
          E.inverse.map_isZero hzero
        letI : HasProjectiveDimensionLT (E.inverse.obj Vfg) 0 :=
          hzeroInv.hasProjectiveDimensionLT_zero
        exact hasProjectiveDimensionLT_of_ge
          (E.inverse.obj Vfg) 0 3 (by omega)
    | @of_simple_quotient V _ _ L _ hL ih =>
        have hVfinite : IsFiniteLength R V :=
          .of_simple_quotient hL
        letI : IsNoetherian R V :=
          (isFiniteLength_iff_isNoetherian_isArtinian.mp hVfinite).1
        letI : Module.Finite R V := inferInstance
        letI : IsNoetherian R L :=
          (isFiniteLength_iff_isNoetherian_isArtinian.mp hL).1
        letI : Module.Finite R L := inferInstance
        let Vfg : FGModuleCat.{u} R := FGModuleCat.of R V
        let Lfg : FGModuleCat.{u} R := FGModuleCat.of R L
        let Qfg : FGModuleCat.{u} R := FGModuleCat.of R (V ⧸ L)
        let i : Lfg ⟶ Vfg := FGModuleCat.ofHom L.subtype
        let q : Vfg ⟶ Qfg := FGModuleCat.ofHom L.mkQ
        have hiq : i ≫ q = 0 := by
          apply FGModuleCat.hom_ext
          ext x
          change L.mkQ (L.subtype x) = 0
          rw [Submodule.mkQ_apply]
          rw [Submodule.Quotient.mk_eq_zero]
          exact x.property
        let Cfg : ShortComplex (FGModuleCat.{u} R) :=
          ShortComplex.mk i q hiq
        have hCfg : Cfg.ShortExact := by
          let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
          apply ShortExact.reflects_shortExact_of_faithful U
          let Cmod : ShortComplex (ModuleCat.{u} R) :=
            ModuleCat.shortComplexOfCompEqZero L.subtype L.mkQ (by
              ext x
              simp)
          have hCmod : Cmod.ShortExact := by
            apply ModuleCat.shortComplex_shortExact
            · exact LinearMap.exact_subtype_mkQ L
            · exact L.injective_subtype
            · exact L.mkQ_surjective
          change Cmod.ShortExact
          exact hCmod
        have hMapped : (Cfg.map E.inverse).ShortExact :=
          hCfg.map_of_exact E.inverse
        have hleft : HasProjectiveDimensionLE
            (Cfg.map E.inverse).X₁ 2 := by
          change HasProjectiveDimensionLE (E.inverse.obj Lfg) 2
          exact ih
        haveI : IsSimpleModule R (V ⧸ L) := inferInstance
        have hQsimple : Simple Qfg := by
          let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
          haveI : Simple (U.obj Qfg) := by
            change Simple (ModuleCat.of R (V ⧸ L))
            infer_instance
          exact Functor.simple_of_simple_obj U Qfg
        letI : Simple Qfg := hQsimple
        haveI : Simple (E.inverse.obj Qfg) :=
          CategoryTheory.simple_obj E.inverse Qfg
        have hright : HasProjectiveDimensionLE
            (Cfg.map E.inverse).X₃ 2 := by
          change HasProjectiveDimensionLE (E.inverse.obj Qfg) 2
          exact S.standardFormSimpleObject_hasProjectiveDimensionLE_two
            (E.inverse.obj Qfg)
        exact hMapped.hasProjectiveDimensionLT_X₂ 3 hleft hright
  have hInv : HasProjectiveDimensionLE (E.inverse.obj N) 2 := by
    exact hInvAll N hNfinite
  letI : HasProjectiveDimensionLE
      ((E.functor ⋙ E.inverse).obj M) 2 := by
    change HasProjectiveDimensionLE (E.inverse.obj N) 2
    exact hInv
  exact hasProjectiveDimensionLT_of_iso (E.unitIso.app M).symm 3

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
