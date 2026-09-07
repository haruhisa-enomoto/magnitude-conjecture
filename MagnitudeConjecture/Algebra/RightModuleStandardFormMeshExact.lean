import MagnitudeConjecture.Algebra.RightModuleStandardFormSimpleResolution

/-!
# Downstairs mesh exactness in standard form

Universal-cover mesh exactness descends to the standard-form mesh category.
This is the first chain-level stage in the proof of mesh Ext vanishing.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u w

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshExtVanishingQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshExtVanishingArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

set_option backward.isDefEq.respectTransparency false in
/-- Projection sends a polarized partner upstairs to the polarized partner
of the projected incoming arrow downstairs. -/
@[simp]
theorem meshProjection_map_standardFormUniversalPairedIncomingHom
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (d : Quiver.Star W.1) :
    (meshProjection S x₀).map
        (S.standardFormUniversalPairedIncomingHom x₀ W d) =
      S.standardFormRightMeshData.incomingArrowHom (k := k)
        (⟨S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W),
          S.standardFormRightMeshData.arrowEquiv
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)
            (projectedIncomingArrow S x₀ W.1 d).1
            (projectedIncomingArrow S x₀ W.1 d).2⟩ :
          MeshCategory.RightMeshData.IncomingArrow
            (projectedIncomingArrow S x₀ W.1 d).1) := by
  unfold standardFormUniversalPairedIncomingHom
  rw [meshProjection_map_incomingArrowHom]
  rfl

end UniversalCover

set_option backward.isDefEq.respectTransparency false in
/-- Downstairs Hom exactness at the middle term of the nonprojective
mesh-simple resolution.  A relation among the polarized partners is obtained
by postcomposing all incoming arrows with one morphism. -/
theorem standardFormMesh_nonprojective_outgoing_exact
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (c : ∀ a : MeshCategory.RightMeshData.IncomingArrow z.1,
      MeshCategory.obj (k := k) S.standardFormRightMeshData a.1 ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData x)
    (hc : (∑ a : MeshCategory.RightMeshData.IncomingArrow z.1,
      S.standardFormRightMeshData.incomingArrowHom (k := k)
          (⟨S.standardFormTau z,
            S.standardFormRightMeshData.arrowEquiv z a.1 a.2⟩ :
            MeshCategory.RightMeshData.IncomingArrow a.1) ≫ c a) = 0) :
    ∃ t : MeshCategory.obj (k := k) S.standardFormRightMeshData z.1 ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData x,
      ∀ a, c a =
        S.standardFormRightMeshData.incomingArrowHom (k := k) a ≫ t := by
  classical
  let T := S.standardFormRightMeshData
  let W₀ := MeshCategory.RightMeshData.UniversalCover.baseVertex T z.1
  have hW₀ : W₀ ∉
      MeshCategory.RightMeshData.UniversalCover.projectiveSet T z.1 := by
    change z.1 ∉ S.standardFormProjectiveSet
    exact z.2
  let W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex T z.1 //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet T z.1} :=
    ⟨W₀, hW₀⟩
  let e : Quiver.Star W.1 ≃
      MeshCategory.RightMeshData.IncomingArrow z.1 :=
    Equiv.ofBijective
      (fun d ↦ UniversalCover.projectedIncomingArrow S z.1 W.1 d)
      (by
        change Function.Bijective
          ((MeshCategory.RightMeshData.UniversalCover.projection T z.1).star W.1)
        exact MeshCategory.RightMeshData.UniversalCover.projection_star_bijective
          T z.1 W.1)
  let cF : ∀ d : Quiver.Star W.1, S.fgObj d.1.1 ⟶ S.fgObj x :=
    fun d ↦ (UniversalCover.meshHomLinearEquivFGIndec
      S z.1 d.1 x (c (e d))).hom
  have hcDown : (∑ d : Quiver.Star W.1,
      (UniversalCover.meshProjection S z.1).map
          (S.standardFormUniversalPairedIncomingHom z.1 W d) ≫
        c (e d)) = 0 := by
    let f : MeshCategory.RightMeshData.IncomingArrow z.1 →
        (MeshCategory.obj (k := k) S.standardFormRightMeshData
            (S.standardFormTau z) ⟶
          MeshCategory.obj (k := k) S.standardFormRightMeshData x) := fun a ↦
      S.standardFormRightMeshData.incomingArrowHom (k := k)
          (⟨S.standardFormTau z,
            S.standardFormRightMeshData.arrowEquiv z a.1 a.2⟩ :
            MeshCategory.RightMeshData.IncomingArrow a.1) ≫ c a
    calc
      (∑ d : Quiver.Star W.1,
          (UniversalCover.meshProjection S z.1).map
              (S.standardFormUniversalPairedIncomingHom z.1 W d) ≫
            c (e d)) = ∑ d : Quiver.Star W.1, f (e d) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [UniversalCover.meshProjection_map_standardFormUniversalPairedIncomingHom]
        rfl
      _ = ∑ a : MeshCategory.RightMeshData.IncomingArrow z.1, f a :=
        by simpa only using e.sum_comp f
      _ = 0 := hc
  have hcFCat : (∑ d : Quiver.Star W.1,
      (UniversalCover.realization S z.1).map
          (S.standardFormUniversalPairedIncomingHom z.1 W d) ≫
        UniversalCover.meshHomLinearEquivFGIndec S z.1 d.1 x (c (e d))) = 0 := by
    let Wτ := MeshCategory.RightMeshData.UniversalCover.tau T z.1 W
    let Eτ := UniversalCover.meshHomLinearEquivFGIndec S z.1 Wτ x
    have hmap := congrArg Eτ hcDown
    rw [map_zero, map_sum] at hmap
    calc
      (∑ d : Quiver.Star W.1,
          (UniversalCover.realization S z.1).map
              (S.standardFormUniversalPairedIncomingHom z.1 W d) ≫
            UniversalCover.meshHomLinearEquivFGIndec S z.1 d.1 x (c (e d))) =
          ∑ d : Quiver.Star W.1,
            Eτ ((UniversalCover.meshProjection S z.1).map
                (S.standardFormUniversalPairedIncomingHom z.1 W d) ≫ c (e d)) := by
        apply Finset.sum_congr rfl
        intro d _
        exact (UniversalCover.meshHomLinearEquivFGIndec_precomp
          S z.1 Wτ d.1 x
          (S.standardFormUniversalPairedIncomingHom z.1 W d) (c (e d))).symm
      _ = 0 := hmap
  have hcF : (∑ d : Quiver.Star W.1,
      S.standardFormUniversalMappedPairedIncomingHom z.1 W d ≫ cF d) = 0 := by
    have h := congrArg (InducedCategory.homLinearEquiv (R := k)) hcFCat
    change (InducedCategory.homLinearEquiv (R := k))
        (∑ d : Quiver.Star W.1,
          (UniversalCover.realization S z.1).map
              (S.standardFormUniversalPairedIncomingHom z.1 W d) ≫
            UniversalCover.meshHomLinearEquivFGIndec S z.1 d.1 x (c (e d))) =
      (InducedCategory.homLinearEquiv (R := k)) 0 at h
    rw [map_sum, map_zero] at h
    simpa only [map_sum, map_zero, InducedCategory.homLinearEquiv_apply,
      InducedCategory.comp_hom, cF,
      standardFormUniversalMappedPairedIncomingHom,
      S.standardFormUniversalIndecMeshFunctor_obj_meshObj] using h
  obtain ⟨tF, htF⟩ :=
    S.standardFormUniversal_nonprojective_outgoingStar_exact
      z.1 x W cF hcF
  let tC : (show S.FGIndecCategory from z.1) ⟶
      (show S.FGIndecCategory from x) := InducedCategory.homMk tF
  let EW := UniversalCover.meshHomLinearEquivFGIndec S z.1 W.1 x
  let t : MeshCategory.obj (k := k) T z.1 ⟶
      MeshCategory.obj (k := k) T x := EW.symm tC
  refine ⟨t, fun a ↦ ?_⟩
  obtain ⟨d, rfl⟩ := e.surjective a
  let Ed := UniversalCover.meshHomLinearEquivFGIndec S z.1 d.1 x
  apply Ed.injective
  calc
    Ed (c (e d)) = InducedCategory.homMk (cF d) := by
      apply InducedCategory.hom_ext
      rfl
    _ = InducedCategory.homMk
        (S.standardFormUniversalMappedIncomingHom z.1 W.1 d ≫ tF) := by
      rw [htF d]
    _ = (UniversalCover.realization S z.1).map
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData T z.1).incomingArrowHom
            (k := k) d) ≫ tC := by
      apply InducedCategory.hom_ext
      change S.standardFormUniversalMappedIncomingHom z.1 W.1 d ≫ tF =
        ((UniversalCover.realization S z.1).map
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData T z.1).incomingArrowHom
            (k := k) d) ≫ tC).hom
      rw [S.standardFormUniversalMappedIncomingHom_eq_normalized]
      change S.standardFormUniversalNormalizedArrowMap z.1 d.2 ≫ tF =
        ((UniversalCover.realization S z.1).map
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData T z.1).incomingArrowHom
            (k := k) d)).hom ≫ tF
      rw [S.standardFormUniversalIndecMeshFunctor_map_incomingArrowHom]
    _ = Ed ((UniversalCover.meshProjection S z.1).map
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData T z.1).incomingArrowHom
            (k := k) d) ≫ t) := by
      rw [UniversalCover.meshHomLinearEquivFGIndec_precomp]
      dsimp only [t, EW]
      rw [LinearEquiv.apply_symm_apply]
    _ = Ed (T.incomingArrowHom (k := k) (e d) ≫ t) := by
      rw [UniversalCover.meshProjection_map_incomingArrowHom]
      rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
