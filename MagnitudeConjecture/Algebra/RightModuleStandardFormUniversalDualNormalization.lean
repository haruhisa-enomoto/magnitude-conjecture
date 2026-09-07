import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalNormalization

/-!
# Dual normalization on the standard-form universal cover

The positive-height construction normalizes realized sinks.  This file
implements the dual induction on arrows whose module-theoretic source has
nonpositive Bongartz--Gabriel height.  It normalizes realized sources while
retaining their minimal left almost-split invariant.
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

local instance standardFormUniversalDualNormalizationQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

/-- A lifted standard-form vertex whose represented module is
noninjective. -/
abbrev StandardFormUniversalNoninjectiveVertex (x₀ : Fin S.n) :=
  {Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀ //
    ¬ Injective (S.fgObj Z.1)}

/-- Polarization commutes with transport of its nonprojective mesh
endpoint. -/
theorem standardFormRightMeshData_arrowEquiv_cast
    {z z' : {z : Fin S.n // z ∉ S.standardFormRightMeshData.projective}}
    (h : z = z') (y : Fin S.n) (b : S.StandardFormArrow z.1 y) :
    Quiver.Hom.cast rfl (congrArg S.standardFormRightMeshData.tau h)
        ((S.standardFormRightMeshData.arrowEquiv z y) b) =
      (S.standardFormRightMeshData.arrowEquiv z' y)
        (Quiver.Hom.cast (congrArg Subtype.val h) rfl b) := by
  subst z'
  rfl

/-- The inverse polarization also commutes with transport of its
nonprojective mesh endpoint. -/
theorem standardFormRightMeshData_arrowEquiv_symm_cast
    {z z' : {z : Fin S.n // z ∉ S.standardFormRightMeshData.projective}}
    (h : z = z') (y : Fin S.n)
    (a : S.StandardFormArrow y (S.standardFormRightMeshData.tau z)) :
    Quiver.Hom.cast (congrArg Subtype.val h) rfl
        ((S.standardFormRightMeshData.arrowEquiv z y).symm a) =
      (S.standardFormRightMeshData.arrowEquiv z' y).symm
        (Quiver.Hom.cast rfl
          (congrArg S.standardFormRightMeshData.tau h) a) := by
  subst z'
  rfl

/-- Extract a component from a replacement source at one downstairs
noninjective standard-form vertex. -/
def standardFormSourceArrowMap
    (z : {z : Fin S.n // z ∉ S.standardFormRightMeshData.projective})
    (g : S.finiteTauCategoryData.obj
        (S.standardFormRightMeshData.tau z) ⟶
      (S.finiteTauCategoryData.rightMesh
        (S.finiteTauCategoryData.obj z.1)).X₂)
    {y : Fin S.n}
    (a : S.StandardFormArrow y (S.standardFormRightMeshData.tau z)) :
    S.finiteTauCategoryData.obj (S.standardFormRightMeshData.tau z) ⟶
      S.finiteTauCategoryData.obj y := by
  let b : S.StandardFormArrow z.1 y :=
    (S.standardFormRightMeshData.arrowEquiv z y).symm a
  let j := S.standardFormArrowOccurrenceEquiv z.1 y b
  exact g ≫ FiniteTauMatrix.rightMiddleProjection
      S.finiteTauCategoryData z.1 j.1 ≫
    eqToHom (congrArg S.finiteTauCategoryData.obj j.2)

set_option backward.isDefEq.respectTransparency false in
/-- On a polarized displayed occurrence, downstairs source-component
extraction is literal postcomposition with the middle projection. -/
@[simp]
theorem standardFormSourceArrowMap_paired
    (z : {z : Fin S.n // z ∉ S.standardFormRightMeshData.projective})
    (g : S.finiteTauCategoryData.obj
        (S.standardFormRightMeshData.tau z) ⟶
      (S.finiteTauCategoryData.rightMesh
        (S.finiteTauCategoryData.obj z.1)).X₂)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1)) :
    S.standardFormSourceArrowMap z g
        ((S.standardFormRightMeshData.arrowEquiv z
          (S.standardFormMiddleIndexEquiv z.1 i).1)
            (S.standardFormMiddleIndexEquiv z.1 i).2) =
      g ≫ FiniteTauMatrix.rightMiddleProjection
        S.finiteTauCategoryData z.1 i ≫
          eqToHom (congrArg S.finiteTauCategoryData.obj
            (S.standardFormMiddleIndexEquiv_fst z.1 i).symm) := by
  let b := (S.standardFormMiddleIndexEquiv z.1 i).2
  let a := (S.standardFormRightMeshData.arrowEquiv z
    (S.standardFormMiddleIndexEquiv z.1 i).1) b
  let b' := (S.standardFormRightMeshData.arrowEquiv z
    (S.standardFormMiddleIndexEquiv z.1 i).1).symm a
  have hb : b' = b :=
    (S.standardFormRightMeshData.arrowEquiv z
      (S.standardFormMiddleIndexEquiv z.1 i).1).symm_apply_apply b
  let j := S.standardFormArrowOccurrenceEquiv z.1
    (S.standardFormMiddleIndexEquiv z.1 i).1
      (S.standardFormMiddleIndexEquiv z.1 i).2
  let j' := S.standardFormArrowOccurrenceEquiv z.1
    (S.standardFormMiddleIndexEquiv z.1 i).1 b'
  have hj' : j' = j := congrArg
    (S.standardFormArrowOccurrenceEquiv z.1
      (S.standardFormMiddleIndexEquiv z.1 i).1) hb
  have hj : j = ⟨i, S.standardFormMiddleIndexEquiv_fst z.1 i⟩ :=
    S.standardFormArrowOccurrenceEquiv_middleIndex z.1 i
  unfold standardFormSourceArrowMap
  dsimp only
  change g ≫ FiniteTauMatrix.rightMiddleProjection
      S.finiteTauCategoryData z.1 j'.1 ≫
        eqToHom (congrArg S.finiteTauCategoryData.obj j'.2) = _
  rw [hj', hj]

/-- Extract from a replacement mesh source the component represented by one
arrow ending at the translated vertex. -/
def standardFormUniversalSourceArrowMap (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (g : S.fgObj (S.standardFormTau
        (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
          S.standardFormRightMeshData x₀ W)) ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂)
    {Y : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (a : Y ⟶ MeshCategory.RightMeshData.UniversalCover.tau
      S.standardFormRightMeshData x₀ W) :
    S.standardFormUniversalObj x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) ⟶
      S.standardFormUniversalObj x₀ Y := by
  let z := MeshCategory.RightMeshData.UniversalCover.baseNonprojective
    S.standardFormRightMeshData x₀ W
  exact S.standardFormSourceArrowMap z g a.1

/-- Component extraction recovers the indicated component on each explicit
polarized middle arrow. -/
@[simp]
theorem standardFormUniversalSourceArrowMap_pairedMiddleArrow
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (g : S.fgObj (S.standardFormTau
        (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
          S.standardFormRightMeshData x₀ W)) ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1)) :
    S.standardFormUniversalSourceArrowMap x₀ W g
        (S.standardFormUniversalPairedMiddleArrow x₀ W i) =
      g ≫ FiniteTauMatrix.rightMiddleProjection
        S.finiteTauCategoryData
          (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
            S.standardFormRightMeshData x₀ W).1 i := by
  change S.standardFormSourceArrowMap
      (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
        S.standardFormRightMeshData x₀ W) g
          (S.standardFormUniversalPairedMiddleArrow x₀ W i).1 = _
  rw [S.standardFormUniversalPairedMiddleArrow_val]
  exact S.standardFormSourceArrowMap_paired _ g i

/-- Source-component extraction is invariant under simultaneous transport of
the lifted mesh endpoint and its outgoing arrow. -/
theorem standardFormUniversalSourceArrowMap_transport
    (x₀ : Fin S.n) (m : ℤ)
    (g : ∀ W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀},
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ W) = m →
        (S.fgObj (S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)) ⟶
          (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂))
    {Y : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (W' W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (h : W' = W) (b' : W'.1 ⟶ Y) (b : W.1 ⟶ Y)
    (hb : Quiver.Hom.cast (congrArg Subtype.val h) rfl b' = b)
    (hW' : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W') = m)
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = m) :
    eqToHom (congrArg (S.standardFormUniversalObj x₀)
        (congrArg (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀) h).symm) ≫
      S.standardFormUniversalSourceArrowMap x₀ W' (g W' hW')
        (MeshCategory.RightMeshData.UniversalCover.pairedArrow
          S.standardFormRightMeshData x₀ W' Y b') =
      S.standardFormUniversalSourceArrowMap x₀ W (g W hW)
        (MeshCategory.RightMeshData.UniversalCover.pairedArrow
          S.standardFormRightMeshData x₀ W Y b) := by
  subst W'
  have hb₀ : b' = b := by
    exact eq_of_heq ((Quiver.Hom.cast_eq_iff_heq _ _ b' b).1 hb)
  subst b'
  rfl

/-- For an arrow whose represented module source is noninjective, recover
the downstairs endpoint of the right mesh that produces it by polarization. -/
def standardFormUniversalArrowSourceBase (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (_a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    {z : Fin S.n // z ∉ S.standardFormRightMeshData.projective} :=
  ⟨((S.rightTranslationEquiv).symm ⟨Z.1, hZ⟩).1,
    ((S.rightTranslationEquiv).symm ⟨Z.1, hZ⟩).2⟩

/-- The recovered downstairs mesh endpoint translates to the arrow target's
base label. -/
theorem standardFormUniversalArrowSourceBase_tau (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    S.standardFormRightMeshData.tau
        (S.standardFormUniversalArrowSourceBase x₀ a hZ) = Z.1 := by
  exact congrArg Subtype.val
    (S.rightTranslationEquiv.apply_symm_apply ⟨Z.1, hZ⟩)

/-- The downstairs polarized partner of an arrow ending at a noninjective
lifted vertex. -/
def standardFormUniversalArrowSourceBasePartner (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    S.StandardFormArrow
      (S.standardFormUniversalArrowSourceBase x₀ a hZ).1 Y.1 :=
  (S.standardFormRightMeshData.arrowEquiv
    (S.standardFormUniversalArrowSourceBase x₀ a hZ) Y.1).symm
      (Quiver.Hom.cast rfl
        (S.standardFormUniversalArrowSourceBase_tau x₀ a hZ).symm a.1)

/-- Lift the recovered downstairs polarized partner into the costar of the
arrow's source vertex.  This determines the unique lifted mesh containing
the arrow. -/
def standardFormUniversalArrowSourceCostar (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) : Quiver.Costar Y :=
  (Equiv.ofBijective
    ((MeshCategory.RightMeshData.UniversalCover.projection
      S.standardFormRightMeshData x₀).costar Y)
    (MeshCategory.RightMeshData.UniversalCover.projection_costar_bijective
      S.standardFormRightMeshData x₀ Y)).symm
        ⟨(S.standardFormUniversalArrowSourceBase x₀ a hZ).1,
          S.standardFormUniversalArrowSourceBasePartner x₀ a hZ⟩

/-- Projecting the recovered costar lift returns its defining downstairs
polarized partner. -/
theorem standardFormUniversalArrowSourceCostar_projection (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    (MeshCategory.RightMeshData.UniversalCover.projection
      S.standardFormRightMeshData x₀).costar Y
        (S.standardFormUniversalArrowSourceCostar x₀ a hZ) =
      ⟨(S.standardFormUniversalArrowSourceBase x₀ a hZ).1,
        S.standardFormUniversalArrowSourceBasePartner x₀ a hZ⟩ := by
  exact (Equiv.ofBijective
    ((MeshCategory.RightMeshData.UniversalCover.projection
      S.standardFormRightMeshData x₀).costar Y)
    (MeshCategory.RightMeshData.UniversalCover.projection_costar_bijective
      S.standardFormRightMeshData x₀ Y)).apply_symm_apply _

/-- The nonprojective lifted mesh endpoint recovered from an arrow ending at
a noninjective vertex. -/
def standardFormUniversalArrowSourceMesh (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀} := by
  let c := S.standardFormUniversalArrowSourceCostar x₀ a hZ
  have hc : c.1.1 =
      (S.standardFormUniversalArrowSourceBase x₀ a hZ).1 :=
    congrArg Sigma.fst
      (S.standardFormUniversalArrowSourceCostar_projection x₀ a hZ)
  exact ⟨c.1, by
    change c.1.1 ∉ S.standardFormRightMeshData.projective
    rw [hc]
    exact (S.standardFormUniversalArrowSourceBase x₀ a hZ).2⟩

/-- The lifted polarized partner from the recovered mesh endpoint to the
original arrow's source vertex. -/
def standardFormUniversalArrowSourceMeshArrow (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    (S.standardFormUniversalArrowSourceMesh x₀ a hZ).1 ⟶ Y :=
  (S.standardFormUniversalArrowSourceCostar x₀ a hZ).2

/-- The recovered mesh endpoint and arrow are exactly the costar lift
constructed above. -/
theorem standardFormUniversalArrowSourceMesh_costar (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    (⟨(S.standardFormUniversalArrowSourceMesh x₀ a hZ).1,
      S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ⟩ :
        Quiver.Costar Y) =
      S.standardFormUniversalArrowSourceCostar x₀ a hZ :=
  rfl

/-- The recovered lifted mesh endpoint lies over its recovered downstairs
endpoint. -/
theorem standardFormUniversalArrowSourceMesh_base (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    (S.standardFormUniversalArrowSourceMesh x₀ a hZ).1.1 =
      (S.standardFormUniversalArrowSourceBase x₀ a hZ).1 := by
  have hp := S.standardFormUniversalArrowSourceCostar_projection x₀ a hZ
  rw [← S.standardFormUniversalArrowSourceMesh_costar x₀ a hZ] at hp
  exact congrArg Sigma.fst hp

/-- After the base-label transport, the recovered lifted arrow projects to
the recovered downstairs polarized partner. -/
theorem standardFormUniversalArrowSourceMeshArrow_val (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    Quiver.Hom.cast
        (S.standardFormUniversalArrowSourceMesh_base x₀ a hZ) rfl
          (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ).1 =
      S.standardFormUniversalArrowSourceBasePartner x₀ a hZ := by
  have hp := S.standardFormUniversalArrowSourceCostar_projection x₀ a hZ
  rw [← S.standardFormUniversalArrowSourceMesh_costar x₀ a hZ] at hp
  exact (Quiver.Hom.cast_eq_iff_heq
    (S.standardFormUniversalArrowSourceMesh_base x₀ a hZ) rfl
      (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ).1
        (S.standardFormUniversalArrowSourceBasePartner x₀ a hZ)).2
          (Sigma.ext_iff.mp hp).2

/-- Pairing the recovered mesh arrow returns the original universal-cover
arrow, including its target vertex. -/
theorem standardFormUniversalArrowSourceMesh_paired (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z)
    (hZ : ¬ Injective (S.fgObj Z.1)) :
    (⟨MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalArrowSourceMesh x₀ a hZ),
        MeshCategory.RightMeshData.UniversalCover.pairedArrow
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalArrowSourceMesh x₀ a hZ) Y
              (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ)⟩ :
      Quiver.Star Y) = ⟨Z, a⟩ := by
  apply (MeshCategory.RightMeshData.UniversalCover.projection_star_bijective
    S.standardFormRightMeshData x₀ Y).1
  let W := S.standardFormUniversalArrowSourceMesh x₀ a hZ
  let z := S.standardFormUniversalArrowSourceBase x₀ a hZ
  have hs : MeshCategory.RightMeshData.UniversalCover.baseNonprojective
      S.standardFormRightMeshData x₀ W = z := by
    apply Subtype.ext
    exact S.standardFormUniversalArrowSourceMesh_base x₀ a hZ
  let zW := MeshCategory.RightMeshData.UniversalCover.baseNonprojective
    S.standardFormRightMeshData x₀ W
  have htranslate : S.standardFormRightMeshData.tau zW =
      S.standardFormRightMeshData.tau z :=
    congrArg S.standardFormRightMeshData.tau hs
  have htarget : S.standardFormRightMeshData.tau z = Z.1 :=
    S.standardFormUniversalArrowSourceBase_tau x₀ a hZ
  have hbase : S.standardFormRightMeshData.tau zW = Z.1 :=
    htranslate.trans htarget
  apply Sigma.ext hbase
  apply (Quiver.Hom.cast_eq_iff_heq rfl hbase
    (MeshCategory.RightMeshData.UniversalCover.pairedArrow
      S.standardFormRightMeshData x₀ W Y
        (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ)).1 a.1).1
  rw [MeshCategory.RightMeshData.UniversalCover.pairedArrow_val]
  have harrow :=
    S.standardFormUniversalArrowSourceMeshArrow_val x₀ a hZ
  have harrow' : Quiver.Hom.cast (congrArg Subtype.val hs) rfl
      (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ).1 =
        S.standardFormUniversalArrowSourceBasePartner x₀ a hZ := by
    convert harrow using 1
    congr
  have hpolarized := S.standardFormRightMeshData_arrowEquiv_cast
    hs Y.1 (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ).1
  calc
    Quiver.Hom.cast rfl hbase
        ((S.standardFormRightMeshData.arrowEquiv zW Y.1)
          (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ).1) =
      Quiver.Hom.cast rfl htarget
        (Quiver.Hom.cast rfl htranslate
          ((S.standardFormRightMeshData.arrowEquiv zW Y.1)
            (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ).1)) := by
        simp only [Quiver.Hom.cast_cast]
    _ = Quiver.Hom.cast rfl htarget
        ((S.standardFormRightMeshData.arrowEquiv z Y.1)
          (Quiver.Hom.cast (congrArg Subtype.val hs) rfl
            (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ).1)) := by
      rw [hpolarized]
    _ = Quiver.Hom.cast rfl htarget
        ((S.standardFormRightMeshData.arrowEquiv z Y.1)
          (S.standardFormUniversalArrowSourceBasePartner x₀ a hZ)) := by
      rw [harrow']
    _ = Quiver.Hom.cast rfl htarget
        (Quiver.Hom.cast rfl htarget.symm a.1) := by
      rw [show (S.standardFormRightMeshData.arrowEquiv z Y.1)
          (S.standardFormUniversalArrowSourceBasePartner x₀ a hZ) =
        Quiver.Hom.cast rfl htarget.symm a.1 from
          (S.standardFormRightMeshData.arrowEquiv z Y.1).apply_symm_apply _]
    _ = a.1 := by simp

/-- The translated source vertex of every universal mesh represents a
noninjective module. -/
theorem standardFormUniversal_tau_noninjective (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    ¬ Injective (S.fgObj
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ W).1) := by
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨W.1.1, W.2⟩
  exact (S.rightTranslationEquiv z).2

/-- Applied to an explicit polarized mesh arrow, the recovered costar is the
original lifted middle arrow. -/
theorem standardFormUniversalArrowSourceCostar_pairedMiddleArrow
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1)) :
    (⟨(S.standardFormUniversalArrowSourceMesh x₀
          (S.standardFormUniversalPairedMiddleArrow x₀ W i)
            (S.standardFormUniversal_tau_noninjective x₀ W)).1,
        S.standardFormUniversalArrowSourceMeshArrow x₀
          (S.standardFormUniversalPairedMiddleArrow x₀ W i)
            (S.standardFormUniversal_tau_noninjective x₀ W)⟩ :
      Quiver.Costar (S.standardFormUniversalMiddleVertex x₀ W.1 i)) =
      ⟨W.1, S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ := by
  let a := S.standardFormUniversalPairedMiddleArrow x₀ W i
  let hZ := S.standardFormUniversal_tau_noninjective x₀ W
  let z := MeshCategory.RightMeshData.UniversalCover.baseNonprojective
    S.standardFormRightMeshData x₀ W
  have hbase : S.standardFormUniversalArrowSourceBase x₀ a hZ = z := by
    apply Subtype.ext
    let z' : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨W.1.1, W.2⟩
    exact congrArg Subtype.val (S.rightTranslationEquiv.symm_apply_apply z')
  have hpartner : Quiver.Hom.cast (congrArg Subtype.val hbase) rfl
      (S.standardFormUniversalArrowSourceBasePartner x₀ a hZ) =
        (S.standardFormUniversalMiddleArrow x₀ W.1 i).1 := by
    let z₀ := S.standardFormUniversalArrowSourceBase x₀ a hZ
    let hsource := S.standardFormUniversalArrowSourceBase_tau x₀ a hZ
    have htransport := S.standardFormRightMeshData_arrowEquiv_symm_cast
      hbase (S.standardFormUniversalMiddleVertex x₀ W.1 i).1
        (Quiver.Hom.cast rfl hsource.symm a.1)
    calc
      Quiver.Hom.cast (congrArg Subtype.val hbase) rfl
          (S.standardFormUniversalArrowSourceBasePartner x₀ a hZ) =
        (S.standardFormRightMeshData.arrowEquiv z
          (S.standardFormUniversalMiddleVertex x₀ W.1 i).1).symm
            (Quiver.Hom.cast rfl
              (congrArg S.standardFormRightMeshData.tau hbase)
                (Quiver.Hom.cast rfl hsource.symm a.1)) := htransport
      _ = (S.standardFormRightMeshData.arrowEquiv z
          (S.standardFormUniversalMiddleVertex x₀ W.1 i).1).symm a.1 := by
        congr 1
        simp only [Quiver.Hom.cast_cast]
        congr
      _ = (S.standardFormUniversalMiddleArrow x₀ W.1 i).1 := by
        rw [S.standardFormUniversalPairedMiddleArrow_val]
        exact (S.standardFormRightMeshData.arrowEquiv z
          (S.standardFormUniversalMiddleVertex x₀ W.1 i).1).symm_apply_apply _
  have hcostar :
      (⟨(S.standardFormUniversalArrowSourceMesh x₀ a hZ).1,
          S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ⟩ :
        Quiver.Costar (S.standardFormUniversalMiddleVertex x₀ W.1 i)) =
      ⟨W.1, S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ := by
    apply (MeshCategory.RightMeshData.UniversalCover.projection_costar_bijective
      S.standardFormRightMeshData x₀
        (S.standardFormUniversalMiddleVertex x₀ W.1 i)).1
    rw [S.standardFormUniversalArrowSourceMesh_costar]
    rw [S.standardFormUniversalArrowSourceCostar_projection]
    apply Sigma.ext (congrArg Subtype.val hbase)
    exact (Quiver.Hom.cast_eq_iff_heq (congrArg Subtype.val hbase) rfl
      (S.standardFormUniversalArrowSourceBasePartner x₀ a hZ)
        (S.standardFormUniversalMiddleArrow x₀ W.1 i).1).1 hpartner
  exact hcostar

/-- Applied to an explicit polarized mesh arrow, source-mesh recovery returns
the original lifted mesh endpoint. -/
theorem standardFormUniversalArrowSourceMesh_pairedMiddleArrow
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1)) :
    S.standardFormUniversalArrowSourceMesh x₀
        (S.standardFormUniversalPairedMiddleArrow x₀ W i)
          (S.standardFormUniversal_tau_noninjective x₀ W) = W := by
  apply Subtype.ext
  exact congrArg Sigma.fst
    (S.standardFormUniversalArrowSourceCostar_pairedMiddleArrow x₀ W i)

/-- Simultaneously replace source components on all arrows whose represented
module source has one fixed height.  Injective sources are left unchanged;
every other arrow canonically recovers its unique lifted mesh. -/
def replaceStandardFormUniversalArrowMapAtTargetHeight (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀},
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ W) = m →
        (S.fgObj (S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)) ⟶
          (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂)) :
    S.StandardFormUniversalArrowAssignment x₀ :=
  fun {Y Z} a ↦ by
    classical
    by_cases hm : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀ Z = m
    · by_cases hZ : Injective (S.fgObj Z.1)
      · exact D a
      · let W := S.standardFormUniversalArrowSourceMesh x₀ a hZ
        let b := S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ
        let p := MeshCategory.RightMeshData.UniversalCover.pairedArrow
          S.standardFormRightMeshData x₀ W Y b
        have hp := S.standardFormUniversalArrowSourceMesh_paired x₀ a hZ
        have ht : MeshCategory.RightMeshData.UniversalCover.tau
            S.standardFormRightMeshData x₀ W = Z :=
          congrArg Sigma.fst hp
        have hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
            S.standardFormRightMeshData x₀
              (MeshCategory.RightMeshData.UniversalCover.tau
                S.standardFormRightMeshData x₀ W) = m := by
          rw [ht]
          exact hm
        exact eqToHom
            (congrArg (S.standardFormUniversalObj x₀) ht.symm) ≫
          S.standardFormUniversalSourceArrowMap x₀ W (g W hW) p
    · exact D a

/-- At a selected mesh source height, simultaneous source replacement
returns the supplied component on every displayed paired arrow. -/
theorem replaceStandardFormUniversalArrowMapAtTargetHeight_pairedMiddleArrow
    (x₀ : Fin S.n) (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀},
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ W) = m →
        (S.fgObj (S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)) ⟶
          (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂))
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = m)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1)) :
    S.replaceStandardFormUniversalArrowMapAtTargetHeight x₀ D m g
        (S.standardFormUniversalPairedMiddleArrow x₀ W i) =
      g W hW ≫ FiniteTauMatrix.rightMiddleProjection
        S.finiteTauCategoryData W.1.1 i := by
  unfold replaceStandardFormUniversalArrowMapAtTargetHeight
  simp [hW, S.standardFormUniversal_tau_noninjective]
  let W' := S.standardFormUniversalArrowSourceMesh x₀
    (S.standardFormUniversalPairedMiddleArrow x₀ W i)
      (S.standardFormUniversal_tau_noninjective x₀ W)
  let b' := S.standardFormUniversalArrowSourceMeshArrow x₀
    (S.standardFormUniversalPairedMiddleArrow x₀ W i)
      (S.standardFormUniversal_tau_noninjective x₀ W)
  have hmesh : W' = W :=
    S.standardFormUniversalArrowSourceMesh_pairedMiddleArrow x₀ W i
  have hcostar :=
    S.standardFormUniversalArrowSourceCostar_pairedMiddleArrow x₀ W i
  have hb : Quiver.Hom.cast (congrArg Subtype.val hmesh) rfl b' =
      S.standardFormUniversalMiddleArrow x₀ W.1 i := by
    apply (Quiver.Hom.cast_eq_iff_heq
      (congrArg Subtype.val hmesh) rfl b'
        (S.standardFormUniversalMiddleArrow x₀ W.1 i)).2
    exact (Sigma.ext_iff.mp hcostar).2
  have hW' : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W') = m := by
    rw [hmesh]
    exact hW
  calc
    _ = S.standardFormUniversalSourceArrowMap x₀ W (g W hW)
          (S.standardFormUniversalPairedMiddleArrow x₀ W i) := by
      convert S.standardFormUniversalSourceArrowMap_transport
        x₀ m g W' W hmesh b'
          (S.standardFormUniversalMiddleArrow x₀ W.1 i) hb hW' hW
      rfl
    _ = _ :=
      S.standardFormUniversalSourceArrowMap_pairedMiddleArrow
        x₀ W (g W hW) i

/-- Target-height replacement leaves an arrow unchanged away from the
selected target height. -/
theorem replaceStandardFormUniversalArrowMapAtTargetHeight_eq_of_ne
    (x₀ : Fin S.n) (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀},
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ W) = m →
        (S.fgObj (S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)) ⟶
          (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂))
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hZ : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ Z ≠ m) (a : Y ⟶ Z) :
    S.replaceStandardFormUniversalArrowMapAtTargetHeight x₀ D m g a = D a := by
  unfold replaceStandardFormUniversalArrowMapAtTargetHeight
  simp [hZ]

/-- Target-height replacement also leaves arrows ending at injective
vertices unchanged. -/
theorem replaceStandardFormUniversalArrowMapAtTargetHeight_eq_of_injective
    (x₀ : Fin S.n) (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀},
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ W) = m →
        (S.fgObj (S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)) ⟶
          (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂))
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hZ : Injective (S.fgObj Z.1)) (a : Y ⟶ Z) :
    S.replaceStandardFormUniversalArrowMapAtTargetHeight x₀ D m g a = D a := by
  unfold replaceStandardFormUniversalArrowMapAtTargetHeight
  simp [hZ]

/-- At the selected translated-source height, the source assembled from all
replaced components is exactly the supplied source. -/
theorem standardFormUniversalRealizedSource_replaceAtTargetHeight_eq
    (x₀ : Fin S.n) (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀},
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ W) = m →
        (S.fgObj (S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)) ⟶
          (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂))
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = m) :
    S.standardFormUniversalRealizedSource x₀
        (S.replaceStandardFormUniversalArrowMapAtTargetHeight x₀ D m g) W =
      g W hW := by
  apply (cancel_mono
    (FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1.1).hom).1
  apply biproduct.hom_ext
  intro i
  change S.standardFormUniversalRealizedSource x₀
      (S.replaceStandardFormUniversalArrowMapAtTargetHeight x₀ D m g) W ≫
        FiniteTauMatrix.rightMiddleProjection
          S.finiteTauCategoryData W.1.1 i =
    g W hW ≫ FiniteTauMatrix.rightMiddleProjection
      S.finiteTauCategoryData W.1.1 i
  rw [S.standardFormUniversalRealizedSource_rightMiddleProjection]
  exact S.replaceStandardFormUniversalArrowMapAtTargetHeight_pairedMiddleArrow
    x₀ D m g W hW i

/-- Away from the selected translated-source height, target-height
replacement leaves the realized mesh source unchanged. -/
theorem standardFormUniversalRealizedSource_replaceAtTargetHeight_eq_of_ne
    (x₀ : Fin S.n) (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀},
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ W) = m →
        (S.fgObj (S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)) ⟶
          (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂))
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) ≠ m) :
    S.standardFormUniversalRealizedSource x₀
        (S.replaceStandardFormUniversalArrowMapAtTargetHeight x₀ D m g) W =
      S.standardFormUniversalRealizedSource x₀ D W := by
  unfold standardFormUniversalRealizedSource
  congr 1
  apply congrArg biproduct.lift
  funext i
  exact S.replaceStandardFormUniversalArrowMapAtTargetHeight_eq_of_ne
    x₀ D m g hW (S.standardFormUniversalPairedMiddleArrow x₀ W i)

omit [IsAlgClosed k] in
/-- A component cut out by a split projection from a minimal left
almost-split morphism between selected indecomposables is irreducible. -/
theorem isIrreducible_comp_of_leftAlmostSplit_leftMinimal
    {x y : Fin S.n}
    {E : RightModule.FinitelyGeneratedCategory A}
    (inc : S.fgObj y ⟶ E) (proj : E ⟶ S.fgObj y)
    (hinc : inc ≫ proj = 𝟙 (S.fgObj y))
    (g : S.fgObj x ⟶ E)
    (hg : IsLeftAlmostSplit g) (hgmin : IsLeftMinimal g) :
    IsIrreducibleMorphism (g ≫ proj) := by
  have hnotmono : ¬ IsSplitMono (g ≫ proj) := by
    intro hf
    obtain ⟨sm⟩ := hf.exists_splitMono
    apply hg.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := proj ≫ sm.retraction
        id := by simpa only [Category.assoc] using sm.id }
  have hnotepi : ¬ IsSplitEpi (g ≫ proj) := by
    intro hf
    obtain ⟨se⟩ := hf.exists_splitEpi
    letI : IsSplitMono se.section_ :=
      IsSplitMono.mk' ⟨g ≫ proj, se.id⟩
    haveI : IsIso se.section_ :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        (S.fgObj_indecomposable x) se.section_
          (S.fgObj_indecomposable y).1
    have hcompIso : IsIso (g ≫ proj) := by
      have heq : g ≫ proj = inv se.section_ := by
        apply (cancel_epi se.section_).1
        rw [se.id, IsIso.hom_inv_id]
      rw [heq]
      infer_instance
    letI : IsIso (g ≫ proj) := hcompIso
    exact hnotmono inferInstance
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M a b hab
  by_cases ha : IsSplitMono a
  · exact Or.inl ha
  · obtain ⟨c, hc⟩ := hg.factors a ha
    let d : E ⟶ E := 𝟙 E + (c ≫ b - proj) ≫ inc
    have hgfix : g ≫ d = g := by
      have hzero : g ≫ (c ≫ b - proj) = 0 := by
        rw [Preadditive.comp_sub, ← Category.assoc, hc, hab, sub_self]
      dsimp only [d]
      rw [Preadditive.comp_add, Category.comp_id, ← Category.assoc,
        hzero, zero_comp, add_zero]
    have hdproj : d ≫ proj = c ≫ b := by
      dsimp only [d]
      rw [Preadditive.add_comp, Category.id_comp,
        Category.assoc, hinc, Category.comp_id]
      abel
    letI : IsIso d := hgmin d hgfix
    exact Or.inr (IsSplitEpi.mk'
      { section_ := inc ≫ inv d ≫ c
        id := by
          calc
            (inc ≫ inv d ≫ c) ≫ b =
                inc ≫ inv d ≫ (c ≫ b) := by
                  simp only [Category.assoc]
            _ = inc ≫ inv d ≫ (d ≫ proj) := by rw [hdproj]
            _ = inc ≫ (inv d ≫ d) ≫ proj := by
                  simp only [Category.assoc]
            _ = inc ≫ proj := by
                  simp
            _ = 𝟙 (S.fgObj y) := hinc })

/-- The global invariant used by the descending source normalization. -/
structure StandardFormUniversalSourceCondition (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀) : Prop where
  arrow_isIrreducible : ∀ {Y Z :
      MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀} (a : Y ⟶ Z),
    IsIrreducibleMorphism (D a)
  leftAlmostSplit : ∀ W : {W :
      MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀},
    IsLeftAlmostSplit (S.standardFormUniversalRealizedSource x₀ D W)
  leftMinimal : ∀ W : {W :
      MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀},
    IsLeftMinimal (S.standardFormUniversalRealizedSource x₀ D W)

/-- The positive limiting assignment supplies the initial invariant for the
descending source normalization. -/
theorem standardFormUniversalPositiveArrowMap_sourceCondition (x₀ : Fin S.n) :
    S.StandardFormUniversalSourceCondition x₀
      (S.standardFormUniversalPositiveArrowMap x₀) where
  arrow_isIrreducible a :=
    (S.standardFormUniversalPositiveArrowMap_sinkCondition x₀)
      |>.arrow_isIrreducible S x₀ a
  leftAlmostSplit W :=
    (S.standardFormUniversalPositiveArrowMap_sinkCondition x₀)
      |>.realizedSource_isLeftAlmostSplit S x₀ W
  leftMinimal W :=
    (S.standardFormUniversalPositiveArrowMap_sinkCondition x₀)
      |>.realizedSource_isLeftMinimal S x₀ W

set_option backward.isDefEq.respectTransparency false in
/-- Under the global source invariant, each realized sink differs from the
chosen right almost-split sink by an automorphism of the displayed middle
term. -/
theorem StandardFormUniversalSourceCondition.exists_realizedSink_iso
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    ∃ e : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ≅
        (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂,
      e.hom ≫ S.standardFormRightSink W.1 =
        S.standardFormUniversalRealizedSink x₀ D W := by
  classical
  let E := (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂
  let n := FiniteTauMatrix.rightMiddleArity
    S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1
  let label := FiniteTauMatrix.rightMiddleLabel
    S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1
  let F : Fin n → FGModuleCat Aᵐᵒᵖ :=
    fun t ↦ S.almostSplitSkeleton.obj
      (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 t)
  let eMiddle : E ≅ ⨁ F :=
    FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1
  let i : E ⟶ S.fgObj W.1 := S.standardFormRightSink W.1
  let q : E ⟶ S.fgObj W.1 :=
    S.standardFormUniversalRealizedSink x₀ D W
  let inc (t : Fin n) : F t ⟶ E :=
    biproduct.ι F t ≫ eMiddle.inv
  let proj (t : Fin n) : E ⟶ F t :=
    eMiddle.hom ≫ biproduct.π F t
  let component (t : Fin n) : F t ⟶ S.fgObj W.1 := inc t ≫ q
  have hcomponent (t : Fin n) :
      IsIrreducibleMorphism (component t) := by
    change IsIrreducibleMorphism
      (FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData W.1 t ≫
          S.standardFormUniversalRealizedSink x₀ D W)
    rw [S.rightMiddleInclusion_standardFormUniversalRealizedSink]
    exact hD.arrow_isIrreducible
      (S.standardFormUniversalMiddleArrow x₀ W t)
  have hiAS : IsRightAlmostSplit i :=
    S.standardFormRightSink_isRightAlmostSplit W.1
  let factor (t : Fin n) : F t ⟶ E :=
    Classical.choose (hiAS.factors (component t)
      (hcomponent t).not_isSplitEpi)
  have factor_spec (t : Fin n) : factor t ≫ i = component t :=
    Classical.choose_spec (hiAS.factors (component t)
      (hcomponent t).not_isSplitEpi)
  have factor_splitMono (t : Fin n) : IsSplitMono (factor t) := by
    rcases (hcomponent t).factorization (factor t) i (factor_spec t) with
      htSplit | hiSplit
    · exact htSplit
    · exact (hiAS.not_isSplitEpi hiSplit).elim
  let h : E ⟶ E := eMiddle.hom ≫ biproduct.desc factor
  have hhi : h ≫ i = q := by
    apply (cancel_epi eMiddle.inv).1
    apply biproduct.hom_ext'
    intro t
    change biproduct.ι F t ≫ eMiddle.inv ≫ h ≫ i =
      biproduct.ι F t ≫ eMiddle.inv ≫ q
    change inc t ≫ h ≫ i = inc t ≫ q
    calc
      inc t ≫ h ≫ i = factor t ≫ i := by
        simp [h, inc, eMiddle, F, Category.assoc]
      _ = component t := factor_spec t
      _ = inc t ≫ q := rfl
  have hlabel : Function.Injective label :=
    S.standardFormRightMiddleLabel_injective W.1
  have hdiag (t : Fin n) : IsIso (factor t ≫ proj t) := by
    have hdiagSplit : IsSplitMono (factor t ≫ proj t) := by
      by_contra hnot
      have hcomponentNot (j : Fin n) :
          ¬ IsSplitMono (factor t ≫ proj j) := by
        by_cases hjt : j = t
        · subst j
          exact hnot
        · intro hsplit
          letI : IsSplitMono (factor t ≫ proj j) := hsplit
          letI : IsSplitEpi (factor t ≫ proj j) :=
            S.almostSplitSkeleton.isSplitEpi_of_isSplitMono_between_obj
              (factor t ≫ proj j)
          letI : IsIso (factor t ≫ proj j) :=
            isIso_of_epi_of_isSplitMono (factor t ≫ proj j)
          apply hjt
          apply hlabel
          exact (S.almostSplitSkeleton.eq_of_iso
            ⟨asIso (factor t ≫ proj j)⟩).symm
      have hlift : biproduct.lift (fun j ↦ factor t ≫ proj j) =
          factor t ≫ eMiddle.hom := by
        apply biproduct.hom_ext
        intro j
        simp only [biproduct.lift_π]
        rfl
      have hnonsplit :=
        S.almostSplitSkeleton.biproductLift_not_isSplitMono F
          (fun j ↦ factor t ≫ proj j) hcomponentNot
      apply hnonsplit
      rw [hlift]
      letI : IsSplitMono (factor t) := factor_splitMono t
      infer_instance
    letI : IsSplitMono (factor t ≫ proj t) := hdiagSplit
    letI : IsSplitEpi (factor t ≫ proj t) :=
      S.almostSplitSkeleton.isSplitEpi_of_isSplitMono_between_obj
        (factor t ≫ proj t)
    exact isIso_of_epi_of_isSplitMono (factor t ≫ proj t)
  let hSum : (⨁ F) ⟶ ⨁ F := eMiddle.inv ≫ h ≫ eMiddle.hom
  have hpair (a b : Fin n) (hab : a ≠ b) :
      ¬ Nonempty (F a ≅ F b) := by
    intro e
    apply hab
    apply hlabel
    exact S.almostSplitSkeleton.eq_of_iso e
  have hsumDiag (t : Fin n) : IsIso
      (biproduct.ι F t ≫ hSum ≫ biproduct.π F t) := by
    dsimp only [hSum, h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have heq : biproduct.ι F t ≫ biproduct.desc factor ≫
        eMiddle.hom ≫ biproduct.π F t = factor t ≫ proj t := by
      simp only [← Category.assoc, biproduct.ι_desc]
      rfl
    rw [heq]
    exact hdiag t
  haveI : IsIso hSum :=
    MagnitudeConjecture.CategoryTheory.isIso_of_finBiproduct_diagonal_isIso
      F (fun t ↦ S.fgObj_indecomposable (label t))
      (fun t ↦ S.fgObj_end_isLocalRing (label t)) hpair hSum hsumDiag
  have heq : h = eMiddle.hom ≫ hSum ≫ eMiddle.inv := by
    simp [hSum, Category.assoc]
  haveI : IsIso h := by
    rw [heq]
    infer_instance
  exact ⟨asIso h, hhi⟩

/-- The canonical comparison automorphism between the chosen mesh sink and
the sink assembled from a source-compatible assignment. -/
def StandardFormUniversalSourceCondition.realizedSinkIso
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ≅
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ :=
  Classical.choose (hD.exists_realizedSink_iso S x₀ W)

/-- The comparison automorphism realizes the assembled sink exactly. -/
theorem StandardFormUniversalSourceCondition.realizedSinkIso_comp_rightSink
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    (hD.realizedSinkIso S x₀ W).hom ≫
        S.standardFormRightSink W.1 =
      S.standardFormUniversalRealizedSink x₀ D W :=
  Classical.choose_spec (hD.exists_realizedSink_iso S x₀ W)

/-- Every sink assembled from a source-compatible assignment is right almost
split, including the projective boundary vertices. -/
theorem StandardFormUniversalSourceCondition.realizedSink_isRightAlmostSplit
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    IsRightAlmostSplit
      (S.standardFormUniversalRealizedSink x₀ D W) := by
  rw [← hD.realizedSinkIso_comp_rightSink S x₀ W]
  exact rightAlmostSplit_precomp_iso
    (S.standardFormRightSink_isRightAlmostSplit W.1)
    (hD.realizedSinkIso S x₀ W)

/-- Twist the chosen mesh source by the inverse sink comparison. -/
def StandardFormUniversalSourceCondition.normalizedSource
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    S.fgObj (S.standardFormTau
        (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
          S.standardFormRightMeshData x₀ W)) ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂ :=
  S.standardFormRightSource
      (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
        S.standardFormRightMeshData x₀ W) ≫
    (hD.realizedSinkIso S x₀ W).inv

/-- The normalized source has zero composite with the currently realized
sink. -/
@[reassoc (attr := simp)]
theorem StandardFormUniversalSourceCondition.normalizedSource_comp_realizedSink
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    hD.normalizedSource S x₀ W ≫
      S.standardFormUniversalRealizedSink x₀ D W.1 = 0 := by
  rw [← hD.realizedSinkIso_comp_rightSink S x₀ W]
  unfold StandardFormUniversalSourceCondition.normalizedSource
  let e := hD.realizedSinkIso S x₀ W
  let z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet} :=
    ⟨W.1.1, W.2⟩
  change (S.standardFormRightSource z ≫ e.inv) ≫
    (e.hom ≫ S.standardFormRightSink W.1.1) = 0
  calc
    _ = S.standardFormRightSource z ≫
        (e.inv ≫ e.hom) ≫ S.standardFormRightSink W.1.1 := by
      simp only [Category.assoc]
    _ = S.standardFormRightSource z ≫
        S.standardFormRightSink W.1.1 := by
      simp
    _ = 0 := S.standardFormRightSource_comp_rightSink z

/-- The normalized source remains left almost split. -/
theorem StandardFormUniversalSourceCondition.normalizedSource_isLeftAlmostSplit
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    IsLeftAlmostSplit (hD.normalizedSource S x₀ W) := by
  exact leftAlmostSplit_postcomp_iso
    (S.standardFormRightSource_isLeftAlmostSplit
      (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
        S.standardFormRightMeshData x₀ W))
    (hD.realizedSinkIso S x₀ W).symm

/-- The normalized source remains left minimal. -/
theorem StandardFormUniversalSourceCondition.normalizedSource_isLeftMinimal
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    IsLeftMinimal (hD.normalizedSource S x₀ W) := by
  exact leftMinimal_postcomp_iso
    (S.standardFormRightSource_isLeftMinimal
      (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
        S.standardFormRightMeshData x₀ W))
    (hD.realizedSinkIso S x₀ W).symm

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Precomposition by equality transport preserves irreducibility. -/
theorem isIrreducibleMorphism_eqToHom_comp
    {X X' Y : RightModule.FinitelyGeneratedCategory A} (h : X = X')
    (f : X' ⟶ Y) (hf : IsIrreducibleMorphism f) :
    IsIrreducibleMorphism (eqToHom h ≫ f) := by
  subst X'
  simpa using hf

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Postcomposition by equality transport preserves irreducibility. -/
theorem isIrreducibleMorphism_comp_eqToHom
    {X Y Y' : RightModule.FinitelyGeneratedCategory A} (h : Y = Y')
    (f : X ⟶ Y) (hf : IsIrreducibleMorphism f) :
    IsIrreducibleMorphism (f ≫ eqToHom h) := by
  subst Y'
  simpa using hf

/-- Every component extracted from the normalized source is irreducible. -/
theorem StandardFormUniversalSourceCondition.normalizedSourceArrowMap_isIrreducible
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    {Y : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (b : W.1 ⟶ Y) :
    IsIrreducibleMorphism
      (S.standardFormUniversalSourceArrowMap x₀ W
        (hD.normalizedSource S x₀ W)
        (MeshCategory.RightMeshData.UniversalCover.pairedArrow
          S.standardFormRightMeshData x₀ W Y b)) := by
  let z := MeshCategory.RightMeshData.UniversalCover.baseNonprojective
    S.standardFormRightMeshData x₀ W
  unfold standardFormUniversalSourceArrowMap standardFormSourceArrowMap
  dsimp only
  rw [← Category.assoc]
  apply isIrreducibleMorphism_comp_eqToHom
  let b' := (S.standardFormRightMeshData.arrowEquiv z Y.1).symm
    (MeshCategory.RightMeshData.UniversalCover.pairedArrow
      S.standardFormRightMeshData x₀ W Y b).1
  let j := S.standardFormArrowOccurrenceEquiv z.1 Y.1 b'
  apply S.isIrreducible_comp_of_leftAlmostSplit_leftMinimal
    (FiniteTauMatrix.rightMiddleInclusion S.finiteTauCategoryData z.1 j.1)
    (FiniteTauMatrix.rightMiddleProjection S.finiteTauCategoryData z.1 j.1)
    (FiniteTauMatrix.rightMiddleInclusion_projection
      S.finiteTauCategoryData z.1 j.1)
    (hD.normalizedSource S x₀ W)
    (hD.normalizedSource_isLeftAlmostSplit S x₀ W)
    (hD.normalizedSource_isLeftMinimal S x₀ W)

/-- The replacement source used at one translated-source height. -/
def StandardFormUniversalSourceCondition.heightSource
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (_m : ℤ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (_hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = _m) :
    S.fgObj (S.standardFormTau
        (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
          S.standardFormRightMeshData x₀ W)) ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂ :=
  hD.normalizedSource S x₀ W

/-- Simultaneously normalize all mesh sources whose translated vertex has
one fixed height. -/
def StandardFormUniversalSourceCondition.normalizeAtTargetHeight
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (m : ℤ) : S.StandardFormUniversalArrowAssignment x₀ :=
  S.replaceStandardFormUniversalArrowMapAtTargetHeight x₀ D m
    (hD.heightSource S x₀ m)

/-- Replacing sources at translated height `m` does not alter the realized
sink in the same mesh: its outgoing arrows end at height `m + 1`. -/
theorem standardFormUniversalRealizedSink_replaceAtTargetHeight_eq
    (x₀ : Fin S.n) (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀},
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ W) = m →
        (S.fgObj (S.standardFormTau
            (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
              S.standardFormRightMeshData x₀ W)) ⟶
          (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂))
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = m) :
    S.standardFormUniversalRealizedSink x₀
        (S.replaceStandardFormUniversalArrowMapAtTargetHeight x₀ D m g) W.1 =
      S.standardFormUniversalRealizedSink x₀ D W.1 := by
  unfold standardFormUniversalRealizedSink
  congr 1
  apply congrArg biproduct.desc
  funext i
  apply S.replaceStandardFormUniversalArrowMapAtTargetHeight_eq_of_ne
  have hmiddle :=
    MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
      S.standardFormRightMeshData x₀
        (S.standardFormUniversalMiddleArrow x₀ W.1 i)
  have htau := MeshCategory.RightMeshData.UniversalCover.vertexHeight_tau
    S.standardFormRightMeshData x₀ W
  rw [hW] at htau
  omega

/-- One target-height normalization preserves irreducibility and the global
minimal left almost-split source invariant. -/
theorem StandardFormUniversalSourceCondition.normalizeAtTargetHeight_sourceCondition
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (m : ℤ) :
    S.StandardFormUniversalSourceCondition x₀
      (hD.normalizeAtTargetHeight S x₀ m) where
  arrow_isIrreducible {Y Z} a := by
    classical
    unfold StandardFormUniversalSourceCondition.normalizeAtTargetHeight
      replaceStandardFormUniversalArrowMapAtTargetHeight
    by_cases hm : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀ Z = m
    · simp only [hm, dite_true]
      by_cases hZ : Injective (S.fgObj Z.1)
      · simp only [hZ, dite_true]
        exact hD.arrow_isIrreducible a
      · simp only [hZ, dite_false]
        apply isIrreducibleMorphism_eqToHom_comp
        exact hD.normalizedSourceArrowMap_isIrreducible S x₀
          (S.standardFormUniversalArrowSourceMesh x₀ a hZ)
          (S.standardFormUniversalArrowSourceMeshArrow x₀ a hZ)
    · simp only [hm, dite_false]
      exact hD.arrow_isIrreducible a
  leftAlmostSplit W := by
    by_cases hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀
          (MeshCategory.RightMeshData.UniversalCover.tau
            S.standardFormRightMeshData x₀ W) = m
    · unfold StandardFormUniversalSourceCondition.normalizeAtTargetHeight
      rw [S.standardFormUniversalRealizedSource_replaceAtTargetHeight_eq
        x₀ D m (hD.heightSource S x₀ m) W hW]
      exact hD.normalizedSource_isLeftAlmostSplit S x₀ W
    · unfold StandardFormUniversalSourceCondition.normalizeAtTargetHeight
      rw [S.standardFormUniversalRealizedSource_replaceAtTargetHeight_eq_of_ne
        x₀ D m (hD.heightSource S x₀ m) W hW]
      exact hD.leftAlmostSplit W
  leftMinimal W := by
    by_cases hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀
          (MeshCategory.RightMeshData.UniversalCover.tau
            S.standardFormRightMeshData x₀ W) = m
    · unfold StandardFormUniversalSourceCondition.normalizeAtTargetHeight
      rw [S.standardFormUniversalRealizedSource_replaceAtTargetHeight_eq
        x₀ D m (hD.heightSource S x₀ m) W hW]
      exact hD.normalizedSource_isLeftMinimal S x₀ W
    · unfold StandardFormUniversalSourceCondition.normalizeAtTargetHeight
      rw [S.standardFormUniversalRealizedSource_replaceAtTargetHeight_eq_of_ne
        x₀ D m (hD.heightSource S x₀ m) W hW]
      exact hD.leftMinimal W

/-- Every mesh at the selected translated-source height satisfies its
literal zero relation after simultaneous source normalization. -/
theorem StandardFormUniversalSourceCondition.normalizeAtTargetHeight_mesh_zero
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSourceCondition x₀ D)
    (m : ℤ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = m) :
    S.standardFormUniversalRealizedSource x₀
        (hD.normalizeAtTargetHeight S x₀ m) W ≫
      S.standardFormUniversalRealizedSink x₀
        (hD.normalizeAtTargetHeight S x₀ m) W.1 = 0 := by
  unfold StandardFormUniversalSourceCondition.normalizeAtTargetHeight
  rw [S.standardFormUniversalRealizedSource_replaceAtTargetHeight_eq
    x₀ D m (hD.heightSource S x₀ m) W hW]
  rw [S.standardFormUniversalRealizedSink_replaceAtTargetHeight_eq
    x₀ D m (hD.heightSource S x₀ m) W hW]
  exact hD.normalizedSource_comp_realizedSink S x₀ W

/-- An arrow assignment together with the global source invariant required
by the descending induction. -/
structure StandardFormUniversalSourceAssignment (x₀ : Fin S.n) where
  arrowMap : S.StandardFormUniversalArrowAssignment x₀
  sourceCondition : S.StandardFormUniversalSourceCondition x₀ arrowMap

/-- The positive limiting assignment is the initial state of the descending
source induction. -/
def standardFormUniversalInitialSourceAssignment (x₀ : Fin S.n) :
    S.StandardFormUniversalSourceAssignment x₀ where
  arrowMap := S.standardFormUniversalPositiveArrowMap x₀
  sourceCondition := S.standardFormUniversalPositiveArrowMap_sourceCondition x₀

/-- Normalize all sources at one translated-source height while retaining
the global source invariant. -/
def StandardFormUniversalSourceAssignment.normalizeAtTargetHeight
    (x₀ : Fin S.n) (E : S.StandardFormUniversalSourceAssignment x₀)
    (m : ℤ) : S.StandardFormUniversalSourceAssignment x₀ where
  arrowMap := E.sourceCondition.normalizeAtTargetHeight S x₀ m
  sourceCondition :=
    E.sourceCondition.normalizeAtTargetHeight_sourceCondition S x₀ m

/-- Stage `n + 1` of the descending induction normalizes translated-source
height `-n`; stage zero is the positive limiting assignment. -/
def standardFormUniversalNonpositiveStage (x₀ : Fin S.n) :
    ℕ → S.StandardFormUniversalSourceAssignment x₀
  | 0 => S.standardFormUniversalInitialSourceAssignment x₀
  | n + 1 =>
      (standardFormUniversalNonpositiveStage x₀ n).normalizeAtTargetHeight
        S x₀ (-(n : ℤ))

/-- A successor descending stage changes only arrows whose target has the
newly processed height. -/
theorem standardFormUniversalNonpositiveStage_succ_arrow_eq_of_height_ne
    (x₀ : Fin S.n) (n : ℕ)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hZ : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ Z ≠ -(n : ℤ)) (a : Y ⟶ Z) :
    (S.standardFormUniversalNonpositiveStage x₀ (n + 1)).arrowMap a =
      (S.standardFormUniversalNonpositiveStage x₀ n).arrowMap a := by
  exact S.replaceStandardFormUniversalArrowMapAtTargetHeight_eq_of_ne
    x₀ (S.standardFormUniversalNonpositiveStage x₀ n).arrowMap
      (-(n : ℤ))
      ((S.standardFormUniversalNonpositiveStage x₀ n).sourceCondition
        |>.heightSource S x₀ (-(n : ℤ))) hZ a

/-- Positive-target arrows are never changed by the descending induction. -/
theorem standardFormUniversalNonpositiveStage_arrow_eq_positive
    (x₀ : Fin S.n) (r : ℕ)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hZ : 0 < MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ Z) (a : Y ⟶ Z) :
    (S.standardFormUniversalNonpositiveStage x₀ r).arrowMap a =
      S.standardFormUniversalPositiveArrowMap x₀ a := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [S.standardFormUniversalNonpositiveStage_succ_arrow_eq_of_height_ne
        x₀ r (by omega) a]
      exact ih

/-- Once target height `-n` has been processed, all later descending stages
agree on arrows with that target height. -/
theorem standardFormUniversalNonpositiveStage_arrow_stable
    (x₀ : Fin S.n) (n r : ℕ)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hZ : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ Z = -(n : ℤ)) (a : Y ⟶ Z) :
    (S.standardFormUniversalNonpositiveStage x₀ (n + 1 + r)).arrowMap a =
      (S.standardFormUniversalNonpositiveStage x₀ (n + 1)).arrowMap a := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [show n + 1 + (r + 1) = (n + 1 + r) + 1 by omega]
      rw [S.standardFormUniversalNonpositiveStage_succ_arrow_eq_of_height_ne
        x₀ (n + 1 + r) (by omega) a]
      exact ih

/-- The two-sided limiting assignment: nonpositive arrow targets use their
stabilized descending stage; positive targets retain the positive limit. -/
def standardFormUniversalNormalizedArrowMap (x₀ : Fin S.n) :
    S.StandardFormUniversalArrowAssignment x₀ :=
  fun {Y Z} a ↦ by
    classical
    let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ Z
    by_cases hn : h ≤ 0
    · exact (S.standardFormUniversalNonpositiveStage x₀
        (h.natAbs + 1)).arrowMap a
    · exact S.standardFormUniversalPositiveArrowMap x₀ a

/-- At target height `-n`, the two-sided limit agrees with descending stage
`n + 1`. -/
theorem standardFormUniversalNormalizedArrowMap_eq_stage_succ
    (x₀ : Fin S.n) (n : ℕ)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hZ : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ Z = -(n : ℤ)) (a : Y ⟶ Z) :
    S.standardFormUniversalNormalizedArrowMap x₀ a =
      (S.standardFormUniversalNonpositiveStage x₀ (n + 1)).arrowMap a := by
  simp [standardFormUniversalNormalizedArrowMap, hZ]

/-- At positive target height, the two-sided limit agrees with the positive
limiting assignment. -/
theorem standardFormUniversalNormalizedArrowMap_eq_positive
    (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hZ : 0 < MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ Z) (a : Y ⟶ Z) :
    S.standardFormUniversalNormalizedArrowMap x₀ a =
      S.standardFormUniversalPositiveArrowMap x₀ a := by
  simp [standardFormUniversalNormalizedArrowMap, not_le_of_gt hZ]

/-- For a mesh whose translated source has height `-n`, its source in the
two-sided limit is already its source at stage `n + 1`. -/
theorem standardFormUniversalNormalizedRealizedSource_eq_stage_succ
    (x₀ : Fin S.n) (n : ℕ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = -(n : ℤ)) :
    S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W =
      S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNonpositiveStage x₀ (n + 1)).arrowMap W := by
  unfold standardFormUniversalRealizedSource
  congr 1
  apply congrArg biproduct.lift
  funext i
  exact S.standardFormUniversalNormalizedArrowMap_eq_stage_succ
    x₀ n hW (S.standardFormUniversalPairedMiddleArrow x₀ W i)

/-- For a mesh whose translated source has height `-n`, its sink in the
two-sided limit is also already its sink at stage `n + 1`. -/
theorem standardFormUniversalNormalizedRealizedSink_eq_stage_succ
    (x₀ : Fin S.n) (n : ℕ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = -(n : ℤ)) :
    S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W.1 =
      S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalNonpositiveStage x₀ (n + 1)).arrowMap W.1 := by
  unfold standardFormUniversalRealizedSink
  congr 1
  apply congrArg biproduct.desc
  funext i
  have hmiddle :=
    MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
      S.standardFormRightMeshData x₀
        (S.standardFormUniversalMiddleArrow x₀ W.1 i)
  have htau := MeshCategory.RightMeshData.UniversalCover.vertexHeight_tau
    S.standardFormRightMeshData x₀ W
  rw [hW] at htau
  rcases n with _ | n
  · have hpositive : 0 <
        MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalMiddleVertex x₀ W.1 i) := by
      omega
    calc
      S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalMiddleArrow x₀ W.1 i) =
          S.standardFormUniversalPositiveArrowMap x₀
            (S.standardFormUniversalMiddleArrow x₀ W.1 i) :=
        S.standardFormUniversalNormalizedArrowMap_eq_positive
          x₀ hpositive _
      _ = (S.standardFormUniversalNonpositiveStage x₀ 1).arrowMap
          (S.standardFormUniversalMiddleArrow x₀ W.1 i) := by
        symm
        exact S.standardFormUniversalNonpositiveStage_arrow_eq_positive
          x₀ 1 hpositive _
  · have htarget :
        MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalMiddleVertex x₀ W.1 i) =
          -(n : ℤ) := by
      omega
    calc
      S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalMiddleArrow x₀ W.1 i) =
          (S.standardFormUniversalNonpositiveStage x₀ (n + 1)).arrowMap
            (S.standardFormUniversalMiddleArrow x₀ W.1 i) :=
        S.standardFormUniversalNormalizedArrowMap_eq_stage_succ
          x₀ n htarget _
      _ = (S.standardFormUniversalNonpositiveStage x₀ (n + 2)).arrowMap
          (S.standardFormUniversalMiddleArrow x₀ W.1 i) := by
        symm
        apply S.standardFormUniversalNonpositiveStage_succ_arrow_eq_of_height_ne
          x₀ (n + 1)
        omega

/-- Every mesh whose translated source has height `-n` satisfies its literal
zero relation in the two-sided limiting assignment. -/
theorem standardFormUniversalNormalized_mesh_zero_of_tau_height_eq_neg
    (x₀ : Fin S.n) (n : ℕ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) = -(n : ℤ)) :
    S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W ≫
      S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W.1 = 0 := by
  rw [S.standardFormUniversalNormalizedRealizedSource_eq_stage_succ
    x₀ n W hW]
  rw [S.standardFormUniversalNormalizedRealizedSink_eq_stage_succ
    x₀ n W hW]
  exact
    (S.standardFormUniversalNonpositiveStage x₀ n).sourceCondition
      |>.normalizeAtTargetHeight_mesh_zero S x₀ (-(n : ℤ)) W hW

/-- Every representative in the two-sided limiting assignment remains
irreducible. -/
theorem standardFormUniversalNormalizedArrowMap_isIrreducible
    (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z) :
    IsIrreducibleMorphism (S.standardFormUniversalNormalizedArrowMap x₀ a) := by
  by_cases hn : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ Z ≤ 0
  · rw [show S.standardFormUniversalNormalizedArrowMap x₀ a =
        (S.standardFormUniversalNonpositiveStage x₀
          ((MeshCategory.RightMeshData.UniversalCover.vertexHeight
            S.standardFormRightMeshData x₀ Z).natAbs + 1)).arrowMap a by
      simp [standardFormUniversalNormalizedArrowMap, hn]]
    exact (S.standardFormUniversalNonpositiveStage x₀
        ((MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀ Z).natAbs + 1))
      |>.sourceCondition.arrow_isIrreducible a
  · rw [show S.standardFormUniversalNormalizedArrowMap x₀ a =
        S.standardFormUniversalPositiveArrowMap x₀ a by
      simp [standardFormUniversalNormalizedArrowMap, hn]]
    exact (S.standardFormUniversalPositiveArrowMap_sinkCondition x₀)
      |>.arrow_isIrreducible S x₀ a

/-- Every lifted mesh satisfies its literal zero relation in the two-sided
limiting assignment. -/
theorem standardFormUniversalNormalized_mesh_zero
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W ≫
      S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W.1 = 0 := by
  let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
    S.standardFormRightMeshData x₀
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ W)
  by_cases hn : h ≤ 0
  · have habs : (h.natAbs : ℤ) = -h := by
      rw [Int.natCast_natAbs, abs_of_nonpos hn]
    apply S.standardFormUniversalNormalized_mesh_zero_of_tau_height_eq_neg
      x₀ h.natAbs W
    dsimp only [h]
    omega
  · have hp : 0 < h := lt_of_not_ge hn
    have hsource :
        S.standardFormUniversalRealizedSource x₀
            (S.standardFormUniversalNormalizedArrowMap x₀) W =
          S.standardFormUniversalRealizedSource x₀
            (S.standardFormUniversalPositiveArrowMap x₀) W := by
      unfold standardFormUniversalRealizedSource
      congr 1
      apply congrArg biproduct.lift
      funext i
      exact S.standardFormUniversalNormalizedArrowMap_eq_positive
        x₀ hp (S.standardFormUniversalPairedMiddleArrow x₀ W i)
    have hsink :
        S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalNormalizedArrowMap x₀) W.1 =
          S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalPositiveArrowMap x₀) W.1 := by
      unfold standardFormUniversalRealizedSink
      congr 1
      apply congrArg biproduct.desc
      funext i
      apply S.standardFormUniversalNormalizedArrowMap_eq_positive
      have hmiddle :=
        MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalMiddleArrow x₀ W.1 i)
      have htau := MeshCategory.RightMeshData.UniversalCover.vertexHeight_tau
        S.standardFormRightMeshData x₀ W
      dsimp only [h] at hp
      omega
    rw [hsource, hsink]
    apply S.standardFormUniversalPositive_mesh_zero x₀ W
    have htau := MeshCategory.RightMeshData.UniversalCover.vertexHeight_tau
      S.standardFormRightMeshData x₀ W
    dsimp only [h] at hp
    omega

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
