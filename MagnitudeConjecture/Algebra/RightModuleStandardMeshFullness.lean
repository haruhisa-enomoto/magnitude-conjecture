import MagnitudeConjecture.Algebra.RightModuleStandardMeshNormalization

/-!
# The local fullness step for a displayed right mesh

Ringel's standardness recursion chooses all arrows ending at one vertex as
the occurrence components of a right almost-split sink.  This file proves
the two local facts needed by that recursion: those components reassemble to
the supplied sink, and fullness at all strict predecessors extends to the
current target.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped BigOperators

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance : Quiver (Fin S.n) := S.meshQuiver
local instance (i j : Fin S.n) : Fintype (i ⟶ j) :=
  S.meshArrowFintype i j

/-- A nonprojective module label as a nonprojective vertex of the concrete
right mesh data. -/
def rightMeshNonprojectiveVertex
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    {z : Fin S.n // z ∉ (S.rightMeshData H).projective} :=
  ⟨z.1, z.2⟩

@[simp]
theorem rightMeshNonprojectiveVertex_val
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (S.rightMeshNonprojectiveVertex H z).1 = z.1 :=
  rfl

@[simp]
theorem rightMeshData_tau_rightMeshNonprojectiveVertex
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (S.rightMeshData H).tau (S.rightMeshNonprojectiveVertex H z) =
      S.rightTranslationLabel z :=
  rfl

/-- The arrow representative at one fixed target obtained by taking an
occurrence component of a supplied map out of the displayed middle. -/
def meshSinkArrowMap (z : Fin S.n)
    (g : (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z)
    {y : Fin S.n} (a : S.MeshArrow z y) :
    S.almostSplitSkeleton.obj y ⟶ S.almostSplitSkeleton.obj z :=
  eqToHom (congrArg S.almostSplitSkeleton.obj a.2.symm) ≫
    biproduct.ι
      (fun t ↦ S.almostSplitSkeleton.obj
        ((S.meshRightAlmostSplitAt z).label t)) a.1 ≫
    (S.meshRightAlmostSplitAt z).decomposition.inv ≫ g

/-- Replace all arrow representatives ending at one fixed target by the
occurrence components of `g`, leaving every other target unchanged. -/
def replaceArrowMapAt
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : Fin S.n)
    (g : (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z)
    {i j : Fin S.n} (a : S.MeshArrow i j) :
    S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i := by
  classical
  by_cases hiz : i = z
  · subst i
    exact S.meshSinkArrowMap z g a
  · exact arrowMap a

@[simp]
theorem replaceArrowMapAt_eq
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : Fin S.n)
    (g : (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z)
    {y : Fin S.n} (a : S.MeshArrow z y) :
    S.replaceArrowMapAt arrowMap z g a = S.meshSinkArrowMap z g a := by
  simp [replaceArrowMapAt]

@[simp]
theorem replaceArrowMapAt_eq_of_ne
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : Fin S.n)
    (g : (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z)
    {i j : Fin S.n} (hiz : i ≠ z) (a : S.MeshArrow i j) :
    S.replaceArrowMapAt arrowMap z g a = arrowMap a := by
  simp [replaceArrowMapAt, hiz]

/-- Assemble all representatives ending at `z` into a map out of its
displayed middle. -/
def realizedRightMeshSink
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : Fin S.n) :
    (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z :=
  (S.meshRightAlmostSplitAt z).decomposition.hom ≫
    biproduct.desc (fun t ↦
      arrowMap
        (⟨t, rfl⟩ : S.MeshArrow z
          ((S.meshRightAlmostSplitAt z).label t)))

/-- Taking all occurrence components and reassembling them recovers the
original map out of the displayed middle. -/
@[simp]
theorem realizedRightMeshSink_replaceArrowMapAt
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : Fin S.n)
    (g : (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z) :
    S.realizedRightMeshSink
        (S.replaceArrowMapAt arrowMap z g) z = g := by
  classical
  let B := S.meshRightAlmostSplitAt z
  letI : Fintype B.index := FintypeCat.fintype
  apply (cancel_epi B.decomposition.inv).1
  apply biproduct.hom_ext'
  intro t
  simp [realizedRightMeshSink, replaceArrowMapAt, meshSinkArrowMap, B]

/-- Updating the representatives ending at `z` leaves the assembled sink at
every other target unchanged. -/
theorem realizedRightMeshSink_replaceArrowMapAt_of_ne
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : Fin S.n)
    (g : (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z)
    (w : Fin S.n) (hwz : w ≠ z) :
    S.realizedRightMeshSink (S.replaceArrowMapAt arrowMap z g) w =
      S.realizedRightMeshSink arrowMap w := by
  simp [realizedRightMeshSink, replaceArrowMapAt, hwz]

/-- The radical inclusion transported from the literal projective radical
to the uniform displayed middle. -/
def meshProjectiveSink
    (z : Fin S.n) (hz : Projective (S.fgObj z)) :
    (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z :=
  eqToHom (S.meshRightAlmostSplitAt_middle_eq_of_projective z hz) ≫
    S.meshProjectiveBoundaryMap z

/-- The transported projective radical inclusion is monic. -/
theorem meshProjectiveSink_mono
    (z : Fin S.n) (hz : Projective (S.fgObj z)) :
    Mono (S.meshProjectiveSink z hz) := by
  letI : Mono (S.meshProjectiveBoundaryMap z) :=
    (IndecomposableSkeleton.fg_mono_iff_injective
      (S.meshProjectiveBoundaryMap z)).2
      (Module.jacobson Aᵐᵒᵖ (S.fgObj z)).subtype_injective
  dsimp only [meshProjectiveSink]
  infer_instance

/-- The transported projective radical inclusion is right almost split. -/
theorem meshProjectiveSink_rightAlmostSplit
    (z : Fin S.n) (hz : Projective (S.fgObj z)) :
    IsRightAlmostSplit (S.meshProjectiveSink z hz) :=
  rightAlmostSplit_precomp_iso
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit z hz)
    (eqToIso (S.meshRightAlmostSplitAt_middle_eq_of_projective z hz))

/-- Changing representatives at a later target does not change free-path
evaluation into an earlier target. -/
theorem lift_map_replaceArrowMapAt_eq_of_lt
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : Fin S.n)
    (g : (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z)
    {x y : Fin S.n} (hyz : (S.directedLinearOrder H).lt y z)
    (p : LinearPathCategory.obj k (Fin S.n) x ⟶
      LinearPathCategory.obj k (Fin S.n) y) :
    (LinearPathCategory.lift
        (k := k) S.almostSplitSkeleton.obj
        (S.replaceArrowMapAt arrowMap z g)).map p =
      (LinearPathCategory.lift
        (k := k) S.almostSplitSkeleton.obj arrowMap).map p := by
  letI : Preorder (Fin S.n) := (S.directedLinearOrder H).toPreorder
  change
    LinearPathCategory.homMap S.almostSplitSkeleton.obj
        (S.replaceArrowMapAt arrowMap z g) _ _ p =
      LinearPathCategory.homMap S.almostSplitSkeleton.obj arrowMap _ _ p
  symm
  apply LinearPathCategory.homMap_eq_of_eq_on_source_le
    S.almostSplitSkeleton.obj arrowMap
      (S.replaceArrowMapAt arrowMap z g) (S.meshArrow_lt H) p
  intro a b e hae
  symm
  apply S.replaceArrowMapAt_eq_of_ne arrowMap z g
  intro haz
  subst a
  exact (not_le_of_gt hyz) hae

/-- Updating a later target leaves the paired source map of every earlier
nonprojective mesh unchanged. -/
theorem rightMeshSourceMap_replaceArrowMapAt_eq_of_le
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : Fin S.n)
    (g : (S.meshRightAlmostSplitAt z).middle ⟶
      S.almostSplitSkeleton.obj z)
    (w : {w : Fin S.n // ¬ Projective (S.fgObj w)})
    (hwz : (S.directedLinearOrder H).le w.1 z) :
    S.rightMeshSourceMap H (S.replaceArrowMapAt arrowMap z g) w =
      S.rightMeshSourceMap H arrowMap w := by
  classical
  letI : Preorder (Fin S.n) := (S.directedLinearOrder H).toPreorder
  let B := S.meshRightAlmostSplitAt w.1
  letI : Fintype B.index := FintypeCat.fintype
  apply (cancel_mono B.decomposition.hom).1
  apply biproduct.hom_ext
  intro t
  dsimp only [B]
  simp only [Category.assoc, S.rightMeshSourceMap_decomposition_π]
  rw [S.replaceArrowMapAt_eq_of_ne]
  intro hlabel
  have hlt : (S.directedLinearOrder H).lt (B.label t) w.1 :=
    S.meshArrow_lt H (S.meshMiddleIndexEquiv w.1 t).2
  have hltz : (S.directedLinearOrder H).lt (B.label t) z :=
    lt_of_lt_of_le hlt hwz
  apply ne_of_lt hltz
  simpa only [B, S.rightMeshSourceIndexEquiv_fst H w t] using hlabel

/-- Evaluation of the literal mesh relation is the recursively assembled
source map followed by the sink assembled from the incoming representatives.
The equality retains the full occurrence indexing on both sides. -/
theorem lift_map_meshRelation_eq_source_comp_sink
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (LinearPathCategory.lift
      (k := k) S.almostSplitSkeleton.obj arrowMap).map
        ((S.rightMeshData H).meshRelation (k := k)
          (S.rightMeshNonprojectiveVertex H z)) =
      S.rightMeshSourceMap H arrowMap z ≫
        S.realizedRightMeshSink arrowMap z.1 := by
  classical
  let T := S.rightMeshData H
  let x := S.rightMeshNonprojectiveVertex H z
  let F := LinearPathCategory.lift
    (k := k) S.almostSplitSkeleton.obj arrowMap
  let B := S.meshRightAlmostSplitAt z.1
  letI : Fintype B.index := FintypeCat.fintype
  letI (y : Fin S.n) : Fintype (S.MeshArrow z.1 y) :=
    S.meshArrowFintype z.1 y
  have hterm (a : T.MeshArrow x) :
      F.map (LinearPathCategory.pathHom (T.meshPath x a)) =
        arrowMap ((T.arrowEquiv x a.1) a.2) ≫ arrowMap a.2 := by
    rw [LinearPathCategory.lift_map_pathHom]
    dsimp only [MeshCategory.RightMeshData.meshPath]
    calc
      _ = LinearPathCategory.pathMap S.almostSplitSkeleton.obj arrowMap
            ((T.arrowEquiv x a.1 a.2).toPath) ≫
          LinearPathCategory.pathMap S.almostSplitSkeleton.obj arrowMap
            a.2.toPath :=
        LinearPathCategory.pathMap_comp
          S.almostSplitSkeleton.obj arrowMap _ _
      _ = _ := by
        rw [LinearPathCategory.pathMap_toPath,
          LinearPathCategory.pathMap_toPath]
  have hrelation :
      F.map (T.meshRelation (k := k) x) =
        ∑ a : T.MeshArrow x,
          arrowMap ((T.arrowEquiv x a.1) a.2) ≫ arrowMap a.2 := by
    rw [MeshCategory.RightMeshData.meshRelation, Functor.map_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact hterm a
  rw [show
    (LinearPathCategory.lift
      (k := k) S.almostSplitSkeleton.obj arrowMap).map
        ((S.rightMeshData H).meshRelation (k := k)
          (S.rightMeshNonprojectiveVertex H z)) =
      F.map (T.meshRelation (k := k) x) from rfl,
    hrelation]
  dsimp only [rightMeshSourceMap, realizedRightMeshSink]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_desc]
  simp only [S.rightMeshSourceIndexEquiv_fst H z,
    eqToHom_refl]
  let e : B.index ≃ T.MeshArrow x := by
    change (S.meshRightAlmostSplitAt z.1).index ≃
      Σ y : Fin S.n, S.MeshArrow z.1 y
    exact S.meshMiddleIndexEquiv z.1
  have hreindex := e.sum_comp
    (fun a : T.MeshArrow x ↦
      arrowMap ((T.arrowEquiv x a.1) a.2) ≫ arrowMap a.2)
  rw [hreindex.symm]
  apply Finset.sum_congr rfl
  intro t _
  rfl

/-- If the displayed incoming-arrow family realizes a right almost-split
sink and the free-path realization is full at every strict predecessor of
`z`, it is full at `z` as well. -/
theorem exists_freePath_map_eq_of_rightAlmostSplit
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z x : Fin S.n)
    (hsink : IsRightAlmostSplit (S.realizedRightMeshSink arrowMap z))
    (hfull : ∀ (y : Fin S.n),
      (S.directedLinearOrder H).lt y z →
      ∀ f : S.almostSplitSkeleton.obj x ⟶
          S.almostSplitSkeleton.obj y,
        ∃ p : LinearPathCategory.obj k (Fin S.n) x ⟶
            LinearPathCategory.obj k (Fin S.n) y,
          (LinearPathCategory.lift
            (k := k) S.almostSplitSkeleton.obj arrowMap).map p = f) :
    ∀ f : S.almostSplitSkeleton.obj x ⟶
        S.almostSplitSkeleton.obj z,
      ∃ p : LinearPathCategory.obj k (Fin S.n) x ⟶
          LinearPathCategory.obj k (Fin S.n) z,
        (LinearPathCategory.lift
          (k := k) S.almostSplitSkeleton.obj arrowMap).map p = f := by
  classical
  intro f
  by_cases hxz : x = z
  · subst x
    obtain ⟨c, hc⟩ := H.endomorphism_eq_smul_id S z f
    refine ⟨c • 𝟙 _, ?_⟩
    have hid :
        (LinearPathCategory.lift
          (k := k) S.almostSplitSkeleton.obj arrowMap).map
            (𝟙 (LinearPathCategory.obj k (Fin S.n) z)) =
          𝟙 (S.almostSplitSkeleton.obj z) := by
      exact (LinearPathCategory.lift
        (k := k) S.almostSplitSkeleton.obj arrowMap).map_id _
    rw [Functor.map_smul, hid]
    exact hc
  · have hf : ¬ IsSplitEpi f := by
      intro hsplit
      letI : IsSplitEpi f := hsplit
      letI : IsSplitMono f :=
        @IndecomposableSkeleton.isSplitMono_of_isSplitEpi_between_obj
          Aᵐᵒᵖ _ _ (Fin S.n) S.almostSplitSkeleton x z f hsplit
      letI : IsIso f := isIso_of_mono_of_epi f
      exact hxz (S.almostSplitSkeleton.eq_of_iso ⟨asIso f⟩)
    obtain ⟨h, hh⟩ := hsink.factors f hf
    let B := S.meshRightAlmostSplitAt z
    letI : Fintype B.index := FintypeCat.fintype
    let component (t : B.index) : S.almostSplitSkeleton.obj x ⟶
        S.almostSplitSkeleton.obj (B.label t) :=
      h ≫ B.decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.almostSplitSkeleton.obj (B.label j)) t
    have hlabel_lt (t : B.index) :
        (S.directedLinearOrder H).lt (B.label t) z :=
      S.meshArrow_lt H
        (⟨t, rfl⟩ : S.MeshArrow z (B.label t))
    let path (t : B.index) :
        LinearPathCategory.obj k (Fin S.n) x ⟶
          LinearPathCategory.obj k (Fin S.n) (B.label t) :=
      Classical.choose (hfull (B.label t) (hlabel_lt t) (component t))
    have path_spec (t : B.index) :
        (LinearPathCategory.lift
          (k := k) S.almostSplitSkeleton.obj arrowMap).map (path t) =
          component t :=
      Classical.choose_spec
        (hfull (B.label t) (hlabel_lt t) (component t))
    let occurrence (t : B.index) : S.MeshArrow z (B.label t) := ⟨t, rfl⟩
    let arrowHom (t : B.index) :
        LinearPathCategory.obj k (Fin S.n) (B.label t) ⟶
          LinearPathCategory.obj k (Fin S.n) z :=
      LinearPathCategory.pathHom
        ((show z ⟶ B.label t from occurrence t).toPath)
    let arrowValue (t : B.index) :
        S.almostSplitSkeleton.obj (B.label t) ⟶
          S.almostSplitSkeleton.obj z :=
      arrowMap (occurrence t)
    let result : LinearPathCategory.obj k (Fin S.n) x ⟶
        LinearPathCategory.obj k (Fin S.n) z :=
      ∑ t : B.index, path t ≫ arrowHom t
    have arrow_spec (t : B.index) :
        (LinearPathCategory.lift
          (k := k) S.almostSplitSkeleton.obj arrowMap).map
            (arrowHom t) = arrowValue t := by
      dsimp only [arrowHom, arrowValue]
      rw [LinearPathCategory.lift_map_pathHom]
      exact LinearPathCategory.pathMap_toPath
        S.almostSplitSkeleton.obj arrowMap
          (show z ⟶ B.label t from
            occurrence t)
    refine ⟨result, ?_⟩
    rw [show f = h ≫ S.realizedRightMeshSink arrowMap z from hh.symm]
    dsimp only [result, realizedRightMeshSink]
    rw [Functor.map_sum]
    have hsum :
        (∑ t : B.index,
          (LinearPathCategory.lift
            (k := k) S.almostSplitSkeleton.obj arrowMap).map
              (path t ≫ arrowHom t)) =
          ∑ t : B.index, component t ≫ arrowValue t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Functor.map_comp, path_spec t, arrow_spec t]
      rfl
    have hlift : biproduct.lift component = h ≫ B.decomposition.hom := by
      apply biproduct.hom_ext
      intro t
      rw [biproduct.lift_π]
      rfl
    have hcomponents :
        (∑ t : B.index, component t ≫ arrowValue t) =
          h ≫ B.decomposition.hom ≫
            biproduct.desc arrowValue := by
      calc
        _ = biproduct.lift component ≫ biproduct.desc arrowValue := by
          rw [biproduct.lift_desc]
        _ = (h ≫ B.decomposition.hom) ≫
            biproduct.desc arrowValue := by rw [hlift]
        _ = _ := Category.assoc _ _ _
    exact hsum.trans (by
      dsimp only [arrowValue, occurrence] at hcomponents
      exact hcomponents)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
