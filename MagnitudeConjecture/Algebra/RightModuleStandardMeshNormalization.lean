import MagnitudeConjecture.Algebra.RightModuleStandardMesh
import MagnitudeConjecture.CategoryTheory.LinearPathDecomposition
import Mathlib.RingTheory.Length

/-!
# Normalizing a recursively assembled mesh map

Ringel's standardness recursion first assembles a map from an
Auslander--Reiten translate to the displayed middle term using arrows that
were chosen at earlier vertices.  Fullness at those earlier vertices gives
factorizations in both directions between this assembled map and the actual
left almost-split kernel inclusion.  This file isolates the finite-length
argument which upgrades the comparison endomorphism of the middle term to an
automorphism.  Twisting the right almost-split map by its inverse then makes
the mesh relation hold literally.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule

universe u

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Postcomposition by an isomorphism preserves left almost-splitness. -/
theorem leftAlmostSplit_postcomp_iso
    {C : Type*} [CategoryTheory.Category C] {X E E' : C} {f : X ⟶ E}
    (hf : IsLeftAlmostSplit f) (e : E ≅ E') :
    IsLeftAlmostSplit (f ≫ e.hom) := by
  constructor
  · intro hsplit
    apply hf.not_isSplitMono
    letI : IsSplitMono (f ≫ e.hom) := hsplit
    have : IsSplitMono ((f ≫ e.hom) ≫ e.inv) := by
      infer_instance
    simpa using this
  · intro Y g hg
    obtain ⟨h, hh⟩ := hf.factors g hg
    refine ⟨e.inv ≫ h, ?_⟩
    rw [Category.assoc, Iso.hom_inv_id_assoc, hh]

/-- Postcomposition by an isomorphism preserves left minimality. -/
theorem leftMinimal_postcomp_iso
    {C : Type*} [CategoryTheory.Category C] {X E E' : C} {f : X ⟶ E}
    (hf : IsLeftMinimal f) (e : E ≅ E') :
    IsLeftMinimal (f ≫ e.hom) := by
  intro a ha
  let b : E ⟶ E := e.hom ≫ a ≫ e.inv
  have hb : f ≫ b = f := by
    have h := congrArg (fun q ↦ q ≫ e.inv) ha
    simpa only [b, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  letI : IsIso b := hf b hb
  let aIso : E' ≅ E' := e.symm.trans ((asIso b).trans e)
  have haIso : aIso.hom = a := by
    simp [aIso, b, Category.assoc]
  rw [← haIso]
  infer_instance

/-- Precomposition by an isomorphism preserves right almost-splitness. -/
theorem rightAlmostSplit_precomp_iso
    {C : Type*} [CategoryTheory.Category C] {E' E Z : C} {f : E ⟶ Z}
    (hf : IsRightAlmostSplit f) (e : E' ≅ E) :
    IsRightAlmostSplit (e.hom ≫ f) := by
  constructor
  · intro hsplit
    apply hf.not_isSplitEpi
    letI : IsSplitEpi (e.hom ≫ f) := hsplit
    have : IsSplitEpi (e.inv ≫ (e.hom ≫ f)) := by
      infer_instance
    simpa using this
  · intro X g hg
    obtain ⟨h, hh⟩ := hf.factors g hg
    refine ⟨h ≫ e.inv, ?_⟩
    rw [Category.assoc, Iso.inv_hom_id_assoc, hh]

/-- A monic endomorphism of a finite-length finitely generated module is an
isomorphism. -/
theorem isIso_of_mono_finiteLength_endomorphism
    {X : FGModuleCat.{u} R} (hX : IsFiniteLength R X)
    (f : X ⟶ X) [Mono f] :
    IsIso f := by
  obtain ⟨hN, hA⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hX
  letI : IsNoetherian R X := hN
  letI : IsArtinian R X := hA
  have hinj : Function.Injective f.hom.hom :=
    (IndecomposableSkeleton.fg_mono_iff_injective f).1 inferInstance
  have hsurj : Function.Surjective f.hom.hom :=
    IsArtinian.surjective_of_injective_endomorphism f.hom.hom hinj
  letI : Epi f :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).2 hsurj
  exact isIso_of_mono_of_epi f

/-- If a nonsplit map and a minimal left almost-split map with the same
source factor through one another, their middle terms differ by an
automorphism.  Finite length is used only to turn the resulting split-monic
endomorphism into an isomorphism. -/
theorem exists_middleIso_of_leftAlmostSplit_mutual_factorization
    {K E : FGModuleCat.{u} R} (i q : K ⟶ E)
    (hE : IsFiniteLength R E)
    (hi : IsLeftAlmostSplit i) (himin : IsLeftMinimal i)
    (hq : ¬ IsSplitMono q)
    (hqi : ∃ r : E ⟶ E, q ≫ r = i) :
    ∃ e : E ≅ E, i ≫ e.hom = q := by
  obtain ⟨h, hh⟩ := hi.factors q hq
  obtain ⟨r, hr⟩ := hqi
  have hfix : i ≫ (h ≫ r) = i := by
    rw [← Category.assoc, hh, hr]
  letI : IsIso (h ≫ r) := himin (h ≫ r) hfix
  letI : IsSplitMono h := IsSplitMono.mk'
    { retraction := r ≫ inv (h ≫ r)
      id := by
        rw [← Category.assoc, IsIso.hom_inv_id] }
  letI : IsIso h := isIso_of_mono_finiteLength_endomorphism hE h
  exact ⟨asIso h, hh⟩

/-- Normalize a comparison map and transport a zero composite across the
resulting automorphism.  This is the literal mesh-relation step used at a
nonprojective vertex of the standardness recursion. -/
theorem exists_middleIso_normalizing_leftAlmostSplit
    {K E Z : FGModuleCat.{u} R} (i q : K ⟶ E) (g : E ⟶ Z)
    (hE : IsFiniteLength R E)
    (hi : IsLeftAlmostSplit i) (himin : IsLeftMinimal i)
    (hq : ¬ IsSplitMono q)
    (hqi : ∃ r : E ⟶ E, q ≫ r = i)
    (hzero : i ≫ g = 0) :
    ∃ e : E ≅ E, i ≫ e.hom = q ∧ q ≫ e.inv ≫ g = 0 := by
  obtain ⟨e, he⟩ :=
    exists_middleIso_of_leftAlmostSplit_mutual_factorization
      i q hE hi himin hq hqi
  refine ⟨e, he, ?_⟩
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc, hzero]

namespace FiniteIndecomposableSkeleton

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance : Quiver (Fin S.n) := S.meshQuiver
local instance (i j : Fin S.n) : Fintype (i ⟶ j) :=
  S.meshArrowFintype i j

/-- The displayed middle summands at a nonprojective vertex, reindexed by
all reversed quiver arrows out of its AR translate. -/
def rightMeshSourceIndexEquiv
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (S.meshRightAlmostSplitAt z.1).index ≃
      Σ y : Fin S.n, S.MeshArrow y (S.rightTranslationLabel z) := by
  exact (S.meshMiddleIndexEquiv z.1).trans
    (Equiv.sigmaCongrRight fun y ↦ S.meshArrowEquiv H z y)

@[simp]
theorem rightMeshSourceIndexEquiv_fst
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (t : (S.meshRightAlmostSplitAt z.1).index) :
    (S.rightMeshSourceIndexEquiv H z t).1 =
      (S.meshRightAlmostSplitAt z.1).label t :=
  rfl

/-- Assemble the already chosen arrows out of `tau z` into the displayed
middle term at `z`, using the mesh-arrow pairing. -/
def rightMeshSourceMap
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.almostSplitSkeleton.obj (S.rightTranslationLabel z) ⟶
      (S.meshRightAlmostSplitAt z.1).middle :=
  biproduct.lift (fun t ↦
      arrowMap (S.rightMeshSourceIndexEquiv H z t).2 ≫
        eqToHom (congrArg S.almostSplitSkeleton.obj
          (S.rightMeshSourceIndexEquiv_fst H z t))) ≫
    (S.meshRightAlmostSplitAt z.1).decomposition.inv

@[reassoc (attr := simp)]
theorem rightMeshSourceMap_decomposition_π
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (t : (S.meshRightAlmostSplitAt z.1).index) :
    S.rightMeshSourceMap H arrowMap z ≫
        (S.meshRightAlmostSplitAt z.1).decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.almostSplitSkeleton.obj
            ((S.meshRightAlmostSplitAt z.1).label j)) t =
      arrowMap (S.rightMeshSourceIndexEquiv H z t).2 ≫
        eqToHom (congrArg S.almostSplitSkeleton.obj
          (S.rightMeshSourceIndexEquiv_fst H z t)) := by
  simp [rightMeshSourceMap, Category.assoc]

/-- The displayed middle at `z` has no nonzero map back to `tau z`.  This
version uses the uniform mesh middle, before simplifying it to the chosen
nonprojective almost-split middle. -/
theorem hom_meshRightMiddle_to_rightTranslation_eq_zero
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (f : (S.meshRightAlmostSplitAt z.1).middle ⟶
      S.fgObj (S.rightTranslationLabel z)) :
    f = 0 := by
  classical
  let B := S.meshRightAlmostSplitAt z.1
  letI : Fintype B.index := FintypeCat.fintype
  apply (cancel_epi B.decomposition.inv).1
  apply biproduct.hom_ext'
  intro t
  let b := S.rightMeshSourceIndexEquiv H z t
  have hlt :
      (S.directedLinearOrder H).lt (S.rightTranslationLabel z) (B.label t) := by
    simpa only [b, S.rightMeshSourceIndexEquiv_fst H z t] using
      S.meshArrow_lt H b.2
  change
    biproduct.ι (fun j ↦ S.fgObj (B.label j)) t ≫
        B.decomposition.inv ≫ f = 0
  simpa only [Category.assoc, comp_zero] using
    S.hom_eq_zero_of_lt H hlt
      (biproduct.ι (fun j ↦ S.fgObj (B.label j)) t ≫
        B.decomposition.inv ≫ f)

/-- In particular, the recursively assembled source map at a nonprojective
mesh is never split monic. -/
theorem rightMeshSourceMap_not_isSplitMono
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    ¬ IsSplitMono (S.rightMeshSourceMap H arrowMap z) := by
  intro hq
  let q := S.rightMeshSourceMap H arrowMap z
  letI : IsSplitMono q := hq
  let r : (S.meshRightAlmostSplitAt z.1).middle ⟶
      S.almostSplitSkeleton.obj (S.rightTranslationLabel z) := retraction q
  have hrzero : r = 0 :=
    S.hom_meshRightMiddle_to_rightTranslation_eq_zero H z r
  have hid : q ≫ r = 𝟙 _ := by
    dsimp only [r]
    exact IsSplitMono.id q
  rw [hrzero, comp_zero] at hid
  exact (S.fgObj_indecomposable (S.rightTranslationLabel z)).1
    ((IsZero.iff_id_eq_zero _).2 hid.symm)

/-- Fullness at the strict predecessors of `z` makes every map from
`tau z` to the displayed middle factor through the assembled source map.
This is Ringel's first-arrow matrix argument, with the total outgoing-arrow
family reindexed by the displayed middle occurrences. -/
theorem exists_rightMeshSourceMap_factor
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (i : S.almostSplitSkeleton.obj (S.rightTranslationLabel z) ⟶
      (S.meshRightAlmostSplitAt z.1).middle)
    (hfull : ∀ (y : Fin S.n),
      (S.directedLinearOrder H).lt y z.1 →
      ∀ f : S.almostSplitSkeleton.obj (S.rightTranslationLabel z) ⟶
          S.almostSplitSkeleton.obj y,
        ∃ p : MagnitudeConjecture.LinearPathCategory.obj k (Fin S.n)
              (S.rightTranslationLabel z) ⟶
            MagnitudeConjecture.LinearPathCategory.obj k (Fin S.n) y,
          (MagnitudeConjecture.LinearPathCategory.lift
            (k := k) S.almostSplitSkeleton.obj arrowMap).map p = f) :
    ∃ r : (S.meshRightAlmostSplitAt z.1).middle ⟶
        (S.meshRightAlmostSplitAt z.1).middle,
      S.rightMeshSourceMap H arrowMap z ≫ r = i := by
  classical
  let B := S.meshRightAlmostSplitAt z.1
  letI : Fintype B.index := FintypeCat.fintype
  let E := S.rightMeshSourceIndexEquiv H z
  letI (y : Fin S.n) : Fintype
      (S.MeshArrow y (S.rightTranslationLabel z)) :=
    S.meshArrowFintype y (S.rightTranslationLabel z)
  let F := MagnitudeConjecture.LinearPathCategory.lift
    (k := k) S.almostSplitSkeleton.obj arrowMap
  let targetMap (t : B.index) :
      S.almostSplitSkeleton.obj (S.rightTranslationLabel z) ⟶
        S.almostSplitSkeleton.obj (B.label t) :=
    i ≫ B.decomposition.hom ≫
      biproduct.π (fun j ↦ S.almostSplitSkeleton.obj (B.label j)) t
  have htarget_lt (t : B.index) :
      (S.directedLinearOrder H).lt (B.label t) z.1 :=
    S.meshArrow_lt H (S.meshMiddleIndexEquiv z.1 t).2
  let path (t : B.index) :
      MagnitudeConjecture.LinearPathCategory.obj k (Fin S.n)
          (S.rightTranslationLabel z) ⟶
        MagnitudeConjecture.LinearPathCategory.obj k (Fin S.n) (B.label t) :=
    Classical.choose (hfull (B.label t) (htarget_lt t) (targetMap t))
  have path_spec (t : B.index) : F.map (path t) = targetMap t :=
    Classical.choose_spec (hfull (B.label t) (htarget_lt t) (targetMap t))
  have htranslate_ne (t : B.index) :
      S.rightTranslationLabel z ≠ B.label t := by
    have hlt := S.meshArrow_lt H (E t).2
    have hlt' : (S.directedLinearOrder H).lt
        (S.rightTranslationLabel z) (B.label t) := by
      simpa only [E, S.rightMeshSourceIndexEquiv_fst H z t] using hlt
    intro hEq
    rw [← hEq] at hlt'
    have hirr := ((S.directedLinearOrder H).lt_iff_le_not_ge
      (S.rightTranslationLabel z) (S.rightTranslationLabel z)).1 hlt'
    exact hirr.2 hirr.1
  let coeff (t : B.index) :
      MagnitudeConjecture.LinearPathCategory.OutgoingCoefficient
        (k := k) (S.rightTranslationLabel z) (B.label t) :=
    Classical.choose
      (MagnitudeConjecture.LinearPathCategory.exists_eq_outgoingSum_of_ne
        (k := k) (htranslate_ne t) (path t))
  have coeff_spec (t : B.index) :
      path t = MagnitudeConjecture.LinearPathCategory.outgoingSum (coeff t) :=
    Classical.choose_spec
      (MagnitudeConjecture.LinearPathCategory.exists_eq_outgoingSum_of_ne
        (k := k) (htranslate_ne t) (path t))
  let coefficientMap (t : B.index)
      (a : MagnitudeConjecture.LinearPathCategory.OutgoingArrow
        (S.rightTranslationLabel z)) :
      S.almostSplitSkeleton.obj a.1 ⟶
        S.almostSplitSkeleton.obj (B.label t) :=
    F.map (coeff t a)
  let matrixEntry (s t : B.index) :
      S.almostSplitSkeleton.obj (B.label s) ⟶
        S.almostSplitSkeleton.obj (B.label t) :=
    eqToHom (congrArg S.almostSplitSkeleton.obj
        (S.rightMeshSourceIndexEquiv_fst H z s).symm) ≫
      coefficientMap t (E s)
  let component (t : B.index) :
      B.middle ⟶ S.almostSplitSkeleton.obj (B.label t) :=
    B.decomposition.hom ≫ biproduct.desc (fun s ↦ matrixEntry s t)
  let r : B.middle ⟶ B.middle :=
    biproduct.lift component ≫ B.decomposition.inv
  refine ⟨r, ?_⟩
  apply (cancel_mono B.decomposition.hom).1
  apply biproduct.hom_ext
  intro t
  simp only [r, Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_π]
  change S.rightMeshSourceMap H arrowMap z ≫ component t = targetMap t
  dsimp only [component]
  rw [← Category.assoc]
  dsimp only [rightMeshSourceMap]
  dsimp only [B]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_desc]
  change
    (∑ s : B.index,
      arrowMap (E s).2 ≫
        eqToHom (congrArg S.almostSplitSkeleton.obj
          (S.rightMeshSourceIndexEquiv_fst H z s)) ≫
        matrixEntry s t) = targetMap t
  have hreindex := E.sum_comp (fun a ↦
    arrowMap a.2 ≫ coefficientMap t a)
  have hcast (s : B.index) :
      eqToHom (congrArg S.almostSplitSkeleton.obj
          (S.rightMeshSourceIndexEquiv_fst H z s)) ≫
        eqToHom (congrArg S.almostSplitSkeleton.obj
          (S.rightMeshSourceIndexEquiv_fst H z s).symm) = 𝟙 _ := by
    simp
  have hcast_assoc (s : B.index) :
      eqToHom (congrArg S.almostSplitSkeleton.obj
          (S.rightMeshSourceIndexEquiv_fst H z s)) ≫
        eqToHom (congrArg S.almostSplitSkeleton.obj
          (S.rightMeshSourceIndexEquiv_fst H z s).symm) ≫
        coefficientMap t (E s) = coefficientMap t (E s) := by
    rw [← Category.assoc, hcast, Category.id_comp]
  dsimp only [matrixEntry]
  simp only [hcast_assoc]
  rw [hreindex]
  dsimp only [coefficientMap]
  have hsum :
      F.map (MagnitudeConjecture.LinearPathCategory.outgoingSum (coeff t)) =
        ∑ a, arrowMap a.2 ≫ F.map (coeff t a) :=
    MagnitudeConjecture.LinearPathCategory.lift_map_outgoingSum
      (k := k) S.almostSplitSkeleton.obj arrowMap (coeff t)
  rw [← path_spec t, coeff_spec t]
  exact hsum.symm

/-- The canonical identification from the chosen nonprojective
right-almost-split middle to the uniform displayed mesh middle. -/
def minimalToMeshRightMiddleIso
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (S.minimalRightAlmostSplitAt z.1).middle ≅
      (S.meshRightAlmostSplitAt z.1).middle :=
  eqToIso (congrArg
    (fun B : S.almostSplitSkeleton.MinimalRightAlmostSplitDecomposition z.1 ↦
      B.middle)
    (S.meshRightAlmostSplitAt_eq_of_not_projective z.1 z.2).symm)

/-- The actual kernel inclusion, transported to the uniform displayed mesh
middle used at both projective and nonprojective vertices. -/
def meshRightKernelMap
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.fgObj (S.rightTranslationLabel z) ⟶
      (S.meshRightAlmostSplitAt z.1).middle :=
  S.rightKernelMap z ≫ (S.minimalToMeshRightMiddleIso z).hom

/-- The chosen nonprojective right almost-split sink, transported out of the
uniform displayed mesh middle. -/
def meshRightSinkMap
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (S.meshRightAlmostSplitAt z.1).middle ⟶ S.fgObj z.1 :=
  (S.minimalToMeshRightMiddleIso z).inv ≫
    (S.minimalRightAlmostSplitAt z.1).map

/-- The transported displayed sink remains right almost split. -/
theorem meshRightSinkMap_rightAlmostSplit
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    IsRightAlmostSplit (S.meshRightSinkMap z) :=
  rightAlmostSplit_precomp_iso
    (S.minimalRightAlmostSplitAt z.1).rightAlmostSplit
    (S.minimalToMeshRightMiddleIso z).symm

/-- The transported kernel inclusion remains left almost split. -/
theorem meshRightKernelMap_leftAlmostSplit
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    IsLeftAlmostSplit (S.meshRightKernelMap z) :=
  leftAlmostSplit_postcomp_iso
    (S.rightKernelMap_leftAlmostSplit z)
    (S.minimalToMeshRightMiddleIso z)

/-- The transported kernel inclusion remains left minimal. -/
theorem meshRightKernelMap_leftMinimal
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    IsLeftMinimal (S.meshRightKernelMap z) :=
  leftMinimal_postcomp_iso
    (S.rightKernelMap_leftMinimal z)
    (S.minimalToMeshRightMiddleIso z)

/-- The transported kernel inclusion followed by the displayed sink map is
zero. -/
@[reassoc (attr := simp)]
theorem meshRightKernelMap_comp_map
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.meshRightKernelMap z ≫ S.meshRightSinkMap z = 0 := by
  dsimp only [meshRightKernelMap, meshRightSinkMap]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  change S.rightKernelMap z ≫
    (S.minimalRightAlmostSplitAt z.1).map = 0
  simp [rightKernelMap, Category.assoc]

/-- The transported AR kernel has the literal kernel factorization property
against the transported displayed sink. -/
theorem exists_comp_meshRightKernelMap_eq_of_comp_meshRightSinkMap_eq_zero
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    {X : FGModuleCat.{u} Aᵐᵒᵖ}
    (q : X ⟶ (S.meshRightAlmostSplitAt z.1).middle)
    (hq : q ≫ S.meshRightSinkMap z = 0) :
    ∃ t : X ⟶ S.fgObj (S.rightTranslationLabel z),
      t ≫ S.meshRightKernelMap z = q := by
  let B := S.minimalRightAlmostSplitAt z.1
  let m := S.minimalToMeshRightMiddleIso z
  let τe := S.rightTranslationKernelIso z
  have hq' : (q ≫ m.inv) ≫ B.map = 0 := by
    change q ≫ m.inv ≫ B.map = 0
    change q ≫ m.inv ≫ B.map = 0 at hq
    exact hq
  let t : X ⟶ S.fgObj (S.rightTranslationLabel z) :=
    kernel.lift B.map (q ≫ m.inv) hq' ≫ τe.hom
  have ht : t ≫ S.rightKernelMap z = q ≫ m.inv := by
    dsimp only [t, rightKernelMap]
    change
      (kernel.lift B.map (q ≫ m.inv) hq' ≫ τe.hom) ≫
          (τe.inv ≫ kernel.ι B.map) = q ≫ m.inv
    simp only [Category.assoc, Iso.hom_inv_id_assoc, kernel.lift_ι]
  refine ⟨t, ?_⟩
  dsimp only [meshRightKernelMap]
  rw [← Category.assoc, ht, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Once an automorphism identifies the actual AR kernel with an assembled
source map, the latter is the literal kernel of the correspondingly twisted
sink. -/
theorem exists_comp_rightMeshSourceMap_eq_of_normalization
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (e : (S.meshRightAlmostSplitAt z.1).middle ≅
      (S.meshRightAlmostSplitAt z.1).middle)
    (he : S.meshRightKernelMap z ≫ e.hom =
      S.rightMeshSourceMap H arrowMap z)
    {X : FGModuleCat.{u} Aᵐᵒᵖ}
    (q : X ⟶ (S.meshRightAlmostSplitAt z.1).middle)
    (hq : q ≫ e.inv ≫ S.meshRightSinkMap z = 0) :
    ∃ t : X ⟶ S.fgObj (S.rightTranslationLabel z),
      t ≫ S.rightMeshSourceMap H arrowMap z = q := by
  obtain ⟨t, ht⟩ :=
    S.exists_comp_meshRightKernelMap_eq_of_comp_meshRightSinkMap_eq_zero z
      (q ≫ e.inv) (by simpa only [Category.assoc] using hq)
  refine ⟨t, ?_⟩
  rw [← he, ← Category.assoc, ht, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Ringel's normalization step at a nonprojective vertex.  Fullness below
`z` compares the recursively assembled source map with the actual AR kernel
inclusion.  A finite-length automorphism of the displayed middle then makes
the mesh relation literal after twisting the displayed sink map. -/
theorem exists_rightMesh_normalization
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : ∀ {i j : Fin S.n}, S.MeshArrow i j →
      (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i))
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hfull : ∀ (y : Fin S.n),
      (S.directedLinearOrder H).lt y z.1 →
      ∀ f : S.almostSplitSkeleton.obj (S.rightTranslationLabel z) ⟶
          S.almostSplitSkeleton.obj y,
        ∃ p : MagnitudeConjecture.LinearPathCategory.obj k (Fin S.n)
              (S.rightTranslationLabel z) ⟶
            MagnitudeConjecture.LinearPathCategory.obj k (Fin S.n) y,
          (MagnitudeConjecture.LinearPathCategory.lift
            (k := k) S.almostSplitSkeleton.obj arrowMap).map p = f) :
    ∃ e : (S.meshRightAlmostSplitAt z.1).middle ≅
        (S.meshRightAlmostSplitAt z.1).middle,
      S.meshRightKernelMap z ≫ e.hom =
          S.rightMeshSourceMap H arrowMap z ∧
        S.rightMeshSourceMap H arrowMap z ≫ e.inv ≫
          S.meshRightSinkMap z = 0 := by
  exact exists_middleIso_normalizing_leftAlmostSplit
    (S.meshRightKernelMap z) (S.rightMeshSourceMap H arrowMap z)
    (S.meshRightSinkMap z)
    (S.meshRightAlmostSplitAt z.1).finiteLength
    (S.meshRightKernelMap_leftAlmostSplit z)
    (S.meshRightKernelMap_leftMinimal z)
    (S.rightMeshSourceMap_not_isSplitMono H arrowMap z)
    (S.exists_rightMeshSourceMap_factor H arrowMap z
      (S.meshRightKernelMap z) hfull)
    (S.meshRightKernelMap_comp_map z)

end FiniteIndecomposableSkeleton

end MagnitudeConjecture.RightModule
