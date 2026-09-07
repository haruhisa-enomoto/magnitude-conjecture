import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import MagnitudeConjecture.CategoryTheory.AlmostSplitShortExact
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitUniqueness
import QuotientSubmoduleEquidistribution.CategoryTheory.SplitMorphismComplement

/-!
# Almost-split maps from pullbacks

Pulling back an epimorphism along a morphism which does not lift through it
produces a right almost-split projection as soon as one right almost-split map
to the endpoint lifts into the pullback.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The complementary object attached to a split epimorphism is canonically
isomorphic to its kernel.  We keep this explicit bridge because split
complements are convenient for counting indecomposable summands, whereas
kernels are the objects naturally produced by pullback arguments. -/
noncomputable def splitEpiComplementIsoKernel
    {X Y : C} (g : X ⟶ Y) [IsSplitEpi g]
    (d : SplitEpiComplement g) :
    d.complement ≅ kernel g where
  hom := kernel.lift g d.inclusion d.inclusion_g
  inv := kernel.ι g ≫ d.projection
  hom_inv_id := by
    letI : IsSplitMono d.inclusion :=
      IsSplitMono.mk'
        { retraction := d.projection, id := d.inclusion_projection }
    apply (cancel_mono d.inclusion).1
    simp [Category.assoc, d.projection_inclusion]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι g)).1
    rw [Category.assoc, kernel.lift_ι]
    simp [Category.assoc, d.projection_inclusion]

/-- A split embedding of an object with local endomorphism ring into a binary
biproduct splits through at least one coordinate.  This is the two-summand
Krull--Schmidt step, stated without choosing decompositions. -/
theorem splitMono_fst_or_snd_of_splitMono_to_biprod
    {X Y Z : C} [IsLocalRing (End X)]
    (f : X ⟶ Y ⊞ Z) [IsSplitMono f] :
    IsSplitMono (f ≫ biprod.fst) ∨
      IsSplitMono (f ≫ biprod.snd) := by
  let a : X ⟶ Y := f ≫ biprod.fst
  let ar : Y ⟶ X := biprod.inl ≫ retraction f
  let b : X ⟶ Z := f ≫ biprod.snd
  let br : Z ⟶ X := biprod.inr ≫ retraction f
  have hsum : (End.of (a ≫ ar) : End X) + End.of (b ≫ br) = 1 := by
    apply End.ext
    change a ≫ ar + b ≫ br = 𝟙 X
    calc
      a ≫ ar + b ≫ br =
          f ≫ (biprod.fst ≫ biprod.inl +
            biprod.snd ≫ biprod.inr) ≫ retraction f := by
              simp only [a, ar, b, br, Category.assoc,
                Preadditive.comp_add, Preadditive.add_comp]
      _ = f ≫ retraction f := by rw [biprod.total]; simp
      _ = 𝟙 X := IsSplitMono.id f
  have hunit : IsUnit
      ((End.of (a ≫ ar) : End X) + End.of (b ≫ br)) := by
    rw [hsum]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit with ha | hb
  · have hai : IsIso (a ≫ ar) :=
      (isUnit_iff_isIso (a ≫ ar)).1 ha
    letI : IsIso (a ≫ ar) := hai
    exact Or.inl <| IsSplitMono.mk'
      { retraction := ar ≫ inv (a ≫ ar)
        id := by rw [← Category.assoc, IsIso.hom_inv_id] }
  · have hbi : IsIso (b ≫ br) :=
      (isUnit_iff_isIso (b ≫ br)).1 hb
    letI : IsIso (b ≫ br) := hbi
    exact Or.inr <| IsSplitMono.mk'
      { retraction := br ≫ inv (b ≫ br)
        id := by rw [← Category.assoc, IsIso.hom_inv_id] }

/-- If `q : P ⟶ Z` factors through `h : X ⟶ Z`, then its pullback
along `h` is the direct sum of `P` and `kernel h`.  The first summand is the
graph of the chosen factorization. -/
noncomputable def pullbackIsoBiprodKernelOfFac
    {P X Z : C} (q : P ⟶ Z) (h : X ⟶ Z) (s : P ⟶ X)
    (hs : s ≫ h = q) :
    pullback q h ≅ P ⊞ kernel h := by
  let graph : P ⟶ pullback q h :=
    pullback.lift (𝟙 P) s (by simpa only [Category.id_comp] using hs.symm)
  let kernelGraph : kernel h ⟶ pullback q h :=
    pullback.lift 0 (kernel.ι h) (by simp)
  let remainder : pullback q h ⟶ kernel h :=
    kernel.lift h
      (pullback.snd q h - pullback.fst q h ≫ s) (by
        rw [Preadditive.sub_comp, Category.assoc, hs,
          ← pullback.condition, sub_self])
  have graph_fst : graph ≫ pullback.fst q h = 𝟙 P :=
    pullback.lift_fst _ _ _
  have graph_snd : graph ≫ pullback.snd q h = s :=
    pullback.lift_snd _ _ _
  have kernelGraph_fst : kernelGraph ≫ pullback.fst q h = 0 :=
    pullback.lift_fst _ _ _
  have kernelGraph_snd : kernelGraph ≫ pullback.snd q h = kernel.ι h :=
    pullback.lift_snd _ _ _
  have remainder_ker : remainder ≫ kernel.ι h =
      pullback.snd q h - pullback.fst q h ≫ s :=
    kernel.lift_ι _ _ _
  refine
    { hom := biprod.lift (pullback.fst q h) remainder
      inv := biprod.desc graph kernelGraph
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · rw [biprod.lift_desc,
        Preadditive.add_comp, Category.id_comp]
      simp only [Category.assoc, graph_fst, kernelGraph_fst,
        Category.comp_id, comp_zero, add_zero]
    · rw [biprod.lift_desc,
        Preadditive.add_comp, Category.id_comp]
      simp only [Category.assoc, graph_snd, kernelGraph_snd,
        remainder_ker, add_sub_cancel]
  · apply biprod.hom_ext'
    · apply biprod.hom_ext
      · rw [biprod.inl_desc_assoc, Category.assoc,
          biprod.lift_fst, graph_fst]
        simp
      · rw [biprod.inl_desc_assoc, Category.assoc,
          biprod.lift_snd]
        simp only [Category.comp_id, biprod.inl_snd]
        apply (cancel_mono (kernel.ι h)).1
        rw [Category.assoc, remainder_ker, Preadditive.comp_sub,
          graph_snd, ← Category.assoc, graph_fst, Category.id_comp,
          sub_self, zero_comp]
    · apply biprod.hom_ext
      · rw [biprod.inr_desc_assoc, Category.assoc,
          biprod.lift_fst, kernelGraph_fst]
        simp
      · rw [biprod.inr_desc_assoc, Category.assoc,
          biprod.lift_snd]
        simp only [Category.comp_id, biprod.inr_snd]
        apply (cancel_mono (kernel.ι h)).1
        rw [Category.assoc, remainder_ker, Preadditive.comp_sub,
          kernelGraph_snd, ← Category.assoc, kernelGraph_fst, zero_comp,
          sub_zero, Category.id_comp]

/-- Isomorphic objects have isomorphic endomorphism rings. -/
def endomorphismRingEquivOfIso {X Y : C} (e : X ≅ Y) :
    End X ≃+* End Y :=
  { e.conj with
    map_add' := by
      intro f g
      apply End.ext
      change e.inv ≫ (End.asHom f + End.asHom g) ≫ e.hom =
        e.inv ≫ End.asHom f ≫ e.hom +
          e.inv ≫ End.asHom g ≫ e.hom
      simp only [Preadditive.comp_add, Preadditive.add_comp] }

/-- A right almost-split epimorphism is right minimal when the endomorphism
ring of its kernel is local. -/
theorem rightAlmostSplit_isRightMinimal_of_kernel_local
    {E Z : C} (f : E ⟶ Z) [Epi f]
    [IsLocalRing (End (kernel f))] (hf : IsRightAlmostSplit f) :
    IsRightMinimal f := by
  let S : ShortComplex C :=
    ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel (kernelIsKernel f) }
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_local_end
      hS hf.not_isSplitEpi

/-- The kernel of the pullback projection of a cokernel is canonically the
source of the original monomorphism. -/
noncomputable def pullbackCokernelKernelSourceIso
    {U P X : C} (g : U ⟶ P) [Mono g] (h : X ⟶ cokernel g) :
    U ≅ kernel (pullback.snd (cokernel.π g) h) := by
  let q := cokernel.π g
  let f := pullback.snd q h
  let sq : IsPullback (pullback.fst q h) f q h :=
    IsPullback.of_hasPullback q h
  let km : kernel f ⟶ kernel q :=
    kernel.map f q (pullback.fst q h) h sq.flip.w
  letI : IsIso km := isIso_kernel_map_of_isPullback sq.flip
  exact
    (QuotientSubmoduleEquidistribution.kernelCokernelIsoSource g).symm ≪≫
      (asIso km).symm

/-- The canonical kernel identification respects the map into the
projective object in the pullback square. -/
@[reassoc]
theorem pullbackCokernelKernelSourceIso_hom_comp_kernel_ι_comp_fst
    {U P X : C} (g : U ⟶ P) [Mono g] (h : X ⟶ cokernel g) :
    (pullbackCokernelKernelSourceIso g h).hom ≫
        kernel.ι (pullback.snd (cokernel.π g) h) ≫
        pullback.fst (cokernel.π g) h = g := by
  let q := cokernel.π g
  let f := pullback.snd q h
  let sq : IsPullback (pullback.fst q h) f q h :=
    IsPullback.of_hasPullback q h
  let km : kernel f ⟶ kernel q :=
    kernel.map f q (pullback.fst q h) h sq.flip.w
  letI : IsIso km := isIso_kernel_map_of_isPullback sq.flip
  have hkm : km ≫ kernel.ι q =
      kernel.ι f ≫ pullback.fst q h :=
    by simp [km]
  have hinv : inv km ≫ kernel.ι f ≫ pullback.fst q h =
      kernel.ι q := by
    apply (cancel_epi km).1
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, hkm]
  dsimp only [pullbackCokernelKernelSourceIso, Iso.trans_hom,
    Iso.symm_hom]
  simp only [Category.assoc]
  change (QuotientSubmoduleEquidistribution.kernelCokernelIsoSource g).inv ≫
      inv km ≫ kernel.ι f ≫ pullback.fst q h = g
  rw [hinv]
  have hx := limit.isoLimitCone_inv_π
    { cone := KernelFork.ofι g (cokernel.condition g)
      isLimit := Abelian.monoIsKernelOfCokernel
        (CokernelCofork.ofπ (cokernel.π g) (cokernel.condition g))
        (cokernelIsCokernel g) }
    WalkingParallelPair.zero
  change (QuotientSubmoduleEquidistribution.kernelCokernelIsoSource g).inv ≫
      kernel.ι (cokernel.π g) = g at hx
  simpa only [q] using hx

/-- If `q : P ⟶ Z` is epic, `h : X ⟶ Z` does not lift through `q`, and a
right almost-split map to `X` becomes liftable after composition with `h`,
then the pullback projection to `X` is right almost split. -/
theorem pullback_snd_isRightAlmostSplit_of_rightAlmostSplit_lifts
    {P Z X B : C} (q : P ⟶ Z) [Epi q] (h : X ⟶ Z)
    (hnot : ¬ ∃ a : X ⟶ P, a ≫ q = h)
    (d : B ⟶ X) (hd : IsRightAlmostSplit d)
    (a : B ⟶ P) (ha : a ≫ q = d ≫ h) :
    IsRightAlmostSplit (pullback.snd q h) := by
  let m : B ⟶ pullback q h := pullback.lift a d ha
  have hmd : m ≫ pullback.snd q h = d := pullback.lift_snd _ _ _
  constructor
  · intro hs
    letI : IsSplitEpi (pullback.snd q h) := hs
    apply hnot
    refine ⟨section_ (pullback.snd q h) ≫ pullback.fst q h, ?_⟩
    rw [Category.assoc, pullback.condition]
    simpa only [Category.assoc, IsSplitEpi.id_assoc]
  · intro Y f hf
    obtain ⟨e, he⟩ := hd.factors f hf
    exact ⟨e ≫ m, by rw [Category.assoc, hmd, he]⟩

end MagnitudeConjecture.CategoryTheory
