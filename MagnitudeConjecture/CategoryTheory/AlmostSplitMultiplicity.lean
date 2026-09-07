import MagnitudeConjecture.CategoryTheory.AlmostSplitShortExact
import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.AlmostSplitDuality
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecompositionUniqueness
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitUniqueness

/-!
# Incoming multiplicity from minimal right almost-split maps

The total incoming-arrow multiplicity at an indecomposable endpoint is the
number of indecomposable occurrences in the source of a minimal right
almost-split map.  Uniqueness of minimal right almost-split maps and finite
Krull--Schmidt cancellation make this number independent of the chosen map
and decomposition.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable [IsIdempotentComplete C]

/-- A minimal right almost-split map together with an explicit finite
indecomposable decomposition of its source and a bound on the number of
displayed summands. -/
structure RightAlmostSplitDecompositionBound (Y : C) (bound : ℕ) where
  source : C
  map : source ⟶ Y
  decomposition : FiniteIndecomposableDecomposition source
  rightAlmostSplit : IsRightAlmostSplit map
  rightMinimal : IsRightMinimal map
  arity_le : decomposition.n ≤ bound

/-- Enlarge the numerical bound without changing the displayed minimal
right almost-split map. -/
def RightAlmostSplitDecompositionBound.mono
    {Y : C} {m n : ℕ}
    (w : RightAlmostSplitDecompositionBound Y m) (h : m ≤ n) :
    RightAlmostSplitDecompositionBound Y n where
  source := w.source
  map := w.map
  decomposition := w.decomposition
  rightAlmostSplit := w.rightAlmostSplit
  rightMinimal := w.rightMinimal
  arity_le := w.arity_le.trans h

/-- Transport a bounded right almost-split witness across an isomorphism of
its endpoint. -/
def RightAlmostSplitDecompositionBound.postcompIso
    {Y Z : C} {bound : ℕ}
    (w : RightAlmostSplitDecompositionBound Y bound) (e : Y ≅ Z) :
    RightAlmostSplitDecompositionBound Z bound where
  source := w.source
  map := w.map ≫ e.hom
  decomposition := w.decomposition
  rightAlmostSplit := w.rightAlmostSplit.postcomp_iso e
  rightMinimal := IsRightMinimal.postcomp_iso e w.rightMinimal
  arity_le := w.arity_le

/-- A short exact sequence whose kernel has local endomorphism ring produces
a bounded minimal right almost-split witness as soon as its terminal map is
right almost split and its displayed middle decomposition has the required
size. -/
def ShortComplex.ShortExact.rightAlmostSplitDecompositionBound
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasFiniteBiproducts D] [HasBinaryBiproducts D]
    {S : ShortComplex D} (hS : S.ShortExact)
    [IsLocalRing (End S.X₁)] {bound : ℕ}
    (d : FiniteIndecomposableDecomposition S.X₂)
    (hAS : IsRightAlmostSplit S.g) (hn : d.n ≤ bound) :
    RightAlmostSplitDecompositionBound S.X₃ bound where
  source := S.X₂
  map := S.g
  decomposition := d
  rightAlmostSplit := hAS
  rightMinimal :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_local_end
      hS hAS.not_isSplitEpi
  arity_le := hn

/-- Two short exact realizations of minimal right almost-split maps with
isomorphic endpoints have isomorphic left terms.  This is the kernel-level
form of uniqueness of minimal right almost-split maps. -/
theorem nonempty_leftTermIso_of_shortExact_minimalRightAlmostSplit
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {S T : ShortComplex D}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (hSAS : IsRightAlmostSplit S.g) (hSmin : IsRightMinimal S.g)
    (hTAS : IsRightAlmostSplit T.g) (hTmin : IsRightMinimal T.g)
    (e₃ : S.X₃ ≅ T.X₃) : Nonempty (S.X₁ ≅ T.X₁) := by
  obtain ⟨e₂, he₂⟩ :=
    exists_rightAlmostSplit_middleIso
      (hSAS.postcomp_iso e₃) (IsRightMinimal.postcomp_iso e₃ hSmin)
      hTAS hTmin
  let eS : S.X₁ ≅ kernel S.g :=
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g)
      hS.fIsKernel).symm
  let eT : T.X₁ ≅ kernel T.g :=
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel T.g)
      hT.fIsKernel).symm
  let eK : kernel S.g ≅ kernel T.g :=
    kernel.mapIso S.g T.g e₂ e₃ he₂.symm
  exact ⟨eS ≪≫ eK ≪≫ eT.symm⟩

/-- The sources of two minimal right almost-split maps to the same endpoint
have finite indecomposable decompositions of the same size. -/
theorem FiniteIndecomposableDecomposition.n_eq_of_minimalRightAlmostSplit
    {E E' Y : C} {f : E ⟶ Y} {g : E' ⟶ Y}
    (d : FiniteIndecomposableDecomposition E)
    (d' : FiniteIndecomposableDecomposition E')
    (hlocal : ∀ i, IsLocalRing (End (d.summand i)))
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f)
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g) :
    d.n = d'.n := by
  obtain ⟨e, _⟩ :=
    exists_rightAlmostSplit_middleIso hf hfmin hg hgmin
  exact d.n_eq_of_iso d' hlocal e

omit [IsIdempotentComplete C] in
/-- If an additive functor preserves the displayed indecomposable summands
and carries a minimal right almost-split map to a minimal right almost-split
map, then the displayed source has the same number of occurrences as any
minimal right almost-split source at the image endpoint. -/
theorem FiniteIndecomposableDecomposition.n_eq_of_map_minimalRightAlmostSplit
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasFiniteBiproducts D] [HasBinaryBiproducts D]
    [IsIdempotentComplete D]
    (F : C ⥤ D) [F.Additive]
    {E Y : C} {f : E ⟶ Y}
    (d : FiniteIndecomposableDecomposition E)
    (hIndec : ∀ i, Indecomposable (F.obj (d.summand i)))
    (hlocal : ∀ i, IsLocalRing (End (F.obj (d.summand i))))
    {E' : D} {g : E' ⟶ F.obj Y}
    (d' : FiniteIndecomposableDecomposition E')
    (hf : IsRightAlmostSplit (F.map f))
    (hfmin : IsRightMinimal (F.map f))
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g) :
    d.n = d'.n := by
  let dMap := d.mapOfIndecomposable F hIndec
  have h := dMap.n_eq_of_minimalRightAlmostSplit d' hlocal
    hf hfmin hg hgmin
  exact h

omit [IsIdempotentComplete C] in
/-- If the cokernel of the anti-equivalent image of a minimal right
almost-split map has a bounded minimal right almost-split source, then the
original displayed source has the same bound.  This is the categorical
rotation used to transfer a right-mesh arity estimate through coefficient
duality. -/
theorem FiniteIndecomposableDecomposition.n_le_of_mapOp_cokernel_bound
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasFiniteBiproducts D] [HasBinaryBiproducts D]
    [IsIdempotentComplete D]
    (E : Cᵒᵖ ≌ D) [E.functor.Additive]
    {X Y : C} {f : X ⟶ Y} [Epi f]
    (d : FiniteIndecomposableDecomposition X)
    (hYindec : Indecomposable (E.functor.obj (Opposite.op Y)))
    (hYlocal : IsLocalRing
      (End (E.functor.obj (Opposite.op Y))))
    (hIndec : ∀ i,
      Indecomposable (E.functor.obj (Opposite.op (d.summand i))))
    (hlocal : ∀ i, IsLocalRing
      (End (E.functor.obj (Opposite.op (d.summand i)))))
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f)
    {bound : ℕ}
    (hbound : ∀ Z : D, Indecomposable Z → ¬ Projective Z →
      Nonempty (RightAlmostSplitDecompositionBound Z bound)) :
    d.n ≤ bound := by
  let g : E.functor.obj (Opposite.op Y) ⟶
      E.functor.obj (Opposite.op X) := E.functor.map f.op
  letI : Mono g := by
    dsimp only [g]
    infer_instance
  have hgAS : IsLeftAlmostSplit g := hf.map_op_equivalence E
  have hgMin : IsLeftMinimal g := hfmin.map_op_equivalence E
  let q : E.functor.obj (Opposite.op X) ⟶ cokernel g := cokernel.π g
  have hqAS : IsRightAlmostSplit q :=
    leftAlmostSplit_cokernel_π_isRightAlmostSplit g hgAS hgMin
  let S : ShortComplex D :=
    ShortComplex.mk g q (cokernel.condition g)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel g }
  letI : IsLocalRing (End S.X₁) := hYlocal
  have hgRadical : IsRadicalMorphism g :=
    (isRadicalMorphism_iff_not_isSplitMono_of_local_end
      hYindec.1 g).2 hgAS.not_isSplitMono
  have hqMin : IsRightMinimal q :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_isRadicalMorphism_f
      hS hgRadical
  have hQindec : Indecomposable (cokernel g) :=
    IsRightAlmostSplit.target_indecomposable q hqAS
  have hQnonprojective : ¬ Projective (cokernel g) := by
    intro hQ
    letI : Projective (cokernel g) := hQ
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 (cokernel g)) q
    apply hqAS.not_isSplitEpi
    exact IsSplitEpi.mk' { section_ := s, id := hs }
  obtain ⟨w⟩ := hbound (cokernel g) hQindec hQnonprojective
  let dMap := d.mapOpOfIndecomposable E.functor hIndec
  have hn : dMap.n = w.decomposition.n :=
    dMap.n_eq_of_minimalRightAlmostSplit w.decomposition hlocal
      hqAS hqMin w.rightAlmostSplit w.rightMinimal
  exact hn.le.trans w.arity_le

end MagnitudeConjecture.CategoryTheory
