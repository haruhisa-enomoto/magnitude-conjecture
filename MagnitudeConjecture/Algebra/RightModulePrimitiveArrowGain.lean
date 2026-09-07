import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientSkeleton
import MagnitudeConjecture.Algebra.RightModulePrimitiveContragredientBoundary
import MagnitudeConjecture.Algebra.RightModulePrimitiveContragredientMultiplicity
import MagnitudeConjecture.Algebra.RightModulePrimitiveRelativeMesh
import QuotientSubmoduleEquidistribution.RepresentationTheory.LeftAROccurrenceBasis
import QuotientSubmoduleEquidistribution.RepresentationTheory.RightAROccurrenceBasis

/-!
# Global arrow gains under primitive deletion

The manuscript counts ordered pairs of surviving indecomposables whose
irreducible-arrow multiplicity increases after passing from `A` to `A/AeA`.
Both arrow multiplicities are defined intrinsically as dimensions of
`Irr = rad / rad²`, using the literal common label type supplied by the
primitive-quotient skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : PrimitiveIdempotentData e)
variable [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ]

/-- Ambient irreducible-arrow multiplicity between surviving labels. -/
def ambientIrreducibleArrowMultiplicity
    (x y : S.PrimitiveQuotientLabel D) : ℕ := by
  letI : ∀ i : Fin S.n, Module k (S.almostSplitSkeleton.obj i) :=
    fun i ↦ Module.restrictScalars k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i)
  letI : ∀ i : Fin S.n,
      IsScalarTower k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k Aᵐᵒᵖ
      (S.almostSplitSkeleton.obj i)
  exact Module.finrank k
    (S.almostSplitSkeleton.irreducibleHomSpace (K := k) x.1 y.1)

/-- Irreducible-arrow multiplicity inside the literal primitive quotient. -/
def primitiveQuotientIrreducibleArrowMultiplicity
    (x y : S.PrimitiveQuotientLabel D) : ℕ := by
  let sigma := S.primitiveQuotientAlmostSplitSkeleton D
  letI : ∀ i : S.PrimitiveQuotientLabel D,
      Module k (sigma.obj i) :=
    fun i ↦ Module.restrictScalars k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i)
  letI : ∀ i : S.PrimitiveQuotientLabel D,
      IsScalarTower k
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i)
  exact Module.finrank k
    ((S.primitiveQuotientAlmostSplitSkeleton D).irreducibleHomSpace
      (K := k) x y)

/-- The multiplicity gained by an ordered pair after primitive deletion. -/
def primitiveArrowGain (x y : S.PrimitiveQuotientLabel D) : ℕ :=
  S.primitiveQuotientIrreducibleArrowMultiplicity D x y -
    S.ambientIrreducibleArrowMultiplicity D x y

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
/-- Every endomorphism of a quotient-skeleton representative is scalar.
This is transported from the literal ambient representative through the
linear quotient equivalence. -/
theorem primitiveQuotient_endomorphism_eq_smul_id [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : S.PrimitiveQuotientLabel D)
    (f : S.primitiveQuotientFGObj D x ⟶
      S.primitiveQuotientFGObj D x) :
    ∃ a : k, a • 𝟙 (S.primitiveQuotientFGObj D x) = f := by
  let E := RightModule.primitiveQuotientEquivalence (k := k) e
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  let g := E.functor.preimage f
  obtain ⟨a, ha⟩ := H.endomorphism_eq_smul_id S x.1 (U.map g)
  have hg : a • 𝟙 (S.primitiveQuotientLabelObj D x) = g := by
    apply U.map_injective
    change a • 𝟙 (S.fgObj x.1) = U.map g
    exact ha
  refine ⟨a, ?_⟩
  have hmap := congrArg E.functor.map hg
  rw [E.functor.map_smul, E.functor.map_id,
    E.functor.map_preimage] at hmap
  exact hmap

/-- The Hoshino quotient mesh equipped with the ambient middle term's chosen
decomposition, now relabeled by literal surviving quotient labels. -/
def primitiveQuotientMinimalRightAlmostSplitDecomposition
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (S.primitiveQuotientAlmostSplitSkeleton D)
      |>.MinimalRightAlmostSplitDecomposition N.label := by
  classical
  let E := RightModule.primitiveQuotientEquivalence (k := k) e
  let C := RightModule.PrimitiveQuotientSubcategory e
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence E.functor
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  let T := N.quotientShortComplex
  let c := S.chosenLabelDecomposition N.middleModule
  let label : Fin c.n → S.PrimitiveQuotientLabel D := fun i ↦
    ⟨c.label i,
      S.chosenLabelDecomposition_label_mem_primitiveKilledLabels D
        N.middleModule
        (RightModule.primitiveTorsionFGObj_isAnnihilatedBy e
          (S.minimalRightAlmostSplitAt N.label.1).middle) i⟩
  letI : PreservesBiproduct
      (fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i)) U :=
    preservesBiproduct_of_preservesProduct U
  let dAmbient : U.obj T.X₂ ≅
      ⨁ fun i : Fin c.n ↦
        U.obj (S.primitiveQuotientLabelObj D (label i)) := c.iso
  let dSub : T.X₂ ≅
      ⨁ fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i) :=
    U.preimageIso (dAmbient.trans
      (U.mapBiproduct
        (fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i))).symm)
  letI : PreservesBiproduct
      (fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i))
      E.functor := preservesBiproduct_of_preservesProduct E.functor
  let dQuotient : E.functor.obj T.X₂ ≅
      ⨁ fun i : Fin c.n ↦ S.primitiveQuotientFGObj D (label i) :=
    (E.functor.mapIso dSub).trans
      (E.functor.mapBiproduct
        (fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i)))
  let hg := N.quotientShortComplex_g_minimalRightAlmostSplit H he
  exact {
    middle := E.functor.obj T.X₂
    finiteLength := fgModule_isFiniteLength (k := k)
      (A := RightModule.primitiveQuotientAlgebra e) (E.functor.obj T.X₂)
    map := E.functor.map T.g
    rightAlmostSplit := hg.1.map_equivalence E
    rightMinimal := hg.2.map_equivalence E
    index := FintypeCat.of (Fin c.n)
    label := label
    decomposition := dQuotient }

/-- The same Hoshino quotient mesh equipped as a minimal left almost-split
decomposition at its literal source label. -/
def primitiveQuotientMinimalLeftAlmostSplitDecomposition
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (S.primitiveQuotientAlmostSplitSkeleton D)
      |>.MinimalLeftAlmostSplitDecomposition (N.sourceLabel H he) := by
  classical
  let E := RightModule.primitiveQuotientEquivalence (k := k) e
  let C := RightModule.PrimitiveQuotientSubcategory e
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence E.functor
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  let T := N.quotientShortComplex
  let c := S.chosenLabelDecomposition N.middleModule
  let label : Fin c.n → S.PrimitiveQuotientLabel D := fun i ↦
    ⟨c.label i,
      S.chosenLabelDecomposition_label_mem_primitiveKilledLabels D
        N.middleModule
        (RightModule.primitiveTorsionFGObj_isAnnihilatedBy e
          (S.minimalRightAlmostSplitAt N.label.1).middle) i⟩
  letI : PreservesBiproduct
      (fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i)) U :=
    preservesBiproduct_of_preservesProduct U
  let dAmbient : U.obj T.X₂ ≅
      ⨁ fun i : Fin c.n ↦
        U.obj (S.primitiveQuotientLabelObj D (label i)) := c.iso
  let dSub : T.X₂ ≅
      ⨁ fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i) :=
    U.preimageIso (dAmbient.trans
      (U.mapBiproduct
        (fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i))).symm)
  letI : PreservesBiproduct
      (fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i))
      E.functor := preservesBiproduct_of_preservesProduct E.functor
  let dQuotient : E.functor.obj T.X₂ ≅
      ⨁ fun i : Fin c.n ↦ S.primitiveQuotientFGObj D (label i) :=
    (E.functor.mapIso dSub).trans
      (E.functor.mapBiproduct
        (fun i : Fin c.n ↦ S.primitiveQuotientLabelObj D (label i)))
  let eSourceSub : T.X₁ ≅
      S.primitiveQuotientLabelObj D (N.sourceLabel H he) :=
    ObjectProperty.isoMk _ (N.sourceIso H he)
  let eSource : S.primitiveQuotientFGObj D (N.sourceLabel H he) ≅
      E.functor.obj T.X₁ :=
    (E.functor.mapIso eSourceSub).symm
  let hf := N.quotientShortComplex_f_minimalLeftAlmostSplit H he
  exact {
    middle := E.functor.obj T.X₂
    finiteLength := fgModule_isFiniteLength (k := k)
      (A := RightModule.primitiveQuotientAlgebra e) (E.functor.obj T.X₂)
    map := eSource.hom ≫ E.functor.map T.f
    leftAlmostSplit :=
      (hf.1.map_equivalence E).precomp_iso eSource
    leftMinimal := (hf.2.map_equivalence E).precomp_iso eSource
    index := FintypeCat.of (Fin c.n)
    label := label
    decomposition := dQuotient }

/-- At a new quotient mesh, the intrinsic quotient `Irr` dimension is the
existing relative middle-term multiplicity. -/
theorem primitiveQuotientIrreducibleArrowMultiplicity_eq_relative
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (source : S.PrimitiveQuotientLabel D)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.primitiveQuotientIrreducibleArrowMultiplicity D source N.label =
      N.relativeArrowMultiplicity source := by
  classical
  let sigma := S.primitiveQuotientAlmostSplitSkeleton D
  letI : ∀ i : S.PrimitiveQuotientLabel D,
      Module k (sigma.obj i) :=
    fun i ↦ Module.restrictScalars k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i)
  letI : ∀ i : S.PrimitiveQuotientLabel D,
      IsScalarTower k
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i)
  let B := S.primitiveQuotientMinimalRightAlmostSplitDecomposition D H he N
  rw [show S.primitiveQuotientIrreducibleArrowMultiplicity D source N.label =
      Module.finrank k (sigma.irreducibleHomSpace (K := k) source N.label)
    from rfl]
  rw [sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence
    (K := k) B source
      (S.primitiveQuotient_endomorphism_eq_smul_id D H source)]
  let c := S.chosenLabelDecomposition N.middleModule
  rw [show N.relativeArrowMultiplicity source =
      ∑ i : Fin c.n, if c.label i = source.1 then 1 else 0 by
    exact S.indecomposableMultiplicity_eq_of_decomposition
      source.1 N.middleModule c.iso]
  dsimp [B, primitiveQuotientMinimalRightAlmostSplitDecomposition]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Subtype.ext_iff]
  rfl

/-- Reading the same quotient mesh from its left side identifies the
intrinsic arrow multiplicity out of its source with the same relative middle
multiplicity. -/
theorem primitiveQuotientIrreducibleArrowMultiplicity_eq_relative_left
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (target : S.PrimitiveQuotientLabel D) :
    S.primitiveQuotientIrreducibleArrowMultiplicity D
        (N.sourceLabel H he) target =
      N.relativeArrowMultiplicity target := by
  classical
  let sigma := S.primitiveQuotientAlmostSplitSkeleton D
  letI : ∀ i : S.PrimitiveQuotientLabel D,
      Module k (sigma.obj i) :=
    fun i ↦ Module.restrictScalars k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i)
  letI : ∀ i : S.PrimitiveQuotientLabel D,
      IsScalarTower k
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (sigma.obj i)
  let L := S.primitiveQuotientMinimalLeftAlmostSplitDecomposition D H he N
  rw [show S.primitiveQuotientIrreducibleArrowMultiplicity D
      (N.sourceLabel H he) target =
      Module.finrank k (sigma.irreducibleHomSpace (K := k)
        (N.sourceLabel H he) target) from rfl]
  rw [sigma.finrank_irreducibleHomSpace_eq_card_leftAROccurrence
    (K := k) L target
      (S.primitiveQuotient_endomorphism_eq_smul_id D H target)]
  let c := S.chosenLabelDecomposition N.middleModule
  rw [show N.relativeArrowMultiplicity target =
      ∑ i : Fin c.n, if c.label i = target.1 then 1 else 0 by
    exact S.indecomposableMultiplicity_eq_of_decomposition
      target.1 N.middleModule c.iso]
  dsimp [L, primitiveQuotientMinimalLeftAlmostSplitDecomposition]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Subtype.ext_iff]
  rfl

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
/-- The intrinsic irreducible-Hom dimension agrees with the official
finite-tau arrow multiplicity whenever the source endomorphisms are scalar.
This is the occurrence-basis comparison, including the projective boundary
mesh. -/
theorem finrank_irreducibleHomSpace_eq_arrowMultiplicity_of_scalarEndomorphisms
    (source target : Fin S.n)
    (hscalar : ∀ f : S.fgObj source ⟶ S.fgObj source,
      ∃ a : k, a • 𝟙 (S.fgObj source) = f) :
    Module.finrank k
        (S.almostSplitSkeleton.irreducibleHomSpace
          (K := k) source target) =
      MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target := by
  classical
  let sigma := S.almostSplitSkeleton
  letI : ∀ i : Fin S.n, Module k (sigma.obj i) :=
    fun i ↦ Module.restrictScalars k Aᵐᵒᵖ (sigma.obj i)
  letI : ∀ i : Fin S.n, IsScalarTower k Aᵐᵒᵖ (sigma.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k Aᵐᵒᵖ (sigma.obj i)
  let B := S.meshRightAlmostSplitAt target
  rw [sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence
    (K := k) B source hscalar]
  rw [← S.indecomposableMultiplicity_meshRightMiddle source target]
  rw [S.indecomposableMultiplicity_eq_of_fintype_decomposition
    source B.middle B.decomposition]
  change Nat.card {i : B.index // B.label i = source} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
/-- At every ambient endpoint, including the projective boundary, the
intrinsic ambient `Irr` dimension is the manuscript's ambient arrow
multiplicity. -/
theorem ambientIrreducibleArrowMultiplicity_eq_arrowMultiplicity
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (source target : S.PrimitiveQuotientLabel D) :
    S.ambientIrreducibleArrowMultiplicity D source target =
      MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
          source.1 target.1 := by
  exact S.finrank_irreducibleHomSpace_eq_arrowMultiplicity_of_scalarEndomorphisms
    source.1 target.1 (H.endomorphism_eq_smul_id S source.1)

/-- The manuscript's gaining pairs: ordered surviving labels whose arrow
multiplicity strictly increases in the primitive quotient. -/
abbrev PrimitiveGainingPair :=
  {p : S.PrimitiveQuotientLabel D × S.PrimitiveQuotientLabel D //
    S.ambientIrreducibleArrowMultiplicity D p.1 p.2 <
      S.primitiveQuotientIrreducibleArrowMultiplicity D p.1 p.2}

/-- The manuscript's gaining pair selected by a positive new mesh. -/
def positiveGainingPair [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (P : PrimitiveNewRightMeshEndpoint.PositiveEndpoint
      (S := S) (D := D)) :
    PrimitiveGainingPair (S := S) (D := D) := by
  let N := P.1
  let source := N.positiveSourceLabel B P.2
  refine ⟨(source, N.label), ?_⟩
  rw [S.ambientIrreducibleArrowMultiplicity_eq_arrowMultiplicity
    D H source N.label]
  rw [S.primitiveQuotientIrreducibleArrowMultiplicity_eq_relative
    D H he source N]
  exact N.positiveSourceLabel_strict_multiplicity B P.2

/-- Distinct positive new meshes select distinct gaining pairs, since the
second coordinate is the mesh endpoint. -/
theorem positiveGainingPair_injective [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    Function.Injective (S.positiveGainingPair D H he B) := by
  intro P Q h
  apply Subtype.ext
  apply PrimitiveNewRightMeshEndpoint.ext
  exact congrArg (fun p : PrimitiveGainingPair (S := S) (D := D) ↦
    p.1.2) h

/-- Positive new meshes inject into the manuscript's global gaining-pair
set. -/
theorem card_positiveEndpoint_le_card_primitiveGainingPair
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    Nat.card (PrimitiveNewRightMeshEndpoint.PositiveEndpoint
      (S := S) (D := D)) ≤
      Nat.card (PrimitiveGainingPair (S := S) (D := D)) :=
  Nat.card_le_card_of_injective (S.positiveGainingPair D H he B)
    (S.positiveGainingPair_injective D H he B)

/-- The manuscript's gaining pair selected from a new mesh whose
contragredient new mesh is positive.  Its source is the original new-mesh
source; its target is the dual of the positive source selected on the
opposite side.  This is the numerical core of the negative-mesh case, kept
separate from the marker-complement theorem that supplies dual positivity. -/
def negativeGainingPairOfContragredientPositive [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositiveOp : letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
        IsNoetherianRing.of_finite k _
      (N.contragredientNewMeshEndpoint H he).IsPositive) :
    PrimitiveGainingPair (S := S) (D := D) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra (MulOpposite.op e))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Sop := S.contragredientSkeleton
  let Hop := S.contragredientSkeleton_hasAcyclicNonzeroNonisomorphisms H
  let dualBoundary := PrimitiveDirectedBoundaryData.contragredient S D H E
  let Nop := N.contragredientNewMeshEndpoint H he
  let wop := Nop.positiveSourceLabel dualBoundary hpositiveOp
  let target := (S.contragredientPrimitiveQuotientLabelEquiv D).symm wop
  refine ⟨(N.sourceLabel H he, target), ?_⟩
  rw [S.ambientIrreducibleArrowMultiplicity_eq_arrowMultiplicity
    D H (N.sourceLabel H he) target]
  rw [S.primitiveQuotientIrreducibleArrowMultiplicity_eq_relative_left
    D H he N target]
  apply (N.contragredient_relative_gt_ambient_iff H he target).1
  simpa [Nop, wop, target, Hop,
    contragredientPrimitiveQuotientLabelEquiv] using
      Nop.positiveSourceLabel_strict_multiplicity dualBoundary hpositiveOp

/-- The negative primitive new meshes in the manuscript's sign convention.
-/
abbrev PrimitiveNewRightMeshEndpoint.NegativeEndpoint :=
  {N : S.PrimitiveNewRightMeshEndpoint D // ¬ N.IsPositive}

/-- The negative-side gaining-pair assignment.  Marker complement converts
the negative mesh to a positive dual mesh before the numerical construction
above is applied. -/
def negativeGainingPair [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (P : PrimitiveNewRightMeshEndpoint.NegativeEndpoint
      (S := S) (D := D)) :
    PrimitiveGainingPair (S := S) (D := D) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact S.negativeGainingPairOfContragredientPositive D H he E P.1
    (S.contragredientNewMeshEndpoint_isPositive_of_not_isPositive
      D H he B P.1 P.2)

/-- Distinct contragredient-positive meshes select distinct negative-side
gaining pairs, since their first coordinates are the original mesh sources. -/
theorem negativeGainingPair_injective [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    Function.Injective
      (S.negativeGainingPair D H he E B) := by
  intro P Q h
  apply Subtype.ext
  apply PrimitiveNewRightMeshEndpoint.sourceLabel_injective H he
  exact congrArg
    (fun p : PrimitiveGainingPair (S := S) (D := D) ↦ p.1.1) h

/-- Negative new meshes inject into the global gaining-pair set. -/
theorem card_negativeEndpoint_le_card_primitiveGainingPair
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    Nat.card (PrimitiveNewRightMeshEndpoint.NegativeEndpoint
      (S := S) (D := D)) ≤
      Nat.card (PrimitiveGainingPair (S := S) (D := D)) :=
  Nat.card_le_card_of_injective
    (S.negativeGainingPair D H he E B)
    (S.negativeGainingPair_injective D H he E B)

/-- The sign partition of the manuscript's primitive new meshes. -/
abbrev SignedNewMeshEndpoint :=
  PrimitiveNewRightMeshEndpoint.PositiveEndpoint (S := S) (D := D) ⊕
    PrimitiveNewRightMeshEndpoint.NegativeEndpoint (S := S) (D := D)

/-- Every new mesh belongs to exactly one of the positive and negative
parts. -/
def newMeshSignEquiv :
    S.PrimitiveNewRightMeshEndpoint D ≃
      SignedNewMeshEndpoint (S := S) (D := D) := by
  classical
  exact {
    toFun := fun N =>
      if h : N.IsPositive then Sum.inl ⟨N, h⟩ else Sum.inr ⟨N, h⟩
    invFun := fun P => P.elim Subtype.val Subtype.val
    left_inv := by
      intro N
      by_cases h : N.IsPositive <;> simp [h]
    right_inv := by
      intro P
      cases P with
      | inl P => simp [P.2]
      | inr P => simp [P.2] }

/-- The manuscript's gaining-pair assignment on the disjoint sign
partition. -/
def signedGainingPair [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    SignedNewMeshEndpoint (S := S) (D := D) →
      PrimitiveGainingPair (S := S) (D := D) :=
  Sum.elim (S.positiveGainingPair D H he B)
    (S.negativeGainingPair D H he E B)

/-- Positive and negative meshes cannot select the same gaining pair: the
first entry of a positive pair has a nonzero map from its inverse translate
to the deleted simple, whereas the first entry of a negative pair has none.
-/
theorem signedGainingPair_injective [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    Function.Injective
      (S.signedGainingPair D H he E B) := by
  intro P Q hPQ
  cases P with
  | inl P =>
      cases Q with
      | inl Q =>
          exact congrArg Sum.inl
            (S.positiveGainingPair_injective D H he B hPQ)
      | inr Q =>
          exfalso
          have hsource : P.1.positiveSourceLabel B P.2 =
              Q.1.sourceLabel H he :=
            congrArg
              (fun p : PrimitiveGainingPair (S := S) (D := D) => p.1.1)
              hPQ
          have hnoninjective :
              P.1.positiveSourceNoninjectiveLabel B P.2 =
                Q.1.sourceNoninjectiveLabel H he := by
            apply Subtype.ext
            exact congrArg
              (fun x : S.PrimitiveQuotientLabel D => x.1) hsource
          have hmarker :
              P.1.positiveSourceLeftMarkerAmbientLabel B P.2 =
                Q.1.leftMarkerAmbientLabel H he :=
            congrArg
              (fun x => ((S.rightTranslationEquiv).symm x).1)
              hnoninjective
          obtain ⟨f, hf⟩ :=
            P.1.exists_nonzero_positiveSourceMarker H B P.2
          have hzero : ∀ g : S.fgObj (Q.1.leftMarker H he).1 ⟶
              S.primitiveDeletedSimple D, g = 0 := by
            intro g
            by_contra hg
            apply Q.2
            exact (Q.1.hasComplementaryMarkers B H he).1 ⟨g, hg⟩
          let iMarker : S.fgObj (Q.1.leftMarker H he).1 ≅
              S.fgObj
                (P.1.positiveSourceLeftMarkerAmbientLabel B P.2) :=
            eqToIso (congrArg S.fgObj hmarker.symm)
          let f' : S.fgObj (Q.1.leftMarker H he).1 ⟶
              S.primitiveDeletedSimple D := iMarker.hom ≫ f
          have hf' : f' ≠ 0 := by
            intro hzero'
            apply hf
            apply (cancel_epi iMarker.hom).1
            simpa [f'] using hzero'
          exact hf' (hzero f')
  | inr P =>
      cases Q with
      | inl Q =>
          exfalso
          have hsource : Q.1.positiveSourceLabel B Q.2 =
              P.1.sourceLabel H he :=
            congrArg
              (fun p : PrimitiveGainingPair (S := S) (D := D) => p.1.1)
              hPQ.symm
          have hnoninjective :
              Q.1.positiveSourceNoninjectiveLabel B Q.2 =
                P.1.sourceNoninjectiveLabel H he := by
            apply Subtype.ext
            exact congrArg
              (fun x : S.PrimitiveQuotientLabel D => x.1) hsource
          have hmarker :
              Q.1.positiveSourceLeftMarkerAmbientLabel B Q.2 =
                P.1.leftMarkerAmbientLabel H he :=
            congrArg
              (fun x => ((S.rightTranslationEquiv).symm x).1)
              hnoninjective
          obtain ⟨f, hf⟩ :=
            Q.1.exists_nonzero_positiveSourceMarker H B Q.2
          have hzero : ∀ g : S.fgObj (P.1.leftMarker H he).1 ⟶
              S.primitiveDeletedSimple D, g = 0 := by
            intro g
            by_contra hg
            apply P.2
            exact (P.1.hasComplementaryMarkers B H he).1 ⟨g, hg⟩
          let iMarker : S.fgObj (P.1.leftMarker H he).1 ≅
              S.fgObj
                (Q.1.positiveSourceLeftMarkerAmbientLabel B Q.2) :=
            eqToIso (congrArg S.fgObj hmarker.symm)
          let f' : S.fgObj (P.1.leftMarker H he).1 ⟶
              S.primitiveDeletedSimple D := iMarker.hom ≫ f
          have hf' : f' ≠ 0 := by
            intro hzero'
            apply hf
            apply (cancel_epi iMarker.hom).1
            simpa [f'] using hzero'
          exact hf' (hzero f')
      | inr Q =>
          exact congrArg Sum.inr
            (S.negativeGainingPair_injective D H he E B hPQ)

/-- The manuscript's gaining-pair assignment on the original, unsigned new
mesh type. -/
def newMeshGainingPair [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    S.PrimitiveNewRightMeshEndpoint D →
      PrimitiveGainingPair (S := S) (D := D) :=
  S.signedGainingPair D H he E B ∘ S.newMeshSignEquiv D

/-- Distinct new meshes receive distinct gaining pairs. -/
theorem newMeshGainingPair_injective [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    Function.Injective
      (S.newMeshGainingPair D H he E B) :=
  (S.signedGainingPair_injective D H he E B).comp
    (S.newMeshSignEquiv D).injective

/-- The number of new meshes is at most the number of gaining pairs. -/
theorem card_primitiveNewRightMeshEndpoint_le_card_primitiveGainingPair
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    Nat.card (S.PrimitiveNewRightMeshEndpoint D) ≤
      Nat.card (PrimitiveGainingPair (S := S) (D := D)) :=
  Nat.card_le_card_of_injective
    (S.newMeshGainingPair D H he E B)
    (S.newMeshGainingPair_injective D H he E B)

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
/-- The manuscript's total arrow gain `c`.  The primitive quotient algebra is
finite-dimensional, so the routine noetherian instance is constructed
internally rather than exposed by this numerical invariant. -/
def primitiveTotalArrowGain : ℕ := by
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Fintype (S.PrimitiveQuotientLabel D) := Fintype.ofFinite _
  exact ∑ x : S.PrimitiveQuotientLabel D,
    ∑ y : S.PrimitiveQuotientLabel D, S.primitiveArrowGain D x y

noncomputable instance primitiveGainingPairFinite :
    Finite (PrimitiveGainingPair (S := S) (D := D)) := by
  infer_instance

/-- Every gaining pair contributes at least one to the total arrow gain. -/
theorem card_primitiveGainingPair_le_primitiveTotalArrowGain :
    Nat.card (PrimitiveGainingPair (S := S) (D := D)) ≤
      S.primitiveTotalArrowGain D := by
  classical
  letI : Fintype (S.PrimitiveQuotientLabel D) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  let P := {p : S.PrimitiveQuotientLabel D ×
      S.PrimitiveQuotientLabel D //
        S.ambientIrreducibleArrowMultiplicity D p.1 p.2 <
          S.primitiveQuotientIrreducibleArrowMultiplicity D p.1 p.2}
  change Fintype.card P ≤ _
  have hcard : Fintype.card P =
      ∑ x : S.PrimitiveQuotientLabel D,
        ∑ y : S.PrimitiveQuotientLabel D,
          if S.ambientIrreducibleArrowMultiplicity D x y <
              S.primitiveQuotientIrreducibleArrowMultiplicity D x y
            then 1 else 0 := by
    dsimp only [P]
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones,
      Finset.sum_filter, ← Finset.univ_product_univ,
      Finset.sum_product]
  rw [hcard]
  unfold primitiveTotalArrowGain primitiveArrowGain
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  by_cases hgain : S.ambientIrreducibleArrowMultiplicity D x y <
      S.primitiveQuotientIrreducibleArrowMultiplicity D x y
  · simp only [hgain, ↓reduceIte]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_iff_lt.mpr hgain)
  · simp [hgain]

/-- The manuscript's inequality `c ≥ r`: total arrow gain dominates the
number of primitive new meshes. -/
theorem card_primitiveNewRightMeshEndpoint_le_primitiveTotalArrowGain
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D)) :
    Nat.card (S.PrimitiveNewRightMeshEndpoint D) ≤
      S.primitiveTotalArrowGain D :=
  (S.card_primitiveNewRightMeshEndpoint_le_card_primitiveGainingPair
    D H he E B).trans
      (S.card_primitiveGainingPair_le_primitiveTotalArrowGain D)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
