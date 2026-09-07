import MagnitudeConjecture.Algebra.RightModulePrimitiveCrossingMesh
import MagnitudeConjecture.Algebra.RightModulePrimitiveProjectiveCount
import MagnitudeConjecture.Algebra.RightModulePrimitiveArrowDescent
import MagnitudeConjecture.CategoryTheory.FiniteTauAlmostSplitMultiplicity

/-!
# Direct arrow and mesh partitions for primitive deletion

This file formalizes the finite partitions used in the live manuscript's
direct count.  Every ambient arrow occurrence is internal to the killed
subcategory, internal to its complement, or crosses the boundary.  Every
ambient nonprojective mesh likewise has both translation endpoints killed,
both surviving, or on opposite sides.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace QuotientSubmoduleEquidistribution

universe v w

variable {C : Type v} [Category.{w} C]

/-- A right almost-split morphism remains right almost split after
restricting both endpoints to a full subcategory. -/
theorem IsRightAlmostSplit.fullSubcategory
    (P : ObjectProperty C) {X Y : P.FullSubcategory}
    (f : X ⟶ Y) (hf : IsRightAlmostSplit f.hom) :
    IsRightAlmostSplit f := by
  constructor
  · intro hsplit
    apply hf.not_isSplitEpi
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    exact IsSplitEpi.mk' {
      section_ := s.section_.hom
      id := congrArg (fun q ↦ q.hom) s.id }
  · intro Z g hg
    have hgAmbient : ¬ IsSplitEpi g.hom := by
      intro hsplit
      apply hg
      obtain ⟨s⟩ := hsplit.exists_splitEpi
      exact IsSplitEpi.mk' {
        section_ := ObjectProperty.homMk s.section_
        id := by
          apply ObjectProperty.hom_ext
          exact s.id }
    obtain ⟨h, hh⟩ := hf.factors g.hom hgAmbient
    refine ⟨ObjectProperty.homMk h, ?_⟩
    apply ObjectProperty.hom_ext
    exact hh

end QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : RightModule.PrimitiveIdempotentData e)

noncomputable local instance primitiveDirectCountQuotientFintype :
    Fintype (S.PrimitiveQuotientLabel D) :=
  Fintype.ofFinite _

/-- All ambient Auslander--Reiten arrow occurrences, with parallel arrows
retained. -/
abbrev AmbientArrowOccurrence :=
  Σ target : Fin S.n, Σ source : Fin S.n, S.MeshArrow target source

/-- Ambient arrows with both endpoints in the primitive quotient
subcategory `mod (A/AeA)`. -/
abbrev PrimitiveKilledInternalArrow :=
  {a : S.AmbientArrowOccurrence //
    a.1 ∈ S.primitiveKilledLabels D ∧
      a.2.1 ∈ S.primitiveKilledLabels D}

/-- Internal ambient arrow occurrences, reindexed by the literal quotient
labels at their two endpoints. -/
def primitiveKilledInternalArrowEquiv :
    S.PrimitiveKilledInternalArrow D ≃
      Σ target : S.PrimitiveQuotientLabel D,
        Σ source : S.PrimitiveQuotientLabel D,
          S.MeshArrow target.1 source.1 where
  toFun a :=
    ⟨⟨a.1.1, a.2.1⟩, ⟨⟨a.1.2.1, a.2.2⟩, a.1.2.2⟩⟩
  invFun a :=
    ⟨⟨a.1.1, ⟨a.2.1.1, a.2.2⟩⟩, a.1.2, a.2.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The official ambient arrow multiplicity is the cardinality of the chosen
ambient mesh-arrow occurrence type. -/
theorem arrowMultiplicity_eq_card_meshArrow
    (source target : Fin S.n) :
    MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target =
      Nat.card (S.MeshArrow target source) := by
  classical
  let B := S.meshRightAlmostSplitAt target
  rw [← S.indecomposableMultiplicity_meshRightMiddle source target]
  rw [S.indecomposableMultiplicity_eq_of_fintype_decomposition
    source B.middle B.decomposition]
  change (∑ i : B.index, if B.label i = source then 1 else 0) =
    Nat.card {i : B.index // B.label i = source}
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]

/-- For surviving labels, the ambient intrinsic irreducible-arrow
multiplicity is the cardinality of the chosen ambient mesh-arrow type. -/
theorem ambientIrreducibleArrowMultiplicity_eq_card_meshArrow
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (source target : S.PrimitiveQuotientLabel D) :
    S.ambientIrreducibleArrowMultiplicity D source target =
      Nat.card (S.MeshArrow target.1 source.1) := by
  rw [S.ambientIrreducibleArrowMultiplicity_eq_arrowMultiplicity
      D H source target,
    S.arrowMultiplicity_eq_card_meshArrow source.1 target.1]

/-- The ambient-arrow count internal to `mod (A/AeA)` is the sum of the
ambient intrinsic arrow multiplicities over surviving endpoints. -/
theorem card_primitiveKilledInternalArrow_eq_sum_ambientMultiplicity
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    Nat.card (S.PrimitiveKilledInternalArrow D) =
      ∑ source : S.PrimitiveQuotientLabel D,
        ∑ target : S.PrimitiveQuotientLabel D,
          S.ambientIrreducibleArrowMultiplicity D source target := by
  classical
  calc
    Nat.card (S.PrimitiveKilledInternalArrow D) =
        Nat.card
          (Σ target : S.PrimitiveQuotientLabel D,
            Σ source : S.PrimitiveQuotientLabel D,
              S.MeshArrow target.1 source.1) :=
      Nat.card_congr (S.primitiveKilledInternalArrowEquiv D)
    _ = ∑ target : S.PrimitiveQuotientLabel D,
          Nat.card
            (Σ source : S.PrimitiveQuotientLabel D,
              S.MeshArrow target.1 source.1) := Nat.card_sigma
    _ = ∑ target : S.PrimitiveQuotientLabel D,
          ∑ source : S.PrimitiveQuotientLabel D,
            Nat.card (S.MeshArrow target.1 source.1) := by
      apply Finset.sum_congr rfl
      intro target _htarget
      exact Nat.card_sigma
    _ = ∑ target : S.PrimitiveQuotientLabel D,
          ∑ source : S.PrimitiveQuotientLabel D,
            S.ambientIrreducibleArrowMultiplicity D source target := by
      apply Finset.sum_congr rfl
      intro target _htarget
      apply Finset.sum_congr rfl
      intro source _hsource
      exact (S.ambientIrreducibleArrowMultiplicity_eq_card_meshArrow
        D H source target).symm
    _ = ∑ source : S.PrimitiveQuotientLabel D,
          ∑ target : S.PrimitiveQuotientLabel D,
            S.ambientIrreducibleArrowMultiplicity D source target := by
      rw [Finset.sum_comm]

/-- The official total ambient arrow count is the cardinality of all chosen
ambient mesh-arrow occurrences, with parallel arrows retained. -/
theorem ambientArrowCount_eq_card_ambientArrowOccurrence :
    MagnitudeConjecture.ARCount.arrowCount
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData) =
      (Nat.card S.AmbientArrowOccurrence : ℤ) := by
  classical
  calc
    MagnitudeConjecture.ARCount.arrowCount
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData) =
        ∑ target : Fin S.n, ∑ source : Fin S.n,
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            S.finiteTauCategoryData.toFiniteRightTauCategoryData
              source target : ℤ) := by
      rw [MagnitudeConjecture.ARCount.arrowCount, Finset.sum_comm]
    _ = ∑ target : Fin S.n, ∑ source : Fin S.n,
          (Nat.card (S.MeshArrow target source) : ℤ) := by
      apply Finset.sum_congr rfl
      intro target _htarget
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [S.arrowMultiplicity_eq_card_meshArrow source target]
    _ = ∑ target : Fin S.n,
          (Nat.card (Σ source : Fin S.n,
            S.MeshArrow target source) : ℤ) := by
      apply Finset.sum_congr rfl
      intro target _htarget
      rw [Nat.card_sigma]
      norm_cast
    _ = (Nat.card
        (Σ target : Fin S.n, Σ source : Fin S.n,
          S.MeshArrow target source) : ℤ) := by
      rw [Nat.card_sigma]
      norm_cast
    _ = (Nat.card S.AmbientArrowOccurrence : ℤ) := rfl

/-- Ambient arrows with both endpoints in the strict factor. -/
abbrev PrimitiveSurvivingInternalArrow :=
  {a : S.AmbientArrowOccurrence //
    a.1 ∉ S.primitiveKilledLabels D ∧
      a.2.1 ∉ S.primitiveKilledLabels D}

/-- Internal strict-factor arrow occurrences, reindexed by their surviving
endpoint labels. -/
def primitiveSurvivingInternalArrowEquiv :
    S.PrimitiveSurvivingInternalArrow D ≃
      Σ target : S.SurvivingLabel (S.primitiveKilledLabels D),
        Σ source : S.SurvivingLabel (S.primitiveKilledLabels D),
          S.MeshArrow target.1 source.1 where
  toFun a :=
    ⟨⟨a.1.1, a.2.1⟩, ⟨⟨a.1.2.1, a.2.2⟩, a.1.2.2⟩⟩
  invFun a :=
    ⟨⟨a.1.1, ⟨a.2.1.1, a.2.2⟩⟩, a.1.2, a.2.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The surviving summand indices in the ambient right-mesh middle term are
exactly its arrow occurrences whose source also survives. -/
def factorMiddleSurvivingIndexEquiv
    (target : S.SurvivingLabel (S.primitiveKilledLabels D)) :
    {i : (S.meshRightAlmostSplitAt target.1).index //
        (S.meshRightAlmostSplitAt target.1).label i ∉
          S.primitiveKilledLabels D} ≃
      Σ source : S.SurvivingLabel (S.primitiveKilledLabels D),
        S.MeshArrow target.1 source.1 where
  toFun i :=
    ⟨⟨(S.meshRightAlmostSplitAt target.1).label i.1, i.2⟩,
      ⟨i.1, rfl⟩⟩
  invFun a := ⟨a.2.1, by rw [a.2.2]; exact a.1.2⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨⟨source, hsource⟩, ⟨i, hi⟩⟩
    dsimp at hi
    subst source
    rfl

/-- The strict factor's right-mesh middle term, decomposed by the surviving
summands of the corresponding ambient right-mesh middle term. -/
def factorRightMiddleSurvivingDecomposition
    (target : S.SurvivingLabel (S.primitiveKilledLabels D)) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (((S.factorFiniteTauCategoryData
        (S.primitiveKilledLabels D)).rightMesh
          ((S.factorFiniteTauCategoryData
            (S.primitiveKilledLabels D)).obj target)).X₂) := by
  classical
  let K := S.primitiveKilledLabels D
  let B := S.meshRightAlmostSplitAt target.1
  let FM := S.factorModuleFunctor K
  let J := {i : B.index // B.label i ∉ K}
  let epsilon : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let label : Fin (Fintype.card J) → S.SurvivingLabel K :=
    fun t ↦ ⟨B.label (epsilon.symm t), (epsilon.symm t).2⟩
  let eAmbient : (S.labelRightMesh target.1).X₂ ≅
      ⨁ fun i : B.index ↦ S.fgObj (B.label i) :=
    (eqToIso (S.labelRightMesh_X₂ target.1)).trans B.decomposition
  let eAll : (S.factorRawRightMesh K target.1).X₂ ≅
      ⨁ fun i : B.index ↦ FM.obj (S.fgObj (B.label i)) :=
    (FM.mapIso eAmbient).trans
      (FM.mapBiproduct (fun i : B.index ↦ S.fgObj (B.label i)))
  let eDelete :
      (⨁ fun i : B.index ↦ FM.obj (S.fgObj (B.label i))) ≅
        ⨁ fun i : J ↦ FM.obj (S.fgObj (B.label i.1)) :=
    S.factorBiproductIsoSubtypeOfIsZero
      (fun i : B.index ↦ FM.obj (S.fgObj (B.label i)))
      (fun i ↦ B.label i ∉ K) (by
        intro i hi
        have hiK : B.label i ∈ K := not_not.mp hi
        exact (S.factorObject_isZero_of_mem K hiK).of_iso
          (S.factorAmbientPointIsoFactorModule K (B.label i)))
  let eReindex :
      (⨁ fun i : J ↦ FM.obj (S.fgObj (B.label i.1))) ≅
        ⨁ fun t : Fin (Fintype.card J) ↦
          S.factorObject K (label t) :=
    biproduct.whiskerEquiv epsilon
      (fun i : J ↦ eqToIso (by
        apply CategoryTheory.Quotient.ext
        apply ObjectProperty.FullSubcategory.ext
        simp [label, FM]
        rfl))
  have hcanonical :
      ((S.factorFiniteTauCategoryData K).rightMesh
        ((S.factorFiniteTauCategoryData K).obj target)).X₂ =
        (S.factorLabelRightMesh K target).X₂ := by
    change (S.canonicalFactorRightMesh K
      (S.factorObject K target)).X₂ = _
    rw [S.canonicalFactorRightMesh_at_label K target]
  exact {
    n := Fintype.card J
    summand := fun t ↦ S.factorObject K (label t)
    indecomposable := fun t ↦ S.factorObject_indecomposable K (label t)
    isoBiproduct :=
      (eqToIso hcanonical).trans
        ((eqToIso (S.factorLabelRightMesh_X₂ K target)).trans
          (eAll.trans (eDelete.trans eReindex))) }

/-- The total incoming multiplicity at a strict-factor vertex is the number
of surviving ambient arrow occurrences entering it. -/
theorem factorRightMiddleArity_eq_card_survivingMeshArrows
    (target : S.SurvivingLabel (S.primitiveKilledLabels D)) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        (S.factorFiniteTauCategoryData
          (S.primitiveKilledLabels D)).toFiniteRightTauCategoryData target =
      Nat.card
        (Σ source : S.SurvivingLabel (S.primitiveKilledLabels D),
          S.MeshArrow target.1 source.1) := by
  classical
  let K := S.primitiveKilledLabels D
  let T := (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData
  let d := S.factorRightMiddleSurvivingDecomposition D target
  have harity :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      T target d
        (MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit
          T target)
        (MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightMinimal
          T target)
  change MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity T target =
    Fintype.card
      {i : (S.meshRightAlmostSplitAt target.1).index //
        (S.meshRightAlmostSplitAt target.1).label i ∉ K} at harity
  calc
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity T target =
        Nat.card
          {i : (S.meshRightAlmostSplitAt target.1).index //
            (S.meshRightAlmostSplitAt target.1).label i ∉ K} := by
      rw [Nat.card_eq_fintype_card]
      exact harity
    _ = Nat.card
        (Σ source : S.SurvivingLabel K,
          S.MeshArrow target.1 source.1) :=
      Nat.card_congr (S.factorMiddleSurvivingIndexEquiv D target)

/-- The strict factor's official total arrow count is the cardinality of the
ambient arrow occurrences internal to the strict factor. -/
theorem factorArrowCount_eq_card_primitiveSurvivingInternalArrow :
    MagnitudeConjecture.ARCount.arrowCount
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          (S.factorFiniteTauCategoryData
            (S.primitiveKilledLabels D)).toFiniteRightTauCategoryData) =
      (Nat.card (S.PrimitiveSurvivingInternalArrow D) : ℤ) := by
  classical
  let K := S.primitiveKilledLabels D
  let T := (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData
  calc
    MagnitudeConjecture.ARCount.arrowCount
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T) =
        ∑ target : S.SurvivingLabel K,
          ∑ source : S.SurvivingLabel K,
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T source target : ℤ) := by
      rw [MagnitudeConjecture.ARCount.arrowCount, Finset.sum_comm]
    _ = ∑ target : S.SurvivingLabel K,
          (MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
            T target : ℤ) := by
      apply Finset.sum_congr rfl
      intro target _htarget
      exact_mod_cast
        MagnitudeConjecture.FiniteTauMatrix.sum_arrowMultiplicity_source
          T target
    _ = ∑ target : S.SurvivingLabel K,
          (Nat.card
            (Σ source : S.SurvivingLabel K,
              S.MeshArrow target.1 source.1) : ℤ) := by
      apply Finset.sum_congr rfl
      intro target _htarget
      rw [S.factorRightMiddleArity_eq_card_survivingMeshArrows D target]
    _ = (Nat.card
        (Σ target : S.SurvivingLabel K,
          Σ source : S.SurvivingLabel K,
            S.MeshArrow target.1 source.1) : ℤ) := by
      rw [Nat.card_sigma]
      norm_cast
    _ = (Nat.card (S.PrimitiveSurvivingInternalArrow D) : ℤ) := by
      rw [Nat.card_congr (S.primitiveSurvivingInternalArrowEquiv D)]

/-- The manuscript's three-region partition of ambient arrows. -/
def ambientArrowRegionEquiv :
    S.AmbientArrowOccurrence ≃
      S.PrimitiveKilledInternalArrow D ⊕
        (S.PrimitiveSurvivingInternalArrow D ⊕
          S.PrimitiveCrossingArrow D) := by
  classical
  refine
    { toFun := fun a ↦ ?_
      invFun := fun a ↦ ?_
      left_inv := ?_
      right_inv := ?_ }
  · by_cases htarget : a.1 ∈ S.primitiveKilledLabels D
    · by_cases hsource : a.2.1 ∈ S.primitiveKilledLabels D
      · exact Sum.inl ⟨a, htarget, hsource⟩
      · exact Sum.inr (Sum.inr (Sum.inl ⟨a, htarget, hsource⟩))
    · by_cases hsource : a.2.1 ∈ S.primitiveKilledLabels D
      · exact Sum.inr (Sum.inr (Sum.inr ⟨a, htarget, hsource⟩))
      · exact Sum.inr (Sum.inl ⟨a, htarget, hsource⟩)
  · rcases a with a | a
    · exact a.1
    · rcases a with a | a
      · exact a.1
      · rcases a with a | a <;> exact a.1
  · intro a
    dsimp
    split <;> split <;> rfl
  · rintro (a | a)
    · simp only [a.2.1, a.2.2, dite_true]
    · rcases a with a | a
      · simp only [a.2.1, a.2.2, dite_false]
      · rcases a with a | a
        · simp only [a.2.1, a.2.2, dite_true, dite_false]
        · simp only [a.2.1, a.2.2, dite_true, dite_false]

/-- The ambient arrow count is `a₀ + a_H + z`. -/
theorem card_ambientArrowOccurrence_eq_internal_add_crossing :
    Nat.card S.AmbientArrowOccurrence =
      Nat.card (S.PrimitiveKilledInternalArrow D) +
        Nat.card (S.PrimitiveSurvivingInternalArrow D) +
          Nat.card (S.PrimitiveCrossingArrow D) := by
  rw [Nat.card_congr (S.ambientArrowRegionEquiv D), Nat.card_sum,
    Nat.card_sum]
  omega

/-- An ambient projective label remains tau-projective in the strict
factor. -/
theorem factorProjective_of_ambient_projective
    (x : S.SurvivingLabel (S.primitiveKilledLabels D))
    (hx : Projective (S.fgObj x.1)) :
    (S.factorFiniteTauCategoryData
      (S.primitiveKilledLabels D)).IsProjective x := by
  let K := S.primitiveKilledLabels D
  have hraw : IsZero (S.factorRawRightMesh K x.1).X₁ :=
    (S.factorModuleFunctor K).map_isZero
      ((S.labelRightMesh_X₁_isZero_iff_projective x.1).2 hx)
  change IsZero
    (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁
  rw [S.canonicalFactorRightMesh_at_label K x]
  rw [show S.factorLabelRightMesh K x =
      S.factorZeroLeftRightMesh K x by
    simp only [factorLabelRightMesh, hraw, Or.inl, dite_true]]
  exact S.factorZeroObject_isZero K

/-- If the ambient translate of a surviving nonprojective label is killed,
that label is tau-projective in the strict factor. -/
theorem factorProjective_of_translation_killed
    (x : S.SurvivingLabel (S.primitiveKilledLabels D))
    (hx : ¬ Projective (S.fgObj x.1))
    (htranslate : S.rightTranslationLabel ⟨x.1, hx⟩ ∈
      S.primitiveKilledLabels D) :
    (S.factorFiniteTauCategoryData
      (S.primitiveKilledLabels D)).IsProjective x := by
  let K := S.primitiveKilledLabels D
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨x.1, hx⟩
  let y := S.rightTranslationLabel z
  let T := S.labelRightMesh x.1
  let eT : T.X₁ ≅ S.fgObj y := by
    simpa [T, labelRightMesh, hx, nonprojectiveRightMesh, z, y] using
      S.rightTranslationKernelIso z
  let eQ : (S.factorRawRightMesh K x.1).X₁ ≅
      (S.factorModuleFunctor K).obj (S.fgObj y) :=
    (S.factorModuleFunctor K).mapIso eT
  have hy : y ∈ K := by simpa only [K, y, z] using htranslate
  have htarget : IsZero ((S.factorModuleFunctor K).obj (S.fgObj y)) :=
    (S.factorObject_isZero_of_mem K hy).of_iso
      (S.factorAmbientPointIsoFactorModule K y)
  have hraw : IsZero (S.factorRawRightMesh K x.1).X₁ :=
    htarget.of_iso eQ
  change IsZero
    (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁
  rw [S.canonicalFactorRightMesh_at_label K x]
  rw [show S.factorLabelRightMesh K x =
      S.factorZeroLeftRightMesh K x by
    simp only [factorLabelRightMesh, hraw, Or.inl, dite_true]]
  exact S.factorZeroObject_isZero K

/-- A strict-factor label is tau-projective exactly at the ambient
projective boundary or when its ambient translate is killed. -/
theorem factorProjective_iff_ambient_projective_or_translation_killed
    (x : S.SurvivingLabel (S.primitiveKilledLabels D)) :
    (S.factorFiniteTauCategoryData
        (S.primitiveKilledLabels D)).IsProjective x ↔
      Projective (S.fgObj x.1) ∨
        ∃ hx : ¬ Projective (S.fgObj x.1),
          S.rightTranslationLabel ⟨x.1, hx⟩ ∈
            S.primitiveKilledLabels D := by
  constructor
  · intro hx
    exact
      PrimitiveMultiplicityInput.factorProjective_ambient_projective_or_translation_killed
        (S := S) (S.primitiveMultiplicityInput D) x hx
  · rintro (hx | ⟨hx, htranslate⟩)
    · exact S.factorProjective_of_ambient_projective D x hx
    · exact S.factorProjective_of_translation_killed D x hx htranslate

/-- Ambient nonprojective meshes whose two translation endpoints lie in the
strict factor. -/
abbrev PrimitiveSurvivingInternalMesh :=
  {z : {x : Fin S.n // ¬ Projective (S.fgObj x)} //
    z.1 ∉ S.primitiveKilledLabels D ∧
      S.rightTranslationLabel z ∉ S.primitiveKilledLabels D}

/-- Nonprojective strict-factor labels are precisely ambient meshes whose
two translation endpoints survive. -/
def factorNonprojectiveEquivPrimitiveSurvivingInternalMesh :
    {x : S.SurvivingLabel (S.primitiveKilledLabels D) //
      ¬ (S.factorFiniteTauCategoryData
        (S.primitiveKilledLabels D)).IsProjective x} ≃
      S.PrimitiveSurvivingInternalMesh D := by
  classical
  refine
    { toFun := fun x ↦ ?_
      invFun := fun z ↦ ?_
      left_inv := ?_
      right_inv := ?_ }
  · have hambient : ¬ Projective (S.fgObj x.1.1) := by
      intro hprojective
      exact x.2 (S.factorProjective_of_ambient_projective D x.1 hprojective)
    let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
      ⟨x.1.1, hambient⟩
    have htranslate : S.rightTranslationLabel z ∉
        S.primitiveKilledLabels D := by
      intro hkilled
      exact x.2
        (S.factorProjective_of_translation_killed D x.1 hambient hkilled)
    exact ⟨z, x.1.2, htranslate⟩
  · let x : S.SurvivingLabel (S.primitiveKilledLabels D) :=
      ⟨z.1.1, z.2.1⟩
    refine ⟨x, ?_⟩
    intro hfactor
    rcases
        (S.factorProjective_iff_ambient_projective_or_translation_killed
          D x).1 hfactor with hprojective | ⟨hnp, hkilled⟩
    · exact z.1.2 hprojective
    · exact z.2.2 (by simpa only [x] using hkilled)
  · rintro ⟨⟨x, hx⟩, hfactor⟩
    rfl
  · rintro ⟨⟨z, hz⟩, hendpoint, htranslate⟩
    rfl

/-- The `q-p` meshes of the strict primitive factor are exactly the
ambient meshes internal to the surviving region. -/
theorem card_factorNonprojective_eq_card_primitiveSurvivingInternalMesh :
    Nat.card
        {x : S.SurvivingLabel (S.primitiveKilledLabels D) //
          ¬ (S.factorFiniteTauCategoryData
            (S.primitiveKilledLabels D)).IsProjective x} =
      Nat.card (S.PrimitiveSurvivingInternalMesh D) :=
  Nat.card_congr
    (S.factorNonprojectiveEquivPrimitiveSurvivingInternalMesh D)

/-- Ambient nonprojective meshes whose two translation endpoints lie in the
primitive quotient subcategory. -/
abbrev PrimitiveKilledInternalMesh :=
  {z : {x : Fin S.n // ¬ Projective (S.fgObj x)} //
    z.1 ∈ S.primitiveKilledLabels D ∧
      S.rightTranslationLabel z ∈ S.primitiveKilledLabels D}

/-- An ambient-projective quotient label remains projective in the exact
full subcategory of modules annihilated by `AeA`. -/
theorem primitiveQuotientLabelObj_projective_of_ambient_projective
    (x : S.PrimitiveQuotientLabel D)
    (hx : Projective (S.fgObj x.1)) :
    Projective (S.primitiveQuotientLabelObj D x) := by
  constructor
  intro E Y f g _hg
  letI : Epi g.hom :=
    RightModule.primitiveQuotientSubcategory_epi_ambient e g
  obtain ⟨h, hh⟩ := hx.factors f.hom g.hom
  refine ⟨ObjectProperty.homMk h, ?_⟩
  apply ObjectProperty.hom_ext
  exact hh

/-- An ambient mesh with both translation endpoints in `mod (A/AeA)`
remains a right almost-split mesh there, so its endpoint is nonprojective
in the literal quotient subcategory. -/
theorem primitiveQuotientLabelObj_not_projective_of_internalMesh
    (z : S.PrimitiveKilledInternalMesh D) :
    ¬ Projective (S.primitiveQuotientLabelObj D
      ⟨z.1.1, z.2.1⟩) := by
  let B := S.minimalRightAlmostSplitAt z.1.1
  have hsource : RightModule.IsAnnihilatedBy
      (RightModule.primitiveIdeal e)
      (S.fgObj (S.rightTranslationLabel z.1)) :=
    (S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D _).1 z.2.2
  have htarget : RightModule.IsAnnihilatedBy
      (RightModule.primitiveIdeal e) (S.fgObj z.1.1) :=
    (S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D _).1 z.2.1
  have hmiddle : RightModule.IsAnnihilatedBy
      (RightModule.primitiveIdeal e) B.middle :=
    isAnnihilatedBy_primitiveIdeal_middle_of_exact D.idempotent
      (S.rightKernelMap z.1) B.map
      (S.rightKernelMap_functionExact z.1) hsource htarget
  let M : RightModule.PrimitiveQuotientSubcategory e :=
    ⟨B.middle, hmiddle⟩
  let N : RightModule.PrimitiveQuotientSubcategory e :=
    S.primitiveQuotientLabelObj D ⟨z.1.1, z.2.1⟩
  let g : M ⟶ N := ObjectProperty.homMk B.map
  have hgAS : IsRightAlmostSplit g :=
    B.rightAlmostSplit.fullSubcategory
      (RightModule.PrimitiveQuotientProperty e) g
  haveI : Epi B.map :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      S.almostSplitSkeleton B.map B.rightAlmostSplit z.1.2
  haveI : Epi g := by
    constructor
    intro Z f h hfh
    apply ObjectProperty.hom_ext
    apply (cancel_epi B.map).1
    exact congrArg (fun q ↦ q.hom) hfh
  exact IsRightAlmostSplit.not_projective_target g hgAS

/-- The nonprojective mesh endpoints of the literal primitive quotient. -/
abbrev PrimitiveQuotientNonprojectiveMesh :=
  {x : S.PrimitiveQuotientLabel D //
    ¬ Projective (S.primitiveQuotientLabelObj D x)}

/-- Every quotient mesh is either inherited from an ambient mesh with both
translation endpoints killed, or is new; the two cases are disjoint. -/
def primitiveQuotientNonprojectiveMeshEquiv :
    S.PrimitiveQuotientNonprojectiveMesh D ≃
      S.PrimitiveKilledInternalMesh D ⊕
        S.PrimitiveNewRightMeshEndpoint D := by
  classical
  refine
    { toFun := fun x ↦ ?_
      invFun := fun x ↦ ?_
      left_inv := ?_
      right_inv := ?_ }
  · have hambient : ¬ Projective (S.fgObj x.1.1) := by
      intro hprojective
      exact x.2
        (S.primitiveQuotientLabelObj_projective_of_ambient_projective
          D x.1 hprojective)
    let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
      ⟨x.1.1, hambient⟩
    by_cases htranslate : S.rightTranslationLabel z ∈
        S.primitiveKilledLabels D
    · exact Sum.inl ⟨z, x.1.2, htranslate⟩
    · exact Sum.inr {
        label := x.1
        ambient_nonprojective := hambient
        quotient_nonprojective := x.2
        translation_not_mem := htranslate }
  · rcases x with z | N
    · exact ⟨⟨z.1.1, z.2.1⟩,
        S.primitiveQuotientLabelObj_not_projective_of_internalMesh D z⟩
    · exact ⟨N.label, N.quotient_nonprojective⟩
  · intro x
    apply Subtype.ext
    dsimp
    split <;> rfl
  · rintro (z | N)
    · simp only [z.2.2, dite_true]
    · simp only [N.translation_not_mem, dite_false]

/-- The quotient mesh count is the number of inherited internal meshes plus
the number of genuinely new meshes. -/
theorem card_primitiveQuotientNonprojectiveMesh_eq_internal_add_new :
    Nat.card (S.PrimitiveQuotientNonprojectiveMesh D) =
      Nat.card (S.PrimitiveKilledInternalMesh D) +
        Nat.card (S.PrimitiveNewRightMeshEndpoint D) := by
  rw [Nat.card_congr (S.primitiveQuotientNonprojectiveMeshEquiv D),
    Nat.card_sum]

/-- The manuscript's three-region partition of ambient meshes. -/
def ambientMeshRegionEquiv :
    {x : Fin S.n // ¬ Projective (S.fgObj x)} ≃
      S.PrimitiveKilledInternalMesh D ⊕
        (S.PrimitiveSurvivingInternalMesh D ⊕
          S.PrimitiveBoundaryMesh D) := by
  classical
  refine
    { toFun := fun z ↦ ?_
      invFun := fun z ↦ ?_
      left_inv := ?_
      right_inv := ?_ }
  · by_cases hendpoint : z.1 ∈ S.primitiveKilledLabels D
    · by_cases htranslate :
          S.rightTranslationLabel z ∈ S.primitiveKilledLabels D
      · exact Sum.inl ⟨z, hendpoint, htranslate⟩
      · exact Sum.inr (Sum.inr (Sum.inl
          ⟨z, hendpoint, htranslate⟩))
    · by_cases htranslate :
          S.rightTranslationLabel z ∈ S.primitiveKilledLabels D
      · exact Sum.inr (Sum.inr (Sum.inr
          ⟨z, hendpoint, htranslate⟩))
      · exact Sum.inr (Sum.inl ⟨z, hendpoint, htranslate⟩)
  · rcases z with z | z
    · exact z.1
    · rcases z with z | z
      · exact z.1
      · rcases z with z | z <;> exact z.1
  · intro z
    dsimp
    split <;> split <;> rfl
  · rintro (z | z)
    · simp only [z.2.1, z.2.2, dite_true]
    · rcases z with z | z
      · simp only [z.2.1, z.2.2, dite_false]
      · rcases z with z | z
        · simp only [z.2.1, z.2.2, dite_true, dite_false]
        · simp only [z.2.1, z.2.2, dite_true, dite_false]

/-- The ambient mesh count is the sum of the two internal regions and the
boundary meshes. -/
theorem card_ambientNonprojective_eq_internalMesh_add_boundary :
    Nat.card {x : Fin S.n // ¬ Projective (S.fgObj x)} =
      Nat.card (S.PrimitiveKilledInternalMesh D) +
        Nat.card (S.PrimitiveSurvivingInternalMesh D) +
          Nat.card (S.PrimitiveBoundaryMesh D) := by
  rw [Nat.card_congr (S.ambientMeshRegionEquiv D), Nat.card_sum,
    Nat.card_sum]
  omega

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- The ambient labels split into the literal quotient labels and the
strict-factor labels. -/
theorem card_ambientVertex_eq_quotient_add_factor :
    Nat.card (Fin S.n) =
      Nat.card (S.PrimitiveQuotientLabel D) +
        Nat.card (S.SurvivingLabel (S.primitiveKilledLabels D)) := by
  classical
  rw [Nat.card_congr
      (Equiv.sumCompl
        (fun x : Fin S.n ↦ x ∈ S.primitiveKilledLabels D)).symm,
    Nat.card_sum]

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- Ambient vertices split into projective vertices and mesh endpoints. -/
theorem card_ambientVertex_eq_projective_add_nonprojective :
    Nat.card (Fin S.n) =
      Nat.card {x : Fin S.n // Projective (S.fgObj x)} +
        Nat.card {x : Fin S.n // ¬ Projective (S.fgObj x)} := by
  classical
  rw [Nat.card_congr
      (Equiv.sumCompl
        (fun x : Fin S.n ↦ Projective (S.fgObj x))).symm,
    Nat.card_sum]

/-- Literal quotient vertices split into projective vertices and mesh
endpoints. -/
theorem card_primitiveQuotientVertex_eq_projective_add_nonprojective :
    Nat.card (S.PrimitiveQuotientLabel D) =
      Nat.card {x : S.PrimitiveQuotientLabel D //
        Projective (S.primitiveQuotientLabelObj D x)} +
        Nat.card (S.PrimitiveQuotientNonprojectiveMesh D) := by
  classical
  rw [Nat.card_congr
      (Equiv.sumCompl
        (fun x : S.PrimitiveQuotientLabel D ↦
          Projective (S.primitiveQuotientLabelObj D x))).symm,
    Nat.card_sum]

/-- Strict-factor vertices split into tau-projectives and ambient meshes
internal to the surviving region. -/
theorem card_factorVertex_eq_projective_add_internalMesh :
    Nat.card (S.SurvivingLabel (S.primitiveKilledLabels D)) =
      Nat.card (S.FactorProjectiveLabel (S.primitiveKilledLabels D)) +
        Nat.card (S.PrimitiveSurvivingInternalMesh D) := by
  classical
  rw [Nat.card_congr
      (Equiv.sumCompl
        (S.factorFiniteTauCategoryData
          (S.primitiveKilledLabels D)).IsProjective).symm,
    Nat.card_sum,
    S.card_factorNonprojective_eq_card_primitiveSurvivingInternalMesh D]

/-- The complete primitive-projective presentation and the finite mesh
partitions give the manuscript's exact formula `r = z - (p - 1)`. -/
theorem card_primitiveNewRightMeshEndpoint_eq_crossing_sub_projectiveRemainder
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput (P.primitive p))) :
    (Nat.card (S.PrimitiveNewRightMeshEndpoint (P.primitive p)) : ℤ) =
      (Nat.card (S.PrimitiveCrossingArrow (P.primitive p)) : ℤ) -
        ((Nat.card
          (S.FactorProjectiveLabel
            (S.primitiveKilledLabels (P.primitive p))) : ℤ) - 1) := by
  let D := P.primitive p
  have hprojectiveDrop :=
    P.card_ambientProjective_eq_primitiveQuotientProjective_add_one H p
  have hvertices := S.card_ambientVertex_eq_quotient_add_factor D
  have hambientProjective :=
    S.card_ambientVertex_eq_projective_add_nonprojective
  have hquotientProjective :=
    S.card_primitiveQuotientVertex_eq_projective_add_nonprojective D
  have hfactorProjective :=
    S.card_factorVertex_eq_projective_add_internalMesh D
  have hambientMesh :=
    S.card_ambientNonprojective_eq_internalMesh_add_boundary D
  have hquotientMesh :=
    S.card_primitiveQuotientNonprojectiveMesh_eq_internal_add_new D
  have hcrossing :=
    S.card_primitiveCrossingArrow_eq_card_primitiveBoundaryMesh D H E
  have hverticesInt := congrArg (fun n : ℕ ↦ (n : ℤ)) hvertices
  have hprojectiveDropInt :=
    congrArg (fun n : ℕ ↦ (n : ℤ)) hprojectiveDrop
  have hambientProjectiveInt :=
    congrArg (fun n : ℕ ↦ (n : ℤ)) hambientProjective
  have hquotientProjectiveInt :=
    congrArg (fun n : ℕ ↦ (n : ℤ)) hquotientProjective
  have hfactorProjectiveInt :=
    congrArg (fun n : ℕ ↦ (n : ℤ)) hfactorProjective
  have hambientMeshInt :=
    congrArg (fun n : ℕ ↦ (n : ℤ)) hambientMesh
  have hquotientMeshInt :=
    congrArg (fun n : ℕ ↦ (n : ℤ)) hquotientMesh
  have hcrossingInt :=
    congrArg (fun n : ℕ ↦ (n : ℤ)) hcrossing
  norm_num at hverticesInt hprojectiveDropInt hambientProjectiveInt hquotientProjectiveInt hfactorProjectiveInt hambientMeshInt hquotientMeshInt hcrossingInt
  omega

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
