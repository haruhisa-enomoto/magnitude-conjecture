import MagnitudeConjecture.Algebra.RightModuleStandardMeshConstruction
import MagnitudeConjecture.Algebra.RightModuleStandardMeshGrading
import MagnitudeConjecture.Algebra.RightModuleIyamaBoundaryDefect
import MagnitudeConjecture.CategoryTheory.FiniteTauIrreducible
import MagnitudeConjecture.CategoryTheory.FiniteTauTranslationMultiplicity
import MagnitudeConjecture.Combinatorics.TranslationSliceCount

/-!
# Concrete level slices in a directed primitive factor

Ringel standardness supplies the literal factor path grading, and the
primitive poset-space realization concentrates every surviving indecomposable
in one degree.  This file removes the former presentation parameter from that
grading and records the finite level fibers used by the translation recurrence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The concrete path-length grading on the literal factor skeleton. -/
def standardFactorSkeletonHomGrading
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) :
    S.SkeletonHomGrading K :=
  (S.standardMeshPresentation H).factorSkeletonHomGrading
    (quiver := S.meshQuiver) (arrowFintype := S.meshArrowFintype)
      (T := S.rightMeshData H) K

variable {S}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

namespace PrimitiveDirectedBoundaryData

/-- The intrinsic level of a surviving indecomposable in the concrete
standard factor grading. -/
def standardFactorLevel
    (B : S.PrimitiveDirectedBoundaryData D)
    (x : S.SurvivingLabel K) : ℕ :=
  (S.standardFactorSkeletonHomGrading B.acyclic K).objLevel
    B.projectivePosetData B.acyclic
      (B.injective_multiplicity_eq_one D.sinkInjectiveLabel) x

/-- The length of the concrete grading is the level of the distinguished
sink. -/
def standardFactorLength
    (B : S.PrimitiveDirectedBoundaryData D) : ℕ :=
  B.standardFactorLevel D.sink

@[simp]
theorem standardFactorLevel_source
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.standardFactorLevel D.source = 0 := by
  exact (S.standardFactorSkeletonHomGrading B.acyclic K).objLevel_source_eq_zero
    B.projectivePosetData B.acyclic
      (B.injective_multiplicity_eq_one D.sinkInjectiveLabel)

@[simp]
theorem standardFactorLevel_sink
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.standardFactorLevel D.sink = B.standardFactorLength :=
  rfl

/-- Every surviving indecomposable lies at or below the distinguished sink. -/
theorem standardFactorLevel_le_length
    (B : S.PrimitiveDirectedBoundaryData D)
    (x : S.SurvivingLabel K) :
    B.standardFactorLevel x ≤ B.standardFactorLength := by
  exact (S.standardFactorSkeletonHomGrading B.acyclic K).objLevel_le_sink
    B.projectivePosetData B.acyclic
      (B.injective_multiplicity_eq_one D.sinkInjectiveLabel) x

/-- The source is the unique vertex at level zero. -/
theorem standardFactorLevel_eq_zero_iff
    (B : S.PrimitiveDirectedBoundaryData D)
    (x : S.SurvivingLabel K) :
    B.standardFactorLevel x = 0 ↔ x = D.source := by
  constructor
  · intro hx
    by_contra hxs
    obtain ⟨f, hf⟩ := B.projectivePosetData.exists_source_hom_ne_zero x
    have hniso : ¬ IsIso f := by
      intro hfi
      letI : IsIso f := hfi
      exact hxs (S.factorObject_skeletal K ⟨(asIso f).symm⟩)
    have hlt :=
      (S.standardFactorSkeletonHomGrading B.acyclic K).objLevel_lt_of_nonzero_not_isIso
        B.projectivePosetData B.acyclic
          (B.injective_multiplicity_eq_one D.sinkInjectiveLabel) f hf hniso
    change B.standardFactorLevel D.source < B.standardFactorLevel x at hlt
    rw [B.standardFactorLevel_source, hx] at hlt
    omega
  · rintro rfl
    exact B.standardFactorLevel_source

/-- The distinguished sink is the unique vertex at the top level. -/
theorem standardFactorLevel_eq_length_iff
    (B : S.PrimitiveDirectedBoundaryData D)
    (x : S.SurvivingLabel K) :
    B.standardFactorLevel x = B.standardFactorLength ↔ x = D.sink := by
  constructor
  · intro hx
    by_contra hxs
    have hfinrank : 0 < Module.finrank k
        (S.factorObject K x ⟶ S.factorObject K D.sink) := by
      rw [PrimitiveMultiplicityInput.factorHomTo_finrank_eq_multiplicity
        (S := S) D x]
      exact PrimitiveMultiplicityInput.multiplicity_pos (S := S) D x
    obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hfinrank
    have hniso : ¬ IsIso f := by
      intro hfi
      letI : IsIso f := hfi
      exact hxs (S.factorObject_skeletal K ⟨asIso f⟩)
    have hlt :=
      (S.standardFactorSkeletonHomGrading B.acyclic K).objLevel_lt_of_nonzero_not_isIso
        B.projectivePosetData B.acyclic
          (B.injective_multiplicity_eq_one D.sinkInjectiveLabel) f hf hniso
    change B.standardFactorLevel x < B.standardFactorLevel D.sink at hlt
    rw [hx, B.standardFactorLevel_sink] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  · rintro rfl
    rfl

/-- Every factor irreducible raises the concrete level by exactly one. -/
theorem standardFactorLevel_succ_of_irreducible
    (B : S.PrimitiveDirectedBoundaryData D)
    {x y : S.SurvivingLabel K}
    {f : S.factorObject K x ⟶ S.factorObject K y}
    (hfirr : IsIrreducibleMorphism f) :
    B.standardFactorLevel x + 1 = B.standardFactorLevel y := by
  let P := S.standardMeshPresentation B.acyclic
  let G := S.standardFactorSkeletonHomGrading B.acyclic K
  have hfne : f ≠ 0 := by
    intro hf
    subst f
    exact
      (MagnitudeConjecture.FiniteTauMatrix.not_isIrreducibleMorphism_of_mem_radical_mul
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData
        (zero_mem _)) hfirr
  have hdegree : f ∈ G.component x y 1 :=
    P.irreducible_mem_factorComponent_one
      (quiver := S.meshQuiver) (arrowFintype := S.meshArrowFintype)
      B.acyclic K
      B.projectivePosetData
      (B.injective_multiplicity_eq_one D.sinkInjectiveLabel) hfirr
  exact G.objLevel_add_degree_eq_of_mem B.projectivePosetData B.acyclic
    (B.injective_multiplicity_eq_one D.sinkInjectiveLabel) hfne hdegree

/-- Every occurrence in the chosen right-mesh middle decomposition lies
exactly one level below its endpoint. -/
theorem standardFactorLevel_rightMiddleLabel_succ
    (B : S.PrimitiveDirectedBoundaryData D)
    (Y : S.SurvivingLabel K)
    (i : Fin (MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Y)) :
    B.standardFactorLevel
          (MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel
            (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Y i) + 1 =
      B.standardFactorLevel Y := by
  exact B.standardFactorLevel_succ_of_irreducible
    (MagnitudeConjecture.FiniteTauMatrix.rightMiddleComponent_isIrreducible
      (S.factorFiniteTauCategoryData K) Y i)

/-- An official arrow multiplicity can be nonzero only between adjacent
concrete levels. -/
theorem factorArrowMultiplicity_eq_zero_of_level_ne
    (B : S.PrimitiveDirectedBoundaryData D)
    (X Y : S.SurvivingLabel K)
    (hlevel : B.standardFactorLevel X + 1 ≠
      B.standardFactorLevel Y) :
    MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y = 0 := by
  classical
  rw [MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  intro hi
  apply hlevel
  rw [← hi]
  exact B.standardFactorLevel_rightMiddleLabel_succ Y i

/-- Nonzero official arrow multiplicity forces adjacent levels. -/
theorem standardFactorLevel_succ_of_factorArrowMultiplicity_ne_zero
    (B : S.PrimitiveDirectedBoundaryData D)
    (X Y : S.SurvivingLabel K)
    (harrow : MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y ≠ 0) :
    B.standardFactorLevel X + 1 = B.standardFactorLevel Y := by
  by_contra hlevel
  exact harrow (B.factorArrowMultiplicity_eq_zero_of_level_ne X Y hlevel)

/-- Positive Auslander--Reiten translation lowers the concrete level by two. -/
theorem standardFactorLevel_tauPlus_add_two
    (B : S.PrimitiveDirectedBoundaryData D)
    (Y : (S.factorFiniteTauCategoryData K).Nonprojective) :
    B.standardFactorLevel
          ((S.factorFiniteTauCategoryData K).tauPlus Y) + 2 =
      B.standardFactorLevel Y.1 := by
  let T := S.factorFiniteTauCategoryData K
  have hpos :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_pos_of_nonprojective
      T Y
  let i : Fin (MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      T.toFiniteRightTauCategoryData Y.1) :=
    ⟨0, hpos⟩
  let M : S.SurvivingLabel K :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel
      T.toFiniteRightTauCategoryData Y.1 i
  have hleft : B.standardFactorLevel
        ((S.factorFiniteTauCategoryData K).tauPlus Y) + 1 =
      B.standardFactorLevel M :=
    B.standardFactorLevel_succ_of_irreducible
      (MagnitudeConjecture.FiniteTauMatrix.rightMiddleSourceComponent_isIrreducible
        T Y i)
  have hright : B.standardFactorLevel M + 1 =
      B.standardFactorLevel Y.1 :=
    B.standardFactorLevel_rightMiddleLabel_succ Y.1 i
  calc
    B.standardFactorLevel
          ((S.factorFiniteTauCategoryData K).tauPlus Y) + 2 =
        (B.standardFactorLevel
          ((S.factorFiniteTauCategoryData K).tauPlus Y) + 1) + 1 := by omega
    _ = B.standardFactorLevel M + 1 :=
      congrArg (fun n ↦ n + 1) hleft
    _ = B.standardFactorLevel Y.1 := hright

/-- The official factor-arrow multiplicities satisfy translation across a
mesh. -/
theorem factorArrowMultiplicity_eq_translation
    (_B : S.PrimitiveDirectedBoundaryData D)
    (X : (S.factorFiniteTauCategoryData K).Noninjective)
    (Y : S.SurvivingLabel K) :
    MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X.1 Y =
      MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Y
          ((S.factorFiniteTauCategoryData K).tauMinus X) := by
  exact MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity_eq_translation
    (S.factorFiniteTauCategoryData K) D.homMeshInverseData D.leftMesh_epi X Y

/-- Every vertex at level one is tau-projective. -/
theorem isProjective_of_standardFactorLevel_eq_one
    (B : S.PrimitiveDirectedBoundaryData D)
    (Y : S.SurvivingLabel K)
    (hlevel : B.standardFactorLevel Y = 1) :
    (S.factorFiniteTauCategoryData K).IsProjective Y := by
  by_contra hprojective
  have hshift := B.standardFactorLevel_tauPlus_add_two ⟨Y, hprojective⟩
  rw [hlevel] at hshift
  omega

/-- The finite type of vertices in one concrete level slice. -/
abbrev StandardFactorLevelVertex
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :=
  {x : S.SurvivingLabel K // B.standardFactorLevel x = j}

/-- Tau-projective vertices in one level. -/
abbrev StandardFactorProjectiveLevelVertex
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :=
  {x : B.StandardFactorLevelVertex j //
    (S.factorFiniteTauCategoryData K).IsProjective x.1}

/-- Non-tau-projective vertices in one level. -/
abbrev StandardFactorNonprojectiveLevelVertex
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :=
  {x : B.StandardFactorLevelVertex j //
    ¬ (S.factorFiniteTauCategoryData K).IsProjective x.1}

/-- Tau-injective vertices in one level. -/
abbrev StandardFactorInjectiveLevelVertex
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :=
  {x : B.StandardFactorLevelVertex j //
    (S.factorFiniteTauCategoryData K).IsInjective x.1}

/-- Non-tau-injective vertices in one level. -/
abbrev StandardFactorNoninjectiveLevelVertex
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :=
  {x : B.StandardFactorLevelVertex j //
    ¬ (S.factorFiniteTauCategoryData K).IsInjective x.1}

/-- Negative translation identifies the noninjective vertices at level `j`
with the nonprojective vertices two levels later. -/
def standardFactorTauMinusLevelEquiv
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :
    B.StandardFactorNoninjectiveLevelVertex j ≃
      B.StandardFactorNonprojectiveLevelVertex (j + 2) := by
  let T := S.factorFiniteTauCategoryData K
  let forward (x : B.StandardFactorNoninjectiveLevelVertex j) :
      B.StandardFactorNonprojectiveLevelVertex (j + 2) := by
    let X : T.Noninjective := ⟨x.1.1, x.2⟩
    let Y : T.Nonprojective := T.tauPlusEquiv.symm X
    refine ⟨⟨Y.1, ?_⟩, Y.2⟩
    have hshift := B.standardFactorLevel_tauPlus_add_two Y
    have hcancel : T.tauPlus Y = X.1 := by
      exact congrArg Subtype.val (T.tauPlusEquiv.apply_symm_apply X)
    have hshift' : B.standardFactorLevel X.1 + 2 =
        B.standardFactorLevel Y.1 := by
      rw [← hcancel]
      exact hshift
    have hxlevel : B.standardFactorLevel X.1 = j := x.1.2
    omega
  let inverse (Y : B.StandardFactorNonprojectiveLevelVertex (j + 2)) :
      B.StandardFactorNoninjectiveLevelVertex j := by
    let Yn : T.Nonprojective := ⟨Y.1.1, Y.2⟩
    let X : T.Noninjective := T.tauPlusEquiv Yn
    refine ⟨⟨X.1, ?_⟩, X.2⟩
    have hshift := B.standardFactorLevel_tauPlus_add_two Yn
    change B.standardFactorLevel X.1 = j
    change B.standardFactorLevel X.1 + 2 =
      B.standardFactorLevel (Y.1 : S.SurvivingLabel K) at hshift
    have hylevel :
        B.standardFactorLevel (Y.1 : S.SurvivingLabel K) = j + 2 :=
      Y.1.2
    omega
  exact
    { toFun := forward
      invFun := inverse
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        dsimp only [forward, inverse]
        exact congrArg Subtype.val
          (T.tauPlusEquiv.apply_symm_apply
            (⟨x.1.1, x.2⟩ : T.Noninjective))
      right_inv := by
        intro Y
        apply Subtype.ext
        apply Subtype.ext
        dsimp only [forward, inverse]
        exact congrArg Subtype.val
          (T.tauPlusEquiv.symm_apply_apply
            (⟨Y.1.1, Y.2⟩ : T.Nonprojective)) }

noncomputable instance standardFactorProjectiveLevelVertexFintype
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :
    Fintype (B.StandardFactorProjectiveLevelVertex j) :=
  Fintype.ofFinite _

noncomputable instance standardFactorNonprojectiveLevelVertexFintype
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :
    Fintype (B.StandardFactorNonprojectiveLevelVertex j) :=
  Fintype.ofFinite _

noncomputable instance standardFactorInjectiveLevelVertexFintype
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :
    Fintype (B.StandardFactorInjectiveLevelVertex j) :=
  Fintype.ofFinite _

noncomputable instance standardFactorNoninjectiveLevelVertexFintype
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :
    Fintype (B.StandardFactorNoninjectiveLevelVertex j) :=
  Fintype.ofFinite _

private theorem sum_eq_one_of_positive_weighted_sum_eq_one
    {ι : Type u} [Fintype ι]
    (a weight : ι → ℕ) (weight_pos : ∀ i, 0 < weight i)
    (hweighted : ∑ i, (a i : ℤ) * weight i = 1) :
    (∑ i, (a i : ℤ)) = 1 := by
  classical
  have hweightedNat : ∑ i, a i * weight i = 1 := by
    exact_mod_cast hweighted
  have hle : ∑ i, a i ≤ ∑ i, a i * weight i := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.le_mul_of_pos_right (a i) (weight_pos i)
  have hne : ∑ i, a i ≠ 0 := by
    intro hzero
    have ha : ∀ i, a i = 0 := by
      have hafun : a = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg
          (fun j ↦ Nat.zero_le (a j))).1 hzero
      exact fun i ↦ congrFun hafun i
    simp [ha] at hweightedNat
  have hsum : ∑ i, a i = 1 := by omega
  exact_mod_cast hsum

/-- A tau-projective vertex other than the distinguished source has exactly
one incoming official arrow occurrence. -/
theorem sum_factorArrowMultiplicity_source_eq_one_of_projective_ne_source
    (B : S.PrimitiveDirectedBoundaryData D)
    (Y : S.SurvivingLabel K)
    (hprojective : (S.factorFiniteTauCategoryData K).IsProjective Y)
    (hsource : Y ≠ D.source) :
    (∑ X, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y : ℤ)) = 1 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let weight : S.SurvivingLabel K → ℕ := fun X ↦ D.multiplicity X.1
  have hunit := D.meshUnitEquations.1 Y
  have hweightY : weight Y = 1 := by
    exact B.projective_multiplicity_eq_one ⟨Y, hprojective⟩
  have hweighted :
      ∑ X, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData X Y : ℤ) * weight X = 1 := by
    change MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight T
      (fun X ↦ (weight X : ℤ)) Y = if Y = D.source then 1 else 0 at hunit
    rw [MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight] at hunit
    simp_rw [MagnitudeConjecture.FiniteTauMatrix.meshMatrix_apply_of_projective
      T hprojective] at hunit
    simp only [mul_sub, Finset.sum_sub_distrib] at hunit
    have hindicator :
        ∑ X, (weight X : ℤ) * (if X = Y then 1 else 0) = weight Y := by
      simp
    rw [hindicator] at hunit
    simp [hsource, hweightY] at hunit
    simpa only [mul_comm] using (show
      ∑ X, (weight X : ℤ) *
          MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X Y = 1 by
        omega)
  exact sum_eq_one_of_positive_weighted_sum_eq_one
    (fun X ↦ MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X Y)
    weight
    (fun X ↦ PrimitiveMultiplicityInput.multiplicity_pos (S := S) D X)
    hweighted

/-- A tau-injective vertex other than the distinguished sink has exactly one
outgoing official arrow occurrence. -/
theorem sum_factorArrowMultiplicity_target_eq_one_of_injective_ne_sink
    (B : S.PrimitiveDirectedBoundaryData D)
    (X : S.SurvivingLabel K)
    (hinjective : (S.factorFiniteTauCategoryData K).IsInjective X)
    (hsink : X ≠ D.sink) :
    (∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y : ℤ)) = 1 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let weight : S.SurvivingLabel K → ℕ := fun Y ↦ D.multiplicity Y.1
  have hunit := D.meshUnitEquations.2 X
  have hweightX : weight X = 1 := by
    exact B.injective_multiplicity_eq_one ⟨X, hinjective⟩
  rw [MagnitudeConjecture.FiniteTauMatrix.meshRowWeight_eq_of_injective T
      (fun Y ↦ (weight Y : ℤ)) X hinjective] at hunit
  have hweighted :
      ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData X Y : ℤ) * weight Y = 1 := by
    simp [hsink, hweightX] at hunit
    omega
  exact sum_eq_one_of_positive_weighted_sum_eq_one
    (fun Y ↦ MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X Y)
    weight
    (fun Y ↦ PrimitiveMultiplicityInput.multiplicity_pos (S := S) D Y)
    hweighted

/-- Summing arrows into a vertex at level `j+1` may be restricted to sources
at level `j`. -/
theorem sum_factorArrowMultiplicity_source_level
    (B : S.PrimitiveDirectedBoundaryData D)
    (j : ℕ) (Y : S.SurvivingLabel K)
    (hY : B.standardFactorLevel Y = j + 1) :
    (∑ X : B.StandardFactorLevelVertex j,
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X.1 Y : ℤ)) =
      ∑ X, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y : ℤ) := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let p : S.SurvivingLabel K → Prop :=
    fun X ↦ B.standardFactorLevel X = j
  have hcomplement :
      (∑ X : {X : S.SurvivingLabel K // ¬ p X},
          MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X.1 Y : ℤ) =
        0 := by
    apply Finset.sum_eq_zero
    intro X hX
    have hlevel : B.standardFactorLevel X.1 + 1 ≠
        B.standardFactorLevel Y := by
      intro h
      apply X.2
      dsimp only [p]
      omega
    exact_mod_cast B.factorArrowMultiplicity_eq_zero_of_level_ne X.1 Y hlevel
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun X ↦ (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      T.toFiniteRightTauCategoryData X Y : ℤ))
  change (∑ X : B.StandardFactorLevelVertex j,
      (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X.1 Y : ℤ)) = _
  change (∑ X : {X : S.SurvivingLabel K // p X},
      (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X.1 Y : ℤ)) = _
  rw [← hsplit, hcomplement, add_zero]

/-- Summing arrows out of a vertex at level `j` may be restricted to targets
at level `j+1`. -/
theorem sum_factorArrowMultiplicity_target_level
    (B : S.PrimitiveDirectedBoundaryData D)
    (j : ℕ) (X : S.SurvivingLabel K)
    (hX : B.standardFactorLevel X = j) :
    (∑ Y : B.StandardFactorLevelVertex (j + 1),
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y.1 : ℤ)) =
      ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y : ℤ) := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let p : S.SurvivingLabel K → Prop :=
    fun Y ↦ B.standardFactorLevel Y = j + 1
  have hcomplement :
      (∑ Y : {Y : S.SurvivingLabel K // ¬ p Y},
          MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X Y.1 : ℤ) =
        0 := by
    apply Finset.sum_eq_zero
    intro Y hY
    have hlevel : B.standardFactorLevel X + 1 ≠
        B.standardFactorLevel Y.1 := by
      intro h
      apply Y.2
      dsimp only [p]
      omega
    exact_mod_cast B.factorArrowMultiplicity_eq_zero_of_level_ne X Y.1 hlevel
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun Y ↦ (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      T.toFiniteRightTauCategoryData X Y : ℤ))
  change (∑ Y : {Y : S.SurvivingLabel K // p Y},
      (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X Y.1 : ℤ)) = _
  rw [← hsplit, hcomplement, add_zero]

/-- Number of surviving indecomposables in a concrete level slice. -/
def standardFactorVertexCount
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) : ℤ :=
  Fintype.card (B.StandardFactorLevelVertex j)

/-- Number of tau-projective vertices in one level. -/
def standardFactorProjectiveCount
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) : ℤ :=
  Fintype.card (B.StandardFactorProjectiveLevelVertex j)

/-- Number of tau-injective vertices in one level. -/
def standardFactorInjectiveCount
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) : ℤ :=
  Fintype.card (B.StandardFactorInjectiveLevelVertex j)

/-- Total official arrow multiplicity between two adjacent concrete levels. -/
def standardFactorArrowCount
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) : ℤ :=
  ∑ X : B.StandardFactorLevelVertex j,
    ∑ Y : B.StandardFactorLevelVertex (j + 1),
      (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X.1 Y.1 : ℤ)

/-- The categorical translation equivalence gives the exact vertex part of
the manuscript's pruning/translation/attachment recurrence. -/
theorem standardFactorVertexCount_add_two
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ) :
    B.standardFactorVertexCount (j + 2) =
      B.standardFactorVertexCount j - B.standardFactorInjectiveCount j +
        B.standardFactorProjectiveCount (j + 2) := by
  classical
  let T := S.factorFiniteTauCategoryData K
  have hnoninjective :
      Fintype.card (B.StandardFactorNoninjectiveLevelVertex j) =
        Fintype.card (B.StandardFactorLevelVertex j) -
          Fintype.card (B.StandardFactorInjectiveLevelVertex j) :=
    Fintype.card_subtype_compl
      (fun x : B.StandardFactorLevelVertex j ↦ T.IsInjective x.1)
  have hnonprojective :
      Fintype.card (B.StandardFactorNonprojectiveLevelVertex (j + 2)) =
        Fintype.card (B.StandardFactorLevelVertex (j + 2)) -
          Fintype.card (B.StandardFactorProjectiveLevelVertex (j + 2)) :=
    Fintype.card_subtype_compl
      (fun x : B.StandardFactorLevelVertex (j + 2) ↦ T.IsProjective x.1)
  have hequiv :
      Fintype.card (B.StandardFactorNoninjectiveLevelVertex j) =
        Fintype.card (B.StandardFactorNonprojectiveLevelVertex (j + 2)) :=
    Fintype.card_congr (B.standardFactorTauMinusLevelEquiv j)
  have hinjectiveLe :
      Fintype.card (B.StandardFactorInjectiveLevelVertex j) ≤
        Fintype.card (B.StandardFactorLevelVertex j) :=
    Fintype.card_subtype_le _
  have hprojectiveLe :
      Fintype.card (B.StandardFactorProjectiveLevelVertex (j + 2)) ≤
        Fintype.card (B.StandardFactorLevelVertex (j + 2)) :=
    Fintype.card_subtype_le _
  have hj :
      Fintype.card (B.StandardFactorNoninjectiveLevelVertex j) +
          Fintype.card (B.StandardFactorInjectiveLevelVertex j) =
        Fintype.card (B.StandardFactorLevelVertex j) := by
    omega
  have hj2 :
      Fintype.card (B.StandardFactorNonprojectiveLevelVertex (j + 2)) +
          Fintype.card (B.StandardFactorProjectiveLevelVertex (j + 2)) =
        Fintype.card (B.StandardFactorLevelVertex (j + 2)) := by
    omega
  have hjZ :
      (Fintype.card (B.StandardFactorNoninjectiveLevelVertex j) : ℤ) +
          Fintype.card (B.StandardFactorInjectiveLevelVertex j) =
        Fintype.card (B.StandardFactorLevelVertex j) := by
    exact_mod_cast hj
  have hj2Z :
      (Fintype.card
          (B.StandardFactorNonprojectiveLevelVertex (j + 2)) : ℤ) +
          Fintype.card (B.StandardFactorProjectiveLevelVertex (j + 2)) =
        Fintype.card (B.StandardFactorLevelVertex (j + 2)) := by
    exact_mod_cast hj2
  have hequivZ :
      (Fintype.card (B.StandardFactorNoninjectiveLevelVertex j) : ℤ) =
        Fintype.card
          (B.StandardFactorNonprojectiveLevelVertex (j + 2)) := by
    exact_mod_cast hequiv
  simp only [standardFactorVertexCount, standardFactorInjectiveCount,
    standardFactorProjectiveCount]
  omega

/-- The official arrow counts satisfy the manuscript's
pruning/translation/attachment recurrence. -/
theorem standardFactorArrowCount_add_one
    (B : S.PrimitiveDirectedBoundaryData D) (j : ℕ)
    (hj : j + 1 < B.standardFactorLength) :
    B.standardFactorArrowCount (j + 1) =
      B.standardFactorArrowCount j - B.standardFactorInjectiveCount j +
        B.standardFactorProjectiveCount (j + 2) := by
  classical
  let T := S.factorFiniteTauCategoryData K
  letI : DecidablePred
      (fun X : B.StandardFactorLevelVertex j ↦ T.IsInjective X.1) :=
    Classical.decPred _
  let injectiveFintype : Fintype (B.StandardFactorInjectiveLevelVertex j) :=
    Subtype.fintype _
  letI := injectiveFintype
  let noninjectiveFintype :
      Fintype (B.StandardFactorNoninjectiveLevelVertex j) :=
    Subtype.fintype _
  letI := noninjectiveFintype
  letI : DecidablePred
      (fun Z : B.StandardFactorLevelVertex (j + 2) ↦ T.IsProjective Z.1) :=
    Classical.decPred _
  let projectiveFintype :
      Fintype (B.StandardFactorProjectiveLevelVertex (j + 2)) :=
    Subtype.fintype _
  letI := projectiveFintype
  let nonprojectiveFintype :
      Fintype (B.StandardFactorNonprojectiveLevelVertex (j + 2)) :=
    Subtype.fintype _
  letI := nonprojectiveFintype
  let injectiveArrows : ℤ :=
    ∑ X : B.StandardFactorInjectiveLevelVertex j,
      ∑ Y : B.StandardFactorLevelVertex (j + 1),
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData X.1.1 Y.1 : ℤ)
  let noninjectiveArrows : ℤ :=
    ∑ X : B.StandardFactorNoninjectiveLevelVertex j,
      ∑ Y : B.StandardFactorLevelVertex (j + 1),
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData X.1.1 Y.1 : ℤ)
  let projectiveArrows : ℤ :=
    ∑ Y : B.StandardFactorLevelVertex (j + 1),
      ∑ Z : B.StandardFactorProjectiveLevelVertex (j + 2),
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData Y.1 Z.1.1 : ℤ)
  let nonprojectiveArrows : ℤ :=
    ∑ Y : B.StandardFactorLevelVertex (j + 1),
      ∑ Z : B.StandardFactorNonprojectiveLevelVertex (j + 2),
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData Y.1 Z.1.1 : ℤ)
  have hsplitLeft :
      B.standardFactorArrowCount j = injectiveArrows + noninjectiveArrows := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun X : B.StandardFactorLevelVertex j ↦ T.IsInjective X.1)
      (fun X ↦ ∑ Y : B.StandardFactorLevelVertex (j + 1),
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData X.1 Y.1 : ℤ))
    simpa only [standardFactorArrowCount, injectiveArrows,
      noninjectiveArrows, T] using hsplit.symm
  have hsplitRight :
      B.standardFactorArrowCount (j + 1) =
        projectiveArrows + nonprojectiveArrows := by
    rw [standardFactorArrowCount]
    change (∑ Y : B.StandardFactorLevelVertex (j + 1),
      ∑ Z : B.StandardFactorLevelVertex ((j + 1) + 1),
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData Y.1 Z.1 : ℤ)) = _
    rw [show (j + 1) + 1 = j + 2 by omega]
    calc
      (∑ Y : B.StandardFactorLevelVertex (j + 1),
          ∑ Z : B.StandardFactorLevelVertex (j + 2),
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData Y.1 Z.1 : ℤ)) =
          ∑ Y : B.StandardFactorLevelVertex (j + 1),
            ((∑ Z : B.StandardFactorProjectiveLevelVertex (j + 2),
                (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                  T.toFiniteRightTauCategoryData Y.1 Z.1.1 : ℤ)) +
              ∑ Z : B.StandardFactorNonprojectiveLevelVertex (j + 2),
                (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                  T.toFiniteRightTauCategoryData Y.1 Z.1.1 : ℤ)) := by
            apply Finset.sum_congr rfl
            intro Y hY
            exact (Fintype.sum_subtype_add_sum_subtype
              (fun Z : B.StandardFactorLevelVertex (j + 2) ↦
                T.IsProjective Z.1)
              (fun Z ↦ (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                T.toFiniteRightTauCategoryData Y.1 Z.1 : ℤ))).symm
      _ = projectiveArrows + nonprojectiveArrows := by
        simp only [Finset.sum_add_distrib, projectiveArrows,
          nonprojectiveArrows]
  have hinjective :
      injectiveArrows = B.standardFactorInjectiveCount j := by
    dsimp only [injectiveArrows]
    calc
      (∑ X : B.StandardFactorInjectiveLevelVertex j,
          ∑ Y : B.StandardFactorLevelVertex (j + 1),
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData X.1.1 Y.1 : ℤ)) =
          ∑ _X : B.StandardFactorInjectiveLevelVertex j, (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro X hX
            have hsink : X.1.1 ≠ D.sink := by
              intro h
              have hxlevel : B.standardFactorLevel X.1.1 = j := X.1.2
              rw [h, B.standardFactorLevel_sink] at hxlevel
              omega
            calc
              (∑ Y : B.StandardFactorLevelVertex (j + 1),
                  (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                    T.toFiniteRightTauCategoryData X.1.1 Y.1 : ℤ)) =
                  ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                    T.toFiniteRightTauCategoryData X.1.1 Y : ℤ) :=
                B.sum_factorArrowMultiplicity_target_level j X.1.1 X.1.2
              _ = 1 :=
                B.sum_factorArrowMultiplicity_target_eq_one_of_injective_ne_sink
                  X.1.1 X.2 hsink
      _ = (@Fintype.card (B.StandardFactorInjectiveLevelVertex j)
          injectiveFintype : ℤ) := by simp
      _ = B.standardFactorInjectiveCount j := by
        rw [standardFactorInjectiveCount]
        exact_mod_cast (@Fintype.card_congr
          (B.StandardFactorInjectiveLevelVertex j)
          (B.StandardFactorInjectiveLevelVertex j)
          injectiveFintype
          (B.standardFactorInjectiveLevelVertexFintype j)
          (Equiv.refl _))
  have hprojective :
      projectiveArrows = B.standardFactorProjectiveCount (j + 2) := by
    dsimp only [projectiveArrows]
    rw [Finset.sum_comm]
    calc
      (∑ Z : B.StandardFactorProjectiveLevelVertex (j + 2),
          ∑ Y : B.StandardFactorLevelVertex (j + 1),
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData Y.1 Z.1.1 : ℤ)) =
          ∑ _Z : B.StandardFactorProjectiveLevelVertex (j + 2), (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro Z hZ
            have hsource : Z.1.1 ≠ D.source := by
              intro h
              have hzlevel : B.standardFactorLevel Z.1.1 = j + 2 := Z.1.2
              rw [h, B.standardFactorLevel_source] at hzlevel
              omega
            have hzlevel : B.standardFactorLevel Z.1.1 = (j + 1) + 1 := by
              simpa [Nat.add_assoc] using Z.1.2
            calc
              (∑ Y : B.StandardFactorLevelVertex (j + 1),
                  (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                    T.toFiniteRightTauCategoryData Y.1 Z.1.1 : ℤ)) =
                  ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                    T.toFiniteRightTauCategoryData Y Z.1.1 : ℤ) :=
                B.sum_factorArrowMultiplicity_source_level
                  (j + 1) Z.1.1 hzlevel
              _ = 1 :=
                B.sum_factorArrowMultiplicity_source_eq_one_of_projective_ne_source
                  Z.1.1 Z.2 hsource
      _ = (@Fintype.card (B.StandardFactorProjectiveLevelVertex (j + 2))
          projectiveFintype : ℤ) := by simp
      _ = B.standardFactorProjectiveCount (j + 2) := by
        rw [standardFactorProjectiveCount]
        exact_mod_cast (@Fintype.card_congr
          (B.StandardFactorProjectiveLevelVertex (j + 2))
          (B.StandardFactorProjectiveLevelVertex (j + 2))
          projectiveFintype
          (B.standardFactorProjectiveLevelVertexFintype (j + 2))
          (Equiv.refl _))
  have htranslation : noninjectiveArrows = nonprojectiveArrows := by
    let E := B.standardFactorTauMinusLevelEquiv j
    let translatedOutgoing
        (Z : B.StandardFactorNonprojectiveLevelVertex (j + 2)) : ℤ :=
      ∑ Y : B.StandardFactorLevelVertex (j + 1),
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData Y.1 Z.1.1 : ℤ)
    have hreindex :
        (∑ X : B.StandardFactorNoninjectiveLevelVertex j,
            translatedOutgoing (E X)) =
          ∑ Z : B.StandardFactorNonprojectiveLevelVertex (j + 2),
            translatedOutgoing Z :=
      E.sum_comp translatedOutgoing
    calc
      noninjectiveArrows =
          ∑ X : B.StandardFactorNoninjectiveLevelVertex j,
            ∑ Y : B.StandardFactorLevelVertex (j + 1),
              (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                T.toFiniteRightTauCategoryData Y.1 (T.tauMinus ⟨X.1.1, X.2⟩) : ℤ) := by
            dsimp only [noninjectiveArrows]
            apply Finset.sum_congr rfl
            intro X hX
            apply Finset.sum_congr rfl
            intro Y hY
            exact_mod_cast B.factorArrowMultiplicity_eq_translation
              (⟨X.1.1, X.2⟩ : T.Noninjective) Y.1
      _ = ∑ X : B.StandardFactorNoninjectiveLevelVertex j,
            ∑ Y : B.StandardFactorLevelVertex (j + 1),
              (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                T.toFiniteRightTauCategoryData Y.1 (E X).1.1 : ℤ) := by rfl
      _ = ∑ Z : B.StandardFactorNonprojectiveLevelVertex (j + 2),
            ∑ Y : B.StandardFactorLevelVertex (j + 1),
              (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
                T.toFiniteRightTauCategoryData Y.1 Z.1.1 : ℤ) := by
          exact hreindex
      _ = nonprojectiveArrows := by
        dsimp only [nonprojectiveArrows]
        rw [Finset.sum_comm]
  rw [hsplitRight, hsplitLeft, hinjective, hprojective, htranslation]
  ring

/-- The first adjacent slice has the tree edge count: each level-one vertex
is projective and has exactly one incoming arrow from the unique source. -/
theorem standardFactorArrowCount_zero
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.standardFactorArrowCount 0 =
      B.standardFactorVertexCount 0 + B.standardFactorVertexCount 1 - 1 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  have hvertexZero : B.standardFactorVertexCount 0 = 1 := by
    letI : Unique (B.StandardFactorLevelVertex 0) :=
      { default := ⟨D.source, B.standardFactorLevel_source⟩
        uniq := by
          intro x
          apply Subtype.ext
          exact (B.standardFactorLevel_eq_zero_iff x.1).1 x.2 }
    change (Fintype.card (B.StandardFactorLevelVertex 0) : ℤ) = 1
    norm_num [Fintype.card_unique]
  calc
    B.standardFactorArrowCount 0 =
        ∑ Y : B.StandardFactorLevelVertex 1,
          ∑ X : B.StandardFactorLevelVertex 0,
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData X.1 Y.1 : ℤ) := by
          rw [standardFactorArrowCount, Finset.sum_comm]
    _ = ∑ _Y : B.StandardFactorLevelVertex 1, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro Y hY
      have hprojective : T.IsProjective Y.1 :=
        B.isProjective_of_standardFactorLevel_eq_one Y.1 Y.2
      have hsource : Y.1 ≠ D.source := by
        intro h
        have hlevel : B.standardFactorLevel Y.1 = 1 := Y.2
        rw [h, B.standardFactorLevel_source] at hlevel
        omega
      calc
        (∑ X : B.StandardFactorLevelVertex 0,
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData X.1 Y.1 : ℤ)) =
            ∑ X, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData X Y.1 : ℤ) :=
          B.sum_factorArrowMultiplicity_source_level 0 Y.1 (by simpa using Y.2)
        _ = 1 :=
          B.sum_factorArrowMultiplicity_source_eq_one_of_projective_ne_source
            Y.1 hprojective hsource
    _ = B.standardFactorVertexCount 1 := by
      simp [standardFactorVertexCount]
    _ = B.standardFactorVertexCount 0 +
          B.standardFactorVertexCount 1 - 1 := by
      rw [hvertexZero]
      ring

/-- Every adjacent concrete level slice has the edge count of a tree. -/
theorem standardFactorArrowCount_eq_vertexCount_add_vertexCount_sub_one
    (B : S.PrimitiveDirectedBoundaryData D)
    (j : ℕ) (hj : j < B.standardFactorLength) :
    B.standardFactorArrowCount j =
      B.standardFactorVertexCount j +
        B.standardFactorVertexCount (j + 1) - 1 := by
  exact MagnitudeConjecture.GradedTreeExcess.sliceEdgeCount_of_translationRecurrence
    B.standardFactorVertexCount B.standardFactorArrowCount
    B.standardFactorInjectiveCount B.standardFactorProjectiveCount
    B.standardFactorArrowCount_zero
    (fun i hi ↦ B.standardFactorArrowCount_add_one i hi)
    (fun i _hi ↦ B.standardFactorVertexCount_add_two i)
    j hj

@[simp]
theorem standardFactorVertexCount_zero
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.standardFactorVertexCount 0 = 1 := by
  letI : Unique (B.StandardFactorLevelVertex 0) :=
    { default := ⟨D.source, B.standardFactorLevel_source⟩
      uniq := by
        intro x
        apply Subtype.ext
        exact (B.standardFactorLevel_eq_zero_iff x.1).1 x.2 }
  change (Fintype.card (B.StandardFactorLevelVertex 0) : ℤ) = 1
  norm_num [Fintype.card_unique]

@[simp]
theorem standardFactorVertexCount_length
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.standardFactorVertexCount B.standardFactorLength = 1 := by
  letI : Unique (B.StandardFactorLevelVertex B.standardFactorLength) :=
    { default := ⟨D.sink, rfl⟩
      uniq := by
        intro x
        apply Subtype.ext
        exact (B.standardFactorLevel_eq_length_iff x.1).1 x.2 }
  change
    (Fintype.card
      (B.StandardFactorLevelVertex B.standardFactorLength) : ℤ) = 1
  norm_num [Fintype.card_unique]

end PrimitiveDirectedBoundaryData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
