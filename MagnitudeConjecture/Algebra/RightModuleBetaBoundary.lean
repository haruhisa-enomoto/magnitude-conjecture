import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.RightModuleContragredientMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteTauBeta

/-!
# Projective boundary summands in Auslander--Reiten meshes

If one summand of a right almost-split middle term is projective, the
corresponding left component is monic.  Exactness then makes every other
right component monic, so none of the other middle summands can be injective.
This is the boundary-counting step used in the comparison of the left and
right beta invariants and in projective-injective socle rejection.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped BigOperators

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

set_option synthInstance.maxHeartbeats 100000

universe u

private theorem irreducible_not_epi_of_projective_target
    {C : Type u} [CategoryTheory.Category C] {X Y : C} (f : X ⟶ Y)
    (hf : IsIrreducibleMorphism f)
    (hY : CategoryTheory.Projective Y) : ¬ Epi f := by
  intro hepi
  letI : Epi f := hepi
  letI : CategoryTheory.Projective Y := hY
  apply hf.not_isSplitEpi
  exact IsSplitEpi.mk'
    { section_ := Projective.factorThru (𝟙 Y) f
      id := Projective.factorThru_comp (𝟙 Y) f }

private theorem irreducible_not_injective_source_of_mono
    {C : Type u} [CategoryTheory.Category C] {X Y : C} (f : X ⟶ Y)
    (hf : IsIrreducibleMorphism f) (hmono : Mono f) :
    ¬ CategoryTheory.Injective X := by
  intro hinjective
  letI : Mono f := hmono
  letI : CategoryTheory.Injective X := hinjective
  apply hf.not_isSplitMono
  exact IsSplitMono.mk'
    { retraction := Injective.factorThru (𝟙 X) f
      id := Injective.comp_factorThru (𝟙 X) f }

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Number of noninjective indecomposable occurrences leaving a selected
label.  Under contragredient duality this is the ordinary `betaAt` for the
opposite-algebra skeleton. -/
def leftBetaAt (source : Fin S.n) : ℕ := by
  classical
  exact ∑ target,
    if Injective (S.fgObj target) then 0 else
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target

/-- Maximum number of noninjective occurrences leaving a noninjective
label.  This is the right-module realization of the classical left beta
invariant. -/
def leftBeta : ℕ := by
  classical
  exact Finset.univ.sup fun source ↦
    if Injective (S.fgObj source) then 0 else S.leftBetaAt source

/-- A bound on left beta is exactly a bound on the outgoing noninjective
occurrences at every noninjective source. -/
theorem leftBeta_le_iff (bound : ℕ) :
    S.leftBeta ≤ bound ↔
      ∀ source, ¬ Injective (S.fgObj source) →
        S.leftBetaAt source ≤ bound := by
  classical
  constructor
  · intro hbeta source hsource
    have hle :
        (if Injective (S.fgObj source) then 0 else S.leftBetaAt source) ≤
          S.leftBeta := by
      unfold leftBeta
      exact Finset.le_sup
        (s := Finset.univ)
        (f := fun source ↦
          if Injective (S.fgObj source) then 0 else S.leftBetaAt source)
        (Finset.mem_univ source)
    simpa [hsource] using hle.trans hbeta
  · intro h
    unfold leftBeta
    rw [Finset.sup_le_iff]
    intro source _
    by_cases hsource : Injective (S.fgObj source)
    · simp [hsource]
    · simpa [hsource] using h source hsource

/-- Contragredient duality identifies opposite `betaAt` with the original
outgoing noninjective-occurrence count. -/
theorem contragredient_betaAt_eq_leftBetaAt [IsAlgClosed k]
    [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)}) :
    FiniteTauMatrix.betaAt
        S.contragredientSkeleton.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.contragredientNonprojectiveLabel x).1 =
      S.leftBetaAt x.1 := by
  classical
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory Aᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives (Aᵐᵒᵖ)ᵐᵒᵖ
  let Sop := S.contragredientSkeleton
  let B := S.contragredientAlignedBiduality
  unfold FiniteTauMatrix.betaAt leftBetaAt
  apply Finset.sum_congr rfl
  intro target _
  change Fin S.n at target
  have hprojective :
      Sop.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective target ↔
        Injective (S.fgObj target) := by
    rw [FiniteTauMatrix.isProjective_iff_projective_obj]
    exact (B.forward.injective_iff_projective_image
      S.almostSplitSkeleton S.contragredientAlmostSplitSkeleton target).symm
  by_cases htarget : Injective (S.fgObj target)
  · rw [if_pos htarget, if_pos (hprojective.2 htarget)]
  · rw [if_neg htarget,
      if_neg (fun h ↦ htarget (hprojective.1 h))]
    exact S.contragredient_arrowMultiplicity_eq_reverse x target

/-- The beta invariant of the label-aligned contragredient skeleton is the
original left beta invariant. -/
theorem contragredient_beta_eq_leftBeta [IsAlgClosed k]
    [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ] :
    FiniteTauMatrix.beta
        S.contragredientSkeleton.finiteTauCategoryData.toFiniteRightTauCategoryData =
      S.leftBeta := by
  classical
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory Aᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives (Aᵐᵒᵖ)ᵐᵒᵖ
  let Sop := S.contragredientSkeleton
  let B := S.contragredientAlignedBiduality
  unfold FiniteTauMatrix.beta leftBeta
  apply Finset.sup_congr rfl
  intro source _
  change Fin S.n at source
  have hprojective :
      Sop.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective source ↔
        Injective (S.fgObj source) := by
    rw [FiniteTauMatrix.isProjective_iff_projective_obj]
    exact (B.forward.injective_iff_projective_image
      S.almostSplitSkeleton S.contragredientAlmostSplitSkeleton source).symm
  by_cases hsource : Injective (S.fgObj source)
  · rw [if_pos hsource, if_pos (hprojective.2 hsource)]
  · rw [if_neg hsource,
      if_neg (fun h ↦ hsource (hprojective.1 h))]
    exact S.contragredient_betaAt_eq_leftBetaAt ⟨source, hsource⟩

/-- Number of nonprojective indecomposable occurrences leaving a selected
label.  Unlike `betaAt`, this is an outgoing count. -/
def nonprojectiveOutgoingAt (source : Fin S.n) : ℕ := by
  classical
  exact ∑ target,
    if Projective (S.fgObj target) then 0 else
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target

/-- Simultaneous inverse Auslander--Reiten translation preserves arrow
multiplicity between noninjective labels. -/
theorem arrowMultiplicity_inverseTranslation_pair [IsAlgClosed k]
    (x y : {i : Fin S.n // ¬ Injective (S.fgObj i)}) :
    FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
          ((S.rightTranslationEquiv).symm x).1
          ((S.rightTranslationEquiv).symm y).1 =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x.1 y.1 := by
  calc
    FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData
            ((S.rightTranslationEquiv).symm x).1
            ((S.rightTranslationEquiv).symm y).1 =
        FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData y.1
            ((S.rightTranslationEquiv).symm x).1 :=
      (S.arrowMultiplicity_eq_inverseTranslation y
        ((S.rightTranslationEquiv).symm x).1).symm
    _ = FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData x.1 y.1 :=
      (S.arrowMultiplicity_eq_inverseTranslation x y.1).symm

/-- Inverse translation identifies the noninjective outgoing count at `x`
with the nonprojective outgoing count at `tauMinus x`. -/
theorem leftBetaAt_eq_nonprojectiveOutgoingAt_inverseTranslation
    [IsAlgClosed k]
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)}) :
    S.leftBetaAt x.1 =
      S.nonprojectiveOutgoingAt ((S.rightTranslationEquiv).symm x).1 := by
  classical
  let e := S.rightTranslationEquiv.symm
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  unfold leftBetaAt nonprojectiveOutgoingAt
  calc
    (∑ target, if Injective (S.fgObj target) then 0 else
        FiniteTauMatrix.arrowMultiplicity T x.1 target) =
        (∑ target ∈ Finset.univ.filter
            (fun y : Fin S.n ↦ ¬ Injective (S.fgObj y)),
          FiniteTauMatrix.arrowMultiplicity T x.1 target) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : Injective (S.fgObj y) <;> simp [hy]
    _ = ∑ y : {i : Fin S.n // ¬ Injective (S.fgObj i)},
          FiniteTauMatrix.arrowMultiplicity T x.1 y.1 := by
      exact Finset.sum_subtype
        (Finset.univ.filter
          (fun y : Fin S.n ↦ ¬ Injective (S.fgObj y)))
        (by simp) _
    _ = ∑ y : {i : Fin S.n // ¬ Projective (S.fgObj i)},
          FiniteTauMatrix.arrowMultiplicity T (e x).1 y.1 := by
      exact Fintype.sum_equiv e
        (fun y : {i : Fin S.n // ¬ Injective (S.fgObj i)} ↦
          FiniteTauMatrix.arrowMultiplicity T x.1 y.1)
        (fun y : {i : Fin S.n // ¬ Projective (S.fgObj i)} ↦
          FiniteTauMatrix.arrowMultiplicity T (e x).1 y.1)
        (fun y ↦ by
          simpa only [e] using
            (S.arrowMultiplicity_inverseTranslation_pair x y).symm)
    _ = (∑ target ∈ Finset.univ.filter
            (fun y : Fin S.n ↦ ¬ Projective (S.fgObj y)),
          FiniteTauMatrix.arrowMultiplicity T (e x).1 target) := by
      exact (Finset.sum_subtype
        (Finset.univ.filter
          (fun y : Fin S.n ↦ ¬ Projective (S.fgObj y)))
        (by simp) _).symm
    _ = ∑ target, if Projective (S.fgObj target) then 0 else
        FiniteTauMatrix.arrowMultiplicity T (e x).1 target := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : Projective (S.fgObj y) <;> simp [hy]

/-- At a noninjective source, the nonprojective outgoing count is the
ordinary `betaAt` count at its inverse translate. -/
theorem nonprojectiveOutgoingAt_eq_betaAt_inverseTranslation
    [IsAlgClosed k]
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)}) :
    S.nonprojectiveOutgoingAt x.1 =
      FiniteTauMatrix.betaAt
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
          ((S.rightTranslationEquiv).symm x).1 := by
  classical
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  unfold nonprojectiveOutgoingAt FiniteTauMatrix.betaAt
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : Projective (S.fgObj y)
  · have hyT : T.IsProjective y := by
      rw [FiniteTauMatrix.isProjective_iff_projective_obj]
      exact hy
    rw [if_pos hy, if_pos hyT]
  · have hyT : ¬ T.IsProjective y := by
      rw [FiniteTauMatrix.isProjective_iff_projective_obj]
      exact hy
    rw [if_neg hy, if_neg hyT]
    exact S.arrowMultiplicity_eq_inverseTranslation x y

/-- A left-beta count can exceed the global right beta only at the terminal
injective boundary of inverse translation. -/
theorem leftBetaAt_le_beta_of_inverseTranslation_not_injective
    [IsAlgClosed k]
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)})
    (hx : ¬ Injective
      (S.fgObj ((S.rightTranslationEquiv).symm x).1)) :
    S.leftBetaAt x.1 ≤
      FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData := by
  classical
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let y : {i : Fin S.n // ¬ Injective (S.fgObj i)} :=
    ⟨((S.rightTranslationEquiv).symm x).1, hx⟩
  rw [S.leftBetaAt_eq_nonprojectiveOutgoingAt_inverseTranslation x,
    S.nonprojectiveOutgoingAt_eq_betaAt_inverseTranslation y]
  let z := (S.rightTranslationEquiv).symm y
  have hz : ¬ T.IsProjective z.1 := by
    rw [FiniteTauMatrix.isProjective_iff_projective_obj]
    exact z.2
  have hle :
      (if T.IsProjective z.1 then 0 else FiniteTauMatrix.betaAt T z.1) ≤
        FiniteTauMatrix.beta T := by
    unfold FiniteTauMatrix.beta
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Fin S.n)))
      (f := fun target ↦
        if T.IsProjective target then 0 else
          FiniteTauMatrix.betaAt T target)
      (Finset.mem_univ z.1)
  simpa only [if_neg hz, T, z] using hle

/-- Under a right-beta bound, any larger left-beta count is forced to sit at
an injective inverse translate. -/
theorem inverseTranslation_injective_of_beta_lt_leftBetaAt
    [IsAlgClosed k]
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)})
    (hx : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData <
      S.leftBetaAt x.1) :
    Injective (S.fgObj ((S.rightTranslationEquiv).symm x).1) := by
  by_contra hnot
  exact (not_le_of_gt hx)
    (S.leftBetaAt_le_beta_of_inverseTranslation_not_injective x hnot)

/-- If the global left beta is strictly larger than the global right beta,
the excess is witnessed by a noninjective source whose inverse translate is
injective.  Thus simultaneous translation eliminates every non-boundary
case of the one-sided beta comparison. -/
theorem exists_injective_inverseTranslation_of_beta_lt_leftBeta
    [IsAlgClosed k]
    (hbeta : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData < S.leftBeta) :
    ∃ x : {i : Fin S.n // ¬ Injective (S.fgObj i)},
      FiniteTauMatrix.beta
          S.finiteTauCategoryData.toFiniteRightTauCategoryData <
        S.leftBetaAt x.1 ∧
      Injective (S.fgObj ((S.rightTranslationEquiv).symm x).1) := by
  classical
  unfold leftBeta at hbeta
  rw [Finset.lt_sup_iff] at hbeta
  obtain ⟨source, -, hsource⟩ := hbeta
  by_cases hinjective : Injective (S.fgObj source)
  · simp only [if_pos hinjective] at hsource
    omega
  · have hsource' : FiniteTauMatrix.beta
          S.finiteTauCategoryData.toFiniteRightTauCategoryData <
        S.leftBetaAt source := by
      simpa only [if_neg hinjective] using hsource
    let x : {i : Fin S.n // ¬ Injective (S.fgObj i)} :=
      ⟨source, hinjective⟩
    exact ⟨x, hsource',
      S.inverseTranslation_injective_of_beta_lt_leftBetaAt x hsource'⟩

/-- If a proposed common bound holds for right beta but fails for left beta,
the whole failure is concentrated at an injective nonprojective label: more
than `bound` nonprojective arrow occurrences leave that label. -/
theorem exists_injective_nonprojective_boundary_of_beta_le_of_not_leftBeta_le
    [IsAlgClosed k] {bound : ℕ}
    (hbeta : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ bound)
    (hleft : ¬ S.leftBeta ≤ bound) :
    ∃ z : {i : Fin S.n // ¬ Projective (S.fgObj i)},
      Injective (S.fgObj z.1) ∧
        bound < S.nonprojectiveOutgoingAt z.1 := by
  classical
  have hexists : ∃ source : Fin S.n,
      ¬ Injective (S.fgObj source) ∧ bound < S.leftBetaAt source := by
    by_contra hnone
    apply hleft
    rw [S.leftBeta_le_iff bound]
    intro source hsource
    by_contra hnot
    apply hnone
    exact ⟨source, hsource, by omega⟩
  obtain ⟨source, hsource, hsourceBound⟩ := hexists
  let x : {i : Fin S.n // ¬ Injective (S.fgObj i)} :=
    ⟨source, hsource⟩
  have hbetaAt : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData <
      S.leftBetaAt x.1 :=
    lt_of_le_of_lt hbeta hsourceBound
  have hinjective :=
    S.inverseTranslation_injective_of_beta_lt_leftBetaAt x hbetaAt
  let z : {i : Fin S.n // ¬ Projective (S.fgObj i)} :=
    (S.rightTranslationEquiv).symm x
  refine ⟨z, hinjective, ?_⟩
  rw [← S.leftBetaAt_eq_nonprojectiveOutgoingAt_inverseTranslation x]
  exact hsourceBound

/-- In particular, failure of the desired left-beta-two bound under the
right-beta-two hypothesis produces an injective nonprojective boundary label
with at least three nonprojective outgoing occurrences. -/
theorem exists_injective_nonprojective_boundary_of_beta_le_two
    [IsAlgClosed k]
    (hbeta : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2)
    (hleft : ¬ S.leftBeta ≤ 2) :
    ∃ z : {i : Fin S.n // ¬ Projective (S.fgObj i)},
      Injective (S.fgObj z.1) ∧
        3 ≤ S.nonprojectiveOutgoingAt z.1 := by
  obtain ⟨z, hzInjective, hz⟩ :=
    S.exists_injective_nonprojective_boundary_of_beta_le_of_not_leftBeta_le
      hbeta hleft
  exact ⟨z, hzInjective, by omega⟩

/-- The ordinary `betaAt` count may be read directly from the skeleton's
displayed minimal right almost-split decomposition, whose index is a finite
category rather than a chosen finite ordinal. -/
theorem betaAt_eq_natCard_nonprojective_minimalRightMiddle
    (z : {i : Fin S.n // ¬ Projective (S.fgObj i)}) :
    let B := S.minimalRightAlmostSplitAt z.1
    FiniteTauMatrix.betaAt
        S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1 =
      Nat.card {i : B.index //
        ¬ Projective (S.fgObj (B.label i))} := by
  classical
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let B := S.minimalRightAlmostSplitAt z.1
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  letI : Fintype B.index := FintypeCat.fintype
  let n := Fintype.card B.index
  let epsilon : B.index ≃ Fin n := Fintype.equivFin B.index
  let label : Fin n → Fin S.n := fun i ↦ B.label (epsilon.symm i)
  let eReindex :
      S.almostSplitSkeleton.sumOver B.index B.label ≅
        ⨁ fun i : Fin n ↦ T.obj (label i) :=
    biproduct.whiskerEquiv epsilon
      (fun i ↦ eqToIso (by
        simp only [label, Equiv.symm_apply_apply]
        rfl))
  let eDisplayed :
      (T.rightMesh (T.obj z.1)).X₂ ≅
        ⨁ fun i : Fin n ↦ T.obj (label i) :=
    (eqToIso (by
      change (S.canonicalRightMesh (S.fgObj z.1)).X₂ = B.middle
      rw [S.canonicalRightMesh_at_label z.1,
        S.labelRightMesh_X₂ z.1,
        S.meshRightAlmostSplitAt_eq_of_not_projective z.1 z.2]
      )).trans (B.decomposition.trans eReindex)
  have hcount :=
    FiniteTauMatrix.betaAt_eq_natCard_nonprojective_of_rightMiddleDecomposition
      T z.1 label ⟨eDisplayed⟩
  let eSubtype := Equiv.subtypeEquiv epsilon.symm
    (p := fun i : Fin n ↦ ¬ T.IsProjective (label i))
    (q := fun i : B.index ↦ ¬ Projective (S.fgObj (B.label i)))
    (fun i ↦ by
      rw [FiniteTauMatrix.isProjective_iff_projective_obj]
      simp only [label]
      rfl)
  change FiniteTauMatrix.betaAt T z.1 =
    Nat.card {i : B.index //
      ¬ Projective (S.fgObj (B.label i))}
  rw [hcount, Nat.card_congr eSubtype]

/-- `leftBetaAt` counts the noninjective occurrences in the displayed
right almost-split middle term whose left endpoint is the specified source.
This is the occurrence-level form of translation invariance. -/
theorem leftBetaAt_eq_natCard_noninjective_rightMiddle [IsAlgClosed k]
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)}) :
    let z := (S.rightTranslationEquiv).symm x
    let B := S.minimalRightAlmostSplitAt z.1
    S.leftBetaAt x.1 = Nat.card {i : B.index //
      ¬ Injective (S.fgObj (B.label i))} := by
  classical
  let z := (S.rightTranslationEquiv).symm x
  let B := S.minimalRightAlmostSplitAt z.1
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let weight : Fin S.n → ℕ := fun target ↦
    if Injective (S.fgObj target) then 0 else 1
  letI : Fintype B.index := FintypeCat.fintype
  let n := Fintype.card B.index
  let epsilon : B.index ≃ Fin n := Fintype.equivFin B.index
  let label : Fin n → Fin S.n := fun i ↦ B.label (epsilon.symm i)
  change S.leftBetaAt x.1 = Nat.card {i : B.index //
    ¬ Injective (S.fgObj (B.label i))}
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold leftBetaAt
  calc
    (∑ target, if Injective (S.fgObj target) then 0 else
        FiniteTauMatrix.arrowMultiplicity T x.1 target) =
        ∑ target,
          FiniteTauMatrix.arrowMultiplicity T x.1 target * weight target := by
      apply Finset.sum_congr rfl
      intro target _
      by_cases htarget : Injective (S.fgObj target) <;>
        simp [weight, htarget]
    _ = ∑ target,
          FiniteTauMatrix.arrowMultiplicity T target z.1 * weight target := by
      apply Finset.sum_congr rfl
      intro target _
      rw [S.arrowMultiplicity_eq_inverseTranslation x target]
    _ = ∑ i : Fin (FiniteTauMatrix.rightMiddleArity T z.1),
          weight (FiniteTauMatrix.rightMiddleLabel T z.1 i) :=
      FiniteTauMatrix.sum_arrowMultiplicity_mul T z.1 weight
    _ = ∑ i : Fin n, weight (label i) := by
      let eReindex :
          S.almostSplitSkeleton.sumOver B.index B.label ≅
            ⨁ fun i : Fin n ↦ T.obj (label i) :=
        biproduct.whiskerEquiv epsilon
          (fun i ↦ eqToIso (by
            simp only [label, Equiv.symm_apply_apply]
            rfl))
      let eDisplayed :
          (T.rightMesh (T.obj z.1)).X₂ ≅
            ⨁ fun i : Fin n ↦ T.obj (label i) :=
        (eqToIso (by
          change (S.canonicalRightMesh (S.fgObj z.1)).X₂ = B.middle
          rw [S.canonicalRightMesh_at_label z.1,
            S.labelRightMesh_X₂ z.1,
            S.meshRightAlmostSplitAt_eq_of_not_projective z.1 z.2]
          )).trans (B.decomposition.trans eReindex)
      obtain ⟨eChosen⟩ := FiniteTauMatrix.rightMiddleIso T z.1
      exact T.sum_weight_eq_of_nonempty_iso_finBiproduct_obj
        (M := ℕ) weight
        (FiniteTauMatrix.rightMiddleArity T z.1) n
        (FiniteTauMatrix.rightMiddleLabel T z.1) label
        ⟨eChosen.symm.trans eDisplayed⟩
    _ = ∑ i : B.index, weight (B.label i) := by
      exact Fintype.sum_equiv epsilon.symm
        (fun i : Fin n ↦ weight (label i))
        (fun i : B.index ↦ weight (B.label i))
        (fun i ↦ by simp [label])
    _ = ∑ i : B.index,
          if ¬ Injective (S.fgObj (B.label i)) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : Injective (S.fgObj (B.label i)) <;>
        simp [weight, hi]
    _ = _ := by rw [Finset.card_filter]

/-- If one displayed summand of a nonprojective right almost-split middle
term is projective, every different displayed summand is noninjective. -/
theorem rightMiddleLabel_not_injective_of_ne_of_projective
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (i j : (S.minimalRightAlmostSplitAt z.1).index) (hji : j ≠ i)
    (hi : Projective
      (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label i))) :
    ¬ Injective
      (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label j)) := by
  let B := S.minimalRightAlmostSplitAt z.1
  let L := S.rightSequenceLeftDecomposition z
  let σ := S.almostSplitSkeleton
  have hiNotEpi : ¬ Epi (L.component σ i) :=
    irreducible_not_epi_of_projective_target
      (L.component σ i) (L.component_irreducible σ i) hi
  have hiMono : Mono (L.component σ i) :=
    (L.component_mono_or_epi σ i).resolve_right hiNotEpi
  have hjMono : Mono (B.component σ j) :=
    S.rightComponent_mono_of_ne_of_leftComponent_mono
      z i j hji hiMono
  exact irreducible_not_injective_source_of_mono
    (B.component σ j) (B.component_irreducible σ j) hjMono

/-- If the right almost-split middle term attached to a noninjective left
endpoint contains a projective occurrence, all but that occurrence are
counted by `leftBetaAt`. -/
theorem rightMiddle_natCard_le_leftBetaAt_add_one_of_projective
    [IsAlgClosed k]
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)})
    (i : (S.minimalRightAlmostSplitAt
      ((S.rightTranslationEquiv).symm x).1).index)
    (hi : Projective
      (S.fgObj ((S.minimalRightAlmostSplitAt
        ((S.rightTranslationEquiv).symm x).1).label i))) :
    Nat.card (S.minimalRightAlmostSplitAt
        ((S.rightTranslationEquiv).symm x).1).index ≤
      S.leftBetaAt x.1 + 1 := by
  classical
  let z := (S.rightTranslationEquiv).symm x
  let B := S.minimalRightAlmostSplitAt z.1
  letI : Fintype B.index := FintypeCat.fintype
  let f : {j : B.index // j ≠ i} →
      {j : B.index // ¬ Injective (S.fgObj (B.label j))} :=
    fun j ↦ ⟨j.1,
      S.rightMiddleLabel_not_injective_of_ne_of_projective
        z i j.1 j.2 hi⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg
      (fun q : {j : B.index //
        ¬ Injective (S.fgObj (B.label j))} ↦ q.1) hab
  have hcardLe : Fintype.card {j : B.index // j ≠ i} ≤
      Fintype.card {j : B.index //
        ¬ Injective (S.fgObj (B.label j))} :=
    Fintype.card_le_of_injective f hf
  have hcompl : Fintype.card {j : B.index // j ≠ i} =
      Fintype.card B.index - 1 := by
    simpa using Fintype.card_subtype_compl (fun j : B.index ↦ j = i)
  have hpositive : 0 < Fintype.card B.index :=
    Fintype.card_pos_iff.mpr ⟨i⟩
  have hbeta := S.leftBetaAt_eq_natCard_noninjective_rightMiddle x
  change S.leftBetaAt x.1 = Nat.card {j : B.index //
    ¬ Injective (S.fgObj (B.label j))} at hbeta
  rw [Nat.card_eq_fintype_card] at hbeta
  change Nat.card B.index ≤ S.leftBetaAt x.1 + 1
  rw [Nat.card_eq_fintype_card, hbeta]
  omega

/-- If a nonprojective right almost-split middle term contains no
projective-injective occurrence, its total arity is bounded by the maximum
of the right and left beta bounds.  With no projective occurrence, right beta
counts the whole middle; with one, the boundary lemma makes left beta count
the whole middle. -/
theorem rightMiddle_natCard_le_of_no_projectiveInjective [IsAlgClosed k]
    {bound : ℕ}
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ bound)
    (hleft : S.leftBeta ≤ bound)
    (z : {i : Fin S.n // ¬ Projective (S.fgObj i)})
    (hnoPI : ∀ i : (S.minimalRightAlmostSplitAt z.1).index,
      Projective
          (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label i)) →
        ¬ Injective
          (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label i))) :
    Nat.card (S.minimalRightAlmostSplitAt z.1).index ≤ bound := by
  classical
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let B := S.minimalRightAlmostSplitAt z.1
  letI : Fintype B.index := FintypeCat.fintype
  by_cases hprojective : ∃ i : B.index,
      Projective (S.fgObj (B.label i))
  · obtain ⟨i, hi⟩ := hprojective
    have hall : ∀ j : B.index,
        ¬ Injective (S.fgObj (B.label j)) := by
      intro j
      by_cases hji : j = i
      · subst j
        exact hnoPI i hi
      · exact S.rightMiddleLabel_not_injective_of_ne_of_projective
          z i j hji hi
    let x := S.rightTranslationEquiv z
    have hcount := S.leftBetaAt_eq_natCard_noninjective_rightMiddle x
    have hzval : ((S.rightTranslationEquiv).symm x).1 = z.1 :=
      congrArg Subtype.val (S.rightTranslationEquiv.symm_apply_apply z)
    change S.leftBetaAt x.1 = Nat.card
      {j : (S.minimalRightAlmostSplitAt
        ((S.rightTranslationEquiv).symm x).1).index //
          ¬ Injective (S.fgObj ((S.minimalRightAlmostSplitAt
            ((S.rightTranslationEquiv).symm x).1).label j))} at hcount
    rw [hzval] at hcount
    have hcount' : S.leftBetaAt x.1 = Nat.card {j : B.index //
        ¬ Injective (S.fgObj (B.label j))} := by
      exact hcount
    have hAt : S.leftBetaAt x.1 ≤ bound :=
      (S.leftBeta_le_iff bound).1 hleft x.1 x.2
    calc
      Nat.card B.index = Nat.card {j : B.index //
          ¬ Injective (S.fgObj (B.label j))} := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Fintype.card_subtype]
        simp [hall]
      _ = S.leftBetaAt x.1 := hcount'.symm
      _ ≤ bound := hAt
  · have hall : ∀ j : B.index,
        ¬ Projective (S.fgObj (B.label j)) := by
      simpa only [not_exists] using hprojective
    have hcount := S.betaAt_eq_natCard_nonprojective_minimalRightMiddle z
    have hzT :
        ¬ S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
          z.1 := by
      rw [FiniteTauMatrix.isProjective_iff_projective_obj]
      exact z.2
    have hAt : FiniteTauMatrix.betaAt
        S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1 ≤ bound :=
      (FiniteTauMatrix.beta_le_iff
        S.finiteTauCategoryData.toFiniteRightTauCategoryData bound).1
          hbeta z.1 hzT
    calc
      Nat.card B.index = Nat.card {j : B.index //
          ¬ Projective (S.fgObj (B.label j))} := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Fintype.card_subtype]
        simp [hall]
      _ = FiniteTauMatrix.betaAt
          S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1 :=
        hcount.symm
      _ ≤ bound := hAt

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
