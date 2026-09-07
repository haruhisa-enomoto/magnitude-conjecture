import MagnitudeConjecture.Algebra.BiserialModuleDecomposition
import MagnitudeConjecture.Algebra.RightModuleBetaProjectiveRadical
import MagnitudeConjecture.Algebra.RightModuleIrreducibleProjectiveSourceUniserial
import MagnitudeConjecture.CategoryTheory.AlgebraicallyClosedOccurrenceBasis
import MagnitudeConjecture.CategoryTheory.AlmostSplitSummandIrreducible

/-!
# Projective-radical recursion under the beta-two bound

This file implements the finite radical recursion in Auslander--Reiten,
Lemma 4.5.  The common left/right beta bound makes the radical of a
projective occurring irreducibly inside a noninjective projective either
zero or indecomposable.  If that radical is nonprojective, Proposition
1.3 makes it uniserial; if it is projective, the argument repeats at the
strictly smaller radical.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CategoryTheory
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

variable [HasExt.{u} (RightModule.FinitelyGeneratedCategory A)]

/-- Over an algebraically closed field, the dimension of the intrinsic
irreducible-morphism space is the official arrow multiplicity, at projective
and nonprojective endpoints alike. -/
theorem finrank_irreducibleHomSpace_eq_arrowMultiplicity
    (source target : Fin S.n) :
    Module.finrank k
        (S.almostSplitSkeleton.irreducibleHomSpace
          (K := k) source target) =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target := by
  classical
  let σ := S.almostSplitSkeleton
  let B := S.meshRightAlmostSplitAt target
  calc
    Module.finrank k (σ.irreducibleHomSpace (K := k) source target) =
        Nat.card (σ.RightAROccurrence B source) :=
      σ.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
        B source
    _ = ∑ i : B.index, if B.label i = source then 1 else 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
        Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = S.indecomposableMultiplicity source B.middle := by
      symm
      exact S.indecomposableMultiplicity_eq_of_fintype_decomposition
        source B.middle B.decomposition
    _ = FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData source target :=
      S.indecomposableMultiplicity_meshRightMiddle source target

/-- An actual irreducible morphism forces positive official arrow
multiplicity. -/
theorem arrowMultiplicity_pos_of_irreducible
    (source target : Fin S.n) (g : S.fgObj source ⟶ S.fgObj target)
    (hg : IsIrreducibleMorphism g) :
    0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData source target := by
  let B := S.meshRightAlmostSplitAt target
  letI : Module.Finite k
      (S.almostSplitSkeleton.irreducibleHomSpace
        (K := k) source target) :=
    Module.Finite.equiv
      (S.almostSplitSkeleton.rightAROccurrenceLinearEquivOfIsAlgClosed
        B source)
  have hnontrivial : Nontrivial
      (S.almostSplitSkeleton.irreducibleHomSpace
        (K := k) source target) :=
    (S.almostSplitSkeleton
      |>.nontrivial_irreducibleHomSpace_iff_hasIrreducibleMorphism
        (K := k) source target).2 ⟨g, hg⟩
  rw [← S.finrank_irreducibleHomSpace_eq_arrowMultiplicity source target]
  exact Module.finrank_pos

/-- Positive incoming multiplicity at a nonprojective endpoint supplies a
literal occurrence in its selected minimal right almost-split middle. -/
theorem exists_minimalRightAlmostSplitAt_label_of_arrowMultiplicity_pos
    (source : Fin S.n)
    (target : {i : Fin S.n // ¬ Projective (S.fgObj i)})
    (hpos : 0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData source target.1) :
    ∃ i : (S.minimalRightAlmostSplitAt target.1).index,
      (S.minimalRightAlmostSplitAt target.1).label i = source := by
  classical
  let B := S.minimalRightAlmostSplitAt target.1
  have hpos' : 0 < S.indecomposableMultiplicity source B.middle := by
    dsimp only [B]
    rw [← S.meshRightAlmostSplitAt_eq_of_not_projective target.1 target.2,
      S.indecomposableMultiplicity_meshRightMiddle]
    exact hpos
  rw [S.indecomposableMultiplicity_eq_of_fintype_decomposition
    source B.middle B.decomposition] at hpos'
  by_contra hnone
  push_neg at hnone
  have hzero : (∑ i : B.index,
      if B.label i = source then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : B.label i ≠ source := by
      exact hnone i
    simp [hi]
  omega

/-- If a projective embeds irreducibly in a noninjective projective, its
projective-boundary radical has at most one indecomposable occurrence. -/
theorem projective_rightMiddleArity_le_one_of_irreducible_to_noninjectiveProjective
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g)
    (hu : Projective (S.fgObj u))
    (hp : Projective (S.fgObj p))
    (hpNotInjective : ¬ Injective (S.fgObj p)) :
    FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData u ≤ 1 := by
  classical
  let x : {i : Fin S.n // ¬ Injective (S.fgObj i)} :=
    ⟨u, S.irreducibleIntoProjective_source_not_injective u p g hg hp⟩
  let z : {i : Fin S.n // ¬ Projective (S.fgObj i)} :=
    (S.rightTranslationEquiv).symm x
  let B := S.minimalRightAlmostSplitAt z.1
  have hUP : 0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData u p :=
    S.arrowMultiplicity_pos_of_irreducible u p g hg
  have hPZ : 0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p z.1 := by
    rw [← S.arrowMultiplicity_eq_inverseTranslation x p]
    exact hUP
  obtain ⟨i, hi⟩ :=
    S.exists_minimalRightAlmostSplitAt_label_of_arrowMultiplicity_pos p z hPZ
  have hiProjective : Projective (S.fgObj (B.label i)) := by
    simpa only [B, hi] using hp
  have hiNotInjective : ¬ Injective (S.fgObj (B.label i)) := by
    simpa only [B, hi] using hpNotInjective
  have hnoPI : ∀ j : B.index,
      Projective (S.fgObj (B.label j)) →
        ¬ Injective (S.fgObj (B.label j)) := by
    intro j hjProjective
    by_cases hji : j = i
    · subst j
      exact hiNotInjective
    · exact S.rightMiddleLabel_not_injective_of_ne_of_projective
        z i j hji hiProjective
  have htotal : Nat.card B.index ≤ 2 :=
    S.rightMiddle_natCard_le_of_no_projectiveInjective hbeta
      (S.leftBeta_le_two_of_beta_le_two hbeta) z hnoPI
  have htotal' : Fintype.card B.index ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using htotal
  let N := {j : B.index // ¬ Projective (S.fgObj (B.label j))}
  have hiNotRange : i ∉ Set.range (fun j : N ↦ j.1) := by
    rintro ⟨j, hj⟩
    have hji : j.1 = i := hj
    exact j.2 (hji.symm ▸ hiProjective)
  have hproper : Fintype.card N < Fintype.card B.index :=
    Fintype.card_lt_of_injective_of_notMem
      (fun j : N ↦ j.1) Subtype.val_injective hiNotRange
  have hN : Nat.card N ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    omega
  rw [S.projective_rightMiddleArity_eq_betaAt_inverseTranslation
    u hu x.2]
  have hcount := S.betaAt_eq_natCard_nonprojective_minimalRightMiddle z
  change FiniteTauMatrix.betaAt
      S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1 = Nat.card N
    at hcount
  rw [hcount]
  exact hN

/-- Under a global two-middle-term bound, a projective which occurs
irreducibly inside another projective has radical arity at most one.  The
projective occurrence itself uses one of the two places in the translated
almost-split middle. -/
theorem projective_rightMiddleArity_le_one_of_irreducible
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g)
    (hu : Projective (S.fgObj u))
    (hp : Projective (S.fgObj p)) :
    FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData u ≤ 1 := by
  classical
  let x : {i : Fin S.n // ¬ Injective (S.fgObj i)} :=
    ⟨u, S.irreducibleIntoProjective_source_not_injective u p g hg hp⟩
  let z : {i : Fin S.n // ¬ Projective (S.fgObj i)} :=
    (S.rightTranslationEquiv).symm x
  let B := S.minimalRightAlmostSplitAt z.1
  have hUP : 0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData u p :=
    S.arrowMultiplicity_pos_of_irreducible u p g hg
  have hPZ : 0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p z.1 := by
    rw [← S.arrowMultiplicity_eq_inverseTranslation x p]
    exact hUP
  obtain ⟨i, hi⟩ :=
    S.exists_minimalRightAlmostSplitAt_label_of_arrowMultiplicity_pos p z hPZ
  have hiProjective : Projective (S.fgObj (B.label i)) := by
    simpa only [B, hi] using hp
  let N := {j : B.index // ¬ Projective (S.fgObj (B.label j))}
  have hiNotRange : i ∉ Set.range (fun j : N ↦ j.1) := by
    rintro ⟨j, hj⟩
    have hji : j.1 = i := hj
    exact j.2 (hji.symm ▸ hiProjective)
  have hproper : Fintype.card N < Fintype.card B.index :=
    Fintype.card_lt_of_injective_of_notMem
      (fun j : N ↦ j.1) Subtype.val_injective hiNotRange
  have htotal : Fintype.card B.index ≤ 2 := by
    let d := S.minimalRightAlmostSplitAtDecomposition z.1
    have hcount :=
      FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
        S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1 d
          B.rightAlmostSplit B.rightMinimal
    change FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1 =
      Fintype.card B.index at hcount
    rw [← hcount]
    exact harity z.1 z.2
  have hN : Nat.card N ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    omega
  rw [S.projective_rightMiddleArity_eq_betaAt_inverseTranslation
    u hu x.2]
  have hcount := S.betaAt_eq_natCard_nonprojective_minimalRightMiddle z
  change FiniteTauMatrix.betaAt
      S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1 = Nat.card N
    at hcount
  rw [hcount]
  exact hN

/-- Finite projective-radical recursion.  A projective source of an
irreducible morphism to a projective is uniserial under the global
two-middle-term bound. -/
theorem projective_source_isUniserialModule_of_irreducible
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g)
    (hu : Projective (S.fgObj u))
    (hp : Projective (S.fgObj p)) :
    IsUniserialModule Aᵐᵒᵖ (S.fgObj u).obj := by
  classical
  generalize hn : Module.finrank k (S.fgObj u) = n
  induction n using Nat.strong_induction_on generalizing u p with
  | h n ih =>
      let J := S.projectiveBoundaryRadical u
      let j : J ⟶ S.fgObj u := S.projectiveBoundaryRadicalInclusion u
      have hJfinite : Module.Finite k J :=
        RightModule.finite_over_field_of_finitelyGenerated k A J
      letI : Module.Finite k J := hJfinite
      obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
        (k := k) J
      have hd : d.n ≤ 1 := by
        have hcount : FiniteTauMatrix.rightMiddleArity
            S.finiteTauCategoryData.toFiniteRightTauCategoryData u = d.n :=
          FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
            S.finiteTauCategoryData.toFiniteRightTauCategoryData u d
              (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit u hu)
              (S.projectiveBoundaryRadicalInclusion_isRightMinimal u)
        rw [← hcount]
        exact S.projective_rightMiddleArity_le_one_of_irreducible
          harity u p g hg hu hp
      have hJuni : IsUniserialModule Aᵐᵒᵖ J := by
        by_cases hJzero : IsZero J
        · haveI : Subsingleton J := ModuleCat.isZero_iff_subsingleton.mp
            ((forget₂ (RightModule.FinitelyGeneratedCategory A)
              (ModuleCat Aᵐᵒᵖ)).map_isZero hJzero)
          exact IsUniserialModule.of_subsingleton
        · have hJindec : Indecomposable J :=
            finiteIndecomposableDecomposition_indecomposable_of_n_le_one
              (k := k) d hd hJzero
          obtain ⟨v, ⟨e⟩⟩ := S.fgObj_complete J hJindec
          let gv : S.fgObj v ⟶ S.fgObj u := e.inv ≫ j
          have hgv : IsIrreducibleMorphism gv := by
            exact
              (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit u hu
                ).irreducible_comp_of_splitSummand j
                  (S.projectiveBoundaryRadicalInclusion_isRightMinimal u)
                  e.inv e.hom e.inv_hom_id
                  (S.fgObj_indecomposable v) (S.fgObj_indecomposable u)
          by_cases hv : Projective (S.fgObj v)
          · letI : Nontrivial (S.fgObj u) :=
              (S.fgObj_isIndecomposableModule u).nontrivial
            letI : Module.Finite k (S.fgObj u) :=
              RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj u)
            have hWProper :
                (Module.jacobson Aᵐᵒᵖ (S.fgObj u)).restrictScalars k ≠ ⊤ := by
              simpa using (Module.jacobson_lt_top Aᵐᵒᵖ (S.fgObj u)).ne
            have hJlt : Module.finrank k J < Module.finrank k (S.fgObj u) := by
              let eJ : J ≃ₗ[k]
                  (Module.jacobson Aᵐᵒᵖ
                    (S.fgObj u)).restrictScalars k := LinearEquiv.refl k _
              exact eJ.finrank_eq.trans_lt (Submodule.finrank_lt hWProper)
            have hev : Module.finrank k (S.fgObj v) = Module.finrank k J := by
              exact
                ((FGModuleCat.isoToLinearEquiv e.symm).restrictScalars k).finrank_eq
            have hvlt : Module.finrank k (S.fgObj v) < n := by
              rw [hev, ← hn]
              exact hJlt
            have hvUni : IsUniserialModule Aᵐᵒᵖ (S.fgObj v).obj :=
              ih (Module.finrank k (S.fgObj v)) hvlt
                v u gv hgv hv hu rfl
            exact IsUniserialModule.congr
              (FGModuleCat.isoToLinearEquiv e.symm) hvUni
          · have hvUni : IsUniserialModule Aᵐᵒᵖ (S.fgObj v).obj :=
              S.irreducibleIntoProjective_source_isUniserialModule
                harity v u gv hgv hu hv
            exact IsUniserialModule.congr
              (FGModuleCat.isoToLinearEquiv e.symm) hvUni
      have htop : IsSimpleModule Aᵐᵒᵖ
          (S.fgObj u ⧸ Module.jacobson Aᵐᵒᵖ (S.fgObj u)) :=
        isSimpleModule_iff_isCoatom.mpr
          (S.projectiveBoundary_jacobson_isCoatom u hu)
      exact IsUniserialModule.of_simpleTop_of_jacobson htop hJuni

/-- A global two-middle-term bound gives at most two indecomposable
summands in the radical of a noninjective indecomposable projective. -/
theorem projective_rightMiddleArity_le_two_of_global_bound
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (hpNotInjective : ¬ Injective (S.fgObj p)) :
    FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p ≤ 2 := by
  let z := (S.rightTranslationEquiv).symm ⟨p, hpNotInjective⟩
  rw [S.projective_rightMiddleArity_eq_betaAt_inverseTranslation
    p hp hpNotInjective]
  exact
    (FiniteTauMatrix.betaAt_le_rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1).trans
        (harity z.1 z.2)

/-- Every displayed indecomposable summand of a noninjective projective's
radical is uniserial under the global two-middle-term bound. -/
theorem projectiveBoundary_decomposition_summand_isUniserialModule
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (d : FiniteIndecomposableDecomposition
      (S.projectiveBoundaryRadical p)) (i : Fin d.n) :
    IsUniserialModule Aᵐᵒᵖ (d.summand i).obj := by
  classical
  let inc : d.summand i ⟶ S.projectiveBoundaryRadical p :=
    biproduct.ι d.summand i ≫ d.isoBiproduct.inv
  let proj : S.projectiveBoundaryRadical p ⟶ d.summand i :=
    d.isoBiproduct.hom ≫ biproduct.π d.summand i
  have hincproj : inc ≫ proj = 𝟙 (d.summand i) := by
    simp [inc, proj, Category.assoc]
  let f : d.summand i ⟶ S.fgObj p :=
    inc ≫ S.projectiveBoundaryRadicalInclusion p
  have hf : IsIrreducibleMorphism f :=
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp
      ).irreducible_comp_of_splitSummand
        (S.projectiveBoundaryRadicalInclusion p)
        (S.projectiveBoundaryRadicalInclusion_isRightMinimal p)
        inc proj hincproj (d.indecomposable i) (S.fgObj_indecomposable p)
  obtain ⟨v, ⟨e⟩⟩ := S.fgObj_complete (d.summand i) (d.indecomposable i)
  let fv : S.fgObj v ⟶ S.fgObj p := e.inv ≫ f
  have hfv : IsIrreducibleMorphism fv := hf.precomp_iso e.symm
  have hvUni : IsUniserialModule Aᵐᵒᵖ (S.fgObj v).obj := by
    by_cases hv : Projective (S.fgObj v)
    · exact S.projective_source_isUniserialModule_of_irreducible
        harity v p fv hfv hv hp
    · exact S.irreducibleIntoProjective_source_isUniserialModule
        harity v p fv hfv hp hv
  exact IsUniserialModule.congr
    (FGModuleCat.isoToLinearEquiv e.symm) hvUni

/-- A global right-middle arity bound is self-dual.  Contragredient duality
reverses arrows, while inverse Auslander--Reiten translation rewrites the
resulting outgoing sum as an incoming right-middle sum in the original
skeleton. -/
theorem contragredient_rightMiddleArity_le_two_of_global_bound
    [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (j : S.contragredientSkeleton.IndecCategory)
    (hj : ¬ Projective (S.contragredientSkeleton.fgObj j)) :
    FiniteTauMatrix.rightMiddleArity
        (S.contragredientSkeleton.finiteTauCategoryData
          ).toFiniteRightTauCategoryData j ≤ 2 := by
  classical
  let Sop := S.contragredientSkeleton
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let Top := Sop.finiteTauCategoryData.toFiniteRightTauCategoryData
  have hjNoninjective : ¬ Injective (S.fgObj j) := by
    intro hjInjective
    apply hj
    have hiff : Projective (Sop.fgObj j) ↔ Injective (S.fgObj j) := by
      exact (S.contragredientAlignedBiduality.forward
        |>.injective_iff_projective_image
          S.almostSplitSkeleton S.contragredientAlmostSplitSkeleton j).symm
    exact hiff.2 hjInjective
  let x : {i : Fin S.n // ¬ Injective (S.fgObj i)} :=
    ⟨j, hjNoninjective⟩
  let z : {i : Fin S.n // ¬ Projective (S.fgObj i)} :=
    (S.rightTranslationEquiv).symm x
  rw [← FiniteTauMatrix.sum_arrowMultiplicity_source Top j]
  calc
    (∑ source, FiniteTauMatrix.arrowMultiplicity Top source j) =
        ∑ source, FiniteTauMatrix.arrowMultiplicity TA j source := by
      apply Finset.sum_congr rfl
      intro source _
      exact S.contragredient_arrowMultiplicity_eq_reverse x source
    _ = ∑ source, FiniteTauMatrix.arrowMultiplicity TA source z.1 := by
      apply Finset.sum_congr rfl
      intro source _
      exact S.arrowMultiplicity_eq_inverseTranslation x source
    _ = FiniteTauMatrix.rightMiddleArity TA z.1 :=
      FiniteTauMatrix.sum_arrowMultiplicity_source TA z.1
    _ ≤ 2 := harity z.1 z.2

/-- If the nonprojective right meshes have arity at most two and a chosen
projective has projective-boundary arity at most two, then its radical is the
internal direct sum of at most two uniserial branches. -/
theorem projective_hasSeparatedUniserialJacobsonBranches_of_bounds
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (hpArity : FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p ≤ 2) :
    IsBiserialModule.HasSeparatedUniserialJacobsonBranches
      Aᵐᵒᵖ (S.fgObj p).obj := by
  classical
  let J := S.projectiveBoundaryRadical p
  have hJfinite : Module.Finite k J :=
    RightModule.finite_over_field_of_finitelyGenerated k A J
  letI : Module.Finite k J := hJfinite
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) J
  have hd : d.n ≤ 2 := by
    have hcount : FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData p = d.n :=
      FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
        S.finiteTauCategoryData.toFiniteRightTauCategoryData p d
          (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp)
          (S.projectiveBoundaryRadicalInclusion_isRightMinimal p)
    rw [← hcount]
    exact hpArity
  have hall : ∀ i : Fin d.n,
      IsUniserialModule Aᵐᵒᵖ (d.summand i).obj := fun i ↦
    S.projectiveBoundary_decomposition_summand_isUniserialModule
      harity p hp d i
  rcases d with ⟨n, F, hF, e⟩
  change n ≤ 2 at hd
  change ∀ i : Fin n, IsUniserialModule Aᵐᵒᵖ (F i).obj at hall
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn with hn | hn | hn
  · subst n
    have hsum : IsZero (⨁ F) := by
      rw [IsZero.iff_id_eq_zero]
      apply biproduct.hom_ext
      intro i
      exact Fin.elim0 i
    have hJzero : IsZero J := hsum.of_iso e
    have hJsub : Subsingleton J := ModuleCat.isZero_iff_subsingleton.mp
      ((forget₂ (RightModule.FinitelyGeneratedCategory A)
        (ModuleCat Aᵐᵒᵖ)).map_isZero hJzero)
    have hrad : Module.jacobson Aᵐᵒᵖ (S.fgObj p) = ⊥ := by
      apply le_antisymm
      · intro x hx
        have hx0 : (⟨x, hx⟩ : J) = 0 := hJsub.elim _ _
        simpa using congrArg Subtype.val hx0
      · exact bot_le
    exact ⟨⊥, ⊥, by simp [hrad], by simp,
      IsUniserialModule.of_subsingleton,
      IsUniserialModule.of_subsingleton⟩
  · subst n
    let eOne : J ≅ F default := e.trans (biproductUniqueIso F)
    have hJuni : IsUniserialModule Aᵐᵒᵖ J :=
      IsUniserialModule.congr
        (FGModuleCat.isoToLinearEquiv eOne).symm (hall default)
    exact ⟨Module.jacobson Aᵐᵒᵖ (S.fgObj p), ⊥,
      by simp, by simp, hJuni, IsUniserialModule.of_subsingleton⟩
  · subst n
    let U := forget₂ (RightModule.FinitelyGeneratedCategory A)
      (ModuleCat Aᵐᵒᵖ)
    let ePi : (⨁ F : RightModule.FinitelyGeneratedCategory A) ≃ₗ[Aᵐᵒᵖ]
        (∀ i, F i) :=
      ((U.mapIso (biproduct.isoProduct F)).toLinearEquiv).trans
        (((preservesLimitIso U (Discrete.functor F)).toLinearEquiv).trans
          (((HasLimit.isoOfNatIso
              (Discrete.compNatIsoDiscrete F U)).toLinearEquiv).trans
            (ModuleCat.piIsoPi (fun i ↦ (F i).obj)).toLinearEquiv))
    let eProd : J ≃ₗ[Aᵐᵒᵖ] (F 0) × (F 1) :=
      (FGModuleCat.isoToLinearEquiv e).trans <|
        ePi.trans (LinearEquiv.piFinTwo Aᵐᵒᵖ
          (fun i ↦ (F i : Type u)))
    exact IsBiserialModule.hasSeparatedUniserialJacobsonBranches_of_linearEquiv_prod
      eProd (hall 0) (hall 1)

/-- Under the global two-middle-term bound, the radical of every
noninjective indecomposable projective is the internal direct sum of at most
two uniserial branches. -/
theorem projective_hasSeparatedUniserialJacobsonBranches_of_global_bound
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (hpNotInjective : ¬ Injective (S.fgObj p)) :
    IsBiserialModule.HasSeparatedUniserialJacobsonBranches
      Aᵐᵒᵖ (S.fgObj p).obj :=
  S.projective_hasSeparatedUniserialJacobsonBranches_of_bounds
    harity p hp
      (S.projective_rightMiddleArity_le_two_of_global_bound
        harity p hp hpNotInjective)

/-- A total right-middle arity bound of two makes every indecomposable
projective radical an internal direct sum of at most two uniserial branches. -/
theorem projective_hasSeparatedUniserialJacobsonBranches_of_total_bound
    (harity : ∀ j : S.IndecCategory,
      FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    IsBiserialModule.HasSeparatedUniserialJacobsonBranches
      Aᵐᵒᵖ (S.fgObj p).obj :=
  S.projective_hasSeparatedUniserialJacobsonBranches_of_bounds
    (fun j _ ↦ harity j) p hp (harity p)

/-- Under the global two-middle-term bound, every noninjective
indecomposable projective is biserial. -/
theorem projective_isBiserialModule_of_global_bound
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (hpNotInjective : ¬ Injective (S.fgObj p)) :
    IsBiserialModule Aᵐᵒᵖ (S.fgObj p).obj := by
  obtain ⟨U, V, hsup, hinf, hU, hV⟩ :=
    S.projective_hasSeparatedUniserialJacobsonBranches_of_global_bound
      harity p hp hpNotInjective
  refine ⟨U, V, hsup, hU, hV, ?_⟩
  rw [hinf]
  exact IsSimpleOrZeroModule.of_subsingleton

/-- Under a total two-middle-term bound, every indecomposable projective is
biserial. -/
theorem projective_isBiserialModule_of_total_bound
    (harity : ∀ j : S.IndecCategory,
      FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    IsBiserialModule Aᵐᵒᵖ (S.fgObj p).obj := by
  obtain ⟨U, V, hsup, hinf, hU, hV⟩ :=
    S.projective_hasSeparatedUniserialJacobsonBranches_of_total_bound
      harity p hp
  refine ⟨U, V, hsup, hU, hV, ?_⟩
  rw [hinf]
  exact IsSimpleOrZeroModule.of_subsingleton

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
