import MagnitudeConjecture.Algebra.RightModuleBetaBoundary
import MagnitudeConjecture.Algebra.RightModuleRepresentationFiniteSquareFree

/-!
# The D4 boundary forced by one-sided beta failure

Translation removes every interior obstruction to comparing the two beta
invariants.  If right beta is at most two but left beta is not, the remaining
injective boundary vertex has three distinct nonprojective successors.  This
file packages those successors as literal reversed-AR-quiver arrows, retaining
the occurrence data needed by the subsequent sectional or module argument.
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

/-- Literal outgoing AR occurrences from `source` whose target is
nonprojective.  The standard-form arrow is reversed, so an element over
`target` represents an irreducible module map `source ⟶ target`. -/
abbrev NonprojectiveOutgoingOccurrence (source : Fin S.n) :=
  Σ target : {i : Fin S.n // ¬ Projective (S.fgObj i)},
    S.StandardFormArrow target.1 source

/-- Literal incoming AR occurrences at `target` whose source is
nonprojective.  In the reversed standard-form quiver these are arrows from
`target` to the displayed source. -/
abbrev NonprojectiveIncomingOccurrence (target : Fin S.n) :=
  Σ source : {i : Fin S.n // ¬ Projective (S.fgObj i)},
    S.StandardFormArrow target source.1

/-- The occurrence type has the cardinality recorded by the numerical
nonprojective outgoing count. -/
theorem natCard_nonprojectiveOutgoingOccurrence (source : Fin S.n) :
    Nat.card (S.NonprojectiveOutgoingOccurrence source) =
      S.nonprojectiveOutgoingAt source := by
  classical
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  rw [Nat.card_sigma]
  unfold nonprojectiveOutgoingAt
  calc
    (∑ target : {i : Fin S.n // ¬ Projective (S.fgObj i)},
        Nat.card (S.StandardFormArrow target.1 source)) =
        ∑ target : {i : Fin S.n // ¬ Projective (S.fgObj i)},
          FiniteTauMatrix.arrowMultiplicity T source target.1 := by
      apply Finset.sum_congr rfl
      intro target _
      exact S.natCard_standardFormArrow target.1 source
    _ = ∑ target ∈ Finset.univ.filter
          (fun i : Fin S.n ↦ ¬ Projective (S.fgObj i)),
        FiniteTauMatrix.arrowMultiplicity T source target := by
      exact (Finset.sum_subtype
        (p := fun i : Fin S.n ↦ ¬ Projective (S.fgObj i))
        (Finset.univ.filter
          (fun i : Fin S.n ↦ ¬ Projective (S.fgObj i)))
        (by simp)
        (fun target : Fin S.n ↦
          FiniteTauMatrix.arrowMultiplicity T source target)).symm
    _ = ∑ target,
          if Projective (S.fgObj target) then 0 else
            FiniteTauMatrix.arrowMultiplicity T source target := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro target _
      by_cases htarget : Projective (S.fgObj target) <;>
        simp [htarget]

/-- The incoming occurrence type has cardinality `betaAt`. -/
theorem natCard_nonprojectiveIncomingOccurrence (target : Fin S.n) :
    Nat.card (S.NonprojectiveIncomingOccurrence target) =
      FiniteTauMatrix.betaAt
        S.finiteTauCategoryData.toFiniteRightTauCategoryData target := by
  classical
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  rw [Nat.card_sigma]
  unfold FiniteTauMatrix.betaAt
  calc
    (∑ source : {i : Fin S.n // ¬ Projective (S.fgObj i)},
        Nat.card (S.StandardFormArrow target source.1)) =
        ∑ source : {i : Fin S.n // ¬ Projective (S.fgObj i)},
          FiniteTauMatrix.arrowMultiplicity T source.1 target := by
      apply Finset.sum_congr rfl
      intro source _
      exact S.natCard_standardFormArrow target source.1
    _ = ∑ source ∈ Finset.univ.filter
          (fun i : Fin S.n ↦ ¬ Projective (S.fgObj i)),
        FiniteTauMatrix.arrowMultiplicity T source target := by
      exact (Finset.sum_subtype
        (p := fun i : Fin S.n ↦ ¬ Projective (S.fgObj i))
        (Finset.univ.filter
          (fun i : Fin S.n ↦ ¬ Projective (S.fgObj i)))
        (by simp)
        (fun source : Fin S.n ↦
          FiniteTauMatrix.arrowMultiplicity T source target)).symm
    _ = ∑ source,
          if Projective (S.fgObj source) then 0 else
            FiniteTauMatrix.arrowMultiplicity T source target := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro source _
      by_cases hsource : Projective (S.fgObj source) <;>
        simp [hsource]
    _ = ∑ source,
          if T.IsProjective source then 0 else
            FiniteTauMatrix.arrowMultiplicity T source target := by
      apply Finset.sum_congr rfl
      intro source _
      rw [FiniteTauMatrix.isProjective_iff_projective_obj,
        S.finiteTauCategoryData_obj]

/-- A literal three-armed boundary fork.  Its arrows point from the center to
the three targets in the module AR quiver (and hence from each target to the
center in the standard-form quiver). -/
structure InjectiveNonprojectiveD4Fork where
  center : {i : Fin S.n // ¬ Projective (S.fgObj i)}
  center_injective : Injective (S.fgObj center.1)
  target : Fin 3 → {i : Fin S.n // ¬ Projective (S.fgObj i)}
  arrow : ∀ j, S.StandardFormArrow (target j).1 center.1
  target_injective : Function.Injective target

/-- The actual irreducible quotient map represented by one fork arm. -/
def InjectiveNonprojectiveD4Fork.outgoingMap
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    S.fgObj F.center.1 ⟶ S.fgObj (F.target j).1 :=
  S.standardFormArrowMap (F.arrow j)

/-- Every fork arm is an epimorphism: a monic irreducible map out of the
injective center would split. -/
theorem InjectiveNonprojectiveD4Fork.outgoingMap_epi
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    Epi (F.outgoingMap S j) := by
  let f := F.outgoingMap S j
  have hf : IsIrreducibleMorphism f :=
    S.standardFormArrowMap_isIrreducible (F.arrow j)
  rcases hf.mono_or_epi with hmono | hepi
  · letI : Mono f := hmono
    letI : Injective (S.fgObj F.center.1) := F.center_injective
    exfalso
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := Injective.factorThru (𝟙 (S.fgObj F.center.1)) f
        id := Injective.comp_factorThru (𝟙 (S.fgObj F.center.1)) f }
  · exact hepi

/-- Every target of the injective boundary fork has strictly smaller
coefficient-field dimension than its center. -/
theorem InjectiveNonprojectiveD4Fork.target_objectFinrank_lt_center
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    S.objectFinrank (F.target j).1 < S.objectFinrank F.center.1 := by
  let f := F.outgoingMap S j
  letI : Epi f := F.outgoingMap_epi S j
  exact S.objectFinrank_lt_of_irreducible_epi f
    (S.standardFormArrowMap_isIrreducible (F.arrow j))

/-- The source paired to one arm by the mesh polarization. -/
def InjectiveNonprojectiveD4Fork.translatedTarget
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) : Fin S.n :=
  (S.rightTranslationEquiv (F.target j)).1

/-- A translated fork target is noninjective. -/
theorem InjectiveNonprojectiveD4Fork.translatedTarget_not_injective
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    ¬ Injective (S.fgObj (F.translatedTarget S j)) :=
  (S.rightTranslationEquiv (F.target j)).2

/-- Polarizing an outgoing fork arrow gives an incoming arrow from its
translated target to the center. -/
def InjectiveNonprojectiveD4Fork.translatedArrow
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    S.StandardFormArrow F.center.1 (F.translatedTarget S j) := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  let z : {x : Fin S.n // x ∉ S.standardFormProjectiveSet} :=
    ⟨(F.target j).1, by
      simpa [standardFormProjectiveSet] using (F.target j).2⟩
  have a := S.standardFormRightMeshData.arrowEquiv z F.center.1 (F.arrow j)
  change S.StandardFormArrow F.center.1 (S.standardFormTau z) at a
  have htau : S.standardFormTau z = F.translatedTarget S j := by
    unfold standardFormTau InjectiveNonprojectiveD4Fork.translatedTarget
    congr 2
  rw [htau] at a
  exact a

/-- Distinct fork arms have distinct translated targets. -/
theorem InjectiveNonprojectiveD4Fork.translatedTarget_injective
    (F : S.InjectiveNonprojectiveD4Fork) :
    Function.Injective (F.translatedTarget S) := by
  intro i j hij
  apply F.target_injective
  apply S.rightTranslationEquiv.injective
  apply Subtype.ext
  exact hij

/-- If right beta is at most two, a three-armed boundary fork has a
projective translated arm.  Otherwise polarization would inject its three
arms into the nonprojective incoming occurrences at the center. -/
theorem InjectiveNonprojectiveD4Fork.exists_projective_translatedTarget
    (F : S.InjectiveNonprojectiveD4Fork)
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    ∃ j : Fin 3, Projective (S.fgObj (F.translatedTarget S j)) := by
  classical
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  by_contra hprojective
  simp only [not_exists] at hprojective
  let occurrence : Fin 3 → S.NonprojectiveIncomingOccurrence F.center.1 :=
    fun j ↦ ⟨⟨F.translatedTarget S j, hprojective j⟩,
      F.translatedArrow S j⟩
  have hOccurrence : Function.Injective occurrence := by
    intro i j hij
    apply F.translatedTarget_injective S
    simpa [occurrence] using congrArg (fun q ↦ q.1.1) hij
  have hthree : 3 ≤ Nat.card
      (S.NonprojectiveIncomingOccurrence F.center.1) := by
    simpa using Nat.card_le_card_of_injective occurrence hOccurrence
  have hcenter : ¬
      S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
        F.center.1 := by
    rw [FiniteTauMatrix.isProjective_iff_projective_obj]
    exact F.center.2
  have htwo : FiniteTauMatrix.betaAt
      S.finiteTauCategoryData.toFiniteRightTauCategoryData F.center.1 ≤ 2 :=
    (FiniteTauMatrix.beta_le_iff
      S.finiteTauCategoryData.toFiniteRightTauCategoryData 2).1
        hbeta F.center.1 hcenter
  rw [S.natCard_nonprojectiveIncomingOccurrence F.center.1] at hthree
  omega

/-- Three distinct outgoing occurrences determine a literal `D4` boundary
fork.  Representation-finite square-freeness is what makes their target
labels distinct rather than merely their occurrence indices. -/
theorem exists_injectiveNonprojectiveD4Fork_of_boundary
    (z : {i : Fin S.n // ¬ Projective (S.fgObj i)})
    (hzInjective : Injective (S.fgObj z.1))
    (hz : 3 ≤ S.nonprojectiveOutgoingAt z.1) :
    Nonempty S.InjectiveNonprojectiveD4Fork := by
  classical
  let Occ := S.NonprojectiveOutgoingOccurrence z.1
  letI : Fintype Occ := Fintype.ofFinite Occ
  have hcard : 3 ≤ Fintype.card Occ := by
    rw [← Nat.card_eq_fintype_card,
      S.natCard_nonprojectiveOutgoingOccurrence z.1]
    exact hz
  let occurrence : Fin 3 → Occ := fun j ↦
    (Fintype.equivFin Occ).symm (Fin.castLE hcard j)
  have hOccurrence : Function.Injective occurrence :=
    (Fintype.equivFin Occ).symm.injective.comp
      (Fin.castLE_injective hcard)
  let target : Fin 3 → {i : Fin S.n // ¬ Projective (S.fgObj i)} :=
    fun j ↦ (occurrence j).1
  have htarget : Function.Injective target := by
    intro i j hij
    apply hOccurrence
    rcases hi : occurrence i with ⟨ti, ai⟩
    rcases hj : occurrence j with ⟨tj, aj⟩
    have ht : ti = tj := by
      simpa [target, hi, hj] using hij
    subst tj
    have ha : ai = aj :=
      (S.standardFormArrow_subsingleton _ _).elim _ _
    subst aj
    rfl
  exact ⟨
    { center := z
      center_injective := hzInjective
      target := target
      arrow := fun j ↦ (occurrence j).2
      target_injective := htarget }⟩

/-- Under `beta ≤ 2`, failure of the opposite beta bound yields the canonical
three-armed injective boundary fork. -/
theorem exists_injectiveNonprojectiveD4Fork_of_beta_le_two
    (hbeta : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2)
    (hleft : ¬ S.leftBeta ≤ 2) :
    Nonempty S.InjectiveNonprojectiveD4Fork := by
  obtain ⟨z, hzInjective, hz⟩ :=
    S.exists_injective_nonprojective_boundary_of_beta_le_two hbeta hleft
  exact S.exists_injectiveNonprojectiveD4Fork_of_boundary
    z hzInjective hz

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
