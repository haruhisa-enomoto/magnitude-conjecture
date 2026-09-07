import MagnitudeConjecture.CategoryTheory.FiniteTauOccurrences
import MagnitudeConjecture.CategoryTheory.AlmostSplitMultiplicity
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaKrullSchmidtWeight

/-!
# The nonprojective middle-term bound of a finite tau-category

For a nonprojective endpoint, `betaAt` counts the nonprojective
indecomposable occurrences in its chosen right almost-split middle term.
`beta` is the maximum of these counts.  Both definitions retain repeated
summands.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.Iyama

namespace MagnitudeConjecture.FiniteTauMatrix

universe v u w v' u'

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
  [HasFiniteBiproducts D] [HasBinaryBiproducts D]
  [IsIdempotentComplete D]
variable {Ind : Type w} [Fintype Ind]

/-- Number of nonprojective indecomposable occurrences in the chosen
right-mesh middle term ending at `target`. -/
def betaAt (T : FiniteRightTauCategoryData C Ind) (target : Ind) : ℕ := by
  classical
  exact ∑ source,
    if T.IsProjective source then 0 else arrowMultiplicity T source target

/-- A nonprojective right-middle occurrence is a displayed indecomposable
summand of the chosen right-mesh middle term whose label is nonprojective. -/
abbrev NonprojectiveRightMiddleOccurrence
    (T : FiniteRightTauCategoryData C Ind) (target : Ind) :=
  {i : Fin (rightMiddleArity T target) //
    ¬ T.IsProjective (rightMiddleLabel T target i)}

/-- `betaAt` counts the nonprojective occurrences in any displayed
indecomposable decomposition of the chosen right-mesh middle term.  Thus a
later structural argument may use its own explicit decomposition instead of
the noncomputable one used to define `arrowMultiplicity`. -/
theorem betaAt_eq_natCard_nonprojective_of_rightMiddleDecomposition
    (T : FiniteRightTauCategoryData C Ind) (target : Ind)
    {m : ℕ} (label : Fin m → Ind)
    (decomposition : Nonempty
      ((T.rightMesh (T.obj target)).X₂ ≅
        ⨁ fun i ↦ T.obj (label i))) :
    betaAt T target = Nat.card {i : Fin m //
      ¬ T.IsProjective (label i)} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold betaAt
  calc
    (∑ source, if T.IsProjective source then 0
        else arrowMultiplicity T source target) =
        ∑ source, arrowMultiplicity T source target *
          (if T.IsProjective source then 0 else 1) := by
            apply Finset.sum_congr rfl
            intro source _
            split_ifs <;> simp
    _ = ∑ i : Fin (rightMiddleArity T target),
          (if T.IsProjective (rightMiddleLabel T target i) then 0 else 1) :=
      sum_arrowMultiplicity_mul T target
        (fun source ↦ if T.IsProjective source then 0 else 1)
    _ = ∑ i : Fin m,
          (if T.IsProjective (label i) then 0 else 1) := by
      obtain ⟨eChosen⟩ := rightMiddleIso T target
      obtain ⟨eDisplayed⟩ := decomposition
      exact T.sum_weight_eq_of_nonempty_iso_finBiproduct_obj
        (M := ℕ) (fun source ↦
          if T.IsProjective source then 0 else 1)
        (rightMiddleArity T target) m
        (rightMiddleLabel T target) label
        ⟨eChosen.symm.trans eDisplayed⟩
    _ = ∑ i : Fin m,
          if ¬ T.IsProjective (label i) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : T.IsProjective (label i) <;> simp [h]
    _ = _ := by
      rw [Finset.card_filter]

/-- `betaAt` is the literal cardinality of the nonprojective occurrences in
the chosen right-mesh middle term.  In particular, repeated isomorphic
summands remain distinct occurrences. -/
theorem betaAt_eq_natCard_nonprojectiveRightMiddleOccurrence
    (T : FiniteRightTauCategoryData C Ind) (target : Ind) :
    betaAt T target =
      Nat.card (NonprojectiveRightMiddleOccurrence T target) :=
  betaAt_eq_natCard_nonprojective_of_rightMiddleDecomposition
    T target (rightMiddleLabel T target) (rightMiddleIso T target)

/-- Discarding the projective summands of a right-mesh middle term can only
decrease its number of indecomposable occurrences. -/
theorem betaAt_le_rightMiddleArity
    (T : FiniteRightTauCategoryData C Ind) (target : Ind) :
    betaAt T target ≤ rightMiddleArity T target := by
  classical
  unfold betaAt
  rw [← sum_arrowMultiplicity_source T target]
  apply Finset.sum_le_sum
  intro source _
  by_cases hsource : T.IsProjective source
  · simp [hsource]
  · simp [hsource]

/-- If one displayed middle-term summand is projective, then the
nonprojective occurrence count is at least one smaller than the total
displayed arity. -/
theorem betaAt_add_one_le_of_rightMiddleDecomposition_projective
    (T : FiniteRightTauCategoryData C Ind) (target : Ind)
    {m : ℕ} (label : Fin m → Ind)
    (decomposition : Nonempty
      ((T.rightMesh (T.obj target)).X₂ ≅
        ⨁ fun i ↦ T.obj (label i)))
    (i : Fin m) (hi : T.IsProjective (label i)) :
    betaAt T target + 1 ≤ m := by
  classical
  rw [betaAt_eq_natCard_nonprojective_of_rightMiddleDecomposition
    T target label decomposition, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  let s : Finset (Fin m) := Finset.univ.filter fun j ↦
    ¬ T.IsProjective (label j)
  have his : i ∉ s := by simp [s, hi]
  have hssubset : s ⊆ (Finset.univ : Finset (Fin m)) :=
    Finset.subset_univ s
  have hsne : s ≠ (Finset.univ : Finset (Fin m)) := by
    intro h
    exact his (h.symm ▸ Finset.mem_univ i)
  have hcard : s.card < (Finset.univ : Finset (Fin m)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hssubset, hsne⟩)
  change s.card + 1 ≤ m
  simpa using hcard

/-- The preceding estimate may be read from any finite indecomposable
decomposition of any right-minimal right almost-split map to the endpoint;
uniqueness of minimal right almost-split sources identifies it with the
chosen right mesh. -/
theorem betaAt_add_one_le_of_minimalRightAlmostSplitDecomposition_projective
    (T : FiniteRightTauCategoryData C Ind) (target : Ind)
    {E : C} {f : E ⟶ T.obj target}
    {m : ℕ} (label : Fin m → Ind)
    (decomposition : Nonempty (E ≅ ⨁ fun i ↦ T.obj (label i)))
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f)
    (i : Fin m) (hi : T.IsProjective (label i)) :
    betaAt T target + 1 ≤ m := by
  let g := (T.rightMesh (T.obj target)).g ≫
    (T.rightTermIso (T.obj target)).hom
  have hg : IsRightAlmostSplit g :=
    rightMesh_terminal_isRightAlmostSplit T target
  have hgmin : IsRightMinimal g :=
    rightMesh_terminal_isRightMinimal T target
  obtain ⟨eMiddle, -⟩ :=
    QuotientSubmoduleEquidistribution.exists_rightAlmostSplit_middleIso
      hg hgmin hf hfmin
  exact betaAt_add_one_le_of_rightMiddleDecomposition_projective
    T target label ⟨eMiddle.trans (Classical.choice decomposition)⟩ i hi

/-- Maximum number of nonprojective indecomposable occurrences in a chosen
right almost-split middle term.  Projective endpoints contribute zero. -/
def beta (T : FiniteRightTauCategoryData C Ind) : ℕ := by
  classical
  exact Finset.univ.sup fun target ↦
    if T.IsProjective target then 0 else betaAt T target

theorem betaAt_eq_of_projective_iff_of_arrowMultiplicity_eq
    (T : FiniteRightTauCategoryData C Ind)
    (U : FiniteRightTauCategoryData D Ind)
    (hprojective : ∀ i, T.IsProjective i ↔ U.IsProjective i)
    (harrow : ∀ source target,
      arrowMultiplicity T source target =
        arrowMultiplicity U source target)
    (target : Ind) :
    betaAt T target = betaAt U target := by
  classical
  unfold betaAt
  apply Finset.sum_congr rfl
  intro source _
  by_cases hsource : T.IsProjective source
  · rw [if_pos hsource, if_pos ((hprojective source).1 hsource)]
  · rw [if_neg hsource,
      if_neg (fun h ↦ hsource ((hprojective source).2 h)),
      harrow]

theorem beta_eq_of_projective_iff_of_arrowMultiplicity_eq
    (T : FiniteRightTauCategoryData C Ind)
    (U : FiniteRightTauCategoryData D Ind)
    (hprojective : ∀ i, T.IsProjective i ↔ U.IsProjective i)
    (harrow : ∀ source target,
      arrowMultiplicity T source target =
        arrowMultiplicity U source target) :
    beta T = beta U := by
  classical
  unfold beta
  apply Finset.sup_congr rfl
  intro target _
  by_cases htarget : T.IsProjective target
  · rw [if_pos htarget, if_pos ((hprojective target).1 htarget)]
  · rw [if_neg htarget,
      if_neg (fun h ↦ htarget ((hprojective target).2 h)),
      betaAt_eq_of_projective_iff_of_arrowMultiplicity_eq
        T U hprojective harrow target]

/-- A bound on `beta` is exactly a bound on the nonprojective middle
occurrences at every nonprojective endpoint. -/
theorem beta_le_iff
    (T : FiniteRightTauCategoryData C Ind) (bound : ℕ) :
    beta T ≤ bound ↔
      ∀ target, ¬ T.IsProjective target → betaAt T target ≤ bound := by
  classical
  constructor
  · intro hbeta target htarget
    have hle :
        (if T.IsProjective target then 0 else betaAt T target) ≤ beta T := by
      unfold beta
      exact Finset.le_sup
        (s := Finset.univ)
        (f := fun target ↦
          if T.IsProjective target then 0 else betaAt T target)
        (Finset.mem_univ target)
    simpa [htarget] using hle.trans hbeta
  · intro h
    unfold beta
    rw [Finset.sup_le_iff]
    intro target _
    by_cases htarget : T.IsProjective target
    · simp [htarget]
    · simpa [htarget] using h target htarget

/-- A uniform bound on the total arity of nonprojective right-mesh middle
terms also bounds `beta`. -/
theorem beta_le_of_rightMiddleArity_le
    (T : FiniteRightTauCategoryData C Ind) (bound : ℕ)
    (h : ∀ target, ¬ T.IsProjective target →
      rightMiddleArity T target ≤ bound) :
    beta T ≤ bound := by
  rw [beta_le_iff]
  intro target htarget
  exact (betaAt_le_rightMiddleArity T target).trans (h target htarget)

/-- To prove a uniform `beta` bound, it suffices to inject the
nonprojective occurrences in every nonprojective right-mesh middle term into
a fixed finite set. -/
theorem beta_le_of_nonprojectiveRightMiddleOccurrence_embedding
    (T : FiniteRightTauCategoryData C Ind) (bound : ℕ)
    (embed : ∀ target, ¬ T.IsProjective target →
      NonprojectiveRightMiddleOccurrence T target ↪ Fin bound) :
    beta T ≤ bound := by
  classical
  rw [beta_le_iff]
  intro target htarget
  rw [betaAt_eq_natCard_nonprojectiveRightMiddleOccurrence]
  rw [Nat.card_eq_fintype_card, ← Fintype.card_fin bound]
  exact Fintype.card_le_of_injective
    (embed target htarget) (embed target htarget).injective

/-- A structural description may choose a convenient indecomposable
decomposition separately at every nonprojective endpoint.  Bounding the
nonprojective occurrences in those displayed decompositions bounds `beta`,
independently of all noncomputable decomposition choices in the finite-tau
data. -/
theorem beta_le_of_rightMiddleDecomposition_nonprojective_card_le
    (T : FiniteRightTauCategoryData C Ind) (bound : ℕ)
    (display : ∀ target, ¬ T.IsProjective target →
      ∃ (m : ℕ) (label : Fin m → Ind),
        Nonempty
          ((T.rightMesh (T.obj target)).X₂ ≅
            ⨁ fun i ↦ T.obj (label i)) ∧
        Nat.card {i : Fin m // ¬ T.IsProjective (label i)} ≤ bound) :
    beta T ≤ bound := by
  rw [beta_le_iff]
  intro target htarget
  obtain ⟨m, label, decomposition, hcard⟩ := display target htarget
  rw [betaAt_eq_natCard_nonprojective_of_rightMiddleDecomposition
    T target label decomposition]
  exact hcard

end MagnitudeConjecture.FiniteTauMatrix
