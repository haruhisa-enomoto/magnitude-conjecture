import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiverSpecialBiserialAssembly

/-!
# Finite correction of ordinary-arrow representatives

Skowroński--Waschbüsch construct special-biserial representatives by
successively changing an arrow by a radical-square term.  Each change retains
every two-arrow composite which was already zero and makes at least one
additional composite zero.  This file makes the finite termination argument
literal.

The remaining algebraic input is consequently local: whenever one of the two
continuation bounds fails, produce one such zero-preserving correction.  No
induction or global compatibility is left in that input.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

local instance ordinaryAdaptedQuiver : Quiver S.ProjectiveLabel :=
  S.ordinaryQuiver

local instance ordinaryAdaptedArrowFintype (x y : S.ProjectiveLabel) :
    Fintype (x ⟶ y) :=
  S.ordinaryArrowFintype x y

/-- A composable pair of ordinary arrows, retaining its three vertices. -/
abbrev OrdinaryTwoStep (S : RightModule.FiniteIndecomposableSkeleton k A) :=
  Σ x : S.ProjectiveLabel, Σ y : S.ProjectiveLabel,
    Σ z : S.ProjectiveLabel,
      S.OrdinaryArrow x y × S.OrdinaryArrow y z

/-- An ordinary arrow together with its source and target. -/
abbrev OrdinaryArrowTotal
    (S : RightModule.FiniteIndecomposableSkeleton k A) :=
  Σ x : S.ProjectiveLabel, Σ y : S.ProjectiveLabel,
    S.OrdinaryArrow x y

noncomputable instance ordinaryTwoStepFintype : Fintype S.OrdinaryTwoStep :=
  Fintype.ofFinite S.OrdinaryTwoStep

namespace OrdinaryArrowRepresentatives

/-- A literal failure witness for the right-continuation bound: two distinct
arrows follow the same arrow with nonzero composites. -/
structure RightContinuationFork (D : S.OrdinaryArrowRepresentatives) where
  startVertex : S.ProjectiveLabel
  middleVertex : S.ProjectiveLabel
  first : S.OrdinaryArrow startVertex middleVertex
  following₁ :
    {b : Quiver.Star middleVertex // D.hom b.2 ≫ D.hom first ≠ 0}
  following₂ :
    {b : Quiver.Star middleVertex // D.hom b.2 ≫ D.hom first ≠ 0}
  distinct : following₁ ≠ following₂

/-- A literal failure witness for the left-continuation bound: two distinct
arrows precede the same arrow with nonzero composites. -/
structure LeftContinuationFork (D : S.OrdinaryArrowRepresentatives) where
  middleVertex : S.ProjectiveLabel
  targetVertex : S.ProjectiveLabel
  second : S.OrdinaryArrow middleVertex targetVertex
  preceding₁ :
    {c : Quiver.Costar middleVertex // D.hom second ≫ D.hom c.2 ≠ 0}
  preceding₂ :
    {c : Quiver.Costar middleVertex // D.hom second ≫ D.hom c.2 ≠ 0}
  distinct : preceding₁ ≠ preceding₂

/-- The radical-square correction space belonging to a total ordinary
arrow. -/
def arrowCorrectionSpace (a : S.OrdinaryArrowTotal) :=
  S.projectiveRadicalSquareSubmodule a.1 a.2.1

/-- The radical-square perturbation supported at one total ordinary arrow. -/
def perturbationAt (a : S.OrdinaryArrowTotal)
    (r : arrowCorrectionSpace a) :
    ∀ {x y : S.ProjectiveLabel} (_ : S.OrdinaryArrow x y),
      S.projectiveRadicalSquareSubmodule x y := by
  intro x y b
  classical
  by_cases hx : x = a.1
  · subst x
    by_cases hy : y = a.2.1
    · subst y
      exact if b = a.2.2 then r else 0
    · exact 0
  · exact 0

/-- Change exactly one arrow representative by the supplied radical-square
term. -/
def perturbAt (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1) :
    S.OrdinaryArrowRepresentatives :=
  D.perturb (perturbationAt a r)

/-- The radical-square correction `-(x ≫ a)` obtained from a radical
endomorphism of the domain of the arrow representative `a`. -/
def domainCorrection (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (x : S.ordinaryProjectiveObj a.2.1 ⟶
      S.ordinaryProjectiveObj a.2.1)
    (hx : x ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.2.1)
      (S.ordinaryProjectiveObj a.2.1)) :
    S.projectiveRadicalSquareSubmodule a.1 a.2.1 := by
  refine ⟨-(x ≫ D.hom a.2.2), ?_⟩
  apply neg_mem
  change x ≫ D.hom a.2.2 ∈
    (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _
  rw [show 2 = 1 + 1 by omega,
    QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.pow_add,
    QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.pow_one]
  exact
    QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.comp_mem_mul
      hx (D.hom_mem_radical a.2.2)

/-- The radical-square correction `-(a ≫ y)` obtained from a radical
endomorphism of the codomain of the arrow representative `a`. -/
def codomainCorrection (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (y : S.ordinaryProjectiveObj a.1 ⟶
      S.ordinaryProjectiveObj a.1)
    (hy : y ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.1)
      (S.ordinaryProjectiveObj a.1)) :
    S.projectiveRadicalSquareSubmodule a.1 a.2.1 := by
  refine ⟨-(D.hom a.2.2 ≫ y), ?_⟩
  apply neg_mem
  change D.hom a.2.2 ≫ y ∈
    (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _
  rw [show 2 = 1 + 1 by omega,
    QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.pow_add,
    QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.pow_one]
  exact
    QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.comp_mem_mul
      (D.hom_mem_radical a.2.2) hy

@[simp]
theorem perturbationAt_self (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1) :
    perturbationAt a r a.2.2 = r := by
  classical
  simp [perturbationAt]

@[simp]
theorem perturbAt_hom_self (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1) :
    (D.perturbAt a r).hom a.2.2 = D.hom a.2.2 + r.1 := by
  simp [perturbAt]

theorem perturbationAt_eq_zero_of_ne (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1)
    {x y : S.ProjectiveLabel} (b : S.OrdinaryArrow x y)
    (hba : (⟨x, y, b⟩ : S.OrdinaryArrowTotal) ≠ a) :
    perturbationAt a r b = 0 := by
  classical
  by_cases hx : x = a.1
  · subst x
    by_cases hy : y = a.2.1
    · subst y
      have hb : b ≠ a.2.2 := by
        intro hb
        subst b
        exact hba rfl
      simp [perturbationAt, hb]
    · simp [perturbationAt, hy]
  · simp [perturbationAt, hx]

theorem perturbAt_hom_eq_of_ne (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1)
    {x y : S.ProjectiveLabel} (b : S.OrdinaryArrow x y)
    (hba : (⟨x, y, b⟩ : S.OrdinaryArrowTotal) ≠ a) :
    (D.perturbAt a r).hom b = D.hom b := by
  rw [perturbAt, perturb_hom,
    perturbationAt_eq_zero_of_ne a r b hba]
  simp

/-- The selected-projective composite represented by a composable pair of
ordinary arrows. -/
def twoStepComposite (D : S.OrdinaryArrowRepresentatives)
    (q : S.OrdinaryTwoStep) :
    S.ordinaryProjectiveObj q.2.2.1 ⟶
      S.ordinaryProjectiveObj q.1 :=
  D.hom q.2.2.2.2 ≫ D.hom q.2.2.2.1

/-- The first total arrow in a two-step path. -/
def OrdinaryTwoStep.firstArrow (q : S.OrdinaryTwoStep) :
    S.OrdinaryArrowTotal :=
  ⟨q.1, q.2.1, q.2.2.2.1⟩

/-- The second total arrow in a two-step path. -/
def OrdinaryTwoStep.secondArrow (q : S.OrdinaryTwoStep) :
    S.OrdinaryArrowTotal :=
  ⟨q.2.1, q.2.2.1, q.2.2.2.2⟩

/-- A two-step path is incident to an arrow if that arrow is one of its two
steps. -/
def OrdinaryTwoStep.UsesArrow (q : S.OrdinaryTwoStep)
    (a : S.OrdinaryArrowTotal) : Prop :=
  OrdinaryTwoStep.firstArrow q = a ∨ OrdinaryTwoStep.secondArrow q = a

/-- Perturbing one arrow leaves every nonincident two-step composite
unchanged. -/
theorem perturbAt_twoStepComposite_eq_of_not_uses
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1)
    (q : S.OrdinaryTwoStep) (hq : ¬ OrdinaryTwoStep.UsesArrow q a) :
    (D.perturbAt a r).twoStepComposite q = D.twoStepComposite q := by
  rw [twoStepComposite, twoStepComposite]
  rw [D.perturbAt_hom_eq_of_ne a r q.2.2.2.2
      (fun h ↦ hq (Or.inr h)),
    D.perturbAt_hom_eq_of_ne a r q.2.2.2.1
      (fun h ↦ hq (Or.inl h))]

/-- A one-arrow perturbation preserves the zero composites incident to its
support.  This is the precise local obligation in the SW replacement step. -/
def PreservesIncidentZeros (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1) : Prop :=
  ∀ q : S.OrdinaryTwoStep, OrdinaryTwoStep.UsesArrow q a →
    D.twoStepComposite q = 0 →
      (D.perturbAt a r).twoStepComposite q = 0

/-- The changed representative factors through the old one on both sides.
This is a useful sufficient condition for preserving all old two-arrow zero
relations; the actual asymmetric SW replacement below needs only one side. -/
def HasTwoSidedFactorization (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1) : Prop :=
  ∃ (u : S.ordinaryProjectiveObj a.2.1 ⟶
      S.ordinaryProjectiveObj a.2.1)
      (v : S.ordinaryProjectiveObj a.1 ⟶
        S.ordinaryProjectiveObj a.1),
    (D.perturbAt a r).hom a.2.2 = u ≫ D.hom a.2.2 ∧
      (D.perturbAt a r).hom a.2.2 = D.hom a.2.2 ≫ v

/-- No zero two-step composite has `a` as its first arrow. -/
def NoZeroWhenFirst (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal) : Prop :=
  ∀ q : S.OrdinaryTwoStep,
    OrdinaryTwoStep.firstArrow q = a → D.twoStepComposite q ≠ 0

/-- No zero two-step composite has `a` as its second arrow. -/
def NoZeroWhenSecond (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal) : Prop :=
  ∀ q : S.OrdinaryTwoStep,
    OrdinaryTwoStep.secondArrow q = a → D.twoStepComposite q ≠ 0

/-- If at most two arrows end at a vertex and two distinct such arrows have
nonzero composite with `a`, then no arrow preceding `a` has zero composite.
This is the finite-degree step in the asymmetric SW correction. -/
theorem noZeroWhenSecond_of_costar_card_le_two
    (D : S.OrdinaryArrowRepresentatives)
    {y z : S.ProjectiveLabel} (a : S.OrdinaryArrow y z)
    (c₁ c₂ : Quiver.Costar y) (hc : c₁ ≠ c₂)
    (h₁ : D.hom a ≫ D.hom c₁.2 ≠ 0)
    (h₂ : D.hom a ≫ D.hom c₂.2 ≠ 0)
    (hcard : Nat.card (Quiver.Costar y) ≤ 2) :
    D.NoZeroWhenSecond ⟨y, z, a⟩ := by
  intro q hsecond
  rcases q with ⟨x, y', z', α, β⟩
  change (⟨y', z', β⟩ : S.OrdinaryArrowTotal) = ⟨y, z, a⟩ at hsecond
  cases hsecond
  change D.hom a ≫ D.hom α ≠ 0
  intro hzero
  let c : Quiver.Costar y := ⟨x, α⟩
  have hc₁ : c ≠ c₁ := by
    intro heq
    apply h₁
    rw [← heq]
    exact hzero
  have hc₂ : c ≠ c₂ := by
    intro heq
    apply h₂
    rw [← heq]
    exact hzero
  let f : Fin 3 → Quiver.Costar y := ![c₁, c₂, c]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hc (by simpa [f] using hij)).elim
    · exact (hc₁ (by simpa [f] using hij.symm)).elim
    · exact (hc (by simpa [f] using hij.symm)).elim
    · rfl
    · exact (hc₂ (by simpa [f] using hij.symm)).elim
    · exact (hc₁ (by simpa [f] using hij)).elim
    · exact (hc₂ (by simpa [f] using hij)).elim
    · rfl
  have hthree : 3 ≤ Nat.card (Quiver.Costar y) := by
    simpa using Nat.card_le_card_of_injective f hf
  omega

/-- The left-right symmetric finite-degree criterion: two distinct nonzero
arrows following `a` exhaust a star of cardinality at most two. -/
theorem noZeroWhenFirst_of_star_card_le_two
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y)
    (b₁ b₂ : Quiver.Star y) (hb : b₁ ≠ b₂)
    (h₁ : D.hom b₁.2 ≫ D.hom a ≠ 0)
    (h₂ : D.hom b₂.2 ≫ D.hom a ≠ 0)
    (hcard : Nat.card (Quiver.Star y) ≤ 2) :
    D.NoZeroWhenFirst ⟨x, y, a⟩ := by
  intro q hfirst
  rcases q with ⟨x', y', z, α, β⟩
  change (⟨x', y', α⟩ : S.OrdinaryArrowTotal) = ⟨x, y, a⟩ at hfirst
  cases hfirst
  change D.hom β ≫ D.hom a ≠ 0
  intro hzero
  let b : Quiver.Star y := ⟨z, β⟩
  have hb₁ : b ≠ b₁ := by
    intro heq
    apply h₁
    rw [← heq]
    exact hzero
  have hb₂ : b ≠ b₂ := by
    intro heq
    apply h₂
    rw [← heq]
    exact hzero
  let f : Fin 3 → Quiver.Star y := ![b₁, b₂, b]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hb (by simpa [f] using hij)).elim
    · exact (hb₁ (by simpa [f] using hij.symm)).elim
    · exact (hb (by simpa [f] using hij.symm)).elim
    · rfl
    · exact (hb₂ (by simpa [f] using hij.symm)).elim
    · exact (hb₁ (by simpa [f] using hij)).elim
    · exact (hb₂ (by simpa [f] using hij)).elim
    · rfl
  have hthree : 3 ≤ Nat.card (Quiver.Star y) := by
    simpa using Nat.card_le_card_of_injective f hf
  omega

/-- Failure of the right-continuation bound supplies two explicit distinct
nonzero continuations. -/
theorem exists_rightContinuationFork_of_not_hasRightContinuationBound
    (D : S.OrdinaryArrowRepresentatives)
    (hbad : ¬ D.HasRightContinuationBound) :
    Nonempty D.RightContinuationFork := by
  classical
  rw [HasRightContinuationBound] at hbad
  push Not at hbad
  obtain ⟨x, y, a, hcard⟩ := hbad
  let T := {b : Quiver.Star y // D.hom b.2 ≫ D.hom a ≠ 0}
  change 1 < Nat.card T at hcard
  letI : Fintype T := Fintype.ofFinite T
  have hnsub : ¬ Subsingleton T := by
    intro hsub
    have hle : Fintype.card T ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.2 hsub
    have hcard' : Nat.card T ≤ 1 := by
      simpa only [Nat.card_eq_fintype_card] using hle
    omega
  letI : Nontrivial T := not_subsingleton_iff_nontrivial.mp hnsub
  obtain ⟨b₁, b₂, hb⟩ := exists_pair_ne T
  exact ⟨⟨x, y, a, b₁, b₂, hb⟩⟩

/-- Failure of the left-continuation bound supplies two explicit distinct
nonzero predecessors. -/
theorem exists_leftContinuationFork_of_not_hasLeftContinuationBound
    (D : S.OrdinaryArrowRepresentatives)
    (hbad : ¬ D.HasLeftContinuationBound) :
    Nonempty D.LeftContinuationFork := by
  classical
  rw [HasLeftContinuationBound] at hbad
  push Not at hbad
  obtain ⟨x, y, a, hcard⟩ := hbad
  let T := {c : Quiver.Costar x // D.hom a ≫ D.hom c.2 ≠ 0}
  change 1 < Nat.card T at hcard
  letI : Fintype T := Fintype.ofFinite T
  have hnsub : ¬ Subsingleton T := by
    intro hsub
    have hle : Fintype.card T ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.2 hsub
    have hcard' : Nat.card T ≤ 1 := by
      simpa only [Nat.card_eq_fintype_card] using hle
    omega
  letI : Nontrivial T := not_subsingleton_iff_nontrivial.mp hnsub
  obtain ⟨c₁, c₂, hc⟩ := exists_pair_ne T
  exact ⟨⟨x, y, a, c₁, c₂, hc⟩⟩

variable {D : S.OrdinaryArrowRepresentatives}

namespace RightContinuationFork

/-- Exchange the two nonzero continuations in a right fork.  The local
uniserial comparison chooses one of these two orderings. -/
def swap (F : D.RightContinuationFork) : D.RightContinuationFork where
  startVertex := F.startVertex
  middleVertex := F.middleVertex
  first := F.first
  following₁ := F.following₂
  following₂ := F.following₁
  distinct := F.distinct.symm

/-- The second branch of a right fork, bundled as a total arrow. -/
def changedArrow (F : D.RightContinuationFork) : S.OrdinaryArrowTotal :=
  ⟨F.middleVertex, F.following₂.1.1, F.following₂.1.2⟩

/-- The nonzero two-step path which the correction will kill. -/
def killedTwoStep (F : D.RightContinuationFork) : S.OrdinaryTwoStep :=
  ⟨F.startVertex, F.middleVertex, F.following₂.1.1,
    F.first, F.following₂.1.2⟩

/-- The original first arrow, regarded as a predecessor of the changed
second branch. -/
def firstPredecessor (F : D.RightContinuationFork) :
    Quiver.Costar F.middleVertex :=
  ⟨F.startVertex, F.first⟩

@[simp]
theorem killedTwoStepComposite_ne_zero (F : D.RightContinuationFork) :
    D.twoStepComposite F.killedTwoStep ≠ 0 :=
  F.following₂.2

end RightContinuationFork

namespace LeftContinuationFork

/-- Exchange the two nonzero predecessors in a left fork.  This is the
left-right symmetric branch choice used by the local comparison. -/
def swap (F : D.LeftContinuationFork) : D.LeftContinuationFork where
  middleVertex := F.middleVertex
  targetVertex := F.targetVertex
  second := F.second
  preceding₁ := F.preceding₂
  preceding₂ := F.preceding₁
  distinct := F.distinct.symm

/-- The second predecessor branch of a left fork, bundled as a total
arrow. -/
def changedArrow (F : D.LeftContinuationFork) : S.OrdinaryArrowTotal :=
  ⟨F.preceding₂.1.1, F.middleVertex, F.preceding₂.1.2⟩

/-- The nonzero two-step path which the symmetric correction will kill. -/
def killedTwoStep (F : D.LeftContinuationFork) : S.OrdinaryTwoStep :=
  ⟨F.preceding₂.1.1, F.middleVertex, F.targetVertex,
    F.preceding₂.1.2, F.second⟩

/-- The original second arrow, regarded as a continuation of the changed
first branch. -/
def firstFollowing (F : D.LeftContinuationFork) :
    Quiver.Star F.middleVertex :=
  ⟨F.targetVertex, F.second⟩

@[simp]
theorem killedTwoStepComposite_ne_zero (F : D.LeftContinuationFork) :
    D.twoStepComposite F.killedTwoStep ≠ 0 :=
  F.preceding₂.2

end LeftContinuationFork

/-- The exact categorical local output needed on the right-handed side of the
SW correction.  Besides the radical corner endomorphism, it records the
second nonzero predecessor which proves that no old zero relation occurs on
the unprotected side. -/
structure RightSWCorrectionData (D : S.OrdinaryArrowRepresentatives)
    (F : D.RightContinuationFork) where
  secondPredecessor : Quiver.Costar F.middleVertex
  secondPredecessor_ne :
    F.firstPredecessor ≠ secondPredecessor
  secondPredecessor_composite_ne :
    D.hom F.following₂.1.2 ≫ D.hom secondPredecessor.2 ≠ 0
  cornerEndomorphism :
    S.ordinaryProjectiveObj F.middleVertex ⟶
      S.ordinaryProjectiveObj F.middleVertex
  cornerEndomorphism_mem_radical :
    cornerEndomorphism ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj F.middleVertex)
      (S.ordinaryProjectiveObj F.middleVertex)
  kills :
    (D.perturbAt F.changedArrow
      (D.codomainCorrection F.changedArrow cornerEndomorphism
        cornerEndomorphism_mem_radical)).twoStepComposite F.killedTwoStep = 0

/-- The left-right symmetric local output of the Kupisch--Nakayama step. -/
structure LeftSWCorrectionData (D : S.OrdinaryArrowRepresentatives)
    (F : D.LeftContinuationFork) where
  secondFollowing : Quiver.Star F.middleVertex
  secondFollowing_ne : F.firstFollowing ≠ secondFollowing
  secondFollowing_composite_ne :
    D.hom secondFollowing.2 ≫ D.hom F.preceding₂.1.2 ≠ 0
  cornerEndomorphism :
    S.ordinaryProjectiveObj F.middleVertex ⟶
      S.ordinaryProjectiveObj F.middleVertex
  cornerEndomorphism_mem_radical :
    cornerEndomorphism ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj F.middleVertex)
      (S.ordinaryProjectiveObj F.middleVertex)
  kills :
    (D.perturbAt F.changedArrow
      (D.domainCorrection F.changedArrow cornerEndomorphism
        cornerEndomorphism_mem_radical)).twoStepComposite F.killedTwoStep = 0

/-- The source's right-handed local comparison may select either ordering of
the two displayed continuations.  Requiring data for a predetermined ordering
would be stronger than uniserial comparability. -/
def RightSWCorrectionChoice (D : S.OrdinaryArrowRepresentatives)
    (F : D.RightContinuationFork) : Prop :=
  Nonempty (RightSWCorrectionData D F) ∨
    Nonempty (RightSWCorrectionData D F.swap)

/-- The left-right symmetric choice between the two predecessor orderings. -/
def LeftSWCorrectionChoice (D : S.OrdinaryArrowRepresentatives)
    (F : D.LeftContinuationFork) : Prop :=
  Nonempty (LeftSWCorrectionData D F) ∨
    Nonempty (LeftSWCorrectionData D F.swap)

/-- Precomposition factorization of the changed representative through the
old one. -/
def HasDomainFactorization (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1) : Prop :=
  ∃ u : S.ordinaryProjectiveObj a.2.1 ⟶
      S.ordinaryProjectiveObj a.2.1,
    (D.perturbAt a r).hom a.2.2 = u ≫ D.hom a.2.2

/-- Postcomposition factorization of the changed representative through the
old one. -/
def HasCodomainFactorization (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1) : Prop :=
  ∃ v : S.ordinaryProjectiveObj a.1 ⟶
      S.ordinaryProjectiveObj a.1,
    (D.perturbAt a r).hom a.2.2 = D.hom a.2.2 ≫ v

/-- A domain correction is literally precomposition by `1 - x`. -/
theorem domainCorrection_hasDomainFactorization
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (x : S.ordinaryProjectiveObj a.2.1 ⟶
      S.ordinaryProjectiveObj a.2.1)
    (hx : x ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.2.1)
      (S.ordinaryProjectiveObj a.2.1)) :
    D.HasDomainFactorization a (D.domainCorrection a x hx) := by
  refine ⟨𝟙 (S.ordinaryProjectiveObj a.2.1) - x, ?_⟩
  rw [perturbAt_hom_self]
  rw [show (D.domainCorrection a x hx).1 =
    -(x ≫ D.hom a.2.2) by rfl, ← sub_eq_add_neg]
  rw [Preadditive.sub_comp, Category.id_comp]

/-- A codomain correction is literally postcomposition by `1 - y`. -/
theorem codomainCorrection_hasCodomainFactorization
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (y : S.ordinaryProjectiveObj a.1 ⟶
      S.ordinaryProjectiveObj a.1)
    (hy : y ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.1)
      (S.ordinaryProjectiveObj a.1)) :
    D.HasCodomainFactorization a (D.codomainCorrection a y hy) := by
  refine ⟨𝟙 (S.ordinaryProjectiveObj a.1) - y, ?_⟩
  rw [perturbAt_hom_self]
  rw [show (D.codomainCorrection a y hy).1 =
    -(D.hom a.2.2 ≫ y) by rfl, ← sub_eq_add_neg]
  rw [Preadditive.comp_sub, Category.comp_id]

/-- A domain-factor replacement preserves the zero composites in which the
changed arrow occurs second.  If no zero composite used it first, all
incident zeros are therefore preserved. -/
theorem preservesIncidentZeros_of_domainFactorization_of_noZeroWhenFirst
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1)
    (hfactor : D.HasDomainFactorization a r)
    (hno : D.NoZeroWhenFirst a) :
    D.PreservesIncidentZeros a r := by
  obtain ⟨u, hu⟩ := hfactor
  intro q huses hzero
  by_cases hfirst : OrdinaryTwoStep.firstArrow q = a
  · exact False.elim (hno q hfirst hzero)
  · have hsecond : OrdinaryTwoStep.secondArrow q = a :=
      huses.resolve_left hfirst
    rcases q with ⟨x, y, z, α, β⟩
    change (⟨y, z, β⟩ : S.OrdinaryArrowTotal) = a at hsecond
    cases hsecond
    change (⟨x, y, α⟩ : S.OrdinaryArrowTotal) ≠
      (⟨y, z, β⟩ : S.OrdinaryArrowTotal) at hfirst
    change (D.perturbAt ⟨y, z, β⟩ r).hom β =
      u ≫ D.hom β at hu
    rw [twoStepComposite, hu,
      D.perturbAt_hom_eq_of_ne ⟨y, z, β⟩ r α hfirst,
      Category.assoc]
    change D.hom β ≫ D.hom α = 0 at hzero
    simp [hzero]

/-- The left-right symmetric zero-preservation criterion for a codomain
factor replacement. -/
theorem preservesIncidentZeros_of_codomainFactorization_of_noZeroWhenSecond
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1)
    (hfactor : D.HasCodomainFactorization a r)
    (hno : D.NoZeroWhenSecond a) :
    D.PreservesIncidentZeros a r := by
  obtain ⟨v, hv⟩ := hfactor
  intro q huses hzero
  by_cases hsecond : OrdinaryTwoStep.secondArrow q = a
  · exact False.elim (hno q hsecond hzero)
  · have hfirst : OrdinaryTwoStep.firstArrow q = a :=
      huses.resolve_right hsecond
    rcases q with ⟨x, y, z, α, β⟩
    change (⟨x, y, α⟩ : S.OrdinaryArrowTotal) = a at hfirst
    cases hfirst
    change (⟨y, z, β⟩ : S.OrdinaryArrowTotal) ≠
      (⟨x, y, α⟩ : S.OrdinaryArrowTotal) at hsecond
    change (D.perturbAt ⟨x, y, α⟩ r).hom α =
      D.hom α ≫ v at hv
    rw [twoStepComposite,
      D.perturbAt_hom_eq_of_ne ⟨x, y, α⟩ r β hsecond, hv,
      ← Category.assoc]
    change D.hom β ≫ D.hom α = 0 at hzero
    simp [hzero]

/-- If the radical endomorphisms on the two sides satisfy `x ≫ a = a ≫ y`,
then the balanced correction replaces `a` simultaneously by
`(1 - x) ≫ a` and by `a ≫ (1 - y)`. -/
theorem domainCorrection_hasTwoSidedFactorization_of_balanced
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (x : S.ordinaryProjectiveObj a.2.1 ⟶
      S.ordinaryProjectiveObj a.2.1)
    (y : S.ordinaryProjectiveObj a.1 ⟶
      S.ordinaryProjectiveObj a.1)
    (hx : x ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.2.1)
      (S.ordinaryProjectiveObj a.2.1))
    (hbalanced : x ≫ D.hom a.2.2 = D.hom a.2.2 ≫ y) :
    D.HasTwoSidedFactorization a (D.domainCorrection a x hx) := by
  refine ⟨𝟙 (S.ordinaryProjectiveObj a.2.1) - x,
    𝟙 (S.ordinaryProjectiveObj a.1) - y, ?_, ?_⟩
  · rw [perturbAt_hom_self]
    rw [show (D.domainCorrection a x hx).1 =
      -(x ≫ D.hom a.2.2) by rfl, ← sub_eq_add_neg]
    rw [Preadditive.sub_comp, Category.id_comp]
  · rw [perturbAt_hom_self]
    rw [show (D.domainCorrection a x hx).1 =
      -(x ≫ D.hom a.2.2) by rfl, ← sub_eq_add_neg]
    rw [Preadditive.comp_sub, Category.comp_id, hbalanced]

/-- A two-sided factor replacement preserves every incident two-arrow zero
relation, including the square of a loop arrow. -/
theorem preservesIncidentZeros_of_twoSidedFactorization
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1)
    (hfactor : D.HasTwoSidedFactorization a r) :
    D.PreservesIncidentZeros a r := by
  obtain ⟨u, v, hu, hv⟩ := hfactor
  intro q huses hzero
  rcases q with ⟨x, y, z, α, β⟩
  change
    OrdinaryTwoStep.firstArrow ⟨x, y, z, α, β⟩ = a ∨
      OrdinaryTwoStep.secondArrow ⟨x, y, z, α, β⟩ = a at huses
  change D.hom β ≫ D.hom α = 0 at hzero
  by_cases hα : (⟨x, y, α⟩ : S.OrdinaryArrowTotal) = a
  · cases hα
    by_cases hβ : (⟨y, z, β⟩ : S.OrdinaryArrowTotal) =
        (⟨x, y, α⟩ : S.OrdinaryArrowTotal)
    · cases hβ
      rw [twoStepComposite]
      calc
        (D.perturbAt ⟨x, x, α⟩ r).hom α ≫
              (D.perturbAt ⟨x, x, α⟩ r).hom α =
            (u ≫ D.hom α) ≫ (D.hom α ≫ v) :=
          congrArg₂ (· ≫ ·) hu hv
        _ = u ≫ (D.hom α ≫ D.hom α) ≫ v := by
          simp only [Category.assoc]
        _ = 0 := by simp [hzero]
    · rw [twoStepComposite,
        D.perturbAt_hom_eq_of_ne ⟨x, y, α⟩ r β hβ, hv,
        ← Category.assoc, hzero]
      simp
  · have hβ : (⟨y, z, β⟩ : S.OrdinaryArrowTotal) = a :=
      huses.resolve_left hα
    cases hβ
    rw [twoStepComposite, hu,
      D.perturbAt_hom_eq_of_ne ⟨y, z, β⟩ r α hα,
      Category.assoc, hzero]
    simp

/-- The finite set of two-step paths whose representative composite is
nonzero. -/
def nonzeroTwoSteps (D : S.OrdinaryArrowRepresentatives) :
    Finset S.OrdinaryTwoStep := by
  classical
  exact Finset.univ.filter fun q ↦ D.twoStepComposite q ≠ 0

@[simp]
theorem mem_nonzeroTwoSteps_iff (D : S.OrdinaryArrowRepresentatives)
    (q : S.OrdinaryTwoStep) :
    q ∈ D.nonzeroTwoSteps ↔ D.twoStepComposite q ≠ 0 := by
  classical
  simp [nonzeroTwoSteps]

/-- A change of representatives is zero-monotone on two-step paths when it
does not turn any existing zero composite into a nonzero composite. -/
def TwoStepZeroMonotone (D E : S.OrdinaryArrowRepresentatives) : Prop :=
  ∀ q : S.OrdinaryTwoStep,
    D.twoStepComposite q = 0 → E.twoStepComposite q = 0

/-- Local preservation at the changed arrow implies global two-step
zero-monotonicity. -/
theorem perturbAt_twoStepZeroMonotone
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (r : S.projectiveRadicalSquareSubmodule a.1 a.2.1)
    (hlocal : D.PreservesIncidentZeros a r) :
    D.TwoStepZeroMonotone (D.perturbAt a r) := by
  intro q hq
  by_cases huses : OrdinaryTwoStep.UsesArrow q a
  · exact hlocal q huses hq
  · rw [D.perturbAt_twoStepComposite_eq_of_not_uses a r q huses]
    exact hq

/-- A domain correction is globally zero-monotone provided the changed arrow
did not occur first in an old zero composite. -/
theorem domainCorrection_twoStepZeroMonotone_of_noZeroWhenFirst
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (x : S.ordinaryProjectiveObj a.2.1 ⟶
      S.ordinaryProjectiveObj a.2.1)
    (hx : x ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.2.1)
      (S.ordinaryProjectiveObj a.2.1))
    (hno : D.NoZeroWhenFirst a) :
    D.TwoStepZeroMonotone (D.perturbAt a (D.domainCorrection a x hx)) :=
  D.perturbAt_twoStepZeroMonotone a (D.domainCorrection a x hx)
    (D.preservesIncidentZeros_of_domainFactorization_of_noZeroWhenFirst
      a (D.domainCorrection a x hx)
      (D.domainCorrection_hasDomainFactorization a x hx) hno)

/-- A codomain correction is globally zero-monotone provided the changed
arrow did not occur second in an old zero composite. -/
theorem codomainCorrection_twoStepZeroMonotone_of_noZeroWhenSecond
    (D : S.OrdinaryArrowRepresentatives)
    (a : S.OrdinaryArrowTotal)
    (y : S.ordinaryProjectiveObj a.1 ⟶
      S.ordinaryProjectiveObj a.1)
    (hy : y ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.1)
      (S.ordinaryProjectiveObj a.1))
    (hno : D.NoZeroWhenSecond a) :
    D.TwoStepZeroMonotone (D.perturbAt a (D.codomainCorrection a y hy)) :=
  D.perturbAt_twoStepZeroMonotone a (D.codomainCorrection a y hy)
    (D.preservesIncidentZeros_of_codomainFactorization_of_noZeroWhenSecond
      a (D.codomainCorrection a y hy)
      (D.codomainCorrection_hasCodomainFactorization a y hy) hno)

theorem twoStepZeroMonotone_refl (D : S.OrdinaryArrowRepresentatives) :
    D.TwoStepZeroMonotone D := by
  intro q hq
  exact hq

theorem TwoStepZeroMonotone.trans
    {D E F : S.OrdinaryArrowRepresentatives}
    (hDE : D.TwoStepZeroMonotone E)
    (hEF : E.TwoStepZeroMonotone F) :
    D.TwoStepZeroMonotone F := by
  intro q hq
  exact hEF q (hDE q hq)

/-- A zero-monotone change can only decrease the finite set of nonzero
two-step composites. -/
theorem nonzeroTwoSteps_subset_of_twoStepZeroMonotone
    {D E : S.OrdinaryArrowRepresentatives}
    (hDE : D.TwoStepZeroMonotone E) :
    E.nonzeroTwoSteps ⊆ D.nonzeroTwoSteps := by
  intro q hq
  rw [mem_nonzeroTwoSteps_iff E q] at hq
  rw [mem_nonzeroTwoSteps_iff D q]
  intro hzero
  exact hq (hDE q hzero)

/-- If a zero-monotone change kills one previously nonzero two-step
composite, the total number of nonzero two-step composites strictly drops. -/
theorem card_nonzeroTwoSteps_lt_of_twoStepZeroMonotone_of_kills
    {D E : S.OrdinaryArrowRepresentatives}
    (hDE : D.TwoStepZeroMonotone E)
    (q : S.OrdinaryTwoStep)
    (hDq : D.twoStepComposite q ≠ 0)
    (hEq : E.twoStepComposite q = 0) :
    E.nonzeroTwoSteps.card < D.nonzeroTwoSteps.card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨nonzeroTwoSteps_subset_of_twoStepZeroMonotone hDE, ?_⟩
  intro heq
  have hmemD : q ∈ D.nonzeroTwoSteps :=
    (mem_nonzeroTwoSteps_iff D q).2 hDq
  have hmemE : q ∈ E.nonzeroTwoSteps := by
    rw [heq]
    exact hmemD
  exact ((mem_nonzeroTwoSteps_iff E q).1 hmemE) hEq

/-- One local SW correction: retain every existing zero two-step relation and
kill the specified nonzero two-step composite. -/
def HasTwoStepCorrection (D : S.OrdinaryArrowRepresentatives)
    (q : S.OrdinaryTwoStep) : Prop :=
  D.twoStepComposite q ≠ 0 ∧
    ∃ E : S.OrdinaryArrowRepresentatives,
      D.TwoStepZeroMonotone E ∧ E.twoStepComposite q = 0

/-- Package a successful domain correction as the local correction consumed
by the finite minimization argument. -/
theorem hasTwoStepCorrection_of_domainCorrection
    (D : S.OrdinaryArrowRepresentatives)
    (q : S.OrdinaryTwoStep)
    (a : S.OrdinaryArrowTotal)
    (x : S.ordinaryProjectiveObj a.2.1 ⟶
      S.ordinaryProjectiveObj a.2.1)
    (hx : x ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.2.1)
      (S.ordinaryProjectiveObj a.2.1))
    (hq : D.twoStepComposite q ≠ 0)
    (hno : D.NoZeroWhenFirst a)
    (hkill : (D.perturbAt a (D.domainCorrection a x hx)).twoStepComposite q = 0) :
    D.HasTwoStepCorrection q :=
  ⟨hq, D.perturbAt a (D.domainCorrection a x hx),
    D.domainCorrection_twoStepZeroMonotone_of_noZeroWhenFirst a x hx hno,
    hkill⟩

/-- Package a successful codomain correction as the local correction
consumed by the finite minimization argument. -/
theorem hasTwoStepCorrection_of_codomainCorrection
    (D : S.OrdinaryArrowRepresentatives)
    (q : S.OrdinaryTwoStep)
    (a : S.OrdinaryArrowTotal)
    (y : S.ordinaryProjectiveObj a.1 ⟶
      S.ordinaryProjectiveObj a.1)
    (hy : y ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj a.1)
      (S.ordinaryProjectiveObj a.1))
    (hq : D.twoStepComposite q ≠ 0)
    (hno : D.NoZeroWhenSecond a)
    (hkill : (D.perturbAt a (D.codomainCorrection a y hy)).twoStepComposite q = 0) :
    D.HasTwoStepCorrection q :=
  ⟨hq, D.perturbAt a (D.codomainCorrection a y hy),
    D.codomainCorrection_twoStepZeroMonotone_of_noZeroWhenSecond a y hy hno,
    hkill⟩

/-- The right-handed SW local data gives a zero-monotone correction once the
incoming degree at the middle vertex is at most two. -/
theorem RightSWCorrectionData.hasTwoStepCorrection
    {D : S.OrdinaryArrowRepresentatives}
    {F : D.RightContinuationFork} (C : RightSWCorrectionData D F)
    (hcard : Nat.card (Quiver.Costar F.middleVertex) ≤ 2) :
    D.HasTwoStepCorrection F.killedTwoStep := by
  have hno : D.NoZeroWhenSecond F.changedArrow :=
    D.noZeroWhenSecond_of_costar_card_le_two
      F.following₂.1.2 F.firstPredecessor C.secondPredecessor
      C.secondPredecessor_ne F.following₂.2
      C.secondPredecessor_composite_ne hcard
  exact D.hasTwoStepCorrection_of_codomainCorrection
    F.killedTwoStep F.changedArrow C.cornerEndomorphism
    C.cornerEndomorphism_mem_radical F.killedTwoStepComposite_ne_zero
    hno C.kills

/-- The left-handed SW local data gives the symmetric zero-monotone
correction once the outgoing degree at the middle vertex is at most two. -/
theorem LeftSWCorrectionData.hasTwoStepCorrection
    {D : S.OrdinaryArrowRepresentatives}
    {F : D.LeftContinuationFork} (C : LeftSWCorrectionData D F)
    (hcard : Nat.card (Quiver.Star F.middleVertex) ≤ 2) :
    D.HasTwoStepCorrection F.killedTwoStep := by
  have hno : D.NoZeroWhenFirst F.changedArrow :=
    D.noZeroWhenFirst_of_star_card_le_two
      F.preceding₂.1.2 F.firstFollowing C.secondFollowing
      C.secondFollowing_ne F.preceding₂.2
      C.secondFollowing_composite_ne hcard
  exact D.hasTwoStepCorrection_of_domainCorrection
    F.killedTwoStep F.changedArrow C.cornerEndomorphism
    C.cornerEndomorphism_mem_radical F.killedTwoStepComposite_ne_zero
    hno C.kills

/-- Either ordering selected by the right-handed local comparison supplies a
usable correction of one of the two original nonzero paths. -/
theorem exists_hasTwoStepCorrection_of_rightSWCorrectionChoice
    {D : S.OrdinaryArrowRepresentatives}
    {F : D.RightContinuationFork} (C : RightSWCorrectionChoice D F)
    (hcard : Nat.card (Quiver.Costar F.middleVertex) ≤ 2) :
    ∃ q : S.OrdinaryTwoStep, D.HasTwoStepCorrection q := by
  rcases C with C | C
  · let C' := Classical.choice C
    exact ⟨F.killedTwoStep, C'.hasTwoStepCorrection hcard⟩
  · let C' := Classical.choice C
    exact ⟨F.swap.killedTwoStep, C'.hasTwoStepCorrection hcard⟩

/-- Either ordering selected by the left-handed local comparison supplies the
symmetric usable correction. -/
theorem exists_hasTwoStepCorrection_of_leftSWCorrectionChoice
    {D : S.OrdinaryArrowRepresentatives}
    {F : D.LeftContinuationFork} (C : LeftSWCorrectionChoice D F)
    (hcard : Nat.card (Quiver.Star F.middleVertex) ≤ 2) :
    ∃ q : S.OrdinaryTwoStep, D.HasTwoStepCorrection q := by
  rcases C with C | C
  · let C' := Classical.choice C
    exact ⟨F.killedTwoStep, C'.hasTwoStepCorrection hcard⟩
  · let C' := Classical.choice C
    exact ⟨F.swap.killedTwoStep, C'.hasTwoStepCorrection hcard⟩

/-- There is a representative system minimizing the finite number of
nonzero two-step composites. -/
theorem exists_minimal_nonzeroTwoSteps :
    ∃ D : S.OrdinaryArrowRepresentatives,
      ∀ E : S.OrdinaryArrowRepresentatives,
        D.nonzeroTwoSteps.card ≤ E.nonzeroTwoSteps.card := by
  classical
  let D₀ : S.OrdinaryArrowRepresentatives :=
    { representative := fun {_ _} a ↦ S.ordinaryArrowRadical a
      representative_mkQ := fun {_ _} a ↦
        S.ordinaryArrowRadical_mkQ a }
  have hCandidate : ∃ n : ℕ,
      ∃ D : S.OrdinaryArrowRepresentatives,
        D.nonzeroTwoSteps.card = n :=
    ⟨D₀.nonzeroTwoSteps.card, D₀, rfl⟩
  let n := Nat.find hCandidate
  obtain ⟨D, hDn⟩ := Nat.find_spec hCandidate
  refine ⟨D, fun E ↦ ?_⟩
  rw [hDn]
  exact Nat.find_min' hCandidate ⟨E, rfl⟩

/-- The source-faithful finite correction principle.  Once every failure of
the two continuation conditions supplies one local zero-monotone correction,
a globally adapted representative system exists. -/
theorem exists_adapted_of_exists_twoStepCorrection
    (hCorrection : ∀ D : S.OrdinaryArrowRepresentatives,
      ¬ (D.HasRightContinuationBound ∧ D.HasLeftContinuationBound) →
        ∃ q : S.OrdinaryTwoStep, D.HasTwoStepCorrection q) :
    ∃ D : S.OrdinaryArrowRepresentatives,
      D.HasRightContinuationBound ∧ D.HasLeftContinuationBound := by
  obtain ⟨D, hDmin⟩ :=
    (exists_minimal_nonzeroTwoSteps (S := S))
  refine ⟨D, ?_⟩
  by_contra hbad
  obtain ⟨q, hDq, E, hDE, hEq⟩ := hCorrection D hbad
  have hlt :=
    card_nonzeroTwoSteps_lt_of_twoStepZeroMonotone_of_kills
      hDE q hDq hEq
  exact (Nat.not_lt_of_ge (hDmin E)) hlt

/-- The exact SW assembly theorem after separating its local
Kupisch--Nakayama output from the finite correction argument. -/
theorem exists_adapted_of_swCorrectionData
    (hStar : ∀ x : S.ProjectiveLabel, Nat.card (Quiver.Star x) ≤ 2)
    (hCostar : ∀ x : S.ProjectiveLabel, Nat.card (Quiver.Costar x) ≤ 2)
    (hRight : ∀ (D : S.OrdinaryArrowRepresentatives)
      (F : D.RightContinuationFork), RightSWCorrectionChoice D F)
    (hLeft : ∀ (D : S.OrdinaryArrowRepresentatives)
      (F : D.LeftContinuationFork), LeftSWCorrectionChoice D F) :
    ∃ D : S.OrdinaryArrowRepresentatives,
      D.HasRightContinuationBound ∧ D.HasLeftContinuationBound := by
  apply exists_adapted_of_exists_twoStepCorrection
  intro D hbad
  by_cases hright : D.HasRightContinuationBound
  · have hleft : ¬ D.HasLeftContinuationBound := by
      intro hleft
      exact hbad ⟨hright, hleft⟩
    let F := Classical.choice
      (D.exists_leftContinuationFork_of_not_hasLeftContinuationBound hleft)
    exact exists_hasTwoStepCorrection_of_leftSWCorrectionChoice
      (hLeft D F) (hStar F.middleVertex)
  · let F := Classical.choice
      (D.exists_rightContinuationFork_of_not_hasRightContinuationBound hright)
    exact exists_hasTwoStepCorrection_of_rightSWCorrectionChoice
      (hRight D F) (hCostar F.middleVertex)

variable [IsNoetherianRing A] [IsAlgClosed k]

/-- For a biserial primitive-projective presentation, the already proved
ordinary-quiver degree bounds discharge the two finite-degree hypotheses in
the SW assembly.  Only the local Kupisch--Nakayama correction data remains. -/
theorem exists_adapted_of_isBiserial_of_swCorrectionData
    (P : S.PrimitiveProjectivePresentation) (hP : P.IsBiserial)
    (hRight : ∀ (D : S.OrdinaryArrowRepresentatives)
      (F : D.RightContinuationFork), RightSWCorrectionChoice D F)
    (hLeft : ∀ (D : S.OrdinaryArrowRepresentatives)
      (F : D.LeftContinuationFork), LeftSWCorrectionChoice D F) :
    ∃ D : S.OrdinaryArrowRepresentatives,
      D.HasRightContinuationBound ∧ D.HasLeftContinuationBound := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact exists_adapted_of_swCorrectionData
    (fun x ↦
      S.ordinaryStar_card_le_two_of_primitiveProjectivePresentation_isBiserial
        P hP x)
    (fun x ↦ P.ordinaryCostar_card_le_two_of_isBiserial hP x)
    hRight hLeft

end OrdinaryArrowRepresentatives

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
