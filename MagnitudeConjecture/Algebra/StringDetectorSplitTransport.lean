import MagnitudeConjecture.Algebra.StringDetectorSplitNaturality

/-!
# Transporting contextual string detectors along a word

One-letter split equivalences compose along a finite walk of displayed cuts.
Their naturality therefore composes as well.  A walk ending at the target cut
identifies its contextual detector with the canonical endpoint detector.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}

namespace Word.Split

/-- A split is determined by its displayed vertex and its two dependent path
pieces. -/
@[ext]
theorem ext {E : Word P.toPresentation.relations} {c d : E.Split}
    (hvertex : c.vertex = d.vertex)
    (hprefix : HEq c.prefixPath d.prefixPath)
    (hsuffix : HEq c.suffixPath d.suffixPath) : c = d := by
  rcases c with ⟨vertex, pref, suff, factor⟩
  rcases d with ⟨vertex', pref', suff', factor'⟩
  dsimp at hvertex hprefix hsuffix
  subst vertex'
  simp only [heq_eq_eq] at hprefix hsuffix
  subst pref'
  subst suff'
  rfl

/-- Consecutive word positions separated by a positively traversed arrow
give a positive split step. -/
def positiveStepOfArrowStep
    {E : Word P.toPresentation.relations} {x y : Q}
    (i : E.PositionAt x) (j : E.PositionAt y) (a : x ⟶ y)
    (hindex : j.index = i.index + 1) (hstep : E.ArrowStep a i j) :
    (ofPosition E ⟨x, i⟩).PositiveStep (ofPosition E ⟨y, j⟩) := by
  have hprefix : j.1 = i.1.comp (positiveArrow a).toPath := by
    rcases hstep with hpositive | hnegative
    · exact hpositive
    · have hlength := congrArg Quiver.Path.length hnegative
      change i.index = j.index + 1 at hlength
      omega
  refine ⟨a, hprefix, ?_⟩
  apply Quiver.Path.comp_injective_right i.1
  calc
    i.1.comp i.suffix = E.path := i.prefix_comp_suffix.symm
    _ = j.1.comp j.suffix := j.prefix_comp_suffix
    _ = (i.1.comp (positiveArrow a).toPath).comp j.suffix := by
      rw [hprefix]
    _ = i.1.comp ((positiveArrow a).toPath.comp j.suffix) :=
      Quiver.Path.comp_assoc _ _ _

/-- Consecutive word positions separated by an inversely traversed arrow
give a negative split step. -/
def negativeStepOfArrowStep
    {E : Word P.toPresentation.relations} {x y : Q}
    (i : E.PositionAt x) (j : E.PositionAt y) (a : y ⟶ x)
    (hindex : j.index = i.index + 1) (hstep : E.ArrowStep a j i) :
    (ofPosition E ⟨x, i⟩).NegativeStep (ofPosition E ⟨y, j⟩) := by
  have hprefix : j.1 = i.1.comp (negativeArrow a).toPath := by
    rcases hstep with hpositive | hnegative
    · have hlength := congrArg Quiver.Path.length hpositive
      change i.index = j.index + 1 at hlength
      omega
    · exact hnegative
  refine ⟨a, hprefix, ?_⟩
  apply Quiver.Path.comp_injective_right i.1
  calc
    i.1.comp i.suffix = E.path := i.prefix_comp_suffix.symm
    _ = j.1.comp j.suffix := j.prefix_comp_suffix
    _ = (i.1.comp (negativeArrow a).toPath).comp j.suffix := by
      rw [hprefix]
    _ = i.1.comp ((negativeArrow a).toPath.comp j.suffix) :=
      Quiver.Path.comp_assoc _ _ _

/-- The total position at the target endpoint. -/
def targetPosition (E : Word P.toPresentation.relations) : E.Position :=
  ⟨E.target, E.targetPosition⟩

@[simp]
theorem targetPosition_index (E : Word P.toPresentation.relations) :
    (targetPosition E).index = E.length :=
  rfl

/-- The split attached to the target position is the target split. -/
theorem ofPosition_targetPosition (E : Word P.toPresentation.relations) :
    ofPosition E (targetPosition E) = .target E := by
  apply Word.Split.ext (c := ofPosition E (targetPosition E))
    (d := .target E) rfl HEq.rfl
  apply heq_of_eq
  apply E.targetPosition.suffix.eq_nil_of_length_zero
  rw [Word.PositionAt.suffix_length, E.targetPosition_index]
  omega

/-- A finite sequence of consecutive displayed cuts, moving from left to
right through the word. -/
inductive Walk {E : Word P.toPresentation.relations} : E.Split → E.Split → Type u
  | nil (c : E.Split) : Walk c c
  | positive {c d e : E.Split} (step : c.PositiveStep d) (tail : Walk d e) :
      Walk c e
  | negative {c d e : E.Split} (step : c.NegativeStep d) (tail : Walk d e) :
      Walk c e

/-- Every displayed word position admits a finite walk through consecutive
letters to the target cut. -/
theorem nonempty_walk_to_target
    (E : Word P.toPresentation.relations) (i : E.Position) :
    Nonempty ((ofPosition E i).Walk (.target E)) := by
  induction hrem : E.length - i.index using Nat.strong_induction_on
      generalizing i with
  | h n ih =>
      by_cases htarget : i.index = E.length
      · have hi : i = targetPosition E := by
          apply Word.Position.ext_index
          simpa only [targetPosition_index] using htarget
        subst i
        rw [ofPosition_targetPosition]
        exact ⟨Walk.nil _⟩
      · have hindexLt : i.index < E.length :=
          lt_of_le_of_ne i.2.index_le htarget
        rcases E.exists_arrowStep_of_index_lt_length i hindexLt with
          hpositive | hnegative
        · obtain ⟨y, j, a, hj, hstep⟩ := hpositive
          let next : E.Position := ⟨y, j⟩
          have hnextLt : E.length - next.index < n := by
            rw [← hrem]
            change E.length - j.index < E.length - i.index
            rw [hj]
            omega
          obtain ⟨tail⟩ := ih (E.length - next.index) hnextLt next rfl
          exact ⟨Walk.positive
            (positiveStepOfArrowStep i.2 j a hj hstep) tail⟩
        · obtain ⟨y, j, a, hj, hstep⟩ := hnegative
          let next : E.Position := ⟨y, j⟩
          have hnextLt : E.length - next.index < n := by
            rw [← hrem]
            change E.length - j.index < E.length - i.index
            rw [hj]
            omega
          obtain ⟨tail⟩ := ih (E.length - next.index) hnextLt next rfl
          exact ⟨Walk.negative
            (negativeStepOfArrowStep i.2 j a hj hstep) tail⟩

/-- A chosen walk from a displayed position to the target cut. -/
def walkToTarget (E : Word P.toPresentation.relations) (i : E.Position) :
    (ofPosition E i).Walk (.target E) :=
  Classical.choice (nonempty_walk_to_target E i)

end Word.Split

namespace EndpointWord

variable {E : Word P.toPresentation.relations}

/-- Composite change of split along a finite walk. -/
def splitDetectorSpaceWalkEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (S : P.ArrowPolarization)
    {c d : E.Split} (walk : c.Walk d) :
    SplitDetectorSpace N S E c ≃ₗ[k] SplitDetectorSpace N S E d := by
  induction walk with
  | nil c => exact LinearEquiv.refl k _
  | positive step tail ih =>
      exact (splitDetectorSpacePositiveStepEquiv N S E step).trans ih
  | negative step tail ih =>
      exact (splitDetectorSpaceNegativeStepEquiv N S E step).trans ih

@[simp]
theorem splitDetectorSpaceWalkEquiv_nil
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (S : P.ArrowPolarization) (c : E.Split) :
    splitDetectorSpaceWalkEquiv N S (Word.Split.Walk.nil c) =
      LinearEquiv.refl k _ :=
  rfl

@[simp]
theorem splitDetectorSpaceWalkEquiv_positive
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (S : P.ArrowPolarization)
    {c d e : E.Split} (step : c.PositiveStep d) (tail : d.Walk e) :
    splitDetectorSpaceWalkEquiv N S (Word.Split.Walk.positive step tail) =
      (splitDetectorSpacePositiveStepEquiv N S E step).trans
        (splitDetectorSpaceWalkEquiv N S tail) :=
  rfl

@[simp]
theorem splitDetectorSpaceWalkEquiv_negative
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (S : P.ArrowPolarization)
    {c d e : E.Split} (step : c.NegativeStep d) (tail : d.Walk e) :
    splitDetectorSpaceWalkEquiv N S (Word.Split.Walk.negative step tail) =
      (splitDetectorSpaceNegativeStepEquiv N S E step).trans
        (splitDetectorSpaceWalkEquiv N S tail) :=
  rfl

/-- Composite change of split commutes with every module morphism. -/
theorem splitDetectorLinearMap_walk
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (S : P.ArrowPolarization) {c d : E.Split} (walk : c.Walk d)
    (q : SplitDetectorSpace M S E c) :
    splitDetectorSpaceWalkEquiv N S walk
        (splitDetectorLinearMap f S E c q) =
      splitDetectorLinearMap f S E d
        (splitDetectorSpaceWalkEquiv M S walk q) := by
  induction walk with
  | nil c => rfl
  | positive step tail ih =>
      rw [splitDetectorSpaceWalkEquiv_positive,
        splitDetectorSpaceWalkEquiv_positive,
        LinearEquiv.trans_apply, LinearEquiv.trans_apply,
        splitDetectorLinearMap_positiveStep]
      exact ih _
  | negative step tail ih =>
      rw [splitDetectorSpaceWalkEquiv_negative,
        splitDetectorSpaceWalkEquiv_negative,
        LinearEquiv.trans_apply, LinearEquiv.trans_apply,
        splitDetectorLinearMap_negativeStep]
      exact ih _

/-- A walk to the target cut identifies a contextual detector with the
canonical endpoint detector. -/
def splitDetectorSpaceToTargetEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (S : P.ArrowPolarization) {c : E.Split}
    (walk : c.Walk (.target E)) :
    SplitDetectorSpace N S E c ≃ₗ[k]
      DetectorSpace N (detectorEndpoint S E) :=
  (splitDetectorSpaceWalkEquiv N S walk).trans
    (splitDetectorSpaceTargetEquiv N S E)

/-- Transport to the target detector is natural in the represented
module. -/
theorem splitDetectorLinearMap_toTarget
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (S : P.ArrowPolarization) {c : E.Split}
    (walk : c.Walk (.target E)) (q : SplitDetectorSpace M S E c) :
    splitDetectorSpaceToTargetEquiv N S walk
        (splitDetectorLinearMap f S E c q) =
      detectorLinearMap f (detectorEndpoint S E)
        (splitDetectorSpaceToTargetEquiv M S walk q) := by
  rw [splitDetectorSpaceToTargetEquiv, splitDetectorSpaceToTargetEquiv,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    splitDetectorLinearMap_walk]
  exact splitDetectorLinearMap_target f S E _

/-- The canonical endpoint detector, transported from the contextual
detector at a displayed position. -/
def splitDetectorSpacePositionEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (S : P.ArrowPolarization) (i : E.Position) :
    SplitDetectorSpace N S E (.ofPosition E i) ≃ₗ[k]
      DetectorSpace N (detectorEndpoint S E) :=
  splitDetectorSpaceToTargetEquiv N S (Word.Split.walkToTarget E i)

/-- Position-to-endpoint transport commutes with every module morphism. -/
theorem splitDetectorLinearMap_position
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (S : P.ArrowPolarization) (i : E.Position)
    (q : SplitDetectorSpace M S E (.ofPosition E i)) :
    splitDetectorSpacePositionEquiv N S i
        (splitDetectorLinearMap f S E (.ofPosition E i) q) =
      detectorLinearMap f (detectorEndpoint S E)
        (splitDetectorSpacePositionEquiv M S i q) :=
  splitDetectorLinearMap_toTarget f S (Word.Split.walkToTarget E i) q

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
