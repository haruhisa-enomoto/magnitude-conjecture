import MagnitudeConjecture.Algebra.StringCohookDeletionNesting
import MagnitudeConjecture.Algebra.StringDetectorTrajectory
import MagnitudeConjecture.Algebra.StringPositivePath

/-!
# Peak wedges in string modules

A string which runs backwards along one ordinary path into a common vertex
and then forwards along another ordinary path is a peak wedge.  When both
endpoints are maximal peaks, every position of the word is reached from the
common vertex by one of the two outgoing arms.

The strict overlap of left and right cohook deletions has exactly this form.
This file packages that geometry independently of the deletion bookkeeping;
the resulting peak position is the generator used to compare the literal
right-string module with a covariant representable on the opposite quotient
category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A positive path occurring literally after one word prefix gives
reachability in the displayed arrow direction. -/
theorem pathReach_of_prefix_eq_positivePath
    (C : Word R) :
    ∀ {x y : Q} (p : Quiver.Path x y)
      (i : C.PositionAt x) (j : C.PositionAt y),
      j.1 = i.1.comp (positivePath p) →
        C.PathReach p i j := by
  intro x y p
  induction p with
  | nil =>
      intro i j hij
      change j.1 = i.1 at hij
      exact Subtype.ext hij.symm
  | @cons z y p a ih =>
      intro i j hij
      rcases j.2 with ⟨tail, htail⟩
      let middle : C.PositionAt z :=
        ⟨i.1.comp (positivePath p),
          ⟨(positiveArrow a).toPath.comp tail, by
            calc
              C.path = j.1.comp tail := htail
              _ = (i.1.comp (positivePath (p.cons a))).comp
                  tail := by rw [hij]
              _ = (i.1.comp (positivePath p)).comp
                  ((positiveArrow a).toPath.comp tail) := by
                simp only [positivePath_cons, positivePath_toPath,
                  Quiver.Path.comp_assoc]⟩⟩
      refine ⟨middle, ih i middle rfl, Or.inl ?_⟩
      exact hij

/-- A maximal two-arm peak decomposition of a string word. -/
structure PeakWedge (C : Word R) where
  peak : Q
  leftArm : Quiver.Path peak C.source
  rightArm : Quiver.Path peak C.target
  path_eq : C.path =
    (positivePath leftArm).reverse.comp (positivePath rightArm)
  startsOnPeak : C.StartsOnPeak
  endsOnPeak : C.EndsOnPeak

namespace PeakWedge

variable {C : Word R} (W : C.PeakWedge)

/-- The word length is the sum of the two arm lengths. -/
@[simp]
theorem word_length : C.length = W.leftArm.length + W.rightArm.length := by
  change C.path.length = _
  rw [W.path_eq, Quiver.Path.length_comp, length_reverse,
    positivePath_length, positivePath_length]

/-- The occurrence of the common peak between the two arms. -/
def peakPosition : C.PositionAt W.peak :=
  ⟨(positivePath W.leftArm).reverse,
    ⟨positivePath W.rightArm, W.path_eq⟩⟩

@[simp]
theorem peakPosition_index : W.peakPosition.index = W.leftArm.length := by
  change (positivePath W.leftArm).reverse.length = W.leftArm.length
  rw [length_reverse, positivePath_length]

/-- The position reached after following an initial segment of the right
arm from the peak. -/
def rightPosition {x : Q} (p : Quiver.Path W.peak x)
    (q : Quiver.Path x C.target) (h : W.rightArm = p.comp q) :
    C.PositionAt x :=
  ⟨(positivePath W.leftArm).reverse.comp (positivePath p),
    ⟨positivePath q, by
      calc
        C.path = (positivePath W.leftArm).reverse.comp
            (positivePath W.rightArm) := W.path_eq
        _ = (positivePath W.leftArm).reverse.comp
            ((positivePath p).comp (positivePath q)) := by
          rw [h, positivePath_comp]
        _ = ((positivePath W.leftArm).reverse.comp
            (positivePath p)).comp (positivePath q) := by
          rw [Quiver.Path.comp_assoc]⟩⟩

@[simp]
theorem rightPosition_index {x : Q} (p : Quiver.Path W.peak x)
    (q : Quiver.Path x C.target) (h : W.rightArm = p.comp q) :
    (W.rightPosition p q h).index = W.leftArm.length + p.length := by
  change ((positivePath W.leftArm).reverse.comp
    (positivePath p)).length = _
  rw [Quiver.Path.length_comp, length_reverse,
    positivePath_length, positivePath_length]

/-- The right-arm position is reached from the peak by its defining initial
segment. -/
theorem pathReach_rightPosition {x : Q} (p : Quiver.Path W.peak x)
    (q : Quiver.Path x C.target) (h : W.rightArm = p.comp q) :
    C.PathReach p W.peakPosition (W.rightPosition p q h) := by
  apply C.pathReach_of_prefix_eq_positivePath
  rfl

/-- The position reached after following an initial segment of the left arm
from the peak.  In the written word this position occurs on the reversed
left arm. -/
def leftPosition {x : Q} (p : Quiver.Path W.peak x)
    (q : Quiver.Path x C.source) (h : W.leftArm = p.comp q) :
    C.PositionAt x :=
  ⟨(positivePath q).reverse,
    ⟨(positivePath p).reverse.comp (positivePath W.rightArm), by
      calc
        C.path = (positivePath W.leftArm).reverse.comp
            (positivePath W.rightArm) := W.path_eq
        _ = ((positivePath p).comp (positivePath q)).reverse.comp
            (positivePath W.rightArm) := by
          rw [h, positivePath_comp]
        _ = (positivePath q).reverse.comp
            ((positivePath p).reverse.comp
              (positivePath W.rightArm)) := by
          rw [Quiver.Path.reverse_comp, Quiver.Path.comp_assoc]⟩⟩

@[simp]
theorem leftPosition_index {x : Q} (p : Quiver.Path W.peak x)
    (q : Quiver.Path x C.source) (h : W.leftArm = p.comp q) :
    (W.leftPosition p q h).index = q.length := by
  change (positivePath q).reverse.length = q.length
  rw [length_reverse, positivePath_length]

/-- The left-arm position is reached from the peak by its defining initial
segment. -/
theorem pathReach_leftPosition {x : Q} (p : Quiver.Path W.peak x)
    (q : Quiver.Path x C.source) (h : W.leftArm = p.comp q) :
    C.PathReach p W.peakPosition (W.leftPosition p q h) := by
  apply C.pathReach_of_prefix_eq_positivePath_reverse
  change (positivePath W.leftArm).reverse =
    (positivePath q).reverse.comp (positivePath p).reverse
  rw [h, positivePath_comp, Quiver.Path.reverse_comp]

/-- Every occurrence along a peak wedge is reached from the common peak by
an ordinary path along one of its two arms. -/
theorem exists_pathReach_peak (i : C.Position) :
    ∃ p : Quiver.Path W.peak i.1,
      C.PathReach p W.peakPosition i.2 := by
  by_cases hi : i.index ≤ W.leftArm.length
  · obtain ⟨x, p, q, hpq, hp⟩ :=
      W.leftArm.exists_eq_comp_of_le_length
        (n := W.leftArm.length - i.index) (Nat.sub_le _ _)
    have hq : q.length = i.index := by
      have hlength := congrArg Quiver.Path.length hpq
      simp only [Quiver.Path.length_comp, hp] at hlength
      omega
    let j : C.PositionAt x := W.leftPosition p q hpq
    have hji : (⟨x, j⟩ : C.Position) = i := by
      apply Position.ext_index
      change (W.leftPosition p q hpq).index = i.index
      rw [W.leftPosition_index]
      exact hq
    cases hji
    exact ⟨p, W.pathReach_leftPosition p q hpq⟩
  · have hleft : W.leftArm.length ≤ i.index := Nat.le_of_not_ge hi
    have hindexBound :
        i.index ≤ W.leftArm.length + W.rightArm.length := by
      rw [← W.word_length]
      exact i.2.index_le
    have hbound : i.index - W.leftArm.length ≤ W.rightArm.length := by
      omega
    obtain ⟨x, p, q, hpq, hp⟩ :=
      W.rightArm.exists_eq_comp_of_le_length hbound
    let j : C.PositionAt x := W.rightPosition p q hpq
    have hji : (⟨x, j⟩ : C.Position) = i := by
      apply Position.ext_index
      change (W.rightPosition p q hpq).index = i.index
      rw [W.rightPosition_index, hp]
      omega
    cases hji
    exact ⟨p, W.pathReach_rightPosition p q hpq⟩

/-- An ordinary path from the common peak is determined by the word
position which it reaches. -/
theorem path_eq_of_pathReach_peak
    {y : Q} (p q : Quiver.Path W.peak y) (j : C.PositionAt y)
    (hp : C.PathReach p W.peakPosition j)
    (hq : C.PathReach q W.peakPosition j) : p = q := by
  rcases C.pathReach_forward_or_backward p W.peakPosition j hp with
    hpforward | hpbackward <;>
  rcases C.pathReach_forward_or_backward q W.peakPosition j hq with
    hqforward | hqbackward
  · apply positivePath_injective p q
    apply Quiver.Path.comp_injective_right W.peakPosition.1
    exact hpforward.symm.trans hqforward
  · have hpLength := congrArg Quiver.Path.length hpforward
    have hqLength := congrArg Quiver.Path.length hqbackward
    simp only [Quiver.Path.length_comp, positivePath_length,
      length_reverse] at hpLength hqLength
    have hpzero : p.length = 0 := by omega
    have hqzero : q.length = 0 := by omega
    have hpy : W.peak = y := p.eq_of_length_zero hpzero
    subst y
    rw [p.eq_nil_of_length_zero hpzero,
      q.eq_nil_of_length_zero hqzero]
  · have hpLength := congrArg Quiver.Path.length hpbackward
    have hqLength := congrArg Quiver.Path.length hqforward
    simp only [Quiver.Path.length_comp, positivePath_length,
      length_reverse] at hpLength hqLength
    have hpzero : p.length = 0 := by omega
    have hqzero : q.length = 0 := by omega
    have hpy : W.peak = y := p.eq_of_length_zero hpzero
    subst y
    rw [p.eq_nil_of_length_zero hpzero,
      q.eq_nil_of_length_zero hqzero]
  · have hreverse : (positivePath p).reverse =
        (positivePath q).reverse := by
      apply Quiver.Path.comp_injective_right j.1
      exact hpbackward.symm.trans hqbackward
    apply positivePath_injective p q
    have := congrArg Quiver.Path.reverse hreverse
    simpa only [Quiver.Path.reverse_reverse] using this

/-- Reversing a peak wedge exchanges its two outgoing arms. -/
def reverse : C.reverse.PeakWedge where
  peak := W.peak
  leftArm := W.rightArm
  rightArm := W.leftArm
  path_eq := by
    change C.path.reverse =
      (positivePath W.rightArm).reverse.comp (positivePath W.leftArm)
    rw [W.path_eq, Quiver.Path.reverse_comp,
      Quiver.Path.reverse_reverse]
  startsOnPeak := W.endsOnPeak
  endsOnPeak := by
    rw [EndsOnPeak, reverse_reverse]
    exact W.startsOnPeak

end PeakWedge

namespace PeakWedge

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable (P : SpecialBiserialPresentation k A Q)
variable {C : Word P.toPresentation.relations}
variable (W : C.PeakWedge)

/-- A surviving path cannot strictly extend the maximal right arm of a
two-sided peak wedge. -/
theorem not_surviving_of_rightArm_strictPrefix
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    {y : Q} (p : Quiver.Path W.peak y)
    (hp : pathMap P.toPresentation.relations p ≠ 0)
    (hprefix : ∃ r : Quiver.Path C.target y,
      p = W.rightArm.comp r)
    (hlength : W.rightArm.length < p.length) : False := by
  obtain ⟨r, hr⟩ := hprefix
  have hrpos : 0 < r.length := by
    have hlen := congrArg Quiver.Path.length hr
    simp only [Quiver.Path.length_comp] at hlen
    omega
  obtain ⟨z, b, tail, _, hrpath⟩ :=
    r.eq_toPath_comp_of_length_eq_succ (show r.length =
      (r.length - 1) + 1 by omega)
  have hshort :
      pathMap P.toPresentation.relations (W.rightArm.cons b) ≠ 0 := by
    intro hzero
    apply hp
    rw [hr, hrpath, ← Quiver.Path.comp_assoc]
    change pathMap P.toPresentation.relations
      ((W.rightArm.cons b).comp tail) = 0
    rw [(pathMap_comp P.toPresentation.relations
      (W.rightArm.cons b) tail).symm, hzero,
      CategoryTheory.Limits.comp_zero]
  have hpositive : IsString P.toPresentation.relations
      (positivePath (W.rightArm.cons b)) :=
    isString_positivePath_of_pathMap_ne_zero
      P.toPresentation.admissible (W.rightArm.cons b) hshort
  obtain ⟨v, a, leftTail, _, hleftPath⟩ :=
    W.leftArm.eq_toPath_comp_of_length_eq_succ (show W.leftArm.length =
      (W.leftArm.length - 1) + 1 by omega)
  have hwedgePath :
      (positivePath leftTail).reverse.comp
          ((negativeArrow a).toPath.comp (positivePath W.rightArm)) =
        C.path := by
    calc
      (positivePath leftTail).reverse.comp
          ((negativeArrow a).toPath.comp (positivePath W.rightArm)) =
          ((positivePath leftTail).reverse.comp
            (negativeArrow a).toPath).comp
              (positivePath W.rightArm) :=
        (Quiver.Path.comp_assoc _ _ _).symm
      _ = ((positiveArrow a).toPath.comp
          (positivePath leftTail)).reverse.comp
            (positivePath W.rightArm) := by
        simp only [Quiver.Path.reverse_comp,
          Quiver.Path.reverse_toPath, reverse_positiveArrow]
      _ = (positivePath W.leftArm).reverse.comp
          (positivePath W.rightArm) := by
        rw [hleftPath, positivePath_comp, positivePath_toPath]
      _ = C.path := W.path_eq.symm
  have hleftString : IsString P.toPresentation.relations
      ((positivePath leftTail).reverse.comp
        ((negativeArrow a).toPath.comp (positivePath W.rightArm))) := by
    rw [hwedgePath]
    exact C.isString
  have hrightString : IsString P.toPresentation.relations
      ((positivePath W.rightArm).comp
        ((positiveArrow b).toPath.comp Quiver.Path.nil)) := by
    simpa only [Quiver.Path.comp_nil, positivePath_cons,
      positivePath_toPath] using hpositive
  have hfull := isString_comp_of_negative_positive_boundaries
    P.toPresentation.relations
    (positivePath leftTail).reverse a
    (positivePath W.rightArm) b Quiver.Path.nil
    (by simpa only [positivePath_length] using hright)
    hleftString hrightString
  apply W.startsOnPeak b
  have hfullPath :
      (positivePath leftTail).reverse.comp
          ((negativeArrow a).toPath.comp
            ((positivePath W.rightArm).comp
              ((positiveArrow b).toPath.comp Quiver.Path.nil))) =
        C.path.comp (positiveArrow b).toPath := by
    simp only [Quiver.Path.comp_nil]
    calc
      (positivePath leftTail).reverse.comp
          ((negativeArrow a).toPath.comp
            ((positivePath W.rightArm).comp
              (positiveArrow b).toPath)) =
          ((positivePath leftTail).reverse.comp
            ((negativeArrow a).toPath.comp
              (positivePath W.rightArm))).comp
                (positiveArrow b).toPath := by
            simp only [Quiver.Path.comp_assoc]
      _ = C.path.comp (positiveArrow b).toPath :=
        congrArg (fun t ↦ t.comp (positiveArrow b).toPath) hwedgePath
  rw [← hfullPath]
  exact hfull

/-- A surviving path cannot strictly extend the maximal left arm of a
two-sided peak wedge. -/
theorem not_surviving_of_leftArm_strictPrefix
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    {y : Q} (p : Quiver.Path W.peak y)
    (hp : pathMap P.toPresentation.relations p ≠ 0)
    (hprefix : ∃ r : Quiver.Path C.source y,
      p = W.leftArm.comp r)
    (hlength : W.leftArm.length < p.length) : False := by
  exact W.reverse.not_surviving_of_rightArm_strictPrefix P
    hright hleft p hp hprefix hlength

/-- A path from the peak is a prefix of one of the two outgoing arms. -/
def IsArmPrefix {y : Q} (p : Quiver.Path W.peak y) : Prop :=
  (∃ r : Quiver.Path y C.source, W.leftArm = p.comp r) ∨
    (∃ r : Quiver.Path y C.target, W.rightArm = p.comp r)

end PeakWedge

namespace PeakWedge

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable (P : SpecialBiserialPresentation k A Q)
variable {C : Word P.toPresentation.relations}
variable (W : C.PeakWedge)

/-- Every surviving ordinary path starting at the common peak is a prefix
of one of the two arms. -/
theorem isArmPrefix_of_pathMap_ne_zero
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    {y : Q} (p : Quiver.Path W.peak y)
    (hp : pathMap P.toPresentation.relations p ≠ 0) :
    IsArmPrefix P W p := by
  have hleftFactor : W.leftArm = W.leftArm.comp Quiver.Path.nil := by simp
  have hrightFactor : W.rightArm = W.rightArm.comp Quiver.Path.nil := by simp
  have hleftSurvives :
      pathMap P.toPresentation.relations W.leftArm ≠ 0 :=
    C.pathMap_ne_zero_of_pathReach W.leftArm W.peakPosition
      (W.leftPosition W.leftArm Quiver.Path.nil hleftFactor)
      (W.pathReach_leftPosition W.leftArm Quiver.Path.nil hleftFactor)
  have hrightSurvives :
      pathMap P.toPresentation.relations W.rightArm ≠ 0 :=
    C.pathMap_ne_zero_of_pathReach W.rightArm W.peakPosition
      (W.rightPosition W.rightArm Quiver.Path.nil hrightFactor)
      (W.pathReach_rightPosition W.rightArm Quiver.Path.nil hrightFactor)
  by_cases hpzero : p.length = 0
  · have hpy : W.peak = y := p.eq_of_length_zero hpzero
    subst y
    have hpNil : p = Quiver.Path.nil := p.eq_nil_of_length_zero hpzero
    subst p
    left
    exact ⟨W.leftArm, by simp⟩
  · obtain ⟨z, c, pTail, _, hpPath⟩ :=
      p.eq_toPath_comp_of_length_eq_succ (show p.length =
        (p.length - 1) + 1 by omega)
    obtain ⟨v, a, leftTail, _, hleftPath⟩ :=
      W.leftArm.eq_toPath_comp_of_length_eq_succ
        (show W.leftArm.length = W.leftArm.length - 1 + 1 by omega)
    obtain ⟨w, b, rightTail, _, hrightPath⟩ :=
      W.rightArm.eq_toPath_comp_of_length_eq_succ
        (show W.rightArm.length = W.rightArm.length - 1 + 1 by omega)
    let previous : C.PositionAt v :=
      W.leftPosition a.toPath leftTail hleftPath
    let next : C.PositionAt w :=
      W.rightPosition b.toPath rightTail hrightPath
    have hprevIndex : previous.index + 1 = W.peakPosition.index := by
      simp only [previous, W.leftPosition_index,
        W.peakPosition_index]
      have hlen := congrArg Quiver.Path.length hleftPath
      simp only [Quiver.Path.length_comp,
        Quiver.Path.length_toPath] at hlen
      omega
    have hnextIndex : next.index = W.peakPosition.index + 1 := by
      simp only [next, W.rightPosition_index,
        W.peakPosition_index, Quiver.Path.length_toPath]
    have hprevStep : C.ArrowStep a W.peakPosition previous := by
      have hreach :=
        W.pathReach_leftPosition a.toPath leftTail hleftPath
      rcases hreach with ⟨middle, hmiddle, hstep⟩
      change W.peakPosition = middle at hmiddle
      subst middle
      exact hstep
    have hnextStep : C.ArrowStep b W.peakPosition next := by
      have hreach :=
        W.pathReach_rightPosition b.toPath rightTail hrightPath
      rcases hreach with ⟨middle, hmiddle, hstep⟩
      change W.peakPosition = middle at hmiddle
      subst middle
      exact hstep
    have hab : (⟨v, a⟩ : Quiver.Star W.peak) ≠ ⟨w, b⟩ :=
      C.outgoingAdjacentArrows_ne a b previous W.peakPosition next
        hprevIndex hnextIndex hprevStep hnextStep
    have hc : (⟨z, c⟩ : Quiver.Star W.peak) = ⟨v, a⟩ ∨
        (⟨z, c⟩ : Quiver.Star W.peak) = ⟨w, b⟩ := by
      by_cases hca : (⟨z, c⟩ : Quiver.Star W.peak) = ⟨v, a⟩
      · exact Or.inl hca
      · right
        exact eq_of_ne_of_ne_of_natCard_le_two
          (⟨v, a⟩ : Quiver.Star W.peak) ⟨z, c⟩ ⟨w, b⟩
          hca hab.symm (P.arrows_starting_le_two W.peak)
    rcases hc with hca | hcb
    · cases hca
      have hpTail :
          pathMap P.toPresentation.relations pTail ≫
              arrowMap P.toPresentation.relations c ≠ 0 := by
        change pathMap P.toPresentation.relations pTail ≫
          pathMap P.toPresentation.relations c.toPath ≠ 0
        rw [pathMap_comp]
        rw [← hpPath]
        exact hp
      have hleftTail :
          pathMap P.toPresentation.relations leftTail ≫
              arrowMap P.toPresentation.relations c ≠ 0 := by
        change pathMap P.toPresentation.relations leftTail ≫
          pathMap P.toPresentation.relations c.toPath ≠ 0
        rw [pathMap_comp]
        rw [← hleftPath]
        exact hleftSurvives
      let pp : P.RightContinuationPath c :=
        ⟨⟨y, pTail⟩, hpTail⟩
      let ll : P.RightContinuationPath c :=
        ⟨⟨C.source, leftTail⟩, hleftTail⟩
      by_cases hle : p.length ≤ W.leftArm.length
      · have htailLe : pTail.length ≤ leftTail.length := by
          have hpLen := congrArg Quiver.Path.length hpPath
          have hleftLen := congrArg Quiver.Path.length hleftPath
          simp only [Quiver.Path.length_comp,
            Quiver.Path.length_toPath] at hpLen hleftLen
          omega
        obtain ⟨r, hr⟩ :=
          P.rightContinuationPath_factor_of_length_le c pp ll htailLe
        change leftTail = pTail.comp r at hr
        left
        refine ⟨r, ?_⟩
        rw [hleftPath, hpPath, hr, Quiver.Path.comp_assoc]
      · have htailLe : leftTail.length ≤ pTail.length := by
          have hpLen := congrArg Quiver.Path.length hpPath
          have hleftLen := congrArg Quiver.Path.length hleftPath
          simp only [Quiver.Path.length_comp,
            Quiver.Path.length_toPath] at hpLen hleftLen
          omega
        obtain ⟨r, hr⟩ :=
          P.rightContinuationPath_factor_of_length_le c ll pp htailLe
        change pTail = leftTail.comp r at hr
        exfalso
        apply not_surviving_of_leftArm_strictPrefix P W
          hleft hright p hp ⟨r, ?_⟩ (Nat.lt_of_not_ge hle)
        rw [hpPath, hleftPath, hr, Quiver.Path.comp_assoc]
    · cases hcb
      have hpTail :
          pathMap P.toPresentation.relations pTail ≫
              arrowMap P.toPresentation.relations c ≠ 0 := by
        change pathMap P.toPresentation.relations pTail ≫
          pathMap P.toPresentation.relations c.toPath ≠ 0
        rw [pathMap_comp]
        rw [← hpPath]
        exact hp
      have hrightTail :
          pathMap P.toPresentation.relations rightTail ≫
              arrowMap P.toPresentation.relations c ≠ 0 := by
        change pathMap P.toPresentation.relations rightTail ≫
          pathMap P.toPresentation.relations c.toPath ≠ 0
        rw [pathMap_comp]
        rw [← hrightPath]
        exact hrightSurvives
      let pp : P.RightContinuationPath c :=
        ⟨⟨y, pTail⟩, hpTail⟩
      let rr : P.RightContinuationPath c :=
        ⟨⟨C.target, rightTail⟩, hrightTail⟩
      by_cases hle : p.length ≤ W.rightArm.length
      · have htailLe : pTail.length ≤ rightTail.length := by
          have hpLen := congrArg Quiver.Path.length hpPath
          have hrightLen := congrArg Quiver.Path.length hrightPath
          simp only [Quiver.Path.length_comp,
            Quiver.Path.length_toPath] at hpLen hrightLen
          omega
        obtain ⟨r, hr⟩ :=
          P.rightContinuationPath_factor_of_length_le c pp rr htailLe
        change rightTail = pTail.comp r at hr
        right
        refine ⟨r, ?_⟩
        rw [hrightPath, hpPath, hr, Quiver.Path.comp_assoc]
      · have htailLe : rightTail.length ≤ pTail.length := by
          have hpLen := congrArg Quiver.Path.length hpPath
          have hrightLen := congrArg Quiver.Path.length hrightPath
          simp only [Quiver.Path.length_comp,
            Quiver.Path.length_toPath] at hpLen hrightLen
          omega
        obtain ⟨r, hr⟩ :=
          P.rightContinuationPath_factor_of_length_le c rr pp htailLe
        change pTail = rightTail.comp r at hr
        exfalso
        apply not_surviving_of_rightArm_strictPrefix P W
          hleft hright p hp ⟨r, ?_⟩ (Nat.lt_of_not_ge hle)
        rw [hpPath, hrightPath, hr, Quiver.Path.comp_assoc]

/-- Every surviving path from the common peak reaches a word position. -/
theorem exists_pathReach_peak_of_pathMap_ne_zero
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    {y : Q} (p : Quiver.Path W.peak y)
    (hp : pathMap P.toPresentation.relations p ≠ 0) :
    ∃ j : C.PositionAt y, C.PathReach p W.peakPosition j := by
  rcases W.isArmPrefix_of_pathMap_ne_zero P hleft hright p hp with
    ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨W.leftPosition p r hr, W.pathReach_leftPosition p r hr⟩
  · exact ⟨W.rightPosition p r hr, W.pathReach_rightPosition p r hr⟩

/-- The target position reached by a surviving path from the common peak. -/
noncomputable def survivingPathTargetPosition
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    (y : Q)
    (p : SurvivingPath P.toPresentation.relations W.peak y) :
    C.PositionAt y :=
  Classical.choose
    (exists_pathReach_peak_of_pathMap_ne_zero P W
      hleft hright p.1 p.2)

theorem pathReach_survivingPathTargetPosition
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    (y : Q)
    (p : SurvivingPath P.toPresentation.relations W.peak y) :
    C.PathReach p.1 W.peakPosition
      (survivingPathTargetPosition P W hleft hright y p) :=
  Classical.choose_spec
    (exists_pathReach_peak_of_pathMap_ne_zero P W
      hleft hright p.1 p.2)

/-- The surviving ordinary path which reaches a given word position from
the common peak. -/
noncomputable def positionSurvivingPath
    (y : Q) (j : C.PositionAt y) :
    SurvivingPath P.toPresentation.relations W.peak y := by
  let h := W.exists_pathReach_peak ⟨y, j⟩
  exact ⟨Classical.choose h,
    C.pathMap_ne_zero_of_pathReach (Classical.choose h)
      W.peakPosition j (Classical.choose_spec h)⟩

theorem pathReach_positionSurvivingPath
    (y : Q) (j : C.PositionAt y) :
    C.PathReach (positionSurvivingPath P W y j).1
      W.peakPosition j := by
  exact Classical.choose_spec (W.exists_pathReach_peak ⟨y, j⟩)

/-- Surviving paths from the common peak are in bijection with the word
positions over each displayed vertex. -/
noncomputable def survivingPathEquivPositionAt
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    (y : Q) :
    SurvivingPath P.toPresentation.relations W.peak y ≃
      C.PositionAt y where
  toFun := survivingPathTargetPosition P W hleft hright y
  invFun := positionSurvivingPath P W y
  left_inv p := by
    apply Subtype.ext
    exact W.path_eq_of_pathReach_peak _ _ _
      (pathReach_positionSurvivingPath P W y
        (survivingPathTargetPosition P W hleft hright y p))
      (pathReach_survivingPathTargetPosition P W hleft hright y p)
  right_inv j := by
    have htarget := pathReach_survivingPathTargetPosition P W
      hleft hright y (positionSurvivingPath P W y j)
    have hj := pathReach_positionSurvivingPath P W y j
    exact congrArg Subtype.val
      (@Subsingleton.elim
        {t : C.PositionAt y //
          C.PathReach (positionSurvivingPath P W y j).1
            W.peakPosition t}
        (C.pathReach_subsingleton
          (positionSurvivingPath P W y j).1 W.peakPosition)
        ⟨survivingPathTargetPosition P W hleft hright y
          (positionSurvivingPath P W y j), htarget⟩
        ⟨j, hj⟩)

end PeakWedge

/-- A strict overlap of left and right cohook deletions produces a maximal
peak wedge whose two nonempty arms have exactly the cohook-tail lengths. -/
theorem exists_peakWedge_of_overlappingCohookDeletions
    {A : Type u} [Ring A] [Algebra k A]
    [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
    (P : SpecialBiserialPresentation k A Q)
    {C L D : Word P.toPresentation.relations}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L)
    (hoverlap : C.length < leftDeletion.steps + rightDeletion.steps) :
    ∃ W : C.PeakWedge,
      W.leftArm.length = leftDeletion.cohook.tail.steps ∧
      W.rightArm.length = rightDeletion.cohook.tail.steps ∧
      0 < W.leftArm.length ∧ 0 < W.rightArm.length := by
  obtain ⟨u, leftArm, rightArm, hpath, hleftArm, hrightArm⟩ :=
    exists_peak_path_decomposition_of_overlappingCohookDeletions
      leftDeletion rightDeletion hoverlap
  obtain ⟨hrightLength, hleftLength, _⟩ :=
    overlappingCohookDeletion_rigidity
      leftDeletion rightDeletion hoverlap
  let W : C.PeakWedge :=
    ⟨u, leftArm, rightArm, hpath,
      rightDeletion.source_startsOnPeak,
      leftDeletion.source_endsOnPeak⟩
  refine ⟨W, hleftArm, hrightArm, ?_, ?_⟩
  · rw [hleftArm, hleftLength]
    omega
  · rw [hrightArm, hrightLength]
    omega

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
